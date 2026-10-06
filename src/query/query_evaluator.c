/*
 * Copyright 2008 Search Solution Corporation
 * Copyright 2016 CUBRID Corporation
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 *
 */

/*
 * query_evaluator.c - Predicate evaluator
 */

#ident "$Id$"

#include "config.h"

#include <stdio.h>
#include <string.h>

#include "system_parameter.h"
#include "error_manager.h"
#include "heap_file.h"
#include "fetch.h"
#include "list_file.h"
#include "qfile_tuple_layout.h"
#include "object_primitive.h"
#include "object_representation.h"
#include "regu_var.hpp"
#include "set_object.h"
#include "xasl.h"
#include "dbtype.h"
#include "query_executor.h"
#include "query_opfunc.h"
#include "dbtype.h"
#include "language_support.h"
#include "string_opfunc.h"
#include "thread_entry.hpp"
#include "xasl_predicate.hpp"
// XXX: SHOULD BE THE LAST INCLUDE HEADER
#include "memory_wrapper.hpp"

#define UNKNOWN_CARD   -2	/* Unknown cardinality of a set member */

/* What an ALL/SOME term compares its item with in this execution: a constant right side's elements
 * by position (`constant`), else a computed collection's elements by their keys in the item's row of the type pair
 * comparison table (`row`), else `each` for every element; `all` for every value of a list or a right side that is
 * no collection. */
struct EVAL_ELEMENTS
{
  const DOMAIN_COMPARE *all;
  const DOMAIN_COMPARE *each;
  int row;			/* -1: none */
  const DOMAIN_ELEMENTS *constant;
};

static DB_LOGICAL eval_negative (DB_LOGICAL res);
static DB_LOGICAL eval_logical_result (DB_LOGICAL res1, DB_LOGICAL res2);
static DB_LOGICAL eval_value_rel_cmp (THREAD_ENTRY * thread_p, DB_VALUE * dbval1, DB_VALUE * dbval2,
				      REL_OP rel_operator, const COMP_EVAL_TERM * et_comp, const val_descr * vd,
				      const DOMAIN_COMPARE * compare, const DB_VALUE * unconverted2);
static DB_LOGICAL eval_some_eval (THREAD_ENTRY * thread_p, DB_VALUE * item, DB_SET * set, REL_OP rel_operator,
				  const EVAL_ELEMENTS * elements, const val_descr * vd);
static DB_LOGICAL eval_all_eval (THREAD_ENTRY * thread_p, DB_VALUE * item, DB_SET * set, REL_OP rel_operator,
				 const EVAL_ELEMENTS * elements, const val_descr * vd);
static int eval_item_card_set (THREAD_ENTRY * thread_p, DB_VALUE * item, DB_SET * set, REL_OP rel_operator);
static DB_LOGICAL eval_some_list_eval (THREAD_ENTRY * thread_p, DB_VALUE * item, QFILE_LIST_ID * list_id,
				       REL_OP rel_operator, const DOMAIN_COMPARE * compare, const val_descr * vd);
static DB_LOGICAL eval_all_list_eval (THREAD_ENTRY * thread_p, DB_VALUE * item, QFILE_LIST_ID * list_id,
				      REL_OP rel_operator, const DOMAIN_COMPARE * compare, const val_descr * vd);
static int eval_item_card_sort_list (THREAD_ENTRY * thread_p, DB_VALUE * item, QFILE_LIST_ID * list_id);
static DB_LOGICAL eval_sub_multi_set_to_sort_list (THREAD_ENTRY * thread_p, DB_SET * set1, QFILE_LIST_ID * list_id);
static DB_LOGICAL eval_sub_sort_list_to_multi_set (THREAD_ENTRY * thread_p, QFILE_LIST_ID * list_id, DB_SET * set);
static DB_LOGICAL eval_sub_sort_list_to_sort_list (THREAD_ENTRY * thread_p, QFILE_LIST_ID * list_id1,
						   QFILE_LIST_ID * list_id2);
static DB_LOGICAL eval_eq_multi_set_to_sort_list (THREAD_ENTRY * thread_p, DB_SET * set, QFILE_LIST_ID * list_id);
static DB_LOGICAL eval_ne_multi_set_to_sort_list (THREAD_ENTRY * thread_p, DB_SET * set, QFILE_LIST_ID * list_id);
static DB_LOGICAL eval_le_multi_set_to_sort_list (THREAD_ENTRY * thread_p, DB_SET * set, QFILE_LIST_ID * list_id);
static DB_LOGICAL eval_lt_multi_set_to_sort_list (THREAD_ENTRY * thread_p, DB_SET * set, QFILE_LIST_ID * list_id);
static DB_LOGICAL eval_le_sort_list_to_multi_set (THREAD_ENTRY * thread_p, QFILE_LIST_ID * list_id, DB_SET * set);
static DB_LOGICAL eval_lt_sort_list_to_multi_set (THREAD_ENTRY * thread_p, QFILE_LIST_ID * list_id, DB_SET * set);
static DB_LOGICAL eval_eq_sort_list_to_sort_list (THREAD_ENTRY * thread_p, QFILE_LIST_ID * list_id1,
						  QFILE_LIST_ID * list_id2);
static DB_LOGICAL eval_ne_sort_list_to_sort_list (THREAD_ENTRY * thread_p, QFILE_LIST_ID * list_id1,
						  QFILE_LIST_ID * list_id2);
static DB_LOGICAL eval_le_sort_list_to_sort_list (THREAD_ENTRY * thread_p, QFILE_LIST_ID * list_id1,
						  QFILE_LIST_ID * list_id2);
static DB_LOGICAL eval_lt_sort_list_to_sort_list (THREAD_ENTRY * thread_p, QFILE_LIST_ID * list_id1,
						  QFILE_LIST_ID * list_id2);
static DB_LOGICAL eval_multi_set_to_sort_list (THREAD_ENTRY * thread_p, DB_SET * set, QFILE_LIST_ID * list_id,
					       REL_OP rel_operator);
static DB_LOGICAL eval_sort_list_to_multi_set (THREAD_ENTRY * thread_p, QFILE_LIST_ID * list_id, DB_SET * set,
					       REL_OP rel_operator);
static DB_LOGICAL eval_sort_list_to_sort_list (THREAD_ENTRY * thread_p, QFILE_LIST_ID * list_id1,
					       QFILE_LIST_ID * list_id2, REL_OP rel_operator);
static DB_LOGICAL eval_set_list_cmp (THREAD_ENTRY * thread_p, const COMP_EVAL_TERM * et_comp, val_descr * vd,
				     DB_VALUE * dbval1, DB_VALUE * dbval2);

/*
 * eval_negative () - negate the result
 *   return: DB_LOGICAL (V_TRUE, V_FALSE, V_UNKNOWN or V_ERROR)
 *   res(in): result
 */
static DB_LOGICAL
eval_negative (DB_LOGICAL res)
{
  /* negate the result */
  if (res == V_TRUE)
    {
      return V_FALSE;
    }
  else if (res == V_FALSE)
    {
      return V_TRUE;
    }

  /* V_ERROR, V_UNKNOWN */
  return res;
}

/*
 * eval_logical_result () - evaluate the given two results
 *   return: DB_LOGICAL (V_TRUE, V_FALSE, V_UNKNOWN or V_ERROR)
 *   res1(in): first result
 *   res2(in): second result
 */
static DB_LOGICAL
eval_logical_result (DB_LOGICAL res1, DB_LOGICAL res2)
{
  if (res1 == V_ERROR || res2 == V_ERROR)
    {
      return V_ERROR;
    }

  if (res1 == V_TRUE && res2 == V_TRUE)
    {
      return V_TRUE;
    }
  else if (res1 == V_FALSE || res2 == V_FALSE)
    {
      return V_FALSE;
    }

  return V_UNKNOWN;
}

/*
 * Predicate Evaluation
 */

/*
 * Planned comparisons
 *
 * A comparison term's resolved comparison holds the comparison tp_value_compare_with_error makes between its sides'
 * values, resolved by the load or, once per execution, by resolve_domains: the converters in the order that function
 * runs them, the type whose cmpval compares, the collation, and its outcome when a conversion fails. The row runs
 * them; it resolves nothing.
 */

/* tp_value_compare_with_error on the values (comparison method VALUES): a NULL element, a side the plan leaves
 * variable, a comparison no resolution holds; constant-initialized */
/*
 * [리뷰] eval_values_comparison — "해결된 것이 없다 = 두 DB_VALUE 를 tp_value_compare_with_error 로 그냥 비교" 를 뜻하는
 * DOMAIN_COMPARE 상수를 만든다 — 정적 상수 eval_Compare_values 의 초기값이고, 모든 폴백 경로가 이 주소를 돌려준다.
 * develop: develop 에 없음 — 이 PR 이 신설(develop 에는 DOMAIN_COMPARE 타입 자체가 없다).
 * 이 PR: method=DOMAIN_COMPARE_VALUES, value[0]=value[1]=-1(양쪽 모두 행의 값), codeset_side=-1, compare_index=-1 로 채워
 * 돌려주는 constexpr 함수.
 * 바뀐 것: 신설 +12줄. 주석대로 GCC 8.5 의 constexpr ICE 때문에 대입을 한 줄씩 쪼갰다.
 */
static constexpr DOMAIN_COMPARE
eval_values_comparison ()
{
  DOMAIN_COMPARE compare = DOMAIN_COMPARE ();
  compare.method = DOMAIN_COMPARE_VALUES;
  /* one assignment each: GCC 8.5 fails with an internal compiler error on a chained one in a constexpr function */
  compare.value[0] = -1;
  compare.value[1] = -1;
  compare.codeset_side = -1;
  compare.compare_index = -1;
  return compare;
}

static constexpr DOMAIN_COMPARE eval_Compare_values = eval_values_comparison ();

/* The element comparisons of a set or list comparison: the collections' elements are their data, so the comparison
 * reads the key pair table by the two values' keys. */
/*
 * [리뷰] eval_keys_comparison — 컬렉션 원소끼리의 비교(= 두 값의 키 쌍표로 비교)를 뜻하는 DOMAIN_COMPARE 상수 — 정적 상수
 * eval_Compare_elements 의 초기값.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: eval_values_comparison () 결과를 받아 method 만 DOMAIN_COMPARE_KEYS 로 바꿔 돌려준다.
 * 바뀐 것: 신설 +7줄.
 */
static constexpr DOMAIN_COMPARE
eval_keys_comparison (void)
{
  DOMAIN_COMPARE compare = eval_values_comparison ();
  compare.method = DOMAIN_COMPARE_KEYS;
  return compare;
}

static constexpr DOMAIN_COMPARE eval_Compare_elements = eval_keys_comparison ();

/*
 * eval_resolved_comparison () - the resolution of a resolved comparison in this execution: the load's, or
 *			  resolve_domains' for a comparison resolve_domains resolves
 *   return: comparison method VALUES with its reason where the row compares by value: a late-bind comparison read
 *	     without resolve_domains' state
 */
/*
 * [리뷰] eval_resolved_comparison — 비교항이 들고 있는 DOMAIN_COMPARE_PLAN 에서 '이번 실행이 쓸 해결 결과' 하나를 골라 돌려준다 — 행마다 불리는
 * 조회자로, 결정은 하지 않는다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: 로드가 고정한 fixed 를 기본으로 쓰고, method 가 LATE_BIND(_SESSION) 이면
 * vd->xasl_state->resolved_domain.compares[compare_index] 로 바꿔 돌려준다. vd·xasl_state·compares 중 하나라도 없으면
 * eval_Compare_values 로 떨어진다. PX 워커 클론이 리더와 같은 번호를 쓰는지는 assert 로 교차검증한다.
 * 바뀐 것: 신설 +23줄, static inline. 실행 전 게이트가 채운 표를 행이 번호로 읽는 구조의 핵심 접근자.
 * [지적 A2-06]
 */
static inline const DOMAIN_COMPARE *
eval_resolved_comparison (const DOMAIN_COMPARE_PLAN * comparison, const val_descr * vd)
{
  const DOMAIN_COMPARE *compare = &comparison->fixed;
  if (compare->method == DOMAIN_COMPARE_LATE_BIND || compare->method == DOMAIN_COMPARE_LATE_BIND_SESSION)
    {
      if (vd == NULL || vd->xasl_state == NULL || vd->xasl_state->resolved_domain.compares == NULL)
	{
	  return &eval_Compare_values;
	}
      const RESOLVED_DOMAIN_TABLE & resolved = vd->xasl_state->resolved_domain;
      /* a PX worker's own XASL clone loaded the same stream: its comparisons number the leader's resolutions as the
       * leader's plan does, and it reads them by that number */
      assert (compare->compare_index >= 0 && compare->compare_index < resolved.n_compare_indexes
	      && resolved.plan != NULL
	      && (resolved.copied_from_leader ? resolved.plan->compares[compare->compare_index]->value[0] ==
		  comparison->value[0]
		  && resolved.plan->compares[compare->compare_index]->value[1] ==
		  comparison->value[1] : resolved.plan->compares[compare->compare_index] == comparison));
      compare = &resolved.compares[compare->compare_index];
    }
  return compare;
}

/*
 * eval_resolved_compare () - the comparison this execution makes for a term
 *   return: its resolved comparison's resolution; a term without one is the load's omission: every load plans its
 *	     terms, a predicate stream's included
 */
/*
 * [리뷰] eval_resolved_compare — COMP_EVAL_TERM(비교 술어 한 항)에 대해 이번 실행의 DOMAIN_COMPARE 를 돌려주는 얇은 래퍼 —
 * eval_compare_term·eval_value_rel_cmp 가 쓴다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: et_comp->domain_compare 가 NULL(=로드가 계획을 붙이지 않은 항)이면 eval_Compare_values 를, 아니면
 * eval_resolved_comparison 의 결과를 돌려준다.
 * 바뀐 것: 신설 +10줄.
 */
static inline const DOMAIN_COMPARE *
eval_resolved_compare (const COMP_EVAL_TERM * et_comp, const val_descr * vd)
{
  const DOMAIN_COMPARE_PLAN *comparison = et_comp->domain_compare;
  if (comparison == NULL)
    {
      return &eval_Compare_values;
    }
  return eval_resolved_comparison (comparison, vd);
}

/* A computed collection's elements against the item's row of the type pair comparison table; an item whose key has no
 * row (domain_compare_key_row) compares each element by the two values' keys. */
/*
 * [리뷰] eval_element_row — ALL/SOME 의 오른쪽이 계산된 컬렉션일 때 원소를 '아이템 타입의 행(타입쌍 비교표 row)' 으로 비교할지를 EVAL_ELEMENTS 에
 * 적는다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: elements->row 에 row 를 쓰고, row<0(그 타입의 행이 없음)이면 each 를 eval_Compare_elements(키 쌍 비교)로 되돌린다.
 * 바뀐 것: 신설 +9줄.
 */
static inline void
eval_element_row (int row, EVAL_ELEMENTS * elements)
{
  elements->row = row;
  if (row < 0)
    {
      elements->each = &eval_Compare_elements;
    }
}

/*
 * eval_resolved_elements () - what an ALL/SOME term compares its item with in this execution
 *
 * The load's resolved comparison or table, or the resolved domains: the row reads them and resolves nothing. Where
 * neither holds, the comparisons are tp_value_compare_with_error on the values (comparison method VALUES), and the
 * unresolved-domain check (execution) stops one whose values would resolve a domain.
 */
/*
 * [리뷰] eval_resolved_elements — ALSM_EVAL_TERM 하나에 대해 '이번 실행에서 원소들을 무엇으로 비교하나' 를
 * EVAL_ELEMENTS(all/each/row/constant) 한 덩어리로 채운다 — eval_pred·eval_pred_alsm4·eval_pred_alsm5 가 집합/리스트 평가 직전에
 * 한 번만 부른다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 에서는 이 개념이 없어 eval_some_eval 등이 원소마다 tp_value_compare_with_error
 * 안에서 코어션을 했다.
 * 이 PR: 기본값은 all=each=eval_Compare_values, row=-1, constant=NULL. 계획의 kind 가 DOMAIN_ELEMENTS_PAIR 면 그 비교를(KEYS
 * 면 each 도 같게), ROW 면 행 번호를 쓰고, 그 밖이면 vd 의 resolved.elements[resolved_elements_index] 를 읽어 read
 * 종류(POSITIONS/ROW/PAIR)별로 채운다.
 * 바뀐 것: 신설 +53줄. 원소당 결정을 스캔당 1회 도출로 끌어올린 자리.
 */
static inline void
eval_resolved_elements (const ALSM_EVAL_TERM * et_alsm, const val_descr * vd, EVAL_ELEMENTS * elements)
{
  const DOMAIN_ELEMENT_COMPARE_PLAN *comparison = et_alsm->domain_compare;
  elements->all = elements->each = &eval_Compare_values;
  elements->row = -1;
  elements->constant = NULL;
  if (comparison == NULL)
    {
      return;
    }
  if (comparison->kind == DOMAIN_ELEMENTS_PAIR)
    {
      elements->all = eval_resolved_comparison (&comparison->pair, vd);
      if (elements->all->method == DOMAIN_COMPARE_KEYS)
	{
	  /* the key pair table (a stream's item) holds for any value the right side has */
	  elements->each = elements->all;
	}
      return;
    }
  if (comparison->kind == DOMAIN_ELEMENTS_ROW)
    {
      eval_element_row (comparison->row, elements);
      return;
    }
  if (vd == NULL || vd->xasl_state == NULL || vd->xasl_state->resolved_domain.elements == NULL)
    {
      return;
    }
  const RESOLVED_DOMAIN_TABLE & resolved = vd->xasl_state->resolved_domain;
  /* a PX worker's own XASL clone numbers its comparisons as the leader's plan does */
  assert (comparison->resolved_elements_index >= 0 && comparison->resolved_elements_index < resolved.n_elements
	  && resolved.plan != NULL && comparison->resolved_elements_index < resolved.plan->n_element_comparisons);
  assert (resolved.copied_from_leader ? resolved.plan->element_comparisons[comparison->resolved_elements_index]->kind ==
	  comparison->kind : resolved.plan->element_comparisons[comparison->resolved_elements_index] == comparison);
  const DOMAIN_ELEMENTS *resolved_domain = &resolved.elements[comparison->resolved_elements_index];
  switch (resolved_domain->read)
    {
    case DOMAIN_READ_POSITIONS:
      elements->constant = resolved_domain;
      break;
    case DOMAIN_READ_ROW:
      eval_element_row (resolved_domain->row, elements);
      break;
    case DOMAIN_READ_PAIR:
      elements->all = &resolved_domain->compares[0];
      break;
    default:
      /* nothing resolved: a NULL constant compares nothing */
      break;
    }
}

/* The resolution an item's row holds for an element: by its type and, for a string or an ENUM, its collation. */
/*
 * [리뷰] eval_element_compare — 아이템 타입의 행(row)과 원소 값 하나로 타입쌍 비교표에서 비교 한 건을 꺼낸다 — eval_some_eval 의 원소 루프가 쓴다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: domain_compare_row_entry (row, element) 가 NULL 이면 eval_Compare_values 로 떨어진다.
 * 바뀐 것: 신설 +6줄.
 * [지적 A2-02]
 */
static inline const DOMAIN_COMPARE *
eval_element_compare (int row, const DB_VALUE * element)
{
  const DOMAIN_COMPARE *compare = domain_compare_row_entry (row, element);
  return compare != NULL ? compare : &eval_Compare_values;
}

/* The value side i compares: the constant resolve_domains converted once, or the row's value. */
/*
 * [리뷰] eval_compare_side — 비교 한쪽이 '게이트가 한 번 변환해 vd 에 넣어둔 상수' 인지 '행에서 온 값' 인지 골라 돌려주는 최하단 접근자 — 행마다 두 번 불린다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: compare->value[side] >= 0 이면 vd->dbval_ptr + value[side], 아니면 row_value.
 * 바뀐 것: 신설 +5줄.
 */
static inline const DB_VALUE *
eval_compare_side (const DOMAIN_COMPARE * compare, const val_descr * vd, int side, const DB_VALUE * row_value)
{
  return compare->value[side] >= 0 ? vd->dbval_ptr + compare->value[side] : row_value;
}

/*
 * eval_compare_resolved () - a comparison resolved before any row: tp_value_compare_with_error's NULL rule, then the
 *			     comparison method the resolved comparison names, on the row's values and
 *			     resolve_domains' own values of the constant sides
 *   comparison(in): the resolved comparison; a side it names fixed for a scope comes in converted once per scope
 */
/*
 * [리뷰] eval_compare_resolved — 해결된 DOMAIN_COMPARE 하나를 실제 두 값에 적용하는 핵심 — NULL 규칙을 먼저 적용하고 비교 method 로 한 번만 분기해
 * DB_VALUE_COMPARE_RESULT 를 돌려준다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 에서 이 자리는 eval_value_rel_cmp(153) 안의 '상수 측 1회 코어션 +
 * tp_value_compare_with_error' 였다.
 * 이 PR: DIRECT 면 compare->cmp->cmpval 직접 호출, CONVERT 면 상관(correlated) 측을 스코프당 한 번만 qexec_execution_temporary 로
 * 변환한 뒤 domain_compare_converted, OBJECT/KEYS 면 domain_compare_by_type_pair, 그 밖(RANK·COLLATIONS)은
 * domain_compare_values.
 * 바뀐 것: 신설 +51줄. 행당 타입 판정·코어션 분기가 method switch 한 번으로 줄었다.
 * [지적 A2-03]
 */
static DB_VALUE_COMPARE_RESULT
eval_compare_resolved (THREAD_ENTRY * thread_p, const DOMAIN_COMPARE * compare, const DOMAIN_COMPARE_PLAN * comparison,
		       const val_descr * vd, const DB_VALUE * dbval1, const DB_VALUE * dbval2, int total_order,
		       bool * can_compare)
{
  const DB_VALUE *value[2] = { eval_compare_side (compare, vd, 0, dbval1), eval_compare_side (compare, vd, 1, dbval2) };
  if (DB_IS_NULL (value[0]))
    {
      return DB_IS_NULL (value[1]) ? (total_order ? DB_EQ : DB_UNK) : (total_order ? DB_LT : DB_UNK);
    }
  if (DB_IS_NULL (value[1]))
    {
      return total_order ? DB_GT : DB_UNK;
    }
  /* one switch on the comparison method the resolved comparison names */
  switch (compare->method)
    {
    case DOMAIN_COMPARE_DIRECT:
      return compare->cmp->cmpval ((DB_VALUE *) value[0], (DB_VALUE *) value[1], compare->coercion, total_order, NULL,
				   compare->collation);

    case DOMAIN_COMPARE_CONVERT:
      {
	unsigned char converted = 0;
	for (int side = 0; comparison != NULL && side < 2; side++)
	  {
	    /* a correlated side is converted once per scope (its outer row), not at every inner row */
	    const DB_VALUE *temporary = comparison->temporaries[side] != 0 && compare->conv[side] != NULL
	      ? qexec_execution_temporary (thread_p, vd, comparison->temporaries[side], compare->conv[side],
					   compare->target[side],
					   value[side]) : NULL;
	    if (temporary != NULL)
	      {
		value[side] = temporary;
		converted |= (unsigned char) (1 << side);
	      }
	  }
	return domain_compare_converted (compare, value[0], value[1], total_order, can_compare, converted);
      }

    case DOMAIN_COMPARE_OBJECT:
    case DOMAIN_COMPARE_KEYS:
      /* an object side meets OIDs on the server, and a collection's elements are its data: the key pair table's
       * comparison of the two values' keys */
      return domain_compare_by_type_pair (dbval1, dbval2, 1, total_order, can_compare);

    default:
      /* RANK, COLLATIONS */
      return domain_compare_values (compare, value[0], value[1], total_order, can_compare);
    }
}

#if !defined (NDEBUG)
/* One side of a resolved comparison in the debug cross-checks' report: the regu, its domain, and the plan's view of
 * it. */
/*
 * [리뷰] eval_report_resolved_side — 디버그 진단 출력 — 비교 한쪽의 regu 타입·opcode·도메인/콜레이션, 계획 슬롯, 고정 도메인, 해결된 도메인을 stderr
 * 에 한 줄로 찍는다. eval_report_resolved_compare 만 부른다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: qexec_get_node_domain 으로 regu 의 실행 도메인을, item->resolved_index 로 해결표의 도메인을 함께 찍어 '계획이 정한 것 vs 실제' 를 나란히
 * 보여준다.
 * 바뀐 것: 신설 +25줄, NDEBUG 아닐 때만 컴파일.
 */
static void
eval_report_resolved_side (const char *name, const REGU_VARIABLE * regu, const DOMAIN_PLAN_ITEM * item,
			   const val_descr * vd)
{
  const TP_DOMAIN *domain = regu != NULL ? qexec_get_node_domain (vd, regu->domain, regu->plan_item) : NULL;
  const TP_DOMAIN *resolved_domain = NULL;
  if (item != NULL && item->resolved_index >= 0 && vd != NULL && vd->xasl_state != NULL
      && item->resolved_index < vd->xasl_state->resolved_domain.n_resolved)
    {
      resolved_domain = vd->xasl_state->resolved_domain.domains[item->resolved_index].domain;
    }
  const TP_DOMAIN *fixed = item != NULL ? item->fixed.domain : NULL;
  const int opcode = regu != NULL && (regu->type == TYPE_INARITH || regu->type == TYPE_OUTARITH)
    && regu->value.arithptr != NULL ? (int) regu->value.arithptr->opcode : -1;
  fprintf (stderr, "planned comparison   %s regu type=%d opcode=%d flags=0x%x domain=%d/%d/%d item slot=%d ref=%d "
	   "fixed=%d/%d/%d decided=%d/%d/%d\n", name, regu != NULL ? (int) regu->type : -1, opcode,
	   regu != NULL ? regu->flags : 0,
	   domain != NULL ? (int) TP_DOMAIN_TYPE (domain) : -1, domain != NULL ? domain->collation_id : -1,
	   domain != NULL ? (int) domain->collation_flag : -1, item != NULL ? item->resolved_index : -2,
	   item != NULL ? item->ref : -2, fixed != NULL ? (int) TP_DOMAIN_TYPE (fixed) : -1,
	   fixed != NULL ? fixed->collation_id : -1, fixed != NULL ? (int) fixed->collation_flag : -1,
	   resolved_domain != NULL ? (int) TP_DOMAIN_TYPE (resolved_domain) : -1,
	   resolved_domain != NULL ? resolved_domain->collation_id : -1,
	   resolved_domain != NULL ? (int) resolved_domain->collation_flag : -1);
}

/* The debug cross-checks' report of a resolved comparison and its values (optdebug), before they assert. */
/*
 * [리뷰] eval_report_resolved_compare — 계획된 비교가 기대와 어긋났을 때 무엇이
 * 어긋났는지(method·first·source·collation·codeset_side·value 와 양쪽 값의 실제 타입/콜레이션)를 stderr 에 찍는 디버그 보고자 — 세 assert
 * 보조함수와 미해결 도메인(boundary) 경로가 부른다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: 양쪽 값의 타입·collation·codeset 을 문자열로 만들어 찍고, et_comp 가 있으면 계획
 * 측(fixed.method·compare_index·constant/literal 유무)과 양쪽 side 보고까지 이어 찍는다.
 * 바뀐 것: 신설 +33줄, 디버그 전용.
 */
static void
eval_report_resolved_compare (const char *what, const DOMAIN_COMPARE * compare, const DB_VALUE * dbval1,
			      const DB_VALUE * dbval2, const COMP_EVAL_TERM * et_comp, const val_descr * vd)
{
  const DB_VALUE *values[2] = { dbval1, dbval2 };
  char sides[2][96];
  for (int i = 0; i < 2; i++)
    {
      const DB_TYPE type = DB_IS_NULL (values[i]) ? DB_TYPE_NULL : DB_VALUE_DOMAIN_TYPE (values[i]);
      const int collation = TP_IS_CHAR_TYPE (type) ? db_get_string_collation (values[i])
	: type == DB_TYPE_ENUMERATION ? db_get_enum_collation (values[i]) : -1;
      const int codeset = TP_IS_CHAR_TYPE (type) ? db_get_string_codeset (values[i])
	: type == DB_TYPE_ENUMERATION ? db_get_enum_codeset (values[i]) : -1;
      snprintf (sides[i], sizeof (sides[i]), "type=%d collation=%d codeset=%d", (int) type, collation, codeset);
    }
  fprintf (stderr, "planned comparison %s: kernel=%d first=%d source=%d,%d converted_first=%d "
	   "collation=%d codeset_side=%d value=%d,%d failed=%d | lhs %s | rhs %s\n", what, (int) compare->method,
	   (int) compare->first, (int) compare->source[0], (int) compare->source[1],
	   (int) compare->converted_first, compare->collation, compare->codeset_side, compare->value[0],
	   compare->value[1], (int) compare->failed, sides[0], sides[1]);
  if (et_comp != NULL)
    {
      const DOMAIN_COMPARE_PLAN *comparison = et_comp->domain_compare;
      fprintf (stderr, "planned comparison   site fixed.kernel=%d site=%d constant=%d,%d literal=%d,%d\n",
	       comparison != NULL ? (int) comparison->fixed.method : -1,
	       comparison != NULL ? comparison->fixed.compare_index : -2, comparison != NULL
	       && comparison->constant[0] != NULL, comparison != NULL
	       && comparison->constant[1] != NULL, comparison != NULL
	       && comparison->literal[0] != NULL, comparison != NULL && comparison->literal[1] != NULL);
      eval_report_resolved_side ("lhs", et_comp->lhs, comparison != NULL ? comparison->operand[0] : NULL, vd);
      eval_report_resolved_side ("rhs", et_comp->rhs, comparison != NULL ? comparison->operand[1] : NULL, vd);
    }
}

/*
 * eval_assert_resolved_sides () - debug cross-check before the comparison method: a side read from the row has the type
 *				  its converters and cmpval were resolved for (a constant side compares resolve_domains'
 *				  own value)
 */
/*
 * [리뷰] eval_assert_resolved_sides — 비교 실행 직전의 디버그 교차검증 — 행에서 읽은 쪽의 실제 타입이 해결 당시 기록한 source 타입과 같은지 assert 한다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: OBJECT/KEYS 는 값의 키로 비교하므로 면제. 그 외는 (상수라서 value[side]!=-1) 또는 NULL 또는 타입 일치여야 하고, 어긋나면
 * eval_report_resolved_compare 로 찍은 뒤 assert.
 * 바뀐 것: 신설 +19줄, 디버그 전용.
 */
static void
eval_assert_resolved_sides (const DOMAIN_COMPARE * compare, const DB_VALUE * dbval1, const DB_VALUE * dbval2,
			    const COMP_EVAL_TERM * et_comp, const val_descr * vd)
{
  if (compare->method == DOMAIN_COMPARE_OBJECT || compare->method == DOMAIN_COMPARE_KEYS)
    {
      /* the key pair table reads the values' own keys */
      return;
    }
  const bool lhs = compare->value[0] != -1 || DB_IS_NULL (dbval1)
    || DB_VALUE_DOMAIN_TYPE (dbval1) == (DB_TYPE) compare->source[0];
  const bool rhs = compare->value[1] != -1 || DB_IS_NULL (dbval2)
    || DB_VALUE_DOMAIN_TYPE (dbval2) == (DB_TYPE) compare->source[1];
  if (!lhs || !rhs)
    {
      eval_report_resolved_compare ("side type", compare, dbval1, dbval2, et_comp, vd);
    }
  assert (lhs && rhs);
}

/*
 * eval_assert_resolved_compare () - debug cross-check after the comparison method: tp_value_compare_with_error on the
 *				    same values gives the resolved comparison's result, comparability and error
 *   asks_comparable(in): the caller asks whether the values compare (tp_value_compare_with_error's contract); false
 *			  for tp_value_compare's, which asks nothing
 */
/*
 * [리뷰] eval_assert_resolved_compare — 계획된 비교의 결과를 develop 의 경로(tp_value_compare_with_error)로 다시 계산해 같은지 assert
 * — 이 PR 의 전환이 답을 바꾸지 않았음을 디버그 빌드가 행마다 보증하는 장치.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: er_stack_push/pop 으로 대조용 에러를 격리하고 결과·comparable·errid 세 가지를 모두 비교, 다르면 보고 후 assert.
 * 바뀐 것: 신설 +22줄, 디버그 전용. 릴리스에서는 사라진다.
 */
static void
eval_assert_resolved_compare (const DOMAIN_COMPARE * compare, const DB_VALUE * dbval1, const DB_VALUE * dbval2,
			      int total_order, DB_VALUE_COMPARE_RESULT result, bool comparable,
			      const COMP_EVAL_TERM * et_comp, const val_descr * vd, bool asks_comparable)
{
  const int error = comparable ? NO_ERROR : er_errid ();
  bool expected_comparable = true;
  er_stack_push ();
  const DB_VALUE_COMPARE_RESULT expected =
    tp_value_compare_with_error (dbval1, dbval2, 1, total_order, asks_comparable ? &expected_comparable : NULL);
  const int expected_error = expected_comparable ? NO_ERROR : er_errid ();
  er_stack_pop ();
  const bool same = expected == result && expected_comparable == comparable && expected_error == error;
  if (!same)
    {
      eval_report_resolved_compare ("result", compare, dbval1, dbval2, et_comp, vd);
      fprintf (stderr, "planned comparison result: planned=%d comparable=%d error=%d expected=%d comparable=%d "
	       "error=%d\n",
	       (int) result, (int) comparable, error, (int) expected, (int) expected_comparable, expected_error);
    }
  assert (same);
}
#endif

/*
 * eval_compare_values_resolved () - a comparison of two values resolved before any row outside a predicate term: the
 *				    comparison's resolution in this execution, tp_value_compare_with_error's NULL rule
 *				    and the comparison method it names
 *   return: the result; *can_compare false with tp_value_compare_with_error's error where the values do not compare,
 *	     and at the unresolved-domain check (execution) (ER_QPROC_DOMAIN_UNRESOLVED)
 *   comparison(in): the resolved comparison; NULL is the load's omission
 *   vd(in): value descriptor of the execution (the resolved domains and converted constants)
 *   can_compare(out): NULL for tp_value_compare's contract, which asks nothing: values that do not compare answer by
 *		       their rank without an error
 */
/*
 * [리뷰] eval_compare_values_resolved — 술어 항 바깥에서 두 값을 '계획이 정한 대로' 비교해 달라는 외부 진입점(비정적) — px_scan 의 instnum 한계
 * 해결(resolve_instnum_limit) 등이 부른다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: comparison 에서 이번 실행의 해결을 집어, method 가 VALUES 가 아니면 eval_compare_resolved 로, VALUES 인데 두 값의 도메인이 다르면
 * 미해결 도메인 검사(domain_unresolved_error)로 *can_compare=false·DB_UNK, 같으면 tp_value_compare_with_error.
 * 바뀐 것: 신설 +39줄.
 */
DB_VALUE_COMPARE_RESULT
eval_compare_values_resolved (THREAD_ENTRY * thread_p, const DOMAIN_COMPARE_PLAN * comparison, const val_descr * vd,
			      const DB_VALUE * value1, const DB_VALUE * value2, int total_order, bool * can_compare)
{
  if (can_compare != NULL)
    {
      *can_compare = true;
    }
  const DOMAIN_COMPARE *compare = comparison != NULL ? eval_resolved_comparison (comparison, vd) : &eval_Compare_values;
  if (compare->method != DOMAIN_COMPARE_VALUES)
    {
#if !defined (NDEBUG)
      eval_assert_resolved_sides (compare, value1, value2, NULL, vd);
#endif
      const DB_VALUE_COMPARE_RESULT result =
	eval_compare_resolved (thread_p, compare, comparison, vd, value1, value2, total_order, can_compare);
#if !defined (NDEBUG)
      eval_assert_resolved_compare (compare, value1, value2, total_order, result,
				    can_compare != NULL ? *can_compare : true, NULL, vd, can_compare != NULL);
#endif
      return result;
    }
  if (domain_value_domains_differ (value1, value2))
    {
      /* the unresolved-domain check (execution): no plan holds this comparison, and the values differ in type or
       * collation, which only a plan resolves */
#if !defined (NDEBUG)
      eval_report_resolved_compare ("boundary", compare, value1, value2, NULL, vd);
#endif
      (void) domain_unresolved_error ("", -1, DB_VALUE_DOMAIN_TYPE (value2));
      if (can_compare != NULL)
	{
	  *can_compare = false;
	}
      return DB_UNK;
    }
  /* NULL answers first */
  return tp_value_compare_with_error (value1, value2, 1, total_order, can_compare);
}

/* a comparison's result as its relational operator reads it (eval_value_rel_cmp and the operator functions) */
STATIC_INLINE DB_LOGICAL eval_rel_result (REL_OP rel_operator, int result, const DB_VALUE * dbval1,
					  const DB_VALUE * dbval2) __attribute__ ((ALWAYS_INLINE));

/*
 * eval_value_rel_cmp () - Compare two db_values according to the given
 *                       relational operator
 *   return: DB_LOGICAL (V_TRUE, V_FALSE, V_UNKNOWN or V_ERROR)
 *   dbval1(in): first db_value
 *   dbval2(in): second db_value
 *   rel_operator(in): Relational operator
 *   et_comp(in): compound evaluation term; its resolved comparison's correlated sides are converted once per scope
 *   vd(in): value descriptor of the term's execution (the resolved domains and converted constants)
 *   compare(in): the resolution of an element comparison, or the term's resolution its caller read
 *		  (eval_compare_term); NULL: the term's
 *   unconverted2(in): the right side as the term holds it where dbval2 is resolve_domains' converted copy of it,
 *		       which the debug cross-checks compare (an optdebug build reads it); NULL: dbval2
 */
/*
 * [리뷰] eval_value_rel_cmp — 비교 한 건을 REL_OP 로 읽어 DB_LOGICAL 을 돌려주는 범용 경로 — 집합/리스트 평가와 DIRECT 가 아닌 모든 비교가 여기로
 * 모인다.
 * develop: develop(153)은 (thread_p, dbval1, dbval2, rel_operator, et_comp) 5인자. 기본 분기에서 rhs 가
 * REGU_VARIABLE_FETCH_ALL_CONST 이면 **행마다** vtype1/vtype2 를 보고 tp_value_coerce 로 dbval2 를 그 자리에서 덮어썼고(문자↔수치,
 * 문자↔날짜, 일반성 비교), 그 뒤 tp_value_compare_with_error 를 불렀다. 결과 해석 switch 는 함수 꼬리에 인라인돼 있었다.
 * 이 PR: 인자가 8개(vd·compare·unconverted2 추가). 상수 코어션 블록(#if 0 보관분 포함 약 100줄)이 통째로 사라지고, 해결된 비교가 있으면
 * eval_compare_resolved 로, 없고 두 값의 도메인이 다르면 미해결 도메인으로 V_ERROR, 같으면 tp_value_compare_with_error. 꼬리 switch 는
 * eval_rel_result 로 분리했다.
 * 바뀐 것: 시그니처 +3인자, 행당 코어션 삭제(약 -100줄), 분기 재구성, 결과 해석 분리. 이 팩에서 성격이 가장 큰 변경이다.
 * [지적 A2-05]
 * [지적 A2-01]
 */
static DB_LOGICAL
eval_value_rel_cmp (THREAD_ENTRY * thread_p, DB_VALUE * dbval1, DB_VALUE * dbval2, REL_OP rel_operator,
		    const COMP_EVAL_TERM * et_comp, const val_descr * vd, const DOMAIN_COMPARE * compare,
		    const DB_VALUE * unconverted2)
{
  int result;
  bool comparable = true;

  /*
   * we get here for either an ordinal comparison or a set comparison.
   * Set comparisons are R_SUBSET, R_SUBSETEQ, R_SUPERSET, R_SUPSERSETEQ.
   * All others are ordinal comparisons.
   */

  /* tp_value_compare_with_error () does coercion */
  switch (rel_operator)
    {
    case R_SUBSET:
    case R_SUBSETEQ:
    case R_SUPERSET:
    case R_SUPERSETEQ:
      /* do set comparison */
      result = tp_set_compare (dbval1, dbval2, 1, 0);
      break;

    default:
      {
	/* R_EQ_TORDER compares in total order; the others compare ordinally, and NULL's still yield UNKNOWN */
	const int total_order = rel_operator == R_EQ_TORDER;
	/* the term's resolved comparison, whose correlated sides its scope converts once; an element's resolution has
	 * none */
	const DOMAIN_COMPARE_PLAN *comparison = et_comp != NULL ? et_comp->domain_compare : NULL;
	if (compare == NULL)
	  {
	    compare = et_comp != NULL ? eval_resolved_compare (et_comp, vd) : &eval_Compare_values;
	  }
	if (compare->method != DOMAIN_COMPARE_VALUES)
	  {
	    /* the comparison the load or resolve_domains resolved; a constant is converted once,
	     * into a value of its own, and the shared value stays as it is */
#if !defined (NDEBUG)
	    eval_assert_resolved_sides (compare, dbval1, dbval2, et_comp, vd);
#endif
	    result =
	      eval_compare_resolved (thread_p, compare, comparison, vd, dbval1, dbval2, total_order, &comparable);
#if !defined (NDEBUG)
	    eval_assert_resolved_compare (compare, dbval1, unconverted2 != NULL ? unconverted2 : dbval2, total_order,
					  (DB_VALUE_COMPARE_RESULT) result, comparable, et_comp, vd, true);
#endif
	  }
	else if (domain_value_domains_differ (dbval1, dbval2))
	  {
	    /* the unresolved-domain check (execution): no plan holds this comparison, and the values differ in type or
	     * collation, which only a plan resolves */
#if !defined (NDEBUG)
	    eval_report_resolved_compare ("boundary", compare, dbval1, dbval2, et_comp, vd);
#endif
	    (void) domain_unresolved_error ("", -1, DB_VALUE_DOMAIN_TYPE (dbval2));
	    return V_ERROR;
	  }
	else
	  {
	    /* NULL answers first */
	    result = tp_value_compare_with_error (dbval1, dbval2, 1, total_order, &comparable);
	  }
      }
      break;
    }

  if (!comparable)
    {
      return V_ERROR;
    }

  return eval_rel_result (rel_operator, result, dbval1, dbval2);
}

/*
 * eval_rel_result () - a comparison's result as its relational operator reads it: an unknown result is V_UNKNOWN,
 *			except for R_NULLSAFE_EQ, whose own rule reads the two values
 *   return: DB_LOGICAL (V_TRUE, V_FALSE, V_UNKNOWN or V_ERROR)
 *   result(in): DB_VALUE_COMPARE_RESULT of the comparison
 *   dbval1(in), dbval2(in): the values the comparison was given
 */
/*
 * [리뷰] eval_rel_result — 비교 결과(DB_VALUE_COMPARE_RESULT)를 REL_OP 로 읽어 V_TRUE/V_FALSE/V_UNKNOWN/V_ERROR 로 바꾸는 순수
 * 함수 — eval_value_rel_cmp 와 DIRECT 연산자 함수 8개가 공유한다.
 * develop: develop 에는 독립 함수가 없었고, 똑같은 switch(UNK 처리와 R_NULLSAFE_EQ 의 두 값 검사 포함)가 eval_value_rel_cmp(153) 꼬리에
 * 인라인돼 있었다.
 * 이 PR: STATIC_INLINE + ALWAYS_INLINE 로 분리됐다. 본문 로직은 develop 과 줄 단위로 같다.
 * 바뀐 것: 추출(+60줄, develop 쪽 같은 분량 삭제). 동작 변화 없음 — DIRECT 경로가 같은 해석을 재사용하기 위한 분리다.
 */
STATIC_INLINE DB_LOGICAL
eval_rel_result (REL_OP rel_operator, int result, const DB_VALUE * dbval1, const DB_VALUE * dbval2)
{
  if (result == DB_UNK && rel_operator != R_NULLSAFE_EQ)
    {
      return V_UNKNOWN;
    }

  switch (rel_operator)
    {
    case R_EQ:
      return ((result == DB_EQ) ? V_TRUE : V_FALSE);
    case R_EQ_TORDER:
      return ((result == DB_EQ) ? V_TRUE : V_FALSE);
    case R_LT:
      return ((result == DB_LT) ? V_TRUE : V_FALSE);
    case R_LE:
      return (((result == DB_LT) || (result == DB_EQ)) ? V_TRUE : V_FALSE);
    case R_GT:
      return ((result == DB_GT) ? V_TRUE : V_FALSE);
    case R_GE:
      return (((result == DB_GT) || (result == DB_EQ)) ? V_TRUE : V_FALSE);
    case R_NE:
      return ((result != DB_EQ) ? V_TRUE : V_FALSE);
    case R_SUBSET:
      return ((result == DB_SUBSET) ? V_TRUE : V_FALSE);
    case R_SUBSETEQ:
      return (((result == DB_SUBSET) || (result == DB_EQ)) ? V_TRUE : V_FALSE);
    case R_SUPERSET:
      return ((result == DB_SUPERSET) ? V_TRUE : V_FALSE);
    case R_SUPERSETEQ:
      return (((result == DB_SUPERSET) || (result == DB_EQ)) ? V_TRUE : V_FALSE);
    case R_NULLSAFE_EQ:
      if (result == DB_EQ)
	{
	  return V_TRUE;
	}
      else
	{
	  if (DB_IS_NULL (dbval1))
	    {
	      if (DB_IS_NULL (dbval2))
		{
		  return V_TRUE;
		}
	      else
		{
		  return V_FALSE;
		}
	    }
	  else
	    {
	      return V_FALSE;
	    }
	}
      break;
    default:
      return V_ERROR;
    }
}

/*
 * Comparison term leaves
 *
 * A comparison term's resolved comparison names the functions its row runs for its comparison method, one for each
 * relational operator, when the load or resolve_domains resolves it: a resolution of comparison method DIRECT compares
 * its sides by cmpval and reads the result by the operator its function was made for, with no comparison method or
 * operator switch at the row. The row takes the function of its term's operator at the row: qexec_eval_instnum_pred
 * evaluates inst_num () <= n as < first, so the operator is not always the one the load saw. Any other resolution's row
 * is eval_value_rel_cmp's.
 */

/*
 * eval_operator_function_direct () - a comparison term's row over a resolution of comparison method DIRECT, for one
 *			 relational operator: the sides the resolved comparison names, eval_compare_resolved's NULL
 *			 rule, cmpval under the resolved collation, and the operator's reading of
 *			 the result (eval_rel_result)
 *   return: DB_LOGICAL (V_TRUE, V_FALSE or V_UNKNOWN)
 *   dbval1(in), dbval2(in): the values the term fetched
 */
/* *INDENT-OFF* */
template <REL_OP rel_operator>
/*
 * [리뷰] eval_operator_function_direct — DOMAIN_COMPARE_DIRECT 로 해결된 비교항의 행 경로 — REL_OP 를 템플릿 인자로 받아 method 분기도
 * 연산자 분기도 없이 cmpval 한 번 + 결과 해석만 한다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: eval_compare_side 로 양쪽 값을 고르고 NULL 규칙(total_order 면 NULL 을 최소로)을 적용한 뒤 compare->cmp->cmpval 을 해결된
 * collation·coercion 으로 부르고, eval_rel_result 로 읽는다.
 * 바뀐 것: 신설 +23줄(템플릿 1개 → 8개 인스턴스). 행당 비용을 간접호출 1회로 줄이는 것이 목적.
 */
static DB_LOGICAL
eval_operator_function_direct (const DOMAIN_COMPARE * compare, const val_descr * vd, DB_VALUE * dbval1,
			       DB_VALUE * dbval2)
{
  const int total_order = rel_operator == R_EQ_TORDER;
  const DB_VALUE *value1 = eval_compare_side (compare, vd, 0, dbval1);
  const DB_VALUE *value2 = eval_compare_side (compare, vd, 1, dbval2);
  int result;
  if (DB_IS_NULL (value1))
    {
      result = DB_IS_NULL (value2) ? (total_order ? DB_EQ : DB_UNK) : (total_order ? DB_LT : DB_UNK);
    }
  else if (DB_IS_NULL (value2))
    {
      result = total_order ? DB_GT : DB_UNK;
    }
  else
    {
      result = compare->cmp->cmpval ((DB_VALUE *) value1, (DB_VALUE *) value2, compare->coercion, total_order, NULL,
				     compare->collation);
    }
  return eval_rel_result (rel_operator, result, dbval1, dbval2);
}

/* Comparison method DIRECT's operator functions by REL_OP (R_NULLSAFE_EQ is the last): the operators eval_value_rel_cmp
 * reads ordinally; none for a set comparison and the operators no comparison term evaluates here. */
struct EVAL_DIRECT_OPERATOR_FUNCTIONS
{
  DOMAIN_COMPARE_OPERATOR_FUNCTION by_operator[R_NULLSAFE_EQ + 1];
};

/*
 * [리뷰] eval_direct_operator_functions — REL_OP 로 색인되는 DIRECT 연산자 함수표를 컴파일 타임에 만든다 — 정적 상수
 * eval_Direct_operator_functions 의 초기값.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: R_EQ/NE/GT/GE/LT/LE/EQ_TORDER/NULLSAFE_EQ 8칸만 채우고 나머지(집합 비교 등)는 값초기화로 NULL 이라, 호출자가 NULL 을 보면 일반 경로로
 * 떨어진다.
 * 바뀐 것: 신설 +14줄. 배열 크기는 R_NULLSAFE_EQ+1 이고 xasl_predicate.hpp 의 REL_OP 에서 R_NULLSAFE_EQ 가 마지막이라 모든 연산자 값이 범위
 * 안이다(확인함).
 */
static constexpr EVAL_DIRECT_OPERATOR_FUNCTIONS
eval_direct_operator_functions (void)
{
  EVAL_DIRECT_OPERATOR_FUNCTIONS operator_functions = EVAL_DIRECT_OPERATOR_FUNCTIONS ();
  operator_functions.by_operator[R_EQ] = eval_operator_function_direct<R_EQ>;
  operator_functions.by_operator[R_NE] = eval_operator_function_direct<R_NE>;
  operator_functions.by_operator[R_GT] = eval_operator_function_direct<R_GT>;
  operator_functions.by_operator[R_GE] = eval_operator_function_direct<R_GE>;
  operator_functions.by_operator[R_LT] = eval_operator_function_direct<R_LT>;
  operator_functions.by_operator[R_LE] = eval_operator_function_direct<R_LE>;
  operator_functions.by_operator[R_EQ_TORDER] = eval_operator_function_direct<R_EQ_TORDER>;
  operator_functions.by_operator[R_NULLSAFE_EQ] = eval_operator_function_direct<R_NULLSAFE_EQ>;
  return operator_functions;
}

static constexpr EVAL_DIRECT_OPERATOR_FUNCTIONS eval_Direct_operator_functions = eval_direct_operator_functions ();
/* *INDENT-ON* */

/* domain_compare_set_operator_functions () - declared with DOMAIN_COMPARE (domain_rules.h); the load and
 * resolve_domains call it where they resolve a term's comparison, and the operator functions it names are these */
/*
 * [리뷰] domain_compare_set_operator_functions — query_evaluator.c 바깥(로드: domain_plan.c, 실행 전 게이트:
 * domain_resolve.c)이 해결한 DOMAIN_COMPARE 에 행 경로 함수표를 꽂아 주는 유일한 통로 — 함수 포인터는 XASL 스트림으로 나를 수 없으므로 해결 시점마다 여기서 다시
 * 세운다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: method 가 DOMAIN_COMPARE_DIRECT 면 eval_Direct_operator_functions.by_operator 를, 아니면 NULL 을 넣는다. 호출처는
 * domain_plan.c:3555·4320, domain_resolve.c:1300·1385 네 곳.
 * 바뀐 것: 신설 +6줄. 선언은 domain_rules.h:210.
 */
void
domain_compare_set_operator_functions (DOMAIN_COMPARE * compare)
{
  compare->operator_functions =
    compare->method == DOMAIN_COMPARE_DIRECT ? eval_Direct_operator_functions.by_operator : NULL;
}

#if !defined (NDEBUG)
/*
 * eval_assert_operator_function () - debug cross-check of a term's operator function: eval_value_rel_cmp's evaluation
 *			 of the term, the path the function takes the place of, gives the function's answer
 */
/*
 * [리뷰] eval_assert_operator_function — 디버그 교차검증 — DIRECT 연산자 함수가 낸 답을 범용 경로 eval_value_rel_cmp 로 다시 구해 같은지
 * assert 한다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: 다르면 eval_report_resolved_compare 로 양쪽을 찍고 rel_op·두 결과를 stderr 에 남긴 뒤 assert.
 * 바뀐 것: 신설 +13줄, 디버그 전용(eval_compare_term 안에서 #if !defined (NDEBUG) 로 감싸 호출).
 */
static void
eval_assert_operator_function (THREAD_ENTRY * thread_p, const COMP_EVAL_TERM * et_comp, const val_descr * vd,
			       const DOMAIN_COMPARE * compare, DB_VALUE * dbval1, DB_VALUE * dbval2, DB_LOGICAL leaf)
{
  const DB_LOGICAL result = eval_value_rel_cmp (thread_p, dbval1, dbval2, et_comp->rel_op, et_comp, vd, NULL, NULL);
  if (result != leaf)
    {
      eval_report_resolved_compare ("leaf", compare, dbval1, dbval2, et_comp, vd);
      fprintf (stderr, "planned comparison leaf: rel_op=%d leaf=%d eval_value_rel_cmp=%d\n", (int) et_comp->rel_op,
	       (int) leaf, (int) result);
    }
  assert (result == leaf);
}
#endif /* !NDEBUG */

STATIC_INLINE DB_LOGICAL eval_compare_term (THREAD_ENTRY * thread_p, const COMP_EVAL_TERM * et_comp, val_descr * vd,
					    DB_VALUE * dbval1, DB_VALUE * dbval2) __attribute__ ((ALWAYS_INLINE));

/*
 * eval_compare_term () - a comparison term's row on the values it fetched: the operator function its resolved
 *			  comparison in this execution names for the term's operator, or eval_value_rel_cmp on that
 *			  resolution
 *   return: DB_LOGICAL (V_TRUE, V_FALSE, V_UNKNOWN or V_ERROR)
 */
/*
 * [리뷰] eval_compare_term — 비교 술어 한 항의 행 경로 진입점 — eval_pred 의 T_COMP_EVAL_TERM 분기와 eval_pred_comp0 이 양쪽 값을
 * fetch 한 뒤 부른다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 은 같은 자리에서 eval_value_rel_cmp(…, et_comp) 를 직접 불렀다.
 * 이 PR: 이번 실행의 해결(eval_resolved_compare)을 집고, 그 연산자의 DIRECT 함수가 있으면 그것을, 없으면 eval_value_rel_cmp 를 부른다. 디버그 빌드는
 * 두 결과를 대조한다.
 * 바뀐 것: 신설 +17줄, ALWAYS_INLINE. 주석에 적힌 대로 qexec_eval_instnum_pred 가 <= 를 < 로 바꿔 평가하므로 '행에서 보는 연산자' 로 표를 찾는다.
 */
STATIC_INLINE DB_LOGICAL
eval_compare_term (THREAD_ENTRY * thread_p, const COMP_EVAL_TERM * et_comp, val_descr * vd, DB_VALUE * dbval1,
		   DB_VALUE * dbval2)
{
  const DOMAIN_COMPARE *compare = eval_resolved_compare (et_comp, vd);
  const DOMAIN_COMPARE_OPERATOR_FUNCTION leaf =
    compare->operator_functions != NULL ? compare->operator_functions[et_comp->rel_op] : NULL;
  if (leaf == NULL)
    {
      return eval_value_rel_cmp (thread_p, dbval1, dbval2, et_comp->rel_op, et_comp, vd, compare, NULL);
    }
  const DB_LOGICAL result = leaf (compare, vd, dbval1, dbval2);
#if !defined (NDEBUG)
  eval_assert_operator_function (thread_p, et_comp, vd, compare, dbval1, dbval2, result);
#endif /* !NDEBUG */
  return result;
}

/*
 * eval_some_eval () -
 *   return: DB_LOGICAL (V_TRUE, V_FALSE, V_UNKNOWN, V_ERROR)
 *   item(in): db_value item
 *   set(in): collection of elements
 *   rel_operator(in): relational comparison operator
 *   elements(in): the element comparisons resolved for this execution
 *   vd(in): value descriptor of the term's execution
 */

/*
 * [리뷰] eval_some_eval — SOME/ANY 집합 비교 — 아이템과 집합 원소를 차례로 비교해 하나라도 참이면 V_TRUE, 끝까지 아니면 V_FALSE/V_UNKNOWN.
 * develop: develop(354)은 (thread_p, item, set, rel_operator) 4인자. 루프 조건마다 set_size(set) 를 다시 부르고, 원소마다
 * set_get_element 로 꺼내 eval_value_rel_cmp(…, NULL) 로 비교했다 — 비교 방식 결정이 원소마다 tp_value_compare_with_error 안에서
 * 일어났다.
 * 이 PR: elements·vd 2인자가 추가됐다. set_size 를 루프 밖에서 한 번만 읽고, 게이트가 상수 집합을 해결해 뒀으면(elements->constant) 변환된 값
 * value[i] 와 번호로 꺼낸 비교를 쓰고 집합에서 꺼내지 않는다(디버그에서만 원본을 꺼내 대조용 unconverted 로 넘긴다). 아니면 NULL/row/each 중에서 비교를 고른다.
 * 바뀐 것: 시그니처 +2, 상수 경로 분기 추가, set_size 호이스팅(+28줄).
 */
static DB_LOGICAL
eval_some_eval (THREAD_ENTRY * thread_p, DB_VALUE * item, DB_SET * set, REL_OP rel_operator,
		const EVAL_ELEMENTS * elements, const val_descr * vd)
{
  int i;
  DB_LOGICAL res, t_res;
  DB_VALUE elem_val;

  PRIM_SET_NULL (&elem_val);

  res = V_FALSE;

  const int size = set_size (set);
  /* a constant's elements: resolve_domains resolved each one and holds its own value of it, by position */
  assert (elements->constant == NULL || elements->constant->n == size);
  for (i = 0; i < size; i++)
    {
      DB_VALUE *element = &elem_val;
      const DOMAIN_COMPARE *compare;
      const DB_VALUE *unconverted = NULL;
      if (elements->constant != NULL)
	{
	  element = &elements->constant->value[i];
	  compare = &elements->constant->compares[elements->constant->element_compare[i]];
#if !defined (NDEBUG)
	  /* the debug cross-checks compare the element as the set holds it */
	  if (set_get_element (set, i, &elem_val) != NO_ERROR)
	    {
	      return V_ERROR;
	    }
	  unconverted = &elem_val;
#endif
	}
      else
	{
	  if (set_get_element (set, i, &elem_val) != NO_ERROR)
	    {
	      return V_ERROR;
	    }
	  compare = DB_IS_NULL (&elem_val) ? &eval_Compare_values
	    : elements->row >= 0 ? eval_element_compare (elements->row, &elem_val) : elements->each;
	}

      t_res = eval_value_rel_cmp (thread_p, item, element, rel_operator, NULL, vd, compare, unconverted);
      pr_clear_value (&elem_val);
      if (t_res == V_TRUE)
	{
	  return V_TRUE;
	}
      else if (t_res == V_ERROR)
	{
	  return V_ERROR;
	}
      else if (t_res == V_UNKNOWN)
	{
	  res = V_UNKNOWN;	/* never returns here. we should proceed */
	}
    }

  return res;
}

/*
 * eval_all_eval () -
 *   return: DB_LOGICAL (V_TRUE, V_FALSE, V_UNKNOWN, V_ERROR)
 *   item(in): db_value item
 *   set(in): collection of elements
 *   rel_operator(in): relational comparison operator
 *   elements(in): the element comparisons resolved for this execution
 *   vd(in): value descriptor of the term's execution
 *
 * Note: This routine tries to determine whether a specific relation
 *              as determined by the relational operator rel_operator holds between
 *              the given bound item value and all the members of the
 *              given set of elements. The set can be a basic set, multi_set
 *              or sequence. It returns V_TRUE, V_FALSE, V_UNKNOWN using the
 *              following reasoning:
 *
 *              V_TRUE:     - if all the values in the set are determined
 *                            to hold the relationship, or
 *                          - the set is empty
 *              V_FALSE:    - if there exists a value in the set which is
 *                            determined not hold the relationship.
 *              V_UNKNOWN:  - set is homogeneous and set element type is not
 *                            comparable with the item type
 *                          - set has no value determined to fail to hold the
 *                            rel. and at least one value which can not be
 *                            determined to hold the relationship.
 *              V_ERROR:    - an error occurred.
 *
 */
/*
 * [리뷰] eval_all_eval — ALL 집합 비교 — 연산자를 뒤집어 eval_some_eval 을 부르고 결과를 부정한다.
 * develop: develop(418)은 4인자였고, 같은 연산자 뒤집기 switch 뒤 eval_some_eval(…, rel_operator) 를 불렀다.
 * 이 PR: elements·vd 를 받아 그대로 eval_some_eval 에 넘긴다.
 * 바뀐 것: 시그니처 +2인자, 전달만. 뒤집기 로직은 develop 과 동일.
 */
static DB_LOGICAL
eval_all_eval (THREAD_ENTRY * thread_p, DB_VALUE * item, DB_SET * set, REL_OP rel_operator,
	       const EVAL_ELEMENTS * elements, const val_descr * vd)
{
  DB_LOGICAL some_res;

  /*
   * use the some quantifier first on a negated relational operator
   * then find the result boolean value for the all quantifier
   */
  switch (rel_operator)
    {
    case R_LT:
      rel_operator = R_GE;
      break;

    case R_LE:
      rel_operator = R_GT;
      break;

    case R_GT:
      rel_operator = R_LE;
      break;

    case R_GE:
      rel_operator = R_LT;
      break;

    case R_EQ:
    case R_EQ_TORDER:
      rel_operator = R_NE;
      break;

    case R_NE:
      rel_operator = R_EQ;
      break;

    default:
      return V_ERROR;
    }

  some_res = eval_some_eval (thread_p, item, set, rel_operator, elements, vd);
  /* negate the some result */
  return eval_negative (some_res);
}

/*
 * eval_item_card_set () -
 *   return: int (cardinality)
 *           >= 0 : normal cardinality
 *           ER_FAILED : ERROR
 *           UNKNOWN_CARD : unknown cardinality value
 *   item(in): db_value item
 *   set(in): collection of elements
 *   rel_operator(in): relational comparison operator
 *
 * Note: This routine returns the number of set elements (cardinality)
 *              which are determined to hold the given relationship with the
 *              specified item value. If the relationship is the equality
 *              relationship, the returned value means the cardinality of the
 *              given element in the set and must always be less than equal
 *              to 1 for the case of basic sets.
 */
/*
 * [리뷰] eval_item_card_set — 집합 안에서 아이템과 주어진 관계를 만족하는 원소 개수(카디널리티)를 센다 — 다중집합 부분집합 판정(eval_sub_*)이 쓴다. NULL 원소를
 * 만나면 UNKNOWN_CARD.
 * develop: develop(480)은 eval_value_rel_cmp (thread_p, item, &elem_val, rel_operator, NULL) 로 5인자 호출했다.
 * 이 PR: 호출이 (…, rel_operator, NULL, NULL, &eval_Compare_elements, NULL) 로 바뀌어 원소 비교를 '두 값의 키 쌍표' 로 못박는다. 함수
 * 자신의 시그니처와 루프는 그대로.
 * 바뀐 것: 호출 인자만 변경(1줄).
 */
static int
eval_item_card_set (THREAD_ENTRY * thread_p, DB_VALUE * item, DB_SET * set, REL_OP rel_operator)
{
  int num, i;
  DB_LOGICAL res;
  DB_VALUE elem_val;

  PRIM_SET_NULL (&elem_val);

  num = 0;

  for (i = 0; i < set_size (set); i++)
    {
      if (set_get_element (set, i, &elem_val) != NO_ERROR)
	{
	  return ER_FAILED;
	}
      if (db_value_is_null (&elem_val))
	{
	  pr_clear_value (&elem_val);
	  return UNKNOWN_CARD;
	}

      res = eval_value_rel_cmp (thread_p, item, &elem_val, rel_operator, NULL, NULL, &eval_Compare_elements, NULL);
      pr_clear_value (&elem_val);

      if (res == V_ERROR)
	{
	  return ER_FAILED;
	}

      if (res == V_TRUE)
	{
	  num++;
	}
    }

  return num;
}

/*
 * List File Related Evaluation
 */

/*
 * eval_some_list_eval () -
 *   return: DB_LOGICAL (V_TRUE, V_FALSE, V_UNKNOWN, V_ERROR)
 *   item(in): db_value item
 *   list_id(in): list file identifier
 *   rel_operator(in): relational comparison operator
 *   compare(in): the comparison of the item with the list's column resolved for this execution
 *   vd(in): value descriptor of the term's execution
 *
 * Note: This routine tries to determine whether a specific relation
 *              as determined by the relational operator rel_operator holds between
 *              the given bound item value and at least one member of the
 *              given list of elements. It returns V_TRUE, V_FALSE,
 *              V_UNKNOWN, V_ERROR using the following reasoning:
 *
 *              V_TRUE:     - there exists a value in the list that is
 *                            determined to hold the relationship.
 *              V_FALSE:    - all the values in the list are determined not
 *                            to hold the relationship, or
 *                          - the list is empty
 *              V_UNKNOWN:  - list has no value determined to hold the rel.
 *                            and at least one value which can not be
 *                            determined to fail to hold the relationship.
 *              V_ERROR:    - an error occurred.
 *
 *  Note: The IN relationship can be stated as item has the equality rel. with
 *        one of the list elements.
 */
/*
 * [리뷰] eval_some_list_eval — 오른쪽이 리스트파일인 SOME/ANY 비교 — 리스트를 스캔하며 아이템과 비교해 하나라도 참이면 즉시 V_TRUE.
 * develop: develop(550)은 4인자였고 비교가 eval_value_rel_cmp(…, NULL) 였다.
 * 이 PR: compare(호출자가 eval_resolved_elements 로 구한 elements.all)와 vd 를 받아 그대로 비교에 넘긴다. 스캔 열기/닫기·NULL·종료 코드 처리는
 * develop 과 동일.
 * 바뀐 것: 시그니처 +2인자, 호출 인자 전달(+2줄).
 */
static DB_LOGICAL
eval_some_list_eval (THREAD_ENTRY * thread_p, DB_VALUE * item, QFILE_LIST_ID * list_id, REL_OP rel_operator,
		     const DOMAIN_COMPARE * compare, const val_descr * vd)
{
  DB_LOGICAL res, t_res;
  QFILE_LIST_SCAN_ID s_id;
  QFILE_TUPLE_RECORD tplrec = QFILE_TUPLE_RECORD_INITIALIZER;
  DB_VALUE list_val;
  SCAN_CODE qp_scan;
  const PR_TYPE *pr_type;
  bool is_null;

  /* assert */
  if (list_id->type_list.domp == NULL)
    {
      return V_ERROR;
    }

  PRIM_SET_NULL (&list_val);

  if (list_id->tuple_cnt == 0)
    {
      return V_FALSE;		/* empty set */
    }

  if (qfile_open_list_scan (list_id, &s_id) != NO_ERROR)
    {
      return V_ERROR;
    }

  pr_type = list_id->type_list.domp[0]->type;
  if (pr_type == NULL)
    {
      qfile_close_scan (thread_p, &s_id);
      return V_ERROR;
    }

  res = V_FALSE;
  while ((qp_scan = qfile_scan_list_next (thread_p, &s_id, &tplrec, PEEK)) == S_SUCCESS)
    {
      if (qfile_slot_read_column_value (&tplrec, 0, list_id->type_list.domp[0], &list_val, true, &is_null) != NO_ERROR)
	{
	  qfile_close_scan (thread_p, &s_id);
	  return V_ERROR;
	}
      if (is_null)
	{
	  res = V_UNKNOWN;
	}
      else
	{

	  t_res = eval_value_rel_cmp (thread_p, item, &list_val, rel_operator, NULL, vd, compare, NULL);
	  if (t_res == V_TRUE || t_res == V_ERROR)
	    {
	      pr_clear_value (&list_val);
	      qfile_close_scan (thread_p, &s_id);
	      return t_res;
	    }
	  else if (t_res == V_UNKNOWN)
	    {
	      res = V_UNKNOWN;
	    }
	  pr_clear_value (&list_val);
	}
    }

  qfile_close_scan (thread_p, &s_id);

  return (qp_scan == S_END) ? res : V_ERROR;
}

/*
 * eval_all_list_eval () -
 *   return: DB_LOGICAL (V_TRUE, V_FALSE, V_UNKNOWN, V_ERROR)
 *   item(in): db_value
 *   list_id(in): list file identifier
 *   rel_operator(in): relational comparison operator
 *   compare(in): the comparison of the item with the list's column resolved for this execution
 *   vd(in): value descriptor of the term's execution
 *
 * Note: This routine tries to determine whether a specific relation
 *              as determined by the relational operator rel_operator holds between
 *              the given db_value and all the members of the
 *              given list of elements. It returns V_TRUE, V_FALSE, V_UNKNOWN
 *              or V_ERROR using following reasoning:
 *
 *              V_TRUE:     - if all the values in the list are determined
 *                            to hold the relationship, or
 *                          - the list is empty
 *              V_FALSE:    - if there exists a value in the list which is
 *                            determined not hold the relationship.
 *              V_UNKNOWN:  - list has no value determined to fail to hold the
 *                            rel. and at least one value which can not be
 *                            determined to hold the relationship.
 *              V_ERROR:    - an error occurred.
 *
 */
/*
 * [리뷰] eval_all_list_eval — 리스트 상대 ALL 비교 — 연산자를 뒤집어 eval_some_list_eval 을 부르고 결과를 부정한다.
 * develop: develop(645)은 4인자, 같은 뒤집기 switch.
 * 이 PR: compare·vd 를 그대로 전달한다.
 * 바뀐 것: 시그니처 +2인자. 본문 로직 동일.
 */
static DB_LOGICAL
eval_all_list_eval (THREAD_ENTRY * thread_p, DB_VALUE * item, QFILE_LIST_ID * list_id, REL_OP rel_operator,
		    const DOMAIN_COMPARE * compare, const val_descr * vd)
{
  DB_LOGICAL some_res;

  /* first use some quantifier on a negated relational operator */
  switch (rel_operator)
    {
    case R_LT:
      rel_operator = R_GE;
      break;
    case R_LE:
      rel_operator = R_GT;
      break;
    case R_GT:
      rel_operator = R_LE;
      break;
    case R_GE:
      rel_operator = R_LT;
      break;
    case R_EQ:
    case R_EQ_TORDER:
      rel_operator = R_NE;
      break;
    case R_NE:
      rel_operator = R_EQ;
      break;
    default:
      return V_ERROR;
    }

  some_res = eval_some_list_eval (thread_p, item, list_id, rel_operator, compare, vd);
  /* negate the result */
  return eval_negative (some_res);
}

/*
 * eval_item_card_sort_list () -
 *   return: int (cardinality, UNKNOWN_CARD, ER_FAILED for error cases)
 *   item(in): db_value item
 *   list_id(in): list file identifier
 *
 * Note: This routine returns the number of set elements (cardinality)
 *              which are determined to hold the equality relationship with
 *              specified item value. The list file values must have already
 *              been sorted.
 */
/*
 * [리뷰] eval_item_card_sort_list — 정렬된 리스트파일에서 아이템과 같은 값의 개수를 센다(앞쪽 작은 값은 R_LT 로 건너뛰고 같은 구간만 R_EQ 로 센다) — 부분집합
 * 판정용.
 * develop: develop(692)은 두 eval_value_rel_cmp 호출이 모두 5인자(마지막 NULL)였다.
 * 이 PR: 두 호출 모두 (…, NULL, NULL, &eval_Compare_elements, NULL) 로 바뀌어 키 쌍표 비교를 명시한다. 시그니처와 스캔 로직은 그대로.
 * 바뀐 것: 호출 인자만 변경(2줄).
 */
static int
eval_item_card_sort_list (THREAD_ENTRY * thread_p, DB_VALUE * item, QFILE_LIST_ID * list_id)
{
  QFILE_LIST_SCAN_ID s_id;
  QFILE_TUPLE_RECORD tplrec = QFILE_TUPLE_RECORD_INITIALIZER;
  DB_VALUE list_val;
  SCAN_CODE qp_scan;
  const PR_TYPE *pr_type;
  DB_LOGICAL rc;
  int card;
  bool is_null;

  /* assert */
  if (list_id->type_list.domp == NULL)
    {
      return ER_FAILED;
    }

  PRIM_SET_NULL (&list_val);
  card = 0;

  if (qfile_open_list_scan (list_id, &s_id) != NO_ERROR)
    {
      return ER_FAILED;
    }

  pr_type = list_id->type_list.domp[0]->type;
  if (pr_type == NULL)
    {
      qfile_close_scan (thread_p, &s_id);
      return ER_FAILED;
    }

  while ((qp_scan = qfile_scan_list_next (thread_p, &s_id, &tplrec, PEEK)) == S_SUCCESS)
    {
      if (qfile_slot_read_column_value (&tplrec, 0, list_id->type_list.domp[0], &list_val, true, &is_null) != NO_ERROR)
	{
	  qfile_close_scan (thread_p, &s_id);
	  return ER_FAILED;
	}
      if (is_null)
	{
	  qfile_close_scan (thread_p, &s_id);
	  return UNKNOWN_CARD;
	}

      rc = eval_value_rel_cmp (thread_p, item, &list_val, R_LT, NULL, NULL, &eval_Compare_elements, NULL);
      if (rc == V_ERROR)
	{
	  pr_clear_value (&list_val);
	  qfile_close_scan (thread_p, &s_id);
	  return ER_FAILED;
	}
      else if (rc == V_TRUE)
	{
	  pr_clear_value (&list_val);
	  continue;
	}

      rc = eval_value_rel_cmp (thread_p, item, &list_val, R_EQ, NULL, NULL, &eval_Compare_elements, NULL);
      pr_clear_value (&list_val);

      if (rc == V_ERROR)
	{
	  qfile_close_scan (thread_p, &s_id);
	  return ER_FAILED;
	}
      else if (rc == V_TRUE)
	{
	  card++;
	}
      else
	{
	  break;
	}
    }

  qfile_close_scan (thread_p, &s_id);

  return (qp_scan == S_END) ? card : ER_FAILED;
}

/*
 * eval_sub_multi_set_to_sort_list () -
 *   return: DB_LOGICAL (V_TRUE, V_FALSE, V_UNKNOWN or V_ERROR)
 *   set1(in): DB_SET representation
 * 	 list_id(in): Sorted LIST FILE identifier
 *
 * Note: Find if given multi_set is a subset of the given list file.
 *              The list file must be of one column and treated like a
 *              multi_set. The routine uses the same semantics of finding
 *              subset relationship between two multi_sets.
 *
 * Note: in a sorted list file of one column , ALL the NULL values, tuples
 *       appear at the beginning of the list file.
 */
/*
 * [리뷰] eval_sub_multi_set_to_sort_list — 다중집합이 정렬 리스트의 부분집합인지 판정 — 이미 센 값은 건너뛰고, 값마다 집합 쪽(eval_item_card_set)과
 * 리스트 쪽(eval_item_card_sort_list) 카디널리티를 비교한다.
 * develop: develop(788)과 본문이 같고, 중복 탐지용 eval_value_rel_cmp 호출만 5인자였다.
 * 이 PR: 그 호출이 (…, R_EQ, NULL, NULL, &eval_Compare_elements, NULL) 로 바뀌었다.
 * 바뀐 것: 호출 인자만 변경(1줄).
 */
static DB_LOGICAL
eval_sub_multi_set_to_sort_list (THREAD_ENTRY * thread_p, DB_SET * set1, QFILE_LIST_ID * list_id)
{
  int i, k, card, card1, card2;
  DB_LOGICAL res;
  DB_LOGICAL rc;
  DB_VALUE elem_val, elem_val2;
  int found;

  PRIM_SET_NULL (&elem_val);
  PRIM_SET_NULL (&elem_val2);

  card = set_size (set1);
  if (card == 0)
    {
      return V_TRUE;		/* empty set */
    }

  res = V_TRUE;
  for (i = 0; i < card; i++)
    {
      if (set_get_element (set1, i, &elem_val) != NO_ERROR)
	{
	  return V_ERROR;
	}
      if (db_value_is_null (&elem_val))
	{
	  return V_UNKNOWN;
	}

      /* search for the value to see if value has already been considered */
      found = false;
      for (k = 0; !found && k < i; k++)
	{
	  if (set_get_element (set1, k, &elem_val2) != NO_ERROR)
	    {
	      pr_clear_value (&elem_val);
	      return V_ERROR;
	    }
	  if (db_value_is_null (&elem_val2))
	    {
	      pr_clear_value (&elem_val2);
	      continue;
	    }

	  rc = eval_value_rel_cmp (thread_p, &elem_val, &elem_val2, R_EQ, NULL, NULL, &eval_Compare_elements, NULL);
	  if (rc == V_ERROR)
	    {
	      pr_clear_value (&elem_val);
	      pr_clear_value (&elem_val2);
	      return V_ERROR;
	    }
	  else if (rc == V_TRUE)
	    {
	      found = true;
	    }
	  pr_clear_value (&elem_val2);
	}

      if (found)
	{
	  pr_clear_value (&elem_val);
	  continue;
	}

      card1 = eval_item_card_set (thread_p, &elem_val, set1, R_EQ);
      if (card1 == ER_FAILED)
	{
	  pr_clear_value (&elem_val);
	  return V_ERROR;
	}
      else if (card1 == UNKNOWN_CARD)
	{
	  pr_clear_value (&elem_val);
	  return V_UNKNOWN;
	}

      card2 = eval_item_card_sort_list (thread_p, &elem_val, list_id);
      if (card2 == ER_FAILED)
	{
	  pr_clear_value (&elem_val);
	  return V_ERROR;
	}
      else if (card2 == UNKNOWN_CARD)
	{
	  pr_clear_value (&elem_val);
	  return V_UNKNOWN;
	}

      if (card1 > card2)
	{
	  pr_clear_value (&elem_val);
	  return V_FALSE;
	}
    }

  pr_clear_value (&elem_val);
  return res;
}

/*
 * eval_sub_sort_list_to_multi_set () -
 *   return: DB_LOGICAL (V_TRUE, V_FALSE, V_UNKNOWN or V_ERROR)
 * 	 list_id(in): Sorted LIST FILE identifier
 * 	 set(in): DB_SETrepresentation
 *
 * Note: Find if the given list file is a subset of the given multi_set
 *              The list file must be of one column and treated like a
 *              multi_set. The routine uses the same semantics of finding
 *              subset relationship between two multi_sets.
 *
 * Note: in a sorted list file of one column , ALL the NULL values, tuples
 *       appear at the beginning of the list file.
 */
/*
 * [리뷰] eval_sub_sort_list_to_multi_set — 정렬 리스트가 다중집합의 부분집합인지 판정 — 리스트를 훑으며 값이 바뀌는 지점마다 집합 쪽 카디널리티와 비교한다.
 * develop: develop(902)과 본문이 같다. 직전 튜플 사본을 qfile_slot_set_tuple_ptr_and_layout 로 바인딩하고 읽는 것도 develop 에 이미 있다.
 * 비교 호출만 5인자였다.
 * 이 PR: 두 eval_value_rel_cmp 중 중복 판정 호출이 &eval_Compare_elements 를 받는 형태로 바뀌었다. 나머지(p_tplrec alloc/realloc 과
 * end 라벨의 단일 해제)는 그대로.
 * 바뀐 것: 호출 인자만 변경(1줄).
 */
static DB_LOGICAL
eval_sub_sort_list_to_multi_set (THREAD_ENTRY * thread_p, QFILE_LIST_ID * list_id, DB_SET * set)
{
  int card1, card2;
  DB_LOGICAL res, rc;
  DB_VALUE list_val, list_val2;
  QFILE_LIST_SCAN_ID s_id;
  QFILE_TUPLE_RECORD tplrec, p_tplrec;
  SCAN_CODE qp_scan;
  bool list_on;
  int tpl_len;
  bool is_null;

  /* assert */
  if (list_id->type_list.domp == NULL)
    {
      return V_ERROR;
    }

  PRIM_SET_NULL (&list_val);
  PRIM_SET_NULL (&list_val2);

  if (list_id->tuple_cnt == 0)
    {
      return V_TRUE;		/* empty set */
    }

  if (qfile_open_list_scan (list_id, &s_id) != NO_ERROR)
    {
      return V_ERROR;
    }

  res = V_TRUE;

  tplrec = QFILE_TUPLE_RECORD_INITIALIZER;
  p_tplrec.size = DB_PAGESIZE;
  p_tplrec.tpl = (QFILE_TUPLE) db_private_alloc (thread_p, DB_PAGESIZE);
  if (p_tplrec.tpl == NULL)
    {
      qfile_close_scan (thread_p, &s_id);
      return V_ERROR;
    }

  list_on = false;
  card1 = 0;
  while ((qp_scan = qfile_scan_list_next (thread_p, &s_id, &tplrec, PEEK)) == S_SUCCESS)
    {
      pr_clear_value (&list_val);

      if (qfile_slot_read_column_value (&tplrec, 0, list_id->type_list.domp[0], &list_val, true, &is_null) != NO_ERROR)
	{
	  res = V_ERROR;
	  goto end;
	}
      if (is_null)
	{
	  res = V_UNKNOWN;
	  goto end;
	}

      if (list_on == true)
	{
	  /* private copy of the previous tuple: bind + reset the slot before reading it */
	  qfile_slot_set_tuple_ptr_and_layout (&p_tplrec, p_tplrec.tpl, p_tplrec.size, tplrec.type_list);
	  if (qfile_slot_read_column_value (&p_tplrec, 0, list_id->type_list.domp[0], &list_val2, true, &is_null) !=
	      NO_ERROR || is_null)
	    {
	      res = V_ERROR;
	      goto end;
	    }

	  rc = eval_value_rel_cmp (thread_p, &list_val, &list_val2, R_EQ, NULL, NULL, &eval_Compare_elements, NULL);
	  if (rc == V_ERROR)
	    {
	      res = V_ERROR;
	      goto end;
	    }
	  else if (rc != V_TRUE)
	    {
	      card2 = eval_item_card_set (thread_p, &list_val2, set, R_EQ);
	      if (card2 == ER_FAILED)
		{
		  res = V_ERROR;
		  goto end;
		}
	      else if (card2 == UNKNOWN_CARD)
		{
		  res = V_UNKNOWN;
		  goto end;
		}

	      if (card1 > card2)
		{
		  res = V_FALSE;
		  goto end;
		}
	      card1 = 0;
	    }
	  pr_clear_value (&list_val2);
	}

      tpl_len = QFILE_GET_TUPLE_LENGTH (tplrec.tpl);
      if (p_tplrec.size < tpl_len)
	{
	  p_tplrec.size = tpl_len;
	  p_tplrec.tpl = (QFILE_TUPLE) db_private_realloc (thread_p, p_tplrec.tpl, tpl_len);
	  if (p_tplrec.tpl == NULL)
	    {
	      res = V_ERROR;
	      goto end;
	    }
	}
      memcpy (p_tplrec.tpl, tplrec.tpl, tpl_len);
      list_on = true;
      card1++;
    }

  if (qp_scan != S_END)
    {
      res = V_ERROR;
      goto end;
    }

  if (list_on == true)
    {
      /* private copy of the last tuple (no unbound value): bind + reset the slot before reading it */
      qfile_slot_set_tuple_ptr_and_layout (&p_tplrec, p_tplrec.tpl, p_tplrec.size, &s_id.list_id.type_list);
      if (qfile_slot_read_column_value (&p_tplrec, 0, list_id->type_list.domp[0], &list_val2, true, &is_null) !=
	  NO_ERROR || is_null)
	{
	  res = V_ERROR;
	  goto end;
	}

      card2 = eval_item_card_set (thread_p, &list_val2, set, R_EQ);
      if (card2 == ER_FAILED)
	{
	  res = V_ERROR;
	  goto end;
	}
      else if (card2 == UNKNOWN_CARD)
	{
	  res = V_UNKNOWN;
	  goto end;
	}
      else if (card1 > card2)
	{
	  res = V_FALSE;
	  goto end;
	}
    }

end:
  pr_clear_value (&list_val);
  pr_clear_value (&list_val2);
  qfile_close_scan (thread_p, &s_id);
  if (p_tplrec.tpl != NULL)
    {
      db_private_free_and_init (thread_p, p_tplrec.tpl);
    }
  return res;
}

/*
 * eval_sub_sort_list_to_sort_list () -
 *   return: DB_LOGICAL (V_TRUE, V_FALSE, V_UNKNOWN or V_ERROR)
 * 	 list_id1(in): First Sorted LIST FILE identifier
 * 	 list_id2(in): Second Sorted LIST FILE identifier
 *
 * Note: Find if the first list file is a subset of the second list
 *              file. The list files must be of one column and treated like
 *              a multi_set. The routine uses the same semantics of finding
 *              subset relationship between two multi_sets.
 *
 * Note: in a sorted list file of one column , ALL the NULL values, tuples
 *       appear at the beginning of the list file.
 */
/*
 * [리뷰] eval_sub_sort_list_to_sort_list — 정렬 리스트 1이 정렬 리스트 2의 부분집합인지 판정 — 값 구간마다 양쪽 카디널리티를 비교한다.
 * develop: develop(1079)과 본문이 같고, 중복 판정 eval_value_rel_cmp 호출만 5인자였다.
 * 이 PR: 그 호출이 (…, R_EQ, NULL, NULL, &eval_Compare_elements, NULL) 로 바뀌었다. 스캔·p_tplrec 관리·end 라벨 정리는 그대로.
 * 바뀐 것: 호출 인자만 변경(1줄).
 */
static DB_LOGICAL
eval_sub_sort_list_to_sort_list (THREAD_ENTRY * thread_p, QFILE_LIST_ID * list_id1, QFILE_LIST_ID * list_id2)
{
  int card1, card2;
  DB_LOGICAL res, rc;
  DB_VALUE list_val, list_val2;
  QFILE_LIST_SCAN_ID s_id;
  QFILE_TUPLE_RECORD tplrec, p_tplrec;
  SCAN_CODE qp_scan;
  bool list_on;
  int tpl_len;
  bool is_null;

  /* assert */
  if (list_id1->type_list.domp == NULL)
    {
      return V_ERROR;
    }

  PRIM_SET_NULL (&list_val);
  PRIM_SET_NULL (&list_val2);

  if (list_id1->tuple_cnt == 0)
    {
      return V_TRUE;		/* empty set */
    }

  if (qfile_open_list_scan (list_id1, &s_id) != NO_ERROR)
    {
      return V_ERROR;
    }

  res = V_TRUE;

  tplrec = QFILE_TUPLE_RECORD_INITIALIZER;
  p_tplrec.size = DB_PAGESIZE;
  p_tplrec.tpl = (QFILE_TUPLE) db_private_alloc (thread_p, DB_PAGESIZE);
  if (p_tplrec.tpl == NULL)
    {
      qfile_close_scan (thread_p, &s_id);
      return V_ERROR;
    }

  list_on = false;
  card1 = 0;
  while ((qp_scan = qfile_scan_list_next (thread_p, &s_id, &tplrec, PEEK)) == S_SUCCESS)
    {
      pr_clear_value (&list_val);

      if (qfile_slot_read_column_value (&tplrec, 0, list_id1->type_list.domp[0], &list_val, true, &is_null) != NO_ERROR)
	{
	  res = V_ERROR;
	  goto end;
	}
      if (is_null)
	{
	  res = V_UNKNOWN;
	  goto end;
	}

      if (list_on == true)
	{
	  /* private copy of the previous tuple: bind + reset the slot before reading it */
	  qfile_slot_set_tuple_ptr_and_layout (&p_tplrec, p_tplrec.tpl, p_tplrec.size, tplrec.type_list);
	  if (qfile_slot_read_column_value (&p_tplrec, 0, list_id1->type_list.domp[0], &list_val2, true, &is_null) !=
	      NO_ERROR || is_null)
	    {
	      res = V_ERROR;
	      goto end;
	    }

	  rc = eval_value_rel_cmp (thread_p, &list_val, &list_val2, R_EQ, NULL, NULL, &eval_Compare_elements, NULL);

	  if (rc == V_ERROR)
	    {
	      res = V_ERROR;
	      goto end;
	    }
	  else if (rc != V_TRUE)
	    {
	      card2 = eval_item_card_sort_list (thread_p, &list_val2, list_id2);
	      if (card2 == ER_FAILED)
		{
		  res = V_ERROR;
		  goto end;
		}
	      else if (card2 == UNKNOWN_CARD)
		{
		  res = V_UNKNOWN;
		  goto end;
		}

	      if (card1 > card2)
		{
		  res = V_FALSE;
		  goto end;
		}
	      card1 = 0;
	    }
	  pr_clear_value (&list_val2);
	}

      tpl_len = QFILE_GET_TUPLE_LENGTH (tplrec.tpl);
      if (p_tplrec.size < tpl_len)
	{
	  p_tplrec.size = tpl_len;
	  p_tplrec.tpl = (QFILE_TUPLE) db_private_realloc (thread_p, p_tplrec.tpl, tpl_len);
	  if (p_tplrec.tpl == NULL)
	    {
	      res = V_ERROR;
	      goto end;
	    }
	}
      memcpy (p_tplrec.tpl, tplrec.tpl, tpl_len);
      list_on = true;
      card1++;
    }

  if (qp_scan != S_END)
    {
      res = V_ERROR;
      goto end;
    }

  if (list_on == true)
    {
      /* private copy of the last tuple (no unbound value): bind + reset the slot before reading it */
      qfile_slot_set_tuple_ptr_and_layout (&p_tplrec, p_tplrec.tpl, p_tplrec.size, &s_id.list_id.type_list);
      if (qfile_slot_read_column_value (&p_tplrec, 0, list_id1->type_list.domp[0], &list_val2, true, &is_null) !=
	  NO_ERROR || is_null)
	{
	  res = V_ERROR;
	  goto end;
	}

      card2 = eval_item_card_sort_list (thread_p, &list_val2, list_id2);
      if (card2 == ER_FAILED)
	{
	  res = V_ERROR;
	  goto end;
	}
      else if (card2 == UNKNOWN_CARD)
	{
	  res = V_UNKNOWN;
	  goto end;
	}
      else if (card1 > card2)
	{
	  res = V_FALSE;
	  goto end;
	}
    }

end:
  pr_clear_value (&list_val);
  pr_clear_value (&list_val2);
  qfile_close_scan (thread_p, &s_id);
  if (p_tplrec.tpl != NULL)
    {
      db_private_free_and_init (thread_p, p_tplrec.tpl);
    }

  return res;
}

/*
 * eval_eq_multi_set_to_sort_list () -
 *   return: DB_LOGICAL (V_TRUE, V_FALSE, V_UNKNOWN or V_ERROR)
 *   set(in): DB_SET representation
 *   list_id(in): Sorted LIST FILE identifier
 *
 * Note: Find if given multi_set is equal to the given list file.
 *              The routine uses the same semantics of finding equality
 *              relationship between two multi_sets.
 */
static DB_LOGICAL
eval_eq_multi_set_to_sort_list (THREAD_ENTRY * thread_p, DB_SET * set, QFILE_LIST_ID * list_id)
{
  DB_LOGICAL res1, res2;

  res1 = eval_sub_multi_set_to_sort_list (thread_p, set, list_id);
  res2 = eval_sub_sort_list_to_multi_set (thread_p, list_id, set);

  return eval_logical_result (res1, res2);
}

/*
 * eval_ne_multi_set_to_sort_list () -
 *   return: DB_LOGICAL (V_TRUE, V_FALSE, V_UNKNOWN or V_ERROR)
 *   set(in): DB_SET representation
 *   list_id(in): Sorted LIST FILE identifier
 *
 * Note: Find if given multi_set is not equal to the given list file.
 */
static DB_LOGICAL
eval_ne_multi_set_to_sort_list (THREAD_ENTRY * thread_p, DB_SET * set, QFILE_LIST_ID * list_id)
{
  DB_LOGICAL res;

  res = eval_eq_multi_set_to_sort_list (thread_p, set, list_id);
  /* negate the result */
  return eval_negative (res);
}

/*
 * eval_le_multi_set_to_sort_list () -
 *   return: DB_LOGICAL (V_TRUE, V_FALSE, V_UNKNOWN or V_ERROR)
 *   set(in): DB_SET representation
 *   list_id(in): Sorted LIST FILE identifier
 *
 * Note: Find if given multi_set is a subset of the given list file.
 */
static DB_LOGICAL
eval_le_multi_set_to_sort_list (THREAD_ENTRY * thread_p, DB_SET * set, QFILE_LIST_ID * list_id)
{
  return eval_sub_multi_set_to_sort_list (thread_p, set, list_id);
}

/*
 * eval_lt_multi_set_to_sort_list () -
 *   return: DB_LOGICAL (V_TRUE, V_FALSE, V_UNKNOWN or V_ERROR)
 *   set(in): DB_SET representation
 *   list_id(in): Sorted LIST FILE identifier
 *
 * Note: Find if given multi_set is a proper subset of the given list file.
 */
static DB_LOGICAL
eval_lt_multi_set_to_sort_list (THREAD_ENTRY * thread_p, DB_SET * set, QFILE_LIST_ID * list_id)
{
  DB_LOGICAL res1, res2;

  res1 = eval_sub_multi_set_to_sort_list (thread_p, set, list_id);
  res2 = eval_ne_multi_set_to_sort_list (thread_p, set, list_id);

  return eval_logical_result (res1, res2);
}

/*
 * eval_le_sort_list_to_multi_set () -
 *   return: DB_LOGICAL (V_TRUE, V_FALSE, V_UNKNOWN or V_ERROR)
 *   list_id(in): Sorted LIST FILE identifier
 *   set(in): Multi_set disk representation
 *
 * Note: Find if given list file is a subset of the multi_set.
 */
static DB_LOGICAL
eval_le_sort_list_to_multi_set (THREAD_ENTRY * thread_p, QFILE_LIST_ID * list_id, DB_SET * set)
{
  return eval_sub_sort_list_to_multi_set (thread_p, list_id, set);
}

/*
 * eval_lt_sort_list_to_multi_set () -
 *   return: DB_LOGICAL (V_TRUE, V_FALSE, V_UNKNOWN or V_ERROR)
 *   list_id(in): Sorted LIST FILE identifier
 *   set(in): DB_SET representation
 *
 * Note: Find if given list file is a proper subset of the multi_set.
 */
static DB_LOGICAL
eval_lt_sort_list_to_multi_set (THREAD_ENTRY * thread_p, QFILE_LIST_ID * list_id, DB_SET * set)
{
  DB_LOGICAL res1, res2;

  res1 = eval_sub_sort_list_to_multi_set (thread_p, list_id, set);
  res2 = eval_ne_multi_set_to_sort_list (thread_p, set, list_id);

  return eval_logical_result (res1, res2);
}

/*
 * eval_eq_sort_list_to_sort_list () -
 *   return: DB_LOGICAL (V_TRUE, V_FALSE, V_UNKNOWN or V_ERROR)
 *   list_id1(in): First Sorted LIST FILE identifier
 *   list_id2(in): Second Sorted LIST FILE identifier
 *
 * Note: Find if the first list file is equal to the second list file.
 *              The list files must be of one column and treated like
 *              multi_sets. The routine uses the same semantics of finding
 *              equality relationship between two multi_sets.
 */
static DB_LOGICAL
eval_eq_sort_list_to_sort_list (THREAD_ENTRY * thread_p, QFILE_LIST_ID * list_id1, QFILE_LIST_ID * list_id2)
{
  DB_LOGICAL res1, res2;

  res1 = eval_sub_sort_list_to_sort_list (thread_p, list_id1, list_id2);
  res2 = eval_sub_sort_list_to_sort_list (thread_p, list_id2, list_id1);

  return eval_logical_result (res1, res2);
}

/*
 * eval_ne_sort_list_to_sort_list () -
 *   return: DB_LOGICAL (V_TRUE, V_FALSE, V_UNKNOWN or V_ERROR)
 *   list_id1(in): First Sorted LIST FILE identifier
 *   list_id2(in): Second Sorted LIST FILE identifier
 *
 * Note: Find if the first list file is not equal to the second one.
 */
static DB_LOGICAL
eval_ne_sort_list_to_sort_list (THREAD_ENTRY * thread_p, QFILE_LIST_ID * list_id1, QFILE_LIST_ID * list_id2)
{
  DB_LOGICAL res;

  res = eval_eq_sort_list_to_sort_list (thread_p, list_id1, list_id2);
  /* negate the result */
  return eval_negative (res);
}

/*
 * eval_le_sort_list_to_sort_list () -
 *   return: DB_LOGICAL (V_TRUE, V_FALSE, V_UNKNOWN or V_ERROR)
 *   list_id1(in): First Sorted LIST FILE identifier
 *   list_id2(in): Second Sorted LIST FILE identifier
 *
 * Note: Find if the first list file is a subset if the second one.
 */
static DB_LOGICAL
eval_le_sort_list_to_sort_list (THREAD_ENTRY * thread_p, QFILE_LIST_ID * list_id1, QFILE_LIST_ID * list_id2)
{
  return eval_sub_sort_list_to_sort_list (thread_p, list_id1, list_id2);
}

/*
 * eval_lt_sort_list_to_sort_list () -
 *   return: DB_LOGICAL (V_TRUE, V_FALSE, V_UNKNOWN or V_ERROR)
 *   list_id1(in): First Sorted LIST FILE identifier
 *   list_id2(in): Second Sorted LIST FILE identifier
 *
 * Note: Find if the first list file is a proper subset if the second
 *       list file.
 */
static DB_LOGICAL
eval_lt_sort_list_to_sort_list (THREAD_ENTRY * thread_p, QFILE_LIST_ID * list_id1, QFILE_LIST_ID * list_id2)
{
  DB_LOGICAL res1, res2;

  res1 = eval_sub_sort_list_to_sort_list (thread_p, list_id1, list_id2);
  res2 = eval_ne_sort_list_to_sort_list (thread_p, list_id1, list_id2);

  return eval_logical_result (res1, res2);
}

/*
 * eval_multi_set_to_sort_list () -
 *   return: DB_LOGICAL (V_TRUE, V_FALSE, V_UNKNOWN or V_ERROR)
 *   set(in): DB_SET representation
 *   list_id(in): Sorted LIST FILE identifier
 *   rel_operator(in): Relational Operator
 *
 * Note: Find if given multi_set and the list file satisfy the
 *              relationship indicated by the relational operator. The list
 *              file must be of one column, sorted and is treated like a
 *              multi_set.
 */
static DB_LOGICAL
eval_multi_set_to_sort_list (THREAD_ENTRY * thread_p, DB_SET * set, QFILE_LIST_ID * list_id, REL_OP rel_operator)
{
  switch (rel_operator)
    {
    case R_LT:
      return eval_lt_multi_set_to_sort_list (thread_p, set, list_id);
    case R_LE:
      return eval_le_multi_set_to_sort_list (thread_p, set, list_id);
    case R_GT:
      return eval_lt_sort_list_to_multi_set (thread_p, list_id, set);
    case R_GE:
      return eval_le_sort_list_to_multi_set (thread_p, list_id, set);
    case R_EQ:
      return eval_eq_multi_set_to_sort_list (thread_p, set, list_id);
    case R_NE:
      return eval_ne_multi_set_to_sort_list (thread_p, set, list_id);
    default:
      return V_ERROR;
    }
}

/*
 * eval_sort_list_to_multi_set () -
 *   return: DB_LOGICAL (V_TRUE, V_FALSE, V_UNKNOWN or V_ERROR)
 *   list_id(in): Sorted LIST FILE identifier
 *   set(in): DB_SET representation
 *   rel_operator(in): Relational Operator
 *
 * Note: Find if given list file and the multi_set satisfy the
 *              relationship indicated by the relational operator. The list
 *              file must be of one column, sorted and is treated like a
 *              multi_set.
 */
static DB_LOGICAL
eval_sort_list_to_multi_set (THREAD_ENTRY * thread_p, QFILE_LIST_ID * list_id, DB_SET * set, REL_OP rel_operator)
{
  switch (rel_operator)
    {
    case R_LT:
      return eval_lt_sort_list_to_multi_set (thread_p, list_id, set);
    case R_LE:
      return eval_le_sort_list_to_multi_set (thread_p, list_id, set);
    case R_GT:
      return eval_lt_multi_set_to_sort_list (thread_p, set, list_id);
    case R_GE:
      return eval_le_multi_set_to_sort_list (thread_p, set, list_id);
    case R_EQ:
      return eval_eq_multi_set_to_sort_list (thread_p, set, list_id);
    case R_NE:
      return eval_ne_multi_set_to_sort_list (thread_p, set, list_id);
    default:
      return V_ERROR;
    }
}

/*
 * eval_sort_list_to_sort_list () -
 *   return: DB_LOGICAL (V_TRUE, V_FALSE, V_UNKNOWN or V_ERROR)
 *   list_id1(in): First Sorted LIST FILE identifier
 *   list_id2(in): Second Sorted LIST FILE identifier
 *   rel_operator(in): Relational Operator
 *
 * Note: Find if first list file and the second list file satisfy the
 *              relationship indicated by the relational operator. The list
 *              files must be of one column, sorted and are treated like
 *              multi_sets.
 */
static DB_LOGICAL
eval_sort_list_to_sort_list (THREAD_ENTRY * thread_p, QFILE_LIST_ID * list_id1, QFILE_LIST_ID * list_id2,
			     REL_OP rel_operator)
{
  switch (rel_operator)
    {
    case R_LT:
      return eval_lt_sort_list_to_sort_list (thread_p, list_id1, list_id2);
    case R_LE:
      return eval_le_sort_list_to_sort_list (thread_p, list_id1, list_id2);
    case R_GT:
      return eval_lt_sort_list_to_sort_list (thread_p, list_id2, list_id1);
    case R_GE:
      return eval_le_sort_list_to_sort_list (thread_p, list_id2, list_id1);
    case R_EQ:
      return eval_eq_sort_list_to_sort_list (thread_p, list_id1, list_id2);
    case R_NE:
      return eval_ne_sort_list_to_sort_list (thread_p, list_id1, list_id2);
    default:
      return V_ERROR;
    }
}

/*
 * eval_set_list_cmp () -
 *   return: DB_LOGICAL (V_TRUE, V_FALSE, V_UNKNOWN or V_ERROR)
 *   et_comp(in): compound evaluation term
 *   vd(in):
 *   dbval1(in): lhs db_value, if lhs is a set.
 *   dbval2(in): rhs db_value, if rhs is a set.
 *
 * Note: Perform set/set, set/list, and list/list comparisons.
 */
static DB_LOGICAL
eval_set_list_cmp (THREAD_ENTRY * thread_p, const COMP_EVAL_TERM * et_comp, val_descr * vd, DB_VALUE * dbval1,
		   DB_VALUE * dbval2)
{
  QFILE_LIST_ID *t_list_id;
  QFILE_SORTED_LIST_ID *lhs_srlist_id, *rhs_srlist_id;

  if (et_comp->lhs->type == TYPE_LIST_ID)
    {
      /* execute linked query */
      EXECUTE_REGU_VARIABLE_XASL (thread_p, et_comp->lhs, vd);
      if (CHECK_REGU_VARIABLE_XASL_STATUS (et_comp->lhs) != XASL_SUCCESS)
	{
	  return V_ERROR;
	}

      /*
       * lhs value refers to a list file. for efficiency reasons
       * first sort the list file
       */
      lhs_srlist_id = et_comp->lhs->value.srlist_id;
      if (lhs_srlist_id->sorted == false)
	{
	  if (lhs_srlist_id->list_id->tuple_cnt > 1)
	    {
	      t_list_id = qfile_sort_list (thread_p, lhs_srlist_id->list_id, NULL, Q_ALL, true);
	      if (t_list_id == NULL)
		{
		  return V_ERROR;
		}
	    }
	  lhs_srlist_id->sorted = true;
	}

      /* rhs value can only be either a set or a list file */
      if (et_comp->rhs->type == TYPE_LIST_ID)
	{
	  /* execute linked query */
	  EXECUTE_REGU_VARIABLE_XASL (thread_p, et_comp->rhs, vd);
	  if (CHECK_REGU_VARIABLE_XASL_STATUS (et_comp->rhs) != XASL_SUCCESS)
	    {
	      return V_ERROR;
	    }

	  /*
	   * rhs value refers to a list file. for efficiency reasons
	   * first sort the list file
	   */
	  rhs_srlist_id = et_comp->rhs->value.srlist_id;
	  if (rhs_srlist_id->sorted == false)
	    {
	      if (rhs_srlist_id->list_id->tuple_cnt > 1)
		{
		  t_list_id = qfile_sort_list (thread_p, rhs_srlist_id->list_id, NULL, Q_ALL, true);
		  if (t_list_id == NULL)
		    {
		      return V_ERROR;
		    }
		}
	      rhs_srlist_id->sorted = true;
	    }

	  /* compare two list files */
	  return eval_sort_list_to_sort_list (thread_p, lhs_srlist_id->list_id, rhs_srlist_id->list_id,
					      et_comp->rel_op);
	}
      else
	{
	  /* compare list file and set */
	  return eval_sort_list_to_multi_set (thread_p, lhs_srlist_id->list_id, db_get_set (dbval2), et_comp->rel_op);
	}
    }
  else if (et_comp->rhs->type == TYPE_LIST_ID)
    {
      /* execute linked query */
      EXECUTE_REGU_VARIABLE_XASL (thread_p, et_comp->rhs, vd);
      if (CHECK_REGU_VARIABLE_XASL_STATUS (et_comp->rhs) != XASL_SUCCESS)
	{
	  return V_ERROR;
	}

      /*
       * rhs value refers to a list file. for efficiency reasons
       * first sort the list file
       */
      rhs_srlist_id = et_comp->rhs->value.srlist_id;
      if (rhs_srlist_id->sorted == false)
	{
	  if (rhs_srlist_id->list_id->tuple_cnt > 1)
	    {
	      t_list_id = qfile_sort_list (thread_p, rhs_srlist_id->list_id, NULL, Q_ALL, true);
	      if (t_list_id == NULL)
		{
		  return V_ERROR;
		}
	    }
	  rhs_srlist_id->sorted = true;
	}

      /* lhs must be a set value, compare set and list */
      return eval_multi_set_to_sort_list (thread_p, db_get_set (dbval1), rhs_srlist_id->list_id, et_comp->rel_op);
    }

  return V_UNKNOWN;
}

/*
 * Main Predicate Evaluation Routines
 */

/*
 * eval_pred () -
 *   return: DB_LOGICAL (V_TRUE, V_FALSE, V_UNKNOWN or V_ERROR)
 *   pr(in): Predicate Expression Tree
 *   vd(in): Value descriptor for positional values (optional)
 *   obj_oid(in): Object Identifier
 *
 * Note: This is the main predicate expression evalution routine. It
 *              evaluates the given predicate predicate expression on the
 *              specified evaluation item to see if the evaluation item
 *              satisfies the indicate predicate. It uses a 3-valued logic
 *              and returns V_TRUE, V_FALSE or V_UNKNOWN. If an error occurs,
 *              necessary error code is set and V_ERROR is returned.
 */
/*
 * [리뷰] eval_pred — 술어 트리 전체를 재귀로 평가하는 서버 실행의 중심 — qexec_intprt_fnc·qexec_merge_fnc·px_scan 등 21개 호출처가 행마다 부른다.
 * V_TRUE/V_FALSE/V_UNKNOWN/V_ERROR 반환.
 * develop: develop(1660)의 T_COMP_EVAL_TERM 은 eval_value_rel_cmp(…, et_comp) 로 갔고, T_ALSM_EVAL_TERM 은
 * eval_all/some_eval·eval_all/some_list_eval 을 4인자로 불렀으며, 오른쪽이 집합도 리스트도 아니면 eval_value_rel_cmp(…, NULL) 로
 * 떨어졌다. 원소 비교 방식은 매 원소에서 결정됐다.
 * 이 PR: 비교항은 eval_compare_term(계획이 정한 비교)로 가고, ALSM 항은 lhs/rhs fetch 뒤 EVAL_ELEMENTS elements 를 선언해
 * eval_resolved_elements 를 **한 번** 부른 뒤 그 결과를 리스트/집합 경로에 넘긴다. 집합도 리스트도 아닐 때 게이트가 상수 하나를 해결해
 * 뒀으면(elements.constant, n==1) 그 변환된 값과 번호로 꺼낸 비교로 평가하는 분기가 새로 생겼다.
 * 바뀐 것: 비교 호출 교체, ALSM 에 elements 도출 1회 + 분기 1개 추가(약 +20줄). '결정은 스캔당 1회, 행은 읽기만' 이 술어 평가에 드러나는 자리.
 */
DB_LOGICAL
eval_pred (THREAD_ENTRY * thread_p, const PRED_EXPR * pr, val_descr * vd, OID * obj_oid)
{
  const COMP_EVAL_TERM *et_comp;
  const ALSM_EVAL_TERM *et_alsm;
  const LIKE_EVAL_TERM *et_like;
  DB_VALUE *peek_val1, *peek_val2, *peek_val3;
  DB_LOGICAL result = V_UNKNOWN;
  int regexp_res;
  const PRED_EXPR *t_pr;
  QFILE_SORTED_LIST_ID *srlist_id;
  static int max_recursion_sql_depth = prm_get_integer_value (PRM_ID_MAX_RECURSION_SQL_DEPTH);

  peek_val1 = NULL;
  peek_val2 = NULL;
  peek_val3 = NULL;

  if (thread_get_recursion_depth (thread_p) > max_recursion_sql_depth)
    {
      er_set (ER_ERROR_SEVERITY, ARG_FILE_LINE, ER_MAX_RECURSION_SQL_DEPTH, 1, max_recursion_sql_depth);

      return V_ERROR;
    }

  thread_inc_recursion_depth (thread_p);

  switch (pr->type)
    {
    case T_PRED:
      switch (pr->pe.m_pred.bool_op)
	{
	case B_AND:
	  /* 'pt_to_pred_expr()' will generate right-linear tree */
	  result = V_TRUE;
	  for (t_pr = pr; result == V_TRUE && t_pr->type == T_PRED && t_pr->pe.m_pred.bool_op == B_AND;
	       t_pr = t_pr->pe.m_pred.rhs)
	    {
	      if (result == V_UNKNOWN)
		{
		  result = eval_pred (thread_p, t_pr->pe.m_pred.lhs, vd, obj_oid);
		  result = (result == V_TRUE) ? V_UNKNOWN : result;
		}
	      else
		{
		  result = eval_pred (thread_p, t_pr->pe.m_pred.lhs, vd, obj_oid);
		}

	      if (result == V_FALSE || result == V_ERROR)
		{
		  goto exit;
		}
	    }

	  if (result == V_UNKNOWN)
	    {
	      result = eval_pred (thread_p, t_pr, vd, obj_oid);
	      result = (result == V_TRUE) ? V_UNKNOWN : result;
	    }
	  else
	    {
	      result = eval_pred (thread_p, t_pr, vd, obj_oid);
	    }
	  break;

	case B_OR:
	  /* 'pt_to_pred_expr()' will generate right-linear tree */
	  result = V_FALSE;
	  for (t_pr = pr; result == V_FALSE && t_pr->type == T_PRED && t_pr->pe.m_pred.bool_op == B_OR;
	       t_pr = t_pr->pe.m_pred.rhs)
	    {
	      if (result == V_UNKNOWN)
		{
		  result = eval_pred (thread_p, t_pr->pe.m_pred.lhs, vd, obj_oid);
		  result = (result == V_FALSE) ? V_UNKNOWN : result;
		}
	      else
		{
		  result = eval_pred (thread_p, t_pr->pe.m_pred.lhs, vd, obj_oid);
		}

	      if (result == V_TRUE || result == V_ERROR)
		{
		  goto exit;
		}
	    }

	  if (result == V_UNKNOWN)
	    {
	      result = eval_pred (thread_p, t_pr, vd, obj_oid);
	      result = (result == V_FALSE) ? V_UNKNOWN : result;
	    }
	  else
	    {
	      result = eval_pred (thread_p, t_pr, vd, obj_oid);
	    }
	  break;

	case B_XOR:
	  {
	    DB_LOGICAL result_lhs, result_rhs;

	    result_lhs = eval_pred (thread_p, pr->pe.m_pred.lhs, vd, obj_oid);
	    result_rhs = eval_pred (thread_p, pr->pe.m_pred.rhs, vd, obj_oid);

	    if (result_lhs == V_ERROR || result_rhs == V_ERROR)
	      {
		result = V_ERROR;
	      }
	    else if (result_lhs == V_UNKNOWN || result_rhs == V_UNKNOWN)
	      {
		result = V_UNKNOWN;
	      }
	    else if (result_lhs == result_rhs)
	      {
		result = V_FALSE;
	      }
	    else
	      {
		result = V_TRUE;
	      }
	  }
	  break;

	case B_IS:
	case B_IS_NOT:
	  {
	    DB_LOGICAL result_lhs, result_rhs;

	    result_lhs = eval_pred (thread_p, pr->pe.m_pred.lhs, vd, obj_oid);
	    result_rhs = eval_pred (thread_p, pr->pe.m_pred.rhs, vd, obj_oid);

	    if (result_lhs == V_ERROR || result_rhs == V_ERROR)
	      {
		result = V_ERROR;
	      }
	    else if (result_lhs == result_rhs)
	      {
		result = (pr->pe.m_pred.bool_op == B_IS) ? V_TRUE : V_FALSE;
	      }
	    else
	      {
		result = (pr->pe.m_pred.bool_op == B_IS) ? V_FALSE : V_TRUE;
	      }
	  }
	  break;

	default:
	  result = V_ERROR;
	  break;
	}
      break;

    case T_EVAL_TERM:
      switch (pr->pe.m_eval_term.et_type)
	{
	case T_COMP_EVAL_TERM:
	  /*
	   * compound evaluation terms are used to test relationships
	   * such as equality, greater than etc. between two items
	   * Each datatype defines its own meaning of relationship
	   * indicated by one of the relational operators.
	   */
	  et_comp = &pr->pe.m_eval_term.et.et_comp;

	  /* evaluate NULL predicate, if specified */
	  if (et_comp->rel_op == R_NULL)
	    {
	      result = eval_pred_comp1 (thread_p, pr, vd, obj_oid);
	      if (result == V_ERROR)
		{
		  goto exit;
		}
	      break;
	    }

	  /* evaluate EXISTS predicate, if specified */
	  if (et_comp->rel_op == R_EXISTS)
	    {
	      /* leaf node should refer to either a set or list file */
	      if (et_comp->lhs->type == TYPE_LIST_ID)
		{
		  /* execute linked query */
		  REGU_VARIABLE *regu_var = et_comp->lhs;
		  XASL_NODE *xasl = regu_var->xasl;
		  if (xasl && XASL_IS_FLAGED (xasl, XASL_USES_SQ_CACHE)
		      && !(SQ_CACHE_HT (xasl) && !SQ_CACHE_ENABLED (xasl)))
		    {
		      if (!sq_get (thread_p, SQ_CACHE_KEY_STRUCT (xasl), xasl, regu_var))
			{
			  SQ_KEY *key;
			  /* execute linked query */
			  EXECUTE_REGU_VARIABLE_XASL (thread_p, regu_var, vd);
			  if (CHECK_REGU_VARIABLE_XASL_STATUS (regu_var) != XASL_SUCCESS)
			    {
			      result = V_ERROR;
			      goto exit;
			    }
			  if ((key = sq_make_key (thread_p, xasl)) == NULL)
			    {
			      XASL_CLEAR_FLAG (xasl, XASL_USES_SQ_CACHE);
			      result = V_ERROR;
			      goto exit;
			    }
			  if (sq_put (thread_p, key, xasl, regu_var) == ER_FAILED)
			    {
			      sq_free_key (thread_p, key);
			    }
			}
		      else
			{
			  /* FOUND */
			  xasl->status = XASL_SUCCESS;
			}
		    }
		  else
		    {
		      EXECUTE_REGU_VARIABLE_XASL (thread_p, regu_var, vd);
		      if (CHECK_REGU_VARIABLE_XASL_STATUS (regu_var) != XASL_SUCCESS)
			{
			  result = V_ERROR;
			  goto exit;
			}
		    }

		  srlist_id = et_comp->lhs->value.srlist_id;
		  result = ((srlist_id->list_id->tuple_cnt > 0) ? V_TRUE : V_FALSE);
		}
	      else
		{
		  /* must be a set */
		  if (fetch_peek_dbval (thread_p, et_comp->lhs, vd, NULL, obj_oid, NULL, &peek_val1) != NO_ERROR)
		    {
		      result = V_ERROR;
		      goto exit;
		    }
		  else if (db_value_is_null (peek_val1))
		    {
		      result = V_UNKNOWN;
		      goto exit;
		    }
		  else if (!TP_IS_SET_TYPE (DB_VALUE_DOMAIN_TYPE (peek_val1)))
		    {
		      er_set (ER_ERROR_SEVERITY, ARG_FILE_LINE, ER_QPROC_INVALID_DATATYPE, 0);
		      result = V_ERROR;
		      goto exit;
		    }

		  result = ((db_set_size (db_get_set (peek_val1)) > 0) ? V_TRUE : V_FALSE);
		}
	      break;
	    }

	  /*
	   * fetch left hand size and right hand size values, if one of
	   * values are unbound, result = V_UNKNOWN
	   */
	  if (et_comp->lhs->type != TYPE_LIST_ID)
	    {
	      if (fetch_peek_dbval (thread_p, et_comp->lhs, vd, NULL, obj_oid, NULL, &peek_val1) != NO_ERROR)
		{
		  result = V_ERROR;
		  goto exit;
		}
	      else if (db_value_is_null (peek_val1))
		{
		  if (et_comp->rel_op != R_EQ_TORDER && et_comp->rel_op != R_NULLSAFE_EQ)
		    {
		      result = V_UNKNOWN;
		      goto exit;
		    }
		}
	    }

	  if (et_comp->rhs->type != TYPE_LIST_ID)
	    {
	      if (fetch_peek_dbval (thread_p, et_comp->rhs, vd, NULL, obj_oid, NULL, &peek_val2) != NO_ERROR)
		{
		  result = V_ERROR;
		  goto exit;
		}
	      else if (db_value_is_null (peek_val2))
		{
		  if (et_comp->rel_op != R_EQ_TORDER && et_comp->rel_op != R_NULLSAFE_EQ)
		    {
		      result = V_UNKNOWN;
		      goto exit;
		    }
		}
	    }

	  if (et_comp->lhs->type == TYPE_LIST_ID || et_comp->rhs->type == TYPE_LIST_ID)
	    {
	      result = eval_set_list_cmp (thread_p, et_comp, vd, peek_val1, peek_val2);
	    }
	  else
	    {
	      /* general case: compare values as the term's comparison was resolved before any row */
	      result = eval_compare_term (thread_p, et_comp, vd, peek_val1, peek_val2);
	    }
	  break;

	case T_ALSM_EVAL_TERM:
	  {
	    DB_TYPE rhs_type = DB_TYPE_UNKNOWN;
	    bool rhs_is_set = false;

	    et_alsm = &pr->pe.m_eval_term.et.et_alsm;

	    /*
	     * Note: According to ANSI, if the set or list file is empty,
	     * the result of comparison is true/false for ALL/SOME,
	     * regardless of whether lhs value is bound or not.
	     */
	    if (et_alsm->elemset->type != TYPE_LIST_ID)
	      {
		/* fetch rhs value */
		if (fetch_peek_dbval (thread_p, et_alsm->elemset, vd, NULL, obj_oid, NULL, &peek_val2) != NO_ERROR)
		  {
		    result = V_ERROR;
		    goto exit;
		  }
		else if (db_value_is_null (peek_val2))
		  {
		    result = V_UNKNOWN;
		    goto exit;
		  }

		rhs_type = DB_VALUE_TYPE (peek_val2);
		rhs_is_set = TP_IS_SET_TYPE (rhs_type);
		if (rhs_is_set && set_size (db_get_set (peek_val2)) == 0)
		  {
		    /* empty set */
		    result = (et_alsm->eq_flag == F_ALL) ? V_TRUE : V_FALSE;
		    goto exit;
		  }
	      }
	    else
	      {
		/* execute linked query */
		EXECUTE_REGU_VARIABLE_XASL (thread_p, et_alsm->elemset, vd);
		if (CHECK_REGU_VARIABLE_XASL_STATUS (et_alsm->elemset) != XASL_SUCCESS)
		  {
		    result = V_ERROR;
		    goto exit;
		  }
		else
		  {
		    /* check of empty list file */
		    srlist_id = et_alsm->elemset->value.srlist_id;
		    if (srlist_id->list_id->tuple_cnt == 0)
		      {
			result = (et_alsm->eq_flag == F_ALL) ? V_TRUE : V_FALSE;
			goto exit;
		      }
		  }
	      }

	    /* fetch lhs value */
	    if (fetch_peek_dbval (thread_p, et_alsm->elem, vd, NULL, obj_oid, NULL, &peek_val1) != NO_ERROR)
	      {
		result = V_ERROR;
		goto exit;
	      }
	    else if (db_value_is_null (peek_val1))
	      {
		result = V_UNKNOWN;
		goto exit;
	      }

	    EVAL_ELEMENTS elements;
	    eval_resolved_elements (et_alsm, vd, &elements);
	    if (et_alsm->elemset->type == TYPE_LIST_ID)
	      {
		/* rhs value is a list, use list evaluation routines */
		srlist_id = et_alsm->elemset->value.srlist_id;
		if (et_alsm->eq_flag == F_ALL)
		  {
		    result = eval_all_list_eval (thread_p, peek_val1, srlist_id->list_id, et_alsm->rel_op,
						 elements.all, vd);
		  }
		else
		  {
		    result = eval_some_list_eval (thread_p, peek_val1, srlist_id->list_id, et_alsm->rel_op,
						  elements.all, vd);
		  }
	      }
	    else if (rhs_is_set)
	      {
		/* rhs value is a set, use set evaluation routines */
		if (et_alsm->eq_flag == F_ALL)
		  {
		    result =
		      eval_all_eval (thread_p, peek_val1, db_get_set (peek_val2), et_alsm->rel_op, &elements, vd);
		  }
		else
		  {
		    result =
		      eval_some_eval (thread_p, peek_val1, db_get_set (peek_val2), et_alsm->rel_op, &elements, vd);
		  }
	      }
	    else if (elements.constant != NULL)
	      {
		/* a constant that is no collection: its one element, resolve_domains' own value */
		assert (elements.constant->n == 1);
		result =
		  eval_value_rel_cmp (thread_p, peek_val1, &elements.constant->value[0], et_alsm->rel_op, NULL, vd,
				      &elements.constant->compares[elements.constant->element_compare[0]], peek_val2);
	      }
	    else
	      {
		/* other cases, use general evaluation routines */
		result = eval_value_rel_cmp (thread_p, peek_val1, peek_val2, et_alsm->rel_op, NULL, vd, elements.all,
					     NULL);
	      }
	  }
	  break;

	case T_LIKE_EVAL_TERM:
	  et_like = &pr->pe.m_eval_term.et.et_like;

	  /* fetch source text expression */
	  if (fetch_peek_dbval (thread_p, et_like->src, vd, NULL, obj_oid, NULL, &peek_val1) != NO_ERROR)
	    {
	      result = V_ERROR;
	      goto exit;
	    }
	  else if (db_value_is_null (peek_val1))
	    {
	      result = V_UNKNOWN;
	      goto exit;
	    }

	  /* fetch pattern regular expression */
	  if (fetch_peek_dbval (thread_p, et_like->pattern, vd, NULL, obj_oid, NULL, &peek_val2) != NO_ERROR)
	    {
	      result = V_ERROR;
	      goto exit;
	    }
	  else if (db_value_is_null (peek_val2))
	    {
	      result = V_UNKNOWN;
	      goto exit;
	    }

	  if (et_like->esc_char)
	    {
	      /* fetch escape regular expression */
	      if (fetch_peek_dbval (thread_p, et_like->esc_char, vd, NULL, obj_oid, NULL, &peek_val3) != NO_ERROR)
		{
		  result = V_ERROR;
		  goto exit;
		}
	    }
	  /* evaluate regular expression match */
	  /* Note: Currently only STRING type is supported */
	  db_string_like (peek_val1, peek_val2, peek_val3, &regexp_res);
	  result = (DB_LOGICAL) regexp_res;
	  break;

	case T_RLIKE_EVAL_TERM:
	  /* evaluate rlike */
	  result = eval_pred_rlike7 (thread_p, pr, vd, obj_oid);
	  break;

	default:
	  result = V_ERROR;
	  break;
	}
      break;

    case T_NOT_TERM:
      result = eval_pred (thread_p, pr->pe.m_not_term, vd, obj_oid);
      /* negate the result */
      result = eval_negative (result);
      break;

    default:
      result = V_ERROR;
    }

exit:

  thread_dec_recursion_depth (thread_p);

  return result;
}

/*
 * eval_pred_comp0 () -
 *   return: DB_LOGICAL (V_TRUE, V_FALSE, V_UNKNOWN or V_ERROR)
 *   pr(in): Predicate Expression Tree
 *   vd(in): Value descriptor for positional values (optional)
 *   obj_oid(in): Object Identifier
 *
 * Note: single node regular comparison predicate
 */
/*
 * [리뷰] eval_pred_comp0 — 비교 술어 하나짜리 단말 술어 전용 평가자 — eval_fnc 가 술어 모양을 보고 골라 둔 빠른 경로로, 양쪽을 fetch_peek_dbval 로
 * 가져와 비교한다.
 * develop: develop(2144)은 두 값을 fetch 한 뒤 eval_value_rel_cmp (…, et_comp->rel_op, et_comp) 로 넘겼고, 주석은
 * "db_value_compare 가 필요한 코어션을 알아서 한다" 였다.
 * 이 PR: 마지막 호출이 eval_compare_term (thread_p, et_comp, vd, peek_val1, peek_val2) 로 바뀌고 주석도 "행 이전에 해결된 그대로 비교한다"
 * 로 교체됐다. fetch·NULL(R_NULLSAFE_EQ 예외) 처리는 동일.
 * 바뀐 것: 마지막 호출 1줄 + 주석 교체(-6/+2줄).
 */
DB_LOGICAL
eval_pred_comp0 (THREAD_ENTRY * thread_p, const PRED_EXPR * pr, val_descr * vd, OID * obj_oid)
{
  const COMP_EVAL_TERM *et_comp;
  DB_VALUE *peek_val1, *peek_val2;

  peek_val1 = NULL;
  peek_val2 = NULL;

  et_comp = &pr->pe.m_eval_term.et.et_comp;

  /*
   * fetch left hand size and right hand size values, if one of
   * values are unbound, return V_UNKNOWN
   */
  if (fetch_peek_dbval (thread_p, et_comp->lhs, vd, NULL, obj_oid, NULL, &peek_val1) != NO_ERROR)
    {
      return V_ERROR;
    }
  else if (db_value_is_null (peek_val1) && et_comp->rel_op != R_NULLSAFE_EQ)
    {
      return V_UNKNOWN;
    }

  if (fetch_peek_dbval (thread_p, et_comp->rhs, vd, NULL, obj_oid, NULL, &peek_val2) != NO_ERROR)
    {
      return V_ERROR;
    }
  else if (db_value_is_null (peek_val2) && et_comp->rel_op != R_NULLSAFE_EQ)
    {
      return V_UNKNOWN;
    }

  /* general case: compare values as the term's comparison was resolved before any row */
  return eval_compare_term (thread_p, et_comp, vd, peek_val1, peek_val2);
}

/*
 * eval_pred_comp1 () -
 *   return: DB_LOGICAL (V_TRUE, V_FALSE, V_UNKNOWN or V_ERROR)
 *   pr(in): Predicate Expression Tree
 *   vd(in): Value descriptor for positional values (optional)
 *   obj_oid(in): Object Identifier
 *
 * Note: single leaf node NULL predicate
 */
DB_LOGICAL
eval_pred_comp1 (THREAD_ENTRY * thread_p, const PRED_EXPR * pr, val_descr * vd, OID * obj_oid)
{
  const COMP_EVAL_TERM *et_comp;
  DB_VALUE *peek_val1;

  peek_val1 = NULL;

  et_comp = &pr->pe.m_eval_term.et.et_comp;

  if (fetch_peek_dbval (thread_p, et_comp->lhs, vd, NULL, obj_oid, NULL, &peek_val1) != NO_ERROR)
    {
      return V_ERROR;
    }
  else if (db_value_is_null (peek_val1))
    {
      return V_TRUE;
    }

  if (DB_VALUE_DOMAIN_TYPE (peek_val1) == DB_TYPE_OID
      && !heap_is_object_not_null (thread_p, (OID *) NULL, db_get_oid (peek_val1)))
    {
      return V_TRUE;
    }
  else
    {
      return V_FALSE;
    }
}

/*
 * eval_pred_comp2 () -
 *   return: DB_LOGICAL (V_TRUE, V_FALSE, V_UNKNOWN or V_ERROR)
 *   pr(in): Predicate Expression Tree
 *   vd(in): Value descriptor for positional values (optional)
 *   obj_oid(in): Object Identifier
 *
 * Note: single node EXIST predicate
 */
DB_LOGICAL
eval_pred_comp2 (THREAD_ENTRY * thread_p, const PRED_EXPR * pr, val_descr * vd, OID * obj_oid)
{
  const COMP_EVAL_TERM *et_comp;
  DB_VALUE *peek_val1;

  peek_val1 = NULL;

  et_comp = &pr->pe.m_eval_term.et.et_comp;

  /* evaluate EXISTS predicate, if specified */
  /* leaf node should refer to either a set or list file */
  if (et_comp->lhs->type == TYPE_LIST_ID)
    {
      /* execute linked query */
      EXECUTE_REGU_VARIABLE_XASL (thread_p, et_comp->lhs, vd);
      if (CHECK_REGU_VARIABLE_XASL_STATUS (et_comp->lhs) != XASL_SUCCESS)
	{
	  return V_ERROR;
	}
      else
	{
	  QFILE_SORTED_LIST_ID *srlist_id;

	  srlist_id = et_comp->lhs->value.srlist_id;
	  return (srlist_id->list_id->tuple_cnt > 0) ? V_TRUE : V_FALSE;
	}
    }
  else
    {
      if (fetch_peek_dbval (thread_p, et_comp->lhs, vd, NULL, obj_oid, NULL, &peek_val1) != NO_ERROR)
	{
	  return V_ERROR;
	}
      else if (db_value_is_null (peek_val1))
	{
	  return V_UNKNOWN;
	}
      else if (!TP_IS_SET_TYPE (DB_VALUE_DOMAIN_TYPE (peek_val1)))
	{
	  er_set (ER_ERROR_SEVERITY, ARG_FILE_LINE, ER_QPROC_INVALID_DATATYPE, 0);
	  return V_ERROR;
	}

      return (set_size (db_get_set (peek_val1)) > 0) ? V_TRUE : V_FALSE;
    }
}

/*
 * eval_pred_comp3 () -
 *   return: DB_LOGICAL (V_TRUE, V_FALSE, V_UNKNOWN or V_ERROR)
 *   pr(in): Predicate Expression Tree
 *   vd(in): Value descriptor for positional values (optional)
 *   obj_oid(in): Object Identifier
 *
 * Note: single node lhs or rhs list file predicate
 */
DB_LOGICAL
eval_pred_comp3 (THREAD_ENTRY * thread_p, const PRED_EXPR * pr, val_descr * vd, OID * obj_oid)
{
  const COMP_EVAL_TERM *et_comp;
  DB_VALUE *peek_val1, *peek_val2;

  peek_val1 = NULL;
  peek_val2 = NULL;

  et_comp = &pr->pe.m_eval_term.et.et_comp;

  /*
   * fetch left hand size and right hand size values, if one of
   * values are unbound, result = V_UNKNOWN
   */
  if (et_comp->lhs->type != TYPE_LIST_ID)
    {
      if (fetch_peek_dbval (thread_p, et_comp->lhs, vd, NULL, obj_oid, NULL, &peek_val1) != NO_ERROR)
	{
	  return V_ERROR;
	}
      else if (db_value_is_null (peek_val1))
	{
	  return V_UNKNOWN;
	}
    }

  if (et_comp->rhs->type != TYPE_LIST_ID)
    {
      if (fetch_peek_dbval (thread_p, et_comp->rhs, vd, NULL, obj_oid, NULL, &peek_val2) != NO_ERROR)
	{
	  return V_ERROR;
	}
      else if (db_value_is_null (peek_val2))
	{
	  return V_UNKNOWN;
	}
    }

  if (et_comp->lhs->type == TYPE_LIST_ID || et_comp->rhs->type == TYPE_LIST_ID)
    {
      return eval_set_list_cmp (thread_p, et_comp, vd, peek_val1, peek_val2);
    }
  else
    {
      return V_UNKNOWN;
    }
}

/*
 * eval_pred_alsm4 () -
 *   return: DB_LOGICAL (V_TRUE, V_FALSE, V_UNKNOWN or V_ERROR)
 *   pr(in): Predicate Expression Tree
 *   vd(in): Value descriptor for positional values (optional)
 *   obj_oid(in): Object Identifier
 *
 * Note: single node all/some predicate with a set
 */
/*
 * [리뷰] eval_pred_alsm4 — 오른쪽이 집합(컬렉션)인 ALL/SOME 단말 술어 전용 평가자 — 빈 집합 ANSI 규칙과 비집합 타입
 * 에러(ER_QPROC_INVALID_DATATYPE)를 먼저 처리한다.
 * develop: develop(2347)은 lhs fetch 직후 바로 eval_all_eval/eval_some_eval 을 4인자로 불렀다.
 * 이 PR: 그 앞에 EVAL_ELEMENTS elements; eval_resolved_elements (et_alsm, vd, &elements); 가 들어가고 &elements 와 vd 를
 * 넘긴다. 앞쪽 검사들은 그대로.
 * 바뀐 것: +3줄, 호출 인자 +2.
 */
DB_LOGICAL
eval_pred_alsm4 (THREAD_ENTRY * thread_p, const PRED_EXPR * pr, val_descr * vd, OID * obj_oid)
{
  const ALSM_EVAL_TERM *et_alsm;
  DB_VALUE *peek_val1, *peek_val2;

  peek_val1 = NULL;
  peek_val2 = NULL;

  et_alsm = &pr->pe.m_eval_term.et.et_alsm;

  /*
   * Note: According to ANSI, if the set or list file is empty,
   *       the result of comparison is true/false for ALL/SOME,
   *       regardles of whether lhs value is bound or not.
   */
  if (fetch_peek_dbval (thread_p, et_alsm->elemset, vd, NULL, obj_oid, NULL, &peek_val2) != NO_ERROR)
    {
      return V_ERROR;
    }
  else if (db_value_is_null (peek_val2))
    {
      return V_UNKNOWN;
    }
  else if (!TP_IS_SET_TYPE (DB_VALUE_DOMAIN_TYPE (peek_val2)))
    {
      er_set (ER_ERROR_SEVERITY, ARG_FILE_LINE, ER_QPROC_INVALID_DATATYPE, 0);
      return V_ERROR;
    }

  if (set_size (db_get_set (peek_val2)) == 0)
    {
      /* empty set */
      return ((et_alsm->eq_flag == F_ALL) ? V_TRUE : V_FALSE);
    }

  /* fetch item value */
  if (fetch_peek_dbval (thread_p, et_alsm->elem, vd, NULL, obj_oid, NULL, &peek_val1) != NO_ERROR)
    {
      return V_ERROR;
    }
  else if (db_value_is_null (peek_val1))
    {
      return V_UNKNOWN;
    }

  /* rhs value is a set, use set evaluation routines */
  EVAL_ELEMENTS elements;
  eval_resolved_elements (et_alsm, vd, &elements);
  if (et_alsm->eq_flag == F_ALL)
    {
      return eval_all_eval (thread_p, peek_val1, db_get_set (peek_val2), et_alsm->rel_op, &elements, vd);
    }
  else
    {
      return eval_some_eval (thread_p, peek_val1, db_get_set (peek_val2), et_alsm->rel_op, &elements, vd);
    }
}

/*
 * eval_pred_alsm5 () -
 *   return: DB_LOGICAL (V_TRUE, V_FALSE, V_UNKNOWN or V_ERROR)
 *   pr(in): Predicate Expression Tree
 *   vd(in): Value descriptor for positional values (optional)
 *   obj_oid(in): Object Identifier
 *
 * Note: single node all/some  predicate with a list file
 */
/*
 * [리뷰] eval_pred_alsm5 — 오른쪽이 리스트파일(연결된 부질의 결과)인 ALL/SOME 단말 술어 전용 평가자 — 연결 질의를 실행하고 빈 리스트 ANSI 규칙을 먼저 처리한다.
 * develop: develop(2413)은 lhs fetch 직후 eval_all_list_eval/eval_some_list_eval 을 4인자로 불렀다.
 * 이 PR: EVAL_ELEMENTS elements; eval_resolved_elements (…) 로 이번 실행의 원소 비교를 구해 elements.all 과 vd 를 넘긴다.
 * 바뀐 것: +3줄, 호출 인자 +2.
 */
DB_LOGICAL
eval_pred_alsm5 (THREAD_ENTRY * thread_p, const PRED_EXPR * pr, val_descr * vd, OID * obj_oid)
{
  const ALSM_EVAL_TERM *et_alsm;
  DB_VALUE *peek_val1;
  QFILE_SORTED_LIST_ID *srlist_id;

  peek_val1 = NULL;

  et_alsm = &pr->pe.m_eval_term.et.et_alsm;

  /* execute linked query */
  EXECUTE_REGU_VARIABLE_XASL (thread_p, et_alsm->elemset, vd);
  if (CHECK_REGU_VARIABLE_XASL_STATUS (et_alsm->elemset) != XASL_SUCCESS)
    {
      return V_ERROR;
    }

  /*
   * Note: According to ANSI, if the set or list file is empty,
   *       the result of comparison is true/false for ALL/SOME,
   *       regardless of whether lhs value is bound or not.
   */
  srlist_id = et_alsm->elemset->value.srlist_id;
  if (srlist_id->list_id->tuple_cnt == 0)
    {
      return (et_alsm->eq_flag == F_ALL) ? V_TRUE : V_FALSE;
    }

  /* fetch item value */
  if (fetch_peek_dbval (thread_p, et_alsm->elem, vd, NULL, obj_oid, NULL, &peek_val1) != NO_ERROR)
    {
      return V_ERROR;
    }
  else if (db_value_is_null (peek_val1))
    {
      return V_UNKNOWN;
    }

  EVAL_ELEMENTS elements;
  eval_resolved_elements (et_alsm, vd, &elements);
  if (et_alsm->eq_flag == F_ALL)
    {
      return eval_all_list_eval (thread_p, peek_val1, srlist_id->list_id, et_alsm->rel_op, elements.all, vd);
    }
  else
    {
      return eval_some_list_eval (thread_p, peek_val1, srlist_id->list_id, et_alsm->rel_op, elements.all, vd);
    }
}

/*
 * eval_pred_like6 () -
 *   return: DB_LOGICAL (V_TRUE, V_FALSE, V_UNKNOWN or V_ERROR)
 *   pr(in): Predicate Expression Tree
 *   vd(in): Value descriptor for positional values (optional)
 *   obj_oid(in): Object Identifier
 *
 * Note: single node like predicate
 */
DB_LOGICAL
eval_pred_like6 (THREAD_ENTRY * thread_p, const PRED_EXPR * pr, val_descr * vd, OID * obj_oid)
{
  const LIKE_EVAL_TERM *et_like;
  DB_VALUE *peek_val1, *peek_val2, *peek_val3;
  int regexp_res;

  peek_val1 = NULL;
  peek_val2 = NULL;
  peek_val3 = NULL;

  et_like = &pr->pe.m_eval_term.et.et_like;

  /* fetch source text expression */
  if (fetch_peek_dbval (thread_p, et_like->src, vd, NULL, obj_oid, NULL, &peek_val1) != NO_ERROR)
    {
      return V_ERROR;
    }
  else if (db_value_is_null (peek_val1))
    {
      return V_UNKNOWN;
    }

  /* fetch pattern regular expression */
  if (fetch_peek_dbval (thread_p, et_like->pattern, vd, NULL, obj_oid, NULL, &peek_val2) != NO_ERROR)
    {
      return V_ERROR;
    }
  else if (db_value_is_null (peek_val2))
    {
      return V_UNKNOWN;
    }

  if (et_like->esc_char)
    {
      /* fetch escape regular expression */
      if (fetch_peek_dbval (thread_p, et_like->esc_char, vd, NULL, obj_oid, NULL, &peek_val3) != NO_ERROR)
	{
	  return V_ERROR;
	}
    }

  /* evaluate regular expression match */
  /* Note: Currently only STRING type is supported */
  db_string_like (peek_val1, peek_val2, peek_val3, &regexp_res);

  return (DB_LOGICAL) regexp_res;
}

/*
 * eval_pred_rlike7 () -
 *   return: DB_LOGICAL (V_TRUE, V_FALSE, V_UNKNOWN or V_ERROR)
 *   pr(in): Predicate Expression Tree
 *   vd(in): Value descriptor for positional values (optional)
 *   obj_oid(in): Object Identifier
 *
 * Note: single node like predicate
 */
DB_LOGICAL
eval_pred_rlike7 (THREAD_ENTRY * thread_p, const PRED_EXPR * pr, val_descr * vd, OID * obj_oid)
{
  const RLIKE_EVAL_TERM *et_rlike;
  DB_VALUE *peek_val1, *peek_val2, *peek_val3;
  int regexp_res;

  peek_val1 = NULL;
  peek_val2 = NULL;
  peek_val3 = NULL;

  et_rlike = &pr->pe.m_eval_term.et.et_rlike;

  /* fetch source text expression */
  if (fetch_peek_dbval (thread_p, et_rlike->src, vd, NULL, obj_oid, NULL, &peek_val1) != NO_ERROR)
    {
      return V_ERROR;
    }
  else if (db_value_is_null (peek_val1))
    {
      return V_UNKNOWN;
    }

  /* fetch pattern */
  if (fetch_peek_dbval (thread_p, et_rlike->pattern, vd, NULL, obj_oid, NULL, &peek_val2) != NO_ERROR)
    {
      return V_ERROR;
    }
  else if (db_value_is_null (peek_val2))
    {
      return V_UNKNOWN;
    }

  /* fetch case sensitiveness */
  if (fetch_peek_dbval (thread_p, et_rlike->case_sensitive, vd, NULL, obj_oid, NULL, &peek_val3) != NO_ERROR)
    {
      return V_ERROR;
    }
  else if (db_value_is_null (peek_val3))
    {
      return V_UNKNOWN;
    }

  /* evaluate regular expression match */
  db_string_rlike (peek_val1, peek_val2, peek_val3, &et_rlike->compiled_regex, &regexp_res);

  return (DB_LOGICAL) regexp_res;
}

/*
 * eval_fnc () -
 *   return:
 *   pr(in): Predicate Expression Tree
 *   single_node_type(in):
 */
PR_EVAL_FNC
eval_fnc (THREAD_ENTRY * thread_p, const PRED_EXPR * pr, DB_TYPE * single_node_type)
{
  // todo - thread_p is never used

  const COMP_EVAL_TERM *et_comp;
  const ALSM_EVAL_TERM *et_alsm;

  *single_node_type = DB_TYPE_NULL;
  if (pr == NULL)
    {
      return NULL;
    }

  if (pr->type == T_EVAL_TERM)
    {
      switch (pr->pe.m_eval_term.et_type)
	{
	case T_COMP_EVAL_TERM:
	  et_comp = &pr->pe.m_eval_term.et.et_comp;

	  /*
	   * et_comp->type can be DB_TYPE_NULL,
	   * in the case of positional variables
	   */
	  *single_node_type = et_comp->type;

	  if (et_comp->rel_op == R_NULL)
	    {
	      return (PR_EVAL_FNC) eval_pred_comp1;
	    }
	  else if (et_comp->rel_op == R_EXISTS)
	    {
	      return (PR_EVAL_FNC) eval_pred_comp2;
	    }

	  if (et_comp->lhs->type == TYPE_LIST_ID || et_comp->rhs->type == TYPE_LIST_ID)
	    {
	      return (PR_EVAL_FNC) eval_pred_comp3;
	    }

	  return (PR_EVAL_FNC) eval_pred_comp0;

	case T_ALSM_EVAL_TERM:
	  et_alsm = &pr->pe.m_eval_term.et.et_alsm;

	  /*
	   * et_alsm->item_type can be DB_TYPE_NULL,
	   * in the case of positional variables
	   */
	  *single_node_type = et_alsm->item_type;

	  return ((et_alsm->elemset->type != TYPE_LIST_ID)
		  ? (PR_EVAL_FNC) eval_pred_alsm4 : (PR_EVAL_FNC) eval_pred_alsm5);

	case T_LIKE_EVAL_TERM:
	  return (PR_EVAL_FNC) eval_pred_like6;

	case T_RLIKE_EVAL_TERM:
	  return (PR_EVAL_FNC) eval_pred_rlike7;

	default:
	  return NULL;
	}
    }

  /* general case */
  return (PR_EVAL_FNC) eval_pred;
}

/*
 * update_logical_result () - checks DB_LOGICAL value and qualification
 *   return: new DB_LOGICAL value and qualification (if needed)
 *   thread_p(in):
 *   ev_res(in): logical value to be checked
 *   qualification(in/out): a pointer to the qualification to be used in logical
 *			    value check. This member can be modified.
 */
DB_LOGICAL
update_logical_result (THREAD_ENTRY * thread_p, DB_LOGICAL ev_res, int *qualification)
{
  int q;

  if (ev_res == V_ERROR)
    {
      return ev_res;
    }

  if (qualification != NULL)
    {
      q = *qualification;
      if (q == QPROC_QUALIFIED)
	{
	  if (ev_res != V_TRUE)	/* V_FALSE || V_UNKNOWN */
	    {
	      return V_FALSE;	/* not qualified, continue to the next tuple */
	    }
	}
      else if (q == QPROC_NOT_QUALIFIED)
	{
	  if (ev_res != V_FALSE)	/* V_TRUE || V_UNKNOWN */
	    {
	      return V_FALSE;	/* qualified, continue to the next tuple */
	    }
	}
      else if (q == QPROC_QUALIFIED_OR_NOT)
	{
	  if (ev_res == V_TRUE)
	    {
	      *qualification = QPROC_QUALIFIED;
	    }
	  else if (ev_res == V_FALSE)
	    {
	      *qualification = QPROC_NOT_QUALIFIED;
	    }
	  else			/* V_UNKNOWN */
	    {
	      /* nop */
	      ;
	    }
	}
      else
	{			/* invalid value; the same as QPROC_QUALIFIED */
	  if (ev_res != V_TRUE)	/* V_FALSE || V_UNKNOWN */
	    {
	      return V_FALSE;	/* not qualified, continue to the next tuple */
	    }
	}
    }

  assert (ev_res != V_ERROR);
  if (ev_res == V_TRUE)
    {
      return V_TRUE;
    }
  else
    {
      /* V_FALSE || V_UNKNOWN */
      return V_FALSE;		/* not qualified, continue to the next tuple */
    }
}

/*
 * eval_mark_lazy_always_eager_regu () - if regu (recursively, through arithmetic / function operands)
 *   references an attribute of attr_cache, flag its value slot to be read eagerly even in lazy mode.
 */
static void
eval_mark_lazy_always_eager_regu (const REGU_VARIABLE * regu, HEAP_CACHE_ATTRINFO * attr_cache)
{
  REGU_VARIABLE_LIST operand;
  int i;

  if (regu == NULL)
    {
      return;
    }

  switch (regu->type)
    {
    case TYPE_ATTR_ID:
    case TYPE_SHARED_ATTR_ID:
    case TYPE_CLASS_ATTR_ID:
      if (regu->value.attr_descr.cache_attrinfo == attr_cache)
	{
	  for (i = 0; i < attr_cache->num_values; i++)
	    {
	      if (attr_cache->values[i].attrid == regu->value.attr_descr.id)
		{
		  attr_cache->values[i].lazy_always_eager = true;
		  break;
		}
	    }
	}
      break;

    case TYPE_INARITH:
    case TYPE_OUTARITH:
      if (regu->value.arithptr != NULL)
	{
	  eval_mark_lazy_always_eager_regu (regu->value.arithptr->leftptr, attr_cache);
	  eval_mark_lazy_always_eager_regu (regu->value.arithptr->rightptr, attr_cache);
	  eval_mark_lazy_always_eager_regu (regu->value.arithptr->thirdptr, attr_cache);
	}
      break;

    case TYPE_FUNC:
      if (regu->value.funcp != NULL)
	{
	  for (operand = regu->value.funcp->operand; operand != NULL; operand = operand->next)
	    {
	      eval_mark_lazy_always_eager_regu (&operand->value, attr_cache);
	    }
	}
      break;

    default:
      break;
    }
}

/*
 * eval_mark_first_term_attrs () - find the terms eval_pred () evaluates for EVERY row: it walks the
 *   right-linear AND/OR chains left to right with short-circuit, so their leftmost term always runs, and
 *   B_XOR / B_IS / B_IS_NOT have no short-circuit, so both of their sides always run. The lazy read cannot
 *   skip those terms' attributes; it would only pay the fetch_peek_dbval_slow () dispatch on them. Flag
 *   their slots to stay on the eager path (heap_attrinfo_read_dbvalues_lazy () reads them now).
 *   return: none
 *   pr(in): data filter predicate
 *   attr_cache(in/out): predicate attribute cache
 */
void
eval_mark_first_term_attrs (const PRED_EXPR * pr, HEAP_CACHE_ATTRINFO * attr_cache)
{
  while (pr != NULL)
    {
      if (pr->type == T_PRED)
	{
	  if (pr->pe.m_pred.bool_op == B_AND || pr->pe.m_pred.bool_op == B_OR)
	    {
	      /* short-circuit: only the leftmost term is evaluated on every row */
	      pr = pr->pe.m_pred.lhs;
	    }
	  else
	    {
	      /* B_XOR / B_IS / B_IS_NOT evaluate both sides on every row - mark both */
	      eval_mark_first_term_attrs (pr->pe.m_pred.lhs, attr_cache);
	      pr = pr->pe.m_pred.rhs;
	    }
	}
      else if (pr->type == T_NOT_TERM)
	{
	  pr = pr->pe.m_not_term;
	}
      else
	{
	  break;
	}
    }
  if (pr == NULL || pr->type != T_EVAL_TERM)
    {
      return;
    }

  switch (pr->pe.m_eval_term.et_type)
    {
    case T_COMP_EVAL_TERM:
      eval_mark_lazy_always_eager_regu (pr->pe.m_eval_term.et.et_comp.lhs, attr_cache);
      eval_mark_lazy_always_eager_regu (pr->pe.m_eval_term.et.et_comp.rhs, attr_cache);
      break;
    case T_ALSM_EVAL_TERM:
      eval_mark_lazy_always_eager_regu (pr->pe.m_eval_term.et.et_alsm.elem, attr_cache);
      eval_mark_lazy_always_eager_regu (pr->pe.m_eval_term.et.et_alsm.elemset, attr_cache);
      break;
    case T_LIKE_EVAL_TERM:
      eval_mark_lazy_always_eager_regu (pr->pe.m_eval_term.et.et_like.src, attr_cache);
      eval_mark_lazy_always_eager_regu (pr->pe.m_eval_term.et.et_like.pattern, attr_cache);
      eval_mark_lazy_always_eager_regu (pr->pe.m_eval_term.et.et_like.esc_char, attr_cache);
      break;
    case T_RLIKE_EVAL_TERM:
      eval_mark_lazy_always_eager_regu (pr->pe.m_eval_term.et.et_rlike.src, attr_cache);
      eval_mark_lazy_always_eager_regu (pr->pe.m_eval_term.et.et_rlike.pattern, attr_cache);
      eval_mark_lazy_always_eager_regu (pr->pe.m_eval_term.et.et_rlike.case_sensitive, attr_cache);
      break;
    default:
      break;
    }
}

/*
 * eval_disable_lazy_read () - turn the lazy predicate-column read off when this scan defers nothing
 *   return: none
 *   attr_cache(in/out): predicate attribute cache, already marked by eval_mark_first_term_attrs ()
 *
 * Note: with every predicate column read up front (all slots flagged lazy_always_eager) nothing is ever
 *   deferred, so short-circuit evaluation has nothing to skip. A single predicate column, or two conditions
 *   on the same column, is exactly this case; no measurement is needed to know it cannot pay off.
 *   Also the feature's off switch: with the enable_lazy_predicate_read system parameter off, every scan
 *   starts disabled and reads exactly as before.
 */
void
eval_disable_lazy_read (HEAP_CACHE_ATTRINFO * attr_cache)
{
  int i;

  if (attr_cache == NULL || attr_cache->num_values <= 0)
    {
      return;
    }

  if (!prm_get_bool_value (PRM_ID_ENABLE_LAZY_PREDICATE_READ))
    {
      /* the feature's off switch: behave as before this optimization */
      attr_cache->lazy_disabled = true;
      return;
    }

  for (i = 0; i < attr_cache->num_values; i++)
    {
      if (!attr_cache->values[i].lazy_always_eager)
	{
	  /* this column is deferred - the lazy read can still pay off */
	  return;
	}
    }

  attr_cache->lazy_disabled = true;
}

/*
 * eval_data_filter () -
 *   return: DB_LOGICAL (V_TRUE, V_FALSE, V_UNKNOWN or V_ERROR)
 * 	 oid(in): pointer to OID
 *   recdesp(in): pointer to RECDES (record descriptor)
 *   filterp(in): pointer to FILTER_INFO (filter information)
 *
 * Note: evaluate data filter(predicates) given as FILTER_INFO.
 */
DB_LOGICAL
eval_data_filter (THREAD_ENTRY * thread_p, OID * oid, RECDES * recdesp, HEAP_SCANCACHE * scan_cache,
		  FILTER_INFO * filterp)
{
  SCAN_PRED *scan_predp;
  SCAN_ATTRS *scan_attrsp;
  DB_LOGICAL ev_res;

  if (!filterp)
    {
      return V_TRUE;
    }

  scan_predp = filterp->scan_pred;
  scan_attrsp = filterp->scan_attrs;
  if (!scan_predp)
    {
      return V_ERROR;
    }

  if (scan_attrsp != NULL && scan_attrsp->attr_cache != NULL && scan_predp->regu_list != NULL)
    {
      /* Defer reading the predicate values: mark them and stash the record, so columns skipped by
       * short-circuit evaluation in eval_pred () below are never read. heap_attrvalue_peek_lazy () reads
       * each one on demand. The first-evaluated term's column(s) were flagged lazy_always_eager at scan
       * setup (eval_mark_first_term_attrs () in scan_start_scan ()) so they stay on the eager path. For
       * class attribute scans (recdesp == NULL) this reads everything now. */
      if (heap_attrinfo_read_dbvalues_lazy (thread_p, oid, recdesp, scan_attrsp->attr_cache) != NO_ERROR)
	{
	  return V_ERROR;
	}

      if (oid == NULL && recdesp == NULL && filterp->val_list)
	{
	  /*
	   * In the case of class attribute scan, we should fetch regu_list
	   * before pred evaluation because eval_pred*() functions do not
	   * know class OID so that TYPE_CLASSOID regu cannot be handled
	   * correctly.
	   */
	  if (fetch_val_list (thread_p, scan_predp->regu_list, filterp->val_descr, filterp->class_oid, oid, NULL, PEEK)
	      != NO_ERROR)
	    {
	      return V_ERROR;
	    }
	}
    }

  /* evaluate the predicates of the data filter */
  ev_res = V_TRUE;
  if (scan_predp->pr_eval_fnc && scan_predp->pred_expr)
    {
      ev_res = (*scan_predp->pr_eval_fnc) (thread_p, scan_predp->pred_expr, filterp->val_descr, oid);
    }

  if (oid == NULL && recdesp == NULL)
    {
      /* class attribute scan case; fetch was done before evaluation */
      return ev_res;
    }

  if (ev_res == V_TRUE && scan_predp->regu_list && filterp->val_list)
    {
      /*
       * fetch the values for the regu variable list of the data filter
       * from the cached attribute information
       */
      if (fetch_val_list (thread_p, scan_predp->regu_list, filterp->val_descr, filterp->class_oid, oid, NULL, PEEK) !=
	  NO_ERROR)
	{
	  return V_ERROR;
	}
    }

  return ev_res;
}

/*
 * eval_key_filter () -
 *   return: DB_LOGICAL (V_TRUE, V_FALSE, V_UNKNOWN or V_ERROR)
 * 	 value(in): pointer to DB_VALUE (key value)
 *   filterp(in): pointer to FILTER_INFO (filter information)
 *
 * Note: evaluate key filter(predicates) given as FILTER_INFO
 */
DB_LOGICAL
eval_key_filter (THREAD_ENTRY * thread_p, DB_VALUE * value, int prefix_size, DB_VALUE * prefix_value,
		 FILTER_INFO * filterp)
{
  DB_MIDXKEY *midxkey;
  int i, j;
  SCAN_PRED *scan_predp;
  SCAN_ATTRS *scan_attrsp;
  DB_LOGICAL ev_res;
  bool found_empty_str;
  DB_TYPE type;
  HEAP_ATTRVALUE *attrvalue;
  DB_VALUE *valp;
  int prev_j_index;
  char *prev_j_ptr;
  static bool oracle_style_empty_string = prm_get_bool_value (PRM_ID_ORACLE_STYLE_EMPTY_STRING);

  if (value == NULL)
    {
      return V_ERROR;
    }

  if (filterp == NULL)
    {
      return V_TRUE;
    }

  scan_predp = filterp->scan_pred;
  scan_attrsp = filterp->scan_attrs;
  if (scan_predp == NULL || scan_attrsp == NULL)
    {
      return V_ERROR;
    }

  if (scan_predp->regu_list == NULL)
    {
      return V_TRUE;
    }

  ev_res = V_TRUE;

  if (scan_predp->pr_eval_fnc && scan_predp->pred_expr)
    {
      if (DB_VALUE_TYPE (value) == DB_TYPE_MIDXKEY)
	{
	  int func_idx_col_id = filterp->func_idx_col_id;

	  midxkey = db_get_midxkey (value);

	  if (filterp->btree_num_attrs <= 0 || !filterp->btree_attr_ids || !midxkey)
	    {
	      return V_ERROR;
	    }

	  DB_MIDXKEY *prefix_midxkey = NULL;
	  if (!prefix_value || prefix_size <= 0)
	    {
	      prefix_size = -1;
	    }
	  else
	    {
	      prefix_midxkey = db_get_midxkey (prefix_value);
	      if (!prefix_midxkey)
		{
		  return V_ERROR;
		}
	    }

	  prev_j_index = 0;
	  prev_j_ptr = NULL;

	  if (func_idx_col_id == -1)
	    {
	      func_idx_col_id = filterp->btree_num_attrs + 1;
	    }

	  bool filled_match_idx = (filterp->matched_attid_idx_4_keyflt && filterp->matched_attid_idx_4_keyflt[0] >= 0);

	  /* for all attributes specified in the filter */
	  for (i = 0; i < scan_attrsp->num_attrs; i++)
	    {
	      if (filled_match_idx)
		{
		  j = filterp->matched_attid_idx_4_keyflt[i];
		}
	      else
		{
		  /* for the attribute ID array of the index key */
		  for (j = 0; j < filterp->btree_num_attrs; j++)
		    {
		      if (scan_attrsp->attr_ids[i] == filterp->btree_attr_ids[j])
			{
			  if (filterp->matched_attid_idx_4_keyflt)
			    {
			      filterp->matched_attid_idx_4_keyflt[i] = j;
			    }
			  break;	/* immediately exit inner-loop */
			}
		    }
		}

	      if (j < filterp->btree_num_attrs)
		{
		  /* now, found the attr */

		  attrvalue = heap_attrvalue_locate (scan_attrsp->attr_ids[i], scan_attrsp->attr_cache);
		  if (attrvalue == NULL)
		    {
		      return V_ERROR;
		    }

		  valp = &(attrvalue->dbvalue);
		  if (pr_clear_value (valp) != NO_ERROR)
		    {
		      return V_ERROR;
		    }

		  /* get j-th element value from the midxkey */
		  // TODO: Let's find a way to reuse the value of "j" instead of finding it anew every time.         
		  if (pr_midxkey_get_element_nocopy (((j < prefix_size) ? prefix_midxkey : midxkey),
						     ((j < func_idx_col_id) ? j : j + 1),
						     valp, &prev_j_index, &prev_j_ptr) != NO_ERROR)
		    {
		      return V_ERROR;
		    }

		  found_empty_str = false;
		  if (oracle_style_empty_string && db_value_is_null (valp))
		    {
		      if (valp->need_clear)
			{
			  type = DB_VALUE_DOMAIN_TYPE (valp);
			  if (QSTR_IS_ANY_CHAR_OR_BIT (type) && valp->data.ch.medium.buf != NULL)
			    {
			      /* convert NULL into Empty-string */
			      valp->domain.general_info.is_null = 0;
			      found_empty_str = true;
			    }
			}
		    }

		  if (found_empty_str)
		    {
		      /* convert NULL into Empty-string */
		      valp->domain.general_info.is_null = 0;
		    }

		  attrvalue->state = HEAP_WRITTEN_ATTRVALUE;
		}
	      else
		{
		  /*
		   * the attribute exists in key filter scan cache, but it is
		   * not a member of attributes consisting index key
		   */
		  DB_VALUE null;

		  db_make_null (&null);
		  if (heap_attrinfo_set (NULL, scan_attrsp->attr_ids[i], &null, scan_attrsp->attr_cache) != NO_ERROR)
		    {
		      return V_ERROR;
		    }
		}
	    }
	}
      else
	{
	  if (scan_attrsp->attr_ids == NULL)
	    {
	      /* defense code */
	      assert_release (false);
	      return V_ERROR;
	    }
	  attrvalue = heap_attrvalue_locate (scan_attrsp->attr_ids[0], scan_attrsp->attr_cache);
	  if (attrvalue == NULL)
	    {
	      return V_ERROR;
	    }

	  valp = &(attrvalue->dbvalue);
	  if (pr_clear_value (valp) != NO_ERROR)
	    {
	      return V_ERROR;
	    }

	  if (pr_clone_value (value, valp) != NO_ERROR)
	    {
	      return V_ERROR;
	    }

	  found_empty_str = false;
	  if (oracle_style_empty_string && db_value_is_null (valp))
	    {
	      if (valp->need_clear)
		{
		  type = DB_VALUE_DOMAIN_TYPE (valp);
		  if (QSTR_IS_ANY_CHAR_OR_BIT (type) && valp->data.ch.medium.buf != NULL)
		    {
		      /* convert NULL into Empty-string */
		      found_empty_str = true;
		    }
		}
	    }

	  if (found_empty_str)
	    {
	      /* convert NULL into Empty-string */
	      valp->domain.general_info.is_null = 0;

	      /* set single-column key val */
	      value->domain.general_info.is_null = 0;
	    }

	  attrvalue->state = HEAP_WRITTEN_ATTRVALUE;
	}

      /*
       * evaluate the predicates of the key filter
       * using the given key value
       */
      ev_res = (*scan_predp->pr_eval_fnc) (thread_p, scan_predp->pred_expr, filterp->val_descr, NULL /* obj_oid */ );
    }

  return ev_res;
}
