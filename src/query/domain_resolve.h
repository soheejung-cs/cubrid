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
 * domain_resolve.h - resolve the variable domains of an execution's domain plan before its first row, and the
 *                    accessors the row path reads the resolved domains with
 */

#ifndef _DOMAIN_RESOLVE_H_
#define _DOMAIN_RESOLVE_H_

#if !defined (SERVER_MODE) && !defined (SA_MODE)
#error Belongs to server module
#endif /* !defined (SERVER_MODE) && !defined (SA_MODE) */

#include "domain_plan.h"
#include "query_executor.h"
#include "regu_var.hpp"

// forward definitions
/*
 * [리뷰] cubxasl — 헤더가 aggregate_list_node 포인터를 쓰기 위한 네임스페이스 전방 선언 — xasl_aggregate 헤더를 끌어들이지 않게 한다.
 * develop: develop 에 없음 — domain_resolve.h 자체가 이 PR 이 신설한 파일이다.
 * 이 PR: cubxasl::aggregate_list_node 전방 선언 한 줄.
 * 바뀐 것: 신설 +4줄. 함수가 아니라 선언이다.
 */
namespace cubxasl
{
  struct aggregate_list_node;
}
struct buildlist_proc_node;
struct regu_variable_list_node;
struct val_list_node;

/* The accessors of this execution's resolved-domain state, which the row path calls: inlined at every call in a release
 * build. */
inline bool qexec_owns_resolved_index (const RESOLVED_DOMAIN_TABLE & resolved, const DOMAIN_PLAN_ITEM * item)
  __attribute__ ((ALWAYS_INLINE));
inline bool qexec_owns_node_domain (const XASL_STATE & xasl_state, const DOMAIN_PLAN_ITEM * item)
  __attribute__ ((ALWAYS_INLINE));
inline const RESOLVED_DOMAIN *qexec_late_bind_domain (const VAL_DESCR * vd, const DOMAIN_PLAN_ITEM * item)
  __attribute__ ((ALWAYS_INLINE));
inline int qexec_node_domain_index (const VAL_DESCR * vd, const DOMAIN_PLAN_ITEM * item)
  __attribute__ ((ALWAYS_INLINE));
inline TP_DOMAIN *qexec_get_node_domain (const VAL_DESCR * vd, TP_DOMAIN * compiled, const DOMAIN_PLAN_ITEM * item)
  __attribute__ ((ALWAYS_INLINE));
inline bool qexec_node_domain_is_set (const VAL_DESCR * vd, const DOMAIN_PLAN_ITEM * item)
  __attribute__ ((ALWAYS_INLINE));
inline bool qexec_node_domain_is_variable (const VAL_DESCR * vd, const DOMAIN_PLAN_ITEM * item)
  __attribute__ ((ALWAYS_INLINE));
inline bool qexec_position_domain_is_variable (const VAL_DESCR * vd, const DOMAIN_PLAN_ITEM * item)
  __attribute__ ((ALWAYS_INLINE));
inline void qexec_set_node_domain (const VAL_DESCR * vd, const DOMAIN_PLAN_ITEM * item, const TP_DOMAIN * compiled,
				   const TP_DOMAIN * domain) __attribute__ ((ALWAYS_INLINE));
inline TP_DOMAIN *qexec_interpolation_list_domain (const VAL_DESCR * vd, TP_DOMAIN * compiled,
						   const DOMAIN_PLAN_ITEM * item) __attribute__ ((ALWAYS_INLINE));
inline void qexec_take_interpolation_list_domain (const VAL_DESCR * vd, const DOMAIN_PLAN_ITEM * item,
						  const TP_DOMAIN * domain) __attribute__ ((ALWAYS_INLINE));
inline DB_TYPE qexec_node_operand_type (const VAL_DESCR * vd, DB_TYPE compiled, const DOMAIN_PLAN_ITEM * item)
  __attribute__ ((ALWAYS_INLINE));
inline void qexec_take_operand_type (const VAL_DESCR * vd, const DOMAIN_PLAN_ITEM * item, DB_TYPE compiled,
				     DB_TYPE type) __attribute__ ((ALWAYS_INLINE));
inline int qexec_item_index (const VAL_DESCR * vd, const DOMAIN_PLAN_ITEM * item) __attribute__ ((ALWAYS_INLINE));
inline const DB_VALUE *qexec_execution_temporary (THREAD_ENTRY * thread_p, const VAL_DESCR * vd, int temporary,
						  TP_VALUE_CONVERTER conv, const TP_DOMAIN * target,
						  const DB_VALUE * value) __attribute__ ((ALWAYS_INLINE));

/* Whether a plan item's resolved index is an entry of this execution's resolved domain table: an item of the plan
 * resolve_domains resolved, or, in a PX worker's copy from the leader, an item of the worker's own load of the same
 * stream, which numbers its resolved indexes alike. */
/*
 * [리뷰] qexec_owns_resolved_index — 어떤 DOMAIN_PLAN_ITEM 의 해결 인덱스를 이 실행 상태에서 읽어도 되는지 판정하는 소유권 검사 — 행 경로 인라인들의
 * assert 가 전부 이것을 부른다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: 결정표가 frozen 이고 플랜이 있고 인덱스가 표와 플랜 양쪽 범위 안일 것을 요구한 뒤, 리더 복사본(copied_from_leader)이거나 item 이 그 플랜의 items
 * 배열 안을 가리킬 때만 참.
 * 바뀐 것: 신설 +11줄. 「다른 로드의 item 으로 이 실행의 결정표를 읽지 않는다」가 이 한 조건으로 표현된다.
 */
inline bool
qexec_owns_resolved_index (const RESOLVED_DOMAIN_TABLE & resolved, const DOMAIN_PLAN_ITEM * item)
{
  const DOMAIN_PLAN *plan = resolved.plan;
  if (!resolved.frozen || plan == NULL || item->resolved_index < 0 || item->resolved_index >= resolved.n_resolved
      || item->resolved_index >= plan->n_resolved)
    {
      return false;
    }
  return resolved.copied_from_leader || (item >= plan->items && item < plan->items + plan->n_items);
}

/* Whether a plan item's execution domain is this execution's: an item of the plan resolve_domains resolved, or, in a PX
 * worker's copy from the leader copy, an item of the worker's own load of the same stream, which numbers its execution
 * domains alike. */
/*
 * [리뷰] qexec_owns_node_domain — 노드 실행 도메인 슬롯(node_domain_index)을 이 실행 상태에서 읽고 써도 되는지 판정한다 —
 * qexec_node_domain_index 의 assert 가 부른다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: 플랜이 있고 인덱스가 1..n_node_domains 범위이며, 리더 복사본이거나 item 이 그 플랜의 items 안일 때 참. frozen 은 보지 않는다(실행 도메인은 게이트
 * 이후에도 노드가 채운다).
 * 바뀐 것: 신설 +9줄. qexec_owns_resolved_index 와 달리 frozen 조건이 빠진 것이 의도적 차이인데, 코드에 설명이 없다.
 */
inline bool
qexec_owns_node_domain (const XASL_STATE & xasl_state, const DOMAIN_PLAN_ITEM * item)
{
  const RESOLVED_DOMAIN_TABLE & resolved = xasl_state.resolved_domain;
  const DOMAIN_PLAN *plan = resolved.plan;
  return plan != NULL && item->node_domain_index > 0
    && item->node_domain_index <= xasl_state.domain_execution.n_node_domains
    && (resolved.copied_from_leader || (item >= plan->items && item < plan->items + plan->n_items));
}

/* resolve_domains' resolution for a late-binding node of the tree this execution loaded, or NULL when resolve_domains
 * did not resolve it (a node resolve_domains does not resolve, a node it left unresolved). fetch reads it in place of a
 * row-time late binding; the debug cross-checks compare against it. */
/*
 * [리뷰] qexec_late_bind_domain — 행 경로가 늦은 바인딩 노드의 해결 도메인을 꺼내는 읽기 전용 접근자 — fetch/evaluator 가 값 계산 직전에 부르고, 결정이
 * 없으면 NULL 을 돌려 컴파일 도메인을 쓰게 한다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 에서는 같은 자리에서 tp_domain_resolve_value 류 호출이 매 행 일어났다.
 * 이 PR: DOMAIN_PLAN_LATE_BIND 플래그가 없으면 바로 NULL. 있으면 소유권을 assert 로만 확인하고 domains[resolved_index] 를 바로 읽는다 — 검사
 * 대신 단언이라 행당 비용이 사실상 배열 한 번 읽기다.
 * 바뀐 것: 신설 +14줄. 릴리스 빌드에서는 소유권이 검사되지 않는다는 것이 명시적 설계 선택이다(주석 116).
 */
inline const RESOLVED_DOMAIN *
qexec_late_bind_domain (const VAL_DESCR * vd, const DOMAIN_PLAN_ITEM * item)
{
  /* a node resolve_domains does not resolve answers before the descriptor's resolved-domain state is read */
  if (vd == NULL || item == NULL || !(item->flags & DOMAIN_PLAN_LATE_BIND))
    {
      return NULL;
    }
  /* every read comes after resolve_domains frozen its resolutions, with the descriptor of the execution that loaded the
   * node or a PX worker's copy of its state: what an execution never changes is asserted, not tested at every row */
  assert (vd->xasl_state != NULL && qexec_owns_resolved_index (vd->xasl_state->resolved_domain, item));
  const RESOLVED_DOMAIN *resolved_domain = &vd->xasl_state->resolved_domain.domains[item->resolved_index];
  return resolved_domain->domain != NULL ? resolved_domain : NULL;
}

/* The index of a node's execution domain in this execution's state, or -1 when it has none: an item without one - most
 * nodes, at every row - or no descriptor. The descriptor comes first: a temporary regu fetched without one
 * (qdata_get_interpolation_function_result) leaves its position's item pointer unset. A node with an execution domain
 * is read with the descriptor of the execution that loaded it, or with a PX worker's copy of its state, whose own load
 * numbers the execution domains as the plan does: that never changes during an execution, so it is asserted, not tested
 * at every row. */
/*
 * [리뷰] qexec_node_domain_index — 노드의 실행 도메인 슬롯 번호(1기준)를 0기준 배열 첨자로 바꿔 주는 공통 입구 — 아래의 get/set/is_set/보간/피연산자 타입
 * 접근자가 전부 여기를 거친다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: vd/item 이 없거나 슬롯이 0 이면 -1(= 실행 도메인 없음). 있으면 소유권을 assert 하고 index-1 을 돌려준다.
 * 바뀐 것: 신설 +10줄. 1기준 저장 + 0 을 「없음」으로 쓰는 규약이 여기 한 곳에 모여 있다.
 */
inline int
qexec_node_domain_index (const VAL_DESCR * vd, const DOMAIN_PLAN_ITEM * item)
{
  if (vd == NULL || item == NULL || item->node_domain_index <= 0)
    {
      return -1;
    }
  assert (vd->xasl_state != NULL && qexec_owns_node_domain (*vd->xasl_state, item));
  return item->node_domain_index - 1;
}

/*
 * qexec_get_node_domain () - the domain a plan node has now in this execution
 *   return: the domain the node took in this execution, or its compiled domain
 *   compiled(in): the node's domain field, as the stream loaded it; the execution never writes it
 *   item(in): the node's plan item
 */
/*
 * [리뷰] qexec_get_node_domain — 행 경로가 노드의 실제 도메인을 얻는 자리 — 게이트가 실행 도메인을 채웠으면 그것을, 아니면 컴파일 도메인을 돌려준다. arch 요약 기준
 * 호출자 52곳으로 이 PR 에서 가장 넓게 퍼진 접근자다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 에서는 각 호출 지점이 regu->domain 을 직접 읽거나 그 자리에서 도메인을 다시 계산했다.
 * 이 PR: 슬롯이 없거나 비어 있으면 compiled 를 그대로 돌려준다 — 즉 기본 동작이 develop 과 같고, 게이트가 결정한 노드에서만 달라진다.
 * 바뀐 것: 신설 +11줄. 분기 두 개와 배열 한 번 읽기뿐이라 행당 비용이 작다.
 */
inline TP_DOMAIN *
qexec_get_node_domain (const VAL_DESCR * vd, TP_DOMAIN * compiled, const DOMAIN_PLAN_ITEM * item)
{
  const int node_domain_index = qexec_node_domain_index (vd, item);
  if (node_domain_index < 0)
    {
      return compiled;
    }
  const TP_DOMAIN *node_domain = vd->xasl_state->domain_execution.node_domains[node_domain_index];
  return node_domain != NULL ? (TP_DOMAIN *) node_domain : compiled;
}

/* Whether a node with an execution domain took its domain in this execution (qexec_set_node_domain): the inline
 * fetch_peek_dbval () peeks a variable regu directly from then on */
/*
 * [리뷰] qexec_node_domain_is_set — 이 노드에 실행 도메인이 실제로 채워졌는지만 묻는다 — 아래 두 is_variable 판정과 여러 호출부의 분기 조건으로 쓰인다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: 슬롯이 있고 node_domains[idx] 가 NULL 이 아니면 참.
 * 바뀐 것: 신설 +6줄.
 */
inline bool
qexec_node_domain_is_set (const VAL_DESCR * vd, const DOMAIN_PLAN_ITEM * item)
{
  const int node_domain_index = qexec_node_domain_index (vd, item);
  return node_domain_index >= 0 && vd->xasl_state->domain_execution.node_domains[node_domain_index] != NULL;
}

/*
 * qexec_node_domain_is_variable () - whether a plan node's domain is still variable in this execution
 *   return: its compiled domain is variable - the load's answer to VARIABLE || collation flag != NORMAL,
 *	     DOMAIN_PLAN_VARIABLE - and the node took no domain yet
 *
 * The execution comparisons that asked the pair condition of the node's domain at every row, which the execution wrote
 * a resolution into, ask this: the plan item and the execution domain answer it, the node never changes.
 */
/*
 * [리뷰] qexec_node_domain_is_variable — 「컴파일 때 가변으로 표시됐고 실행 도메인도 아직 없는 노드」인지 판정한다 — 호출부가 이 노드의 값을 아직 믿으면 안 된다고
 * 알 때 쓴다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: DOMAIN_PLAN_VARIABLE 플래그가 있고 qexec_node_domain_is_set 이 거짓일 때만 참.
 * 바뀐 것: 신설 +5줄.
 */
inline bool
qexec_node_domain_is_variable (const VAL_DESCR * vd, const DOMAIN_PLAN_ITEM * item)
{
  return item != NULL && (item->flags & DOMAIN_PLAN_VARIABLE) && !qexec_node_domain_is_set (vd, item);
}

/* The same for a list position's value descriptor, which shares the position's execution domain: its own compiled
 * domain is variable (DOMAIN_PLAN_VARIABLE_POSITION) and the position took no domain yet */
/*
 * [리뷰] qexec_position_domain_is_variable — 위의 판정을 bind 위치 쪽에 대해 한 것 — DOMAIN_PLAN_VARIABLE_POSITION 플래그를 본다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: VARIABLE_POSITION 플래그가 있고 실행 도메인이 아직 없으면 참.
 * 바뀐 것: 신설 +5줄. 앞 함수와 플래그 한 개만 다른 쌍둥이다.
 */
inline bool
qexec_position_domain_is_variable (const VAL_DESCR * vd, const DOMAIN_PLAN_ITEM * item)
{
  return item != NULL && (item->flags & DOMAIN_PLAN_VARIABLE_POSITION) && !qexec_node_domain_is_set (vd, item);
}

/*
 * qexec_set_node_domain () - a plan node takes a domain for the rest of this execution as its execution domain; the
 *   node keeps its compiled domain, so the plan stays what the stream loaded
 *   compiled(in): the node's domain field; a node without an execution domain keeps it, and then takes nothing else
 *   domain(in): the domain; NULL takes the compiled one back
 *
 * Only the execution's owner thread writes its execution domains.
 */
/*
 * [리뷰] qexec_set_node_domain — 노드가 자기 실행 도메인을 적는 유일한 자리 — 컴파일 도메인과 같으면 NULL 로 저장해 「바뀐 것 없음」을 표현한다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: 슬롯이 없는 노드에 대해서는 「도메인을 바꿀 수 없다」를 assert 로 확인하고 조용히 반환한다. 슬롯이 있으면 domain==compiled 일 때 NULL, 아니면 domain
 * 을 쓴다.
 * 바뀐 것: 신설 +13줄. NULL 저장 규약 덕에 qexec_get_node_domain 이 분기 하나로 끝난다.
 */
inline void
qexec_set_node_domain (const VAL_DESCR * vd, const DOMAIN_PLAN_ITEM * item, const TP_DOMAIN * compiled,
		       const TP_DOMAIN * domain)
{
  const int node_domain_index = qexec_node_domain_index (vd, item);
  if (node_domain_index < 0)
    {
      /* a node the load gave no execution domain has a domain its execution cannot change */
      assert (domain == NULL || domain == compiled);
      return;
    }
  vd->xasl_state->domain_execution.node_domains[node_domain_index] = domain == compiled ? NULL : domain;
}

/* The domain a MEDIAN / PERCENTILE list holds and its sort key sorts in this execution
 * (qexec_setup_interpolation_list): the key's compiled domain until the setup gives the function its type. The key
 * shares the function's item, so the list domain has execution domains of its own. Only a MEDIAN / PERCENTILE
 * aggregate has one: the load numbers those first. */
/*
 * [리뷰] qexec_interpolation_list_domain — MEDIAN/PERCENTILE 의 리스트 도메인을 꺼낸다 — 게이트가 정한 것이 있으면 그것을, 없으면 컴파일 도메인을
 * 돌려준다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: 슬롯 번호가 보간 그룹 범위 안이라는 것을 assert 하고 interpolation_list_domains[idx] 를 읽는다.
 * 바뀐 것: 신설 +11줄. 로드가 보간 노드를 0번 그룹으로 먼저 번호 매긴 것(stx_build_domain_plan 4739~4751)에 의존하며, 그 범위 밖 item 으로 불리면 릴리스
 * 빌드에서 같은 블록의 다른 구역을 읽는다 — assert 로만 지켜지는 계약.
 * [지적 C4-04]
 */
inline TP_DOMAIN *
qexec_interpolation_list_domain (const VAL_DESCR * vd, TP_DOMAIN * compiled, const DOMAIN_PLAN_ITEM * item)
{
  const int node_domain_index = qexec_node_domain_index (vd, item);
  assert (node_domain_index < 0 || node_domain_index < vd->xasl_state->domain_execution.n_interpolation_list_domains);
  if (node_domain_index < 0 || vd->xasl_state->domain_execution.interpolation_list_domains[node_domain_index] == NULL)
    {
      return compiled;
    }
  return (TP_DOMAIN *) vd->xasl_state->domain_execution.interpolation_list_domains[node_domain_index];
}

/*
 * [리뷰] qexec_take_interpolation_list_domain — 보간 리스트 도메인을 기록하는 쪽 — 집계/분석 실행이 리스트 도메인을 정했을 때 슬롯에 넣는다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: 슬롯이 있어야 한다고 assert 한 뒤, 그래도 음수면 아무것도 하지 않는다.
 * 바뀐 것: 신설 +10줄. assert 와 if 가 같은 조건을 두 번 보는 형태라, 릴리스에서는 기록이 조용히 사라진다.
 */
inline void
qexec_take_interpolation_list_domain (const VAL_DESCR * vd, const DOMAIN_PLAN_ITEM * item, const TP_DOMAIN * domain)
{
  const int node_domain_index = qexec_node_domain_index (vd, item);
  assert (node_domain_index >= 0 && node_domain_index < vd->xasl_state->domain_execution.n_interpolation_list_domains);
  if (node_domain_index >= 0)
    {
      vd->xasl_state->domain_execution.interpolation_list_domains[node_domain_index] = domain;
    }
}

/* An aggregate's or an analytic function's operand type now in this execution: the one it took, or
 * its compiled opr_dbtype. The load numbers the functions' execution domains first, so theirs are the operand types'
 * indexes. */
/*
 * [리뷰] qexec_node_operand_type — 게이트/실행이 정한 피연산자 타입을 꺼낸다 — 정해진 것이 없으면 컴파일 타입을 그대로 돌려준다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: operand_types[idx] 는 -1 이 「컴파일 타입 그대로」를 뜻하는 센티넬이고(할당 때 0xff 로 채움), 그 외 값이면 DB_TYPE 으로 캐스팅해 돌려준다.
 * 바뀐 것: 신설 +11줄. 슬롯 범위(n_operand_types)는 assert 로만 지켜진다 — 보간 접근자와 같은 형태의 암묵 계약.
 */
inline DB_TYPE
qexec_node_operand_type (const VAL_DESCR * vd, DB_TYPE compiled, const DOMAIN_PLAN_ITEM * item)
{
  const int node_domain_index = qexec_node_domain_index (vd, item);
  assert (node_domain_index < 0 || node_domain_index < vd->xasl_state->domain_execution.n_operand_types);
  if (node_domain_index < 0 || vd->xasl_state->domain_execution.operand_types[node_domain_index] < 0)
    {
      return compiled;
    }
  return (DB_TYPE) vd->xasl_state->domain_execution.operand_types[node_domain_index];
}

/*
 * [리뷰] qexec_take_operand_type — 피연산자 타입을 기록하는 쪽 — 컴파일 타입과 같으면 -1 을 써 「바뀐 것 없음」으로 둔다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: 슬롯이 없는 노드에 대해서는 type==compiled 를 assert 하고 반환한다.
 * 바뀐 것: 신설 +12줄. qexec_set_node_domain 과 같은 「같으면 센티넬」 규약이다.
 */
inline void
qexec_take_operand_type (const VAL_DESCR * vd, const DOMAIN_PLAN_ITEM * item, DB_TYPE compiled, DB_TYPE type)
{
  const int node_domain_index = qexec_node_domain_index (vd, item);
  if (node_domain_index < 0)
    {
      assert (type == compiled);
      return;
    }
  assert (node_domain_index < vd->xasl_state->domain_execution.n_operand_types);
  vd->xasl_state->domain_execution.operand_types[node_domain_index] = type == compiled ? -1 : (int) type;
}

extern const TP_DOMAIN *qexec_resolved_domain (const VAL_DESCR * vd, const DOMAIN_PLAN_ITEM * item);
extern const TP_DOMAIN *qexec_null_bind_domain (const VAL_DESCR * vd, const DOMAIN_PLAN_ITEM * item);
extern const TP_DOMAIN *qexec_plan_domain (const VAL_DESCR * vd, const DOMAIN_PLAN_ITEM * item);
extern const TP_DOMAIN *qexec_consumer_domain (const VAL_DESCR * vd, const TP_DOMAIN * compiled,
					       const DOMAIN_PLAN_ITEM * item);
extern int qexec_domain_unresolved (const VAL_DESCR * vd, const DOMAIN_PLAN_ITEM * item, const TP_DOMAIN * compiled);

/* A plan item's index in this execution's plan, which the unresolved-domain check (execution) names; -1 for an item of
 * another load */
/*
 * [리뷰] qexec_item_index — DOMAIN_PLAN_ITEM 포인터를 플랜 안 첨자로 되돌린다 — 에러 메시지와 디버깅에서 노드를 번호로 가리킬 때 쓴다. 플랜 밖 포인터면 -1.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: vd·xasl_state·plan 을 전부 NULL 검사한 뒤 items 배열 범위 안인지 포인터 비교로 확인한다.
 * 바뀐 것: 신설 +7줄. 다른 접근자들과 달리 assert 가 아니라 실제 검사라, 에러 경로에서 안전하게 부를 수 있다.
 */
inline int
qexec_item_index (const VAL_DESCR * vd, const DOMAIN_PLAN_ITEM * item)
{
  const DOMAIN_PLAN *plan = vd != NULL && vd->xasl_state != NULL ? vd->xasl_state->resolved_domain.plan : NULL;
  return item != NULL && plan != NULL && item >= plan->items && item < plan->items + plan->n_items
    ? (int) (item - plan->items) : -1;
}

extern const TP_DOMAIN *qexec_value_domain (const VAL_DESCR * vd, const regu_variable_node * regu);
extern void qexec_enter_temporary_scope (const VAL_DESCR * vd, const val_list_node * val_list);
extern const DB_VALUE *qexec_convert_execution_temporary (THREAD_ENTRY * thread_p, XASL_STATE * xasl_state,
							  DOMAIN_EXECUTION_TEMPORARY * entry, TP_VALUE_CONVERTER conv,
							  const TP_DOMAIN * target, const DB_VALUE * value);

/*
 * qexec_execution_temporary () - the value a scope fixes, converted once in the scope: a comparison
 *   side, an arithmetic operand or the value a SUM or AVG adds that is a constant (the execution's scope) or a
 *   correlated value (its block's scope)
 *   return: the converted value; NULL when the row converts it - the scope was not entered, or the conversion failed
 *	     (the outcome follows from the row's own conversion)
 *   temporary(in): 1 + its domain_execution.temporaries index (a plan item's, a resolved comparison's or an accumulator
 *	     domain's), not 0
 *   conv(in), target(in): the converter the row would run, and its target: the execution's, the same at every read
 *   value(in): the value, not NULL
 *
 * The first read in the scope's generation converts the value (qexec_convert_execution_temporary). Every other read is
 * one comparison of generations and the pointer that read left, which is NULL in a scope never entered: no owner,
 * converter or target is compared on the row. Only the thread that owns the execution's state reads it.
 */
/*
 * [리뷰] qexec_execution_temporary — 행 경로의 변환값 캐시 조회 — 같은 스코프 세대 안에서 이미 변환해 둔 값이 있으면 그대로 돌려주고, 없으면
 * qexec_convert_execution_temporary 로 한 번 변환한다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 에서는 같은 변환이 행마다 다시 일어났다.
 * 이 PR: entry->generation 과 scope_generations[entry->scope] 가 같으면 캐시 적중. 디버그 빌드에서는 같은 변환기·같은 목표 도메인인지까지 assert
 * 한다. 소유 스레드 확인도 assert 로만 한다.
 * 바뀐 것: 신설 +15줄. 이 PR 의 반복 변환 제거가 실제로 돈을 버는 자리다 — 적중 시 비교 두 번으로 끝난다.
 * [지적 C4-03]
 */
inline const DB_VALUE *
qexec_execution_temporary (THREAD_ENTRY * thread_p, const VAL_DESCR * vd, int temporary, TP_VALUE_CONVERTER conv,
			   const TP_DOMAIN * target, const DB_VALUE * value)
{
  assert (vd != NULL && vd->xasl_state != NULL && temporary > 0);
  DOMAIN_EXECUTION_STATE & execution = vd->xasl_state->domain_execution;
  assert (temporary <= execution.n_temporaries && vd->xasl_state->resolved_domain.owner == thread_p);
  DOMAIN_EXECUTION_TEMPORARY *entry = &execution.temporaries[temporary - 1];
  if (entry->generation == execution.scope_generations[entry->scope])
    {
      assert (entry->generation == 0 || (entry->conv == conv && entry->target == target));
      return entry->converted;
    }
  return qexec_convert_execution_temporary (thread_p, vd->xasl_state, entry, conv, target, value);
}

extern int qexec_session_variable_type_error (const DB_VALUE * name, const TP_DOMAIN * type, const TP_DOMAIN * other);

/* Read-only execution view. Peek callers retain the existing no-write
 * contract even though their public DB_VALUE ** output is not const. The row path calls it: inlined at every call
 * in a release build. */
inline const DB_VALUE *REGU_RESOLVED_VALUE (const VAL_DESCR * vd, const REGU_VARIABLE * regu)
  __attribute__ ((ALWAYS_INLINE));

/*
 * [리뷰] REGU_RESOLVED_VALUE — regu 가 읽을 bind 값의 주소를 돌려주는 인라인 — 플랜이 배정한 참조 번호(plan_item->ref)로 vd->dbval_ptr 에서
 * 바로 찾는다. 같은 위치라도 도메인이 다르면 다른 ref 를 받으므로, 행은 자기 몫의 값만 본다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 에서는 같은 자리에서 regu->value.val_pos 로 직접 dbval_ptr 을 찾았다.
 * 이 PR: 결정표가 frozen 인지, plan_item 과 ref 가 유효한지, ref 가 n_vals 범위인지 셋 다 assert 한 뒤 포인터 산술 한 번으로 끝낸다.
 * 바뀐 것: 신설 +8줄(팩은 함수명을 `?` 로 잡았지만 소스에서는 REGU_RESOLVED_VALUE 다). 세 조건 모두 릴리스 빌드에서는 검사되지 않는다.
 */
inline const DB_VALUE *
REGU_RESOLVED_VALUE (const VAL_DESCR * vd, const REGU_VARIABLE * regu)
{
  assert (vd->xasl_state->resolved_domain.frozen);
  assert (regu->plan_item != NULL && regu->plan_item->ref >= 0);
  assert (regu->plan_item->ref < vd->xasl_state->resolved_domain.n_vals);
  return vd->dbval_ptr + regu->plan_item->ref;
}

extern int qexec_resolve_domains (THREAD_ENTRY * thread_p, xasl_node * xasl, xasl_state * xasl_state);
extern void qexec_clear_resolved_domains (THREAD_ENTRY * thread_p, xasl_state * xasl_state);
extern int qexec_copy_resolved_domains (THREAD_ENTRY * thread_p, const xasl_state * from, xasl_state * to,
					bool own_load);
extern int qexec_plan_sort_list_domains (THREAD_ENTRY * thread_p, const VAL_DESCR * vd, SORT_LIST * order_list,
					 SORT_LIST ** resolved_list);
extern int qexec_plan_group_by_domains (THREAD_ENTRY * thread_p, const VAL_DESCR * vd, buildlist_proc_node * buildlist,
					SORT_LIST ** resolved_groupby);
extern void qexec_finish_group_by_domains (const VAL_DESCR * vd, buildlist_proc_node * buildlist);
extern void qexec_setup_hash_aggregate_lists (const VAL_DESCR * vd, buildlist_proc_node * buildlist);
extern int qexec_setup_aggregate_domains (cubxasl::aggregate_list_node * agg_list, const VAL_DESCR * vd, int *resolved);
extern int qexec_aggregate_first_values (THREAD_ENTRY * thread_p, cubxasl::aggregate_list_node * agg_list,
					 VAL_DESCR * vd, QFILE_TUPLE_RECORD * tplrec,
					 regu_variable_list_node * regu_list, int *resolved);
extern void qexec_type_accumulator_outputs (const VAL_DESCR * vd, xasl_node * xasl);
extern int qexec_setup_parallel_aggregates (xasl_node * xasl, const VAL_DESCR * vd, int *resolved);
extern int qexec_parallel_aggregate_first_values (THREAD_ENTRY * thread_p, xasl_node * xasl, VAL_DESCR * vd,
						  int *resolved);

#endif /* _DOMAIN_RESOLVE_H_ */
