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

#include "config.h"
#include "domain_plan.h"
#include "dbtype.h"
#include "error_manager.h"
#include "object_primitive.h"
#include "xasl.h"
#include "xasl_aggregate.hpp"
#include "xasl_analytic.hpp"
#include "xasl_predicate.hpp"
#include "xasl_stream.hpp"
#include "xasl_unpack_info.hpp"
#include "query_hash_join.h"
#include "fetch.h"
#include "system_parameter.h"
#include <climits>
#include <cstdlib>
#include <cstring>

// XXX: SHOULD BE THE LAST INCLUDE HEADER
#include "memory_wrapper.hpp"

/* The unresolved-domain check (load): every item the compiler left without a type is a variable POS, a late-binding
 * node or an alias of one; anything else refuses the load with ER_QPROC_DOMAIN_UNRESOLVED. A derived consumer (a value
 * pointer, a list position, a sort key, an accumulator) reads its producer: the producer's resolved index (ALIAS) or
 * its domain. The collation axis: a string the compiler typed but whose collation the values give (LEAVE, ENFORCE) is a
 * variable POS recording its bound value's domain, a collation late-binding node resolve_domains resolves from its
 * operands, or a consumer reading its producer. */

/* Temporary load entries are freed before publishing the plan. No load entry, owner
 * link or traversal scratch survives in the hot arrays. Shared XASLs are marked
 * on entry; expression items are appended after their operands (producer order). */

/* What the resolution pass resolves for a load entry after the walk. */
enum DOMAIN_LOAD_KIND
{
  DOMAIN_LOAD_LEAF,		/* a bind, a literal, an attribute, a compiled node: nothing to derive */
  DOMAIN_LOAD_CONSUMER,		/* a value pointer, a list position, a set-operation column: reads its producer */
  DOMAIN_LOAD_NODE,		/* a node the compiler left without a type: a late-binding node when every operand
				 * is known */
  DOMAIN_LOAD_ARITH_REGU,	/* the regu wrapping an arithmetic node: carries that node's answer */
  DOMAIN_LOAD_FIXED_AGG		/* a compiled aggregate or analytic: accumulator derived once */
};

struct DOMAIN_LOAD_ENTRY
{
  DOMAIN_LOAD_ENTRY *next;
  DOMAIN_PLAN_ITEM item;
  DOMAIN_PLAN_ITEM_COLD cold;
  DOMAIN_PLAN_ITEM **owner;
  int index;
  DB_VALUE *output[2];
  REGU_VARIABLE *regu;
  DOMAIN_LOAD_ENTRY *alias;
  unsigned char kind;		/* DOMAIN_LOAD_KIND */
  unsigned char state;		/* resolution pass: 0 not started, 1 in progress, 2 done */
  bool known;			/* after resolution: resolve_domains knows this operand's type (a resolved index, a
				 * value or a domain) */
  bool literal_value;		/* a bind or a literal: resolve_domains reads its value */
  bool follows_producer;	/* after resolution: this entry carries its producer's answer (a link source goes
				 * through it to the producer, a bind's value included) */
  bool needs_node_domain;	/* the node gets an execution domain (domain_give_node_domain) */
  bool needs_operand_type;	/* an aggregate or analytic function: its execution also records the operand type it
				 * evaluates with (domain_execution.operand_types) */
  bool needs_list_domain;	/* a MEDIAN / PERCENTILE aggregate: and the domain its list holds
				 * (domain_execution.interpolation_list_domains) */
  bool variable;		/* its compiled domain is variable: DOMAIN_PLAN_VARIABLE once published */
  bool variable_position;	/* a list position whose pos_descr.dom is variable: DOMAIN_PLAN_VARIABLE_POSITION */
  bool row_invariant;		/* no row changes its value: a constant, or a branch or collection node over such
				 * operands - what a constant branch's condition reads */
  DOMAIN_LOAD_ENTRY *producer;	/* CONSUMER / ARITH_REGU: whose answer this entry reads */
  /* NODE / FIXED_AGG: the operands in operand order, and the literal a TYPE_DBVAL operand carries; the inline arrays
   * hold three, a function with more operands allocates its own */
  DOMAIN_PLAN_ITEM **link;
  const DB_VALUE **literal;
  DOMAIN_PLAN_ITEM *link_inline[3];
  const DB_VALUE *literal_inline[3];
  int n_link;
  bool elt_index;		/* ELT: link[0] is the index, a bind or a literal (DOMAIN_LATE_BIND_LINK) */
  const TP_DOMAIN *elt_index_cast;	/* ELT: the cast the compiler wraps that index in (DOMAIN_LATE_BIND_LINK) */
  const TP_DOMAIN *consumer;
  const TP_DOMAIN *argument;	/* FIXED_AGG: the argument's compiled domain when it is fixed (DOMAIN_LATE_BIND_LINK) */
  DOMAIN_PLAN_ITEM *self_owner;	/* owner storage of a synthetic entry (a set-operation column) */
  /* T_ADD, T_SUB, T_MUL, T_DIV, a SUM or AVG: the operands whose operand coercion the execution may convert once per
   * scope ([1]: the value an aggregate adds), and for a correlated one the block whose scans fix it */
  REGU_VARIABLE *temporary_operand[2];
  XASL_NODE *temporary_scope[2];
};
struct DOMAIN_LOAD_BINDING
{
  DOMAIN_LOAD_BINDING *next;
  DOMAIN_PLAN_ITEM **owner;
  DOMAIN_PLAN_ITEM *target;
};
/* An ALL/SOME term the walk met: the list column its item compares with, bound to the published item. */
struct DOMAIN_LOAD_ELEMENT_TERM
{
  DOMAIN_LOAD_ELEMENT_TERM *next;
  ALSM_EVAL_TERM *term;
  DOMAIN_PLAN_ITEM *list_column;
  int constant_branch;		/* the constant branch around the term */
  bool key_range;		/* a term of an index scan's key range */
};
/* A comparison of two values outside a predicate term the walk met: FIELD, NULLIF, LEAST and GREATEST over
 * their operands, LIMIT's row count against 0, a merge join's column pair. A side is a regu, a list column (bound to
 * the published item) or a literal no regu holds; the published resolved comparison goes to owner. */
struct DOMAIN_LOAD_COMPARE_PAIR
{
  DOMAIN_LOAD_COMPARE_PAIR *next;
  REGU_VARIABLE *regu[2];
  DOMAIN_PLAN_ITEM *column[2];
  const DB_VALUE *literal[2];
  const DOMAIN_COMPARE_PLAN **owner;
};
/* A set-operation or CTE list column, unified from its branches, made once per (list, column). */
struct DOMAIN_LOAD_LIST_COLUMN
{
  DOMAIN_LOAD_LIST_COLUMN *next;
  const XASL_NODE *xasl;
  int pos;
  DOMAIN_PLAN_ITEM *item;
};
struct DOMAIN_LOAD_CONTEXT
{
  THREAD_ENTRY *thread_p;
  DOMAIN_PLAN *plan;
  DOMAIN_LOAD_ENTRY *head;
  DOMAIN_LOAD_ENTRY *tail;
  DOMAIN_LOAD_BINDING *bindings;
  bool failed;
  XASL_NODE *block;
  /* the list the TYPE_POSITION regus being walked read: its producer XASL, or its producer columns */
  XASL_NODE *position_source;
  REGU_VARIABLE_LIST position_columns;
  DOMAIN_LOAD_LIST_COLUMN *list_columns;
  DOMAIN_LOAD_ENTRY **late_bind_order;	/* late-binding nodes in resolution order (producers first) */
  int n_late_bind_order;
  int max_late_bind_order;
  COMP_EVAL_TERM **compare_terms;	/* the comparison terms met, in walk order */
  int *compare_term_constant_branches;	/* [max_compare_terms] the constant branch around each term */
  XASL_NODE **compare_term_scopes;	/* [2 * max_compare_terms] per side, the block whose scans fix a correlated side
					 * (domain_outer_scope); NULL */
  bool *compare_term_ranges;	/* [max_compare_terms] a term of an index scan's key range */
  bool in_key_range;		/* the walk is in an index scan's key range predicate, where_range */
  int n_compare_terms;
  int max_compare_terms;
  DOMAIN_LOAD_ELEMENT_TERM *element_terms;	/* the ALL/SOME terms met, last first */
  int n_element_terms;
  DOMAIN_LOAD_COMPARE_PAIR *compare_pairs;	/* the comparisons outside a term met, last first */
  int n_compare_pairs;
  INDX_INFO **indexes;		/* the index scans met, in walk order */
  int *index_constant_branches;	/* [max_indexes] the constant branch around each scan */
  int n_indexes;
  int max_indexes;
  ARITH_TYPE **defines;		/* the session variable assignments met (T_DEFINE_VARIABLE) */
  int n_defines;
  int max_defines;
  /* the branches taken by a constant condition: the innermost one around the walk's position, and all of them,
   * outer ones first */
  int constant_branch;
  DOMAIN_PLAN_CONSTANT_BRANCH *constant_branches;
  int n_constant_branches;
  int max_constant_branches;
  bool constant_branches_ambiguous;	/* a node met under two constant branches (domain_note_met_again) */
  XASL_NODE **blocks;		/* the blocks walked, and the constant branch each was first walked below */
  int *block_constant_branches;
  int n_blocks;
  int max_blocks;
  /* the blocks whose execution holds the walk's position, the outermost first, the block walked last: a value
   * of one of them but the last is fixed while the last one's scan runs */
  XASL_NODE **ancestors;
  int n_ancestors;
  int max_ancestors;
  /* the values converted once per scope published so far (plan->n_temporaries): each one's scope, and the block whose
   * scans fix a correlated one (NULL for a constant) */
  int *temporary_scopes;
  XASL_NODE **temporary_blocks;
  int max_temporaries;
};

static void domain_walk_xasl (DOMAIN_LOAD_CONTEXT *, XASL_NODE *);
static void *domain_plan_alloc (THREAD_ENTRY * thread_p, int count, size_t size);
static void domain_walk_pred (DOMAIN_LOAD_CONTEXT *, PRED_EXPR *);
static void domain_walk_regu (DOMAIN_LOAD_CONTEXT *, REGU_VARIABLE *, DOMAIN_CTX = DOMAIN_CTX_FUNC_ARG);
static OUTPTR_LIST *domain_block_output (XASL_NODE * xasl);
static DOMAIN_PLAN_ITEM *domain_list_column (DOMAIN_LOAD_CONTEXT * ctx, XASL_NODE * xasl, int pos);
static void domain_add_define (DOMAIN_LOAD_CONTEXT * ctx, ARITH_TYPE * define);
static XASL_NODE *domain_outer_scope (const DOMAIN_LOAD_CONTEXT * ctx, const REGU_VARIABLE * regu);

/* The type axis only: the collation of a character result is merged at resolve_domains. */
/*
 * [리뷰] domain_type_is_fixed — TP_DOMAIN 이 컴파일 시점에 타입이 정해진 것인지(= DB_TYPE_VARIABLE 이 아닌지) 판정하는 술어. 로드·해소 전 과정에서
 * '이 항목은 더 볼 필요 없다'의 기준으로 쓰인다.
 * develop: develop 에 없음 — 이 PR 이 신설(domain_plan.c 파일 자체가 새 파일이고, develop 전체에 domain_* 심볼이 없다).
 * 이 PR: 도메인 NULL 이거나 VARIABLE 이면 false. domain_plan_validate 의 게이트 조건, domain_resolve_node 의 compiled 판정,
 * domain_fixed_operand 의 변환기 조회 조건이 모두 이 한 술어를 공유한다.
 * 바뀐 것: 신설(+5줄).
 */
static bool
domain_type_is_fixed (const TP_DOMAIN * domain)
{
  return domain != NULL && TP_DOMAIN_TYPE (domain) != DB_TYPE_VARIABLE;
}

/* A typed character domain whose collation the compiler left to the values (LEAVE) or enforced over an operand it
 * could not type (ENFORCE): the values give it, so resolve_domains resolves it. */
/*
 * [리뷰] domain_character_is_variable — 문자열 도메인인데 collation 이 아직 값에 달려 있는지(TP_DOMAIN_COLL_NORMAL 이 아닌
 * LEAVE/ENFORCE) 판정한다. 타입 축과 분리된 'collation 축' 판정의 유일한 입구다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: 타입은 컴파일러가 정했지만 collation 은 값이 주는 경우를 true 로 돌려, 그런 항목을 DOMAIN_PLAN_LATE_BIND_COLLATION 으로 표시하게 한다.
 * domain_plan_validate 는 이 표시 없이 collation 이 미확정인 항목을 로드 거부 사유로 쓴다.
 * 바뀐 것: 신설(+6줄).
 */
static bool
domain_character_is_variable (const TP_DOMAIN * domain)
{
  return domain != NULL && TP_IS_CHAR_TYPE (TP_DOMAIN_TYPE (domain))
    && TP_DOMAIN_COLLATION_FLAG (domain) != TP_DOMAIN_COLL_NORMAL;
}

/* The load entry an item lives in: every item is an entry's embedded item until the plan is published. */
/*
 * [리뷰] domain_load_entry_of — 공개될 DOMAIN_PLAN_ITEM 포인터에서 그것을 품은 로드 전용 DOMAIN_LOAD_ENTRY 를 offsetof 로 역산한다. 로드
 * 중에만 유효한 스크래치(producer/link/row_invariant 등)에 접근하는 유일한 통로다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: item == NULL 이면 NULL. 로드가 끝나면 LOAD_ENTRY 는 해제되고 핫 배열에는 ITEM 만 남으므로, 이 역산은 로드 단계 안에서만 유효하다.
 * 바뀐 것: 신설(+6줄).
 */
static DOMAIN_LOAD_ENTRY *
domain_load_entry_of (const DOMAIN_PLAN_ITEM * item)
{
  return item == NULL ? NULL
    : (DOMAIN_LOAD_ENTRY *) ((char *) const_cast < DOMAIN_PLAN_ITEM * >(item) - offsetof (DOMAIN_LOAD_ENTRY, item));
}

/*
 * domain_give_node_domain () - the node of an item gets an execution domain
 *   variable(in): the node's compiled domain is variable (domain_is_variable): DOMAIN_PLAN_VARIABLE, set when the plan
 *	       is published so that it does not change which value pointers share their producer's item
 *
 * The domain an execution gives a node - a resolved domain the node reads at its first computation or its consumer's
 * setup - lives in the execution domain, never in the node: the plan stays what the stream loaded. An aggregate or an
 * analytic function gets one whether or not its domain is variable: its execution also records the operand type it
 * evaluates with.
 */
/*
 * [리뷰] domain_give_node_domain — 이 항목에 실행 도메인 슬롯(domain_execution.node_domains 의 한 칸)이 필요하다고 표시한다.
 * stx_build_domain_plan 이 나중에 이 표시만 보고 node_domain_index 를 번호 매긴다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: needs_node_domain=true 로 하고 variable 플래그는 OR 로 누적한다(여러 경로에서 같은 항목에 대해 불려도 한 번이라도 variable 이면
 * variable).
 * 바뀐 것: 신설(+11줄).
 */
static void
domain_give_node_domain (DOMAIN_PLAN_ITEM * item, bool variable)
{
  if (item == NULL)
    {
      return;
    }
  DOMAIN_LOAD_ENTRY *load_entry = domain_load_entry_of (item);
  load_entry->needs_node_domain = true;
  load_entry->variable = load_entry->variable || variable;
}

/* The resolver context of a late-binding operator node. */
/*
 * [리뷰] domain_late_bind_context — 지연 바인딩 노드로 확정된 연산자를 실행 시 해소 규칙 문맥(DOMAIN_CTX_ARITH / COMMON_VALUE /
 * FUNC_ARG)으로 사상한다. domain_resolve_node 가 노드를 LATE_BIND 로 확정할 때 cold.ctx 를 이 값으로 덮어쓴다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: 산술 11종은 ARITH, NVL/COALESCE/NULLIF/LEAST/GREATEST 등 7종은 COMMON_VALUE, 나머지는 FUNC_ARG. 컴파일 시
 * 문맥(COMPARE·ASSIGN 등)과 달리 '실행이 피연산자들로부터 타입을 합칠 때 쓸 규칙'을 고른다.
 * 바뀐 것: 신설(+29줄, switch 하나).
 */
static DOMAIN_CTX
domain_late_bind_context (OPERATOR_TYPE opcode)
{
  switch (opcode)
    {
    case T_ADD:
    case T_SUB:
    case T_MUL:
    case T_DIV:
    case T_MOD:
    case T_UNMINUS:
    case T_ABS:
    case T_FLOOR:
    case T_CEIL:
    case T_ROUND:
    case T_TRUNC:
      return DOMAIN_CTX_ARITH;
    case T_NVL:
    case T_NVL2:
    case T_IFNULL:
    case T_COALESCE:
    case T_NULLIF:
    case T_LEAST:
    case T_GREATEST:
      return DOMAIN_CTX_COMMON_VALUE;
    default:
      return DOMAIN_CTX_FUNC_ARG;
    }
}

/* Records the operands a node the compiler left without a type is resolved from (resolution pass). A load entry links
 * three operands in place; a function with more links an array of its own, freed with the load entries. */
/*
 * [리뷰] domain_set_links — 지연 바인딩 노드의 피연산자 목록을 LOAD_ENTRY 에 적는다. 피연산자 regu 들에서 plan_item 포인터(link)와 TYPE_DBVAL
 * 리터럴 포인터(literal)를 뽑고 consumer 도메인을 기록한다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: 피연산자가 3개 이하면 inline 배열, 넘으면 db_private_alloc 로 link/literal 두 배열을 한 번 할당한다. 한쪽만 성공하면 둘 다 해제하고
 * ctx->failed. plan_item 이 NULL 인 피연산자는 건너뛰므로 n_link 가 n_operands 보다 작을 수 있다.
 * 바뀐 것: 신설(+35줄).
 * [지적 C3-04]
 */
static void
domain_set_links (DOMAIN_LOAD_CONTEXT * ctx, DOMAIN_LOAD_ENTRY * load_entry, REGU_VARIABLE * const *operands,
		  int n_operands, const TP_DOMAIN * consumer)
{
  load_entry->n_link = 0;
  if (n_operands > 3 && load_entry->link == load_entry->link_inline)
    {
      DOMAIN_PLAN_ITEM **link = (DOMAIN_PLAN_ITEM **) db_private_alloc (ctx->thread_p, n_operands * sizeof (*link));
      const DB_VALUE **literal = (const DB_VALUE **) db_private_alloc (ctx->thread_p, n_operands * sizeof (*literal));
      if (link == NULL || literal == NULL)
	{
	  if (link != NULL)
	    {
	      db_private_free (ctx->thread_p, link);
	    }
	  if (literal != NULL)
	    {
	      db_private_free (ctx->thread_p, literal);
	    }
	  ctx->failed = true;
	  return;
	}
      load_entry->link = link;
      load_entry->literal = literal;
    }
  for (int i = 0; i < n_operands; i++)
    {
      if (operands[i] != NULL && operands[i]->plan_item != NULL)
	{
	  load_entry->literal[load_entry->n_link] = operands[i]->type == TYPE_DBVAL ? &operands[i]->value.dbval : NULL;
	  load_entry->link[load_entry->n_link++] = operands[i]->plan_item;
	}
    }
  load_entry->consumer = consumer;
}

/* Makes a resolved node a late-binding node: resolve_domains resolves it into its own resolved domain table entry once
 * per execution, after every operand (the resolution pass appends it after its producers). */
/*
 * [리뷰] domain_mark_late_bind_node — 항목을 '실행 전 게이트가 해소할 노드'로 확정한다 — DOMAIN_PLAN_LATE_BIND 플래그, plan->n_resolved
 * 에서 받은 resolved_index, fixed.domain=NULL, 그리고 해소 순서 배열(late_bind_order)에 등록.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: late_bind_order 는 16에서 시작해 2배씩 db_private_realloc 한다. 호출 시점이 domain_resolve_record 의 깊이 우선 해소 안이므로 배열에
 * 들어가는 순서가 곧 '생산자 먼저' 순서가 되고, 실행 전 게이트는 그 순서대로 한 번에 훑는다.
 * 바뀐 것: 신설(+21줄).
 */
static void
domain_mark_late_bind_node (DOMAIN_LOAD_CONTEXT * ctx, DOMAIN_LOAD_ENTRY * load_entry)
{
  if (ctx->n_late_bind_order == ctx->max_late_bind_order)
    {
      int max = ctx->max_late_bind_order == 0 ? 16 : ctx->max_late_bind_order * 2;
      DOMAIN_LOAD_ENTRY **order =
	(DOMAIN_LOAD_ENTRY **) db_private_realloc (ctx->thread_p, ctx->late_bind_order, max * sizeof (*order));
      if (order == NULL)
	{
	  ctx->failed = true;
	  return;
	}
      ctx->late_bind_order = order;
      ctx->max_late_bind_order = max;
    }
  load_entry->item.flags |= DOMAIN_PLAN_LATE_BIND;
  load_entry->item.resolved_index = ctx->plan->n_resolved++;
  load_entry->item.fixed.domain = NULL;
  ctx->late_bind_order[ctx->n_late_bind_order++] = load_entry;
}

/*
 * [리뷰] domain_add_item — GATE 슬롯 하나(DOMAIN_PLAN_ITEM)를 만들어 소유 포인터(*owner)에 달고 로드 연결 리스트 꼬리에 잇는다. 워크 전체에서 '이
 * regu/arith/aggregate 에 대응하는 항목'을 만드는 유일한 생성기다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: *owner 가 이미 차 있으면 기존 것을 돌려 멱등하다. index 는 plan->n_items 순번, ref/resolved_index 는 -1, operand_class 가
 * OPERAND_CONST 면 row_invariant 초기값 true. COMPARE/KEY_ELEM/ASSIGN 문맥이면 DOMAIN_PLAN_CONSUMER_CONVERTS 를 켠다.
 * ctx->tail 을 갱신하므로 호출 직후의 tail 이 방금 만든 항목이다.
 * 바뀐 것: 신설(+44줄).
 */
static DOMAIN_PLAN_ITEM *
domain_add_item (DOMAIN_LOAD_CONTEXT * ctx, DOMAIN_PLAN_ITEM ** owner, const TP_DOMAIN * domain,
		 DOMAIN_OPERAND_CLASS operand_class, DOMAIN_CTX context, int opcode)
{
  if (ctx->failed || *owner != NULL)
    {
      return *owner;
    }
  DOMAIN_LOAD_ENTRY *load_entry = (DOMAIN_LOAD_ENTRY *) db_private_alloc (ctx->thread_p, sizeof (*load_entry));
  if (load_entry == NULL)
    {
      ctx->failed = true;
      return NULL;
    }
  memset (load_entry, 0, sizeof (*load_entry));
  load_entry->link = load_entry->link_inline;
  load_entry->literal = load_entry->literal_inline;
  load_entry->owner = owner;
  load_entry->index = ctx->plan->n_items++;
  load_entry->item.resolved_index = -1;
  load_entry->item.ref = -1;
  load_entry->item.operand_class = operand_class;
  load_entry->row_invariant = operand_class == OPERAND_CONST;
  load_entry->item.fixed.domain = domain;
  if (context == DOMAIN_CTX_COMPARE || context == DOMAIN_CTX_KEY_ELEM || context == DOMAIN_CTX_ASSIGN)
    {
      load_entry->item.flags |= DOMAIN_PLAN_CONSUMER_CONVERTS;
    }
  load_entry->cold.val_pos = -1;
  load_entry->cold.ctx = context;
  load_entry->cold.opcode = opcode;
  load_entry->cold.constant_branch = ctx->constant_branch;
  if (ctx->tail == NULL)
    {
      ctx->head = load_entry;
    }
  else
    {
      ctx->tail->next = load_entry;
    }
  ctx->tail = load_entry;
  *owner = &load_entry->item;
  return *owner;
}

/*
 * domain_regu_is_row_invariant () - whether no row changes the value of a regu the walk met: a bind, a
 *   literal, a constant expression, or a CASE, IF, DECODE, predicate or collection node over such operands. A branch
 *   constant branch's condition reads only these; the cache class is another question - a fetch computes a branch
 *   node every time, so its class stays NON_CACHEABLE.
 */
/*
 * [리뷰] domain_regu_is_row_invariant — regu 가 행마다 값이 바뀌지 않는지(상수 분기 판정의 기본 단위) 묻는다. plan_item 을 통해 로드 엔트리의
 * row_invariant 를 읽는다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: plan_item 이 아직 없으면(아직 안 걸은 regu) false — 즉 보수적으로 '행마다 바뀐다'로 본다.
 * 바뀐 것: 신설(+5줄).
 */
static bool
domain_regu_is_row_invariant (const REGU_VARIABLE * regu)
{
  return regu != NULL && regu->plan_item != NULL && domain_load_entry_of (regu->plan_item)->row_invariant;
}

/* Whether no row changes a predicate the walk met: every value each of its terms compares is so. */
/*
 * [리뷰] domain_pred_is_row_invariant — 술어 트리 전체가 행과 무관한지 재귀로 판정한다. CASE/IF 의 선택자나 블록의 if_pred 가 상수 분기(constant
 * branch)를 만들 자격이 있는지의 기준.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: T_PRED 는 양쪽 AND, NOT 은 하나, EVAL_TERM 은 COMP/ALSM/LIKE 세 종류만 피연산자 regu 들로 판정하고 나머지(RLIKE 포함)는 false.
 * RLIKE 를 뺀 이유가 주석에 있다 — 컴파일된 패턴을 항에 들고 있어 게이트가 평가하지 않는다.
 * 바뀐 것: 신설(+38줄).
 */
static bool
domain_pred_is_row_invariant (const PRED_EXPR * pred)
{
  if (pred == NULL)
    {
      return false;
    }
  switch (pred->type)
    {
    case T_PRED:
      return domain_pred_is_row_invariant (pred->pe.m_pred.lhs) && domain_pred_is_row_invariant (pred->pe.m_pred.rhs);
    case T_NOT_TERM:
      return domain_pred_is_row_invariant (pred->pe.m_not_term);
    case T_EVAL_TERM:
      {
	const EVAL_TERM *term = &pred->pe.m_eval_term;
	switch (term->et_type)
	  {
	  case T_COMP_EVAL_TERM:
	    return domain_regu_is_row_invariant (term->et.et_comp.lhs)
	      && (term->et.et_comp.rhs == NULL || domain_regu_is_row_invariant (term->et.et_comp.rhs));
	  case T_ALSM_EVAL_TERM:
	    return domain_regu_is_row_invariant (term->et.et_alsm.elem)
	      && domain_regu_is_row_invariant (term->et.et_alsm.elemset);
	  case T_LIKE_EVAL_TERM:
	    return domain_regu_is_row_invariant (term->et.et_like.src)
	      && domain_regu_is_row_invariant (term->et.et_like.pattern)
	      && (term->et.et_like.esc_char == NULL || domain_regu_is_row_invariant (term->et.et_like.esc_char));
	  default:
	    /* an RLIKE term keeps its compiled pattern in the term, which resolve_domains does not evaluate (it is no
	     * selector) */
	    return false;
	  }
      }
    default:
      return false;
    }
}

/*
 * domain_push_constant_branch () - a branch the walk enters whose condition is a constant becomes the innermost
 *   constant branch of what lies below it; the caller restores ctx->constant branch when it leaves the branch
 */
/*
 * [리뷰] domain_push_constant_branch — '이 조건이 거짓이면 아래 것들은 실행되지 않는다'는 상수 분기를 ctx 스택에 밀어 넣는다. 이후 만들어지는 항목들은
 * cold.constant_branch 에 이 번호를 달고, 게이트는 도달 불가능한 분기의 해소 실패를 에러로 올리지 않는다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: 8에서 시작해 2배씩 realloc. parent 로 바깥 분기를 가리켜 트리를 이루고, ctx->constant_branch 는 현재 위치의 가장 안쪽 분기를 가리킨다. 실패 시
 * ctx->failed 만 세우고 조용히 돌아온다.
 * 바뀐 것: 신설(+27줄).
 */
static void
domain_push_constant_branch (DOMAIN_LOAD_CONTEXT * ctx, DOMAIN_CONSTANT_BRANCH_KIND kind, const void *selector)
{
  if (ctx->failed)
    {
      return;
    }
  if (ctx->n_constant_branches == ctx->max_constant_branches)
    {
      const int max = ctx->max_constant_branches == 0 ? 8 : ctx->max_constant_branches * 2;
      DOMAIN_PLAN_CONSTANT_BRANCH *constant_branches =
	(DOMAIN_PLAN_CONSTANT_BRANCH *) db_private_realloc (ctx->thread_p, ctx->constant_branches,
							    max * sizeof (*constant_branches));
      if (constant_branches == NULL)
	{
	  ctx->failed = true;
	  return;
	}
      ctx->constant_branches = constant_branches;
      ctx->max_constant_branches = max;
    }
  DOMAIN_PLAN_CONSTANT_BRANCH *constant_branch = &ctx->constant_branches[ctx->n_constant_branches];
  constant_branch->selector = selector;
  constant_branch->parent = ctx->constant_branch;
  constant_branch->kind = (unsigned char) kind;
  ctx->constant_branch = ctx->n_constant_branches++;
}

/* Whether constant branch outer is inner or one of the constant branches around it (-1, no constant branch, is around
 * every constant branch). */
/*
 * [리뷰] domain_constant_branch_encloses — 상수 분기 outer 가 inner 를 감싸는지 parent 사슬을 따라가며 본다. 같은 항을 두 번 만났을 때 두 번째
 * 자리가 첫 번째의 분기 안인지 확인하는 데 쓴다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: inner 사슬에서 outer 를 찾으면 true, 못 찾으면 `outer < 0`(= outer 가 '분기 없음'이면 무엇이든 감싼다)을 돌려준다.
 * 바뀐 것: 신설(+12줄).
 */
static bool
domain_constant_branch_encloses (const DOMAIN_LOAD_CONTEXT * ctx, int outer, int inner)
{
  for (; inner >= 0; inner = ctx->constant_branches[inner].parent)
    {
      if (inner == outer)
	{
	  return true;
	}
    }
  return outer < 0;
}

/* A node the walk meets again, first met below constant branch: its constant branch chain holds for this place too when
 * the first place's constant branch is around this one; otherwise the node is also reached another way than its chain
 * says, and the plan keeps no constant branches (every failure is resolve_domains' error). */
/*
 * [리뷰] domain_note_met_again — 이미 만든 항목/블록/인덱스를 워크가 다시 만났을 때, 지금 위치의 분기가 처음 만났을 때의 분기 안이 아니면 '분기 정보가 모호하다'고
 * ctx 에 표시한다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: constant_branches_ambiguous 가 서면 stx_build_domain_plan 이 플랜의 상수 분기 정보를 전부 -1 로 지워 보수적으로 동작한다(4890행대).
 * 바뀐 것: 신설(+8줄).
 */
static void
domain_note_met_again (DOMAIN_LOAD_CONTEXT * ctx, int constant_branch)
{
  if (!domain_constant_branch_encloses (ctx, constant_branch, ctx->constant_branch))
    {
      ctx->constant_branches_ambiguous = true;
    }
}

/*
 * [리뷰] domain_bind_item — 워크 중 XASL 안의 보조 소유 포인터(pos_descr.plan_item, 비교쌍의 column 등)에 이미 만든 항목을 연결하고, 그 연결을
 * bindings 리스트에 기록한다. 공개 단계에서 임시 item 주소를 최종 배열 주소로 고쳐 쓰기 위한 추적이다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: *owner 가 비어 있고 target 이 있을 때만 DOMAIN_LOAD_BINDING 하나를 할당해 ctx->bindings 머리에 붙이고 *owner=target. 할당 실패는
 * ctx->failed.
 * 바뀐 것: 신설(+19줄).
 */
static void
domain_bind_item (DOMAIN_LOAD_CONTEXT * ctx, DOMAIN_PLAN_ITEM ** owner, DOMAIN_PLAN_ITEM * target)
{
  if (*owner != NULL || target == NULL || ctx->failed)
    {
      return;
    }
  DOMAIN_LOAD_BINDING *binding = (DOMAIN_LOAD_BINDING *) db_private_alloc (ctx->thread_p, sizeof (*binding));
  if (binding == NULL)
    {
      ctx->failed = true;
      return;
    }
  binding->owner = owner;
  binding->target = target;
  binding->next = ctx->bindings;
  ctx->bindings = binding;
  *owner = target;
}

/*
 * domain_add_compare_pair () - a comparison of two values outside a predicate term: its resolved comparison is
 *   published with the terms' (domain_plan_add_compares) into *owner
 *   regu(in), column(in), literal(in): per side, the regu, the list column item or the literal it compares; one each
 */
/*
 * [리뷰] domain_add_compare_pair — 술어 항 밖의 두 값 비교(FIELD·NULLIF·LEAST/GREATEST·LIMIT 의 0 비교·머지조인 컬럼쌍)를
 * ctx->compare_pairs 에 적어 둔다. 나중에 domain_plan_add_compares 가 이것들을 DOMAIN_COMPARE_PLAN 으로 공개한다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: *owner 가 이미 차 있으면 멱등 반환. 한 쪽은 regu / 리스트 컬럼 / 어떤 regu 도 들지 않는 리터럴 중 하나이고, column 쪽은 domain_bind_item
 * 으로 연결해 공개 시 주소가 고쳐진다.
 * 바뀐 것: 신설(+26줄).
 */
static void
domain_add_compare_pair (DOMAIN_LOAD_CONTEXT * ctx, REGU_VARIABLE * const regu[2], DOMAIN_PLAN_ITEM * const column[2],
			 const DB_VALUE * const literal[2], const DOMAIN_COMPARE_PLAN ** owner)
{
  if (ctx->failed || *owner != NULL)
    {
      return;
    }
  DOMAIN_LOAD_COMPARE_PAIR *pair = (DOMAIN_LOAD_COMPARE_PAIR *) db_private_alloc (ctx->thread_p, sizeof (*pair));
  if (pair == NULL)
    {
      ctx->failed = true;
      return;
    }
  for (int side = 0; side < 2; side++)
    {
      pair->regu[side] = regu[side];
      pair->column[side] = NULL;
      pair->literal[side] = literal[side];
      domain_bind_item (ctx, &pair->column[side], column[side]);
    }
  pair->owner = owner;
  pair->next = ctx->compare_pairs;
  ctx->compare_pairs = pair;
  ctx->n_compare_pairs++;
}

/* The two resolved comparison entries of a FIELD, NULLIF, LEAST or GREATEST node, in the plan's arena: the node's
 * item carries them; NULL for any other operator */
/*
 * [리뷰] domain_arith_compares — NULLIF/LEAST/GREATEST/FIELD 네 연산자에 대해, 그 노드가 들 비교 계획 슬롯 2칸을 XASL 언팩
 * 버퍼(stx_alloc_struct)에 미리 잡아 준다. 다른 연산자면 NULL.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: stx_alloc_struct 로 잡으므로 플랜과 수명이 같다(로드 임시 메모리가 아니다). 두 칸 모두 NULL 초기화하고, 할당 실패는 호출자의 failed 플래그로 전달한다.
 * 바뀐 것: 신설(+23줄).
 */
static const DOMAIN_COMPARE_PLAN **
domain_arith_compares (THREAD_ENTRY * thread_p, OPERATOR_TYPE opcode, bool * failed)
{
  switch (opcode)
    {
    case T_NULLIF:
    case T_LEAST:
    case T_GREATEST:
    case T_FIELD:
      break;
    default:
      return NULL;
    }
  const DOMAIN_COMPARE_PLAN **compares =
    (const DOMAIN_COMPARE_PLAN **) stx_alloc_struct (thread_p, (int) (2 * sizeof (*compares)));
  if (compares == NULL)
    {
      *failed = true;
      return NULL;
    }
  compares[0] = compares[1] = NULL;
  return compares;
}

/* A comparison of two regus outside a predicate term. */
/*
 * [리뷰] domain_add_regu_compare — 두 regu 사이의 비교 하나를 compare pair 로 등록하는 얇은 어댑터. domain_walk_arith 가
 * FIELD/NULLIF/LEAST/GREATEST 노드에서 부른다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: 한쪽이라도 NULL 이면 아무것도 하지 않고, 아니면 column/literal 을 비운 채 domain_add_compare_pair 로 넘긴다.
 * 바뀐 것: 신설(+13줄).
 */
static void
domain_add_regu_compare (DOMAIN_LOAD_CONTEXT * ctx, REGU_VARIABLE * lhs, REGU_VARIABLE * rhs,
			 const DOMAIN_COMPARE_PLAN ** owner)
{
  if (lhs == NULL || rhs == NULL)
    {
      return;
    }
  REGU_VARIABLE *const regu[2] = { lhs, rhs };
  DOMAIN_PLAN_ITEM *const column[2] = { NULL, NULL };
  const DB_VALUE *const literal[2] = { NULL, NULL };
  domain_add_compare_pair (ctx, regu, column, literal, owner);
}

/*
 * [리뷰] domain_merge_class — 피연산자들의 캐시 등급(OPERAND_CONST < CORRELATED < ROW < NON_CACHEABLE)을 합쳐 상위 노드 등급을 정한다.
 * 이 등급이 '게이트가 한 번 계산하고 끝낼 수 있는 값인가'를 가른다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: NON_CACHEABLE 이 하나라도 있으면 NON_CACHEABLE, 다음 ROW, 다음 CORRELATED, 아니면 CONST. rhs 가 NULL 이면 lhs 그대로.
 * 바뀐 것: 신설(+18줄).
 */
static DOMAIN_OPERAND_CLASS
domain_merge_class (DOMAIN_OPERAND_CLASS lhs, const DOMAIN_PLAN_ITEM * rhs)
{
  if (rhs == NULL)
    {
      return lhs;
    }
  DOMAIN_OPERAND_CLASS other = (DOMAIN_OPERAND_CLASS) rhs->operand_class;
  if (lhs == OPERAND_NON_CACHEABLE || other == OPERAND_NON_CACHEABLE)
    {
      return OPERAND_NON_CACHEABLE;
    }
  if (lhs == OPERAND_ROW || other == OPERAND_ROW)
    {
      return OPERAND_ROW;
    }
  return lhs == OPERAND_CORRELATED || other == OPERAND_CORRELATED ? OPERAND_CORRELATED : OPERAND_CONST;
}

/*
 * [리뷰] domain_non_cacheable_operator — 값이 매 평가마다 달라질 수 있는 연산자(INCR/DECR, 시퀀스, 분기 노드, 세션 변수, 난수, UUID, SLEEP,
 * 통계 등 21종)를 열거한다. 이 목록에 들면 항목은 OPERAND_NON_CACHEABLE 로 시작한다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: domain_walk_arith 가 노드의 초기 등급을 정할 때, 그리고 row_invariant 판정에서 쓴다. CASE/DECODE/IF/PREDICATE 는 여기 들어 있지만
 * domain_branch_operator 가 따로 걸러 row_invariant 는 될 수 있게 한다.
 * 바뀐 것: 신설(+31줄, switch 하나).
 */
static bool
domain_non_cacheable_operator (OPERATOR_TYPE opcode)
{
  switch (opcode)
    {
    case T_INCR:
    case T_DECR:
    case T_CURRENT_VALUE:
    case T_NEXT_VALUE:
    case T_CASE:
    case T_DECODE:
    case T_IF:
    case T_PREDICATE:
    case T_ROW_COUNT:
    case T_LAST_INSERT_ID:
    case T_EVALUATE_VARIABLE:
    case T_DEFINE_VARIABLE:
    case T_RAND:
    case T_RANDOM:
    case T_DRAND:
    case T_DRANDOM:
    case T_SYS_GUID:
    case T_UUID:
    case T_EXEC_STATS:
    case T_TRACE_STATS:
    case T_SLEEP:
      return true;
    default:
      return false;
    }
}

/* The non-cacheable operators a fetch computes every time only because it does not analyze their predicate: over
 * operands no row changes, no row changes them either. */
/*
 * [리뷰] domain_branch_operator — CASE/DECODE/IF/PREDICATE 넷을 가려낸다. 이 넷은 non-cacheable 이면서도 '피연산자가 모두 행 불변이면 결과도
 * 행 불변'이라는 예외를 받는다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: domain_walk_arith 의 row_invariant 계산에서 domain_non_cacheable_operator 의 결과를 되돌리는 예외 조건으로만 쓰인다.
 * 바뀐 것: 신설(+5줄).
 */
static bool
domain_branch_operator (OPERATOR_TYPE opcode)
{
  return opcode == T_CASE || opcode == T_DECODE || opcode == T_IF || opcode == T_PREDICATE;
}

/* A fetch caches a function over constant operands only for these (the FETCH_ALL_CONST resolution of TYPE_FUNC);
 * every other function computes each time it is fetched, so it is no constant resolve_domains evaluates */
/*
 * [리뷰] domain_function_caches — fetch 가 결과를 캐시해도 되는 함수(JSON 계열 22종, REGEXP 5종, INSERT_SUBSTRING, ELT)를 열거한다.
 * 여기 들면 TYPE_FUNC regu 의 등급이 OPERAND_CONST 로 시작하고 행 불변 후보가 된다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: domain_walk_regu 의 TYPE_FUNC 가지에서 등급 초기값과 row_invariant 초기값 두 군데에 쓰인다. 목록 밖 함수는 OPERAND_ROW 로 시작한다.
 * 바뀐 것: 신설(+40줄, switch 하나).
 */
static bool
domain_function_caches (FUNC_CODE ftype)
{
  switch (ftype)
    {
    case F_JSON_ARRAY:
    case F_JSON_ARRAY_APPEND:
    case F_JSON_ARRAY_INSERT:
    case F_JSON_CONTAINS:
    case F_JSON_CONTAINS_PATH:
    case F_JSON_DEPTH:
    case F_JSON_EXTRACT:
    case F_JSON_GET_ALL_PATHS:
    case F_JSON_KEYS:
    case F_JSON_INSERT:
    case F_JSON_LENGTH:
    case F_JSON_MERGE:
    case F_JSON_MERGE_PATCH:
    case F_JSON_OBJECT:
    case F_JSON_PRETTY:
    case F_JSON_QUOTE:
    case F_JSON_REMOVE:
    case F_JSON_REPLACE:
    case F_JSON_SEARCH:
    case F_JSON_SET:
    case F_JSON_TYPE:
    case F_JSON_UNQUOTE:
    case F_JSON_VALID:
    case F_REGEXP_COUNT:
    case F_REGEXP_INSTR:
    case F_REGEXP_LIKE:
    case F_REGEXP_REPLACE:
    case F_REGEXP_SUBSTR:
    case F_INSERT_SUBSTRING:
    case F_ELT:
      return true;
    default:
      return false;
    }
}

/* A BENCHMARK target and a stored procedure's arguments are computed again at every call: fetch marks them not
 * constant through regu_variable_node::map_regu (arithmetic left and right operands, function operands, procedure
 * arguments, value and regu lists), so none of them is a constant resolve_domains evaluates once */
/*
 * [리뷰] domain_force_row — regu 서브트리를 훑어 OPERAND_CONST 로 표시돼 있던 노드들을 OPERAND_ROW 로 되돌린다. 게이트가 미리 한 번 계산해 두면 안
 * 되는 자리(인덱스 키 리밋, 저장 프로시저 인자, BENCHMARK 의 대상)에 쓴다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: 노드(INARITH/OUTARITH/FUNC/SP)만 등급을 내리고 그 아래의 bind·리터럴은 상수로 남긴다는 규칙이 주석에 명시돼 있다. 재귀로 arith 의 left/right,
 * FUNC/SP 의 인자, REGUVAL_LIST·REGU_VAR_LIST 의 원소까지 내려간다.
 * 바뀐 것: 신설(+57줄).
 */
static void
domain_force_row (REGU_VARIABLE * regu)
{
  if (regu == NULL)
    {
      return;
    }
  /* only the nodes fetch marks: a bind or a literal under them stays a constant */
  const bool node = regu->type == TYPE_INARITH || regu->type == TYPE_OUTARITH || regu->type == TYPE_FUNC
    || regu->type == TYPE_SP;
  if (node && regu->plan_item != NULL && regu->plan_item->operand_class == OPERAND_CONST)
    {
      regu->plan_item->operand_class = OPERAND_ROW;
    }
  switch (regu->type)
    {
    case TYPE_INARITH:
    case TYPE_OUTARITH:
      if (regu->value.arithptr != NULL)
	{
	  DOMAIN_PLAN_ITEM *arith = regu->value.arithptr->plan_item;
	  if (arith != NULL && arith->operand_class == OPERAND_CONST)
	    {
	      arith->operand_class = OPERAND_ROW;
	    }
	  domain_force_row (regu->value.arithptr->leftptr);
	  domain_force_row (regu->value.arithptr->rightptr);
	}
      break;
    case TYPE_FUNC:
      for (REGU_VARIABLE_LIST op = regu->value.funcp->operand; op != NULL; op = op->next)
	{
	  domain_force_row (&op->value);
	}
      break;
    case TYPE_SP:
      for (REGU_VARIABLE_LIST arg = regu->value.sp_ptr->args; arg != NULL; arg = arg->next)
	{
	  domain_force_row (&arg->value);
	}
      break;
    case TYPE_REGUVAL_LIST:
      for (REGU_VALUE_ITEM * item = regu->value.reguval_list->regu_list; item != NULL; item = item->next)
	{
	  domain_force_row (item->value);
	}
      break;
    case TYPE_REGU_VAR_LIST:
      for (REGU_VARIABLE_LIST node = regu->value.regu_var_list; node != NULL; node = node->next)
	{
	  domain_force_row (&node->value);
	}
      break;
    default:
      break;
    }
}

/*
 * [리뷰] domain_fixed_operand — 항목의 i 번째 피연산자에 대해 '컴파일 시점에 확정 가능한' 목표 도메인과 변환 함수(fixed.conv[i])를 적는다. 실행은 이 변환기를
 * 그냥 호출만 한다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: source·target 둘 다 타입이 확정이고 둘 다 collation_flag != TP_DOMAIN_COLL_LEAVE 일 때만 tp_value_find_converter 로
 * 변환기를 미리 찾는다. 하나라도 미확정이면 operand_domain 만 적고 conv 는 비운다 — 그 경우는 실행 전 게이트의 몫이다.
 * 바뀐 것: 신설(+16줄).
 */
static void
domain_fixed_operand (DOMAIN_PLAN_ITEM * item, int i, const TP_DOMAIN * source,
		      const TP_DOMAIN * target, DOMAIN_CTX mode)
{
  if (item == NULL)
    {
      return;
    }
  item->fixed.operand_domain[i] = target;
  /* both types known, and neither collation left to the values (LEAVE) */
  if (domain_type_is_fixed (source) && source->collation_flag != TP_DOMAIN_COLL_LEAVE
      && domain_type_is_fixed (target) && target->collation_flag != TP_DOMAIN_COLL_LEAVE)
    {
      item->fixed.conv[i] = tp_value_find_converter (TP_DOMAIN_TYPE (source), target, domain_convert_mode (mode));
    }
}

/* The operators qdata_*_dbval took through an operand coercion by their values' types; the resolver's type rules is its
 * one rule, and the plan carries it. */
/*
 * [리뷰] domain_operand_coercion_operator — 피연산자 강제변환(operand coercion) 규칙이 적용되는 산술 연산자 넷(ADD/SUB/MUL/DIV)인지 본다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: domain_walk_arith 와 스트림 로드 쪽(domain_stream_walk_arith) 양쪽이 같은 술어를 공유해, 두 로드 경로가 같은 연산자 집합을 보게 한다.
 * 바뀐 것: 신설(+5줄).
 */
static bool
domain_operand_coercion_operator (OPERATOR_TYPE opcode)
{
  return opcode == T_ADD || opcode == T_SUB || opcode == T_MUL || opcode == T_DIV;
}

/*
 * domain_plan_operand_coercion () - the operand converters of an addition, subtraction, multiplication or division over
 *   its operands' compiled domains: fetch converts the operands with them and qdata_*_dbval casts nothing. A node
 *   resolve_domains resolves the type of reads resolve_domains' instead; an operand whose domain is variable plans
 *   no converter here: the operands keep their compiled domains as their targets.
 */
/*
 * [리뷰] domain_plan_operand_coercion — ADD/SUB/MUL/DIV 노드의 두 피연산자 목표 도메인과 변환기를 컴파일 시점에 확정해 항목의 fixed 에 적는다. 실행
 * 전 게이트가 아니라 로드가 끝내는 자리다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: 양쪽 타입이 모두 확정일 때만 domain_resolve_operand_coercion() 으로 규칙을 적용한다. 하나라도 VARIABLE 이면 conv 를 비우고 피연산자 도메인만
 * 남겨 게이트로 넘긴다.
 * 바뀐 것: 신설(+26줄).
 */
static void
domain_plan_operand_coercion (DOMAIN_PLAN_ITEM * item, OPERATOR_TYPE opcode, const TP_DOMAIN * left,
			      const TP_DOMAIN * right)
{
  if (item == NULL)
    {
      return;
    }
  item->fixed.conv[0] = item->fixed.conv[1] = NULL;
  if (!domain_type_is_fixed (left) || !domain_type_is_fixed (right))
    {
      item->fixed.operand_domain[0] = left;
      item->fixed.operand_domain[1] = right;
      return;
    }
  const DOMAIN_OPERAND operands[2] = {
    {left, TP_DOMAIN_TYPE (left), -1, false}, {right, TP_DOMAIN_TYPE (right), -1, false}
  };
  DOMAIN_OPERAND_COERCION operand_coercion;
  domain_resolve_operand_coercion (opcode, operands, &operand_coercion);
  for (int i = 0; i < 2; i++)
    {
      item->fixed.operand_domain[i] = operand_coercion.operand_domain[i];
      item->fixed.conv[i] = operand_coercion.conv[i];
    }
}

/*
 * [리뷰] domain_walk_list — REGU_VARIABLE_LIST 를 순회하며 각 원소에 domain_walk_regu 를 적용한다. 워크 전반에서 가장 많이 쓰이는 반복자.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: ctx->failed 가 서면 즉시 멈춘다. 문맥(DOMAIN_CTX)은 기본 FUNC_ARG 이고 호출자가 LIST_COLUMN·ASSIGN 등으로 바꿔 넘긴다.
 * 바뀐 것: 신설(+8줄).
 */
static void
domain_walk_list (DOMAIN_LOAD_CONTEXT * ctx, REGU_VARIABLE_LIST list, DOMAIN_CTX context = DOMAIN_CTX_FUNC_ARG)
{
  for (; list != NULL && !ctx->failed; list = list->next)
    {
      domain_walk_regu (ctx, &list->value, context);
    }
}

/* Walks regu lists that read the list file of `source` (or whose columns are `columns`): their TYPE_POSITION regus
 * read that list's columns. */
/*
 * [리뷰] domain_walk_position_list — TYPE_POSITION regu 들을 걸을 때, 그들이 읽는 리스트의 출처(source XASL 또는 columns 목록)를 ctx
 * 에 임시로 걸어 두고 걷는다. 위치가 자기 생산자를 찾을 수 있게 하는 스코프 설정자.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: position_source/position_columns 를 저장-설정-복원하는 전형적 save/restore 쌍. 복원이 무조건 일어나므로 중첩 호출에도 안전하다.
 * 바뀐 것: 신설(+12줄).
 */
static void
domain_walk_position_list (DOMAIN_LOAD_CONTEXT * ctx, REGU_VARIABLE_LIST list, XASL_NODE * source,
			   REGU_VARIABLE_LIST columns)
{
  XASL_NODE *saved_source = ctx->position_source;
  REGU_VARIABLE_LIST saved_columns = ctx->position_columns;
  ctx->position_source = source;
  ctx->position_columns = columns;
  domain_walk_list (ctx, list);
  ctx->position_source = saved_source;
  ctx->position_columns = saved_columns;
}

/* The item of column `pos` of a column list. A list file does not store hidden columns; a sort list numbers the
 * output list with them (qexec_plan_sort_list_domains). */
/*
 * [리뷰] domain_column_item — regu 목록에서 pos 번째 컬럼(선택적으로 hidden 컬럼 제외)을 찾아 그 컬럼의 plan_item 을 돌려준다. 리스트 위치·정렬 키·집합
 * 연산 컬럼이 자기 생산자를 집는 경로다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: 찾은 컬럼을 그 자리에서 domain_walk_regu(LIST_COLUMN 문맥)로 걷되, position_source/columns 를 NULL 로 비우고 걷는다 — 생산자 컬럼은
 * 읽는 쪽 문맥이 아니라 자기 리스트 문맥에서 걸려야 하기 때문.
 * 바뀐 것: 신설(+24줄).
 */
static DOMAIN_PLAN_ITEM *
domain_column_item (DOMAIN_LOAD_CONTEXT * ctx, REGU_VARIABLE_LIST columns, int pos, bool skip_hidden)
{
  for (REGU_VARIABLE_LIST col = columns; col != NULL && pos >= 0; col = col->next)
    {
      if (skip_hidden && REGU_VARIABLE_IS_FLAGED (&col->value, REGU_VARIABLE_HIDDEN_COLUMN))
	{
	  continue;
	}
      if (pos-- == 0)
	{
	  /* a producer column is walked in its own list's context, not in the reader's */
	  XASL_NODE *saved_source = ctx->position_source;
	  REGU_VARIABLE_LIST saved_columns = ctx->position_columns;
	  ctx->position_source = NULL;
	  ctx->position_columns = NULL;
	  domain_walk_regu (ctx, &col->value, DOMAIN_CTX_LIST_COLUMN);
	  ctx->position_source = saved_source;
	  ctx->position_columns = saved_columns;
	  return col->value.plan_item;
	}
    }
  return NULL;
}

/* A synthetic load entry owning an item no XASL node points at: a set-operation or CTE list column. */
/*
 * [리뷰] domain_add_synthetic — 대응하는 regu 가 없는 합성 항목(집합 연산/CTE 의 통합 컬럼)을 만든다.
 * tp_Variable_domain·OPERAND_ROW·LIST_COLUMN 문맥으로 시작한다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: cold.synthetic=true 로 표시하고 self_owner 를 자기 소유 포인터로 삼는다(공개 시 자기 자신에게 최종 item 주소를 쓴다).
 * domain_plan_validate 는 synthetic 항목의 미해소를 거부 사유에서 제외한다.
 * 바뀐 것: 신설(+16줄).
 */
static DOMAIN_LOAD_ENTRY *
domain_add_synthetic (DOMAIN_LOAD_CONTEXT * ctx)
{
  DOMAIN_PLAN_ITEM *owner = NULL;
  DOMAIN_PLAN_ITEM *item = domain_add_item (ctx, &owner, &tp_Variable_domain, OPERAND_ROW, DOMAIN_CTX_LIST_COLUMN, 0);
  if (item == NULL)
    {
      return NULL;
    }
  DOMAIN_LOAD_ENTRY *load_entry = domain_load_entry_of (item);
  load_entry->cold.synthetic = true;
  /* the entry keeps its own owner pointer: publishing writes the published item there */
  load_entry->self_owner = item;
  load_entry->owner = &load_entry->self_owner;
  return load_entry;
}

/*
 * domain_list_column () - the item giving column `pos` of the list file `xasl` produces
 *
 * A block's list holds its output columns. A set operation's list unifies its branches' lists, and a CTE's list its
 * non-recursive part's with the rows its recursive part appends (qfile_unify_types): that column is a node over the
 * branch columns, made once per (list, column).
 */
/*
 * [리뷰] domain_list_column — XASL 블록의 pos 번째 출력 컬럼에 해당하는 항목을 돌려준다. UNION/DIFFERENCE/INTERSECTION/CTE 면 가지들을 통합한
 * 합성 항목을, 아니면 출력 리스트의 그 컬럼 항목을 준다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: (xasl, pos) 쌍으로 ctx->list_columns 에 메모해 한 번만 만든다. 합성 항목을 **가지를 묻기 전에** 등록하는 것이 핵심 — 재귀 CTE 가 자기 컬럼을 다시
 * 물어도 무한 재귀 대신 진행 중인 항목을 받는다. 가지를 하나도 못 얻으면 n_link=-1(영구 미해소)로 둔다.
 * 바뀐 것: 신설(+66줄).
 */
static DOMAIN_PLAN_ITEM *
domain_list_column (DOMAIN_LOAD_CONTEXT * ctx, XASL_NODE * xasl, int pos)
{
  if (xasl == NULL || pos < 0 || ctx->failed)
    {
      return NULL;
    }
  XASL_NODE *branches[2] = { NULL, NULL };
  switch (xasl->type)
    {
    case UNION_PROC:
    case DIFFERENCE_PROC:
    case INTERSECTION_PROC:
      branches[0] = xasl->proc.union_.left;
      branches[1] = xasl->proc.union_.right;
      break;
    case CTE_PROC:
      branches[0] = xasl->proc.cte.non_recursive_part;
      branches[1] = xasl->proc.cte.recursive_part;
      break;
    default:
      {
	OUTPTR_LIST *output = domain_block_output (xasl);
	return output == NULL ? NULL : domain_column_item (ctx, output->valptrp, pos, true);
      }
    }
  for (DOMAIN_LOAD_LIST_COLUMN * c = ctx->list_columns; c != NULL; c = c->next)
    {
      if (c->xasl == xasl && c->pos == pos)
	{
	  return c->item;
	}
    }
  DOMAIN_LOAD_LIST_COLUMN *entry = (DOMAIN_LOAD_LIST_COLUMN *) db_private_alloc (ctx->thread_p, sizeof (*entry));
  DOMAIN_LOAD_ENTRY *load_entry = entry == NULL ? NULL : domain_add_synthetic (ctx);
  if (load_entry == NULL)
    {
      if (entry != NULL)
	{
	  db_private_free (ctx->thread_p, entry);
	}
      ctx->failed = true;
      return NULL;
    }
  /* registered before the branches are asked: a recursive part reads this very column */
  entry->xasl = xasl;
  entry->pos = pos;
  entry->item = &load_entry->item;
  entry->next = ctx->list_columns;
  ctx->list_columns = entry;
  load_entry->kind = DOMAIN_LOAD_NODE;
  load_entry->n_link = 0;
  for (int i = 0; i < 2; i++)
    {
      DOMAIN_PLAN_ITEM *column = domain_list_column (ctx, branches[i], pos);
      if (column != NULL)
	{
	  load_entry->link[load_entry->n_link++] = column;
	}
    }
  if (load_entry->n_link == 0)
    {
      load_entry->n_link = -1;
    }
  return &load_entry->item;
}

/* The output list whose columns a block's result list file holds: the analytic or GROUP BY output when the block
 * has one (a BUILDLIST has at most one of the two). */
/*
 * [리뷰] domain_block_output — XASL 블록이 실제로 내보내는 출력 리스트를 고른다. BUILDLIST 는 분석함수용 a_outptr_list, GROUP BY 용
 * g_outptr_list, 그 밖에는 xasl->outptr_list.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: a_eval_list·groupby_list 가 있는지로 단계별 출력 리스트를 고르므로, 리스트 컬럼을 찾는 쪽과 ORDER BY 키가 같은 '최종 출력'을 보게 된다.
 * 바뀐 것: 신설(+17줄).
 */
static OUTPTR_LIST *
domain_block_output (XASL_NODE * xasl)
{
  if (xasl->type == BUILDLIST_PROC)
    {
      BUILDLIST_PROC_NODE *b = &xasl->proc.buildlist;
      if (b->a_eval_list != NULL && b->a_outptr_list != NULL)
	{
	  return b->a_outptr_list;
	}
      if (b->groupby_list != NULL && b->g_outptr_list != NULL)
	{
	  return b->g_outptr_list;
	}
    }
  return xasl->outptr_list;
}

/* Every column of a set operation's or a CTE's list is a node over its branches' columns, read or not: resolve_domains
 * rejects branches it cannot unify before execution (qexec_resolve_late_bind_node), whether a reader asks for the
 * column or the list is the statement's result. */
/*
 * [리뷰] domain_walk_set_columns — 집합 연산/CTE 블록의 컬럼 개수만큼 domain_list_column 을 불러 통합 항목을 모두 만들어 둔다. 어느 독자도 묻지 않은
 * 컬럼까지 포함한다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: 컬럼 개수는 가장 왼쪽(CTE 면 non_recursive_part) 가지의 출력 리스트에서 hidden 을 뺀 개수로 센다 — '리스트는 첫 가지의 컬럼을 들고 있다'는 주석의
 * 규칙.
 * 바뀐 것: 신설(+20줄).
 */
static void
domain_walk_set_columns (DOMAIN_LOAD_CONTEXT * ctx, XASL_NODE * xasl)
{
  /* the list holds the columns of its first branch */
  XASL_NODE *first = xasl;
  while (first != NULL && (first->type == UNION_PROC || first->type == DIFFERENCE_PROC
			   || first->type == INTERSECTION_PROC || first->type == CTE_PROC))
    {
      first = first->type == CTE_PROC ? first->proc.cte.non_recursive_part : first->proc.union_.left;
    }
  OUTPTR_LIST *output = first == NULL ? NULL : domain_block_output (first);
  int pos = 0;
  for (REGU_VARIABLE_LIST col = output == NULL ? NULL : output->valptrp; col != NULL && !ctx->failed; col = col->next)
    {
      if (!REGU_VARIABLE_IS_FLAGED (&col->value, REGU_VARIABLE_HIDDEN_COLUMN))
	{
	  (void) domain_list_column (ctx, xasl, pos++);
	}
    }
}

/* The producer of a TYPE_POSITION regu being walked: the column of the list it reads. */
/*
 * [리뷰] domain_position_producer — 지금 걷는 TYPE_POSITION regu 의 생산자 항목을 돌려준다. ctx 에 걸린 position_columns 가 있으면 그
 * 목록에서, 없으면 position_source XASL 의 리스트 컬럼에서 찾는다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: domain_walk_regu 의 TYPE_POSITION 가지가 producer 를 채울 때 부른다. 둘 다 없으면 NULL 이 나오고 그 위치는 미해소로 남는다.
 * 바뀐 것: 신설(+9줄).
 */
static DOMAIN_PLAN_ITEM *
domain_position_producer (DOMAIN_LOAD_CONTEXT * ctx, int pos)
{
  if (ctx->position_columns != NULL)
    {
      return domain_column_item (ctx, ctx->position_columns, pos, true);
    }
  return domain_list_column (ctx, ctx->position_source, pos);
}

/*
 * [리뷰] domain_walk_out — OUTPTR_LIST 하나를 LIST_COLUMN 문맥으로 걷는 어댑터.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: NULL 이면 아무것도 하지 않는다. 출력 컬럼은 반드시 LIST_COLUMN 문맥이어야 하므로 이 한 군데로 모았다.
 * 바뀐 것: 신설(+8줄).
 */
static void
domain_walk_out (DOMAIN_LOAD_CONTEXT * ctx, OUTPTR_LIST * list)
{
  if (list != NULL)
    {
      domain_walk_list (ctx, list->valptrp, DOMAIN_CTX_LIST_COLUMN);
    }
}

/* field_bottom: a FIELD node whose left operand is a value, not a nested FIELD (REGU_VARIABLE_FIELD_COMPARE); a node
 * met without its regu plans both of its comparisons */
/*
 * [리뷰] domain_walk_arith — ARITH_TYPE 노드 하나를 걸어 GATE 슬롯을 만들고, 그 노드가 (a) 지연 바인딩인지 (b) collation 만 지연인지 (c) 피연산자
 * 강제변환만 지연인지 세 축으로 분류해 표시한다. 이 PR 의 '컴파일이 슬롯을 표시한다' 단계의 중심.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: 이미 걸은 노드면 재방문 표시만 하고 스코프가 달라진 temporary_operand 를 해제한다. 아니면 CASE/IF 의 선택자, COALESCE/NVL 계열의 첫 피연산자가 행
 * 불변이면 나머지 팔에 상수 분기를 씌우고 걷는다. 그다음 FIELD/NULLIF/LEAST/GREATEST 의 비교쌍 등록, row_invariant 계산, domain_add_item,
 * late_bound/collation_variable/coercion_variable 세 플래그와 링크 설정, 정적으로 확정 가능한 피연산자
 * 변환기(domain_fixed_operand·domain_plan_operand_coercion), 마지막으로 스코프당 1회 변환 후보(temporary_operand) 기록까지 한다.
 * 바뀐 것: 신설(+189줄). 이 파일에서 두 번째로 큰 함수.
 */
static void
domain_walk_arith (DOMAIN_LOAD_CONTEXT * ctx, ARITH_TYPE * arith, bool field_bottom = true)
{
  if (arith == NULL || ctx->failed)
    {
      return;
    }
  if (arith->plan_item != NULL)
    {
      DOMAIN_LOAD_ENTRY *met = domain_load_entry_of (arith->plan_item);
      domain_note_met_again (ctx, met->cold.constant_branch);
      for (int i = 0; i < 2; i++)
	{
	  /* an operand a scope fixes is converted once per scope only where this place is in the same scope */
	  if (met->temporary_operand[i] != NULL
	      && met->temporary_scope[i] != domain_outer_scope (ctx, met->temporary_operand[i]))
	    {
	      met->temporary_operand[i] = NULL;
	    }
	}
      return;
    }
  bool is_cast = arith->opcode == T_CAST || arith->opcode == T_CAST_WRAP;
  REGU_VARIABLE *operands[] = { arith->leftptr, arith->rightptr, arith->thirdptr };
  DOMAIN_OPERAND_CLASS cls = domain_non_cacheable_operator (arith->opcode) || arith->pred != NULL
    ? OPERAND_NON_CACHEABLE : OPERAND_CONST;
  /* CASE, DECODE and IF take one arm by their predicate, which they evaluate first; COALESCE, NVL, IFNULL and NVL2
   * read their other operands by the first one's NULL-ness - when the node's domain is fixed: of a variable (VARIABLE)
   * domain, every operand counts as read (fetch_peek_arith read each to infer the domain from the values). A
   * selector no row changes is the constant branch of each arm it may skip (a branch node inside it too,
   * domain_regu_is_row_invariant). */
  const int entry_constant_branch = ctx->constant_branch;
  const bool by_predicate = arith->opcode == T_CASE || arith->opcode == T_DECODE || arith->opcode == T_IF;
  const bool by_first = (arith->opcode == T_COALESCE || arith->opcode == T_NVL || arith->opcode == T_IFNULL
			 || arith->opcode == T_NVL2) && arith->domain != NULL
    && TP_DOMAIN_TYPE (arith->domain) != DB_TYPE_VARIABLE;
  if (by_predicate)
    {
      domain_walk_pred (ctx, arith->pred);
    }
  const bool guarded_arms = by_predicate && domain_pred_is_row_invariant (arith->pred);
  for (int operand_index = 0; operand_index < 3; operand_index++)
    {
      REGU_VARIABLE *operand = operands[operand_index];
      ctx->constant_branch = entry_constant_branch;
      if (operand != NULL && guarded_arms && operand_index < 2)
	{
	  domain_push_constant_branch (ctx,
				       operand_index ==
				       0 ? DOMAIN_CONSTANT_BRANCH_PRED_TRUE : DOMAIN_CONSTANT_BRANCH_PRED_NOT_TRUE,
				       arith->pred);
	}
      else if (operand != NULL && by_first && operand_index > 0 && domain_regu_is_row_invariant (arith->leftptr))
	{
	  domain_push_constant_branch (ctx, arith->opcode == T_NVL2
				       && operand_index ==
				       1 ? DOMAIN_CONSTANT_BRANCH_FIRST_NOT_NULL : DOMAIN_CONSTANT_BRANCH_FIRST_NULL,
				       arith->leftptr);
	}
      domain_walk_regu (ctx, operand, is_cast ? DOMAIN_CTX_ASSIGN : DOMAIN_CTX_ARITH);
      if (operand != NULL)
	{
	  cls = domain_merge_class (cls, operand->plan_item);
	}
    }
  ctx->constant_branch = entry_constant_branch;
  if (!by_predicate)
    {
      domain_walk_pred (ctx, arith->pred);
    }
  /* the comparisons the node makes are resolved like a term's: FIELD compares its third operand with each value,
   * NULLIF and LEAST / GREATEST their two operands; the node's item carries them */
  const DOMAIN_COMPARE_PLAN **compares = domain_arith_compares (ctx->thread_p, arith->opcode, &ctx->failed);
  if (compares != NULL)
    {
      if (arith->opcode == T_FIELD)
	{
	  if (field_bottom)
	    {
	      domain_add_regu_compare (ctx, arith->thirdptr, arith->leftptr, &compares[0]);
	    }
	  domain_add_regu_compare (ctx, arith->thirdptr, arith->rightptr, &compares[1]);
	}
      else
	{
	  domain_add_regu_compare (ctx, arith->leftptr, arith->rightptr, &compares[0]);
	}
    }
  /* no row changes a CASE, DECODE, IF or predicate node over operands no row changes, though a fetch computes it
   * every time (its class stays NON_CACHEABLE); a non-cacheable operator's value is the row's */
  bool row_invariant = (!domain_non_cacheable_operator (arith->opcode) || domain_branch_operator (arith->opcode))
    && (arith->pred == NULL || domain_pred_is_row_invariant (arith->pred));
  for (int i = 0; i < 3 && row_invariant; i++)
    {
      row_invariant = operands[i] == NULL || domain_regu_is_row_invariant (operands[i]);
    }
  DOMAIN_PLAN_ITEM *item = domain_add_item (ctx, &arith->plan_item, arith->domain, cls,
					    is_cast ? DOMAIN_CTX_ASSIGN : DOMAIN_CTX_ARITH, arith->opcode);
  if (item != NULL)
    {
      domain_load_entry_of (item)->row_invariant = row_invariant;
    }
  if (arith->opcode == T_DEFINE_VARIABLE)
    {
      /* resolve_domains types a variable the statement reads from the values the statement assigns it */
      domain_add_define (ctx, arith);
    }
  if (item != NULL)
    {
      item->compares = compares;
      ctx->tail->output[0] = arith->value;
      if (domain_is_variable (arith->domain))
	{
	  domain_give_node_domain (item, true);
	}
    }
  /* A node the compiler left without a result type (a late-bound operator over a variable POS) is resolved by
   * resolve_domains once per execution when every operand gives it a type resolve_domains knows. Whether an operand is
   * known is settled only after derived consumers read their producers, so the resolution pass resolves it; a session
   * variable read is such a node too. CONNECT_BY_ROOT and QPRIOR carry their XASL in thirdptr. */
  const bool late_bound = arith->domain != NULL && TP_DOMAIN_TYPE (arith->domain) == DB_TYPE_VARIABLE;
  /* a string the compiler typed but whose collation its values give (LEAVE, ENFORCE) is resolved by resolve_domains
   * from its operands' resolved domains, as a late-binding node on the collation axis */
  const bool collation_variable = !late_bound && domain_character_is_variable (arith->domain);
  /* an addition, subtraction, multiplication or division the compiler typed over an operand it did not (LIMIT's offset
   * + count, an ORDERBY_NUM bound over a bind) keeps its compiled domain; resolve_domains resolves its operands'
   * operand coercion from their resolved domains */
  const bool coercion_variable = domain_operand_coercion_operator (arith->opcode) && !late_bound && !collation_variable
    && operands[0] != NULL && operands[1] != NULL && operands[0]->plan_item != NULL
    && operands[1]->plan_item != NULL && (!domain_type_is_fixed (operands[0]->domain)
					  || !domain_type_is_fixed (operands[1]->domain));
  if (item != NULL && (late_bound || collation_variable || coercion_variable))
    {
      DOMAIN_LOAD_ENTRY *load_entry = domain_load_entry_of (item);
      const int n_value_operands = (arith->opcode == T_CONNECT_BY_ROOT || arith->opcode == T_QPRIOR) ? 2 : 3;
      load_entry->kind = DOMAIN_LOAD_NODE;
      if (collation_variable)
	{
	  item->flags |= DOMAIN_PLAN_LATE_BIND_COLLATION;
	}
      if (coercion_variable)
	{
	  item->flags |= DOMAIN_PLAN_LATE_BIND_COERCION;
	}
      domain_set_links (ctx, load_entry, operands, n_value_operands, arith->domain);
      for (int i = 0; i < n_value_operands; i++)
	{
	  if (operands[i] != NULL && operands[i]->plan_item == NULL)
	    {
	      /* an operand without a value domain leaves the node unresolved */
	      load_entry->n_link = -1;
	    }
	}
    }
  /* the operand coercion of a node the compiler typed - its collation may still be resolve_domains' - is the
   * resolver's over its operands' compiled domains */
  const bool operand_coercion = domain_operand_coercion_operator (arith->opcode) && !late_bound && operands[0] != NULL
    && operands[1] != NULL;
  for (int i = operand_coercion ? 2 : 0; i < 3; i++)
    {
      if (operands[i] != NULL)
	{
	  /* Static operand targets come from compiled operand domains, never
	   * from an arithmetic result domain (DATE + INTEGER is not DATE + DATE).
	   * A CAST, and a NVL, IFNULL, COALESCE or NVL2 result operand, is cast into the node's domain at the row
	   * (fetch_cast_operand): its target is that domain, and the cast takes the converter found here. */
	  const bool casts_into_node = is_cast
	    || ((arith->opcode == T_NVL || arith->opcode == T_IFNULL || arith->opcode == T_COALESCE) && i < 2)
	    || (arith->opcode == T_NVL2 && i > 0);
	  domain_fixed_operand (item, i, operands[i]->domain, casts_into_node ? arith->domain : operands[i]->domain,
				DOMAIN_CTX_ASSIGN);
	}
    }
  if (operand_coercion)
    {
      domain_plan_operand_coercion (item, arith->opcode, operands[0]->domain, operands[1]->domain);
    }
  if (item != NULL && domain_operand_coercion_operator (arith->opcode) && operands[0] != NULL && operands[1] != NULL)
    {
      /* an operand a scope fixes - a constant, or a value an outer block's scan fixes - has
       * its operand coercion converted once per scope (domain_plan_add_temporaries) */
      DOMAIN_LOAD_ENTRY *load_entry = domain_load_entry_of (item);
      for (int i = 0; i < 2; i++)
	{
	  load_entry->temporary_operand[i] = operands[i];
	  load_entry->temporary_scope[i] = domain_outer_scope (ctx, operands[i]);
	}
    }
}

/*
 * [리뷰] domain_value_in_list — VAL_LIST 안에 특정 DB_VALUE 포인터가 들어 있는지 포인터 동일성으로 찾는다. 값 포인터가 어느 블록 소유인지 가리는 바닥 함수.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: 리스트 선형 탐색. 값 비교가 아니라 주소 비교라는 점이 핵심 — 같은 내용의 값이라도 다른 칸이면 다른 소유다.
 * 바뀐 것: 신설(+12줄).
 */
static bool
domain_value_in_list (VAL_LIST * list, DB_VALUE * value)
{
  for (QPROC_DB_VALUE_LIST p = list == NULL ? NULL : list->valp; p != NULL; p = p->next)
    {
      if (p->val == value)
	{
	  return true;
	}
    }
  return false;
}

/*
 * [리뷰] domain_local_value — 어떤 DB_VALUE 칸이 주어진 XASL 블록의 소유인지(= 그 블록의 스캔이 매 행 쓰는 칸인지) 판정한다. 값 포인터 regu 가
 * OPERAND_ROW 인지 OPERAND_CORRELATED 인지를 가른다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: val_list·merge_val_list, BUILDVALUE/BUILDLIST 의 집계 누적기, BUILDLIST 의 분석함수 value/out_value,
 * g_val_list·a_val_list 까지 블록이 쓰는 칸을 모두 본다.
 * 바뀐 것: 신설(+37줄).
 */
static bool
domain_local_value (XASL_NODE * block, DB_VALUE * value)
{
  if (block == NULL || value == NULL)
    {
      return false;
    }
  if (domain_value_in_list (block->val_list, value) || domain_value_in_list (block->merge_val_list, value))
    {
      return true;
    }
  AGGREGATE_TYPE *aggregate = block->type == BUILDVALUE_PROC ? block->proc.buildvalue.agg_list
    : block->type == BUILDLIST_PROC ? block->proc.buildlist.g_agg_list : NULL;
  for (; aggregate != NULL; aggregate = aggregate->next)
    {
      if (aggregate->accumulator.value == value)
	{
	  return true;
	}
    }
  if (block->type != BUILDLIST_PROC)
    {
      return false;
    }
  for (ANALYTIC_EVAL_TYPE * eval = block->proc.buildlist.a_eval_list; eval != NULL; eval = eval->next)
    {
      for (ANALYTIC_TYPE * analytic = eval->head; analytic != NULL; analytic = analytic->next)
	{
	  if (analytic->value == value || analytic->out_value == value)
	    {
	      return true;
	    }
	}
    }
  return domain_value_in_list (block->proc.buildlist.g_val_list, value)
    || domain_value_in_list (block->proc.buildlist.a_val_list, value);
}

/*
 * domain_outer_scope () - the block whose scans fix a correlated value the walk meets: the block
 *   walked, when the value is one of an outer block's - an outer scan's row, which an inner scan restarts for and a
 *   correlated subquery runs for; NULL otherwise
 *
 * A value of a block walked after this one (an inner scan's row the outer block's output reads) changes at every row
 * this block evaluates, and a subquery's result is computed on demand: neither is fixed for a scope.
 */
/*
 * [리뷰] domain_outer_scope — 상관 참조 regu 가 '바깥 블록의 스캔이 고정하는 값'인지 보고, 그렇다면 그 값이 고정돼 있는 동안인 현재 블록을 돌려준다. 스코프당 1회
 * 변환(temporary)의 스코프를 정하는 자리.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: TYPE_CONSTANT 이고 자기 xasl 이 없고 현재 블록 소유가 아닐 때만 조상 스택을 바깥쪽으로 훑어 소유 블록을 찾는다. 찾으면 ctx->block, 아니면 NULL.
 * 바뀐 것: 신설(+18줄).
 */
static XASL_NODE *
domain_outer_scope (const DOMAIN_LOAD_CONTEXT * ctx, const REGU_VARIABLE * regu)
{
  if (regu == NULL || regu->type != TYPE_CONSTANT || regu->xasl != NULL || regu->value.dbvalptr == NULL
      || ctx->n_ancestors < 2 || ctx->ancestors[ctx->n_ancestors - 1] != ctx->block
      || domain_local_value (ctx->block, regu->value.dbvalptr))
    {
      return NULL;
    }
  for (int i = ctx->n_ancestors - 2; i >= 0; i--)
    {
      if (domain_local_value (ctx->ancestors[i], regu->value.dbvalptr))
	{
	  return ctx->block;
	}
    }
  return NULL;
}

/*
 * domain_link_string_function () - a function the compiler typed as a string whose collation its values give: a node
 *   resolve_domains resolves from its string operands (out of domain_walk_regu)
 *   return: false when the walk stops (no memory)
 */
/*
 * [리뷰] domain_link_string_function — 컴파일러가 문자열로 타입은 정했지만 collation 은 값이 주는 함수(F_ELT 포함)에 대해, 게이트가 collation 을
 * 합칠 문자열 피연산자들을 링크로 건다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: ELT 는 모든 피연산자를 순서대로 걸고 인덱스는 값으로 읽을 수 있을 때(bind·리터럴)만 링크에 넣으며 컴파일러가 씌운 BIGINT 캐스트를 elt_index_cast 에
 * 보관한다. 그 외 함수는 collation 을 가진 피연산자만 고른다. 8개까지는 스택 배열, 넘으면 db_private_alloc 하고 반환 전 해제. plan_item 없는 피연산자가
 * 하나라도 있으면 n_link=-1.
 * 바뀐 것: 신설(+70줄).
 */
static bool
domain_link_string_function (DOMAIN_LOAD_CONTEXT * ctx, REGU_VARIABLE * regu, DOMAIN_PLAN_ITEM * item,
			     DOMAIN_LOAD_ENTRY * load_entry)
{
  /* a function the compiler typed as a string whose collation its values give is resolved by resolve_domains from
   * its string operands, every one of them (a node links as many as it has). ELT links all its operands in
   * order: resolve_domains picks the branch its index names, or merges the branches' collations. */
  const bool elt = regu->value.funcp->ftype == F_ELT;
  REGU_VARIABLE_LIST index = regu->value.funcp->operand;
  /* the index joins the links only where resolve_domains reads its value: a bind or a literal, which the compiler wraps
   * in a cast to BIGINT when its type is another (func_type.cpp) - resolve_domains applies that cast as the row does */
  REGU_VARIABLE *index_value = &index->value;
  const TP_DOMAIN *index_cast = NULL;
  if (elt && (index_value->type == TYPE_INARITH || index_value->type == TYPE_OUTARITH)
      && index_value->value.arithptr->rightptr != NULL
      && (index_value->value.arithptr->opcode == T_CAST || index_value->value.arithptr->opcode == T_CAST_WRAP
	  || index_value->value.arithptr->opcode == T_CAST_NOFAIL))
    {
      index_cast = index_value->value.arithptr->domain;
      index_value = index_value->value.arithptr->rightptr;
    }
  const bool elt_index = elt && (index_value->type == TYPE_DBVAL
				 || (index_value->type == TYPE_POS_VALUE && index_value->domain != NULL));
  int n_all = 0;
  for (REGU_VARIABLE_LIST op = regu->value.funcp->operand; op != NULL; op = op->next)
    {
      n_all++;
    }
  REGU_VARIABLE *inline_operands[8];
  REGU_VARIABLE **operands = n_all <= 8 ? inline_operands
    : (REGU_VARIABLE **) db_private_alloc (ctx->thread_p, n_all * sizeof (*operands));
  if (operands == NULL)
    {
      ctx->failed = true;
      return false;
    }
  int n_operands = 0;
  for (REGU_VARIABLE_LIST op = regu->value.funcp->operand; op != NULL; op = op->next)
    {
      const TP_DOMAIN *d = op->value.domain;
      if (elt ? (op == index && !elt_index)
	  : (d != NULL && TP_DOMAIN_TYPE (d) != DB_TYPE_VARIABLE && !TP_TYPE_HAS_COLLATION (TP_DOMAIN_TYPE (d))))
	{
	  continue;
	}
      operands[n_operands++] = elt && op == index ? index_value : &op->value;
    }
  if (n_operands == 0)
    {
      operands[n_operands++] = &regu->value.funcp->operand->value;
    }
  load_entry->kind = DOMAIN_LOAD_NODE;
  item->flags |= DOMAIN_PLAN_LATE_BIND_COLLATION;
  load_entry->cold.opcode = regu->value.funcp->ftype;
  load_entry->elt_index = elt_index;
  load_entry->elt_index_cast = elt_index ? index_cast : NULL;
  domain_set_links (ctx, load_entry, operands, n_operands, regu->domain);
  for (int i = 0; i < n_operands; i++)
    {
      if (operands[i]->plan_item == NULL)
	{
	  load_entry->n_link = -1;
	}
    }
  if (operands != inline_operands)
    {
      db_private_free (ctx->thread_p, operands);
    }
  return true;
}

/*
 * [리뷰] domain_walk_regu — REGU_VARIABLE 하나를 걸어 그 자리의 GATE 슬롯을 만들고, 그 슬롯이 리프인지·생산자를 읽는 소비자인지·지연 바인딩
 * 노드인지(DOMAIN_LOAD_KIND)를 정한다. 워크의 실질적 중심.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: regu 종류별로 등급(OPERAND_*)과 row_invariant 를 정한 뒤 domain_add_item 으로 슬롯을 만든다. 그다음 variable 여부로 실행 도메인 슬롯과
 * REGU_VARIABLE_VARIABLE_DOMAIN/FAST_PEEK 플래그를 켜고, variable POS 는 LATE_BIND·resolved_index 를, collation 만 지연인
 * POS 는 LATE_BIND_COLLATION 을, 출력 리스트의 bind 는 LIST_BIND 를 단다. 마지막으로 TYPE_CONSTANT/TYPE_POSITION/REGUVAL_LIST 는
 * CONSUMER, arith 래퍼는 ARITH_REGU 로 kind 를 정하고, 아닌 경우에만 정적 피연산자 변환기를 건다.
 * 바뀐 것: 신설(+218줄). 이 파일에서 domain_walk_xasl 다음으로 큰 함수.
 */
static void
domain_walk_regu (DOMAIN_LOAD_CONTEXT * ctx, REGU_VARIABLE * regu, DOMAIN_CTX context)
{
  if (regu == NULL || ctx->failed)
    {
      return;
    }
  if (regu->plan_item != NULL)
    {
      const DOMAIN_LOAD_ENTRY *load_entry = domain_load_entry_of (regu->plan_item);
      if (load_entry->regu == regu)
	{
	  domain_note_met_again (ctx, load_entry->cold.constant_branch);
	}
      return;
    }
  domain_walk_xasl (ctx, regu->xasl);
  if (regu->plan_item != NULL || ctx->failed)
    {
      return;
    }
  DOMAIN_OPERAND_CLASS cls = OPERAND_ROW;
  bool row_invariant = false;	/* a constant's is its class's (domain_add_item) */
  switch (regu->type)
    {
    case TYPE_REGU_VAR_LIST:
      domain_walk_list (ctx, regu->value.regu_var_list, context);
      return;
    case TYPE_LIST_ID:
    case TYPE_ORDERBY_NUM:
      return;
    case TYPE_POS_VALUE:
      if (regu->domain == NULL)
	{
	  /* An allocated but unset regu (regu_init: TYPE_POS_VALUE 0) is no bind reference;
	   * every host variable regu carries a domain, VARIABLE for a variable POS. */
	  return;
	}
      cls = OPERAND_CONST;
      break;
    case TYPE_DBVAL:
      cls = OPERAND_CONST;
      break;
    case TYPE_CONSTANT:
      cls = domain_local_value (ctx->block, regu->value.dbvalptr) ? OPERAND_ROW : OPERAND_CORRELATED;
      break;
    case TYPE_INARITH:
    case TYPE_OUTARITH:
      domain_walk_arith (ctx, regu->value.arithptr, REGU_VARIABLE_IS_FLAGED (regu, REGU_VARIABLE_FIELD_COMPARE));
      if (regu->value.arithptr->plan_item != NULL)
	{
	  cls = (DOMAIN_OPERAND_CLASS) regu->value.arithptr->plan_item->operand_class;
	  row_invariant = domain_load_entry_of (regu->value.arithptr->plan_item)->row_invariant;
	}
      break;
    case TYPE_FUNC:
      domain_walk_list (ctx, regu->value.funcp->operand, context);
      cls = domain_function_caches (regu->value.funcp->ftype) ? OPERAND_CONST : OPERAND_ROW;
      /* a fetch never caches these functions, even when their
       * argument list consists entirely of constants. */
      switch (regu->value.funcp->ftype)
	{
	case F_SET:
	case F_MULTISET:
	case F_SEQUENCE:
	case F_VID:
	case F_TABLE_SET:
	case F_TABLE_MULTISET:
	case F_TABLE_SEQUENCE:
	case F_GENERIC:
	case F_CLASS_OF:
	case F_BENCHMARK:
	  cls = OPERAND_NON_CACHEABLE;
	  break;
	default:
	  break;
	}
      if (regu->value.funcp->ftype == F_BENCHMARK && regu->value.funcp->operand != NULL
	  && regu->value.funcp->operand->next != NULL)
	{
	  /* the target, recomputed at every iteration */
	  domain_force_row (&regu->value.funcp->operand->next->value);
	}
      /* a collection built from values no row changes is one too (an IN list of binds in a branch condition) */
      row_invariant = domain_function_caches (regu->value.funcp->ftype) || regu->value.funcp->ftype == F_SET
	|| regu->value.funcp->ftype == F_MULTISET || regu->value.funcp->ftype == F_SEQUENCE;
      for (REGU_VARIABLE_LIST op = regu->value.funcp->operand; op != NULL; op = op->next)
	{
	  cls = domain_merge_class (cls, op->value.plan_item);
	  row_invariant = row_invariant && domain_regu_is_row_invariant (&op->value);
	}
      break;
    case TYPE_SP:
      domain_walk_list (ctx, regu->value.sp_ptr->args, DOMAIN_CTX_FUNC_ARG);
      for (REGU_VARIABLE_LIST arg = regu->value.sp_ptr->args; arg != NULL; arg = arg->next)
	{
	  domain_force_row (&arg->value);
	}
      cls = OPERAND_NON_CACHEABLE;
      break;
    case TYPE_REGUVAL_LIST:
      for (REGU_VALUE_ITEM * p = regu->value.reguval_list->regu_list; p != NULL; p = p->next)
	{
	  domain_walk_regu (ctx, p->value, context);
	}
      break;
    default:
      break;
    }
  if (REGU_VARIABLE_IS_FLAGED (regu, REGU_VARIABLE_CORRELATED) || regu->xasl != NULL)
    {
      cls = cls == OPERAND_NON_CACHEABLE ? cls : OPERAND_CORRELATED;
    }
  DOMAIN_PLAN_ITEM *item = domain_add_item (ctx, &regu->plan_item, regu->domain, cls, context, regu->type);
  if (item == NULL)
    {
      return;
    }
  if (row_invariant && cls != OPERAND_CORRELATED)
    {
      domain_load_entry_of (item)->row_invariant = true;
    }
  /* a list position's value descriptor shares the regu's item: one execution domain for both; each
   * half keeps its own variable flag */
  const bool position_variable = regu->type == TYPE_POSITION && domain_is_variable (regu->value.pos_descr.dom);
  const bool variable = domain_is_variable (regu->domain) || position_variable;
  if (variable)
    {
      domain_give_node_domain (item, domain_is_variable (regu->domain));
      domain_load_entry_of (item)->variable_position = position_variable;
      REGU_VARIABLE_SET_FLAG (regu, REGU_VARIABLE_VARIABLE_DOMAIN);
    }
  /* the load marks what the inline fetch_peek_dbval () may peek directly - a bind reference with its item, and
   * a stable regu whose domain is variable, once it took its domain (the stream load marked the fixed ones) */
  if (!REGU_VARIABLE_IS_FLAGED (regu, REGU_VARIABLE_APPLY_COLLATION)
      && ((regu->type == TYPE_POS_VALUE)
	  || (variable && (regu->type == TYPE_DBVAL || regu->type == TYPE_ATTR_ID || regu->type == TYPE_SHARED_ATTR_ID
			   || regu->type == TYPE_CLASS_ATTR_ID
			   || (regu->type == TYPE_CONSTANT && regu->xasl == NULL && regu->value.dbvalptr != NULL)))))
    {
      REGU_VARIABLE_SET_FLAG (regu, REGU_VARIABLE_FAST_PEEK);
    }
  DOMAIN_LOAD_ENTRY *load_entry = domain_load_entry_of (item);
  load_entry->regu = regu;
  load_entry->output[0] = regu->vfetch_to;
  load_entry->literal_value = regu->type == TYPE_POS_VALUE || regu->type == TYPE_DBVAL;
  if (regu->type == TYPE_POS_VALUE)
    {
      load_entry->cold.val_pos = regu->value.val_pos;
    }
  if (regu_is_variable_pos (regu))
    {
      item->flags |= DOMAIN_PLAN_LATE_BIND;
      item->resolved_index = ctx->plan->n_resolved++;
      item->fixed.domain = NULL;
    }
  else if (regu->type == TYPE_POS_VALUE && domain_character_is_variable (regu->domain))
    {
      /* a string variable POS the compiler typed but whose collation is the bound value's (LEAVE) or enforced over the
       * value the client sends as it is (an auto-parameter, ENFORCE): resolve_domains records the value domain in this
       * variable POS; the compiled type stays the plan type */
      item->flags |= DOMAIN_PLAN_LATE_BIND_COLLATION;
      item->resolved_index = ctx->plan->n_resolved++;
    }
  else if (regu->type == TYPE_POS_VALUE && context == DOMAIN_CTX_LIST_COLUMN)
    {
      /* an output list's bind - an UPDATE's SET value among them, an auto-parameterized literal typed by its own
       * type. A statement sharing the plan (one hash text) can bind a literal of another type: DEFAULT (another column)
       * is not coerced into the assigned column's type */
      item->flags |= DOMAIN_PLAN_LIST_BIND;
    }
  if (regu->type == TYPE_CONSTANT)
    {
      /* a value pointer holds what its producer wrote there, whatever domain the reader was compiled with (an
       * INSERT ... SELECT reader carries the target column's domain): its producer is found by value identity after
       * the walk */
      load_entry->kind = DOMAIN_LOAD_CONSUMER;
    }
  else if (regu->type == TYPE_POSITION)
    {
      /* a list position reads its list's column: its resolved domain table entry, or its domain */
      load_entry->kind = DOMAIN_LOAD_CONSUMER;
      load_entry->producer = domain_load_entry_of (domain_position_producer (ctx, regu->value.pos_descr.pos_no));
      domain_bind_item (ctx, &regu->value.pos_descr.plan_item, item);
    }
  else if (regu->type == TYPE_REGUVAL_LIST && regu->value.reguval_list->regu_list != NULL
	   && !domain_type_is_fixed (regu->domain))
    {
      /* a multi-row VALUES column takes its first row's domain; later rows are checked against it as they are read
       * (fetch_peek_dbval_slow) */
      load_entry->kind = DOMAIN_LOAD_CONSUMER;
      load_entry->producer = domain_load_entry_of (regu->value.reguval_list->regu_list->value->plan_item);
    }
  else if (regu->type == TYPE_FUNC && domain_character_is_variable (regu->domain) && regu->value.funcp->operand != NULL)
    {
      if (!domain_link_string_function (ctx, regu, item, load_entry))
	{
	  return;
	}
    }
  if (regu->type == TYPE_INARITH || regu->type == TYPE_OUTARITH)
    {
      ARITH_TYPE *arith = regu->value.arithptr;
      if (arith->plan_item != NULL)
	{
	  /* the wrapper carries its node's answer once the resolution pass has it */
	  item->fixed = arith->plan_item->fixed;
	  load_entry->kind = DOMAIN_LOAD_ARITH_REGU;
	  load_entry->producer = domain_load_entry_of (arith->plan_item);
	}
    }
  else
    {
      DOMAIN_CTX mode = context == DOMAIN_CTX_ASSIGN ? DOMAIN_CTX_ASSIGN
	: context == DOMAIN_CTX_COMPARE || context == DOMAIN_CTX_KEY_ELEM ? DOMAIN_CTX_COMPARE : DOMAIN_CTX_FUNC_ARG;
      domain_fixed_operand (item, 0, regu->domain, regu->domain, mode);
    }
}

/* A comparison term of two values: the load resolves it or gives it a late-bind comparison when the plan is published.
 * The set comparisons (subset and superset, tp_set_compare) and a list side (eval_set_list_cmp) are not these. */
/*
 * [리뷰] domain_add_compare_term — 술어의 비교 항(COMP_EVAL_TERM)을 워크 순서대로 ctx 에 모은다. 항과 함께 그 자리의 상수 분기·키 범위 여부·양쪽의 외부
 * 스코프를 같이 적는다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: 지원하는 8개 관계 연산자(EQ..NULLSAFE_EQ)만, 그리고 양쪽이 TYPE_LIST_ID 가 아닌 항만 모은다. 4개 평행 배열(terms / constant_branches
 * / scopes(2배) / ranges)을 같은 max 로 함께 키운다.
 * 바뀐 것: 신설(+63줄). arch.json 이 alloc-free=+4 로 표시했으나 네 배열 모두 ctx 가 소유하고 domain_load_context_free 가 해제하는 구조다.
 */
static void
domain_add_compare_term (DOMAIN_LOAD_CONTEXT * ctx, COMP_EVAL_TERM * term)
{
  switch (term->rel_op)
    {
    case R_EQ:
    case R_NE:
    case R_GT:
    case R_GE:
    case R_LT:
    case R_LE:
    case R_EQ_TORDER:
    case R_NULLSAFE_EQ:
      break;
    default:
      return;
    }
  if (term->lhs == NULL || term->rhs == NULL || term->lhs->type == TYPE_LIST_ID || term->rhs->type == TYPE_LIST_ID)
    {
      return;
    }
  if (ctx->n_compare_terms == ctx->max_compare_terms)
    {
      int max = ctx->max_compare_terms == 0 ? 16 : ctx->max_compare_terms * 2;
      COMP_EVAL_TERM **terms =
	(COMP_EVAL_TERM **) db_private_realloc (ctx->thread_p, ctx->compare_terms, max * sizeof (*terms));
      if (terms == NULL)
	{
	  ctx->failed = true;
	  return;
	}
      ctx->compare_terms = terms;
      int *constant_branches = (int *) db_private_realloc (ctx->thread_p, ctx->compare_term_constant_branches,
							   max * sizeof (*constant_branches));
      if (constant_branches == NULL)
	{
	  ctx->failed = true;
	  return;
	}
      ctx->compare_term_constant_branches = constant_branches;
      XASL_NODE **scopes =
	(XASL_NODE **) db_private_realloc (ctx->thread_p, ctx->compare_term_scopes, 2 * max * sizeof (*scopes));
      if (scopes == NULL)
	{
	  ctx->failed = true;
	  return;
	}
      ctx->compare_term_scopes = scopes;
      bool *ranges = (bool *) db_private_realloc (ctx->thread_p, ctx->compare_term_ranges, max * sizeof (*ranges));
      if (ranges == NULL)
	{
	  ctx->failed = true;
	  return;
	}
      ctx->compare_term_ranges = ranges;
      ctx->max_compare_terms = max;
    }
  ctx->compare_term_constant_branches[ctx->n_compare_terms] = ctx->constant_branch;
  ctx->compare_term_ranges[ctx->n_compare_terms] = ctx->in_key_range;
  ctx->compare_term_scopes[2 * ctx->n_compare_terms] = domain_outer_scope (ctx, term->lhs);
  ctx->compare_term_scopes[2 * ctx->n_compare_terms + 1] = domain_outer_scope (ctx, term->rhs);
  ctx->compare_terms[ctx->n_compare_terms++] = term;
}

/* An ALL/SOME term: its comparisons are published with the plan; a list's column is found now. */
/*
 * [리뷰] domain_add_element_term — ALL/SOME 항(ALSM_EVAL_TERM)을 ctx->element_terms 에 모은다. 비교 대상이 서브쿼리 리스트면 그 리스트의
 * 0번 컬럼 항목을 같이 묶어 둔다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: 리스트 머리에 밀어 넣으므로 나중 것이 앞에 온다(구조체 주석의 'last first'). elemset 이 TYPE_LIST_ID 면 domain_list_column(xasl,
 * 0) 을 domain_bind_item 으로 연결해 공개 시 주소가 갱신되게 한다.
 * 바뀐 것: 신설(+26줄).
 */
static void
domain_add_element_term (DOMAIN_LOAD_CONTEXT * ctx, ALSM_EVAL_TERM * term)
{
  if (term->elem == NULL || term->elemset == NULL || ctx->failed)
    {
      return;
    }
  DOMAIN_LOAD_ELEMENT_TERM *entry = (DOMAIN_LOAD_ELEMENT_TERM *) db_private_alloc (ctx->thread_p, sizeof (*entry));
  if (entry == NULL)
    {
      ctx->failed = true;
      return;
    }
  entry->term = term;
  entry->list_column = NULL;
  entry->constant_branch = ctx->constant_branch;
  entry->key_range = ctx->in_key_range;
  entry->next = ctx->element_terms;
  ctx->element_terms = entry;
  ctx->n_element_terms++;
  if (term->elemset->type == TYPE_LIST_ID)
    {
      /* the item compares with column 0 of the list its subquery produces (eval_some_list_eval) */
      domain_bind_item (ctx, &entry->list_column, domain_list_column (ctx, term->elemset->xasl, 0));
    }
}

/*
 * [리뷰] domain_walk_pred — PRED_EXPR 트리를 걸어 각 항의 피연산자 regu 를 COMPARE 문맥으로 걷고, 비교 항·ALL/SOME 항을 수집한다. AND/OR 의
 * 왼쪽이 행 불변이면 오른쪽에 상수 분기를 씌운다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: T_PRED 는 오른쪽으로 루프를 돌아(꼬리 재귀 제거) 깊은 AND 사슬에서도 스택을 쓰지 않는다. eval_pred 의 단축 평가 규칙(AND 는 거짓 아닐 때만, OR 은 참
 * 아닐 때만 나머지를 본다)을 그대로 분기 종류로 옮겼다. 함수 끝에서 constant_branch 를 진입값으로 복원한다.
 * 바뀐 것: 신설(+58줄).
 * [지적 A3-03]
 */
static void
domain_walk_pred (DOMAIN_LOAD_CONTEXT * ctx, PRED_EXPR * pred)
{
  const int entry_constant_branch = ctx->constant_branch;
  while (pred != NULL && !ctx->failed)
    {
      if (pred->type == T_PRED)
	{
	  domain_walk_pred (ctx, pred->pe.m_pred.lhs);
	  const BOOL_OP op = pred->pe.m_pred.bool_op;
	  if ((op == B_AND || op == B_OR) && domain_pred_is_row_invariant (pred->pe.m_pred.lhs))
	    {
	      /* eval_pred evaluates the rest of an AND only when this term is not false, of an OR only when it is
	       * not true */
	      domain_push_constant_branch (ctx,
					   op ==
					   B_AND ? DOMAIN_CONSTANT_BRANCH_TERM_NOT_FALSE :
					   DOMAIN_CONSTANT_BRANCH_TERM_NOT_TRUE, pred->pe.m_pred.lhs);
	    }
	  pred = pred->pe.m_pred.rhs;
	  continue;
	}
      else if (pred->type == T_NOT_TERM)
	{
	  pred = pred->pe.m_not_term;
	  continue;
	}
      else
	{
	  EVAL_TERM *term = &pred->pe.m_eval_term;
	  switch (term->et_type)
	    {
	    case T_COMP_EVAL_TERM:
	      domain_walk_regu (ctx, term->et.et_comp.lhs, DOMAIN_CTX_COMPARE);
	      domain_walk_regu (ctx, term->et.et_comp.rhs, DOMAIN_CTX_COMPARE);
	      domain_add_compare_term (ctx, &term->et.et_comp);
	      break;
	    case T_ALSM_EVAL_TERM:
	      domain_walk_regu (ctx, term->et.et_alsm.elem, DOMAIN_CTX_COMPARE);
	      domain_walk_regu (ctx, term->et.et_alsm.elemset, DOMAIN_CTX_COMPARE);
	      domain_add_element_term (ctx, &term->et.et_alsm);
	      break;
	    case T_LIKE_EVAL_TERM:
	      domain_walk_regu (ctx, term->et.et_like.src, DOMAIN_CTX_COMPARE);
	      domain_walk_regu (ctx, term->et.et_like.pattern, DOMAIN_CTX_COMPARE);
	      domain_walk_regu (ctx, term->et.et_like.esc_char, DOMAIN_CTX_COMPARE);
	      break;
	    case T_RLIKE_EVAL_TERM:
	      domain_walk_regu (ctx, term->et.et_rlike.src, DOMAIN_CTX_COMPARE);
	      domain_walk_regu (ctx, term->et.et_rlike.pattern, DOMAIN_CTX_COMPARE);
	      domain_walk_regu (ctx, term->et.et_rlike.case_sensitive, DOMAIN_CTX_COMPARE);
	      break;
	    }
	}
      break;
    }
  ctx->constant_branch = entry_constant_branch;
}

/* A sort key reads column pos_no of the list it sorts: the producer's item is the key's item. An aggregate's
 * ORDER BY sorts the aggregate's own list, whose columns are its operands. */
/*
 * [리뷰] domain_walk_sort — SORT_LIST 의 각 정렬 키가 읽는 컬럼 항목을 찾아 pos_descr.plan_item 에 연결한다. 못 찾으면 그 키 자리에 독립 항목을 새로
 * 만든다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: columns 가 주어지면 그 목록에서(hidden 포함, skip_hidden=false), 아니면 source XASL 의 리스트 컬럼에서 찾는다 — 출력 리스트가 없는 집합 연산
 * 블록은 자기 리스트 파일을 정렬하기 때문.
 * 바뀐 것: 신설(+19줄).
 */
static void
domain_walk_sort (DOMAIN_LOAD_CONTEXT * ctx, SORT_LIST * list, REGU_VARIABLE_LIST columns, XASL_NODE * source = NULL)
{
  for (; list != NULL && !ctx->failed; list = list->next)
    {
      QFILE_TUPLE_VALUE_POSITION *pos = &list->pos_descr;
      /* a block without an output list (a set operation) sorts its own list file: the key reads that list's column */
      DOMAIN_PLAN_ITEM *column = columns != NULL ? domain_column_item (ctx, columns, pos->pos_no, false)
	: domain_list_column (ctx, source, pos->pos_no);
      if (column != NULL)
	{
	  domain_bind_item (ctx, &pos->plan_item, column);
	}
      else
	{
	  (void) domain_add_item (ctx, &pos->plan_item, pos->dom, OPERAND_ROW, DOMAIN_CTX_LIST_COLUMN, 0);
	}
    }
}

/*
 * [리뷰] domain_walk_agg — 집계 함수 목록을 걸어 각 집계에 GATE 슬롯을 만들고, 누적기·피연산자 타입·보간 리스트 도메인이라는 세 가지 실행 상태가 필요한지 표시한다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: COUNT(*)·GROUPBY_NUM 은 피연산자가 없는 것으로 보고 그 가짜 regu 를 걷지 않는다. kind 는 FIXED_AGG 이고 링크는 인자 하나. opr_dbtype 이
 * VARIABLE 이 아니고 인자 도메인도 확정이면 argument 에 컴파일 도메인을 남긴다. SUM/AVG(non-DISTINCT)는 더하는 값을 temporary_operand[1] 후보로
 * 적는다. MEDIAN/PERCENTILE 은 정렬 키를 집계 항목에 묶고, CUME_DIST/PERCENT_RANK 는 REGU_VAR_LIST 로 싸인 ORDER BY 값들을 컬럼으로 삼아
 * domain_walk_sort 로 넘긴다.
 * 바뀐 것: 신설(+75줄).
 */
static void
domain_walk_agg (DOMAIN_LOAD_CONTEXT * ctx, AGGREGATE_TYPE * agg)
{
  for (; agg != NULL && !ctx->failed; agg = agg->next)
    {
      if (agg->plan_item != NULL)
	{
	  continue;
	}
      /* COUNT(*) and GROUPBY_NUM pack a default regu (TYPE_POS_VALUE 0, xasl_generation.c
       * "hack") only to carry a domain. It is never fetched, so it is no bind reference. */
      const bool has_operand = agg->function != PT_COUNT_STAR && agg->function != PT_GROUPBY_NUM;
      if (has_operand)
	{
	  domain_walk_list (ctx, agg->operands, DOMAIN_CTX_AGG);
	}
      if (agg->function == PT_PERCENTILE_CONT || agg->function == PT_PERCENTILE_DISC)
	{
	  /* the fraction is fetched with the execution's value descriptor (qdata_evaluate_aggregate_list) */
	  domain_walk_regu (ctx, agg->info.percentile.percentile_reguvar);
	}
      DOMAIN_PLAN_ITEM *item = domain_add_item (ctx, &agg->plan_item, agg->domain, OPERAND_ROW,
						DOMAIN_CTX_AGG, agg->function);
      domain_give_node_domain (item, domain_is_variable (agg->domain));
      if (item != NULL)
	{
	  DOMAIN_LOAD_ENTRY *load_entry = domain_load_entry_of (item);
	  load_entry->needs_operand_type = true;
	  load_entry->needs_list_domain = QPROC_IS_INTERPOLATION_FUNC (agg);
	  load_entry->output[0] = agg->accumulator.value;
	  if (has_operand && agg->operands != NULL)
	    {
	      REGU_VARIABLE *operand = &agg->operands->value;
	      domain_fixed_operand (item, 0, operand->domain, operand->domain, DOMAIN_CTX_FUNC_ARG);
	      /* the function, accumulator and list domains follow the argument: resolve_domains resolves them when it
	       * resolves the argument or the compiler left the function's domain variable; a compiled one gets its
	       * accumulator derived once (resolution pass) */
	      load_entry->kind = DOMAIN_LOAD_FIXED_AGG;
	      domain_set_links (ctx, load_entry, &operand, 1, agg->domain);
	      load_entry->argument = agg->opr_dbtype != DB_TYPE_VARIABLE && domain_type_is_fixed (operand->domain)
		? operand->domain : NULL;
	      if (operand->plan_item == NULL)
		{
		  load_entry->n_link = -1;
		}
	      if ((agg->function == PT_SUM || agg->function == PT_AVG) && agg->option != Q_DISTINCT)
		{
		  /* the value SUM and AVG add, when a scope fixes it (domain_plan_add_temporaries) */
		  load_entry->temporary_operand[1] = operand;
		  load_entry->temporary_scope[1] = domain_outer_scope (ctx, operand);
		}
	    }
	}
      if (QPROC_IS_INTERPOLATION_FUNC (agg) && agg->plan_item != NULL)
	{
	  /* MEDIAN / PERCENTILE sort values cast to the function's domain, the type their list holds: the key
	   * reads the aggregate */
	  for (SORT_LIST * key = agg->sort_list; key != NULL && !ctx->failed; key = key->next)
	    {
	      domain_bind_item (ctx, &key->pos_descr.plan_item, agg->plan_item);
	    }
	}
      else
	{
	  /* CUME_DIST / PERCENT_RANK wrap their ORDER BY values in one TYPE_REGU_VAR_LIST operand: those values
	   * are the columns of the list the key sorts */
	  REGU_VARIABLE_LIST columns = agg->operands;
	  if (columns != NULL && columns->value.type == TYPE_REGU_VAR_LIST)
	    {
	      columns = columns->value.value.regu_var_list;
	    }
	  domain_walk_sort (ctx, agg->sort_list, columns);
	}
    }
}

/*
 * [리뷰] domain_walk_analytic — 분석함수 평가 목록을 걸어 각 분석함수에 GATE 슬롯을 만들고 출력 두 칸(value, out_value)과 피연산자 타입 슬롯을 표시한다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: 집계와 같은 FIXED_AGG 모양이되 피연산자가 a_val_list 의 값 포인터라 생산자를 통해 해소된다는 점이 주석에 명시돼 있다. eval 단위마다 정렬 리스트를
 * a_outptr_list_ex 의 컬럼으로 걷는다.
 * 바뀐 것: 신설(+42줄).
 */
static void
domain_walk_analytic (DOMAIN_LOAD_CONTEXT * ctx, ANALYTIC_EVAL_TYPE * eval, OUTPTR_LIST * output)
{
  for (; eval != NULL && !ctx->failed; eval = eval->next)
    {
      for (ANALYTIC_TYPE * analytic = eval->head; analytic != NULL; analytic = analytic->next)
	{
	  if (analytic->plan_item != NULL)
	    {
	      continue;
	    }
	  domain_walk_regu (ctx, &analytic->operand, DOMAIN_CTX_ANALYTIC);
	  if (analytic->function == PT_PERCENTILE_CONT || analytic->function == PT_PERCENTILE_DISC)
	    {
	      /* the ratio, fetched with the execution's descriptor as an aggregate's is */
	      domain_walk_regu (ctx, analytic->info.percentile.percentile_reguvar);
	    }
	  DOMAIN_PLAN_ITEM *item = domain_add_item (ctx, &analytic->plan_item, analytic->domain, OPERAND_ROW,
						    DOMAIN_CTX_ANALYTIC, analytic->function);
	  domain_give_node_domain (item, domain_is_variable (analytic->domain));
	  if (item != NULL)
	    {
	      DOMAIN_LOAD_ENTRY *load_entry = domain_load_entry_of (item);
	      load_entry->needs_operand_type = true;
	      REGU_VARIABLE *operand = &analytic->operand;
	      load_entry->output[0] = analytic->value;
	      load_entry->output[1] = analytic->out_value;
	      domain_fixed_operand (item, 0, operand->domain, operand->domain, DOMAIN_CTX_FUNC_ARG);
	      /* as an aggregate's: the operand is a value pointer into a_val_list, so its producer resolves */
	      load_entry->kind = DOMAIN_LOAD_FIXED_AGG;
	      domain_set_links (ctx, load_entry, &operand, 1, analytic->domain);
	      load_entry->argument = analytic->opr_dbtype != DB_TYPE_VARIABLE && domain_type_is_fixed (operand->domain)
		? operand->domain : NULL;
	      if (operand->plan_item == NULL)
		{
		  load_entry->n_link = -1;
		}
	    }
	}
      domain_walk_sort (ctx, eval->sort_list, output == NULL ? NULL : output->valptrp);
    }
}

/* An index scan the walk meets: its key plan is published once its elements' items are. */
/*
 * [리뷰] domain_add_index — 인덱스 스캔(INDX_INFO)을 워크 순서대로 모으고 그 자리의 상수 분기를 같이 적는다. 같은 스캔을 다시 만나면 분기 모호성만 표시한다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: indexes / index_constant_branches 두 평행 배열을 4에서 시작해 2배씩 키운다. 중복 검사는 선형 탐색(인덱스 스캔 수가 적다는 전제).
 * 바뀐 것: 신설(+34줄).
 */
static void
domain_add_index (DOMAIN_LOAD_CONTEXT * ctx, INDX_INFO * index)
{
  for (int i = 0; i < ctx->n_indexes; i++)
    {
      if (ctx->indexes[i] == index)
	{
	  domain_note_met_again (ctx, ctx->index_constant_branches[i]);
	  return;
	}
    }
  if (ctx->n_indexes == ctx->max_indexes)
    {
      const int max = ctx->max_indexes == 0 ? 4 : ctx->max_indexes * 2;
      INDX_INFO **indexes = (INDX_INFO **) db_private_realloc (ctx->thread_p, ctx->indexes, max * sizeof (*indexes));
      if (indexes == NULL)
	{
	  ctx->failed = true;
	  return;
	}
      ctx->indexes = indexes;
      int *constant_branches =
	(int *) db_private_realloc (ctx->thread_p, ctx->index_constant_branches, max * sizeof (*constant_branches));
      if (constant_branches == NULL)
	{
	  ctx->failed = true;
	  return;
	}
      ctx->index_constant_branches = constant_branches;
      ctx->max_indexes = max;
    }
  ctx->index_constant_branches[ctx->n_indexes] = ctx->constant_branch;
  ctx->indexes[ctx->n_indexes++] = index;
}

/* Records a session variable assignment: resolve_domains types the variable from the values the statement assigns. */
/*
 * [리뷰] domain_add_define — 세션 변수 대입(T_DEFINE_VARIABLE 노드)을 ctx->defines 에 모은다. 나중에
 * domain_plan_add_session_variables 가 '이 변수를 읽는 자리'와 짝지어 준다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: domain_walk_arith 가 T_DEFINE_VARIABLE 을 만나면 부른다. 4에서 시작해 2배씩 realloc.
 * 바뀐 것: 신설(+17줄).
 */
static void
domain_add_define (DOMAIN_LOAD_CONTEXT * ctx, ARITH_TYPE * define)
{
  if (ctx->n_defines == ctx->max_defines)
    {
      const int max = ctx->max_defines == 0 ? 4 : ctx->max_defines * 2;
      ARITH_TYPE **defines = (ARITH_TYPE **) db_private_realloc (ctx->thread_p, ctx->defines, max * sizeof (*defines));
      if (defines == NULL)
	{
	  ctx->failed = true;
	  return;
	}
      ctx->defines = defines;
      ctx->max_defines = max;
    }
  ctx->defines[ctx->n_defines++] = define;
}

/*
 * [리뷰] domain_walk_specs — ACCESS_SPEC 사슬을 걸어 인덱스 키 범위·키 리밋·세 술어(where_key/pred/range)와 대상 종류별 regu 목록을 모두 건다.
 * 스캔이 읽는 모든 값이 여기서 슬롯을 받는다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: where_range 를 걷는 동안만 ctx->in_key_range 를 세워, 그 안의 비교 항이 'B-tree 탐색에서 만나는 항'으로 표시되게 한다. 키 리밋은 걷고 나서
 * domain_force_row 로 상수 등급을 내린다 — 스캔이 열릴 때 자기가 계산하고 오버플로를 리밋으로 바꾸므로 게이트의 에러가 아니어야 하기 때문. TARGET_LIST 는 생산자
 * XASL 을 먼저 걷고 네 개의 위치 목록을 그 출처로 걷는다.
 * 바뀐 것: 신설(+78줄).
 */
static void
domain_walk_specs (DOMAIN_LOAD_CONTEXT * ctx, ACCESS_SPEC_TYPE * spec)
{
  for (; spec != NULL && !ctx->failed; spec = spec->next)
    {
      if (spec->indexptr != NULL)
	{
	  domain_add_index (ctx, spec->indexptr);
	  KEY_INFO *key = &spec->indexptr->key_info;
	  for (int i = 0; i < key->key_cnt; i++)
	    {
	      domain_walk_regu (ctx, key->key_ranges[i].key1, DOMAIN_CTX_KEY_ELEM);
	      domain_walk_regu (ctx, key->key_ranges[i].key2, DOMAIN_CTX_KEY_ELEM);
	    }
	  domain_walk_regu (ctx, key->key_limit_l);
	  domain_walk_regu (ctx, key->key_limit_u);
	  /* the scan computes its key limits when it opens, and turns an overflow of their arithmetic into a limit
	   * (scan_handle_overflow_subtraction_upper, fetch_and_coerce_key_limit_lower): a constant there is the scan's
	   * to compute, not one whose failure is resolve_domains' error */
	  domain_force_row (key->key_limit_l);
	  domain_force_row (key->key_limit_u);
	}
      domain_walk_pred (ctx, spec->where_key);
      domain_walk_pred (ctx, spec->where_pred);
      /* a key range term's constant that does not coerce is met in the B-tree search, not in the term */
      ctx->in_key_range = true;
      domain_walk_pred (ctx, spec->where_range);
      ctx->in_key_range = false;
      switch (spec->type)
	{
	case TARGET_CLASS:
	case TARGET_CLASS_ATTR:
	  domain_walk_list (ctx, spec->s.cls_node.cls_regu_list_key);
	  domain_walk_list (ctx, spec->s.cls_node.cls_regu_list_pred);
	  domain_walk_list (ctx, spec->s.cls_node.cls_regu_list_rest);
	  domain_walk_list (ctx, spec->s.cls_node.cls_regu_list_range);
	  domain_walk_list (ctx, spec->s.cls_node.cls_regu_val_list);
	  domain_walk_list (ctx, spec->s.cls_node.cls_regu_list_reserved);
	  domain_walk_out (ctx, spec->s.cls_node.cls_output_val_list);
	  break;
	case TARGET_LIST:
	  {
	    /* the list regus read the list file of the spec's XASL: its columns are their producers */
	    XASL_NODE *source = spec->s.list_node.xasl_node;
	    domain_walk_xasl (ctx, source);
	    domain_walk_position_list (ctx, spec->s.list_node.list_regu_list_pred, source, NULL);
	    domain_walk_position_list (ctx, spec->s.list_node.list_regu_list_rest, source, NULL);
	    domain_walk_position_list (ctx, spec->s.list_node.list_regu_list_build, source, NULL);
	    domain_walk_position_list (ctx, spec->s.list_node.list_regu_list_probe, source, NULL);
	  }
	  break;
	case TARGET_JSON_TABLE:
	  domain_walk_regu (ctx, spec->s.json_table_node.m_json_reguvar);
	  break;
	case TARGET_SET:
	  domain_walk_regu (ctx, spec->s.set_node.set_ptr);
	  domain_walk_list (ctx, spec->s.set_node.set_regu_list);
	  break;
	case TARGET_METHOD:
	  domain_walk_xasl (ctx, spec->s.method_node.xasl_node);
	  domain_walk_list (ctx, spec->s.method_node.method_regu_list);
	  break;
	case TARGET_SHOWSTMT:
	  domain_walk_list (ctx, spec->s.showstmt_node.arg_list);
	  break;
	case TARGET_DBLINK:
	  domain_walk_list (ctx, spec->s.dblink_node.dblink_regu_list_pred);
	  domain_walk_list (ctx, spec->s.dblink_node.dblink_regu_list_rest);
	  domain_walk_list (ctx, spec->s.dblink_node.corr_key_regu_list);
	  break;
	case TARGET_REGUVAL_LIST:
	  domain_walk_out (ctx, spec->s.reguval_list_node.valptr_list);
	  break;
	default:
	  break;
	}
    }
}

/*
 * [리뷰] domain_walk_assignments — UPDATE/ODKU 의 대입식들을 ASSIGN 문맥으로 걷는다. ASSIGN 문맥이어야 대상 컬럼으로의 캐스트가
 * CONSUMER_CONVERTS 로 표시된다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: count 만큼 배열을 돌며 regu_var 를 걷는 단순 반복자.
 * 바뀐 것: 신설(+8줄).
 */
static void
domain_walk_assignments (DOMAIN_LOAD_CONTEXT * ctx, UPDATE_ASSIGNMENT * assignments, int count)
{
  for (int i = 0; i < count; i++)
    {
      domain_walk_regu (ctx, assignments[i].regu_var, DOMAIN_CTX_ASSIGN);
    }
}

/*
 * domain_fix_connect_by_probe () - the probe domain of a START WITH ... CONNECT BY hash list scan
 *
 * The scan coerces its probe values to the first probe item's domain. When the join widened that domain to a float
 * NUMERIC, the first fixed-precision NUMERIC of the rest list gives its precision and scale, so integers scale the way
 * the fixed numeric column's hash keys do. Only compiled domains resolve this: the load sets it once, not each
 * execution.
 */
/*
 * [리뷰] domain_fix_connect_by_probe — CONNECT BY 블록의 프로브 regu 가 기본 정밀도 NUMERIC 으로 디코드된 경우, 같은 리스트의 rest 목록에서 실제
 * 정밀도를 찾아 프로브 도메인을 그것으로 고친다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: tp_domain_copy 로 복사해 precision/scale 만 바꾸고 tp_domain_cache 로 캐시 도메인을 얻어 regu->domain 에 쓴다. 즉 로드가 디코드된
 * 스트림 자체를 한 번 고치는 것이고, 주석대로 '이 클론의 모든 실행이 그것을 읽는다'. domain_walk_xasl 이 블록당 한 번만 부르므로(이미 domain_plan 이 달린 블록은
 * 조기 반환) 중복 수정은 없다.
 * 바뀐 것: 신설(+39줄).
 */
static void
domain_fix_connect_by_probe (DOMAIN_LOAD_CONTEXT * ctx, XASL_NODE * xasl)
{
  ACCESS_SPEC_TYPE *spec = xasl->spec_list;
  if (spec == NULL || spec->type != TARGET_LIST || spec->s.list_node.list_regu_list_probe == NULL)
    {
      return;
    }
  REGU_VARIABLE *probe = &spec->s.list_node.list_regu_list_probe->value;
  if (REGU_VARIABLE_GET_TYPE (probe) != DB_TYPE_NUMERIC || probe->domain == NULL
      || probe->domain->precision != DB_DEFAULT_NUMERIC_PRECISION)
    {
      return;
    }
  const TP_DOMAIN *fixed = NULL;
  for (REGU_VARIABLE_LIST rest = spec->s.list_node.list_regu_list_rest; rest != NULL && fixed == NULL;
       rest = rest->next)
    {
      if (TP_DOMAIN_TYPE (rest->value.domain) == DB_TYPE_NUMERIC
	  && rest->value.domain->precision != DB_DEFAULT_NUMERIC_PRECISION)
	{
	  fixed = rest->value.domain;
	}
    }
  if (fixed == NULL)
    {
      return;
    }
  TP_DOMAIN *domain = tp_domain_copy (probe->domain, false);
  if (domain == NULL)
    {
      ctx->failed = true;
      return;
    }
  domain->precision = fixed->precision;
  domain->scale = fixed->scale;
  /* the load's fix of the stream: every execution of this clone reads it */
  probe->domain = tp_domain_cache (domain);
}

/*
 * domain_mark_aggregate_operands () - flag the expressions that only feed a SUM / AVG (REGU_VARIABLE_AGG_OPERAND), once
 *   at load (each execution marked them before its scan, and each PX worker its own copy)
 *
 * BUILDLIST reaches the aggregate through a TYPE_CONSTANT operand pointing to the DB_VALUE the scan's expression writes
 * (regu->vfetch_to); BUILDVALUE's operand is the expression itself. fetch_peek_arith evaluates a flagged expression in
 * one register pass; the shape check reads the compiled domains, which an execution's regus hold again before its scan
 * (qexec_clear_regu_var). Analytic functions read their operands from list columns: nothing to mark there.
 */
/*
 * [리뷰] domain_mark_aggregate_operands — SUM/AVG(non-DISTINCT)의 피연산자가 fetch 가 집계식 모양으로 알아보는 산술식이면 그 regu 에
 * REGU_VARIABLE_AGG_OPERAND 플래그를 단다. 실행이 그 자리에서 값을 한 번만 변환하도록 하는 표시.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: BUILDVALUE 는 집계의 피연산자 regu 를 직접 보고, BUILDLIST 는 출력 리스트의 regu 중 vfetch_to 가 집계의 값 포인터와 같은 것을 찾아 거기에 단다.
 * 재귀 깊이 예산은 PRM_ID_MAX_RECURSION_SQL_DEPTH 를 쓴다.
 * 바뀐 것: 신설(+42줄).
 */
static void
domain_mark_aggregate_operands (XASL_NODE * xasl)
{
  const int budget = prm_get_integer_value (PRM_ID_MAX_RECURSION_SQL_DEPTH);
  if (xasl->type == BUILDVALUE_PROC)
    {
      for (AGGREGATE_TYPE * agg = xasl->proc.buildvalue.agg_list; agg != NULL; agg = agg->next)
	{
	  if ((agg->function == PT_SUM || agg->function == PT_AVG) && agg->option != Q_DISTINCT
	      && agg->operands != NULL && agg->operands->value.type == TYPE_INARITH
	      && fetch_is_agg_expr_shape (&agg->operands->value, budget))
	    {
	      REGU_VARIABLE_SET_FLAG (&agg->operands->value, REGU_VARIABLE_AGG_OPERAND);
	    }
	}
      return;
    }
  if (xasl->type != BUILDLIST_PROC || xasl->proc.buildlist.g_agg_list == NULL || xasl->outptr_list == NULL)
    {
      return;
    }
  for (REGU_VARIABLE_LIST regu = xasl->outptr_list->valptrp; regu != NULL; regu = regu->next)
    {
      if (regu->value.type != TYPE_INARITH || regu->value.vfetch_to == NULL)
	{
	  continue;
	}
      for (AGGREGATE_TYPE * agg = xasl->proc.buildlist.g_agg_list; agg != NULL; agg = agg->next)
	{
	  if ((agg->function == PT_SUM || agg->function == PT_AVG) && agg->option != Q_DISTINCT
	      && agg->operands != NULL && agg->operands->value.type == TYPE_CONSTANT
	      && agg->operands->value.value.dbvalptr == regu->value.vfetch_to)
	    {
	      if (fetch_is_agg_expr_shape (&regu->value, budget))
		{
		  REGU_VARIABLE_SET_FLAG (&regu->value, REGU_VARIABLE_AGG_OPERAND);
		}
	      break;
	    }
	}
    }
}

/* The INT 0 a LIMIT row count is compared with (qexec_check_limit_clause). */
/* *INDENT-OFF* */
static const DB_VALUE domain_Int_zero = []
{
  DB_VALUE zero;
  db_make_int (&zero, 0);
  return zero;
} ();
/* *INDENT-ON* */

/* A merge join compares each pair of merge columns, the outer list's with the inner list's (qexec_cmp_tpl_vals_merge):
 * one resolved comparison per pair. */
/*
 * [리뷰] domain_add_merge_compares — 머지 조인 블록의 컬럼 쌍마다 비교 계획 슬롯을 만들고 양쪽 리스트의 해당 컬럼 항목을 비교쌍으로 등록한다.
 * merge->merge_compares 배열의 주인.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: ls_column_cnt 개를 domain_plan_alloc(플랜 수명)으로 한 번에 잡고 NULL 초기화한 뒤, 각 칸을 domain_add_compare_pair 의 owner
 * 로 넘긴다. 양쪽 다 regu 없이 컬럼만 있는 쌍이다.
 * 바뀐 것: 신설(+30줄).
 */
static void
domain_add_merge_compares (DOMAIN_LOAD_CONTEXT * ctx, XASL_NODE * xasl)
{
  MERGELIST_PROC_NODE *merge = &xasl->proc.mergelist;
  const QFILE_LIST_MERGE_INFO *info = &merge->ls_merge;
  merge->merge_compares = NULL;
  if (info->ls_column_cnt <= 0 || ctx->failed)
    {
      return;
    }
  merge->merge_compares =
    (const DOMAIN_COMPARE_PLAN **) domain_plan_alloc (ctx->thread_p, info->ls_column_cnt,
						      sizeof (*merge->merge_compares));
  if (merge->merge_compares == NULL)
    {
      ctx->failed = true;
      return;
    }
  for (int k = 0; k < info->ls_column_cnt; k++)
    {
      merge->merge_compares[k] = NULL;
      REGU_VARIABLE *const regu[2] = { NULL, NULL };
      DOMAIN_PLAN_ITEM *const column[2] = {
	domain_list_column (ctx, merge->outer_xasl, info->ls_outer_column[k]),
	domain_list_column (ctx, merge->inner_xasl, info->ls_inner_column[k])
      };
      const DB_VALUE *const literal[2] = { NULL, NULL };
      domain_add_compare_pair (ctx, regu, column, literal, &merge->merge_compares[k]);
    }
}

/*
 * [리뷰] domain_walk_xasl — XASL 트리 한 블록을 정해진 순서로 걷는 최상위 워크. 블록·조상 스택·상수 분기 문맥을 관리하며 모든 하위
 * 워크(specs·pred·agg·analytic·sort·out·regu)를 부른다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: xasl->domain_plan 이 이미 차 있으면 재방문 표시만 하고 돌아온다(공유 XASL 1회 방문 보장). 블록 목록·조상 스택을 8부터 2배씩 키우고, if_pred 가 행
 * 불변이면 그 아래(fptr·내부 스캔·행 번호·출력)를 상수 분기 안으로 넣는다. 최상위 블록의 LIMIT 은 if_pred 분기 밖에서 걷고 행 수 > INT 0 비교쌍을 등록한다. 순서가
 * '생산자 먼저'로 짜여 있다 — 스캔 출력 → GROUP BY → 분석함수 → 최종 출력 → ORDER BY.
 * 바뀐 것: 신설(+277줄). 이 파일에서 가장 큰 함수.
 */
static void
domain_walk_xasl (DOMAIN_LOAD_CONTEXT * ctx, XASL_NODE * xasl)
{
  if (xasl == NULL || ctx->failed)
    {
      return;
    }
  if (xasl->domain_plan != NULL)
    {
      for (int i = 0; i < ctx->n_blocks; i++)
	{
	  if (ctx->blocks[i] == xasl)
	    {
	      domain_note_met_again (ctx, ctx->block_constant_branches[i]);
	      break;
	    }
	}
      return;
    }
  if (ctx->n_blocks == ctx->max_blocks)
    {
      const int max = ctx->max_blocks == 0 ? 8 : ctx->max_blocks * 2;
      XASL_NODE **blocks = (XASL_NODE **) db_private_realloc (ctx->thread_p, ctx->blocks, max * sizeof (*blocks));
      int *constant_branches = blocks == NULL ? NULL
	: (int *) db_private_realloc (ctx->thread_p, ctx->block_constant_branches, max * sizeof (*constant_branches));
      if (blocks != NULL)
	{
	  ctx->blocks = blocks;
	}
      if (constant_branches == NULL)
	{
	  ctx->failed = true;
	  return;
	}
      ctx->block_constant_branches = constant_branches;
      ctx->max_blocks = max;
    }
  ctx->blocks[ctx->n_blocks] = xasl;
  ctx->block_constant_branches[ctx->n_blocks++] = ctx->constant_branch;
  if (ctx->n_ancestors == ctx->max_ancestors)
    {
      const int max = ctx->max_ancestors == 0 ? 8 : ctx->max_ancestors * 2;
      XASL_NODE **ancestors =
	(XASL_NODE **) db_private_realloc (ctx->thread_p, ctx->ancestors, max * sizeof (*ancestors));
      if (ancestors == NULL)
	{
	  ctx->failed = true;
	  return;
	}
      ctx->ancestors = ancestors;
      ctx->max_ancestors = max;
    }
  ctx->ancestors[ctx->n_ancestors++] = xasl;
  XASL_NODE *previous_block = ctx->block;
  const int entry_constant_branch = ctx->constant_branch;
  /* a subquery of a key range term is no part of the key range */
  const bool entry_key_range = ctx->in_key_range;
  ctx->in_key_range = false;
  ctx->block = xasl;
  xasl->domain_plan = ctx->plan;
  if (XASL_IS_FLAGED (xasl, XASL_TOP_MOST_XASL) && xasl->limit_row_count != NULL)
    {
      /* qexec_execute_mainblock_internal checks the top-most block's LIMIT first and executes nothing more when its row
       * count is not above 0 - a constant row count is the constant branch of everything else of the statement */
      domain_walk_regu (ctx, xasl->limit_offset);
      domain_walk_regu (ctx, xasl->limit_row_count);
      if (domain_regu_is_row_invariant (xasl->limit_row_count)
	  && (xasl->limit_offset == NULL || domain_regu_is_row_invariant (xasl->limit_offset)))
	{
	  domain_push_constant_branch (ctx, DOMAIN_CONSTANT_BRANCH_LIMIT, xasl);
	}
    }
  if (xasl->type == CONNECTBY_PROC)
    {
      /* before its specs are walked: the probe item records the domain the scan coerces to */
      domain_fix_connect_by_probe (ctx, xasl);
    }
  domain_walk_xasl (ctx, xasl->aptr_list);
  domain_walk_xasl (ctx, xasl->bptr_list);
  domain_walk_xasl (ctx, xasl->dptr_list);
  /* the scan loop takes a row on only when the block's if_pred holds (qexec_intprt_fnc, after the join
   * predicates): what reads the qualified rows - fptr, the inner scans, the row numbers, the outputs - lies below it,
   * so a constant if_pred is their constant branch */
  const int block_constant_branch = ctx->constant_branch;
  domain_walk_pred (ctx, xasl->if_pred);
  int if_constant_branch = block_constant_branch;
  if (domain_pred_is_row_invariant (xasl->if_pred))
    {
      domain_push_constant_branch (ctx, DOMAIN_CONSTANT_BRANCH_PRED_TRUE, xasl->if_pred);
      if_constant_branch = ctx->constant_branch;
      ctx->constant_branch = block_constant_branch;
    }
  ctx->constant_branch = if_constant_branch;
  domain_walk_xasl (ctx, xasl->fptr_list);
  ctx->constant_branch = block_constant_branch;
  domain_walk_xasl (ctx, xasl->connect_by_ptr);
  switch (xasl->type)
    {
    case BUILDLIST_PROC:
      domain_walk_xasl (ctx, xasl->proc.buildlist.eptr_list);
      break;
    case UNION_PROC:
    case DIFFERENCE_PROC:
    case INTERSECTION_PROC:
      domain_walk_xasl (ctx, xasl->proc.union_.left);
      domain_walk_xasl (ctx, xasl->proc.union_.right);
      domain_walk_set_columns (ctx, xasl);
      break;
    case MERGELIST_PROC:
      domain_walk_xasl (ctx, xasl->proc.mergelist.outer_xasl);
      domain_walk_xasl (ctx, xasl->proc.mergelist.inner_xasl);
      domain_walk_specs (ctx, xasl->proc.mergelist.outer_spec_list);
      domain_walk_specs (ctx, xasl->proc.mergelist.inner_spec_list);
      domain_add_merge_compares (ctx, xasl);
      break;
    case HASHJOIN_PROC:
      domain_walk_xasl (ctx, xasl->proc.hashjoin.outer.xasl);
      domain_walk_xasl (ctx, xasl->proc.hashjoin.inner.xasl);
      domain_walk_position_list (ctx, xasl->proc.hashjoin.outer.regu_list_pred, xasl->proc.hashjoin.outer.xasl, NULL);
      domain_walk_position_list (ctx, xasl->proc.hashjoin.inner.regu_list_pred, xasl->proc.hashjoin.inner.xasl, NULL);
      break;
    case CTE_PROC:
      domain_walk_xasl (ctx, xasl->proc.cte.non_recursive_part);
      domain_walk_xasl (ctx, xasl->proc.cte.recursive_part);
      domain_walk_set_columns (ctx, xasl);
      break;
    case MERGE_PROC:
      domain_walk_xasl (ctx, xasl->proc.merge.update_xasl);
      domain_walk_xasl (ctx, xasl->proc.merge.insert_xasl);
      break;
    default:
      break;
    }
  domain_walk_specs (ctx, xasl->spec_list);
  domain_walk_specs (ctx, xasl->merge_spec);
  domain_walk_pred (ctx, xasl->during_join_pred);
  domain_walk_pred (ctx, xasl->after_join_pred);
  ctx->constant_branch = if_constant_branch;
  domain_walk_pred (ctx, xasl->instnum_pred);
  domain_walk_pred (ctx, xasl->ordbynum_pred);
  domain_walk_regu (ctx, xasl->orderby_limit);
  /* the LIMIT is checked before the scan: outside the if_pred's constant branch, and outside its own when the block is
   * the top-most one */
  ctx->constant_branch = XASL_IS_FLAGED (xasl, XASL_TOP_MOST_XASL) ? entry_constant_branch : block_constant_branch;
  domain_walk_regu (ctx, xasl->limit_offset);
  domain_walk_regu (ctx, xasl->limit_row_count);
  ctx->constant_branch = block_constant_branch;
  if (xasl->limit_row_count != NULL)
    {
      /* qexec_check_limit_clause runs the query only for a row count greater than an INT 0 */
      REGU_VARIABLE *const regu[2] = { xasl->limit_row_count, NULL };
      DOMAIN_PLAN_ITEM *const column[2] = { NULL, NULL };
      const DB_VALUE *const literal[2] = { NULL, &domain_Int_zero };
      domain_add_compare_pair (ctx, regu, column, literal, &xasl->limit_compare);
    }
  domain_walk_regu (ctx, xasl->level_regu);
  domain_walk_regu (ctx, xasl->isleaf_regu);
  domain_walk_regu (ctx, xasl->iscycle_regu);
  ctx->constant_branch = if_constant_branch;
  for (SELUPD_LIST * p = xasl->selected_upd_list; p != NULL; p = p->next)
    {
      for (REGU_VARLIST_LIST list = p->select_list; list != NULL; list = list->next)
	{
	  domain_walk_list (ctx, list->list);
	}
    }
  /* a list or a value built from the qualified rows is below the if_pred's constant branch; the other procedures keep
   * the block's */
  ctx->constant_branch = xasl->type == BUILDLIST_PROC
    || xasl->type == BUILDVALUE_PROC ? if_constant_branch : block_constant_branch;
  switch (xasl->type)
    {
    case BUILDLIST_PROC:
      {
	BUILDLIST_PROC_NODE *b = &xasl->proc.buildlist;
	/* the scan output (the intermediate list the GROUP BY and analytic passes read) first: producers before
	 * their readers */
	domain_walk_out (ctx, xasl->outptr_list);
	REGU_VARIABLE_LIST scan_columns = xasl->outptr_list == NULL ? NULL : xasl->outptr_list->valptrp;
	domain_walk_list (ctx, b->g_scan_regu_list);
	domain_walk_position_list (ctx, b->g_regu_list, NULL, scan_columns);
	domain_walk_agg (ctx, b->g_agg_list);
	domain_walk_out (ctx, b->g_outptr_list);
	domain_walk_position_list (ctx, b->g_hk_sort_regu_list, NULL, scan_columns);
	domain_walk_list (ctx, b->g_hk_scan_regu_list);
	domain_walk_pred (ctx, b->g_having_pred);
	domain_walk_pred (ctx, b->g_grbynum_pred);
	domain_walk_sort (ctx, b->groupby_list, scan_columns);
	domain_walk_sort (ctx, b->after_groupby_list, b->g_outptr_list == NULL ? NULL : b->g_outptr_list->valptrp);
	domain_walk_list (ctx, b->a_scan_regu_list);
	domain_walk_position_list (ctx, b->a_regu_list, NULL, scan_columns);
	domain_walk_analytic (ctx, b->a_eval_list, b->a_outptr_list_ex);
	domain_walk_out (ctx, b->a_outptr_list);
	domain_walk_out (ctx, b->a_outptr_list_ex);
	domain_walk_out (ctx, b->a_outptr_list_interm);
	domain_mark_aggregate_operands (xasl);
      }
      break;
    case BUILDVALUE_PROC:
      domain_walk_agg (ctx, xasl->proc.buildvalue.agg_list);
      domain_walk_arith (ctx, xasl->proc.buildvalue.outarith_list);
      domain_walk_pred (ctx, xasl->proc.buildvalue.having_pred);
      domain_mark_aggregate_operands (xasl);
      break;
    case OBJFETCH_PROC:
      domain_walk_pred (ctx, xasl->proc.fetch.set_pred);
      break;
    case CONNECTBY_PROC:
      {
	CONNECTBY_PROC_NODE *b = &xasl->proc.connect_by;
	domain_walk_pred (ctx, b->start_with_pred);
	domain_walk_pred (ctx, b->after_connect_by_pred);
	domain_walk_list (ctx, b->regu_list_pred);
	domain_walk_list (ctx, b->regu_list_rest);
	domain_walk_list (ctx, b->prior_regu_list_pred);
	domain_walk_list (ctx, b->prior_regu_list_rest);
	domain_walk_list (ctx, b->after_cb_regu_list_pred);
	domain_walk_list (ctx, b->after_cb_regu_list_rest);
	domain_walk_out (ctx, b->prior_outptr_list);
      }
      break;
    case UPDATE_PROC:
      domain_walk_pred (ctx, xasl->proc.update.cons_pred);
      domain_walk_assignments (ctx, xasl->proc.update.assigns, xasl->proc.update.num_assigns);
      break;
    case INSERT_PROC:
      domain_walk_pred (ctx, xasl->proc.insert.cons_pred);
      for (int i = 0; i < xasl->proc.insert.num_val_lists; i++)
	{
	  if (xasl->proc.insert.valptr_lists[i] != NULL)
	    {
	      domain_walk_list (ctx, xasl->proc.insert.valptr_lists[i]->valptrp, DOMAIN_CTX_ASSIGN);
	    }
	}
      if (xasl->proc.insert.odku != NULL)
	{
	  domain_walk_pred (ctx, xasl->proc.insert.odku->cons_pred);
	  domain_walk_assignments (ctx, xasl->proc.insert.odku->assignments, xasl->proc.insert.odku->num_assigns);
	}
      break;
    default:
      break;
    }
  ctx->constant_branch = if_constant_branch;
  domain_walk_out (ctx, xasl->outptr_list);
  OUTPTR_LIST *output = domain_block_output (xasl);
  domain_walk_sort (ctx, xasl->orderby_list, output == NULL ? NULL : output->valptrp, xasl);
  domain_walk_sort (ctx, xasl->after_iscan_list, xasl->outptr_list == NULL ? NULL : xasl->outptr_list->valptrp);
  if (xasl->single_tuple != NULL)
    {
      /* a single-row subquery copies its result row into single_tuple (qdata_get_single_tuple_from_list_id):
       * value k there is written by list column k, which a scalar-subquery reader's value pointer then finds */
      int k = 0;
      for (QPROC_DB_VALUE_LIST value = xasl->single_tuple->valp; value != NULL && !ctx->failed; value = value->next)
	{
	  DOMAIN_LOAD_ENTRY *column = domain_load_entry_of (domain_list_column (ctx, xasl, k++));
	  if (column != NULL && column->output[1] == NULL)
	    {
	      column->output[1] = value->val;
	    }
	}
    }
  /* an uncorrelated scalar subquery runs once before the scan that reads it (qexec_execute_mainblock_internal), fetched
   * through the regu that owns it: a predicate operand, or a regu no predicate holds (an index key range reads a
   * copy) */
  ctx->constant_branch = block_constant_branch;
  domain_walk_regu (ctx, xasl->precomp_owner_regu, DOMAIN_CTX_COMPARE);
  ctx->constant_branch = if_constant_branch;
  domain_walk_xasl (ctx, xasl->scan_ptr);
  /* the next block is no part of this one's execution: outside its constant branches, and not an outer block of it */
  ctx->constant_branch = entry_constant_branch;
  assert (ctx->n_ancestors > 0 && ctx->ancestors[ctx->n_ancestors - 1] == xasl);
  ctx->n_ancestors--;
  domain_walk_xasl (ctx, xasl->next);
  ctx->block = previous_block;
  ctx->in_key_range = entry_key_range;
}

/*
 * Resolution pass: after the walk every derived consumer reads its producer and every node the compiler left
 * without a type becomes a late-binding node when all its operands are known. It recurses producer first, so the
 * late-binding nodes come out in an order resolve_domains can resolve them in, whatever order the walk met them.
 */

/*
 * [리뷰] domain_owner_load_entry — 로드 엔트리의 alias(값 포인터가 생산자 항목을 공유하기로 한 경우의 대표)를 따라가 '답을 가진 쪽'을 돌려준다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: 한 단계만 따라간다 — alias 가 또 alias 를 가지지 않는다는 것이 암묵 전제다.
 * 바뀐 것: 신설(+5줄).
 */
static DOMAIN_LOAD_ENTRY *
domain_owner_load_entry (DOMAIN_LOAD_ENTRY * load_entry)
{
  return load_entry != NULL && load_entry->alias != NULL ? load_entry->alias : load_entry;
}

/*
 * [리뷰] domain_is_value_pointer — 로드 엔트리가 TYPE_CONSTANT regu(값 포인터, 즉 생산자가 써 둔 칸을 읽는 자리)인지 본다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: domain_link_producer 가 '컴파일 도메인을 믿어도 되는가'를 가를 때 쓴다 — 값 포인터는 독자의 컴파일 도메인이 아니라 생산자의 도메인을 따라야 하기 때문.
 * 바뀐 것: 신설(+5줄).
 */
static bool
domain_is_value_pointer (const DOMAIN_LOAD_ENTRY * load_entry)
{
  return load_entry->regu != NULL && load_entry->regu->type == TYPE_CONSTANT;
}

/* GROUP_CONCAT accumulates in its compiled string type under the function's collation (qdata_group_concat_first_value):
 * the function domain resolve_domains resolves follows the argument (a CHAR bind makes it CHAR), the accumulator does
 * not. An output column reading it is retyped with the function domain before its first fetch (qexec_end_one_iteration,
 * the GROUP BY setup), so the list carries that domain; any other reader sees the accumulator's own value. */
/*
 * [리뷰] domain_reads_group_concat_value — 독자가 GROUP_CONCAT 누적기의 값을 (출력 컬럼이 아닌 자리에서) 읽는 경우인지 판정한다. 게이트의
 * GROUP_CONCAT collation 규칙을 적용할 조건.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: 생산자가 FIXED_AGG·AGG 문맥·opcode PT_GROUP_CONCAT 이고 독자 문맥이 LIST_COLUMN 이 아닐 때 true.
 * 바뀐 것: 신설(+6줄).
 */
static bool
domain_reads_group_concat_value (const DOMAIN_LOAD_ENTRY * reader, const DOMAIN_LOAD_ENTRY * producer)
{
  return producer->kind == DOMAIN_LOAD_FIXED_AGG && producer->cold.ctx == DOMAIN_CTX_AGG
    && producer->cold.opcode == PT_GROUP_CONCAT && reader->cold.ctx != DOMAIN_CTX_LIST_COLUMN;
}

static void domain_resolve_record (DOMAIN_LOAD_CONTEXT * ctx, DOMAIN_LOAD_ENTRY * load_entry);

/* The item a node's operand is resolved from: through value pointers, list positions and wrappers that share a resolved
 * domain table entry to the bind or node owning it, so resolve_domains sees a bind's value (a value-dependent argument
 * type). */
/*
 * [리뷰] domain_link_source — 생산자를 따라가는 사슬(follows_producer)을 끝까지 좇아 '실제로 답을 내는' 항목을 돌려준다. 지연 바인딩 노드가 링크로 걸 대상을
 * 한 점으로 정규화한다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: 매 단계 alias 를 먼저 푼 뒤 follows_producer·producer 가 있으면 생산자로 넘어간다. 루프 변수 이름이 `constant_branch` 지만 실제로는
 * 256회 홉 상한일 뿐이고, 상한에 걸리면 정규화되지 않은 item 을 그대로 돌려준다.
 * 바뀐 것: 신설(+14줄).
 * [지적 C3-03]
 */
static DOMAIN_PLAN_ITEM *
domain_link_source (DOMAIN_PLAN_ITEM * item)
{
  for (int constant_branch = 0; item != NULL && constant_branch < 256; constant_branch++)
    {
      DOMAIN_LOAD_ENTRY *load_entry = domain_owner_load_entry (domain_load_entry_of (item));
      if (!load_entry->follows_producer || load_entry->producer == NULL)
	{
	  return &load_entry->item;
	}
      item = &load_entry->producer->item;
    }
  return item;
}

/* A derived consumer reads its producer: the producer's resolved domain table entry (ALIAS) or its domain. A value
 * pointer takes the producer's domain even when it was compiled with another one (the reader's), because the value is
 * the producer's; a compiled list position or VALUES column keeps its domain, which is what its list holds. */
/*
 * [리뷰] domain_link_producer — CONSUMER 엔트리(값 포인터·리스트 위치·VALUES 컬럼)를 생산자에 묶어 해소한다. 생산자가 게이트 해소 대상이면 ALIAS 로
 * resolved_index 를 공유하고, 아니면 생산자의 도메인을 그대로 가져온다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: 값 포인터가 아니고 타입·collation 이 모두 확정이면 그대로 known. 단 TYPE_POSITION 은 예외로, 생산자 사슬의 뿌리가 같은 타입(또는 둘 다 문자형)의
 * 리터럴/bind 를 들고 있으면 그 생산자를 따라간다. 재귀 CTE 가 자기 컬럼을 읽는 경우(생산자 state==1)는 비재귀 가지 컬럼으로 바꿔 잡는다. GROUP_CONCAT 누적기를 읽는
 * 값 포인터는 collation 축 지연 바인딩 노드로 승격한다.
 * 바뀐 것: 신설(+79줄).
 */
static void
domain_link_producer (DOMAIN_LOAD_CONTEXT * ctx, DOMAIN_LOAD_ENTRY * load_entry)
{
  DOMAIN_PLAN_ITEM *item = &load_entry->item;
  const bool value_pointer = domain_is_value_pointer (load_entry);
  /* a compiled position keeps its domain unless the values give its collation: then its list's column does */
  if (!value_pointer && domain_type_is_fixed (item->fixed.domain) && !domain_character_is_variable (item->fixed.domain))
    {
      load_entry->known = true;
      if (load_entry->regu != NULL && load_entry->regu->type == TYPE_POSITION && load_entry->producer != NULL)
	{
	  /* the list holds its producer's values: when the producer carries a literal or a bind of the position's
	   * type, a node over the position types that value as its first value would */
	  domain_resolve_record (ctx, load_entry->producer);
	  DOMAIN_LOAD_ENTRY *producer = domain_owner_load_entry (load_entry->producer);
	  const DOMAIN_LOAD_ENTRY *root =
	    domain_owner_load_entry (domain_load_entry_of (domain_link_source (&producer->item)));
	  const TP_DOMAIN *carried = root->item.fixed.domain;
	  if (root->literal_value && carried != NULL
	      && (TP_DOMAIN_TYPE (carried) == TP_DOMAIN_TYPE (item->fixed.domain)
		  || (TP_IS_CHAR_TYPE (TP_DOMAIN_TYPE (carried))
		      && TP_IS_CHAR_TYPE (TP_DOMAIN_TYPE (item->fixed.domain)))))
	    {
	      load_entry->producer = producer;
	      load_entry->follows_producer = true;
	    }
	}
      return;
    }
  if (load_entry->producer == NULL)
    {
      /* a value pointer no walked node writes (an execution counter such as inst_num): its compiled domain */
      load_entry->known = domain_type_is_fixed (item->fixed.domain);
      return;
    }
  domain_resolve_record (ctx, load_entry->producer);
  DOMAIN_LOAD_ENTRY *producer = domain_owner_load_entry (load_entry->producer);
  if (producer->state == 1 && producer->regu == NULL && producer->kind == DOMAIN_LOAD_NODE && producer->n_link > 0)
    {
      /* a recursive CTE part reads the column it is producing: its first iteration reads the non-recursive part's
       * rows (qexec_execute_cte), so that column is its producer; the CTE column itself unifies both parts */
      DOMAIN_LOAD_ENTRY *first = domain_owner_load_entry (domain_load_entry_of (producer->link[0]));
      domain_resolve_record (ctx, first);
      producer = first;
    }
  if (!producer->known)
    {
      load_entry->known = false;
      return;
    }
  if (value_pointer && domain_reads_group_concat_value (load_entry, producer) && producer->item.resolved_index >= 0
      && domain_character_is_variable (item->fixed.domain))
    {
      /* a reader of the accumulator of a GROUP_CONCAT resolve_domains resolves takes the accumulator's string under the
       * resolved collation, a late-binding node on the collation axis: the resolver's GROUP_CONCAT rule */
      load_entry->kind = DOMAIN_LOAD_NODE;
      load_entry->cold.opcode = PT_GROUP_CONCAT;
      load_entry->link[0] = &producer->item;
      load_entry->literal[0] = NULL;
      load_entry->n_link = 1;
      load_entry->consumer = item->fixed.domain;
      item->flags |= DOMAIN_PLAN_LATE_BIND_COLLATION;
      domain_mark_late_bind_node (ctx, load_entry);
      load_entry->known = !ctx->failed;
      return;
    }
  if (producer->item.resolved_index >= 0)
    {
      item->flags |= DOMAIN_PLAN_ALIAS;
      item->resolved_index = producer->item.resolved_index;
    }
  else
    {
      item->fixed.domain = producer->item.fixed.domain;
    }
  load_entry->producer = producer;
  load_entry->follows_producer = true;
  load_entry->known = true;
}

/* A node over known operands becomes a late-binding node; a compiled aggregate or analytic gets its accumulator
 * domain derived once from its operand's. A set-operation column over compiled branches of one type is that
 * type. */
/*
 * [리뷰] domain_resolve_node — NODE / FIXED_AGG 엔트리의 피연산자를 모두 해소한 뒤, 그 노드를 (a) 로드가 끝낼 수 있는지 (b) 실행 전 게이트로 넘길지
 * 판정한다. 로드 단계 해소 패스의 핵심 분기.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: 링크마다 domain_link_source 로 정규화 → 재귀 해소 → 다시 정규화(사슬이 움직였을 수 있으므로) 한다. MEDIAN/PERCENTILE 은 인자가 값 인자인지로
 * VALUE_ARGUMENT 를 표시. 전부 known 이고 FIXED_AGG 이며 variable POS 가 없으면 domain_resolve() 를 **로드 시점에 한 번** 돌려 누적기
 * 규칙(ACCUMULATOR)을 확정한다. 집합 연산 컬럼은 가지 타입이 모두 같으면 그 타입으로 끝낸다. 그 외는 domain_mark_late_bind_node 로 게이트에 넘기고
 * cold.ctx 를 실행용 문맥으로 바꾼다.
 * 바뀐 것: 신설(+88줄).
 */
static void
domain_resolve_node (DOMAIN_LOAD_CONTEXT * ctx, DOMAIN_LOAD_ENTRY * load_entry)
{
  DOMAIN_PLAN_ITEM *item = &load_entry->item;
  const bool compiled = domain_type_is_fixed (item->fixed.domain);
  if (load_entry->n_link <= 0)
    {
      load_entry->known = load_entry->kind == DOMAIN_LOAD_FIXED_AGG && compiled;
      return;
    }
  bool known = true, any_variable_pos = false;
  for (int i = 0; i < load_entry->n_link; i++)
    {
      load_entry->link[i] = domain_link_source (load_entry->link[i]);
      DOMAIN_LOAD_ENTRY *operand = domain_owner_load_entry (domain_load_entry_of (load_entry->link[i]));
      domain_resolve_record (ctx, operand);
      /* the link may have moved through a chain: re-read the source after the operand is resolved */
      load_entry->link[i] = domain_link_source (&operand->item);
      operand = domain_owner_load_entry (domain_load_entry_of (load_entry->link[i]));
      known = known && operand->known;
      any_variable_pos = any_variable_pos || operand->item.resolved_index >= 0;
      if (operand->regu != NULL && operand->regu->type == TYPE_DBVAL)
	{
	  load_entry->literal[i] = &operand->regu->value.dbval;
	}
    }
  if (load_entry->kind == DOMAIN_LOAD_FIXED_AGG
      && (load_entry->cold.opcode == PT_MEDIAN || load_entry->cold.opcode == PT_PERCENTILE_CONT
	  || load_entry->cold.opcode == PT_PERCENTILE_DISC))
    {
      /* at execution: a value argument takes its value-dependent argument type, a value-less string is DOUBLE. The
       * argument of a function over a list (GROUP BY, analytic) is a value pointer; its source tells which. */
      const DOMAIN_LOAD_ENTRY *argument = domain_owner_load_entry (domain_load_entry_of (load_entry->link[0]));
      if (argument->literal_value
	  || (argument->regu == NULL && argument->kind == DOMAIN_LOAD_NODE
	      && argument->cold.opcode == T_EVALUATE_VARIABLE))
	{
	  item->flags |= DOMAIN_PLAN_VALUE_ARGUMENT;
	}
    }
  if (!known)
    {
      load_entry->known = compiled && load_entry->kind == DOMAIN_LOAD_FIXED_AGG;
      return;
    }
  if (load_entry->kind == DOMAIN_LOAD_FIXED_AGG && compiled && !any_variable_pos)
    {
      const DOMAIN_PLAN_ITEM *argument = load_entry->link[0];
      DOMAIN_OPERAND operand = { argument->fixed.domain, TP_DOMAIN_TYPE (argument->fixed.domain), -1, false };
      RESOLVED_DOMAIN resolved;
      bool needs_late_bind = false;
      if (domain_type_is_fixed (argument->fixed.domain)
	  && domain_resolve ((DOMAIN_CTX) load_entry->cold.ctx, load_entry->cold.opcode, &operand, 1,
			     item->fixed.domain, &resolved, &needs_late_bind) == NO_ERROR && !needs_late_bind
	  && resolved.domain != NULL)
	{
	  /* the function domain stays the compiled one; the accumulator is the operand's rule */
	  item->fixed.operand_domain[0] = resolved.operand_domain[0];
	  item->fixed.conv[0] = resolved.conv[0];
	  item->flags |= DOMAIN_PLAN_ACCUMULATOR;
	}
      load_entry->known = true;
      return;
    }
  if (load_entry->regu == NULL && load_entry->kind == DOMAIN_LOAD_NODE && load_entry->cold.ctx == DOMAIN_CTX_LIST_COLUMN
      && !any_variable_pos)
    {
      /* a set-operation column over compiled branches: one type, or resolve_domains unifies them at execution */
      const TP_DOMAIN *first = load_entry->link[0]->fixed.domain;
      bool same = true;
      for (int i = 1; i < load_entry->n_link; i++)
	{
	  same = same && TP_DOMAIN_TYPE (load_entry->link[i]->fixed.domain) == TP_DOMAIN_TYPE (first);
	}
      if (same)
	{
	  item->fixed.domain = first;
	  load_entry->known = true;
	  return;
	}
    }
  domain_mark_late_bind_node (ctx, load_entry);
  if (load_entry->kind == DOMAIN_LOAD_NODE && load_entry->cold.ctx != DOMAIN_CTX_LIST_COLUMN)
    {
      load_entry->cold.ctx = domain_late_bind_context ((OPERATOR_TYPE) load_entry->cold.opcode);
    }
  load_entry->known = !ctx->failed;
}

/*
 * [리뷰] domain_resolve_record — 엔트리 하나를 해소하는 진입점 — kind 별로 domain_link_producer / domain_resolve_node 로 보낸다.
 * state(0/1/2)로 중복과 순환을 막는다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: state!=0 이면 즉시 반환하므로 진행 중(state==1)인 것을 다시 만나면 '아직 모름'으로 남는다 — 재귀 CTE 의 자기 참조가 여기서 멈춘다. ARITH_REGU 는
 * 노드의 fixed 를 통째로 복사하고 노드가 LATE_BIND 면 ALIAS 로 resolved_index 를 공유한다. LEAF 는 resolved_index·리터럴·확정 도메인 중 하나면
 * known.
 * 바뀐 것: 신설(+42줄).
 */
static void
domain_resolve_record (DOMAIN_LOAD_CONTEXT * ctx, DOMAIN_LOAD_ENTRY * load_entry)
{
  load_entry = domain_owner_load_entry (load_entry);
  if (load_entry == NULL || load_entry->state != 0 || ctx->failed)
    {
      /* done, or in progress: a recursive CTE part reads the column it produces; the reader stays variable */
      return;
    }
  load_entry->state = 1;
  DOMAIN_PLAN_ITEM *item = &load_entry->item;
  switch (load_entry->kind)
    {
    case DOMAIN_LOAD_CONSUMER:
      domain_link_producer (ctx, load_entry);
      break;
    case DOMAIN_LOAD_ARITH_REGU:
      {
	domain_resolve_record (ctx, load_entry->producer);
	DOMAIN_LOAD_ENTRY *node = domain_owner_load_entry (load_entry->producer);
	item->fixed = node->item.fixed;
	if (node->item.flags & DOMAIN_PLAN_LATE_BIND)
	  {
	    item->flags |= DOMAIN_PLAN_ALIAS;
	    item->resolved_index = node->item.resolved_index;
	  }
	load_entry->producer = node;
	load_entry->follows_producer = true;
	load_entry->known = node->known;
      }
      break;
    case DOMAIN_LOAD_NODE:
    case DOMAIN_LOAD_FIXED_AGG:
      domain_resolve_node (ctx, load_entry);
      break;
    case DOMAIN_LOAD_LEAF:
      load_entry->known = item->resolved_index >= 0 || load_entry->literal_value
	|| domain_type_is_fixed (item->fixed.domain);
      break;
    }
  load_entry->state = 2;
}

/* The unresolved-domain check (load): both axes are strict: an item resolve_domains does not resolve has a fixed
 * type, and a fixed string whose collation the values give is a variable POS recording its bound value's domain. */
/*
 * [리뷰] domain_plan_validate — 로드의 마지막 관문 — 공개된 모든 항목이 타입과 collation 둘 다 확정됐거나 게이트가 책임지기로 표시돼 있는지 본다. false 면
 * stx_build_domain_plan 이 ER_QPROC_DOMAIN_UNRESOLVED 로 로드를 거부한다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: LATE_BIND·ALIAS 플래그가 있거나 synthetic 인 항목은 건너뛴다. 나머지는 (1) 타입이 VARIABLE 이면 거부, (2) collation 이 미확정인데
 * LATE_BIND_COLLATION 표시가 없으면 거부. 타입 축과 collation 축을 각각 한 조건으로 고정한 것이 이 PR 의 '게이트 둘' 중 로드 측 관문이다.
 * 바뀐 것: 신설(+22줄). 파일에서 몇 안 되는 비-static 함수.
 */
bool
domain_plan_validate (const DOMAIN_PLAN * plan)
{
  for (int i = 0; i < plan->n_items; i++)
    {
      const DOMAIN_PLAN_ITEM *item = &plan->items[i];
      if ((item->flags & (DOMAIN_PLAN_LATE_BIND | DOMAIN_PLAN_ALIAS)) || plan->items_cold[i].synthetic)
	{
	  /* a synthetic list column no reader could use leaves its readers variable, and they answer for it */
	  continue;
	}
      if (!domain_type_is_fixed (item->fixed.domain))
	{
	  return false;
	}
      if (domain_character_is_variable (item->fixed.domain) && !(item->flags & DOMAIN_PLAN_LATE_BIND_COLLATION))
	{
	  return false;
	}
    }
  return true;
}

/*
 * [리뷰] domain_plan_alloc — 플랜 수명 배열(count × size)을 XASL 언팩 버퍼에서 잡는다. 오버플로를 막는 곱셈 검사가 붙은 stx_alloc_struct 래퍼.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: count==0 이면 NULL 을 정상 반환하므로 호출자는 NULL 을 실패로만 보면 안 된다(대부분 n>0 을 먼저 검사한다). count<0 이거나 size*count 가
 * INT_MAX 를 넘으면 NULL.
 * 바뀐 것: 신설(+13줄).
 */
static void *
domain_plan_alloc (THREAD_ENTRY * thread_p, int count, size_t size)
{
  if (count == 0)
    {
      return NULL;
    }
  if (count < 0 || size > INT_MAX / (size_t) count)
    {
      return NULL;
    }
  return stx_alloc_struct (thread_p, (int) (count * size));
}

/*
 * [리뷰] domain_compare_refs — plan->const_refs(값 참조 번호를 가진 항목들)를 ref 오름차순으로 정렬하기 위한 qsort 비교자. 실행의 bind 단계가 참조를
 * 순서대로 훑을 수 있게 한다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: ref 가 같으면 항목 주소로 동점을 가른다. const_refs 원소는 모두 연속 배열 plan->items 안을 가리키므로 주소 순서 = 항목 인덱스 순서로
 * 결정적이다(domain_assign_references 가 같은 (위치, 도메인, 변환정책) 에 같은 ref 를 재사용하므로 동점은 실제로 생긴다).
 * 바뀐 것: 신설(+11줄).
 */
static int
domain_compare_refs (const void *lhs, const void *rhs)
{
  const DOMAIN_PLAN_ITEM *a = *(const DOMAIN_PLAN_ITEM * const *) lhs;
  const DOMAIN_PLAN_ITEM *b = *(const DOMAIN_PLAN_ITEM * const *) rhs;
  if (a->ref != b->ref)
    {
      return a->ref < b->ref ? -1 : 1;
    }
  return a < b ? -1 : a > b ? 1 : 0;
}

/* The constant expression a load entry's regu computes, if resolve_domains evaluates it once: a constant arithmetic
 * node (its value is the node's item's) or a constant function that caches. */
/*
 * [리뷰] domain_constant_of — 로드 엔트리가 '상수 식'(행과 무관해 게이트가 첫 행 전에 한 번 계산할 수 있는 산술·함수 노드)인지 보고 그 항목을 돌려준다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: INARITH/OUTARITH 는 arithptr 의 항목을, TYPE_FUNC 는 regu 자신의 항목을 보고, operand_class 가 OPERAND_CONST 일 때만
 * 돌려준다. 그 외는 NULL.
 * 바뀐 것: 신설(+19줄).
 */
static DOMAIN_PLAN_ITEM *
domain_constant_of (const DOMAIN_LOAD_ENTRY * load_entry)
{
  const REGU_VARIABLE *regu = load_entry->regu;
  if (regu == NULL)
    {
      return NULL;
    }
  DOMAIN_PLAN_ITEM *item = NULL;
  if ((regu->type == TYPE_INARITH || regu->type == TYPE_OUTARITH) && regu->value.arithptr != NULL)
    {
      item = regu->value.arithptr->plan_item;
    }
  else if (regu->type == TYPE_FUNC)
    {
      item = regu->plan_item;
    }
  return item != NULL && item->operand_class == OPERAND_CONST ? item : NULL;
}

/*
 * domain_plan_add_item_copies () - the item copy of a value pointer that does not share its producer's execution
 *   domain: the producer's published item - its resolved index, reference and answers, so the consumer reads the same
 *   resolutions - with the consumer's execution domain and variable domain flags; after the constant references, which
 *   the producer's item takes
 */
/*
 * [리뷰] domain_plan_add_item_copies — 생산자 항목을 공유(alias)하되 자기 실행 도메인이 필요해 별도 인덱스를 받은 엔트리에, 생산자 항목 내용을 복사하고 자기
 * variable 플래그·node_domain_index 만 되살린다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: alias 가 있고 인덱스가 다른 엔트리만 대상. VARIABLE/VARIABLE_POSITION 플래그를 지우고 자기 r->variable 로 다시 세우며 cold 도 자기 것으로
 * 덮어쓴다 — '소비자의 노드는 자기 실행 도메인을 따로 갖는다'는 stx_build_domain_plan 주석의 구현부.
 * 바뀐 것: 신설(+17줄).
 */
static void
domain_plan_add_item_copies (DOMAIN_LOAD_CONTEXT * ctx, DOMAIN_PLAN * plan)
{
  for (DOMAIN_LOAD_ENTRY * r = ctx->head; r != NULL; r = r->next)
    {
      if (r->alias == NULL || r->index == r->alias->index)
	{
	  continue;
	}
      DOMAIN_PLAN_ITEM *item = &plan->items[r->index];
      *item = plan->items[r->alias->index];
      item->flags &= ~(DOMAIN_PLAN_VARIABLE | DOMAIN_PLAN_VARIABLE_POSITION);
      item->flags |= r->variable ? DOMAIN_PLAN_VARIABLE : 0;
      item->node_domain_index = r->item.node_domain_index;
      plan->items_cold[r->index] = r->cold;
    }
}

/*
 * domain_plan_add_constants () - every constant expression gets a value of its own in resolve_domains' array, which
 *   resolve_domains fills once before the main block: this replaces fetch's FETCH_ALL_CONST marking. Nested constants
 *   come first, in the order the walk appended them.
 */
/*
 * [리뷰] domain_plan_add_constants — 상수 식들에 값 참조 번호(ref)를 매기고 plan->constant_expressions 배열(항목 + 그 값을 계산할 regu)을
 * 만든다. 실행 전 게이트의 '상수 식 단계'가 읽을 목록이다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: 두 번 훑는다 — 먼저 ref 를 매겨 개수를 확정하고, 배열을 잡아 0 으로 민 뒤 다시 훑어 (item, regu) 를 채운다. 같은 항목이 여러 엔트리에서 나와도 처음 것만
 * 들어간다(`.item == NULL` 검사). 개수가 0이면 배열 없이 true.
 * 바뀐 것: 신설(+36줄).
 */
static bool
domain_plan_add_constants (THREAD_ENTRY * thread_p, DOMAIN_LOAD_CONTEXT * ctx, DOMAIN_PLAN * plan)
{
  const int base = plan->n_refs;
  for (DOMAIN_LOAD_ENTRY * r = ctx->head; r != NULL; r = r->next)
    {
      DOMAIN_PLAN_ITEM *item = domain_constant_of (r);
      if (item != NULL && item->ref < 0)
	{
	  item->ref = plan->n_refs++;
	}
    }
  plan->n_constant_expressions = plan->n_refs - base;
  if (plan->n_constant_expressions == 0)
    {
      return true;
    }
  plan->constant_expressions =
    (DOMAIN_PLAN_CONSTANT_EXPRESSION *) domain_plan_alloc (thread_p, plan->n_constant_expressions,
							   sizeof (*plan->constant_expressions));
  if (plan->constant_expressions == NULL)
    {
      return false;
    }
  memset (plan->constant_expressions, 0, sizeof (*plan->constant_expressions) * plan->n_constant_expressions);
  for (DOMAIN_LOAD_ENTRY * r = ctx->head; r != NULL; r = r->next)
    {
      DOMAIN_PLAN_ITEM *item = domain_constant_of (r);
      if (item != NULL && item->ref >= base && plan->constant_expressions[item->ref - base].item == NULL)
	{
	  plan->constant_expressions[item->ref - base].item = item;
	  plan->constant_expressions[item->ref - base].regu = r->regu;
	}
    }
  return true;
}

/* Whether resolve_domains resolves an entry only in the constant expression step (qexec_evaluate_constant_expression):
 * the entry of a node that waits for constant expressions. */
/*
 * [리뷰] domain_resolved_after_constant_expressions — 어떤 resolved_index 의 해소가 상수 식 계산 뒤에야 가능한지 묻는다. 비교가 '상수 단계
 * 이후'로 미뤄져야 하는지 판정하는 기본 술어.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: resolved_index → 그 값을 내는 지연 바인딩 노드(resolved_late_bind_node)로 가서 그 노드의 after_constants 를 읽는다. 생산자가
 * 없으면(-1) false.
 * 바뀐 것: 신설(+6줄).
 */
static bool
domain_resolved_after_constant_expressions (const DOMAIN_PLAN * plan, int resolved_index)
{
  const int producer = plan->resolved_late_bind_node[resolved_index];
  return producer >= 0 && plan->late_bind_links[producer].after_constants;
}

/*
 * domain_plan_add_late_bind_waits () - the late-binding nodes resolve_domains resolves only once the constant
 *   expressions they read were evaluated: a common value folds its operands' value domains, and a
 *   constant expression's value is known only in the constant expression step (qexec_evaluate_constant_expression) - a
 *   NULL without a type drops out of the fold, which its compiled domain does not tell. A node above such a node reads
 *   its resolution, so it waits too (producers come first).
 */
/*
 * [리뷰] domain_plan_add_late_bind_waits — 각 지연 바인딩 노드의 after_constants 를 결정한다 — 피연산자 중 상수 식 참조를 쓰거나, 상수 단계 뒤에
 * 풀리는 다른 노드를 읽으면 이 노드도 상수 단계를 기다려야 한다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: g 를 0부터 올라가며 계산하는데, 전파 조건이 `domain_resolved_after_constant_expressions`(= 다른 노드의 after_constants
 * 읽기)이므로 **late_bind_nodes 가 생산자 먼저 순서**여야 맞는다. 그 순서는 domain_mark_late_bind_node 의 호출 시점(깊이 우선 해소)으로만 보장된다.
 * COMMON_VALUE 문맥 노드만 피연산자의 ref 가 상수 영역인지로 직접 걸린다.
 * 바뀐 것: 신설(+17줄).
 */
static void
domain_plan_add_late_bind_waits (DOMAIN_PLAN * plan, int constant_base)
{
  for (int g = 0; g < plan->n_late_bind_nodes; g++)
    {
      DOMAIN_LATE_BIND_LINK *link = &plan->late_bind_links[g];
      const bool common_value = plan->items_cold[plan->late_bind_nodes[g] - plan->items].ctx == DOMAIN_CTX_COMMON_VALUE;
      for (int i = 0; i < link->n_operands && !link->after_constants; i++)
	{
	  /* a constant expression's reference follows every bind's (domain_plan_add_constants) */
	  const DOMAIN_PLAN_ITEM *operand = link->operands[i];
	  link->after_constants = (common_value && operand->ref >= constant_base)
	    || (operand->resolved_index >= 0
		&& domain_resolved_after_constant_expressions (plan, operand->resolved_index));
	}
    }
}

/* A session variable's name as a read or an assignment carries it: the CHAR literal the parser writes for @name. */
/*
 * [리뷰] domain_session_variable_name — DB_VALUE 가 세션 변수 이름으로 쓸 수 있는 값(NULL 아닌 CHAR)인지 보고 그대로 돌려주거나 NULL 을 준다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: 읽기(T_EVALUATE_VARIABLE)와 대입(T_DEFINE_VARIABLE) 양쪽의 이름 추출이 이 한 술어를 공유한다.
 * 바뀐 것: 신설(+5줄).
 */
static const DB_VALUE *
domain_session_variable_name (const DB_VALUE * value)
{
  return value != NULL && DB_VALUE_DOMAIN_TYPE (value) == DB_TYPE_CHAR && !DB_IS_NULL (value) ? value : NULL;
}

/* The name late-binding node g reads, when it is a session variable read. */
/*
 * [리뷰] domain_session_read_name — g 번째 지연 바인딩 노드가 세션 변수 읽기라면 그 변수 이름 값을 돌려준다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: 노드의 cold.opcode 가 T_EVALUATE_VARIABLE 일 때만 link[0] 자리의 리터럴을 이름으로 본다. opcode 가 다르면 NULL.
 * 바뀐 것: 신설(+6줄).
 */
static const DB_VALUE *
domain_session_read_name (const DOMAIN_PLAN * plan, int g)
{
  return plan->items_cold[plan->late_bind_nodes[g] - plan->items].opcode == T_EVALUATE_VARIABLE
    ? domain_session_variable_name (plan->late_bind_links[g].literal[0]) : NULL;
}

/* The variable a name refers to among the first n, compared as the session compares names; -1 none. */
/*
 * [리뷰] domain_find_session_variable — 수집한 세션 변수 배열에서 이름이 같은 항목의 인덱스를 찾는다. 비교는 intl_identifier_casecmp(식별자 규칙,
 * 대소문자 무시).
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: name 이 NULL 이면 루프가 돌지 않아 -1. 선형 탐색이고, 한 질의의 세션 변수 수가 적다는 전제다.
 * 바뀐 것: 신설(+12줄).
 */
static int
domain_find_session_variable (const DOMAIN_SESSION_VARIABLE * variables, int n, const DB_VALUE * name)
{
  for (int v = 0; name != NULL && v < n; v++)
    {
      if (intl_identifier_casecmp (db_get_string (variables[v].name), db_get_string (name)) == 0)
	{
	  return v;
	}
    }
  return -1;
}

/* The variable an assignment writes, among the first n; -1 when the statement does not read it. */
/*
 * [리뷰] domain_session_define_variable — T_DEFINE_VARIABLE 노드가 수집된 변수 중 어느 것에 대입하는지 인덱스를 돌려준다. 읽기가 하나도 없는 변수에
 * 대한 대입은 -1.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: 왼쪽이 TYPE_DBVAL(이름 리터럴)이고 오른쪽에 plan_item 이 있을 때만 유효로 본다. 그 외는 -1 로 떨어뜨려 세션 변수 묶음에서 제외한다.
 * 바뀐 것: 신설(+10줄).
 */
static int
domain_session_define_variable (const DOMAIN_SESSION_VARIABLE * variables, int n, const ARITH_TYPE * define)
{
  if (define->leftptr == NULL || define->leftptr->type != TYPE_DBVAL || define->rightptr == NULL
      || define->rightptr->plan_item == NULL)
    {
      return -1;
    }
  return domain_find_session_variable (variables, n, domain_session_variable_name (&define->leftptr->value.dbval));
}

/*
 * domain_plan_add_session_variables () - the session variables the statement reads, each with its reads and the values
 *   its assignments store: resolve_domains gives each of them one type per execution. A variable the
 *   statement only assigns is none of them: nothing here reads it.
 */
/*
 * [리뷰] domain_plan_add_session_variables — 세션 변수별로 '이 변수를 읽는 지연 바인딩 노드들'과 '이 변수에 대입하는 항목들'을 한 배열에 모아
 * plan->session_variables 로 공개한다. 게이트의 세션 변수 단계가 읽을 표다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: 읽기가 하나도 없으면 바로 true(표를 만들지 않는다). 세 번 훑는 전형적 counting layout — 먼저 변수별 읽기/대입 수를 세고, reads·assigns 슬라이스
 * 시작점을 잡고 카운터를 0으로 되돌린 뒤 실제 인덱스를 채운다. variables 배열은 n_reads 개로 잡지만 실제 변수 수(n_variables)는 그 이하다.
 * 바뀐 것: 신설(+82줄).
 */
static bool
domain_plan_add_session_variables (THREAD_ENTRY * thread_p, DOMAIN_LOAD_CONTEXT * ctx, DOMAIN_PLAN * plan)
{
  int n_reads = 0;
  for (int g = 0; g < plan->n_late_bind_nodes; g++)
    {
      n_reads += domain_session_read_name (plan, g) != NULL ? 1 : 0;
    }
  if (n_reads == 0)
    {
      return true;
    }
  DOMAIN_SESSION_VARIABLE *variables =
    (DOMAIN_SESSION_VARIABLE *) domain_plan_alloc (thread_p, n_reads, sizeof (*variables));
  int *reads = (int *) domain_plan_alloc (thread_p, n_reads, sizeof (*reads));
  if (variables == NULL || reads == NULL)
    {
      return false;
    }
  /* count each variable's reads and assignments, lay them out, then fill them in */
  int n_variables = 0;
  for (int g = 0; g < plan->n_late_bind_nodes; g++)
    {
      const DB_VALUE *name = domain_session_read_name (plan, g);
      if (name == NULL)
	{
	  continue;
	}
      int v = domain_find_session_variable (variables, n_variables, name);
      if (v < 0)
	{
	  v = n_variables++;
	  variables[v] = DOMAIN_SESSION_VARIABLE
	  {
	  name, NULL, NULL, 0, 0};
	}
      variables[v].n_reads++;
    }
  int n_assigns = 0;
  for (int d = 0; d < ctx->n_defines; d++)
    {
      const int v = domain_session_define_variable (variables, n_variables, ctx->defines[d]);
      if (v >= 0)
	{
	  variables[v].n_assigns++;
	  n_assigns++;
	}
    }
  const DOMAIN_PLAN_ITEM **assigns = n_assigns == 0 ? NULL
    : (const DOMAIN_PLAN_ITEM **) domain_plan_alloc (thread_p, n_assigns, sizeof (*assigns));
  if (n_assigns > 0 && assigns == NULL)
    {
      return false;
    }
  for (int v = 0, r = 0, a = 0; v < n_variables; v++)
    {
      variables[v].reads = reads + r;
      variables[v].assigns = assigns != NULL ? assigns + a : NULL;
      r += variables[v].n_reads;
      a += variables[v].n_assigns;
      variables[v].n_reads = variables[v].n_assigns = 0;
    }
  for (int g = 0; g < plan->n_late_bind_nodes; g++)
    {
      const int v = domain_find_session_variable (variables, n_variables, domain_session_read_name (plan, g));
      if (v >= 0)
	{
	  variables[v].reads[variables[v].n_reads++] = g;
	}
    }
  for (int d = 0; d < ctx->n_defines; d++)
    {
      const int v = domain_session_define_variable (variables, n_variables, ctx->defines[d]);
      if (v >= 0)
	{
	  variables[v].assigns[variables[v].n_assigns++] = ctx->defines[d]->rightptr->plan_item;
	}
    }
  plan->session_variables = variables;
  plan->n_session_variables = n_variables;
  return true;
}

/* Whether a load entry reads an aggregate that finalizes to DOUBLE whatever its function domain says: AVG, STDDEV* and
 * VAR* (qdata_finalize_aggregate_list), whose function domain over a late-bound argument is the argument's. Through
 * value pointers and list positions to the producer. */
/*
 * [리뷰] domain_reads_double_aggregate — 어떤 항목이 (alias·생산자 사슬을 따라가) 결국 DOUBLE 을 내는 집계(AVG·STDDEV·VARIANCE 계열)를
 * 읽는지 판정한다. 그런 쪽은 집계의 해소 도메인과 무관하게 DOUBLE 로 비교해야 한다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: alias 면 대표로 옮기고, FIXED_AGG 를 만나면 AGG 문맥인지와 opcode 7종으로 판정하고 끝낸다. CONSUMER 가 아니거나 생산자가 없으면 false. 여기서도
 * 루프 변수 이름이 `constant_branch` 지만 실제로는 256회 홉 상한이고, 상한에 걸리면 false(보수적).
 * 바뀐 것: 신설(+38줄).
 */
static bool
domain_reads_double_aggregate (const DOMAIN_LOAD_ENTRY * load_entry)
{
  for (int constant_branch = 0; load_entry != NULL && constant_branch < 256; constant_branch++)
    {
      if (load_entry->alias != NULL)
	{
	  load_entry = load_entry->alias;
	  continue;
	}
      if (load_entry->kind == DOMAIN_LOAD_FIXED_AGG)
	{
	  if (load_entry->cold.ctx != DOMAIN_CTX_AGG)
	    {
	      return false;
	    }
	  switch (load_entry->cold.opcode)
	    {
	    case PT_AVG:
	    case PT_STDDEV:
	    case PT_STDDEV_POP:
	    case PT_STDDEV_SAMP:
	    case PT_VARIANCE:
	    case PT_VAR_POP:
	    case PT_VAR_SAMP:
	      return true;
	    default:
	      return false;
	    }
	}
      if (load_entry->kind != DOMAIN_LOAD_CONSUMER || load_entry->producer == NULL)
	{
	  return false;
	}
      load_entry = load_entry->producer;
    }
  return false;
}

/* What the load knows of one side of a comparison. */
enum DOMAIN_COMPARE_SIDE
{
  DOMAIN_SIDE_KNOWN,		/* its key is the plan's */
  DOMAIN_SIDE_LATE_BIND,	/* a bind or a constant expression (it compares with its value's type), or a side with a
				 * resolved index: resolve_domains' */
  DOMAIN_SIDE_VARIABLE		/* the plan leaves its values' type or collation variable: the row compares by value */
};

/* One side of a comparison at publication: a literal gives its value's key, a bind, a constant expression or a side
 * with a resolved index is resolve_domains', a reader of an aggregate that finalizes to DOUBLE a DOUBLE, anything else
 * its plan domain.
 * load_entries(in): the load entry of each published item, by index */
/*
 * [리뷰] domain_compare_side — 비교 한쪽(regu)을 보고 그 쪽이 KNOWN(로드가 비교 키를 확정) / LATE_BIND(게이트가 확정) / VARIABLE(아무도 확정 못
 * 함) 중 무엇인지 판정하면서 DOMAIN_COMPARE_PLAN 의 그 쪽 칸을 채운다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: 순서대로 — COLLATE 수식(REGU_VARIABLE_APPLY_COLLATION) 기록 → DOUBLE 집계 독자면 tp_Double_domain 으로 KNOWN →
 * TYPE_POS_VALUE 면 LATE_BIND(bind 여부 기록) → TYPE_DBVAL 이면 리터럴 값에서 키를 뽑아 KNOWN → 상수 식이면
 * LATE_BIND(after_constants) → resolved_index 가 있으면 LATE_BIND(세션 의존·상수 대기 전파) → 그 외는 도메인이 값을 고정하면 KNOWN, 아니면
 * VARIABLE.
 * 바뀐 것: 신설(+75줄).
 */
static DOMAIN_COMPARE_SIDE
domain_compare_side (const DOMAIN_PLAN * plan, DOMAIN_LOAD_ENTRY * const *load_entries, int constant_base,
		     REGU_VARIABLE * regu, DOMAIN_COMPARE_PLAN * comparison, int side, DOMAIN_COMPARE_KEY * key,
		     bool * session_dependent)
{
  const DOMAIN_PLAN_ITEM *item = regu->plan_item;
  comparison->operand[side] = item;
  comparison->domain[side] = regu->domain;
  comparison->value[side] = -1;
  /* a COLLATE modifier on the side itself: the fetch overwrites its value's codeset and collation with the domain's
   * (xasl_generation.c drops the T_CAST and flags the operand's regu) */
  comparison->collate[side] = REGU_VARIABLE_IS_FLAGED (regu, REGU_VARIABLE_APPLY_COLLATION) && regu->domain != NULL
    && TP_TYPE_HAS_COLLATION (TP_DOMAIN_TYPE (regu->domain)) ? regu->domain : NULL;
  if (item != NULL && regu->type != TYPE_DBVAL && regu->type != TYPE_POS_VALUE
      && domain_reads_double_aggregate (load_entries[item - plan->items]))
    {
      /* the value is a DOUBLE (or NULL) whatever the aggregate's resolved domain says; resolve_domains reads the
       * side's domain, not its item */
      comparison->operand[side] = NULL;
      comparison->domain[side] = &tp_Double_domain;
      domain_compare_key_of (&tp_Double_domain, key);
      return DOMAIN_SIDE_KNOWN;
    }
  if (regu->type == TYPE_POS_VALUE && item != NULL)
    {
      comparison->constant[side] = item;
      comparison->bind[side] = plan->items_cold[item - plan->items].val_pos >= 0;
      return DOMAIN_SIDE_LATE_BIND;
    }
  if (regu->type == TYPE_DBVAL)
    {
      const DB_VALUE *literal = &regu->value.dbval;
      comparison->literal[side] = literal;
      domain_compare_key_of (DB_IS_NULL (literal) ? &tp_Null_domain : tp_domain_resolve_value (literal, NULL), key);
      domain_compare_key_collate (key, comparison->collate[side]);
      return DOMAIN_SIDE_KNOWN;
    }
  const DOMAIN_PLAN_ITEM *cached = NULL;
  if ((regu->type == TYPE_INARITH || regu->type == TYPE_OUTARITH) && regu->value.arithptr != NULL)
    {
      cached = regu->value.arithptr->plan_item;
    }
  else if (regu->type == TYPE_FUNC)
    {
      cached = item;
    }
  if (cached != NULL && cached->ref >= constant_base)
    {
      /* a constant expression compares with its value's key, as a bind or a literal does: resolve_domains evaluates it
       * before any row, and its compiled domain need not describe its value (a LIKE bound's collation is its pattern
       * value's) */
      comparison->constant[side] = cached;
      comparison->after_constants = true;
      return DOMAIN_SIDE_LATE_BIND;
    }
  if (item != NULL && item->resolved_index >= 0)
    {
      if (plan->resolved_non_cacheable[item->resolved_index])
	{
	  *session_dependent = *session_dependent || plan->resolved_session_dependent[item->resolved_index];
	}
      /* a node resolve_domains resolves in the constant expression step: the comparison waits for its resolution */
      comparison->after_constants = comparison->after_constants
	|| domain_resolved_after_constant_expressions (plan, item->resolved_index);
      return DOMAIN_SIDE_LATE_BIND;
    }
  const TP_DOMAIN *domain = item != NULL ? item->fixed.domain : regu->domain;
  if (!domain_fixes_values (domain))
    {
      return DOMAIN_SIDE_VARIABLE;
    }
  domain_compare_key_of (domain, key);
  domain_compare_key_collate (key, comparison->collate[side]);
  return DOMAIN_SIDE_KNOWN;
}

/* A side resolve_domains converts once when its comparison converts it: a literal, a bind or a constant expression. */
/*
 * [리뷰] domain_compare_constant_side — 비교의 한쪽이 상수(리터럴 또는 상수 항목)인지 본다. 그런 쪽의 변환은 행마다가 아니라 게이트가 한 번만 하면 된다는 판단의
 * 근거.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: literal[side] 나 constant[side] 중 하나라도 있으면 true.
 * 바뀐 것: 신설(+5줄).
 */
static bool
domain_compare_constant_side (const DOMAIN_COMPARE_PLAN * comparison, int side)
{
  return comparison->literal[side] != NULL || comparison->constant[side] != NULL;
}

/*
 * domain_plan_add_comparison () - the resolution of one comparison: the load's when both sides' keys are the plan's and
 *   no constant side needs converting, otherwise a late-bind comparison resolve_domains resolves once per execution
 *   (and converts its constant sides into values of their own). A side whose values the plan leaves variable keeps
 *   tp_value_compare_with_error on the values (comparison method VALUES).
 */
/*
 * [리뷰] domain_plan_add_comparison — 양쪽 판정(lhs/rhs)을 합쳐 비교의 해소 방식(fixed.method)을 정한다 — 행마다 값으로 비교할지, 로드가 변환까지
 * 확정할지, 게이트가 한 번 확정할지.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: 한쪽이라도 VARIABLE 이면 DOMAIN_COMPARE_VALUES(행마다). 둘 다 KNOWN 이면 domain_resolve_comparison 으로 로드가 확정하되, 상수
 * 쪽에 변환이 필요하면 그 변환을 한 번만 하려고 다시 late_bind 로 돌린다. 그 외는 late_bind. late_bind 로 가면 compare_index 를 받고 상수 쪽마다 값 참조
 * 번호(plan->n_refs++)를 받아 변환 결과를 둘 자리를 확보한다. 세션 의존이면 LATE_BIND_SESSION.
 * 바뀐 것: 신설(+48줄).
 */
static bool
domain_plan_add_comparison (DOMAIN_PLAN * plan, DOMAIN_COMPARE_PLAN * comparison, DOMAIN_COMPARE_SIDE lhs,
			    DOMAIN_COMPARE_SIDE rhs, const DOMAIN_COMPARE_KEY * key, bool session_dependent,
			    DOMAIN_COMPARE_PLAN ** late_bind_comparisons, int *n_late_bind_comparisons)
{
  bool late_bind = false;
  if (lhs == DOMAIN_SIDE_VARIABLE || rhs == DOMAIN_SIDE_VARIABLE)
    {
      comparison->fixed = DOMAIN_COMPARE
      {
      };
      comparison->fixed.method = DOMAIN_COMPARE_VALUES;
      comparison->fixed.compare_index = -1;
      comparison->fixed.value[0] = comparison->fixed.value[1] = comparison->fixed.codeset_side = -1;
    }
  else if (lhs == DOMAIN_SIDE_KNOWN && rhs == DOMAIN_SIDE_KNOWN)
    {
      if (domain_resolve_comparison (&key[0], &key[1], &comparison->fixed) != NO_ERROR)
	{
	  return false;
	}
      /* a constant side the comparison converts is converted once, by resolve_domains */
      late_bind = (domain_compare_constant_side (comparison, 0) && comparison->fixed.conv[0] != NULL)
	|| (domain_compare_constant_side (comparison, 1) && comparison->fixed.conv[1] != NULL);
    }
  else
    {
      late_bind = true;
    }
  if (late_bind)
    {
      comparison->fixed = DOMAIN_COMPARE
      {
      };
      comparison->fixed.method = session_dependent ? DOMAIN_COMPARE_LATE_BIND_SESSION : DOMAIN_COMPARE_LATE_BIND;
      comparison->fixed.compare_index = *n_late_bind_comparisons;
      comparison->fixed.value[0] = comparison->fixed.value[1] = comparison->fixed.codeset_side = -1;
      for (int side = 0; side < 2; side++)
	{
	  if (domain_compare_constant_side (comparison, side))
	    {
	      comparison->value[side] = plan->n_refs++;
	    }
	}
      late_bind_comparisons[(*n_late_bind_comparisons)++] = comparison;
    }
  return true;
}

/* A list column side of an ALL/SOME term: its resolved domain table entry, a DOUBLE for a reader of AVG, STDDEV* or
 * VAR*, or its plan domain; VARIABLE when the plan leaves its values' type or collation variable. */
/*
 * [리뷰] domain_compare_column_side — regu 가 아니라 리스트 컬럼 항목으로 주어진 비교 한쪽을 판정한다(서브쿼리 리스트와 비교하는 ALL/SOME, 머지 조인
 * 컬럼쌍).
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: domain_compare_side 와 같은 순서를 컬럼 항목만으로 돌린다 — column==NULL 이면 VARIABLE, DOUBLE 집계면 KNOWN, resolved_index
 * 가 있으면 LATE_BIND, 도메인이 값을 고정하면 KNOWN, 아니면 VARIABLE. regu 가 없으므로 COLLATE 수식 처리는 없다.
 * 바뀐 것: 신설(+37줄).
 */
static DOMAIN_COMPARE_SIDE
domain_compare_column_side (const DOMAIN_PLAN * plan, DOMAIN_LOAD_ENTRY * const *load_entries,
			    const DOMAIN_PLAN_ITEM * column, DOMAIN_COMPARE_PLAN * comparison, int side,
			    DOMAIN_COMPARE_KEY * key, bool * session_dependent)
{
  comparison->operand[side] = column;
  comparison->domain[side] = NULL;
  comparison->value[side] = -1;
  if (column == NULL)
    {
      return DOMAIN_SIDE_VARIABLE;
    }
  if (domain_reads_double_aggregate (load_entries[column - plan->items]))
    {
      comparison->operand[side] = NULL;
      comparison->domain[side] = &tp_Double_domain;
      domain_compare_key_of (&tp_Double_domain, key);
      return DOMAIN_SIDE_KNOWN;
    }
  if (column->resolved_index >= 0)
    {
      if (plan->resolved_non_cacheable[column->resolved_index])
	{
	  *session_dependent = *session_dependent || plan->resolved_session_dependent[column->resolved_index];
	}
      comparison->after_constants = comparison->after_constants
	|| domain_resolved_after_constant_expressions (plan, column->resolved_index);
      return DOMAIN_SIDE_LATE_BIND;
    }
  if (!domain_fixes_values (column->fixed.domain))
    {
      return DOMAIN_SIDE_VARIABLE;
    }
  comparison->domain[side] = column->fixed.domain;
  domain_compare_key_of (column->fixed.domain, key);
  return DOMAIN_SIDE_KNOWN;
}

/* One side of a comparison outside a term: a regu as a term's side, a list column as an ALL/SOME term's list
 * side, a literal no regu holds by its value's key. */
/*
 * [리뷰] domain_compare_pair_side — compare pair 의 한쪽이 regu / 리터럴 / 컬럼 중 무엇으로 주어졌는지에 따라 적절한 판정 함수로 보내는 디스패처.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: regu 가 있으면 domain_compare_side, 리터럴이면 여기서 직접 키를 뽑아 KNOWN, 아니면 domain_compare_column_side. 리터럴 경로는 NULL
 * 이면 tp_Null_domain 을 쓴다.
 * 바뀐 것: 신설(+22줄).
 */
static DOMAIN_COMPARE_SIDE
domain_compare_pair_side (const DOMAIN_PLAN * plan, DOMAIN_LOAD_ENTRY * const *load_entries, int constant_base,
			  const DOMAIN_LOAD_COMPARE_PAIR * pair, DOMAIN_COMPARE_PLAN * comparison, int side,
			  DOMAIN_COMPARE_KEY * key, bool * session_dependent)
{
  if (pair->regu[side] != NULL)
    {
      return domain_compare_side (plan, load_entries, constant_base, pair->regu[side], comparison, side, key,
				  session_dependent);
    }
  if (pair->literal[side] != NULL)
    {
      const DB_VALUE *literal = pair->literal[side];
      comparison->operand[side] = NULL;
      comparison->domain[side] = NULL;
      comparison->value[side] = -1;
      comparison->literal[side] = literal;
      domain_compare_key_of (DB_IS_NULL (literal) ? &tp_Null_domain : tp_domain_resolve_value (literal, NULL), key);
      return DOMAIN_SIDE_KNOWN;
    }
  return domain_compare_column_side (plan, load_entries, pair->column[side], comparison, side, key, session_dependent);
}

/*
 * domain_plan_add_elements () - one ALL/SOME term's comparisons, each resolved before any row
 *
 * The item against a list's column or a right side that is no collection: a resolved comparison, as a comparison
 * term's. Against a collection the row computes: the item's row of the type pair comparison table, the load's, or the
 * resolve_domains' when resolve_domains resolves the item. Against a constant (a literal, a bind, a constant
 * expression): resolve_domains resolves and converts each element once, by position. A right side resolve_domains types
 * is resolve_domains' too.
 */
/*
 * [리뷰] domain_plan_add_elements — ALL/SOME 항 하나의 해소 계획(DOMAIN_ELEMENT_COMPARE_PLAN)을 만든다. 원소 비교를 쌍 비교로 할지, 행마다
 * 할지, 게이트가 원소들을 위치별로 풀지(kind)를 정한다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: 왼쪽은 항상 domain_compare_side. 오른쪽은 서브쿼리 리스트면 컬럼 판정, 아니면 regu 판정 후 — 상수/bind/상수식이면 LATE_BIND, variable
 * POS 면 LATE_BIND, 확정된 집합 타입이면 왼쪽도 KNOWN 일 때만 ROW — 로 kind 를 정한다. 한쪽이라도 VARIABLE 이면 무조건 PAIR 로 되돌린다. 마지막에
 * term->domain_compare 에 연결한다.
 * 바뀐 것: 신설(+74줄).
 */
static bool
domain_plan_add_elements (THREAD_ENTRY * thread_p, DOMAIN_PLAN * plan, DOMAIN_LOAD_ENTRY * const *load_entries,
			  int constant_base, DOMAIN_LOAD_ELEMENT_TERM * entry,
			  DOMAIN_COMPARE_PLAN ** late_bind_comparisons, int *n_late_bind_comparisons,
			  DOMAIN_ELEMENT_COMPARE_PLAN ** element_comparisons, int *n_late_bind_element_comparisons)
{
  ALSM_EVAL_TERM *term = entry->term;
  DOMAIN_ELEMENT_COMPARE_PLAN *comparison =
    (DOMAIN_ELEMENT_COMPARE_PLAN *) domain_plan_alloc (thread_p, 1, sizeof (*comparison));
  if (comparison == NULL)
    {
      return false;
    }
  memset (comparison, 0, sizeof (*comparison));
  comparison->row = -1;
  comparison->resolved_elements_index = -1;
  DOMAIN_COMPARE_PLAN *pair = &comparison->pair;
  pair->predicate = true;
  pair->key_range = entry->key_range;
  pair->constant_branch = entry->constant_branch;
  DOMAIN_COMPARE_KEY key[2];
  bool session_dependent = false;
  const DOMAIN_COMPARE_SIDE item = domain_compare_side (plan, load_entries, constant_base, term->elem, pair, 0, &key[0],
							&session_dependent);
  DOMAIN_COMPARE_SIDE right;
  comparison->kind = DOMAIN_ELEMENTS_PAIR;
  if (term->elemset->type == TYPE_LIST_ID)
    {
      right = domain_compare_column_side (plan, load_entries, entry->list_column, pair, 1, &key[1], &session_dependent);
    }
  else
    {
      right =
	domain_compare_side (plan, load_entries, constant_base, term->elemset, pair, 1, &key[1], &session_dependent);
      if (domain_compare_constant_side (pair, 1))
	{
	  /* a literal, a bind or a constant expression: resolve_domains resolves its elements by position */
	  comparison->kind = DOMAIN_ELEMENTS_LATE_BIND;
	}
      else if (right == DOMAIN_SIDE_LATE_BIND)
	{
	  /* a variable POS: the resolved domain says whether its values are collections */
	  comparison->kind = DOMAIN_ELEMENTS_LATE_BIND;
	}
      else if (right == DOMAIN_SIDE_KNOWN && TP_IS_SET_TYPE (key[1].type))
	{
	  comparison->kind = item == DOMAIN_SIDE_KNOWN ? DOMAIN_ELEMENTS_ROW : DOMAIN_ELEMENTS_LATE_BIND;
	}
    }
  if (item == DOMAIN_SIDE_VARIABLE || right == DOMAIN_SIDE_VARIABLE)
    {
      comparison->kind = DOMAIN_ELEMENTS_PAIR;
    }
  switch (comparison->kind)
    {
    case DOMAIN_ELEMENTS_PAIR:
      if (!domain_plan_add_comparison
	  (plan, pair, item, right, key, session_dependent, late_bind_comparisons, n_late_bind_comparisons))
	{
	  return false;
	}
      break;
    case DOMAIN_ELEMENTS_ROW:
      comparison->row = domain_compare_key_row (&key[0]);
      break;
    default:
      comparison->resolved_elements_index = *n_late_bind_element_comparisons;
      comparison->session_dependent = session_dependent;
      element_comparisons[(*n_late_bind_element_comparisons)++] = comparison;
      break;
    }
  term->domain_compare = comparison;
  return true;
}

/*
 * domain_block_scope () - the scope of a block whose scans fix the correlated values it reads
 *   return: the scope; -1 when the block's scans do not start it anew
 *
 * The value lists the block's scans fill carry it: a scan filling one starts the scope anew (scan_start_scan,
 * scan_reset_scan_block: an inner scan for each outer row), and so does the block's execution (a correlated subquery,
 * qexec_execute_mainblock). Only a scan procedure's block is one; a list another block's scope marked already is not.
 */
/*
 * [리뷰] domain_block_scope — XASL 블록에 '스코프 번호'를 부여한다. 스코프란 그 블록의 스캔이 한 행을 잡고 있는 동안 — 바깥 상관 값이 고정돼 있어 변환을 한 번만
 * 하면 되는 구간이다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: BUILDLIST/BUILDVALUE/SCAN 이고 val_list 가 있을 때만 번호를 준다. val_list 와 merge_val_list 의 기존 번호가 어긋나면 -1(스코프
 * 없음). 아직 0이면 plan->n_scopes 에서 새 번호를 받아 두 리스트에 같이 써 넣는다 — 번호 저장소가 플랜이 아니라 VAL_LIST 라는 점이 특징이다.
 * 바뀐 것: 신설(+27줄).
 */
static int
domain_block_scope (DOMAIN_PLAN * plan, XASL_NODE * block)
{
  if ((block->type != BUILDLIST_PROC && block->type != BUILDVALUE_PROC && block->type != SCAN_PROC)
      || block->val_list == NULL)
    {
      return -1;
    }
  VAL_LIST *const lists[2] = { block->val_list, block->merge_val_list };
  const int scope = lists[0]->domain_scope;
  if (lists[1] != NULL && lists[1]->domain_scope != scope)
    {
      return -1;
    }
  if (scope != 0)
    {
      return scope;
    }
  for (int i = 0; i < 2; i++)
    {
      if (lists[i] != NULL)
	{
	  lists[i]->domain_scope = plan->n_scopes;
	}
    }
  return plan->n_scopes++;
}

/*
 * domain_add_temporary () - a value the execution converts once per scope: a constant's scope is the execution's, a
 *   correlated value's its block's
 *   return: 1 + its domain_execution.temporaries index; 0 when there is none (the block's scans do not start a scope;
 *	     no memory: ctx->failed)
 */
/*
 * [리뷰] domain_add_temporary — '스코프당 한 번만 변환해 두는 값' 하나를 플랜에 등록하고 1부터 시작하는 핸들을 돌려준다(0 은 '없음').
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: block 이 NULL 이면 실행 전체 스코프(DOMAIN_SCOPE_EXECUTION), 아니면 domain_block_scope 로 번호를 얻고 -1 이면 등록하지 않고 0 을
 * 돌려준다. temporary_scopes/temporary_blocks 두 평행 배열을 8부터 2배씩 키운다. 반환값이 `++plan->n_temporaries` 이므로 호출자가 받는 값은
 * 1-based 인덱스다.
 * 바뀐 것: 신설(+32줄).
 */
static int
domain_add_temporary (DOMAIN_LOAD_CONTEXT * ctx, DOMAIN_PLAN * plan, XASL_NODE * block)
{
  const int scope = block == NULL ? DOMAIN_SCOPE_EXECUTION : domain_block_scope (plan, block);
  if (scope < 0)
    {
      return 0;
    }
  if (plan->n_temporaries == ctx->max_temporaries)
    {
      const int max = ctx->max_temporaries == 0 ? 8 : ctx->max_temporaries * 2;
      int *scopes = (int *) db_private_realloc (ctx->thread_p, ctx->temporary_scopes, max * sizeof (*scopes));
      if (scopes == NULL)
	{
	  ctx->failed = true;
	  return 0;
	}
      ctx->temporary_scopes = scopes;
      XASL_NODE **blocks =
	(XASL_NODE **) db_private_realloc (ctx->thread_p, ctx->temporary_blocks, max * sizeof (*blocks));
      if (blocks == NULL)
	{
	  ctx->failed = true;
	  return 0;
	}
      ctx->temporary_blocks = blocks;
      ctx->max_temporaries = max;
    }
  ctx->temporary_scopes[plan->n_temporaries] = scope;
  ctx->temporary_blocks[plan->n_temporaries] = block;
  return ++plan->n_temporaries;
}

/* Whether a node's operand coercion may convert operand i at the row: resolve_domains resolves the operand coercion (a
 * late-binding node, a compiled one over an operand it did not type), or the load's converts it. */
/*
 * [리뷰] domain_arith_may_convert — 산술 항목의 i 번째 피연산자가 실제로 변환을 겪을 수 있는지 본다. 변환이 없으면 스코프당 1회 변환 슬롯을 잡을 필요가 없다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: (타입 축 지연 바인딩이면서 collation 전용이 아님) 또는 (강제변환 지연) 또는 (이미 정적 변환기가 걸려 있음) 셋 중 하나면 true. collation 전용 지연은 값
 * 변환이 아니므로 제외된다.
 * 바뀐 것: 신설(+6줄).
 */
static bool
domain_arith_may_convert (const DOMAIN_PLAN_ITEM * item, int i)
{
  return ((item->flags & DOMAIN_PLAN_LATE_BIND) && !(item->flags & DOMAIN_PLAN_LATE_BIND_COLLATION))
    || (item->flags & DOMAIN_PLAN_LATE_BIND_COERCION) || item->fixed.conv[i] != NULL;
}

/* Whether an operand is a constant the execution fixes: a literal, a bind, or a constant expression resolve_domains
 * evaluates (as domain_compare_side knows one). */
/*
 * [리뷰] domain_constant_operand — 피연산자 regu 가 실행 전체 스코프에서 한 번만 변환해도 되는 상수인지(리터럴·bind·상수 식) 판정한다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: TYPE_DBVAL 이거나 항목이 달린 TYPE_POS_VALUE 면 바로 true. arith/func 는 그 항목의 ref 가 상수 식 영역(>= constant_base)인지로
 * 본다.
 * 바뀐 것: 신설(+18줄).
 */
static bool
domain_constant_operand (const REGU_VARIABLE * regu, int constant_base)
{
  if (regu->type == TYPE_DBVAL || (regu->type == TYPE_POS_VALUE && regu->plan_item != NULL))
    {
      return true;
    }
  const DOMAIN_PLAN_ITEM *cached = NULL;
  if ((regu->type == TYPE_INARITH || regu->type == TYPE_OUTARITH) && regu->value.arithptr != NULL)
    {
      cached = regu->value.arithptr->plan_item;
    }
  else if (regu->type == TYPE_FUNC)
    {
      cached = regu->plan_item;
    }
  return cached != NULL && cached->ref >= constant_base;
}

/* Whether a resolved comparison may convert a side at the row: resolve_domains resolves it, or the load's resolution
 * converts it. */
/*
 * [리뷰] domain_load_entry_may_convert — 비교의 한쪽이 변환을 겪을 수 있는지 본다 — 스코프당 1회 변환 슬롯을 비교에 붙일지 결정하는 조건.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: 해소 방식이 LATE_BIND 또는 LATE_BIND_SESSION 이면(아직 모르므로) true, CONVERT 면 그 쪽 변환기가 실제로 있을 때만 true. VALUES 방식은
 * false.
 * 바뀐 것: 신설(+7줄).
 */
static bool
domain_load_entry_may_convert (const DOMAIN_COMPARE_PLAN * comparison, int side)
{
  return comparison->fixed.method == DOMAIN_COMPARE_LATE_BIND
    || comparison->fixed.method == DOMAIN_COMPARE_LATE_BIND_SESSION
    || (comparison->fixed.method == DOMAIN_COMPARE_CONVERT && comparison->fixed.conv[side] != NULL);
}

/*
 * domain_plan_add_compares () - every comparison term gets its resolved comparison, every ALL/SOME term its
 *   element comparisons, and every comparison outside a term its resolved comparison
 *
 * a term's side that is a correlated value an outer block's scan fixes is converted once per scope,
 * where every place the walk met the term is in that scope.
 */
/*
 * [리뷰] domain_plan_add_compares — 워크가 모은 비교 항·ALL/SOME 항·비교쌍을 전부 DOMAIN_COMPARE_PLAN 으로 공개하고, 게이트가 풀어야 할 것들을
 * plan->compares / plan->element_comparisons 두 배열로 묶는다. 실행 전 게이트의 비교 단계가 읽을 목록.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: 먼저 index→LOAD_ENTRY 역색인(load_entries)을 만든다(alias 인 항목은 대표를 넣는다). 비교 항은 이미 계획이 있으면(두 번 만남) 분기 포함 관계만
 * 검사하고 스코프가 달라진 temporaries 를 0 으로 되돌린다. 새 항은 양쪽 판정 → domain_plan_add_comparison → 연산자 함수 고정 → 스코프당 1회 변환 슬롯
 * 부여. ALL/SOME·비교쌍도 같은 절차를 돈다. 세 임시 배열은 db_private_alloc 로 잡고 끝에서 모두 해제한다.
 * 바뀐 것: 신설(+171줄).
 */
static bool
domain_plan_add_compares (THREAD_ENTRY * thread_p, DOMAIN_LOAD_CONTEXT * ctx, DOMAIN_PLAN * plan, int constant_base)
{
  const int n_terms = ctx->n_compare_terms + ctx->n_element_terms + ctx->n_compare_pairs;
  if (n_terms == 0)
    {
      return true;
    }
  DOMAIN_COMPARE_PLAN **late_bind_comparisons =
    (DOMAIN_COMPARE_PLAN **) db_private_alloc (thread_p, sizeof (*late_bind_comparisons) * n_terms);
  DOMAIN_ELEMENT_COMPARE_PLAN **element_comparisons =
    (DOMAIN_ELEMENT_COMPARE_PLAN **) db_private_alloc (thread_p, sizeof (*element_comparisons) * n_terms);
  const int n_load_entries = plan->n_items > 0 ? plan->n_items : 1;
  DOMAIN_LOAD_ENTRY **load_entries =
    (DOMAIN_LOAD_ENTRY **) db_private_alloc (thread_p, sizeof (*load_entries) * n_load_entries);
  bool ok = late_bind_comparisons != NULL && element_comparisons != NULL && load_entries != NULL;
  for (DOMAIN_LOAD_ENTRY * r = ctx->head; ok && r != NULL; r = r->next)
    {
      if (r->alias == NULL)
	{
	  load_entries[r->index] = r;
	}
      else if (r->index != r->alias->index)
	{
	  /* a value pointer's item copy answers as the producer's item it shared */
	  load_entries[r->index] = r->alias;
	}
    }
  int n_late_bind_comparisons = 0, n_late_bind_element_comparisons = 0;
  for (int t = 0; t < ctx->n_compare_terms && ok; t++)
    {
      COMP_EVAL_TERM *term = ctx->compare_terms[t];
      if (term->domain_compare != NULL)
	{
	  /* a term the walk met twice: its constant branch chain holds for the second place too, or the plan keeps no
	   * constant branches */
	  if (!domain_constant_branch_encloses
	      (ctx, term->domain_compare->constant_branch, ctx->compare_term_constant_branches[t]))
	    {
	      ctx->constant_branches_ambiguous = true;
	    }
	  /* and a side is converted once per scope only where the second place is in the same scope */
	  DOMAIN_COMPARE_PLAN *met = const_cast < DOMAIN_COMPARE_PLAN * >(term->domain_compare);
	  for (int side = 0; side < 2; side++)
	    {
	      if (met->temporaries[side] != 0
		  && ctx->temporary_blocks[met->temporaries[side] - 1] != ctx->compare_term_scopes[2 * t + side])
		{
		  met->temporaries[side] = 0;
		}
	    }
	  met->key_range = met->key_range || ctx->compare_term_ranges[t];
	  continue;
	}
      DOMAIN_COMPARE_PLAN *comparison = (DOMAIN_COMPARE_PLAN *) domain_plan_alloc (thread_p, 1, sizeof (*comparison));
      if (comparison == NULL)
	{
	  ok = false;
	  break;
	}
      memset (comparison, 0, sizeof (*comparison));
      comparison->predicate = true;
      comparison->key_range = ctx->compare_term_ranges[t];
      comparison->constant_branch = ctx->compare_term_constant_branches[t];
      DOMAIN_COMPARE_KEY key[2];
      bool session_dependent = false;
      const DOMAIN_COMPARE_SIDE lhs =
	domain_compare_side (plan, load_entries, constant_base, term->lhs, comparison, 0, &key[0],
			     &session_dependent);
      const DOMAIN_COMPARE_SIDE rhs =
	domain_compare_side (plan, load_entries, constant_base, term->rhs, comparison, 1, &key[1],
			     &session_dependent);
      ok =
	domain_plan_add_comparison (plan, comparison, lhs, rhs, key, session_dependent, late_bind_comparisons,
				    &n_late_bind_comparisons);
      /* a fixed resolution's operator functions; a late-bind comparison's come with the resolved domains */
      domain_compare_set_operator_functions (&comparison->fixed);
      term->domain_compare = comparison;
      for (int side = 0; ok && side < 2; side++)
	{
	  XASL_NODE *block = ctx->compare_term_scopes[2 * t + side];
	  if (block != NULL && domain_load_entry_may_convert (comparison, side))
	    {
	      comparison->temporaries[side] = domain_add_temporary (ctx, plan, block);
	    }
	}
    }
  for (DOMAIN_LOAD_ELEMENT_TERM * e = ctx->element_terms; e != NULL && ok; e = e->next)
    {
      if (e->term->domain_compare == NULL)
	{
	  ok =
	    domain_plan_add_elements (thread_p, plan, load_entries, constant_base, e, late_bind_comparisons,
				      &n_late_bind_comparisons, element_comparisons, &n_late_bind_element_comparisons);
	}
      else
	{
	  DOMAIN_ELEMENT_COMPARE_PLAN *met = const_cast < DOMAIN_ELEMENT_COMPARE_PLAN * >(e->term->domain_compare);
	  met->pair.key_range = met->pair.key_range || e->key_range;
	  if (!domain_constant_branch_encloses (ctx, met->pair.constant_branch, e->constant_branch))
	    {
	      /* a term the walk met twice below constant branches neither of which is around the other */
	      ctx->constant_branches_ambiguous = true;
	    }
	}
    }
  for (DOMAIN_LOAD_COMPARE_PAIR * pair = ctx->compare_pairs; pair != NULL && ok; pair = pair->next)
    {
      if (*pair->owner != NULL)
	{
	  continue;
	}
      DOMAIN_COMPARE_PLAN *comparison = (DOMAIN_COMPARE_PLAN *) domain_plan_alloc (thread_p, 1, sizeof (*comparison));
      if (comparison == NULL)
	{
	  ok = false;
	  break;
	}
      memset (comparison, 0, sizeof (*comparison));
      comparison->constant_branch = -1;
      DOMAIN_COMPARE_KEY key[2];
      bool session_dependent = false;
      const DOMAIN_COMPARE_SIDE lhs =
	domain_compare_pair_side (plan, load_entries, constant_base, pair, comparison, 0, &key[0],
				  &session_dependent);
      const DOMAIN_COMPARE_SIDE rhs =
	domain_compare_pair_side (plan, load_entries, constant_base, pair, comparison, 1, &key[1],
				  &session_dependent);
      ok =
	domain_plan_add_comparison (plan, comparison, lhs, rhs, key, session_dependent, late_bind_comparisons,
				    &n_late_bind_comparisons);
      *pair->owner = comparison;
    }
  if (ok && n_late_bind_comparisons > 0)
    {
      plan->compares =
	(DOMAIN_COMPARE_PLAN **) domain_plan_alloc (thread_p, n_late_bind_comparisons, sizeof (*plan->compares));
      ok = plan->compares != NULL;
      if (ok)
	{
	  memcpy (plan->compares, late_bind_comparisons, sizeof (*plan->compares) * n_late_bind_comparisons);
	  plan->n_compare_indexes = n_late_bind_comparisons;
	}
    }
  if (ok && n_late_bind_element_comparisons > 0)
    {
      plan->element_comparisons =
	(DOMAIN_ELEMENT_COMPARE_PLAN **) domain_plan_alloc (thread_p, n_late_bind_element_comparisons,
							    sizeof (*plan->element_comparisons));
      ok = plan->element_comparisons != NULL;
      if (ok)
	{
	  memcpy (plan->element_comparisons, element_comparisons,
		  sizeof (*plan->element_comparisons) * n_late_bind_element_comparisons);
	  plan->n_element_comparisons = n_late_bind_element_comparisons;
	}
    }
  if (late_bind_comparisons != NULL)
    {
      db_private_free (thread_p, late_bind_comparisons);
    }
  if (element_comparisons != NULL)
    {
      db_private_free (thread_p, element_comparisons);
    }
  if (load_entries != NULL)
    {
      db_private_free (thread_p, load_entries);
    }
  return ok;
}

/*
 * domain_plan_add_temporaries () - the arithmetic operands and the values SUM and AVG add that a scope fixes: a
 *   constant - a literal, a bind, a constant expression - for the execution, a correlated value for its block's scope;
 *   the execution converts each once per scope where the node's operand coercion converts it. Then the scope of every
 *   such value, the comparison sides' (domain_plan_add_compares) included.
 */
/*
 * [리뷰] domain_plan_add_temporaries — 산술 노드와 집계가 적어 둔 temporary_operand 후보를 실제 '스코프당 1회 변환' 슬롯으로 확정하고,
 * plan->temporary_scope 배열을 공개한다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: alias 엔트리와 후보가 없는 엔트리는 건너뛴다. 집계(AGG 문맥)는 변환 여부를 실행 시 값 도메인으로 정하므로 domain_arith_may_convert 검사를 면제한다.
 * 외부 스코프가 잡혀 있으면 그 블록 스코프로, 아니면 상수 피연산자일 때 실행 전체 스코프로 등록한다. 끝에서 ctx 의 스코프 배열을 플랜 메모리로 복사한다.
 * 바뀐 것: 신설(+41줄).
 */
static bool
domain_plan_add_temporaries (THREAD_ENTRY * thread_p, DOMAIN_LOAD_CONTEXT * ctx, DOMAIN_PLAN * plan, int constant_base)
{
  for (DOMAIN_LOAD_ENTRY * r = ctx->head; r != NULL && !ctx->failed; r = r->next)
    {
      if (r->alias != NULL || (r->temporary_operand[0] == NULL && r->temporary_operand[1] == NULL))
	{
	  continue;
	}
      DOMAIN_PLAN_ITEM *item = &plan->items[r->index];
      /* an aggregate plans its operand coercion at its setup, from its value's domain in the execution */
      const bool aggregate = r->cold.ctx == DOMAIN_CTX_AGG;
      for (int i = 0; i < 2; i++)
	{
	  const REGU_VARIABLE *operand = r->temporary_operand[i];
	  if (operand == NULL || (!aggregate && !domain_arith_may_convert (item, i)))
	    {
	      continue;
	    }
	  if (r->temporary_scope[i] != NULL)
	    {
	      item->temporaries[i] = domain_add_temporary (ctx, plan, r->temporary_scope[i]);
	    }
	  else if (domain_constant_operand (operand, constant_base))
	    {
	      item->temporaries[i] = domain_add_temporary (ctx, plan, NULL);
	    }
	}
    }
  if (ctx->failed || plan->n_temporaries == 0)
    {
      return !ctx->failed;
    }
  plan->temporary_scope = (int *) domain_plan_alloc (thread_p, plan->n_temporaries, sizeof (*plan->temporary_scope));
  if (plan->temporary_scope == NULL)
    {
      return false;
    }
  memcpy (plan->temporary_scope, ctx->temporary_scopes, sizeof (*plan->temporary_scope) * plan->n_temporaries);
  return true;
}

/*
 * domain_comparison_resolvable_at () - the constant the constant expression step (qexec_evaluate_constant_expression)
 *   resolves a comparison over a constant expression or ALL/SOME term to resolve before: one past its last constant
 *   expression, or the constant a late-binding node over a constant expression it reads is (resolve_domains resolves it
 *   just before evaluating it); n_constant_expressions when it reads a late-binding node over a constant expression
 *   that reads a row - after the last constant
 */
/*
 * [리뷰] domain_comparison_resolvable_at — 상수 단계를 기다리는 비교 하나가 '몇 번째 상수 식까지 계산되면' 풀 수 있는지 그 지점을 돌려준다. 게이트가 상수를 하나
 * 계산할 때마다 그 지점에 걸린 비교만 풀 수 있게 하는 계수 정렬의 키.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: 양쪽을 보며 — 상수 쪽이면 그 상수 식 번호+1, 상수 단계 뒤에 풀리는 피연산자면 그 생산 노드가 상수 식이면 그 번호, 아니면 n_constant_expressions(= 전부
 * 끝난 뒤) — 중 최대값을 취한다. 범위 검사는 assert 뿐이지만 호출자(domain_plan_add_constant_comparisons)가 `at[s] <
 * n_constant_expressions` 로 다시 거르므로 범위 밖 값은 '상수 뒤가 아님' 쪽으로 떨어진다.
 * 바뀐 것: 신설(+27줄).
 */
static int
domain_comparison_resolvable_at (const DOMAIN_PLAN * plan, const DOMAIN_COMPARE_PLAN * comparison, int constant_base)
{
  int at = 0;
  for (int side = 0; side < 2; side++)
    {
      const DOMAIN_PLAN_ITEM *constant = comparison->constant[side];
      if (constant != NULL && constant->ref >= 0 && plan->items_cold[constant - plan->items].val_pos < 0)
	{
	  const int c = constant->ref - constant_base;
	  assert (c >= 0 && c < plan->n_constant_expressions);
	  at = c + 1 > at ? c + 1 : at;
	}
      const DOMAIN_PLAN_ITEM *operand = comparison->operand[side];
      if (operand != NULL && operand->resolved_index >= 0
	  && domain_resolved_after_constant_expressions (plan, operand->resolved_index))
	{
	  const DOMAIN_PLAN_ITEM *node = plan->late_bind_nodes[plan->resolved_late_bind_node[operand->resolved_index]];
	  const int c = node->ref - constant_base;
	  const bool constant_node = c >= 0 && c < plan->n_constant_expressions
	    && plan->constant_expressions[c].item == node;
	  const int node_at = constant_node ? c : plan->n_constant_expressions;
	  at = node_at > at ? node_at : at;
	}
    }
  return at;
}

/*
 * domain_plan_add_constant_comparisons () - for each constant expression, the comparison over a constant expression and
 *   ALL/SOME terms to resolve the constant expression step (qexec_evaluate_constant_expression) resolves just before it
 *   evaluates that constant: the constant expression step resolves a comparison as soon as its constants have their
 *   values, and this list lets it do so without going over every comparison before every constant
 */
/*
 * [리뷰] domain_plan_add_constant_comparisons — 로드 단계의 마지막 조립 단계 — stx_build_domain_plan 이 상수식·비교를 모두 모은 뒤 불러,
 * 「어느 상수식이 평가되면 어느 비교를 결정할 수 있나」를 CSR 두 배열(plan->constant_comparisons_first / constant_comparisons)로 plan 에 달고
 * 성공 여부를 bool 로 돌려준다. 실행 전 게이트의 상수식 단계가 이 인덱스를 보고 그 자리에서 비교를 확정한다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 에는 비교 결정을 미리 모아 두는 구조 자체가 없고, 비교 도메인은 행마다 eval_value_rel_cmp →
 * tp_value_compare_with_error 가 정했다(src/query/query_evaluator.c:153).
 * 이 PR: 비교(plan->compares)와 원소 비교(element_comparisons)를 한 줄로 이어 각각이 기다리는 상수 인덱스 at[s] 를 구하고, 상수별 계수정렬로 CSR 을
 * 만든다. 세션 변수를 읽는 비교는 at[s]=n_constant_expressions 로 빼서 상수 단계가 아니라 세션 변수 단계로 넘긴다.
 * 바뀐 것: 신설 +69줄. 스크래치 at 은 db_private_alloc/db_private_free 짝(3748/3806)이고, CSR 두 배열은
 * domain_plan_alloc(=stx_alloc_struct, XASL 언팩 아레나)이라 플랜 수명을 따른다.
 */
static bool
domain_plan_add_constant_comparisons (THREAD_ENTRY * thread_p, DOMAIN_PLAN * plan, int constant_base)
{
  const int n_comparisons = plan->n_compare_indexes + plan->n_element_comparisons;
  if (plan->n_constant_expressions == 0 || n_comparisons == 0)
    {
      return true;
    }
  int *at = (int *) db_private_alloc (thread_p, sizeof (int) * n_comparisons);
  if (at == NULL)
    {
      return false;
    }
  int n_after_constants = 0;
  for (int s = 0; s < n_comparisons; s++)
    {
      const bool is_compare = s < plan->n_compare_indexes;
      const DOMAIN_COMPARE_PLAN *comparison =
	is_compare ? plan->compares[s] : &plan->element_comparisons[s - plan->n_compare_indexes]->pair;
      /* a comparison over a session variable read waits for the session variable step; one that waits for no constant
       * is resolved in the comparison step */
      const bool session_comparison = is_compare ? comparison->fixed.method == DOMAIN_COMPARE_LATE_BIND_SESSION
	: plan->element_comparisons[s - plan->n_compare_indexes]->session_dependent;
      at[s] = comparison->after_constants
	&& !session_comparison ? domain_comparison_resolvable_at (plan, comparison,
								  constant_base) : plan->n_constant_expressions;
      n_after_constants += at[s] < plan->n_constant_expressions;
    }
  bool ok = true;
  if (n_after_constants > 0)
    {
      int *first = (int *) domain_plan_alloc (thread_p, plan->n_constant_expressions + 1, sizeof (int));
      int *comparisons = (int *) domain_plan_alloc (thread_p, n_after_constants, sizeof (int));
      ok = first != NULL && comparisons != NULL;
      if (ok)
	{
	  /* a counting sort by the constant each comparison waits for, plan order within one */
	  memset (first, 0, sizeof (int) * (plan->n_constant_expressions + 1));
	  for (int s = 0; s < n_comparisons; s++)
	    {
	      if (at[s] < plan->n_constant_expressions)
		{
		  first[at[s] + 1]++;
		}
	    }
	  for (int i = 0; i < plan->n_constant_expressions; i++)
	    {
	      first[i + 1] += first[i];
	    }
	  for (int s = 0; s < n_comparisons; s++)
	    {
	      if (at[s] < plan->n_constant_expressions)
		{
		  comparisons[first[at[s]]++] = s;
		}
	    }
	  /* each first[i] ran to the start of the next constant's comparisons */
	  for (int i = plan->n_constant_expressions; i > 0; i--)
	    {
	      first[i] = first[i - 1];
	    }
	  first[0] = 0;
	  plan->constant_comparisons_first = first;
	  plan->constant_comparisons = comparisons;
	}
    }
  db_private_free (thread_p, at);
  return ok;
}

/*
 * domain_key_literal () - the domain of a literal key element's value, which the load reads once; NULL for a constant
 *   resolve_domains forms at every execution: a bind (a WHERE literal the parser auto-parameterized is one,
 *   qo_auto_parameterize) or a constant expression, a NULL (the range answers it), a value no index key holds
 *   (resolve_domains' error before any row), a literal under a COLLATE modifier (the fetch gives its value the
 *   modifier's collation)
 */
/*
 * [리뷰] domain_key_literal — domain_plan_key_element 가 인덱스 키 칼럼 하나를 볼 때 호출 — 그 regu 가 「컴파일 시점에 값이 박힌, 인덱스에 쓸 수
 * 있는 리터럴」인지 판정해 값의 도메인을 돌려주고, 아니면 NULL 을 돌려준다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: TYPE_DBVAL 이 아니거나 REGU_VARIABLE_APPLY_COLLATION 이 붙었거나 NULL 이거나 인덱스 타입이 아니면 NULL. 통과하면
 * domain_value_domain() 의 도메인을 domain_fixes_values() 로 한 번 더 걸러 돌려준다.
 * 바뀐 것: 신설 +11줄.
 */
static const TP_DOMAIN *
domain_key_literal (const REGU_VARIABLE * regu)
{
  if (regu->type != TYPE_DBVAL || REGU_VARIABLE_IS_FLAGED (regu, REGU_VARIABLE_APPLY_COLLATION)
      || DB_IS_NULL (&regu->value.dbval) || !tp_valid_indextype (DB_VALUE_DOMAIN_TYPE (&regu->value.dbval)))
    {
      return NULL;
    }
  const TP_DOMAIN *domain = domain_value_domain (&regu->value.dbval);
  return domain_fixes_values (domain) ? domain : NULL;
}

/* Whether key2's constant element reads key1's value at its column: two binds of one reference - resolve_domains'
 * vals[ref] - without a COLLATE modifier, against the same column. */
/*
 * [리뷰] domain_key_same_bind — domain_plan_key_element 가 range 의 key2 원소를 볼 때 호출 — 짝(key1)의 같은 자리 원소가 같은 bind
 * 위치를 읽는지 판정해, 같으면 게이트의 결정 슬롯(resolved_element)을 공유시킨다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: 짝이 DOMAIN_KEY_CONSTANT 이고 아직 공유되지 않았고 같은 인덱스 칼럼이며, 양쪽 regu 가 모두 TYPE_POS_VALUE 로 같은
 * plan_item->ref(>=0)를 읽고 둘 다 APPLY_COLLATION 이 아닐 때만 true.
 * 바뀐 것: 신설 +14줄. pair->shared 를 막아 공유가 연쇄되지 않게 한다.
 */
static bool
domain_key_same_bind (const domain_plan_key_elem * pair, const domain_plan_key_elem * elem)
{
  if (pair == NULL || pair->rule != DOMAIN_KEY_CONSTANT || pair->shared || pair->index_elem != elem->index_elem)
    {
      return false;
    }
  const REGU_VARIABLE *first = pair->regu, *second = elem->regu;
  return first != NULL && second != NULL && first->type == TYPE_POS_VALUE && second->type == TYPE_POS_VALUE
    && first->plan_item != NULL && second->plan_item != NULL && first->plan_item->ref >= 0
    && first->plan_item->ref == second->plan_item->ref
    && !REGU_VARIABLE_IS_FLAGED (first, REGU_VARIABLE_APPLY_COLLATION)
    && !REGU_VARIABLE_IS_FLAGED (second, REGU_VARIABLE_APPLY_COLLATION);
}

/*
 * domain_plan_key_element () - how one column of a search key takes its value
 *
 * A constant is resolve_domains' (its value, once per execution); so is an element whose domain resolve_domains
 * resolves (its rule, from that domain). The load derives the rule of any other element from its domain: the column's
 * type, strict or kept (domain_key_rule). keep_elem is the element's domain in the column's direction, which a
 * multi-column key writes the value with once any column is kept.
 *
 * A literal is the load's: its value's domain gives the rule resolve_domains gave it at every execution
 * (qexec_resolve_key_constant). One resolve_domains converts strictly stays resolve_domains': resolve_domains converts
 * it once per execution, the range would at every range it builds.
 *
 * pair(in): key1's element at this column when this is key2's, else NULL. A key2 constant over the same bind (an IN
 * list's range, key1 = key2 = ?) takes key1's resolution: the same value against the same column in the same index is
 * one resolution, which resolve_domains makes once.
 */
/*
 * [리뷰] domain_plan_key_element — 인덱스 키 한 칼럼의 결정 규칙을 로드 시점에 확정한다 — domain_plan_key_bound 가 원소마다 호출하고, elem 에
 * rule(INDEX/KEEP/CONSTANT/LATE_BIND)·keep_elem·strict_conv·resolved_element 를 채워 성공 여부를 돌려준다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 은 키를 만들 때마다 scan_dbvals_to_midxkey 가 칼럼별로
 * tp_domain_match_ignore_order 를 돌려 setdomain 재구성 여부를 정하고 btree_coerce_key 로
 * 변환했다(src/query/scan_manager.c:2042, 2274).
 * 이 PR: ISS 의 skip 값은 인덱스에서 읽으므로 INDEX 로 두고 끝낸다. OPERAND_CONST 면 리터럴 도메인으로 규칙을 정하고, 규칙이 CONSTANT 면 짝과 bind 를
 * 공유하거나 새 resolved_element 를 받는다. 비상수는 컴파일 도메인이 값을 고정하지 못하면 LATE_BIND 로 돌려 게이트가 결정하게 한다.
 * 바뀐 것: 신설 +51줄. 한 칼럼의 결정이 네 갈래(INDEX/KEEP/CONSTANT/LATE_BIND)로 분기한다.
 */
static bool
domain_plan_key_element (domain_plan_index * index, bool midxkey, REGU_VARIABLE * regu, const TP_DOMAIN * column,
			 bool skip_value, const domain_plan_key_elem * pair, domain_plan_key_elem * elem)
{
  elem->regu = regu;
  elem->index_elem = column;
  elem->keep_elem = column;
  elem->strict_conv = NULL;
  elem->resolved_element = -1;
  elem->rule = DOMAIN_KEY_INDEX;
  elem->shared = false;
  if (skip_value)
    {
      /* an index skip scan's skip value is read from the index */
      return true;
    }
  const DOMAIN_PLAN_ITEM *item = regu != NULL ? regu->plan_item : NULL;
  if (item != NULL && item->operand_class == OPERAND_CONST)
    {
      const TP_DOMAIN *literal = domain_key_literal (regu);
      TP_VALUE_CONVERTER strict_conv = NULL;
      const DOMAIN_KEY_RULE rule = literal != NULL ? domain_key_rule (literal, column, midxkey, &strict_conv)
	: DOMAIN_KEY_CONSTANT;
      if (rule == DOMAIN_KEY_INDEX || rule == DOMAIN_KEY_KEEP)
	{
	  elem->rule = rule;
	  elem->keep_elem = domain_in_key_direction (literal, column);
	  return elem->keep_elem != NULL;
	}
      elem->rule = DOMAIN_KEY_CONSTANT;
      if (domain_key_same_bind (pair, elem))
	{
	  elem->resolved_element = pair->resolved_element;
	  elem->shared = true;
	  return true;
	}
      elem->resolved_element = index->n_resolved_elements++;
      return true;
    }
  const TP_DOMAIN *domain = item != NULL && item->resolved_index < 0 ? item->fixed.domain : NULL;
  if (item == NULL || item->operand_class == OPERAND_NON_CACHEABLE || !domain_fixes_values (domain))
    {
      elem->rule = DOMAIN_KEY_LATE_BIND;
      elem->resolved_element = index->n_resolved_elements++;
      return true;
    }
  domain = domain_key_value_domain (domain);
  elem->rule = domain_key_rule (domain, column, midxkey, &elem->strict_conv);
  elem->keep_elem = domain_in_key_direction (domain, column);
  return elem->keep_elem != NULL;
}

/* One bound of a key range: the columns of a multi-column key's F_MIDXKEY, or the single-column key itself.
 * pair(in): key1's bound when this is key2's (domain_plan_key_element), else NULL */
/*
 * [리뷰] domain_plan_key_bound — KEY_RANGE 한쪽 경계(단일 regu 또는 MIDXKEY 의 F_MIDXKEY 피연산자 목록) 전체를 돌며 domain_plan_key
 * 를 채운다 — domain_plan_add_indexes 가 range 당 두 번(+ISS fetch range 한 번) 호출한다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: midxkey 면 피연산자 수만큼, 아니면 1개를 domain_plan_key_element 에 넘긴다. 전부 상수이고 행이 정하는 원소가 없으면 bound->constant=true
 * 로 두어 게이트가 도메인을 한 번만 쓰게 하고, 섞이면 mixed_key_cache 슬롯을 하나 배정해 스캔이 캐시를 쓰게 한다.
 * 바뀐 것: 신설 +59줄. elems 는 아레나 할당이고 n>0 일 때만 NULL 을 실패로 본다.
 */
static bool
domain_plan_key_bound (THREAD_ENTRY * thread_p, domain_plan_index * index, REGU_VARIABLE * bound_regu, bool skip_first,
		       const domain_plan_key * pair, domain_plan_key * bound)
{
  memset (bound, 0, sizeof (*bound));
  bound->mixed_key_cache = -1;
  if (bound_regu == NULL)
    {
      return true;
    }
  bound->midxkey = TP_DOMAIN_TYPE (index->key_type) == DB_TYPE_MIDXKEY;
  REGU_VARIABLE_LIST operand = NULL;
  int n = 1;
  if (bound->midxkey)
    {
      assert (bound_regu->type == TYPE_FUNC && bound_regu->value.funcp->ftype == F_MIDXKEY);
      operand = bound_regu->value.funcp->operand;
      n = 0;
      for (REGU_VARIABLE_LIST op = operand; op != NULL; op = op->next)
	{
	  n++;
	}
    }
  bound->elems = (domain_plan_key_elem *) domain_plan_alloc (thread_p, n, sizeof (*bound->elems));
  if (n > 0 && bound->elems == NULL)
    {
      return false;
    }
  bool mixes = false, constant = false, row = false;
  for (int i = 0; i < n; i++)
    {
      REGU_VARIABLE *regu = bound->midxkey ? &operand->value : bound_regu;
      const TP_DOMAIN *column = domain_key_column (index->key_type, i);
      if (column == NULL)
	{
	  /* more columns than the index has: not a key of this index */
	  assert (false);
	  return false;
	}
      domain_plan_key_elem *elem = &bound->elems[bound->n_elems++];
      const domain_plan_key_elem *pair_elem = pair != NULL && i < pair->n_elems ? &pair->elems[i] : NULL;
      if (!domain_plan_key_element (index, bound->midxkey, regu, column, skip_first && i == 0, pair_elem, elem))
	{
	  return false;
	}
      mixes = mixes || elem->rule != DOMAIN_KEY_INDEX;
      constant = constant || elem->rule == DOMAIN_KEY_CONSTANT;
      row = row || (elem->rule != DOMAIN_KEY_INDEX && elem->rule != DOMAIN_KEY_CONSTANT);
      operand = operand != NULL ? operand->next : NULL;
    }
  if (bound->midxkey && mixes)
    {
      /* constants only: resolve_domains writes the domain once per execution (every constant has its value before any
       * row); the scan fills a mixed key domain cache otherwise */
      bound->constant = constant && !row;
      bound->mixed_key_cache = bound->constant ? -1 : index->n_mixed_key_caches++;
    }
  return true;
}

/* Whether a key column takes values of a key other than its own under a load-fixed element: the scan compares them
 * by the type pair comparison table. resolve_domains resolves it for an index whose elements wait for it
 * (qexec_resolve_index_keys). */
/*
 * [리뷰] domain_key_other_keys — 결정 원소가 하나도 없는 인덱스(resolved_keys_index 를 받지 않는 인덱스)에 대해, keep 도메인이 인덱스 칼럼 도메인과
 * 다른 원소가 하나라도 있는지 로드 때 한 번 계산해 index->other_keys 에 캐시한다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: 모든 경계(2*n_ranges+1 개)의 모든 원소를 훑어, CONSTANT·LATE_BIND 가 아닌 원소 중 domain_key_differs(keep_elem,
 * index_elem) 가 참인 것이 있으면 true.
 * 바뀐 것: 신설 +18줄. 루프 상한 2*n_ranges+1 이 domain_plan_add_indexes 의 bounds 할당 개수와 같다.
 */
static bool
domain_key_other_keys (const domain_plan_index * index)
{
  for (int b = 0; b < 2 * index->n_ranges + 1; b++)
    {
      const domain_plan_key *bound = &index->bounds[b];
      for (int i = 0; i < bound->n_elems; i++)
	{
	  const domain_plan_key_elem *elem = &bound->elems[i];
	  if (elem->rule != DOMAIN_KEY_CONSTANT && elem->rule != DOMAIN_KEY_LATE_BIND
	      && domain_key_differs (elem->keep_elem, elem->index_elem))
	    {
	      return true;
	    }
	}
    }
  return false;
}

/*
 * domain_plan_add_indexes () - every index scan's key plan: its bounds' elements and their
 *   rules, from INDX_INFO.key_type; the scan finds it through INDX_INFO.key_plan
 */
/*
 * [리뷰] domain_plan_add_indexes — 로드가 XASL 에서 모은 INDX_INFO 전부에 domain_plan_index 를 붙이고 indx_info->key_plan 으로
 * 건다 — stx_build_domain_plan 이 비교·상수 단계를 끝낸 뒤 부른다. 이후 스캔은 key_plan 만 읽는다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 에는 indx_info->key_plan 필드가 없고, 키 도메인 판단이 매 키 생성 때 scan_manager.c
 * 안에서 일어났다.
 * 이 PR: 인덱스마다 bounds 배열(2*n_ranges+1)을 아레나에 잡고 range 별 key1/key2 와 ISS fetch range 를 domain_plan_key_bound 로
 * 채운다. 결정 원소가 있으면 plan->n_resolved_index_keys 슬롯을 받고, 없으면 other_keys 를 한 번 계산한다.
 * 바뀐 것: 신설 +61줄. key_type==NULL 인 인덱스는 key_plan 을 NULL 로 남겨 실행 시 미해결 도메인 검사에서 걸리게 한다(코드 주석 4021).
 */
static bool
domain_plan_add_indexes (THREAD_ENTRY * thread_p, DOMAIN_LOAD_CONTEXT * ctx, DOMAIN_PLAN * plan)
{
  plan->n_indexes = ctx->n_indexes;
  plan->indexes = (domain_plan_index *) domain_plan_alloc (thread_p, plan->n_indexes, sizeof (*plan->indexes));
  if (plan->n_indexes > 0 && plan->indexes == NULL)
    {
      return false;
    }
  for (int j = 0; j < ctx->n_indexes; j++)
    {
      INDX_INFO *indx_info = ctx->indexes[j];
      domain_plan_index *index = &plan->indexes[j];
      memset (index, 0, sizeof (*index));
      index->resolved_keys_index = -1;
      index->constant_branch = ctx->index_constant_branches[j];
      indx_info->key_plan = NULL;
      if (indx_info->key_type == NULL)
	{
	  /* no key domain in the stream: the scan fails the unresolved-domain check (execution) */
	  continue;
	}
      index->key_type = indx_info->key_type;
      index->asc_key_type = domain_ascending_key_type (index->key_type);
      index->n_ranges = indx_info->key_info.key_cnt;
      index->bounds =
	(domain_plan_key *) domain_plan_alloc (thread_p, 2 * index->n_ranges + 1, sizeof (*index->bounds));
      if (index->asc_key_type == NULL || index->bounds == NULL)
	{
	  return false;
	}
      const bool iss = indx_info->use_iss != 0;
      for (int i = 0; i < index->n_ranges; i++)
	{
	  KEY_RANGE *range = &indx_info->key_info.key_ranges[i];
	  /* an index skip scan's ranges start with its skip value */
	  if (!domain_plan_key_bound (thread_p, index, range->key1, iss, NULL, &index->bounds[2 * i])
	      || !domain_plan_key_bound (thread_p, index, range->key2, iss, &index->bounds[2 * i],
					 &index->bounds[2 * i + 1]))
	    {
	      return false;
	    }
	}
      /* the index skip scan's fetch range: its one column is the skip value */
      if (!domain_plan_key_bound (thread_p, index, iss ? indx_info->iss_range.key1 : NULL, true, NULL,
				  &index->bounds[2 * index->n_ranges]))
	{
	  return false;
	}
      if (index->n_resolved_elements > 0)
	{
	  index->resolved_keys_index = plan->n_resolved_index_keys++;
	}
      else
	{
	  index->other_keys = domain_key_other_keys (index);
	}
      indx_info->key_plan = index;
    }
  return true;
}

/*
 * Predicate and function streams: a filter index predicate, a function index expression and a partition expression are
 * loaded without an execution and evaluated without resolve_domains. A regu resolve_domains would resolve refuses the
 * stream at its load (stx_index_stream_rejected), but the stream's domains need not describe its values either: the
 * catalog keeps a stream compiled against a column's type across an ALTER that changes that type
 * (filtered_index_basicfunction_delete_004: a SMALLINT column MODIFY'd to CHAR(10) under its filter predicate). So the
 * load resolves a comparison of two literals, and any comparison over another side reads the key pair table by the two
 * values' keys (comparison method KEYS) - resolved before any row, the stream's domains unused.
 */
struct DOMAIN_STREAM_CONTEXT
{
  THREAD_ENTRY *thread_p;
  bool failed;
};

static void domain_stream_walk_regu (DOMAIN_STREAM_CONTEXT * ctx, REGU_VARIABLE * regu);
static void domain_stream_walk_pred (DOMAIN_STREAM_CONTEXT * ctx, PRED_EXPR * pred);

/* A literal side's key, its value's (and the codeset and collation a COLLATE modifier gives it); false for any other
 * side, whose values are the catalog's. */
/*
 * [리뷰] domain_stream_literal_key — 스트림 보강 경로(domain_plan_stream_compares)에서 비교 한쪽 피연산자를 보고, 리터럴이면
 * DOMAIN_COMPARE_PLAN 의 그 side 를 채우고 비교 키(DOMAIN_COMPARE_KEY)를 만들어 true, 아니면 false 를 돌려준다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: TYPE_DBVAL 이 아니면 operand/domain/value 만 채우고 false. 리터럴이면 APPLY_COLLATION 이 붙고 콜레이션을 갖는 타입일 때만
 * collate[side] 를 세우고, NULL 이면 tp_Null_domain 으로 키를 만든다.
 * 바뀐 것: 신설 +19줄. false 를 돌려줄 때 collate/literal 은 건드리지 않아 memset 0 상태로 남는다.
 */
static bool
domain_stream_literal_key (const REGU_VARIABLE * regu, DOMAIN_COMPARE_PLAN * comparison, int side,
			   DOMAIN_COMPARE_KEY * key)
{
  comparison->operand[side] = NULL;
  comparison->domain[side] = regu->domain;
  comparison->value[side] = -1;
  if (regu->type != TYPE_DBVAL)
    {
      return false;
    }
  comparison->collate[side] = REGU_VARIABLE_IS_FLAGED (regu, REGU_VARIABLE_APPLY_COLLATION) && regu->domain != NULL
    && TP_TYPE_HAS_COLLATION (TP_DOMAIN_TYPE (regu->domain)) ? regu->domain : NULL;
  const DB_VALUE *literal = &regu->value.dbval;
  comparison->literal[side] = literal;
  domain_compare_key_of (DB_IS_NULL (literal) ? &tp_Null_domain : tp_domain_resolve_value (literal, NULL), key);
  domain_compare_key_collate (key, comparison->collate[side]);
  return true;
}

/* A stream comparison over a side the catalog gives its values: the key pair table by the values' keys. */
/*
 * [리뷰] domain_stream_by_keys — 비교를 「로드 때 결정하지 못했다」로 표시하는 한 줄 초기화 — 한쪽이라도 리터럴이 아니면
 * domain_stream_compare·domain_stream_elements 가 불러 method=DOMAIN_COMPARE_KEYS 로 두고, 실행 경로가 키로 비교하게 한다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: DOMAIN_COMPARE 를 값 초기화한 뒤 method·compare_index(-1)·value[0..1]·codeset_side(-1)를 센티넬로 세운다.
 * 바뀐 것: 신설 +10줄.
 */
static void
domain_stream_by_keys (DOMAIN_COMPARE * fixed)
{
  *fixed = DOMAIN_COMPARE
  {
  };
  fixed->method = DOMAIN_COMPARE_KEYS;
  fixed->compare_index = -1;
  fixed->value[0] = fixed->value[1] = fixed->codeset_side = -1;
}

/* A comparison of two stream regus, resolved now. */
/*
 * [리뷰] domain_stream_compare — 비교식 하나에 대한 DOMAIN_COMPARE_PLAN 을 XASL 언팩 아레나에 만들어 돌려준다 —
 * domain_stream_walk_pred·domain_stream_walk_arith 가 호출하고, 결과는 comp->domain_compare / compares[] 에 매달린다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 에서 두 값의 비교 도메인은 행마다 tp_value_compare_with_error 안에서 정해졌다.
 * 이 PR: 양쪽이 모두 리터럴이면 domain_resolve_comparison 으로 로드 시점에 비교 방식을 확정하고, 하나라도 아니면 domain_stream_by_keys 로 키 비교로
 * 떨어뜨린다. 할당 실패는 ctx->failed 로 올린다.
 * 바뀐 것: 신설 +26줄. 실패를 반환값이 아니라 ctx->failed 로 전파하는 계약이다.
 */
static DOMAIN_COMPARE_PLAN *
domain_stream_compare (DOMAIN_STREAM_CONTEXT * ctx, const REGU_VARIABLE * lhs, const REGU_VARIABLE * rhs)
{
  DOMAIN_COMPARE_PLAN *comparison = (DOMAIN_COMPARE_PLAN *) stx_alloc_struct (ctx->thread_p, sizeof (*comparison));
  if (comparison == NULL)
    {
      ctx->failed = true;
      return NULL;
    }
  memset (comparison, 0, sizeof (*comparison));
  comparison->constant_branch = -1;
  DOMAIN_COMPARE_KEY key[2];
  const bool lhs_literal = domain_stream_literal_key (lhs, comparison, 0, &key[0]);
  const bool rhs_literal = domain_stream_literal_key (rhs, comparison, 1, &key[1]);
  if (!lhs_literal || !rhs_literal)
    {
      domain_stream_by_keys (&comparison->fixed);
      return comparison;
    }
  if (domain_resolve_comparison (&key[0], &key[1], &comparison->fixed) != NO_ERROR)
    {
      ctx->failed = true;
      return NULL;
    }
  return comparison;
}

/* An ALL/SOME term of a stream: a literal item against the elements of its collection by the item's row of the type
 * pair comparison table, any other item by the two values' keys. */
/*
 * [리뷰] domain_stream_elements — ALL/SOME(ALSM) 항의 원소 쪽을 보고 DOMAIN_ELEMENT_COMPARE_PLAN 을 만들어
 * alsm->domain_compare 에 달 것을 돌려준다 — 원소가 리터럴이면 ROW, 아니면 PAIR 로 분류한다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: domain_stream_literal_key 가 실패하면 kind=DOMAIN_ELEMENTS_PAIR + 키 비교. 성공하면 kind=DOMAIN_ELEMENTS_ROW 이고
 * row 에 domain_compare_key_row() 결과를 넣는다.
 * 바뀐 것: 신설 +25줄.
 * [지적 C4-05]
 */
static const DOMAIN_ELEMENT_COMPARE_PLAN *
domain_stream_elements (DOMAIN_STREAM_CONTEXT * ctx, const REGU_VARIABLE * elem)
{
  DOMAIN_ELEMENT_COMPARE_PLAN *comparison =
    (DOMAIN_ELEMENT_COMPARE_PLAN *) stx_alloc_struct (ctx->thread_p, sizeof (*comparison));
  if (comparison == NULL)
    {
      ctx->failed = true;
      return NULL;
    }
  memset (comparison, 0, sizeof (*comparison));
  comparison->row = -1;
  comparison->resolved_elements_index = -1;
  comparison->pair.constant_branch = -1;
  DOMAIN_COMPARE_KEY item;
  if (!domain_stream_literal_key (elem, &comparison->pair, 0, &item))
    {
      comparison->kind = DOMAIN_ELEMENTS_PAIR;
      domain_stream_by_keys (&comparison->pair.fixed);
      return comparison;
    }
  comparison->kind = DOMAIN_ELEMENTS_ROW;
  comparison->row = domain_compare_key_row (&item);
  return comparison;
}

/* A stream has no plan items: a node that needs one gets a bare item */
/*
 * [리뷰] domain_stream_item — ARITH_TYPE 하나에 DOMAIN_PLAN_ITEM 을 만들어 arith->plan_item 에 건다 — 스트림 보강 경로에서 플랜 항목이
 * 없는 산술 노드에 자리를 만들어 주는 최소 생성자다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 의 ARITH_TYPE 에는 plan_item 필드가 없다.
 * 이 PR: stx_alloc_struct 로 잡아 0 으로 밀고 resolved_index=-1, ref=-1, operand_class=OPERAND_ROW,
 * fixed.domain=arith->domain 으로 둔다. 즉 「행이 정하는 노드」 기본값이다.
 * 바뀐 것: 신설 +17줄.
 */
static DOMAIN_PLAN_ITEM *
domain_stream_item (DOMAIN_STREAM_CONTEXT * ctx, ARITH_TYPE * arith)
{
  DOMAIN_PLAN_ITEM *item = (DOMAIN_PLAN_ITEM *) stx_alloc_struct (ctx->thread_p, (int) sizeof (*item));
  if (item == NULL)
    {
      ctx->failed = true;
      return NULL;
    }
  memset (item, 0, sizeof (*item));
  item->resolved_index = -1;
  item->ref = -1;
  item->operand_class = OPERAND_ROW;
  item->fixed.domain = arith->domain;
  arith->plan_item = item;
  return item;
}

/* A FIELD, NULLIF, LEAST or GREATEST node's resolved comparisons, carried by its bare item; NULL for
 * any other operator */
/*
 * [리뷰] domain_stream_arith_compares — 산술 노드의 비교 슬롯 배열(compares[])을 돌려준다 — 이미 plan_item 이 있으면 그 배열을, 없으면 opcode
 * 가 요구하는 개수만큼 새로 잡고 plan_item 을 만들어 매단다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: domain_arith_compares 가 NULL 이면(그 opcode 는 비교를 쓰지 않거나 할당 실패) NULL. 할당 실패는 그 함수와 domain_stream_item 이
 * ctx->failed 로 올린다.
 * 바뀐 것: 신설 +20줄. 반환 NULL 이 「비교 없음」과 「실패」 둘 다를 뜻하고, 구분은 ctx->failed 로만 된다.
 */
static const DOMAIN_COMPARE_PLAN **
domain_stream_arith_compares (DOMAIN_STREAM_CONTEXT * ctx, ARITH_TYPE * arith)
{
  if (arith->plan_item != NULL)
    {
      return arith->plan_item->compares;
    }
  const DOMAIN_COMPARE_PLAN **compares = domain_arith_compares (ctx->thread_p, arith->opcode, &ctx->failed);
  if (compares == NULL)
    {
      return NULL;
    }
  DOMAIN_PLAN_ITEM *item = domain_stream_item (ctx, arith);
  if (item == NULL)
    {
      return NULL;
    }
  item->compares = compares;
  return compares;
}

/*
 * [리뷰] domain_stream_walk_arith — ARITH_TYPE 한 노드의 자식(left/right/third/pred)을 먼저 내려간 뒤, 그 노드에 피연산자
 * 강제변환(operand coercion)과 비교 플랜을 다는 스트림 보강 워커.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: domain_operand_coercion_operator 인 연산자는 domain_plan_operand_coercion 으로 좌우 스트림 도메인에서 강제변환을 로드 때 정한다.
 * T_FIELD 는 third 와 left/right 의 두 비교를, 그 밖은 left/right 한 비교를 채운다.
 * 바뀐 것: 신설 +40줄. ctx->failed 이면 즉시 반환하는 단락 조건이 모든 워커에 공통이다.
 */
static void
domain_stream_walk_arith (DOMAIN_STREAM_CONTEXT * ctx, ARITH_TYPE * arith, bool field_bottom)
{
  if (arith == NULL || ctx->failed)
    {
      return;
    }
  domain_stream_walk_regu (ctx, arith->leftptr);
  domain_stream_walk_regu (ctx, arith->rightptr);
  domain_stream_walk_regu (ctx, arith->thirdptr);
  domain_stream_walk_pred (ctx, arith->pred);
  if (domain_operand_coercion_operator (arith->opcode) && arith->plan_item == NULL && arith->leftptr != NULL
      && arith->rightptr != NULL)
    {
      /* the operand coercion over the stream's operand domains, which describe its values - ALTER compiles
       * anew a stream that reads a changed column */
      domain_plan_operand_coercion (domain_stream_item (ctx, arith), arith->opcode, arith->leftptr->domain,
				    arith->rightptr->domain);
    }
  const DOMAIN_COMPARE_PLAN **compares = domain_stream_arith_compares (ctx, arith);
  if (compares == NULL)
    {
      return;
    }
  if (arith->opcode == T_FIELD)
    {
      if (field_bottom && compares[0] == NULL && arith->thirdptr != NULL && arith->leftptr != NULL)
	{
	  compares[0] = domain_stream_compare (ctx, arith->thirdptr, arith->leftptr);
	}
      if (compares[1] == NULL && arith->thirdptr != NULL && arith->rightptr != NULL)
	{
	  compares[1] = domain_stream_compare (ctx, arith->thirdptr, arith->rightptr);
	}
    }
  else if (compares[0] == NULL && arith->leftptr != NULL && arith->rightptr != NULL)
    {
      compares[0] = domain_stream_compare (ctx, arith->leftptr, arith->rightptr);
    }
}

/*
 * [리뷰] domain_stream_walk_regu — REGU_VARIABLE 한 노드의 종류를 보고 자식으로 내려가는 디스패처 — 산술이면 walk_arith, 함수/regu 목록이면
 * 피연산자 목록을 재귀한다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: TYPE_INARITH/OUTARITH 는 REGU_VARIABLE_FIELD_COMPARE 플래그를 field_bottom 으로 넘겨 T_FIELD 의 첫 비교를 달지 말지 알린다.
 * 그 밖의 타입은 아무것도 하지 않는다.
 * 바뀐 것: 신설 +29줄.
 */
static void
domain_stream_walk_regu (DOMAIN_STREAM_CONTEXT * ctx, REGU_VARIABLE * regu)
{
  if (regu == NULL || ctx->failed)
    {
      return;
    }
  switch (regu->type)
    {
    case TYPE_INARITH:
    case TYPE_OUTARITH:
      domain_stream_walk_arith (ctx, regu->value.arithptr, REGU_VARIABLE_IS_FLAGED (regu, REGU_VARIABLE_FIELD_COMPARE));
      break;
    case TYPE_FUNC:
      for (REGU_VARIABLE_LIST op = regu->value.funcp->operand; op != NULL; op = op->next)
	{
	  domain_stream_walk_regu (ctx, &op->value);
	}
      break;
    case TYPE_REGU_VAR_LIST:
      for (REGU_VARIABLE_LIST op = regu->value.regu_var_list; op != NULL; op = op->next)
	{
	  domain_stream_walk_regu (ctx, &op->value);
	}
      break;
    default:
      break;
    }
}

/*
 * [리뷰] domain_stream_walk_pred — PRED_EXPR 트리를 돌며 비교항(T_COMP)·ALSM 항에 비교 플랜을 달고 LIKE/RLIKE 항의 regu 를 내려간다 —
 * 스트림 보강의 술어 쪽 진입점.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 에서는 COMP_EVAL_TERM 에 domain_compare 필드가 없고 비교 도메인이 행마다
 * 결정됐다(query_evaluator.c:153 eval_value_rel_cmp).
 * 이 PR: T_PRED 는 lhs 를 재귀하고 rhs 로 꼬리이동, T_NOT_TERM 은 꼬리이동한다. 값 비교 연산자(R_EQ 등 7종)이고 양쪽이 LIST_ID 가 아닐 때만
 * comp->domain_compare 를 만들고, 만들었으면 domain_compare_set_operator_functions 로 연산자 함수를 미리 박는다.
 * 바뀐 것: 신설 +66줄. 값 비교 판정 조건을 domain_add_compare_term 과 똑같이 손으로 한 번 더 적은 자리다(주석 4309) — 두 곳이 같이 바뀌어야 하는 암묵 계약.
 */
static void
domain_stream_walk_pred (DOMAIN_STREAM_CONTEXT * ctx, PRED_EXPR * pred)
{
  while (pred != NULL && !ctx->failed)
    {
      if (pred->type == T_PRED)
	{
	  domain_stream_walk_pred (ctx, pred->pe.m_pred.lhs);
	  pred = pred->pe.m_pred.rhs;
	  continue;
	}
      if (pred->type == T_NOT_TERM)
	{
	  pred = pred->pe.m_not_term;
	  continue;
	}
      EVAL_TERM *term = &pred->pe.m_eval_term;
      switch (term->et_type)
	{
	case T_COMP_EVAL_TERM:
	  {
	    COMP_EVAL_TERM *comp = &term->et.et_comp;
	    domain_stream_walk_regu (ctx, comp->lhs);
	    domain_stream_walk_regu (ctx, comp->rhs);
	    /* as domain_add_compare_term: the value comparisons, not a set comparison or a list side */
	    const bool value_comparison = comp->rel_op == R_EQ || comp->rel_op == R_NE || comp->rel_op == R_GT
	      || comp->rel_op == R_GE || comp->rel_op == R_LT || comp->rel_op == R_LE || comp->rel_op == R_EQ_TORDER
	      || comp->rel_op == R_NULLSAFE_EQ;
	    if (value_comparison && comp->domain_compare == NULL && comp->lhs != NULL && comp->rhs != NULL
		&& comp->lhs->type != TYPE_LIST_ID && comp->rhs->type != TYPE_LIST_ID)
	      {
		DOMAIN_COMPARE_PLAN *comparison = domain_stream_compare (ctx, comp->lhs, comp->rhs);
		if (comparison != NULL)
		  {
		    /* the term's row runs its resolution's operator functions */
		    domain_compare_set_operator_functions (&comparison->fixed);
		  }
		comp->domain_compare = comparison;
	      }
	  }
	  break;
	case T_ALSM_EVAL_TERM:
	  {
	    ALSM_EVAL_TERM *alsm = &term->et.et_alsm;
	    domain_stream_walk_regu (ctx, alsm->elem);
	    domain_stream_walk_regu (ctx, alsm->elemset);
	    if (alsm->domain_compare == NULL && alsm->elem != NULL && alsm->elemset != NULL)
	      {
		alsm->domain_compare = domain_stream_elements (ctx, alsm->elem);
	      }
	  }
	  break;
	case T_LIKE_EVAL_TERM:
	  domain_stream_walk_regu (ctx, term->et.et_like.src);
	  domain_stream_walk_regu (ctx, term->et.et_like.pattern);
	  domain_stream_walk_regu (ctx, term->et.et_like.esc_char);
	  break;
	case T_RLIKE_EVAL_TERM:
	  domain_stream_walk_regu (ctx, term->et.et_rlike.src);
	  domain_stream_walk_regu (ctx, term->et.et_rlike.pattern);
	  domain_stream_walk_regu (ctx, term->et.et_rlike.case_sensitive);
	  break;
	}
      return;
    }
}

/*
 * [리뷰] domain_plan_stream_compares — 스트림에서 개별 술어/regu 만 따로 복원하는 경로의 공개 진입점 — stream_to_xasl.c:373·443 이 불러 그
 * 조각에도 비교 플랜을 달아 주고, 실패는 ER_OUT_OF_VIRTUAL_MEMORY 로 돌려준다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: DOMAIN_STREAM_CONTEXT 를 스택에 만들어 pred 와 regu 를 차례로 걷고 ctx.failed 를 에러 코드로 번역한다.
 * 바뀐 것: 신설 +8줄. 전체 XASL 경로(stx_build_domain_plan)와 조각 경로가 같은 워커를 공유하는 두 번째 입구다.
 */
int
domain_plan_stream_compares (THREAD_ENTRY * thread_p, PRED_EXPR * pred, REGU_VARIABLE * regu)
{
  DOMAIN_STREAM_CONTEXT ctx = { thread_p, false };
  domain_stream_walk_pred (&ctx, pred);
  domain_stream_walk_regu (&ctx, regu);
  return ctx.failed ? ER_OUT_OF_VIRTUAL_MEMORY : NO_ERROR;
}

/*
 * A load entry's output - the value it writes: a fetch into a value list, an arithmetic result, an accumulator, an
 * analytic result, a single-row subquery's column - for finding the load entries a value pointer reads. The outputs are
 * sorted by the value and then by walk order, so a value's writers come in the order a scan of the load entries met
 * them.
 */
struct DOMAIN_LOAD_OUTPUT
{
  const DB_VALUE *value;
  DOMAIN_LOAD_ENTRY *load_entry;
  int order;
};

/*
 * [리뷰] domain_compare_outputs — qsort 비교자 — domain_match_value_pointers 가 로드 엔트리의 출력 DB_VALUE 포인터 목록을 값 주소
 * 오름차순(동률이면 원래 순서)으로 정렬할 때 쓴다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: 포인터를 uintptr_t 로 비교하고, 같으면 order 로 안정 정렬을 흉내낸다.
 * 바뀐 것: 신설 +12줄.
 */
static int
domain_compare_outputs (const void *lhs, const void *rhs)
{
  const DOMAIN_LOAD_OUTPUT *a = (const DOMAIN_LOAD_OUTPUT *) lhs;
  const DOMAIN_LOAD_OUTPUT *b = (const DOMAIN_LOAD_OUTPUT *) rhs;
  const uintptr_t va = (uintptr_t) a->value, vb = (uintptr_t) b->value;
  if (va != vb)
    {
      return va < vb ? -1 : 1;
    }
  return a->order < b->order ? -1 : a->order > b->order ? 1 : 0;
}

/* The first of a value's outputs among the sorted outputs; n when no load entry writes it. */
/*
 * [리뷰] domain_first_output — 정렬된 출력 목록에서 주어진 DB_VALUE 포인터의 하한(lower bound)을 이진 탐색으로 찾는다 —
 * domain_match_value_pointers 가 값 포인터마다 전체 엔트리 스캔 대신 이것을 쓴다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: 표준 lower_bound 루프. n==0 이면 0 을 돌려주므로 outputs==NULL 과도 안전하게 맞물린다.
 * 바뀐 것: 신설 +18줄. 로드 1회 비용을 O(E^2) 에서 O(E log E) 로 낮추는 자리.
 */
static int
domain_first_output (const DOMAIN_LOAD_OUTPUT * outputs, int n, const DB_VALUE * value)
{
  int lo = 0, hi = n;
  while (lo < hi)
    {
      const int mid = lo + (hi - lo) / 2;
      if ((uintptr_t) outputs[mid].value < (uintptr_t) value)
	{
	  lo = mid + 1;
	}
      else
	{
	  hi = mid;
	}
    }
  return lo;
}

/* A (domain, DOMAIN_PLAN_CONSUMER_CONVERTS) a bind position's references were given, and its reference: the
 * positions' lists replace a scan of the load entries before each bind. */
struct DOMAIN_LOAD_REF
{
  const TP_DOMAIN *domain;
  bool consumer_converts;
  int ref;
  int next;			/* the position's next entry; -1 */
};

/* The load context's lists and load entries, once the plan is published; on a failure the owners the walk bound are
 * left without an item (one function of stx_build_domain_plan's steps). */
/*
 * [리뷰] domain_load_context_free — 로드 중에만 쓰는 스크래치(DOMAIN_LOAD_CONTEXT)의 db_private 블록과 연결 리스트를 전부 되돌려준다 —
 * stx_build_domain_plan 이 플랜 조립을 끝낸 직후 한 번 부른다. 플랜 본체는 아레나라 여기서 풀지 않는다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: 14개 배열과 element_terms/list_columns/bindings/compare_pairs/head 다섯 리스트를 해제한다. ctx->failed 이면
 * bindings·compare_pairs 의 *owner 를 NULL 로 되돌려, 실패한 로드가 반쯤 연결된 포인터를 XASL 에 남기지 않게 한다.
 * 바뀐 것: 신설 +104줄. bindings 를 compare_pairs 보다 먼저 푸는 순서가 의도된 것이고 주석 4500 에 적혀 있다.
 */
static void
domain_load_context_free (THREAD_ENTRY * thread_p, DOMAIN_LOAD_CONTEXT * ctx)
{
  if (ctx->constant_branches != NULL)
    {
      db_private_free (thread_p, ctx->constant_branches);
    }
  if (ctx->blocks != NULL)
    {
      db_private_free (thread_p, ctx->blocks);
    }
  if (ctx->block_constant_branches != NULL)
    {
      db_private_free (thread_p, ctx->block_constant_branches);
    }
  if (ctx->index_constant_branches != NULL)
    {
      db_private_free (thread_p, ctx->index_constant_branches);
    }
  if (ctx->compare_term_constant_branches != NULL)
    {
      db_private_free (thread_p, ctx->compare_term_constant_branches);
    }
  if (ctx->compare_term_scopes != NULL)
    {
      db_private_free (thread_p, ctx->compare_term_scopes);
    }
  if (ctx->compare_term_ranges != NULL)
    {
      db_private_free (thread_p, ctx->compare_term_ranges);
    }
  if (ctx->ancestors != NULL)
    {
      db_private_free (thread_p, ctx->ancestors);
    }
  if (ctx->temporary_scopes != NULL)
    {
      db_private_free (thread_p, ctx->temporary_scopes);
    }
  if (ctx->temporary_blocks != NULL)
    {
      db_private_free (thread_p, ctx->temporary_blocks);
    }
  if (ctx->late_bind_order != NULL)
    {
      db_private_free (thread_p, ctx->late_bind_order);
    }
  if (ctx->indexes != NULL)
    {
      db_private_free (thread_p, ctx->indexes);
    }
  if (ctx->defines != NULL)
    {
      db_private_free (thread_p, ctx->defines);
    }
  if (ctx->compare_terms != NULL)
    {
      db_private_free (thread_p, ctx->compare_terms);
    }
  while (ctx->element_terms != NULL)
    {
      DOMAIN_LOAD_ELEMENT_TERM *e = ctx->element_terms;
      ctx->element_terms = e->next;
      db_private_free (thread_p, e);
    }
  while (ctx->list_columns != NULL)
    {
      DOMAIN_LOAD_LIST_COLUMN *c = ctx->list_columns;
      ctx->list_columns = c->next;
      db_private_free (thread_p, c);
    }
  while (ctx->bindings != NULL)
    {
      DOMAIN_LOAD_BINDING *b = ctx->bindings;
      ctx->bindings = b->next;
      if (ctx->failed)
	{
	  *b->owner = NULL;
	}
      db_private_free (thread_p, b);
    }
  /* after the bindings, which write into the pairs' column sides */
  while (ctx->compare_pairs != NULL)
    {
      DOMAIN_LOAD_COMPARE_PAIR *pair = ctx->compare_pairs;
      ctx->compare_pairs = pair->next;
      if (ctx->failed)
	{
	  *pair->owner = NULL;
	}
      db_private_free (thread_p, pair);
    }
  while (ctx->head != NULL)
    {
      DOMAIN_LOAD_ENTRY *r = ctx->head;
      ctx->head = r->next;
      if (r->link != r->link_inline)
	{
	  db_private_free (thread_p, r->link);
	  db_private_free (thread_p, (void *) r->literal);
	}
      db_private_free (thread_p, r);
    }
}

/* The value pointers' aliases and producers, found through the load entries' sorted outputs */
/*
 * [리뷰] domain_match_value_pointers — 로드 엔트리들 가운데 「같은 DB_VALUE 를 가리키는 소비자와 생산자」를 이어 준다 — stx_build_domain_plan
 * 이 XASL 걷기 직후 불러 r->alias(같은 항목 재사용)와 r->producer(값을 쓰는 노드)를 채운다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: 출력 포인터 목록을 만들어 qsort 한 뒤, TYPE_CONSTANT regu 마다 이진 탐색으로 같은 값을 쓰는 엔트리를 찾는다. alias 는 컴파일
 * 도메인·operand_class·flags 가 모두 같고 GROUP_CONCAT 값을 읽는 경우가 아닐 때만 맺는다.
 * 바뀐 것: 신설 +84줄. db_private_alloc/free 짝(4538/4606)이고 ctx->failed 이면 두 매칭 루프가 모두 건너뛴다.
 */
static void
domain_match_value_pointers (THREAD_ENTRY * thread_p, DOMAIN_LOAD_CONTEXT * ctx)
{
  /* the load entries' outputs, sorted: a value pointer finds the entries writing its value by a binary search, not by a
   * scan of every entry */
  int n_outputs = 0;
  for (DOMAIN_LOAD_ENTRY * r = ctx->head; r != NULL; r = r->next)
    {
      n_outputs += (r->output[0] != NULL) + (r->output[1] != NULL);
    }
  DOMAIN_LOAD_OUTPUT *outputs = NULL;
  if (n_outputs > 0 && !ctx->failed)
    {
      outputs = (DOMAIN_LOAD_OUTPUT *) db_private_alloc (thread_p, sizeof (*outputs) * (size_t) n_outputs);
      ctx->failed = outputs == NULL;
    }
  if (outputs != NULL)
    {
      int k = 0, order = 0;
      for (DOMAIN_LOAD_ENTRY * r = ctx->head; r != NULL; r = r->next, order++)
	{
	  for (int i = 0; i < 2; i++)
	    {
	      if (r->output[i] != NULL)
		{
		  outputs[k].value = r->output[i];
		  outputs[k].load_entry = r;
		  outputs[k++].order = order;
		}
	    }
	}
      qsort (outputs, (size_t) n_outputs, sizeof (*outputs), domain_compare_outputs);
    }
  /* Output/list readers borrow their producer's answer. Match the restored
   * value identity, not a column ordinal from a different XASL block. Keep an
   * independent item when the consumer has a different compiled domain. */
  for (DOMAIN_LOAD_ENTRY * r = ctx->head; r != NULL && !ctx->failed; r = r->next)
    {
      if (r->regu == NULL || r->regu->type != TYPE_CONSTANT || r->regu->value.dbvalptr == NULL)
	{
	  continue;
	}
      const DB_VALUE *value = r->regu->value.dbvalptr;
      for (int k = domain_first_output (outputs, n_outputs, value); k < n_outputs && outputs[k].value == value; k++)
	{
	  DOMAIN_LOAD_ENTRY *p = outputs[k].load_entry;
	  if (p == r || (p->regu != NULL && p->regu->type == TYPE_CONSTANT))
	    {
	      continue;
	    }
	  if (p->item.fixed.domain == r->item.fixed.domain
	      && p->item.operand_class == r->item.operand_class
	      && p->item.flags == r->item.flags && !domain_reads_group_concat_value (r, p))
	    {
	      r->alias = p;
	      break;
	    }
	}
    }
  /* A value pointer's producer is the node writing the value it points at: a fetch into a value
   * list, an arithmetic result, an accumulator, an analytic result, a single-row subquery's column. */
  for (DOMAIN_LOAD_ENTRY * r = ctx->head; r != NULL && !ctx->failed; r = r->next)
    {
      if (r->alias != NULL || r->regu == NULL || r->regu->type != TYPE_CONSTANT || r->regu->value.dbvalptr == NULL)
	{
	  continue;
	}
      /* a writer that is itself a value pointer counts too: a scalar subquery's BUILDVALUE column points at its
       * accumulator and is copied into single_tuple */
      const DB_VALUE *value = r->regu->value.dbvalptr;
      for (int k = domain_first_output (outputs, n_outputs, value); k < n_outputs && outputs[k].value == value; k++)
	{
	  if (outputs[k].load_entry != r)
	    {
	      r->producer = outputs[k].load_entry;
	      break;
	    }
	}
    }
  if (outputs != NULL)
    {
      db_private_free (thread_p, outputs);
    }
}

/* Each bind's reference and the constant count (one of stx_build_domain_plan's steps) */
/*
 * [리뷰] domain_assign_references — bind 위치(val_pos)마다 참조 번호(item->ref)를 정한다 — 같은 위치라도 (도메인, 소비자 변환 여부)가 다르면 별도
 * 참조를 하나 더 만들어, 실행 전 게이트가 한 위치를 서로 다른 도메인으로 두 번 쓰는 일이 없게 한다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: 위치별 단일 연결 리스트(ref_first/refs)로 이미 만든 (도메인, consumer_converts) 조합을 찾고, 없으면 첫 사용은 val_pos 를 그대로, 그 뒤는
 * plan->n_refs++ 를 쓴다. OPERAND_CONST 엔트리 수를 세어 plan->n_const_refs 로 올린다.
 * 바뀐 것: 신설 +67줄. ref_first 길이가 plan->dbval_cnt 라, 호출자가 먼저 dbval_cnt 를 최대 val_pos+1 로 늘려 둔 것(4760~4767)에 의존한다 —
 * 그 확장 루프가 이 호출보다 앞에 있어야 한다는 계약이 코드 순서로만 보장된다.
 */
static void
domain_assign_references (THREAD_ENTRY * thread_p, DOMAIN_LOAD_CONTEXT * ctx, DOMAIN_PLAN * plan)
{
  /* References are assigned in deterministic traversal order. The first use of
   * each bind keeps val_pos; only a different (domain, failure policy) adds a value.
   * Each position keeps the pairs its references were given so far. */
  int n_binds = 0;
  for (DOMAIN_LOAD_ENTRY * r = ctx->head; r != NULL; r = r->next)
    {
      n_binds += r->alias == NULL && r->cold.val_pos >= 0;
    }
  int *ref_first = NULL;
  DOMAIN_LOAD_REF *refs = NULL;
  if (n_binds > 0 && !ctx->failed)
    {
      ref_first = (int *) db_private_alloc (thread_p, sizeof (*ref_first) * (size_t) plan->dbval_cnt);
      refs = (DOMAIN_LOAD_REF *) db_private_alloc (thread_p, sizeof (*refs) * (size_t) n_binds);
      ctx->failed = ref_first == NULL || refs == NULL;
      for (int i = 0; ref_first != NULL && i < plan->dbval_cnt; i++)
	{
	  ref_first[i] = -1;
	}
    }
  int n_ref_entries = 0;
  for (DOMAIN_LOAD_ENTRY * r = ctx->head; r != NULL && !ctx->failed; r = r->next)
    {
      if (r->alias != NULL)
	{
	  continue;
	}
      if (r->cold.val_pos >= 0)
	{
	  const int pos = r->cold.val_pos;
	  const bool first = ref_first[pos] < 0;
	  for (int e = ref_first[pos]; e >= 0; e = refs[e].next)
	    {
	      if (refs[e].domain == r->item.fixed.domain
		  && refs[e].consumer_converts == ((r->item.flags & DOMAIN_PLAN_CONSUMER_CONVERTS) != 0))
		{
		  r->item.ref = refs[e].ref;
		  break;
		}
	    }
	  if (r->item.ref < 0)
	    {
	      r->item.ref = first ? pos : plan->n_refs++;
	      refs[n_ref_entries].domain = r->item.fixed.domain;
	      refs[n_ref_entries].consumer_converts = (r->item.flags & DOMAIN_PLAN_CONSUMER_CONVERTS) != 0;
	      refs[n_ref_entries].ref = r->item.ref;
	      refs[n_ref_entries].next = ref_first[pos];
	      ref_first[pos] = n_ref_entries++;
	    }
	}
      if (r->item.operand_class == OPERAND_CONST)
	{
	  plan->n_const_refs++;
	}
    }
  if (ref_first != NULL)
    {
      db_private_free (thread_p, ref_first);
    }
  if (refs != NULL)
    {
      db_private_free (thread_p, refs);
    }
}

/*
 * [리뷰] stx_build_domain_plan — 로드 게이트의 본체 — stream_to_xasl.c:269 가 XASL 언팩 직후 루트마다 한 번 부르고, XASL 전체를 걸어
 * DOMAIN_PLAN 을 아레나에 완성해 root->domain_plan 에 단다. 실행 전 게이트(qexec_resolve_domains)는 이 플랜만 읽는다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 의 stx_map_stream_to_xasl 은 언팩만 하고 도메인에 관한 사전 계산을 하지 않았다.
 * 이 PR: domain_walk_xasl → 값 포인터 매칭 → (CTE 칼럼 먼저) 해결 기록 → 항목 번호 매기기 → 실행 도메인 번호를 3그룹(보간 리스트 / 피연산자 타입 / 나머지)
 * 순으로 매기기 → dbval_cnt 확장 → 참조 배정 → 늦은 바인딩 링크 작성 → 상수·비교·인덱스·임시값 단계 → 상수 분기 확정 → 스크래치 해제 → const_refs 정렬 →
 * domain_plan_validate. 검증 실패는 ER_QPROC_DOMAIN_UNRESOLVED 로 로드를 거절한다.
 * 바뀐 것: 신설 +273줄. 실패는 전부 ctx.failed 한 플래그로 모여 ER_OUT_OF_VIRTUAL_MEMORY 하나로 번역되고, 실패 시 모든 *r->owner 가 NULL 로
 * 되돌아간다.
 * [지적 C3-01]
 */
int
stx_build_domain_plan (THREAD_ENTRY * thread_p, XASL_NODE * root, XASL_UNPACK_INFO * unpack_info)
{
  if (root->domain_plan != NULL)
    {
      return NO_ERROR;
    }
  assert (unpack_info == get_xasl_unpack_info_ptr (thread_p));
  DOMAIN_PLAN *plan = (DOMAIN_PLAN *) stx_alloc_struct (thread_p, sizeof (*plan));
  if (plan == NULL)
    {
      return ER_OUT_OF_VIRTUAL_MEMORY;
    }
  memset (plan, 0, sizeof (*plan));
  plan->dbval_cnt = root->dbval_cnt;
  plan->n_refs = root->dbval_cnt;
  /* the execution's scope comes first (DOMAIN_SCOPE_EXECUTION) */
  plan->n_scopes = 1;
  DOMAIN_LOAD_CONTEXT ctx;
  memset (&ctx, 0, sizeof (ctx));
  ctx.thread_p = thread_p;
  ctx.plan = plan;
  ctx.constant_branch = -1;
  domain_walk_xasl (&ctx, root);
  domain_match_value_pointers (thread_p, &ctx);
  /* CTE columns first: a recursive part then meets its own column in progress and reads the non-recursive column in
   * its place, whichever load entry the walk met first */
  for (DOMAIN_LOAD_LIST_COLUMN * c = ctx.list_columns; c != NULL && !ctx.failed; c = c->next)
    {
      if (c->xasl->type == CTE_PROC)
	{
	  domain_resolve_record (&ctx, domain_load_entry_of (c->item));
	}
    }
  for (DOMAIN_LOAD_ENTRY * r = ctx.head; r != NULL && !ctx.failed; r = r->next)
    {
      domain_resolve_record (&ctx, r);
    }
  /* a value pointer reads its producer's resolutions through the producer's item, but each node keeps a domain of
   * its own - a column over an aggregate's accumulator, say, stays as compiled when the aggregate resolves. Where
   * either has an execution domain, the consumer's node gets its own copy of the item (domain_plan_add_item_copies) and
   * its own execution domain. */
  plan->n_items = 0;
  for (DOMAIN_LOAD_ENTRY * r = ctx.head; r != NULL; r = r->next)
    {
      if (r->alias == NULL || r->needs_node_domain || r->alias->needs_node_domain)
	{
	  r->index = plan->n_items++;
	}
    }
  for (DOMAIN_LOAD_ENTRY * r = ctx.head; r != NULL; r = r->next)
    {
      if (r->alias != NULL && !r->needs_node_domain && !r->alias->needs_node_domain)
	{
	  r->index = r->alias->index;
	}
    }
  /* the execution domains: MEDIAN / PERCENTILE aggregates first, then the other aggregates and analytic functions,
   * then every other node, so that the list domains and the operand types, which only those keep, are the first
   * entries' alone (n_interpolation_list_domains, n_operand_types) */
  for (int group = 0; group < 3; group++)
    {
      for (DOMAIN_LOAD_ENTRY * r = ctx.head; r != NULL; r = r->next)
	{
	  if (r->needs_node_domain && group == (r->needs_list_domain ? 0 : r->needs_operand_type ? 1 : 2))
	    {
	      r->item.node_domain_index = ++plan->n_node_domains;
	    }
	}
      if (group == 0)
	{
	  plan->n_interpolation_list_domains = plan->n_node_domains;
	}
      else if (group == 1)
	{
	  plan->n_operand_types = plan->n_node_domains;
	}
    }
  /* A nested parser_generate_xasl () restarts parser->dbval_cnt, so root->dbval_cnt can
   * understate the positions the tree references (qmgr then sees surplus values). The
   * plan covers every referenced position so secondary references never overlap one. */
  for (DOMAIN_LOAD_ENTRY * r = ctx.head; r != NULL; r = r->next)
    {
      if (r->cold.val_pos >= plan->dbval_cnt)
	{
	  plan->dbval_cnt = r->cold.val_pos + 1;
	}
    }
  plan->n_refs = plan->dbval_cnt;
  domain_assign_references (thread_p, &ctx, plan);
  /* late-binding nodes in resolution order: producers first */
  plan->n_late_bind_nodes = ctx.n_late_bind_order;
  plan->items = (DOMAIN_PLAN_ITEM *) domain_plan_alloc (thread_p, plan->n_items, sizeof (*plan->items));
  plan->items_cold = (DOMAIN_PLAN_ITEM_COLD *) domain_plan_alloc (thread_p, plan->n_items, sizeof (*plan->items_cold));
  plan->late_bind_nodes =
    (DOMAIN_PLAN_ITEM **) domain_plan_alloc (thread_p, plan->n_late_bind_nodes, sizeof (*plan->late_bind_nodes));
  plan->late_bind_links =
    (DOMAIN_LATE_BIND_LINK *) domain_plan_alloc (thread_p, plan->n_late_bind_nodes, sizeof (*plan->late_bind_links));
  plan->const_refs = (DOMAIN_PLAN_ITEM **) domain_plan_alloc (thread_p, plan->n_const_refs, sizeof (*plan->const_refs));
  plan->resolved_late_bind_node =
    (int *) domain_plan_alloc (thread_p, plan->n_resolved, sizeof (*plan->resolved_late_bind_node));
  plan->resolved_non_cacheable =
    (bool *) domain_plan_alloc (thread_p, plan->n_resolved, sizeof (*plan->resolved_non_cacheable));
  plan->resolved_session_dependent =
    (bool *) domain_plan_alloc (thread_p, plan->n_resolved, sizeof (*plan->resolved_session_dependent));
  ctx.failed = ctx.failed || (plan->n_items && (!plan->items || !plan->items_cold)) || (plan->n_late_bind_nodes
											&& (!plan->late_bind_nodes
											    || !plan->late_bind_links))
    || (plan->n_const_refs && !plan->const_refs)
    || (plan->n_resolved
	&& (!plan->resolved_late_bind_node || !plan->resolved_non_cacheable || !plan->resolved_session_dependent));
  int constant = 0;
  for (DOMAIN_LOAD_ENTRY * r = ctx.head; r != NULL; r = r->next)
    {
      if (!ctx.failed)
	{
	  DOMAIN_PLAN_ITEM *item = &plan->items[r->index];
	  *r->owner = item;
	  if (r->alias == NULL)
	    {
	      *item = r->item;
	      item->flags |=
		(r->variable ? DOMAIN_PLAN_VARIABLE : 0) | (r->variable_position ? DOMAIN_PLAN_VARIABLE_POSITION : 0);
	      plan->items_cold[r->index] = r->cold;
	      if (item->operand_class == OPERAND_CONST)
		{
		  plan->const_refs[constant++] = item;
		}
	    }
	}
      else
	{
	  *r->owner = NULL;
	}
    }
  /* a binding's target is a load entry's item: the binding takes that entry's published item (not a scan
   * of the bindings for each entry) */
  for (DOMAIN_LOAD_BINDING * b = ctx.bindings; b != NULL && !ctx.failed; b = b->next)
    {
      *b->owner = &plan->items[domain_load_entry_of (b->target)->index];
    }
  if (!ctx.failed)
    {
      for (int i = 0; i < plan->n_resolved; i++)
	{
	  plan->resolved_late_bind_node[i] = -1;
	  plan->resolved_non_cacheable[i] = false;
	  plan->resolved_session_dependent[i] = false;
	}
      for (int g = 0; g < ctx.n_late_bind_order; g++)
	{
	  /* every operand is a load entry's item; its published copy sits at that entry's index */
	  DOMAIN_LOAD_ENTRY *r = ctx.late_bind_order[g];
	  DOMAIN_LATE_BIND_LINK *link = &plan->late_bind_links[g];
	  memset (link, 0, sizeof (*link));
	  link->operands =
	    (const DOMAIN_PLAN_ITEM **) domain_plan_alloc (thread_p, r->n_link, sizeof (*link->operands));
	  link->literal = (const DB_VALUE **) domain_plan_alloc (thread_p, r->n_link, sizeof (*link->literal));
	  if (link->operands == NULL || link->literal == NULL)
	    {
	      ctx.failed = true;
	      break;
	    }
	  link->n_operands = r->n_link;
	  link->elt_index = r->elt_index;
	  link->elt_index_cast = r->elt_index_cast;
	  link->consumer = r->consumer;
	  link->argument = r->argument;
	  /* a node's resolution inherits its sources' limits (producers come first, so theirs are set) */
	  bool is_non_cacheable = r->item.operand_class == OPERAND_NON_CACHEABLE;
	  /* a session variable read is its own source: the resolutions above it wait for
	   * qexec_resolve_session_variables, where the variable gets its type for the statement */
	  bool session_dependent = r->cold.opcode == T_EVALUATE_VARIABLE;
	  for (int i = 0; i < r->n_link; i++)
	    {
	      const DOMAIN_LOAD_ENTRY *source = domain_owner_load_entry (domain_load_entry_of (r->link[i]));
	      link->operands[i] = &plan->items[source->index];
	      link->literal[i] = r->literal[i];
	      if (source->item.resolved_index >= 0)
		{
		  is_non_cacheable = is_non_cacheable || plan->resolved_non_cacheable[source->item.resolved_index];
		  session_dependent = session_dependent
		    || plan->resolved_session_dependent[source->item.resolved_index];
		}
	    }
	  plan->late_bind_nodes[g] = &plan->items[r->index];
	  plan->resolved_late_bind_node[r->item.resolved_index] = g;
	  plan->resolved_non_cacheable[r->item.resolved_index] = is_non_cacheable;
	  plan->resolved_session_dependent[r->item.resolved_index] = session_dependent;
	}
    }
  if (!ctx.failed)
    {
      /* constant expressions before comparisons, whose constant sides read them */
      const int constant_base = plan->n_refs;
      ctx.failed = !domain_plan_add_constants (thread_p, &ctx, plan);
      if (!ctx.failed)
	{
	  domain_plan_add_item_copies (&ctx, plan);
	  /* before the comparisons, whose comparisons wait for the nodes that wait */
	  domain_plan_add_late_bind_waits (plan, constant_base);
	  ctx.failed = !domain_plan_add_session_variables (thread_p, &ctx, plan);
	}
      ctx.failed = ctx.failed || !domain_plan_add_compares (thread_p, &ctx, plan, constant_base)
	|| !domain_plan_add_constant_comparisons (thread_p, plan, constant_base)
	|| !domain_plan_add_indexes (thread_p, &ctx, plan)
	|| !domain_plan_add_temporaries (thread_p, &ctx, plan, constant_base);
    }
  if (!ctx.failed && ctx.constant_branches_ambiguous)
    {
      /* a node below two constant branches neither of which is around the other - no constant branch chain says every
       * way to it, so the plan keeps no constant branches and every failure is resolve_domains' error */
      for (int i = 0; i < plan->n_items; i++)
	{
	  plan->items_cold[i].constant_branch = -1;
	}
      for (int k = 0; k < plan->n_compare_indexes; k++)
	{
	  plan->compares[k]->constant_branch = -1;
	}
      for (int k = 0; k < plan->n_element_comparisons; k++)
	{
	  plan->element_comparisons[k]->pair.constant_branch = -1;
	}
      for (int j = 0; j < plan->n_indexes; j++)
	{
	  plan->indexes[j].constant_branch = -1;
	}
    }
  else if (!ctx.failed && ctx.n_constant_branches > 0)
    {
      plan->constant_branches =
	(DOMAIN_PLAN_CONSTANT_BRANCH *) domain_plan_alloc (thread_p, ctx.n_constant_branches,
							   sizeof (*plan->constant_branches));
      ctx.failed = plan->constant_branches == NULL;
      if (!ctx.failed)
	{
	  memcpy (plan->constant_branches, ctx.constant_branches,
		  sizeof (*plan->constant_branches) * ctx.n_constant_branches);
	  plan->n_constant_branches = ctx.n_constant_branches;
	}
    }
  domain_load_context_free (thread_p, &ctx);
  if (ctx.failed)
    {
      return ER_OUT_OF_VIRTUAL_MEMORY;
    }
  if (plan->n_const_refs > 1)
    {
      qsort (plan->const_refs, plan->n_const_refs, sizeof (*plan->const_refs), domain_compare_refs);
    }
  if (plan->n_const_refs > 0)
    {
      /* each reference's bind position beside it, in the sorted order: the bind step (qexec_share_value) walks the
       * references at every execution */
      plan->const_ref_pos = (int *) domain_plan_alloc (thread_p, plan->n_const_refs, sizeof (*plan->const_ref_pos));
      if (plan->const_ref_pos == NULL)
	{
	  return ER_OUT_OF_VIRTUAL_MEMORY;
	}
      for (int i = 0; i < plan->n_const_refs; i++)
	{
	  plan->const_ref_pos[i] = plan->items_cold[plan->const_refs[i] - plan->items].val_pos;
	}
    }
  if (!domain_plan_validate (plan))
    {
      er_set (ER_ERROR_SEVERITY, ARG_FILE_LINE, ER_QPROC_DOMAIN_UNRESOLVED, 4, "load",
	      root->query_alias != NULL ? root->query_alias : "", plan->n_items, pr_type_name (DB_TYPE_VARIABLE));
      return ER_QPROC_DOMAIN_UNRESOLVED;
    }
  return NO_ERROR;
}
