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
#include "domain_rules.h"
#include "object_domain_convert.h"
#include "db_date_status.h"
#include "db_function.hpp"
#include "dbtype.h"
#include "memory_alloc.h"
#include "object_primitive.h"
#include "object_representation.h"
#include "chartype.h"
#include "storage_common.h"
#include "system_parameter.h"
#include "language_support.h"
#include "error_manager.h"
#include "string_opfunc.h"
#include <atomic>
#include <cstddef>
#include <mutex>

// XXX: SHOULD BE THE LAST INCLUDE HEADER
#include "memory_wrapper.hpp"

static int domain_character_result (int opcode, const DOMAIN_OPERAND * operands, int n_operands,
				    const TP_DOMAIN * compiled, RESOLVED_DOMAIN * result);
static const TP_DOMAIN *domain_variable_string_value (const TP_DOMAIN * domain);

/* The conversion a context's consumer makes. CAST and operand coercion consumers supply ASSIGN explicitly. */
/*
 * [리뷰] domain_convert_mode — DOMAIN_CTX(어떤 문맥의 노드인가)를 변환 모드(ASSIGN/COMPARE/OPERAND)로 옮긴다 — 로드의
 * domain_plan.c:771 과 게이트의 domain_rules.c:2390 이 tp_value_find_converter 에 넘길 모드를 여기서 얻는다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 에는 변환 모드라는 구분 자체가 없고 tp_value_coerce 계열이 문맥별로 흩어져 불렸다.
 * 이 PR: ASSIGN 문맥이면 ASSIGN, COMPARE·KEY_ELEM 이면 COMPARE, 나머지는 OPERAND.
 * 바뀐 것: 신설 +6줄. 세 모드의 대응표가 이 한 줄로 모였다.
 */
DOMAIN_CONVERT_MODE
domain_convert_mode (DOMAIN_CTX context)
{
  return context == DOMAIN_CTX_ASSIGN ? DOMAIN_CONVERT_ASSIGN
    : context == DOMAIN_CTX_COMPARE || context == DOMAIN_CTX_KEY_ELEM ? DOMAIN_CONVERT_COMPARE : DOMAIN_CONVERT_OPERAND;
}

/*
 * [리뷰] domain_operand_type — 타입 규칙이 피연산자를 볼 때 쓰는 단일 창구 — 값에서 온 타입이 있으면 그것을, 없으면 도메인의 타입을 돌려준다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: val_type 이 DB_TYPE_NULL 이 아니거나 도메인이 없으면 val_type 을 그대로, 그 밖에는 TP_DOMAIN_TYPE(domain) 을 돌려준다.
 * 바뀐 것: 신설 +9줄. 「NULL 이면 도메인으로 물러선다」가 여기 한 곳에만 적혀 있다.
 */
static DB_TYPE
domain_operand_type (const DOMAIN_OPERAND * operand)
{
  if (operand->val_type != DB_TYPE_NULL || operand->domain == NULL)
    {
      return operand->val_type;
    }
  return TP_DOMAIN_TYPE (operand->domain);
}

/* The operand's own domain when it describes its type, otherwise the default domain of that type
 * (a value-dependent argument keeps its value domain while val_type is its type). */
/*
 * [리뷰] domain_operand_domain — 피연산자의 도메인을 고른다 — 가진 도메인의 타입이 실제 타입과 맞으면 그 도메인을, 어긋나면 그 타입의 기본 도메인을 돌려준다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: domain_operand_type 으로 타입을 먼저 정하고, 도메인과 일치할 때만 원래 도메인을 유지한다(정밀도·콜레이션이 보존되는 자리).
 * 바뀐 것: 신설 +10줄.
 */
static const TP_DOMAIN *
domain_operand_domain (const DOMAIN_OPERAND * operand)
{
  DB_TYPE type = domain_operand_type (operand);
  if (operand->domain != NULL && TP_DOMAIN_TYPE (operand->domain) == type)
    {
      return operand->domain;
    }
  return tp_domain_resolve_default (type);
}

/*
 * [리뷰] domain_set_operand — 타입 규칙이 「이 피연산자를 target 타입으로 맞춘다」는 결론을 RESOLVED_DOMAIN 에 적는 자리 — operand_domain[i]
 * 와 conv[i] 한 쌍을 정한다. 행은 이 conv 를 그냥 부르기만 한다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 에서는 이 결정이 행마다 tp_value_coerce / tp_value_compare_with_error 안에서
 * 다시 내려졌다.
 * 이 PR: 이미 target 타입이면 도메인만 적고 conv 를 NULL 로 둬 변환을 건너뛰게 하고, 아니면 target 의 기본 도메인과 tp_value_find_converter 가 고른
 * 변환 함수를 적는다.
 * 바뀐 것: 신설 +13줄. 「변환이 필요 없으면 conv=NULL」이 행 경로의 분기 기준이다.
 */
static void
domain_set_operand (RESOLVED_DOMAIN * result, int i, const DOMAIN_OPERAND * operand, DB_TYPE target,
		    DOMAIN_CONVERT_MODE mode)
{
  if (target == domain_operand_type (operand))
    {
      result->operand_domain[i] = domain_operand_domain (operand);
      result->conv[i] = NULL;
      return;
    }
  result->operand_domain[i] = tp_domain_resolve_default (target);
  result->conv[i] = tp_value_find_converter (domain_operand_type (operand), result->operand_domain[i], mode);
}

/* Result of two numbers after the operand coercion: the typed dispatch of
 * qdata_{add,subtract,multiply,divide}_*_to_dbval. */
/*
 * [리뷰] domain_arith_number — domain_arith_dispatch 가 두 숫자 피연산자를 만났을 때 부르는 표로, 연산자 코드와 좌/우 DB_TYPE 를 받아
 * qdata_{add,subtract,multiply,divide}_*_to_dbval 의 타입별 분기가 내놓을 결과 타입 하나를 돌려준다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 에서는 같은 승격 규칙이 행마다 query_opfunc.c 의
 * qdata_add_int_to_dbval·qdata_add_float_to_dbval 같은 타입별 헬퍼 안에서 값과 함께 결정됐다.
 * 이 PR: MONETARY > DOUBLE > FLOAT > NUMERIC > BIGINT > INTEGER > SHORT 순의 우선순위로 결과 타입을 고르고, FLOAT 와 NUMERIC,
 * 그리고 T_ADD 의 FLOAT+BIGINT(좌가 FLOAT 일 때만) 만 DOUBLE 로 올린다.
 * 바뀐 것: 신규 함수(+36줄). 행-시점 타입 분기를 실행 전 게이트가 쓸 수 있는 순수 타입 함수로 추출.
 */
static DB_TYPE
domain_arith_number (int opcode, DB_TYPE left, DB_TYPE right)
{
  if (left == DB_TYPE_MONETARY || right == DB_TYPE_MONETARY)
    {
      return DB_TYPE_MONETARY;
    }
  if (left == DB_TYPE_DOUBLE || right == DB_TYPE_DOUBLE)
    {
      return DB_TYPE_DOUBLE;
    }
  if (left == DB_TYPE_FLOAT || right == DB_TYPE_FLOAT)
    {
      DB_TYPE other = left == DB_TYPE_FLOAT ? right : left;
      /* FLOAT with NUMERIC goes through qdata_coerce_numeric_to_double; FLOAT + BIGINT (not BIGINT + FLOAT) is
       * qdata_add_double in qdata_add_float_to_dbval. */
      if (other == DB_TYPE_NUMERIC || (opcode == T_ADD && left == DB_TYPE_FLOAT && right == DB_TYPE_BIGINT))
	{
	  return DB_TYPE_DOUBLE;
	}
      return DB_TYPE_FLOAT;
    }
  if (left == DB_TYPE_NUMERIC || right == DB_TYPE_NUMERIC)
    {
      return DB_TYPE_NUMERIC;
    }
  if (left == DB_TYPE_BIGINT || right == DB_TYPE_BIGINT)
    {
      return DB_TYPE_BIGINT;
    }
  if (left == DB_TYPE_INTEGER || right == DB_TYPE_INTEGER)
    {
      return DB_TYPE_INTEGER;
    }
  return DB_TYPE_SHORT;
}

/* db_string_concatenate on two values: character strings give VARCHAR (qstr_make_typed_string;
 * CHAR comes only from the NULL/empty-string path) and bit strings BIT or VARBIT; a character with a bit string is
 * ER_QSTR_INCOMPATIBLE_CODE_SETS and any other operand ER_QSTR_INVALID_DATA_TYPE. */
/*
 * [리뷰] domain_arith_concat — domain_arith_binary/dispatch 가 문자열·비트열 덧셈(plus_as_concat, CONCAT)을 만났을 때 결과 타입과
 * 에러 코드를 정하는 판정부로, 호출자에게 NO_ERROR 와 *result_type, 또는 ER_QSTR_* 를 돌려준다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 에서는 행마다 qdata_strcat_dbval → db_string_concatenate 가 값의 타입을 보고 같은
 * 두 에러를 냈다.
 * 이 PR: 둘 다 문자/비트형이 아니면 ER_QSTR_INVALID_DATA_TYPE, 문자형과 비트형이 섞이면 ER_QSTR_INCOMPATIBLE_CODE_SETS, 문자형이면
 * VARCHAR, 비트형이면 한쪽이 VARBIT 일 때 VARBIT 아니면 BIT 를 돌려준다.
 * 바뀐 것: 신규 함수(+21줄). db_string_concatenate 의 타입 판정만 떼어 실행 전으로 옮김.
 */
static int
domain_arith_concat (DB_TYPE left, DB_TYPE right, DB_TYPE * result_type)
{
  if (!TP_IS_CHAR_BIT_TYPE (left) || !TP_IS_CHAR_BIT_TYPE (right))
    {
      return ER_QSTR_INVALID_DATA_TYPE;
    }
  if (TP_IS_CHAR_TYPE (left) != TP_IS_CHAR_TYPE (right))
    {
      return ER_QSTR_INCOMPATIBLE_CODE_SETS;
    }
  if (TP_IS_CHAR_TYPE (left))
    {
      *result_type = DB_TYPE_VARCHAR;
    }
  else
    {
      *result_type = (left == DB_TYPE_VARBIT || right == DB_TYPE_VARBIT) ? DB_TYPE_VARBIT : DB_TYPE_BIT;
    }
  return NO_ERROR;
}

/* Date/time subtraction after the operand coercion (qdata_subtract_*_to_dbval): one side is a date/time, the other a
 * date/time or a discrete number. */
/*
 * [리뷰] domain_arith_subtract_datetime — domain_arith_dispatch 가 날짜/시간이 끼어든 뺄셈에서 부르는 표로,
 * qdata_subtract_*_to_dbval 의 타입별 결과(차이는 INTEGER/BIGINT, 이동은 원래 날짜형)를 돌려준다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 에서는 qdata_subtract_dbval 의 타입별 헬퍼가 행마다 같은 조합을 판단했다.
 * 이 PR: 좌가 이산 숫자면 우 날짜형별로, 좌가 날짜형이면 우가 숫자/타임스탬프/데이트타임/DATE 인지에 따라 결과 타입을 주고, 헬퍼가 값을 안 남기는 조합(DATETIME - TIME
 * 등)은 DB_TYPE_NULL 을 돌려준다.
 * 바뀐 것: 신규 함수(+50줄). DATETIMELTZ 를 DATETIMETZ 로 빼는 것 같은 develop 의 비대칭까지 그대로 표에 적어둔 형태.
 */
static DB_TYPE
domain_arith_subtract_datetime (DB_TYPE left, DB_TYPE right)
{
  if (TP_IS_DISCRETE_NUMBER_TYPE (left))
    {
      switch (right)
	{
	case DB_TYPE_TIME:
	case DB_TYPE_TIMESTAMP:
	case DB_TYPE_TIMESTAMPLTZ:
	case DB_TYPE_TIMESTAMPTZ:
	  return right;
	case DB_TYPE_DATETIME:
	case DB_TYPE_DATETIMELTZ:
	case DB_TYPE_DATETIMETZ:
	  return left == DB_TYPE_BIGINT ? DB_TYPE_NULL : DB_TYPE_BIGINT;
	case DB_TYPE_DATE:
	  return left == DB_TYPE_SHORT ? DB_TYPE_TIME : DB_TYPE_DATE;
	default:
	  return DB_TYPE_NULL;
	}
    }

  bool right_is_number = TP_IS_DISCRETE_NUMBER_TYPE (right);
  bool right_is_timestamp = right == DB_TYPE_TIMESTAMP || right == DB_TYPE_TIMESTAMPLTZ || right == DB_TYPE_TIMESTAMPTZ;
  bool right_is_datetime = right == DB_TYPE_DATETIME || right == DB_TYPE_DATETIMELTZ || right == DB_TYPE_DATETIMETZ;
  switch (left)
    {
    case DB_TYPE_TIME:
      return right_is_number ? DB_TYPE_TIME : right == DB_TYPE_TIME ? DB_TYPE_INTEGER : DB_TYPE_NULL;
    case DB_TYPE_TIMESTAMP:
    case DB_TYPE_TIMESTAMPLTZ:
    case DB_TYPE_TIMESTAMPTZ:
      return right_is_number ? left : right_is_timestamp ? DB_TYPE_INTEGER : right_is_datetime ? DB_TYPE_BIGINT
	: DB_TYPE_NULL;
    case DB_TYPE_DATETIME:
    case DB_TYPE_DATETIMELTZ:
    case DB_TYPE_DATETIMETZ:
      if (right_is_number)
	{
	  /* DATETIMELTZ is subtracted as DATETIMETZ (qdata_subtract_dbval) */
	  return left == DB_TYPE_DATETIME ? DB_TYPE_DATETIME : DB_TYPE_DATETIMETZ;
	}
      return (right_is_timestamp || right_is_datetime || right == DB_TYPE_DATE) ? DB_TYPE_BIGINT : DB_TYPE_NULL;
    case DB_TYPE_DATE:
      return right_is_number ? DB_TYPE_DATE : right == DB_TYPE_DATE ? DB_TYPE_INTEGER : DB_TYPE_NULL;
    default:
      return DB_TYPE_NULL;
    }
}

/*
 * domain_arith_dispatch - the typed dispatch of qdata_{add,subtract,multiply,divide}_dbval after the operand coercion
 *   return: NO_ERROR, or the error the dispatcher raises for the pair
 *   first, second(in): operand types after the operand coercion and, for addition, the swap
 *   result_type(out): the result type; DB_TYPE_NULL when a typed helper passes the pair over without an error
 *
 * A dispatcher rejects a first operand it has no helper for: addition always, the others unless
 * return_null_on_function_errors; a collection with a non-collection always. A typed helper leaves no value for a
 * second operand it has no case for (DATETIME - TIME), except the date addition, which rejects it like the
 * dispatchers (qdata_add_date_to_dbval).
 */
/*
 * [리뷰] domain_arith_dispatch — 피연산자 강제변환이 끝난 뒤의 타입 쌍을 받아 qdata_{add,subtract,multiply,divide}_dbval 의 디스패처가 그
 * 쌍을 받는지·어떤 타입을 내는지를 결정하고, domain_arith_binary 에 NO_ERROR 또는 디스패처가 낼 에러를 돌려준다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 에서는 query_opfunc.c:2418 qdata_add_dbval 등이 행마다 DB_VALUE 의 타입으로
 * switch 해서 헬퍼를 고르고 거부 여부를 정했다.
 * 이 PR: 숫자+숫자는 domain_arith_number, T_SUB 의 숫자+날짜는 domain_arith_subtract_datetime, 컬렉션 쌍은 SET/MULTISET 규칙,
 * 문자/비트 덧셈은 domain_arith_concat 으로 보내고, 헬퍼가 없는 첫 피연산자는 return_null_on_function_errors 에 따라 NO_ERROR 또는
 * ER_QPROC_INVALID_DATATYPE 로 거부한다.
 * 바뀐 것: 신규 함수(+71줄). 행마다 돌던 디스패처 분기를 실행 전 1회 판정으로 옮긴 핵심 지점.
 */
static int
domain_arith_dispatch (int opcode, DB_TYPE first, DB_TYPE second, DB_TYPE * result_type)
{
  const int reject = prm_get_bool_value (PRM_ID_RETURN_NULL_ON_FUNCTION_ERRORS) ? NO_ERROR : ER_QPROC_INVALID_DATATYPE;

  *result_type = DB_TYPE_NULL;
  if (TP_IS_NUMERIC_TYPE (first))
    {
      if (TP_IS_NUMERIC_TYPE (second))
	{
	  *result_type = domain_arith_number (opcode, first, second);
	}
      else if (opcode == T_SUB && TP_IS_DATE_OR_TIME_TYPE (second))
	{
	  /* the operand coercion made a floating first operand BIGINT */
	  *result_type = domain_arith_subtract_datetime (first, second);
	}
      return NO_ERROR;
    }
  if (TP_IS_SET_TYPE (first) && opcode != T_DIV)
    {
      if (!TP_IS_SET_TYPE (second))
	{
	  return ER_QPROC_INVALID_DATATYPE;
	}
      /* partial resolve of a late-bound collection result (domain_p == NULL) */
      *result_type = (opcode == T_ADD ? first == second : (first == second && first == DB_TYPE_SET))
	? first : DB_TYPE_MULTISET;
      return NO_ERROR;
    }

  switch (opcode)
    {
    case T_ADD:
      if (TP_IS_CHAR_BIT_TYPE (first))
	{
	  return domain_arith_concat (first, second, result_type);
	}
      if (first == DB_TYPE_DATE)
	{
	  if (!TP_IS_DISCRETE_NUMBER_TYPE (second))
	    {
	      return reject;
	    }
	  *result_type = first;
	  return NO_ERROR;
	}
      if (TP_IS_DATE_OR_TIME_TYPE (first))
	{
	  /* TIMESTAMPLTZ and DATETIMETZ with anything but an integer read an unset value: that
	   * answer is not kept, no value like their siblings */
	  if (TP_IS_DISCRETE_NUMBER_TYPE (second))
	    {
	      *result_type = first;
	    }
	  return NO_ERROR;
	}
      return ER_QPROC_INVALID_DATATYPE;

    case T_SUB:
      if (TP_IS_DATE_OR_TIME_TYPE (first))
	{
	  *result_type = domain_arith_subtract_datetime (first, second);
	  return NO_ERROR;
	}
      return reject;

    default:
      return reject;
    }
}

/*
 * domain_arith_binary - the operand coercion and typed dispatch of the four binary operators
 *   return: NO_ERROR, or the error the operator raises for the pair
 *   left, right(in): operand types
 *   left_target, right_target(out): type each operand is cast to
 *   result_type(out): type the operator produces; DB_TYPE_NULL for a NULL operand or a pair it passes over
 */
/*
 * [리뷰] domain_arith_binary — domain_resolve_arith 와 domain_resolve_operand_coercion 이 부르는 이항 산술의 상위 규칙으로, 좌/우
 * 타입에서 각 피연산자의 캐스트 목표 타입과 결과 타입을 한 번에 돌려준다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 의 qdata_add_dbval(query_opfunc.c:2418)은 행마다 ENUM 을
 * VARCHAR/SMALLINT 로 tp_value_auto_cast 한 뒤 자기 자신을 재귀 호출하고, plus_as_concat 검사와 피연산자 스왑을 거쳐 디스패치했다.
 * 이 PR: 같은 순서를 타입만으로 재현한다 — NULL 단락, ENUM 치환 후 재귀, plus_as_concat, 덧셈의 스왑, 문자↔숫자/날짜의 DOUBLE·BIGINT·DATETIME
 * 치환, ORACLE_COMPAT 의 NUMERIC 승격, 마지막에 domain_arith_dispatch.
 * 바뀐 것: 신규 함수(+97줄). develop 의 값 기반 재귀 캐스트를 타입 기반 재귀로 바꾼 것이 성격상 가장 큰 변화.
 */
static int
domain_arith_binary (int opcode, DB_TYPE left, DB_TYPE right, DB_TYPE * left_target, DB_TYPE * right_target,
		     DB_TYPE * result_type)
{
  bool is_add = opcode == T_ADD;

  *left_target = left;
  *right_target = right;
  *result_type = DB_TYPE_NULL;

  if (!is_add && (left == DB_TYPE_NULL || right == DB_TYPE_NULL))
    {
      return NO_ERROR;
    }

  /* ENUM: the name when added to a string, the ordinal otherwise; multiply and divide take no ENUM */
  if ((is_add || opcode == T_SUB) && (left == DB_TYPE_ENUMERATION || right == DB_TYPE_ENUMERATION))
    {
      if (left == DB_TYPE_ENUMERATION)
	{
	  DB_TYPE step = (is_add && TP_IS_CHAR_BIT_TYPE (right)) ? DB_TYPE_VARCHAR : DB_TYPE_SHORT;
	  return domain_arith_binary (opcode, step, right, left_target, right_target, result_type);
	}
      DB_TYPE step = (is_add && TP_IS_CHAR_BIT_TYPE (left)) ? DB_TYPE_VARCHAR : DB_TYPE_SHORT;
      return domain_arith_binary (opcode, left, step, left_target, right_target, result_type);
    }

  if (is_add && prm_get_bool_value (PRM_ID_PLUS_AS_CONCAT) && TP_IS_CHAR_BIT_TYPE (left) && TP_IS_CHAR_BIT_TYPE (right))
    {
      return domain_arith_concat (left, right, result_type);
    }

  if (left == DB_TYPE_NULL || right == DB_TYPE_NULL)
    {
      return NO_ERROR;
    }

  /* addition handles STRING + NUMBER, NUMBER + DATE and STRING + DATE with the operands swapped */
  DB_TYPE *first_target = left_target, *second_target = right_target;
  DB_TYPE first = left, second = right;
  if (is_add && ((TP_IS_CHAR_TYPE (left) && TP_IS_NUMERIC_TYPE (right))
		 || (TP_IS_NUMERIC_TYPE (left) && TP_IS_DATE_OR_TIME_TYPE (right))
		 || (TP_IS_CHAR_TYPE (left) && TP_IS_DATE_OR_TIME_TYPE (right))))
    {
      first = right;
      second = left;
      first_target = right_target;
      second_target = left_target;
    }

  if (TP_IS_NUMERIC_TYPE (first) && TP_IS_CHAR_TYPE (second))
    {
      second = DB_TYPE_DOUBLE;
    }
  else if (!is_add && TP_IS_CHAR_TYPE (first) && TP_IS_NUMERIC_TYPE (second))
    {
      first = DB_TYPE_DOUBLE;
    }
  else if (TP_IS_CHAR_TYPE (first) && TP_IS_CHAR_TYPE (second))
    {
      first = DB_TYPE_DOUBLE;
      second = DB_TYPE_DOUBLE;
    }
  else if (is_add && TP_IS_DATE_OR_TIME_TYPE (first) && (TP_IS_FLOATING_NUMBER_TYPE (second)
							 || TP_IS_CHAR_TYPE (second)))
    {
      second = DB_TYPE_BIGINT;
    }
  else if (opcode == T_SUB && TP_IS_DATE_OR_TIME_TYPE (first) && TP_IS_FLOATING_NUMBER_TYPE (second))
    {
      second = DB_TYPE_BIGINT;
    }
  else if (opcode == T_SUB && TP_IS_FLOATING_NUMBER_TYPE (first) && TP_IS_DATE_OR_TIME_TYPE (second))
    {
      first = DB_TYPE_BIGINT;
    }
  else if (opcode == T_SUB && TP_IS_DATE_OR_TIME_TYPE (first) && TP_IS_CHAR_TYPE (second))
    {
      second = first == DB_TYPE_TIME ? DB_TYPE_TIME : DB_TYPE_DATETIME;
      first = first == DB_TYPE_TIME ? DB_TYPE_TIME : DB_TYPE_DATETIME;
    }
  else if (opcode == T_SUB && TP_IS_CHAR_TYPE (first) && TP_IS_DATE_OR_TIME_TYPE (second))
    {
      first = second == DB_TYPE_TIME ? DB_TYPE_TIME : DB_TYPE_DATETIME;
      second = second == DB_TYPE_TIME ? DB_TYPE_TIME : DB_TYPE_DATETIME;
    }
  else if (opcode == T_DIV && prm_get_bool_value (PRM_ID_ORACLE_COMPAT_NUMBER_BEHAVIOR)
	   && TP_IS_DISCRETE_NUMBER_TYPE (first) && TP_IS_DISCRETE_NUMBER_TYPE (second))
    {
      first = DB_TYPE_NUMERIC;
      second = DB_TYPE_NUMERIC;
    }
  *first_target = first;
  *second_target = second;

  return domain_arith_dispatch (opcode, first, second, result_type);
}

/* The result of the db_mod_<type> helpers for two numbers; a character operand is DOUBLE by then. */
/*
 * [리뷰] domain_arith_mod_number — domain_arith_mod 가 두 숫자 타입을 받았을 때 db_mod_<type> 헬퍼가 내는 결과 타입을 돌려주는 표.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 에서는 db_mod_dbval 이 행마다 값의 타입으로 헬퍼를 골라 결과 타입이 정해졌다.
 * 이 PR: MONETARY·DOUBLE 우선, FLOAT 와 NUMERIC 이 만나면 DOUBLE, 그 외는 FLOAT/NUMERIC/BIGINT/INTEGER/SHORT 순. 덧셈
 * 표(domain_arith_number)와 달리 좌/우 비대칭이 있다.
 * 바뀐 것: 신규 함수(+34줄). MOD 전용 승격 규칙을 덧셈 표와 분리해 따로 둠.
 */
static DB_TYPE
domain_arith_mod_number (DB_TYPE left, DB_TYPE right)
{
  if (left == DB_TYPE_MONETARY || right == DB_TYPE_MONETARY)
    {
      return DB_TYPE_MONETARY;
    }
  if (left == DB_TYPE_DOUBLE || right == DB_TYPE_DOUBLE)
    {
      return DB_TYPE_DOUBLE;
    }
  if (left == DB_TYPE_FLOAT)
    {
      return right == DB_TYPE_NUMERIC ? DB_TYPE_DOUBLE : DB_TYPE_FLOAT;
    }
  if (left == DB_TYPE_NUMERIC)
    {
      return right == DB_TYPE_FLOAT ? DB_TYPE_DOUBLE : DB_TYPE_NUMERIC;
    }
  /* an integer first operand */
  if (right == DB_TYPE_FLOAT || right == DB_TYPE_NUMERIC)
    {
      return right;
    }
  if (left == DB_TYPE_BIGINT || right == DB_TYPE_BIGINT)
    {
      return DB_TYPE_BIGINT;
    }
  if (left == DB_TYPE_INTEGER || right == DB_TYPE_INTEGER)
    {
      return DB_TYPE_INTEGER;
    }
  return DB_TYPE_SHORT;
}

/*
 * domain_arith_mod - db_mod_dbval: a character first operand is taken as DOUBLE (db_mod_string), the typed
 *		      helpers take a number or character second operand as DOUBLE; any other pair is rejected unless
 *		      return_null_on_function_errors
 */
/*
 * [리뷰] domain_arith_mod — domain_resolve_arith 의 T_MOD 분기가 부르며, db_mod_dbval 의 규칙대로 두 피연산자의 캐스트 목표와 결과 타입을
 * 돌려준다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 에서는 db_mod_dbval 과 db_mod_string 이 행마다 문자열을 DOUBLE 로 읽고 거부 여부를
 * 판단했다.
 * 이 PR: 문자형 피연산자를 DOUBLE 목표로 바꾸고, NULL 이면 목표를 원래 타입으로 되돌린 채 결과 NULL, 숫자가 아니면 return_null_on_function_errors 에
 * 따라 NO_ERROR 또는 ER_QPROC_INVALID_DATATYPE.
 * 바뀐 것: 신규 함수(+22줄). 거부 경로에서 목표 타입을 원래대로 되돌리는 처리를 명시적으로 둠.
 */
static int
domain_arith_mod (DB_TYPE left, DB_TYPE right, DB_TYPE * left_target, DB_TYPE * right_target, DB_TYPE * result_type)
{
  *left_target = TP_IS_CHAR_TYPE (left) ? DB_TYPE_DOUBLE : left;
  *right_target = TP_IS_CHAR_TYPE (right) ? DB_TYPE_DOUBLE : right;
  *result_type = DB_TYPE_NULL;

  if (left == DB_TYPE_NULL || right == DB_TYPE_NULL)
    {
      *left_target = left;
      *right_target = right;
      return NO_ERROR;
    }
  if (!TP_IS_NUMERIC_TYPE (*left_target) || !TP_IS_NUMERIC_TYPE (*right_target))
    {
      *left_target = left;
      *right_target = right;
      return prm_get_bool_value (PRM_ID_RETURN_NULL_ON_FUNCTION_ERRORS) ? NO_ERROR : ER_QPROC_INVALID_DATATYPE;
    }
  *result_type = domain_arith_mod_number (*left_target, *right_target);
  return NO_ERROR;
}

/* The operands' operand coercion of a binary arithmetic operator */
/*
 * [리뷰] domain_set_arith_operands — domain_resolve_arith·domain_resolve_operand_coercion 이 목표 타입을 정한 뒤 부르며,
 * RESOLVED_DOMAIN 의 operand_domain[0..1] 과 conv[0..1] 에 ASSIGN 모드 변환기를 채운다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 에서는 행마다 tp_value_auto_cast 가 값과 목표 도메인을 받아 변환기를 그때그때 찾았다.
 * 이 PR: domain_set_operand 으로 양쪽 변환기를 ASSIGN 모드로 미리 고정하고, plus_as_concat 없이 ENUM 이 문자열과 더해져 DOUBLE 로 가는 경우만
 * domain_enumeration_name_converter() 로 바꿔 끼운다.
 * 바뀐 것: 신규 함수(+17줄). 변환기 탐색을 행-시점에서 게이트 시점으로 옮기는 접합부.
 */
static void
domain_set_arith_operands (int opcode, const DOMAIN_OPERAND * operands, DB_TYPE left_target, DB_TYPE right_target,
			   RESOLVED_DOMAIN * result)
{
  /* the operand coercion is tp_value_auto_cast, ASSIGN (ROUND) */
  domain_set_operand (result, 0, &operands[0], left_target, DOMAIN_CONVERT_ASSIGN);
  domain_set_operand (result, 1, &operands[1], right_target, DOMAIN_CONVERT_ASSIGN);
  /* an ENUM added to a string without plus_as_concat reaches DOUBLE through its name, not its ordinal */
  for (int i = 0; i < 2 && opcode == T_ADD; i++)
    {
      if (domain_operand_type (&operands[i]) == DB_TYPE_ENUMERATION
	  && TP_DOMAIN_TYPE (result->operand_domain[i]) == DB_TYPE_DOUBLE)
	{
	  result->conv[i] = domain_enumeration_name_converter ();
	}
    }
}

/*
 * [리뷰] domain_resolve_arith — domain_resolve 의 DOMAIN_CTX_ARITH 분기 본체로, 이항
 * 4연산·MOD·단항(UNMINUS/ABS/FLOOR/CEIL/ROUND/TRUNC)의 결과 도메인과 피연산자 변환기를 RESOLVED_DOMAIN 에 채운다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 에서는 이 규칙들이 qdata_*_dbval 과 단항 연산자 구현 안에 흩어져 행마다 적용됐다.
 * 이 PR: opcode 로 분기해 domain_arith_mod/domain_arith_binary 로 목표·결과를 받고, 단항은 값 위치(ROUND/TRUNC 는 0번, 나머지는 마지막)를
 * 골라 숫자/DATE/DOUBLE 로 목표를 정한다. T_ADD 가 문자 결과면 domain_character_result(T_CONCAT) 로 콜레이션 병합까지 넘기고, 모르는 연산자는
 * ER_QPROC_DOMAIN_UNRESOLVED 로 추측을 거부한다.
 * 바뀐 것: 신규 함수(+86줄). "모르면 추측하지 않고 UNRESOLVED" 라는 게이트 계약이 처음 드러나는 자리.
 */
static int
domain_resolve_arith (int opcode, const DOMAIN_OPERAND * operands, int n_operands, RESOLVED_DOMAIN * result)
{
  DB_TYPE result_type;

  switch (opcode)
    {
    case T_ADD:
    case T_SUB:
    case T_MUL:
    case T_DIV:
    case T_MOD:
      {
	DB_TYPE left_target, right_target;
	const DB_TYPE left = domain_operand_type (&operands[0]), right = domain_operand_type (&operands[1]);
	assert (n_operands == 2);
	int error = opcode == T_MOD ? domain_arith_mod (left, right, &left_target, &right_target, &result_type)
	  : domain_arith_binary (opcode, left, right, &left_target, &right_target, &result_type);
	if (error != NO_ERROR)
	  {
	    return error;
	  }
	domain_set_arith_operands (opcode, operands, left_target, right_target, result);
	break;
      }

    case T_UNMINUS:
    case T_ABS:
    case T_FLOOR:
    case T_CEIL:
    case T_ROUND:
    case T_TRUNC:
      {
	/* the value is the right operand of the unary operators and the left one of ROUND/TRUNC */
	int arg = (opcode == T_ROUND || opcode == T_TRUNC) ? 0 : n_operands - 1;
	DB_TYPE type = domain_operand_type (&operands[arg]);
	DB_TYPE target;
	if (type == DB_TYPE_NULL || TP_IS_NUMERIC_TYPE (type))
	  {
	    result_type = target = type;
	  }
	else if ((opcode == T_ROUND || opcode == T_TRUNC) && TP_IS_DATE_TYPE (type))
	  {
	    result_type = DB_TYPE_DATE;
	    target = type;
	  }
	else if (TP_IS_CHAR_TYPE (type) || opcode == T_ROUND || opcode == T_TRUNC)
	  {
	    /* tp_value_str_auto_cast_to_number, or ROUND/TRUNC try DOUBLE for anything else */
	    result_type = target = DB_TYPE_DOUBLE;
	  }
	else if (prm_get_bool_value (PRM_ID_RETURN_NULL_ON_FUNCTION_ERRORS))
	  {
	    result_type = DB_TYPE_NULL;
	    target = type;
	  }
	else
	  {
	    return ER_QPROC_INVALID_DATATYPE;
	  }
	domain_set_operand (result, arg, &operands[arg], target, DOMAIN_CONVERT_ASSIGN);
	for (int i = 0; i < n_operands && i < 3; i++)
	  {
	    if (i != arg)
	      {
		domain_set_operand (result, i, &operands[i], domain_operand_type (&operands[i]), DOMAIN_CONVERT_ASSIGN);
	      }
	  }
	break;
      }

    default:
      /* an operator the type rules do not know: resolve_domains must not guess */
      return ER_QPROC_DOMAIN_UNRESOLVED;
    }

  if (opcode == T_ADD && TP_IS_CHAR_TYPE (result_type))
    {
      /* plus as concatenation (qdata_strcat_dbval, db_string_concatenate): the operands' collations merge
       * and their precisions add, as CONCAT's do */
      return domain_character_result (T_CONCAT, operands, n_operands, NULL, result);
    }
  /* NUMERIC results stay floating: the value operation resolves p/s */
  result->domain = tp_domain_resolve_default (result_type);
  return NO_ERROR;
}

/*
 * domain_resolve_operand_coercion () - the operands' operand coercion of an addition, subtraction, multiplication or
 *   division: the targets and converters of domain_resolve's ARITH rule, without its result. qdata_*_dbval cast its
 *   operands before its typed dispatch took or rejected the pair and before plus as concatenation merged their
 *   collations, so the operand coercion stands whatever the result.
 */
/*
 * [리뷰] domain_resolve_operand_coercion — 집계 SUM/AVG 초기화(qdata_initialize_analytic_func,
 * qexec_setup_aggregate_accumulators), orderby_num 상한, qdata_coerce_arith_operands 가 부르는 공개 진입점으로, 4연산의 결과는 빼고
 * 피연산자 쪽 목표 도메인과 변환기만 돌려준다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 에서는 각 호출부가 행마다 qdata_*_dbval 안의 캐스트에 의존했다.
 * 이 PR: domain_arith_binary 의 결과값(에러 포함)은 버리고 목표 타입만 취해 domain_set_arith_operands 로 conv/operand_domain 두 쌍을
 * 채운다 — 디스패처가 쌍을 거부하든 말든 피연산자 캐스트는 같다는 근거를 주석으로 적어 둠.
 * 바뀐 것: 신규 공개 함수(+16줄). 에러 반환 없이 void 로 계약을 좁힌 것이 특징.
 */
void
domain_resolve_operand_coercion (int opcode, const DOMAIN_OPERAND * operands, DOMAIN_OPERAND_COERCION * result)
{
  assert (opcode == T_ADD || opcode == T_SUB || opcode == T_MUL || opcode == T_DIV);
  DB_TYPE left_target, right_target, result_type;
  RESOLVED_DOMAIN resolved = RESOLVED_DOMAIN ();
  /* the targets are set before the typed dispatch answers whether it takes the pair */
  (void) domain_arith_binary (opcode, domain_operand_type (&operands[0]), domain_operand_type (&operands[1]),
			      &left_target, &right_target, &result_type);
  domain_set_arith_operands (opcode, operands, left_target, right_target, &resolved);
  for (int i = 0; i < 2; i++)
    {
      result->conv[i] = resolved.conv[i];
      result->operand_domain[i] = resolved.operand_domain[i];
    }
}

/* The cached domain tp_domain_resolve (type, NULL, precision, 0, NULL, collation_id) gives a string (the collation's
 * codeset) or a bit string, found without the transient domain tp_domain_resolve makes and frees; a domain not
 * cached yet, and one of another type, are tp_domain_resolve's. */
/*
 * [리뷰] domain_character_domain — 이 파일의 문자/비트 결과 도메인을 만드는 공통 바닥으로, (타입, 정밀도, 콜레이션)에 해당하는 캐시된 TP_DOMAIN 을 임시 도메인
 * 생성 없이 찾아 돌려준다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 은 같은 자리에서 tp_domain_resolve 를 불러 임시 도메인을 만들고 캐시 조회 후 해제하는 비용을 행마다
 * 치렀다.
 * 이 PR: tp_domain_find_charbit 로 캐시를 먼저 보고, CHAR 의 codeset 불일치를 직접 걸러낸 뒤 못 찾으면 tp_domain_resolve 로 넘어간다. 디버그
 * 빌드에서는 두 경로가 같은 도메인을 주는지 assert 로 교차 검증한다.
 * 바뀐 것: 신규 함수(+29줄). 캐시 조회 경로를 추가하고 NDEBUG 아닌 빌드에 교차검증 assert 를 둔 형태.
 */
static const TP_DOMAIN *
domain_character_domain (DB_TYPE type, int precision, int collation_id)
{
  const TP_DOMAIN *domain = NULL;
  if (TP_IS_CHAR_TYPE (type))
    {
      const int codeset = lang_get_collation (collation_id)->codeset;
      domain = tp_domain_find_charbit (type, codeset, collation_id, TP_DOMAIN_COLL_NORMAL, precision, false);
      if (domain != NULL && domain->codeset != codeset)
	{
	  /* the cache matches a string's codeset as well, which tp_domain_find_charbit leaves out for a CHAR */
	  domain = NULL;
	}
    }
  else if (TP_IS_BIT_TYPE (type))
    {
      /* a bit string's domain has no collation: the cache matches its precision alone */
      domain = tp_domain_find_charbit (type, INTL_CODESET_RAW_BITS, 0, TP_DOMAIN_COLL_NORMAL, precision, false);
    }
  if (domain == NULL)
    {
      return tp_domain_resolve (type, NULL, precision, 0, NULL, collation_id);
    }
#if !defined (NDEBUG)
  /* debug cross-check (optdebug): tp_domain_resolve finds the same cached domain */
  assert (domain == tp_domain_resolve (type, NULL, precision, 0, NULL, collation_id));
#endif
  return domain;
}

/*
 * [리뷰] domain_char_with_collation — 비교 해석(domain_compute_comparison, domain_compare_target)이 "상대 타입에 내 콜레이션을
 * 얹은 도메인" 을 필요로 할 때 부르며, 기본 정밀도의 문자 도메인을 돌려준다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 의 tp_value_compare_with_error 는 행마다 임시 도메인을 꾸며 강제변환했다.
 * 이 PR: codeset 이 콜레이션의 codeset 과 같으면 domain_character_domain 으로 캐시에서 찾고, 다르면 기본 도메인을 복사해 codeset·collation_id
 * 를 박고 tp_domain_cache 로 등록한다.
 * 바뀐 것: 신규 함수(+17줄). 캐시 미스 시 복사+캐시 등록 경로를 명시.
 */
static const TP_DOMAIN *
domain_char_with_collation (DB_TYPE type, int codeset, int collation_id)
{
  if (codeset == lang_get_collation (collation_id)->codeset)
    {
      /* the default domain's precision under the collation, as tp_domain_resolve caches it */
      return domain_character_domain (type, tp_domain_resolve_default (type)->precision, collation_id);
    }
  TP_DOMAIN *domain = tp_domain_copy (tp_domain_resolve_default (type), false);
  if (domain == NULL)
    {
      return NULL;
    }
  domain->codeset = codeset;
  domain->collation_id = collation_id;
  return tp_domain_cache (domain);
}

/* The coerced side's target of tp_value_compare_with_error: the default domain of the other side's type, carrying
 * the collation of the coerced side when a character or ENUM becomes a character string. */
/*
 * [리뷰] domain_compare_target — domain_resolve_compare 가 한쪽을 상대 타입으로 강제변환할 때 그 목표 도메인을 정해 주며, 문자/ENUM 이 문자열로 갈
 * 때 자기 콜레이션을 유지시킨다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 에서는 tp_value_compare_with_error 가 행마다 같은 판단을 값에서 했다.
 * 이 PR: 강제변환되는 쪽이 콜레이션을 가진 타입이고 목표가 문자형이면 coll_id(또는 원 도메인의 collation_id)를 얹은 domain_char_with_collation 을,
 * 아니면 목표 타입의 기본 도메인을 돌려준다.
 * 바뀐 것: 신규 함수(+12줄). COLLATE 수정자(coll_id)를 도메인보다 우선 읽는 규칙이 새로 명시됨.
 */
static const TP_DOMAIN *
domain_compare_target (const DOMAIN_OPERAND * coerced, DB_TYPE target_type)
{
  DB_TYPE coerced_type = domain_operand_type (coerced);
  if (TP_TYPE_HAS_COLLATION (coerced_type) && TP_IS_CHAR_TYPE (target_type))
    {
      const TP_DOMAIN *source = domain_operand_domain (coerced);
      int collation_id = coerced->coll_id >= 0 ? coerced->coll_id : source->collation_id;
      return domain_char_with_collation (target_type, source->codeset, collation_id);
    }
  return tp_domain_resolve_default (target_type);
}

/*
 * [리뷰] domain_resolve_compare — domain_resolve 의 DOMAIN_CTX_COMPARE 분기로, 두 피연산자를 비교할 때 어느 쪽이 무엇으로
 * 변환되는지(operand_domain·conv)와 비교 도메인(result->domain)을 채운다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 에서는 tp_value_compare_with_error 가 행마다
 * tp_value_compare_common_domain 을 호출해 같은 방향을 정했다.
 * 이 PR: 타입이 다르고 둘 다 NULL 이 아닐 때만 tp_value_compare_common_domain 의 6가지 방향으로 목표를 정하고, 목표가 원 도메인과 다를 때만 ASSIGN
 * 변환기를 찾는다. 도메인 캐시 실패는 ER_OUT_OF_VIRTUAL_MEMORY.
 * 바뀐 것: 신규 함수(+47줄). 행-시점 공통 도메인 계산을 1회 해석으로 옮김.
 */
static int
domain_resolve_compare (const DOMAIN_OPERAND * operands, RESOLVED_DOMAIN * result)
{
  DB_TYPE type1 = domain_operand_type (&operands[0]);
  DB_TYPE type2 = domain_operand_type (&operands[1]);
  const TP_DOMAIN *target1 = domain_operand_domain (&operands[0]);
  const TP_DOMAIN *target2 = domain_operand_domain (&operands[1]);

  if (type1 != DB_TYPE_NULL && type2 != DB_TYPE_NULL && type1 != type2)
    {
      switch (tp_value_compare_common_domain (type1, type2))
	{
	case TP_COMPARE_COERCE_NONE:
	  break;
	case TP_COMPARE_COERCE_TO_DOUBLE:
	  target1 = target2 = tp_domain_resolve_default (DB_TYPE_DOUBLE);
	  break;
	case TP_COMPARE_COERCE_FIRST_TO_DATE:
	  target1 = tp_domain_resolve_default (type2);
	  break;
	case TP_COMPARE_COERCE_SECOND_TO_DATE:
	  target2 = tp_domain_resolve_default (type1);
	  break;
	case TP_COMPARE_COERCE_SECOND_TO_FIRST:
	  target2 = domain_compare_target (&operands[1], type1);
	  break;
	case TP_COMPARE_COERCE_FIRST_TO_SECOND:
	  target1 = domain_compare_target (&operands[0], type2);
	  break;
	}
      if (target1 == NULL || target2 == NULL)
	{
	  return ER_OUT_OF_VIRTUAL_MEMORY;
	}
    }

  /* the resolved comparison converters are ASSIGN converters (tp_value_coerce's on the pairs a comparison reaches) */
  const TP_DOMAIN *targets[2] = { target1, target2 };
  for (int i = 0; i < 2; i++)
    {
      result->operand_domain[i] = targets[i];
      result->conv[i] = targets[i] == domain_operand_domain (&operands[i]) ? NULL
	: tp_value_find_converter (domain_operand_type (&operands[i]), targets[i], DOMAIN_CONVERT_ASSIGN);
    }
  result->domain = target1 != domain_operand_domain (&operands[0]) ? target1 : target2;
  return NO_ERROR;
}

/* tp_infer_common_domain folded left to right: NVL/NVL2/IFNULL/COALESCE/NULLIF/LEAST/GREATEST. */
/*
 * [리뷰] domain_resolve_common_value — domain_resolve 의 DOMAIN_CTX_COMMON_VALUE 분기로,
 * NVL/IFNULL/COALESCE/NULLIF/LEAST/GREATEST 처럼 여러 값을 한 도메인으로 모으는 연산의 공통 도메인과 각 피연산자 변환기를 채운다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 에서는 tp_infer_common_domain 이 행마다 값 도메인 위에서 좌→우로 접혔다.
 * 이 PR: tp_infer_common_domain 을 왼쪽부터 접어 공통 도메인을 얻고, 모든 피연산자에 OPERAND 모드 변환기를 걸며, 결과 도메인은
 * domain_variable_string_value 로 가변 문자열의 부동 정밀도를 최대 정밀도로 읽는다.
 * 바뀐 것: 신규 함수(+21줄). 접기 순서(좌→우)와 "부동 정밀도는 최대로 읽는다" 규칙이 코드로 고정됨.
 */
static int
domain_resolve_common_value (const DOMAIN_OPERAND * operands, int n_operands, RESOLVED_DOMAIN * result)
{
  TP_DOMAIN *common = (TP_DOMAIN *) domain_operand_domain (&operands[0]);
  for (int i = 1; i < n_operands && common != NULL; i++)
    {
      common = tp_infer_common_domain (common, (TP_DOMAIN *) domain_operand_domain (&operands[i]));
    }
  if (common == NULL)
    {
      return ER_OUT_OF_VIRTUAL_MEMORY;
    }
  for (int i = 0; i < n_operands && i < 3; i++)
    {
      result->operand_domain[i] = common;
      result->conv[i] = tp_value_find_converter (domain_operand_type (&operands[i]), common, DOMAIN_CONVERT_OPERAND);
    }
  /* the value cast to the common domain reads as a floating string's maximum precision */
  result->domain = domain_variable_string_value (common);
  return NO_ERROR;
}

/*
 * [리뷰] domain_is_interpolation_type — MEDIAN/PERCENTILE 계열이 그대로 받을 수 있는 타입인지(숫자 또는 날짜/시간)를 한 줄로 답하는 술어로,
 * domain_resolve_aggregate·domain_resolve_analytic·domain_classify_interpolation 이 공유한다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 에서는 같은 조건이 집계·분석 각각의 코드에 중복돼 있었다.
 * 이 PR: TP_IS_NUMERIC_TYPE || TP_IS_DATE_OR_TIME_TYPE 하나로 세 호출부가 같은 판정을 쓴다.
 * 바뀐 것: 신규 함수(+5줄). 중복 조건식의 단일화.
 */
static bool
domain_is_interpolation_type (DB_TYPE type)
{
  return TP_IS_NUMERIC_TYPE (type) || TP_IS_DATE_OR_TIME_TYPE (type);
}

/*
 * domain_interpolation_final () - the domain MEDIAN / PERCENTILE_CONT / PERCENTILE_DISC takes from its first value
 *   (qdata_update_agg_interpolation_func_value_and_domain; the analytic first-execution block)
 *   return: the final domain, or NULL when only a value could tell (a string nobody typed)
 *   domain(in): the domain the function holds before that value (never VARIABLE here)
 *   argument_type(in): the type resolve_domains gave a string value (DOUBLE, DATETIME or TIME), DB_TYPE_NULL otherwise
 *
 * A date or time stays; a DOUBLE (MEDIAN, PERCENTILE_CONT) or any number (PERCENTILE_DISC) stays; any other number
 * becomes DOUBLE, and a string becomes the first of DOUBLE, DATETIME, TIME it casts to.
 */
/*
 * [리뷰] domain_interpolation_final — MEDIAN/PERCENTILE_CONT/PERCENTILE_DISC 가 첫 값을 보고 확정하던 최종 도메인을, 집계·분석 양쪽
 * 해석기가 실행 전에 부르는 공통 규칙으로 돌려준다(값으로만 알 수 있으면 NULL).
 * develop: develop 에 없음 — 이 PR 이 신설. develop 에서는 qdata_update_agg_interpolation_func_value_and_domain 과 분석함수 첫
 * 실행 블록이 각자 같은 확정을 행에서 했다.
 * 이 PR: 날짜/시간은 유지, PERCENTILE_DISC 는 모든 숫자 유지(그 외는 DOUBLE 만 유지), 나머지 숫자는 DOUBLE, 문자열은 resolve_domains 가 준
 * DOUBLE/DATETIME/TIME 을 취한다.
 * 바뀐 것: 신규 함수(+19줄). 두 군데 흩어진 첫-값 확정 규칙을 한 함수로 합침.
 */
static const TP_DOMAIN *
domain_interpolation_final (int function, const TP_DOMAIN * domain, DB_TYPE argument_type)
{
  const DB_TYPE type = TP_DOMAIN_TYPE (domain);
  if (TP_IS_DATE_OR_TIME_TYPE (type)
      || (function == PT_PERCENTILE_DISC ? TP_IS_NUMERIC_TYPE (type) : type == DB_TYPE_DOUBLE))
    {
      return domain;
    }
  if (TP_IS_NUMERIC_TYPE (type))
    {
      return tp_domain_resolve_default (DB_TYPE_DOUBLE);
    }
  if (argument_type == DB_TYPE_DOUBLE || argument_type == DB_TYPE_DATETIME || argument_type == DB_TYPE_TIME)
    {
      return tp_domain_resolve_default (argument_type);
    }
  return NULL;
}

/* Whether an aggregate's or an analytic function's domain is late-bound, typed by its argument's value: the operand
 * was VARIABLE when compiled (opr_dbtype, not the function's domain) or the function domain leaves collation. */
/*
 * [리뷰] domain_function_is_late_bound — 집계·분석 함수의 도메인을 컴파일 시점 도메인으로 확정할 수 없는지(인자가 VARIABLE 위치거나 함수 도메인이 콜레이션을
 * 남겼는지)를 판정해, 두 해석기가 늦은 바인딩 경로로 갈지 결정한다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 에는 이 판정 자체가 없고 행에서 값 도메인을 보고 처리했다.
 * 이 PR: operand->is_variable_pos, compiled == NULL, 또는 TP_DOMAIN_COLLATION_FLAG(compiled) != NORMAL 중 하나면
 * late-bound 로 본다 — 컴파일이 표시한 GATE 슬롯을 읽는 자리.
 * 바뀐 것: 신규 함수(+5줄). 컴파일 표시(VARIABLE/COLL 플래그)를 해석 경로 선택으로 번역하는 지점.
 */
static bool
domain_function_is_late_bound (const TP_DOMAIN * compiled, const DOMAIN_OPERAND * operand)
{
  return operand->is_variable_pos || compiled == NULL || TP_DOMAIN_COLLATION_FLAG (compiled) != TP_DOMAIN_COLL_NORMAL;
}

/*
 * domain_resolve_aggregate - an aggregate's function and accumulator domains, as its argument's value types them
 *   compiled(in): consumer = the aggregate's compiled domain (agg_p->domain, set by xasl_generation.c)
 *   operand(in): the argument; domain = its compiled domain (opr_dbtype), or its value domain when resolve_domains
 *		  resolves it (is_variable_pos: opr_dbtype is VARIABLE); val_type = value type, typed by its value at
 *		  resolve_domains
 *   result(out): domain = the function domain (agg_p->domain after the row-time resolve, which the result is cast
 *		  to); operand_domain[0] / conv[0] = the accumulator domain (value_dom) the argument values are coerced
 *		  to. value2_dom is a per-function constant the load puts in domain_plan_acc.
 */
/*
 * [리뷰] domain_resolve_aggregate — domain_resolve 의 DOMAIN_CTX_AGG 분기로, 집계 함수의 결과 도메인(agg_p->domain)과 누산기
 * 도메인(value_dom)·인자 변환기를 실행 전에 확정한다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 에서는 qdata_initialize_aggregate_list 와 각 집계 갱신 함수가 첫 값을 보고 행-시점에
 * 도메인을 정했다.
 * 이 PR: COUNT/JSON_* 는 고정 시그니처로 즉시 반환하고, late-bound 면 SUM/AVG 의 문자열→DOUBLE, GROUP_CONCAT 의 비문자열→VARCHAR 를 먼저
 * 적용한 뒤 함수별로 누산기를 고른다(NUMERIC 기본 정밀도, FLOAT→DOUBLE, STDDEV/VARIANCE 는 DOUBLE, MEDIAN/PERCENTILE 는
 * domain_interpolation_final). 타입이 안 되면 ER_ARG_CAN_NOT_BE_CASTED_TO_DESIRED_DOMAIN 을 실행 전에 낸다.
 * 바뀐 것: 신규 함수(+149줄). 이 배정 묶음에서 두 번째로 큰 함수이며, 첫-행 도메인 확정을 게이트로 끌어올린 핵심.
 */
static int
domain_resolve_aggregate (int function, const TP_DOMAIN * compiled, const DOMAIN_OPERAND * operand,
			  RESOLVED_DOMAIN * result)
{
  DB_TYPE val_type = domain_operand_type (operand);
  const TP_DOMAIN *function_domain = compiled;
  DB_TYPE operand_type = operand->domain != NULL ? TP_DOMAIN_TYPE (operand->domain) : val_type;
  const TP_DOMAIN *accumulator = NULL;

  if (function == PT_COUNT || function == PT_COUNT_STAR || function == PT_JSON_ARRAYAGG
      || function == PT_JSON_OBJECTAGG)
    {
      /* fixed signatures; the argument is counted or wrapped as it is */
      if (function_domain == NULL)
	{
	  function_domain = (function == PT_COUNT || function == PT_COUNT_STAR) ? &tp_Bigint_domain : &tp_Json_domain;
	}
      result->domain = function_domain;
      result->operand_domain[0] = domain_operand_domain (operand);
      result->conv[0] = NULL;
      return NO_ERROR;
    }

  if (domain_function_is_late_bound (compiled, operand))
    {
      if (TP_IS_CHAR_TYPE (val_type) && (function == PT_SUM || function == PT_AVG))
	{
	  function_domain = tp_domain_resolve_default (DB_TYPE_DOUBLE);
	}
      else if (!TP_IS_CHAR_TYPE (val_type) && function == PT_GROUP_CONCAT)
	{
	  function_domain = tp_domain_resolve_default (DB_TYPE_VARCHAR);
	}
      else
	{
	  function_domain = domain_operand_domain (operand);
	}
      operand_type = TP_DOMAIN_TYPE (function_domain);
    }

  switch (function)
    {
    case PT_AVG:
    case PT_SUM:
      if (!TP_IS_NUMERIC_TYPE (val_type))
	{
	  accumulator = function_domain;
	}
      else if (TP_DOMAIN_TYPE (function_domain) == DB_TYPE_NUMERIC || val_type == DB_TYPE_NUMERIC)
	{
	  accumulator = tp_domain_resolve (DB_TYPE_NUMERIC, NULL, DB_DEFAULT_NUMERIC_PRECISION,
					   DB_DEFAULT_NUMERIC_SCALE, NULL, 0);
	}
      else if (val_type == DB_TYPE_FLOAT)
	{
	  accumulator = tp_domain_resolve (DB_TYPE_DOUBLE, NULL, DB_DOUBLE_DECIMAL_PRECISION, 0, NULL, 0);
	}
      else
	{
	  accumulator = tp_domain_resolve_default (val_type);
	}
      break;

    case PT_STDDEV:
    case PT_STDDEV_POP:
    case PT_STDDEV_SAMP:
    case PT_VARIANCE:
    case PT_VAR_POP:
    case PT_VAR_SAMP:
      accumulator = &tp_Double_domain;
      break;

    case PT_GROUPBY_NUM:
      accumulator = &tp_Null_domain;
      break;

    case PT_MEDIAN:
    case PT_PERCENTILE_CONT:
    case PT_PERCENTILE_DISC:
      /* keyed on the operand type (opr_dbtype), as the operator does; a number or date operand leaves value_dom unset,
       * so the accumulator here is the function domain */
      if (operand->val_type == DB_TYPE_NULL && operand->domain != NULL
	  && TP_IS_CHAR_TYPE (TP_DOMAIN_TYPE (operand->domain)))
	{
	  /* a string value none of DOUBLE, DATETIME, TIME takes (resolve_domains could not type it): no domain;
	   * the first value would raise the error; resolve_domains raises it */
	  return ER_ARG_CAN_NOT_BE_CASTED_TO_DESIRED_DOMAIN;
	}
      if (!domain_is_interpolation_type (operand_type))
	{
	  if (domain_is_interpolation_type (val_type))
	    {
	      /* resolve_domains typed the value as DOUBLE, DATETIME or TIME */
	      function_domain = tp_domain_resolve_default (val_type);
	    }
	  else if (TP_IS_CHAR_TYPE (val_type))
	    {
	      /* a string resolve_domains has no value for (a column, an expression) is a number */
	      function_domain = &tp_Double_domain;
	    }
	  else
	    {
	      return ER_ARG_CAN_NOT_BE_CASTED_TO_DESIRED_DOMAIN;
	    }
	}
      else if (function_domain == NULL || TP_DOMAIN_TYPE (function_domain) == DB_TYPE_VARIABLE)
	{
	  /* the compiler leaves the function's domain variable for a number or date argument (func_type.cpp) and
	   * the first value gives it the default domain of its type */
	  function_domain = tp_domain_resolve_default (operand_type);
	}
      /* then the value takes the function's final type: resolve_domains records that domain */
      {
	const TP_DOMAIN *final_domain = domain_interpolation_final (function, function_domain, val_type);
	if (final_domain != NULL)
	  {
	    function_domain = final_domain;
	  }
      }
      accumulator = function_domain;
      break;

    default:
      /* BIT_AND/OR/XOR, MIN, MAX, GROUP_CONCAT and the rest accumulate in the function domain */
      accumulator = function_domain;
      break;
    }

  if (accumulator == NULL || function_domain == NULL)
    {
      return ER_OUT_OF_VIRTUAL_MEMORY;
    }
  result->domain = function_domain;
  result->operand_domain[0] = accumulator;
  /* a value-dependent argument converts from its own type to its argument type (tp_value_cast), and so
   * does a string interpolation argument typed DOUBLE */
  if (operand->domain != NULL && val_type != DB_TYPE_NULL
      && (TP_DOMAIN_TYPE (operand->domain) != val_type
	  || (TP_IS_CHAR_TYPE (val_type) && TP_DOMAIN_TYPE (accumulator) == DB_TYPE_DOUBLE
	      && (function == PT_MEDIAN || function == PT_PERCENTILE_CONT || function == PT_PERCENTILE_DISC))))
    {
      result->conv[0] = tp_value_find_converter (TP_DOMAIN_TYPE (operand->domain), accumulator, DOMAIN_CONVERT_ASSIGN);
    }
  else
    {
      result->conv[0] = tp_value_find_converter (val_type, accumulator, DOMAIN_CONVERT_OPERAND);
    }
  return NO_ERROR;
}

/* Late-bound analytic function domain: its own rules, not the aggregate ones. Same inputs as the
 * aggregate; domain = operand_domain[0] = the function domain the operand value is coerced to. */
/*
 * [리뷰] domain_resolve_analytic — domain_resolve 의 DOMAIN_CTX_ANALYTIC 분기로, 분석 함수(윈도 함수)의 도메인과 인자 변환기를 집계와는 다른
 * 자체 규칙으로 확정한다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 에서는 qdata_initialize_analytic_func 가 첫 실행에서 같은 선택을 했다.
 * 이 PR: late-bound 일 때 COUNT→BIGINT, AVG/STDDEV/VARIANCE 류→DOUBLE, SUM 은 숫자면 피연산자 도메인·아니면 DOUBLE 로 잡고,
 * MEDIAN/PERCENTILE 는 시작 도메인에서 domain_interpolation_final 로 확정하며 캐스트 불가 값은
 * ER_ARG_CAN_NOT_BE_CASTED_TO_DESIRED_DOMAIN 으로 미리 실패시킨다. 결과 도메인과 누산 도메인이 같다.
 * 바뀐 것: 신규 함수(+69줄). 집계 규칙과 분석 규칙을 의도적으로 분리해 둔 점이 성격.
 */
static int
domain_resolve_analytic (int function, const TP_DOMAIN * compiled, const DOMAIN_OPERAND * operand,
			 RESOLVED_DOMAIN * result)
{
  DB_TYPE val_type = domain_operand_type (operand);
  const TP_DOMAIN *argument = compiled;

  if (domain_function_is_late_bound (compiled, operand))
    {
      switch (function)
	{
	case PT_COUNT:
	case PT_COUNT_STAR:
	  argument = tp_domain_resolve_default (DB_TYPE_BIGINT);
	  break;
	case PT_AVG:
	case PT_STDDEV:
	case PT_STDDEV_POP:
	case PT_STDDEV_SAMP:
	case PT_VARIANCE:
	case PT_VAR_POP:
	case PT_VAR_SAMP:
	  argument = tp_domain_resolve_default (DB_TYPE_DOUBLE);
	  break;
	case PT_SUM:
	  argument = TP_IS_NUMERIC_TYPE (val_type) ? domain_operand_domain (operand)
	    : tp_domain_resolve_default (DB_TYPE_DOUBLE);
	  break;
	case PT_MEDIAN:
	case PT_PERCENTILE_CONT:
	  argument = TP_IS_NUMERIC_TYPE (val_type) ? tp_domain_resolve_default (DB_TYPE_DOUBLE)
	    : domain_operand_domain (operand);
	  break;
	default:
	  argument = domain_operand_domain (operand);
	  break;
	}
    }
  if (function == PT_MEDIAN || function == PT_PERCENTILE_CONT || function == PT_PERCENTILE_DISC)
    {
      /* an interpolation function is typed as its first execution types it: a function the compiler left variable takes
       * its operand's domain, then a number becomes DOUBLE (PERCENTILE_DISC keeps it) and a string the type
       * resolve_domains gave its value, or DOUBLE when it has no value */
      const TP_DOMAIN *start_domain = argument == NULL || TP_DOMAIN_TYPE (argument) == DB_TYPE_VARIABLE
	? domain_operand_domain (operand) : argument;
      if (start_domain != NULL && TP_DOMAIN_TYPE (start_domain) != DB_TYPE_VARIABLE)
	{
	  if (!domain_is_interpolation_type (TP_DOMAIN_TYPE (start_domain))
	      && TP_DOMAIN_TYPE (start_domain) != DB_TYPE_NULL && operand->val_type == DB_TYPE_NULL)
	    {
	      /* a value none of DOUBLE, DATETIME, TIME takes (resolve_domains types a string, a BIT, a LOB, a
	       * collection): the first execution would raise the error; resolve_domains raises it */
	      return ER_ARG_CAN_NOT_BE_CASTED_TO_DESIRED_DOMAIN;
	    }
	  const TP_DOMAIN *final_domain = domain_interpolation_final (function, start_domain, val_type);
	  argument = final_domain != NULL ? final_domain
	    : TP_IS_CHAR_TYPE (TP_DOMAIN_TYPE (start_domain)) ? tp_domain_resolve_default (DB_TYPE_DOUBLE) :
	    start_domain;
	}
    }
  if (argument == NULL)
    {
      return ER_FAILED;
    }
  result->domain = argument;
  result->operand_domain[0] = argument;
  result->conv[0] = tp_value_find_converter (val_type, argument, DOMAIN_CONVERT_OPERAND);
  return NO_ERROR;
}

/*
 * domain_resolve_function - result types of the late-bound functions (pt_is_op_hv_late_bind) and the value copies
 *   return: NO_ERROR, or the error the function raises for this argument type
 *
 * The value-dependent ones take their type from resolve_domains (ADDTIME and STR_TO_DATE in string_opfunc.c); the
 * others have a fixed result type or the type of the argument they copy. fetch_peek_arith gives no
 * value for a NULL first argument, and for any NULL argument of ADDTIME, STR_TO_DATE, NEW_TIME, FROM_TZ and CONV.
 */
/*
 * [리뷰] domain_resolve_function — domain_resolve 의 DOMAIN_CTX_FUNC_ARG 분기로, 늦은 바인딩 함수(ADDTIME, STR_TO_DATE,
 * TO_CHAR, CAST, PRIOR 등)의 결과 도메인과 인자 처리를 확정한다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 에서는 fetch_peek_arith 가 행마다 값을 보고 각 함수 구현이 결과 타입을 정했다.
 * 이 PR: 먼저 NULL 인자 단락 규칙(함수군별로 어느 인자의 NULL 이 결과를 NULL 로 만드는지)을 적용하고, opcode 별로 결과 타입을 정한다. CAST 계열은 컴파일 도메인을,
 * DEFINE_VARIABLE/PRIOR 류는 인자 도메인을 그대로 쓰고, 모르는 함수는 ER_QPROC_DOMAIN_UNRESOLVED 로 추측을 거부한다.
 * 바뀐 것: 신규 함수(+209줄). 배정 묶음에서 가장 큰 함수로, 함수별 결과 타입 표가 한 자리에 모였다.
 */
static int
domain_resolve_function (int opcode, const DOMAIN_OPERAND * operands, int n_operands,
			 const TP_DOMAIN * consumer_domain, RESOLVED_DOMAIN * result)
{
  DB_TYPE result_type = DB_TYPE_NULL;
  bool null_any = false;
  for (int i = 0; i < n_operands; i++)
    {
      null_any = null_any || domain_operand_type (&operands[i]) == DB_TYPE_NULL;
    }

  switch (opcode)
    {
    case T_ADDTIME:
    case T_STR_TO_DATE:
    case T_NEW_TIME:
    case T_FROM_TZ:
    case T_CONV:
      if (null_any)
	{
	  goto set_operands;
	}
      break;
    case T_TO_CHAR:
    case T_HEX:
    case T_ASCII:
    case T_BIT_LENGTH:
    case T_OCTET_LENGTH:
    case T_HOUR:
    case T_MINUTE:
    case T_SECOND:
    case T_TO_DATE:
    case T_TO_TIME:
    case T_TO_TIMESTAMP:
    case T_TO_TIMESTAMP_TZ:
    case T_TO_DATETIME:
    case T_TO_DATETIME_TZ:
      if (domain_operand_type (&operands[0]) == DB_TYPE_NULL)
	{
	  goto set_operands;
	}
      break;
    default:
      /* a copy takes its argument's domain, NULL included; any other operator is looked up below */
      break;
    }

  switch (opcode)
    {
    case T_ADDTIME:
      switch (domain_operand_type (&operands[0]))
	{
	case DB_TYPE_CHAR:
	case DB_TYPE_VARCHAR:
	  /* a value is typed before this (VARCHAR without a zone, DATETIMETZ with one); a string resolve_domains has no
	   * value for (a column, an expression) is VARCHAR, the manual's "date/time string" row */
	  result_type = DB_TYPE_VARCHAR;
	  break;
	case DB_TYPE_DATETIME:
	case DB_TYPE_TIMESTAMP:
	case DB_TYPE_DATE:
	  result_type = DB_TYPE_DATETIME;
	  break;
	case DB_TYPE_DATETIMELTZ:
	case DB_TYPE_TIMESTAMPLTZ:
	  result_type = DB_TYPE_DATETIMELTZ;
	  break;
	case DB_TYPE_DATETIMETZ:
	case DB_TYPE_TIMESTAMPTZ:
	  result_type = DB_TYPE_DATETIMETZ;
	  break;
	case DB_TYPE_TIME:
	  result_type = DB_TYPE_TIME;
	  break;
	default:
	  return ER_QSTR_INVALID_DATA_TYPE;
	}
      break;

    case T_STR_TO_DATE:
      assert (n_operands >= 2);
      result_type = consumer_domain != NULL && TP_DOMAIN_TYPE (consumer_domain) != DB_TYPE_VARIABLE
	? TP_DOMAIN_TYPE (consumer_domain) : domain_operand_type (&operands[1]);
      if (result_type != DB_TYPE_TIME && result_type != DB_TYPE_DATE && result_type != DB_TYPE_DATETIME
	  && result_type != DB_TYPE_DATETIMETZ)
	{
	  return ER_OBJ_INVALID_ARGUMENTS;
	}
      break;

    case T_NEW_TIME:
      /* db_new_time converts DATETIME and TIME within their type */
      result_type = domain_operand_type (&operands[0]);
      if (result_type != DB_TYPE_DATETIME && result_type != DB_TYPE_TIME)
	{
	  return ER_QSTR_INVALID_DATA_TYPE;
	}
      break;

    case T_FROM_TZ:
      /* db_from_tz */
      if (domain_operand_type (&operands[0]) != DB_TYPE_DATETIME)
	{
	  return ER_QSTR_INVALID_DATA_TYPE;
	}
      result_type = DB_TYPE_DATETIMETZ;
      break;

    case T_TO_CHAR:
      /* db_to_char: numbers and dates print to VARCHAR, a string comes back as it is */
      result_type = domain_operand_type (&operands[0]);
      if (TP_IS_NUMERIC_TYPE (result_type) || TP_IS_DATE_OR_TIME_TYPE (result_type))
	{
	  result_type = DB_TYPE_VARCHAR;
	}
      else if (!TP_IS_CHAR_TYPE (result_type))
	{
	  return ER_QSTR_INVALID_DATA_TYPE;
	}
      break;

    case T_HEX:
    case T_CONV:
      /* db_hex, db_conv: db_make_string, a floating VARCHAR in LANG_SYS */
      result->domain = domain_character_domain (DB_TYPE_VARCHAR, DB_MAX_VARCHAR_PRECISION, LANG_SYS_COLLATION);
      if (result->domain == NULL)
	{
	  return ER_OUT_OF_VIRTUAL_MEMORY;
	}
      goto copy_operands;

    case T_ASCII:
      /* db_ascii: db_make_short */
      result_type = DB_TYPE_SHORT;
      break;

    case T_BIT_LENGTH:
    case T_OCTET_LENGTH:
    case T_HOUR:
    case T_MINUTE:
    case T_SECOND:
      result_type = DB_TYPE_INTEGER;
      break;

    case T_TO_DATE:
      result_type = DB_TYPE_DATE;
      break;

    case T_TO_TIME:
      result_type = DB_TYPE_TIME;
      break;

    case T_TO_TIMESTAMP:
      result_type = DB_TYPE_TIMESTAMP;
      break;

    case T_TO_TIMESTAMP_TZ:
      result_type = DB_TYPE_TIMESTAMPTZ;
      break;

    case T_TO_DATETIME:
      result_type = DB_TYPE_DATETIME;
      break;

    case T_TO_DATETIME_TZ:
      result_type = DB_TYPE_DATETIMETZ;
      break;

    case T_DEFINE_VARIABLE:
      /* session_define_variable returns the value it stores: (name, value) */
      assert (n_operands == 2);
      result->domain = domain_operand_domain (&operands[1]);
      goto copy_operands;

    case T_PRIOR:
    case T_CONNECT_BY_ROOT:
    case T_QPRIOR:
      /* the argument's value in another row */
      result->domain = domain_operand_domain (&operands[0]);
      goto copy_operands;

    case T_CAST:
    case T_CAST_NOFAIL:
    case T_CAST_WRAP:
      /* the value is cast into the compiled target (fetch_peek_arith, tp_value_cast_internal): a target the compiler
       * left VARIABLE (the set operation's CAST(x AS uncertain) wrapper) casts no value - a NULL stays NULL and
       * any other argument fails (-181) - so the node holds no value */
      result->domain = consumer_domain != NULL && TP_DOMAIN_TYPE (consumer_domain) != DB_TYPE_VARIABLE
	? consumer_domain : &tp_Null_domain;
      goto copy_operands;

    default:
      /* a function the type rules do not know: resolve_domains must not guess */
      return ER_QPROC_DOMAIN_UNRESOLVED;
    }

set_operands:
  result->domain = tp_domain_resolve_default (result_type);

copy_operands:
  /* the functions take their arguments as they are; a value-dependent argument keeps its value */
  for (int i = 0; i < n_operands && i < 3; i++)
    {
      result->operand_domain[i] = operands[i].domain;
      result->conv[i] = NULL;
    }
  result->domain = domain_variable_string_value (result->domain);
  return NO_ERROR;
}

/*
 * domain_resolve_list_column - a list column: its producer's domain (ALIAS); a set-operation or CTE column
 *   unifies its branches as qfile_unify_types does
 *   return: NO_ERROR, or ER_QPROC_INCOMPATIBLE_TYPES when the branches differ
 *
 * A branch without a value (a NULL bind) takes the other's domain; one domain, or one variable string type, keeps
 * the first branch's. Two different domains are rejected before execution: qfile_unify_types alone raises the error
 * only when both branch lists hold rows and takes the other branch's domain when one is empty, which no resolution
 * before the rows can follow.
 */
/*
 * [리뷰] domain_resolve_list_column — domain_resolve 의 DOMAIN_CTX_LIST_COLUMN 분기로, 리스트파일 컬럼(UNION/CTE 가지,
 * ALIAS)의 도메인을 분기들로부터 하나로 모아 돌려준다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 의 qfile_unify_types 는 두 리스트에 행이 있을 때만 에러를 내고 한쪽이 비면 상대 도메인을 취해, 행
 * 전에는 따라갈 수 없는 동작이었다.
 * 이 PR: NULL 도메인 분기는 건너뛰고, 서로 다른 도메인은 (같은 타입의 가변 문자열이나 JSON 이 아닌 한) ER_QPROC_INCOMPATIBLE_TYPES 로 실행 전에 거부한다.
 * 바뀐 것: 신규 함수(+26줄). develop 의 "행 수에 따라 달라지던" 규칙을 행과 무관한 규칙으로 바꾼 의도적 동작 변화 — 주석에 그 근거가 적혀 있다.
 */
static int
domain_resolve_list_column (const DOMAIN_OPERAND * operands, int n_operands, RESOLVED_DOMAIN * result)
{
  const TP_DOMAIN *domain = NULL;
  for (int i = 0; i < n_operands; i++)
    {
      const TP_DOMAIN *branch = domain_operand_domain (&operands[i]);
      if (branch == NULL || TP_DOMAIN_TYPE (branch) == DB_TYPE_NULL)
	{
	  continue;
	}
      if (domain == NULL)
	{
	  domain = branch;
	}
      else if (branch != domain
	       && !(TP_DOMAIN_TYPE (branch) == TP_DOMAIN_TYPE (domain)
		    && ((pr_is_string_type (TP_DOMAIN_TYPE (domain)) && pr_is_variable_type (TP_DOMAIN_TYPE (domain)))
			|| TP_DOMAIN_TYPE (domain) == DB_TYPE_JSON)))
	{
	  return ER_QPROC_INCOMPATIBLE_TYPES;
	}
    }
  result->domain = result->operand_domain[0] = domain != NULL ? domain : &tp_Null_domain;
  return NO_ERROR;
}

/* tp_value_compare_with_error compares through tp_value_coerce, which refuses these pairs before it converts
 * (TP_IMPLICIT_COERCION_NOT_ALLOWED): a comparison's converter fails there as that coercion does, where the ASSIGN
 * converter would convert */
/*
 * [리뷰] domain_implicit_coercion_refused — domain_compute_comparison 과 domain_compare_converter 가 쓰는 술어로,
 * tp_value_coerce 가 암시적 강제변환을 거부하는 타입 쌍(TP_IMPLICIT_COERCION_NOT_ALLOWED)인지 답한다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 에서는 tp_value_coerce 안의 TP_IMPLICIT_COERCION_NOT_ALLOWED 분기가 행마다
 * 같은 거부를 했다.
 * 이 PR: BLOB/CLOB 이 끼면 거부, 문자 소스는 문자/날짜/숫자/ENUM 목표만 허용, 그 외 소스는 문자 목표를 거부한다.
 * 바뀐 것: 신규 함수(+14줄). 거부 규칙을 비교 해석기가 미리 읽을 수 있게 분리.
 */
static bool
domain_implicit_coercion_refused (DB_TYPE source, DB_TYPE target)
{
  if (source == DB_TYPE_BLOB || source == DB_TYPE_CLOB || target == DB_TYPE_BLOB || target == DB_TYPE_CLOB)
    {
      return true;
    }
  if (TP_IS_CHAR_TYPE (source))
    {
      return !(TP_IS_CHAR_TYPE (target) || TP_IS_DATE_OR_TIME_TYPE (target) || TP_IS_NUMERIC_TYPE (target)
	       || target == DB_TYPE_ENUMERATION);
    }
  return source != DB_TYPE_ENUMERATION && TP_IS_CHAR_TYPE (target);
}

/* The converter a comparison runs on a side: the ASSIGN converter (tp_value_coerce's on the pairs a
 * comparison reaches), failing what implicit coercion refuses. */
/*
 * [리뷰] domain_compare_converter — 비교 한쪽에 걸 변환기를 고르는 함수로, 암시적 강제변환이 거부하는 쌍이면 "실패하는 변환기" 를 돌려줘 행에서 develop 과 같은
 * 실패를 재현한다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 에서는 변환 자체가 행에서 거부돼 -181 경로로 갔다.
 * 이 PR: 거부 쌍이면 tp_value_find_converter(source, NULL, ASSIGN) 로 호환 불가 변환기를, 아니면 정상 ASSIGN 변환기를 돌려준다.
 * 바뀐 것: 신규 함수(+10줄). "실패도 미리 결정한다" 는 설계가 드러나는 작은 접합부.
 */
static TP_VALUE_CONVERTER
domain_compare_converter (DB_TYPE source, const TP_DOMAIN * target)
{
  if (domain_implicit_coercion_refused (source, TP_DOMAIN_TYPE (target)))
    {
      /* the incompatible converter */
      return tp_value_find_converter (source, NULL, DOMAIN_CONVERT_ASSIGN);
    }
  return tp_value_find_converter (source, target, DOMAIN_CONVERT_ASSIGN);
}

/*
 * [리뷰] domain_fixes_values — 플랜/해석 양쪽(domain_plan.c:domain_compare_side,
 * domain_resolve.c:qexec_compare_side_key)이 부르는 공개 술어로, 이 도메인이 값의 타입과 콜레이션을 확정하는지를 답한다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 에는 VARIABLE 여부와 콜레이션 플래그를 함께 보는 공용 판정이 없었다.
 * 이 PR: domain != NULL && 타입이 VARIABLE 이 아니고, 콜레이션을 갖는 타입이면 콜레이션 플래그가 NORMAL 일 때만 true.
 * 바뀐 것: 신규 공개 함수(+6줄). domain_is_variable(헤더 인라인)의 사실상 반대 술어를 NULL 처리만 달리해 둔 쌍.
 */
bool
domain_fixes_values (const TP_DOMAIN * domain)
{
  return domain != NULL && TP_DOMAIN_TYPE (domain) != DB_TYPE_VARIABLE
    && (!TP_TYPE_HAS_COLLATION (TP_DOMAIN_TYPE (domain)) || TP_DOMAIN_COLLATION_FLAG (domain) == TP_DOMAIN_COLL_NORMAL);
}

/*
 * [리뷰] domain_compare_key_of — 컴파일(domain_plan.c)과 해석(domain_resolve.c) 양쪽이 도메인을 비교 키(타입+codeset+콜레이션)로 바꿀 때
 * 부르는 공개 함수.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 에는 비교 키라는 개념 자체가 없었다.
 * 이 PR: NULL 도메인은 type=DB_TYPE_NULL, 콜레이션 없는 타입은 codeset/collation 을 -1 로 두고, 콜레이션 있는 타입만 도메인의 값을 복사한다.
 * 바뀐 것: 신규 공개 함수(+8줄). 타입 쌍 비교표의 색인 키를 만드는 입구.
 */
void
domain_compare_key_of (const TP_DOMAIN * domain, DOMAIN_COMPARE_KEY * key)
{
  key->type = domain != NULL ? TP_DOMAIN_TYPE (domain) : DB_TYPE_NULL;
  const bool has_collation = domain != NULL && TP_TYPE_HAS_COLLATION (key->type);
  key->codeset = has_collation ? TP_DOMAIN_CODESET (domain) : -1;
  key->collation = has_collation ? TP_DOMAIN_COLLATION (domain) : -1;
}

/*
 * [리뷰] domain_compare_key_collate — COLLATE 수정자가 붙은 쪽의 비교 키에 그 codeset·콜레이션을 덮어쓰는 공개 함수로, 플랜·해석·스트림 세 곳이 같은
 * 방식으로 쓴다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 에서는 COLLATE 가 행에서 값의 콜레이션으로만 나타났다.
 * 이 PR: collate 가 NULL 이 아니고 키 타입이 콜레이션을 가질 때만 codeset·collation 을 교체한다.
 * 바뀐 것: 신규 공개 함수(+9줄).
 */
void
domain_compare_key_collate (DOMAIN_COMPARE_KEY * key, const TP_DOMAIN * collate)
{
  if (collate != NULL && TP_TYPE_HAS_COLLATION (key->type))
    {
      key->codeset = TP_DOMAIN_CODESET (collate);
      key->collation = TP_DOMAIN_COLLATION (collate);
    }
}

/* tp_value_compare_with_error's outcome of a conversion that failed: the rank of the two sides' types at that point,
 * and -181 where the caller asks whether the values compare (tp_value_compare asks nothing and gets no error) */
/*
 * [리뷰] domain_compare_conversion_failed — domain_compare_converted 안에서 변환이 실패했을 때 tp_value_compare_with_error
 * 와 같은 결과(랭크)와 같은 에러(-181)를 만들어 돌려준다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 에서는 tp_value_compare_with_error 가 그 시점까지의 변환 상태로 같은 메시지를 만들었다.
 * 이 PR: source[0..1] 과 (첫 변환이 끝났으면) converted_first 로 두 타입 이름을 복원해 can_compare 가 있으면 ER_TP_CANT_COERCE 를 올리고,
 * tp_more_general_type 의 랭크로 DB_GT/DB_LT 를 돌려준다.
 * 바뀐 것: 신규 함수(+15줄). DOMAIN_COMPARE 에 source/converted_first 필드를 둔 이유가 여기서 드러난다.
 */
static DB_VALUE_COMPARE_RESULT
domain_compare_conversion_failed (const DOMAIN_COMPARE * compare, bool first_converted, bool * can_compare)
{
  DB_TYPE type[2] = { (DB_TYPE) compare->source[0], (DB_TYPE) compare->source[1] };
  if (first_converted)
    {
      type[compare->first] = (DB_TYPE) compare->converted_first;
    }
  if (can_compare != NULL)
    {
      *can_compare = false;
      er_set (ER_ERROR_SEVERITY, ARG_FILE_LINE, ER_TP_CANT_COERCE, 2, pr_type_name (type[0]), pr_type_name (type[1]));
    }
  return tp_more_general_type (type[0], type[1]) > 0 ? DB_GT : DB_LT;
}

/*
 * domain_compare_converted () - comparison method CONVERT: tp_value_compare_with_error's coercion with its converters
 *				 resolved - the first side, then the other, then an ENUM's codeset for the string it
 *				 meets - and cmpval
 *
 * A constant side resolve_domains converted comes in converted; one whose conversion failed gives the failure's
 * outcome at its turn. A correlated side its scope converted comes in converted too (preconverted).
 */
/*
 * [리뷰] domain_compare_converted — 해석된 비교의 CONVERT 커널로, 공개 API 이자 domain_compare_values 의 한 갈래 — 미리 정해진 순서대로
 * 변환기를 돌리고 cmpval 로 비교해 결과를 돌려준다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 의 tp_value_compare_with_error 가 행마다 공통 도메인 판정→강제변환→cmpval 을 모두
 * 했다.
 * 이 PR: first 가 가리키는 쪽부터 변환하고, failed 비트면 그 차례에 실패 결과를 내며, codeset_side 가 있으면 ENUM 의 codeset 으로 상대 문자열을
 * db_char_string_coerce 한 뒤 cmpval 을 부른다. 사용한 임시 DB_VALUE 는 used 비트로 모두 pr_clear_value 한다.
 * 바뀐 것: 신규 공개 함수(+63줄). 변환 실패·codeset 보정 실패 모두 develop 과 같은 반환(DB_UNK, can_compare 미변경)을 유지하도록 맞춰져 있다(develop
 * object_domain.c:10766 과 동일).
 */
DB_VALUE_COMPARE_RESULT
domain_compare_converted (const DOMAIN_COMPARE * compare, const DB_VALUE * value1, const DB_VALUE * value2,
			  int total_order, bool * can_compare, unsigned char preconverted)
{
  const DB_VALUE *side[2] = { value1, value2 };
  DB_VALUE converted[2], codeset_value;
  int used = 0;			/* bit i: converted[i] holds a value, bit 2: codeset_value */
  DB_VALUE_COMPARE_RESULT result;

  for (int k = 0; k < 2; k++)
    {
      const int s = k == 0 ? compare->first : 1 - compare->first;
      if (compare->failed & (1 << s))
	{
	  result = domain_compare_conversion_failed (compare, k == 1, can_compare);
	  goto end;
	}
      if (compare->conv[s] == NULL || (preconverted & (1 << s)))
	{
	  continue;
	}
      used |= 1 << s;
      if (tp_value_convert (compare->conv[s], compare->target[s], side[s], &converted[s]) != DOMAIN_COMPATIBLE)
	{
	  result = domain_compare_conversion_failed (compare, k == 1, can_compare);
	  goto end;
	}
      side[s] = &converted[s];
    }
  if (compare->codeset_side >= 0)
    {
      /* an ENUM compared as a string of another codeset: the other string is brought into the ENUM's */
      const DB_VALUE *text = side[compare->codeset_side];
      DB_DATA_STATUS data_status;
      used |= 4;
      db_value_domain_init (&codeset_value, DB_VALUE_DOMAIN_TYPE (text), DB_VALUE_PRECISION (text), 0);
      db_string_put_cs_and_collation (&codeset_value, lang_get_collation (compare->collation)->codeset,
				      compare->collation);
      if (db_char_string_coerce (text, &codeset_value, &data_status) != NO_ERROR)
	{
	  result = DB_UNK;
	  goto end;
	}
      assert (data_status == DATA_STATUS_OK);
      side[compare->codeset_side] = &codeset_value;
    }
  result = compare->cmp->cmpval (side[0], side[1], compare->coercion, total_order, NULL, compare->collation);

end:
  if (used & 1)
    {
      pr_clear_value (&converted[0]);
    }
  if (used & 2)
    {
      pr_clear_value (&converted[1]);
    }
  if (used & 4)
    {
      pr_clear_value (&codeset_value);
    }
  return result;
}

/*
 * [리뷰] domain_compare_values — 해석된 DOMAIN_COMPARE 와 값 두 개를 받아 행에서 실제 비교를 수행하는 공개 진입점으로, 인덱스 키 비교와 타입 쌍 표 비교가
 * 모두 여기로 들어온다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 에서는 같은 호출부가 tp_value_compare_with_error 를 직접 불러 행마다 해석까지 했다.
 * 이 PR: method 에 따라 DIRECT(cmpval 직행)·CONVERT(domain_compare_converted)·RANK(미리 정한 랭크와 -181)로 갈라지고, 기본 분기는
 * COLLATIONS 로 보고 매 행 ER_QSTR_INCOMPATIBLE_COLLATIONS 를 낸다.
 * 바뀐 것: 신규 공개 함수(+39줄). 행 경로에서 분기 하나와 표 조회만 남긴 것이 이 PR 의 성능 논지.
 */
DB_VALUE_COMPARE_RESULT
domain_compare_values (const DOMAIN_COMPARE * compare, const DB_VALUE * value1, const DB_VALUE * value2,
		       int total_order, bool * can_compare)
{
  switch (compare->method)
    {
    case DOMAIN_COMPARE_DIRECT:
      return compare->cmp->cmpval ((DB_VALUE *) value1, (DB_VALUE *) value2, compare->coercion, total_order, NULL,
				   compare->collation);
    case DOMAIN_COMPARE_CONVERT:
      return domain_compare_converted (compare, value1, value2, total_order, can_compare, 0);
    case DOMAIN_COMPARE_RANK:
      /* types that do not compare as they are, without coercion: the answer is their rank */
      if (can_compare != NULL)
	{
	  *can_compare = false;
	  er_set (ER_ERROR_SEVERITY, ARG_FILE_LINE, ER_TP_CANT_COERCE, 2, pr_type_name ((DB_TYPE) compare->source[0]),
		  pr_type_name ((DB_TYPE) compare->source[1]));
	}
      return (DB_VALUE_COMPARE_RESULT) compare->rank;
    default:
      /* strings whose collations do not merge: -1150 at every row */
#if !defined (NDEBUG)
      if (compare->method != DOMAIN_COMPARE_COLLATIONS)
	{
	  fprintf (stderr, "planned comparison kernel: kernel=%d site=%d source=%d,%d values=%d,%d\n",
		   (int) compare->method, compare->compare_index, (int) compare->source[0], (int) compare->source[1],
		   (int) DB_VALUE_DOMAIN_TYPE (value1), (int) DB_VALUE_DOMAIN_TYPE (value2));
	}
#endif
      assert (compare->method == DOMAIN_COMPARE_COLLATIONS);
      er_set (ER_ERROR_SEVERITY, ARG_FILE_LINE, ER_QSTR_INCOMPATIBLE_COLLATIONS, 0);
      if (can_compare != NULL)
	{
	  *can_compare = false;
	}
      return DB_UNK;
    }
}

/*
 * [리뷰] domain_compare_key_of_value — 값 하나에서 비교 키(타입+codeset+콜레이션)를 뽑는 공개 함수로, 행 경로(domain_search_key_compare,
 * domain_compare_by_type_pair, domain_compare_row_entry)가 표를 찾을 때 쓴다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: 문자형이면 db_get_string_codeset/collation, ENUM 이면 db_get_enum_codeset/collation 을 읽고 나머지는 -1 로 둔다.
 * 바뀐 것: 신규 공개 함수(+16줄). domain_compare_key_of(도메인용)의 값 버전.
 */
void
domain_compare_key_of_value (const DB_VALUE * value, DOMAIN_COMPARE_KEY * key)
{
  key->type = DB_VALUE_DOMAIN_TYPE (value);
  key->codeset = key->collation = -1;
  if (TP_IS_CHAR_TYPE (key->type))
    {
      key->codeset = db_get_string_codeset (value);
      key->collation = db_get_string_collation (value);
    }
  else if (key->type == DB_TYPE_ENUMERATION)
    {
      key->codeset = db_get_enum_codeset (value);
      key->collation = db_get_enum_collation (value);
    }
}

/*
 * [리뷰] domain_value_domain — qexec_resolve_domains_internal 이 상수·바인드 값의 도메인을 알아낼 때 부르는 공개 함수로,
 * tp_domain_resolve_value 가 만들고 버리는 임시 도메인 없이 캐시된 도메인을 돌려준다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 은 tp_domain_resolve_value 를 그대로 불러 임시 TP_DOMAIN 생성·해제를 반복했다.
 * 이 PR: 파라미터 없는 타입은 내장 도메인, 문자/비트는 codeset·콜레이션·정밀도(부동 정밀도는 최대값으로 읽음)로 tp_domain_find_charbit, NUMERIC 은
 * tp_domain_find_numeric 으로 찾고, 못 찾으면 tp_domain_resolve_value 로 떨어진다. 디버그 빌드에서 두 경로 동치를 assert 한다.
 * 바뀐 것: 신규 공개 함수(+89줄). 타입별 캐시 조회 표를 새로 씀.
 */
const TP_DOMAIN *
domain_value_domain (const DB_VALUE * value)
{
  const DB_TYPE type = DB_VALUE_DOMAIN_TYPE (value);
  const TP_DOMAIN *domain = NULL;
  switch (type)
    {
    case DB_TYPE_NULL:
    case DB_TYPE_INTEGER:
    case DB_TYPE_BIGINT:
    case DB_TYPE_FLOAT:
    case DB_TYPE_DOUBLE:
    case DB_TYPE_BLOB:
    case DB_TYPE_CLOB:
    case DB_TYPE_TIME:
    case DB_TYPE_TIMESTAMP:
    case DB_TYPE_TIMESTAMPTZ:
    case DB_TYPE_TIMESTAMPLTZ:
    case DB_TYPE_DATE:
    case DB_TYPE_DATETIME:
    case DB_TYPE_DATETIMETZ:
    case DB_TYPE_DATETIMELTZ:
    case DB_TYPE_MONETARY:
    case DB_TYPE_SHORT:
    case DB_TYPE_ENUMERATION:
      /* no parameters: the built-in domain (an ENUM value carries no element list) */
      domain = tp_domain_resolve_default (type);
      break;

    case DB_TYPE_CHAR:
    case DB_TYPE_VARCHAR:
    case DB_TYPE_BIT:
    case DB_TYPE_VARBIT:
      {
	/* the value's codeset, collation and precision, a variable string's floating one read as its maximum */
	const int codeset = db_get_string_codeset (value);
	int precision = db_value_precision (value);
	if (type == DB_TYPE_VARCHAR
	    && (precision == 0 || precision == TP_FLOATING_PRECISION_VALUE || precision > DB_MAX_VARCHAR_PRECISION))
	  {
	    precision = DB_MAX_VARCHAR_PRECISION;
	  }
	else if (type == DB_TYPE_VARBIT
		 && (precision == 0 || precision == TP_FLOATING_PRECISION_VALUE || precision > DB_MAX_VARBIT_PRECISION))
	  {
	    precision = DB_MAX_VARBIT_PRECISION;
	  }
	domain = tp_domain_find_charbit (type, codeset, db_get_string_collation (value), TP_DOMAIN_COLL_NORMAL,
					 precision, false);
	if (domain != NULL && TP_IS_CHAR_TYPE (type) && domain->codeset != codeset)
	  {
	    /* the cache matches a string's codeset as well, which tp_domain_find_charbit leaves out for a CHAR */
	    domain = NULL;
	  }
      }
      break;

    case DB_TYPE_NUMERIC:
      {
	/* a default precision or scale reads as NUMERIC's default */
	int precision = db_value_precision (value);
	int scale = db_value_scale (value);
	if (precision == DB_DEFAULT_PRECISION)
	  {
	    precision = DB_DEFAULT_NUMERIC_PRECISION;
	  }
	if (scale == DB_DEFAULT_SCALE)
	  {
	    scale = DB_DEFAULT_NUMERIC_SCALE;
	  }
	domain = tp_domain_find_numeric (DB_TYPE_NUMERIC, precision, scale, false);
      }
      break;

    default:
      /* a collection, a MIDXKEY, an OBJECT or OID, JSON: tp_domain_resolve_value reads the value itself */
      break;
    }
  if (domain == NULL)
    {
      /* not cached yet: tp_domain_resolve_value caches it */
      return tp_domain_resolve_value (value, NULL);
    }
#if !defined (NDEBUG)
  /* debug cross-check (optdebug): tp_domain_resolve_value finds the same cached domain */
  assert (domain == tp_domain_resolve_value (value, NULL));
#endif
  return domain;
}

/*
 * [리뷰] domain_compare_key_equal — 두 비교 키가 완전히 같은지 보는 내부 술어로, domain_key_differs 와 domain_search_key_compare 의
 * 빠른 경로 판정에 쓰인다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: type·codeset·collation 세 필드를 모두 비교한다.
 * 바뀐 것: 신규 함수(+5줄).
 */
static bool
domain_compare_key_equal (const DOMAIN_COMPARE_KEY * lhs, const DOMAIN_COMPARE_KEY * rhs)
{
  return lhs->type == rhs->type && lhs->codeset == rhs->codeset && lhs->collation == rhs->collation;
}

/*
 * [리뷰] domain_key_value_domain — 인덱스 키 원소의 플랜 도메인을 서버가 실제로 보는 값의 도메인으로 바꿔 주는 공개 함수로, 플랜
 * 적재(domain_plan_key_element)와 해석(qexec_key_element_domain)이 공유한다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 에서는 OBJECT→OID 치환이 각 호출부에 흩어져 있었다.
 * 이 PR: OBJECT 도메인이면 OID 기본 도메인, 그 외는 받은 도메인 그대로.
 * 바뀐 것: 신규 공개 함수(+5줄).
 */
const TP_DOMAIN *
domain_key_value_domain (const TP_DOMAIN * domain)
{
  return domain != NULL && TP_DOMAIN_TYPE (domain) == DB_TYPE_OBJECT ? tp_domain_resolve_default (DB_TYPE_OID) : domain;
}

/*
 * [리뷰] domain_key_column — B-tree 키 도메인에서 i번째 컬럼 도메인을 꺼내는 공개 함수로, btree_range_opt_check_add_index_key 와 플랜·해석
 * 양쪽이 같은 규칙으로 컬럼을 센다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 에서는 호출부마다 setdomain 연결리스트를 직접 걸어 내려갔다.
 * 이 PR: MIDXKEY 가 아니면 column==0 일 때만 자신을, MIDXKEY 면 setdomain 을 column 번 따라간 노드를 돌려준다(범위를 넘으면 NULL).
 * 바뀐 것: 신규 공개 함수(+14줄). 중복된 setdomain 순회를 한 곳으로 모음.
 */
const TP_DOMAIN *
domain_key_column (const TP_DOMAIN * key_type, int column)
{
  if (key_type == NULL || TP_DOMAIN_TYPE (key_type) != DB_TYPE_MIDXKEY)
    {
      return column == 0 ? key_type : NULL;
    }
  const TP_DOMAIN *domain = key_type->setdomain;
  for (; domain != NULL && column > 0; column--)
    {
      domain = domain->next;
    }
  return domain;
}

/*
 * [리뷰] domain_in_key_direction — 값의 도메인을 인덱스 컬럼의 정렬 방향(is_desc)에 맞춘 캐시 도메인으로 바꿔 주며, qexec_resolve_index_keys 와
 * domain_plan_key_element 가 쓴다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 에서는 방향 보정이 키 쓰기 코드 안에 묻혀 있었다.
 * 이 PR: 방향이 이미 같거나 둘 중 하나가 NULL 이면 그대로, 다르면 domain_copy_one 으로 한 노드만 복사해 is_desc 를 바꾸고 tp_domain_cache 로 등록한다.
 * 바뀐 것: 신규 공개 함수(+15줄). 형제 리스트를 끌고 오지 않는 단일 노드 복사를 쓰는 점이 핵심.
 */
const TP_DOMAIN *
domain_in_key_direction (const TP_DOMAIN * domain, const TP_DOMAIN * column)
{
  if (domain == NULL || column == NULL || domain->is_desc == column->is_desc)
    {
      return domain;
    }
  TP_DOMAIN *copy = domain_copy_one (domain);
  if (copy == NULL)
    {
      return NULL;
    }
  copy->is_desc = column->is_desc;
  return tp_domain_cache (copy);
}

/*
 * [리뷰] domain_ascending_key_type — 멀티레인지 최적화의 정렬 도메인을 만들기 위해, 키 도메인의 모든 컬럼을 오름차순으로 바꾼 캐시 도메인을
 * domain_plan_add_indexes 에 돌려준다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 에서는 같은 변환이 실행 중 정렬 준비 코드에서 이뤄졌다.
 * 이 PR: 내림차순 컬럼이 하나도 없으면 원본을 그대로 돌려주고, 있으면 단일 컬럼은 복사 후 is_desc=0, MIDXKEY 는 setdomain 전체를 복사해 전 컬럼을 0 으로 만들고
 * tp_domain_construct→tp_domain_cache 한다. construct 실패 시 복사한 컬럼 리스트를 직접 순회하며 tp_domain_free 한다.
 * 바뀐 것: 신규 공개 함수(+46줄). 실패 경로의 해제 짝이 함수 안에서 맞춰져 있다.
 */
const TP_DOMAIN *
domain_ascending_key_type (const TP_DOMAIN * key_type)
{
  bool descending = false;
  const bool midxkey = TP_DOMAIN_TYPE (key_type) == DB_TYPE_MIDXKEY;
  for (const TP_DOMAIN * column = midxkey ? key_type->setdomain : key_type; column != NULL;
       column = midxkey ? column->next : NULL)
    {
      descending = descending || column->is_desc;
    }
  if (!descending)
    {
      return key_type;
    }
  if (!midxkey)
    {
      TP_DOMAIN *ascending = tp_domain_copy (key_type, false);
      if (ascending == NULL)
	{
	  return NULL;
	}
      ascending->is_desc = 0;
      return tp_domain_cache (ascending);
    }
  TP_DOMAIN *columns = tp_domain_copy (key_type->setdomain, false);
  if (columns == NULL)
    {
      return NULL;
    }
  for (TP_DOMAIN * column = columns; column != NULL; column = column->next)
    {
      column->is_desc = 0;
    }
  TP_DOMAIN *ascending = tp_domain_construct (DB_TYPE_MIDXKEY, NULL, key_type->precision, key_type->scale, columns);
  if (ascending == NULL)
    {
      while (columns != NULL)
	{
	  TP_DOMAIN *next = columns->next;
	  tp_domain_free (columns);
	  columns = next;
	}
      return NULL;
    }
  return tp_domain_cache (ascending);
}

/*
 * [리뷰] domain_copy_one — 형제 리스트를 함께 복사하는 tp_domain_copy 와 달리 도메인 노드 하나만 복사해 주는 공개 유틸로,
 * qexec_key_constant_domain 과 domain_in_key_direction 이 쓴다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 에서는 tp_domain_copy 가 next 사슬까지 복사해 호출부가 따로 끊어야 했다.
 * 이 PR: 스택에 구조체를 복사해 next 를 NULL 로 만든 뒤 tp_domain_copy 를 부른다 — 소유권은 호출자에게 넘어간다.
 * 바뀐 것: 신규 공개 함수(+7줄).
 */
TP_DOMAIN *
domain_copy_one (const TP_DOMAIN * domain)
{
  TP_DOMAIN one = *domain;
  one.next = NULL;
  return tp_domain_copy (&one, false);
}

/*
 * [리뷰] domain_key_strict_converter — domain_key_rule 이 부르며, tp_value_coerce_strict 가 값을 인덱스 컬럼 도메인으로 가져갈 때 쓰는
 * 변환기를 돌려준다(거부하는 목표면 NULL).
 * develop: develop 에 없음 — 이 PR 이 신설. develop 에서는 scan_dbvals_to_midxkey 가 행마다 tp_value_coerce_strict 를 호출해 성패를
 * 봤다.
 * 이 PR: 목표가 숫자나 날짜/시간이 아니면 NULL(= strict 불가), 맞으면 COMPARE 모드 변환기를 찾아 돌려준다.
 * 바뀐 것: 신규 공개 함수(+11줄). strict 가능 타입 집합이 코드로 명시됨.
 */
TP_VALUE_CONVERTER
domain_key_strict_converter (DB_TYPE source, const TP_DOMAIN * column)
{
  const DB_TYPE target = TP_DOMAIN_TYPE (column);
  /* tp_value_coerce_strict refuses any other target */
  if (!TP_IS_NUMERIC_TYPE (target) && !TP_IS_DATE_OR_TIME_TYPE (target))
    {
      return NULL;
    }
  return tp_value_find_converter (source, column, DOMAIN_CONVERT_COMPARE);
}

/*
 * [리뷰] domain_key_rule — 검색 키 컬럼이 값을 어떻게 받는지(DOMAIN_KEY_INDEX/STRICT/KEEP)를 정하는 공개 함수로, 플랜 적재와 해석이 같은 규칙으로 컬럼별
 * 규칙을 미리 박아 둔다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 의 scan_dbvals_to_midxkey 가 행마다 같은 판단을 값과 도메인으로 했다.
 * 이 PR: 단일 컬럼 키는 항상 INDEX, MIDXKEY 는 타입이 다르면 strict 변환기 유무로 STRICT/KEEP, 같은 타입이라도 NUMERIC·CHAR·BIT 는
 * tp_domain_match_ignore_order(EXACT) 로 파라미터까지 봐 INDEX/KEEP 을 가른다.
 * 바뀐 것: 신규 공개 함수(+23줄). 행-시점 규칙을 컴파일/해석 시점 열거형으로 승격.
 */
DOMAIN_KEY_RULE
domain_key_rule (const TP_DOMAIN * element, const TP_DOMAIN * column, bool midxkey, TP_VALUE_CONVERTER * strict_conv)
{
  *strict_conv = NULL;
  if (!midxkey)
    {
      /* a single-column key takes its value as it is */
      return DOMAIN_KEY_INDEX;
    }
  const DB_TYPE type = TP_DOMAIN_TYPE (element);
  const DB_TYPE column_type = TP_DOMAIN_TYPE (column);
  if (type != column_type)
    {
      *strict_conv = domain_key_strict_converter (type, column);
      return *strict_conv != NULL ? DOMAIN_KEY_STRICT : DOMAIN_KEY_KEEP;
    }
  if (column_type == DB_TYPE_NUMERIC || column_type == DB_TYPE_CHAR || column_type == DB_TYPE_BIT)
    {
      /* the parameters too: precision and scale, length, collation */
      return tp_domain_match_ignore_order (column, element, TP_EXACT_MATCH) ? DOMAIN_KEY_INDEX : DOMAIN_KEY_KEEP;
    }
  return DOMAIN_KEY_INDEX;
}

/*
 * [리뷰] domain_key_differs — 인덱스 컬럼이 자기 키와 다른 키의 값을 받게 되는지를 답해, 스캔이 DOMAIN_SEARCH_KEYS_OTHER 로 가야 하는지를 플랜·해석이
 * 결정하게 한다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 에는 이 구분이 없어 모든 키 비교가 행에서 해석됐다.
 * 이 PR: 두 도메인의 비교 키를 뽑아, 값 쪽 키가 NULL 타입이 아니면서 컬럼 키와 다르면 true.
 * 바뀐 것: 신규 공개 함수(+9줄). NULL 키를 먼저 제외하는 규칙이 주석으로 근거와 함께 명시됨.
 */
bool
domain_key_differs (const TP_DOMAIN * domain, const TP_DOMAIN * column)
{
  DOMAIN_COMPARE_KEY key[2];
  domain_compare_key_of (domain, &key[0]);
  domain_compare_key_of (column, &key[1]);
  /* a NULL key compares nothing: its values are NULL, which the B-tree and the range build answer first */
  return key[0].type != DB_TYPE_NULL && !domain_compare_key_equal (&key[0], &key[1]);
}

/* The collation a comparison of two keys compares the strings of type in: theirs when they share it, the common
 * collation of their codeset (LANG_RT_COMMON_COLL), or -1 for keys of two codesets; 0 when type is no string. */
/*
 * [리뷰] domain_compare_collation — domain_compute_comparison 과 domain_resolve_comparison_uncoerced 가 부르며, 두 키의
 * 문자열을 어느 콜레이션으로 비교할지(또는 병합 불가 -1)를 돌려준다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 의 tp_value_compare_with_error 꼬리에서 행마다 LANG_RT_COMMON_COLL 이
 * 호출됐다.
 * 이 PR: 문자형이 아니면 0, 콜레이션이 같으면 그것, codeset 이 다르면 -1, 같으면 LANG_RT_COMMON_COLL 의 공통 콜레이션.
 * 바뀐 것: 신규 함수(+19줄).
 */
static int
domain_compare_collation (DB_TYPE type, const DOMAIN_COMPARE_KEY * lhs, const DOMAIN_COMPARE_KEY * rhs)
{
  if (!TP_IS_CHAR_TYPE (type))
    {
      return 0;
    }
  if (lhs->collation == rhs->collation)
    {
      return lhs->collation;
    }
  if (lhs->codeset != rhs->codeset)
    {
      return -1;
    }
  int common;
  LANG_RT_COMMON_COLL (lhs->collation, rhs->collation, common);
  return common;
}

/*
 * domain_compute_comparison () - the comparison tp_value_compare_with_error makes between a value of each
 *   key, resolved before any row: the type pair comparison table's cells, and a comparison of keys the table has no row
 *   for (domain_resolve_comparison)
 *   return: NO_ERROR, or ER_OUT_OF_VIRTUAL_MEMORY when a target domain cannot be cached
 *
 * Follows od:tp_value_compare_with_error step by step: the direction of tp_value_compare_common_domain (TO_DOUBLE
 * converts the string first and the other side only after it), the target a string or an ENUM keeps its codeset and
 * collation in, the collation rule of its tail (equal collations, the ENUM's, LANG_RT_COMMON_COLL on one codeset,
 * otherwise -1), and the type whose cmpval compares. A NULL key (a side whose values are NULL) and an OBJECT key keep
 * tp_value_compare_with_error on the values: NULL answers before any coercion, and the server holds an object as its
 * OID.
 */
/*
 * [리뷰] domain_compute_comparison — 타입 쌍 비교표의 각 칸을 계산하는 본체이자 표에 없는 키 쌍의 즉석 계산기로, 두 비교 키에서
 * DOMAIN_COMPARE(방향·목표·변환기·콜레이션·커널)를 만들어 준다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 의 tp_value_compare_with_error(object_domain.c:10422~)가 행마다 같은 순서를
 * 값 위에서 수행했다.
 * 이 PR: NULL 키는 VALUES, OBJECT 는 OBJECT 커널로 빠지고, 타입이 다르면 tp_value_compare_common_domain 의 방향대로 목표·변환기·first 를
 * 채운 뒤 ENUM/codeset 보정과 콜레이션 규칙을 적용한다. 콜레이션이 안 맞으면 COLLATIONS, 변환기가 생기면 CONVERT, 아니면 DIRECT.
 * 바뀐 것: 신규 함수(+124줄). develop 의 행-시점 비교 절차를 단계별로 베껴 상태 구조체로 굳힌, 이 배정 묶음의 중심 함수.
 */
static int
domain_compute_comparison (const DOMAIN_COMPARE_KEY * lhs, const DOMAIN_COMPARE_KEY * rhs, DOMAIN_COMPARE * result)
{
  const DOMAIN_COMPARE_KEY *key[2] = { lhs, rhs };
  DB_TYPE after[2] = { lhs->type, rhs->type };
  int enum_side = -1;

  *result = DOMAIN_COMPARE
  {
  };
  result->value[0] = result->value[1] = -1;
  result->codeset_side = -1;
  result->compare_index = -1;
  result->source[0] = (unsigned char) lhs->type;
  result->source[1] = (unsigned char) rhs->type;
  result->method = DOMAIN_COMPARE_DIRECT;
  result->coercion = 1;

  if (lhs->type == DB_TYPE_NULL || rhs->type == DB_TYPE_NULL)
    {
      /* its value is NULL, and the comparison answers NULL before it counts or coerces */
      result->method = DOMAIN_COMPARE_VALUES;
      return NO_ERROR;
    }
  if (lhs->type == DB_TYPE_OBJECT || rhs->type == DB_TYPE_OBJECT)
    {
      /* an OBJECT domain's values are OIDs on the server (and OID against OBJECT compares by OID on the client) */
      result->method = DOMAIN_COMPARE_OBJECT;
      return NO_ERROR;
    }
  if (lhs->type != rhs->type)
    {
      const TP_COMPARE_COERCION coercion = tp_value_compare_common_domain (lhs->type, rhs->type);
      const TP_DOMAIN *target = NULL;
      int side = 0;
      switch (coercion)
	{
	case TP_COMPARE_COERCE_NONE:
	  break;

	case TP_COMPARE_COERCE_TO_DOUBLE:
	  side = TP_IS_CHAR_TYPE (lhs->type) ? 0 : 1;
	  target = tp_domain_resolve_default (DB_TYPE_DOUBLE);
	  result->first = (unsigned char) side;
	  result->target[side] = target;
	  result->conv[side] = domain_compare_converter (key[side]->type, target);
	  if (key[1 - side]->type != DB_TYPE_DOUBLE)
	    {
	      result->target[1 - side] = target;
	      result->conv[1 - side] = domain_compare_converter (key[1 - side]->type, target);
	    }
	  after[0] = after[1] = DB_TYPE_DOUBLE;
	  break;

	case TP_COMPARE_COERCE_FIRST_TO_DATE:
	case TP_COMPARE_COERCE_SECOND_TO_DATE:
	  side = coercion == TP_COMPARE_COERCE_FIRST_TO_DATE ? 0 : 1;
	  target = tp_domain_resolve_default (key[1 - side]->type);
	  result->first = (unsigned char) side;
	  result->target[side] = target;
	  result->conv[side] = domain_compare_converter (key[side]->type, target);
	  after[side] = key[1 - side]->type;
	  break;

	case TP_COMPARE_COERCE_SECOND_TO_FIRST:
	case TP_COMPARE_COERCE_FIRST_TO_SECOND:
	  side = coercion == TP_COMPARE_COERCE_SECOND_TO_FIRST ? 1 : 0;
	  target = tp_domain_resolve_default (key[1 - side]->type);
	  if (TP_TYPE_HAS_COLLATION (key[side]->type) && TP_IS_CHAR_TYPE (key[1 - side]->type))
	    {
	      /* the coerced string or ENUM keeps its codeset and collation; an ENUM's collation is the comparison's */
	      target = domain_char_with_collation (key[1 - side]->type, key[side]->codeset, key[side]->collation);
	      if (key[side]->type == DB_TYPE_ENUMERATION)
		{
		  enum_side = side;
		}
	    }
	  if (target == NULL)
	    {
	      return ER_OUT_OF_VIRTUAL_MEMORY;
	    }
	  result->first = (unsigned char) side;
	  result->target[side] = target;
	  result->conv[side] = domain_compare_converter (key[side]->type, target);
	  after[side] = key[1 - side]->type;
	  break;
	}
    }
  result->converted_first = (unsigned char) after[result->first];

  /* the tail on the converted values: the first side's cmpval under the comparison's collation */
  result->cmp = pr_type_from_id (after[0]);
  if (enum_side >= 0 && key[0]->collation != key[1]->collation)
    {
      /* both sides compare as strings of the ENUM's collation */
      assert (TP_IS_CHAR_TYPE (after[0]));
      const int codeset = lang_get_collation (key[enum_side]->collation)->codeset;
      result->collation = key[enum_side]->collation;
      result->codeset_side = key[0]->codeset != codeset ? 0 : key[1]->codeset != codeset ? 1 : -1;
    }
  else
    {
      result->collation = domain_compare_collation (after[0], key[0], key[1]);
    }

  /* the collations are checked on the coerced values: a conversion implicit coercion refuses fails before that,
   * into a string type too (its outcome, not -1150) */
  bool refused = false;
  for (int side = 0; side < 2; side++)
    {
      refused = refused || (result->conv[side] != NULL
			    && domain_implicit_coercion_refused (key[side]->type,
								 TP_DOMAIN_TYPE (result->target[side])));
    }
  if (result->collation == -1 && !refused)
    {
      result->method = DOMAIN_COMPARE_COLLATIONS;
    }
  else if (result->conv[0] != NULL || result->conv[1] != NULL || result->codeset_side >= 0)
    {
      result->method = DOMAIN_COMPARE_CONVERT;
    }
  return NO_ERROR;
}

/* The element types the type pair comparison table covers, by DB_TYPE, and the collation ids it tells apart. */
#define DOMAIN_ELEMENT_TYPES (DB_TYPE_LAST + 1)
#define DOMAIN_ELEMENT_COLLATIONS 256
static_assert (DOMAIN_ELEMENT_COLLATIONS == LANG_MAX_COLLATIONS, "type pair comparison table collations");

/* A type a collection element can have as a value: NULL answers before any comparison, and the national character
 * types have no values (the parser takes NCHAR for CHAR). */
/*
 * [리뷰] domain_element_type — 타입 쌍 비교표가 다룰 원소 타입을 정의하는 표로, domain_key_pairs_make 가 행·열을 만들 때 쓴다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: 컬렉션 원소가 값으로 가질 수 있는 타입만 true 를 돌려준다 — NULL 과 내셔널 문자 타입(NCHAR/VARNCHAR)은 제외한다는 근거가 주석에 있다.
 * 바뀐 것: 신규 함수(+40줄). 표 크기를 결정하는 화이트리스트.
 */
static bool
domain_element_type (int type)
{
  switch (type)
    {
    case DB_TYPE_INTEGER:
    case DB_TYPE_FLOAT:
    case DB_TYPE_DOUBLE:
    case DB_TYPE_VARCHAR:
    case DB_TYPE_OBJECT:
    case DB_TYPE_SET:
    case DB_TYPE_MULTISET:
    case DB_TYPE_SEQUENCE:
    case DB_TYPE_ELO:
    case DB_TYPE_TIME:
    case DB_TYPE_TIMESTAMP:
    case DB_TYPE_DATE:
    case DB_TYPE_MONETARY:
    case DB_TYPE_SHORT:
    case DB_TYPE_VOBJ:
    case DB_TYPE_OID:
    case DB_TYPE_NUMERIC:
    case DB_TYPE_BIT:
    case DB_TYPE_VARBIT:
    case DB_TYPE_CHAR:
    case DB_TYPE_BIGINT:
    case DB_TYPE_DATETIME:
    case DB_TYPE_BLOB:
    case DB_TYPE_CLOB:
    case DB_TYPE_ENUMERATION:
    case DB_TYPE_TIMESTAMPTZ:
    case DB_TYPE_TIMESTAMPLTZ:
    case DB_TYPE_DATETIMETZ:
    case DB_TYPE_DATETIMELTZ:
    case DB_TYPE_JSON:
      return true;
    default:
      return false;
    }
}

/* A collation a value can carry: a registered one (an id nothing registered holds ISO binary's placeholder). */
/*
 * [리뷰] domain_collation_registered — 등록된 콜레이션 id 인지 확인해, 표가 콜레이션 축으로 몇 칸을 가질지 domain_key_pairs_make 가 정하게 한다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: lang_get_collation(c) 이 NULL 이 아니고 그 coll.coll_id 가 c 와 같을 때만 true — 미등록 id 가 받는 ISO 바이너리 자리표시자를 걸러낸다.
 * 바뀐 것: 신규 함수(+6줄).
 */
static bool
domain_collation_registered (int collation)
{
  const LANG_COLLATION *lang_coll = lang_get_collation (collation);
  return lang_coll != NULL && lang_coll->coll.coll_id == collation;
}

/*
 * [리뷰] domain_resolve_comparison_uncoerced — 강제변환 없는 비교(do_coercion 0, 예: 컬렉션 순서)의 해석을 만드는 공개 함수로, 표의 mode 0
 * 평면을 채우는 데도 쓰인다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 에서는 tp_value_compare_with_error 가 do_coercion 0 일 때 행마다 랭크 비교로
 * 떨어졌다.
 * 이 PR: NULL/OBJECT 는 각각 VALUES/OBJECT 커널, 타입이 다르고 둘 다 문자형이 아니면 RANK(tp_more_general_type 결과를 미리 저장), 나머지는
 * DIRECT 에 콜레이션 규칙을 적용하고 병합 불가면 COLLATIONS.
 * 바뀐 것: 신규 공개 함수(+42줄). 강제변환 있는 경로와 대칭 구조로 작성됨.
 */
void
domain_resolve_comparison_uncoerced (const DOMAIN_COMPARE_KEY * lhs, const DOMAIN_COMPARE_KEY * rhs,
				     DOMAIN_COMPARE * result)
{
  *result = DOMAIN_COMPARE
  {
  };
  result->value[0] = result->value[1] = -1;
  result->codeset_side = -1;
  result->compare_index = -1;
  result->source[0] = (unsigned char) lhs->type;
  result->source[1] = (unsigned char) rhs->type;
  result->coercion = 0;

  if (lhs->type == DB_TYPE_NULL || rhs->type == DB_TYPE_NULL)
    {
      /* its value is NULL, and the comparison answers NULL first */
      result->method = DOMAIN_COMPARE_VALUES;
      return;
    }
  if (lhs->type == DB_TYPE_OBJECT || rhs->type == DB_TYPE_OBJECT)
    {
      /* an OBJECT's values are OIDs on the server (and OID against OBJECT compares by OID on the client) */
      result->method = DOMAIN_COMPARE_OBJECT;
      return;
    }
  if (lhs->type != rhs->type && !(TP_IS_CHAR_TYPE (lhs->type) && TP_IS_CHAR_TYPE (rhs->type)))
    {
      /* od:tp_value_compare_with_error without coercion: types that do not compare as they are answer by their rank */
      result->method = DOMAIN_COMPARE_RANK;
      result->rank = (signed char) (tp_more_general_type (lhs->type, rhs->type) > 0 ? DB_GT : DB_LT);
      return;
    }
  /* the first value's cmpval under the collation of the tail, as with coercion when nothing is converted */
  result->method = DOMAIN_COMPARE_DIRECT;
  result->cmp = pr_type_from_id (lhs->type);
  result->collation = domain_compare_collation (lhs->type, lhs, rhs);
  if (result->collation == -1)
    {
      result->method = DOMAIN_COMPARE_COLLATIONS;
    }
}

/*
 * The key pair table: the comparison of every pair of keys a value can have - an element type
 * (domain_element_type) and, for a string or an ENUM, a registered collation - with coercion and without. A pair's
 * entry indexes a pool of the distinct resolutions: most pairs share one (a string's collation does not change how it
 * compares with a number). Its entries depend on no value and no plan, so it is made once - at server boot
 * (domain_type_pair_table_init), or by the first comparison that finds none - and freed before the type
 * module whose cached domains its string targets are (domain_type_pair_table_final).
 */
struct DOMAIN_TYPE_PAIR_TABLE
{
  short first[DOMAIN_ELEMENT_TYPES];	/* a type's key, a string or ENUM type's first; -1: no element type */
  short ordinal[DOMAIN_ELEMENT_COLLATIONS];	/* a registered collation's key among its type's; -1 */
  int n_keys;
  int *entry[2];		/* [coercion][key1 * n_keys + key2]: the pair's resolution in pool; the diagonal is a
				 * key against itself, which an item's row (domain_compare_key_row) reads */
  DOMAIN_COMPARE *pool;
  int n_pool;
};

/* *INDENT-OFF* */
static std::atomic<DOMAIN_TYPE_PAIR_TABLE *> domain_Key_pairs (NULL);
static std::mutex domain_Key_pairs_mutex;
/* *INDENT-ON* */

/*
 * [리뷰] domain_compare_equal — domain_key_pairs_make 가 표의 칸을 풀(pool)에 중복 없이 넣기 위해 두 DOMAIN_COMPARE 가 같은지 비교하는
 * 술어.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR:
 * method·first·source·converted_first·failed·coercion·rank·collation·value·codeset_side·compare_index·cmp·conv·target·operator_functions
 * 등 구조체의 모든 의미 필드를 나열해 비교한다.
 * 바뀐 것: 신규 함수(+10줄). 구조체에 필드가 추가되면 여기도 같이 고쳐야 하는 암묵 계약이 생긴다(패딩 때문에 memcmp 를 못 쓰는 자리).
 */
static bool
domain_compare_equal (const DOMAIN_COMPARE * a, const DOMAIN_COMPARE * b)
{
  return a->method == b->method && a->first == b->first && a->source[0] == b->source[0]
    && a->source[1] == b->source[1] && a->converted_first == b->converted_first && a->failed == b->failed
    && a->coercion == b->coercion && a->rank == b->rank && a->collation == b->collation
    && a->value[0] == b->value[0] && a->value[1] == b->value[1] && a->codeset_side == b->codeset_side
    && a->compare_index == b->compare_index && a->cmp == b->cmp && a->conv[0] == b->conv[0] && a->conv[1] == b->conv[1]
    && a->target[0] == b->target[0] && a->target[1] == b->target[1] && a->operator_functions == b->operator_functions;
}

/*
 * [리뷰] domain_key_pairs_free — 타입 쌍 비교표의 해제부로, domain_type_pair_table_final 과 생성 실패 경로가 부른다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: entry[0], entry[1], pool, 테이블 자체를 free 한다(NULL 이면 아무 것도 안 한다).
 * 바뀐 것: 신규 함수(+11줄). domain_key_pairs_make 의 네 번의 할당과 짝이 맞는다(하네스의 alloc/free 사실로도 4:4 로 확인).
 */
static void
domain_key_pairs_free (DOMAIN_TYPE_PAIR_TABLE * pairs)
{
  if (pairs != NULL)
    {
      free (pairs->entry[0]);
      free (pairs->entry[1]);
      free (pairs->pool);
      free (pairs);
    }
}

/* The table itself: NULL when it cannot be made (no memory). */
/*
 * [리뷰] domain_key_pairs_make — 타입 쌍 비교표를 실제로 만드는 함수로, 모든 (원소 타입 × 등록 콜레이션) 키 쌍에 대해 강제변환 있는/없는 두 평면의 해석을 계산해 풀에
 * 중복 제거해 담는다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 에는 이런 사전 계산표가 없고 모든 비교가 행에서 해석됐다.
 * 이 PR: 등록 콜레이션과 원소 타입으로 n_keys 를 세고, entry[2] 와 2*n*n 크기의 pool 을 할당한 뒤 타입 쌍 단위로 domain_compute_comparison /
 * domain_resolve_comparison_uncoerced 를 돌려 같은 해석은 같은 풀 인덱스를 가리키게 한다. 마지막에 realloc 으로 풀을 줄이고, 어느 할당이든 실패하면
 * domain_key_pairs_free 로 전부 되돌린다.
 * 바뀐 것: 신규 함수(+108줄). 표 크기가 등록 콜레이션 수의 제곱으로 커진다 — 콜레이션 3종 타입 × 등록 수가 n 에 들어가므로 pool 초기 할당은 2*n*n*72B 이고, 로케일을
 * 많이 켠 설치본에서는 부팅 시 수십 MB 가 될 수 있다(계산 근거는 코드의 할당식, 실측은 하지 않음).
 */
static DOMAIN_TYPE_PAIR_TABLE *
domain_key_pairs_make (void)
{
  DOMAIN_TYPE_PAIR_TABLE *pairs = (DOMAIN_TYPE_PAIR_TABLE *) calloc (1, sizeof (*pairs));
  if (pairs == NULL)
    {
      return NULL;
    }
  int collation_of[DOMAIN_ELEMENT_COLLATIONS];
  int n_collations = 0;
  for (int c = 0; c < DOMAIN_ELEMENT_COLLATIONS; c++)
    {
      pairs->ordinal[c] = -1;
      if (domain_collation_registered (c))
	{
	  pairs->ordinal[c] = (short) n_collations;
	  collation_of[n_collations++] = c;
	}
    }
  for (int t = 0; t < DOMAIN_ELEMENT_TYPES; t++)
    {
      pairs->first[t] = -1;
      if (domain_element_type (t))
	{
	  pairs->first[t] = (short) pairs->n_keys;
	  pairs->n_keys += TP_TYPE_HAS_COLLATION (t) ? n_collations : 1;
	}
    }
  const int n = pairs->n_keys;
  DOMAIN_COMPARE_KEY *keys = (DOMAIN_COMPARE_KEY *) malloc (sizeof (*keys) * n);
  pairs->entry[0] = (int *) malloc (sizeof (int) * n * n);
  pairs->entry[1] = (int *) malloc (sizeof (int) * n * n);
  pairs->pool = (DOMAIN_COMPARE *) malloc (sizeof (DOMAIN_COMPARE) * 2 * n * n);
  bool ok = keys != NULL && pairs->entry[0] != NULL && pairs->entry[1] != NULL && pairs->pool != NULL;
  for (int t = 0; ok && t < DOMAIN_ELEMENT_TYPES; t++)
    {
      for (int o = 0; pairs->first[t] >= 0 && o < (TP_TYPE_HAS_COLLATION (t) ? n_collations : 1); o++)
	{
	  DOMAIN_COMPARE_KEY *key = &keys[pairs->first[t] + o];
	  key->type = (DB_TYPE) t;
	  key->codeset = key->collation = -1;
	  if (TP_TYPE_HAS_COLLATION (t))
	    {
	      key->collation = collation_of[o];
	      key->codeset = lang_get_collation (key->collation)->codeset;
	    }
	}
    }
  /* type pair by type pair, so the resolutions of one pair are contiguous in the pool and a key pair looks for its
   * resolution only among its type pair's */
  for (int mode = 0; ok && mode < 2; mode++)
    {
      for (int t1 = 0; ok && t1 < DOMAIN_ELEMENT_TYPES; t1++)
	{
	  for (int t2 = 0; ok && pairs->first[t1] >= 0 && t2 < DOMAIN_ELEMENT_TYPES; t2++)
	    {
	      if (pairs->first[t2] < 0)
		{
		  continue;
		}
	      const int pair_first = pairs->n_pool;
	      const int n1 = TP_TYPE_HAS_COLLATION (t1) ? n_collations : 1;
	      const int n2 = TP_TYPE_HAS_COLLATION (t2) ? n_collations : 1;
	      for (int i = pairs->first[t1]; ok && i < pairs->first[t1] + n1; i++)
		{
		  for (int j = pairs->first[t2]; ok && j < pairs->first[t2] + n2; j++)
		    {
		      int *entry = &pairs->entry[mode][i * n + j];
		      *entry = -1;
		      DOMAIN_COMPARE resolved_domain;
		      if (mode == 1)
			{
			  ok = domain_compute_comparison (&keys[i], &keys[j], &resolved_domain) == NO_ERROR;
			}
		      else
			{
			  domain_resolve_comparison_uncoerced (&keys[i], &keys[j], &resolved_domain);
			}
		      for (int p = pair_first; ok && p < pairs->n_pool && *entry < 0; p++)
			{
			  if (domain_compare_equal (&pairs->pool[p], &resolved_domain))
			    {
			      *entry = p;
			    }
			}
		      if (ok && *entry < 0)
			{
			  pairs->pool[pairs->n_pool] = resolved_domain;
			  *entry = pairs->n_pool++;
			}
		    }
		}
	    }
	}
    }
  free (keys);
  if (!ok)
    {
      domain_key_pairs_free (pairs);
      return NULL;
    }
  DOMAIN_COMPARE *pool = (DOMAIN_COMPARE *) realloc (pairs->pool, sizeof (DOMAIN_COMPARE) * pairs->n_pool);
  if (pool != NULL)
    {
      pairs->pool = pool;
    }
  return pairs;
}

/* The table: the boot made it; the first comparison that finds none makes it here. */
/*
 * [리뷰] domain_key_pairs — 표에 접근하는 유일한 통로로, 부팅이 만들어 둔 표를 돌려주고 없으면 처음 비교가 직접 만들게 한다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: std::atomic 포인터를 acquire 로 읽고, NULL 이면 뮤텍스를 잡아 다시 확인한 뒤 domain_key_pairs_make 를 호출해 release 로 저장하는 이중
 * 검사 잠금. 메모리 부족으로 NULL 이 저장되면 다음 호출이 다시 시도한다.
 * 바뀐 것: 신규 함수(+16줄). 서버 전역 공유 자원에 새 뮤텍스가 생기는 자리 — 다만 획득은 표가 없을 때뿐이다.
 */
static const DOMAIN_TYPE_PAIR_TABLE *
domain_key_pairs (void)
{
  DOMAIN_TYPE_PAIR_TABLE *pairs = domain_Key_pairs.load (std::memory_order_acquire);
  if (pairs == NULL)
    {
      std::lock_guard < std::mutex > lock (domain_Key_pairs_mutex);
      pairs = domain_Key_pairs.load (std::memory_order_relaxed);
      if (pairs == NULL)
	{
	  pairs = domain_key_pairs_make ();
	  domain_Key_pairs.store (pairs, std::memory_order_release);
	}
    }
  return pairs;
}

/*
 * [리뷰] domain_type_pair_table_init — 서버 부팅(boot_restart_server)이 부르는 공개 초기화로, 첫 질의가 치를 표 생성 비용을 부팅으로 옮긴다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: domain_key_pairs() 를 한 번 호출할 뿐이며, 부팅이 못 만들면 첫 비교에 맡긴다.
 * 바뀐 것: 신규 공개 함수(+6줄). boot_sr.c:2656 에서 호출된다.
 */
void
domain_type_pair_table_init (void)
{
  /* a table the boot cannot make is left to the first comparison, as before */
  (void) domain_key_pairs ();
}

/*
 * [리뷰] domain_type_pair_table_final — 표를 해제하는 공개 종료부로, 서버 종료(boot_server_all_finalize)와 SA 모드 클라이언트 종료·util_sa
 * 가 타입 모듈(tp_final)보다 먼저 부른다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: 뮤텍스를 잡고 atomic exchange(NULL) 한 포인터를 domain_key_pairs_free 로 해제한다.
 * 바뀐 것: 신규 공개 함수(+6줄). 호출부는 boot_cl.c 673·1571 과 util_sa.c 2122 모두 `#if defined(SA_MODE)` 안에 있어 INV-3(세 바이너리)의
 * 가드가 지켜진다.
 * [지적 X1-06]
 */
void
domain_type_pair_table_final (void)
{
  std::lock_guard < std::mutex > lock (domain_Key_pairs_mutex);
  domain_key_pairs_free (domain_Key_pairs.exchange (NULL));
}

/*
 * [리뷰] domain_unresolved_error — 실행 전 게이트가 해석했어야 할 비교가 해석 없이 행에 도달했을 때 모든 호출부가 공유하는 단일 보고 지점으로, optdebug 는 멈추고
 * release 는 ER_QPROC_DOMAIN_UNRESOLVED 를 낸다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 에는 "해석되지 않은 도메인" 이라는 상태 자체가 없었다.
 * 이 PR: 무조건 assert(false) 한 뒤 alias·index·타입 이름을 담아 ER_QPROC_DOMAIN_UNRESOLVED 를 올리고 그 코드를 돌려준다. btree,
 * query_evaluator, px_scan 등이 모두 여기를 거친다.
 * 바뀐 것: 신규 공개 함수(+8줄). 이 PR 의 "행은 읽기만 한다" 계약을 어겼을 때의 단일 출구.
 */
int
domain_unresolved_error (const char *alias, int index, DB_TYPE type)
{
  assert (false);
  er_set (ER_ERROR_SEVERITY, ARG_FILE_LINE, ER_QPROC_DOMAIN_UNRESOLVED, 4, "execute", alias, index,
	  pr_type_name (type));
  return ER_QPROC_DOMAIN_UNRESOLVED;
}

/* A key's row and column in the table; -1 for a key no value of an element type carries. */
/*
 * [리뷰] domain_key_pair_index — 비교 키를 표의 행·열 번호로 바꾸는 내부 인라인으로, 행 경로(domain_search_key_compare,
 * domain_compare_row_entry)가 칸을 찾을 때 쓴다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: 타입의 first 를 보고, 콜레이션 있는 타입이면 ordinal[collation] 을 더해 색인을 만들며, 범위를 벗어나거나 미등록이면 -1.
 * 바뀐 것: 신규 함수(+12줄). 행 경로의 비용이 배열 2회 조회로 고정된다.
 */
static inline int
domain_key_pair_index (const DOMAIN_TYPE_PAIR_TABLE * pairs, const DOMAIN_COMPARE_KEY * key)
{
  const int first = key->type >= 0 && key->type < DOMAIN_ELEMENT_TYPES ? pairs->first[key->type] : -1;
  if (first < 0 || !TP_TYPE_HAS_COLLATION (key->type))
    {
      return first;
    }
  const int ordinal = key->collation >= 0 && key->collation < DOMAIN_ELEMENT_COLLATIONS
    ? pairs->ordinal[key->collation] : -1;
  return ordinal >= 0 ? first + ordinal : -1;
}

/* A key's row and column in the table when it is one of the table's keys exactly: a string or ENUM key whose codeset
 * is its collation's, as the table's keys have it; -1 otherwise. The codesets resolve a coerced string's target and
 * whether two collations merge, so a comparison resolved for its keys copies the table's cell only then. */
/*
 * [리뷰] domain_key_pair_index_exact — 표의 칸을 그대로 복사해도 되는 키인지까지 확인하는 색인 함수로, 해석 시점(domain_resolve_comparison,
 * domain_compare_key_row)이 쓴다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: domain_key_pair_index 결과에 더해, 콜레이션 있는 타입인데 키의 codeset 이 그 콜레이션의 codeset 과 다르면 -1 을 돌려 표를 쓰지 못하게 한다.
 * 바뀐 것: 신규 함수(+10줄). codeset 불일치 키를 표에서 배제하는 이유(목표 도메인과 병합 판정이 codeset 에 달려 있음)가 주석에 적혀 있다.
 */
static int
domain_key_pair_index_exact (const DOMAIN_TYPE_PAIR_TABLE * pairs, const DOMAIN_COMPARE_KEY * key)
{
  const int index = domain_key_pair_index (pairs, key);
  if (index >= 0 && TP_TYPE_HAS_COLLATION (key->type) && key->codeset != lang_get_collation (key->collation)->codeset)
    {
      return -1;
    }
  return index;
}

/*
 * [리뷰] domain_resolve_comparison — 플랜 적재(domain_plan_add_comparison)와 해석(qexec_resolve_compare)이 두 키의 비교를 확정할
 * 때 부르는 공개 진입점.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 은 비교마다 행에서 해석했다.
 * 이 PR: 표가 있고 두 키가 정확 색인되면 pool 의 칸을 통째로 복사하고, 아니면 domain_compute_comparison 으로 같은 계산을 즉석에서 한다.
 * 바뀐 것: 신규 공개 함수(+14줄). 표가 없어도(메모리 부족) 결과가 같다는 대칭이 보장되는 자리.
 */
int
domain_resolve_comparison (const DOMAIN_COMPARE_KEY * lhs, const DOMAIN_COMPARE_KEY * rhs, DOMAIN_COMPARE * result)
{
  const DOMAIN_TYPE_PAIR_TABLE *pairs = domain_key_pairs ();
  const int row = pairs != NULL ? domain_key_pair_index_exact (pairs, lhs) : -1;
  const int column = pairs != NULL ? domain_key_pair_index_exact (pairs, rhs) : -1;
  if (row < 0 || column < 0)
    {
      /* a key the table has no row for, or no table (no memory): the same computation the table's cells come from */
      return domain_compute_comparison (lhs, rhs, result);
    }
  *result = pairs->pool[pairs->entry[1][row * pairs->n_keys + column]];
  return NO_ERROR;
}

/*
 * [리뷰] domain_compare_key_row — 컬렉션 원소 비교처럼 상대가 행에서 정해지는 경우에 쓸 "내 키의 표 행 번호" 를 플랜·해석에 돌려준다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: 표가 있으면 domain_key_pair_index_exact 의 값을, 없거나 표에 없는 키면 -1 을 돌려준다.
 * 바뀐 것: 신규 공개 함수(+6줄).
 */
int
domain_compare_key_row (const DOMAIN_COMPARE_KEY * key)
{
  const DOMAIN_TYPE_PAIR_TABLE *pairs = domain_key_pairs ();
  return pairs != NULL ? domain_key_pair_index_exact (pairs, key) : -1;
}

/*
 * [리뷰] domain_compare_row_entry — query_evaluator.c:eval_element_compare 가 행에서 부르며, 미리 받은 행 번호와 지금 본 원소 값으로 표의
 * 칸(DOMAIN_COMPARE)을 꺼내 준다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 에서는 원소마다 tp_value_compare_with_error 가 해석까지 했다.
 * 이 PR: 값에서 키를 뽑아 열 번호를 구하고 pool 의 칸 포인터를 돌려주며, 표에 없는 타입이면 NULL(호출자가 다른 경로로 처리).
 * 바뀐 것: 신규 공개 함수(+11줄). 행 번호가 나간 이상 표는 존재한다는 전제를 assert 로 적고, 그래도 NULL 검사를 남겨 둔 방어적 형태.
 */
const DOMAIN_COMPARE *
domain_compare_row_entry (int row, const DB_VALUE * element)
{
  /* a row was given out, so the table was made; it lives until the server stops */
  const DOMAIN_TYPE_PAIR_TABLE *pairs = domain_key_pairs ();
  assert (pairs != NULL && row >= 0 && row < pairs->n_keys);
  DOMAIN_COMPARE_KEY key;
  domain_compare_key_of_value (element, &key);
  const int column = pairs != NULL ? domain_key_pair_index (pairs, &key) : -1;
  return column >= 0 ? &pairs->pool[pairs->entry[1][row * pairs->n_keys + column]] : NULL;
}

/*
 * [리뷰] domain_compare_by_type_pair — 플랜이 키를 미리 알 수 없는 비교(컬렉션 원소, JSON 스칼라, 해시 그룹 키)의 공개 진입점으로,
 * object_primitive.c:mr_cmpval_json 과 set_object.c:col_element_compare 가 호출한다.
 * develop: develop 에서는 같은 두 호출부가 tp_value_compare_with_error 를 직접 불렀다(develop
 * src/object/object_primitive.c:15498 의 mr_cmpval_json, src/object/set_object.c:col_element_compare) — 즉 원소마다
 * 공통 도메인 판정을 반복했다.
 * 이 PR: 타입·콜레이션이 같은 쌍은 tp_value_compare_with_error 로 그대로 넘기고, NULL 규칙을 먼저 처리한 뒤 두 값의 키로 표의 칸을 찾아
 * domain_compare_values 로 비교한다. OBJECT 커널과 표가 없는 경우는 tp_value_compare_with_error 로 되돌아간다.
 * 바뀐 것: 신규 공개 함수(+73줄). 디버그 빌드에서 매 비교마다 tp_value_compare_with_error 와 결과·비교가능성·에러코드를 대조하는 교차검증 블록이 들어
 * 있다(릴리스에서는 빠진다).
 */
DB_VALUE_COMPARE_RESULT
domain_compare_by_type_pair (const DB_VALUE * value1, const DB_VALUE * value2, int do_coercion, int total_order,
			     bool * can_compare)
{
  const DB_TYPE type = DB_VALUE_DOMAIN_TYPE (value1);
  if (type == DB_VALUE_DOMAIN_TYPE (value2) && !TP_TYPE_HAS_COLLATION (type))
    {
      /* one type without a collation, a homogeneous collection's elements: tp_value_compare_with_error compares them
       * as they are, and resolves nothing */
      return tp_value_compare_with_error (value1, value2, do_coercion, total_order, can_compare);
    }
  if (can_compare != NULL)
    {
      *can_compare = true;
    }
  if (DB_IS_NULL (value1))
    {
      return DB_IS_NULL (value2) ? (total_order ? DB_EQ : DB_UNK) : (total_order ? DB_LT : DB_UNK);
    }
  if (DB_IS_NULL (value2))
    {
      return total_order ? DB_GT : DB_UNK;
    }
  DOMAIN_COMPARE_KEY key[2];
  domain_compare_key_of_value (value1, &key[0]);
  domain_compare_key_of_value (value2, &key[1]);
  if (key[0].type == key[1].type && key[0].collation == key[1].collation)
    {
      /* one type and one collation: tp_value_compare_with_error compares them as they are, and resolves nothing */
      return tp_value_compare_with_error (value1, value2, do_coercion, total_order, can_compare);
    }
  const DOMAIN_TYPE_PAIR_TABLE *pairs = domain_key_pairs ();
  const int row = pairs != NULL ? domain_key_pair_index (pairs, &key[0]) : -1;
  const int column = pairs != NULL ? domain_key_pair_index (pairs, &key[1]) : -1;
  if (row < 0 || column < 0)
    {
      /* every value of an element type has a key the table covers: the table is missing only when it could not be
       * made (no memory), and tp_value_compare_with_error answers */
      assert (pairs == NULL);
      return tp_value_compare_with_error (value1, value2, do_coercion, total_order, can_compare);
    }
  const DOMAIN_COMPARE *compare = &pairs->pool[pairs->entry[do_coercion ? 1 : 0][row * pairs->n_keys + column]];
  if (compare->method == DOMAIN_COMPARE_OBJECT)
    {
      /* an object side: tp_value_compare_with_error, which meets OIDs on the server */
      return tp_value_compare_with_error (value1, value2, do_coercion, total_order, can_compare);
    }
  const DB_VALUE_COMPARE_RESULT result = domain_compare_values (compare, value1, value2, total_order, can_compare);
#if !defined (NDEBUG)
  {
    /* debug cross-check (optdebug): tp_value_compare_with_error on the same values gives the table's result,
     * comparability and error */
    const bool comparable = can_compare != NULL ? *can_compare : true;
    const int error = comparable ? NO_ERROR : er_errid ();
    bool expected_comparable = true;
    bool *const expected_comparable_p = can_compare != NULL ? &expected_comparable : NULL;
    er_stack_push ();
    const DB_VALUE_COMPARE_RESULT expected =
      tp_value_compare_with_error (value1, value2, do_coercion, total_order, expected_comparable_p);
    const int expected_error = expected_comparable ? NO_ERROR : er_errid ();
    er_stack_pop ();
    if (expected != result || expected_comparable != comparable || expected_error != error)
      {
	fprintf (stderr, "key pair comparison: types %d/%d collations %d/%d coercion=%d kernel=%d result=%d/%d "
		 "comparable=%d/%d error=%d/%d\n", (int) key[0].type, (int) key[1].type, key[0].collation,
		 key[1].collation, do_coercion, (int) compare->method, (int) result, (int) expected, (int) comparable,
		 (int) expected_comparable, error, expected_error);
      }
    assert (expected == result && expected_comparable == comparable && expected_error == error);
  }
#endif
  return result;
}

/*
 * [리뷰] domain_search_key_compare — 인덱스 검색 키의 값 비교 본체로, btree.c:23268 과 scan_manager.c:1760 이 OWN/OTHER 래퍼를 통해
 * 호출한다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 에서는 scan_key_compare(src/query/scan_manager.c:1522)와 btree 비교가
 * 행마다 tp_value_compare_with_error 로 해석했다.
 * 이 PR: 두 값의 키가 같으면 tp_value_compare_with_error 로 그대로 가고, OTHER 인 경우만 표에서 칸을 찾아 domain_compare_values 로 비교한다.
 * 둘 다 색인되지 않으면 해석되지 않은 도메인으로 보고 assert 후 ER_QPROC_DOMAIN_UNRESOLVED 를 낸다.
 * 바뀐 것: 신규 공개 함수(+38줄). 실패 경로에서 `*can_compare = false` 를 NULL 검사 없이 쓴다 — 현재 호출부(pr_midxkey_compare_element 는
 * &comparable, scan_manager 는 &can_compare)는 모두 non-NULL 이라 지금은 안전하지만, 이 파일의 다른 함수들이 NULL 을 허용하는 것과 계약이 어긋난다.
 * [지적 C5-05]
 */
DB_VALUE_COMPARE_RESULT
domain_search_key_compare (DOMAIN_SEARCH_KEYS keys, int column, DB_VALUE * value1, DB_VALUE * value2,
			   int do_coercion, int total_order, bool * can_compare)
{
  DOMAIN_COMPARE_KEY key[2];
  domain_compare_key_of_value (value1, &key[0]);
  domain_compare_key_of_value (value2, &key[1]);
  if (domain_compare_key_equal (&key[0], &key[1]))
    {
      /* one type and one collation: nothing to coerce or merge (a kept column of the index column's type with other
       * parameters, whose precision or length alone differs) */
      return tp_value_compare_with_error (value1, value2, do_coercion, total_order, can_compare);
    }
  const DOMAIN_TYPE_PAIR_TABLE *pairs = keys == DOMAIN_SEARCH_KEYS_OTHER ? domain_key_pairs () : NULL;
  const int index[2] = {
    pairs != NULL ? domain_key_pair_index (pairs, &key[0]) : -1,
    pairs != NULL ? domain_key_pair_index (pairs, &key[1]) : -1
  };
  if (index[0] >= 0 && index[1] >= 0)
    {
      /* the table's keys take their collations' codesets, as the values an index scan compares have them */
      assert (!TP_TYPE_HAS_COLLATION (key[0].type) || key[0].codeset == lang_get_collation (key[0].collation)->codeset);
      assert (!TP_TYPE_HAS_COLLATION (key[1].type) || key[1].codeset == lang_get_collation (key[1].collation)->codeset);
      const DOMAIN_COMPARE *compare = &pairs->pool[pairs->entry[1][index[0] * pairs->n_keys + index[1]]];
      if (compare->method == DOMAIN_COMPARE_OBJECT)
	{
	  /* an object side: tp_value_compare_with_error, which meets OIDs on the server */
	  return tp_value_compare_with_error (value1, value2, do_coercion, total_order, can_compare);
	}
      return domain_compare_values (compare, value1, value2, total_order, can_compare);
    }
  /* the unresolved-domain check (execution): the plan knows whether a column's values take a key other than its own */
  assert (false);
  er_set (ER_ERROR_SEVERITY, ARG_FILE_LINE, ER_QPROC_DOMAIN_UNRESOLVED, 4, "execute", "", column,
	  pr_type_name (key[0].type));
  *can_compare = false;
  return DB_UNK;
}

/*
 * [리뷰] domain_search_key_compare_own — 모든 값이 자기 키 컬럼의 키를 갖는 스캔용 래퍼로, pr_midxkey_compare_resolved 에 함수 포인터로
 * 넘어간다(btree.c:23271).
 * develop: develop 에 없음 — 이 PR 이 신설. develop 의 pr_midxkey_compare_element 는 항상 tp_value_compare_with_error 를
 * 불렀다.
 * 이 PR: DOMAIN_SEARCH_KEYS_OWN 으로 domain_search_key_compare 를 호출한다 — 키가 같으면 값 비교, 다르면 해석 누락 보고.
 * 바뀐 것: 신규 공개 함수(+7줄).
 */
DB_VALUE_COMPARE_RESULT
domain_search_key_compare_own (int column, DB_VALUE * value1, DB_VALUE * value2, int do_coercion, int total_order,
			       bool * can_compare)
{
  return domain_search_key_compare (DOMAIN_SEARCH_KEYS_OWN, column, value1, value2, do_coercion, total_order,
				    can_compare);
}

/*
 * [리뷰] domain_search_key_compare_other — 키 컬럼이 자기 키와 다른 키의 값을 받는 스캔용 래퍼로, scan_manager.c:1754·1760 과
 * btree.c:23270 이 쓴다.
 * develop: develop 에 없음 — 이 PR 이 신설.
 * 이 PR: DOMAIN_SEARCH_KEYS_OTHER 로 domain_search_key_compare 를 호출해 타입 쌍 비교표의 칸으로 비교하게 한다.
 * 바뀐 것: 신규 공개 함수(+7줄).
 */
DB_VALUE_COMPARE_RESULT
domain_search_key_compare_other (int column, DB_VALUE * value1, DB_VALUE * value2, int do_coercion, int total_order,
				 bool * can_compare)
{
  return domain_search_key_compare (DOMAIN_SEARCH_KEYS_OTHER, column, value1, value2, do_coercion, total_order,
				    can_compare);
}

/*
 * [리뷰] domain_resolve — 이 파일의 단일 공개 관문으로, 플랜 적재(domain_plan.c:domain_resolve_node)와 실행 전
 * 해석(qexec_resolve_late_bind_node_over), string_opfunc.c:db_add_time 이 모두 여기로 들어와 컨텍스트별 규칙을 받는다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 에는 타입 규칙의 단일 진입점이 없었고 각 실행 함수가 자기 규칙을 가지고 있었다.
 * 이 PR: 먼저 값 타입도 도메인도 확정되지 않은 피연산자가 있으면 *needs_late_bind 를 세우고 즉시 반환하고, 그 다음 DOMAIN_CTX 별로
 * arith/compare/common_value/agg/analytic/func_arg/list_column 해석기로 보내며, ASSIGN·KEY_ELEM 은 소비자 도메인을 목표로 변환기만
 * 찾는다.
 * 바뀐 것: 신규 공개 함수(+58줄). "컴파일이 표시 → 로드가 플랜 도출 → 실행 전 게이트가 한 번에 결정" 의 결정 지점.
 */
int
domain_resolve (DOMAIN_CTX context, int opcode, const DOMAIN_OPERAND * operands, int n_operands,
		const TP_DOMAIN * consumer_domain, RESOLVED_DOMAIN * result, bool * needs_late_bind)
{
  assert (operands != NULL && n_operands > 0 && result != NULL && needs_late_bind != NULL);

  *needs_late_bind = false;
  for (int i = 0; i < n_operands; i++)
    {
      if (operands[i].val_type == DB_TYPE_NULL
	  && (operands[i].domain == NULL || TP_DOMAIN_TYPE (operands[i].domain) == DB_TYPE_VARIABLE))
	{
	  *needs_late_bind = true;
	  return NO_ERROR;
	}
    }

  *result = RESOLVED_DOMAIN
  {
  };

  switch (context)
    {
    case DOMAIN_CTX_ARITH:
      return domain_resolve_arith (opcode, operands, n_operands, result);

    case DOMAIN_CTX_COMPARE:
      assert (n_operands == 2);
      return domain_resolve_compare (operands, result);

    case DOMAIN_CTX_COMMON_VALUE:
      return domain_resolve_common_value (operands, n_operands, result);

    case DOMAIN_CTX_AGG:
      return domain_resolve_aggregate (opcode, consumer_domain, &operands[0], result);

    case DOMAIN_CTX_ANALYTIC:
      return domain_resolve_analytic (opcode, consumer_domain, &operands[0], result);

    case DOMAIN_CTX_FUNC_ARG:
      return domain_resolve_function (opcode, operands, n_operands, consumer_domain, result);

    case DOMAIN_CTX_ASSIGN:
    case DOMAIN_CTX_KEY_ELEM:
      /* the consumer (assignment target, index element) is the target */
      assert (consumer_domain != NULL);
      result->domain = result->operand_domain[0] = consumer_domain;
      result->conv[0] =
	tp_value_find_converter (domain_operand_type (&operands[0]), consumer_domain, domain_convert_mode (context));
      return NO_ERROR;

    case DOMAIN_CTX_LIST_COLUMN:
      return domain_resolve_list_column (operands, n_operands, result);
    }

  assert (false);
  return ER_FAILED;
}

/* MEDIAN/PERCENTILE: DOUBLE, then DATETIME, then TIME, as tp_value_cast (…, false) would. */
/*
 * [리뷰] domain_classify_interpolation — 값 하나를 보고 타입을 정해야 하는 인자(MEDIAN/PERCENTILE 인자, ADDTIME 좌변, STR_TO_DATE
 * 포맷)를 분류하는 블록의 첫 함수로, 공개 입구는 같은 블록의 domain_classify_value 이고 해석기가 domain_resolve 보다 먼저 한 번 부른다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 에서는 같은 분류가 집계 첫 값 처리와 db_add_time·db_str_to_date 안에서 행마다 일어났다.
 * 이 PR: 보간 함수 인자는 DOUBLE→DATETIME→TIME 순으로 실제 변환을 시도해 처음 성공한 타입을 주고, ADDTIME 좌변 문자열은 존이 있으면 DATETIMETZ·시간이면
 * VARCHAR, STR_TO_DATE 포맷은 공백 제거 후 db_check_time_date_format 의 지정자로 타입을 정한다. 어느 것도 아니면 DB_TYPE_NULL(함수 자신의
 * 에러).
 * 바뀐 것: 신규 블록(+315줄, 팩이 한 단위로 묶은 범위). 임시 DB_VALUE 와 db_private_alloc 버퍼를 쓰지만 같은 블록 안에서
 * pr_clear_value·db_private_free 로 짝이 맞는다(하네스 사실: alloc@2481 / free@2523).
 * [지적 C5-03]
 */
static DB_TYPE
domain_classify_interpolation (const DB_VALUE * value)
{
  static const DB_TYPE candidates[] = { DB_TYPE_DOUBLE, DB_TYPE_DATETIME, DB_TYPE_TIME };
  DB_TYPE type = DB_VALUE_DOMAIN_TYPE (value);

  if (domain_is_interpolation_type (type))
    {
      return type;
    }
for (DB_TYPE candidate:candidates)
    {
      const TP_DOMAIN *target = tp_domain_resolve_default (candidate);
      TP_VALUE_CONVERTER converter = tp_value_find_converter (type, target, DOMAIN_CONVERT_ASSIGN);
      if (converter == NULL)
	{
	  return candidate;
	}
      DB_VALUE converted;
      TP_DOMAIN_STATUS status = tp_value_convert (converter, target, value, &converted);
      pr_clear_value (&converted);
      if (status == DOMAIN_COMPATIBLE)
	{
	  return candidate;
	}
    }
  return DB_TYPE_NULL;
}

/* ADDTIME left string: DATETIMETZ with a zone, VARCHAR otherwise; not a time/date string → DB_TYPE_NULL. */
static DB_TYPE
domain_classify_addtime (const DB_VALUE * value)
{
  if (!TP_IS_CHAR_TYPE (DB_VALUE_DOMAIN_TYPE (value)))
    {
      return DB_VALUE_DOMAIN_TYPE (value);
    }

  const char *str = db_get_string (value);
  int size = db_get_string_size (value);
  date_conversion_error date_error;
  DB_DATETIMETZ datetimetz;
  bool has_zone = false;

  if (db_string_to_datetimetz_ex_core (str, size, &datetimetz, &has_zone, &date_error) == NO_ERROR && has_zone)
    {
      return DB_TYPE_DATETIMETZ;
    }

  DB_TIME time;
  int millisecond;
  if (db_date_parse_time_core (str, size, &time, &millisecond, &date_error) == NO_ERROR)
    {
      return DB_TYPE_VARCHAR;
    }

  DB_DATETIME datetime;
  bool has_explicit_time = false;
  if (db_date_parse_datetime_parts_core (str, size, &datetime, &has_explicit_time, NULL, NULL, NULL,
					 &date_error) != NO_ERROR)
    {
      return DB_TYPE_NULL;
    }
  return has_zone ? DB_TYPE_DATETIMETZ : DB_TYPE_VARCHAR;
}

/* STR_TO_DATE format: the specifiers left after removing white space resolve the result type. */
static DB_TYPE
domain_classify_str_to_date_format (const DB_VALUE * value)
{
  if (!TP_IS_CHAR_TYPE (DB_VALUE_DOMAIN_TYPE (value)))
    {
      return DB_TYPE_NULL;
    }

  const char *format = db_get_string (value);
  int length = db_get_string_size (value);
  length = length < 0 ? (int) strlen (format) : length;

  char *compact = (char *) db_private_alloc (NULL, length + 1);
  if (compact == NULL)
    {
      return DB_TYPE_NULL;
    }
  int k = 0;
  bool is_valid = true;
  for (int i = 0; i < length && is_valid; i++)
    {
      if (!char_isspace2 (format[i]))
	{
	  compact[k++] = format[i];
	}
      else if (i > 0 && format[i - 1] == '%')
	{
	  /* '%' without format specifier */
	  is_valid = false;
	}
    }
  compact[k] = '\0';

  DB_TYPE type = DB_TYPE_NULL;
  if (is_valid)
    {
      switch (db_check_time_date_format (compact))
	{
	case TIME_SPECIFIER:
	  type = DB_TYPE_TIME;
	  break;
	case DATE_SPECIFIER:
	  type = DB_TYPE_DATE;
	  break;
	case DATETIME_SPECIFIER:
	  type = DB_TYPE_DATETIME;
	  break;
	case DATETIMETZ_SPECIFIER:
	  type = DB_TYPE_DATETIMETZ;
	  break;
	default:
	  break;
	}
    }
  db_private_free (NULL, compact);
  return type;
}

DB_TYPE
domain_classify_value (DOMAIN_CTX context, int opcode, int arg_index, const DB_VALUE * value)
{
  assert (value != NULL && !DB_IS_NULL (value));

  if ((context == DOMAIN_CTX_AGG || context == DOMAIN_CTX_ANALYTIC) && arg_index == 0
      && (opcode == PT_MEDIAN || opcode == PT_PERCENTILE_CONT || opcode == PT_PERCENTILE_DISC))
    {
      /* an analytic interpolation function types its first value as the aggregate does */
      return domain_classify_interpolation (value);
    }
  if (context == DOMAIN_CTX_FUNC_ARG && opcode == T_ADDTIME && arg_index == 0)
    {
      return domain_classify_addtime (value);
    }
  if (context == DOMAIN_CTX_FUNC_ARG && opcode == T_STR_TO_DATE && arg_index == 1)
    {
      return domain_classify_str_to_date_format (value);
    }
  return DB_VALUE_DOMAIN_TYPE (value);
}

/*
 * the character results of compiled nodes whose collation the compiler left to the values (LEAVE) or enforced
 * over an operand it could not type (ENFORCE). Each rule is what the operator gives its value at execution
 * (string_opfunc.c, tp_value_cast_internal); resolve_domains applies it once to the operands' resolved domains, as
 * tp_domain_resolve_value would read the value.
 */

/* A variable string or bit string at floating precision reads as its maximum (tp_domain_resolve_value). */
static const TP_DOMAIN *
domain_variable_string_value (const TP_DOMAIN * domain)
{
  if (domain == NULL)
    {
      return NULL;
    }
  const bool floating = domain->precision == 0 || domain->precision == TP_FLOATING_PRECISION_VALUE;
  if (TP_DOMAIN_TYPE (domain) == DB_TYPE_VARCHAR && (floating || domain->precision > DB_MAX_VARCHAR_PRECISION))
    {
      return domain_character_domain (DB_TYPE_VARCHAR, DB_MAX_VARCHAR_PRECISION, domain->collation_id);
    }
  if (TP_DOMAIN_TYPE (domain) == DB_TYPE_VARBIT && (floating || domain->precision > DB_MAX_VARBIT_PRECISION))
    {
      return domain_character_domain (DB_TYPE_VARBIT, DB_MAX_VARBIT_PRECISION, 0);
    }
  return domain;
}

const TP_DOMAIN *
domain_as_value_domain (const TP_DOMAIN * domain)
{
  if (domain != NULL && TP_DOMAIN_TYPE (domain) == DB_TYPE_ENUMERATION)
    {
      /* a value carries no element list (tp_domain_resolve_value) */
      return tp_domain_resolve_default (DB_TYPE_ENUMERATION);
    }
  return domain_variable_string_value (domain);
}

/* Where an operator's result takes its collation (and codeset) from. */
enum DOMAIN_CHAR_SOURCE
{
  DOMAIN_CHAR_MERGE,		/* LANG_RT_COMMON_COLL over every character operand in operand order
				 * (db_string_concatenate, db_string_pad, db_string_replace) */
  DOMAIN_CHAR_FIRST,		/* the first character operand: the string being cut, cased, trimmed, reversed,
				 * translated, repeated, hashed or bounded keeps its codeset and collation */
  DOMAIN_CHAR_FORMAT,		/* the format argument, the second operand (db_date_format, db_time_format) */
  DOMAIN_CHAR_SYSTEM,		/* LANG_SYS: a string the operator makes itself (db_make_string, LANG_COERCIBLE_COLL) */
  DOMAIN_CHAR_BRANCH,		/* one operand's value, chosen per row (IF, CASE, DECODE, ELT) */
  DOMAIN_CHAR_FIRST_BINARY	/* the binary collation of the first character operand's codeset (db_from_unixtime) */
};

/* The precision the value takes. */
enum DOMAIN_CHAR_PRECISION
{
  DOMAIN_PREC_FLOATING,		/* the value's own length: floating */
  DOMAIN_PREC_SOURCE,		/* the first character operand's (db_string_substring, db_string_trim,
				 * db_string_reverse) */
  DOMAIN_PREC_SUM,		/* the character operands' added, floating if one is (db_string_concatenate) */
  DOMAIN_PREC_COMPILED,		/* the compiled one (MD5 and SHA1 give CHAR of the digest length, UUID_FORMAT 36) */
  DOMAIN_PREC_CHAR_SOURCE	/* a fixed CHAR source's, else floating */
};

struct DOMAIN_CHAR_RULE
{
  DB_TYPE type;			/* DB_TYPE_NULL: the first character operand's type (UPPER, LOWER keep CHAR) */
  unsigned char source;		/* DOMAIN_CHAR_SOURCE */
  unsigned char precision;	/* DOMAIN_CHAR_PRECISION */
};

/* The rule of a character operator; an operator not listed makes a string from its character operands, merged. */
/* *INDENT-OFF* */
static DOMAIN_CHAR_RULE
domain_character_rule (int opcode)
{
  switch (opcode)
    {
    case T_CONCAT:
    case T_STRCAT:
      return DOMAIN_CHAR_RULE { DB_TYPE_VARCHAR, DOMAIN_CHAR_MERGE, DOMAIN_PREC_SUM };
    case T_SUBSTRING:
    case T_MID:
    case T_LEFT:
    case T_RIGHT:
    case T_TRIM:
    case T_LTRIM:
    case T_RTRIM:
    case T_REVERSE:
      return DOMAIN_CHAR_RULE { DB_TYPE_VARCHAR, DOMAIN_CHAR_FIRST, DOMAIN_PREC_SOURCE };
    case T_UPPER:
    case T_LOWER:
      /* db_string_upper/lower keep the string's type; a fixed CHAR keeps its length (the count of the cased
       * characters), anything else its own length */
      return DOMAIN_CHAR_RULE { DB_TYPE_NULL, DOMAIN_CHAR_FIRST, DOMAIN_PREC_CHAR_SOURCE };
    case T_TRANSLATE:
      /* db_string_translate makes the result in the source string's codeset and collation */
      return DOMAIN_CHAR_RULE { DB_TYPE_VARCHAR, DOMAIN_CHAR_FIRST, DOMAIN_PREC_FLOATING };
    case T_UUID_FORMAT:
      return DOMAIN_CHAR_RULE { DB_TYPE_VARCHAR, DOMAIN_CHAR_FIRST, DOMAIN_PREC_COMPILED };
    case T_REPEAT:
    case T_LIKE_LOWER_BOUND:
    case T_LIKE_UPPER_BOUND:
    case T_SHA_TWO:
    case T_AES_ENCRYPT:
    case T_AES_DECRYPT:
    case T_TO_BASE64:
    case T_FROM_BASE64:
    case F_REGEXP_REPLACE:
    case F_REGEXP_SUBSTR:
      return DOMAIN_CHAR_RULE { DB_TYPE_VARCHAR, DOMAIN_CHAR_FIRST, DOMAIN_PREC_FLOATING };
    case T_MD5:
    case T_SHA_ONE:
      return DOMAIN_CHAR_RULE { DB_TYPE_CHAR, DOMAIN_CHAR_FIRST, DOMAIN_PREC_COMPILED };
    case T_DATE_FORMAT:
    case T_TIME_FORMAT:
      return DOMAIN_CHAR_RULE { DB_TYPE_VARCHAR, DOMAIN_CHAR_FORMAT, DOMAIN_PREC_FLOATING };
    case T_SPACE:
    case T_TZ_OFFSET:
    case T_DATE_ADD:
    case T_DATE_SUB:
    case T_ADDDATE:
    case T_SUBDATE:
    case T_DATE:
    case T_TIME:
      return DOMAIN_CHAR_RULE { DB_TYPE_VARCHAR, DOMAIN_CHAR_SYSTEM, DOMAIN_PREC_FLOATING };
    case T_FROM_UNIXTIME:
      return DOMAIN_CHAR_RULE { DB_TYPE_VARCHAR, DOMAIN_CHAR_FIRST_BINARY, DOMAIN_PREC_FLOATING };
    case T_IF:
    case T_CASE:
    case T_DECODE:
    case T_PRIOR:
    case T_CONNECT_BY_ROOT:
    case T_QPRIOR:
    case F_ELT:
      return DOMAIN_CHAR_RULE { DB_TYPE_NULL, DOMAIN_CHAR_BRANCH, DOMAIN_PREC_SOURCE };
    default:
      return DOMAIN_CHAR_RULE { DB_TYPE_VARCHAR, DOMAIN_CHAR_MERGE, DOMAIN_PREC_FLOATING };
    }
}
/* *INDENT-ON* */

/* The character operands' collation, merged as the string operators merge their argument values: operands without
 * a collation (NULL, a number, a date) take no part. return: false when two do not merge; *collation_id is -1 when no
 * operand has a collation. */
static bool
domain_merge_collations (const DOMAIN_OPERAND * operands, int n_operands, int *collation_id)
{
  int merged = -1;
  for (int i = 0; i < n_operands; i++)
    {
      const TP_DOMAIN *domain = domain_operand_domain (&operands[i]);
      if (domain == NULL || !TP_TYPE_HAS_COLLATION (TP_DOMAIN_TYPE (domain)))
	{
	  continue;
	}
      int common = domain->collation_id;
      if (merged >= 0)
	{
	  LANG_RT_COMMON_COLL (merged, domain->collation_id, common);
	  if (common == -1)
	    {
	      return false;
	    }
	}
      merged = common;
    }
  *collation_id = merged;
  return true;
}

/* The first operand that has a collation, or NULL. */
/*
 * [리뷰] domain_first_character_operand — 문자 결과 규칙에서 "첫 번째 콜레이션을 가진 피연산자" 를 찾아 주는 보조로, domain_character_result 와
 * domain_resolve_branch_merge 가 타입·정밀도·콜레이션의 출처로 쓴다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 에서는 각 문자열 연산자가 행에서 자기 인자 값의 콜레이션을 직접 읽었다.
 * 이 PR: 피연산자를 순서대로 보며 TP_TYPE_HAS_COLLATION 인 첫 도메인을 돌려주고, 없으면 NULL.
 * 바뀐 것: 신규 함수(+13줄).
 */
static const TP_DOMAIN *
domain_first_character_operand (const DOMAIN_OPERAND * operands, int n_operands)
{
  for (int i = 0; i < n_operands; i++)
    {
      const TP_DOMAIN *domain = domain_operand_domain (&operands[i]);
      if (domain != NULL && TP_TYPE_HAS_COLLATION (TP_DOMAIN_TYPE (domain)))
	{
	  return domain;
	}
    }
  return NULL;
}

/* CAST, CAST_WRAP, CAST_NOFAIL to a character target: tp_value_cast_internal. ENFORCE keeps a character
 * source's type and precision under the target's collation, and leaves any other value as it is; LEAVE makes the
 * target type and precision under a character source's collation, or the target's own for any other source. */
/*
 * [리뷰] domain_character_cast — CAST/CAST_WRAP/CAST_NOFAIL 이 문자 대상일 때 결과 도메인을 정해, domain_character_result 가
 * LEAVE/ENFORCE 두 표시를 각각 처리하게 한다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 에서는 tp_value_cast_internal 이 행마다 값의 codeset·콜레이션을 보고 같은 결정을 했다.
 * 이 PR: ENFORCE 면 문자 소스가 아닐 때 소스 도메인을 그대로 두고, codeset 이 다르면 대상 타입·정밀도로, 같으면 소스 타입·정밀도에 대상 콜레이션만 얹는다. LEAVE 면
 * 대상 타입·정밀도에 (문자 소스면) 소스 콜레이션을 얹는다.
 * 바뀐 것: 신규 함수(+23줄). ENFORCE 의 codeset 재인코딩 경로가 CTP _07_session_var 사례와 함께 주석에 근거로 적혀 있다.
 */
static const TP_DOMAIN *
domain_character_cast (const DOMAIN_OPERAND * source, const TP_DOMAIN * compiled)
{
  const TP_DOMAIN *from = domain_operand_domain (source);
  const bool char_source = from != NULL && TP_IS_CHAR_TYPE (TP_DOMAIN_TYPE (from));
  if (TP_DOMAIN_COLLATION_FLAG (compiled) == TP_DOMAIN_COLL_ENFORCE)
    {
      if (!char_source)
	{
	  return from;
	}
      if (from->codeset != compiled->codeset)
	{
	  /* a string recoded into the target codeset comes out in the target type (CTP _07_session_var: an
	   * iso88591 or binary CHAR bind cast to a utf8 VARCHAR) */
	  return domain_character_domain (TP_DOMAIN_TYPE (compiled), compiled->precision, compiled->collation_id);
	}
      return domain_character_domain (TP_DOMAIN_TYPE (from), from->precision, compiled->collation_id);
    }
  /* neither the domain cache nor a string conversion reads a string domain's scale */
  return domain_character_domain (TP_DOMAIN_TYPE (compiled), compiled->precision,
				  char_source ? from->collation_id : compiled->collation_id);
}

/* The character result of opcode over the operands' resolved domains; compiled is the node's compiled domain (NULL
 * for a late-binding node: the rule's type and precision). */
/*
 * [리뷰] domain_character_result — 컴파일러가 콜레이션을 값에 맡긴(LEAVE) 또는 피연산자에 강제한(ENFORCE) 문자 결과 노드의 도메인을 정하는 본체로,
 * domain_resolve_character 와 domain_resolve_arith(plus-as-concat)가 부른다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 에서는 string_opfunc.c 의 각 연산자가 행마다 인자 값의 콜레이션을 병합하고 결과 문자열을 만들었다.
 * 이 PR: CAST 계열은 domain_character_cast, TO_CHAR 와 GROUP_CONCAT 은 전용 규칙으로 처리하고, 나머지는 domain_character_rule 의
 * (출처, 정밀도) 규칙표대로 MERGE/FIRST/FORMAT/SYSTEM/BRANCH/FIRST_BINARY 중 하나로 콜레이션을,
 * FLOATING/SOURCE/SUM/COMPILED/CHAR_SOURCE 중 하나로 정밀도를 정한다. 병합 실패는 ER_QSTR_INCOMPATIBLE_COLLATIONS, 분기 도메인이 서로
 * 다르면 ER_QPROC_DOMAIN_UNRESOLVED 로 분기 해석(branch_pick/merge)에 넘긴다.
 * 바뀐 것: 신규 함수(+153줄). 문자열 연산자별 콜레이션·정밀도 규칙이 처음으로 한 표에 모인 자리.
 */
static int
domain_character_result (int opcode, const DOMAIN_OPERAND * operands, int n_operands, const TP_DOMAIN * compiled,
			 RESOLVED_DOMAIN * result)
{
  const TP_DOMAIN *domain = NULL;
  if (compiled != NULL && (opcode == T_CAST || opcode == T_CAST_WRAP || opcode == T_CAST_NOFAIL))
    {
      domain = n_operands > 0 ? domain_character_cast (&operands[n_operands - 1], compiled) : NULL;
    }
  else if (compiled != NULL && opcode == T_TO_CHAR)
    {
      /* db_to_char over the node's compiled domain: a string is coerced to it, keeping its collation
       * (LEAVE); a number or a date prints into the compiled domain's codeset and collation */
      const TP_DOMAIN *value = n_operands > 0 ? domain_operand_domain (&operands[0]) : NULL;
      if (value != NULL && TP_IS_CHAR_TYPE (TP_DOMAIN_TYPE (value)))
	{
	  domain = domain_character_domain (TP_DOMAIN_TYPE (compiled), compiled->precision, value->collation_id);
	}
      else
	{
	  domain = domain_character_domain (DB_TYPE_VARCHAR, DB_MAX_VARCHAR_PRECISION, compiled->collation_id);
	}
    }
  else if (compiled != NULL && opcode == PT_GROUP_CONCAT)
    {
      /* a reader of a GROUP_CONCAT accumulator: qdata_group_concat_first_value makes the accumulator in its
       * compiled string type under the function domain's codeset and collation, of its own length; a function the
       * resolve_domains saw no value for gives no value */
      const TP_DOMAIN *function = n_operands > 0 ? domain_operand_domain (&operands[0]) : NULL;
      if (function == NULL || !TP_TYPE_HAS_COLLATION (TP_DOMAIN_TYPE (function)))
	{
	  result->domain = &tp_Null_domain;
	  return NO_ERROR;
	}
      domain = domain_character_domain (TP_DOMAIN_TYPE (compiled), TP_FLOATING_PRECISION_VALUE, function->collation_id);
    }
  else
    {
      const DOMAIN_CHAR_RULE rule = domain_character_rule (opcode);
      const TP_DOMAIN *first = domain_first_character_operand (operands, n_operands);
      int collation_id = -1;
      switch (rule.source)
	{
	case DOMAIN_CHAR_MERGE:
	  if (!domain_merge_collations (operands, n_operands, &collation_id))
	    {
	      return ER_QSTR_INCOMPATIBLE_COLLATIONS;
	    }
	  break;
	case DOMAIN_CHAR_FIRST:
	  collation_id = first != NULL ? first->collation_id : -1;
	  break;
	case DOMAIN_CHAR_FORMAT:
	  {
	    const TP_DOMAIN *format = n_operands > 1 ? domain_operand_domain (&operands[1]) : NULL;
	    collation_id = format != NULL && TP_TYPE_HAS_COLLATION (TP_DOMAIN_TYPE (format))
	      ? format->collation_id : -1;
	  }
	  break;
	case DOMAIN_CHAR_SYSTEM:
	  collation_id = LANG_SYS_COLLATION;
	  break;
	case DOMAIN_CHAR_FIRST_BINARY:
	  collation_id = first != NULL ? LANG_GET_BINARY_COLLATION (first->codeset) : -1;
	  break;
	case DOMAIN_CHAR_BRANCH:
	  {
	    /* the row takes one branch's value: one domain for every character branch, or the row resolves */
	    const TP_DOMAIN *branch = NULL;
	    for (int i = 0; i < n_operands; i++)
	      {
		const TP_DOMAIN *d = domain_as_value_domain (domain_operand_domain (&operands[i]));
		if (d == NULL || !TP_TYPE_HAS_COLLATION (TP_DOMAIN_TYPE (d)))
		  {
		    continue;
		  }
		if (branch != NULL && branch != d)
		  {
		    return ER_QPROC_DOMAIN_UNRESOLVED;
		  }
		branch = d;
	      }
	    if (branch == NULL)
	      {
		result->domain = &tp_Null_domain;
		return NO_ERROR;
	      }
	    result->domain = branch;
	    return NO_ERROR;
	  }
	}
      if (collation_id < 0)
	{
	  /* no operand carries a collation: the value is NULL (the operators return NULL for NULL arguments) */
	  result->domain = &tp_Null_domain;
	  return NO_ERROR;
	}

      DB_TYPE type = rule.type;
      if (type == DB_TYPE_NULL)
	{
	  type = first != NULL && TP_IS_CHAR_TYPE (TP_DOMAIN_TYPE (first)) ? TP_DOMAIN_TYPE (first) : DB_TYPE_VARCHAR;
	}
      int precision = TP_FLOATING_PRECISION_VALUE;
      switch (rule.precision)
	{
	case DOMAIN_PREC_SOURCE:
	  precision = first != NULL ? first->precision : TP_FLOATING_PRECISION_VALUE;
	  break;
	case DOMAIN_PREC_SUM:
	  precision = 0;
	  for (int i = 0; i < n_operands; i++)
	    {
	      const TP_DOMAIN *d = domain_operand_domain (&operands[i]);
	      if (d == NULL || !TP_TYPE_HAS_COLLATION (TP_DOMAIN_TYPE (d)))
		{
		  continue;
		}
	      if (d->precision == TP_FLOATING_PRECISION_VALUE || precision == TP_FLOATING_PRECISION_VALUE
		  || TP_DOMAIN_TYPE (d) == DB_TYPE_ENUMERATION)
		{
		  precision = TP_FLOATING_PRECISION_VALUE;
		}
	      else
		{
		  precision = (int) MIN ((INT64) DB_MAX_VARCHAR_PRECISION, (INT64) precision + d->precision);
		}
	    }
	  break;
	case DOMAIN_PREC_COMPILED:
	  precision = compiled != NULL ? compiled->precision : TP_FLOATING_PRECISION_VALUE;
	  break;
	case DOMAIN_PREC_CHAR_SOURCE:
	  precision = first != NULL && TP_DOMAIN_TYPE (first) == DB_TYPE_CHAR ? first->precision
	    : TP_FLOATING_PRECISION_VALUE;
	  break;
	default:
	  break;
	}
      if (type == DB_TYPE_CHAR && precision == 0)
	{
	  precision = TP_FLOATING_PRECISION_VALUE;
	}
      domain = domain_character_domain (type, precision, collation_id);
    }

  if (domain == NULL)
    {
      return ER_OUT_OF_VIRTUAL_MEMORY;
    }
  result->domain = domain_as_value_domain (domain);
  return NO_ERROR;
}

/*
 * [리뷰] domain_resolve_character — qexec_resolve_late_bind_node_over 가 부르는 공개 입구로, 컴파일 도메인이 LEAVE/ENFORCE 로 표시된
 * 문자 노드의 결과 도메인을 실행 전에 확정한다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 에서는 콜레이션이 행마다 값에서 결정됐다.
 * 이 PR: compiled 가 콜레이션 타입이고 플래그가 NORMAL 이 아님을 assert 로 전제한 뒤 RESOLVED_DOMAIN 을 비우고 피연산자 도메인을 복사한 다음
 * domain_character_result 로 위임한다.
 * 바뀐 것: 신규 공개 함수(+16줄). GATE 슬롯 표시를 전제 조건(assert)으로 못 박았다.
 */
int
domain_resolve_character (int opcode, const DOMAIN_OPERAND * operands, int n_operands, const TP_DOMAIN * compiled,
			  RESOLVED_DOMAIN * result)
{
  assert (compiled != NULL && TP_TYPE_HAS_COLLATION (TP_DOMAIN_TYPE (compiled)));
  assert (TP_DOMAIN_COLLATION_FLAG (compiled) != TP_DOMAIN_COLL_NORMAL);

  *result = RESOLVED_DOMAIN
  {
  };
  for (int i = 0; i < n_operands && i < 3; i++)
    {
      result->operand_domain[i] = operands[i].domain;
    }
  return domain_character_result (opcode, operands, n_operands, compiled, result);
}

/*
 * [리뷰] domain_resolve_branch_pick — ELT 처럼 행이 고른 한 분기의 값을 결과로 쓰는 노드에서, 해석 시점에 읽은 분기 번호로 그 분기의 도메인을 돌려주는 공개 함수.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 의 qdata_elt 는 행마다 고른 값의 도메인을 그대로 썼다.
 * 이 PR: branch 가 1..n_operands-1 범위이고 그 분기가 콜레이션 있는 값 도메인을 가질 때 그것을, 아니면 tp_Null_domain 을 결과로 둔다(모든 행이 NULL).
 * 바뀐 것: 신규 공개 함수(+12줄). 피연산자 0 이 인덱스라는 규약 때문에 branch > 0 이 조건에 들어 있다.
 */
int
domain_resolve_branch_pick (const DOMAIN_OPERAND * operands, int n_operands, int branch, RESOLVED_DOMAIN * result)
{
  *result = RESOLVED_DOMAIN
  {
  };
  const TP_DOMAIN *domain = branch > 0 && branch < n_operands
    ? domain_as_value_domain (domain_operand_domain (&operands[branch])) : NULL;
  /* no branch, or a branch without a string value (a NULL bind): every row gives NULL (qdata_elt) */
  result->domain = domain != NULL && TP_TYPE_HAS_COLLATION (TP_DOMAIN_TYPE (domain)) ? domain : &tp_Null_domain;
  return NO_ERROR;
}

/*
 * [리뷰] domain_resolve_branch_merge — 분기들의 문자열 도메인이 서로 달라 한 분기를 고를 수 없을 때, 콜레이션을 병합한 하나의 결과 도메인과 그 도메인으로 값을 가져올
 * 변환기 둘을 돌려주는 공개 함수.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 에서는 분기 값이 행에서 그대로 결과가 됐고 콜레이션 충돌도 행에서 드러났다.
 * 이 PR: domain_merge_collations 로 전 분기를 병합해 실패하면 ER_QSTR_INCOMPATIBLE_COLLATIONS 를 실행 전에 내고, 성공하면 첫 문자 피연산자가
 * CHAR 인지에 따라 CHAR/VARCHAR 부동 정밀도 도메인을 만들어 conv[0](VARCHAR 값용)·conv[1](CHAR 값용)을 채운다.
 * 바뀐 것: 신규 공개 함수(+29줄). conv[0]/conv[1] 이 피연산자 순서가 아니라 "값의 타입" 을 뜻하는 예외적 쓰임이라 헤더 주석에 따로 적혀 있다.
 */
int
domain_resolve_branch_merge (const DOMAIN_OPERAND * operands, int n_operands, RESOLVED_DOMAIN * result)
{
  *result = RESOLVED_DOMAIN
  {
  };
  int collation_id = -1;
  if (!domain_merge_collations (operands, n_operands, &collation_id))
    {
      return ER_QSTR_INCOMPATIBLE_COLLATIONS;
    }
  if (collation_id < 0)
    {
      result->domain = &tp_Null_domain;
      return NO_ERROR;
    }
  /* the branches' string type (the compiler casts every branch to it) of the value's own length */
  const TP_DOMAIN *first = domain_first_character_operand (operands, n_operands);
  const DB_TYPE type = first != NULL && TP_DOMAIN_TYPE (first) == DB_TYPE_CHAR ? DB_TYPE_CHAR : DB_TYPE_VARCHAR;
  const TP_DOMAIN *domain = domain_character_domain (type, TP_FLOATING_PRECISION_VALUE, collation_id);
  if (domain == NULL)
    {
      return ER_OUT_OF_VIRTUAL_MEMORY;
    }
  result->domain = domain_as_value_domain (domain);
  result->conv[0] = tp_value_find_converter (DB_TYPE_VARCHAR, result->domain, DOMAIN_CONVERT_ASSIGN);
  result->conv[1] = tp_value_find_converter (DB_TYPE_CHAR, result->domain, DOMAIN_CONVERT_ASSIGN);
  return NO_ERROR;
}
