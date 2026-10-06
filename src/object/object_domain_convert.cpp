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
 * object_domain_convert.cpp - the value converters: one function per pair of a value's type and a target
 *                             domain's type, and the switch that finds a pair's converter
 */

#include "config.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <float.h>
#include <math.h>
#include <errno.h>
#include <assert.h>

#include "object_domain.h"
#include "object_domain_convert.h"
#include "db_date_status.h"
#include <utility>
#include "object_primitive.h"
#include "object_representation.h"
#include "numeric_opfunc.h"
#include "tz_support.h"
#include "db_date.h"
#include "mprec.h"
#include "porting_inline.hpp"
#include "set_object.h"
#include "string_opfunc.h"
#include "chartype.h"
#include "db_json.hpp"
#include "string_buffer.hpp"
#include "db_value_printer.hpp"

#if !defined (SERVER_MODE)
#include "work_space.h"
#include "virtual_object.h"
#include "schema_manager.h"
#include "locator_cl.h"
#include "object_template.h"
#include "dbi.h"
#endif /* !defined (SERVER_MODE) */

#include "dbtype.h"
#include "error_manager.h"
// XXX: SHOULD BE THE LAST INCLUDE HEADER
#include "memory_wrapper.hpp"

#if defined (SUPPRESS_STRLEN_WARNING)
#define strlen(s1)  ((int) strlen(s1))
#endif /* defined (SUPPRESS_STRLEN_WARNING) */

#define DBL_MAX_DIGITS    ((int)ceil(DBL_MAX_EXP * log10((double) FLT_RADIX)))
#define DB_DATETIMETZ_INITIALIZER { {0, 0}, 0 }
#define ROUND(x)		  ((x) > 0 ? ((x) + .5) : ((x) - .5))
#define SECONDS_IN_A_DAY	  (long)(86400)	/* 24L * 60L * 60L */

/* Numeric converters share the legacy formulas; source, destination and mode are compile-time parameters. */
template <DB_TYPE TYPE> struct tp_numeric_value;

template <> struct tp_numeric_value<DB_TYPE_SHORT>
{
  static auto get (const DB_VALUE *value)
  {
    return db_get_short (value);
  }
  static void make (DB_VALUE *value, short number)
  {
    db_make_short (value, number);
  }
};
template <> struct tp_numeric_value<DB_TYPE_INTEGER>
{
  static auto get (const DB_VALUE *value)
  {
    return db_get_int (value);
  }
  static void make (DB_VALUE *value, int number)
  {
    db_make_int (value, number);
  }
};
template <> struct tp_numeric_value<DB_TYPE_BIGINT>
{
  static auto get (const DB_VALUE *value)
  {
    return db_get_bigint (value);
  }
  static void make (DB_VALUE *value, DB_BIGINT number)
  {
    db_make_bigint (value, number);
  }
};
template <> struct tp_numeric_value<DB_TYPE_FLOAT>
{
  static auto get (const DB_VALUE *value)
  {
    return db_get_float (value);
  }
  static void make (DB_VALUE *value, float number)
  {
    db_make_float (value, number);
  }
};
template <> struct tp_numeric_value<DB_TYPE_DOUBLE>
{
  static auto get (const DB_VALUE *value)
  {
    return db_get_double (value);
  }
  static void make (DB_VALUE *value, double number)
  {
    db_make_double (value, number);
  }
};
template <> struct tp_numeric_value<DB_TYPE_MONETARY>
{
  /*
   * [리뷰] get — tp_numeric_value<DB_TYPE_MONETARY> 특수화의 읽기 훅 — DB_VALUE 에서 MONETARY 금액(double)만 꺼내 준다. 숫자 변환 템플릿이
   * 소스 타입을 컴파일 타임에 고를 때 쓴다.
   * develop: develop 에 없음 — 이 PR 이 신설. develop 은 MONETARY 분기마다 `db_get_monetary (src)->amount` 를 그 자리에 적었다.
   * 이 PR: db_get_monetary(value)->amount 를 돌려준다. SHORT/INTEGER/BIGINT/FLOAT/DOUBLE 특수화도 같은 모양의 get 을 갖는다.
   * 바뀐 것: 트레이트 구조체의 1줄 접근자 신설(+4줄). 타입별 getter 선택이 런타임 switch 에서 컴파일 타임 특수화로 옮겨졌다.
   */
  static auto get (const DB_VALUE *value)
  {
    return db_get_monetary (value)->amount;
  }
  /*
   * [리뷰] make — tp_numeric_value<DB_TYPE_MONETARY> 특수화의 쓰기 훅 — 변환 결과 double 을 MONETARY 로 target 에 담는다. 통화는
   * DB_CURRENCY_DEFAULT 고정.
   * develop: develop 에 없음 — 이 PR 이 신설. develop 은 각 분기에서 db_make_monetary (target, DB_CURRENCY_DEFAULT, …) 를 직접
   * 불렀다(예: object_domain.c:7913).
   * 이 PR: db_make_monetary(value, DB_CURRENCY_DEFAULT, number) 한 줄.
   * 바뀐 것: 트레이트 구조체의 1줄 생성자 신설(+4줄). 통화 기본값은 develop 과 같다.
   */
  static void make (DB_VALUE *value, double number)
  {
    db_make_monetary (value, DB_CURRENCY_DEFAULT, number);
  }
};

template <DB_TYPE DST, typename T>
/*
 * [리뷰] tp_numeric_overflow — 숫자 변환 템플릿의 범위 검사 훅 — 목적 타입 DST 에 맞는 OR_CHECK_*_OVERFLOW 를 컴파일 타임에 골라 준다.
 * tp_value_convert_number 가 값을 담기 전에 부른다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 은 목적 타입별 case 안에 OR_CHECK_SHORT/INT/BIGINT/FLOAT_OVERFLOW 를 직접
 * 적었다(object_domain.c:7396·7510·7650·7725).
 * 이 PR: if constexpr 사슬로 SHORT/INTEGER/BIGINT/FLOAT 는 각 매크로를, DOUBLE·MONETARY 는 static_assert 로 '범위 검사 없음'을 못
 * 박고 false 를 돌려준다.
 * 바뀐 것: 타입별 매크로 선택을 constexpr 분기로 묶은 템플릿 신설(+25줄). 새 숫자 타입이 들어오면 static_assert 가 빌드에서 잡는다.
 */
static bool
tp_numeric_overflow (T number)
{
  if constexpr (DST == DB_TYPE_SHORT)
    {
      return OR_CHECK_SHORT_OVERFLOW (number);
    }
  else if constexpr (DST == DB_TYPE_INTEGER)
    {
      return OR_CHECK_INT_OVERFLOW (number);
    }
  else if constexpr (DST == DB_TYPE_BIGINT)
    {
      return OR_CHECK_BIGINT_OVERFLOW (number);
    }
  else if constexpr (DST == DB_TYPE_FLOAT)
    {
      return OR_CHECK_FLOAT_OVERFLOW (number);
    }
  else
    {
      static_assert (DST == DB_TYPE_DOUBLE || DST == DB_TYPE_MONETARY, "missing numeric range check");
      return false;
    }
}

template <DB_TYPE DST, bool STRICT>
/*
 * [리뷰] tp_numeric_from_num — NUMERIC 소스를 다른 숫자 타입으로 내릴 때 numeric_opfunc 의 어느 coerce 함수를 부를지 DST·STRICT 조합으로 골라
 * 준다. tp_value_convert_number 의 SRC==NUMERIC 가지가 쓴다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 은 숫자 target case 마다
 * numeric_db_value_coerce_from_num(7372·7486·7626·7701·7764·7878)을, tp_value_coerce_strict 에서는
 * …_from_num_strict(5872·5970·6063·6107·6154·6244)를 불렀고 목적 타입 분기가 그 두 함수 안에 또 있었다.
 * 이 PR: scale 을 한 번 읽고 if constexpr(DST) × if constexpr(STRICT) 로, 이 PR 이 numeric_opfunc.h 에 새로 내보낸
 * numeric_coerce_num_to_{short,int,bigint,float,double,…}[_strict] 중 하나를 부른다.
 * 바뀐 것: 두 함수 안에 숨어 있던 목적 타입 switch 를 이름 있는 함수로 꺼내고 선택을 컴파일 타임으로 합쳤다(+72줄). 캐스트 경로와 strict 경로가 같은 셀을 쓰게 하는 핵심
 * 장치다.
 */
static int
tp_numeric_from_num (const DB_VALUE *src, DB_VALUE *target)
{
  int scale = db_get_numeric_scale (src, NULL);
  if constexpr (DST == DB_TYPE_SHORT)
    {
      if constexpr (STRICT)
	{
	  return numeric_coerce_num_to_short_strict (src, scale, target);
	}
      else
	{
	  return numeric_coerce_num_to_short (src, scale, target);
	}
    }
  else if constexpr (DST == DB_TYPE_INTEGER)
    {
      if constexpr (STRICT)
	{
	  return numeric_coerce_num_to_int_strict (src, scale, target);
	}
      else
	{
	  return numeric_coerce_num_to_int (src, scale, target);
	}
    }
  else if constexpr (DST == DB_TYPE_BIGINT)
    {
      if constexpr (STRICT)
	{
	  return numeric_coerce_num_to_bigint_strict (src, scale, target);
	}
      else
	{
	  return numeric_coerce_num_to_bigint (src, scale, target);
	}
    }
  else if constexpr (DST == DB_TYPE_FLOAT)
    {
      if constexpr (STRICT)
	{
	  return numeric_coerce_num_to_float_strict (src, scale, target);
	}
      else
	{
	  return numeric_coerce_num_to_float (src, scale, target);
	}
    }
  else if constexpr (DST == DB_TYPE_DOUBLE)
    {
      if constexpr (STRICT)
	{
	  return numeric_coerce_num_to_double_strict (src, scale, target);
	}
      else
	{
	  return numeric_coerce_num_to_double (src, scale, target);
	}
    }
  else
    {
      static_assert (DST == DB_TYPE_MONETARY, "missing numeric target operation");
      if constexpr (STRICT)
	{
	  return numeric_coerce_num_to_monetary_strict (src, scale, target);
	}
      else
	{
	  return numeric_coerce_num_to_monetary (src, scale, target);
	}
    }
}

template <DB_TYPE SRC, DB_TYPE DST, DOMAIN_CONVERT_MODE MODE>
/*
 * [리뷰] tp_value_convert_number — 숫자·숫자문자열 ↔ 숫자 변환 표의 셀 전부를 만들어 내는 템플릿. <SRC,DST,MODE> 조합마다 함수 하나가 실체화돼 표에 실리고,
 * 게이트가 고른 뒤 행마다 tp_value_convert 가 부른다.
 * develop: develop 에 없음 — 이 PR 이 신설. 같은 규칙이 tp_value_cast_internal 의
 * SHORT(7317)·INTEGER(7415)·BIGINT(7529)·FLOAT(7667)·DOUBLE(7744)·NUMERIC(7808)·MONETARY(7859) 7개 case 와, 거의
 * 같은 내용을 다시 적은 tp_value_coerce_strict(5743~)에 흩어져 있었다.
 * 이 PR: DST==NUMERIC(문자열은 numeric_coerce_string_to_num_status 후 재귀, COMPARE 모드의 FLOAT/DOUBLE/MONETARY 는 거절,
 * precision·scale 동일이면 통째 복사) / SRC==NUMERIC(tp_numeric_from_num) / 문자열 소스(tp_atobi·tp_atof + 반올림 또는 modf 정수성)
 * / 그 밖(get→범위검사→make) 네 갈래를 constexpr 로 가른다. MODE!=ASSIGN 이 strict.
 * 바뀐 것: 7개 case + strict 사본을 템플릿 하나(+221줄)로 합쳤다. AIX 포화 캐스트·OR_CHECK_ASSIGN_OVERFLOW·ROUND 같은 레거시 예외는
 * constexpr 가드 안에 그대로 보존돼 있다.
 */
TP_DOMAIN_STATUS
tp_value_convert_number (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
			 date_conversion_error *date_error)
{
  static_assert (MODE == DOMAIN_CONVERT_ASSIGN || MODE == DOMAIN_CONVERT_COMPARE || MODE == DOMAIN_CONVERT_OPERAND,
		 "missing numeric conversion mode");
  static_assert (SRC == DB_TYPE_SHORT || SRC == DB_TYPE_INTEGER || SRC == DB_TYPE_BIGINT || SRC == DB_TYPE_FLOAT
		 || SRC == DB_TYPE_DOUBLE || SRC == DB_TYPE_MONETARY || SRC == DB_TYPE_NUMERIC
		 || SRC == DB_TYPE_CHAR || SRC == DB_TYPE_VARCHAR, "missing numeric source cell");
  static_assert (DST == DB_TYPE_SHORT || DST == DB_TYPE_INTEGER || DST == DB_TYPE_BIGINT || DST == DB_TYPE_FLOAT
		 || DST == DB_TYPE_DOUBLE || DST == DB_TYPE_MONETARY || DST == DB_TYPE_NUMERIC,
		 "missing numeric destination cell");
  constexpr bool integer_target = DST == DB_TYPE_SHORT || DST == DB_TYPE_INTEGER || DST == DB_TYPE_BIGINT;
  constexpr bool integer_source = SRC == DB_TYPE_SHORT || SRC == DB_TYPE_INTEGER || SRC == DB_TYPE_BIGINT;
  constexpr bool string_source = SRC == DB_TYPE_CHAR || SRC == DB_TYPE_VARCHAR;
  constexpr bool strict = MODE != DOMAIN_CONVERT_ASSIGN;

  if constexpr (DST == DB_TYPE_NUMERIC)
    {
      if constexpr (string_source)
	{
	  DB_VALUE number;
	  const char *string = db_get_string (src);
	  if (string == NULL)
	    {
	      return DOMAIN_INCOMPATIBLE;
	    }
	  int error = numeric_coerce_string_to_num_status (string, db_get_string_size (src),
		      db_get_string_codeset (src), &number);
	  if (error != NO_ERROR)
	    {
	      return error == ER_IT_DATA_OVERFLOW ? DOMAIN_OVERFLOW : DOMAIN_INCOMPATIBLE;
	    }
	  /* The legacy strict string path also rounds when fitting the parsed NUMERIC to the target. */
	  return tp_value_convert_number<DB_TYPE_NUMERIC, DB_TYPE_NUMERIC, DOMAIN_CONVERT_ASSIGN>
		 (&number, target, desired_domain, date_error);
	}
      else if constexpr (MODE == DOMAIN_CONVERT_COMPARE
			 && (SRC == DB_TYPE_FLOAT || SRC == DB_TYPE_DOUBLE || SRC == DB_TYPE_MONETARY))
	{
	  return DOMAIN_INCOMPATIBLE;
	}
      else
	{
	  if constexpr (SRC == DB_TYPE_NUMERIC && MODE != DOMAIN_CONVERT_COMPARE)
	    {
	      if (desired_domain->precision == DB_VALUE_PRECISION (src)
		  && desired_domain->scale == DB_VALUE_SCALE (src))
		{
		  /* NUMERIC owns its inline buffer; no generic value/type dispatch is necessary. */
		  *target = *src;
		  return DOMAIN_COMPATIBLE;
		}
	    }
	  DB_DATA_STATUS data_stat = DATA_STATUS_OK;
	  int error = numeric_coerce_value_to_num<SRC> (src, target, &data_stat);
	  if (error == ER_IT_DATA_OVERFLOW || data_stat == DATA_STATUS_TRUNCATED)
	    {
	      return DOMAIN_OVERFLOW;
	    }
	  return error == NO_ERROR ? DOMAIN_COMPATIBLE : DOMAIN_INCOMPATIBLE;
	}
    }
  else if constexpr (SRC == DB_TYPE_NUMERIC)
    {
      int error = tp_numeric_from_num<DST, strict> (src, target);
      return error == NO_ERROR ? DOMAIN_COMPATIBLE : (strict ? DOMAIN_INCOMPATIBLE : DOMAIN_OVERFLOW);
    }
  else if constexpr (string_source)
    {
      DB_DATA_STATUS data_stat = DATA_STATUS_OK;
      if constexpr (DST == DB_TYPE_BIGINT && !strict)
	{
	  DB_BIGINT number = 0;
	  if (tp_atobi (src, &number, &data_stat) != NO_ERROR)
	    {
	      return er_errid () != NO_ERROR ? DOMAIN_ERROR : DOMAIN_INCOMPATIBLE;
	    }
	  if (data_stat == DATA_STATUS_TRUNCATED)
	    {
	      return DOMAIN_OVERFLOW;
	    }
	  db_make_bigint (target, number);
	  return DOMAIN_COMPATIBLE;
	}
      else
	{
	  double number = 0.0;
	  if (tp_atof (src, &number, &data_stat) != NO_ERROR || data_stat == DATA_STATUS_NOT_CONSUMED)
	    {
	      if constexpr (strict)
		{
		  return DOMAIN_INCOMPATIBLE;
		}
	      else
		{
		  return er_errid () != NO_ERROR ? DOMAIN_ERROR : DOMAIN_INCOMPATIBLE;
		}
	    }
	  if (data_stat == DATA_STATUS_TRUNCATED || tp_numeric_overflow<DST> (number))
	    {
	      return DOMAIN_OVERFLOW;
	    }
	  if constexpr (integer_target)
	    {
	      if constexpr (strict)
		{
		  double integral = 0.0;
		  if (modf (number, &integral) != 0)
		    {
		      return DOMAIN_INCOMPATIBLE;
		    }
		  tp_numeric_value<DST>::make (target, integral);
		}
	      else
		{
		  tp_numeric_value<DST>::make (target, ROUND (number));
		}
	    }
	  else
	    {
	      tp_numeric_value<DST>::make (target, number);
	    }
	  return DOMAIN_COMPATIBLE;
	}
    }
  else
    {
      const auto number = tp_numeric_value<SRC>::get (src);
      if constexpr (SRC == DST)
	{
	  /* Includes the currency field of a MONETARY identity. */
	  *target = *src;
	  return DOMAIN_COMPATIBLE;
	}
      else if constexpr (integer_target)
	{
	  if (tp_numeric_overflow<DST> (number))
	    {
	      return DOMAIN_OVERFLOW;
	    }
	  if constexpr (integer_source)
	    {
	      tp_numeric_value<DST>::make (target, number);
	    }
	  else if constexpr (strict)
	    {
	      auto integral = number;
	      if constexpr (SRC == DB_TYPE_FLOAT)
		{
		  if (modff (number, &integral) != 0)
		    {
		      return DOMAIN_INCOMPATIBLE;
		    }
		}
	      else
		{
		  if (modf (number, &integral) != 0)
		    {
		      return DOMAIN_INCOMPATIBLE;
		    }
		}
	      tp_numeric_value<DST>::make (target, integral);
	    }
	  else
	    {
	      using target_type = decltype (tp_numeric_value<DST>::get (target));
	      target_type integral = static_cast<target_type> (ROUND (number));
	      /* Preserve the legacy assignment overflow checks, including AIX's saturating casts. */
	      if constexpr (DST == DB_TYPE_BIGINT || (DST == DB_TYPE_INTEGER && SRC == DB_TYPE_FLOAT))
		{
#if defined (AIX)
		  if constexpr (SRC == DB_TYPE_FLOAT || SRC == DB_TYPE_DOUBLE)
		    {
		      if constexpr (DST == DB_TYPE_BIGINT)
			{
			  if (number == static_cast<decltype (number)> (DB_BIGINT_MAX))
			    {
			      integral = DB_BIGINT_MIN;
			    }
			}
		      else
			{
			  if (number == static_cast<decltype (number)> (DB_INT32_MAX))
			    {
			      integral = DB_INT32_MIN;
			    }
			}
		    }
#endif
		  if (OR_CHECK_ASSIGN_OVERFLOW (integral, number))
		    {
		      return DOMAIN_OVERFLOW;
		    }
		}
	      tp_numeric_value<DST>::make (target, integral);
	    }
	}
      else if constexpr (DST == DB_TYPE_FLOAT && (SRC == DB_TYPE_DOUBLE || SRC == DB_TYPE_MONETARY))
	{
	  /* These two source types are absent from the legacy strict FLOAT switch. */
	  if constexpr (strict)
	    {
	      return DOMAIN_INCOMPATIBLE;
	    }
	  else
	    {
	      if (tp_numeric_overflow<DST> (number))
		{
		  return DOMAIN_OVERFLOW;
		}
	      tp_numeric_value<DST>::make (target, number);
	    }
	}
      else
	{
	  tp_numeric_value<DST>::make (target, number);
	}
      return DOMAIN_COMPATIBLE;
    }
}

/*
 * [리뷰] tp_value_convert_blob_to_varchar — BLOB→VARCHAR 셀 — 항상 DOMAIN_INCOMPATIBLE 을 돌려줘 이 쌍이 금지됨을 표에 명시한다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 은 VARCHAR/CHAR target switch 에 BLOB case 가 없어 default:
 * DOMAIN_INCOMPATIBLE 로 떨어졌다.
 * 이 PR: 인자를 모두 무시하고 DOMAIN_INCOMPATIBLE 만 돌려준다.
 * 바뀐 것: default 로 떨어지던 쌍을 '표의 빈칸이 아니라 금지 셀'로 명시화한 5줄 함수 신설. 표가 모든 쌍을 덮는지 빌드 시점에 보이게 한다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_blob_to_varchar (const DB_VALUE *, DB_VALUE *, const TP_DOMAIN *, date_conversion_error *)
{
  return DOMAIN_INCOMPATIBLE;
}

/*
 * [리뷰] tp_atotime_core — 문자열 DB_VALUE 를 DB_TIME 으로 파싱한다. 날짜·시간 셀들이 CHAR/VARCHAR 소스에 공통으로 쓰는 1차 파서로, 실패는
 * ER_FAILED 로만 알리고 상세는 date_conversion_error 에 적는다.
 * develop: develop object_domain.c:4668 의 static tp_atotime(src, temp) 가 같은 일을 했지만 db_date_parse_time() 을 불러 그
 * 자리에서 er_set 까지 했다.
 * 이 PR: 인자에 date_conversion_error* 가 붙고 db_date_parse_time_core() 를 부른다. 전역 에러 상태는 건드리지 않고 error 에 코드·파일·줄만
 * 기록한다.
 * 바뀐 것: 시그니처에 date_conversion_error* 추가, 호출 대상을 _core 변종으로 교체. 에러 게시는 호출자(conversion_error.publish())로 미뤄졌다 —
 * 변환기가 행마다 전역 에러를 흔들지 않게 하려는 것.
 */
static int
tp_atotime_core (const DB_VALUE *src, DB_TIME *temp, date_conversion_error *error)
{
  int milisec;
  const char *strp = db_get_string (src);
  int str_len = db_get_string_size (src);
  int status = NO_ERROR;

  if (db_date_parse_time_core (strp, str_len, temp, &milisec, error) != NO_ERROR)
    {
      status = ER_FAILED;
    }

  return status;
}

/*
 * [리뷰] tp_atodate_core — 문자열 DB_VALUE 를 DB_DATE 로 파싱한다. DATE·DATETIME 계열 셀의 CHAR/VARCHAR 입구다.
 * develop: develop object_domain.c:4693 의 static tp_atodate(src, temp) — db_date_parse_date() 를 불러 그 자리에서
 * er_set 했다.
 * 이 PR: date_conversion_error* 를 받고 db_date_parse_date_core() 를 부른다.
 * 바뀐 것: 시그니처 +1 인자, _core 호출로 교체. 본문 구조는 develop 과 같고 에러 게시만 호출자로 미뤄졌다.
 */
static int
tp_atodate_core (const DB_VALUE *src, DB_DATE *temp, date_conversion_error *error)
{
  const char *strp = db_get_string (src);
  int str_len = db_get_string_size (src);
  int status = NO_ERROR;

  if (db_date_parse_date_core (strp, str_len, temp, error) != NO_ERROR)
    {
      status = ER_FAILED;
    }

  return status;
}

/*
 * [리뷰] tp_atoutime_core — 문자열 DB_VALUE 를 DB_UTIME(TIMESTAMP)로 파싱한다. char→timestamp 계열 셀의 입구다.
 * develop: develop object_domain.c:4717 의 static tp_atoutime(src, temp) — db_date_parse_timestamp() 가 er_set
 * 했다.
 * 이 PR: date_conversion_error* 를 받고 db_date_parse_timestamp_core() 를 부른다.
 * 바뀐 것: 시그니처 +1 인자, _core 호출로 교체.
 */
static int
tp_atoutime_core (const DB_VALUE *src, DB_UTIME *temp, date_conversion_error *error)
{
  const char *strp = db_get_string (src);
  int str_len = db_get_string_size (src);
  int status = NO_ERROR;

  if (db_date_parse_timestamp_core (strp, str_len, temp, error) != NO_ERROR)
    {
      status = ER_FAILED;
    }

  return status;
}

/*
 * [리뷰] tp_atotimestamptz_core — 문자열을 DB_TIMESTAMPTZ 로 파싱한다(is_cast=true). char→timestamptz·timestampltz 셀이 쓴다.
 * develop: develop object_domain.c:4741 의 static tp_atotimestamptz(src, temp) — db_string_to_timestamptz_ex()
 * 가 er_set 했다.
 * 이 PR: date_conversion_error* 를 받고 db_string_to_timestamptz_ex_core(…, true, error) 를 부른다. has_zone 은 버린다.
 * 바뀐 것: 시그니처 +1 인자, _core 호출로 교체.
 */
static int
tp_atotimestamptz_core (const DB_VALUE *src, DB_TIMESTAMPTZ *temp, date_conversion_error *error)
{
  const char *strp = db_get_string (src);
  int str_len = db_get_string_size (src);
  int status = NO_ERROR;
  bool dummy_has_zone;

  if (db_string_to_timestamptz_ex_core (strp, str_len, temp, &dummy_has_zone, true, error) != NO_ERROR)
    {
      status = ER_FAILED;
    }

  return status;
}

/*
 * [리뷰] tp_atoudatetime_core — 문자열을 DB_DATETIME 으로 파싱한다. char→datetime 셀의 입구다.
 * develop: develop object_domain.c:4766 의 static tp_atoudatetime(src, temp) — db_date_parse_datetime() 이
 * er_set 했다.
 * 이 PR: date_conversion_error* 를 받고 db_date_parse_datetime_core() 를 부른다.
 * 바뀐 것: 시그니처 +1 인자, _core 호출로 교체.
 */
static int
tp_atoudatetime_core (const DB_VALUE *src, DB_DATETIME *temp, date_conversion_error *error)
{
  const char *strp = db_get_string (src);
  int str_len = db_get_string_size (src);
  int status = NO_ERROR;

  if (db_date_parse_datetime_core (strp, str_len, temp, error) != NO_ERROR)
    {
      status = ER_FAILED;
    }

  return status;
}

/*
 * [리뷰] tp_atodatetimetz_core — 문자열을 DB_DATETIMETZ 로 파싱한다. char→datetimetz·datetimeltz 셀이 쓴다.
 * develop: develop object_domain.c:4790 의 static tp_atodatetimetz(src, temp) — db_string_to_datetimetz_ex() 가
 * er_set 했다.
 * 이 PR: date_conversion_error* 를 받고 db_string_to_datetimetz_ex_core() 를 부른다. has_zone 은 버린다.
 * 바뀐 것: 시그니처 +1 인자, _core 호출로 교체.
 */
static int
tp_atodatetimetz_core (const DB_VALUE *src, DB_DATETIMETZ *temp, date_conversion_error *error)
{
  const char *strp = db_get_string (src);
  int str_len = db_get_string_size (src);
  int status = NO_ERROR;
  bool dummy_has_zone;

  if (db_string_to_datetimetz_ex_core (strp, str_len, temp, &dummy_has_zone, error) != NO_ERROR)
    {
      status = ER_FAILED;
    }

  return status;
}

/*
 * [리뷰] tp_make_char_conversion — 임의의 문자열 버퍼를 목적 도메인의 CHAR 로 만들어 target 에 담는다(precision·codeset·collation 적용,
 * db_char_string_coerce 로 길이 맞춤). 숫자·날짜 → CHAR 셀들이 마지막에 부른다.
 * develop: develop 의 static make_desired_string_db_value(object_domain.c:5684)가 desired_type 을 인자로 받아 switch 로
 * db_make_char / db_make_varchar 를 갈랐다.
 * 이 PR: switch 없이 db_make_char 만 한다. assert·need_clear·db_char_string_coerce·pr_clear_value 는 develop 과 같다.
 * 바뀐 것: switch 의 CHAR 팔만 떼어낸 함수(+25줄). desired_type 인자가 사라졌다 — 어느 셀이 부르느냐로 이미 정해져 런타임 분기가 필요 없다.
 */
static void
tp_make_char_conversion (const TP_DOMAIN *desired_domain, const char *new_string, DB_VALUE *target,
			 TP_DOMAIN_STATUS *status, DB_DATA_STATUS *data_stat)
{
  DB_VALUE temp;

  assert (desired_domain->collation_flag == TP_DOMAIN_COLL_NORMAL
	  || desired_domain->collation_flag == TP_DOMAIN_COLL_LEAVE);

  *status = DOMAIN_COMPATIBLE;

  db_make_char (&temp, desired_domain->precision, new_string, strlen (new_string),
		TP_DOMAIN_CODESET (desired_domain), TP_DOMAIN_COLLATION (desired_domain));

  temp.need_clear = true;
  if (db_char_string_coerce (&temp, target, data_stat) != NO_ERROR)
    {
      *status = DOMAIN_INCOMPATIBLE;
    }
  else
    {
      *status = DOMAIN_COMPATIBLE;
    }
  pr_clear_value (&temp);
}

/*
 * [리뷰] tp_make_varchar_conversion — tp_make_char_conversion 의 VARCHAR 짝 — 버퍼를 목적 도메인의 VARCHAR 로 만들어 target 에
 * 담는다. 숫자·날짜 → VARCHAR 셀들이 부른다.
 * develop: develop make_desired_string_db_value(object_domain.c:5684)의 `case DB_TYPE_VARCHAR:` 팔이었다.
 * 이 PR: db_make_varchar 만 하고 나머지는 CHAR 판과 같다.
 * 바뀐 것: switch 의 VARCHAR 팔을 떼어낸 함수(+25줄). CHAR 판과 db_make_* 한 줄만 다르다.
 */
static void
tp_make_varchar_conversion (const TP_DOMAIN *desired_domain, const char *new_string, DB_VALUE *target,
			    TP_DOMAIN_STATUS *status, DB_DATA_STATUS *data_stat)
{
  DB_VALUE temp;

  assert (desired_domain->collation_flag == TP_DOMAIN_COLL_NORMAL
	  || desired_domain->collation_flag == TP_DOMAIN_COLL_LEAVE);

  *status = DOMAIN_COMPATIBLE;

  db_make_varchar (&temp, desired_domain->precision, new_string, strlen (new_string),
		   TP_DOMAIN_CODESET (desired_domain), TP_DOMAIN_COLLATION (desired_domain));

  temp.need_clear = true;
  if (db_char_string_coerce (&temp, target, data_stat) != NO_ERROR)
    {
      *status = DOMAIN_INCOMPATIBLE;
    }
  else
    {
      *status = DOMAIN_COMPATIBLE;
    }
  pr_clear_value (&temp);
}

/*
 * [리뷰] tp_ftoa_buffer — FLOAT 값을 _dtoa 로 10진 문자열로 만들어 db_private_alloc 버퍼를 돌려준다. 소유권은
 * 호출자(tp_ftoa_char/varchar)가 need_clear=true 로 받는다. 실패하면 result 를 NULL 로 만들고 nullptr 을 돌려준다.
 * develop: develop tp_ftoa(object_domain.c:5405)의 앞부분(alloc·_dtoa·format_floating_point)이었고, 같은 함수가 이어서 result
 * 도메인으로 switch 해 담기까지 했다.
 * 이 PR: 문자열만 만들어 포인터를 돌려주고 끝난다. target 에 담는 일은 하지 않는다.
 * 바뀐 것: tp_ftoa 를 '버퍼 만들기'와 '담기' 둘로 쪼갠 앞쪽(+28줄). preamble 의 gate-imbalance(alloc-free=+1)는 이 소유권 이전에 따른 오탐이다.
 */
char *
tp_ftoa_buffer (const DB_VALUE *src, DB_VALUE *result)
{
  /* dtoa() appears to ignore the requested number of digits... */
  const int ndigits = TP_FLOAT_MANTISA_DECIMAL_PRECISION;
  char *str_float, *rve;
  int decpt, sign;

  assert (DB_VALUE_TYPE (src) == DB_TYPE_FLOAT);
  assert (DB_VALUE_TYPE (result) == DB_TYPE_NULL);

  rve = str_float = (char *) db_private_alloc (NULL, TP_FLOAT_AS_CHAR_LENGTH + 1);
  if (str_float == NULL)
    {
      db_make_null (result);
      return nullptr;
    }

  /* _dtoa just returns the digits sequence and the exponent as for a number in the form 0.4321344e+14 */
  _dtoa (db_get_float (src), 0, ndigits, &decpt, &sign, &rve, str_float, 1);

  /* rounding should also be performed here */
  str_float[ndigits] = '\0';	/* _dtoa() disregards ndigits */

  format_floating_point (str_float, str_float + strlen (str_float), ndigits, decpt, sign);

  return str_float;
}

/*
 * [리뷰] tp_ftoa_char — FLOAT → CHAR 문자열화 — tp_ftoa_buffer 의 버퍼를 result 의 precision·codeset·collation 으로 CHAR 에
 * 담고 need_clear 를 세운다. object_domain_convert.h 가 내보내 다른 번역 단위도 쓴다.
 * develop: develop tp_ftoa 안 `switch (DB_VALUE_DOMAIN_TYPE (result)) case DB_TYPE_CHAR:` 팔이었다.
 * 이 PR: 버퍼가 nullptr 이면 조용히 돌아가고(이미 result 는 NULL), 아니면 db_make_char + need_clear=true.
 * 바뀐 것: switch 팔을 함수로 분리(+13줄). develop 의 default 팔(버퍼 free 후 ER_TP_CANT_COERCE)은 호출자가 이미 CHAR 셀이라 도달 불가라서
 * 사라졌다.
 */
void
tp_ftoa_char (const DB_VALUE *src, DB_VALUE *result)
{
  char *str_float = tp_ftoa_buffer (src, result);
  if (str_float == nullptr)
    {
      return;
    }

  db_make_char (result, DB_VALUE_PRECISION (result), str_float, strlen (str_float), db_get_string_codeset (result),
		db_get_string_collation (result));
  result->need_clear = true;
}

/*
 * [리뷰] tp_ftoa_varchar — FLOAT → VARCHAR 문자열화 — tp_ftoa_char 의 VARCHAR 짝.
 * develop: develop tp_ftoa 안 `case DB_TYPE_VARCHAR:` 팔이었다.
 * 이 PR: db_make_varchar 로 담는 것 외에는 CHAR 판과 같다.
 * 바뀐 것: switch 팔을 함수로 분리(+13줄).
 */
void
tp_ftoa_varchar (const DB_VALUE *src, DB_VALUE *result)
{
  char *str_float = tp_ftoa_buffer (src, result);
  if (str_float == nullptr)
    {
      return;
    }

  db_make_varchar (result, DB_VALUE_PRECISION (result), str_float, strlen (str_float),
		   db_get_string_codeset (result), db_get_string_collation (result));
  result->need_clear = true;
}

/*
 * [리뷰] tp_dtoa_buffer — DOUBLE 값을 _dtoa 로 문자열화해 db_private_alloc 버퍼를 돌려준다. 소유권은 tp_dtoa_char/varchar 가 받는다.
 * develop: develop tp_dtoa(object_domain.c:5464)의 앞부분이었고, 같은 함수가 result 도메인으로 switch 해 담기까지 했다.
 * 이 PR: ndigits 가 TP_DOUBLE_MANTISA_DECIMAL_PRECISION, _dtoa 마지막 인자가 0 인 것만 FLOAT 판과 다르고, 버퍼만 돌려준다.
 * 바뀐 것: tp_dtoa 를 둘로 쪼갠 앞쪽(+26줄). preamble 의 gate-imbalance(alloc-free=+1)는 같은 이유의 오탐이다.
 */
char *
tp_dtoa_buffer (const DB_VALUE *src, DB_VALUE *result)
{
  /* dtoa() appears to ignore the requested number of digits... */
  const int ndigits = TP_DOUBLE_MANTISA_DECIMAL_PRECISION;
  char *str_double, *rve;
  int decpt, sign;

  assert (DB_VALUE_TYPE (src) == DB_TYPE_DOUBLE);
  assert (DB_VALUE_TYPE (result) == DB_TYPE_NULL);

  rve = str_double = (char *) db_private_alloc (NULL, TP_DOUBLE_AS_CHAR_LENGTH + 1);
  if (str_double == NULL)
    {
      db_make_null (result);
      return nullptr;
    }

  _dtoa (db_get_double (src), 0, ndigits, &decpt, &sign, &rve, str_double, 0);
  /* rounding should also be performed here */
  str_double[ndigits] = '\0';	/* _dtoa() disregards ndigits */

  format_floating_point (str_double, str_double + strlen (str_double), ndigits, decpt, sign);

  return str_double;
}

/*
 * [리뷰] tp_dtoa_char — DOUBLE → CHAR 문자열화 — tp_dtoa_buffer 의 버퍼를 result 에 CHAR 로 담는다.
 * develop: develop tp_dtoa 안 `case DB_TYPE_CHAR:` 팔이었다.
 * 이 PR: nullptr 이면 조용히 반환, 아니면 db_make_char + need_clear=true.
 * 바뀐 것: switch 팔을 함수로 분리(+13줄). develop 의 default 에러 팔은 도달 불가라 삭제됐다.
 */
void
tp_dtoa_char (const DB_VALUE *src, DB_VALUE *result)
{
  char *str_double = tp_dtoa_buffer (src, result);
  if (str_double == nullptr)
    {
      return;
    }

  db_make_char (result, DB_VALUE_PRECISION (result), str_double, strlen (str_double),
		db_get_string_codeset (result), db_get_string_collation (result));
  result->need_clear = true;
}

/*
 * [리뷰] tp_dtoa_varchar — DOUBLE → VARCHAR 문자열화 — tp_dtoa_char 의 VARCHAR 짝.
 * develop: develop tp_dtoa 안 `case DB_TYPE_VARCHAR:` 팔이었다.
 * 이 PR: db_make_varchar 로 담는다.
 * 바뀐 것: switch 팔을 함수로 분리(+13줄).
 */
void
tp_dtoa_varchar (const DB_VALUE *src, DB_VALUE *result)
{
  char *str_double = tp_dtoa_buffer (src, result);
  if (str_double == nullptr)
    {
      return;
    }

  db_make_varchar (result, DB_VALUE_PRECISION (result), str_double, strlen (str_double),
		   db_get_string_codeset (result), db_get_string_collation (result));
  result->need_clear = true;
}

/*
 * [리뷰] tp_make_date_conversion — DB_VALUE 를 DATE 로 직접 조립한다 — 도메인 헤더를 손으로 세우고 db_date_encode_core 로 날짜를 채운다.
 * 문자열·날짜 → DATE 셀들이 쓴다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 은 db_make_date(target, month, day, year) 를 불렀고 그 안의
 * db_date_encode 가 실패 시 er_set 했다.
 * 이 PR: type/is_null/need_clear 를 직접 쓰고 db_date_encode_core(…, error) 의 반환값을 그대로 돌려준다. 에러는 error 구조체에만 남는다.
 * 바뀐 것: er_set 하는 db_make_date 대신 _core 를 쓰는 조립 헬퍼 신설(+8줄). DB_VALUE 내부 필드를 직접 써서 레이아웃에 암묵적으로 묶인다.
 */
static int
tp_make_date_conversion (DB_VALUE *value, int month, int day, int year, date_conversion_error *error)
{
  value->domain.general_info.type = DB_TYPE_DATE;
  value->domain.general_info.is_null = 0;
  value->need_clear = false;
  return db_date_encode_core (&value->data.date, month, day, year, error);
}

/*
 * [리뷰] tp_make_time_conversion — DB_VALUE 를 TIME 으로 직접 조립한다 — tp_make_date_conversion 의 TIME 짝. 숫자·문자열·날짜 →
 * TIME 셀들이 쓴다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 은 db_make_time() 을 불렀고 그 안의 db_time_encode 가 er_set 했다.
 * 이 PR: type/is_null/need_clear 를 직접 세우고 db_time_encode_core(…, error) 의 반환값을 돌려준다.
 * 바뀐 것: DATE 판과 같은 모양의 조립 헬퍼 신설(+8줄). 역시 DB_VALUE 레이아웃 직접 접근이다.
 */
static int
tp_make_time_conversion (DB_VALUE *value, int hour, int minute, int second, date_conversion_error *error)
{
  value->domain.general_info.type = DB_TYPE_TIME;
  value->domain.general_info.is_null = 0;
  value->need_clear = false;
  return db_time_encode_core (&value->data.time, hour, minute, second, error);
}

/*
 * [리뷰] tp_finish_enumeration_conversion — ENUM 을 목적으로 하는 모든 셀의 공통 뒷부분 — 인덱스(val_idx)나 이름(val_str) 중 가진 것으로
 * 나머지를 ENUM 도메인에서 찾아 db_make_enumeration 으로 target 을 완성하고 임시값을 정리한다. ENUM target 셀 22개가 부른다.
 * develop: develop tp_value_cast_internal `case DB_TYPE_ENUMERATION:`(object_domain.c:9617) 블록에서 소스 switch 뒤의
 * 꼬리 전체(9824~9937)였다 — val_idx·val_str·conv_val·exit 를 공유하는 같은 블록 안이라 밖에서 부를 수 없었다.
 * 이 PR: 그 꼬리를 인자로 넘겨받는다. 이름이 있으면 QSTR_COMPARE 로 요소를 선형 탐색(못 찾고 빈 문자열이면 특수 에러값 0), 인덱스만 있으면 범위를 보고 이름을 꺼낸 뒤,
 * 문자셋 변환 버퍼가 있으면 재사용하고 없으면 db_private_alloc 복사해 db_make_enumeration 한다.
 * 바뀐 것: switch 꼬리를 공유 함수로 승격(+122줄). develop 의 `ti = (desired_domain->type->id == DB_TYPE_CHAR);` 가 `ti =
 * false;` 로 단순화됐는데 여기 desired_domain 은 언제나 ENUMERATION 이라 develop 에서도 항상 false 였다 — 결과는 같다. break 자리는 전부
 * return 으로 바뀌었다.
 */
static TP_DOMAIN_STATUS
tp_finish_enumeration_conversion (DB_VALUE *target, const TP_DOMAIN *desired_domain, DB_VALUE &conv_val,
				  unsigned short val_idx, const char *val_str, int val_str_size,
				  TP_DOMAIN_STATUS status, bool exit)
{
  bool alloc_string = true, ti = true;
  bool ignore_trailing_space = tp_conversion_ignore_trailing_space ();

  if (exit)
    {
      return status;
    }

  if (status == DOMAIN_COMPATIBLE)
    {
      if (val_str != NULL)
	{
	  /* We have to search through the elements of the desired domain to find the index for val_str. */
	  int i, size;
	  DB_ENUM_ELEMENT *db_enum = NULL;
	  int elem_count = DOM_GET_ENUM_ELEMS_COUNT (desired_domain);

	  for (i = 1; i <= elem_count; i++)
	    {
	      db_enum = &DOM_GET_ENUM_ELEM (desired_domain, i);
	      size = DB_GET_ENUM_ELEM_STRING_SIZE (db_enum);

	      if (!ignore_trailing_space)
		{
		  ti = false;
		}

	      /* use collation from the PT_TYPE_ENUMERATION */
	      if (QSTR_COMPARE (desired_domain->collation_id, (const unsigned char *) val_str, val_str_size,
				(const unsigned char *) DB_GET_ENUM_ELEM_STRING (db_enum), size, ti) == 0)
		{
		  break;
		}
	    }

	  val_idx = i;
	  if (i > elem_count)
	    {
	      if (val_str[0] == 0)
		{
		  /* The source value is string with length 0 and can be matched with enum "special error value"
		   * if it's not a valid ENUM value */
		  db_make_enumeration (target, 0, NULL, 0, TP_DOMAIN_CODESET (desired_domain),
				       TP_DOMAIN_COLLATION (desired_domain));
		  return status;
		}
	      else
		{
		  status = DOMAIN_INCOMPATIBLE;
		}
	    }
	}
      else
	{
	  /* We have the index, we need to get the actual string value from the desired domain */
	  if (val_idx > DOM_GET_ENUM_ELEMS_COUNT (desired_domain))
	    {
	      status = DOMAIN_INCOMPATIBLE;
	    }
	  else if (val_idx == 0)
	    {
	      /* ENUM Special error value */
	      db_make_enumeration (target, 0, NULL, 0, TP_DOMAIN_CODESET (desired_domain),
				   TP_DOMAIN_COLLATION (desired_domain));
	      return status;
	    }
	  else
	    {
	      val_str_size = DB_GET_ENUM_ELEM_STRING_SIZE (&DOM_GET_ENUM_ELEM (desired_domain, val_idx));
	      val_str = DB_GET_ENUM_ELEM_STRING (&DOM_GET_ENUM_ELEM (desired_domain, val_idx));
	    }
	}

      if (status == DOMAIN_COMPATIBLE)
	{
	  const char *enum_str;

	  assert (val_str != NULL);

	  if (!DB_IS_NULL (&conv_val))
	    {
	      /* if charset conversion, than use the converted value buffer to avoid an additional copy */
	      alloc_string = false;
	      conv_val.need_clear = false;
	    }

	  if (alloc_string)
	    {
	      char *enum_str_tmp = (char *) db_private_alloc (NULL, val_str_size + 1);
	      if (enum_str_tmp == NULL)
		{
		  status = DOMAIN_ERROR;
		  pr_clear_value (&conv_val);
		  return status;
		}
	      else
		{
		  memcpy (enum_str_tmp, val_str, val_str_size);
		  enum_str_tmp[val_str_size] = 0;
		}

	      enum_str = enum_str_tmp;
	    }
	  else
	    {
	      enum_str = val_str;
	    }

	  db_make_enumeration (target, val_idx, enum_str, val_str_size, TP_DOMAIN_CODESET (desired_domain),
			       TP_DOMAIN_COLLATION (desired_domain));
	  target->need_clear = true;
	}
    }
  pr_clear_value (&conv_val);

  return status;
}

/*
 * [리뷰] tp_value_convert_enumeration_to_numeric — ENUM → NUMERIC 셀 — ENUM 의 짧은 정수 인덱스를 NUMERIC 으로 만든다. 게이트가 고른
 * 뒤 행마다 tp_value_convert 가 부른다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop tp_value_cast_internal `case DB_TYPE_NUMERIC:`(7808) 안
 * ENUMERATION 분기였다.
 * 이 PR: numeric_coerce_value_to_num<DB_TYPE_ENUMERATION> 을 부르고 ER_IT_DATA_OVERFLOW 나 DATA_STATUS_TRUNCATED 면
 * DOMAIN_OVERFLOW, 그 밖엔 NO_ERROR 여부로 COMPATIBLE/INCOMPATIBLE.
 * 바뀐 것: switch 분기를 셀로 분리(+12줄). numeric_coerce_value_to_num 이 소스 타입을 템플릿 인자로 받는 꼴로 바뀐 데 맞춰 호출이 바뀌었다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_enumeration_to_numeric (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
    date_conversion_error *error)
{
  DB_DATA_STATUS data_stat = DATA_STATUS_OK;
  int result = numeric_coerce_value_to_num < DB_TYPE_ENUMERATION > (src, target, &data_stat);
  if (result == ER_IT_DATA_OVERFLOW || data_stat == DATA_STATUS_TRUNCATED)
    {
      return DOMAIN_OVERFLOW;
    }
  return result == NO_ERROR ? DOMAIN_COMPATIBLE : DOMAIN_INCOMPATIBLE;
}

/* An ENUM into a number other than NUMERIC (DST): the ENUM's index */
template <DB_TYPE DST>
/*
 * [리뷰] tp_value_convert_enumeration_to_number — ENUM → SHORT/INTEGER/BIGINT/FLOAT/DOUBLE/MONETARY 셀들을 만드는 템플릿
 * — ENUM 인덱스를 그대로 숫자로 담는다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 은 숫자 target case 마다 `case DB_TYPE_ENUMERATION: db_make_xxx
 * (target, db_get_enum_short (src));` 를 따로 적었다(예: 7913).
 * 이 PR: tp_numeric_value<DST>::make (target, db_get_enum_short (src)) 한 줄, 항상 DOMAIN_COMPATIBLE.
 * 바뀐 것: 6개 case 를 템플릿 하나로 합쳤다(+8줄). 범위 검사가 없는 것도 develop 과 같다 — ENUM 인덱스는 unsigned short 범위다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_enumeration_to_number (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *,
					date_conversion_error *)
{
  tp_numeric_value<DST>::make (target, db_get_enum_short (src));

  return DOMAIN_COMPATIBLE;
}

/* A number into a TIMESTAMP, a TIMESTAMPLTZ or a TIMESTAMPTZ (DST): the number as an INTEGER (ASSIGN) is the seconds
 * since the epoch, which may not be negative; a TIMESTAMPTZ takes the session's time zone */
template <DB_TYPE SRC, DB_TYPE DST>
/*
 * [리뷰] tp_value_convert_number_to_timestamp — 숫자 → TIMESTAMP/TIMESTAMPLTZ/TIMESTAMPTZ 셀들을 만드는 템플릿 — 숫자를 UNIX
 * epoch 초로 읽어 타임스탬프를 만든다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 은 TIMESTAMP(7921)·TIMESTAMPTZ(8035)·TIMESTAMPLTZ(8167) 세 case 안에서
 * 숫자를 INTEGER 로 캐스트→음수 검사→db_make_* 하는 코드를 세 벌 갖고 있었다.
 * 이 PR: tp_value_convert_number<SRC,DB_TYPE_INTEGER,ASSIGN> 로 정수화(실패 시 그 status 전달), 음수면 DOMAIN_INCOMPATIBLE,
 * 그 뒤 DST 에 따라 db_make_timestamp / db_make_timestampltz / tz_create_session_tzid_for_timestamp_core +
 * db_make_timestamptz.
 * 바뀐 것: 세 벌을 DST 템플릿 하나로 합쳤다(+38줄). 숫자→정수 단계를 같은 파일의 숫자 셀에 위임해 반올림·오버플로 규칙이 한 곳에서만 정의된다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_number_to_timestamp (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *,
				      date_conversion_error *error)
{
  TP_DOMAIN_STATUS status =
	  tp_value_convert_number < SRC, DB_TYPE_INTEGER, DOMAIN_CONVERT_ASSIGN > (src, target, &tp_Integer_domain, error);
  if (status != DOMAIN_COMPATIBLE)
    {
      return status;
    }
  int tmpint = db_get_int (target);
  if (tmpint < 0)
    {
      return DOMAIN_INCOMPATIBLE;
    }
  if constexpr (DST == DB_TYPE_TIMESTAMP)
    {
      db_make_timestamp (target, (DB_UTIME) tmpint);
    }
  else if constexpr (DST == DB_TYPE_TIMESTAMPLTZ)
    {
      db_make_timestampltz (target, (DB_UTIME) tmpint);
    }
  else
    {
      static_assert (DST == DB_TYPE_TIMESTAMPTZ, "missing timestamp target");
      DB_TIMESTAMPTZ v_timestamptz;
      v_timestamptz.timestamp = (DB_UTIME) tmpint;
      if (tz_create_session_tzid_for_timestamp_core (&v_timestamptz.timestamp, &v_timestamptz.tz_id, error) !=
	  NO_ERROR)
	{
	  return DOMAIN_INCOMPATIBLE;
	}
      db_make_timestamptz (target, &v_timestamptz);
    }

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_char_to_timestamp — CHAR·VARCHAR → TIMESTAMP 셀. 게이트가 고른 뒤 행마다 tp_value_convert 가 부른다.
 * develop: develop 에 없음 — 이 PR 이 신설. tp_value_cast_internal `case DB_TYPE_TIMESTAMP:`(object_domain.c:7921) 안
 * VARCHAR/CHAR 분기였다.
 * 이 PR: tp_atoutime_core 로 파싱해 실패하면 DOMAIN_ERROR, 성공하면 db_make_timestamp.
 * 바뀐 것: switch 분기를 함수로 떼어낸 것이고, 날짜 API 를 er_set 하지 않는 _core 변종으로 바꾼 것이 유일한 실질 차이다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_char_to_timestamp (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				    date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;
  DB_UTIME v_utime;

  if (tp_atoutime_core (src, &v_utime, error) != NO_ERROR)
    {
      status = DOMAIN_ERROR;
    }
  else
    {
      db_make_timestamp (target, v_utime);
    }

  return status;
}

/*
 * [리뷰] tp_value_convert_date_to_timestamp — DATE → TIMESTAMP 셀 — 자정(00:00:00)으로 세션 타임존 기준 인코딩한다.
 * develop: develop 에 없음 — 이 PR 이 신설. `case DB_TYPE_TIMESTAMP:`(7921) 안에서 DATE 와 DATETIME 이 한 case 로 묶여 `if
 * (original_type == DB_TYPE_DATE)` 로 갈라졌다.
 * 이 PR: db_time_encode_core 로 0시0분0초를 만들고 db_timestamp_encode_ses_core 로 인코딩, 실패하면 DOMAIN_OVERFLOW.
 * 바뀐 것: 묶인 DATE/DATETIME case 를 둘로 나누면서 안쪽 if 가 사라졌다. 그 자리에 중첩 `{ { … } }` 만 흔적으로 남고, 함수 끝에 도달 불가 return 이 하나
 * 더 붙어 있다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_date_to_timestamp (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				    date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;
  DB_UTIME v_utime;
  DB_TIME v_time;
  DB_DATE v_date;

  {
    {
      v_date = *db_get_date (src);
      db_time_encode_core (&v_time, 0, 0, 0, error);
    }

    if (db_timestamp_encode_ses_core (&v_date, &v_time, &v_utime, NULL, error) == NO_ERROR)
      {
	db_make_timestamp (target, v_utime);
      }
    else
      {
	status = DOMAIN_OVERFLOW;
      }
    return status;
  }

  return status;
}

/*
 * [리뷰] tp_value_convert_timestampltz_to_timestamp — TIMESTAMPLTZ → TIMESTAMP 셀 — 둘 다 UTC 저장이라 값만 옮긴다.
 * develop: develop 에 없음 — 이 PR 이 신설. `case DB_TYPE_TIMESTAMP:`(7921) 안 TIMESTAMPLTZ 분기였다.
 * 이 PR: db_make_timestamp (target, *db_get_timestamp (src)) 한 줄, 항상 DOMAIN_COMPATIBLE.
 * 바뀐 것: switch 분기를 함수로 분리했을 뿐 계산은 develop 과 같다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_timestampltz_to_timestamp (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  /* copy timestamp (UTC) */
  db_make_timestamp (target, *db_get_timestamp (src));

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_timestamptz_to_timestamp — TIMESTAMPTZ → TIMESTAMP 셀 — TZ 를 버리고 UTC 시각만 남긴다.
 * develop: develop 에 없음 — 이 PR 이 신설. `case DB_TYPE_TIMESTAMP:`(7921) 안 TIMESTAMPTZ 분기였다.
 * 이 PR: db_get_timestamptz 의 .timestamp 만 꺼내 db_make_timestamp.
 * 바뀐 것: switch 분기를 함수로 분리했을 뿐 계산은 develop 과 같다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_timestamptz_to_timestamp (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  DB_TIMESTAMPTZ v_timestamptz;

  v_timestamptz = *db_get_timestamptz (src);
  /* copy timestamp (UTC) */
  db_make_timestamp (target, v_timestamptz.timestamp);

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_datetime_to_timestamp — DATETIME → TIMESTAMP 셀 — 밀리초를 버리고 세션 타임존 기준으로 인코딩한다.
 * develop: develop 에 없음 — 이 PR 이 신설. `case DB_TYPE_TIMESTAMP:`(7921) 안에서 DATE 와 한 case 로 묶여 있었다.
 * 이 PR: v_time = datetime.time / 1000 으로 밀리초를 버리고 db_timestamp_encode_ses_core, 실패하면 DOMAIN_OVERFLOW.
 * 바뀐 것: 묶인 case 를 분리. DATE 판과 마찬가지로 빈 중첩 블록과 도달 불가 return 이 남았다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_datetime_to_timestamp (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
					date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;
  DB_UTIME v_utime;
  DB_DATETIME v_datetime;
  DB_TIME v_time;
  DB_DATE v_date;

  {
    {
      v_datetime = *db_get_datetime (src);
      v_date = v_datetime.date;
      v_time = v_datetime.time / 1000;
    }

    if (db_timestamp_encode_ses_core (&v_date, &v_time, &v_utime, NULL, error) == NO_ERROR)
      {
	db_make_timestamp (target, v_utime);
      }
    else
      {
	status = DOMAIN_OVERFLOW;
      }
    return status;
  }

  return status;
}

/*
 * [리뷰] tp_value_convert_datetimeltz_to_timestamp — DATETIMELTZ → TIMESTAMP 셀 — 소스가 이미 UTC 라 UTC 인코딩을 쓴다.
 * develop: develop 에 없음 — 이 PR 이 신설. `case DB_TYPE_TIMESTAMP:`(7921) 안 DATETIMELTZ 분기였다.
 * 이 PR: db_timestamp_encode_utc_core, 실패하면 DOMAIN_OVERFLOW.
 * 바뀐 것: switch 분기 분리 + 날짜 API 를 _core 변종으로 교체. 계산 순서·반환 status 는 develop 과 같다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_datetimeltz_to_timestamp (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;
  DB_UTIME v_utime;
  DB_DATETIME v_datetime;
  DB_TIME v_time;
  DB_DATE v_date;

  v_datetime = *db_get_datetime (src);
  v_date = v_datetime.date;
  v_time = v_datetime.time / 1000;

  if (db_timestamp_encode_utc_core (&v_date, &v_time, &v_utime, error) == NO_ERROR)
    {
      db_make_timestamp (target, v_utime);
    }
  else
    {
      status = DOMAIN_OVERFLOW;
    }

  return status;
}

/*
 * [리뷰] tp_value_convert_datetimetz_to_timestamp — DATETIMETZ → TIMESTAMP 셀 — UTC 부분만 인코딩하고 TZ 는 버린다.
 * develop: develop 에 없음 — 이 PR 이 신설. `case DB_TYPE_TIMESTAMP:`(7921) 안 DATETIMETZ 분기였다.
 * 이 PR: datetimetz.datetime 에서 date/time 을 꺼내 db_timestamp_encode_utc_core, 실패하면 DOMAIN_OVERFLOW.
 * 바뀐 것: switch 분기 분리 + _core 교체. 계산은 develop 과 같다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_datetimetz_to_timestamp (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;
  DB_UTIME v_utime;
  DB_DATETIMETZ v_datetimetz;
  DB_TIME v_time;
  DB_DATE v_date;

  v_datetimetz = *db_get_datetimetz (src);
  v_date = v_datetimetz.datetime.date;
  v_time = v_datetimetz.datetime.time / 1000;

  if (db_timestamp_encode_utc_core (&v_date, &v_time, &v_utime, error) == NO_ERROR)
    {
      db_make_timestamp (target, v_utime);
    }
  else
    {
      status = DOMAIN_OVERFLOW;
    }

  return status;
}

/*
 * [리뷰] tp_value_convert_enumeration_to_timestamp — ENUM → TIMESTAMP 셀 — ENUM 이름 문자열을 거쳐 문자열 파싱 규칙을 그대로 쓴다.
 * develop: develop 에 없음 — 이 PR 이 신설. `case DB_TYPE_TIMESTAMP:`(7921) 안 ENUMERATION 분기로, varchar 뷰를 만든 뒤
 * tp_value_cast_internal 을 재귀 호출해 switch 를 다시 돌았다.
 * 이 PR: tp_enumeration_to_varchar 로 얕은 VARCHAR 뷰를 만들고 tp_value_convert_char_to_timestamp 를 직접 부른다.
 * 바뀐 것: 재귀 호출이 목표 셀 직접 호출로 바뀌었다(+18줄) — 행마다 switch 를 두 번 돌던 비용이 없어진다. 끝에 도달 불가 return 이 남았다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_enumeration_to_timestamp (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;

  {
    DB_VALUE varchar_val;
    if (tp_enumeration_to_varchar (src, &varchar_val) != NO_ERROR)
      {
	return DOMAIN_ERROR;
      }
    status = tp_value_convert_char_to_timestamp (&varchar_val, target, desired_domain, error);
    return status;
  }

  return status;
}

/*
 * [리뷰] tp_value_convert_char_to_timestamptz — CHAR·VARCHAR → TIMESTAMPTZ 셀.
 * develop: develop 에 없음 — 이 PR 이 신설. `case DB_TYPE_TIMESTAMPTZ:`(object_domain.c:8035) 안 VARCHAR/CHAR 분기였다.
 * 이 PR: tp_atotimestamptz_core 로 파싱(실패 DOMAIN_ERROR) 후 db_make_timestamptz.
 * 바뀐 것: switch 분기 분리 + _core 교체. 계산은 develop 과 같다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_char_to_timestamptz (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				      date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;
  DB_TIMESTAMPTZ v_timestamptz;

  if (tp_atotimestamptz_core (src, &v_timestamptz, error) != NO_ERROR)
    {
      status = DOMAIN_ERROR;
    }
  else
    {
      db_make_timestamptz (target, &v_timestamptz);
    }

  return status;
}

/*
 * [리뷰] tp_value_convert_date_to_timestamptz — DATE → TIMESTAMPTZ 셀 — 자정을 세션 TZ 로 해석해 UTC 시각과 TZ_ID 를 함께 만든다.
 * develop: develop 에 없음 — 이 PR 이 신설. `case DB_TYPE_TIMESTAMPTZ:`(8035) 안 DATE 분기로, DATETIME 과 한 case 였다.
 * 이 PR: v_time=0 으로 db_timestamp_encode_ses_core 에 tz_id 출력 인자를 함께 넘기고 실패하면 DOMAIN_ERROR.
 * 바뀐 것: case 분리. DATE/DATETIME 공용 코드가 갈라지면서 `assert (DB_TYPE_DATE == DB_TYPE_DATE)` 라는 항상 참인 assert 가 흔적으로 남았다
 * — develop 의 `if (original_type == DB_TYPE_DATE)` 자리다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_date_to_timestamptz (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				      date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;
  DB_TIMESTAMPTZ v_timestamptz;
  DB_TIME v_time;
  DB_DATE v_date;

  /* convert from session to UTC */
  {
    assert (DB_TYPE_DATE == DB_TYPE_DATE);
    v_date = *db_get_date (src);
    v_time = 0;
  }

  if (db_timestamp_encode_ses_core (&v_date, &v_time, &v_timestamptz.timestamp, &v_timestamptz.tz_id, error) !=
      NO_ERROR)
    {
      status = DOMAIN_ERROR;
    }
  else
    {
      db_make_timestamptz (target, &v_timestamptz);
    }

  return status;
}

/*
 * [리뷰] tp_value_convert_timestamp_to_timestamptz — TIMESTAMP → TIMESTAMPTZ 셀 — UTC 시각은 그대로 두고 세션 TZ_ID 를 붙인다.
 * develop: develop 에 없음 — 이 PR 이 신설. `case DB_TYPE_TIMESTAMPTZ:`(8035) 안 TIMESTAMP 분기였다.
 * 이 PR: tz_create_session_tzid_for_timestamp_core 로 TZ_ID 를 만들고(실패 DOMAIN_ERROR) db_make_timestamptz.
 * 바뀐 것: switch 분기 분리 + _core 교체.
 */
static TP_DOMAIN_STATUS
tp_value_convert_timestamp_to_timestamptz (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  DB_TIMESTAMPTZ v_timestamptz;

  /* copy TS value and create TZ_ID for system TZ */
  v_timestamptz.timestamp = *db_get_timestamp (src);

  if (tz_create_session_tzid_for_timestamp_core (&v_timestamptz.timestamp, & (v_timestamptz.tz_id), error) !=
      NO_ERROR)
    {
      return DOMAIN_ERROR;
    }

  db_make_timestamptz (target, &v_timestamptz);

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_datetime_to_timestamptz — DATETIME → TIMESTAMPTZ 셀 — 세션 TZ 로 해석해 UTC+TZ_ID 로 바꾼다.
 * develop: develop 에 없음 — 이 PR 이 신설. `case DB_TYPE_TIMESTAMPTZ:`(8035) 안 DATETIME 분기로 DATE 와 한 case 였다.
 * 이 PR: 밀리초를 버리고 db_timestamp_encode_ses_core 에 tz_id 출력 인자를 넘긴다. 실패하면 DOMAIN_ERROR.
 * 바뀐 것: case 분리. 빈 중첩 블록이 흔적으로 남았다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_datetime_to_timestamptz (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;
  DB_TIMESTAMPTZ v_timestamptz;
  DB_DATETIME v_datetime;
  DB_TIME v_time;
  DB_DATE v_date;

  /* convert from session to UTC */
  {
    v_datetime = *db_get_datetime (src);
    v_date = v_datetime.date;
    v_time = v_datetime.time / 1000;
  }

  if (db_timestamp_encode_ses_core (&v_date, &v_time, &v_timestamptz.timestamp, &v_timestamptz.tz_id, error) !=
      NO_ERROR)
    {
      status = DOMAIN_ERROR;
    }
  else
    {
      db_make_timestamptz (target, &v_timestamptz);
    }

  return status;
}

/*
 * [리뷰] tp_value_convert_datetimeltz_to_timestamptz — DATETIMELTZ → TIMESTAMPTZ 셀 — UTC 값은 UTC 인코딩으로 옮기고 TZ_ID
 * 만 세션 것으로 만든다.
 * develop: develop 에 없음 — 이 PR 이 신설. `case DB_TYPE_TIMESTAMPTZ:`(8035) 안 DATETIMELTZ 분기였다.
 * 이 PR: db_timestamp_encode_utc_core(실패 DOMAIN_ERROR) 뒤 tz_create_session_tzid_for_datetime_core(…, true, …)로
 * TZ_ID 를 만든다.
 * 바뀐 것: switch 분기 분리 + _core 교체. 계산은 develop 과 같다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_datetimeltz_to_timestamptz (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;
  DB_TIMESTAMPTZ v_timestamptz;
  DB_DATETIME v_datetime;
  DB_TIME v_time;
  DB_DATE v_date;

  v_datetime = *db_get_datetime (src);
  v_date = v_datetime.date;
  v_time = v_datetime.time / 1000;

  /* encode DT as UTC and the TZ of session */
  if (db_timestamp_encode_utc_core (&v_date, &v_time, &v_timestamptz.timestamp, error) != NO_ERROR)
    {
      return DOMAIN_ERROR;
    }
  if (tz_create_session_tzid_for_datetime_core (&v_datetime, true, & (v_timestamptz.tz_id), error) != NO_ERROR)
    {
      status = DOMAIN_ERROR;
    }
  else
    {
      db_make_timestamptz (target, &v_timestamptz);
    }

  return status;
}

/*
 * [리뷰] tp_value_convert_datetimetz_to_timestamptz — DATETIMETZ → TIMESTAMPTZ 셀 — UTC 로 인코딩하고 소스의 TZ_ID 를 그대로
 * 복사한다.
 * develop: develop 에 없음 — 이 PR 이 신설. `case DB_TYPE_TIMESTAMPTZ:`(8035) 안 DATETIMETZ 분기였다.
 * 이 PR: db_timestamp_encode_utc_core 성공 시 tz_id 복사 후 db_make_timestamptz, 실패하면 DOMAIN_OVERFLOW.
 * 바뀐 것: switch 분기 분리 + _core 교체.
 */
static TP_DOMAIN_STATUS
tp_value_convert_datetimetz_to_timestamptz (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;
  DB_TIMESTAMPTZ v_timestamptz;
  DB_DATETIMETZ v_datetimetz;
  DB_TIME v_time;
  DB_DATE v_date;

  v_datetimetz = *db_get_datetimetz (src);
  v_date = v_datetimetz.datetime.date;
  v_time = v_datetimetz.datetime.time / 1000;

  /* encode TS to DT (UTC) and copy TZ from DT_TZ */
  if (db_timestamp_encode_utc_core (&v_date, &v_time, &v_timestamptz.timestamp, error) == NO_ERROR)
    {
      v_timestamptz.tz_id = v_datetimetz.tz_id;
      db_make_timestamptz (target, &v_timestamptz);
    }
  else
    {
      status = DOMAIN_OVERFLOW;
    }

  return status;
}

/*
 * [리뷰] tp_value_convert_enumeration_to_timestamptz — ENUM → TIMESTAMPTZ 셀.
 * develop: develop 에 없음 — 이 PR 이 신설. `case DB_TYPE_TIMESTAMPTZ:`(8035) 안 ENUMERATION 분기로
 * tp_value_cast_internal 재귀였다.
 * 이 PR: tp_enumeration_to_varchar 뒤 tp_value_convert_char_to_timestamptz 를 직접 부른다.
 * 바뀐 것: 재귀 → 직접 호출(+18줄). 끝에 도달 불가 return 이 남았다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_enumeration_to_timestamptz (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;

  {
    DB_VALUE varchar_val;
    if (tp_enumeration_to_varchar (src, &varchar_val) != NO_ERROR)
      {
	return DOMAIN_ERROR;
      }
    status = tp_value_convert_char_to_timestamptz (&varchar_val, target, desired_domain, error);
    return status;
  }

  return status;
}

/*
 * [리뷰] tp_value_convert_char_to_timestampltz — CHAR·VARCHAR → TIMESTAMPLTZ 셀 — TZ 가 붙은 문자열로 읽고 UTC 시각만 남긴다.
 * develop: develop 에 없음 — 이 PR 이 신설. `case DB_TYPE_TIMESTAMPLTZ:`(object_domain.c:8167) 안 VARCHAR/CHAR 분기였다.
 * 이 PR: tp_atotimestamptz_core 로 읽고(실패 DOMAIN_ERROR) .timestamp 만 db_make_timestampltz.
 * 바뀐 것: switch 분기 분리 + _core 교체.
 */
static TP_DOMAIN_STATUS
tp_value_convert_char_to_timestampltz (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				       date_conversion_error *error)
{
  DB_TIMESTAMPTZ v_timestamptz;

  /* read as DATETIMETZ */
  if (tp_atotimestamptz_core (src, &v_timestamptz, error) != NO_ERROR)
    {
      return DOMAIN_ERROR;
    }
  else
    {
      db_make_timestampltz (target, v_timestamptz.timestamp);
    }

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_date_to_timestampltz — DATE → TIMESTAMPLTZ 셀 — 자정을 세션 TZ 로 인코딩해 UTC 로 저장한다.
 * develop: develop 에 없음 — 이 PR 이 신설. `case DB_TYPE_TIMESTAMPLTZ:`(8167) 안 DATE 분기로 DATETIME 과 한 case 였다.
 * 이 PR: v_time=0 으로 db_timestamp_encode_ses_core, 실패하면 DOMAIN_OVERFLOW.
 * 바뀐 것: case 분리. 여기에도 항상 참인 `assert (DB_TYPE_DATE == DB_TYPE_DATE)` 와 빈 중첩 블록이 남았다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_date_to_timestampltz (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				       date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;
  DB_UTIME v_utime;
  DB_TIME v_time;
  DB_DATE v_date;

  {
    {
      assert (DB_TYPE_DATE == DB_TYPE_DATE);
      v_date = *db_get_date (src);
      v_time = 0;
    }

    if (db_timestamp_encode_ses_core (&v_date, &v_time, &v_utime, NULL, error) != NO_ERROR)
      {
	status = DOMAIN_OVERFLOW;
	return status;
      }

    db_make_timestampltz (target, v_utime);
  }

  return status;
}

/*
 * [리뷰] tp_value_convert_timestamp_to_timestampltz — TIMESTAMP → TIMESTAMPLTZ 셀 — 둘 다 UTC 저장이라 값만 옮긴다.
 * develop: develop 에 없음 — 이 PR 이 신설. `case DB_TYPE_TIMESTAMPLTZ:`(8167) 안 TIMESTAMP 분기였다.
 * 이 PR: db_make_timestampltz (target, *db_get_timestamp (src)) 한 줄.
 * 바뀐 것: switch 분기 분리. 계산은 develop 과 같다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_timestamp_to_timestampltz (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  /* original value stored in UTC, copy it */
  db_make_timestampltz (target, *db_get_timestamp (src));

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_timestamptz_to_timestampltz — TIMESTAMPTZ → TIMESTAMPLTZ 셀 — TZ_ID 를 버리고 UTC 시각만 남긴다.
 * develop: develop 에 없음 — 이 PR 이 신설. `case DB_TYPE_TIMESTAMPLTZ:`(8167) 안 TIMESTAMPTZ 분기였다.
 * 이 PR: .timestamp 만 db_make_timestampltz.
 * 바뀐 것: switch 분기 분리. 계산은 develop 과 같다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_timestamptz_to_timestampltz (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  DB_TIMESTAMPTZ v_timestamptz;

  v_timestamptz = *db_get_timestamptz (src);
  /* original value stored in UTC, copy it */
  db_make_timestampltz (target, v_timestamptz.timestamp);

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_datetime_to_timestampltz — DATETIME → TIMESTAMPLTZ 셀 — 세션 TZ 로 해석해 UTC 로 저장한다.
 * develop: develop 에 없음 — 이 PR 이 신설. `case DB_TYPE_TIMESTAMPLTZ:`(8167) 안 DATETIME 분기로 DATE 와 한 case 였다.
 * 이 PR: 밀리초를 버리고 db_timestamp_encode_ses_core, 실패하면 DOMAIN_OVERFLOW.
 * 바뀐 것: case 분리, 빈 중첩 블록이 남았다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_datetime_to_timestampltz (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;
  DB_UTIME v_utime;
  DB_DATETIME v_datetime;
  DB_TIME v_time;
  DB_DATE v_date;

  {
    {
      v_datetime = *db_get_datetime (src);
      v_date = v_datetime.date;
      v_time = v_datetime.time / 1000;
    }

    if (db_timestamp_encode_ses_core (&v_date, &v_time, &v_utime, NULL, error) != NO_ERROR)
      {
	status = DOMAIN_OVERFLOW;
	return status;
      }

    db_make_timestampltz (target, v_utime);
  }

  return status;
}

/*
 * [리뷰] tp_value_convert_datetimeltz_to_timestampltz — DATETIMELTZ → TIMESTAMPLTZ 셀 — 둘 다 UTC 라 UTC 인코딩만 한다.
 * develop: develop 에 없음 — 이 PR 이 신설. `case DB_TYPE_TIMESTAMPLTZ:`(8167) 안 DATETIMELTZ 분기였다.
 * 이 PR: db_timestamp_encode_utc_core, 실패하면 DOMAIN_OVERFLOW.
 * 바뀐 것: switch 분기 분리 + _core 교체.
 */
static TP_DOMAIN_STATUS
tp_value_convert_datetimeltz_to_timestampltz (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;
  DB_UTIME v_utime;
  DB_DATETIME v_datetime;
  DB_TIME v_time;
  DB_DATE v_date;

  {
    v_datetime = *db_get_datetime (src);
    v_date = v_datetime.date;
    v_time = v_datetime.time / 1000;
  }

  /* both values are in UTC */
  if (db_timestamp_encode_utc_core (&v_date, &v_time, &v_utime, error) == NO_ERROR)
    {
      db_make_timestampltz (target, v_utime);
    }
  else
    {
      status = DOMAIN_OVERFLOW;
    }

  return status;
}

/*
 * [리뷰] tp_value_convert_datetimetz_to_timestampltz — DATETIMETZ → TIMESTAMPLTZ 셀 — UTC 부분만 인코딩하고 TZ_ID 는 버린다.
 * develop: develop 에 없음 — 이 PR 이 신설. `case DB_TYPE_TIMESTAMPLTZ:`(8167) 안 DATETIMETZ 분기였다.
 * 이 PR: db_timestamp_encode_utc_core, 실패하면 DOMAIN_OVERFLOW.
 * 바뀐 것: case 분리. `assert (DB_TYPE_DATETIMETZ == DB_TYPE_DATETIMETZ)` 라는 항상 참인 흔적 assert 가 남았다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_datetimetz_to_timestampltz (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;
  DB_UTIME v_utime;
  DB_DATETIMETZ v_datetimetz;
  DB_TIME v_time;
  DB_DATE v_date;

  {
    assert (DB_TYPE_DATETIMETZ == DB_TYPE_DATETIMETZ);
    v_datetimetz = *db_get_datetimetz (src);
    v_date = v_datetimetz.datetime.date;
    v_time = v_datetimetz.datetime.time / 1000;
  }

  /* both values are in UTC */
  if (db_timestamp_encode_utc_core (&v_date, &v_time, &v_utime, error) == NO_ERROR)
    {
      db_make_timestampltz (target, v_utime);
    }
  else
    {
      status = DOMAIN_OVERFLOW;
    }

  return status;
}

/*
 * [리뷰] tp_value_convert_enumeration_to_timestampltz — ENUM → TIMESTAMPLTZ 셀.
 * develop: develop 에 없음 — 이 PR 이 신설. `case DB_TYPE_TIMESTAMPLTZ:`(8167) 안 ENUMERATION 분기로 재귀 캐스트였다.
 * 이 PR: tp_enumeration_to_varchar 뒤 tp_value_convert_char_to_timestampltz 직접 호출.
 * 바뀐 것: 재귀 → 직접 호출(+18줄), 끝에 도달 불가 return.
 */
static TP_DOMAIN_STATUS
tp_value_convert_enumeration_to_timestampltz (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;

  {
    DB_VALUE varchar_val;
    if (tp_enumeration_to_varchar (src, &varchar_val) != NO_ERROR)
      {
	return DOMAIN_ERROR;
      }
    status = tp_value_convert_char_to_timestampltz (&varchar_val, target, desired_domain, error);
    return status;
  }

  return status;
}

/*
 * [리뷰] tp_value_convert_char_to_datetime — CHAR·VARCHAR → DATETIME 셀.
 * develop: develop 에 없음 — 이 PR 이 신설. `case DB_TYPE_DATETIME:`(object_domain.c:8280) 안 VARCHAR/CHAR 분기였다.
 * 이 PR: tp_atoudatetime_core 로 파싱(실패 DOMAIN_ERROR) 후 db_make_datetime.
 * 바뀐 것: switch 분기 분리 + _core 교체.
 */
static TP_DOMAIN_STATUS
tp_value_convert_char_to_datetime (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				   date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;
  DB_DATETIME v_datetime;

  if (tp_atoudatetime_core (src, &v_datetime, error) != NO_ERROR)
    {
      status = DOMAIN_ERROR;
    }
  else
    {
      db_make_datetime (target, &v_datetime);
    }

  return status;
}

/*
 * [리뷰] tp_value_convert_date_to_datetime — DATE → DATETIME 셀 — 시각을 0 으로 채운다.
 * develop: develop 에 없음 — 이 PR 이 신설. `case DB_TYPE_DATETIME:`(8280) 안 DATE 분기였다.
 * 이 PR: date 복사, time=0, db_make_datetime, 항상 DOMAIN_COMPATIBLE.
 * 바뀐 것: switch 분기 분리. 계산은 develop 과 같다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_date_to_datetime (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				   date_conversion_error *error)
{
  DB_DATETIME v_datetime;

  v_datetime.date = *db_get_date (src);
  v_datetime.time = 0;
  db_make_datetime (target, &v_datetime);

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_timestamp_to_datetime — TIMESTAMP **과 TIMESTAMPLTZ** 를 DATETIME 으로 바꾸는 셀 — 변환 표가 두 소스
 * 타입을 이 한 셀에 매핑한다(object_domain_convert.cpp:8024~8026).
 * develop: develop 에 없음 — 이 PR 이 신설. `case DB_TYPE_DATETIME:`(8280) 안에서 develop 도 TIMESTAMP·TIMESTAMPLTZ 를 한
 * case 로 묶었다.
 * 이 PR: db_timestamp_decode_ses_core 로 세션 TZ 기준 날짜·시각을 뽑고(실패 DOMAIN_ERROR) 밀리초로 환산해 db_make_datetime.
 * 바뀐 것: switch 분기 분리 + _core 교체. 두 소스 공유는 표에서 그대로 유지된다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_timestamp_to_datetime (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
					date_conversion_error *error)
{
  DB_UTIME v_utime;
  DB_DATETIME v_datetime;
  DB_TIME v_time;
  DB_DATE v_date;

  v_utime = *db_get_timestamp (src);
  if (db_timestamp_decode_ses_core (&v_utime, &v_date, &v_time, error) != NO_ERROR)
    {
      return DOMAIN_ERROR;
    }
  v_datetime.date = v_date;
  v_datetime.time = v_time * 1000;
  db_make_datetime (target, &v_datetime);

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_timestamptz_to_datetime — TIMESTAMPTZ → DATETIME 셀 — 값에 붙은 TZ_ID 로 지역 시각을 푼다.
 * develop: develop 에 없음 — 이 PR 이 신설. `case DB_TYPE_DATETIME:`(8280) 안 TIMESTAMPTZ 분기였다.
 * 이 PR: db_timestamp_decode_w_tz_id_core(실패 DOMAIN_ERROR) 뒤 db_make_datetime.
 * 바뀐 것: switch 분기 분리 + _core 교체.
 */
static TP_DOMAIN_STATUS
tp_value_convert_timestamptz_to_datetime (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  DB_TIMESTAMPTZ v_timestamptz;
  DB_DATETIME v_datetime;
  DB_TIME v_time;
  DB_DATE v_date;

  v_timestamptz = *db_get_timestamptz (src);
  if (db_timestamp_decode_w_tz_id_core (&v_timestamptz.timestamp, &v_timestamptz.tz_id, &v_date, &v_time, error)
      != NO_ERROR)
    {
      return DOMAIN_ERROR;
    }
  v_datetime.date = v_date;
  v_datetime.time = v_time * 1000;
  db_make_datetime (target, &v_datetime);

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_datetimeltz_to_datetime — DATETIMELTZ → DATETIME 셀 — UTC 저장값을 세션 TZ 지역 시각으로 바꾼다.
 * develop: develop 에 없음 — 이 PR 이 신설. `case DB_TYPE_DATETIME:`(8280) 안 DATETIMELTZ 분기였다.
 * 이 PR: tz_datetimeltz_to_local_core(실패 DOMAIN_ERROR) 뒤 db_make_datetime.
 * 바뀐 것: switch 분기 분리 + _core 교체.
 */
static TP_DOMAIN_STATUS
tp_value_convert_datetimeltz_to_datetime (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  DB_DATETIME v_datetime;

  {
    DB_DATETIME utc_dt;

    /* DATETIMELTZ store in UTC, DATETIME in session TZ */
    utc_dt = *db_get_datetime (src);
    if (tz_datetimeltz_to_local_core (&utc_dt, &v_datetime, error) != NO_ERROR)
      {
	return DOMAIN_ERROR;
      }

    db_make_datetime (target, &v_datetime);
  }

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_datetimetz_to_datetime — DATETIMETZ → DATETIME 셀 — 값에 붙은 TZ_ID 로 지역 시각을 푼다.
 * develop: develop 에 없음 — 이 PR 이 신설. `case DB_TYPE_DATETIME:`(8280) 안 DATETIMETZ 분기였다.
 * 이 PR: tz_utc_datetimetz_to_local_core 성공 시 db_make_datetime, 실패하면 DOMAIN_ERROR.
 * 바뀐 것: switch 분기 분리 + _core 교체.
 */
static TP_DOMAIN_STATUS
tp_value_convert_datetimetz_to_datetime (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
    date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;
  DB_DATETIME v_datetime;
  DB_DATETIMETZ v_datetimetz;

  /* DATETIMETZ store in UTC, DATETIME in session TZ */
  v_datetimetz = *db_get_datetimetz (src);
  if (tz_utc_datetimetz_to_local_core (&v_datetimetz.datetime, &v_datetimetz.tz_id, &v_datetime, error) ==
      NO_ERROR)
    {
      db_make_datetime (target, &v_datetime);
    }
  else
    {
      status = DOMAIN_ERROR;
    }

  return status;
}

/*
 * [리뷰] tp_value_convert_enumeration_to_datetime — ENUM → DATETIME 셀.
 * develop: develop 에 없음 — 이 PR 이 신설. `case DB_TYPE_DATETIME:`(8280) 안 ENUMERATION 분기로 재귀 캐스트였다.
 * 이 PR: tp_enumeration_to_varchar 뒤 tp_value_convert_char_to_datetime 직접 호출.
 * 바뀐 것: 재귀 → 직접 호출(+18줄), 끝에 도달 불가 return.
 */
static TP_DOMAIN_STATUS
tp_value_convert_enumeration_to_datetime (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;

  {
    DB_VALUE varchar_val;
    if (tp_enumeration_to_varchar (src, &varchar_val) != NO_ERROR)
      {
	return DOMAIN_ERROR;
      }
    status = tp_value_convert_char_to_datetime (&varchar_val, target, desired_domain, error);
    return status;
  }

  return status;
}

/*
 * [리뷰] tp_value_convert_char_to_datetimeltz — CHAR·VARCHAR → DATETIMELTZ 셀 — TZ 포함 문자열로 읽고 UTC datetime 만 남긴다.
 * develop: develop 에 없음 — 이 PR 이 신설. `case DB_TYPE_DATETIMELTZ:`(object_domain.c:8375) 안 VARCHAR/CHAR 분기였다.
 * 이 PR: tp_atodatetimetz_core 로 읽고(실패 DOMAIN_ERROR) .datetime 만 db_make_datetimeltz.
 * 바뀐 것: switch 분기 분리 + _core 교체.
 */
static TP_DOMAIN_STATUS
tp_value_convert_char_to_datetimeltz (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				      date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;
  DB_DATETIMETZ v_datetimetz;

  if (tp_atodatetimetz_core (src, &v_datetimetz, error) != NO_ERROR)
    {
      status = DOMAIN_ERROR;
    }
  else
    {
      db_make_datetimeltz (target, &v_datetimetz.datetime);
    }

  return status;
}

/*
 * [리뷰] tp_value_convert_date_to_datetimeltz — DATE → DATETIMELTZ 셀 — 자정을 세션 TZ 로 해석해 UTC 로 저장한다.
 * develop: develop 에 없음 — 이 PR 이 신설. `case DB_TYPE_DATETIMELTZ:`(8375) 안 DATE 분기였다.
 * 이 PR: date+time0 으로 tz_create_datetimetz_from_ses_core(실패 DOMAIN_ERROR) 뒤 .datetime 을 db_make_datetimeltz.
 * 바뀐 것: case 분리, 빈 중첩 블록이 남았다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_date_to_datetimeltz (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				      date_conversion_error *error)
{
  DB_DATETIME v_datetime;
  DB_DATETIMETZ v_datetimetz;

  {
    v_datetime.date = *db_get_date (src);
    v_datetime.time = 0;
  }

  if (tz_create_datetimetz_from_ses_core (&v_datetime, &v_datetimetz, error) != NO_ERROR)
    {
      return DOMAIN_ERROR;
    }
  db_make_datetimeltz (target, &v_datetimetz.datetime);

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_timestamp_to_datetimeltz — TIMESTAMP → DATETIMELTZ 셀 — UTC 시각을 UTC datetime 으로 푼다.
 * develop: develop 에 없음 — 이 PR 이 신설. `case DB_TYPE_DATETIMELTZ:`(8375) 안 TIMESTAMP 분기였다.
 * 이 PR: db_timestamp_decode_utc 로 풀어 밀리초 환산 후 db_make_datetimeltz, 항상 DOMAIN_COMPATIBLE.
 * 바뀐 것: case 분리. 이 셀만 _core 가 아닌 db_timestamp_decode_utc 를 그대로 쓰는데, 그 함수가 er_set 하지 않아 바꿀 필요가 없었기 때문이다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_timestamp_to_datetimeltz (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  DB_UTIME v_utime;
  DB_DATETIME v_datetime;
  DB_TIME v_time;
  DB_DATE v_date;

  v_utime = *db_get_timestamp (src);

  (void) db_timestamp_decode_utc (&v_utime, &v_date, &v_time);
  v_datetime.time = v_time * 1000;
  v_datetime.date = v_date;
  db_make_datetimeltz (target, &v_datetime);

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_timestamptz_to_datetimeltz — TIMESTAMPTZ → DATETIMELTZ 셀 — TZ_ID 를 버리고 UTC datetime 만
 * 남긴다.
 * develop: develop 에 없음 — 이 PR 이 신설. `case DB_TYPE_DATETIMELTZ:`(8375) 안 TIMESTAMPTZ 분기였다.
 * 이 PR: db_timestamp_decode_utc 로 풀어 db_make_datetimeltz.
 * 바뀐 것: switch 분기 분리. 계산은 develop 과 같다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_timestamptz_to_datetimeltz (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  DB_TIMESTAMPTZ v_timestamptz;
  DB_DATETIME v_datetime;
  DB_TIME v_time;
  DB_DATE v_date;

  v_timestamptz = *db_get_timestamptz (src);
  (void) db_timestamp_decode_utc (&v_timestamptz.timestamp, &v_date, &v_time);
  v_datetime.time = v_time * 1000;
  v_datetime.date = v_date;
  db_make_datetimeltz (target, &v_datetime);

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_datetime_to_datetimeltz — DATETIME → DATETIMELTZ 셀 — 지역 시각을 세션 TZ 로 해석해 UTC 로 저장한다.
 * develop: develop 에 없음 — 이 PR 이 신설. `case DB_TYPE_DATETIMELTZ:`(8375) 안 DATETIME 분기였다.
 * 이 PR: tz_create_datetimetz_from_ses_core(실패 DOMAIN_ERROR) 뒤 .datetime 을 db_make_datetimeltz.
 * 바뀐 것: case 분리, 빈 중첩 블록이 남았다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_datetime_to_datetimeltz (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  DB_DATETIME v_datetime;
  DB_DATETIMETZ v_datetimetz;

  {
    v_datetime = *db_get_datetime (src);
  }

  if (tz_create_datetimetz_from_ses_core (&v_datetime, &v_datetimetz, error) != NO_ERROR)
    {
      return DOMAIN_ERROR;
    }
  db_make_datetimeltz (target, &v_datetimetz.datetime);

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_datetimetz_to_datetimeltz — DATETIMETZ → DATETIMELTZ 셀 — 둘 다 UTC 저장이라 TZ_ID 만 떼고 복사한다.
 * develop: develop 에 없음 — 이 PR 이 신설. `case DB_TYPE_DATETIMELTZ:`(8375) 안 DATETIMETZ 분기였다.
 * 이 PR: v_datetimetz.datetime 을 db_make_datetimeltz, 항상 DOMAIN_COMPATIBLE.
 * 바뀐 것: switch 분기 분리. 계산은 develop 과 같다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_datetimetz_to_datetimeltz (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  DB_DATETIMETZ v_datetimetz;

  /* copy (UTC) */
  v_datetimetz = *db_get_datetimetz (src);
  db_make_datetimeltz (target, &v_datetimetz.datetime);

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_enumeration_to_datetimeltz — ENUM → DATETIMELTZ 셀.
 * develop: develop 에 없음 — 이 PR 이 신설. `case DB_TYPE_DATETIMELTZ:`(8375) 안 ENUMERATION 분기로 재귀 캐스트였다.
 * 이 PR: tp_enumeration_to_varchar 뒤 tp_value_convert_char_to_datetimeltz 직접 호출.
 * 바뀐 것: 재귀 → 직접 호출(+18줄), 끝에 도달 불가 return.
 */
static TP_DOMAIN_STATUS
tp_value_convert_enumeration_to_datetimeltz (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;

  {
    DB_VALUE varchar_val;
    if (tp_enumeration_to_varchar (src, &varchar_val) != NO_ERROR)
      {
	return DOMAIN_ERROR;
      }
    status = tp_value_convert_char_to_datetimeltz (&varchar_val, target, desired_domain, error);
    return status;
  }

  return status;
}

/*
 * [리뷰] tp_value_convert_char_to_datetimetz — CHAR·VARCHAR → DATETIMETZ 셀.
 * develop: develop 에 없음 — 이 PR 이 신설. `case DB_TYPE_DATETIMETZ:`(object_domain.c:8457) 안 VARCHAR/CHAR 분기였다.
 * 이 PR: tp_atodatetimetz_core 로 읽고(실패 DOMAIN_ERROR) db_make_datetimetz.
 * 바뀐 것: case 분리 + _core 교체, 빈 중첩 블록이 남았다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_char_to_datetimetz (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				     date_conversion_error *error)
{
  DB_DATETIMETZ v_datetimetz;

  {
    if (tp_atodatetimetz_core (src, &v_datetimetz, error) != NO_ERROR)
      {
	return DOMAIN_ERROR;
      }

    db_make_datetimetz (target, &v_datetimetz);
  }

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_date_to_datetimetz — DATE → DATETIMETZ 셀 — 자정을 세션 TZ 로 해석해 UTC+TZ_ID 로 만든다.
 * develop: develop 에 없음 — 이 PR 이 신설. `case DB_TYPE_DATETIMETZ:`(8457) 안 DATE 분기였다.
 * 이 PR: date+time0 으로 tz_create_datetimetz_from_ses_core(실패 DOMAIN_ERROR) 뒤 db_make_datetimetz.
 * 바뀐 것: switch 분기 분리 + _core 교체.
 */
static TP_DOMAIN_STATUS
tp_value_convert_date_to_datetimetz (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				     date_conversion_error *error)
{
  DB_DATETIME v_datetime;
  DB_DATETIMETZ v_datetimetz;

  v_datetime.date = *db_get_date (src);
  v_datetime.time = 0;

  if (tz_create_datetimetz_from_ses_core (&v_datetime, &v_datetimetz, error) != NO_ERROR)
    {
      return DOMAIN_ERROR;
    }
  db_make_datetimetz (target, &v_datetimetz);

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_timestamp_to_datetimetz — TIMESTAMP → DATETIMETZ 셀 — UTC datetime 으로 풀고 세션 TZ_ID 를
 * 붙인다.
 * develop: develop 에 없음 — 이 PR 이 신설. `case DB_TYPE_DATETIMETZ:`(8457) 안 TIMESTAMP 분기였다.
 * 이 PR: db_timestamp_decode_utc 로 풀고 tz_create_session_tzid_for_datetime_core(…, true, …)로 TZ_ID 를 만든다(실패
 * DOMAIN_ERROR).
 * 바뀐 것: case 분리, 빈 중첩 블록이 남았다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_timestamp_to_datetimetz (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  DB_UTIME v_utime;
  DB_DATETIMETZ v_datetimetz;
  DB_TIME v_time;
  DB_DATE v_date;

  {
    v_utime = *db_get_timestamp (src);
    db_timestamp_decode_utc (&v_utime, &v_date, &v_time);
    v_datetimetz.datetime.time = v_time * 1000;
    v_datetimetz.datetime.date = v_date;

    if (tz_create_session_tzid_for_datetime_core (&v_datetimetz.datetime, true, &v_datetimetz.tz_id, error) !=
	NO_ERROR)
      {
	return DOMAIN_ERROR;
      }

    db_make_datetimetz (target, &v_datetimetz);
  }

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_timestamptz_to_datetimetz — TIMESTAMPTZ → DATETIMETZ 셀 — UTC datetime 으로 풀고 소스의 TZ_ID
 * 를 복사한다.
 * develop: develop 에 없음 — 이 PR 이 신설. `case DB_TYPE_DATETIMETZ:`(8457) 안 TIMESTAMPTZ 분기였다.
 * 이 PR: db_timestamp_decode_utc 로 풀고 tz_id 복사 후 db_make_datetimetz, 항상 DOMAIN_COMPATIBLE.
 * 바뀐 것: switch 분기 분리. 계산은 develop 과 같다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_timestamptz_to_datetimetz (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  DB_TIMESTAMPTZ v_timestamptz;
  DB_DATETIMETZ v_datetimetz;
  DB_TIME v_time;
  DB_DATE v_date;

  v_timestamptz = *db_get_timestamptz (src);
  (void) db_timestamp_decode_utc (&v_timestamptz.timestamp, &v_date, &v_time);
  v_datetimetz.datetime.time = v_time * 1000;
  v_datetimetz.datetime.date = v_date;
  v_datetimetz.tz_id = v_timestamptz.tz_id;
  db_make_datetimetz (target, &v_datetimetz);

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_datetime_to_datetimetz — DATETIME → DATETIMETZ 셀 — 지역 시각을 세션 TZ 로 해석한다.
 * develop: develop 에 없음 — 이 PR 이 신설. `case DB_TYPE_DATETIMETZ:`(8457) 안 DATETIME 분기였다.
 * 이 PR: db_get_datetime(src) 를 바로 tz_create_datetimetz_from_ses_core 에 넘기고(실패 DOMAIN_ERROR)
 * db_make_datetimetz.
 * 바뀐 것: switch 분기 분리 + _core 교체.
 */
static TP_DOMAIN_STATUS
tp_value_convert_datetime_to_datetimetz (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
    date_conversion_error *error)
{
  DB_DATETIMETZ v_datetimetz;

  if (tz_create_datetimetz_from_ses_core (db_get_datetime (src), &v_datetimetz, error) != NO_ERROR)
    {
      return DOMAIN_ERROR;
    }
  db_make_datetimetz (target, &v_datetimetz);

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_datetimeltz_to_datetimetz — DATETIMELTZ → DATETIMETZ 셀 — UTC datetime 은 그대로 두고 세션
 * TZ_ID 를 붙인다.
 * develop: develop 에 없음 — 이 PR 이 신설. `case DB_TYPE_DATETIMETZ:`(8457) 안 DATETIMELTZ 분기였다.
 * 이 PR: datetime 복사 후 tz_create_session_tzid_for_datetime_core(…, true, …), 실패하면 DOMAIN_ERROR.
 * 바뀐 것: switch 분기 분리 + _core 교체.
 */
static TP_DOMAIN_STATUS
tp_value_convert_datetimeltz_to_datetimetz (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  DB_DATETIMETZ v_datetimetz;

  v_datetimetz.datetime = *db_get_datetime (src);
  if (tz_create_session_tzid_for_datetime_core (&v_datetimetz.datetime, true, &v_datetimetz.tz_id, error) !=
      NO_ERROR)
    {
      return DOMAIN_ERROR;
    }
  db_make_datetimetz (target, &v_datetimetz);

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_enumeration_to_datetimetz — ENUM → DATETIMETZ 셀.
 * develop: develop 에 없음 — 이 PR 이 신설. `case DB_TYPE_DATETIMETZ:`(8457) 안 ENUMERATION 분기로 재귀 캐스트였다.
 * 이 PR: tp_enumeration_to_varchar 뒤 tp_value_convert_char_to_datetimetz 직접 호출.
 * 바뀐 것: 재귀 → 직접 호출(+18줄), 끝에 도달 불가 return.
 */
static TP_DOMAIN_STATUS
tp_value_convert_enumeration_to_datetimetz (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;

  {
    DB_VALUE varchar_val;
    if (tp_enumeration_to_varchar (src, &varchar_val) != NO_ERROR)
      {
	return DOMAIN_ERROR;
      }
    status = tp_value_convert_char_to_datetimetz (&varchar_val, target, desired_domain, error);
    return status;
  }

  return status;
}

/*
 * [리뷰] tp_value_convert_char_to_date — CHAR·VARCHAR → DATE 셀.
 * develop: develop 에 없음 — 이 PR 이 신설. `case DB_TYPE_DATE:`(object_domain.c:8555) 안 VARCHAR/CHAR 분기였다.
 * 이 PR: tp_atodate_core 로 파싱(실패 DOMAIN_ERROR), db_date_decode 로 연·월·일을 풀어 tp_make_date_conversion 으로 다시 조립한다.
 * 바뀐 것: db_make_date 대신 er_set 하지 않는 tp_make_date_conversion 과 _core 파서를 쓰는 것 말고는 develop 과 같다. decode 후 다시
 * encode 하는 왕복(범위 재검증)도 develop 그대로다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_char_to_date (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
			       date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;
  DB_DATE v_date;
  int year;
  int month;
  int day;

  if (tp_atodate_core (src, &v_date, error) == NO_ERROR)
    {
      db_date_decode (&v_date, &month, &day, &year);
    }
  else
    {
      return DOMAIN_ERROR;
    }

  if (tp_make_date_conversion (target, month, day, year, error) != NO_ERROR)
    {
      status = DOMAIN_ERROR;
    }

  return status;
}

/*
 * [리뷰] tp_value_convert_timestamp_to_date — TIMESTAMP(표가 TIMESTAMPLTZ 도 함께 매핑) → DATE 셀 — 세션 TZ 기준 날짜만 남긴다.
 * develop: develop 에 없음 — 이 PR 이 신설. `case DB_TYPE_DATE:`(8555) 안 TIMESTAMP/TIMESTAMPLTZ 한 분기(8589~8593)였다.
 * 이 PR: db_timestamp_decode_ses_core 의 반환값을 (void) 로 버리고 날짜만 decode·재조립한다.
 * 바뀐 것: 분기 분리 + _core·tp_make_date_conversion 교체. decode 실패를 무시해 v_date 가 미초기화인 채 쓰이는 성질은 develop 에서 그대로 옮겨왔다.
 * [지적 A3-04]
 */
static TP_DOMAIN_STATUS
tp_value_convert_timestamp_to_date (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				    date_conversion_error *error)
{
  DB_DATE v_date;
  int year;
  int month;
  int day;

  (void) db_timestamp_decode_ses_core (db_get_timestamp (src), &v_date, NULL, error);
  db_date_decode (&v_date, &month, &day, &year);
  tp_make_date_conversion (target, month, day, year, error);

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_timestamptz_to_date — TIMESTAMPTZ → DATE 셀 — 값에 붙은 TZ_ID 로 지역 날짜를 푼다.
 * develop: develop 에 없음 — 이 PR 이 신설. `case DB_TYPE_DATE:`(8555) 안 TIMESTAMPTZ 분기였다.
 * 이 PR: db_timestamp_decode_w_tz_id_core(실패 DOMAIN_ERROR) 뒤 날짜만 재조립.
 * 바뀐 것: 분기 분리 + _core·tp_make_date_conversion 교체. 계산은 develop 과 같다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_timestamptz_to_date (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				      date_conversion_error *error)
{
  DB_TIMESTAMPTZ v_timestamptz;
  DB_DATE v_date;
  int year;
  int month;
  int day;

  v_timestamptz = *db_get_timestamptz (src);
  if (db_timestamp_decode_w_tz_id_core (&v_timestamptz.timestamp, &v_timestamptz.tz_id, &v_date, NULL, error) !=
      NO_ERROR)
    {
      return DOMAIN_ERROR;
    }
  db_date_decode (&v_date, &month, &day, &year);
  tp_make_date_conversion (target, month, day, year, error);

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_datetime_to_date — DATETIME → DATE 셀 — 시각을 버리고 날짜만 남긴다.
 * develop: develop 에 없음 — 이 PR 이 신설. `case DB_TYPE_DATE:`(8555) 안 DATETIME 분기였다.
 * 이 PR: db_datetime_decode 로 전부 풀고 연·월·일만 tp_make_date_conversion 에 넘긴다.
 * 바뀐 것: 분기 분리 + tp_make_date_conversion 교체.
 */
static TP_DOMAIN_STATUS
tp_value_convert_datetime_to_date (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				   date_conversion_error *error)
{
  int hour;
  int minute;
  int second;
  int millisecond;
  int year;
  int month;
  int day;

  db_datetime_decode ((DB_DATETIME *) db_get_datetime (src), &month, &day, &year, &hour, &minute, &second,
		      &millisecond);
  tp_make_date_conversion (target, month, day, year, error);

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_datetimeltz_to_date — DATETIMELTZ → DATE 셀 — UTC 저장값을 세션 TZ 지역 시각으로 바꾼 뒤 날짜만 남긴다.
 * develop: develop 에 없음 — 이 PR 이 신설. `case DB_TYPE_DATE:`(8555) 안에서 DATETIMELTZ 와 DATETIMETZ 가 한
 * case(8613~8646)로 묶여 안쪽에서 소스를 다시 갈랐다.
 * 이 PR: tz_create_session_tzid_for_datetime_core 로 TZ_ID 를 만들고 tz_utc_datetimetz_to_local_core 로 지역화한 뒤 날짜만
 * 재조립한다.
 * 바뀐 것: 묶인 case 를 둘로 분리. 안쪽 분기가 사라진 자리에 중첩 블록과 도달 불가 return 이 흔적으로 남았다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_datetimeltz_to_date (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				      date_conversion_error *error)
{
  DB_DATETIME v_datetime;
  int hour;
  int minute;
  int second;
  int millisecond;
  int year;
  int month;
  int day;

  {
    DB_DATETIME *utc_dt_p;
    TZ_ID tz_id;

    /* DATETIMELTZ and DATETIMETZ store in UTC, convert to session */
    {
      utc_dt_p = db_get_datetime (src);
      if (tz_create_session_tzid_for_datetime_core (utc_dt_p, true, &tz_id, error) != NO_ERROR)
	{
	  return DOMAIN_ERROR;
	}
    }

    if (tz_utc_datetimetz_to_local_core (utc_dt_p, &tz_id, &v_datetime, error) != NO_ERROR)
      {
	return DOMAIN_ERROR;
      }

    db_datetime_decode (&v_datetime, &month, &day, &year, &hour, &minute, &second, &millisecond);

    tp_make_date_conversion (target, month, day, year, error);
    return DOMAIN_COMPATIBLE;
  }

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_datetimetz_to_date — DATETIMETZ → DATE 셀 — 값에 붙은 TZ_ID 로 지역화한 뒤 날짜만 남긴다.
 * develop: develop 에 없음 — 이 PR 이 신설. `case DB_TYPE_DATE:`(8555) 안에서 DATETIMELTZ 와 한 case 였다.
 * 이 PR: db_get_datetimetz 에서 datetime·tz_id 를 꺼내 tz_utc_datetimetz_to_local_core 로 지역화한 뒤 날짜만 재조립한다.
 * 바뀐 것: 묶인 case 분리. 같은 모양의 흔적 블록·도달 불가 return 이 남았다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_datetimetz_to_date (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				     date_conversion_error *error)
{
  DB_DATETIME v_datetime;
  int hour;
  int minute;
  int second;
  int millisecond;
  int year;
  int month;
  int day;

  {
    DB_DATETIME *utc_dt_p;
    DB_DATETIMETZ *dt_tz_p;
    TZ_ID tz_id;

    /* DATETIMELTZ and DATETIMETZ store in UTC, convert to session */
    {
      dt_tz_p = db_get_datetimetz (src);
      utc_dt_p = &dt_tz_p->datetime;
      tz_id = dt_tz_p->tz_id;
    }

    if (tz_utc_datetimetz_to_local_core (utc_dt_p, &tz_id, &v_datetime, error) != NO_ERROR)
      {
	return DOMAIN_ERROR;
      }

    db_datetime_decode (&v_datetime, &month, &day, &year, &hour, &minute, &second, &millisecond);

    tp_make_date_conversion (target, month, day, year, error);
    return DOMAIN_COMPATIBLE;
  }

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_enumeration_to_date — ENUM → DATE 셀.
 * develop: develop 에 없음 — 이 PR 이 신설. `case DB_TYPE_DATE:`(8555) 안 ENUMERATION 분기로 재귀 캐스트였다.
 * 이 PR: tp_enumeration_to_varchar 뒤 tp_value_convert_char_to_date 직접 호출.
 * 바뀐 것: 재귀 → 직접 호출(+18줄), 끝에 도달 불가 return.
 */
static TP_DOMAIN_STATUS
tp_value_convert_enumeration_to_date (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				      date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;

  {
    DB_VALUE varchar_val;
    if (tp_enumeration_to_varchar (src, &varchar_val) != NO_ERROR)
      {
	return DOMAIN_ERROR;
      }
    status = tp_value_convert_char_to_date (&varchar_val, target, desired_domain, error);
    return status;
  }

  return status;
}

/*
 * [리뷰] tp_value_convert_short_to_time — SHORT → TIME 셀 — 정수를 '자정 이후 초'로 읽는다.
 * develop: develop 에 없음 — 이 PR 이 신설. `case DB_TYPE_TIME:`(object_domain.c:8655) 안 SHORT 분기였다.
 * 이 PR: db_get_short(src) % SECONDS_IN_A_DAY 로 하루 범위로 접고 db_time_decode → tp_make_time_conversion. 항상
 * DOMAIN_COMPATIBLE.
 * 바뀐 것: 분기 분리 + db_make_time → tp_make_time_conversion 교체.
 */
static TP_DOMAIN_STATUS
tp_value_convert_short_to_time (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				date_conversion_error *error)
{
  DB_TIME v_time;
  int hour;
  int minute;
  int second;

  v_time = db_get_short (src) % SECONDS_IN_A_DAY;
  db_time_decode (&v_time, &hour, &minute, &second);
  tp_make_time_conversion (target, hour, minute, second, error);

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_integer_to_time — INTEGER → TIME 셀 — 정수를 '자정 이후 초'로 읽는다.
 * develop: develop 에 없음 — 이 PR 이 신설. `case DB_TYPE_TIME:`(8655) 안 INTEGER 분기였다.
 * 이 PR: db_get_int(src) % SECONDS_IN_A_DAY 로 접고 db_time_decode → tp_make_time_conversion.
 * 바뀐 것: 분기 분리 + tp_make_time_conversion 교체.
 */
static TP_DOMAIN_STATUS
tp_value_convert_integer_to_time (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				  date_conversion_error *error)
{
  DB_TIME v_time;
  int hour;
  int minute;
  int second;

  v_time = db_get_int (src) % SECONDS_IN_A_DAY;
  db_time_decode (&v_time, &hour, &minute, &second);
  tp_make_time_conversion (target, hour, minute, second, error);

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_bigint_to_time — BIGINT → TIME 셀 — 정수를 '자정 이후 초'로 읽는다.
 * develop: develop 에 없음 — 이 PR 이 신설. `case DB_TYPE_TIME:`(8655) 안 BIGINT 분기였다.
 * 이 PR: db_get_bigint(src) % SECONDS_IN_A_DAY 로 접고 db_time_decode → tp_make_time_conversion.
 * 바뀐 것: 분기 분리 + tp_make_time_conversion 교체.
 */
static TP_DOMAIN_STATUS
tp_value_convert_bigint_to_time (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				 date_conversion_error *error)
{
  DB_TIME v_time;
  int hour;
  int minute;
  int second;

  v_time = db_get_bigint (src) % SECONDS_IN_A_DAY;
  db_time_decode (&v_time, &hour, &minute, &second);
  tp_make_time_conversion (target, hour, minute, second, error);

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_float_to_time — FLOAT → TIME 셀 — 반올림한 초를 하루 범위로 접는다.
 * develop: develop 에 없음 — 이 PR 이 신설. `case DB_TYPE_TIME:`(8655) 안 FLOAT 분기였다.
 * 이 PR: OR_CHECK_INT_OVERFLOW 면 DOMAIN_OVERFLOW, 아니면 (int)ROUND(ftmp) % SECONDS_IN_A_DAY 로 접어 조립.
 * 바뀐 것: case 분리. 흔적 중첩 블록과 도달 불가 return 이 남았다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_float_to_time (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;
  DB_TIME v_time;
  int hour;
  int minute;
  int second;

  {
    float ftmp = db_get_float (src);
    if (OR_CHECK_INT_OVERFLOW (ftmp))
      {
	status = DOMAIN_OVERFLOW;
      }
    else
      {
	v_time = ((int) ROUND (ftmp)) % SECONDS_IN_A_DAY;
	db_time_decode (&v_time, &hour, &minute, &second);
	tp_make_time_conversion (target, hour, minute, second, error);
      }
    return status;
  }

  return status;
}

/*
 * [리뷰] tp_value_convert_double_to_time — DOUBLE → TIME 셀 — FLOAT 판과 같은 규칙.
 * develop: develop 에 없음 — 이 PR 이 신설. `case DB_TYPE_TIME:`(8655) 안 DOUBLE 분기였다.
 * 이 PR: OR_CHECK_INT_OVERFLOW 검사 후 (int)ROUND(dtmp) % SECONDS_IN_A_DAY.
 * 바뀐 것: case 분리, 흔적 블록·도달 불가 return 이 남았다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_double_to_time (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				 date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;
  DB_TIME v_time;
  int hour;
  int minute;
  int second;

  {
    double dtmp = db_get_double (src);
    if (OR_CHECK_INT_OVERFLOW (dtmp))
      {
	status = DOMAIN_OVERFLOW;
      }
    else
      {
	v_time = ((int) ROUND (dtmp)) % SECONDS_IN_A_DAY;
	db_time_decode (&v_time, &hour, &minute, &second);
	tp_make_time_conversion (target, hour, minute, second, error);
      }
    return status;
  }

  return status;
}

/*
 * [리뷰] tp_value_convert_monetary_to_time — MONETARY → TIME 셀 — 금액을 초로 읽는다.
 * develop: develop 에 없음 — 이 PR 이 신설. `case DB_TYPE_TIME:`(8655) 안 MONETARY 분기였다.
 * 이 PR: db_get_monetary(src)->amount 에 OR_CHECK_INT_OVERFLOW 후 ROUND·모듈로.
 * 바뀐 것: 분기 분리 + tp_make_time_conversion 교체.
 */
static TP_DOMAIN_STATUS
tp_value_convert_monetary_to_time (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				   date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;
  const DB_MONETARY *v_money;
  DB_TIME v_time;
  int hour;
  int minute;
  int second;

  v_money = db_get_monetary (src);
  if (OR_CHECK_INT_OVERFLOW (v_money->amount))
    {
      status = DOMAIN_OVERFLOW;
    }
  else
    {
      v_time = (int) ROUND (v_money->amount) % SECONDS_IN_A_DAY;
      db_time_decode (&v_time, &hour, &minute, &second);
      tp_make_time_conversion (target, hour, minute, second, error);
    }

  return status;
}

/*
 * [리뷰] tp_value_convert_char_to_time — CHAR·VARCHAR → TIME 셀.
 * develop: develop 에 없음 — 이 PR 이 신설. `case DB_TYPE_TIME:`(8655) 안 VARCHAR/CHAR 분기였다.
 * 이 PR: tp_atotime_core 로 파싱(실패 DOMAIN_ERROR), db_time_decode 후 tp_make_time_conversion(실패 DOMAIN_ERROR).
 * 바뀐 것: 분기 분리 + _core·tp_make_time_conversion 교체.
 */
static TP_DOMAIN_STATUS
tp_value_convert_char_to_time (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
			       date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;
  DB_TIME v_time;
  int hour;
  int minute;
  int second;

  if (tp_atotime_core (src, &v_time, error) == NO_ERROR)
    {
      db_time_decode (&v_time, &hour, &minute, &second);
    }
  else
    {
      return DOMAIN_ERROR;
    }

  if (tp_make_time_conversion (target, hour, minute, second, error) != NO_ERROR)
    {
      status = DOMAIN_ERROR;
    }

  return status;
}

/*
 * [리뷰] tp_value_convert_timestamp_to_time — TIMESTAMP(표가 TIMESTAMPLTZ 도 함께 매핑) → TIME 셀 — 세션 TZ 기준 시각만 남긴다.
 * develop: develop 에 없음 — 이 PR 이 신설. `case DB_TYPE_TIME:`(8655) 안 TIMESTAMP/TIMESTAMPLTZ 한 분기(8658~8666)였다.
 * 이 PR: db_timestamp_decode_ses_core(date 는 NULL, 실패 DOMAIN_ERROR) 뒤 db_value_put_encoded_time 으로 바로 담는다.
 * 바뀐 것: 분기 분리 + _core 교체.
 */
static TP_DOMAIN_STATUS
tp_value_convert_timestamp_to_time (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				    date_conversion_error *error)
{
  DB_TIME v_time;

  if (db_timestamp_decode_ses_core (db_get_timestamp (src), NULL, &v_time, error) != NO_ERROR)
    {
      return DOMAIN_ERROR;
    }
  db_value_put_encoded_time (target, &v_time);

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_timestamptz_to_time — TIMESTAMPTZ → TIME 셀 — 값에 붙은 TZ_ID 로 지역 시각을 푼다.
 * develop: develop 에 없음 — 이 PR 이 신설. `case DB_TYPE_TIME:`(8655) 안 TIMESTAMPTZ 분기였다.
 * 이 PR: db_timestamp_decode_w_tz_id_core(date NULL) 후 db_value_put_encoded_time.
 * 바뀐 것: 분기 분리 + _core 교체.
 */
static TP_DOMAIN_STATUS
tp_value_convert_timestamptz_to_time (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				      date_conversion_error *error)
{
  DB_TIMESTAMPTZ v_timestamptz;
  DB_TIME v_time;

  /* convert TS from UTC to value TZ */
  v_timestamptz = *db_get_timestamptz (src);
  if (db_timestamp_decode_w_tz_id_core (&v_timestamptz.timestamp, &v_timestamptz.tz_id, NULL, &v_time, error) !=
      NO_ERROR)
    {
      return DOMAIN_ERROR;
    }
  db_value_put_encoded_time (target, &v_time);

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_datetime_to_time — DATETIME → TIME 셀 — 날짜를 버리고 시·분·초만 남긴다(밀리초도 버린다).
 * develop: develop 에 없음 — 이 PR 이 신설. `case DB_TYPE_TIME:`(8655) 안 DATETIME 분기였다.
 * 이 PR: db_datetime_decode 후 시·분·초만 tp_make_time_conversion.
 * 바뀐 것: 분기 분리 + tp_make_time_conversion 교체.
 */
static TP_DOMAIN_STATUS
tp_value_convert_datetime_to_time (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				   date_conversion_error *error)
{
  int hour;
  int minute;
  int second;
  int millisecond;
  int year;
  int month;
  int day;

  db_datetime_decode ((DB_DATETIME *) db_get_datetime (src), &month, &day, &year, &hour, &minute, &second,
		      &millisecond);
  tp_make_time_conversion (target, hour, minute, second, error);

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_datetimeltz_to_time — DATETIMELTZ → TIME 셀 — 세션 TZ 로 지역화한 뒤 시각만 남긴다.
 * develop: develop 에 없음 — 이 PR 이 신설. `case DB_TYPE_TIME:`(8655) 안 DATETIMELTZ 분기였다.
 * 이 PR: tz_datetimeltz_to_local_core(실패 DOMAIN_ERROR) 뒤 decode·조립.
 * 바뀐 것: case 분리, 흔적 블록과 도달 불가 return 이 남았다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_datetimeltz_to_time (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				      date_conversion_error *error)
{
  DB_DATETIME v_datetime;
  int hour;
  int minute;
  int second;
  int millisecond;
  int year;
  int month;
  int day;

  {
    DB_DATETIME dt_local;

    v_datetime = *db_get_datetime (src);

    if (tz_datetimeltz_to_local_core (&v_datetime, &dt_local, error) != NO_ERROR)
      {
	return DOMAIN_ERROR;
      }

    db_datetime_decode (&dt_local, &month, &day, &year, &hour, &minute, &second, &millisecond);
    tp_make_time_conversion (target, hour, minute, second, error);
    return DOMAIN_COMPATIBLE;
  }

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_datetimetz_to_time — DATETIMETZ → TIME 셀 — 값의 TZ_ID 로 지역화한 뒤 시각만 남긴다.
 * develop: develop 에 없음 — 이 PR 이 신설. `case DB_TYPE_TIME:`(8655) 안 DATETIMETZ 분기였다.
 * 이 PR: tz_utc_datetimetz_to_local_core(실패 DOMAIN_ERROR) 뒤 decode·조립.
 * 바뀐 것: case 분리, 흔적 블록과 도달 불가 return 이 남았다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_datetimetz_to_time (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				     date_conversion_error *error)
{
  DB_DATETIMETZ v_datetimetz;
  int hour;
  int minute;
  int second;
  int millisecond;
  int year;
  int month;
  int day;

  {
    DB_DATETIME dt_local;

    v_datetimetz = *db_get_datetimetz (src);
    if (tz_utc_datetimetz_to_local_core (&v_datetimetz.datetime, &v_datetimetz.tz_id, &dt_local, error) !=
	NO_ERROR)
      {
	return DOMAIN_ERROR;
      }
    db_datetime_decode (&dt_local, &month, &day, &year, &hour, &minute, &second, &millisecond);
    tp_make_time_conversion (target, hour, minute, second, error);
    return DOMAIN_COMPATIBLE;
  }

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_enumeration_to_time — ENUM → TIME 셀.
 * develop: develop 에 없음 — 이 PR 이 신설. `case DB_TYPE_TIME:`(8655) 안 ENUMERATION 분기로 재귀 캐스트였다.
 * 이 PR: tp_enumeration_to_varchar 뒤 tp_value_convert_char_to_time 직접 호출.
 * 바뀐 것: 재귀 → 직접 호출(+18줄), 끝에 도달 불가 return.
 */
static TP_DOMAIN_STATUS
tp_value_convert_enumeration_to_time (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				      date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;

  {
    DB_VALUE varchar_val;
    if (tp_enumeration_to_varchar (src, &varchar_val) != NO_ERROR)
      {
	return DOMAIN_ERROR;
      }
    status = tp_value_convert_char_to_time (&varchar_val, target, desired_domain, error);
    return status;
  }

  return status;
}

#if !defined (SERVER_MODE)
/*
 * [리뷰] tp_value_convert_object_to_object — OBJECT → OBJECT 셀 — 뷰 객체를 실제 객체로 내리고 목적 도메인의 클래스(또는 서브클래스)에 속하는지
 * 확인한다. 클라이언트 전용이라 #if !defined (SERVER_MODE) 가드 안에 있다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop `case DB_TYPE_OBJECT:`(object_domain.c:8807)에서 소스별 if/else 로
 * v_obj 를 구한 뒤 공통 꼬리에서 클래스 검사와 db_make_object 를 했다.
 * 이 PR: sm_coerce_object_domain 으로 v_obj 를 얻고(실패 DOMAIN_INCOMPATIBLE), 공통 꼬리(클래스 동일/서브클래스/vclass 판정)를 거쳐
 * db_make_object.
 * 바뀐 것: 소스별 갈래를 함수로 떼면서 공통 꼬리를 셀마다 복제했다(+60줄).
 */
static TP_DOMAIN_STATUS
tp_value_convert_object_to_object (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				   date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;

  {
    DB_OBJECT *v_obj = NULL;
    int is_vclass = 0;

    /* Make sure the domains are compatible.  Coerce view objects to real objects. */

    if (!sm_coerce_object_domain ((TP_DOMAIN *) desired_domain, db_get_object (src), &v_obj))
      {
	status = DOMAIN_INCOMPATIBLE;
      }

    {
      /* check we got an object in a proper class */
      if (v_obj && desired_domain->class_mop)
	{
	  DB_OBJECT *obj_class;

	  obj_class = db_get_class (v_obj);
	  if (obj_class == desired_domain->class_mop)
	    {
	      /* everything is fine */
	    }
	  else if (db_is_subclass (obj_class, desired_domain->class_mop) > 0)
	    {
	      /* everything is also ok */
	    }
	  else
	    {
	      is_vclass = db_is_vclass (desired_domain->class_mop);
	      if (is_vclass < 0)
		{
		  return DOMAIN_ERROR;
		}
	      if (is_vclass)
		{
		  /*
		   * This should still be an error, and the above
		   * code should have constructed a virtual mop.
		   * I'm not sure the rest of the code is consistent
		   * in this regard.
		   */
		}
	      else
		{
		  status = DOMAIN_INCOMPATIBLE;
		}
	    }
	}
      db_make_object (target, v_obj);
    }
  }

  return status;
}
#endif /* !defined (SERVER_MODE) */

#if !defined (SERVER_MODE)
/*
 * [리뷰] tp_value_convert_oid_to_object — OID → OBJECT 셀 — OID 를 워크스페이스 MOP 으로 바꾼 뒤 클래스를 확인한다. 클라이언트 전용 가드 안.
 * develop: develop 에 없음 — 이 PR 이 신설. develop OBJECT case(8807)의 vid_oid_to_object 갈래 + 공통 꼬리였다.
 * 이 PR: vid_oid_to_object 로 v_obj 를 얻고 같은 공통 꼬리를 돈 뒤 db_make_object.
 * 바뀐 것: 갈래 분리 + 공통 꼬리 복제(+57줄).
 */
static TP_DOMAIN_STATUS
tp_value_convert_oid_to_object (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;

  {
    DB_OBJECT *v_obj = NULL;
    int is_vclass = 0;

    /* Make sure the domains are compatible.  Coerce view objects to real objects. */

    vid_oid_to_object (src, &v_obj);

    {
      /* check we got an object in a proper class */
      if (v_obj && desired_domain->class_mop)
	{
	  DB_OBJECT *obj_class;

	  obj_class = db_get_class (v_obj);
	  if (obj_class == desired_domain->class_mop)
	    {
	      /* everything is fine */
	    }
	  else if (db_is_subclass (obj_class, desired_domain->class_mop) > 0)
	    {
	      /* everything is also ok */
	    }
	  else
	    {
	      is_vclass = db_is_vclass (desired_domain->class_mop);
	      if (is_vclass < 0)
		{
		  return DOMAIN_ERROR;
		}
	      if (is_vclass)
		{
		  /*
		   * This should still be an error, and the above
		   * code should have constructed a virtual mop.
		   * I'm not sure the rest of the code is consistent
		   * in this regard.
		   */
		}
	      else
		{
		  status = DOMAIN_INCOMPATIBLE;
		}
	    }
	}
      db_make_object (target, v_obj);
    }
  }

  return status;
}
#endif /* !defined (SERVER_MODE) */

#if !defined (SERVER_MODE)
/*
 * [리뷰] tp_value_convert_pointer_to_object — POINTER(DB_OTMPL) → OBJECT 셀 — 객체 템플릿의 클래스가 목적 도메인과 맞는지만 보고 포인터를
 * 그대로 넘긴다. 클라이언트 전용 가드 안.
 * develop: develop 에 없음 — 이 PR 이 신설. develop OBJECT case(8807)의 POINTER 갈래였다.
 * 이 PR: sm_check_class_domain 실패면 DOMAIN_INCOMPATIBLE, 아니면 db_make_pointer 로 포인터 복사.
 * 바뀐 것: 갈래를 함수로 분리(+21줄). 이 갈래만 공통 꼬리를 타지 않는 것도 develop 과 같다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_pointer_to_object (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				    date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;

  {
    /* Make sure the domains are compatible.  Coerce view objects to real objects. */
    if (!sm_check_class_domain ((TP_DOMAIN *) desired_domain, ((DB_OTMPL *) db_get_pointer (src))->classobj))
      {
	status = DOMAIN_INCOMPATIBLE;
      }
    else
      {
	db_make_pointer (target, db_get_pointer (src));
      }

  }

  return status;
}
#endif /* !defined (SERVER_MODE) */

#if !defined (SERVER_MODE)
/*
 * [리뷰] tp_value_convert_vobj_to_object — VOBJ → OBJECT 셀 — 가상 객체를 풀어 MOP 을 얻고, 목적이 뷰가 아니면 실제 인스턴스로 내린다. 클라이언트
 * 전용 가드 안.
 * develop: develop 에 없음 — 이 PR 이 신설. develop OBJECT case(8807)의 VOBJ 갈래 + 공통 꼬리였다.
 * 이 PR: vid_vobj_to_object → db_is_vclass 판정 → 비-뷰면 db_real_instance → 공통 꼬리 → db_make_object.
 * 바뀐 것: 갈래 분리 + 공통 꼬리 복제(+64줄). db_is_vclass 를 앞뒤로 두 번 부르는 것도 develop 그대로다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_vobj_to_object (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				 date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;

  {
    DB_OBJECT *v_obj = NULL;
    int is_vclass = 0;

    /* Make sure the domains are compatible.  Coerce view objects to real objects. */
    vid_vobj_to_object (src, &v_obj);
    is_vclass = db_is_vclass (desired_domain->class_mop);
    if (is_vclass < 0)
      {
	status = DOMAIN_ERROR;
      }
    else if (!is_vclass)
      {
	v_obj = db_real_instance (v_obj);
      }
    {
      /* check we got an object in a proper class */
      if (v_obj && desired_domain->class_mop)
	{
	  DB_OBJECT *obj_class;

	  obj_class = db_get_class (v_obj);
	  if (obj_class == desired_domain->class_mop)
	    {
	      /* everything is fine */
	    }
	  else if (db_is_subclass (obj_class, desired_domain->class_mop) > 0)
	    {
	      /* everything is also ok */
	    }
	  else
	    {
	      is_vclass = db_is_vclass (desired_domain->class_mop);
	      if (is_vclass < 0)
		{
		  return DOMAIN_ERROR;
		}
	      if (is_vclass)
		{
		  /*
		   * This should still be an error, and the above
		   * code should have constructed a virtual mop.
		   * I'm not sure the rest of the code is consistent
		   * in this regard.
		   */
		}
	      else
		{
		  status = DOMAIN_INCOMPATIBLE;
		}
	    }
	}
      db_make_object (target, v_obj);
    }
  }

  return status;
}
#endif /* !defined (SERVER_MODE) */

#if !defined (SERVER_MODE)
/*
 * [리뷰] tp_value_convert_object_to_vobj — OBJECT → VOBJ 셀 — 실제 객체를 가상 객체 표현으로 감싼다. 클라이언트 전용 가드 안.
 * develop: develop 에 없음 — 이 PR 이 신설. develop `case DB_TYPE_VOBJ:`(object_domain.c:8981) 안 OBJECT 갈래였다.
 * 이 PR: vid_object_to_vobj 가 음수면 DOMAIN_INCOMPATIBLE, 아니면 DOMAIN_COMPATIBLE.
 * 바뀐 것: 갈래 분리(+20줄). 흔적 블록과 도달 불가 return 이 남았다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_object_to_vobj (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				 date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;

  {
    if (vid_object_to_vobj (db_get_object (src), target) < 0)
      {
	status = DOMAIN_INCOMPATIBLE;
      }
    else
      {
	status = DOMAIN_COMPATIBLE;
      }
    return status;
  }

  return status;
}
#endif /* !defined (SERVER_MODE) */

/*
 * [리뷰] tp_value_convert_oid_to_vobj — OID → VOBJ 셀 — {뷰 OID(NULL), 클래스 OID(NULL), 키} 3원소 시퀀스를 만들어 VOBJ 로 타입을
 * 바꾼다. 서버 쪽 표현을 흉내내는 역사적 경로다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop VOBJ case(8981)의 OID 갈래였다(주석까지 같다).
 * 이 PR: db_seq_create(3) 에 view_oid·class_oid·keys 를 넣고 db_make_sequence 후 db_value_alter_type(DB_TYPE_VOBJ).
 * db_seq_put 실패면 DOMAIN_INCOMPATIBLE.
 * 바뀐 것: 갈래 분리(+44줄). 실패 시 seq 를 해제하지 않는 것도 develop 그대로다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_oid_to_vobj (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
			      date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;

  {
    DB_VALUE view_oid;
    DB_VALUE class_oid;
    DB_VALUE keys;
    OID nulloid;
    DB_SEQ *seq;

    OID_SET_NULL (&nulloid);
    db_make_oid (&class_oid, &nulloid);
    db_make_oid (&view_oid, &nulloid);
    seq = db_seq_create (NULL, NULL, 3);
    keys = *src;

    /*
     * if we are on the server, and get a DB_TYPE_OBJECT,
     * then its only possible representation is a DB_TYPE_OID,
     * and it may be treated that way. However, this should
     * not really be a case that can happen. It may still
     * for historical reasons, so is not falgged as an error.
     * On the client, a worskapce based scheme must be used,
     * which is just above in a conditional compiled section.
     */

    if ((db_seq_put (seq, 0, &view_oid) != NO_ERROR) || (db_seq_put (seq, 1, &class_oid) != NO_ERROR)
	|| (db_seq_put (seq, 2, &keys) != NO_ERROR))
      {
	status = DOMAIN_INCOMPATIBLE;
      }
    else
      {
	db_make_sequence (target, seq);
	db_value_alter_type (target, DB_TYPE_VOBJ);
	status = DOMAIN_COMPATIBLE;
      }
  }

  return status;
}

/*
 * [리뷰] tp_value_convert_vobj_to_vobj — VOBJ → VOBJ 셀 — 뷰 정보를 비교할 방법이 없어 무조건 성공으로 보고 값만 복제한다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop VOBJ case(8981)의 VOBJ 갈래였다(주석 포함 동일).
 * 이 PR: pr_clone_value 로 복제하고 DOMAIN_COMPATIBLE.
 * 바뀐 것: 갈래 분리(+23줄). 흔적 중첩 블록이 남았다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_vobj_to_vobj (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
			       date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;

  {
    /*
     * We should try and convert the view of the src to match
     * the view of the desired_domain. However, the desired
     * domain generally does not contain this information.
     * We will detect domain incompatibly later on assignment,
     * so we treat casting any DB_TYPE_VOBJ to DB_TYPE_VOBJ
     * as success.
     */
    status = DOMAIN_COMPATIBLE;
    {
      pr_clone_value ((DB_VALUE *) src, target);
    }
  }

  return status;
}

/*
 * [리뷰] tp_value_convert_char_to_bit — CHAR·VARCHAR → BIT·VARBIT 셀 — 16진 문자열을 비트열로 바꾼다. 변환 표가 BIT 와 VARBIT 양쪽에서
 * 이 셀을 쓴다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop `case DB_TYPE_BIT: case DB_TYPE_VARBIT:`(object_domain.c:9068) 안
 * VARCHAR/CHAR 갈래였고, 그 자리에서 coercion_mode·PRM_ID_ALLOW_TRUNCATED_STRING 을 보고 잘림을 DOMAIN_OVERFLOW 로 올릴지
 * 정했다(9096).
 * 이 PR: qstr_hex_to_bin 으로 변환해 db_bit_string_coerce 하고, 잘리면 새 상태값 DOMAIN_TRUNCATED 를 돌려준다. coercion_mode 와
 * 파라미터는 보지 않는다.
 * 바뀐 것: 분기 분리 + 잘림 정책의 호출자 이전(+49줄). 셀은 coercion_mode 를 받지 않으므로 tp_value_cast_internal 이 publish 뒤 한 번만
 * 판정한다(object_domain.c:5893~). 이 PR 이 DOMAIN_TRUNCATED 를 추가한 이유다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_char_to_bit (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
			      date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;
  DB_DATA_STATUS data_stat = DATA_STATUS_OK;

  {
    DB_VALUE temp;
    char *bit_char_string;
    int src_size = db_get_string_size (src);
    int dst_size = (src_size + 1) / 2;

    bit_char_string = (char *) db_private_alloc (NULL, dst_size + 1);
    if (bit_char_string)
      {
	if (qstr_hex_to_bin (bit_char_string, dst_size, db_get_string (src), src_size) != src_size)
	  {
	    status = DOMAIN_ERROR;
	    db_private_free_and_init (NULL, bit_char_string);
	  }
	else
	  {
	    db_make_bit (&temp, TP_FLOATING_PRECISION_VALUE, bit_char_string, src_size * 4);
	    temp.need_clear = true;
	    if (db_bit_string_coerce (&temp, target, &data_stat) != NO_ERROR)
	      {
		status = DOMAIN_INCOMPATIBLE;
	      }
	    else if (data_stat == DATA_STATUS_TRUNCATED)
	      {
		status = DOMAIN_TRUNCATED;
	      }
	    else
	      {
		status = DOMAIN_COMPATIBLE;
	      }
	    pr_clear_value (&temp);
	  }
      }
    else
      {
	/* Couldn't allocate space for bit_char_string */
	status = DOMAIN_INCOMPATIBLE;
      }
  }

  return status;
}

/*
 * [리뷰] tp_value_convert_enumeration_to_bit — ENUM → BIT 셀.
 * develop: develop 에 없음 — 이 PR 이 신설. develop BIT/VARBIT case(9068)의 ENUMERATION 갈래로 tp_value_cast_internal
 * 재귀였다.
 * 이 PR: tp_enumeration_to_varchar 뒤 tp_value_convert_char_to_bit 직접 호출.
 * 바뀐 것: 재귀 → 직접 호출(+18줄).
 */
static TP_DOMAIN_STATUS
tp_value_convert_enumeration_to_bit (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				     date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;

  {
    DB_VALUE varchar_val;

    if (tp_enumeration_to_varchar (src, &varchar_val) != NO_ERROR)
      {
	return DOMAIN_ERROR;
      }
    status = tp_value_convert_char_to_bit (&varchar_val, target, desired_domain, error);
  }

  return status;
}

/*
 * [리뷰] tp_value_convert_bit_to_bit — BIT → BIT 셀 — 정밀도가 같아도 db_bit_string_coerce 를 거친다. DBLink 의 BIT(n) 값이 바이트
 * 단위라 precision 보다 많은 비트를 가질 수 있기 때문이다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop BIT/VARBIT case 의 default 갈래에서 tp_can_steal_string 이면 도메인만
 * 갈아끼우고(slam), 아니면 db_bit_string_coerce 를 했다(9157~9168).
 * 이 PR: 항상 db_bit_string_coerce 를 하고, 잘리면 DOMAIN_TRUNCATED, 실패면 DOMAIN_INCOMPATIBLE.
 * 바뀐 것: slam 최적화는 셀에서 빠지고 호출자 tp_value_cast_internal 의 `if (src == dest)` 앞단(object_domain.c:5786~5797,
 * bit_path)으로 올라갔다 — 셀은 src==dest 를 모르기 때문이다. 셀에는 항상 coerce 하는 경로만 남았다(+25줄).
 */
static TP_DOMAIN_STATUS
tp_value_convert_bit_to_bit (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
			     date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;
  DB_DATA_STATUS data_stat = DATA_STATUS_OK;

  /* a bit string of the same precision is coerced too: a value can hold more bits than its precision (a DBLink
   * BIT(n) value holds whole bytes, dblink_scan.c), which the coercion truncates */

  if (db_bit_string_coerce (src, target, &data_stat) != NO_ERROR)
    {
      status = DOMAIN_INCOMPATIBLE;
    }
  else if (data_stat == DATA_STATUS_TRUNCATED)
    {
      status = DOMAIN_TRUNCATED;
    }
  else
    {
      status = DOMAIN_COMPATIBLE;
    }

  return status;
}

/*
 * [리뷰] tp_value_convert_varbit_to_bit — VARBIT → BIT 셀 — bit_to_bit 과 같은 db_bit_string_coerce 경로.
 * develop: develop 에 없음 — 이 PR 이 신설. develop BIT/VARBIT case 의 default 갈래였다.
 * 이 PR: db_bit_string_coerce 후 잘림이면 DOMAIN_TRUNCATED.
 * 바뀐 것: 본문이 tp_value_convert_bit_to_bit 과 한 글자도 다르지 않다(주석만 없다). 같은 일을 하는 셀 둘이 이름만 다르게 존재한다(+22줄).
 */
static TP_DOMAIN_STATUS
tp_value_convert_varbit_to_bit (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;
  DB_DATA_STATUS data_stat = DATA_STATUS_OK;

  if (db_bit_string_coerce (src, target, &data_stat) != NO_ERROR)
    {
      status = DOMAIN_INCOMPATIBLE;
    }
  else if (data_stat == DATA_STATUS_TRUNCATED)
    {
      status = DOMAIN_TRUNCATED;
    }
  else
    {
      status = DOMAIN_COMPATIBLE;
    }

  return status;
}

/*
 * [리뷰] tp_value_convert_blob_to_bit — BLOB → BIT 셀 — LOB 내용을 비트열로 읽은 뒤 목적 BIT 도메인에 맞춘다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop BIT/VARBIT case 의 BLOB 갈래로, db_blob_to_bit 결과를
 * tp_value_cast_internal 로 재귀 캐스트하고 그 TP_DOMAIN_STATUS 를 int err 에 덮어써 사실상 버렸다(9136).
 * 이 PR: db_blob_to_bit 뒤 tp_value_convert_varbit_to_bit 를 부르고, 성공·잘림이면 그 상태를 쓰고 실패면 target 을 NULL 로 만든 뒤
 * DOMAIN_COMPATIBLE 을 돌려준다. 최종 반환은 `err < 0 ? DOMAIN_ERROR : status`.
 * 바뀐 것: 재귀 → 직접 호출(+33줄). develop 이 상태를 흘려 버려 '실패해도 성공+NULL' 이 되던 동작을 주석과 함께 의도적으로 재현했다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_blob_to_bit (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
			      date_conversion_error *error)
{
  int err = NO_ERROR;
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;

  {
    DB_VALUE tmpval;

    db_make_null (&tmpval);

    err = db_blob_to_bit (src, NULL, &tmpval);
    if (err == NO_ERROR)
      {
	TP_DOMAIN_STATUS nested_status =
		tp_value_convert_varbit_to_bit (&tmpval, target, desired_domain, error);
	if (nested_status == DOMAIN_COMPATIBLE || nested_status == DOMAIN_TRUNCATED)
	  {
	    status = nested_status;
	  }
	else
	  {
	    /* The old outer LOB cast returned success with a NULL result. */
	    pr_clear_value (target);
	    db_make_null (target);
	  }
      }
    (void) pr_clear_value (&tmpval);
  }

  return err < 0 ? DOMAIN_ERROR : status;
}

/*
 * [리뷰] tp_value_convert_enumeration_to_varbit — ENUM → VARBIT 셀.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 에서는 BIT 와 VARBIT 이 한 case 라 ENUM→BIT 와 같은 코드였다.
 * 이 PR: tp_enumeration_to_varchar 뒤 tp_value_convert_char_to_bit 직접 호출 — BIT 판과 같은 셀을 부른다.
 * 바뀐 것: 재귀 → 직접 호출(+18줄). 이름은 varbit 이지만 char_to_bit 를 부르는데, 그 셀이 BIT·VARBIT 공용이라 결과는 같다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_enumeration_to_varbit (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
					date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;

  {
    DB_VALUE varchar_val;

    if (tp_enumeration_to_varchar (src, &varchar_val) != NO_ERROR)
      {
	return DOMAIN_ERROR;
      }
    status = tp_value_convert_char_to_bit (&varchar_val, target, desired_domain, error);
  }

  return status;
}

/*
 * [리뷰] tp_value_convert_blob_to_varbit — BLOB → VARBIT 셀 — blob_to_bit 의 VARBIT 짝.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 에서 BIT 와 VARBIT 이 한 case 라 BLOB→BIT 와 같은 코드였다.
 * 이 PR: db_blob_to_bit 뒤 tp_value_convert_bit_to_bit 를 부르고 같은 실패 흡수 규칙을 쓴다.
 * 바뀐 것: 재귀 → 직접 호출(+33줄). blob_to_bit 은 varbit_to_bit 를, blob_to_varbit 은 bit_to_bit 를 부르는 이름이 엇갈린 짝인데, 두 피호출
 * 셀의 본문이 동일해 동작 차이는 없다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_blob_to_varbit (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				 date_conversion_error *error)
{
  int err = NO_ERROR;
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;

  {
    DB_VALUE tmpval;

    db_make_null (&tmpval);

    err = db_blob_to_bit (src, NULL, &tmpval);
    if (err == NO_ERROR)
      {
	TP_DOMAIN_STATUS nested_status =
		tp_value_convert_bit_to_bit (&tmpval, target, desired_domain, error);
	if (nested_status == DOMAIN_COMPATIBLE || nested_status == DOMAIN_TRUNCATED)
	  {
	    status = nested_status;
	  }
	else
	  {
	    /* The old outer LOB cast returned success with a NULL result. */
	    pr_clear_value (target);
	    db_make_null (target);
	  }
      }
    (void) pr_clear_value (&tmpval);
  }

  return err < 0 ? DOMAIN_ERROR : status;
}

/*
 * [리뷰] tp_value_convert_short_to_varchar — SHORT → VARCHAR 셀 — 정수를 10진 문자열로 찍어 목적 VARCHAR 도메인에 맞춘다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 은 VARCHAR·CHAR 목적이 한 case(object_domain.c:9177),
 * BIGINT/INTEGER/SMALLINT 소스가 또 한 case(9229)라 `if (original_type == …)` 와
 * make_desired_string_db_value(desired_type, …) 두 겹 분기 안이었다.
 * 이 PR: db_private_alloc(TP_BIGINT_PRECISION+2+1) 버퍼에 tp_ltoa 로 찍고, 목적 precision 보다 길면 DOMAIN_OVERFLOW(버퍼 해제),
 * 아니면 tp_make_varchar_conversion. tp_ltoa 실패는 DOMAIN_ERROR.
 * 바뀐 것: 두 겹 분기가 셀 6개로 펼쳐졌다(+44줄). 값을 꺼내는 한 줄만 자리 표시 블록 `{ … }` 안에 남아 develop 의 if/else 자리를 보여 준다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_short_to_varchar (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				   date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;
  DB_DATA_STATUS data_stat = DATA_STATUS_OK;

  {
    int max_size = TP_BIGINT_PRECISION + 2 + 1;
    char *new_string;
    DB_BIGINT num;

    new_string = (char *) db_private_alloc (NULL, max_size);
    if (!new_string)
      {
	return DOMAIN_ERROR;
      }

    {
      num = (DB_BIGINT) db_get_short (src);
    }

    if (tp_ltoa (num, new_string, 10))
      {
	if (db_value_precision (target) != TP_FLOATING_PRECISION_VALUE
	    && db_value_precision (target) < (int) strlen (new_string))
	  {
	    status = DOMAIN_OVERFLOW;
	    db_private_free_and_init (NULL, new_string);
	  }
	else
	  {
	    tp_make_varchar_conversion (desired_domain, new_string, target, &status, &data_stat);
	  }
      }
    else
      {
	status = DOMAIN_ERROR;
	db_private_free_and_init (NULL, new_string);
      }
  }

  return status;
}

/*
 * [리뷰] tp_value_convert_integer_to_varchar — INTEGER → VARCHAR 셀 — 정수를 10진 문자열로 찍는다.
 * develop: develop 에 없음 — 이 PR 이 신설. VARCHAR/CHAR 목적 한 case(9177) × BIGINT/INTEGER/SMALLINT 소스 한 case(9229)의 두
 * 겹 분기 안이었다.
 * 이 PR: tp_ltoa 로 찍고 precision 초과면 DOMAIN_OVERFLOW, 아니면 tp_make_varchar_conversion.
 * 바뀐 것: 두 겹 분기를 셀로 펼쳤다(+44줄). 값 꺼내는 한 줄만 흔적 블록 안에 남았다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_integer_to_varchar (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				     date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;
  DB_DATA_STATUS data_stat = DATA_STATUS_OK;

  {
    int max_size = TP_BIGINT_PRECISION + 2 + 1;
    char *new_string;
    DB_BIGINT num;

    new_string = (char *) db_private_alloc (NULL, max_size);
    if (!new_string)
      {
	return DOMAIN_ERROR;
      }

    {
      num = (DB_BIGINT) db_get_int (src);
    }

    if (tp_ltoa (num, new_string, 10))
      {
	if (db_value_precision (target) != TP_FLOATING_PRECISION_VALUE
	    && db_value_precision (target) < (int) strlen (new_string))
	  {
	    status = DOMAIN_OVERFLOW;
	    db_private_free_and_init (NULL, new_string);
	  }
	else
	  {
	    tp_make_varchar_conversion (desired_domain, new_string, target, &status, &data_stat);
	  }
      }
    else
      {
	status = DOMAIN_ERROR;
	db_private_free_and_init (NULL, new_string);
      }
  }

  return status;
}

/*
 * [리뷰] tp_value_convert_bigint_to_varchar — BIGINT → VARCHAR 셀.
 * develop: develop 에 없음 — 이 PR 이 신설. 같은 두 겹 분기(9177 × 9229) 안이었다.
 * 이 PR: db_get_bigint 값을 tp_ltoa 로 찍고 precision 검사 후 tp_make_varchar_conversion.
 * 바뀐 것: 두 겹 분기를 셀로 펼쳤다(+44줄).
 */
static TP_DOMAIN_STATUS
tp_value_convert_bigint_to_varchar (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				    date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;
  DB_DATA_STATUS data_stat = DATA_STATUS_OK;

  {
    int max_size = TP_BIGINT_PRECISION + 2 + 1;
    char *new_string;
    DB_BIGINT num;

    new_string = (char *) db_private_alloc (NULL, max_size);
    if (!new_string)
      {
	return DOMAIN_ERROR;
      }

    {
      num = db_get_bigint (src);
    }

    if (tp_ltoa (num, new_string, 10))
      {
	if (db_value_precision (target) != TP_FLOATING_PRECISION_VALUE
	    && db_value_precision (target) < (int) strlen (new_string))
	  {
	    status = DOMAIN_OVERFLOW;
	    db_private_free_and_init (NULL, new_string);
	  }
	else
	  {
	    tp_make_varchar_conversion (desired_domain, new_string, target, &status, &data_stat);
	  }
      }
    else
      {
	status = DOMAIN_ERROR;
	db_private_free_and_init (NULL, new_string);
      }
  }

  return status;
}

/*
 * [리뷰] tp_value_convert_float_to_varchar — FLOAT → VARCHAR 셀 — _dtoa 로 유효숫자만 찍는다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 은 DOUBLE·FLOAT 이 한 case(object_domain.c:9276)로 `if (original_type
 * == DB_TYPE_FLOAT) tp_ftoa; else tp_dtoa;` 였고 그 뒤 공통으로 NULL·precision 을 봤다.
 * 이 PR: tp_ftoa_varchar 를 부르고, target 이 NULL 이면 er_errid()==ER_OUT_OF_VIRTUAL_MEMORY 여부로
 * DOMAIN_ERROR/INCOMPATIBLE, 길이가 precision 초과면 DOMAIN_OVERFLOW.
 * 바뀐 것: 소스 if/else 와 목적 switch 가 모두 풀려 FLOAT/DOUBLE × CHAR/VARCHAR 4칸이 됐다(+33줄). NULL 로 OOM 을 역추적하는 레거시 수법은
 * 그대로다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_float_to_varchar (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				   date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;

  {
    {
      tp_ftoa_varchar (src, target);
    }

    if (DB_IS_NULL (target))
      {
	if (er_errid () == ER_OUT_OF_VIRTUAL_MEMORY)
	  {
	    /* no way to report "out of memory" from tp_value_cast_internal() ?? */
	    status = DOMAIN_ERROR;
	  }
	else
	  {
	    status = DOMAIN_INCOMPATIBLE;
	  }
      }
    else if (DB_VALUE_PRECISION (target) != TP_FLOATING_PRECISION_VALUE
	     && (db_get_string_length (target) > DB_VALUE_PRECISION (target)))
      {
	status = DOMAIN_OVERFLOW;
	pr_clear_value (target);
      }
  }

  return status;
}

/*
 * [리뷰] tp_value_convert_double_to_varchar — DOUBLE → VARCHAR 셀.
 * develop: develop 에 없음 — 이 PR 이 신설. develop DOUBLE/FLOAT 한 case(9276)의 else 쪽(tp_dtoa)이었다.
 * 이 PR: tp_dtoa_varchar 를 부르고 FLOAT 판과 같은 NULL·precision 검사를 한다.
 * 바뀐 것: 소스·목적 분기 펼침(+33줄).
 */
static TP_DOMAIN_STATUS
tp_value_convert_double_to_varchar (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				    date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;

  {
    {
      tp_dtoa_varchar (src, target);
    }

    if (DB_IS_NULL (target))
      {
	if (er_errid () == ER_OUT_OF_VIRTUAL_MEMORY)
	  {
	    /* no way to report "out of memory" from tp_value_cast_internal() ?? */
	    status = DOMAIN_ERROR;
	  }
	else
	  {
	    status = DOMAIN_INCOMPATIBLE;
	  }
      }
    else if (DB_VALUE_PRECISION (target) != TP_FLOATING_PRECISION_VALUE
	     && (db_get_string_length (target) > DB_VALUE_PRECISION (target)))
      {
	status = DOMAIN_OVERFLOW;
	pr_clear_value (target);
      }
  }

  return status;
}

/*
 * [리뷰] tp_value_convert_monetary_to_varchar — MONETARY → VARCHAR 셀 — 통화 기호 + 소수 2자리로 찍고 꼬리 0 과 소수점을 지운다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop VARCHAR/CHAR case 안 `case
 * DB_TYPE_MONETARY:`(object_domain.c:9342)였다.
 * 이 PR: snprintf("%s%.*f", lang_currency_symbol(...), 2, amount) 뒤 꼬리 0·'.' 제거, precision 초과면 DOMAIN_OVERFLOW,
 * 아니면 tp_make_varchar_conversion.
 * 바뀐 것: 목적 타입 분기만 풀렸다(+48줄). 포맷·꼬리 제거 루프는 develop 과 한 글자도 다르지 않다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_monetary_to_varchar (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				      date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;
  DB_DATA_STATUS data_stat = DATA_STATUS_OK;

  {
    /* monetary symbol = 3 sign = 1 dot = 1 fraction digits = 2 NUL terminator = 1 */
    int max_size = DBL_MAX_DIGITS + 3 + 1 + 1 + 2 + 1;
    char *new_string;
    char *p;

    new_string = (char *) db_private_alloc (NULL, max_size);
    if (!new_string)
      {
	return DOMAIN_ERROR;
      }

    snprintf (new_string, max_size - 1, "%s%.*f", lang_currency_symbol (db_get_monetary (src)->type), 2,
	      db_get_monetary (src)->amount);
    new_string[max_size - 1] = '\0';

    p = new_string + strlen (new_string);
    for (--p; p >= new_string && *p == '0'; p--)
      {
	/* remove trailing zeros */
	*p = '\0';
      }
    if (*p == '.')	/* remove point */
      {
	*p = '\0';
      }

    if (db_value_precision (target) != TP_FLOATING_PRECISION_VALUE
	&& db_value_precision (target) < (int) strlen (new_string))
      {
	status = DOMAIN_OVERFLOW;
	db_private_free_and_init (NULL, new_string);
      }
    else
      {
	tp_make_varchar_conversion (desired_domain, new_string, target, &status, &data_stat);
      }
  }

  return status;
}

/*
 * [리뷰] tp_value_convert_numeric_to_varchar — NUMERIC → VARCHAR 셀 — numeric_db_value_print 의 10진 표기를 그대로 담는다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop VARCHAR/CHAR case 안 NUMERIC 갈래(9310 근처)였다.
 * 이 PR: 스택 버퍼에 print 한 뒤 길이+1 만큼 db_private_alloc 해 복사, precision 초과면 DOMAIN_OVERFLOW, 아니면
 * tp_make_varchar_conversion.
 * 바뀐 것: 목적 타입 분기만 풀렸다(+37줄). precision 비교에 strlen 대신 max_size-1 을 쓰는 것도 develop 과 같다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_numeric_to_varchar (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				     date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;
  DB_DATA_STATUS data_stat = DATA_STATUS_OK;

  {
    char str_buf[NUMERIC_MAX_STRING_SIZE];
    char *new_string;
    int max_size;

    numeric_db_value_print (src, str_buf);

    max_size = strlen (str_buf) + 1;
    new_string = (char *) db_private_alloc (NULL, max_size);
    if (new_string == NULL)
      {
	return DOMAIN_ERROR;
      }

    strcpy (new_string, str_buf);

    if (db_value_precision (target) != TP_FLOATING_PRECISION_VALUE
	&& db_value_precision (target) < max_size - 1)
      {
	status = DOMAIN_OVERFLOW;
	db_private_free_and_init (NULL, new_string);
      }
    else
      {
	tp_make_varchar_conversion (desired_domain, new_string, target, &status, &data_stat);
      }
  }

  return status;
}

/*
 * [리뷰] tp_value_convert_char_to_varchar — 문자열 → 문자열 중 서로 다른 CHAR 계열끼리(CHAR→VARCHAR, VARCHAR→CHAR) 쓰는 셀. 표가
 * CHAR 목적·VARCHAR 소스(object_domain_convert.cpp:7679)와 VARCHAR 목적·CHAR 소스(7727)에 이것을 건다 — 길이 패딩/자르기가 반드시 필요한
 * 조합이다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 은 VARCHAR/CHAR 목적 × VARCHAR/CHAR 소스가 한
 * 갈래(object_domain.c:9180~9208)였고, src==dest 이고 tp_can_steal_string 이면 도메인만 갈아끼우고, 아니면 db_char_string_coerce 뒤
 * 그 자리에서 coercion_mode·PRM_ID_ALLOW_TRUNCATED_STRING 으로 잘림 판정을 했다(9197).
 * 이 PR: db_char_string_coerce 만 하고 잘림이면 DOMAIN_TRUNCATED 를 돌려준다. collation_flag 가 LEAVE 가 아니면 목적 도메인의
 * 코드셋·collation 을 찍는다.
 * 바뀐 것: 잘림 정책이 호출자로, slam 최적화는 호출자의 `if (src == dest)` 앞단(object_domain.c:5786~)으로 올라가고 셀에는 순수 변환만 남았다(+24줄).
 * ENUM→CHAR·CLOB→CHAR 셀도 임시 VARCHAR 를 만든 뒤 이 셀을 부른다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_char_to_varchar (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				  date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;
  DB_DATA_STATUS data_stat = DATA_STATUS_OK;

  if (db_char_string_coerce (src, target, &data_stat) != NO_ERROR)
    {
      status = DOMAIN_INCOMPATIBLE;
    }
  else if (data_stat == DATA_STATUS_TRUNCATED)
    {
      status = DOMAIN_TRUNCATED;
    }
  else if (desired_domain->collation_flag != TP_DOMAIN_COLL_LEAVE)
    {
      db_string_put_cs_and_collation (target, TP_DOMAIN_CODESET (desired_domain),
				      TP_DOMAIN_COLLATION (desired_domain));
      status = DOMAIN_COMPATIBLE;
    }

  return status;
}

/*
 * [리뷰] tp_value_convert_varchar_to_varchar — 문자열 → 문자열 중 소스와 목적이 같은 CHAR 계열일 때(CHAR→CHAR, VARCHAR→VARCHAR) 쓰는
 * 셀. 표가 CHAR 목적·CHAR 소스(object_domain_convert.cpp:7678)와 VARCHAR 목적·VARCHAR 소스(7730)에 이것을 건다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 에서는 cross 타입과 같은 한 갈래였고, src != dest 이면 항상 db_char_string_coerce
 * 를 탔다.
 * 이 PR: precision 이 같고 (COLL_LEAVE 이거나 코드셋이 같으면) pr_clone_value 로 복제하고 collation 만 찍어 바로 COMPATIBLE. 아니면
 * db_char_string_coerce + DOMAIN_TRUNCATED 판정.
 * 바뀐 것: develop 에 없던 복제 빠른 경로가 추가됐다(+35줄). 행마다 같은 셀을 반복해 부르는 새 실행 모델에서 재코딩을 피하려는 것으로, PR 설명의 '같은 타입 바인드' 셀이
 * 0.94~0.96 으로 줄어든 것과 같은 방향이다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_varchar_to_varchar (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				     date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;
  DB_DATA_STATUS data_stat = DATA_STATUS_OK;

  if (DB_VALUE_PRECISION (src) == desired_domain->precision
      && (desired_domain->collation_flag == TP_DOMAIN_COLL_LEAVE
	  || db_get_string_codeset (src) == TP_DOMAIN_CODESET (desired_domain)))
    {
      pr_clone_value (src, target);
      if (desired_domain->collation_flag != TP_DOMAIN_COLL_LEAVE)
	db_string_put_cs_and_collation (target, TP_DOMAIN_CODESET (desired_domain),
					TP_DOMAIN_COLLATION (desired_domain));
      return DOMAIN_COMPATIBLE;
    }

  if (db_char_string_coerce (src, target, &data_stat) != NO_ERROR)
    {
      status = DOMAIN_INCOMPATIBLE;
    }
  else if (data_stat == DATA_STATUS_TRUNCATED)
    {
      status = DOMAIN_TRUNCATED;
    }
  else if (desired_domain->collation_flag != TP_DOMAIN_COLL_LEAVE)
    {
      db_string_put_cs_and_collation (target, TP_DOMAIN_CODESET (desired_domain),
				      TP_DOMAIN_COLLATION (desired_domain));
      status = DOMAIN_COMPATIBLE;
    }

  return status;
}

/*
 * [리뷰] tp_value_convert_date_to_varchar — DATE → VARCHAR 셀 — db_date_to_string 의 표기를 담는다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 은 날짜·시간 8개 소스가 VARCHAR/CHAR 목적의 한 case(object_domain.c:9383)로 묶여
 * 안쪽 switch 가 문자열화 함수만 갈랐다.
 * 이 PR: DATETIMETZ_BUF_SIZE 버퍼에 db_date_to_string 으로 찍고, precision 초과면 DOMAIN_OVERFLOW, 아니면
 * tp_make_varchar_conversion.
 * 바뀐 것: 8개 소스가 묶여 있던 case 가 소스별 셀로 펼쳐졌다(+41줄). 안쪽 switch 가 사라지면서 `err = NO_ERROR;` 직후의 `if (err != NO_ERROR)`
 * 가 항상 거짓인 죽은 분기로 남았다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_date_to_varchar (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				  date_conversion_error *error)
{
  int err = NO_ERROR;
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;
  DB_DATA_STATUS data_stat = DATA_STATUS_OK;

  {
    int max_size = DATETIMETZ_BUF_SIZE;
    char *new_string;

    new_string = (char *) db_private_alloc (NULL, max_size);
    if (!new_string)
      {
	return DOMAIN_ERROR;
      }

    err = NO_ERROR;

    db_date_to_string (new_string, max_size, (DB_DATE *) db_get_date (src));

    if (err != NO_ERROR)
      {
	return DOMAIN_ERROR;
      }

    if (db_value_precision (target) != TP_FLOATING_PRECISION_VALUE
	&& db_value_precision (target) < (int) strlen (new_string))
      {
	status = DOMAIN_OVERFLOW;
	db_private_free_and_init (NULL, new_string);
      }
    else
      {
	tp_make_varchar_conversion (desired_domain, new_string, target, &status, &data_stat);
      }
  }

  return err < 0 ? DOMAIN_ERROR : status;
}

/*
 * [리뷰] tp_value_convert_time_to_varchar — TIME → VARCHAR 셀.
 * develop: develop 에 없음 — 이 PR 이 신설. 날짜·시간 8개 소스가 묶인 한 case(object_domain.c:9383)의 TIME 갈래였다.
 * 이 PR: db_time_to_string 으로 찍고 같은 precision 검사를 한다.
 * 바뀐 것: 소스별 셀로 분리(+41줄). 같은 죽은 err 분기가 남았다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_time_to_varchar (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				  date_conversion_error *error)
{
  int err = NO_ERROR;
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;
  DB_DATA_STATUS data_stat = DATA_STATUS_OK;

  {
    int max_size = DATETIMETZ_BUF_SIZE;
    char *new_string;

    new_string = (char *) db_private_alloc (NULL, max_size);
    if (!new_string)
      {
	return DOMAIN_ERROR;
      }

    err = NO_ERROR;

    db_time_to_string (new_string, max_size, (DB_TIME *) db_get_time (src));

    if (err != NO_ERROR)
      {
	return DOMAIN_ERROR;
      }

    if (db_value_precision (target) != TP_FLOATING_PRECISION_VALUE
	&& db_value_precision (target) < (int) strlen (new_string))
      {
	status = DOMAIN_OVERFLOW;
	db_private_free_and_init (NULL, new_string);
      }
    else
      {
	tp_make_varchar_conversion (desired_domain, new_string, target, &status, &data_stat);
      }
  }

  return err < 0 ? DOMAIN_ERROR : status;
}

/*
 * [리뷰] tp_value_convert_timestamp_to_varchar — TIMESTAMP → VARCHAR 셀 — 세션 타임존 기준 표기.
 * develop: develop 에 없음 — 이 PR 이 신설. 날짜·시간 8개 소스가 묶인 한 case(9383)의 TIMESTAMP 갈래였다.
 * 이 PR: db_timestamp_to_string_core(…, error) 로 찍고 같은 precision 검사를 한다.
 * 바뀐 것: 소스별 셀 분리 + 문자열화 함수를 er_set 하지 않는 _core 변종으로 교체(+41줄). 죽은 err 분기가 남았다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_timestamp_to_varchar (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				       date_conversion_error *error)
{
  int err = NO_ERROR;
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;
  DB_DATA_STATUS data_stat = DATA_STATUS_OK;

  {
    int max_size = DATETIMETZ_BUF_SIZE;
    char *new_string;

    new_string = (char *) db_private_alloc (NULL, max_size);
    if (!new_string)
      {
	return DOMAIN_ERROR;
      }

    err = NO_ERROR;

    db_timestamp_to_string_core (new_string, max_size, (DB_TIMESTAMP *) db_get_timestamp (src), error);

    if (err != NO_ERROR)
      {
	return DOMAIN_ERROR;
      }

    if (db_value_precision (target) != TP_FLOATING_PRECISION_VALUE
	&& db_value_precision (target) < (int) strlen (new_string))
      {
	status = DOMAIN_OVERFLOW;
	db_private_free_and_init (NULL, new_string);
      }
    else
      {
	tp_make_varchar_conversion (desired_domain, new_string, target, &status, &data_stat);
      }
  }

  return err < 0 ? DOMAIN_ERROR : status;
}

/*
 * [리뷰] tp_value_convert_timestampltz_to_varchar — TIMESTAMPLTZ → VARCHAR 셀 — 세션 TZ_ID 를 만들어 TZ 가 붙은 표기로 찍는다.
 * develop: develop 에 없음 — 이 PR 이 신설. 날짜·시간 8개 소스가 묶인 한 case(9383)의 TIMESTAMPLTZ 갈래였다.
 * 이 PR: tz_create_session_tzid_for_timestamp_core 로 TZ_ID 를 얻고(실패 DOMAIN_ERROR) db_timestamptz_to_string_core
 * 로 찍는다.
 * 바뀐 것: 소스별 셀 분리 + _core 교체(+48줄). err != NO_ERROR 로 빠지는 경로에서 new_string 을 해제하지 않는데, develop 의 같은
 * 자리(object_domain.c:9447)도 해제하지 않았다 — 기존 누수를 그대로 옮겼다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_timestampltz_to_varchar (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  int err = NO_ERROR;
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;
  DB_UTIME v_utime;
  DB_DATA_STATUS data_stat = DATA_STATUS_OK;
  TZ_ID ses_tz_id;

  {
    int max_size = DATETIMETZ_BUF_SIZE;
    char *new_string;

    new_string = (char *) db_private_alloc (NULL, max_size);
    if (!new_string)
      {
	return DOMAIN_ERROR;
      }

    err = NO_ERROR;

    v_utime = *db_get_timestamp (src);
    err = tz_create_session_tzid_for_timestamp_core (&v_utime, &ses_tz_id, error);
    if (err == NO_ERROR)
      {
	db_timestamptz_to_string_core (new_string, max_size, &v_utime, &ses_tz_id, error);
      }

    if (err != NO_ERROR)
      {
	return DOMAIN_ERROR;
      }

    if (db_value_precision (target) != TP_FLOATING_PRECISION_VALUE
	&& db_value_precision (target) < (int) strlen (new_string))
      {
	status = DOMAIN_OVERFLOW;
	db_private_free_and_init (NULL, new_string);
      }
    else
      {
	tp_make_varchar_conversion (desired_domain, new_string, target, &status, &data_stat);
      }
  }

  return err < 0 ? DOMAIN_ERROR : status;
}

/*
 * [리뷰] tp_value_convert_timestamptz_to_varchar — TIMESTAMPTZ → VARCHAR 셀 — 값에 붙은 TZ_ID 로 TZ 표기를 찍는다.
 * develop: develop 에 없음 — 이 PR 이 신설. 날짜·시간 8개 소스가 묶인 한 case(object_domain.c:9383)의 TIMESTAMPTZ 갈래였다.
 * 이 PR: db_timestamptz_to_string_core(…, &tz_id, error) 로 찍고 precision 초과면 DOMAIN_OVERFLOW, 아니면
 * tp_make_varchar_conversion.
 * 바뀐 것: 소스별 셀 분리 + _core 교체(+44줄). `err = NO_ERROR;` 직후의 `if (err != NO_ERROR)` 는 죽은 분기로 남았다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_timestamptz_to_varchar (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
    date_conversion_error *error)
{
  int err = NO_ERROR;
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;
  DB_TIMESTAMPTZ v_timestamptz;
  DB_DATA_STATUS data_stat = DATA_STATUS_OK;

  {
    int max_size = DATETIMETZ_BUF_SIZE;
    char *new_string;

    new_string = (char *) db_private_alloc (NULL, max_size);
    if (!new_string)
      {
	return DOMAIN_ERROR;
      }

    err = NO_ERROR;

    v_timestamptz = *db_get_timestamptz (src);
    db_timestamptz_to_string_core (new_string, max_size, &v_timestamptz.timestamp, &v_timestamptz.tz_id,
				   error);

    if (err != NO_ERROR)
      {
	return DOMAIN_ERROR;
      }

    if (db_value_precision (target) != TP_FLOATING_PRECISION_VALUE
	&& db_value_precision (target) < (int) strlen (new_string))
      {
	status = DOMAIN_OVERFLOW;
	db_private_free_and_init (NULL, new_string);
      }
    else
      {
	tp_make_varchar_conversion (desired_domain, new_string, target, &status, &data_stat);
      }
  }

  return err < 0 ? DOMAIN_ERROR : status;
}

/*
 * [리뷰] tp_value_convert_datetime_to_varchar — DATETIME → VARCHAR 셀.
 * develop: develop 에 없음 — 이 PR 이 신설. 날짜·시간 8개 소스가 묶인 한 case(9383)의 DATETIME 갈래였다.
 * 이 PR: db_datetime_to_string 으로 찍고 같은 precision 검사.
 * 바뀐 것: 소스별 셀 분리(+41줄). 죽은 err 분기가 남았다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_datetime_to_varchar (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				      date_conversion_error *error)
{
  int err = NO_ERROR;
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;
  DB_DATA_STATUS data_stat = DATA_STATUS_OK;

  {
    int max_size = DATETIMETZ_BUF_SIZE;
    char *new_string;

    new_string = (char *) db_private_alloc (NULL, max_size);
    if (!new_string)
      {
	return DOMAIN_ERROR;
      }

    err = NO_ERROR;

    db_datetime_to_string (new_string, max_size, (DB_DATETIME *) db_get_datetime (src));

    if (err != NO_ERROR)
      {
	return DOMAIN_ERROR;
      }

    if (db_value_precision (target) != TP_FLOATING_PRECISION_VALUE
	&& db_value_precision (target) < (int) strlen (new_string))
      {
	status = DOMAIN_OVERFLOW;
	db_private_free_and_init (NULL, new_string);
      }
    else
      {
	tp_make_varchar_conversion (desired_domain, new_string, target, &status, &data_stat);
      }
  }

  return err < 0 ? DOMAIN_ERROR : status;
}

/*
 * [리뷰] tp_value_convert_datetimeltz_to_varchar — DATETIMELTZ → VARCHAR 셀 — 세션 TZ_ID 를 만들어 TZ 표기를 찍는다.
 * develop: develop 에 없음 — 이 PR 이 신설. 날짜·시간 8개 소스가 묶인 한 case(9383)의 DATETIMELTZ 갈래였다.
 * 이 PR: tz_create_session_tzid_for_datetime_core(…, true, …)로 TZ_ID 를 얻고(실패 DOMAIN_ERROR)
 * db_datetimetz_to_string_core 로 찍는다.
 * 바뀐 것: 소스별 셀 분리 + _core 교체(+48줄). err != NO_ERROR 로 빠질 때 new_string 을 해제하지 않는 것은
 * develop(object_domain.c:9447)에서 그대로 옮겨온 누수다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_datetimeltz_to_varchar (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
    date_conversion_error *error)
{
  int err = NO_ERROR;
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;
  DB_DATETIME v_datetime;
  DB_DATA_STATUS data_stat = DATA_STATUS_OK;
  TZ_ID ses_tz_id;

  {
    int max_size = DATETIMETZ_BUF_SIZE;
    char *new_string;

    new_string = (char *) db_private_alloc (NULL, max_size);
    if (!new_string)
      {
	return DOMAIN_ERROR;
      }

    err = NO_ERROR;

    v_datetime = *db_get_datetime (src);
    err = tz_create_session_tzid_for_datetime_core (&v_datetime, true, &ses_tz_id, error);
    if (err == NO_ERROR)
      {
	db_datetimetz_to_string_core (new_string, max_size, &v_datetime, &ses_tz_id, error);
      }

    if (err != NO_ERROR)
      {
	return DOMAIN_ERROR;
      }

    if (db_value_precision (target) != TP_FLOATING_PRECISION_VALUE
	&& db_value_precision (target) < (int) strlen (new_string))
      {
	status = DOMAIN_OVERFLOW;
	db_private_free_and_init (NULL, new_string);
      }
    else
      {
	tp_make_varchar_conversion (desired_domain, new_string, target, &status, &data_stat);
      }
  }

  return err < 0 ? DOMAIN_ERROR : status;
}

/*
 * [리뷰] tp_value_convert_datetimetz_to_varchar — DATETIMETZ → VARCHAR 셀 — 값의 TZ_ID 로 TZ 표기를 찍는다.
 * develop: develop 에 없음 — 이 PR 이 신설. 날짜·시간 8개 소스가 묶인 한 case(9383)의 DATETIMETZ 갈래였다.
 * 이 PR: db_datetimetz_to_string_core(…, &v_datetimetz.tz_id, error) 로 찍는다.
 * 바뀐 것: 소스별 셀 분리 + _core 교체(+43줄). 죽은 err 분기가 남았다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_datetimetz_to_varchar (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
					date_conversion_error *error)
{
  int err = NO_ERROR;
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;
  DB_DATETIMETZ v_datetimetz;
  DB_DATA_STATUS data_stat = DATA_STATUS_OK;

  {
    int max_size = DATETIMETZ_BUF_SIZE;
    char *new_string;

    new_string = (char *) db_private_alloc (NULL, max_size);
    if (!new_string)
      {
	return DOMAIN_ERROR;
      }

    err = NO_ERROR;

    v_datetimetz = *db_get_datetimetz (src);
    db_datetimetz_to_string_core (new_string, max_size, &v_datetimetz.datetime, &v_datetimetz.tz_id, error);

    if (err != NO_ERROR)
      {
	return DOMAIN_ERROR;
      }

    if (db_value_precision (target) != TP_FLOATING_PRECISION_VALUE
	&& db_value_precision (target) < (int) strlen (new_string))
      {
	status = DOMAIN_OVERFLOW;
	db_private_free_and_init (NULL, new_string);
      }
    else
      {
	tp_make_varchar_conversion (desired_domain, new_string, target, &status, &data_stat);
      }
  }

  return err < 0 ? DOMAIN_ERROR : status;
}

/*
 * [리뷰] tp_value_convert_enumeration_to_varchar — ENUM → VARCHAR 셀 — ENUM 이름 문자열을 목적 VARCHAR 도메인으로 옮긴다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop VARCHAR/CHAR case 의 ENUMERATION 갈래(object_domain.c:9212)로,
 * varchar 뷰를 만든 뒤 tp_value_cast_internal 재귀였다.
 * 이 PR: tp_enumeration_to_varchar 로 뷰를 만들고 tp_value_convert_varchar_to_varchar(동일 타입용 셀)를 직접 부른다.
 * 바뀐 것: 재귀 → 직접 호출(+21줄). 목적지가 VARCHAR 이고 뷰도 VARCHAR 이라 동일 타입 셀을 고정으로 부른다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_enumeration_to_varchar (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
    date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;

  {
    DB_VALUE varchar_val;

    if (tp_enumeration_to_varchar (src, &varchar_val) != NO_ERROR)
      {
	status = DOMAIN_ERROR;
      }
    else
      {
	status = tp_value_convert_varchar_to_varchar (&varchar_val, target, desired_domain, error);
      }
  }

  return status;
}

/*
 * [리뷰] tp_value_convert_bit_to_varchar — BIT·VARBIT → VARCHAR 셀 — 비트열을 16진 문자열로 찍는다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop VARCHAR/CHAR case 의 `case DB_TYPE_BIT: case
 * DB_TYPE_VARBIT:`(object_domain.c:9465)였다.
 * 이 PR: ((len+3)/4)+1 바이트를 잡아 bfmt_print(BIT_STRING_HEX) 로 찍고, 성공이면 precision 검사 후 tp_make_varchar_conversion,
 * -1 이면 DOMAIN_OVERFLOW, 그 밖은 DOMAIN_ERROR.
 * 바뀐 것: 목적 타입 분기만 풀렸다(+49줄). 세 갈래 에러 처리는 develop 과 같다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_bit_to_varchar (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				 date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;
  DB_DATA_STATUS data_stat = DATA_STATUS_OK;

  {
    int max_size;
    char *new_string;
    int convert_error;

    max_size = ((db_get_string_length (src) + 3) / 4) + 1;
    new_string = (char *) db_private_alloc (NULL, max_size);
    if (!new_string)
      {
	return DOMAIN_ERROR;
      }

    convert_error = bfmt_print (1 /* BIT_STRING_HEX */, src,
				new_string, max_size);

    if (convert_error == NO_ERROR)
      {
	if (db_value_precision (target) != TP_FLOATING_PRECISION_VALUE
	    && (db_value_precision (target) < (int) strlen (new_string)))
	  {
	    status = DOMAIN_OVERFLOW;
	    db_private_free_and_init (NULL, new_string);
	  }
	else
	  {
	    tp_make_varchar_conversion (desired_domain, new_string, target, &status, &data_stat);
	  }
      }
    else if (convert_error == -1)
      {
	status = DOMAIN_OVERFLOW;
	db_private_free_and_init (NULL, new_string);
      }
    else
      {
	status = DOMAIN_ERROR;
	db_private_free_and_init (NULL, new_string);
      }
  }

  return status;
}

/*
 * [리뷰] tp_value_convert_clob_to_varchar — CLOB → VARCHAR 셀 — LOB 내용을 목적 도메인의 코드셋으로 읽어 문자열로 만든다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop VARCHAR/CHAR case 의 CLOB 갈래였고, db_clob_to_char 결과를
 * tp_value_cast_internal 로 재귀 캐스트한 뒤 그 상태를 int err 에 덮어써 사실상 버렸다.
 * 이 PR: db_clob_to_char 뒤 tp_value_convert_varchar_to_varchar 를 부르고, 실패면 target 을 NULL 로 만든 뒤 COMPATIBLE 로
 * 흡수한다. 최종 반환은 `err < 0 ? DOMAIN_ERROR : status`.
 * 바뀐 것: 재귀 → 직접 호출(+36줄). develop 의 '실패해도 성공+NULL' 동작을 주석과 함께 재현했다. src==dest 인 CLOB→CHAR 는 셀이 아니라 호출자
 * tp_value_cast_internal(object_domain.c:5863~)이 따로 처리한다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_clob_to_varchar (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				  date_conversion_error *error)
{
  int err = NO_ERROR;
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;

  {
    DB_VALUE tmpval;
    DB_VALUE cs;

    db_make_null (&tmpval);
    /* convert directly from CLOB into charset of desired domain string */
    db_make_int (&cs, desired_domain->codeset);
    err = db_clob_to_char (src, &cs, &tmpval);
    if (err == NO_ERROR)
      {
	TP_DOMAIN_STATUS nested_status =
		tp_value_convert_varchar_to_varchar (&tmpval, target, desired_domain, error);
	if (nested_status == DOMAIN_COMPATIBLE || nested_status == DOMAIN_TRUNCATED)
	  {
	    status = nested_status;
	  }
	else
	  {
	    /* The old outer LOB cast returned success with a NULL result. */
	    pr_clear_value (target);
	    db_make_null (target);
	  }
      }

    pr_clear_value (&tmpval);
  }

  return err < 0 ? DOMAIN_ERROR : status;
}

/*
 * [리뷰] tp_value_convert_json_to_varchar — JSON → VARCHAR 셀 — 문서의 원문(raw body)을 그대로 문자열로 만든다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop VARCHAR/CHAR case 의 `case DB_TYPE_JSON:` 였다.
 * 이 PR: db_json_get_raw_json_body_from_document 가 돌려준 버퍼를 precision 과 비교해 넘치면 해제 후 DOMAIN_OVERFLOW, 아니면
 * tp_make_varchar_conversion 으로 담고 need_clear 를 세운다.
 * 바뀐 것: 목적 타입 분기만 풀렸다(+28줄).
 */
static TP_DOMAIN_STATUS
tp_value_convert_json_to_varchar (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				  date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;
  DB_DATA_STATUS data_stat = DATA_STATUS_OK;

  {
    char *json_str;
    int len;

    json_str = db_json_get_raw_json_body_from_document (db_get_json_document (src));
    len = strlen (json_str);

    if (db_value_precision (target) != TP_FLOATING_PRECISION_VALUE && db_value_precision (target) < len)
      {
	status = DOMAIN_OVERFLOW;
	db_private_free_and_init (NULL, json_str);
      }
    else
      {
	tp_make_varchar_conversion (desired_domain, json_str, target, &status, &data_stat);
	target->need_clear = true;
      }
  }

  return status;
}

/*
 * [리뷰] tp_value_convert_short_to_char — SHORT → CHAR 셀 — 정수를 10진 문자열로 찍어 고정 길이 CHAR 도메인에 담는다.
 * develop: develop 에 없음 — 이 PR 이 신설. VARCHAR/CHAR 목적 한 case(object_domain.c:9177) × BIGINT/INTEGER/SMALLINT 소스
 * 한 case(9229)의 두 겹 분기 안이었다.
 * 이 PR: tp_ltoa 로 찍고 precision 초과면 DOMAIN_OVERFLOW, 아니면 tp_make_char_conversion(VARCHAR 판과 여기만 다르다).
 * 바뀐 것: 두 겹 분기를 셀로 펼친 6칸 중 CHAR 쪽(+44줄). 같은 소스의 _to_varchar 판과 마지막 한 줄만 다르다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_short_to_char (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;
  DB_DATA_STATUS data_stat = DATA_STATUS_OK;

  {
    int max_size = TP_BIGINT_PRECISION + 2 + 1;
    char *new_string;
    DB_BIGINT num;

    new_string = (char *) db_private_alloc (NULL, max_size);
    if (!new_string)
      {
	return DOMAIN_ERROR;
      }

    {
      num = (DB_BIGINT) db_get_short (src);
    }

    if (tp_ltoa (num, new_string, 10))
      {
	if (db_value_precision (target) != TP_FLOATING_PRECISION_VALUE
	    && db_value_precision (target) < (int) strlen (new_string))
	  {
	    status = DOMAIN_OVERFLOW;
	    db_private_free_and_init (NULL, new_string);
	  }
	else
	  {
	    tp_make_char_conversion (desired_domain, new_string, target, &status, &data_stat);
	  }
      }
    else
      {
	status = DOMAIN_ERROR;
	db_private_free_and_init (NULL, new_string);
      }
  }

  return status;
}

/*
 * [리뷰] tp_value_convert_integer_to_char — INTEGER → CHAR 셀.
 * develop: develop 에 없음 — 이 PR 이 신설. 같은 두 겹 분기(9177 × 9229) 안이었다.
 * 이 PR: tp_ltoa 로 찍고 precision 검사 후 tp_make_char_conversion.
 * 바뀐 것: 두 겹 분기를 셀로 펼친 6칸 중 하나(+44줄).
 */
static TP_DOMAIN_STATUS
tp_value_convert_integer_to_char (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				  date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;
  DB_DATA_STATUS data_stat = DATA_STATUS_OK;

  {
    int max_size = TP_BIGINT_PRECISION + 2 + 1;
    char *new_string;
    DB_BIGINT num;

    new_string = (char *) db_private_alloc (NULL, max_size);
    if (!new_string)
      {
	return DOMAIN_ERROR;
      }

    {
      num = (DB_BIGINT) db_get_int (src);
    }

    if (tp_ltoa (num, new_string, 10))
      {
	if (db_value_precision (target) != TP_FLOATING_PRECISION_VALUE
	    && db_value_precision (target) < (int) strlen (new_string))
	  {
	    status = DOMAIN_OVERFLOW;
	    db_private_free_and_init (NULL, new_string);
	  }
	else
	  {
	    tp_make_char_conversion (desired_domain, new_string, target, &status, &data_stat);
	  }
      }
    else
      {
	status = DOMAIN_ERROR;
	db_private_free_and_init (NULL, new_string);
      }
  }

  return status;
}

/*
 * [리뷰] tp_value_convert_bigint_to_char — BIGINT → CHAR 셀.
 * develop: develop 에 없음 — 이 PR 이 신설. 같은 두 겹 분기(9177 × 9229) 안이었다.
 * 이 PR: tp_ltoa 로 찍고 precision 검사 후 tp_make_char_conversion.
 * 바뀐 것: 두 겹 분기를 셀로 펼친 6칸 중 하나(+44줄).
 */
static TP_DOMAIN_STATUS
tp_value_convert_bigint_to_char (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				 date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;
  DB_DATA_STATUS data_stat = DATA_STATUS_OK;

  {
    int max_size = TP_BIGINT_PRECISION + 2 + 1;
    char *new_string;
    DB_BIGINT num;

    new_string = (char *) db_private_alloc (NULL, max_size);
    if (!new_string)
      {
	return DOMAIN_ERROR;
      }

    {
      num = db_get_bigint (src);
    }

    if (tp_ltoa (num, new_string, 10))
      {
	if (db_value_precision (target) != TP_FLOATING_PRECISION_VALUE
	    && db_value_precision (target) < (int) strlen (new_string))
	  {
	    status = DOMAIN_OVERFLOW;
	    db_private_free_and_init (NULL, new_string);
	  }
	else
	  {
	    tp_make_char_conversion (desired_domain, new_string, target, &status, &data_stat);
	  }
      }
    else
      {
	status = DOMAIN_ERROR;
	db_private_free_and_init (NULL, new_string);
      }
  }

  return status;
}

/*
 * [리뷰] tp_value_convert_float_to_char — FLOAT → CHAR 셀.
 * develop: develop 에 없음 — 이 PR 이 신설. develop DOUBLE/FLOAT 한 case(object_domain.c:9276)의 tp_ftoa 쪽 + 목적 switch
 * 였다.
 * 이 PR: tp_ftoa_char 뒤 NULL 이면 er_errid()==ER_OUT_OF_VIRTUAL_MEMORY 로 DOMAIN_ERROR/INCOMPATIBLE, 길이가 precision
 * 초과면 DOMAIN_OVERFLOW.
 * 바뀐 것: 소스·목적 분기를 모두 펼친 4칸 중 하나(+33줄).
 */
static TP_DOMAIN_STATUS
tp_value_convert_float_to_char (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;

  {
    {
      tp_ftoa_char (src, target);
    }

    if (DB_IS_NULL (target))
      {
	if (er_errid () == ER_OUT_OF_VIRTUAL_MEMORY)
	  {
	    /* no way to report "out of memory" from tp_value_cast_internal() ?? */
	    status = DOMAIN_ERROR;
	  }
	else
	  {
	    status = DOMAIN_INCOMPATIBLE;
	  }
      }
    else if (DB_VALUE_PRECISION (target) != TP_FLOATING_PRECISION_VALUE
	     && (db_get_string_length (target) > DB_VALUE_PRECISION (target)))
      {
	status = DOMAIN_OVERFLOW;
	pr_clear_value (target);
      }
  }

  return status;
}

/*
 * [리뷰] tp_value_convert_double_to_char — DOUBLE → CHAR 셀.
 * develop: develop 에 없음 — 이 PR 이 신설. develop DOUBLE/FLOAT case(9276)의 tp_dtoa 쪽 + 목적 switch 였다.
 * 이 PR: tp_dtoa_char 를 부르고 FLOAT 판과 같은 검사를 한다.
 * 바뀐 것: 소스·목적 분기 펼침(+33줄).
 */
static TP_DOMAIN_STATUS
tp_value_convert_double_to_char (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				 date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;

  {
    {
      tp_dtoa_char (src, target);
    }

    if (DB_IS_NULL (target))
      {
	if (er_errid () == ER_OUT_OF_VIRTUAL_MEMORY)
	  {
	    /* no way to report "out of memory" from tp_value_cast_internal() ?? */
	    status = DOMAIN_ERROR;
	  }
	else
	  {
	    status = DOMAIN_INCOMPATIBLE;
	  }
      }
    else if (DB_VALUE_PRECISION (target) != TP_FLOATING_PRECISION_VALUE
	     && (db_get_string_length (target) > DB_VALUE_PRECISION (target)))
      {
	status = DOMAIN_OVERFLOW;
	pr_clear_value (target);
      }
  }

  return status;
}

/*
 * [리뷰] tp_value_convert_monetary_to_char — MONETARY → CHAR 셀 — 통화 기호 + 소수 2자리로 찍고 꼬리 0·소수점을 지운다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop VARCHAR/CHAR case 의 `case
 * DB_TYPE_MONETARY:`(object_domain.c:9342)에서 make_desired_string_db_value 가 목적을 갈랐다.
 * 이 PR: VARCHAR 판과 같은 snprintf·꼬리 제거를 하고 마지막에 tp_make_char_conversion 으로 담는다.
 * 바뀐 것: 목적 타입 switch 가 풀리면서 VARCHAR 판과 한 줄만 다른 쌍둥이 셀이 생겼다(+48줄).
 */
static TP_DOMAIN_STATUS
tp_value_convert_monetary_to_char (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				   date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;
  DB_DATA_STATUS data_stat = DATA_STATUS_OK;

  {
    /* monetary symbol = 3 sign = 1 dot = 1 fraction digits = 2 NUL terminator = 1 */
    int max_size = DBL_MAX_DIGITS + 3 + 1 + 1 + 2 + 1;
    char *new_string;
    char *p;

    new_string = (char *) db_private_alloc (NULL, max_size);
    if (!new_string)
      {
	return DOMAIN_ERROR;
      }

    snprintf (new_string, max_size - 1, "%s%.*f", lang_currency_symbol (db_get_monetary (src)->type), 2,
	      db_get_monetary (src)->amount);
    new_string[max_size - 1] = '\0';

    p = new_string + strlen (new_string);
    for (--p; p >= new_string && *p == '0'; p--)
      {
	/* remove trailing zeros */
	*p = '\0';
      }
    if (*p == '.')	/* remove point */
      {
	*p = '\0';
      }

    if (db_value_precision (target) != TP_FLOATING_PRECISION_VALUE
	&& db_value_precision (target) < (int) strlen (new_string))
      {
	status = DOMAIN_OVERFLOW;
	db_private_free_and_init (NULL, new_string);
      }
    else
      {
	tp_make_char_conversion (desired_domain, new_string, target, &status, &data_stat);
      }
  }

  return status;
}

/*
 * [리뷰] tp_value_convert_numeric_to_char — NUMERIC → CHAR 셀.
 * develop: develop 에 없음 — 이 PR 이 신설. develop VARCHAR/CHAR case 의 NUMERIC 갈래였다.
 * 이 PR: numeric_db_value_print 결과를 복사해 precision 검사 후 tp_make_char_conversion.
 * 바뀐 것: 목적 타입 switch 가 풀리면서 VARCHAR 판과 한 줄만 다른 쌍둥이 셀이 생겼다(+37줄).
 */
static TP_DOMAIN_STATUS
tp_value_convert_numeric_to_char (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				  date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;
  DB_DATA_STATUS data_stat = DATA_STATUS_OK;

  {
    char str_buf[NUMERIC_MAX_STRING_SIZE];
    char *new_string;
    int max_size;

    numeric_db_value_print (src, str_buf);

    max_size = strlen (str_buf) + 1;
    new_string = (char *) db_private_alloc (NULL, max_size);
    if (new_string == NULL)
      {
	return DOMAIN_ERROR;
      }

    strcpy (new_string, str_buf);

    if (db_value_precision (target) != TP_FLOATING_PRECISION_VALUE
	&& db_value_precision (target) < max_size - 1)
      {
	status = DOMAIN_OVERFLOW;
	db_private_free_and_init (NULL, new_string);
      }
    else
      {
	tp_make_char_conversion (desired_domain, new_string, target, &status, &data_stat);
      }
  }

  return status;
}

/*
 * [리뷰] tp_value_convert_date_to_char — DATE → CHAR 셀.
 * develop: develop 에 없음 — 이 PR 이 신설. 날짜·시간 8개 소스가 VARCHAR/CHAR 한 case(object_domain.c:9383)로 묶여 있었고 목적 구분은
 * make_desired_string_db_value 안이었다.
 * 이 PR: db_date_to_string 으로 찍고 tp_make_char_conversion 으로 담는다.
 * 바뀐 것: 목적 switch 가 풀려 VARCHAR 판과 한 줄만 다른 쌍둥이 셀이 됐다. `err = NO_ERROR;` 직후의 `if (err != NO_ERROR)` 는 죽은
 * 분기다(+41줄).
 */
static TP_DOMAIN_STATUS
tp_value_convert_date_to_char (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
			       date_conversion_error *error)
{
  int err = NO_ERROR;
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;
  DB_DATA_STATUS data_stat = DATA_STATUS_OK;

  {
    int max_size = DATETIMETZ_BUF_SIZE;
    char *new_string;

    new_string = (char *) db_private_alloc (NULL, max_size);
    if (!new_string)
      {
	return DOMAIN_ERROR;
      }

    err = NO_ERROR;

    db_date_to_string (new_string, max_size, (DB_DATE *) db_get_date (src));

    if (err != NO_ERROR)
      {
	return DOMAIN_ERROR;
      }

    if (db_value_precision (target) != TP_FLOATING_PRECISION_VALUE
	&& db_value_precision (target) < (int) strlen (new_string))
      {
	status = DOMAIN_OVERFLOW;
	db_private_free_and_init (NULL, new_string);
      }
    else
      {
	tp_make_char_conversion (desired_domain, new_string, target, &status, &data_stat);
      }
  }

  return err < 0 ? DOMAIN_ERROR : status;
}

/*
 * [리뷰] tp_value_convert_time_to_char — TIME → CHAR 셀.
 * develop: develop 에 없음 — 이 PR 이 신설. 날짜·시간 8개 소스가 묶인 한 case(9383) + 목적 switch 안이었다.
 * 이 PR: db_time_to_string 으로 찍고 tp_make_char_conversion.
 * 바뀐 것: 목적 switch 가 풀린 쌍둥이 셀, 죽은 err 분기가 남았다(+41줄).
 */
static TP_DOMAIN_STATUS
tp_value_convert_time_to_char (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
			       date_conversion_error *error)
{
  int err = NO_ERROR;
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;
  DB_DATA_STATUS data_stat = DATA_STATUS_OK;

  {
    int max_size = DATETIMETZ_BUF_SIZE;
    char *new_string;

    new_string = (char *) db_private_alloc (NULL, max_size);
    if (!new_string)
      {
	return DOMAIN_ERROR;
      }

    err = NO_ERROR;

    db_time_to_string (new_string, max_size, (DB_TIME *) db_get_time (src));

    if (err != NO_ERROR)
      {
	return DOMAIN_ERROR;
      }

    if (db_value_precision (target) != TP_FLOATING_PRECISION_VALUE
	&& db_value_precision (target) < (int) strlen (new_string))
      {
	status = DOMAIN_OVERFLOW;
	db_private_free_and_init (NULL, new_string);
      }
    else
      {
	tp_make_char_conversion (desired_domain, new_string, target, &status, &data_stat);
      }
  }

  return err < 0 ? DOMAIN_ERROR : status;
}

/*
 * [리뷰] tp_value_convert_timestamp_to_char — TIMESTAMP → CHAR 셀.
 * develop: develop 에 없음 — 이 PR 이 신설. 날짜·시간 8개 소스가 묶인 한 case(9383) + 목적 switch 안이었다.
 * 이 PR: db_timestamp_to_string_core(…, error) 로 찍고 tp_make_char_conversion.
 * 바뀐 것: 목적 switch 가 풀린 쌍둥이 셀 + 문자열화 함수의 _core 교체. 죽은 err 분기가 남았다(+41줄).
 */
static TP_DOMAIN_STATUS
tp_value_convert_timestamp_to_char (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				    date_conversion_error *error)
{
  int err = NO_ERROR;
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;
  DB_DATA_STATUS data_stat = DATA_STATUS_OK;

  {
    int max_size = DATETIMETZ_BUF_SIZE;
    char *new_string;

    new_string = (char *) db_private_alloc (NULL, max_size);
    if (!new_string)
      {
	return DOMAIN_ERROR;
      }

    err = NO_ERROR;

    db_timestamp_to_string_core (new_string, max_size, (DB_TIMESTAMP *) db_get_timestamp (src), error);

    if (err != NO_ERROR)
      {
	return DOMAIN_ERROR;
      }

    if (db_value_precision (target) != TP_FLOATING_PRECISION_VALUE
	&& db_value_precision (target) < (int) strlen (new_string))
      {
	status = DOMAIN_OVERFLOW;
	db_private_free_and_init (NULL, new_string);
      }
    else
      {
	tp_make_char_conversion (desired_domain, new_string, target, &status, &data_stat);
      }
  }

  return err < 0 ? DOMAIN_ERROR : status;
}

/*
 * [리뷰] tp_value_convert_timestampltz_to_char — TIMESTAMPLTZ → CHAR 셀 — 세션 TZ_ID 를 만들어 TZ 표기를 찍는다.
 * develop: develop 에 없음 — 이 PR 이 신설. 날짜·시간 8개 소스가 묶인 한 case(9383) + 목적 switch 안이었다.
 * 이 PR: tz_create_session_tzid_for_timestamp_core 로 TZ_ID 를 얻고(실패 DOMAIN_ERROR) db_timestamptz_to_string_core
 * 로 찍는다.
 * 바뀐 것: 목적 switch 가 풀린 쌍둥이 셀 + _core 교체. err != NO_ERROR 로 빠질 때 new_string 을 해제하지 않는데
 * develop(object_domain.c:9447)도 해제하지 않았다 — 기존 누수를 그대로 옮겼다(+48줄).
 */
static TP_DOMAIN_STATUS
tp_value_convert_timestampltz_to_char (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				       date_conversion_error *error)
{
  int err = NO_ERROR;
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;
  DB_UTIME v_utime;
  DB_DATA_STATUS data_stat = DATA_STATUS_OK;
  TZ_ID ses_tz_id;

  {
    int max_size = DATETIMETZ_BUF_SIZE;
    char *new_string;

    new_string = (char *) db_private_alloc (NULL, max_size);
    if (!new_string)
      {
	return DOMAIN_ERROR;
      }

    err = NO_ERROR;

    v_utime = *db_get_timestamp (src);
    err = tz_create_session_tzid_for_timestamp_core (&v_utime, &ses_tz_id, error);
    if (err == NO_ERROR)
      {
	db_timestamptz_to_string_core (new_string, max_size, &v_utime, &ses_tz_id, error);
      }

    if (err != NO_ERROR)
      {
	return DOMAIN_ERROR;
      }

    if (db_value_precision (target) != TP_FLOATING_PRECISION_VALUE
	&& db_value_precision (target) < (int) strlen (new_string))
      {
	status = DOMAIN_OVERFLOW;
	db_private_free_and_init (NULL, new_string);
      }
    else
      {
	tp_make_char_conversion (desired_domain, new_string, target, &status, &data_stat);
      }
  }

  return err < 0 ? DOMAIN_ERROR : status;
}

/*
 * [리뷰] tp_value_convert_timestamptz_to_char — TIMESTAMPTZ → CHAR 셀 — 값의 TZ_ID 로 TZ 표기를 찍는다.
 * develop: develop 에 없음 — 이 PR 이 신설. 날짜·시간 8개 소스가 묶인 한 case(9383) + 목적 switch 안이었다.
 * 이 PR: db_timestamptz_to_string_core(…, &v_timestamptz.tz_id, error) 로 찍는다.
 * 바뀐 것: 목적 switch 가 풀린 쌍둥이 셀 + _core 교체, 죽은 err 분기(+44줄).
 */
static TP_DOMAIN_STATUS
tp_value_convert_timestamptz_to_char (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				      date_conversion_error *error)
{
  int err = NO_ERROR;
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;
  DB_TIMESTAMPTZ v_timestamptz;
  DB_DATA_STATUS data_stat = DATA_STATUS_OK;

  {
    int max_size = DATETIMETZ_BUF_SIZE;
    char *new_string;

    new_string = (char *) db_private_alloc (NULL, max_size);
    if (!new_string)
      {
	return DOMAIN_ERROR;
      }

    err = NO_ERROR;

    v_timestamptz = *db_get_timestamptz (src);
    db_timestamptz_to_string_core (new_string, max_size, &v_timestamptz.timestamp, &v_timestamptz.tz_id,
				   error);

    if (err != NO_ERROR)
      {
	return DOMAIN_ERROR;
      }

    if (db_value_precision (target) != TP_FLOATING_PRECISION_VALUE
	&& db_value_precision (target) < (int) strlen (new_string))
      {
	status = DOMAIN_OVERFLOW;
	db_private_free_and_init (NULL, new_string);
      }
    else
      {
	tp_make_char_conversion (desired_domain, new_string, target, &status, &data_stat);
      }
  }

  return err < 0 ? DOMAIN_ERROR : status;
}

/*
 * [리뷰] tp_value_convert_datetime_to_char — DATETIME → CHAR 셀.
 * develop: develop 에 없음 — 이 PR 이 신설. 날짜·시간 8개 소스가 묶인 한 case(9383) + 목적 switch 안이었다.
 * 이 PR: db_datetime_to_string 으로 찍고 tp_make_char_conversion.
 * 바뀐 것: 목적 switch 가 풀린 쌍둥이 셀, 죽은 err 분기(+41줄).
 */
static TP_DOMAIN_STATUS
tp_value_convert_datetime_to_char (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				   date_conversion_error *error)
{
  int err = NO_ERROR;
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;
  DB_DATA_STATUS data_stat = DATA_STATUS_OK;

  {
    int max_size = DATETIMETZ_BUF_SIZE;
    char *new_string;

    new_string = (char *) db_private_alloc (NULL, max_size);
    if (!new_string)
      {
	return DOMAIN_ERROR;
      }

    err = NO_ERROR;

    db_datetime_to_string (new_string, max_size, (DB_DATETIME *) db_get_datetime (src));

    if (err != NO_ERROR)
      {
	return DOMAIN_ERROR;
      }

    if (db_value_precision (target) != TP_FLOATING_PRECISION_VALUE
	&& db_value_precision (target) < (int) strlen (new_string))
      {
	status = DOMAIN_OVERFLOW;
	db_private_free_and_init (NULL, new_string);
      }
    else
      {
	tp_make_char_conversion (desired_domain, new_string, target, &status, &data_stat);
      }
  }

  return err < 0 ? DOMAIN_ERROR : status;
}

/*
 * [리뷰] tp_value_convert_datetimeltz_to_char — DATETIMELTZ → CHAR 셀 — 세션 TZ_ID 를 만들어 TZ 표기를 찍는다.
 * develop: develop 에 없음 — 이 PR 이 신설. 날짜·시간 8개 소스가 묶인 한 case(9383) + 목적 switch 안이었다.
 * 이 PR: tz_create_session_tzid_for_datetime_core(…, true, …) 뒤 db_datetimetz_to_string_core.
 * 바뀐 것: 목적 switch 가 풀린 쌍둥이 셀 + _core 교체. 같은 자리의 new_string 누수도 develop 그대로다(+48줄).
 */
static TP_DOMAIN_STATUS
tp_value_convert_datetimeltz_to_char (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				      date_conversion_error *error)
{
  int err = NO_ERROR;
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;
  DB_DATETIME v_datetime;
  DB_DATA_STATUS data_stat = DATA_STATUS_OK;
  TZ_ID ses_tz_id;

  {
    int max_size = DATETIMETZ_BUF_SIZE;
    char *new_string;

    new_string = (char *) db_private_alloc (NULL, max_size);
    if (!new_string)
      {
	return DOMAIN_ERROR;
      }

    err = NO_ERROR;

    v_datetime = *db_get_datetime (src);
    err = tz_create_session_tzid_for_datetime_core (&v_datetime, true, &ses_tz_id, error);
    if (err == NO_ERROR)
      {
	db_datetimetz_to_string_core (new_string, max_size, &v_datetime, &ses_tz_id, error);
      }

    if (err != NO_ERROR)
      {
	return DOMAIN_ERROR;
      }

    if (db_value_precision (target) != TP_FLOATING_PRECISION_VALUE
	&& db_value_precision (target) < (int) strlen (new_string))
      {
	status = DOMAIN_OVERFLOW;
	db_private_free_and_init (NULL, new_string);
      }
    else
      {
	tp_make_char_conversion (desired_domain, new_string, target, &status, &data_stat);
      }
  }

  return err < 0 ? DOMAIN_ERROR : status;
}

/*
 * [리뷰] tp_value_convert_datetimetz_to_char — DATETIMETZ → CHAR 셀.
 * develop: develop 에 없음 — 이 PR 이 신설. 날짜·시간 8개 소스가 묶인 한 case(9383) + 목적 switch 안이었다.
 * 이 PR: db_datetimetz_to_string_core(…, &v_datetimetz.tz_id, error).
 * 바뀐 것: 목적 switch 가 풀린 쌍둥이 셀 + _core 교체, 죽은 err 분기(+43줄).
 */
static TP_DOMAIN_STATUS
tp_value_convert_datetimetz_to_char (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				     date_conversion_error *error)
{
  int err = NO_ERROR;
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;
  DB_DATETIMETZ v_datetimetz;
  DB_DATA_STATUS data_stat = DATA_STATUS_OK;

  {
    int max_size = DATETIMETZ_BUF_SIZE;
    char *new_string;

    new_string = (char *) db_private_alloc (NULL, max_size);
    if (!new_string)
      {
	return DOMAIN_ERROR;
      }

    err = NO_ERROR;

    v_datetimetz = *db_get_datetimetz (src);
    db_datetimetz_to_string_core (new_string, max_size, &v_datetimetz.datetime, &v_datetimetz.tz_id, error);

    if (err != NO_ERROR)
      {
	return DOMAIN_ERROR;
      }

    if (db_value_precision (target) != TP_FLOATING_PRECISION_VALUE
	&& db_value_precision (target) < (int) strlen (new_string))
      {
	status = DOMAIN_OVERFLOW;
	db_private_free_and_init (NULL, new_string);
      }
    else
      {
	tp_make_char_conversion (desired_domain, new_string, target, &status, &data_stat);
      }
  }

  return err < 0 ? DOMAIN_ERROR : status;
}

/*
 * [리뷰] tp_value_convert_enumeration_to_char — ENUM → CHAR 셀 — ENUM 이름 문자열을 고정 길이 CHAR 도메인으로 옮긴다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop VARCHAR/CHAR case 의 ENUMERATION 갈래(object_domain.c:9212)로
 * tp_value_cast_internal 재귀였다.
 * 이 PR: tp_enumeration_to_varchar 로 VARCHAR 뷰를 만들고 tp_value_convert_char_to_varchar(= 서로 다른 CHAR 계열용 셀)를 부른다 —
 * 뷰는 VARCHAR, 목적은 CHAR 이라 길이 보정이 필요하기 때문이다.
 * 바뀐 것: 재귀 → 직접 호출(+21줄). 같은 자리의 VARCHAR 판이 varchar_to_varchar(동일 타입용)를 부르는 것과 짝이 맞는다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_enumeration_to_char (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				      date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;

  {
    DB_VALUE varchar_val;

    if (tp_enumeration_to_varchar (src, &varchar_val) != NO_ERROR)
      {
	status = DOMAIN_ERROR;
      }
    else
      {
	status = tp_value_convert_char_to_varchar (&varchar_val, target, desired_domain, error);
      }
  }

  return status;
}

/*
 * [리뷰] tp_value_convert_bit_to_char — BIT·VARBIT → CHAR 셀 — 비트열을 16진 문자열로 찍는다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop VARCHAR/CHAR case 의 `case DB_TYPE_BIT: case
 * DB_TYPE_VARBIT:`(object_domain.c:9465)였다.
 * 이 PR: bfmt_print(BIT_STRING_HEX) 후 성공이면 precision 검사 → tp_make_char_conversion, -1 이면 DOMAIN_OVERFLOW, 그 밖은
 * DOMAIN_ERROR.
 * 바뀐 것: 목적 switch 가 풀려 VARCHAR 판과 한 줄만 다른 쌍둥이 셀이 됐다(+49줄).
 */
static TP_DOMAIN_STATUS
tp_value_convert_bit_to_char (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
			      date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;
  DB_DATA_STATUS data_stat = DATA_STATUS_OK;

  {
    int max_size;
    char *new_string;
    int convert_error;

    max_size = ((db_get_string_length (src) + 3) / 4) + 1;
    new_string = (char *) db_private_alloc (NULL, max_size);
    if (!new_string)
      {
	return DOMAIN_ERROR;
      }

    convert_error = bfmt_print (1 /* BIT_STRING_HEX */, src,
				new_string, max_size);

    if (convert_error == NO_ERROR)
      {
	if (db_value_precision (target) != TP_FLOATING_PRECISION_VALUE
	    && (db_value_precision (target) < (int) strlen (new_string)))
	  {
	    status = DOMAIN_OVERFLOW;
	    db_private_free_and_init (NULL, new_string);
	  }
	else
	  {
	    tp_make_char_conversion (desired_domain, new_string, target, &status, &data_stat);
	  }
      }
    else if (convert_error == -1)
      {
	status = DOMAIN_OVERFLOW;
	db_private_free_and_init (NULL, new_string);
      }
    else
      {
	status = DOMAIN_ERROR;
	db_private_free_and_init (NULL, new_string);
      }
  }

  return status;
}

/*
 * [리뷰] tp_value_convert_clob_to_char — CLOB → CHAR 셀 — LOB 내용을 목적 도메인 코드셋으로 읽어 CHAR 에 담는다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop VARCHAR/CHAR case 의 CLOB 갈래로, db_clob_to_char 결과를
 * tp_value_cast_internal 로 재귀 캐스트하고 그 상태를 int err 에 덮어써 버렸다.
 * 이 PR: db_clob_to_char 뒤 tp_value_convert_char_to_varchar 를 부르고, 성공·잘림이면 그대로, 실패면 target 을 NULL 로 만들고
 * COMPATIBLE 로 흡수한다.
 * 바뀐 것: 재귀 → 직접 호출(+36줄). develop 의 '실패해도 성공+NULL' 을 주석과 함께 재현했다. src==dest 인 CLOB→CHAR 는 호출자
 * tp_value_cast_internal(object_domain.c:5863~)이 따로 다룬다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_clob_to_char (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
			       date_conversion_error *error)
{
  int err = NO_ERROR;
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;

  {
    DB_VALUE tmpval;
    DB_VALUE cs;

    db_make_null (&tmpval);
    /* convert directly from CLOB into charset of desired domain string */
    db_make_int (&cs, desired_domain->codeset);
    err = db_clob_to_char (src, &cs, &tmpval);
    if (err == NO_ERROR)
      {
	TP_DOMAIN_STATUS nested_status =
		tp_value_convert_char_to_varchar (&tmpval, target, desired_domain, error);
	if (nested_status == DOMAIN_COMPATIBLE || nested_status == DOMAIN_TRUNCATED)
	  {
	    status = nested_status;
	  }
	else
	  {
	    /* The old outer LOB cast returned success with a NULL result. */
	    pr_clear_value (target);
	    db_make_null (target);
	  }
      }

    pr_clear_value (&tmpval);
  }

  return err < 0 ? DOMAIN_ERROR : status;
}

/*
 * [리뷰] tp_value_convert_json_to_char — JSON → CHAR 셀 — 문서의 원문을 그대로 CHAR 에 담는다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop VARCHAR/CHAR case 의 `case DB_TYPE_JSON:` 였고 목적 구분은
 * make_desired_string_db_value 안이었다.
 * 이 PR: db_json_get_raw_json_body_from_document 버퍼를 precision 과 비교해 넘치면 해제 후 DOMAIN_OVERFLOW, 아니면
 * tp_make_char_conversion + need_clear.
 * 바뀐 것: 목적 타입 분기가 풀려 VARCHAR 판과 한 줄만 다른 쌍둥이 셀이 됐다(+28줄).
 */
static TP_DOMAIN_STATUS
tp_value_convert_json_to_char (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
			       date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;
  DB_DATA_STATUS data_stat = DATA_STATUS_OK;

  {
    char *json_str;
    int len;

    json_str = db_json_get_raw_json_body_from_document (db_get_json_document (src));
    len = strlen (json_str);

    if (db_value_precision (target) != TP_FLOATING_PRECISION_VALUE && db_value_precision (target) < len)
      {
	status = DOMAIN_OVERFLOW;
	db_private_free_and_init (NULL, json_str);
      }
    else
      {
	tp_make_char_conversion (desired_domain, json_str, target, &status, &data_stat);
	target->need_clear = true;
      }
  }

  return status;
}

/*
 * [리뷰] tp_value_convert_char_to_blob — CHAR·VARCHAR → BLOB 셀 — 문자열을 LOB 파일로 써서 LOB 핸들을 만든다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop `case DB_TYPE_BLOB:`(object_domain.c:9556) 안 CHAR/VARCHAR 갈래로
 * `err = db_char_to_blob (src, target);` 한 줄이었다.
 * 이 PR: db_char_to_blob 의 반환값을 받아 `err < 0 ? DOMAIN_ERROR : DOMAIN_COMPATIBLE`.
 * 바뀐 것: 한 줄 갈래를 셀 함수로 승격(+11줄). develop 이 함수 끝 공통 처리에서 하던 `err < 0` 판정을 셀 안으로 가져왔다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_char_to_blob (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
			       date_conversion_error *error)
{
  int err = NO_ERROR;
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;

  err = db_char_to_blob (src, target);

  return err < 0 ? DOMAIN_ERROR : status;
}

/*
 * [리뷰] tp_value_convert_enumeration_to_blob — ENUM → BLOB 셀.
 * develop: develop 에 없음 — 이 PR 이 신설. develop BLOB case(9556)의 ENUMERATION 갈래로 tp_value_cast_internal 재귀였다.
 * 이 PR: tp_enumeration_to_varchar 뒤 tp_value_convert_char_to_blob 직접 호출.
 * 바뀐 것: 재귀 → 직접 호출(+18줄).
 */
static TP_DOMAIN_STATUS
tp_value_convert_enumeration_to_blob (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				      date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;

  {
    DB_VALUE varchar_val;

    if (tp_enumeration_to_varchar (src, &varchar_val) != NO_ERROR)
      {
	return DOMAIN_ERROR;
      }
    status = tp_value_convert_char_to_blob (&varchar_val, target, desired_domain, error);
  }

  return status;
}

/*
 * [리뷰] tp_value_convert_bit_to_blob — BIT·VARBIT → BLOB 셀 — 비트열을 LOB 파일로 쓴다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop BLOB case(9556)의 BIT/VARBIT 갈래로 `err = db_bit_to_blob (src,
 * target);` 한 줄이었다.
 * 이 PR: db_bit_to_blob 의 반환값으로 DOMAIN_ERROR/DOMAIN_COMPATIBLE 을 정한다.
 * 바뀐 것: 한 줄 갈래를 셀로 승격(+11줄).
 */
static TP_DOMAIN_STATUS
tp_value_convert_bit_to_blob (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
			      date_conversion_error *error)
{
  int err = NO_ERROR;
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;

  err = db_bit_to_blob (src, target);

  return err < 0 ? DOMAIN_ERROR : status;
}

/*
 * [리뷰] tp_value_convert_char_to_clob — CHAR·VARCHAR → CLOB 셀.
 * develop: develop 에 없음 — 이 PR 이 신설. develop `case DB_TYPE_CLOB:`(object_domain.c:9589) 안 CHAR/VARCHAR 갈래로
 * `err = db_char_to_clob (src, target);` 한 줄이었다.
 * 이 PR: db_char_to_clob 의 반환값으로 상태를 정한다.
 * 바뀐 것: 한 줄 갈래를 셀로 승격(+11줄).
 */
static TP_DOMAIN_STATUS
tp_value_convert_char_to_clob (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
			       date_conversion_error *error)
{
  int err = NO_ERROR;
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;

  err = db_char_to_clob (src, target);

  return err < 0 ? DOMAIN_ERROR : status;
}

/*
 * [리뷰] tp_value_convert_enumeration_to_clob — ENUM → CLOB 셀.
 * develop: develop 에 없음 — 이 PR 이 신설. develop CLOB case(9589)의 ENUMERATION 갈래로 tp_value_cast_internal 재귀였다.
 * 이 PR: tp_enumeration_to_varchar 뒤 tp_value_convert_char_to_clob 직접 호출.
 * 바뀐 것: 재귀 → 직접 호출(+18줄), 끝에 도달 불가 return.
 */
static TP_DOMAIN_STATUS
tp_value_convert_enumeration_to_clob (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				      date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;

  {
    DB_VALUE varchar_val;
    if (tp_enumeration_to_varchar (src, &varchar_val) != NO_ERROR)
      {
	return DOMAIN_ERROR;
      }
    status = tp_value_convert_char_to_clob (&varchar_val, target, desired_domain, error);
    return status;
  }

  return status;
}

/*
 * [리뷰] tp_value_convert_short_to_enumeration — SHORT → ENUM 셀 — 정수를 ENUM 요소 인덱스로 읽는다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop `case DB_TYPE_ENUMERATION:`(object_domain.c:9617) 블록 안 소스 switch
 * 의 한 갈래였고, 공유 지역 변수 val_idx·val_str·conv_val·exit 에 결과를 남긴 뒤 같은 블록의 공통 꼬리(9824~9937)로 떨어졌다.
 * 이 PR: 지역 변수를 함수 안에서 선언하고, src 가 NULL 이면 target 을 NULL 로 만든 뒤 끝낸다. val_idx = (unsigned short)
 * db_get_short(src) 만 채워 tp_finish_enumeration_conversion 에 넘긴다.
 * 바뀐 것: switch 갈래를 셀로 분리하고 블록 지역 변수 공유를 인자 전달로 바꿨다. 범위 검사가 없는 것도 develop 과 같다(short 는 이미 2바이트). exit 는 늘 false
 * 로 넘어가고 끝에 도달 불가 return 이 남았다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_short_to_enumeration (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				       date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;

  {
    unsigned short val_idx = 0;
    int val_str_size = 0;
    const char *val_str = NULL;
    bool exit = false;
    DB_VALUE conv_val;

    db_make_null (&conv_val);

    if (src->domain.general_info.is_null)
      {
	db_make_null (target);
	return DOMAIN_COMPATIBLE;
      }

    val_idx = (unsigned short) db_get_short (src);

    return tp_finish_enumeration_conversion (target, desired_domain, conv_val, val_idx, val_str, val_str_size,
	   status, exit);
  }
  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_integer_to_enumeration — INTEGER → ENUM 셀 — 정수를 ENUM 인덱스로 읽는다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop ENUM case(9617) 안 소스 switch 의 INTEGER 갈래로, 공통 꼬리와 지역 변수를 공유했다.
 * 이 PR: OR_CHECK_USHRT_OVERFLOW(db_get_int (src)) 면 DOMAIN_INCOMPATIBLE, 아니면 val_idx 로 캐스트해
 * tp_finish_enumeration_conversion 에 넘긴다.
 * 바뀐 것: switch 갈래를 셀로 분리, 지역 변수 공유를 인자 전달로 교체. 공통 꼬리는 tp_finish_enumeration_conversion 하나로 모였다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_integer_to_enumeration (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
    date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;

  {
    unsigned short val_idx = 0;
    int val_str_size = 0;
    const char *val_str = NULL;
    bool exit = false;
    DB_VALUE conv_val;

    db_make_null (&conv_val);

    if (src->domain.general_info.is_null)
      {
	db_make_null (target);
	return status;
      }

    if (OR_CHECK_USHRT_OVERFLOW (db_get_int (src)))
      {
	status = DOMAIN_INCOMPATIBLE;
      }
    else
      {
	val_idx = (unsigned short) db_get_int (src);
      }

    return tp_finish_enumeration_conversion (target, desired_domain, conv_val, val_idx, val_str, val_str_size,
	   status, exit);
  }
  return status;
}

/*
 * [리뷰] tp_value_convert_bigint_to_enumeration — BIGINT → ENUM 셀 — 정수를 ENUM 인덱스로 읽는다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop ENUM case(9617) 안 소스 switch 의 BIGINT 갈래였다.
 * 이 PR: OR_CHECK_USHRT_OVERFLOW(db_get_bigint (src)) 검사 후 val_idx 로 캐스트해 꼬리 함수에 넘긴다.
 * 바뀐 것: switch 갈래를 셀로 분리, 공통 꼬리는 tp_finish_enumeration_conversion 으로 모였다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_bigint_to_enumeration (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
					date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;

  {
    unsigned short val_idx = 0;
    int val_str_size = 0;
    const char *val_str = NULL;
    bool exit = false;
    DB_VALUE conv_val;

    db_make_null (&conv_val);

    if (src->domain.general_info.is_null)
      {
	db_make_null (target);
	return status;
      }

    if (OR_CHECK_USHRT_OVERFLOW (db_get_bigint (src)))
      {
	status = DOMAIN_INCOMPATIBLE;
      }
    else
      {
	val_idx = (unsigned short) db_get_bigint (src);
      }

    return tp_finish_enumeration_conversion (target, desired_domain, conv_val, val_idx, val_str, val_str_size,
	   status, exit);
  }
  return status;
}

/*
 * [리뷰] tp_value_convert_float_to_enumeration — FLOAT → ENUM 셀 — 내림한 값을 ENUM 인덱스로 읽는다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop ENUM case(9617) 안 소스 switch 의 FLOAT 갈래였다.
 * 이 PR: OR_CHECK_USHRT_OVERFLOW(floor (db_get_float (src))) 검사 후 val_idx 로 캐스트한다(반올림이 아니라 floor 인 것도 develop 과
 * 같다).
 * 바뀐 것: switch 갈래를 셀로 분리, 공통 꼬리는 tp_finish_enumeration_conversion 으로 모였다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_float_to_enumeration (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				       date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;

  {
    unsigned short val_idx = 0;
    int val_str_size = 0;
    const char *val_str = NULL;
    bool exit = false;
    DB_VALUE conv_val;

    db_make_null (&conv_val);

    if (src->domain.general_info.is_null)
      {
	db_make_null (target);
	return status;
      }

    if (OR_CHECK_USHRT_OVERFLOW (floor (db_get_float (src))))
      {
	status = DOMAIN_INCOMPATIBLE;
      }
    else
      {
	val_idx = (unsigned short) floor (db_get_float (src));
      }

    return tp_finish_enumeration_conversion (target, desired_domain, conv_val, val_idx, val_str, val_str_size,
	   status, exit);
  }
  return status;
}

/*
 * [리뷰] tp_value_convert_double_to_enumeration — DOUBLE → ENUM 셀 — 내림한 값을 ENUM 인덱스로 읽는다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop ENUM case(9617) 안 소스 switch 의 DOUBLE 갈래였다.
 * 이 PR: OR_CHECK_USHRT_OVERFLOW(floor (db_get_double (src))) 검사 후 val_idx 로 캐스트한다.
 * 바뀐 것: switch 갈래를 셀로 분리, 공통 꼬리는 tp_finish_enumeration_conversion 으로 모였다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_double_to_enumeration (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
					date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;

  {
    unsigned short val_idx = 0;
    int val_str_size = 0;
    const char *val_str = NULL;
    bool exit = false;
    DB_VALUE conv_val;

    db_make_null (&conv_val);

    if (src->domain.general_info.is_null)
      {
	db_make_null (target);
	return status;
      }

    if (OR_CHECK_USHRT_OVERFLOW (floor (db_get_double (src))))
      {
	status = DOMAIN_INCOMPATIBLE;
      }
    else
      {
	val_idx = (unsigned short) floor (db_get_double (src));
      }

    return tp_finish_enumeration_conversion (target, desired_domain, conv_val, val_idx, val_str, val_str_size,
	   status, exit);
  }
  return status;
}

/*
 * [리뷰] tp_value_convert_monetary_to_enumeration — MONETARY → ENUM 셀 — 금액을 내림해 ENUM 인덱스로 읽는다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop ENUM case(9617) 안 소스 switch 의 MONETARY 갈래였다.
 * 이 PR: db_get_monetary(src)->amount 에 floor + OR_CHECK_USHRT_OVERFLOW 검사 후 val_idx 로 캐스트한다.
 * 바뀐 것: switch 갈래를 셀로 분리, 공통 꼬리는 tp_finish_enumeration_conversion 으로 모였다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_monetary_to_enumeration (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;
  const DB_MONETARY *v_money;

  {
    unsigned short val_idx = 0;
    int val_str_size = 0;
    const char *val_str = NULL;
    bool exit = false;
    DB_VALUE conv_val;

    db_make_null (&conv_val);

    if (src->domain.general_info.is_null)
      {
	db_make_null (target);
	return status;
      }

    v_money = db_get_monetary (src);
    if (OR_CHECK_USHRT_OVERFLOW (floor (v_money->amount)))
      {
	status = DOMAIN_INCOMPATIBLE;
      }
    else
      {
	val_idx = (unsigned short) floor (v_money->amount);
      }

    return tp_finish_enumeration_conversion (target, desired_domain, conv_val, val_idx, val_str, val_str_size,
	   status, exit);
  }
  return status;
}

/*
 * [리뷰] tp_value_convert_numeric_to_enumeration — NUMERIC → ENUM 셀 — NUMERIC 을 double 로 풀어 내림한 값을 인덱스로 읽는다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop ENUM case(9617) 안 소스 switch 의 NUMERIC 갈래(9684)였다.
 * 이 PR: numeric_coerce_num_to_double 로 바꾸고(실패 DOMAIN_ERROR) floor + OR_CHECK_USHRT_OVERFLOW 후 val_idx 로 캐스트해
 * 꼬리 함수에 넘긴다.
 * 바뀐 것: switch 갈래를 셀로 분리, 공통 꼬리 통합. err 변수가 남아 있지만 numeric_coerce_num_to_double 은 음수를 돌려주지 않아 `err < 0` 분기는 죽은
 * 코드다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_numeric_to_enumeration (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
    date_conversion_error *error)
{
  int err = NO_ERROR;
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;

  {
    unsigned short val_idx = 0;
    int val_str_size = 0;
    const char *val_str = NULL;
    bool exit = false;
    DB_VALUE conv_val;

    db_make_null (&conv_val);

    if (src->domain.general_info.is_null)
      {
	db_make_null (target);
	return err < 0 ? DOMAIN_ERROR : status;
      }

    {
      DB_VALUE val;

      db_make_double (&val, 0);
      err = numeric_coerce_num_to_double (src, db_get_numeric_scale (src, NULL), &val);
      if (err != NO_ERROR)
	{
	  status = DOMAIN_ERROR;
	}
      else
	{
	  if (OR_CHECK_USHRT_OVERFLOW (floor (db_get_double (&val))))
	    {
	      status = DOMAIN_INCOMPATIBLE;
	    }
	  else
	    {
	      val_idx = (unsigned short) floor (db_get_double (&val));
	    }
	}
    }

    return tp_finish_enumeration_conversion (target, desired_domain, conv_val, val_idx, val_str, val_str_size,
	   status, exit);
  }
  return err < 0 ? DOMAIN_ERROR : status;
}

/*
 * [리뷰] tp_value_convert_char_to_enumeration — CHAR → ENUM 셀 — 문자열을 ENUM 도메인의 코드셋으로 맞춘 뒤 요소 이름으로 찾는다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop ENUM case(9617) 안 소스 switch 에서 CHAR 와 VARCHAR 이 한 갈래(9736~9770)였고
 * 임시값 타입만 DB_VALUE_TYPE(src) 로 갈랐다.
 * 이 PR: 소스 코드셋이 목적과 다르면 CHAR 임시값(conv_val)으로 db_char_string_coerce 해 val_str 을 만들고(실패·잘림이면 DOMAIN_ERROR), 같으면
 * 소스 버퍼를 그대로 가리킨 뒤 꼬리 함수에 넘긴다. RAW_BYTES 목적일 때 precision 대신 byte size 로 잡는 예외도 유지한다.
 * 바뀐 것: CHAR/VARCHAR 한 갈래를 셀 둘로 펼치고 지역 변수 공유를 인자 전달로 바꿨다(+60줄). 변환 버퍼 conv_val 은 꼬리 함수가 재사용하거나 pr_clear_value
 * 로 정리한다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_char_to_enumeration (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				      date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;

  {
    unsigned short val_idx = 0;
    int val_str_size = 0;
    const char *val_str = NULL;
    bool exit = false;
    DB_VALUE conv_val;

    db_make_null (&conv_val);

    if (src->domain.general_info.is_null)
      {
	db_make_null (target);
	return status;
      }

    if (db_get_string_codeset (src) != TP_DOMAIN_CODESET (desired_domain))
      {
	DB_DATA_STATUS data_status = DATA_STATUS_OK;

	if (TP_DOMAIN_CODESET (desired_domain) == INTL_CODESET_RAW_BYTES)
	  {
	    /* avoid data truncation when converting to binary charset */
	    db_value_domain_init (&conv_val, DB_TYPE_CHAR, db_get_string_size (src), 0);
	  }
	else
	  {
	    db_value_domain_init (&conv_val, DB_TYPE_CHAR, DB_VALUE_PRECISION (src), 0);
	  }

	db_string_put_cs_and_collation (&conv_val, TP_DOMAIN_CODESET (desired_domain),
					TP_DOMAIN_COLLATION (desired_domain));

	if (db_char_string_coerce (src, &conv_val, &data_status) != NO_ERROR || data_status != DATA_STATUS_OK)
	  {
	    status = DOMAIN_ERROR;
	    pr_clear_value (&conv_val);
	  }
	else
	  {
	    val_str = db_get_string (&conv_val);
	    val_str_size = db_get_string_size (&conv_val);
	  }
      }
    else
      {
	val_str = db_get_string (src);
	val_str_size = db_get_string_size (src);
      }

    return tp_finish_enumeration_conversion (target, desired_domain, conv_val, val_idx, val_str, val_str_size,
	   status, exit);
  }
  return status;
}

/*
 * [리뷰] tp_value_convert_varchar_to_enumeration — VARCHAR → ENUM 셀 — char 판과 같되 임시값을 VARCHAR 로 만든다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop ENUM case(9617)에서 CHAR 와 VARCHAR 이 한 갈래였고 임시값 타입만 original_type
 * 으로 갈랐다.
 * 이 PR: db_value_domain_init 의 타입이 DB_TYPE_VARCHAR 인 것 외에는 char 판과 같다.
 * 바뀐 것: 한 갈래를 셀 둘로 펼쳤다(+60줄). 지역 변수 공유가 인자 전달로 바뀌고 공통 꼬리는 tp_finish_enumeration_conversion 으로 모였다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_varchar_to_enumeration (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
    date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;

  {
    unsigned short val_idx = 0;
    int val_str_size = 0;
    const char *val_str = NULL;
    bool exit = false;
    DB_VALUE conv_val;

    db_make_null (&conv_val);

    if (src->domain.general_info.is_null)
      {
	db_make_null (target);
	return status;
      }

    if (db_get_string_codeset (src) != TP_DOMAIN_CODESET (desired_domain))
      {
	DB_DATA_STATUS data_status = DATA_STATUS_OK;

	if (TP_DOMAIN_CODESET (desired_domain) == INTL_CODESET_RAW_BYTES)
	  {
	    /* avoid data truncation when converting to binary charset */
	    db_value_domain_init (&conv_val, DB_TYPE_VARCHAR, db_get_string_size (src), 0);
	  }
	else
	  {
	    db_value_domain_init (&conv_val, DB_TYPE_VARCHAR, DB_VALUE_PRECISION (src), 0);
	  }

	db_string_put_cs_and_collation (&conv_val, TP_DOMAIN_CODESET (desired_domain),
					TP_DOMAIN_COLLATION (desired_domain));

	if (db_char_string_coerce (src, &conv_val, &data_status) != NO_ERROR || data_status != DATA_STATUS_OK)
	  {
	    status = DOMAIN_ERROR;
	    pr_clear_value (&conv_val);
	  }
	else
	  {
	    val_str = db_get_string (&conv_val);
	    val_str_size = db_get_string_size (&conv_val);
	  }
      }
    else
      {
	val_str = db_get_string (src);
	val_str_size = db_get_string_size (src);
      }

    return tp_finish_enumeration_conversion (target, desired_domain, conv_val, val_idx, val_str, val_str_size,
	   status, exit);
  }
  return status;
}

/*
 * [리뷰] tp_value_convert_date_to_enumeration — DATE → ENUM 셀 — 값을 기본 STRING 도메인 문자열로 만든 뒤 그 문자열과 같은 ENUM 요소를
 * 찾는다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop ENUM case(object_domain.c:9617) 안 소스 switch 에서
 * TIMESTAMP·TIMESTAMPLTZ·TIMESTAMPTZ·DATETIME·DATETIMETZ·DATETIMELTZ·DATE·TIME·BIT·VARBIT·BLOB·CLOB 12개가 한
 * 갈래(9713~9735)로 묶여 tp_value_cast_internal(src, &conv_val, tp_domain_resolve_default (DB_TYPE_STRING), …) 로 재귀
 * 캐스트했다.
 * 이 PR: conv_val 을 기본 STRING 도메인의 VARCHAR 로 초기화하고 tp_value_convert_date_to_varchar 로 문자열화한 뒤, 성공하면
 * val_str/val_str_size 를 꺼내 tp_finish_enumeration_conversion 에 넘긴다.
 * 바뀐 것: 묶여 있던 12갈래가 소스별 셀로 펼쳐졌고, 재귀 캐스트가 '기본 STRING 도메인으로 conv_val 직접 초기화 + 해당 _to_varchar 셀 직접 호출' 로 바뀌었다 —
 * tp_value_convert 가 하는 초기화를 손으로 편 꼴이다(+41줄).
 */
static TP_DOMAIN_STATUS
tp_value_convert_date_to_enumeration (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				      date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;

  {
    unsigned short val_idx = 0;
    int val_str_size = 0;
    const char *val_str = NULL;
    bool exit = false;
    DB_VALUE conv_val;

    db_make_null (&conv_val);

    if (src->domain.general_info.is_null)
      {
	db_make_null (target);
	return DOMAIN_COMPATIBLE;
      }

    {
      const TP_DOMAIN *string_domain = tp_domain_resolve_default (DB_TYPE_STRING);
      db_value_domain_init (&conv_val, DB_TYPE_VARCHAR, string_domain->precision, string_domain->scale);
      db_string_put_cs_and_collation (&conv_val, TP_DOMAIN_CODESET (string_domain),
				      TP_DOMAIN_COLLATION (string_domain));
      status =
	      tp_value_convert_date_to_varchar (src, &conv_val, tp_domain_resolve_default (DB_TYPE_STRING),
		  error);
      if (status == DOMAIN_COMPATIBLE)
	{
	  val_str = db_get_string (&conv_val);
	  val_str_size = db_get_string_size (&conv_val);
	}
    }

    return tp_finish_enumeration_conversion (target, desired_domain, conv_val, val_idx, val_str, val_str_size,
	   status, exit);
  }
  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_time_to_enumeration — TIME → ENUM 셀 — 문자열로 만든 뒤 ENUM 요소를 찾는다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop ENUM case(9617)의 12개 소스 묶음 갈래(9713)로, 기본 STRING 도메인으로 재귀 캐스트했다.
 * 이 PR: conv_val 을 기본 STRING 도메인 VARCHAR 로 초기화하고 tp_value_convert_time_to_varchar 로 문자열화한 뒤 꼬리 함수에 넘긴다.
 * 바뀐 것: 12갈래를 소스별 셀로 펼치고 재귀 캐스트를 셀 직접 호출로 바꿨다(+41줄). 끝에 도달 불가 return 이 남았다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_time_to_enumeration (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				      date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;

  {
    unsigned short val_idx = 0;
    int val_str_size = 0;
    const char *val_str = NULL;
    bool exit = false;
    DB_VALUE conv_val;

    db_make_null (&conv_val);

    if (src->domain.general_info.is_null)
      {
	db_make_null (target);
	return DOMAIN_COMPATIBLE;
      }

    {
      const TP_DOMAIN *string_domain = tp_domain_resolve_default (DB_TYPE_STRING);
      db_value_domain_init (&conv_val, DB_TYPE_VARCHAR, string_domain->precision, string_domain->scale);
      db_string_put_cs_and_collation (&conv_val, TP_DOMAIN_CODESET (string_domain),
				      TP_DOMAIN_COLLATION (string_domain));
      status =
	      tp_value_convert_time_to_varchar (src, &conv_val, tp_domain_resolve_default (DB_TYPE_STRING),
		  error);
      if (status == DOMAIN_COMPATIBLE)
	{
	  val_str = db_get_string (&conv_val);
	  val_str_size = db_get_string_size (&conv_val);
	}
    }

    return tp_finish_enumeration_conversion (target, desired_domain, conv_val, val_idx, val_str, val_str_size,
	   status, exit);
  }
  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_timestamp_to_enumeration — TIMESTAMP → ENUM 셀 — 문자열로 만든 뒤 ENUM 요소를 찾는다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop ENUM case(9617)의 12개 소스 묶음 갈래(9713)였다.
 * 이 PR: conv_val 을 기본 STRING VARCHAR 로 초기화하고 tp_value_convert_timestamp_to_varchar 로 문자열화한 뒤 꼬리 함수에 넘긴다.
 * 바뀐 것: 12갈래를 셀로 펼치고 재귀 캐스트를 직접 호출로 바꿨다(+41줄).
 */
static TP_DOMAIN_STATUS
tp_value_convert_timestamp_to_enumeration (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;

  {
    unsigned short val_idx = 0;
    int val_str_size = 0;
    const char *val_str = NULL;
    bool exit = false;
    DB_VALUE conv_val;

    db_make_null (&conv_val);

    if (src->domain.general_info.is_null)
      {
	db_make_null (target);
	return DOMAIN_COMPATIBLE;
      }

    {
      const TP_DOMAIN *string_domain = tp_domain_resolve_default (DB_TYPE_STRING);
      db_value_domain_init (&conv_val, DB_TYPE_VARCHAR, string_domain->precision, string_domain->scale);
      db_string_put_cs_and_collation (&conv_val, TP_DOMAIN_CODESET (string_domain),
				      TP_DOMAIN_COLLATION (string_domain));
      status =
	      tp_value_convert_timestamp_to_varchar (src, &conv_val, tp_domain_resolve_default (DB_TYPE_STRING),
		  error);
      if (status == DOMAIN_COMPATIBLE)
	{
	  val_str = db_get_string (&conv_val);
	  val_str_size = db_get_string_size (&conv_val);
	}
    }

    return tp_finish_enumeration_conversion (target, desired_domain, conv_val, val_idx, val_str, val_str_size,
	   status, exit);
  }
  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_timestampltz_to_enumeration — TIMESTAMPLTZ → ENUM 셀 — 세션 TZ 표기 문자열로 만든 뒤 ENUM 요소를 찾는다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop ENUM case(9617)의 12개 소스 묶음 갈래(9713)였다.
 * 이 PR: conv_val 을 기본 STRING VARCHAR 로 초기화하고 tp_value_convert_timestampltz_to_varchar 로 문자열화한 뒤 꼬리 함수에 넘긴다.
 * 바뀐 것: 12갈래를 셀로 펼치고 재귀 캐스트를 직접 호출로 바꿨다(+41줄).
 */
static TP_DOMAIN_STATUS
tp_value_convert_timestampltz_to_enumeration (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;

  {
    unsigned short val_idx = 0;
    int val_str_size = 0;
    const char *val_str = NULL;
    bool exit = false;
    DB_VALUE conv_val;

    db_make_null (&conv_val);

    if (src->domain.general_info.is_null)
      {
	db_make_null (target);
	return DOMAIN_COMPATIBLE;
      }

    {
      const TP_DOMAIN *string_domain = tp_domain_resolve_default (DB_TYPE_STRING);
      db_value_domain_init (&conv_val, DB_TYPE_VARCHAR, string_domain->precision, string_domain->scale);
      db_string_put_cs_and_collation (&conv_val, TP_DOMAIN_CODESET (string_domain),
				      TP_DOMAIN_COLLATION (string_domain));
      status =
	      tp_value_convert_timestampltz_to_varchar (src, &conv_val,
		  tp_domain_resolve_default (DB_TYPE_STRING), error);
      if (status == DOMAIN_COMPATIBLE)
	{
	  val_str = db_get_string (&conv_val);
	  val_str_size = db_get_string_size (&conv_val);
	}
    }

    return tp_finish_enumeration_conversion (target, desired_domain, conv_val, val_idx, val_str, val_str_size,
	   status, exit);
  }
  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_timestamptz_to_enumeration — TIMESTAMPTZ → ENUM 셀 — TZ 표기 문자열로 만든 뒤 ENUM 요소를 찾는다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop ENUM case(9617)의 12개 소스 묶음 갈래(9713)였다.
 * 이 PR: conv_val 을 기본 STRING VARCHAR 로 초기화하고 tp_value_convert_timestamptz_to_varchar 로 문자열화한 뒤 꼬리 함수에 넘긴다.
 * 바뀐 것: 12갈래를 셀로 펼치고 재귀 캐스트를 직접 호출로 바꿨다(+41줄).
 */
static TP_DOMAIN_STATUS
tp_value_convert_timestamptz_to_enumeration (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;

  {
    unsigned short val_idx = 0;
    int val_str_size = 0;
    const char *val_str = NULL;
    bool exit = false;
    DB_VALUE conv_val;

    db_make_null (&conv_val);

    if (src->domain.general_info.is_null)
      {
	db_make_null (target);
	return DOMAIN_COMPATIBLE;
      }

    {
      const TP_DOMAIN *string_domain = tp_domain_resolve_default (DB_TYPE_STRING);
      db_value_domain_init (&conv_val, DB_TYPE_VARCHAR, string_domain->precision, string_domain->scale);
      db_string_put_cs_and_collation (&conv_val, TP_DOMAIN_CODESET (string_domain),
				      TP_DOMAIN_COLLATION (string_domain));
      status =
	      tp_value_convert_timestamptz_to_varchar (src, &conv_val,
		  tp_domain_resolve_default (DB_TYPE_STRING), error);
      if (status == DOMAIN_COMPATIBLE)
	{
	  val_str = db_get_string (&conv_val);
	  val_str_size = db_get_string_size (&conv_val);
	}
    }

    return tp_finish_enumeration_conversion (target, desired_domain, conv_val, val_idx, val_str, val_str_size,
	   status, exit);
  }
  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_datetime_to_enumeration — DATETIME → ENUM 셀 — 문자열로 만든 뒤 ENUM 요소를 찾는다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop ENUM case(9617)의 12개 소스 묶음 갈래(9713)였다.
 * 이 PR: conv_val 을 기본 STRING VARCHAR 로 초기화하고 tp_value_convert_datetime_to_varchar 로 문자열화한 뒤 꼬리 함수에 넘긴다.
 * 바뀐 것: 12갈래를 셀로 펼치고 재귀 캐스트를 직접 호출로 바꿨다(+41줄).
 */
static TP_DOMAIN_STATUS
tp_value_convert_datetime_to_enumeration (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;

  {
    unsigned short val_idx = 0;
    int val_str_size = 0;
    const char *val_str = NULL;
    bool exit = false;
    DB_VALUE conv_val;

    db_make_null (&conv_val);

    if (src->domain.general_info.is_null)
      {
	db_make_null (target);
	return DOMAIN_COMPATIBLE;
      }

    {
      const TP_DOMAIN *string_domain = tp_domain_resolve_default (DB_TYPE_STRING);
      db_value_domain_init (&conv_val, DB_TYPE_VARCHAR, string_domain->precision, string_domain->scale);
      db_string_put_cs_and_collation (&conv_val, TP_DOMAIN_CODESET (string_domain),
				      TP_DOMAIN_COLLATION (string_domain));
      status =
	      tp_value_convert_datetime_to_varchar (src, &conv_val, tp_domain_resolve_default (DB_TYPE_STRING),
		  error);
      if (status == DOMAIN_COMPATIBLE)
	{
	  val_str = db_get_string (&conv_val);
	  val_str_size = db_get_string_size (&conv_val);
	}
    }

    return tp_finish_enumeration_conversion (target, desired_domain, conv_val, val_idx, val_str, val_str_size,
	   status, exit);
  }
  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_datetimeltz_to_enumeration — DATETIMELTZ → ENUM 셀 — 세션 TZ 표기 문자열로 만든 뒤 ENUM 요소를 찾는다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop ENUM case(9617)의 12개 소스 묶음 갈래(9713)였다.
 * 이 PR: conv_val 을 기본 STRING VARCHAR 로 초기화하고 tp_value_convert_datetimeltz_to_varchar 로 문자열화한 뒤 꼬리 함수에 넘긴다.
 * 바뀐 것: 12갈래를 셀로 펼치고 재귀 캐스트를 직접 호출로 바꿨다(+41줄).
 */
static TP_DOMAIN_STATUS
tp_value_convert_datetimeltz_to_enumeration (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;

  {
    unsigned short val_idx = 0;
    int val_str_size = 0;
    const char *val_str = NULL;
    bool exit = false;
    DB_VALUE conv_val;

    db_make_null (&conv_val);

    if (src->domain.general_info.is_null)
      {
	db_make_null (target);
	return DOMAIN_COMPATIBLE;
      }

    {
      const TP_DOMAIN *string_domain = tp_domain_resolve_default (DB_TYPE_STRING);
      db_value_domain_init (&conv_val, DB_TYPE_VARCHAR, string_domain->precision, string_domain->scale);
      db_string_put_cs_and_collation (&conv_val, TP_DOMAIN_CODESET (string_domain),
				      TP_DOMAIN_COLLATION (string_domain));
      status =
	      tp_value_convert_datetimeltz_to_varchar (src, &conv_val,
		  tp_domain_resolve_default (DB_TYPE_STRING), error);
      if (status == DOMAIN_COMPATIBLE)
	{
	  val_str = db_get_string (&conv_val);
	  val_str_size = db_get_string_size (&conv_val);
	}
    }

    return tp_finish_enumeration_conversion (target, desired_domain, conv_val, val_idx, val_str, val_str_size,
	   status, exit);
  }
  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_datetimetz_to_enumeration — DATETIMETZ → ENUM 셀 — TZ 표기 문자열로 만든 뒤 ENUM 요소를 찾는다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop ENUM case(9617)의 12개 소스 묶음 갈래(9713)였다.
 * 이 PR: conv_val 을 기본 STRING VARCHAR 로 초기화하고 tp_value_convert_datetimetz_to_varchar 로 문자열화한 뒤 꼬리 함수에 넘긴다.
 * 바뀐 것: 12갈래를 셀로 펼치고 재귀 캐스트를 직접 호출로 바꿨다(+41줄).
 */
static TP_DOMAIN_STATUS
tp_value_convert_datetimetz_to_enumeration (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;

  {
    unsigned short val_idx = 0;
    int val_str_size = 0;
    const char *val_str = NULL;
    bool exit = false;
    DB_VALUE conv_val;

    db_make_null (&conv_val);

    if (src->domain.general_info.is_null)
      {
	db_make_null (target);
	return DOMAIN_COMPATIBLE;
      }

    {
      const TP_DOMAIN *string_domain = tp_domain_resolve_default (DB_TYPE_STRING);
      db_value_domain_init (&conv_val, DB_TYPE_VARCHAR, string_domain->precision, string_domain->scale);
      db_string_put_cs_and_collation (&conv_val, TP_DOMAIN_CODESET (string_domain),
				      TP_DOMAIN_COLLATION (string_domain));
      status =
	      tp_value_convert_datetimetz_to_varchar (src, &conv_val, tp_domain_resolve_default (DB_TYPE_STRING),
		  error);
      if (status == DOMAIN_COMPATIBLE)
	{
	  val_str = db_get_string (&conv_val);
	  val_str_size = db_get_string_size (&conv_val);
	}
    }

    return tp_finish_enumeration_conversion (target, desired_domain, conv_val, val_idx, val_str, val_str_size,
	   status, exit);
  }
  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_enumeration_to_enumeration — ENUM → 다른 ENUM 도메인 셀 — 이름이 있으면 이름으로, 없으면 인덱스로 목적 ENUM 요소를
 * 찾는다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop ENUM case 의 `case DB_TYPE_ENUMERATION:`
 * 갈래(object_domain.c:9771~)로, 공유 지역 변수에 결과를 남기고 공통 꼬리로 떨어졌다.
 * 이 PR: 목적 ENUM 의 요소 수가 0 이면 pr_clone_value 로 복제하고 exit=true 로 꼬리를 건너뛴다. 그 밖에는 소스 이름 문자열을 쓰되, 코드셋이 다르면
 * DB_MAX_STRING_LENGTH VARCHAR 임시값으로 db_char_string_coerce 해 변환하고(실패 DOMAIN_ERROR + val_str/val_idx 초기화), 이름이
 * 없으면 인덱스를 쓴다.
 * 바뀐 것: 갈래를 셀로 분리하고 지역 변수 공유를 인자 전달로 바꿨다(+76줄). exit 플래그가 실제로 true 가 되는 유일한 셀이라,
 * tp_finish_enumeration_conversion 이 exit 인자를 받는 이유가 여기다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_enumeration_to_enumeration (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;

  {
    unsigned short val_idx = 0;
    int val_str_size = 0;
    const char *val_str = NULL;
    bool exit = false;
    DB_VALUE conv_val;

    db_make_null (&conv_val);

    if (src->domain.general_info.is_null)
      {
	db_make_null (target);
	return status;
      }

    if (DOM_GET_ENUM_ELEMS_COUNT (desired_domain) == 0)
      {
	pr_clone_value (src, target);
	exit = true;
      }
    else
      {
	val_str = db_get_enum_string (src);
	val_str_size = db_get_enum_string_size (src);
	if (val_str == NULL)
	  {
	    /* src has a short value or a string value or both. We prefer to use the string value when matching
	     * against the desired domain but, if this is not set, we will use the value index */
	    val_idx = db_get_enum_short (src);
	  }
	else
	  {
	    if (db_get_enum_codeset (src) != TP_DOMAIN_CODESET (desired_domain))
	      {
		/* first convert charset of the original value to charset of destination domain */
		DB_VALUE tmp;
		DB_DATA_STATUS data_status = DATA_STATUS_OK;

		/* charset conversion can handle only CHAR/VARCHAR DB_VALUEs, create a STRING value with max
		 * precision (so that no truncation occurs) from the ENUM source string */
		db_make_varchar (&tmp, DB_MAX_STRING_LENGTH, val_str, val_str_size, db_get_enum_codeset (src),
				 db_get_enum_collation (src));

		/* initialize destination value of conversion */
		db_value_domain_init (&conv_val, DB_TYPE_STRING, DB_MAX_STRING_LENGTH, 0);
		db_string_put_cs_and_collation (&conv_val, TP_DOMAIN_CODESET (desired_domain),
						TP_DOMAIN_COLLATION (desired_domain));

		if (db_char_string_coerce (&tmp, &conv_val, &data_status) != NO_ERROR
		    || data_status != DATA_STATUS_OK)
		  {
		    status = DOMAIN_ERROR;
		    pr_clear_value (&conv_val);
		    val_str = NULL;
		    val_idx = 0;
		  }
		else
		  {
		    val_str = db_get_string (&conv_val);
		    val_str_size = db_get_string_size (&conv_val);
		  }
		pr_clear_value (&tmp);
	      }
	  }
      }
    return tp_finish_enumeration_conversion (target, desired_domain, conv_val, val_idx, val_str, val_str_size,
	   status, exit);
  }
  return status;
}

/*
 * [리뷰] tp_value_convert_bit_to_enumeration — BIT → ENUM 셀 — 비트열을 16진 문자열로 만든 뒤 그 문자열로 ENUM 요소를 찾는다.
 * develop: develop 에 없음 — 이 PR 이 신설. develop ENUM case(9617)의 12개 소스 묶음 갈래(9713)로 기본 STRING 도메인에 재귀 캐스트했다.
 * 이 PR: conv_val 을 기본 STRING VARCHAR 로 초기화하고 tp_value_convert_bit_to_varchar 로 문자열화한 뒤 꼬리 함수에 넘긴다.
 * 바뀐 것: 12갈래를 셀로 펼치고 재귀 캐스트를 직접 호출로 바꿨다(+41줄).
 */
static TP_DOMAIN_STATUS
tp_value_convert_bit_to_enumeration (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				     date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;

  {
    unsigned short val_idx = 0;
    int val_str_size = 0;
    const char *val_str = NULL;
    bool exit = false;
    DB_VALUE conv_val;

    db_make_null (&conv_val);

    if (src->domain.general_info.is_null)
      {
	db_make_null (target);
	return DOMAIN_COMPATIBLE;
      }

    {
      const TP_DOMAIN *string_domain = tp_domain_resolve_default (DB_TYPE_STRING);
      db_value_domain_init (&conv_val, DB_TYPE_VARCHAR, string_domain->precision, string_domain->scale);
      db_string_put_cs_and_collation (&conv_val, TP_DOMAIN_CODESET (string_domain),
				      TP_DOMAIN_COLLATION (string_domain));
      status =
	      tp_value_convert_bit_to_varchar (src, &conv_val, tp_domain_resolve_default (DB_TYPE_STRING),
		  error);
      if (status == DOMAIN_COMPATIBLE)
	{
	  val_str = db_get_string (&conv_val);
	  val_str_size = db_get_string_size (&conv_val);
	}
    }

    return tp_finish_enumeration_conversion (target, desired_domain, conv_val, val_idx, val_str, val_str_size,
	   status, exit);
  }
  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_varbit_to_enumeration — VARBIT → ENUM 셀 — bit 판과 같은 경로.
 * develop: develop 에 없음 — 이 PR 이 신설. develop 에서는 BIT·VARBIT 이 같은 12개 소스 묶음 갈래(9713) 안이었다.
 * 이 PR: bit 판과 똑같이 tp_value_convert_bit_to_varchar 를 부른다 — 그 셀이 BIT·VARBIT 공용이기 때문이다.
 * 바뀐 것: 12갈래를 셀로 펼치고 재귀 캐스트를 직접 호출로 바꿨다(+41줄). 이름만 다르고 본문은 tp_value_convert_bit_to_enumeration 과 한 글자도 다르지 않다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_varbit_to_enumeration (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
					date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;

  {
    unsigned short val_idx = 0;
    int val_str_size = 0;
    const char *val_str = NULL;
    bool exit = false;
    DB_VALUE conv_val;

    db_make_null (&conv_val);

    if (src->domain.general_info.is_null)
      {
	db_make_null (target);
	return DOMAIN_COMPATIBLE;
      }

    {
      const TP_DOMAIN *string_domain = tp_domain_resolve_default (DB_TYPE_STRING);
      db_value_domain_init (&conv_val, DB_TYPE_VARCHAR, string_domain->precision, string_domain->scale);
      db_string_put_cs_and_collation (&conv_val, TP_DOMAIN_CODESET (string_domain),
				      TP_DOMAIN_COLLATION (string_domain));
      status =
	      tp_value_convert_bit_to_varchar (src, &conv_val, tp_domain_resolve_default (DB_TYPE_STRING),
		  error);
      if (status == DOMAIN_COMPATIBLE)
	{
	  val_str = db_get_string (&conv_val);
	  val_str_size = db_get_string_size (&conv_val);
	}
    }

    return tp_finish_enumeration_conversion (target, desired_domain, conv_val, val_idx, val_str, val_str_size,
	   status, exit);
  }
  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_blob_to_enumeration — BLOB 값을 ENUM 으로 바꾸는 변환기 — 값을 기본 STRING 도메인의 VARCHAR 로 먼저 만든 뒤
 * tp_finish_enumeration_conversion 이 ENUM 원소 목록과 맞춰 target 에 ENUM 을 쓴다. 게이트(tp_value_find_converter)가
 * ASSIGN/IMPLICIT 모드에서 이 포인터를 고른다.
 * develop: develop 에는 없다 — object_domain.c tp_value_cast_internal(develop:6992-10078) 의 `case
 * DB_TYPE_ENUMERATION:`(develop:9617) 안에서 BLOB·CLOB 가 TIMESTAMP·DATE·BIT 등과 한 가지를 공유했고, tp_value_cast_internal
 * 을 STRING 도메인으로 재귀 호출해 conv_val 을 얻었다(develop:9745 부근).
 * 이 PR: 재귀 대신 tp_value_convert_blob_to_varchar 를 직접 부른다. 재귀가 해 주던 db_value_domain_init +
 * db_string_put_cs_and_collation 을 이 함수가 직접 한다.
 * 바뀐 것: case 공유 가지 → 소스 타입별 함수 분리(+41줄). 재귀 호출 1건이 직접 호출로 바뀌고 대상 DB_VALUE 초기화가 함수 안으로 들어왔다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_blob_to_enumeration (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				      date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;

  {
    unsigned short val_idx = 0;
    int val_str_size = 0;
    const char *val_str = NULL;
    bool exit = false;
    DB_VALUE conv_val;

    db_make_null (&conv_val);

    if (src->domain.general_info.is_null)
      {
	db_make_null (target);
	return DOMAIN_COMPATIBLE;
      }

    {
      const TP_DOMAIN *string_domain = tp_domain_resolve_default (DB_TYPE_STRING);
      db_value_domain_init (&conv_val, DB_TYPE_VARCHAR, string_domain->precision, string_domain->scale);
      db_string_put_cs_and_collation (&conv_val, TP_DOMAIN_CODESET (string_domain),
				      TP_DOMAIN_COLLATION (string_domain));
      status =
	      tp_value_convert_blob_to_varchar (src, &conv_val, tp_domain_resolve_default (DB_TYPE_STRING),
		  error);
      if (status == DOMAIN_COMPATIBLE)
	{
	  val_str = db_get_string (&conv_val);
	  val_str_size = db_get_string_size (&conv_val);
	}
    }

    return tp_finish_enumeration_conversion (target, desired_domain, conv_val, val_idx, val_str, val_str_size,
	   status, exit);
  }
  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_clob_to_enumeration — CLOB 값을 ENUM 으로 바꾸는 변환기 — 값을 기본 STRING 도메인의 VARCHAR 로 먼저 만든 뒤
 * tp_finish_enumeration_conversion 이 ENUM 원소 목록과 맞춰 target 에 ENUM 을 쓴다. 게이트(tp_value_find_converter)가
 * ASSIGN/IMPLICIT 모드에서 이 포인터를 고른다.
 * develop: develop 에는 없다 — object_domain.c tp_value_cast_internal(develop:6992-10078) 의 `case
 * DB_TYPE_ENUMERATION:`(develop:9617) 안에서 BLOB·CLOB 가 TIMESTAMP·DATE·BIT 등과 한 가지를 공유했고, tp_value_cast_internal
 * 을 STRING 도메인으로 재귀 호출해 conv_val 을 얻었다(develop:9745 부근).
 * 이 PR: 재귀 대신 tp_value_convert_clob_to_varchar 를 직접 부른다. 재귀가 해 주던 db_value_domain_init +
 * db_string_put_cs_and_collation 을 이 함수가 직접 한다.
 * 바뀐 것: case 공유 가지 → 소스 타입별 함수 분리(+41줄). 재귀 호출 1건이 직접 호출로 바뀌고 대상 DB_VALUE 초기화가 함수 안으로 들어왔다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_clob_to_enumeration (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				      date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;

  {
    unsigned short val_idx = 0;
    int val_str_size = 0;
    const char *val_str = NULL;
    bool exit = false;
    DB_VALUE conv_val;

    db_make_null (&conv_val);

    if (src->domain.general_info.is_null)
      {
	db_make_null (target);
	return DOMAIN_COMPATIBLE;
      }

    {
      const TP_DOMAIN *string_domain = tp_domain_resolve_default (DB_TYPE_STRING);
      db_value_domain_init (&conv_val, DB_TYPE_VARCHAR, string_domain->precision, string_domain->scale);
      db_string_put_cs_and_collation (&conv_val, TP_DOMAIN_CODESET (string_domain),
				      TP_DOMAIN_COLLATION (string_domain));
      status =
	      tp_value_convert_clob_to_varchar (src, &conv_val, tp_domain_resolve_default (DB_TYPE_STRING),
		  error);
      if (status == DOMAIN_COMPATIBLE)
	{
	  val_str = db_get_string (&conv_val);
	  val_str_size = db_get_string_size (&conv_val);
	}
    }

    return tp_finish_enumeration_conversion (target, desired_domain, conv_val, val_idx, val_str, val_str_size,
	   status, exit);
  }
  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_short_to_json — SHORT 값을 JSON 스칼라 문서로 감싸는 변환기 — db_json_allocate_doc 으로 문서를 만들어
 * db_json_set_int_to_doc(db_get_short) 로 값을 넣고 db_make_json(target, doc, true) 로 소유권째 넘긴다. 게이트가 고른
 * TP_VALUE_CONVERTER 중 하나다.
 * develop: develop 에는 없다 — object_domain.c tp_value_cast_internal(develop:6992-10078) 의 `case
 * DB_TYPE_JSON:`(develop:9940) 안 `case DB_TYPE_SHORT:` 한 줄짜리 가지였고, doc 할당·db_make_json·실패 시 db_json_delete_doc
 * 는 JSON 가지 전체가 공유했다.
 * 이 PR: 같은 계산을 하는 단독 함수. 공유하던 뒤처리(`if (status == DOMAIN_COMPATIBLE) db_make_json ... else delete`)가 함수마다 복사됐다.
 * 바뀐 것: case 가지 → 함수 추출(약 +27줄). 소스 타입 판정이 런타임 switch 에서 디스패치 표로 옮겨졌다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_short_to_json (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;

  {
    JSON_DOC *doc = NULL;

    doc = db_json_allocate_doc ();
    db_json_set_int_to_doc (doc, db_get_short (src));

    if (status == DOMAIN_COMPATIBLE)
      {
	db_make_json (target, doc, true);
      }
    else
      {
	if (doc != NULL)
	  {
	    db_json_delete_doc (doc);
	  }
      }
  }

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_integer_to_json — INTEGER 값을 JSON 스칼라 문서로 감싸는 변환기 — db_json_allocate_doc 으로 문서를 만들어
 * db_json_set_int_to_doc(db_get_int) 로 값을 넣고 db_make_json(target, doc, true) 로 소유권째 넘긴다. 게이트가 고른
 * TP_VALUE_CONVERTER 중 하나다.
 * develop: develop 에는 없다 — object_domain.c tp_value_cast_internal(develop:6992-10078) 의 `case
 * DB_TYPE_JSON:`(develop:9940) 안 `case DB_TYPE_INTEGER:` 한 줄짜리 가지였고, doc 할당·db_make_json·실패 시
 * db_json_delete_doc 는 JSON 가지 전체가 공유했다.
 * 이 PR: 같은 계산을 하는 단독 함수. 공유하던 뒤처리(`if (status == DOMAIN_COMPATIBLE) db_make_json ... else delete`)가 함수마다 복사됐다.
 * 바뀐 것: case 가지 → 함수 추출(약 +27줄). 소스 타입 판정이 런타임 switch 에서 디스패치 표로 옮겨졌다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_integer_to_json (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				  date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;

  {
    JSON_DOC *doc = NULL;

    doc = db_json_allocate_doc ();
    db_json_set_int_to_doc (doc, db_get_int (src));

    if (status == DOMAIN_COMPATIBLE)
      {
	db_make_json (target, doc, true);
      }
    else
      {
	if (doc != NULL)
	  {
	    db_json_delete_doc (doc);
	  }
      }
  }

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_bigint_to_json — BIGINT 값을 JSON 스칼라 문서로 감싸는 변환기 — db_json_allocate_doc 으로 문서를 만들어
 * db_json_set_bigint_to_doc(db_get_bigint) 로 값을 넣고 db_make_json(target, doc, true) 로 소유권째 넘긴다. 게이트가 고른
 * TP_VALUE_CONVERTER 중 하나다.
 * develop: develop 에는 없다 — object_domain.c tp_value_cast_internal(develop:6992-10078) 의 `case
 * DB_TYPE_JSON:`(develop:9940) 안 `case DB_TYPE_BIGINT:` 한 줄짜리 가지였고, doc 할당·db_make_json·실패 시
 * db_json_delete_doc 는 JSON 가지 전체가 공유했다.
 * 이 PR: 같은 계산을 하는 단독 함수. 공유하던 뒤처리(`if (status == DOMAIN_COMPATIBLE) db_make_json ... else delete`)가 함수마다 복사됐다.
 * 바뀐 것: case 가지 → 함수 추출(약 +27줄). 소스 타입 판정이 런타임 switch 에서 디스패치 표로 옮겨졌다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_bigint_to_json (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				 date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;

  {
    JSON_DOC *doc = NULL;

    doc = db_json_allocate_doc ();
    db_json_set_bigint_to_doc (doc, db_get_bigint (src));

    if (status == DOMAIN_COMPATIBLE)
      {
	db_make_json (target, doc, true);
      }
    else
      {
	if (doc != NULL)
	  {
	    db_json_delete_doc (doc);
	  }
      }
  }

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_float_to_json — FLOAT 값을 JSON 스칼라(double)로 감싸는 변환기 — 먼저 DOUBLE 로 올린 뒤
 * db_json_set_double_to_doc 에 넣고 db_make_json 으로 target 에 쓴다.
 * develop: develop 에는 없다 — object_domain.c tp_value_cast_internal(develop:6992-10078) 의 JSON 가지에서 FLOAT 와
 * NUMERIC 이 한 case 를 공유했고, `db_value_coerce (src, &double_value, db_type_to_db_domain
 * (DB_TYPE_DOUBLE))`(develop:10006) 로 올린 뒤 반환값을 버렸다. double_value 는 초기화 없이 선언됐다.
 * 이 PR: FLOAT 전용 함수. db_make_double(&double_value, 0) 으로 먼저 초기화하고 tp_value_convert_number<DB_TYPE_FLOAT,
 * DB_TYPE_DOUBLE, DOMAIN_CONVERT_ASSIGN> 을 직접 부른다(반환값은 여전히 버린다).
 * 바뀐 것: FLOAT/NUMERIC 공유 가지 → 두 함수로 분리. db_value_coerce 호출이 템플릿 변환기 직접 호출로 바뀌고, 초기화되지 않은 double_value 를 읽을 수
 * 있던 경로가 db_make_double 로 막혔다(+37줄).
 */
static TP_DOMAIN_STATUS
tp_value_convert_float_to_json (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;

  {
    JSON_DOC *doc = NULL;

    {
      DB_VALUE double_value;

      doc = db_json_allocate_doc ();
      db_make_double (&double_value, 0);
      tp_value_convert_number < DB_TYPE_FLOAT, DB_TYPE_DOUBLE, DOMAIN_CONVERT_ASSIGN > (
	      src, &double_value,
	      &tp_Double_domain, error)
      ;
      db_json_set_double_to_doc (doc, db_get_double (&double_value));
      pr_clear_value (&double_value);
    }

    if (status == DOMAIN_COMPATIBLE)
      {
	db_make_json (target, doc, true);
      }
    else
      {
	if (doc != NULL)
	  {
	    db_json_delete_doc (doc);
	  }
      }
  }

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_double_to_json — DOUBLE 값을 JSON 스칼라 문서로 감싸는 변환기 — db_json_allocate_doc 으로 문서를 만들어
 * db_json_set_double_to_doc(db_get_double) 로 값을 넣고 db_make_json(target, doc, true) 로 소유권째 넘긴다. 게이트가 고른
 * TP_VALUE_CONVERTER 중 하나다.
 * develop: develop 에는 없다 — object_domain.c tp_value_cast_internal(develop:6992-10078) 의 `case
 * DB_TYPE_JSON:`(develop:9940) 안 `case DB_TYPE_DOUBLE:` 한 줄짜리 가지였고, doc 할당·db_make_json·실패 시
 * db_json_delete_doc 는 JSON 가지 전체가 공유했다.
 * 이 PR: 같은 계산을 하는 단독 함수. 공유하던 뒤처리(`if (status == DOMAIN_COMPATIBLE) db_make_json ... else delete`)가 함수마다 복사됐다.
 * 바뀐 것: case 가지 → 함수 추출(약 +27줄). 소스 타입 판정이 런타임 switch 에서 디스패치 표로 옮겨졌다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_double_to_json (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				 date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;

  {
    JSON_DOC *doc = NULL;

    doc = db_json_allocate_doc ();
    db_json_set_double_to_doc (doc, db_get_double (src));

    if (status == DOMAIN_COMPATIBLE)
      {
	db_make_json (target, doc, true);
      }
    else
      {
	if (doc != NULL)
	  {
	    db_json_delete_doc (doc);
	  }
      }
  }

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_numeric_to_json — NUMERIC 값을 JSON 스칼라(double)로 감싸는 변환기 — DOUBLE 로 올려 문서에 넣고
 * db_make_json 으로 target 에 쓴다.
 * develop: develop 에는 없다 — object_domain.c tp_value_cast_internal(develop:6992-10078) 의 JSON 가지에서 FLOAT 와 한
 * case 를 공유하며 db_value_coerce 로 DOUBLE 을 만들었다(develop:10006).
 * 이 PR: NUMERIC 전용 함수. db_make_double 로 초기화한 뒤 tp_value_convert_number<DB_TYPE_NUMERIC, DB_TYPE_DOUBLE,
 * DOMAIN_CONVERT_ASSIGN> 을 부른다.
 * 바뀐 것: FLOAT/NUMERIC 공유 가지의 NUMERIC 쪽 분리(+37줄). 변환 실패 시 develop 이 읽던 미초기화 값 대신 0.0 이 들어간다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_numeric_to_json (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				  date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;

  {
    JSON_DOC *doc = NULL;

    {
      DB_VALUE double_value;

      doc = db_json_allocate_doc ();
      db_make_double (&double_value, 0);
      tp_value_convert_number < DB_TYPE_NUMERIC, DB_TYPE_DOUBLE, DOMAIN_CONVERT_ASSIGN > (
	      src, &double_value,
	      &tp_Double_domain, error)
      ;
      db_json_set_double_to_doc (doc, db_get_double (&double_value));
      pr_clear_value (&double_value);
    }

    if (status == DOMAIN_COMPATIBLE)
      {
	db_make_json (target, doc, true);
      }
    else
      {
	if (doc != NULL)
	  {
	    db_json_delete_doc (doc);
	  }
      }
  }

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_char_to_json — 문자열을 JSON 문서로 파싱하는 변환기 — UTF-8 로 맞춘 뒤 db_json_get_json_from_str 로 파싱하고,
 * desired_domain->json_validator 가 있으면 스키마까지 검증해 db_make_json 으로 target 에 쓴다.
 * develop: develop 에는 없다 — object_domain.c tp_value_cast_internal(develop:6992-10078) 의 `case DB_TYPE_JSON:` 안
 * `case DB_TYPE_CHAR:/VARCHAR:`(develop:9947-9980) 가지였고, 실패 시 `status = DOMAIN_ERROR; break;` 로 공유 뒤처리로 빠졌다.
 * 이 PR: 같은 순서(utf8 변환 → 파싱 → 스키마 검증)를 그대로 가진 단독 함수. break 가 중첩 if/else 로 평탄화됐고 status 를 그대로 반환한다.
 * 바뀐 것: case 가지 → 함수 추출(+58줄). 제어 흐름이 break 에서 if/else 체인으로 바뀌었을 뿐 조건·정리 순서는 같다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_char_to_json (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
			       date_conversion_error *error)
{
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;

  {
    JSON_DOC *doc = NULL;

    DB_VALUE utf8_str;
    const DB_VALUE *json_str_val = &utf8_str;
    int error_code = db_json_copy_and_convert_to_utf8 (src, &utf8_str, &json_str_val);
    if (error_code != NO_ERROR)
      {
	ASSERT_ERROR ();
	status = DOMAIN_ERROR;
      }
    else
      {
	unsigned int str_size = db_get_string_size (json_str_val);
	const char *original_str = db_get_string (json_str_val);

	error_code = db_json_get_json_from_str (original_str, doc, str_size);
	if (error_code != NO_ERROR)
	  {
	    pr_clear_value (&utf8_str);
	    assert (doc == NULL);
	    status = DOMAIN_ERROR;
	  }
	else if (desired_domain->json_validator
		 && db_json_validate_doc (desired_domain->json_validator, doc) != NO_ERROR)
	  {
	    ASSERT_ERROR ();
	    pr_clear_value (&utf8_str);
	    db_json_delete_doc (doc);
	    status = DOMAIN_ERROR;
	  }
	else
	  {
	    pr_clear_value (&utf8_str);
	  }
      }

    if (status == DOMAIN_COMPATIBLE)
      {
	db_make_json (target, doc, true);
      }
    else
      {
	if (doc != NULL)
	  {
	    db_json_delete_doc (doc);
	  }
      }
  }

  return status;
}

/*
 * [리뷰] tp_value_convert_char_to_time_strict — CHAR/VARCHAR 값을 TIME 로 손실 없이 옮기는 변환기. tp_value_coerce_strict 와
 * 비교/피연산자 모드가 tp_value_find_converter 로 이 포인터를 받아 호출하고, target 에 값을 쓴 뒤 TP_DOMAIN_STATUS 를 돌려준다 — 행은 호출만 하고 타입
 * 짝은 다시 풀지 않는다.
 * develop: develop 에 없음 — object_domain.c tp_value_coerce_strict 의 switch 안 `case DB_TYPE_TIME:`(develop:6270)
 * 밑 `case DB_TYPE_CHAR:/VARCHAR:` 가지였다. 실패를 `err = ER_FAILED` 로 적었고 tp_atotime()(실패 시 er_set) 를 썼다.
 * 이 PR: 같은 계산의 단독 static 함수. 실패는 DOMAIN_INCOMPATIBLE 반환이고, tp_atotime_core(src,&time,error) 로 전역 에러 대신
 * date_conversion_error 에만 기록한다(발행은 호출자의 conversion_error.publish()).
 * 바뀐 것: case 가지 → 함수 추출(신설 4인자, 본문 전체가 추가분). ER_FAILED→DOMAIN_INCOMPATIBLE, 헬퍼를
 * tp_atotime_core(src,&time,error) 로 교체.
 */
static TP_DOMAIN_STATUS
tp_value_convert_char_to_time_strict (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				      date_conversion_error *error)
{
  {
    DB_TIME time = 0;
    if (tp_atotime_core (src, &time, error) != NO_ERROR)
      {
	return DOMAIN_INCOMPATIBLE;
      }
    db_value_put_encoded_time (target, &time);
    return DOMAIN_COMPATIBLE;
  }

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_char_to_date_strict — CHAR/VARCHAR 값을 DATE 로 손실 없이 옮기는 변환기. tp_value_coerce_strict 와
 * 비교/피연산자 모드가 tp_value_find_converter 로 이 포인터를 받아 호출하고, target 에 값을 쓴 뒤 TP_DOMAIN_STATUS 를 돌려준다 — 행은 호출만 하고 타입
 * 짝은 다시 풀지 않는다.
 * develop: develop 에 없음 — object_domain.c tp_value_coerce_strict 의 switch 안 `case DB_TYPE_DATE:`(develop:6291)
 * 밑 `case DB_TYPE_CHAR:/VARCHAR:` 가지였다. 실패를 `err = ER_FAILED` 로 적었고 tp_atodate() 를 썼다.
 * 이 PR: 같은 계산의 단독 static 함수. 실패는 DOMAIN_INCOMPATIBLE 반환이고, tp_atodate_core(src,&date,error) 로 전역 에러 대신
 * date_conversion_error 에만 기록한다(발행은 호출자의 conversion_error.publish()).
 * 바뀐 것: case 가지 → 함수 추출(신설 4인자, 본문 전체가 추가분). ER_FAILED→DOMAIN_INCOMPATIBLE, 헬퍼를
 * tp_atodate_core(src,&date,error) 로 교체.
 */
static TP_DOMAIN_STATUS
tp_value_convert_char_to_date_strict (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				      date_conversion_error *error)
{
  {
    DB_DATE date = 0;

    if (tp_atodate_core (src, &date, error) != NO_ERROR)
      {
	return DOMAIN_INCOMPATIBLE;
      }
    db_value_put_encoded_date (target, &date);
    return DOMAIN_COMPATIBLE;
  }

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_timestamp_to_date_strict — TIMESTAMP(및 TIMESTAMPLTZ) 값을 DATE 로 손실 없이 옮기는 변환기.
 * tp_value_coerce_strict 와 비교/피연산자 모드가 tp_value_find_converter 로 이 포인터를 받아 호출하고, target 에 값을 쓴 뒤
 * TP_DOMAIN_STATUS 를 돌려준다 — 행은 호출만 하고 타입 짝은 다시 풀지 않는다.
 * develop: develop 에 없음 — object_domain.c tp_value_coerce_strict 의 switch 안 `case DB_TYPE_DATE:`(develop:6291)
 * 밑 `case DB_TYPE_TIMESTAMP:/TIMESTAMPLTZ:`(두 타입이 한 가지를 공유) 가지였다. 실패를 `err = ER_FAILED` 로 적었고
 * db_timestamp_decode_ses() 를 썼다.
 * 이 PR: 같은 계산의 단독 static 함수. 실패는 DOMAIN_INCOMPATIBLE 반환이고, db_timestamp_decode_ses_core(...,error) 로 전역 에러 대신
 * date_conversion_error 에만 기록한다(발행은 호출자의 conversion_error.publish()). 반환값은 develop 과 똑같이 (void) 로 버리고 time !=
 * 0 만 본다.
 * 바뀐 것: case 가지 → 함수 추출(신설 4인자, 본문 전체가 추가분). ER_FAILED→DOMAIN_INCOMPATIBLE, 헬퍼를
 * db_timestamp_decode_ses_core(...,error) 로 교체. 디스패치 표에서 TIMESTAMP·TIMESTAMPLTZ 두 소스가 모두 이 함수를 가리켜 develop 의
 * 공유 가지를 유지한다.
 * [지적 A4-03]
 */
static TP_DOMAIN_STATUS
tp_value_convert_timestamp_to_date_strict (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  {
    DB_DATE date = 0;
    DB_TIME time = 0;
    DB_TIMESTAMP *ts = NULL;

    ts = db_get_timestamp (src);
    (void) db_timestamp_decode_ses_core (ts, &date, &time, error);
    if (time != 0)
      {
	/* only "downcast" if time is 0 */
	return DOMAIN_INCOMPATIBLE;
      }
    db_value_put_encoded_date (target, &date);
    return DOMAIN_COMPATIBLE;
  }

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_timestamptz_to_date_strict — TIMESTAMPTZ 값을 DATE 로 손실 없이 옮기는 변환기.
 * tp_value_coerce_strict 와 비교/피연산자 모드가 tp_value_find_converter 로 이 포인터를 받아 호출하고, target 에 값을 쓴 뒤
 * TP_DOMAIN_STATUS 를 돌려준다 — 행은 호출만 하고 타입 짝은 다시 풀지 않는다.
 * develop: develop 에 없음 — object_domain.c tp_value_coerce_strict 의 switch 안 `case DB_TYPE_DATE:`(develop:6291)
 * 밑 `case DB_TYPE_TIMESTAMPTZ:` 가지였다. 실패를 `err = ER_FAILED` 로 적었고 db_timestamp_decode_w_tz_id() 를 썼다.
 * 이 PR: 같은 계산의 단독 static 함수. 실패는 DOMAIN_INCOMPATIBLE 반환이고, db_timestamp_decode_w_tz_id_core(...,error) 로 전역 에러
 * 대신 date_conversion_error 에만 기록한다(발행은 호출자의 conversion_error.publish()).
 * 바뀐 것: case 가지 → 함수 추출(신설 4인자, 본문 전체가 추가분). ER_FAILED→DOMAIN_INCOMPATIBLE, 헬퍼를
 * db_timestamp_decode_w_tz_id_core(...,error) 로 교체.
 */
static TP_DOMAIN_STATUS
tp_value_convert_timestamptz_to_date_strict (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  int err = NO_ERROR;

  {
    DB_DATE date = 0;
    DB_TIME time = 0;
    DB_TIMESTAMPTZ *ts_tz = NULL;

    ts_tz = db_get_timestamptz (src);
    err = db_timestamp_decode_w_tz_id_core (&ts_tz->timestamp, &ts_tz->tz_id, &date, &time, error);
    if (err != NO_ERROR || time != 0)
      {
	/* only "downcast" if time is 0 */
	return DOMAIN_INCOMPATIBLE;
      }
    db_value_put_encoded_date (target, &date);
    return err == NO_ERROR ? DOMAIN_COMPATIBLE : DOMAIN_INCOMPATIBLE;
  }

  return err == NO_ERROR ? DOMAIN_COMPATIBLE : DOMAIN_INCOMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_datetime_to_date_strict — DATETIME 값을 DATE 로 손실 없이 옮기는 변환기. tp_value_coerce_strict 와
 * 비교/피연산자 모드가 tp_value_find_converter 로 이 포인터를 받아 호출하고, target 에 값을 쓴 뒤 TP_DOMAIN_STATUS 를 돌려준다 — 행은 호출만 하고 타입
 * 짝은 다시 풀지 않는다.
 * develop: develop 에 없음 — object_domain.c tp_value_coerce_strict 의 switch 안 `case DB_TYPE_DATE:`(develop:6291)
 * 밑 `case DB_TYPE_DATETIME:` 가지였다. 실패를 `err = ER_FAILED` 로 적었고, 변환 헬퍼 없이 필드를 직접 복사했다.
 * 이 PR: 같은 계산의 단독 static 함수. 실패는 DOMAIN_INCOMPATIBLE 반환이고, 부르는 변환 헬퍼가 없어 date_conversion_error 는 건드리지
 * 않는다(시그니처만 맞춰 받는다).
 * 바뀐 것: case 가지 → 함수 추출(신설 4인자, 본문 전체가 추가분). 에러 표현만 ER_FAILED→DOMAIN_INCOMPATIBLE 로 바뀌었고 헬퍼 교체는 없다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_datetime_to_date_strict (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  {
    DB_DATETIME *src_dt = NULL;

    src_dt = db_get_datetime (src);
    if (src_dt->time != 0)
      {
	/* only "downcast" if time is 0 */
	return DOMAIN_INCOMPATIBLE;
      }
    db_value_put_encoded_date (target, (DB_DATE *) (&src_dt->date));
    return DOMAIN_COMPATIBLE;
  }

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_datetimeltz_to_date_strict — DATETIMELTZ 값을 DATE 로 손실 없이 옮기는 변환기.
 * tp_value_coerce_strict 와 비교/피연산자 모드가 tp_value_find_converter 로 이 포인터를 받아 호출하고, target 에 값을 쓴 뒤
 * TP_DOMAIN_STATUS 를 돌려준다 — 행은 호출만 하고 타입 짝은 다시 풀지 않는다.
 * develop: develop 에 없음 — object_domain.c tp_value_coerce_strict 의 switch 안 `case DB_TYPE_DATE:`(develop:6291)
 * 밑 `case DB_TYPE_DATETIMELTZ:/DATETIMETZ:`(한 가지를 `if (original_type == DB_TYPE_DATETIMELTZ)` 로 갈랐다) 가지였다. 실패를
 * `err = ER_FAILED` 로 적었고 tz_create_session_tzid_for_datetime() + tz_utc_datetimetz_to_local() 를 썼다.
 * 이 PR: 같은 계산의 단독 static 함수. 실패는 DOMAIN_INCOMPATIBLE 반환이고,
 * tz_create_session_tzid_for_datetime_core/tz_utc_datetimetz_to_local_core(...,error) 로 전역 에러 대신
 * date_conversion_error 에만 기록한다(발행은 호출자의 conversion_error.publish()).
 * 바뀐 것: case 가지 → 함수 추출(신설 4인자, 본문 전체가 추가분). ER_FAILED→DOMAIN_INCOMPATIBLE, 헬퍼를
 * tz_create_session_tzid_for_datetime_core/tz_utc_datetimetz_to_local_core(...,error) 로 교체. 공유 가지를 둘로 쪼개 런타임
 * if 를 없앴다(이 쪽이 LTZ 분기).
 */
static TP_DOMAIN_STATUS
tp_value_convert_datetimeltz_to_date_strict (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  {
    DB_DATETIME *utc_dt_p;
    DB_DATETIME local_dt;
    TZ_ID tz_id;

    /* DATETIMELTZ and DATETIMETZ store in UTC, convert to session */
    {
      utc_dt_p = db_get_datetime (src);
      if (tz_create_session_tzid_for_datetime_core (utc_dt_p, true, &tz_id, error) != NO_ERROR)
	{
	  return DOMAIN_INCOMPATIBLE;
	}
    }

    if (tz_utc_datetimetz_to_local_core (utc_dt_p, &tz_id, &local_dt, error) != NO_ERROR)
      {
	return DOMAIN_INCOMPATIBLE;
      }

    if (local_dt.time != 0)
      {
	/* only "downcast" if time is 0 */
	return DOMAIN_INCOMPATIBLE;
      }

    db_value_put_encoded_date (target, (DB_DATE *) (&local_dt.date));
    return DOMAIN_COMPATIBLE;
  }

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_datetimetz_to_date_strict — DATETIMETZ 값을 DATE 로 손실 없이 옮기는 변환기. tp_value_coerce_strict
 * 와 비교/피연산자 모드가 tp_value_find_converter 로 이 포인터를 받아 호출하고, target 에 값을 쓴 뒤 TP_DOMAIN_STATUS 를 돌려준다 — 행은 호출만 하고
 * 타입 짝은 다시 풀지 않는다.
 * develop: develop 에 없음 — object_domain.c tp_value_coerce_strict 의 switch 안 `case DB_TYPE_DATE:`(develop:6291)
 * 밑 `case DB_TYPE_DATETIMELTZ:/DATETIMETZ:` 의 TZ 분기 가지였다. 실패를 `err = ER_FAILED` 로 적었고
 * tz_utc_datetimetz_to_local() 를 썼다.
 * 이 PR: 같은 계산의 단독 static 함수. 실패는 DOMAIN_INCOMPATIBLE 반환이고, tz_utc_datetimetz_to_local_core(...,error) 로 전역 에러
 * 대신 date_conversion_error 에만 기록한다(발행은 호출자의 conversion_error.publish()).
 * 바뀐 것: case 가지 → 함수 추출(신설 4인자, 본문 전체가 추가분). ER_FAILED→DOMAIN_INCOMPATIBLE, 헬퍼를
 * tz_utc_datetimetz_to_local_core(...,error) 로 교체. 공유 가지를 둘로 쪼갠 TZ 쪽 — tz_id 를 값에서 직접 읽어 세션 tz 조회가 사라졌다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_datetimetz_to_date_strict (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  {
    DB_DATETIME *utc_dt_p;
    DB_DATETIMETZ *dt_tz_p;
    DB_DATETIME local_dt;
    TZ_ID tz_id;

    /* DATETIMELTZ and DATETIMETZ store in UTC, convert to session */
    {
      dt_tz_p = db_get_datetimetz (src);
      utc_dt_p = &dt_tz_p->datetime;
      tz_id = dt_tz_p->tz_id;
    }

    if (tz_utc_datetimetz_to_local_core (utc_dt_p, &tz_id, &local_dt, error) != NO_ERROR)
      {
	return DOMAIN_INCOMPATIBLE;
      }

    if (local_dt.time != 0)
      {
	/* only "downcast" if time is 0 */
	return DOMAIN_INCOMPATIBLE;
      }

    db_value_put_encoded_date (target, (DB_DATE *) (&local_dt.date));
    return DOMAIN_COMPATIBLE;
  }

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_char_to_datetime_strict — CHAR/VARCHAR 값을 DATETIME 로 손실 없이 옮기는 변환기.
 * tp_value_coerce_strict 와 비교/피연산자 모드가 tp_value_find_converter 로 이 포인터를 받아 호출하고, target 에 값을 쓴 뒤
 * TP_DOMAIN_STATUS 를 돌려준다 — 행은 호출만 하고 타입 짝은 다시 풀지 않는다.
 * develop: develop 에 없음 — object_domain.c tp_value_coerce_strict 의 switch 안 `case
 * DB_TYPE_DATETIME:`(develop:6403) 밑 `case DB_TYPE_VARCHAR:/CHAR:` 가지였다. 실패를 `err = ER_FAILED` 로 적었고
 * tp_atoudatetime() 를 썼다.
 * 이 PR: 같은 계산의 단독 static 함수. 실패는 DOMAIN_INCOMPATIBLE 반환이고, tp_atoudatetime_core(src,&datetime,error) 로 전역 에러
 * 대신 date_conversion_error 에만 기록한다(발행은 호출자의 conversion_error.publish()).
 * 바뀐 것: case 가지 → 함수 추출(신설 4인자, 본문 전체가 추가분). ER_FAILED→DOMAIN_INCOMPATIBLE, 헬퍼를
 * tp_atoudatetime_core(src,&datetime,error) 로 교체.
 */
static TP_DOMAIN_STATUS
tp_value_convert_char_to_datetime_strict (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  {
    DB_DATETIME datetime = { 0, 0 };
    if (tp_atoudatetime_core (src, &datetime, error) != NO_ERROR)
      {
	return DOMAIN_INCOMPATIBLE;
      }
    db_make_datetime (target, &datetime);
    return DOMAIN_COMPATIBLE;
  }

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_date_to_datetime_strict — DATE 값을 DATETIME 로 손실 없이 옮기는 변환기. tp_value_coerce_strict 와
 * 비교/피연산자 모드가 tp_value_find_converter 로 이 포인터를 받아 호출하고, target 에 값을 쓴 뒤 TP_DOMAIN_STATUS 를 돌려준다 — 행은 호출만 하고 타입
 * 짝은 다시 풀지 않는다.
 * develop: develop 에 없음 — object_domain.c tp_value_coerce_strict 의 switch 안 `case
 * DB_TYPE_DATETIME:`(develop:6403) 밑 `case DB_TYPE_DATE:` 가지였다. 실패를 `err = ER_FAILED` 로 적었고, 변환 헬퍼 없이 필드를 직접
 * 복사했다.
 * 이 PR: 같은 계산의 단독 static 함수. 실패는 DOMAIN_INCOMPATIBLE 반환이고, 부르는 변환 헬퍼가 없어 date_conversion_error 는 건드리지
 * 않는다(시그니처만 맞춰 받는다).
 * 바뀐 것: case 가지 → 함수 추출(신설 4인자, 본문 전체가 추가분). 에러 표현만 ER_FAILED→DOMAIN_INCOMPATIBLE 로 바뀌었고 헬퍼 교체는 없다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_date_to_datetime_strict (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  {
    DB_DATETIME datetime = { 0, 0 };
    datetime.date = *db_get_date (src);
    datetime.time = 0;
    db_make_datetime (target, &datetime);
    return DOMAIN_COMPATIBLE;
  }

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_timestamp_to_datetime_strict — TIMESTAMP(및 TIMESTAMPLTZ) 값을 DATETIME 로 손실 없이 옮기는 변환기.
 * tp_value_coerce_strict 와 비교/피연산자 모드가 tp_value_find_converter 로 이 포인터를 받아 호출하고, target 에 값을 쓴 뒤
 * TP_DOMAIN_STATUS 를 돌려준다 — 행은 호출만 하고 타입 짝은 다시 풀지 않는다.
 * develop: develop 에 없음 — object_domain.c tp_value_coerce_strict 의 switch 안 `case
 * DB_TYPE_DATETIME:`(develop:6403) 밑 `case DB_TYPE_TIMESTAMP:/TIMESTAMPLTZ:`(공유 가지) 가지였다. 실패를 `err =
 * ER_FAILED` 로 적었고 db_timestamp_decode_ses() 를 썼다.
 * 이 PR: 같은 계산의 단독 static 함수. 실패는 DOMAIN_INCOMPATIBLE 반환이고, db_timestamp_decode_ses_core(...,error) 로 전역 에러 대신
 * date_conversion_error 에만 기록한다(발행은 호출자의 conversion_error.publish()).
 * 바뀐 것: case 가지 → 함수 추출(신설 4인자, 본문 전체가 추가분). ER_FAILED→DOMAIN_INCOMPATIBLE, 헬퍼를
 * db_timestamp_decode_ses_core(...,error) 로 교체.
 */
static TP_DOMAIN_STATUS
tp_value_convert_timestamp_to_datetime_strict (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  {
    DB_DATETIME datetime = { 0, 0 };
    DB_TIMESTAMP *utime = db_get_timestamp (src);
    DB_DATE date;
    DB_TIME time;

    if (db_timestamp_decode_ses_core (utime, &date, &time, error) != NO_ERROR)
      {
	return DOMAIN_INCOMPATIBLE;
      }
    datetime.time = time * 1000;
    datetime.date = date;
    db_make_datetime (target, &datetime);
    return DOMAIN_COMPATIBLE;
  }

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_timestamptz_to_datetime_strict — TIMESTAMPTZ 값을 DATETIME 로 손실 없이 옮기는 변환기.
 * tp_value_coerce_strict 와 비교/피연산자 모드가 tp_value_find_converter 로 이 포인터를 받아 호출하고, target 에 값을 쓴 뒤
 * TP_DOMAIN_STATUS 를 돌려준다 — 행은 호출만 하고 타입 짝은 다시 풀지 않는다.
 * develop: develop 에 없음 — object_domain.c tp_value_coerce_strict 의 switch 안 `case
 * DB_TYPE_DATETIME:`(develop:6403) 밑 `case DB_TYPE_TIMESTAMPTZ:` 가지였다. 실패를 `err = ER_FAILED` 로 적었고
 * db_timestamp_decode_w_tz_id() 를 썼다.
 * 이 PR: 같은 계산의 단독 static 함수. 실패는 DOMAIN_INCOMPATIBLE 반환이고, db_timestamp_decode_w_tz_id_core(...,error) 로 전역 에러
 * 대신 date_conversion_error 에만 기록한다(발행은 호출자의 conversion_error.publish()).
 * 바뀐 것: case 가지 → 함수 추출(신설 4인자, 본문 전체가 추가분). ER_FAILED→DOMAIN_INCOMPATIBLE, 헬퍼를
 * db_timestamp_decode_w_tz_id_core(...,error) 로 교체.
 */
static TP_DOMAIN_STATUS
tp_value_convert_timestamptz_to_datetime_strict (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  {
    DB_DATETIME datetime = { 0, 0 };
    DB_DATE date;
    DB_TIME time;
    DB_TIMESTAMPTZ *ts_tz = db_get_timestamptz (src);

    if (db_timestamp_decode_w_tz_id_core (&ts_tz->timestamp, &ts_tz->tz_id, &date, &time, error) != NO_ERROR)
      {
	return DOMAIN_INCOMPATIBLE;
      }

    datetime.time = time * 1000;
    datetime.date = date;
    db_make_datetime (target, &datetime);
    return DOMAIN_COMPATIBLE;
  }

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_datetimeltz_to_datetime_strict — DATETIMELTZ 값을 DATETIME 로 손실 없이 옮기는 변환기.
 * tp_value_coerce_strict 와 비교/피연산자 모드가 tp_value_find_converter 로 이 포인터를 받아 호출하고, target 에 값을 쓴 뒤
 * TP_DOMAIN_STATUS 를 돌려준다 — 행은 호출만 하고 타입 짝은 다시 풀지 않는다.
 * develop: develop 에 없음 — object_domain.c tp_value_coerce_strict 의 switch 안 `case
 * DB_TYPE_DATETIME:`(develop:6403) 밑 `case DB_TYPE_DATETIMELTZ:` 가지였다. 실패를 `err = ER_FAILED` 로 적었고, 변환 헬퍼 없이
 * 필드를 직접 복사했다.
 * 이 PR: 같은 계산의 단독 static 함수. 실패는 DOMAIN_INCOMPATIBLE 반환이고, 부르는 변환 헬퍼가 없어 date_conversion_error 는 건드리지
 * 않는다(시그니처만 맞춰 받는다).
 * 바뀐 것: case 가지 → 함수 추출(신설 4인자, 본문 전체가 추가분). 에러 표현만 ER_FAILED→DOMAIN_INCOMPATIBLE 로 바뀌었고 헬퍼 교체는 없다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_datetimeltz_to_datetime_strict (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  {
    DB_DATETIME *dt = db_get_datetime (src);
    db_make_datetime (target, dt);
    return DOMAIN_COMPATIBLE;
  }

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_datetimetz_to_datetime_strict — DATETIMETZ 값을 DATETIME 로 손실 없이 옮기는 변환기.
 * tp_value_coerce_strict 와 비교/피연산자 모드가 tp_value_find_converter 로 이 포인터를 받아 호출하고, target 에 값을 쓴 뒤
 * TP_DOMAIN_STATUS 를 돌려준다 — 행은 호출만 하고 타입 짝은 다시 풀지 않는다.
 * develop: develop 에 없음 — object_domain.c tp_value_coerce_strict 의 switch 안 `case
 * DB_TYPE_DATETIME:`(develop:6403) 밑 `case DB_TYPE_DATETIMETZ:` 가지였다. 실패를 `err = ER_FAILED` 로 적었고, 변환 헬퍼 없이
 * 필드를 직접 복사했다.
 * 이 PR: 같은 계산의 단독 static 함수. 실패는 DOMAIN_INCOMPATIBLE 반환이고, 부르는 변환 헬퍼가 없어 date_conversion_error 는 건드리지
 * 않는다(시그니처만 맞춰 받는다).
 * 바뀐 것: case 가지 → 함수 추출(신설 4인자, 본문 전체가 추가분). 에러 표현만 ER_FAILED→DOMAIN_INCOMPATIBLE 로 바뀌었고 헬퍼 교체는 없다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_datetimetz_to_datetime_strict (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  {
    DB_DATETIMETZ *dt_tz = db_get_datetimetz (src);
    db_make_datetime (target, &dt_tz->datetime);
    return DOMAIN_COMPATIBLE;
  }

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_char_to_datetimetz_strict — CHAR/VARCHAR 값을 DATETIMETZ 로 손실 없이 옮기는 변환기.
 * tp_value_coerce_strict 와 비교/피연산자 모드가 tp_value_find_converter 로 이 포인터를 받아 호출하고, target 에 값을 쓴 뒤
 * TP_DOMAIN_STATUS 를 돌려준다 — 행은 호출만 하고 타입 짝은 다시 풀지 않는다.
 * develop: develop 에 없음 — object_domain.c tp_value_coerce_strict 의 switch 안 `case
 * DB_TYPE_DATETIMETZ:`(develop:6480) 밑 `case DB_TYPE_VARCHAR:/CHAR:` 가지였다. 실패를 `err = ER_FAILED` 로 적었고
 * tp_atodatetimetz() 를 썼다.
 * 이 PR: 같은 계산의 단독 static 함수. 실패는 DOMAIN_INCOMPATIBLE 반환이고, tp_atodatetimetz_core(src,&dt_tz,error) 로 전역 에러 대신
 * date_conversion_error 에만 기록한다(발행은 호출자의 conversion_error.publish()).
 * 바뀐 것: case 가지 → 함수 추출(신설 4인자, 본문 전체가 추가분). ER_FAILED→DOMAIN_INCOMPATIBLE, 헬퍼를
 * tp_atodatetimetz_core(src,&dt_tz,error) 로 교체.
 */
static TP_DOMAIN_STATUS
tp_value_convert_char_to_datetimetz_strict (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  {
    DB_DATETIMETZ dt_tz = DB_DATETIMETZ_INITIALIZER;

    if (tp_atodatetimetz_core (src, &dt_tz, error) != NO_ERROR)
      {
	return DOMAIN_INCOMPATIBLE;
      }

    db_make_datetimetz (target, &dt_tz);
  }

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_date_to_datetimetz_strict — DATE 값을 DATETIMETZ 로 손실 없이 옮기는 변환기. tp_value_coerce_strict
 * 와 비교/피연산자 모드가 tp_value_find_converter 로 이 포인터를 받아 호출하고, target 에 값을 쓴 뒤 TP_DOMAIN_STATUS 를 돌려준다 — 행은 호출만 하고
 * 타입 짝은 다시 풀지 않는다.
 * develop: develop 에 없음 — object_domain.c tp_value_coerce_strict 의 switch 안 `case
 * DB_TYPE_DATETIMETZ:`(develop:6480) 밑 `case DB_TYPE_DATE:/DATETIME:`(한 가지를 `if (original_type ==
 * DB_TYPE_DATE)` 로 갈랐다) 가지였다. 실패를 `err = ER_FAILED` 로 적었고 tz_create_datetimetz_from_ses() 를 썼다.
 * 이 PR: 같은 계산의 단독 static 함수. 실패는 DOMAIN_INCOMPATIBLE 반환이고, tz_create_datetimetz_from_ses_core(...,error) 로 전역
 * 에러 대신 date_conversion_error 에만 기록한다(발행은 호출자의 conversion_error.publish()).
 * 바뀐 것: case 가지 → 함수 추출(신설 4인자, 본문 전체가 추가분). ER_FAILED→DOMAIN_INCOMPATIBLE, 헬퍼를
 * tz_create_datetimetz_from_ses_core(...,error) 로 교체. DATE/DATETIME 공유 가지를 둘로 쪼갠 DATE 쪽(time = 0 고정).
 */
static TP_DOMAIN_STATUS
tp_value_convert_date_to_datetimetz_strict (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  int err = NO_ERROR;

  {
    DB_DATETIMETZ dt_tz = DB_DATETIMETZ_INITIALIZER;

    {
      dt_tz.datetime.date = *db_get_date (src);
      dt_tz.datetime.time = 0;
    }

    err = tz_create_datetimetz_from_ses_core (& (dt_tz.datetime), &dt_tz, error);
    if (err == NO_ERROR)
      {
	db_make_datetimetz (target, &dt_tz);
      }
    return err == NO_ERROR ? DOMAIN_COMPATIBLE : DOMAIN_INCOMPATIBLE;
  }

  return err == NO_ERROR ? DOMAIN_COMPATIBLE : DOMAIN_INCOMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_timestamp_to_datetimetz_strict — TIMESTAMP(및 TIMESTAMPLTZ) 값을 DATETIMETZ 로 손실 없이 옮기는
 * 변환기. tp_value_coerce_strict 와 비교/피연산자 모드가 tp_value_find_converter 로 이 포인터를 받아 호출하고, target 에 값을 쓴 뒤
 * TP_DOMAIN_STATUS 를 돌려준다 — 행은 호출만 하고 타입 짝은 다시 풀지 않는다.
 * develop: develop 에 없음 — object_domain.c tp_value_coerce_strict 의 switch 안 `case
 * DB_TYPE_DATETIMETZ:`(develop:6480) 밑 `case DB_TYPE_TIMESTAMP:/TIMESTAMPLTZ:`(공유 가지) 가지였다. 실패를 `err =
 * ER_FAILED` 로 적었고 tz_create_session_tzid_for_datetime() 를 썼다.
 * 이 PR: 같은 계산의 단독 static 함수. 실패는 DOMAIN_INCOMPATIBLE 반환이고,
 * tz_create_session_tzid_for_datetime_core(...,true,...,error) 로 전역 에러 대신 date_conversion_error 에만 기록한다(발행은
 * 호출자의 conversion_error.publish()). db_timestamp_decode_utc 는 에러를 내지 않아 그대로 둔다.
 * 바뀐 것: case 가지 → 함수 추출(신설 4인자, 본문 전체가 추가분). ER_FAILED→DOMAIN_INCOMPATIBLE, 헬퍼를
 * tz_create_session_tzid_for_datetime_core(...,true,...,error) 로 교체.
 */
static TP_DOMAIN_STATUS
tp_value_convert_timestamp_to_datetimetz_strict (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  int err = NO_ERROR;

  {
    DB_DATETIMETZ dt_tz = DB_DATETIMETZ_INITIALIZER;
    DB_TIMESTAMP *utime = db_get_timestamp (src);
    DB_DATE date;
    DB_TIME time;

    /* convert DT to TS in UTC reference */
    db_timestamp_decode_utc (utime, &date, &time);
    dt_tz.datetime.date = date;
    dt_tz.datetime.time = time * 1000;
    err = tz_create_session_tzid_for_datetime_core (&dt_tz.datetime, true, & (dt_tz.tz_id), error);
    if (err == NO_ERROR)
      {
	db_make_datetimetz (target, &dt_tz);
      }
    return err == NO_ERROR ? DOMAIN_COMPATIBLE : DOMAIN_INCOMPATIBLE;
  }

  return err == NO_ERROR ? DOMAIN_COMPATIBLE : DOMAIN_INCOMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_timestamptz_to_datetimetz_strict — TIMESTAMPTZ 값을 DATETIMETZ 로 손실 없이 옮기는 변환기.
 * tp_value_coerce_strict 와 비교/피연산자 모드가 tp_value_find_converter 로 이 포인터를 받아 호출하고, target 에 값을 쓴 뒤
 * TP_DOMAIN_STATUS 를 돌려준다 — 행은 호출만 하고 타입 짝은 다시 풀지 않는다.
 * develop: develop 에 없음 — object_domain.c tp_value_coerce_strict 의 switch 안 `case
 * DB_TYPE_DATETIMETZ:`(develop:6480) 밑 `case DB_TYPE_TIMESTAMPTZ:` 가지였다. 실패를 `err = ER_FAILED` 로 적었고
 * db_timestamp_decode_utc()(에러 없음) 를 썼다.
 * 이 PR: 같은 계산의 단독 static 함수. 실패는 DOMAIN_INCOMPATIBLE 반환이고, 헬퍼는 에러를 내지 않는 db_timestamp_decode_utc() 그대로라
 * date_conversion_error 를 쓰지 않는다. tz_id 는 원본 값에서 복사하므로 error 를 쓰지 않는다.
 * 바뀐 것: case 가지 → 함수 추출(신설 4인자, 본문 전체가 추가분). 에러 표현만 ER_FAILED→DOMAIN_INCOMPATIBLE 로 바뀌었고
 * 헬퍼(db_timestamp_decode_utc)는 그대로다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_timestamptz_to_datetimetz_strict (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  {
    DB_DATETIMETZ dt_tz = DB_DATETIMETZ_INITIALIZER;
    DB_TIMESTAMPTZ *ts_tz = db_get_timestamptz (src);
    DB_DATE date;
    DB_TIME time;

    (void) db_timestamp_decode_utc (&ts_tz->timestamp, &date, &time);
    dt_tz.datetime.time = time * 1000;
    dt_tz.datetime.date = date;
    dt_tz.tz_id = ts_tz->tz_id;
    db_make_datetimetz (target, &dt_tz);
    return DOMAIN_COMPATIBLE;
  }

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_datetime_to_datetimetz_strict — DATETIME 값을 DATETIMETZ 로 손실 없이 옮기는 변환기.
 * tp_value_coerce_strict 와 비교/피연산자 모드가 tp_value_find_converter 로 이 포인터를 받아 호출하고, target 에 값을 쓴 뒤
 * TP_DOMAIN_STATUS 를 돌려준다 — 행은 호출만 하고 타입 짝은 다시 풀지 않는다.
 * develop: develop 에 없음 — object_domain.c tp_value_coerce_strict 의 switch 안 `case
 * DB_TYPE_DATETIMETZ:`(develop:6480) 밑 `case DB_TYPE_DATE:/DATETIME:` 의 DATETIME 분기 가지였다. 실패를 `err =
 * ER_FAILED` 로 적었고 tz_create_datetimetz_from_ses() 를 썼다.
 * 이 PR: 같은 계산의 단독 static 함수. 실패는 DOMAIN_INCOMPATIBLE 반환이고, tz_create_datetimetz_from_ses_core(...,error) 로 전역
 * 에러 대신 date_conversion_error 에만 기록한다(발행은 호출자의 conversion_error.publish()).
 * 바뀐 것: case 가지 → 함수 추출(신설 4인자, 본문 전체가 추가분). ER_FAILED→DOMAIN_INCOMPATIBLE, 헬퍼를
 * tz_create_datetimetz_from_ses_core(...,error) 로 교체.
 */
static TP_DOMAIN_STATUS
tp_value_convert_datetime_to_datetimetz_strict (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  int err = NO_ERROR;

  {
    DB_DATETIMETZ dt_tz = DB_DATETIMETZ_INITIALIZER;

    {
      dt_tz.datetime = *db_get_datetime (src);
    }

    err = tz_create_datetimetz_from_ses_core (& (dt_tz.datetime), &dt_tz, error);
    if (err == NO_ERROR)
      {
	db_make_datetimetz (target, &dt_tz);
      }
    return err == NO_ERROR ? DOMAIN_COMPATIBLE : DOMAIN_INCOMPATIBLE;
  }

  return err == NO_ERROR ? DOMAIN_COMPATIBLE : DOMAIN_INCOMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_datetimeltz_to_datetimetz_strict — DATETIMELTZ 값을 DATETIMETZ 로 손실 없이 옮기는 변환기.
 * tp_value_coerce_strict 와 비교/피연산자 모드가 tp_value_find_converter 로 이 포인터를 받아 호출하고, target 에 값을 쓴 뒤
 * TP_DOMAIN_STATUS 를 돌려준다 — 행은 호출만 하고 타입 짝은 다시 풀지 않는다.
 * develop: develop 에 없음 — object_domain.c tp_value_coerce_strict 의 switch 안 `case
 * DB_TYPE_DATETIMETZ:`(develop:6480) 밑 `case DB_TYPE_DATETIMELTZ:` 가지였다. 실패를 `err = ER_FAILED` 로 적었고
 * tz_create_session_tzid_for_datetime(dt,false,...) 를 썼다.
 * 이 PR: 같은 계산의 단독 static 함수. 실패는 DOMAIN_INCOMPATIBLE 반환이고,
 * tz_create_session_tzid_for_datetime_core(dt,false,...,error) 로 전역 에러 대신 date_conversion_error 에만 기록한다(발행은
 * 호출자의 conversion_error.publish()).
 * 바뀐 것: case 가지 → 함수 추출(신설 4인자, 본문 전체가 추가분). ER_FAILED→DOMAIN_INCOMPATIBLE, 헬퍼를
 * tz_create_session_tzid_for_datetime_core(dt,false,...,error) 로 교체.
 */
static TP_DOMAIN_STATUS
tp_value_convert_datetimeltz_to_datetimetz_strict (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  int err = NO_ERROR;

  {
    DB_DATETIMETZ dt_tz = DB_DATETIMETZ_INITIALIZER;
    DB_DATETIME *dt = db_get_datetime (src);

    dt_tz.datetime = *dt;
    err = tz_create_session_tzid_for_datetime_core (dt, false, &dt_tz.tz_id, error);
    if (err == NO_ERROR)
      {
	db_make_datetimetz (target, &dt_tz);
      }
    return err == NO_ERROR ? DOMAIN_COMPATIBLE : DOMAIN_INCOMPATIBLE;
  }

  return err == NO_ERROR ? DOMAIN_COMPATIBLE : DOMAIN_INCOMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_char_to_datetimeltz_strict — CHAR/VARCHAR 값을 DATETIMELTZ 로 손실 없이 옮기는 변환기.
 * tp_value_coerce_strict 와 비교/피연산자 모드가 tp_value_find_converter 로 이 포인터를 받아 호출하고, target 에 값을 쓴 뒤
 * TP_DOMAIN_STATUS 를 돌려준다 — 행은 호출만 하고 타입 짝은 다시 풀지 않는다.
 * develop: develop 에 없음 — object_domain.c tp_value_coerce_strict 의 switch 안 `case
 * DB_TYPE_DATETIMELTZ:`(develop:6572) 밑 `case DB_TYPE_VARCHAR:/CHAR:` 가지였다. 실패를 `err = ER_FAILED` 로 적었고
 * tp_atodatetimetz() 를 썼다.
 * 이 PR: 같은 계산의 단독 static 함수. 실패는 DOMAIN_INCOMPATIBLE 반환이고, tp_atodatetimetz_core(src,&dt_tz,error) 로 전역 에러 대신
 * date_conversion_error 에만 기록한다(발행은 호출자의 conversion_error.publish()).
 * 바뀐 것: case 가지 → 함수 추출(신설 4인자, 본문 전체가 추가분). ER_FAILED→DOMAIN_INCOMPATIBLE, 헬퍼를
 * tp_atodatetimetz_core(src,&dt_tz,error) 로 교체.
 */
static TP_DOMAIN_STATUS
tp_value_convert_char_to_datetimeltz_strict (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  {
    DB_DATETIMETZ dt_tz = DB_DATETIMETZ_INITIALIZER;

    if (tp_atodatetimetz_core (src, &dt_tz, error) != NO_ERROR)
      {
	return DOMAIN_INCOMPATIBLE;
      }
    db_make_datetimeltz (target, &dt_tz.datetime);
    return DOMAIN_COMPATIBLE;
  }

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_date_to_datetimeltz_strict — DATE 값을 DATETIMELTZ 로 손실 없이 옮기는 변환기.
 * tp_value_coerce_strict 와 비교/피연산자 모드가 tp_value_find_converter 로 이 포인터를 받아 호출하고, target 에 값을 쓴 뒤
 * TP_DOMAIN_STATUS 를 돌려준다 — 행은 호출만 하고 타입 짝은 다시 풀지 않는다.
 * develop: develop 에 없음 — object_domain.c tp_value_coerce_strict 의 switch 안 `case
 * DB_TYPE_DATETIMELTZ:`(develop:6572) 밑 `case DB_TYPE_DATE:/DATETIME:`(공유 가지) 가지였다. 실패를 `err = ER_FAILED` 로
 * 적었고 tz_create_datetimetz_from_ses() 를 썼다.
 * 이 PR: 같은 계산의 단독 static 함수. 실패는 DOMAIN_INCOMPATIBLE 반환이고,
 * tz_create_datetimetz_from_ses_core(&datetime,&dt_tz,error) 로 전역 에러 대신 date_conversion_error 에만 기록한다(발행은 호출자의
 * conversion_error.publish()).
 * 바뀐 것: case 가지 → 함수 추출(신설 4인자, 본문 전체가 추가분). ER_FAILED→DOMAIN_INCOMPATIBLE, 헬퍼를
 * tz_create_datetimetz_from_ses_core(&datetime,&dt_tz,error) 로 교체. DATE/DATETIME 공유 가지를 둘로 쪼갠 DATE 쪽.
 */
static TP_DOMAIN_STATUS
tp_value_convert_date_to_datetimeltz_strict (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  int err = NO_ERROR;

  {
    DB_DATETIME datetime;
    DB_DATETIMETZ dt_tz;

    {
      datetime.date = *db_get_date (src);
      datetime.time = 0;
    }

    err = tz_create_datetimetz_from_ses_core (&datetime, &dt_tz, error);
    if (err != NO_ERROR)
      {
	return DOMAIN_INCOMPATIBLE;
      }

    db_make_datetimeltz (target, &dt_tz.datetime);
    return err == NO_ERROR ? DOMAIN_COMPATIBLE : DOMAIN_INCOMPATIBLE;
  }

  return err == NO_ERROR ? DOMAIN_COMPATIBLE : DOMAIN_INCOMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_timestamp_to_datetimeltz_strict — TIMESTAMP(및 TIMESTAMPLTZ) 값을 DATETIMELTZ 로 손실 없이 옮기는
 * 변환기. tp_value_coerce_strict 와 비교/피연산자 모드가 tp_value_find_converter 로 이 포인터를 받아 호출하고, target 에 값을 쓴 뒤
 * TP_DOMAIN_STATUS 를 돌려준다 — 행은 호출만 하고 타입 짝은 다시 풀지 않는다.
 * develop: develop 에 없음 — object_domain.c tp_value_coerce_strict 의 switch 안 `case
 * DB_TYPE_DATETIMELTZ:`(develop:6572) 밑 `case DB_TYPE_TIMESTAMP:/TIMESTAMPLTZ:`(공유 가지) 가지였다. 실패를 `err =
 * ER_FAILED` 로 적었고 db_timestamp_decode_utc()(에러 없음) 를 썼다.
 * 이 PR: 같은 계산의 단독 static 함수. 실패는 DOMAIN_INCOMPATIBLE 반환이고, 헬퍼는 에러를 내지 않는 db_timestamp_decode_utc() 그대로라
 * date_conversion_error 를 쓰지 않는다. UTC 그대로 담으므로 error 를 쓰지 않는다.
 * 바뀐 것: case 가지 → 함수 추출(신설 4인자, 본문 전체가 추가분). 에러 표현만 ER_FAILED→DOMAIN_INCOMPATIBLE 로 바뀌었고
 * 헬퍼(db_timestamp_decode_utc)는 그대로다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_timestamp_to_datetimeltz_strict (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  {
    DB_DATETIME datetime = { 0, 0 };
    DB_TIMESTAMP *utime = db_get_timestamp (src);
    DB_DATE date;
    DB_TIME time;

    (void) db_timestamp_decode_utc (utime, &date, &time);
    datetime.time = time * 1000;
    datetime.date = date;
    db_make_datetimeltz (target, &datetime);
    return DOMAIN_COMPATIBLE;
  }

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_timestamptz_to_datetimeltz_strict — TIMESTAMPTZ 값을 DATETIMELTZ 로 손실 없이 옮기는 변환기.
 * tp_value_coerce_strict 와 비교/피연산자 모드가 tp_value_find_converter 로 이 포인터를 받아 호출하고, target 에 값을 쓴 뒤
 * TP_DOMAIN_STATUS 를 돌려준다 — 행은 호출만 하고 타입 짝은 다시 풀지 않는다.
 * develop: develop 에 없음 — object_domain.c tp_value_coerce_strict 의 switch 안 `case
 * DB_TYPE_DATETIMELTZ:`(develop:6572) 밑 `case DB_TYPE_TIMESTAMPTZ:` 가지였다. 실패를 `err = ER_FAILED` 로 적었고
 * db_timestamp_decode_utc()(에러 없음) 를 썼다.
 * 이 PR: 같은 계산의 단독 static 함수. 실패는 DOMAIN_INCOMPATIBLE 반환이고, 헬퍼는 에러를 내지 않는 db_timestamp_decode_utc() 그대로라
 * date_conversion_error 를 쓰지 않는다.
 * 바뀐 것: case 가지 → 함수 추출(신설 4인자, 본문 전체가 추가분). 에러 표현만 ER_FAILED→DOMAIN_INCOMPATIBLE 로 바뀌었고
 * 헬퍼(db_timestamp_decode_utc)는 그대로다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_timestamptz_to_datetimeltz_strict (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain,
    date_conversion_error *error)
{
  {
    DB_DATETIME datetime = { 0, 0 };
    DB_TIMESTAMPTZ *ts_tz = db_get_timestamptz (src);
    DB_DATE date;
    DB_TIME time;

    (void) db_timestamp_decode_utc (&ts_tz->timestamp, &date, &time);
    datetime.time = time * 1000;
    datetime.date = date;
    db_make_datetimeltz (target, &datetime);
    return DOMAIN_COMPATIBLE;
  }

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_datetime_to_datetimeltz_strict — DATETIME 값을 DATETIMELTZ 로 손실 없이 옮기는 변환기.
 * tp_value_coerce_strict 와 비교/피연산자 모드가 tp_value_find_converter 로 이 포인터를 받아 호출하고, target 에 값을 쓴 뒤
 * TP_DOMAIN_STATUS 를 돌려준다 — 행은 호출만 하고 타입 짝은 다시 풀지 않는다.
 * develop: develop 에 없음 — object_domain.c tp_value_coerce_strict 의 switch 안 `case
 * DB_TYPE_DATETIMELTZ:`(develop:6572) 밑 `case DB_TYPE_DATE:/DATETIME:` 의 DATETIME 분기 가지였다. 실패를 `err =
 * ER_FAILED` 로 적었고 tz_create_datetimetz_from_ses() 를 썼다.
 * 이 PR: 같은 계산의 단독 static 함수. 실패는 DOMAIN_INCOMPATIBLE 반환이고, tz_create_datetimetz_from_ses_core(...,error) 로 전역
 * 에러 대신 date_conversion_error 에만 기록한다(발행은 호출자의 conversion_error.publish()).
 * 바뀐 것: case 가지 → 함수 추출(신설 4인자, 본문 전체가 추가분). ER_FAILED→DOMAIN_INCOMPATIBLE, 헬퍼를
 * tz_create_datetimetz_from_ses_core(...,error) 로 교체.
 */
static TP_DOMAIN_STATUS
tp_value_convert_datetime_to_datetimeltz_strict (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  int err = NO_ERROR;

  {
    DB_DATETIME datetime;
    DB_DATETIMETZ dt_tz;

    {
      datetime = *db_get_datetime (src);
    }

    err = tz_create_datetimetz_from_ses_core (&datetime, &dt_tz, error);
    if (err != NO_ERROR)
      {
	return DOMAIN_INCOMPATIBLE;
      }

    db_make_datetimeltz (target, &dt_tz.datetime);
    return err == NO_ERROR ? DOMAIN_COMPATIBLE : DOMAIN_INCOMPATIBLE;
  }

  return err == NO_ERROR ? DOMAIN_COMPATIBLE : DOMAIN_INCOMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_datetimetz_to_datetimeltz_strict — DATETIMETZ 값을 DATETIMELTZ 로 손실 없이 옮기는 변환기.
 * tp_value_coerce_strict 와 비교/피연산자 모드가 tp_value_find_converter 로 이 포인터를 받아 호출하고, target 에 값을 쓴 뒤
 * TP_DOMAIN_STATUS 를 돌려준다 — 행은 호출만 하고 타입 짝은 다시 풀지 않는다.
 * develop: develop 에 없음 — object_domain.c tp_value_coerce_strict 의 switch 안 `case
 * DB_TYPE_DATETIMELTZ:`(develop:6572) 밑 `case DB_TYPE_DATETIMETZ:` 가지였다. 실패를 `err = ER_FAILED` 로 적었고, 변환 헬퍼 없이
 * UTC 값을 그대로 복사했다.
 * 이 PR: 같은 계산의 단독 static 함수. 실패는 DOMAIN_INCOMPATIBLE 반환이고, 부르는 변환 헬퍼가 없어 date_conversion_error 는 건드리지
 * 않는다(시그니처만 맞춰 받는다).
 * 바뀐 것: case 가지 → 함수 추출(신설 4인자, 본문 전체가 추가분). 에러 표현만 ER_FAILED→DOMAIN_INCOMPATIBLE 로 바뀌었고 헬퍼 교체는 없다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_datetimetz_to_datetimeltz_strict (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  {
    DB_DATETIMETZ *dt_tz = db_get_datetimetz (src);

    /* copy datetime (UTC) */
    db_make_datetimeltz (target, &dt_tz->datetime);
    return DOMAIN_COMPATIBLE;
  }

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_char_to_timestamp_strict — CHAR/VARCHAR 값을 TIMESTAMP 로 손실 없이 옮기는 변환기.
 * tp_value_coerce_strict 와 비교/피연산자 모드가 tp_value_find_converter 로 이 포인터를 받아 호출하고, target 에 값을 쓴 뒤
 * TP_DOMAIN_STATUS 를 돌려준다 — 행은 호출만 하고 타입 짝은 다시 풀지 않는다.
 * develop: develop 에 없음 — object_domain.c tp_value_coerce_strict 의 switch 안 `case
 * DB_TYPE_TIMESTAMP:`(develop:6655) 밑 `case DB_TYPE_VARCHAR:/CHAR:` 가지였다. 실패를 `err = ER_FAILED` 로 적었고
 * tp_atoutime() 를 썼다.
 * 이 PR: 같은 계산의 단독 static 함수. 실패는 DOMAIN_INCOMPATIBLE 반환이고, tp_atoutime_core(src,&ts,error) 로 전역 에러 대신
 * date_conversion_error 에만 기록한다(발행은 호출자의 conversion_error.publish()).
 * 바뀐 것: case 가지 → 함수 추출(신설 4인자, 본문 전체가 추가분). ER_FAILED→DOMAIN_INCOMPATIBLE, 헬퍼를
 * tp_atoutime_core(src,&ts,error) 로 교체.
 */
static TP_DOMAIN_STATUS
tp_value_convert_char_to_timestamp_strict (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  {
    DB_TIMESTAMP ts = 0;

    if (tp_atoutime_core (src, &ts, error) != NO_ERROR)
      {
	return DOMAIN_INCOMPATIBLE;
      }
    db_make_timestamp (target, ts);
    return DOMAIN_COMPATIBLE;
  }

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_date_to_timestamp_strict — DATE 값을 TIMESTAMP 로 손실 없이 옮기는 변환기. tp_value_coerce_strict 와
 * 비교/피연산자 모드가 tp_value_find_converter 로 이 포인터를 받아 호출하고, target 에 값을 쓴 뒤 TP_DOMAIN_STATUS 를 돌려준다 — 행은 호출만 하고 타입
 * 짝은 다시 풀지 않는다.
 * develop: develop 에 없음 — object_domain.c tp_value_coerce_strict 의 switch 안 `case
 * DB_TYPE_TIMESTAMP:`(develop:6655) 밑 `case DB_TYPE_DATE:` 가지였다. 실패를 `err = ER_FAILED` 로 적었고 db_time_encode()
 * + db_timestamp_encode_ses() 를 썼다.
 * 이 PR: 같은 계산의 단독 static 함수. 실패는 DOMAIN_INCOMPATIBLE 반환이고,
 * db_time_encode_core/db_timestamp_encode_ses_core(...,error) 로 전역 에러 대신 date_conversion_error 에만 기록한다(발행은
 * 호출자의 conversion_error.publish()).
 * 바뀐 것: case 가지 → 함수 추출(신설 4인자, 본문 전체가 추가분). ER_FAILED→DOMAIN_INCOMPATIBLE, 헬퍼를
 * db_time_encode_core/db_timestamp_encode_ses_core(...,error) 로 교체.
 */
static TP_DOMAIN_STATUS
tp_value_convert_date_to_timestamp_strict (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  {
    DB_TIME tm = 0;
    DB_DATE date = *db_get_date (src);
    DB_TIMESTAMP ts = 0;

    db_time_encode_core (&tm, 0, 0, 0, error);
    if (db_timestamp_encode_ses_core (&date, &tm, &ts, NULL, error) != NO_ERROR)
      {
	return DOMAIN_INCOMPATIBLE;
      }
    db_make_timestamp (target, ts);
    return DOMAIN_COMPATIBLE;
  }

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_timestampltz_to_timestamp_strict — TIMESTAMPLTZ 값을 TIMESTAMP 로 손실 없이 옮기는 변환기.
 * tp_value_coerce_strict 와 비교/피연산자 모드가 tp_value_find_converter 로 이 포인터를 받아 호출하고, target 에 값을 쓴 뒤
 * TP_DOMAIN_STATUS 를 돌려준다 — 행은 호출만 하고 타입 짝은 다시 풀지 않는다.
 * develop: develop 에 없음 — object_domain.c tp_value_coerce_strict 의 switch 안 `case
 * DB_TYPE_TIMESTAMP:`(develop:6655) 밑 `case DB_TYPE_TIMESTAMPLTZ:`(UTC 값 그대로 복사) 가지였다. 실패를 `err = ER_FAILED` 로
 * 적었고, 변환 헬퍼 없이 필드를 직접 복사했다.
 * 이 PR: 같은 계산의 단독 static 함수. 실패는 DOMAIN_INCOMPATIBLE 반환이고, 부르는 변환 헬퍼가 없어 date_conversion_error 는 건드리지
 * 않는다(시그니처만 맞춰 받는다).
 * 바뀐 것: case 가지 → 함수 추출(신설 4인자, 본문 전체가 추가분). 에러 표현만 ER_FAILED→DOMAIN_INCOMPATIBLE 로 바뀌었고 헬퍼 교체는 없다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_timestampltz_to_timestamp_strict (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  {
    DB_TIMESTAMP *ts = db_get_timestamp (src);

    /* copy timestamp value (UTC) */
    db_make_timestamp (target, *ts);
    return DOMAIN_COMPATIBLE;
  }

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_timestamptz_to_timestamp_strict — TIMESTAMPTZ 값을 TIMESTAMP 로 손실 없이 옮기는 변환기.
 * tp_value_coerce_strict 와 비교/피연산자 모드가 tp_value_find_converter 로 이 포인터를 받아 호출하고, target 에 값을 쓴 뒤
 * TP_DOMAIN_STATUS 를 돌려준다 — 행은 호출만 하고 타입 짝은 다시 풀지 않는다.
 * develop: develop 에 없음 — object_domain.c tp_value_coerce_strict 의 switch 안 `case
 * DB_TYPE_TIMESTAMP:`(develop:6655) 밑 `case DB_TYPE_TIMESTAMPTZ:`(UTC 값 그대로 복사) 가지였다. 실패를 `err = ER_FAILED` 로
 * 적었고, 변환 헬퍼 없이 필드를 직접 복사했다.
 * 이 PR: 같은 계산의 단독 static 함수. 실패는 DOMAIN_INCOMPATIBLE 반환이고, 부르는 변환 헬퍼가 없어 date_conversion_error 는 건드리지
 * 않는다(시그니처만 맞춰 받는다).
 * 바뀐 것: case 가지 → 함수 추출(신설 4인자, 본문 전체가 추가분). 에러 표현만 ER_FAILED→DOMAIN_INCOMPATIBLE 로 바뀌었고 헬퍼 교체는 없다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_timestamptz_to_timestamp_strict (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  {
    DB_TIMESTAMPTZ *ts_tz = db_get_timestamptz (src);

    /* copy timestamp value (UTC) */
    db_make_timestamp (target, ts_tz->timestamp);
    return DOMAIN_COMPATIBLE;
  }

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_datetime_to_timestamp_strict — DATETIME 값을 TIMESTAMP 로 손실 없이 옮기는 변환기.
 * tp_value_coerce_strict 와 비교/피연산자 모드가 tp_value_find_converter 로 이 포인터를 받아 호출하고, target 에 값을 쓴 뒤
 * TP_DOMAIN_STATUS 를 돌려준다 — 행은 호출만 하고 타입 짝은 다시 풀지 않는다.
 * develop: develop 에 없음 — object_domain.c tp_value_coerce_strict 의 switch 안 `case
 * DB_TYPE_TIMESTAMP:`(develop:6655) 밑 `case DB_TYPE_DATETIME:` 가지였다. 실패를 `err = ER_FAILED` 로 적었고
 * db_timestamp_encode_ses() 를 썼다.
 * 이 PR: 같은 계산의 단독 static 함수. 실패는 DOMAIN_INCOMPATIBLE 반환이고, db_timestamp_encode_ses_core(...,error) 로 전역 에러 대신
 * date_conversion_error 에만 기록한다(발행은 호출자의 conversion_error.publish()).
 * 바뀐 것: case 가지 → 함수 추출(신설 4인자, 본문 전체가 추가분). ER_FAILED→DOMAIN_INCOMPATIBLE, 헬퍼를
 * db_timestamp_encode_ses_core(...,error) 로 교체.
 */
static TP_DOMAIN_STATUS
tp_value_convert_datetime_to_timestamp_strict (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  {
    DB_DATETIME dt = *db_get_datetime (src);
    DB_DATE date = dt.date;
    DB_TIME time = dt.time / 1000;
    DB_TIMESTAMP ts = 0;

    if (db_timestamp_encode_ses_core (&date, &time, &ts, NULL, error) != NO_ERROR)
      {
	return DOMAIN_INCOMPATIBLE;
      }
    db_make_timestamp (target, ts);
    return DOMAIN_COMPATIBLE;
  }

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_datetimeltz_to_timestamp_strict — DATETIMELTZ 값을 TIMESTAMP 로 손실 없이 옮기는 변환기.
 * tp_value_coerce_strict 와 비교/피연산자 모드가 tp_value_find_converter 로 이 포인터를 받아 호출하고, target 에 값을 쓴 뒤
 * TP_DOMAIN_STATUS 를 돌려준다 — 행은 호출만 하고 타입 짝은 다시 풀지 않는다.
 * develop: develop 에 없음 — object_domain.c tp_value_coerce_strict 의 switch 안 `case
 * DB_TYPE_TIMESTAMP:`(develop:6655) 밑 `case DB_TYPE_DATETIMELTZ:` 가지였다. 실패를 `err = ER_FAILED` 로 적었고
 * db_timestamp_encode_utc() 를 썼다.
 * 이 PR: 같은 계산의 단독 static 함수. 실패는 DOMAIN_INCOMPATIBLE 반환이고, db_timestamp_encode_utc_core(...,error) 로 전역 에러 대신
 * date_conversion_error 에만 기록한다(발행은 호출자의 conversion_error.publish()).
 * 바뀐 것: case 가지 → 함수 추출(신설 4인자, 본문 전체가 추가분). ER_FAILED→DOMAIN_INCOMPATIBLE, 헬퍼를
 * db_timestamp_encode_utc_core(...,error) 로 교체.
 */
static TP_DOMAIN_STATUS
tp_value_convert_datetimeltz_to_timestamp_strict (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  {
    DB_DATETIME dt = *db_get_datetime (src);
    DB_DATE date = dt.date;
    DB_TIME time = dt.time / 1000;
    DB_TIMESTAMP ts = 0;

    if (db_timestamp_encode_utc_core (&date, &time, &ts, error) != NO_ERROR)
      {
	return DOMAIN_INCOMPATIBLE;
      }
    db_make_timestamp (target, ts);
    return DOMAIN_COMPATIBLE;
  }

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_datetimetz_to_timestamp_strict — DATETIMETZ 값을 TIMESTAMP 로 손실 없이 옮기는 변환기.
 * tp_value_coerce_strict 와 비교/피연산자 모드가 tp_value_find_converter 로 이 포인터를 받아 호출하고, target 에 값을 쓴 뒤
 * TP_DOMAIN_STATUS 를 돌려준다 — 행은 호출만 하고 타입 짝은 다시 풀지 않는다.
 * develop: develop 에 없음 — object_domain.c tp_value_coerce_strict 의 switch 안 `case
 * DB_TYPE_TIMESTAMP:`(develop:6655) 밑 `case DB_TYPE_DATETIMETZ:` 가지였다. 실패를 `err = ER_FAILED` 로 적었고
 * db_timestamp_encode_utc() 를 썼다.
 * 이 PR: 같은 계산의 단독 static 함수. 실패는 DOMAIN_INCOMPATIBLE 반환이고, db_timestamp_encode_utc_core(...,error) 로 전역 에러 대신
 * date_conversion_error 에만 기록한다(발행은 호출자의 conversion_error.publish()).
 * 바뀐 것: case 가지 → 함수 추출(신설 4인자, 본문 전체가 추가분). ER_FAILED→DOMAIN_INCOMPATIBLE, 헬퍼를
 * db_timestamp_encode_utc_core(...,error) 로 교체.
 */
static TP_DOMAIN_STATUS
tp_value_convert_datetimetz_to_timestamp_strict (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  {
    DB_DATETIMETZ *dt_tz = db_get_datetimetz (src);
    DB_DATE date = dt_tz->datetime.date;
    DB_TIME time = dt_tz->datetime.time / 1000;
    DB_TIMESTAMP ts = 0;

    if (db_timestamp_encode_utc_core (&date, &time, &ts, error) != NO_ERROR)
      {
	return DOMAIN_INCOMPATIBLE;
      }
    db_make_timestamp (target, ts);
    return DOMAIN_COMPATIBLE;
  }

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_char_to_timestampltz_strict — CHAR/VARCHAR 값을 TIMESTAMPLTZ 로 손실 없이 옮기는 변환기.
 * tp_value_coerce_strict 와 비교/피연산자 모드가 tp_value_find_converter 로 이 포인터를 받아 호출하고, target 에 값을 쓴 뒤
 * TP_DOMAIN_STATUS 를 돌려준다 — 행은 호출만 하고 타입 짝은 다시 풀지 않는다.
 * develop: develop 에 없음 — object_domain.c tp_value_coerce_strict 의 switch 안 `case
 * DB_TYPE_TIMESTAMPLTZ:`(develop:6758) 밑 `case DB_TYPE_VARCHAR:/CHAR:` 가지였다. 실패를 `err = ER_FAILED` 로 적었고
 * tp_atotimestamptz() 를 썼다.
 * 이 PR: 같은 계산의 단독 static 함수. 실패는 DOMAIN_INCOMPATIBLE 반환이고, tp_atotimestamptz_core(src,&ts_tz,error) 로 전역 에러 대신
 * date_conversion_error 에만 기록한다(발행은 호출자의 conversion_error.publish()).
 * 바뀐 것: case 가지 → 함수 추출(신설 4인자, 본문 전체가 추가분). ER_FAILED→DOMAIN_INCOMPATIBLE, 헬퍼를
 * tp_atotimestamptz_core(src,&ts_tz,error) 로 교체.
 */
static TP_DOMAIN_STATUS
tp_value_convert_char_to_timestampltz_strict (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  {
    DB_TIMESTAMPTZ ts_tz = { 0, 0 };

    if (tp_atotimestamptz_core (src, &ts_tz, error) != NO_ERROR)
      {
	return DOMAIN_INCOMPATIBLE;
      }
    db_make_timestampltz (target, ts_tz.timestamp);
    return DOMAIN_COMPATIBLE;
  }

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_date_to_timestampltz_strict — DATE 값을 TIMESTAMPLTZ 로 손실 없이 옮기는 변환기.
 * tp_value_coerce_strict 와 비교/피연산자 모드가 tp_value_find_converter 로 이 포인터를 받아 호출하고, target 에 값을 쓴 뒤
 * TP_DOMAIN_STATUS 를 돌려준다 — 행은 호출만 하고 타입 짝은 다시 풀지 않는다.
 * develop: develop 에 없음 — object_domain.c tp_value_coerce_strict 의 switch 안 `case
 * DB_TYPE_TIMESTAMPLTZ:`(develop:6758) 밑 `case DB_TYPE_DATE:` 가지였다. 실패를 `err = ER_FAILED` 로 적었고
 * db_time_encode() + db_timestamp_encode_ses() 를 썼다.
 * 이 PR: 같은 계산의 단독 static 함수. 실패는 DOMAIN_INCOMPATIBLE 반환이고,
 * db_time_encode_core/db_timestamp_encode_ses_core(...,error) 로 전역 에러 대신 date_conversion_error 에만 기록한다(발행은
 * 호출자의 conversion_error.publish()).
 * 바뀐 것: case 가지 → 함수 추출(신설 4인자, 본문 전체가 추가분). ER_FAILED→DOMAIN_INCOMPATIBLE, 헬퍼를
 * db_time_encode_core/db_timestamp_encode_ses_core(...,error) 로 교체.
 */
static TP_DOMAIN_STATUS
tp_value_convert_date_to_timestampltz_strict (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  {
    DB_TIME tm = 0;
    DB_DATE date = *db_get_date (src);
    DB_TIMESTAMP ts = 0;

    db_time_encode_core (&tm, 0, 0, 0, error);
    if (db_timestamp_encode_ses_core (&date, &tm, &ts, NULL, error) != NO_ERROR)
      {
	return DOMAIN_INCOMPATIBLE;
      }
    db_make_timestampltz (target, ts);
    return DOMAIN_COMPATIBLE;
  }

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_timestamp_to_timestampltz_strict — TIMESTAMP(및 TIMESTAMPLTZ) 값을 TIMESTAMPLTZ 로 손실 없이
 * 옮기는 변환기. tp_value_coerce_strict 와 비교/피연산자 모드가 tp_value_find_converter 로 이 포인터를 받아 호출하고, target 에 값을 쓴 뒤
 * TP_DOMAIN_STATUS 를 돌려준다 — 행은 호출만 하고 타입 짝은 다시 풀지 않는다.
 * develop: develop 에 없음 — object_domain.c tp_value_coerce_strict 의 switch 안 `case
 * DB_TYPE_TIMESTAMPLTZ:`(develop:6758) 밑 `case DB_TYPE_TIMESTAMP:`(UTC 값 그대로 복사) 가지였다. 실패를 `err = ER_FAILED` 로
 * 적었고, 변환 헬퍼 없이 필드를 직접 복사했다.
 * 이 PR: 같은 계산의 단독 static 함수. 실패는 DOMAIN_INCOMPATIBLE 반환이고, 부르는 변환 헬퍼가 없어 date_conversion_error 는 건드리지
 * 않는다(시그니처만 맞춰 받는다).
 * 바뀐 것: case 가지 → 함수 추출(신설 4인자, 본문 전체가 추가분). 에러 표현만 ER_FAILED→DOMAIN_INCOMPATIBLE 로 바뀌었고 헬퍼 교체는 없다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_timestamp_to_timestampltz_strict (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  {
    DB_TIMESTAMP *ts = db_get_timestamp (src);

    /* copy val timestamp value (UTC) */
    db_make_timestampltz (target, *ts);
    return DOMAIN_COMPATIBLE;
  }

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_timestamptz_to_timestampltz_strict — TIMESTAMPTZ 값을 TIMESTAMPLTZ 로 손실 없이 옮기는 변환기.
 * tp_value_coerce_strict 와 비교/피연산자 모드가 tp_value_find_converter 로 이 포인터를 받아 호출하고, target 에 값을 쓴 뒤
 * TP_DOMAIN_STATUS 를 돌려준다 — 행은 호출만 하고 타입 짝은 다시 풀지 않는다.
 * develop: develop 에 없음 — object_domain.c tp_value_coerce_strict 의 switch 안 `case
 * DB_TYPE_TIMESTAMPLTZ:`(develop:6758) 밑 `case DB_TYPE_TIMESTAMPTZ:`(UTC 값 그대로 복사) 가지였다. 실패를 `err = ER_FAILED`
 * 로 적었고, 변환 헬퍼 없이 필드를 직접 복사했다.
 * 이 PR: 같은 계산의 단독 static 함수. 실패는 DOMAIN_INCOMPATIBLE 반환이고, 부르는 변환 헬퍼가 없어 date_conversion_error 는 건드리지
 * 않는다(시그니처만 맞춰 받는다).
 * 바뀐 것: case 가지 → 함수 추출(신설 4인자, 본문 전체가 추가분). 에러 표현만 ER_FAILED→DOMAIN_INCOMPATIBLE 로 바뀌었고 헬퍼 교체는 없다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_timestamptz_to_timestampltz_strict (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain,
    date_conversion_error *error)
{
  {
    DB_TIMESTAMPTZ *ts_tz = db_get_timestamptz (src);

    /* copy val timestamp value (UTC) */
    db_make_timestampltz (target, ts_tz->timestamp);
    return DOMAIN_COMPATIBLE;
  }

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_datetime_to_timestampltz_strict — DATETIME 값을 TIMESTAMPLTZ 로 손실 없이 옮기는 변환기.
 * tp_value_coerce_strict 와 비교/피연산자 모드가 tp_value_find_converter 로 이 포인터를 받아 호출하고, target 에 값을 쓴 뒤
 * TP_DOMAIN_STATUS 를 돌려준다 — 행은 호출만 하고 타입 짝은 다시 풀지 않는다.
 * develop: develop 에 없음 — object_domain.c tp_value_coerce_strict 의 switch 안 `case
 * DB_TYPE_TIMESTAMPLTZ:`(develop:6758) 밑 `case DB_TYPE_DATETIME:` 가지였다. 실패를 `err = ER_FAILED` 로 적었고
 * db_timestamp_encode_ses() 를 썼다.
 * 이 PR: 같은 계산의 단독 static 함수. 실패는 DOMAIN_INCOMPATIBLE 반환이고, db_timestamp_encode_ses_core(...,error) 로 전역 에러 대신
 * date_conversion_error 에만 기록한다(발행은 호출자의 conversion_error.publish()).
 * 바뀐 것: case 가지 → 함수 추출(신설 4인자, 본문 전체가 추가분). ER_FAILED→DOMAIN_INCOMPATIBLE, 헬퍼를
 * db_timestamp_encode_ses_core(...,error) 로 교체.
 */
static TP_DOMAIN_STATUS
tp_value_convert_datetime_to_timestampltz_strict (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  {
    DB_DATETIME dt = *db_get_datetime (src);
    DB_DATE date = dt.date;
    DB_TIME time = dt.time / 1000;
    DB_TIMESTAMP ts = 0;

    if (db_timestamp_encode_ses_core (&date, &time, &ts, NULL, error) != NO_ERROR)
      {
	return DOMAIN_INCOMPATIBLE;
      }
    db_make_timestampltz (target, ts);
    return DOMAIN_COMPATIBLE;
  }

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_datetimeltz_to_timestampltz_strict — DATETIMELTZ 값을 TIMESTAMPLTZ 로 손실 없이 옮기는 변환기.
 * tp_value_coerce_strict 와 비교/피연산자 모드가 tp_value_find_converter 로 이 포인터를 받아 호출하고, target 에 값을 쓴 뒤
 * TP_DOMAIN_STATUS 를 돌려준다 — 행은 호출만 하고 타입 짝은 다시 풀지 않는다.
 * develop: develop 에 없음 — object_domain.c tp_value_coerce_strict 의 switch 안 `case
 * DB_TYPE_TIMESTAMPLTZ:`(develop:6758) 밑 `case DB_TYPE_DATETIMELTZ:` 가지였다. 실패를 `err = ER_FAILED` 로 적었고
 * db_timestamp_encode_utc() 를 썼다.
 * 이 PR: 같은 계산의 단독 static 함수. 실패는 DOMAIN_INCOMPATIBLE 반환이고, db_timestamp_encode_utc_core(...,error) 로 전역 에러 대신
 * date_conversion_error 에만 기록한다(발행은 호출자의 conversion_error.publish()).
 * 바뀐 것: case 가지 → 함수 추출(신설 4인자, 본문 전체가 추가분). ER_FAILED→DOMAIN_INCOMPATIBLE, 헬퍼를
 * db_timestamp_encode_utc_core(...,error) 로 교체.
 */
static TP_DOMAIN_STATUS
tp_value_convert_datetimeltz_to_timestampltz_strict (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain,
    date_conversion_error *error)
{
  {
    DB_DATETIME dt = *db_get_datetime (src);
    DB_DATE date = dt.date;
    DB_TIME time = dt.time / 1000;
    DB_TIMESTAMP ts = 0;

    if (db_timestamp_encode_utc_core (&date, &time, &ts, error) != NO_ERROR)
      {
	return DOMAIN_INCOMPATIBLE;
      }
    db_make_timestampltz (target, ts);
    return DOMAIN_COMPATIBLE;
  }

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_datetimetz_to_timestampltz_strict — DATETIMETZ 값을 TIMESTAMPLTZ 로 손실 없이 옮기는 변환기.
 * tp_value_coerce_strict 와 비교/피연산자 모드가 tp_value_find_converter 로 이 포인터를 받아 호출하고, target 에 값을 쓴 뒤
 * TP_DOMAIN_STATUS 를 돌려준다 — 행은 호출만 하고 타입 짝은 다시 풀지 않는다.
 * develop: develop 에 없음 — object_domain.c tp_value_coerce_strict 의 switch 안 `case
 * DB_TYPE_TIMESTAMPLTZ:`(develop:6758) 밑 `case DB_TYPE_DATETIMETZ:` 가지였다. 실패를 `err = ER_FAILED` 로 적었고
 * db_timestamp_encode_utc() 를 썼다.
 * 이 PR: 같은 계산의 단독 static 함수. 실패는 DOMAIN_INCOMPATIBLE 반환이고, db_timestamp_encode_utc_core(...,error) 로 전역 에러 대신
 * date_conversion_error 에만 기록한다(발행은 호출자의 conversion_error.publish()).
 * 바뀐 것: case 가지 → 함수 추출(신설 4인자, 본문 전체가 추가분). ER_FAILED→DOMAIN_INCOMPATIBLE, 헬퍼를
 * db_timestamp_encode_utc_core(...,error) 로 교체.
 */
static TP_DOMAIN_STATUS
tp_value_convert_datetimetz_to_timestampltz_strict (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain,
    date_conversion_error *error)
{
  {
    DB_DATETIMETZ *dt_tz = db_get_datetimetz (src);
    DB_DATE date = dt_tz->datetime.date;
    DB_TIME time = dt_tz->datetime.time / 1000;
    DB_TIMESTAMP ts = 0;

    if (db_timestamp_encode_utc_core (&date, &time, &ts, error) != NO_ERROR)
      {
	return DOMAIN_INCOMPATIBLE;
      }
    db_make_timestampltz (target, ts);
    return DOMAIN_COMPATIBLE;
  }

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_char_to_timestamptz_strict — CHAR/VARCHAR 값을 TIMESTAMPTZ 로 손실 없이 옮기는 변환기.
 * tp_value_coerce_strict 와 비교/피연산자 모드가 tp_value_find_converter 로 이 포인터를 받아 호출하고, target 에 값을 쓴 뒤
 * TP_DOMAIN_STATUS 를 돌려준다 — 행은 호출만 하고 타입 짝은 다시 풀지 않는다.
 * develop: develop 에 없음 — object_domain.c tp_value_coerce_strict 의 switch 안 `case
 * DB_TYPE_TIMESTAMPTZ:`(develop:6861) 밑 `case DB_TYPE_VARCHAR:/CHAR:` 가지였다. 실패를 `err = ER_FAILED` 로 적었고
 * tp_atotimestamptz() 를 썼다.
 * 이 PR: 같은 계산의 단독 static 함수. 실패는 DOMAIN_INCOMPATIBLE 반환이고, tp_atotimestamptz_core(src,&ts_tz,error) 로 전역 에러 대신
 * date_conversion_error 에만 기록한다(발행은 호출자의 conversion_error.publish()).
 * 바뀐 것: case 가지 → 함수 추출(신설 4인자, 본문 전체가 추가분). ER_FAILED→DOMAIN_INCOMPATIBLE, 헬퍼를
 * tp_atotimestamptz_core(src,&ts_tz,error) 로 교체.
 */
static TP_DOMAIN_STATUS
tp_value_convert_char_to_timestamptz_strict (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  {
    DB_TIMESTAMPTZ ts_tz = { 0, 0 };

    if (tp_atotimestamptz_core (src, &ts_tz, error) != NO_ERROR)
      {
	return DOMAIN_INCOMPATIBLE;
      }
    db_make_timestamptz (target, &ts_tz);
    return DOMAIN_COMPATIBLE;
  }

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_date_to_timestamptz_strict — DATE 값을 TIMESTAMPTZ 로 손실 없이 옮기는 변환기.
 * tp_value_coerce_strict 와 비교/피연산자 모드가 tp_value_find_converter 로 이 포인터를 받아 호출하고, target 에 값을 쓴 뒤
 * TP_DOMAIN_STATUS 를 돌려준다 — 행은 호출만 하고 타입 짝은 다시 풀지 않는다.
 * develop: develop 에 없음 — object_domain.c tp_value_coerce_strict 의 switch 안 `case
 * DB_TYPE_TIMESTAMPTZ:`(develop:6861) 밑 `case DB_TYPE_DATE:` 가지였다. 실패를 `err = ER_FAILED` 로 적었고
 * db_time_encode() + db_timestamp_encode_ses() 를 썼다.
 * 이 PR: 같은 계산의 단독 static 함수. 실패는 DOMAIN_INCOMPATIBLE 반환이고,
 * db_time_encode_core/db_timestamp_encode_ses_core(...,&ts_tz.tz_id,error) 로 전역 에러 대신 date_conversion_error 에만
 * 기록한다(발행은 호출자의 conversion_error.publish()).
 * 바뀐 것: case 가지 → 함수 추출(신설 4인자, 본문 전체가 추가분). ER_FAILED→DOMAIN_INCOMPATIBLE, 헬퍼를
 * db_time_encode_core/db_timestamp_encode_ses_core(...,&ts_tz.tz_id,error) 로 교체.
 */
static TP_DOMAIN_STATUS
tp_value_convert_date_to_timestamptz_strict (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  {
    DB_TIMESTAMPTZ ts_tz = { 0, 0 };
    DB_TIME tm = 0;
    DB_DATE date = *db_get_date (src);

    db_time_encode_core (&tm, 0, 0, 0, error);
    if (db_timestamp_encode_ses_core (&date, &tm, &ts_tz.timestamp, &ts_tz.tz_id, error) != NO_ERROR)
      {
	return DOMAIN_INCOMPATIBLE;
      }
    db_make_timestamptz (target, &ts_tz);
    return DOMAIN_COMPATIBLE;
  }

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_timestamp_to_timestamptz_strict — TIMESTAMP(및 TIMESTAMPLTZ) 값을 TIMESTAMPTZ 로 손실 없이 옮기는
 * 변환기. tp_value_coerce_strict 와 비교/피연산자 모드가 tp_value_find_converter 로 이 포인터를 받아 호출하고, target 에 값을 쓴 뒤
 * TP_DOMAIN_STATUS 를 돌려준다 — 행은 호출만 하고 타입 짝은 다시 풀지 않는다.
 * develop: develop 에 없음 — object_domain.c tp_value_coerce_strict 의 switch 안 `case
 * DB_TYPE_TIMESTAMPTZ:`(develop:6861) 밑 `case DB_TYPE_TIMESTAMP:/TIMESTAMPLTZ:`(공유 가지) 가지였다. 실패를 `err =
 * ER_FAILED` 로 적었고 tz_create_session_tzid_for_timestamp() 를 썼다.
 * 이 PR: 같은 계산의 단독 static 함수. 실패는 DOMAIN_INCOMPATIBLE 반환이고,
 * tz_create_session_tzid_for_timestamp_core(...,error) 로 전역 에러 대신 date_conversion_error 에만 기록한다(발행은 호출자의
 * conversion_error.publish()).
 * 바뀐 것: case 가지 → 함수 추출(신설 4인자, 본문 전체가 추가분). ER_FAILED→DOMAIN_INCOMPATIBLE, 헬퍼를
 * tz_create_session_tzid_for_timestamp_core(...,error) 로 교체.
 */
static TP_DOMAIN_STATUS
tp_value_convert_timestamp_to_timestamptz_strict (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  int err = NO_ERROR;

  {
    DB_TIMESTAMPTZ ts_tz = { 0, 0 };

    ts_tz.timestamp = *db_get_timestamp (src);

    err = tz_create_session_tzid_for_timestamp_core (& (ts_tz.timestamp), & (ts_tz.tz_id), error);

    if (err != NO_ERROR)
      {
	return DOMAIN_INCOMPATIBLE;
      }
    db_make_timestamptz (target, &ts_tz);
    return err == NO_ERROR ? DOMAIN_COMPATIBLE : DOMAIN_INCOMPATIBLE;
  }

  return err == NO_ERROR ? DOMAIN_COMPATIBLE : DOMAIN_INCOMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_datetime_to_timestamptz_strict — DATETIME 값을 TIMESTAMPTZ 로 손실 없이 옮기는 변환기.
 * tp_value_coerce_strict 와 비교/피연산자 모드가 tp_value_find_converter 로 이 포인터를 받아 호출하고, target 에 값을 쓴 뒤
 * TP_DOMAIN_STATUS 를 돌려준다 — 행은 호출만 하고 타입 짝은 다시 풀지 않는다.
 * develop: develop 에 없음 — object_domain.c tp_value_coerce_strict 의 switch 안 `case
 * DB_TYPE_TIMESTAMPTZ:`(develop:6861) 밑 `case DB_TYPE_DATETIME:` 가지였다. 실패를 `err = ER_FAILED` 로 적었고
 * db_timestamp_encode_ses() 를 썼다.
 * 이 PR: 같은 계산의 단독 static 함수. 실패는 DOMAIN_INCOMPATIBLE 반환이고,
 * db_timestamp_encode_ses_core(...,&ts_tz.timestamp,&ts_tz.tz_id,error) 로 전역 에러 대신 date_conversion_error 에만
 * 기록한다(발행은 호출자의 conversion_error.publish()).
 * 바뀐 것: case 가지 → 함수 추출(신설 4인자, 본문 전체가 추가분). ER_FAILED→DOMAIN_INCOMPATIBLE, 헬퍼를
 * db_timestamp_encode_ses_core(...,&ts_tz.timestamp,&ts_tz.tz_id,error) 로 교체.
 */
static TP_DOMAIN_STATUS
tp_value_convert_datetime_to_timestamptz_strict (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  {
    DB_TIMESTAMPTZ ts_tz = { 0, 0 };
    DB_DATETIME dt = *db_get_datetime (src);
    DB_DATE date = dt.date;
    DB_TIME time = dt.time / 1000;

    if (db_timestamp_encode_ses_core (&date, &time, &ts_tz.timestamp, &ts_tz.tz_id, error) != NO_ERROR)
      {
	return DOMAIN_INCOMPATIBLE;
      }
    db_make_timestamptz (target, &ts_tz);
    return DOMAIN_COMPATIBLE;
  }

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_datetimeltz_to_timestamptz_strict — DATETIMELTZ 값을 TIMESTAMPTZ 로 손실 없이 옮기는 변환기.
 * tp_value_coerce_strict 와 비교/피연산자 모드가 tp_value_find_converter 로 이 포인터를 받아 호출하고, target 에 값을 쓴 뒤
 * TP_DOMAIN_STATUS 를 돌려준다 — 행은 호출만 하고 타입 짝은 다시 풀지 않는다.
 * develop: develop 에 없음 — object_domain.c tp_value_coerce_strict 의 switch 안 `case
 * DB_TYPE_TIMESTAMPTZ:`(develop:6861) 밑 `case DB_TYPE_DATETIMELTZ:` 가지였다. 실패를 `err = ER_FAILED` 로 적었고
 * db_timestamp_encode_utc() 를 썼다.
 * 이 PR: 같은 계산의 단독 static 함수. 실패는 DOMAIN_INCOMPATIBLE 반환이고, db_timestamp_encode_utc_core(...,error) 로 전역 에러 대신
 * date_conversion_error 에만 기록한다(발행은 호출자의 conversion_error.publish()). tz_id 는 develop 과 같이 tz_get_utc_tz_id()
 * 로 UTC 를 박는다.
 * 바뀐 것: case 가지 → 함수 추출(신설 4인자, 본문 전체가 추가분). ER_FAILED→DOMAIN_INCOMPATIBLE, 헬퍼를
 * db_timestamp_encode_utc_core(...,error) 로 교체.
 */
static TP_DOMAIN_STATUS
tp_value_convert_datetimeltz_to_timestamptz_strict (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain,
    date_conversion_error *error)
{
  {
    DB_TIMESTAMPTZ ts_tz = { 0, 0 };
    DB_DATETIME dt = *db_get_datetime (src);
    DB_DATE date = dt.date;
    DB_TIME time = dt.time / 1000;

    if (db_timestamp_encode_utc_core (&date, &time, &ts_tz.timestamp, error) != NO_ERROR)
      {
	return DOMAIN_INCOMPATIBLE;
      }
    ts_tz.tz_id = *tz_get_utc_tz_id ();
    db_make_timestamptz (target, &ts_tz);
    return DOMAIN_COMPATIBLE;
  }

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_datetimetz_to_timestamptz_strict — DATETIMETZ 값을 TIMESTAMPTZ 로 손실 없이 옮기는 변환기.
 * tp_value_coerce_strict 와 비교/피연산자 모드가 tp_value_find_converter 로 이 포인터를 받아 호출하고, target 에 값을 쓴 뒤
 * TP_DOMAIN_STATUS 를 돌려준다 — 행은 호출만 하고 타입 짝은 다시 풀지 않는다.
 * develop: develop 에 없음 — object_domain.c tp_value_coerce_strict 의 switch 안 `case
 * DB_TYPE_TIMESTAMPTZ:`(develop:6861) 밑 `case DB_TYPE_DATETIMETZ:` 가지였다. 실패를 `err = ER_FAILED` 로 적었고
 * db_timestamp_encode_utc() 를 썼다.
 * 이 PR: 같은 계산의 단독 static 함수. 실패는 DOMAIN_INCOMPATIBLE 반환이고, db_timestamp_encode_utc_core(...,error) 로 전역 에러 대신
 * date_conversion_error 에만 기록한다(발행은 호출자의 conversion_error.publish()). tz_id 는 원본 값의 것을 그대로 쓴다.
 * 바뀐 것: case 가지 → 함수 추출(신설 4인자, 본문 전체가 추가분). ER_FAILED→DOMAIN_INCOMPATIBLE, 헬퍼를
 * db_timestamp_encode_utc_core(...,error) 로 교체.
 */
static TP_DOMAIN_STATUS
tp_value_convert_datetimetz_to_timestamptz_strict (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  {
    DB_TIMESTAMPTZ ts_tz = { 0, 0 };
    DB_DATETIMETZ *dt_tz = db_get_datetimetz (src);
    DB_DATE date = dt_tz->datetime.date;
    DB_TIME time = dt_tz->datetime.time / 1000;

    if (db_timestamp_encode_utc_core (&date, &time, &ts_tz.timestamp, error) != NO_ERROR)
      {
	return DOMAIN_INCOMPATIBLE;
      }
    ts_tz.tz_id = dt_tz->tz_id;
    db_make_timestamptz (target, &ts_tz);
    return DOMAIN_COMPATIBLE;
  }

  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_incompatible — "이 타입 짝은 변환할 수 없다"를 뜻하는 널 오브젝트 변환기 — tp_value_find_converter 가 표에서 짝을 못
 * 찾거나 strict 모드에서 막는 짝일 때 이 포인터를 돌려주고, 호출자는 DOMAIN_INCOMPATIBLE 을 받는다.
 * develop: develop 에는 없음 — 이 PR 이 신설. develop 에서는 switch 의 `default: status = DOMAIN_INCOMPATIBLE;` 가 같은 일을
 * 했다.
 * 이 PR: 인자 이름 없는 5줄짜리 함수로 DOMAIN_INCOMPATIBLE 만 돌려준다. 덕분에 디스패치 표가 NULL 없이 항상 유효한 포인터를 돌려준다.
 * 바뀐 것: 신설(+5줄). switch 의 default 가 함수 포인터 값으로 바뀌었다 — 게이트가 "변환 불가"를 미리 알 수 있게 된 핵심 장치.
 */
static TP_DOMAIN_STATUS
tp_value_convert_incompatible (const DB_VALUE *, DB_VALUE *, const TP_DOMAIN *, date_conversion_error *)
{
  return DOMAIN_INCOMPATIBLE;
}

/*
 * [리뷰] tp_value_convert_json_validate — JSON→JSON(도메인만 다른 경우) 변환기 — desired_domain 의 json_validator 로 문서를 검증하고
 * 통과하면 값을 복제한다. tp_value_cast_internal 이 desired_type == original_type == JSON 인 매개변수화 도메인에서 직접 부른다.
 * develop: develop 에는 없음 — 이 PR 이 신설. develop 에서는 같은 자리에서 tp_value_cast_internal 의 `desired_type ==
 * original_type` + `is_parameterized` 분기가 JSON 을 따로 다루지 않고 아래 JSON 가지로 흘렸다.
 * 이 PR: json_validator 가 있으면 db_json_validate_doc 로 막고(DOMAIN_ERROR), 아니면 pr_clone_value 로 복제한다.
 * 바뀐 것: 신설(+15줄). 같은 타입 JSON 의 스키마 검증이 전용 변환기로 분리됐다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_json_validate (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				date_conversion_error *)
{
  if (desired_domain->json_validator != nullptr
      && db_json_validate_doc (desired_domain->json_validator, src->data.json.document) != NO_ERROR)
    {
      return DOMAIN_ERROR;
    }
  if (src != target)
    {
      pr_clone_value (src, target);
    }
  return DOMAIN_COMPATIBLE;
}

/*
 * [리뷰] tp_json_unwrap_scalar — JSON 문서가 스칼라(double/int/bigint/bool/string)면 그 값을 DB_VALUE 로 꺼내 주는 공용 헬퍼 — true
 * 면 꺼냈다는 뜻이고 false 면 스칼라가 아니라는 뜻이다. tp_value_cast_internal 과 tp_value_convert_json_scalar_to_* 가 모두 이것을 쓴다.
 * develop: develop 에는 독립 함수가 없다 — object_domain.c tp_value_cast_internal(develop:6992-10078) 의 머리
 * 부분(develop:7058-7097) "TODO this is very hackish" 블록이 같은 switch 를 인라인으로 갖고 있었고, bool 을 문자열로 쓸지는
 * `desired_type` 을 직접 보고 정했다.
 * 이 PR: 같은 switch 를 `bool_as_string` 인자로 외부화한 비정적(extern) 함수. 반환값이 use_replacement 플래그다.
 * 바뀐 것: 인라인 블록 → 공용 함수 추출(+43줄). desired_type 의존이 bool 인자로 바뀌어, 행 전에 결정하는 게이트 쪽에서도 같은 분해를 쓸 수 있게 됐다.
 */
bool
tp_json_unwrap_scalar (const DB_VALUE *src, bool bool_as_string, DB_VALUE *scalar)
{
  DB_JSON_TYPE json_type = db_json_get_type (db_get_json_document (src));
  JSON_DOC *src_doc = db_get_json_document (src);
  bool use_replacement = true;

  switch (json_type)
    {
    case DB_JSON_DOUBLE:
      db_make_double (scalar, db_json_get_double_from_document (src_doc));
      break;
    case DB_JSON_INT:
      db_make_int (scalar, db_json_get_int_from_document (src_doc));
      break;
    case DB_JSON_BIGINT:
      db_make_bigint (scalar, db_json_get_bigint_from_document (src_doc));
      break;
    case DB_JSON_BOOL:
      if (bool_as_string)
	{
	  db_make_string (scalar, db_json_get_bool_as_str_from_document (src_doc));
	  scalar->need_clear = true;

	}
      else
	{

	  db_make_int (scalar, db_json_get_bool_from_document (src_doc) ? 1 : 0);

	}
      break;
    case DB_JSON_STRING:
      db_make_string_copy (scalar, db_json_get_string_from_document (src_doc));
      break;
    default:
      use_replacement = false;
      /* do nothing */
      break;
    }

  return use_replacement;
}

/* A JSON scalar into a number (DST): the scalar's value converted in ASSIGN mode from its own type - a double,
 * an integer, a bigint, a boolean as an INTEGER, a string as a VARCHAR */
template <DB_TYPE DST>
/*
 * [리뷰] tp_value_convert_json_scalar_to_number — JSON 값을 수치 타입(DST 템플릿 인자) 로 바꾸는 변환기 — tp_json_unwrap_scalar 로
 * 스칼라를 꺼낸 뒤 꺼낸 타입에 맞는 변환기로 위임한다: DOUBLE/INT/BIGINT/BOOL/STRING 마다 tp_value_convert_number<해당 소스, DST, ASSIGN>
 * 로 넘긴다. 게이트가 src_type == DB_TYPE_JSON 일 때 고르는 자리다.
 * develop: develop 에는 없다 — object_domain.c tp_value_cast_internal(develop:6992-10078) 가 함수 머리에서 JSON 을 스칼라로
 * 바꿔치기(src_replacement)한 뒤 그냥 "바뀐 소스 타입"으로 아래 switch 를 돌렸다. 즉 JSON→수치 타입 이라는 짝 자체가 존재하지 않았고, 실제로 도는 가지는 언래핑 결과
 * 타입의 가지였다.
 * 이 PR: 언래핑과 위임을 한 함수 안에 담아, 소스 타입이 JSON 인 채로도 하나의 변환기 포인터를 고를 수 있게 했다. 꺼낸 임시 값은 pr_clear_value 로 정리한다.
 * 바뀐 것: 신설(+30~55줄). develop 의 "소스 값을 바꿔치기하고 다시 switch" 가 "JSON 짝 전용 변환기"로 바뀌었다 — 게이트가 행 전에 변환기를 못 박으려면 JSON 도
 * 하나의 짝이어야 하기 때문이다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_json_scalar_to_number (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
					date_conversion_error *error)
{
  DB_VALUE scalar;
  db_make_null (&scalar);
  if (!tp_json_unwrap_scalar (src, false, &scalar))
    {
      return DOMAIN_INCOMPATIBLE;
    }
  TP_DOMAIN_STATUS status = DOMAIN_INCOMPATIBLE;
  switch (db_json_get_type (db_get_json_document (src)))
    {
    case DB_JSON_DOUBLE:
      status =
	      tp_value_convert_number < DB_TYPE_DOUBLE, DST, DOMAIN_CONVERT_ASSIGN > (
		      &scalar, target,
		      desired_domain, error)
	      ;
      break;
    case DB_JSON_INT:
      status =
	      tp_value_convert_number < DB_TYPE_INTEGER, DST, DOMAIN_CONVERT_ASSIGN > (
		      &scalar, target,
		      desired_domain, error)
	      ;
      break;
    case DB_JSON_BIGINT:
      status =
	      tp_value_convert_number < DB_TYPE_BIGINT, DST, DOMAIN_CONVERT_ASSIGN > (
		      &scalar, target,
		      desired_domain, error)
	      ;
      break;
    case DB_JSON_BOOL:
      status =
	      tp_value_convert_number < DB_TYPE_INTEGER, DST, DOMAIN_CONVERT_ASSIGN > (
		      &scalar, target,
		      desired_domain, error)
	      ;
      break;
    case DB_JSON_STRING:
      status =
	      tp_value_convert_number < DB_TYPE_VARCHAR, DST, DOMAIN_CONVERT_ASSIGN > (
		      &scalar, target,
		      desired_domain, error)
	      ;
      break;
    default:
      break;
    }
  pr_clear_value (&scalar);
  return status;
}

/*
 * [리뷰] tp_value_convert_json_scalar_to_char — JSON 값을 CHAR 로 바꾸는 변환기 — tp_json_unwrap_scalar 로 스칼라를 꺼낸 뒤 꺼낸
 * 타입에 맞는 변환기로 위임한다: 스칼라가 아니면 tp_value_convert_json_to_char(문서 전체를 문자열로)로 넘기고, 스칼라면 타입별 *_to_char /
 * char_to_varchar 변환기를 부른다. 게이트가 src_type == DB_TYPE_JSON 일 때 고르는 자리다.
 * develop: develop 에는 없다 — object_domain.c tp_value_cast_internal(develop:6992-10078) 가 함수 머리에서 JSON 을 스칼라로
 * 바꿔치기(src_replacement)한 뒤 그냥 "바뀐 소스 타입"으로 아래 switch 를 돌렸다. 즉 JSON→CHAR 라는 짝 자체가 존재하지 않았고, 실제로 도는 가지는 언래핑 결과
 * 타입의 가지였다.
 * 이 PR: 언래핑과 위임을 한 함수 안에 담아, 소스 타입이 JSON 인 채로도 하나의 변환기 포인터를 고를 수 있게 했다. 꺼낸 임시 값은 pr_clear_value 로 정리한다.
 * 바뀐 것: 신설(+30~55줄). develop 의 "소스 값을 바꿔치기하고 다시 switch" 가 "JSON 짝 전용 변환기"로 바뀌었다 — 게이트가 행 전에 변환기를 못 박으려면 JSON 도
 * 하나의 짝이어야 하기 때문이다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_json_scalar_to_char (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				      date_conversion_error *error)
{
  DB_VALUE scalar;
  db_make_null (&scalar);
  if (!tp_json_unwrap_scalar (src, true, &scalar))
    {
      return tp_value_convert_json_to_char (src, target, desired_domain, error);
    }
  TP_DOMAIN_STATUS status = DOMAIN_INCOMPATIBLE;
  switch (db_json_get_type (db_get_json_document (src)))
    {
    case DB_JSON_DOUBLE:
      status = tp_value_convert_double_to_char (&scalar, target, desired_domain, error);
      break;
    case DB_JSON_INT:
      status = tp_value_convert_integer_to_char (&scalar, target, desired_domain, error);
      break;
    case DB_JSON_BIGINT:
      status = tp_value_convert_bigint_to_char (&scalar, target, desired_domain, error);
      break;
    case DB_JSON_BOOL:
      status = tp_value_convert_char_to_varchar (&scalar, target, desired_domain, error);
      break;
    case DB_JSON_STRING:
      status = tp_value_convert_char_to_varchar (&scalar, target, desired_domain, error);
      break;
    default:
      break;
    }
  pr_clear_value (&scalar);
  return status;
}

/*
 * [리뷰] tp_value_convert_json_scalar_to_varchar — JSON 값을 VARCHAR 로 바꾸는 변환기 — tp_json_unwrap_scalar 로 스칼라를 꺼낸 뒤
 * 꺼낸 타입에 맞는 변환기로 위임한다: 스칼라가 아니면 tp_value_convert_json_to_varchar 로 넘기고, 스칼라면 타입별 *_to_varchar 변환기를 부른다. 게이트가
 * src_type == DB_TYPE_JSON 일 때 고르는 자리다.
 * develop: develop 에는 없다 — object_domain.c tp_value_cast_internal(develop:6992-10078) 가 함수 머리에서 JSON 을 스칼라로
 * 바꿔치기(src_replacement)한 뒤 그냥 "바뀐 소스 타입"으로 아래 switch 를 돌렸다. 즉 JSON→VARCHAR 라는 짝 자체가 존재하지 않았고, 실제로 도는 가지는 언래핑
 * 결과 타입의 가지였다.
 * 이 PR: 언래핑과 위임을 한 함수 안에 담아, 소스 타입이 JSON 인 채로도 하나의 변환기 포인터를 고를 수 있게 했다. 꺼낸 임시 값은 pr_clear_value 로 정리한다.
 * 바뀐 것: 신설(+30~55줄). develop 의 "소스 값을 바꿔치기하고 다시 switch" 가 "JSON 짝 전용 변환기"로 바뀌었다 — 게이트가 행 전에 변환기를 못 박으려면 JSON 도
 * 하나의 짝이어야 하기 때문이다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_json_scalar_to_varchar (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
    date_conversion_error *error)
{
  DB_VALUE scalar;
  db_make_null (&scalar);
  if (!tp_json_unwrap_scalar (src, true, &scalar))
    {
      return tp_value_convert_json_to_varchar (src, target, desired_domain, error);
    }
  TP_DOMAIN_STATUS status = DOMAIN_INCOMPATIBLE;
  switch (db_json_get_type (db_get_json_document (src)))
    {
    case DB_JSON_DOUBLE:
      status = tp_value_convert_double_to_varchar (&scalar, target, desired_domain, error);
      break;
    case DB_JSON_INT:
      status = tp_value_convert_integer_to_varchar (&scalar, target, desired_domain, error);
      break;
    case DB_JSON_BIGINT:
      status = tp_value_convert_bigint_to_varchar (&scalar, target, desired_domain, error);
      break;
    case DB_JSON_BOOL:
      status = tp_value_convert_varchar_to_varchar (&scalar, target, desired_domain, error);
      break;
    case DB_JSON_STRING:
      status = tp_value_convert_varchar_to_varchar (&scalar, target, desired_domain, error);
      break;
    default:
      break;
    }
  pr_clear_value (&scalar);
  return status;
}

/*
 * [리뷰] tp_value_convert_json_scalar_to_date — JSON 값을 DATE 로 바꾸는 변환기 — tp_json_unwrap_scalar 로 스칼라를 꺼낸 뒤 꺼낸
 * 타입에 맞는 변환기로 위임한다: STRING 스칼라만 tp_value_convert_char_to_date 로 넘기고 숫자·불리언은 DOMAIN_INCOMPATIBLE 이다. 게이트가
 * src_type == DB_TYPE_JSON 일 때 고르는 자리다.
 * develop: develop 에는 없다 — object_domain.c tp_value_cast_internal(develop:6992-10078) 가 함수 머리에서 JSON 을 스칼라로
 * 바꿔치기(src_replacement)한 뒤 그냥 "바뀐 소스 타입"으로 아래 switch 를 돌렸다. 즉 JSON→DATE 라는 짝 자체가 존재하지 않았고, 실제로 도는 가지는 언래핑 결과
 * 타입의 가지였다.
 * 이 PR: 언래핑과 위임을 한 함수 안에 담아, 소스 타입이 JSON 인 채로도 하나의 변환기 포인터를 고를 수 있게 했다. 꺼낸 임시 값은 pr_clear_value 로 정리한다.
 * 바뀐 것: 신설(+30~55줄). develop 의 "소스 값을 바꿔치기하고 다시 switch" 가 "JSON 짝 전용 변환기"로 바뀌었다 — 게이트가 행 전에 변환기를 못 박으려면 JSON 도
 * 하나의 짝이어야 하기 때문이다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_json_scalar_to_date (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				      date_conversion_error *error)
{
  DB_VALUE scalar;
  db_make_null (&scalar);
  if (!tp_json_unwrap_scalar (src, false, &scalar))
    {
      return DOMAIN_INCOMPATIBLE;
    }
  TP_DOMAIN_STATUS status = DOMAIN_INCOMPATIBLE;
  switch (db_json_get_type (db_get_json_document (src)))
    {
    case DB_JSON_DOUBLE:
      break;
    case DB_JSON_INT:
      break;
    case DB_JSON_BIGINT:
      break;
    case DB_JSON_BOOL:
      break;
    case DB_JSON_STRING:
      status = tp_value_convert_char_to_date (&scalar, target, desired_domain, error);
      break;
    default:
      break;
    }
  pr_clear_value (&scalar);
  return status;
}

/*
 * [리뷰] tp_value_convert_json_scalar_to_time — JSON 값을 TIME 로 바꾸는 변환기 — tp_json_unwrap_scalar 로 스칼라를 꺼낸 뒤 꺼낸
 * 타입에 맞는 변환기로 위임한다: double/int/bigint/bool 은 *_to_time 수치 변환기로, string 은 char_to_time 으로 넘긴다. 게이트가 src_type ==
 * DB_TYPE_JSON 일 때 고르는 자리다.
 * develop: develop 에는 없다 — object_domain.c tp_value_cast_internal(develop:6992-10078) 가 함수 머리에서 JSON 을 스칼라로
 * 바꿔치기(src_replacement)한 뒤 그냥 "바뀐 소스 타입"으로 아래 switch 를 돌렸다. 즉 JSON→TIME 라는 짝 자체가 존재하지 않았고, 실제로 도는 가지는 언래핑 결과
 * 타입의 가지였다.
 * 이 PR: 언래핑과 위임을 한 함수 안에 담아, 소스 타입이 JSON 인 채로도 하나의 변환기 포인터를 고를 수 있게 했다. 꺼낸 임시 값은 pr_clear_value 로 정리한다.
 * 바뀐 것: 신설(+30~55줄). develop 의 "소스 값을 바꿔치기하고 다시 switch" 가 "JSON 짝 전용 변환기"로 바뀌었다 — 게이트가 행 전에 변환기를 못 박으려면 JSON 도
 * 하나의 짝이어야 하기 때문이다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_json_scalar_to_time (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				      date_conversion_error *error)
{
  DB_VALUE scalar;
  db_make_null (&scalar);
  if (!tp_json_unwrap_scalar (src, false, &scalar))
    {
      return DOMAIN_INCOMPATIBLE;
    }
  TP_DOMAIN_STATUS status = DOMAIN_INCOMPATIBLE;
  switch (db_json_get_type (db_get_json_document (src)))
    {
    case DB_JSON_DOUBLE:
      status = tp_value_convert_double_to_time (&scalar, target, desired_domain, error);
      break;
    case DB_JSON_INT:
      status = tp_value_convert_integer_to_time (&scalar, target, desired_domain, error);
      break;
    case DB_JSON_BIGINT:
      status = tp_value_convert_bigint_to_time (&scalar, target, desired_domain, error);
      break;
    case DB_JSON_BOOL:
      status = tp_value_convert_integer_to_time (&scalar, target, desired_domain, error);
      break;
    case DB_JSON_STRING:
      status = tp_value_convert_char_to_time (&scalar, target, desired_domain, error);
      break;
    default:
      break;
    }
  pr_clear_value (&scalar);
  return status;
}

/*
 * [리뷰] tp_value_convert_json_scalar_to_timestamp — JSON 값을 TIMESTAMP 로 바꾸는 변환기 — tp_json_unwrap_scalar 로 스칼라를
 * 꺼낸 뒤 꺼낸 타입에 맞는 변환기로 위임한다: 수치는 tp_value_convert_number_to_timestamp<소스, TIMESTAMP>, string 은
 * char_to_timestamp 로 넘긴다. 게이트가 src_type == DB_TYPE_JSON 일 때 고르는 자리다.
 * develop: develop 에는 없다 — object_domain.c tp_value_cast_internal(develop:6992-10078) 가 함수 머리에서 JSON 을 스칼라로
 * 바꿔치기(src_replacement)한 뒤 그냥 "바뀐 소스 타입"으로 아래 switch 를 돌렸다. 즉 JSON→TIMESTAMP 라는 짝 자체가 존재하지 않았고, 실제로 도는 가지는 언래핑
 * 결과 타입의 가지였다.
 * 이 PR: 언래핑과 위임을 한 함수 안에 담아, 소스 타입이 JSON 인 채로도 하나의 변환기 포인터를 고를 수 있게 했다. 꺼낸 임시 값은 pr_clear_value 로 정리한다.
 * 바뀐 것: 신설(+30~55줄). develop 의 "소스 값을 바꿔치기하고 다시 switch" 가 "JSON 짝 전용 변환기"로 바뀌었다 — 게이트가 행 전에 변환기를 못 박으려면 JSON 도
 * 하나의 짝이어야 하기 때문이다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_json_scalar_to_timestamp (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  DB_VALUE scalar;
  db_make_null (&scalar);
  if (!tp_json_unwrap_scalar (src, false, &scalar))
    {
      return DOMAIN_INCOMPATIBLE;
    }
  TP_DOMAIN_STATUS status = DOMAIN_INCOMPATIBLE;
  switch (db_json_get_type (db_get_json_document (src)))
    {
    case DB_JSON_DOUBLE:
      status = tp_value_convert_number_to_timestamp<DB_TYPE_DOUBLE, DB_TYPE_TIMESTAMP> (&scalar, target, desired_domain,
	       error);
      break;
    case DB_JSON_INT:
      status = tp_value_convert_number_to_timestamp<DB_TYPE_INTEGER, DB_TYPE_TIMESTAMP> (&scalar, target, desired_domain,
	       error);
      break;
    case DB_JSON_BIGINT:
      status = tp_value_convert_number_to_timestamp<DB_TYPE_BIGINT, DB_TYPE_TIMESTAMP> (&scalar, target, desired_domain,
	       error);
      break;
    case DB_JSON_BOOL:
      status = tp_value_convert_number_to_timestamp<DB_TYPE_INTEGER, DB_TYPE_TIMESTAMP> (&scalar, target, desired_domain,
	       error);
      break;
    case DB_JSON_STRING:
      status = tp_value_convert_char_to_timestamp (&scalar, target, desired_domain, error);
      break;
    default:
      break;
    }
  pr_clear_value (&scalar);
  return status;
}

/*
 * [리뷰] tp_value_convert_json_scalar_to_timestampltz — JSON 값을 TIMESTAMPLTZ 로 바꾸는 변환기 — tp_json_unwrap_scalar 로
 * 스칼라를 꺼낸 뒤 꺼낸 타입에 맞는 변환기로 위임한다: 수치는 number_to_timestamp<소스, TIMESTAMPLTZ>, string 은 char_to_timestampltz 로
 * 넘긴다. 게이트가 src_type == DB_TYPE_JSON 일 때 고르는 자리다.
 * develop: develop 에는 없다 — object_domain.c tp_value_cast_internal(develop:6992-10078) 가 함수 머리에서 JSON 을 스칼라로
 * 바꿔치기(src_replacement)한 뒤 그냥 "바뀐 소스 타입"으로 아래 switch 를 돌렸다. 즉 JSON→TIMESTAMPLTZ 라는 짝 자체가 존재하지 않았고, 실제로 도는 가지는
 * 언래핑 결과 타입의 가지였다.
 * 이 PR: 언래핑과 위임을 한 함수 안에 담아, 소스 타입이 JSON 인 채로도 하나의 변환기 포인터를 고를 수 있게 했다. 꺼낸 임시 값은 pr_clear_value 로 정리한다.
 * 바뀐 것: 신설(+30~55줄). develop 의 "소스 값을 바꿔치기하고 다시 switch" 가 "JSON 짝 전용 변환기"로 바뀌었다 — 게이트가 행 전에 변환기를 못 박으려면 JSON 도
 * 하나의 짝이어야 하기 때문이다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_json_scalar_to_timestampltz (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  DB_VALUE scalar;
  db_make_null (&scalar);
  if (!tp_json_unwrap_scalar (src, false, &scalar))
    {
      return DOMAIN_INCOMPATIBLE;
    }
  TP_DOMAIN_STATUS status = DOMAIN_INCOMPATIBLE;
  switch (db_json_get_type (db_get_json_document (src)))
    {
    case DB_JSON_DOUBLE:
      status = tp_value_convert_number_to_timestamp<DB_TYPE_DOUBLE, DB_TYPE_TIMESTAMPLTZ> (&scalar, target, desired_domain,
	       error);
      break;
    case DB_JSON_INT:
      status = tp_value_convert_number_to_timestamp<DB_TYPE_INTEGER, DB_TYPE_TIMESTAMPLTZ> (&scalar, target, desired_domain,
	       error);
      break;
    case DB_JSON_BIGINT:
      status = tp_value_convert_number_to_timestamp<DB_TYPE_BIGINT, DB_TYPE_TIMESTAMPLTZ> (&scalar, target, desired_domain,
	       error);
      break;
    case DB_JSON_BOOL:
      status = tp_value_convert_number_to_timestamp<DB_TYPE_INTEGER, DB_TYPE_TIMESTAMPLTZ> (&scalar, target, desired_domain,
	       error);
      break;
    case DB_JSON_STRING:
      status = tp_value_convert_char_to_timestampltz (&scalar, target, desired_domain, error);
      break;
    default:
      break;
    }
  pr_clear_value (&scalar);
  return status;
}

/*
 * [리뷰] tp_value_convert_json_scalar_to_timestamptz — JSON 값을 TIMESTAMPTZ 로 바꾸는 변환기 — tp_json_unwrap_scalar 로
 * 스칼라를 꺼낸 뒤 꺼낸 타입에 맞는 변환기로 위임한다: 수치는 number_to_timestamp<소스, TIMESTAMPTZ>, string 은 char_to_timestamptz 로 넘긴다.
 * 게이트가 src_type == DB_TYPE_JSON 일 때 고르는 자리다.
 * develop: develop 에는 없다 — object_domain.c tp_value_cast_internal(develop:6992-10078) 가 함수 머리에서 JSON 을 스칼라로
 * 바꿔치기(src_replacement)한 뒤 그냥 "바뀐 소스 타입"으로 아래 switch 를 돌렸다. 즉 JSON→TIMESTAMPTZ 라는 짝 자체가 존재하지 않았고, 실제로 도는 가지는
 * 언래핑 결과 타입의 가지였다.
 * 이 PR: 언래핑과 위임을 한 함수 안에 담아, 소스 타입이 JSON 인 채로도 하나의 변환기 포인터를 고를 수 있게 했다. 꺼낸 임시 값은 pr_clear_value 로 정리한다.
 * 바뀐 것: 신설(+30~55줄). develop 의 "소스 값을 바꿔치기하고 다시 switch" 가 "JSON 짝 전용 변환기"로 바뀌었다 — 게이트가 행 전에 변환기를 못 박으려면 JSON 도
 * 하나의 짝이어야 하기 때문이다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_json_scalar_to_timestamptz (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  DB_VALUE scalar;
  db_make_null (&scalar);
  if (!tp_json_unwrap_scalar (src, false, &scalar))
    {
      return DOMAIN_INCOMPATIBLE;
    }
  TP_DOMAIN_STATUS status = DOMAIN_INCOMPATIBLE;
  switch (db_json_get_type (db_get_json_document (src)))
    {
    case DB_JSON_DOUBLE:
      status = tp_value_convert_number_to_timestamp<DB_TYPE_DOUBLE, DB_TYPE_TIMESTAMPTZ> (&scalar, target, desired_domain,
	       error);
      break;
    case DB_JSON_INT:
      status = tp_value_convert_number_to_timestamp<DB_TYPE_INTEGER, DB_TYPE_TIMESTAMPTZ> (&scalar, target, desired_domain,
	       error);
      break;
    case DB_JSON_BIGINT:
      status = tp_value_convert_number_to_timestamp<DB_TYPE_BIGINT, DB_TYPE_TIMESTAMPTZ> (&scalar, target, desired_domain,
	       error);
      break;
    case DB_JSON_BOOL:
      status = tp_value_convert_number_to_timestamp<DB_TYPE_INTEGER, DB_TYPE_TIMESTAMPTZ> (&scalar, target, desired_domain,
	       error);
      break;
    case DB_JSON_STRING:
      status = tp_value_convert_char_to_timestamptz (&scalar, target, desired_domain, error);
      break;
    default:
      break;
    }
  pr_clear_value (&scalar);
  return status;
}

/*
 * [리뷰] tp_value_convert_json_scalar_to_datetime — JSON 값을 DATETIME 로 바꾸는 변환기 — tp_json_unwrap_scalar 로 스칼라를 꺼낸
 * 뒤 꺼낸 타입에 맞는 변환기로 위임한다: STRING 스칼라만 char_to_datetime 으로 넘기고 나머지는 DOMAIN_INCOMPATIBLE 이다. 게이트가 src_type ==
 * DB_TYPE_JSON 일 때 고르는 자리다.
 * develop: develop 에는 없다 — object_domain.c tp_value_cast_internal(develop:6992-10078) 가 함수 머리에서 JSON 을 스칼라로
 * 바꿔치기(src_replacement)한 뒤 그냥 "바뀐 소스 타입"으로 아래 switch 를 돌렸다. 즉 JSON→DATETIME 라는 짝 자체가 존재하지 않았고, 실제로 도는 가지는 언래핑
 * 결과 타입의 가지였다.
 * 이 PR: 언래핑과 위임을 한 함수 안에 담아, 소스 타입이 JSON 인 채로도 하나의 변환기 포인터를 고를 수 있게 했다. 꺼낸 임시 값은 pr_clear_value 로 정리한다.
 * 바뀐 것: 신설(+30~55줄). develop 의 "소스 값을 바꿔치기하고 다시 switch" 가 "JSON 짝 전용 변환기"로 바뀌었다 — 게이트가 행 전에 변환기를 못 박으려면 JSON 도
 * 하나의 짝이어야 하기 때문이다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_json_scalar_to_datetime (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  DB_VALUE scalar;
  db_make_null (&scalar);
  if (!tp_json_unwrap_scalar (src, false, &scalar))
    {
      return DOMAIN_INCOMPATIBLE;
    }
  TP_DOMAIN_STATUS status = DOMAIN_INCOMPATIBLE;
  switch (db_json_get_type (db_get_json_document (src)))
    {
    case DB_JSON_DOUBLE:
      break;
    case DB_JSON_INT:
      break;
    case DB_JSON_BIGINT:
      break;
    case DB_JSON_BOOL:
      break;
    case DB_JSON_STRING:
      status = tp_value_convert_char_to_datetime (&scalar, target, desired_domain, error);
      break;
    default:
      break;
    }
  pr_clear_value (&scalar);
  return status;
}

/*
 * [리뷰] tp_value_convert_json_scalar_to_datetimeltz — JSON 값을 DATETIMELTZ 로 바꾸는 변환기 — tp_json_unwrap_scalar 로
 * 스칼라를 꺼낸 뒤 꺼낸 타입에 맞는 변환기로 위임한다: STRING 스칼라만 char_to_datetimeltz 로 넘기고 나머지는 DOMAIN_INCOMPATIBLE 이다. 게이트가
 * src_type == DB_TYPE_JSON 일 때 고르는 자리다.
 * develop: develop 에는 없다 — object_domain.c tp_value_cast_internal(develop:6992-10078) 가 함수 머리에서 JSON 을 스칼라로
 * 바꿔치기(src_replacement)한 뒤 그냥 "바뀐 소스 타입"으로 아래 switch 를 돌렸다. 즉 JSON→DATETIMELTZ 라는 짝 자체가 존재하지 않았고, 실제로 도는 가지는
 * 언래핑 결과 타입의 가지였다.
 * 이 PR: 언래핑과 위임을 한 함수 안에 담아, 소스 타입이 JSON 인 채로도 하나의 변환기 포인터를 고를 수 있게 했다. 꺼낸 임시 값은 pr_clear_value 로 정리한다.
 * 바뀐 것: 신설(+30~55줄). develop 의 "소스 값을 바꿔치기하고 다시 switch" 가 "JSON 짝 전용 변환기"로 바뀌었다 — 게이트가 행 전에 변환기를 못 박으려면 JSON 도
 * 하나의 짝이어야 하기 때문이다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_json_scalar_to_datetimeltz (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  DB_VALUE scalar;
  db_make_null (&scalar);
  if (!tp_json_unwrap_scalar (src, false, &scalar))
    {
      return DOMAIN_INCOMPATIBLE;
    }
  TP_DOMAIN_STATUS status = DOMAIN_INCOMPATIBLE;
  switch (db_json_get_type (db_get_json_document (src)))
    {
    case DB_JSON_DOUBLE:
      break;
    case DB_JSON_INT:
      break;
    case DB_JSON_BIGINT:
      break;
    case DB_JSON_BOOL:
      break;
    case DB_JSON_STRING:
      status = tp_value_convert_char_to_datetimeltz (&scalar, target, desired_domain, error);
      break;
    default:
      break;
    }
  pr_clear_value (&scalar);
  return status;
}

/*
 * [리뷰] tp_value_convert_json_scalar_to_datetimetz — JSON 값을 DATETIMETZ 로 바꾸는 변환기 — tp_json_unwrap_scalar 로
 * 스칼라를 꺼낸 뒤 꺼낸 타입에 맞는 변환기로 위임한다: STRING 스칼라만 char_to_datetimetz 로 넘기고 나머지는 DOMAIN_INCOMPATIBLE 이다. 게이트가
 * src_type == DB_TYPE_JSON 일 때 고르는 자리다.
 * develop: develop 에는 없다 — object_domain.c tp_value_cast_internal(develop:6992-10078) 가 함수 머리에서 JSON 을 스칼라로
 * 바꿔치기(src_replacement)한 뒤 그냥 "바뀐 소스 타입"으로 아래 switch 를 돌렸다. 즉 JSON→DATETIMETZ 라는 짝 자체가 존재하지 않았고, 실제로 도는 가지는
 * 언래핑 결과 타입의 가지였다.
 * 이 PR: 언래핑과 위임을 한 함수 안에 담아, 소스 타입이 JSON 인 채로도 하나의 변환기 포인터를 고를 수 있게 했다. 꺼낸 임시 값은 pr_clear_value 로 정리한다.
 * 바뀐 것: 신설(+30~55줄). develop 의 "소스 값을 바꿔치기하고 다시 switch" 가 "JSON 짝 전용 변환기"로 바뀌었다 — 게이트가 행 전에 변환기를 못 박으려면 JSON 도
 * 하나의 짝이어야 하기 때문이다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_json_scalar_to_datetimetz (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  DB_VALUE scalar;
  db_make_null (&scalar);
  if (!tp_json_unwrap_scalar (src, false, &scalar))
    {
      return DOMAIN_INCOMPATIBLE;
    }
  TP_DOMAIN_STATUS status = DOMAIN_INCOMPATIBLE;
  switch (db_json_get_type (db_get_json_document (src)))
    {
    case DB_JSON_DOUBLE:
      break;
    case DB_JSON_INT:
      break;
    case DB_JSON_BIGINT:
      break;
    case DB_JSON_BOOL:
      break;
    case DB_JSON_STRING:
      status = tp_value_convert_char_to_datetimetz (&scalar, target, desired_domain, error);
      break;
    default:
      break;
    }
  pr_clear_value (&scalar);
  return status;
}

/*
 * [리뷰] tp_value_convert_json_scalar_to_enumeration — JSON 값을 ENUM 로 바꾸는 변환기 — tp_json_unwrap_scalar 로 스칼라를 꺼낸
 * 뒤 꺼낸 타입에 맞는 변환기로 위임한다: 수치는 *_to_enumeration(서수), string 은 varchar_to_enumeration(이름)으로 넘긴다. 게이트가 src_type ==
 * DB_TYPE_JSON 일 때 고르는 자리다.
 * develop: develop 에는 없다 — object_domain.c tp_value_cast_internal(develop:6992-10078) 가 함수 머리에서 JSON 을 스칼라로
 * 바꿔치기(src_replacement)한 뒤 그냥 "바뀐 소스 타입"으로 아래 switch 를 돌렸다. 즉 JSON→ENUM 라는 짝 자체가 존재하지 않았고, 실제로 도는 가지는 언래핑 결과
 * 타입의 가지였다.
 * 이 PR: 언래핑과 위임을 한 함수 안에 담아, 소스 타입이 JSON 인 채로도 하나의 변환기 포인터를 고를 수 있게 했다. 꺼낸 임시 값은 pr_clear_value 로 정리한다.
 * 바뀐 것: 신설(+30~55줄). develop 의 "소스 값을 바꿔치기하고 다시 switch" 가 "JSON 짝 전용 변환기"로 바뀌었다 — 게이트가 행 전에 변환기를 못 박으려면 JSON 도
 * 하나의 짝이어야 하기 때문이다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_json_scalar_to_enumeration (const DB_VALUE *src, DB_VALUE *target,
    const TP_DOMAIN *desired_domain, date_conversion_error *error)
{
  DB_VALUE scalar;
  db_make_null (&scalar);
  if (!tp_json_unwrap_scalar (src, false, &scalar))
    {
      return DOMAIN_INCOMPATIBLE;
    }
  TP_DOMAIN_STATUS status = DOMAIN_INCOMPATIBLE;
  switch (db_json_get_type (db_get_json_document (src)))
    {
    case DB_JSON_DOUBLE:
      status = tp_value_convert_double_to_enumeration (&scalar, target, desired_domain, error);
      break;
    case DB_JSON_INT:
      status = tp_value_convert_integer_to_enumeration (&scalar, target, desired_domain, error);
      break;
    case DB_JSON_BIGINT:
      status = tp_value_convert_bigint_to_enumeration (&scalar, target, desired_domain, error);
      break;
    case DB_JSON_BOOL:
      status = tp_value_convert_integer_to_enumeration (&scalar, target, desired_domain, error);
      break;
    case DB_JSON_STRING:
      status = tp_value_convert_varchar_to_enumeration (&scalar, target, desired_domain, error);
      break;
    default:
      break;
    }
  pr_clear_value (&scalar);
  return status;
}

/*
 * [리뷰] tp_value_convert_json_scalar_to_bit — JSON 값을 BIT 로 바꾸는 변환기 — tp_json_unwrap_scalar 로 스칼라를 꺼낸 뒤 꺼낸 타입에
 * 맞는 변환기로 위임한다: STRING 스칼라만 tp_value_convert_char_to_bit 으로 넘긴다(그 함수는 이미 초기화된 target 도메인에 db_bit_string_coerce
 * 하므로 BIT/VARBIT 공용이다). 게이트가 src_type == DB_TYPE_JSON 일 때 고르는 자리다.
 * develop: develop 에는 없다 — object_domain.c tp_value_cast_internal(develop:6992-10078) 가 함수 머리에서 JSON 을 스칼라로
 * 바꿔치기(src_replacement)한 뒤 그냥 "바뀐 소스 타입"으로 아래 switch 를 돌렸다. 즉 JSON→BIT 라는 짝 자체가 존재하지 않았고, 실제로 도는 가지는 언래핑 결과
 * 타입의 가지였다.
 * 이 PR: 언래핑과 위임을 한 함수 안에 담아, 소스 타입이 JSON 인 채로도 하나의 변환기 포인터를 고를 수 있게 했다. 꺼낸 임시 값은 pr_clear_value 로 정리한다.
 * 바뀐 것: 신설(+30~55줄). develop 의 "소스 값을 바꿔치기하고 다시 switch" 가 "JSON 짝 전용 변환기"로 바뀌었다 — 게이트가 행 전에 변환기를 못 박으려면 JSON 도
 * 하나의 짝이어야 하기 때문이다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_json_scalar_to_bit (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				     date_conversion_error *error)
{
  DB_VALUE scalar;
  db_make_null (&scalar);
  if (!tp_json_unwrap_scalar (src, false, &scalar))
    {
      return DOMAIN_INCOMPATIBLE;
    }
  TP_DOMAIN_STATUS status = DOMAIN_INCOMPATIBLE;
  switch (db_json_get_type (db_get_json_document (src)))
    {
    case DB_JSON_DOUBLE:
      break;
    case DB_JSON_INT:
      break;
    case DB_JSON_BIGINT:
      break;
    case DB_JSON_BOOL:
      break;
    case DB_JSON_STRING:
      status = tp_value_convert_char_to_bit (&scalar, target, desired_domain, error);
      break;
    default:
      break;
    }
  pr_clear_value (&scalar);
  return status;
}

/*
 * [리뷰] tp_value_convert_json_scalar_to_varbit — JSON 값을 VARBIT 로 바꾸는 변환기 — tp_json_unwrap_scalar 로 스칼라를 꺼낸 뒤
 * 꺼낸 타입에 맞는 변환기로 위임한다: STRING 스칼라만 tp_value_convert_char_to_bit 으로 넘긴다 — 이름은 bit 지만 target 도메인이 VARBIT 이면
 * VARBIT 이 나온다(본문이 db_bit_string_coerce 로 target 에 맞춘다). 게이트가 src_type == DB_TYPE_JSON 일 때 고르는 자리다.
 * develop: develop 에는 없다 — object_domain.c tp_value_cast_internal(develop:6992-10078) 가 함수 머리에서 JSON 을 스칼라로
 * 바꿔치기(src_replacement)한 뒤 그냥 "바뀐 소스 타입"으로 아래 switch 를 돌렸다. 즉 JSON→VARBIT 라는 짝 자체가 존재하지 않았고, 실제로 도는 가지는 언래핑 결과
 * 타입의 가지였다.
 * 이 PR: 언래핑과 위임을 한 함수 안에 담아, 소스 타입이 JSON 인 채로도 하나의 변환기 포인터를 고를 수 있게 했다. 꺼낸 임시 값은 pr_clear_value 로 정리한다.
 * 바뀐 것: 신설(+30~55줄). develop 의 "소스 값을 바꿔치기하고 다시 switch" 가 "JSON 짝 전용 변환기"로 바뀌었다 — 게이트가 행 전에 변환기를 못 박으려면 JSON 도
 * 하나의 짝이어야 하기 때문이다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_json_scalar_to_varbit (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
					date_conversion_error *error)
{
  DB_VALUE scalar;
  db_make_null (&scalar);
  if (!tp_json_unwrap_scalar (src, false, &scalar))
    {
      return DOMAIN_INCOMPATIBLE;
    }
  TP_DOMAIN_STATUS status = DOMAIN_INCOMPATIBLE;
  switch (db_json_get_type (db_get_json_document (src)))
    {
    case DB_JSON_DOUBLE:
      break;
    case DB_JSON_INT:
      break;
    case DB_JSON_BIGINT:
      break;
    case DB_JSON_BOOL:
      break;
    case DB_JSON_STRING:
      status = tp_value_convert_char_to_bit (&scalar, target, desired_domain, error);
      break;
    default:
      break;
    }
  pr_clear_value (&scalar);
  return status;
}

/*
 * [리뷰] tp_value_convert_json_scalar_to_blob — JSON 값을 BLOB 로 바꾸는 변환기 — tp_json_unwrap_scalar 로 스칼라를 꺼낸 뒤 꺼낸
 * 타입에 맞는 변환기로 위임한다: STRING 스칼라만 char_to_blob 으로 넘긴다. 게이트가 src_type == DB_TYPE_JSON 일 때 고르는 자리다.
 * develop: develop 에는 없다 — object_domain.c tp_value_cast_internal(develop:6992-10078) 가 함수 머리에서 JSON 을 스칼라로
 * 바꿔치기(src_replacement)한 뒤 그냥 "바뀐 소스 타입"으로 아래 switch 를 돌렸다. 즉 JSON→BLOB 라는 짝 자체가 존재하지 않았고, 실제로 도는 가지는 언래핑 결과
 * 타입의 가지였다.
 * 이 PR: 언래핑과 위임을 한 함수 안에 담아, 소스 타입이 JSON 인 채로도 하나의 변환기 포인터를 고를 수 있게 했다. 꺼낸 임시 값은 pr_clear_value 로 정리한다.
 * 바뀐 것: 신설(+30~55줄). develop 의 "소스 값을 바꿔치기하고 다시 switch" 가 "JSON 짝 전용 변환기"로 바뀌었다 — 게이트가 행 전에 변환기를 못 박으려면 JSON 도
 * 하나의 짝이어야 하기 때문이다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_json_scalar_to_blob (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				      date_conversion_error *error)
{
  DB_VALUE scalar;
  db_make_null (&scalar);
  if (!tp_json_unwrap_scalar (src, false, &scalar))
    {
      return DOMAIN_INCOMPATIBLE;
    }
  TP_DOMAIN_STATUS status = DOMAIN_INCOMPATIBLE;
  switch (db_json_get_type (db_get_json_document (src)))
    {
    case DB_JSON_DOUBLE:
      break;
    case DB_JSON_INT:
      break;
    case DB_JSON_BIGINT:
      break;
    case DB_JSON_BOOL:
      break;
    case DB_JSON_STRING:
      status = tp_value_convert_char_to_blob (&scalar, target, desired_domain, error);
      break;
    default:
      break;
    }
  pr_clear_value (&scalar);
  return status;
}

/*
 * [리뷰] tp_value_convert_json_scalar_to_clob — JSON 값을 CLOB 로 바꾸는 변환기 — tp_json_unwrap_scalar 로 스칼라를 꺼낸 뒤 꺼낸
 * 타입에 맞는 변환기로 위임한다: STRING 스칼라만 char_to_clob 으로 넘긴다. 게이트가 src_type == DB_TYPE_JSON 일 때 고르는 자리다.
 * develop: develop 에는 없다 — object_domain.c tp_value_cast_internal(develop:6992-10078) 가 함수 머리에서 JSON 을 스칼라로
 * 바꿔치기(src_replacement)한 뒤 그냥 "바뀐 소스 타입"으로 아래 switch 를 돌렸다. 즉 JSON→CLOB 라는 짝 자체가 존재하지 않았고, 실제로 도는 가지는 언래핑 결과
 * 타입의 가지였다.
 * 이 PR: 언래핑과 위임을 한 함수 안에 담아, 소스 타입이 JSON 인 채로도 하나의 변환기 포인터를 고를 수 있게 했다. 꺼낸 임시 값은 pr_clear_value 로 정리한다.
 * 바뀐 것: 신설(+30~55줄). develop 의 "소스 값을 바꿔치기하고 다시 switch" 가 "JSON 짝 전용 변환기"로 바뀌었다 — 게이트가 행 전에 변환기를 못 박으려면 JSON 도
 * 하나의 짝이어야 하기 때문이다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_json_scalar_to_clob (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
				      date_conversion_error *error)
{
  DB_VALUE scalar;
  db_make_null (&scalar);
  if (!tp_json_unwrap_scalar (src, false, &scalar))
    {
      return DOMAIN_INCOMPATIBLE;
    }
  TP_DOMAIN_STATUS status = DOMAIN_INCOMPATIBLE;
  switch (db_json_get_type (db_get_json_document (src)))
    {
    case DB_JSON_DOUBLE:
      break;
    case DB_JSON_INT:
      break;
    case DB_JSON_BIGINT:
      break;
    case DB_JSON_BOOL:
      break;
    case DB_JSON_STRING:
      status = tp_value_convert_char_to_clob (&scalar, target, desired_domain, error);
      break;
    default:
      break;
    }
  pr_clear_value (&scalar);
  return status;
}

#if !defined (SERVER_MODE)
/*
 * [리뷰] tp_value_convert_oid_to_oid — OID→OID 변환기 — 값을 그대로 복제해 target 에 넣는다. 매개변수화 도메인 때문에 디스패치 표에 자리가 필요한 짝이다.
 * develop: develop 에는 없다 — object_domain.c tp_value_cast_internal(develop:6992-10078) 가 `desired_type ==
 * original_type` + `is_parameterized` 분기에서 `case DB_TYPE_OID: pr_clone_value(...); return
 * status;`(develop:7146 부근) 로 바로 돌아갔다.
 * 이 PR: 같은 pr_clone_value 를 하는 6줄짜리 변환기. 쓰지 않는 두 인자는 이름을 생략했다.
 * 바뀐 것: early-return 가지 → 변환기 함수(+6줄). 표에 빈칸이 없도록 메우는 성격의 추출.
 */
static TP_DOMAIN_STATUS
tp_value_convert_oid_to_oid (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *, date_conversion_error *)
{
  pr_clone_value (src, target);
  return DOMAIN_COMPATIBLE;
}
#endif /* !defined (SERVER_MODE) */

/*
 * tp_value_convert_enumeration_name_to_double () - an ENUM added to a string without plus_as_concat: its name, then
 *   the name read as a number (qdata_add_dbval casts the ENUM to VARCHAR, then both strings to DOUBLE). The
 *   converter of (ENUM, DOUBLE) stays the ordinal; the type rules pick this one for that position.
 */
/*
 * [리뷰] tp_value_convert_enumeration_name_to_double — ENUM 을 서수가 아니라 이름 문자열로 읽어 DOUBLE 로 바꾸는 변환기 —
 * tp_value_convert_enumeration_to_varchar 로 이름을 얻고 tp_value_convert_number<VARCHAR, DOUBLE, ASSIGN> 로 숫자를 만든다.
 * develop: develop 에는 없다 — object_domain.c tp_value_cast_internal(develop:6992-10078) 의 `case DB_TYPE_DOUBLE:`
 * 안 `case DB_TYPE_ENUMERATION:`(develop:8050 부근)이 tp_enumeration_to_varchar 로 이름을 얻은 뒤 tp_value_cast_internal
 * 을 재귀 호출했다.
 * 이 PR: 재귀 대신 두 변환기를 직접 이어 붙인 단독 함수. 중간 name 값은 pr_clear_value 로 정리한다.
 * 바뀐 것: case 가지 → 함수 추출(+17줄). 재귀 1건이 직접 호출 2건으로 바뀌었다.
 */
static TP_DOMAIN_STATUS
tp_value_convert_enumeration_name_to_double (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
    date_conversion_error *error)
{
  TP_DOMAIN *varchar_domain = tp_domain_resolve_default (DB_TYPE_VARCHAR);
  DB_VALUE name;

  db_value_domain_init (&name, DB_TYPE_VARCHAR, varchar_domain->precision, 0);
  TP_DOMAIN_STATUS status = tp_value_convert_enumeration_to_varchar (src, &name, varchar_domain, error);
  if (status == DOMAIN_COMPATIBLE)
    {
      status = tp_value_convert_number<DB_TYPE_VARCHAR, DB_TYPE_DOUBLE, DOMAIN_CONVERT_ASSIGN> (&name, target,
	       desired_domain, error);
    }
  pr_clear_value (&name);
  return status;
}

/*
 * [리뷰] domain_enumeration_name_converter — 위 변환기의 주소를 바깥(src/query/domain_rules.c)에 내주는 한 줄짜리 접근자 —
 * domain_set_arith_operands 가 T_ADD 의 피연산자가 ENUM 이고 목표가 DOUBLE 일 때 이 포인터를 RESOLVED_DOMAIN.conv[i] 에
 * 박는다(pr.diff:27304).
 * develop: develop 에는 없음 — 이 PR 이 신설. develop 에서는 그런 선택이 없었고, qdata_add_dbval(query_opfunc.c:2438)이 매 행 ENUM
 * 피연산자를 VARCHAR/SMALLINT 로 tp_value_auto_cast 한 뒤 다시 더했다.
 * 이 PR: 변환기 자체는 static 이지만 이 접근자만 외부에 노출된다. 실행 전 게이트가 "이 피연산자는 이름으로 읽는다"를 함수 포인터 한 개로 고정할 수 있게 된다.
 * 바뀐 것: 신설(+5줄). 매 행 타입 분기가 플랜의 포인터 한 칸으로 옮겨가는 이 PR 의 전형적인 연결 고리다.
 */
TP_VALUE_CONVERTER
domain_enumeration_name_converter (void)
{
  return tp_value_convert_enumeration_name_to_double;
}

/*
 * tp_value_convert_collection () - a set, multiset or sequence into a collection of type COLLECTION: the same set
 *   under the target domain when the domains are compatible, a coerced copy otherwise; IMPLICIT_ELEMENTS coerces the
 *   elements implicitly (tp_value_coerce), not explicitly (tp_value_cast)
 */
template <DB_TYPE COLLECTION, bool IMPLICIT_ELEMENTS>
/*
 * [리뷰] tp_value_convert_collection — SET/MULTISET/SEQUENCE 값을 목표 컬렉션 도메인으로 옮기는 변환기(COLLECTION 템플릿 인자로 세 타입에 한
 * 번씩 찍힌다) — 도메인이 호환되면 set_copy 후 setobj_put_domain, 아니면 set_coerce 로 원소까지 변환하고 db_make_set/multiset/sequence 로
 * target 에 넣는다.
 * develop: develop 에는 없다 — object_domain.c tp_value_cast_internal(develop:6992-10078) 의 `case
 * DB_TYPE_SET:/MULTISET:/SEQUENCE:`(develop:8895-8897) 공유 가지였고, 세 타입 중 무엇을 만들지는 런타임에 desired_type 을 보고 골랐다.
 * 이 PR: 같은 알고리즘을 COLLECTION 템플릿 인자로 받아 `if constexpr` 로 db_make_set/multiset/sequence 를 컴파일 시점에 고른다.
 * 바뀐 것: 공유 case → 템플릿 함수 추출(+76줄). 런타임 타입 분기가 `if constexpr` + static_assert 로 바뀌었다. 실패 판정은 여전히 er_errid() 를
 * 읽어 err 로 삼는다(계약이 전역 에러 상태에 묶여 있다).
 */
static TP_DOMAIN_STATUS
tp_value_convert_collection (const DB_VALUE *src, DB_VALUE *target, const TP_DOMAIN *desired_domain,
			     date_conversion_error *error)
{
  int err = NO_ERROR;
  TP_DOMAIN_STATUS status = DOMAIN_COMPATIBLE;

  {
    SETREF *setref;

    setref = db_get_set (src);
    if (setref)
      {
	TP_DOMAIN *set_domain;

	set_domain = setobj_domain (setref->set);
	{
	  if (tp_domain_compatible (set_domain, desired_domain))
	    {
	      /*
	       * Well, we can't use the exact same set, but we don't
	       * have to do the whole hairy coerce thing either: we
	       * can just make a copy and then take the more general
	       * domain.  setobj_put_domain() guards against null
	       * pointers, there's no need to check first.
	       */
	      setref = set_copy (setref);
	      if (setref)
		{
		  setobj_put_domain (setref->set, (TP_DOMAIN *) desired_domain);
		}
	    }
	  else
	    {
	      /*
	       * Well, now we have to use the whole hairy coercion
	       * thing.  Too bad...
	       *
	       * This case will crop up when someone tries to cast a
	       * "set of int" as a "set of float", for example.
	       */
	      setref =
		      set_coerce (setref, (TP_DOMAIN *) desired_domain, IMPLICIT_ELEMENTS);
	    }

	  if (setref == NULL)
	    {
	      assert (er_errid () != NO_ERROR);
	      err = er_errid ();
	    }
	  else
	    {
	      if constexpr (COLLECTION == DB_TYPE_SET)
		{
		  err = db_make_set (target, setref);
		}
	      else if constexpr (COLLECTION == DB_TYPE_MULTISET)
		{
		  err = db_make_multiset (target, setref);
		}
	      else
		{
		  static_assert (COLLECTION == DB_TYPE_SEQUENCE, "not a collection type");
		  err = db_make_sequence (target, setref);
		}
	    }
	}
	if (!setref || err < 0)
	  {
	    status = DOMAIN_INCOMPATIBLE;
	  }
      }
  }

  return err < 0 ? DOMAIN_ERROR : status;
}

/*
 * tp_value_find_converter () - the converter of a value of type src into a domain of type dst in a mode
 *   return: the converter; nullptr for the same type with nothing to convert; tp_value_convert_incompatible
 *	     for a pair that does not convert in the mode
 *
 * Every pair that converts is named once, grouped by its target. The mode picks within a case: COMPARE and
 * OPERAND take the strict converters, IMPLICIT is ASSIGN but for the pairs implicit coercion refuses and the
 * collection targets, which coerce the elements implicitly.
 */
template <DOMAIN_CONVERT_MODE MODE>
static TP_VALUE_CONVERTER
tp_value_find_converter (DB_TYPE src, DB_TYPE dst)
{
  constexpr bool strict = MODE == DOMAIN_CONVERT_COMPARE || MODE == DOMAIN_CONVERT_OPERAND;
  /* the numeric converters of IMPLICIT are ASSIGN's */
  constexpr DOMAIN_CONVERT_MODE CONVERTER_MODE = MODE == DOMAIN_CONVERT_IMPLICIT ? DOMAIN_CONVERT_ASSIGN : MODE;

  if (MODE == DOMAIN_CONVERT_IMPLICIT && TP_IMPLICIT_COERCION_NOT_ALLOWED (src, dst))
    {
      return tp_value_convert_incompatible;
    }
  switch (dst)
    {
    case DB_TYPE_SHORT:
      switch (src)
	{
	case DB_TYPE_INTEGER:
	  return tp_value_convert_number<DB_TYPE_INTEGER, DB_TYPE_SHORT, CONVERTER_MODE>;
	case DB_TYPE_BIGINT:
	  return tp_value_convert_number<DB_TYPE_BIGINT, DB_TYPE_SHORT, CONVERTER_MODE>;
	case DB_TYPE_FLOAT:
	  return tp_value_convert_number<DB_TYPE_FLOAT, DB_TYPE_SHORT, CONVERTER_MODE>;
	case DB_TYPE_DOUBLE:
	  return tp_value_convert_number<DB_TYPE_DOUBLE, DB_TYPE_SHORT, CONVERTER_MODE>;
	case DB_TYPE_MONETARY:
	  return tp_value_convert_number<DB_TYPE_MONETARY, DB_TYPE_SHORT, CONVERTER_MODE>;
	case DB_TYPE_NUMERIC:
	  return tp_value_convert_number<DB_TYPE_NUMERIC, DB_TYPE_SHORT, CONVERTER_MODE>;
	case DB_TYPE_CHAR:
	case DB_TYPE_VARCHAR:
	  return tp_value_convert_number<DB_TYPE_VARCHAR, DB_TYPE_SHORT, CONVERTER_MODE>;
	case DB_TYPE_ENUMERATION:
	  return tp_value_convert_enumeration_to_number<DB_TYPE_SHORT>;
	case DB_TYPE_JSON:
	  return tp_value_convert_json_scalar_to_number<DB_TYPE_SHORT>;
	default:
	  break;
	}
      break;
    case DB_TYPE_INTEGER:
      switch (src)
	{
	case DB_TYPE_SHORT:
	  return tp_value_convert_number<DB_TYPE_SHORT, DB_TYPE_INTEGER, CONVERTER_MODE>;
	case DB_TYPE_BIGINT:
	  return tp_value_convert_number<DB_TYPE_BIGINT, DB_TYPE_INTEGER, CONVERTER_MODE>;
	case DB_TYPE_FLOAT:
	  return tp_value_convert_number<DB_TYPE_FLOAT, DB_TYPE_INTEGER, CONVERTER_MODE>;
	case DB_TYPE_DOUBLE:
	  return tp_value_convert_number<DB_TYPE_DOUBLE, DB_TYPE_INTEGER, CONVERTER_MODE>;
	case DB_TYPE_MONETARY:
	  return tp_value_convert_number<DB_TYPE_MONETARY, DB_TYPE_INTEGER, CONVERTER_MODE>;
	case DB_TYPE_NUMERIC:
	  return tp_value_convert_number<DB_TYPE_NUMERIC, DB_TYPE_INTEGER, CONVERTER_MODE>;
	case DB_TYPE_CHAR:
	case DB_TYPE_VARCHAR:
	  return tp_value_convert_number<DB_TYPE_VARCHAR, DB_TYPE_INTEGER, CONVERTER_MODE>;
	case DB_TYPE_ENUMERATION:
	  return tp_value_convert_enumeration_to_number<DB_TYPE_INTEGER>;
	case DB_TYPE_JSON:
	  return tp_value_convert_json_scalar_to_number<DB_TYPE_INTEGER>;
	default:
	  break;
	}
      break;
    case DB_TYPE_BIGINT:
      switch (src)
	{
	case DB_TYPE_SHORT:
	  return tp_value_convert_number<DB_TYPE_SHORT, DB_TYPE_BIGINT, CONVERTER_MODE>;
	case DB_TYPE_INTEGER:
	  return tp_value_convert_number<DB_TYPE_INTEGER, DB_TYPE_BIGINT, CONVERTER_MODE>;
	case DB_TYPE_FLOAT:
	  return tp_value_convert_number<DB_TYPE_FLOAT, DB_TYPE_BIGINT, CONVERTER_MODE>;
	case DB_TYPE_DOUBLE:
	  return tp_value_convert_number<DB_TYPE_DOUBLE, DB_TYPE_BIGINT, CONVERTER_MODE>;
	case DB_TYPE_MONETARY:
	  return tp_value_convert_number<DB_TYPE_MONETARY, DB_TYPE_BIGINT, CONVERTER_MODE>;
	case DB_TYPE_NUMERIC:
	  return tp_value_convert_number<DB_TYPE_NUMERIC, DB_TYPE_BIGINT, CONVERTER_MODE>;
	case DB_TYPE_CHAR:
	case DB_TYPE_VARCHAR:
	  return tp_value_convert_number<DB_TYPE_VARCHAR, DB_TYPE_BIGINT, CONVERTER_MODE>;
	case DB_TYPE_ENUMERATION:
	  return tp_value_convert_enumeration_to_number<DB_TYPE_BIGINT>;
	case DB_TYPE_JSON:
	  return tp_value_convert_json_scalar_to_number<DB_TYPE_BIGINT>;
	default:
	  break;
	}
      break;
    case DB_TYPE_FLOAT:
      switch (src)
	{
	case DB_TYPE_SHORT:
	  return tp_value_convert_number<DB_TYPE_SHORT, DB_TYPE_FLOAT, CONVERTER_MODE>;
	case DB_TYPE_INTEGER:
	  return tp_value_convert_number<DB_TYPE_INTEGER, DB_TYPE_FLOAT, CONVERTER_MODE>;
	case DB_TYPE_BIGINT:
	  return tp_value_convert_number<DB_TYPE_BIGINT, DB_TYPE_FLOAT, CONVERTER_MODE>;
	case DB_TYPE_DOUBLE:
	  return tp_value_convert_number<DB_TYPE_DOUBLE, DB_TYPE_FLOAT, CONVERTER_MODE>;
	case DB_TYPE_MONETARY:
	  return tp_value_convert_number<DB_TYPE_MONETARY, DB_TYPE_FLOAT, CONVERTER_MODE>;
	case DB_TYPE_NUMERIC:
	  return tp_value_convert_number<DB_TYPE_NUMERIC, DB_TYPE_FLOAT, CONVERTER_MODE>;
	case DB_TYPE_CHAR:
	case DB_TYPE_VARCHAR:
	  return tp_value_convert_number<DB_TYPE_VARCHAR, DB_TYPE_FLOAT, CONVERTER_MODE>;
	case DB_TYPE_ENUMERATION:
	  return tp_value_convert_enumeration_to_number<DB_TYPE_FLOAT>;
	case DB_TYPE_JSON:
	  return tp_value_convert_json_scalar_to_number<DB_TYPE_FLOAT>;
	default:
	  break;
	}
      break;
    case DB_TYPE_DOUBLE:
      switch (src)
	{
	case DB_TYPE_SHORT:
	  return tp_value_convert_number<DB_TYPE_SHORT, DB_TYPE_DOUBLE, CONVERTER_MODE>;
	case DB_TYPE_INTEGER:
	  return tp_value_convert_number<DB_TYPE_INTEGER, DB_TYPE_DOUBLE, CONVERTER_MODE>;
	case DB_TYPE_BIGINT:
	  return tp_value_convert_number<DB_TYPE_BIGINT, DB_TYPE_DOUBLE, CONVERTER_MODE>;
	case DB_TYPE_FLOAT:
	  return tp_value_convert_number<DB_TYPE_FLOAT, DB_TYPE_DOUBLE, CONVERTER_MODE>;
	case DB_TYPE_MONETARY:
	  return tp_value_convert_number<DB_TYPE_MONETARY, DB_TYPE_DOUBLE, CONVERTER_MODE>;
	case DB_TYPE_NUMERIC:
	  return tp_value_convert_number<DB_TYPE_NUMERIC, DB_TYPE_DOUBLE, CONVERTER_MODE>;
	case DB_TYPE_CHAR:
	case DB_TYPE_VARCHAR:
	  return tp_value_convert_number<DB_TYPE_VARCHAR, DB_TYPE_DOUBLE, CONVERTER_MODE>;
	case DB_TYPE_ENUMERATION:
	  return tp_value_convert_enumeration_to_number<DB_TYPE_DOUBLE>;
	case DB_TYPE_JSON:
	  return tp_value_convert_json_scalar_to_number<DB_TYPE_DOUBLE>;
	default:
	  break;
	}
      break;
    case DB_TYPE_MONETARY:
      switch (src)
	{
	case DB_TYPE_SHORT:
	  return tp_value_convert_number<DB_TYPE_SHORT, DB_TYPE_MONETARY, CONVERTER_MODE>;
	case DB_TYPE_INTEGER:
	  return tp_value_convert_number<DB_TYPE_INTEGER, DB_TYPE_MONETARY, CONVERTER_MODE>;
	case DB_TYPE_BIGINT:
	  return tp_value_convert_number<DB_TYPE_BIGINT, DB_TYPE_MONETARY, CONVERTER_MODE>;
	case DB_TYPE_FLOAT:
	  return tp_value_convert_number<DB_TYPE_FLOAT, DB_TYPE_MONETARY, CONVERTER_MODE>;
	case DB_TYPE_DOUBLE:
	  return tp_value_convert_number<DB_TYPE_DOUBLE, DB_TYPE_MONETARY, CONVERTER_MODE>;
	case DB_TYPE_NUMERIC:
	  return tp_value_convert_number<DB_TYPE_NUMERIC, DB_TYPE_MONETARY, CONVERTER_MODE>;
	case DB_TYPE_CHAR:
	case DB_TYPE_VARCHAR:
	  return tp_value_convert_number<DB_TYPE_VARCHAR, DB_TYPE_MONETARY, CONVERTER_MODE>;
	case DB_TYPE_ENUMERATION:
	  return tp_value_convert_enumeration_to_number<DB_TYPE_MONETARY>;
	case DB_TYPE_JSON:
	  return tp_value_convert_json_scalar_to_number<DB_TYPE_MONETARY>;
	default:
	  break;
	}
      break;
    case DB_TYPE_NUMERIC:
      switch (src)
	{
	case DB_TYPE_SHORT:
	  return tp_value_convert_number<DB_TYPE_SHORT, DB_TYPE_NUMERIC, CONVERTER_MODE>;
	case DB_TYPE_INTEGER:
	  return tp_value_convert_number<DB_TYPE_INTEGER, DB_TYPE_NUMERIC, CONVERTER_MODE>;
	case DB_TYPE_BIGINT:
	  return tp_value_convert_number<DB_TYPE_BIGINT, DB_TYPE_NUMERIC, CONVERTER_MODE>;
	case DB_TYPE_FLOAT:
	  return tp_value_convert_number<DB_TYPE_FLOAT, DB_TYPE_NUMERIC, CONVERTER_MODE>;
	case DB_TYPE_DOUBLE:
	  return tp_value_convert_number<DB_TYPE_DOUBLE, DB_TYPE_NUMERIC, CONVERTER_MODE>;
	case DB_TYPE_MONETARY:
	  return tp_value_convert_number<DB_TYPE_MONETARY, DB_TYPE_NUMERIC, CONVERTER_MODE>;
	case DB_TYPE_NUMERIC:
	  return tp_value_convert_number<DB_TYPE_NUMERIC, DB_TYPE_NUMERIC, CONVERTER_MODE>;
	case DB_TYPE_CHAR:
	case DB_TYPE_VARCHAR:
	  return tp_value_convert_number<DB_TYPE_VARCHAR, DB_TYPE_NUMERIC, CONVERTER_MODE>;
	case DB_TYPE_ENUMERATION:
	  return tp_value_convert_enumeration_to_numeric;
	case DB_TYPE_JSON:
	  return tp_value_convert_json_scalar_to_number<DB_TYPE_NUMERIC>;
	default:
	  break;
	}
      break;
    case DB_TYPE_CHAR:
      switch (src)
	{
	case DB_TYPE_SHORT:
	  return tp_value_convert_short_to_char;
	case DB_TYPE_INTEGER:
	  return tp_value_convert_integer_to_char;
	case DB_TYPE_BIGINT:
	  return tp_value_convert_bigint_to_char;
	case DB_TYPE_FLOAT:
	  return tp_value_convert_float_to_char;
	case DB_TYPE_DOUBLE:
	  return tp_value_convert_double_to_char;
	case DB_TYPE_MONETARY:
	  return tp_value_convert_monetary_to_char;
	case DB_TYPE_NUMERIC:
	  return tp_value_convert_numeric_to_char;
	case DB_TYPE_CHAR:
	  return tp_value_convert_varchar_to_varchar;
	case DB_TYPE_VARCHAR:
	  return tp_value_convert_char_to_varchar;
	case DB_TYPE_BIT:
	case DB_TYPE_VARBIT:
	  return tp_value_convert_bit_to_char;
	case DB_TYPE_TIME:
	  return tp_value_convert_time_to_char;
	case DB_TYPE_DATE:
	  return tp_value_convert_date_to_char;
	case DB_TYPE_TIMESTAMP:
	  return tp_value_convert_timestamp_to_char;
	case DB_TYPE_TIMESTAMPLTZ:
	  return tp_value_convert_timestampltz_to_char;
	case DB_TYPE_TIMESTAMPTZ:
	  return tp_value_convert_timestamptz_to_char;
	case DB_TYPE_DATETIME:
	  return tp_value_convert_datetime_to_char;
	case DB_TYPE_DATETIMELTZ:
	  return tp_value_convert_datetimeltz_to_char;
	case DB_TYPE_DATETIMETZ:
	  return tp_value_convert_datetimetz_to_char;
	case DB_TYPE_CLOB:
	  return strict ? tp_value_convert_incompatible : tp_value_convert_clob_to_char;
	case DB_TYPE_ENUMERATION:
	  return tp_value_convert_enumeration_to_char;
	case DB_TYPE_JSON:
	  return tp_value_convert_json_scalar_to_char;
	default:
	  break;
	}
      break;
    case DB_TYPE_VARCHAR:
      switch (src)
	{
	case DB_TYPE_SHORT:
	  return tp_value_convert_short_to_varchar;
	case DB_TYPE_INTEGER:
	  return tp_value_convert_integer_to_varchar;
	case DB_TYPE_BIGINT:
	  return tp_value_convert_bigint_to_varchar;
	case DB_TYPE_FLOAT:
	  return tp_value_convert_float_to_varchar;
	case DB_TYPE_DOUBLE:
	  return tp_value_convert_double_to_varchar;
	case DB_TYPE_MONETARY:
	  return tp_value_convert_monetary_to_varchar;
	case DB_TYPE_NUMERIC:
	  return tp_value_convert_numeric_to_varchar;
	case DB_TYPE_CHAR:
	  return tp_value_convert_char_to_varchar;
	case DB_TYPE_VARCHAR:
	  return tp_value_convert_varchar_to_varchar;
	case DB_TYPE_BIT:
	case DB_TYPE_VARBIT:
	  return tp_value_convert_bit_to_varchar;
	case DB_TYPE_TIME:
	  return tp_value_convert_time_to_varchar;
	case DB_TYPE_DATE:
	  return tp_value_convert_date_to_varchar;
	case DB_TYPE_TIMESTAMP:
	  return tp_value_convert_timestamp_to_varchar;
	case DB_TYPE_TIMESTAMPLTZ:
	  return tp_value_convert_timestampltz_to_varchar;
	case DB_TYPE_TIMESTAMPTZ:
	  return tp_value_convert_timestamptz_to_varchar;
	case DB_TYPE_DATETIME:
	  return tp_value_convert_datetime_to_varchar;
	case DB_TYPE_DATETIMELTZ:
	  return tp_value_convert_datetimeltz_to_varchar;
	case DB_TYPE_DATETIMETZ:
	  return tp_value_convert_datetimetz_to_varchar;
	case DB_TYPE_CLOB:
	  return strict ? tp_value_convert_incompatible : tp_value_convert_clob_to_varchar;
	case DB_TYPE_ENUMERATION:
	  return tp_value_convert_enumeration_to_varchar;
	case DB_TYPE_JSON:
	  return tp_value_convert_json_scalar_to_varchar;
	default:
	  break;
	}
      break;
    case DB_TYPE_NCHAR_DEPRECATED:
      switch (src)
	{
	case DB_TYPE_NCHAR_DEPRECATED:
	  return tp_value_convert_incompatible;
	default:
	  break;
	}
      break;
    case DB_TYPE_VARNCHAR_DEPRECATED:
      switch (src)
	{
	case DB_TYPE_VARNCHAR_DEPRECATED:
	  return tp_value_convert_incompatible;
	default:
	  break;
	}
      break;
    case DB_TYPE_BIT:
      switch (src)
	{
	case DB_TYPE_CHAR:
	case DB_TYPE_VARCHAR:
	  return tp_value_convert_char_to_bit;
	case DB_TYPE_BIT:
	  return tp_value_convert_bit_to_bit;
	case DB_TYPE_VARBIT:
	  return tp_value_convert_varbit_to_bit;
	case DB_TYPE_BLOB:
	  return strict ? tp_value_convert_incompatible : tp_value_convert_blob_to_bit;
	case DB_TYPE_ENUMERATION:
	  return tp_value_convert_enumeration_to_bit;
	case DB_TYPE_JSON:
	  return tp_value_convert_json_scalar_to_bit;
	default:
	  break;
	}
      break;
    case DB_TYPE_VARBIT:
      switch (src)
	{
	case DB_TYPE_CHAR:
	case DB_TYPE_VARCHAR:
	  return tp_value_convert_char_to_bit;
	case DB_TYPE_BIT:
	  return tp_value_convert_varbit_to_bit;
	case DB_TYPE_VARBIT:
	  return tp_value_convert_bit_to_bit;
	case DB_TYPE_BLOB:
	  return strict ? tp_value_convert_incompatible : tp_value_convert_blob_to_varbit;
	case DB_TYPE_ENUMERATION:
	  return tp_value_convert_enumeration_to_varbit;
	case DB_TYPE_JSON:
	  return tp_value_convert_json_scalar_to_varbit;
	default:
	  break;
	}
      break;
    case DB_TYPE_TIME:
      switch (src)
	{
	case DB_TYPE_SHORT:
	  return strict ? tp_value_convert_incompatible : tp_value_convert_short_to_time;
	case DB_TYPE_INTEGER:
	  return strict ? tp_value_convert_incompatible : tp_value_convert_integer_to_time;
	case DB_TYPE_BIGINT:
	  return strict ? tp_value_convert_incompatible : tp_value_convert_bigint_to_time;
	case DB_TYPE_FLOAT:
	  return strict ? tp_value_convert_incompatible : tp_value_convert_float_to_time;
	case DB_TYPE_DOUBLE:
	  return strict ? tp_value_convert_incompatible : tp_value_convert_double_to_time;
	case DB_TYPE_MONETARY:
	  return strict ? tp_value_convert_incompatible : tp_value_convert_monetary_to_time;
	case DB_TYPE_CHAR:
	case DB_TYPE_VARCHAR:
	  return strict ? tp_value_convert_char_to_time_strict : tp_value_convert_char_to_time;
	case DB_TYPE_TIMESTAMP:
	case DB_TYPE_TIMESTAMPLTZ:
	  return strict ? tp_value_convert_incompatible : tp_value_convert_timestamp_to_time;
	case DB_TYPE_TIMESTAMPTZ:
	  return strict ? tp_value_convert_incompatible : tp_value_convert_timestamptz_to_time;
	case DB_TYPE_DATETIME:
	  return strict ? tp_value_convert_incompatible : tp_value_convert_datetime_to_time;
	case DB_TYPE_DATETIMELTZ:
	  return strict ? tp_value_convert_incompatible : tp_value_convert_datetimeltz_to_time;
	case DB_TYPE_DATETIMETZ:
	  return strict ? tp_value_convert_incompatible : tp_value_convert_datetimetz_to_time;
	case DB_TYPE_ENUMERATION:
	  return strict ? tp_value_convert_incompatible : tp_value_convert_enumeration_to_time;
	case DB_TYPE_JSON:
	  return tp_value_convert_json_scalar_to_time;
	default:
	  break;
	}
      break;
    case DB_TYPE_DATE:
      switch (src)
	{
	case DB_TYPE_CHAR:
	case DB_TYPE_VARCHAR:
	  return strict ? tp_value_convert_char_to_date_strict : tp_value_convert_char_to_date;
	case DB_TYPE_TIMESTAMP:
	case DB_TYPE_TIMESTAMPLTZ:
	  return strict ? tp_value_convert_timestamp_to_date_strict : tp_value_convert_timestamp_to_date;
	case DB_TYPE_TIMESTAMPTZ:
	  return strict ? tp_value_convert_timestamptz_to_date_strict : tp_value_convert_timestamptz_to_date;
	case DB_TYPE_DATETIME:
	  return strict ? tp_value_convert_datetime_to_date_strict : tp_value_convert_datetime_to_date;
	case DB_TYPE_DATETIMELTZ:
	  return strict ? tp_value_convert_datetimeltz_to_date_strict : tp_value_convert_datetimeltz_to_date;
	case DB_TYPE_DATETIMETZ:
	  return strict ? tp_value_convert_datetimetz_to_date_strict : tp_value_convert_datetimetz_to_date;
	case DB_TYPE_ENUMERATION:
	  return strict ? tp_value_convert_incompatible : tp_value_convert_enumeration_to_date;
	case DB_TYPE_JSON:
	  return tp_value_convert_json_scalar_to_date;
	default:
	  break;
	}
      break;
    case DB_TYPE_TIMESTAMP:
      switch (src)
	{
	case DB_TYPE_SHORT:
	  return strict ? tp_value_convert_incompatible : tp_value_convert_number_to_timestamp<DB_TYPE_SHORT, DB_TYPE_TIMESTAMP>;
	case DB_TYPE_INTEGER:
	  return strict ? tp_value_convert_incompatible :
		 tp_value_convert_number_to_timestamp<DB_TYPE_INTEGER, DB_TYPE_TIMESTAMP>;
	case DB_TYPE_BIGINT:
	  return strict ? tp_value_convert_incompatible : tp_value_convert_number_to_timestamp<DB_TYPE_BIGINT, DB_TYPE_TIMESTAMP>;
	case DB_TYPE_FLOAT:
	  return strict ? tp_value_convert_incompatible : tp_value_convert_number_to_timestamp<DB_TYPE_FLOAT, DB_TYPE_TIMESTAMP>;
	case DB_TYPE_DOUBLE:
	  return strict ? tp_value_convert_incompatible : tp_value_convert_number_to_timestamp<DB_TYPE_DOUBLE, DB_TYPE_TIMESTAMP>;
	case DB_TYPE_MONETARY:
	  return strict ? tp_value_convert_incompatible :
		 tp_value_convert_number_to_timestamp<DB_TYPE_MONETARY, DB_TYPE_TIMESTAMP>;
	case DB_TYPE_NUMERIC:
	  return strict ? tp_value_convert_incompatible :
		 tp_value_convert_number_to_timestamp<DB_TYPE_NUMERIC, DB_TYPE_TIMESTAMP>;
	case DB_TYPE_CHAR:
	case DB_TYPE_VARCHAR:
	  return strict ? tp_value_convert_char_to_timestamp_strict : tp_value_convert_char_to_timestamp;
	case DB_TYPE_DATE:
	  return strict ? tp_value_convert_date_to_timestamp_strict : tp_value_convert_date_to_timestamp;
	case DB_TYPE_TIMESTAMPLTZ:
	  return strict ? tp_value_convert_timestampltz_to_timestamp_strict : tp_value_convert_timestampltz_to_timestamp;
	case DB_TYPE_TIMESTAMPTZ:
	  return strict ? tp_value_convert_timestamptz_to_timestamp_strict : tp_value_convert_timestamptz_to_timestamp;
	case DB_TYPE_DATETIME:
	  return strict ? tp_value_convert_datetime_to_timestamp_strict : tp_value_convert_datetime_to_timestamp;
	case DB_TYPE_DATETIMELTZ:
	  return strict ? tp_value_convert_datetimeltz_to_timestamp_strict : tp_value_convert_datetimeltz_to_timestamp;
	case DB_TYPE_DATETIMETZ:
	  return strict ? tp_value_convert_datetimetz_to_timestamp_strict : tp_value_convert_datetimetz_to_timestamp;
	case DB_TYPE_ENUMERATION:
	  return strict ? tp_value_convert_incompatible : tp_value_convert_enumeration_to_timestamp;
	case DB_TYPE_JSON:
	  return tp_value_convert_json_scalar_to_timestamp;
	default:
	  break;
	}
      break;
    case DB_TYPE_TIMESTAMPLTZ:
      switch (src)
	{
	case DB_TYPE_SHORT:
	  return strict ? tp_value_convert_incompatible :
		 tp_value_convert_number_to_timestamp<DB_TYPE_SHORT, DB_TYPE_TIMESTAMPLTZ>;
	case DB_TYPE_INTEGER:
	  return strict ? tp_value_convert_incompatible :
		 tp_value_convert_number_to_timestamp<DB_TYPE_INTEGER, DB_TYPE_TIMESTAMPLTZ>;
	case DB_TYPE_BIGINT:
	  return strict ? tp_value_convert_incompatible :
		 tp_value_convert_number_to_timestamp<DB_TYPE_BIGINT, DB_TYPE_TIMESTAMPLTZ>;
	case DB_TYPE_FLOAT:
	  return strict ? tp_value_convert_incompatible :
		 tp_value_convert_number_to_timestamp<DB_TYPE_FLOAT, DB_TYPE_TIMESTAMPLTZ>;
	case DB_TYPE_DOUBLE:
	  return strict ? tp_value_convert_incompatible :
		 tp_value_convert_number_to_timestamp<DB_TYPE_DOUBLE, DB_TYPE_TIMESTAMPLTZ>;
	case DB_TYPE_MONETARY:
	  return strict ? tp_value_convert_incompatible :
		 tp_value_convert_number_to_timestamp<DB_TYPE_MONETARY, DB_TYPE_TIMESTAMPLTZ>;
	case DB_TYPE_NUMERIC:
	  return strict ? tp_value_convert_incompatible :
		 tp_value_convert_number_to_timestamp<DB_TYPE_NUMERIC, DB_TYPE_TIMESTAMPLTZ>;
	case DB_TYPE_CHAR:
	case DB_TYPE_VARCHAR:
	  return strict ? tp_value_convert_char_to_timestampltz_strict : tp_value_convert_char_to_timestampltz;
	case DB_TYPE_DATE:
	  return strict ? tp_value_convert_date_to_timestampltz_strict : tp_value_convert_date_to_timestampltz;
	case DB_TYPE_TIMESTAMP:
	  return strict ? tp_value_convert_timestamp_to_timestampltz_strict : tp_value_convert_timestamp_to_timestampltz;
	case DB_TYPE_TIMESTAMPTZ:
	  return strict ? tp_value_convert_timestamptz_to_timestampltz_strict : tp_value_convert_timestamptz_to_timestampltz;
	case DB_TYPE_DATETIME:
	  return strict ? tp_value_convert_datetime_to_timestampltz_strict : tp_value_convert_datetime_to_timestampltz;
	case DB_TYPE_DATETIMELTZ:
	  return strict ? tp_value_convert_datetimeltz_to_timestampltz_strict : tp_value_convert_datetimeltz_to_timestampltz;
	case DB_TYPE_DATETIMETZ:
	  return strict ? tp_value_convert_datetimetz_to_timestampltz_strict : tp_value_convert_datetimetz_to_timestampltz;
	case DB_TYPE_ENUMERATION:
	  return strict ? tp_value_convert_incompatible : tp_value_convert_enumeration_to_timestampltz;
	case DB_TYPE_JSON:
	  return tp_value_convert_json_scalar_to_timestampltz;
	default:
	  break;
	}
      break;
    case DB_TYPE_TIMESTAMPTZ:
      switch (src)
	{
	case DB_TYPE_SHORT:
	  return strict ? tp_value_convert_incompatible :
		 tp_value_convert_number_to_timestamp<DB_TYPE_SHORT, DB_TYPE_TIMESTAMPTZ>;
	case DB_TYPE_INTEGER:
	  return strict ? tp_value_convert_incompatible :
		 tp_value_convert_number_to_timestamp<DB_TYPE_INTEGER, DB_TYPE_TIMESTAMPTZ>;
	case DB_TYPE_BIGINT:
	  return strict ? tp_value_convert_incompatible :
		 tp_value_convert_number_to_timestamp<DB_TYPE_BIGINT, DB_TYPE_TIMESTAMPTZ>;
	case DB_TYPE_FLOAT:
	  return strict ? tp_value_convert_incompatible :
		 tp_value_convert_number_to_timestamp<DB_TYPE_FLOAT, DB_TYPE_TIMESTAMPTZ>;
	case DB_TYPE_DOUBLE:
	  return strict ? tp_value_convert_incompatible :
		 tp_value_convert_number_to_timestamp<DB_TYPE_DOUBLE, DB_TYPE_TIMESTAMPTZ>;
	case DB_TYPE_MONETARY:
	  return strict ? tp_value_convert_incompatible :
		 tp_value_convert_number_to_timestamp<DB_TYPE_MONETARY, DB_TYPE_TIMESTAMPTZ>;
	case DB_TYPE_NUMERIC:
	  return strict ? tp_value_convert_incompatible :
		 tp_value_convert_number_to_timestamp<DB_TYPE_NUMERIC, DB_TYPE_TIMESTAMPTZ>;
	case DB_TYPE_CHAR:
	case DB_TYPE_VARCHAR:
	  return strict ? tp_value_convert_char_to_timestamptz_strict : tp_value_convert_char_to_timestamptz;
	case DB_TYPE_DATE:
	  return strict ? tp_value_convert_date_to_timestamptz_strict : tp_value_convert_date_to_timestamptz;
	case DB_TYPE_TIMESTAMP:
	case DB_TYPE_TIMESTAMPLTZ:
	  return strict ? tp_value_convert_timestamp_to_timestamptz_strict : tp_value_convert_timestamp_to_timestamptz;
	case DB_TYPE_DATETIME:
	  return strict ? tp_value_convert_datetime_to_timestamptz_strict : tp_value_convert_datetime_to_timestamptz;
	case DB_TYPE_DATETIMELTZ:
	  return strict ? tp_value_convert_datetimeltz_to_timestamptz_strict : tp_value_convert_datetimeltz_to_timestamptz;
	case DB_TYPE_DATETIMETZ:
	  return strict ? tp_value_convert_datetimetz_to_timestamptz_strict : tp_value_convert_datetimetz_to_timestamptz;
	case DB_TYPE_ENUMERATION:
	  return strict ? tp_value_convert_incompatible : tp_value_convert_enumeration_to_timestamptz;
	case DB_TYPE_JSON:
	  return tp_value_convert_json_scalar_to_timestamptz;
	default:
	  break;
	}
      break;
    case DB_TYPE_DATETIME:
      switch (src)
	{
	case DB_TYPE_CHAR:
	case DB_TYPE_VARCHAR:
	  return strict ? tp_value_convert_char_to_datetime_strict : tp_value_convert_char_to_datetime;
	case DB_TYPE_DATE:
	  return strict ? tp_value_convert_date_to_datetime_strict : tp_value_convert_date_to_datetime;
	case DB_TYPE_TIMESTAMP:
	case DB_TYPE_TIMESTAMPLTZ:
	  return strict ? tp_value_convert_timestamp_to_datetime_strict : tp_value_convert_timestamp_to_datetime;
	case DB_TYPE_TIMESTAMPTZ:
	  return strict ? tp_value_convert_timestamptz_to_datetime_strict : tp_value_convert_timestamptz_to_datetime;
	case DB_TYPE_DATETIMELTZ:
	  return strict ? tp_value_convert_datetimeltz_to_datetime_strict : tp_value_convert_datetimeltz_to_datetime;
	case DB_TYPE_DATETIMETZ:
	  return strict ? tp_value_convert_datetimetz_to_datetime_strict : tp_value_convert_datetimetz_to_datetime;
	case DB_TYPE_ENUMERATION:
	  return strict ? tp_value_convert_incompatible : tp_value_convert_enumeration_to_datetime;
	case DB_TYPE_JSON:
	  return tp_value_convert_json_scalar_to_datetime;
	default:
	  break;
	}
      break;
    case DB_TYPE_DATETIMELTZ:
      switch (src)
	{
	case DB_TYPE_CHAR:
	case DB_TYPE_VARCHAR:
	  return strict ? tp_value_convert_char_to_datetimeltz_strict : tp_value_convert_char_to_datetimeltz;
	case DB_TYPE_DATE:
	  return strict ? tp_value_convert_date_to_datetimeltz_strict : tp_value_convert_date_to_datetimeltz;
	case DB_TYPE_TIMESTAMP:
	case DB_TYPE_TIMESTAMPLTZ:
	  return strict ? tp_value_convert_timestamp_to_datetimeltz_strict : tp_value_convert_timestamp_to_datetimeltz;
	case DB_TYPE_TIMESTAMPTZ:
	  return strict ? tp_value_convert_timestamptz_to_datetimeltz_strict : tp_value_convert_timestamptz_to_datetimeltz;
	case DB_TYPE_DATETIME:
	  return strict ? tp_value_convert_datetime_to_datetimeltz_strict : tp_value_convert_datetime_to_datetimeltz;
	case DB_TYPE_DATETIMETZ:
	  return strict ? tp_value_convert_datetimetz_to_datetimeltz_strict : tp_value_convert_datetimetz_to_datetimeltz;
	case DB_TYPE_ENUMERATION:
	  return strict ? tp_value_convert_incompatible : tp_value_convert_enumeration_to_datetimeltz;
	case DB_TYPE_JSON:
	  return tp_value_convert_json_scalar_to_datetimeltz;
	default:
	  break;
	}
      break;
    case DB_TYPE_DATETIMETZ:
      switch (src)
	{
	case DB_TYPE_CHAR:
	case DB_TYPE_VARCHAR:
	  return strict ? tp_value_convert_char_to_datetimetz_strict : tp_value_convert_char_to_datetimetz;
	case DB_TYPE_DATE:
	  return strict ? tp_value_convert_date_to_datetimetz_strict : tp_value_convert_date_to_datetimetz;
	case DB_TYPE_TIMESTAMP:
	case DB_TYPE_TIMESTAMPLTZ:
	  return strict ? tp_value_convert_timestamp_to_datetimetz_strict : tp_value_convert_timestamp_to_datetimetz;
	case DB_TYPE_TIMESTAMPTZ:
	  return strict ? tp_value_convert_timestamptz_to_datetimetz_strict : tp_value_convert_timestamptz_to_datetimetz;
	case DB_TYPE_DATETIME:
	  return strict ? tp_value_convert_datetime_to_datetimetz_strict : tp_value_convert_datetime_to_datetimetz;
	case DB_TYPE_DATETIMELTZ:
	  return strict ? tp_value_convert_datetimeltz_to_datetimetz_strict : tp_value_convert_datetimeltz_to_datetimetz;
	case DB_TYPE_ENUMERATION:
	  return strict ? tp_value_convert_incompatible : tp_value_convert_enumeration_to_datetimetz;
	case DB_TYPE_JSON:
	  return tp_value_convert_json_scalar_to_datetimetz;
	default:
	  break;
	}
      break;
    case DB_TYPE_BLOB:
      switch (src)
	{
	case DB_TYPE_CHAR:
	case DB_TYPE_VARCHAR:
	  return strict ? tp_value_convert_incompatible : tp_value_convert_char_to_blob;
	case DB_TYPE_BIT:
	case DB_TYPE_VARBIT:
	  return strict ? tp_value_convert_incompatible : tp_value_convert_bit_to_blob;
	case DB_TYPE_ENUMERATION:
	  return strict ? tp_value_convert_incompatible : tp_value_convert_enumeration_to_blob;
	case DB_TYPE_JSON:
	  return tp_value_convert_json_scalar_to_blob;
	default:
	  break;
	}
      break;
    case DB_TYPE_CLOB:
      switch (src)
	{
	case DB_TYPE_CHAR:
	case DB_TYPE_VARCHAR:
	  return strict ? tp_value_convert_incompatible : tp_value_convert_char_to_clob;
	case DB_TYPE_ENUMERATION:
	  return strict ? tp_value_convert_incompatible : tp_value_convert_enumeration_to_clob;
	case DB_TYPE_JSON:
	  return tp_value_convert_json_scalar_to_clob;
	default:
	  break;
	}
      break;
    case DB_TYPE_ENUMERATION:
      switch (src)
	{
	case DB_TYPE_SHORT:
	  return tp_value_convert_short_to_enumeration;
	case DB_TYPE_INTEGER:
	  return tp_value_convert_integer_to_enumeration;
	case DB_TYPE_BIGINT:
	  return tp_value_convert_bigint_to_enumeration;
	case DB_TYPE_FLOAT:
	  return tp_value_convert_float_to_enumeration;
	case DB_TYPE_DOUBLE:
	  return tp_value_convert_double_to_enumeration;
	case DB_TYPE_MONETARY:
	  return tp_value_convert_monetary_to_enumeration;
	case DB_TYPE_NUMERIC:
	  return tp_value_convert_numeric_to_enumeration;
	case DB_TYPE_CHAR:
	  return tp_value_convert_char_to_enumeration;
	case DB_TYPE_VARCHAR:
	  return tp_value_convert_varchar_to_enumeration;
	case DB_TYPE_BIT:
	  return tp_value_convert_bit_to_enumeration;
	case DB_TYPE_VARBIT:
	  return tp_value_convert_varbit_to_enumeration;
	case DB_TYPE_TIME:
	  return tp_value_convert_time_to_enumeration;
	case DB_TYPE_DATE:
	  return tp_value_convert_date_to_enumeration;
	case DB_TYPE_TIMESTAMP:
	  return tp_value_convert_timestamp_to_enumeration;
	case DB_TYPE_TIMESTAMPLTZ:
	  return tp_value_convert_timestampltz_to_enumeration;
	case DB_TYPE_TIMESTAMPTZ:
	  return tp_value_convert_timestamptz_to_enumeration;
	case DB_TYPE_DATETIME:
	  return tp_value_convert_datetime_to_enumeration;
	case DB_TYPE_DATETIMELTZ:
	  return tp_value_convert_datetimeltz_to_enumeration;
	case DB_TYPE_DATETIMETZ:
	  return tp_value_convert_datetimetz_to_enumeration;
	case DB_TYPE_BLOB:
	  return strict ? tp_value_convert_incompatible : tp_value_convert_blob_to_enumeration;
	case DB_TYPE_CLOB:
	  return strict ? tp_value_convert_incompatible : tp_value_convert_clob_to_enumeration;
	case DB_TYPE_ENUMERATION:
	  return tp_value_convert_enumeration_to_enumeration;
	case DB_TYPE_JSON:
	  return tp_value_convert_json_scalar_to_enumeration;
	default:
	  break;
	}
      break;
    case DB_TYPE_JSON:
      switch (src)
	{
	case DB_TYPE_SHORT:
	  return tp_value_convert_short_to_json;
	case DB_TYPE_INTEGER:
	  return tp_value_convert_integer_to_json;
	case DB_TYPE_BIGINT:
	  return tp_value_convert_bigint_to_json;
	case DB_TYPE_FLOAT:
	  return tp_value_convert_float_to_json;
	case DB_TYPE_DOUBLE:
	  return tp_value_convert_double_to_json;
	case DB_TYPE_NUMERIC:
	  return tp_value_convert_numeric_to_json;
	case DB_TYPE_CHAR:
	case DB_TYPE_VARCHAR:
	  return tp_value_convert_char_to_json;
	case DB_TYPE_JSON:
	  return tp_value_convert_json_validate;
	default:
	  break;
	}
      break;
    case DB_TYPE_SET:
      switch (src)
	{
	case DB_TYPE_SET:
	case DB_TYPE_MULTISET:
	case DB_TYPE_SEQUENCE:
	  return tp_value_convert_collection<DB_TYPE_SET, MODE == DOMAIN_CONVERT_IMPLICIT>;
	default:
	  break;
	}
      break;
    case DB_TYPE_MULTISET:
      switch (src)
	{
	case DB_TYPE_SET:
	case DB_TYPE_MULTISET:
	case DB_TYPE_SEQUENCE:
	  return tp_value_convert_collection<DB_TYPE_MULTISET, MODE == DOMAIN_CONVERT_IMPLICIT>;
	default:
	  break;
	}
      break;
    case DB_TYPE_SEQUENCE:
      switch (src)
	{
	case DB_TYPE_SET:
	case DB_TYPE_MULTISET:
	case DB_TYPE_SEQUENCE:
	  return tp_value_convert_collection<DB_TYPE_SEQUENCE, MODE == DOMAIN_CONVERT_IMPLICIT>;
	default:
	  break;
	}
      break;
    case DB_TYPE_OBJECT:
      switch (src)
	{
#if !defined (SERVER_MODE)
	case DB_TYPE_OBJECT:
	  return tp_value_convert_object_to_object;
#else /* !defined (SERVER_MODE) */
	case DB_TYPE_OBJECT:
	  return tp_value_convert_incompatible;
#endif /* !defined (SERVER_MODE) */
#if !defined (SERVER_MODE)
	case DB_TYPE_OID:
	  return tp_value_convert_oid_to_object;
#endif /* !defined (SERVER_MODE) */
#if !defined (SERVER_MODE)
	case DB_TYPE_VOBJ:
	  return tp_value_convert_vobj_to_object;
#endif /* !defined (SERVER_MODE) */
#if !defined (SERVER_MODE)
	case DB_TYPE_POINTER:
	  return tp_value_convert_pointer_to_object;
#endif /* !defined (SERVER_MODE) */
	default:
	  break;
	}
      break;
    case DB_TYPE_OID:
      switch (src)
	{
#if !defined (SERVER_MODE)
	case DB_TYPE_OID:
	  return tp_value_convert_oid_to_oid;
#else /* !defined (SERVER_MODE) */
	case DB_TYPE_OID:
	  return tp_value_convert_incompatible;
#endif /* !defined (SERVER_MODE) */
	default:
	  break;
	}
      break;
    case DB_TYPE_VOBJ:
      switch (src)
	{
#if !defined (SERVER_MODE)
	case DB_TYPE_OBJECT:
	  return tp_value_convert_object_to_vobj;
#endif /* !defined (SERVER_MODE) */
	case DB_TYPE_OID:
	  return tp_value_convert_oid_to_vobj;
	case DB_TYPE_VOBJ:
	  return tp_value_convert_vobj_to_vobj;
	default:
	  break;
	}
      break;
    case DB_TYPE_VARIABLE:
      switch (src)
	{
	case DB_TYPE_VARIABLE:
	  return tp_value_convert_incompatible;
	default:
	  break;
	}
      break;
    case DB_TYPE_SUB:
      switch (src)
	{
	case DB_TYPE_SUB:
	  return tp_value_convert_incompatible;
	default:
	  break;
	}
      break;
    case DB_TYPE_DB_VALUE:
      switch (src)
	{
	case DB_TYPE_DB_VALUE:
	  return tp_value_convert_incompatible;
	default:
	  break;
	}
      break;
    case DB_TYPE_MIDXKEY:
      switch (src)
	{
	case DB_TYPE_MIDXKEY:
	  return tp_value_convert_incompatible;
	default:
	  break;
	}
      break;
    case DB_TYPE_TABLE:
      switch (src)
	{
	case DB_TYPE_TABLE:
	  return tp_value_convert_incompatible;
	default:
	  break;
	}
      break;
    default:
      break;
    }
  return src == dst ? nullptr : tp_value_convert_incompatible;
}

/*
 * tp_value_find_converter () - the converter of a value of type src_type into desired_domain in a mode
 *   return: the converter; nullptr for the same type with nothing to convert; tp_value_convert_incompatible for a
 *	     pair that does not convert, a missing domain or a type out of range
 */
/*
 * [리뷰] tp_value_find_converter — 이 파일의 공개 진입점 — (소스 타입, 목표 도메인, 변환 모드)로 TP_VALUE_CONVERTER 함수 포인터 하나를 돌려준다.
 * tp_value_cast_internal 과 tp_value_coerce_strict, 그리고 서버의 실행 전 게이트(domain_rules.c / query_opfunc.c)가 이것을 불러
 * 변환기를 미리 확정한다. 범위를 벗어나면 tp_value_convert_incompatible 을 준다.
 * develop: develop 에는 없음 — 이 PR 이 신설. develop 에서는 "어떤 변환을 할지"가 tp_value_cast_internal 안 2중 switch(목표 타입 × 소스
 * 타입, develop:7317-10030) 였고, 매 값마다 다시 탔다.
 * 이 PR: mode 로 4개 템플릿 인스턴스(ASSIGN/IMPLICIT/COMPARE/OPERAND) 중 하나를 고르고, 그 안에서 (dst, src) 2중 switch 가 변환기 주소를
 * 돌려준다. COMPARE/OPERAND 가 strict 다.
 * 바뀐 것: 신설(+26줄 + 템플릿 본체). 이 PR 의 핵심 전환 — "매 행 switch" 가 "한 번 찾아 둔 함수 포인터"가 됐다. mode→strict
 * 매핑(COMPARE|OPERAND)은 템플릿 안 constexpr 한 줄에만 적혀 있다.
 */
TP_VALUE_CONVERTER
tp_value_find_converter (DB_TYPE src_type, const TP_DOMAIN *desired_domain, DOMAIN_CONVERT_MODE mode)
{
  if (desired_domain == nullptr || src_type < DB_TYPE_NULL || src_type > DB_TYPE_LAST)
    {
      return tp_value_convert_incompatible;
    }
  const DB_TYPE dst_type = TP_DOMAIN_TYPE (desired_domain);
  if (dst_type < DB_TYPE_NULL || dst_type > DB_TYPE_LAST)
    {
      return tp_value_convert_incompatible;
    }
  switch (mode)
    {
    case DOMAIN_CONVERT_ASSIGN:
      return tp_value_find_converter<DOMAIN_CONVERT_ASSIGN> (src_type, dst_type);
    case DOMAIN_CONVERT_IMPLICIT:
      return tp_value_find_converter<DOMAIN_CONVERT_IMPLICIT> (src_type, dst_type);
    case DOMAIN_CONVERT_COMPARE:
      return tp_value_find_converter<DOMAIN_CONVERT_COMPARE> (src_type, dst_type);
    case DOMAIN_CONVERT_OPERAND:
      return tp_value_find_converter<DOMAIN_CONVERT_OPERAND> (src_type, dst_type);
    default:
      return tp_value_convert_incompatible;
    }
}
