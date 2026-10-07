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
 * expr_gen.h - the SQL compiler's expression program generator (client side of expr_program.hpp)
 */

#ifndef _EXPR_GEN_H_
#define _EXPR_GEN_H_

#include "regu_var.hpp"

/* the packed program for a value list's visible columns, in the XASL packing buffer; NULL when nothing is worth
 * a program (no column) or the list is too large for one */
extern struct EXPR_PACKED_PROG *expr_gen_outlist (OUTPTR_LIST * list);

#endif /* _EXPR_GEN_H_ */
