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
 * expr_program.hpp - the expression program the SQL compiler (client) packs into the XASL stream and the
 *		      server runs
 *
 * The client walks a value list's REGU_VARIABLE trees once (expr_gen.c) and emits one program per list: a flat
 * step array over cells (registers), the structure only.  A step whose types the compiler knows is CLOSED - its
 * opcode and type name the typed kernel.  A step over a node the compiler left variable (a bind, an expression
 * over one) is OPEN - its kernel, result domain and operand converters are read from resolve_domains'
 * resolution once per execution, after the gate resolved the node (expr_prog_fill_open).  The packed program
 * lives in the cache entry's stream and every clone shares it; the server binds it to kernels when a clone
 * first runs it (expr_prog_from_packed), and that binding - cells, slots - is the clone's register file.
 *
 * Nothing in here is a pointer the stream cannot carry: kernels are opcodes, tree nodes are paths from the
 * list's root column (root index + left/right/third turns), domains are packed with the stream's domain packer.
 */

#ifndef _EXPR_PROGRAM_HPP_
#define _EXPR_PROGRAM_HPP_

#include "dbtype_def.h"

struct tp_domain;

/* the kernel a step runs, as the stream carries it; the server binds a function per (opcode, type) */
enum EXPR_OPCODE
{
  EXPR_OPC_NONE = 0,
  /* leaves wired to a stable value: no step on the server, the cell points at the value */
  EXPR_OPC_COLUMN,		/* a scan column's value (TYPE_CONSTANT without a subquery): the node at path */
  EXPR_OPC_CONST,		/* a literal (TYPE_DBVAL): the node at path */
  /* leaves published by a step */
  EXPR_OPC_HOSTVAR,		/* the bound value, or the gate's converted copy: the node at path (aux = val_pos) */
  EXPR_OPC_LEAF_FETCH,		/* any other leaf: the interpreted fetch of the node at path */
  EXPR_OPC_FALLBACK,		/* a subtree with no kernel: the interpreted fetch of the node at path */
  /* arithmetic: closed when type is fixed, open (EXPR_STEPF_OPEN) when the gate gives it */
  EXPR_OPC_ADD,
  EXPR_OPC_SUB,
  EXPR_OPC_MUL,
  EXPR_OPC_DIV,
  EXPR_OPC_COERCE_NUMERIC,	/* closed NUMERIC mix: the integer side coerced to NUMERIC (aux unused) */
  EXPR_OPC_CONV,		/* open operand converter the gate chose (aux = operand side 0/1), NULL = as is */
  EXPR_OPC_JUMP_NULL_ARITH,	/* a NULL left operand makes the node NULL and skips its right side */
  EXPR_OPC_LAST
};

enum EXPR_STEP_FLAGS
{
  EXPR_STEPF_OPEN = 0x01	/* kernel / domain / converter come from the gate's resolution each execution */
};

#define EXPR_PATH_MAX 8

/* a step as packed: cells and steps are indexes, paths are turns from the root column's regu */
struct EXPR_PACKED_STEP
{
  int opcode;			/* EXPR_OPCODE */
  int type;			/* DB_TYPE of a closed arithmetic step's result; DB_TYPE_VARIABLE when open */
  int arg1;			/* input cells, -1 none */
  int arg2;
  int out;			/* output cell */
  int root;			/* the list column whose tree holds the node */
  int path_len;			/* turns from that column's regu: 0 left, 1 right, 2 third */
  int path[EXPR_PATH_MAX];
  int aux;			/* HOSTVAR: val_pos; CONV: side; closed arithmetic: 1 when both operands are NUMERIC */
  int flags;			/* EXPR_STEP_FLAGS */
  int jump_to;			/* JUMP_NULL_ARITH: the step the row continues at; -1 */
  int alias_of;			/* JUMP_NULL_ARITH: the arithmetic step whose slot it makes NULL; -1 */
  struct tp_domain *domain;	/* closed NUMERIC result: the node's domain; NULL otherwise */
};

/* one value list's program as packed into the stream */
struct EXPR_PACKED_PROG
{
  int n_steps;
  struct EXPR_PACKED_STEP *steps;
  int n_cells;
  int n_roots;			/* = the list's column count */
  int *root_cells;		/* the cell a column reads, -1 for a column the program leaves to its own fetch */
};

#endif /* _EXPR_PROGRAM_HPP_ */
