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
 * expr_gen.c - the SQL compiler's expression program generator
 *
 * Runs on the client, once per value list, right after xasl_generation built the list's REGU_VARIABLE trees
 * (pt_to_outlist).  It emits the program's STRUCTURE only - steps over cells, the lazy right-operand check, which
 * node each step reads (as a path) - and leaves to the server what the client cannot know: the kernel a node
 * whose type a bind decides takes (an OPEN step the gate fills each execution), and whether a step runs once or
 * per row (the server classifies hoisting when it binds the program, expr_prog_from_packed).
 *
 * Every visible column gets a root cell: a tree with no kernel becomes one FALLBACK step (the interpreted fetch
 * of the column), so a consumer reads every column through the program.  Columns a consumer must fetch itself
 * (hidden, UPDATE/INSERT value lists, analytic windows) have no root cell.
 */

#ident "$Id$"

#include "config.h"

#include <string.h>

#include "expr_gen.h"
#include "expr_program.hpp"
#include "parser_support.h"
#include "object_domain.h"
#include "dbtype.h"
#include "xasl.h"

#define EXPR_GEN_MAX_STEPS 128
#define EXPR_GEN_MAX_CELLS 128

typedef struct expr_gen_ctx EXPR_GEN_CTX;
struct expr_gen_ctx
{
  EXPR_PACKED_STEP steps[EXPR_GEN_MAX_STEPS];
  int n_steps;
  int n_cells;
  /* wired leaves already given a cell: the value's address is the key */
  const void *wired_ptr[EXPR_GEN_MAX_CELLS];
  int wired_cell[EXPR_GEN_MAX_CELLS];
  int n_wired;
  /* the node being compiled: root column and the turns from it */
  int root;
  int path[EXPR_PATH_MAX];
  int path_len;
  bool full;			/* a limit was hit: the list keeps its own fetch */
};

static EXPR_PACKED_STEP *
gen_step (EXPR_GEN_CTX * g, int opcode, int out)
{
  EXPR_PACKED_STEP *s;

  if (g->n_steps >= EXPR_GEN_MAX_STEPS)
    {
      g->full = true;
      return NULL;
    }
  s = &g->steps[g->n_steps++];
  memset (s, 0, sizeof (*s));
  s->opcode = opcode;
  s->type = DB_TYPE_NULL;
  s->arg1 = s->arg2 = -1;
  s->out = out;
  s->root = g->root;
  s->path_len = g->path_len;
  memcpy (s->path, g->path, sizeof (int) * g->path_len);
  s->jump_to = s->alias_of = -1;
  return s;
}

static int
gen_cell (EXPR_GEN_CTX * g)
{
  if (g->n_cells >= EXPR_GEN_MAX_CELLS)
    {
      g->full = true;
      return -1;
    }
  return g->n_cells++;
}

/* a leaf wired to a stable value: one cell per distinct address */
static int
gen_wire (EXPR_GEN_CTX * g, int opcode, const void *ptr)
{
  int i, cell;
  EXPR_PACKED_STEP *s;

  for (i = 0; i < g->n_wired; i++)
    {
      if (g->wired_ptr[i] == ptr)
	{
	  return g->wired_cell[i];
	}
    }
  cell = gen_cell (g);
  if (cell < 0)
    {
      return -1;
    }
  s = gen_step (g, opcode, cell);
  if (s == NULL)
    {
      return -1;
    }
  if (g->n_wired < EXPR_GEN_MAX_CELLS)
    {
      g->wired_ptr[g->n_wired] = ptr;
      g->wired_cell[g->n_wired] = cell;
      g->n_wired++;
    }
  return cell;
}

/* the type a node has at compile time; DB_TYPE_VARIABLE when a value decides it */
static DB_TYPE
gen_node_type (const REGU_VARIABLE * regu)
{
  switch (regu->type)
    {
    case TYPE_DBVAL:
      return DB_VALUE_DOMAIN_TYPE (&regu->value.dbval);
    case TYPE_POS_VALUE:
    case TYPE_CONSTANT:
    case TYPE_INARITH:
    case TYPE_OUTARITH:
      return regu->domain != NULL ? TP_DOMAIN_TYPE (regu->domain) : DB_TYPE_VARIABLE;
    default:
      return DB_TYPE_UNKNOWN;
    }
}

static bool
gen_numeric_side (DB_TYPE t)
{
  return t == DB_TYPE_NUMERIC || t == DB_TYPE_SHORT || t == DB_TYPE_INTEGER || t == DB_TYPE_BIGINT;
}

static int
gen_opcode_of (OPERATOR_TYPE op)
{
  switch (op)
    {
    case T_ADD:
      return EXPR_OPC_ADD;
    case T_SUB:
      return EXPR_OPC_SUB;
    case T_MUL:
      return EXPR_OPC_MUL;
    case T_DIV:
      return EXPR_OPC_DIV;
    default:
      return EXPR_OPC_NONE;
    }
}

static int gen_node (EXPR_GEN_CTX * g, const REGU_VARIABLE * regu);

/* a child: one turn deeper on the path */
static int
gen_child (EXPR_GEN_CTX * g, const REGU_VARIABLE * child, int turn)
{
  int cell;

  if (child == NULL || g->path_len >= EXPR_PATH_MAX)
    {
      return -1;
    }
  g->path[g->path_len++] = turn;
  cell = gen_node (g, child);
  g->path_len--;
  return cell;
}

/* a binary arithmetic node: closed when its types are known and a kernel exists, open when a value decides
 * them, declined (-1) when the types are known and no kernel fits (the whole root falls back) */
static int
gen_arith (EXPR_GEN_CTX * g, const REGU_VARIABLE * regu)
{
  const ARITH_TYPE *arith = regu->value.arithptr;
  const int opcode = arith != NULL ? gen_opcode_of (arith->opcode) : EXPR_OPC_NONE;
  const int mark_steps = g->n_steps, mark_cells = g->n_cells, mark_wired = g->n_wired;
  EXPR_PACKED_STEP *s, *check;
  DB_TYPE rtype, t1, t2;
  bool closed, open;
  int c1, c2, out, check_idx;

  if (opcode == EXPR_OPC_NONE || arith->pred != NULL || arith->thirdptr != NULL || arith->leftptr == NULL
      || arith->rightptr == NULL)
    {
      return -1;
    }
  rtype = gen_node_type (regu);
  t1 = gen_node_type (arith->leftptr);
  t2 = gen_node_type (arith->rightptr);
  open = (rtype == DB_TYPE_VARIABLE || t1 == DB_TYPE_VARIABLE || t2 == DB_TYPE_VARIABLE);
  closed = !open
    && (((rtype == DB_TYPE_INTEGER || rtype == DB_TYPE_BIGINT || rtype == DB_TYPE_DOUBLE) && t1 == rtype
	 && t2 == rtype && !(opcode == EXPR_OPC_DIV && rtype == DB_TYPE_DOUBLE))
	|| (rtype == DB_TYPE_NUMERIC && gen_numeric_side (t1) && gen_numeric_side (t2)));
  if (!closed && !open)
    {
      /* types known, no kernel: the interpreter (a string concatenation, a date, a double division) */
      return -1;
    }

  c1 = gen_child (g, arith->leftptr, 0);
  if (c1 < 0)
    {
      goto decline;
    }
  if (closed && rtype == DB_TYPE_NUMERIC && t1 != DB_TYPE_NUMERIC)
    {
      out = gen_cell (g);
      s = out >= 0 ? gen_step (g, EXPR_OPC_COERCE_NUMERIC, out) : NULL;
      if (s == NULL)
	{
	  goto decline;
	}
      s->arg1 = c1;
      c1 = out;
    }
  /* the interpreter fetches the right operand only for a non-NULL left one (fetch_peek_arith): the check sits
   * before the right side's steps and, on a NULL left operand, makes the node NULL and jumps past it */
  check_idx = g->n_steps;
  check = gen_step (g, EXPR_OPC_JUMP_NULL_ARITH, -1);
  if (check == NULL)
    {
      goto decline;
    }
  check->arg1 = c1;
  c2 = gen_child (g, arith->rightptr, 1);
  if (c2 < 0)
    {
      goto decline;
    }
  if (closed && rtype == DB_TYPE_NUMERIC && t2 != DB_TYPE_NUMERIC)
    {
      out = gen_cell (g);
      s = out >= 0 ? gen_step (g, EXPR_OPC_COERCE_NUMERIC, out) : NULL;
      if (s == NULL)
	{
	  goto decline;
	}
      s->arg1 = c2;
      c2 = out;
    }
  if (open)
    {
      /* the operand converters the gate resolves (plan->conv): one slot per side, NULL = the value as is */
      int cv1, cv2;

      cv1 = gen_cell (g);
      s = cv1 >= 0 ? gen_step (g, EXPR_OPC_CONV, cv1) : NULL;
      if (s == NULL)
	{
	  goto decline;
	}
      s->arg1 = c1;
      s->arg2 = c2;
      s->aux = 0;
      s->flags = EXPR_STEPF_OPEN;
      cv2 = gen_cell (g);
      s = cv2 >= 0 ? gen_step (g, EXPR_OPC_CONV, cv2) : NULL;
      if (s == NULL)
	{
	  goto decline;
	}
      s->arg1 = c2;
      s->arg2 = c1;
      s->aux = 1;
      s->flags = EXPR_STEPF_OPEN;
      c1 = cv1;
      c2 = cv2;
    }
  out = gen_cell (g);
  s = out >= 0 ? gen_step (g, opcode, out) : NULL;
  if (s == NULL)
    {
      goto decline;
    }
  s->arg1 = c1;
  s->arg2 = c2;
  if (closed)
    {
      s->type = rtype;
      s->aux = (t1 == DB_TYPE_NUMERIC && t2 == DB_TYPE_NUMERIC) ? 1 : 0;
      s->domain = (rtype == DB_TYPE_NUMERIC) ? regu->domain : NULL;
    }
  else
    {
      s->type = DB_TYPE_VARIABLE;
      s->flags = EXPR_STEPF_OPEN;
    }
  /* the check's outputs: the node's slot (alias) and the step after the node (jump) */
  check = &g->steps[check_idx];
  check->out = out;
  check->alias_of = (int) (s - g->steps);
  check->jump_to = g->n_steps;
  return out;

decline:
  if (!g->full)
    {
      /* undo this node's steps: the root falls back whole, and the interpreter evaluates its operands itself */
      g->n_steps = mark_steps;
      g->n_cells = mark_cells;
      g->n_wired = mark_wired;
    }
  return -1;
}

static int
gen_node (EXPR_GEN_CTX * g, const REGU_VARIABLE * regu)
{
  EXPR_PACKED_STEP *s;
  int cell;

  if (regu == NULL || g->full)
    {
      return -1;
    }
  if (REGU_VARIABLE_IS_FLAGED (regu, REGU_VARIABLE_APPLY_COLLATION))
    {
      /* COLLATE re-labels the value: no kernel mirrors it */
      return -1;
    }
  switch (regu->type)
    {
    case TYPE_CONSTANT:
      if (regu->xasl != NULL)
	{
	  /* a linked scalar subquery: its fetch executes the XASL first */
	  return -1;
	}
      return gen_wire (g, EXPR_OPC_COLUMN, regu->value.dbvalptr);
    case TYPE_DBVAL:
      return gen_wire (g, EXPR_OPC_CONST, &regu->value.dbval);
    case TYPE_POS_VALUE:
      cell = gen_cell (g);
      s = cell >= 0 ? gen_step (g, EXPR_OPC_HOSTVAR, cell) : NULL;
      if (s == NULL)
	{
	  return -1;
	}
      s->aux = regu->value.val_pos;
      return cell;
    case TYPE_INARITH:
    case TYPE_OUTARITH:
      return gen_arith (g, regu);
    default:
      return -1;
    }
}

/*
 * expr_gen_outlist () - the packed program of a value list, in the XASL packing buffer
 *   return: the program, or NULL when the list has no column a program would read or exceeds its limits
 *   list(in): the value list xasl_generation just built
 */
EXPR_PACKED_PROG *
expr_gen_outlist (OUTPTR_LIST * list)
{
  EXPR_GEN_CTX *g;
  EXPR_PACKED_PROG *prog = NULL;
  REGU_VARIABLE_LIST col;
  int k, any = 0;

  if (list == NULL || list->valptr_cnt <= 0 || list->valptrp == NULL)
    {
      return NULL;
    }
  g = (EXPR_GEN_CTX *) malloc (sizeof (EXPR_GEN_CTX));
  if (g == NULL)
    {
      return NULL;
    }
  memset (g, 0, sizeof (*g));
  prog = (EXPR_PACKED_PROG *) pt_alloc_packing_buf (sizeof (EXPR_PACKED_PROG));
  if (prog == NULL)
    {
      free (g);
      return NULL;
    }
  memset (prog, 0, sizeof (*prog));
  prog->n_roots = list->valptr_cnt;
  prog->root_cells = (int *) pt_alloc_packing_buf (sizeof (int) * prog->n_roots);
  if (prog->root_cells == NULL)
    {
      free (g);
      return NULL;
    }
  for (k = 0, col = list->valptrp; k < prog->n_roots && col != NULL; k++, col = col->next)
    {
      const REGU_VARIABLE *regu = &col->value;
      int cell;

      prog->root_cells[k] = -1;
      if (regu->flags & (REGU_VARIABLE_HIDDEN_COLUMN | REGU_VARIABLE_UPD_INS_LIST | REGU_VARIABLE_ANALYTIC_WINDOW))
	{
	  /* the consumer fetches these itself: a hidden sort key is not written, the others carry flag-dependent
	   * fetch semantics */
	  continue;
	}
      g->root = k;
      g->path_len = 0;
      cell = gen_node (g, regu);
      if (cell < 0 && !g->full)
	{
	  /* no kernel for the tree: the interpreted fetch of the column, as one step */
	  cell = gen_cell (g);
	  if (cell >= 0 && gen_step (g, EXPR_OPC_FALLBACK, cell) == NULL)
	    {
	      cell = -1;
	    }
	}
      if (g->full)
	{
	  free (g);
	  return NULL;
	}
      prog->root_cells[k] = cell;
      any += (cell >= 0);
    }
  if (any == 0 || g->n_steps == 0)
    {
      free (g);
      return NULL;
    }
  prog->n_steps = g->n_steps;
  prog->n_cells = g->n_cells;
  prog->steps = (EXPR_PACKED_STEP *) pt_alloc_packing_buf (sizeof (EXPR_PACKED_STEP) * prog->n_steps);
  if (prog->steps == NULL)
    {
      free (g);
      return NULL;
    }
  memcpy (prog->steps, g->steps, sizeof (EXPR_PACKED_STEP) * prog->n_steps);
  free (g);
  return prog;
}
