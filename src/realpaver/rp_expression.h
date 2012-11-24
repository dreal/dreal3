/****************************************************************************
 * RealPaver v. 1.0                                                         *
 *--------------------------------------------------------------------------*
 * Author: Laurent Granvilliers                                             *
 * Copyright (c) 1999-2003 Institut de Recherche en Informatique de Nantes  *
 * Copyright (c) 2004-2006 Laboratoire d'Informatique de Nantes Atlantique  *
 *--------------------------------------------------------------------------*
 * RealPaver is distributed WITHOUT ANY WARRANTY. Read the associated       *
 * COPYRIGHT file for more details.                                         *
 *--------------------------------------------------------------------------*
 * rp_expression.h                                                          *
 ****************************************************************************/

#ifndef RP_EXPRESSION_H
#define RP_EXPRESSION_H 1

#ifdef __cplusplus
extern "C" {
#endif

#include "rp_expression_symbol.h"

/* ------------------------ */
/* Type for local variables */
/* ------------------------ */

/* Management of nodes for fast evaluation wrt. one variable */
#define rp_vector_node           rp_vector
#define rp_vector_node_elem(v,i) (rp_erep)rp_vector_elem(v,i)
int     rp_node_vector_cmp       (void * x, const void * y);
void    rp_node_vector_free      (void * x);
void    rp_node_vector_display   (FILE * out, void * x);
void    rp_vector_node_create    (rp_vector * v);

typedef struct
{
  int var;              /* global variable index                          */
  int occur;            /* number of occurrences in the expression        */
  rp_erep node;         /* the unique variable node                       */
  rp_interval domain;   /* possibility of memozizing a local context      */
  rp_vector dep;        /* nodes of expression depending on this variable */
}
rp_expr_arg;

typedef struct
{
  int size;           /* number of variables in the expression */
  rp_expr_arg * ptr;  /* array of variables                    */
}
rp_expr_args_def;

typedef rp_expr_args_def rp_expr_args[1];

#define rp_expr_args_size(a)      (a)[0].size
#define rp_expr_args_ptr(a)       (a)[0].ptr
#define rp_expr_args_occur(a,i)   (a)[0].ptr[i].occur
#define rp_expr_args_node(a,i)    (a)[0].ptr[i].node
#define rp_expr_args_var(a,i)     (a)[0].ptr[i].var
#define rp_expr_args_domain(a,i)  (a)[0].ptr[i].domain
#define rp_expr_args_dep(a,i)     (a)[0].ptr[i].dep

/* Creation of an array of local variables */
void rp_expr_args_create  (rp_expr_args * a);

/* Destruction of an array of local variables */
void rp_expr_args_destroy (rp_expr_args * a);


/* ------------------- */
/* The expression type */
/* ------------------- */

typedef struct
{
  rp_expr_args lvar;   /* array of variables                 */
  rp_erep rep;         /* the tree-representation            */
  int derivable;       /* is the expression derivable        */
  int occur;           /* number of occurrences of variables */
}
rp_expression_def;
typedef rp_expression_def * rp_expression;

#define rp_expression_arity(e)        rp_expr_args_size((e)->lvar)
#define rp_expression_rep(e)          (e)->rep
#define rp_expression_lvar(e)         (e)->lvar
#define rp_expression_var(e,i)        rp_expr_args_var((e)->lvar,i)
#define rp_expression_derivable(e)    (e)->derivable
#define rp_expression_occur(e)        (e)->occur
#define rp_expression_occur_var(e,i)  rp_expr_args_occur((e)->lvar,i)

/* Creation of an expression e represented by f */
/* f is destroyed                               */
void rp_expression_create (rp_expression * e, rp_erep * f);

/* Destruction */
void rp_expression_destroy (rp_expression * e);

/* Copy */
void rp_expression_copy (rp_expression * e, rp_expression src);

/* Display e on out */
void rp_expression_display (FILE * out, rp_expression e,
			    rp_vector_variable vars,
			    int digits, int mode);

#define rp_expression_display_simple(f,a)     \
  rp_expression_display(stdout,f,a,8,RP_INTERVAL_MODE_BOUND)

#define rp_expression_display_simple_nl(f,a) \
  rp_expression_display_simple(f,a); \
  printf("\n")

/* rp_expression_val(e) := e(b)                     */
/* Returns false if the resulting interval is empty */
int rp_expression_eval (rp_expression e, rp_box b);

#define rp_expression_val(e) rp_erep_val(rp_expression_rep(e))

/* rp_expression_val(e) := e(b)                     */
/* Only the nodes depending on v are evaluated      */
/* Returns false if the resulting interval is empty */
int rp_expression_eval_single (rp_expression e, rp_box b, int v);

/* rp_expression_val(e) := mean value(e)(b)         */
/* e(mid(b)) + sum_i (de/dxi(b)*(bi - mid(bi)))     */
/* Returns false if the resulting interval is empty */
int rp_expression_eval_center (rp_expression e, rp_box b);

/* rp_expression_val(e) := e(b)                     */
/* Use of Moore's theorem and monotonicity test     */
/* Returns false if the resulting interval is empty */
int rp_expression_eval_best (rp_expression e, rp_box b);

/* Projection onto every subterm of e such that inf(i)<=e<=sup(e) */
/* b is intersected with the projections onto the variables       */
/* Returns false if an empty interval is computed                 */
int rp_expression_project (rp_expression e, rp_interval i, rp_box b);

/* Computation of all the partial derivatives of e   */
/* The expression is first evaluated on b            */
/* Returns false if at least one derivative is empty */
int rp_expression_deriv_num (rp_expression e, rp_box b);

/* Copy in de the value of d(e)/d(v) after the call of rp_expression_deriv_num */
/* Returns false if v does not occur in e                                      */
/* v is a global index                                                         */
int rp_expression_deriv_val (rp_interval de, rp_expression e, int v);

/* i-th derivative of e */
#define rp_expression_deriv_local_val(e,i) \
   rp_erep_deriv(rp_expr_args_node(rp_expression_lvar(e),i))

/* de := d(e)/d(v) */
void rp_expression_deriv_symb (rp_expression * de, rp_expression e, int v);

#ifdef __cplusplus
}
#endif

#endif /* RP_EXPRESSION_H */
