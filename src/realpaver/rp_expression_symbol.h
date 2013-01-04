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
 * rp_expression_symbol.h                                                   *
 ****************************************************************************/

#ifndef RP_EXPRESSION_SYMBOL_H
#define RP_EXPRESSION_SYMBOL_H 1

#define rp_inline inline

#ifdef __cplusplus
extern "C" {
#endif

#include "rp_interval.h"
#include "rp_variable.h"
#include "rp_box.h"
#include "rp_projection.h"

/* ------------ */
/* Term symbols */
/* ------------ */
#define RP_SYMBOL_NO          -1

#define RP_SYMBOL_ADD          0
#define RP_SYMBOL_ADD_R_I      1
#define RP_SYMBOL_SUB          2
#define RP_SYMBOL_SUB_R_I      3
#define RP_SYMBOL_SUB_I_R      4
#define RP_SYMBOL_MUL          5
#define RP_SYMBOL_MUL_R_I      6
#define RP_SYMBOL_MUL_RNEG_I   7
#define RP_SYMBOL_MUL_RPOS_I   8
#define RP_SYMBOL_DIV          9
#define RP_SYMBOL_DIV_I_R     10
#define RP_SYMBOL_DIV_I_RPOS  11
#define RP_SYMBOL_DIV_I_RNEG  12
#define RP_SYMBOL_DIV_R_I     13
#define RP_SYMBOL_DIV_RPOS_I  14
#define RP_SYMBOL_DIV_RNEG_I  15
#define RP_SYMBOL_POW         16
#define RP_SYMBOL_NEG         17
#define RP_SYMBOL_SQR         18
#define RP_SYMBOL_SQRT        19
#define RP_SYMBOL_EXP         20
#define RP_SYMBOL_LOG         21
#define RP_SYMBOL_SIN         22
#define RP_SYMBOL_COS         23
#define RP_SYMBOL_TAN         24
#define RP_SYMBOL_COSH        25
#define RP_SYMBOL_SINH        26
#define RP_SYMBOL_TANH        27
#define RP_SYMBOL_ASIN        28
#define RP_SYMBOL_ACOS        29
#define RP_SYMBOL_ATAN        30
#define RP_SYMBOL_ASINH       31
#define RP_SYMBOL_ACOSH       32
#define RP_SYMBOL_ATANH       33
#define RP_SYMBOL_ABS         34
#define RP_SYMBOL_MIN         35
#define RP_SYMBOL_MAX         36

/* ---------------------------------- */
/* Tree-representation of expressions */
/* ---------------------------------- */

#define RP_EREP_NODE_VAR 0   /* variable node type information  */
#define RP_EREP_NODE_OP  2   /* operation node type information */
#define RP_EREP_NODE_CST 4   /* constant node type information  */

/* Values at nodes */
typedef union
{
  int var;      /* index of the variable          */
  int symb;     /* index of operation symbol      */
  char * cst;   /* string representing a constant */ //sean: what is this?
}
rp_erep_node;

/* Additional values at nodes for algorithmic purposes */
typedef struct
{
  rp_interval val;    /* bottom-up interval evaluation */
  rp_interval proj;   /* top_down projection           */
  rp_interval deriv;  /* top_down numerical derivation */
}
rp_erep_label;

struct rp_erep_cell
{
  struct rp_erep_cell ** childs;  /* sub-expressions      */
  int arity;             /* number of childs     */
  int type;              /* node type            */
  int ref;               /* number of references */
  rp_erep_node node;     /* the node             */
  rp_erep_label label;   /* labels               */
};

typedef struct rp_erep_cell * rp_erep;

#define rp_erep_childs(f)      (f)->childs
#define rp_erep_left(f)        (f)->childs[0]
#define rp_erep_right(f)       (f)->childs[1]
#define rp_erep_sub(f)         (f)->childs[0]
#define rp_erep_arity(f)       (f)->arity
#define rp_erep_child(f,i)     (f)->childs[i]
#define rp_erep_type(f)        (f)->type
#define rp_erep_ref(f)         (f)->ref
#define rp_erep_symb(f)        (f)->node.symb
#define rp_erep_cst(f)         (f)->node.cst
#define rp_erep_var(f)         (f)->node.var
#define rp_erep_val(f)         (f)->label.val
#define rp_erep_proj(f)        (f)->label.proj
#define rp_erep_deriv(f)       (f)->label.deriv

/* Direct access to left and right nodes of the expression f */
#define rp_erep_sub_type(f)    rp_erep_type(rp_erep_sub(f))
#define rp_erep_sub_ref(f)     rp_erep_ref(rp_erep_sub(f))
#define rp_erep_sub_symb(f)    rp_erep_symb(rp_erep_sub(f))
#define rp_erep_sub_cst(f)     rp_erep_cst(rp_erep_sub(f))
#define rp_erep_sub_var(f)     rp_erep_var(rp_erep_sub(f))
#define rp_erep_sub_val(f)     rp_erep_val(rp_erep_sub(f))
#define rp_erep_sub_proj(f)    rp_erep_proj(rp_erep_sub(f))
#define rp_erep_sub_deriv(f)   rp_erep_deriv(rp_erep_sub(f))
#define rp_erep_left_type(f)   rp_erep_type(rp_erep_left(f))
#define rp_erep_left_ref(f)    rp_erep_ref(rp_erep_left(f))
#define rp_erep_left_symb(f)   rp_erep_symb(rp_erep_left(f))
#define rp_erep_left_cst(f)    rp_erep_cst(rp_erep_left(f))
#define rp_erep_left_var(f)    rp_erep_var(rp_erep_left(f))
#define rp_erep_left_val(f)    rp_erep_val(rp_erep_left(f))
#define rp_erep_left_proj(f)   rp_erep_proj(rp_erep_left(f))
#define rp_erep_left_deriv(f)  rp_erep_deriv(rp_erep_left(f))
#define rp_erep_right_type(f)  rp_erep_type(rp_erep_right(f))
#define rp_erep_right_ref(f)   rp_erep_ref(rp_erep_right(f))
#define rp_erep_right_symb(f)  rp_erep_symb(rp_erep_right(f))
#define rp_erep_right_cst(f)   rp_erep_cst(rp_erep_right(f))
#define rp_erep_right_var(f)   rp_erep_var(rp_erep_right(f))
#define rp_erep_right_val(f)   rp_erep_val(rp_erep_right(f))
#define rp_erep_right_proj(f)  rp_erep_proj(rp_erep_right(f))
#define rp_erep_right_deriv(f) rp_erep_deriv(rp_erep_right(f))

/* Creation of a null expression */
void rp_erep_create (rp_erep * f);

/* Creation of an expression equivalent to v */
void rp_erep_create_var (rp_erep * f, int v);

/* Creation of an expression equivalent to a number */
/* which is enclosed by i and represented by s      */
void rp_erep_create_cst (rp_erep * f, const char * s, rp_interval i);

/* Creation of an expression equivalent to op(l) */
void rp_erep_create_unary (rp_erep * f, int op, rp_erep l);

/* Creation of an expression equivalent to op(l,r) */
void rp_erep_create_binary (rp_erep * f, int op,
			    rp_erep l, rp_erep r);

/* Destruction of an expression */
void rp_erep_destroy (rp_erep * f);

/* f := src */
void rp_erep_set (rp_erep * f, rp_erep src);

/* f := a new expression equivalent to src */
/* nothing is shared between f and src     */
void rp_erep_copy (rp_erep * f, rp_erep src);

/* Replace every occurrence of var with a copy of src */
void rp_erep_replace(rp_erep * f, int var, rp_erep src);

/* Count the number of nodes in f */
int rp_erep_count_node (rp_erep f);

/* Display f on out */
void rp_erep_display (FILE* out, rp_erep f,
		      rp_vector_variable vars,
		      int digits, int mode);

#define rp_erep_display_bounds(o,f,a,d) \
  rp_erep_display(o,f,a,d,RP_INTERVAL_MODE_BOUND)

#define rp_erep_display_midpoint(o,f,a,d) \
  rp_erep_display(o,f,a,d,RP_INTERVAL_MODE_MID)

#define rp_erep_display_simple(f,a)	\
  rp_erep_display(stdout,f,a,8,RP_INTERVAL_MODE_BOUND)

#define rp_erep_display_simple_nl(f,a) \
  rp_erep_display_simple(f,a); \
  printf("\n")

/* Evaluation of f on b                             */
/* Returns false if the resulting interval is empty */
int rp_erep_eval (rp_erep f, rp_box b);

/* Projection onto every subterm of f                          */
/* b is intersected with the projections onto the variables    */
/* Returns false if an empty interval is computed              */
int rp_erep_project (rp_erep f, rp_box b);

/* Returns true if f is derivable */
int rp_erep_derivable (rp_erep f);

/* Computes all the partial derivatives of f */
int rp_erep_deriv_num (rp_erep f);

/* df := d(f)/d(v) */
void rp_erep_deriv_symb (rp_erep * df, rp_erep f, int v);

/* ----------------------------- */
/* Simplification of expressions */
/* ----------------------------- */

void rp_erep_shift_child(rp_erep * f);

int rp_erep_is_present  (rp_erep f, int v);
int rp_erep_is_equal    (rp_erep f, rp_erep g);
int rp_erep_is_constant (rp_erep f);
int rp_erep_is_rational (rp_erep f, long * sign, long * num, long * den);
int rp_erep_is_integer  (rp_erep f, long * n);
int rp_erep_is_add      (rp_erep f);
int rp_erep_is_sub      (rp_erep f);
int rp_erep_is_mul      (rp_erep f);
int rp_erep_is_div      (rp_erep f);
int rp_erep_is_zero     (rp_erep f);
int rp_erep_is_one      (rp_erep f);

int rp_erep_simplify_constant (rp_erep * f);
int rp_erep_simplify_mul_inv  (rp_erep * f);
int rp_erep_simplify_mul_one  (rp_erep * f);
int rp_erep_simplify_mul_zero (rp_erep * f);
int rp_erep_simplify_add_zero (rp_erep * f);
int rp_erep_simplify_sub_zero (rp_erep * f);
int rp_erep_simplify_sub_same (rp_erep * f);
int rp_erep_simplify_div_zero (rp_erep * f);
int rp_erep_simplify_div_one  (rp_erep * f);
int rp_erep_simplify_div_same (rp_erep * f);
int rp_erep_simplify_pow      (rp_erep * f);
int rp_erep_simplify_div_pow  (rp_erep * f);
int rp_erep_simplify_sum      (rp_erep * f);
int rp_erep_simplify_prod     (rp_erep * f);
void rp_erep_simplify_symbols (rp_erep * f);

/* Simplification of f */
void rp_erep_simplify (rp_erep * f);

/* ---------------------------- */
/* Symbols evaluation functions */
/* ---------------------------- */

typedef int (* rp_symbol_eval) (rp_interval, rp_interval, rp_interval);

static rp_inline
int rp_eval_add(rp_interval result, rp_interval i, rp_interval j)
{
  rp_interval_add(result,i,j);
  return( !rp_interval_empty(result) );
}
static rp_inline
int rp_eval_add_r_i(rp_interval result, rp_interval i, rp_interval j)
{
  rp_interval_add_r_i(result,i,j);
  return( !rp_interval_empty(result) );
}
static rp_inline
int rp_eval_sub(rp_interval result, rp_interval i, rp_interval j)
{
  rp_interval_sub(result,i,j);
  return( !rp_interval_empty(result) );
}
static rp_inline
int rp_eval_sub_r_i(rp_interval result, rp_interval i, rp_interval j)
{
  rp_interval_sub_r_i(result,i,j);
  return( !rp_interval_empty(result) );
}
static rp_inline
int rp_eval_sub_i_r(rp_interval result, rp_interval i, rp_interval j)
{
  rp_interval_sub_i_r(result,i,j);
  return( !rp_interval_empty(result) );
}
static rp_inline
int rp_eval_mul(rp_interval result, rp_interval i, rp_interval j)
{
  rp_interval_mul(result,i,j);
  return( !rp_interval_empty(result) );
}
static rp_inline
int rp_eval_mul_r_i(rp_interval result, rp_interval i, rp_interval j)
{
  rp_interval_mul_r_i(result,i,j);
  return( !rp_interval_empty(result) );
}
static rp_inline
int rp_eval_mul_rneg_i(rp_interval result, rp_interval i, rp_interval j)
{
  rp_interval_mul_rneg_i(result,i,j);
  return( !rp_interval_empty(result) );
}
static rp_inline
int rp_eval_mul_rpos_i(rp_interval result, rp_interval i, rp_interval j)
{
  rp_interval_mul_rpos_i(result,i,j);
  return( !rp_interval_empty(result) );
}
static rp_inline
int rp_eval_div(rp_interval result, rp_interval i, rp_interval j)
{
  rp_interval_div(result,i,j);
  return( !rp_interval_empty(result) );
}
static rp_inline
int rp_eval_div_i_r(rp_interval result, rp_interval i, rp_interval j)
{
  rp_interval_div_i_r(result,i,j);
  return( !rp_interval_empty(result) );
}
static rp_inline
int rp_eval_div_i_rpos(rp_interval result, rp_interval i, rp_interval j)
{
  rp_interval_div_i_rpos(result,i,j);
  return( !rp_interval_empty(result) );
}
static rp_inline
int rp_eval_div_i_rneg(rp_interval result, rp_interval i, rp_interval j)
{
  rp_interval_div_i_rneg(result,i,j);
  return( !rp_interval_empty(result) );
}
static rp_inline
int rp_eval_div_r_i(rp_interval result, rp_interval i, rp_interval j)
{
  rp_interval_div_r_i(result,i,j);
  return( !rp_interval_empty(result) );
}
static rp_inline
int rp_eval_div_rpos_i(rp_interval result, rp_interval i, rp_interval j)
{
  rp_interval_div_rpos_i(result,i,j);
  return( !rp_interval_empty(result) );
}
static rp_inline
int rp_eval_div_rneg_i(rp_interval result, rp_interval i, rp_interval j)
{
  rp_interval_div_rneg_i(result,i,j);
  return( !rp_interval_empty(result) );
}
static rp_inline
int rp_eval_pow(rp_interval result, rp_interval i, rp_interval j)
{
  rp_interval_pow(result,i,j);
  return( !rp_interval_empty(result) );
}
static rp_inline
int rp_eval_neg(rp_interval result, rp_interval i, rp_interval j)
{
  rp_interval_neg(result,i);
  return( !rp_interval_empty(result) );
}
static rp_inline
int rp_eval_sqr(rp_interval result, rp_interval i, rp_interval j)
{
  rp_interval_sqr(result,i);
  return( !rp_interval_empty(result) );
}
static rp_inline
int rp_eval_sqrt(rp_interval result, rp_interval i, rp_interval j)
{
  rp_interval_sqrt(result,i);
  return( !rp_interval_empty(result) );
}
static rp_inline
int rp_eval_exp(rp_interval result, rp_interval i, rp_interval j)
{
  rp_interval_exp(result,i);
  return( !rp_interval_empty(result) );
}
static rp_inline
int rp_eval_log(rp_interval result, rp_interval i, rp_interval j)
{
  rp_interval_log(result,i);
  return( !rp_interval_empty(result) );
}
static rp_inline
int rp_eval_sin(rp_interval result, rp_interval i, rp_interval j)
{
  rp_interval_sin(result,i);
  return( !rp_interval_empty(result) );
}
static rp_inline
int rp_eval_cos(rp_interval result, rp_interval i, rp_interval j)
{
  rp_interval_cos(result,i);
  return( !rp_interval_empty(result) );
}
static rp_inline
int rp_eval_tan(rp_interval result, rp_interval i, rp_interval j)
{
  rp_interval_tan(result,i);
  return( !rp_interval_empty(result) );
}
static rp_inline
int rp_eval_sinh(rp_interval result, rp_interval i, rp_interval j)
{
  rp_interval_sinh(result,i);
  return( !rp_interval_empty(result) );
}
static rp_inline
int rp_eval_cosh(rp_interval result, rp_interval i, rp_interval j)
{
  rp_interval_cosh(result,i);
  return( !rp_interval_empty(result) );
}
static rp_inline
int rp_eval_tanh(rp_interval result, rp_interval i, rp_interval j)
{
  rp_interval_tanh(result,i);
  return( !rp_interval_empty(result) );
}
static rp_inline
int rp_eval_asin(rp_interval result, rp_interval i, rp_interval j)
{
  rp_interval_asin(result,i);
  return( !rp_interval_empty(result) );
}
static rp_inline
int rp_eval_acos(rp_interval result, rp_interval i, rp_interval j)
{
  rp_interval_acos(result,i);
  return( !rp_interval_empty(result) );
}
static rp_inline
int rp_eval_atan(rp_interval result, rp_interval i, rp_interval j)
{
  rp_interval_atan(result,i);
  return( !rp_interval_empty(result) );
}
static rp_inline
int rp_eval_asinh(rp_interval result, rp_interval i, rp_interval j)
{
  rp_interval_asinh(result,i);
  return( !rp_interval_empty(result) );
}
static rp_inline
int rp_eval_acosh(rp_interval result, rp_interval i, rp_interval j)
{
  rp_interval_acosh(result,i);
  return( !rp_interval_empty(result) );
}
static rp_inline
int rp_eval_atanh(rp_interval result, rp_interval i, rp_interval j)
{
  rp_interval_atanh(result,i);
  return( !rp_interval_empty(result) );
}
static rp_inline
int rp_eval_abs(rp_interval result, rp_interval i, rp_interval j)
{
  rp_interval_abs(result,i);
  return( !rp_interval_empty(result) );
}
static rp_inline
int rp_eval_min(rp_interval result, rp_interval i, rp_interval j)
{
  rp_interval_min(result,i,j);
  return( !rp_interval_empty(result) );
}
static rp_inline
int rp_eval_max(rp_interval result, rp_interval i, rp_interval j)
{
  rp_interval_max(result,i,j);
  return( !rp_interval_empty(result) );
}

/* ---------------------------- */
/* Symbols projection functions */
/* ---------------------------- */

typedef int (* rp_symbol_project) (rp_erep);

static rp_inline
int rp_project_add(rp_erep f)
{
  return( rp_project_add_fst(rp_erep_left_proj(f),
			     rp_erep_proj(f),
			     rp_erep_left_val(f),
			     rp_erep_right_val(f))
	  &&
	  rp_project_add_snd(rp_erep_right_proj(f),
			     rp_erep_proj(f),
			     rp_erep_left_val(f),
			     rp_erep_right_val(f)) );
}
static rp_inline
int rp_project_add_r_i(rp_erep f)
{
  return( rp_project_add_snd(rp_erep_right_proj(f),
			     rp_erep_proj(f),
			     rp_erep_left_val(f),
			     rp_erep_right_val(f)) );
}
static rp_inline
int rp_project_sub(rp_erep f)
{
  return( rp_project_sub_fst(rp_erep_left_proj(f),
			     rp_erep_proj(f),
			     rp_erep_left_val(f),
			     rp_erep_right_val(f))
	  &&
	  rp_project_sub_snd(rp_erep_right_proj(f),
			     rp_erep_proj(f),
			     rp_erep_left_val(f),
			     rp_erep_right_val(f)) );
}
static rp_inline
int rp_project_sub_r_i(rp_erep f)
{
  return( rp_project_sub_snd(rp_erep_right_proj(f),
			     rp_erep_proj(f),
			     rp_erep_left_val(f),
			     rp_erep_right_val(f)) );
}
static rp_inline
int rp_project_sub_i_r(rp_erep f)
{
  return( rp_project_sub_fst(rp_erep_left_proj(f),
			     rp_erep_proj(f),
			     rp_erep_left_val(f),
			     rp_erep_right_val(f)) );
}
static rp_inline
int rp_project_mul(rp_erep f)
{
  return( rp_project_mul_fst(rp_erep_left_proj(f),
			     rp_erep_proj(f),
			     rp_erep_left_val(f),
			     rp_erep_right_val(f))
	  &&
	  rp_project_mul_snd(rp_erep_right_proj(f),
			     rp_erep_proj(f),
			     rp_erep_left_val(f),
			     rp_erep_right_val(f)) );
}
static rp_inline
int rp_project_mul_r_i(rp_erep f)
{
  return( rp_project_mul_snd(rp_erep_right_proj(f),
			     rp_erep_proj(f),
			     rp_erep_left_val(f),
			     rp_erep_right_val(f)) );
}
static rp_inline
int rp_project_mul_rneg_i(rp_erep f)
{
  return( rp_project_mul_snd(rp_erep_right_proj(f),
			     rp_erep_proj(f),
			     rp_erep_left_val(f),
			     rp_erep_right_val(f)) );
}
static rp_inline
int rp_project_mul_rpos_i(rp_erep f)
{
  return( rp_project_mul_snd(rp_erep_right_proj(f),
			     rp_erep_proj(f),
			     rp_erep_left_val(f),
			     rp_erep_right_val(f)) );
}
static rp_inline
int rp_project_div(rp_erep f)
{
  return( rp_project_div_fst(rp_erep_left_proj(f),
			     rp_erep_proj(f),
			     rp_erep_left_val(f),
			     rp_erep_right_val(f))
	  &&
	  rp_project_div_snd(rp_erep_right_proj(f),
			     rp_erep_proj(f),
			     rp_erep_left_val(f),
			     rp_erep_right_val(f)) );
}
static rp_inline
int rp_project_div_i_r(rp_erep f)
{
  return( rp_project_div_fst(rp_erep_left_proj(f),
			     rp_erep_proj(f),
			     rp_erep_left_val(f),
			     rp_erep_right_val(f)) );
}
static rp_inline
int rp_project_div_i_rpos(rp_erep f)
{
  return( rp_project_div_fst(rp_erep_left_proj(f),
			     rp_erep_proj(f),
			     rp_erep_left_val(f),
			     rp_erep_right_val(f)) );
}
static rp_inline
int rp_project_div_i_rneg(rp_erep f)
{
  return( rp_project_div_fst(rp_erep_left_proj(f),
			     rp_erep_proj(f),
			     rp_erep_left_val(f),
			     rp_erep_right_val(f)) );
}
static rp_inline
int rp_project_div_r_i(rp_erep f)
{
  return( rp_project_div_snd(rp_erep_right_proj(f),
			     rp_erep_proj(f),
			     rp_erep_left_val(f),
			     rp_erep_right_val(f)) );
}
static rp_inline
int rp_project_div_rpos_i(rp_erep f)
{
  return( rp_project_div_snd(rp_erep_right_proj(f),
			     rp_erep_proj(f),
			     rp_erep_left_val(f),
			     rp_erep_right_val(f)) );
}
static rp_inline
int rp_project_div_rneg_i(rp_erep f)
{
  return( rp_project_div_snd(rp_erep_right_proj(f),
			     rp_erep_proj(f),
			     rp_erep_left_val(f),
			     rp_erep_right_val(f)) );
}
static rp_inline
int rp_project_pow(rp_erep f)
{
  return( rp_project_pow_fst(rp_erep_left_proj(f),
			     rp_erep_proj(f),
			     rp_erep_left_val(f),
			     rp_erep_right_val(f)) );
}
static rp_inline
int rp_project_neg(rp_erep f)
{
  return( rp_project_neg_fst(rp_erep_left_proj(f),
			     rp_erep_proj(f),
			     rp_erep_left_val(f)) );
}
static rp_inline
int rp_project_sqr(rp_erep f)
{
  return( rp_project_sqr_fst(rp_erep_left_proj(f),
			     rp_erep_proj(f),
			     rp_erep_left_val(f)) );
}
static rp_inline
int rp_project_sqrt(rp_erep f)
{
  return( rp_project_sqrt_fst(rp_erep_left_proj(f),
			      rp_erep_proj(f),
			      rp_erep_left_val(f)) );
}
static rp_inline
int rp_project_exp(rp_erep f)
{
  return( rp_project_exp_fst(rp_erep_left_proj(f),
			     rp_erep_proj(f),
			     rp_erep_left_val(f)) );
}
static rp_inline
int rp_project_log(rp_erep f)
{
  return( rp_project_log_fst(rp_erep_left_proj(f),
			     rp_erep_proj(f),
			     rp_erep_left_val(f)) );
}
static rp_inline
int rp_project_sin(rp_erep f)
{
  return( rp_project_sin_fst(rp_erep_left_proj(f),
			     rp_erep_proj(f),
			     rp_erep_left_val(f)) );
}
static rp_inline
int rp_project_cos(rp_erep f)
{
  return( rp_project_cos_fst(rp_erep_left_proj(f),
			     rp_erep_proj(f),
			     rp_erep_left_val(f)) );
}
static rp_inline
int rp_project_tan(rp_erep f)
{
  return( rp_project_tan_fst(rp_erep_left_proj(f),
			     rp_erep_proj(f),
			     rp_erep_left_val(f)) );
}
static rp_inline
int rp_project_sinh(rp_erep f)
{
  return( rp_project_sinh_fst(rp_erep_left_proj(f),
			      rp_erep_proj(f),
			      rp_erep_left_val(f)) );
}
static rp_inline
int rp_project_cosh(rp_erep f)
{
  return( rp_project_cosh_fst(rp_erep_left_proj(f),
			      rp_erep_proj(f),
			      rp_erep_left_val(f)) );
}
static rp_inline
int rp_project_tanh(rp_erep f)
{
  return( rp_project_tanh_fst(rp_erep_left_proj(f),
			      rp_erep_proj(f),
			      rp_erep_left_val(f)) );
}
static rp_inline
int rp_project_asin(rp_erep f)
{
  return( rp_project_asin_fst(rp_erep_left_proj(f),
			      rp_erep_proj(f),
			      rp_erep_left_val(f)) );
}
static rp_inline
int rp_project_acos(rp_erep f)
{
  return( rp_project_acos_fst(rp_erep_left_proj(f),
			      rp_erep_proj(f),
			      rp_erep_left_val(f)) );
}
static rp_inline
int rp_project_atan(rp_erep f)
{
  return( rp_project_atan_fst(rp_erep_left_proj(f),
			      rp_erep_proj(f),
			      rp_erep_left_val(f)) );
}
static rp_inline
int rp_project_asinh(rp_erep f)
{
  return( rp_project_asinh_fst(rp_erep_left_proj(f),
			       rp_erep_proj(f),
			       rp_erep_left_val(f)) );
}
static rp_inline
int rp_project_acosh(rp_erep f)
{
  return( rp_project_acosh_fst(rp_erep_left_proj(f),
			       rp_erep_proj(f),
			       rp_erep_left_val(f)) );
}
static rp_inline
int rp_project_atanh(rp_erep f)
{
  return( rp_project_atanh_fst(rp_erep_left_proj(f),
			       rp_erep_proj(f),
			       rp_erep_left_val(f)) );
}
static rp_inline
int rp_project_abs(rp_erep f)
{
  return( rp_project_abs_fst(rp_erep_left_proj(f),
			     rp_erep_proj(f),
			     rp_erep_left_val(f)) );
}
static rp_inline
int rp_project_min(rp_erep f)
{
  return( rp_project_min_fst(rp_erep_left_proj(f),
			     rp_erep_proj(f),
			     rp_erep_left_val(f),
			     rp_erep_right_val(f))
	  &&
	  rp_project_min_snd(rp_erep_right_proj(f),
			     rp_erep_proj(f),
			     rp_erep_left_val(f),
			     rp_erep_right_val(f)) );
}
static rp_inline
int rp_project_max(rp_erep f)
{
  return( rp_project_max_fst(rp_erep_left_proj(f),
			     rp_erep_proj(f),
			     rp_erep_left_val(f),
			     rp_erep_right_val(f))
	  &&
	  rp_project_max_snd(rp_erep_right_proj(f),
			     rp_erep_proj(f),
			     rp_erep_left_val(f),
			     rp_erep_right_val(f)) );
}

/* -------------------------------------- */
/* Symbols numerical derivation functions */
/* -------------------------------------- */

typedef int (* rp_symbol_deriv_num) (rp_erep);

/* Implementation of a chain rule                                            */
/* let e be an expression, let f be a subterm of e and let u be a child of f */
/* then we have: d(e)/d(u) = d(e)/d(f) * d(f)/d(u)                           */
/* d(e)/d(f) is computed recursively and d(f)/d(u) corresponds to the usual  */
/* derivation rules, e.g., d(sin(u))/d(u) = cos(u)                           */

/* New contribution i to the derivative wrt. f */
static rp_inline
void rp_deriv_set(rp_erep f, rp_interval i)
{
  if (rp_erep_type(f)==RP_EREP_NODE_VAR)
  {
    rp_interval aux;
    rp_interval_copy(aux,rp_erep_deriv(f));
    rp_interval_add(rp_erep_deriv(f),aux,i);
  }
  else
  {
    rp_interval_copy(rp_erep_deriv(f),i);
  }
}
static rp_inline
int rp_deriv_num_add(rp_erep f)               /* d(u+v)/d(u) = 1 */
{                                             /* d(u+v)/d(v) = 1 */
  rp_deriv_set(rp_erep_left(f),rp_erep_deriv(f));
  rp_deriv_set(rp_erep_right(f),rp_erep_deriv(f));
  return( 1 );
}
static rp_inline
int rp_deriv_num_add_r_i(rp_erep f)           /* d(u+v)/du = 1 */
{
  rp_deriv_set(rp_erep_right(f),rp_erep_deriv(f));
  return( 1 );
}
static rp_inline
int rp_deriv_num_sub(rp_erep f)               /* d(u-v)/d(u) = 1  */
{                                             /* d(u-v)/d(v) = -1 */
  rp_interval i;
  rp_deriv_set(rp_erep_left(f),rp_erep_deriv(f));
  rp_interval_neg(i,rp_erep_deriv(f));
  rp_deriv_set(rp_erep_right(f),i);
  return( 1 );
}
static rp_inline
int rp_deriv_num_sub_r_i(rp_erep f)           /* d(u-v)/d(v) = -1 */
{
  rp_interval i;
  rp_interval_neg(i,rp_erep_deriv(f));
  rp_deriv_set(rp_erep_right(f),i);
  return( 1 );
}
static rp_inline
int rp_deriv_num_sub_i_r(rp_erep f)           /* d(u-v)/d(u) = 1  */
{
  rp_deriv_set(rp_erep_left(f),rp_erep_deriv(f));
  return( 1 );
}
static rp_inline
int rp_deriv_num_mul(rp_erep f)              /* d(u*v)/d(u) = v */
{                                            /* d(u*v)/d(v) = u */
  rp_interval i, j;
  rp_interval_mul(i,rp_erep_deriv(f),rp_erep_right_val(f));
  rp_deriv_set(rp_erep_left(f),i);
  rp_interval_mul(j,rp_erep_deriv(f),rp_erep_left_val(f));
  rp_deriv_set(rp_erep_right(f),j);
  return( 1 );
}
static rp_inline
int rp_deriv_num_mul_r_i(rp_erep f)          /* d(u*v)/d(v) = u */
{
  rp_interval i;
  rp_interval_mul_r_i(i,rp_erep_left_val(f),rp_erep_deriv(f));
  rp_deriv_set(rp_erep_right(f),i);
  return( 1 );
}
static rp_inline
int rp_deriv_num_mul_rneg_i(rp_erep f)       /* d(u*v)/d(v) = u */
{
  rp_interval i;
  rp_interval_mul_rneg_i(i,rp_erep_left_val(f),rp_erep_deriv(f));
  rp_deriv_set(rp_erep_right(f),i);
  return( 1 );
}
static rp_inline
int rp_deriv_num_mul_rpos_i(rp_erep f)       /* d(u*v)/d(v) = u */
{
  rp_interval i;
  rp_interval_mul_rpos_i(i,rp_erep_left_val(f),rp_erep_deriv(f));
  rp_deriv_set(rp_erep_right(f),i);
  return( 1 );
}
static rp_inline
int rp_deriv_num_div(rp_erep f)              /* d(u/v)/d(u) = 1/v    */
{                                            /* d(u/v)/d(v) = -u/v^2 */
  rp_interval i, j, k, r;
  rp_interval_div(r,rp_erep_deriv(f),rp_erep_right_val(f));
  rp_deriv_set(rp_erep_left(f),r);
  rp_interval_neg(i,rp_erep_left_val(f));     /* i := -u */
  rp_interval_sqr(j,rp_erep_right_val(f));    /* j := v^2 */
  rp_interval_div(k,i,j);                     /* k := -u/v^2 */
  rp_interval_mul(r,rp_erep_deriv(f),k);
  rp_deriv_set(rp_erep_right(f),r);
  return( 1 );
}
static rp_inline
int rp_deriv_num_div_i_r(rp_erep f)          /* d(u/v)/d(u) = 1/v    */
{
  rp_interval r;
  rp_interval_div(r,rp_erep_deriv(f),rp_erep_right_val(f));
  rp_deriv_set(rp_erep_left(f),r);
  return( 1 );
}
static rp_inline
int rp_deriv_num_div_i_rpos(rp_erep f)       /* d(u/v)/d(u) = 1/v    */
{
  rp_interval r;
  rp_interval_div_i_rpos(r,rp_erep_deriv(f),rp_erep_right_val(f));
  rp_deriv_set(rp_erep_left(f),r);
  return( 1 );
}
static rp_inline
int rp_deriv_num_div_i_rneg(rp_erep f)       /* d(u/v)/d(u) = 1/v    */
{
  rp_interval r;
  rp_interval_div_i_rneg(r,rp_erep_deriv(f),rp_erep_right_val(f));
  rp_deriv_set(rp_erep_left(f),r);
  return( 1 );
}
static rp_inline
int rp_deriv_num_div_r_i(rp_erep f)          /* d(u/v)/d(v) = -u/v^2 */
{
  rp_interval i, j, k, r;
  rp_interval_neg(i,rp_erep_left_val(f));     /* i := -u */
  rp_interval_sqr(j,rp_erep_right_val(f));    /* j := v^2 */
  rp_interval_div_r_i(k,i,j);                 /* k := -u/v^2 */
  rp_interval_mul(r,rp_erep_deriv(f),k);
  rp_deriv_set(rp_erep_right(f),r);
  return( 1 );
}
static rp_inline
int rp_deriv_num_div_rpos_i(rp_erep f)       /* d(u/v)/d(v) = -u/v^2 */
{
  rp_interval i, j, k, r;
  rp_interval_neg(i,rp_erep_left_val(f));     /* i := -u */
  rp_interval_sqr(j,rp_erep_right_val(f));    /* j := v^2 */
  rp_interval_div_rneg_i(k,i,j);              /* k := -u/v^2 */
  rp_interval_mul(r,rp_erep_deriv(f),k);
  rp_deriv_set(rp_erep_right(f),r);
  return( 1 );
}
static rp_inline
int rp_deriv_num_div_rneg_i(rp_erep f)       /* d(u/v)/d(v) = -u/v^2 */
{
  rp_interval i, j, k, r;
  rp_interval_neg(i,rp_erep_left_val(f));     /* i := -u */
  rp_interval_sqr(j,rp_erep_right_val(f));    /* j := v^2 */
  rp_interval_div_rpos_i(k,i,j);              /* k := -u/v^2 */
  rp_interval_mul(r,rp_erep_deriv(f),k);
  rp_deriv_set(rp_erep_right(f),r);
  return( 1 );
}
static rp_inline
int rp_deriv_num_pow(rp_erep f)              /* d(u^n)/du = n*u^(n-1) */
{
  int n = (int)rp_binf(rp_erep_right_val(f));
  rp_interval i, j, k, l, r;
  rp_interval_set_point(i,n);

  if (n==2)      /* 2*u */
  {
    rp_interval_mul_rpos_i(k,i,rp_erep_left_val(f));  /* k := 2*u */
    rp_interval_mul(r,rp_erep_deriv(f),k);
    rp_deriv_set(rp_erep_left(f),r);
  }
  else if (n==3) /* 3*u^2 */
  {
    rp_interval_sqr(j,rp_erep_left_val(f));   /* j := u^2 */
    rp_interval_mul_rpos_i(k,i,j);            /* k := 3*u^2 */
    rp_interval_mul(r,rp_erep_deriv(f),k);
    rp_deriv_set(rp_erep_left(f),r);
  }
  else           /* n*u^(n-1) */
  {
    rp_interval_set_point(j,n-1);             /* j := n-1 */
    rp_interval_pow(k,rp_erep_left_val(f),j); /* k := u^(n-1) */
    rp_interval_mul_rpos_i(l,i,k);            /* l := n*u^(n-1) */
    rp_interval_mul(r,rp_erep_deriv(f),l);
    rp_deriv_set(rp_erep_left(f),r);
  }
  return( 1 );
}
static rp_inline
int rp_deriv_num_neg(rp_erep f)              /* d(-u)/du = -1 */
{
  rp_interval r;
  rp_interval_neg(r,rp_erep_deriv(f));
  rp_deriv_set(rp_erep_sub(f),r);
  return( 1 );
}
static rp_inline
int rp_deriv_num_sqr(rp_erep f)              /* d(u^2)/du = 2*u */
{
  rp_interval i, j, r;
  rp_interval_set_point(i,2.0);                    /* i := 2.0 */
  rp_interval_mul_rpos_i(j,i,rp_erep_sub_val(f));  /* j := 2.0*u */
  rp_interval_mul(r,rp_erep_deriv(f),j);
  rp_deriv_set(rp_erep_sub(f),r);
  return( 1 );
}
static rp_inline
int rp_deriv_num_sqrt(rp_erep f)             /* d(sqrt(u))/du = 0.5/sqrt(u) */
{
  rp_interval i, j, r;
  rp_interval_set_point(i,0.5);
  rp_interval_div_rpos_i(j,i,rp_erep_val(f));  /* j := 0.5/sqrt(u) */
  rp_interval_mul(r,rp_erep_deriv(f),j);
  rp_deriv_set(rp_erep_sub(f),r);
  return( 1 );
}
static rp_inline
int rp_deriv_num_exp(rp_erep f)             /* d(exp(u))/du = exp(u) */
{
  rp_interval r;
  rp_interval_mul(r,rp_erep_deriv(f),rp_erep_val(f));
  rp_deriv_set(rp_erep_sub(f),r);
  return( 1 );
}
static rp_inline
int rp_deriv_num_log(rp_erep f)             /* d(log(u))/du = 1/u */
{
  rp_interval r;
  rp_interval_div(r,rp_erep_deriv(f),rp_erep_sub_val(f));
  rp_deriv_set(rp_erep_sub(f),r);
  return( 1 );
}
static rp_inline
int rp_deriv_num_sin(rp_erep f)             /* d(sin(u))/du = cos(u) */
{
  rp_interval i, r;
  rp_interval_cos(i,rp_erep_sub_val(f));
  rp_interval_mul(r,rp_erep_deriv(f),i);
  rp_deriv_set(rp_erep_sub(f),r);
  return( 1 );
}
static rp_inline
int rp_deriv_num_cos(rp_erep f)             /* d(cos(u))/du = -sin(u) */
{
  rp_interval i, j, r;
  rp_interval_sin(i,rp_erep_sub_val(f));
  rp_interval_neg(j,i);
  rp_interval_mul(r,rp_erep_deriv(f),j);
  rp_deriv_set(rp_erep_sub(f),r);
  return( 1 );
}
static rp_inline
int rp_deriv_num_tan(rp_erep f)             /* d(tan(u))/du = 1+tan^2(u) */
{
  rp_interval i, j, k, r;
  rp_interval_sqr(i,rp_erep_val(f));   /* i := tan^2(u) */
  rp_interval_set_point(j,1.0);
  rp_interval_add_r_i(k,j,i);          /* k := 1+tan^2(u) */
  rp_interval_mul(r,rp_erep_deriv(f),k);
  rp_deriv_set(rp_erep_sub(f),r);
  return( 1 );
}
static rp_inline
int rp_deriv_num_cosh(rp_erep f)             /* d(cosh(u))/du = sinh(u) */
{
  rp_interval i, r;
  rp_interval_sinh(i,rp_erep_sub_val(f)); /* i := sinh(u) */
  rp_interval_mul(r,rp_erep_deriv(f),i);
  rp_deriv_set(rp_erep_sub(f),r);
  return( 1 );
}
static rp_inline
int rp_deriv_num_sinh(rp_erep f)             /* d(sinh(u))/du = cosh(u) */
{
  rp_interval i, r;
  rp_interval_cosh(i,rp_erep_sub_val(f)); /* i := cosh(u) */
  rp_interval_mul(r,rp_erep_deriv(f),i);
  rp_deriv_set(rp_erep_sub(f),r);
  return( 1 );
}
static rp_inline
int rp_deriv_num_tanh(rp_erep f)             /* d(tanh(u))/du = 1-tanh^2(u) */
{
  rp_interval i, j, k, r;
  rp_interval_sqr(i,rp_erep_val(f));  /* i := tanh^2(u) */
  rp_interval_set_point(j,1.0);
  rp_interval_sub_r_i(k,j,i);
  rp_interval_mul(r,rp_erep_deriv(f),k);
  rp_deriv_set(rp_erep_sub(f),r);
  return( 1 );
}
static rp_inline
int rp_deriv_num_asin(rp_erep f)             /* d(asin(u))/du = 1/sqrt(1-u^2) */
{
  rp_interval i, j, k, r;
  rp_interval_sqr(i,rp_erep_sub_val(f));  /* i := u^2 */
  rp_interval_set_point(j,1.0);
  rp_interval_sub_r_i(k,j,i);             /* k := 1-u^2 */
  rp_interval_sqrt(i,k);                  /* i := sqrt(1-u^2) */
  if (rp_interval_empty(i))
  {
    return( 0 );
  }
  else
  {
    rp_interval_div(r,rp_erep_deriv(f),i);
    rp_deriv_set(rp_erep_sub(f),r);
    return( 1 );
  }
}
static rp_inline
int rp_deriv_num_acos(rp_erep f)             /* d(acos(u))/du = -1/sqrt(1-u^2) */
{
  rp_interval i, j, k, r;
  rp_interval_sqr(i,rp_erep_sub_val(f));  /* i := u^2 */
  rp_interval_set_point(j,1.0);
  rp_interval_sub_r_i(k,j,i);             /* k := 1-u^2 */
  rp_interval_sqrt(i,k);                  /* i := sqrt(1-u^2) */
  if (rp_interval_empty(i))
  {
    return( 0 );
  }
  else
  {
    rp_interval_div(j,rp_erep_deriv(f),i);
    rp_interval_neg(r,j);
    rp_deriv_set(rp_erep_sub(f),r);
    return( 1 );
  }
}
static rp_inline
int rp_deriv_num_atan(rp_erep f)             /* d(atan(u))/du = 1/(1+u^2) */
{
  rp_interval i, j, k, r;
  rp_interval_sqr(i,rp_erep_sub_val(f));  /* i := u^2 */
  rp_interval_set_point(j,1.0);
  rp_interval_add_r_i(k,j,i);             /* k := 1+u^2 */
  rp_interval_div(r,rp_erep_deriv(f),k);
  rp_deriv_set(rp_erep_sub(f),r);
  return( 1 );
}
static rp_inline
int rp_deriv_num_asinh(rp_erep f)            /* d(asinh(u))/du = 1/sqrt(1+u^2) */
{
  rp_interval i, j, k, r;
  rp_interval_sqr(i,rp_erep_sub_val(f));  /* i := u^2 */
  rp_interval_set_point(j,1.0);
  rp_interval_add_r_i(k,j,i);             /* k := 1+u^2 */
  rp_interval_sqrt(i,k);                  /* i := sqrt(1+u^2) */
  if (rp_interval_empty(i))
  {
    return( 0 );
  }
  else
  {
    rp_interval_div(r,rp_erep_deriv(f),i);
    rp_deriv_set(rp_erep_sub(f),r);
    return( 1 );
  }
}
static rp_inline
int rp_deriv_num_acosh(rp_erep f)            /* d(acosh(u))/du = 1/sqrt(u^2-1) */
{
  rp_interval i, j, k, r;
  rp_interval_sqr(i,rp_erep_sub_val(f));  /* i := u^2 */
  rp_interval_set_point(j,1.0);
  rp_interval_sub_i_r(k,i,j);             /* k := u^2-1 */
  rp_interval_sqrt(i,k);                  /* i := sqrt(u^2-1) */
  if (rp_interval_empty(i))
  {
    return( 0 );
  }
  else
  {
    rp_interval_div(r,rp_erep_deriv(f),i);
    rp_deriv_set(rp_erep_sub(f),r);
    return( 1 );
  }
}
static rp_inline
int rp_deriv_num_atanh(rp_erep f)            /* d(atanh(u))/du = 1/(1-u^2) */
{
  rp_interval i, j, k, r;
  rp_interval_sqr(i,rp_erep_sub_val(f));  /* i := u^2 */
  rp_interval_set_point(j,1.0);
  rp_interval_sub_r_i(k,j,i);             /* k := 1-u^2 */
  rp_interval_div(r,rp_erep_deriv(f),k);
  rp_deriv_set(rp_erep_sub(f),r);
  return( 1 );
}

/* ------------------------------------- */
/* Symbols symbolic derivation functions */
/* ------------------------------------- */

typedef void (* rp_symbol_deriv_symb)(rp_erep *, rp_erep, rp_erep, rp_erep);

static rp_inline
void rp_deriv_symb_add(rp_erep * df, rp_erep f, rp_erep du, rp_erep dv)
{
  /* df = d(u+v) = du + dv */
  rp_erep_create_binary(df,RP_SYMBOL_ADD,du,dv);
}
static rp_inline
void rp_deriv_symb_add_r_i(rp_erep * df, rp_erep f, rp_erep du, rp_erep dv)
{
  /* df = d(u+v) = dv */
  rp_erep_set(df,dv);
}
static rp_inline
void rp_deriv_symb_sub(rp_erep * df, rp_erep f, rp_erep du, rp_erep dv)
{
  /* df = d(u-v) = du - dv */
  rp_erep_create_binary(df,RP_SYMBOL_SUB,du,dv);
}
static rp_inline
void rp_deriv_symb_sub_r_i(rp_erep * df, rp_erep f, rp_erep du, rp_erep dv)
{
  /* df = d(u-v) = - dv */
  rp_erep_create_unary(df,RP_SYMBOL_NEG,dv);
}
static rp_inline
void rp_deriv_symb_sub_i_r(rp_erep * df, rp_erep f, rp_erep du, rp_erep dv)
{
  /* df = d(u-v) = du */
  rp_erep_set(df,du);
}
static rp_inline
void rp_deriv_symb_mul(rp_erep * df, rp_erep f, rp_erep du, rp_erep dv)
{
  /* df = d(u*v) = u*dv + v*du */
  rp_erep g, h, u, v;
  rp_erep_copy(&u,rp_erep_left(f));
  rp_erep_copy(&v,rp_erep_right(f));
  rp_erep_create_binary(&g,RP_SYMBOL_MUL,u,dv);
  rp_erep_create_binary(&h,RP_SYMBOL_MUL,v,du);
  rp_erep_create_binary(df,RP_SYMBOL_ADD,g,h);
  rp_erep_destroy(&g);
  rp_erep_destroy(&h);
  rp_erep_destroy(&u);
  rp_erep_destroy(&v);
}
static rp_inline
void rp_deriv_symb_mul_r_i(rp_erep * df, rp_erep f, rp_erep du, rp_erep dv)
{
  /* df = d(u*v) = u*dv */
  rp_erep u;
  rp_erep_copy(&u,rp_erep_left(f));
  rp_erep_create_binary(df,RP_SYMBOL_MUL,u,dv);
  rp_erep_destroy(&u);
}
static rp_inline
void rp_deriv_symb_mul_rneg_i(rp_erep * df, rp_erep f, rp_erep du, rp_erep dv)
{
  /* df = d(u*v) = u*dv */
  rp_erep u;
  rp_erep_copy(&u,rp_erep_left(f));
  rp_erep_create_binary(df,RP_SYMBOL_MUL,u,dv);
  rp_erep_destroy(&u);
}
static rp_inline
void rp_deriv_symb_mul_rpos_i(rp_erep * df, rp_erep f, rp_erep du, rp_erep dv)
{
  /* df = d(u*v) = u*dv */
  rp_erep u;
  rp_erep_copy(&u,rp_erep_left(f));
  rp_erep_create_binary(df,RP_SYMBOL_MUL,u,dv);
  rp_erep_destroy(&u);
}
static rp_inline
void rp_deriv_symb_div(rp_erep * df, rp_erep f, rp_erep du, rp_erep dv)
{
  /* df = d(u/v) = (v*du - u*dv)/v^2 */
  rp_erep g, h, p, q, u, v, w;
  rp_erep_copy(&u,rp_erep_left(f));
  rp_erep_copy(&v,rp_erep_right(f));
  rp_erep_copy(&w,rp_erep_right(f));
  rp_erep_create_binary(&g,RP_SYMBOL_MUL,v,du);
  rp_erep_create_binary(&h,RP_SYMBOL_MUL,u,dv);
  rp_erep_create_binary(&p,RP_SYMBOL_SUB,g,h);
  rp_erep_create_unary(&q,RP_SYMBOL_SQR,w);
  rp_erep_create_binary(df,RP_SYMBOL_DIV,p,q);
  rp_erep_destroy(&g);
  rp_erep_destroy(&h);
  rp_erep_destroy(&p);
  rp_erep_destroy(&q);
  rp_erep_destroy(&u);
  rp_erep_destroy(&v);
  rp_erep_destroy(&w);
}
static rp_inline
void rp_deriv_symb_div_i_r(rp_erep * df, rp_erep f, rp_erep du, rp_erep dv)
{
  /* df = d(u/v) = du/v */
  rp_erep v;
  rp_erep_copy(&v,rp_erep_right(f));
  rp_erep_create_binary(df,RP_SYMBOL_DIV,du,v);
  rp_erep_destroy(&v);
}
static rp_inline
void rp_deriv_symb_div_i_rpos(rp_erep * df, rp_erep f, rp_erep du, rp_erep dv)
{
  /* df = d(u/v) = du/v */
  rp_erep v;
  rp_erep_copy(&v,rp_erep_right(f));
  rp_erep_create_binary(df,RP_SYMBOL_DIV,du,v);
  rp_erep_destroy(&v);
}
static rp_inline
void rp_deriv_symb_div_i_rneg(rp_erep * df, rp_erep f, rp_erep du, rp_erep dv)
{
  /* df = d(u/v) = du/v */
  rp_erep v;
  rp_erep_copy(&v,rp_erep_right(f));
  rp_erep_create_binary(df,RP_SYMBOL_DIV,du,v);
  rp_erep_destroy(&v);
}
static rp_inline
void rp_deriv_symb_div_r_i(rp_erep * df, rp_erep f, rp_erep du, rp_erep dv)
{
  /* df = d(u/v) = (-u*dv)/v^2 */
  rp_erep g, h, p, u, v;
  rp_erep_copy(&u,rp_erep_left(f));
  rp_erep_copy(&v,rp_erep_right(f));
  rp_erep_create_binary(&g,RP_SYMBOL_MUL,u,dv);
  rp_erep_create_unary(&h,RP_SYMBOL_NEG,g);
  rp_erep_create_unary(&p,RP_SYMBOL_SQR,v);
  rp_erep_create_binary(df,RP_SYMBOL_DIV,h,p);
  rp_erep_destroy(&g);
  rp_erep_destroy(&h);
  rp_erep_destroy(&p);
  rp_erep_destroy(&u);
  rp_erep_destroy(&v);
}
static rp_inline
void rp_deriv_symb_div_rpos_i(rp_erep * df, rp_erep f, rp_erep du, rp_erep dv)
{
  /* df = d(u/v) = (-u*dv)/v^2 */
  rp_erep g, h, p, u, v;
  rp_erep_copy(&u,rp_erep_left(f));
  rp_erep_copy(&v,rp_erep_right(f));
  rp_erep_create_binary(&g,RP_SYMBOL_MUL,u,dv);
  rp_erep_create_unary(&h,RP_SYMBOL_NEG,g);
  rp_erep_create_unary(&p,RP_SYMBOL_SQR,v);
  rp_erep_create_binary(df,RP_SYMBOL_DIV,h,p);
  rp_erep_destroy(&g);
  rp_erep_destroy(&h);
  rp_erep_destroy(&p);
  rp_erep_destroy(&u);
  rp_erep_destroy(&v);
}
static rp_inline
void rp_deriv_symb_div_rneg_i(rp_erep * df, rp_erep f, rp_erep du, rp_erep dv)
{
  /* df = d(u/v) = (-u*dv)/v^2 */
  rp_erep g, h, p, u, v;
  rp_erep_copy(&u,rp_erep_left(f));
  rp_erep_copy(&v,rp_erep_right(f));
  rp_erep_create_binary(&g,RP_SYMBOL_MUL,u,dv);
  rp_erep_create_unary(&h,RP_SYMBOL_NEG,g);
  rp_erep_create_unary(&p,RP_SYMBOL_SQR,v);
  rp_erep_create_binary(df,RP_SYMBOL_DIV,h,p);
  rp_erep_destroy(&g);
  rp_erep_destroy(&h);
  rp_erep_destroy(&p);
  rp_erep_destroy(&u);
  rp_erep_destroy(&v);
}
static rp_inline
void rp_deriv_symb_pow(rp_erep * df, rp_erep f, rp_erep du, rp_erep dv)
{
  /* d(u^n) := n*u^(n-1)*du */
  int n = (int)rp_binf(rp_erep_right_val(f));
  rp_erep g, h, p, q, u;
  rp_interval i;
  rp_erep_copy(&u,rp_erep_left(f));
  rp_interval_set_point(i,n-1);
  rp_erep_create_cst(&p,"",i);
  rp_erep_create_binary(&g,RP_SYMBOL_POW,u,p);  /* u^(n-1) */
  rp_interval_set_point(i,n);
  rp_erep_create_cst(&q,"",i);
  rp_erep_create_binary(&h,RP_SYMBOL_MUL,q,g);  /* n*u^(n-1) */
  rp_erep_create_binary(df,RP_SYMBOL_MUL,h,du);
  rp_erep_destroy(&g);
  rp_erep_destroy(&h);
  rp_erep_destroy(&p);
  rp_erep_destroy(&q);
  rp_erep_destroy(&u);
}
static rp_inline
void rp_deriv_symb_neg(rp_erep * df, rp_erep f, rp_erep du, rp_erep dv)
{
  /* d(-u) = -du */
  rp_erep_create_unary(df,RP_SYMBOL_NEG,du);
}
static rp_inline
void rp_deriv_symb_sqr(rp_erep * df, rp_erep f, rp_erep du, rp_erep dv)
{
  /* d(u^2) = 2*u*du */
  rp_erep g, h, u;
  rp_interval i;
  rp_erep_copy(&u,rp_erep_sub(f));
  rp_interval_set_point(i,2.0);
  rp_erep_create_cst(&g,"",i);
  rp_erep_create_binary(&h,RP_SYMBOL_MUL,g,u);
  rp_erep_create_binary(df,RP_SYMBOL_MUL,h,du);
  rp_erep_destroy(&g);
  rp_erep_destroy(&h);
  rp_erep_destroy(&u);
}
static rp_inline
void rp_deriv_symb_sqrt(rp_erep * df, rp_erep f, rp_erep du, rp_erep dv)
{
  /* d(sqrt(u)) = (0.5*du)/sqrt(u) */
  rp_erep g, h, p, u;
  rp_interval i;
  rp_erep_copy(&u,rp_erep_sub(f));
  rp_interval_set_point(i,0.5);
  rp_erep_create_cst(&g,"",i);
  rp_erep_create_binary(&h,RP_SYMBOL_MUL,g,du);  /* 0.5*du */
  rp_erep_create_unary(&p,RP_SYMBOL_SQRT,u);     /* sqrt(u) */
  rp_erep_create_binary(df,RP_SYMBOL_DIV,h,p);
  rp_erep_destroy(&g);
  rp_erep_destroy(&h);
  rp_erep_destroy(&p);
  rp_erep_destroy(&u);
}
static rp_inline
void rp_deriv_symb_exp(rp_erep * df, rp_erep f, rp_erep du, rp_erep dv)
{
  /* d(exp(u) = exp(u)*du */
  rp_erep g, u;
  rp_erep_copy(&u,rp_erep_sub(f));
  rp_erep_create_unary(&g,RP_SYMBOL_EXP,u);
  rp_erep_create_binary(df,RP_SYMBOL_MUL,g,du);
  rp_erep_destroy(&g);
  rp_erep_destroy(&u);
}
static rp_inline
void rp_deriv_symb_log(rp_erep * df, rp_erep f, rp_erep du, rp_erep dv)
{
  /* d(log(u)) = du/u */
  rp_erep u;
  rp_erep_copy(&u,rp_erep_sub(f));
  rp_erep_create_binary(df,RP_SYMBOL_DIV,du,u);
  rp_erep_destroy(&u);
}
static rp_inline
void rp_deriv_symb_sin(rp_erep * df, rp_erep f, rp_erep du, rp_erep dv)
{
  /* d(sin(u)) = cos(u)*du */
  rp_erep g, u;
  rp_erep_copy(&u,rp_erep_sub(f));
  rp_erep_create_unary(&g,RP_SYMBOL_COS,u);
  rp_erep_create_binary(df,RP_SYMBOL_MUL,g,du);
  rp_erep_destroy(&g);
  rp_erep_destroy(&u);
}
static rp_inline
void rp_deriv_symb_cos(rp_erep * df, rp_erep f, rp_erep du, rp_erep dv)
{
  /* d(cos(u)) = -sin(u)*du */
  rp_erep g, h, u;
  rp_erep_copy(&u,rp_erep_sub(f));
  rp_erep_create_unary(&g,RP_SYMBOL_SIN,u);
  rp_erep_create_unary(&h,RP_SYMBOL_NEG,g);
  rp_erep_create_binary(df,RP_SYMBOL_MUL,h,du);
  rp_erep_destroy(&g);
  rp_erep_destroy(&h);
  rp_erep_destroy(&u);
}
static rp_inline
void rp_deriv_symb_tan(rp_erep * df, rp_erep f, rp_erep du, rp_erep dv)
{
  /* d(tan(u)) = (1+tan^2(u))*du */
  rp_erep g, h, p, q, u;
  rp_interval i;
  rp_erep_copy(&u,rp_erep_sub(f));
  rp_erep_create_unary(&g,RP_SYMBOL_TAN,u); /* tan(u) */
  rp_erep_create_unary(&h,RP_SYMBOL_SQR,g); /* tan^2(u) */
  rp_interval_set_point(i,1.0);
  rp_erep_create_cst(&p,"",i);
  rp_erep_create_binary(&q,RP_SYMBOL_ADD,p,h); /* 1+tan^2(u) */
  rp_erep_create_binary(df,RP_SYMBOL_MUL,q,du);
  rp_erep_destroy(&g);
  rp_erep_destroy(&h);
  rp_erep_destroy(&p);
  rp_erep_destroy(&q);
  rp_erep_destroy(&u);
}
static rp_inline
void rp_deriv_symb_cosh(rp_erep * df, rp_erep f, rp_erep du, rp_erep dv)
{
  /* d(cosh(u)) = sinh(u)*du */
  rp_erep g, u;
  rp_erep_copy(&u,rp_erep_sub(f));
  rp_erep_create_unary(&g,RP_SYMBOL_SINH,u);  /* sinh(u) */
  rp_erep_create_binary(df,RP_SYMBOL_MUL,g,du);
  rp_erep_destroy(&g);
  rp_erep_destroy(&u);
}
static rp_inline
void rp_deriv_symb_sinh(rp_erep * df, rp_erep f, rp_erep du, rp_erep dv)
{
  /* d(sinh(u)) = cosh(u)*du */
  rp_erep g, u;
  rp_erep_copy(&u,rp_erep_sub(f));
  rp_erep_create_unary(&g,RP_SYMBOL_COSH,u);  /* cosh(u) */
  rp_erep_create_binary(df,RP_SYMBOL_MUL,g,du);
  rp_erep_destroy(&g);
  rp_erep_destroy(&u);
}
static rp_inline
void rp_deriv_symb_tanh(rp_erep * df, rp_erep f, rp_erep du, rp_erep dv)
{
  /* d(tanh(u)) = (1-tanh^2(u))*du */
  rp_erep g, h, p, q, u;
  rp_interval i;
  rp_erep_copy(&u,rp_erep_sub(f));
  rp_erep_create_unary(&g,RP_SYMBOL_TANH,u);  /* tanh(u) */
  rp_erep_create_unary(&h,RP_SYMBOL_SQR,g);   /* tanh^2(u) */
  rp_interval_set_point(i,1.0);
  rp_erep_create_cst(&p,"",i);
  rp_erep_create_binary(&q,RP_SYMBOL_SUB,p,h); /* 1-tanh^2(u) */
  rp_erep_create_binary(df,RP_SYMBOL_MUL,q,du);
  rp_erep_destroy(&g);
  rp_erep_destroy(&h);
  rp_erep_destroy(&p);
  rp_erep_destroy(&q);
  rp_erep_destroy(&u);
}
static rp_inline
void rp_deriv_symb_asin(rp_erep * df, rp_erep f, rp_erep du, rp_erep dv)
{
  /* d(asin(u)) = du/sqrt(1-u^2) */
  rp_erep g, h, p, q, u;
  rp_interval i;
  rp_erep_copy(&u,rp_erep_sub(f));
  rp_erep_create_unary(&g,RP_SYMBOL_SQR,u);    /* u^2 */
  rp_interval_set_point(i,1.0);
  rp_erep_create_cst(&h,"",i);
  rp_erep_create_binary(&p,RP_SYMBOL_SUB,h,g); /* 1-u^2 */
  rp_erep_create_unary(&q,RP_SYMBOL_SQRT,p);   /* sqrt(1-u^2) */
  rp_erep_create_binary(df,RP_SYMBOL_DIV,du,q);
  rp_erep_destroy(&g);
  rp_erep_destroy(&h);
  rp_erep_destroy(&p);
  rp_erep_destroy(&q);
  rp_erep_destroy(&u);
}
static rp_inline
void rp_deriv_symb_acos(rp_erep * df, rp_erep f, rp_erep du, rp_erep dv)
{
  /* d(asin(u)) = -du/sqrt(1-u^2) */
  rp_erep g, h, p, q, r, u;
  rp_interval i;
  rp_erep_copy(&u,rp_erep_sub(f));
  rp_erep_create_unary(&g,RP_SYMBOL_SQR,u);     /* u^2 */
  rp_interval_set_point(i,1.0);
  rp_erep_create_cst(&h,"",i);
  rp_erep_create_binary(&p,RP_SYMBOL_SUB,h,g);  /* 1-u^2 */
  rp_erep_create_unary(&q,RP_SYMBOL_SQRT,p);    /* sqrt(1-u^2) */
  rp_erep_create_binary(&r,RP_SYMBOL_DIV,du,q); /* du/sqrt(1-u^2) */
  rp_erep_create_unary(df,RP_SYMBOL_NEG,r);
  rp_erep_destroy(&g);
  rp_erep_destroy(&h);
  rp_erep_destroy(&p);
  rp_erep_destroy(&q);
  rp_erep_destroy(&r);
  rp_erep_destroy(&u);
}
static rp_inline
void rp_deriv_symb_atan(rp_erep * df, rp_erep f, rp_erep du, rp_erep dv)
{
  /* d(atan(u)) = du/(1+u^2) */
  rp_erep g, h, p, u;
  rp_interval i;
  rp_erep_copy(&u,rp_erep_sub(f));
  rp_erep_create_unary(&g,RP_SYMBOL_SQR,u);     /* u^2 */
  rp_interval_set_point(i,1.0);
  rp_erep_create_cst(&h,"",i);
  rp_erep_create_binary(&p,RP_SYMBOL_ADD,h,g);  /* 1+u^2 */
  rp_erep_create_binary(df,RP_SYMBOL_DIV,du,p);
  rp_erep_destroy(&g);
  rp_erep_destroy(&h);
  rp_erep_destroy(&p);
  rp_erep_destroy(&u);
}
static rp_inline
void rp_deriv_symb_asinh(rp_erep * df, rp_erep f, rp_erep du, rp_erep dv)
{
  /* d(asinh(u)) = du/sqrt(1+u^2) */
  rp_erep g, h, p, q, u;
  rp_interval i;
  rp_erep_copy(&u,rp_erep_sub(f));
  rp_erep_create_unary(&g,RP_SYMBOL_SQR,u);    /* u^2 */
  rp_interval_set_point(i,1.0);
  rp_erep_create_cst(&h,"",i);
  rp_erep_create_binary(&p,RP_SYMBOL_ADD,h,g); /* 1+u^2 */
  rp_erep_create_unary(&q,RP_SYMBOL_SQRT,p);   /* sqrt(1+u^2) */
  rp_erep_create_binary(df,RP_SYMBOL_DIV,du,q);
  rp_erep_destroy(&g);
  rp_erep_destroy(&h);
  rp_erep_destroy(&p);
  rp_erep_destroy(&q);
  rp_erep_destroy(&u);
}
static rp_inline
void rp_deriv_symb_acosh(rp_erep * df, rp_erep f, rp_erep du, rp_erep dv)
{
  /* d(acosh(u)) = du/sqrt(u^2-1) */
  rp_erep g, h, p, q, u;
  rp_interval i;
  rp_erep_copy(&u,rp_erep_sub(f));
  rp_erep_create_unary(&g,RP_SYMBOL_SQR,u);    /* u^2 */
  rp_interval_set_point(i,1.0);
  rp_erep_create_cst(&h,"",i);
  rp_erep_create_binary(&p,RP_SYMBOL_SUB,g,h); /* u^2-1 */
  rp_erep_create_unary(&q,RP_SYMBOL_SQRT,p);   /* sqrt(u^2-1) */
  rp_erep_create_binary(df,RP_SYMBOL_DIV,du,q);
  rp_erep_destroy(&g);
  rp_erep_destroy(&h);
  rp_erep_destroy(&p);
  rp_erep_destroy(&q);
  rp_erep_destroy(&u);
}
static rp_inline
void rp_deriv_symb_atanh(rp_erep * df, rp_erep f, rp_erep du, rp_erep dv)
{
  /* d(atanh(u)) = du/(1-u^2) */
  rp_erep g, h, p, u;
  rp_interval i;
  rp_erep_copy(&u,rp_erep_sub(f));
  rp_erep_create_unary(&g,RP_SYMBOL_SQR,u);     /* u^2 */
  rp_interval_set_point(i,1.0);
  rp_erep_create_cst(&h,"",i);
  rp_erep_create_binary(&p,RP_SYMBOL_SUB,h,g);  /* 1-u^2 */
  rp_erep_create_binary(df,RP_SYMBOL_DIV,du,p);
  rp_erep_destroy(&g);
  rp_erep_destroy(&h);
  rp_erep_destroy(&p);
  rp_erep_destroy(&u);
}

/* ----------------------------------------------------------- */
/* Mapping symbols-functions                                   */
/* ----------------------------------------------------------- */
/* Each term symbol is associated with a set of functions that */
/* can be applied on it: evaluation, derivation, projection    */
/* ----------------------------------------------------------- */

typedef struct
{
  char                 name[6];    /* name used for display          */
  unsigned int         property;   /* symbol properties              */
  rp_symbol_eval       eval;       /* evaluation function            */
  rp_symbol_project    project;    /* projection function            */
  rp_symbol_deriv_num  numderiv;   /* numerical derivation function  */
  rp_symbol_deriv_symb symderiv;   /* symbolic derivation function   */
} rp_symbol;

/* Encoding of property  */

/* bits b1 b0: priority */
#define RP_SYMBOL_PRIORITY_BIT     0
#define RP_SYMBOL_PRIORITY_S       0
#define RP_SYMBOL_PRIORITY_M       1
#define RP_SYMBOL_PRIORITY_L       2
#define RP_SYMBOL_PRIORITY_XL      3
#define RP_SYMBOL_PRIORITY_MASK    ((1 << 0) + (1 << 1))

/* bit b2: arity */
#define RP_SYMBOL_ARITY_BIT        2
#define RP_SYMBOL_ARITY_UNARY      0
#define RP_SYMBOL_ARITY_BINARY     1
#define RP_SYMBOL_ARITY_MASK       (1 << RP_SYMBOL_ARITY_BIT)

/* bit b3: commutativity */
#define RP_SYMBOL_COMMUTE_BIT      3
#define RP_SYMBOL_COMMUTE_NO       0
#define RP_SYMBOL_COMMUTE_YES      1
#define RP_SYMBOL_COMMUTE_MASK     (1 << RP_SYMBOL_COMMUTE_BIT)

/* bit b4: notation */
#define RP_SYMBOL_NOTATION_BIT     4
#define RP_SYMBOL_NOTATION_PREFIX  0
#define RP_SYMBOL_NOTATION_INFIX   1
#define RP_SYMBOL_NOTATION_MASK    (1 << RP_SYMBOL_NOTATION_BIT)

/* Combinations arity/commutativity/notation */

/* Unary => prefix and non commutative */
#define RP_SYMBOL_UNARY_PREFIX \
  ((RP_SYMBOL_ARITY_UNARY << RP_SYMBOL_ARITY_BIT) + \
   (RP_SYMBOL_COMMUTE_NO << RP_SYMBOL_COMMUTE_BIT) + \
   (RP_SYMBOL_NOTATION_PREFIX << RP_SYMBOL_NOTATION_BIT))

#define RP_SYMBOL_UNARY_INFIX \
  ((RP_SYMBOL_ARITY_UNARY << RP_SYMBOL_ARITY_BIT) + \
   (RP_SYMBOL_COMMUTE_NO << RP_SYMBOL_COMMUTE_BIT) + \
   (RP_SYMBOL_NOTATION_INFIX << RP_SYMBOL_NOTATION_BIT))

#define RP_SYMBOL_BINARY_COMMUTE_INFIX \
  ((RP_SYMBOL_ARITY_BINARY << RP_SYMBOL_ARITY_BIT) + \
   (RP_SYMBOL_COMMUTE_YES << RP_SYMBOL_COMMUTE_BIT) + \
   (RP_SYMBOL_NOTATION_INFIX << RP_SYMBOL_NOTATION_BIT))

#define RP_SYMBOL_BINARY_COMMUTE_PREFIX \
  ((RP_SYMBOL_ARITY_BINARY << RP_SYMBOL_ARITY_BIT) + \
   (RP_SYMBOL_COMMUTE_YES << RP_SYMBOL_COMMUTE_BIT) + \
   (RP_SYMBOL_NOTATION_PREFIX << RP_SYMBOL_NOTATION_BIT))

#define RP_SYMBOL_BINARY_INFIX \
  ((RP_SYMBOL_ARITY_BINARY << RP_SYMBOL_ARITY_BIT) + \
   (RP_SYMBOL_COMMUTE_NO << RP_SYMBOL_COMMUTE_BIT) + \
   (RP_SYMBOL_NOTATION_INFIX << RP_SYMBOL_NOTATION_BIT))

#define RP_SYMBOL_BINARY_PREFIX \
  ((RP_SYMBOL_ARITY_BINARY << RP_SYMBOL_ARITY_BIT) + \
   (RP_SYMBOL_COMMUTE_NO << RP_SYMBOL_COMMUTE_BIT) + \
   (RP_SYMBOL_NOTATION_PREFIX << RP_SYMBOL_NOTATION_BIT))

/* The mapping symbol-functions */
static rp_symbol rp_symbol_set[] =
{
  /* add */
  {"+",
   RP_SYMBOL_BINARY_COMMUTE_INFIX + RP_SYMBOL_PRIORITY_S,
   rp_eval_add,
   rp_project_add,
   rp_deriv_num_add,
   rp_deriv_symb_add},

  /* add_r_i */
  {"+",
   RP_SYMBOL_BINARY_COMMUTE_INFIX + RP_SYMBOL_PRIORITY_S,
   rp_eval_add_r_i,
   rp_project_add_r_i,
   rp_deriv_num_add_r_i,
   rp_deriv_symb_add_r_i},

  /* sub */
  {"-",
   RP_SYMBOL_BINARY_INFIX + RP_SYMBOL_PRIORITY_S,
   rp_eval_sub,
   rp_project_sub,
   rp_deriv_num_sub,
   rp_deriv_symb_sub},

  /* sub_r_i */
  {"-",
   RP_SYMBOL_BINARY_INFIX + RP_SYMBOL_PRIORITY_S,
   rp_eval_sub_r_i,
   rp_project_sub_r_i,
   rp_deriv_num_sub_r_i,
   rp_deriv_symb_sub_r_i},

  /* sub_i_r */
  {"-",
   RP_SYMBOL_BINARY_INFIX + RP_SYMBOL_PRIORITY_S,
   rp_eval_sub_i_r,
   rp_project_sub_i_r,
   rp_deriv_num_sub_i_r,
   rp_deriv_symb_sub_i_r},

  /* mul */
  {"*",
   RP_SYMBOL_BINARY_COMMUTE_INFIX + RP_SYMBOL_PRIORITY_M,
   rp_eval_mul,
   rp_project_mul,
   rp_deriv_num_mul,
   rp_deriv_symb_mul},

  /* mul_r_i */
  {"*",
   RP_SYMBOL_BINARY_COMMUTE_INFIX + RP_SYMBOL_PRIORITY_M,
   rp_eval_mul_r_i,
   rp_project_mul_r_i,
   rp_deriv_num_mul_r_i,
   rp_deriv_symb_mul_r_i},

  /* mul_rneg_i */
  {"*",
   RP_SYMBOL_BINARY_COMMUTE_INFIX + RP_SYMBOL_PRIORITY_M,
   rp_eval_mul_rneg_i,
   rp_project_mul_rneg_i,
   rp_deriv_num_mul_rneg_i,
   rp_deriv_symb_mul_rneg_i},

  /* mul_rpos_i */
  {"*",
   RP_SYMBOL_BINARY_COMMUTE_INFIX + RP_SYMBOL_PRIORITY_M,
   rp_eval_mul_rpos_i,
   rp_project_mul_rpos_i,
   rp_deriv_num_mul_rpos_i,
   rp_deriv_symb_mul_rpos_i},

  /* div */
  {"/",
   RP_SYMBOL_BINARY_INFIX + RP_SYMBOL_PRIORITY_M,
   rp_eval_div,
   rp_project_div,
   rp_deriv_num_div,
   rp_deriv_symb_div},

  /* div_i_r */
  {"/",
   RP_SYMBOL_BINARY_INFIX + RP_SYMBOL_PRIORITY_M,
   rp_eval_div_i_r,
   rp_project_div_i_r,
   rp_deriv_num_div_i_r,
   rp_deriv_symb_div_i_r},

  /* div_i_rpos */
  {"/",
   RP_SYMBOL_BINARY_INFIX + RP_SYMBOL_PRIORITY_M,
   rp_eval_div_i_rpos,
   rp_project_div_i_rpos,
   rp_deriv_num_div_i_rpos,
   rp_deriv_symb_div_i_rpos},

  /* div_i_rneg */
  {"/",
   RP_SYMBOL_BINARY_INFIX + RP_SYMBOL_PRIORITY_M,
   rp_eval_div_i_rneg,
   rp_project_div_i_rneg,
   rp_deriv_num_div_i_rneg,
   rp_deriv_symb_div_i_rneg},

  /* div_r_i */
  {"/",
   RP_SYMBOL_BINARY_INFIX + RP_SYMBOL_PRIORITY_M,
   rp_eval_div_r_i,
   rp_project_div_r_i,
   rp_deriv_num_div_r_i,
   rp_deriv_symb_div_r_i},

  /* div_rpos_i */
  {"/",
   RP_SYMBOL_BINARY_INFIX + RP_SYMBOL_PRIORITY_M,
   rp_eval_div_rpos_i,
   rp_project_div_rpos_i,
   rp_deriv_num_div_rpos_i,
   rp_deriv_symb_div_rpos_i},

  /* div_rneg_i */
  {"/",
   RP_SYMBOL_BINARY_INFIX + RP_SYMBOL_PRIORITY_M,
   rp_eval_div_rneg_i,
   rp_project_div_rneg_i,
   rp_deriv_num_div_rneg_i,
   rp_deriv_symb_div_rneg_i},

  /* pow */
  {"^",
   RP_SYMBOL_BINARY_INFIX + RP_SYMBOL_PRIORITY_XL,
   rp_eval_pow,
   rp_project_pow,
   rp_deriv_num_pow,
   rp_deriv_symb_pow},

  /* neg */
  {"-",
   RP_SYMBOL_UNARY_PREFIX + RP_SYMBOL_PRIORITY_S,
   rp_eval_neg,
   rp_project_neg,
   rp_deriv_num_neg,
   rp_deriv_symb_neg},

  /* sqr */
  {"^2",
   RP_SYMBOL_UNARY_INFIX + RP_SYMBOL_PRIORITY_XL,
   rp_eval_sqr,
   rp_project_sqr,
   rp_deriv_num_sqr,
   rp_deriv_symb_sqr},

  /* sqrt */
  {"sqrt",
   RP_SYMBOL_UNARY_PREFIX + RP_SYMBOL_PRIORITY_L,
   rp_eval_sqrt,
   rp_project_sqrt,
   rp_deriv_num_sqrt,
   rp_deriv_symb_sqrt},

  /* exp */
  {"exp",
   RP_SYMBOL_UNARY_PREFIX + RP_SYMBOL_PRIORITY_L,
   rp_eval_exp,
   rp_project_exp,
   rp_deriv_num_exp,
   rp_deriv_symb_exp},

  /* log */
  {"log",
   RP_SYMBOL_UNARY_PREFIX + RP_SYMBOL_PRIORITY_L,
   rp_eval_log,
   rp_project_log,
   rp_deriv_num_log,
   rp_deriv_symb_log},

  /* sin */
  {"sin",
   RP_SYMBOL_UNARY_PREFIX + RP_SYMBOL_PRIORITY_L,
   rp_eval_sin,
   rp_project_sin,
   rp_deriv_num_sin,
   rp_deriv_symb_sin},

  /* cos */
  {"cos",
   RP_SYMBOL_UNARY_PREFIX + RP_SYMBOL_PRIORITY_L,
   rp_eval_cos,
   rp_project_cos,
   rp_deriv_num_cos,
   rp_deriv_symb_cos},

  /* tan */
  {"tan",
   RP_SYMBOL_UNARY_PREFIX + RP_SYMBOL_PRIORITY_L,
   rp_eval_tan,
   rp_project_tan,
   rp_deriv_num_tan,
   rp_deriv_symb_tan},

  /* cosh */
  {"cosh",
   RP_SYMBOL_UNARY_PREFIX + RP_SYMBOL_PRIORITY_L,
   rp_eval_cosh,
   rp_project_cosh,
   rp_deriv_num_cosh,
   rp_deriv_symb_cosh},

  /* sinh */
  {"sinh",
   RP_SYMBOL_UNARY_PREFIX + RP_SYMBOL_PRIORITY_L,
   rp_eval_sinh,
   rp_project_sinh,
   rp_deriv_num_sinh,
   rp_deriv_symb_sinh},

  /* tanh */
  {"tanh",
   RP_SYMBOL_UNARY_PREFIX + RP_SYMBOL_PRIORITY_L,
   rp_eval_tanh,
   rp_project_tanh,
   rp_deriv_num_tanh,
   rp_deriv_symb_tanh},

  /* asin */
  {"asin",
   RP_SYMBOL_UNARY_PREFIX + RP_SYMBOL_PRIORITY_L,
   rp_eval_asin,
   rp_project_asin,
   rp_deriv_num_asin,
   rp_deriv_symb_asin},

  /* acos */
  {"acos",
   RP_SYMBOL_UNARY_PREFIX + RP_SYMBOL_PRIORITY_L,
   rp_eval_acos,
   rp_project_acos,
   rp_deriv_num_acos,
   rp_deriv_symb_acos},

  /* atan */
  {"atan",
   RP_SYMBOL_UNARY_PREFIX + RP_SYMBOL_PRIORITY_L,
   rp_eval_atan,
   rp_project_atan,
   rp_deriv_num_atan,
   rp_deriv_symb_atan},

  /* asinh */
  {"asinh",
   RP_SYMBOL_UNARY_PREFIX + RP_SYMBOL_PRIORITY_L,
   rp_eval_asinh,
   rp_project_asinh,
   rp_deriv_num_asinh,
   rp_deriv_symb_asinh},

  /* acosh */
  {"acosh",
   RP_SYMBOL_UNARY_PREFIX + RP_SYMBOL_PRIORITY_L,
   rp_eval_acosh,
   rp_project_acosh,
   rp_deriv_num_acosh,
   rp_deriv_symb_acosh},

  /* atanh */
  {"atanh",
   RP_SYMBOL_UNARY_PREFIX + RP_SYMBOL_PRIORITY_L,
   rp_eval_atanh,
   rp_project_atanh,
   rp_deriv_num_atanh,
   rp_deriv_symb_atanh},

  /* abs */
  {"abs",
   RP_SYMBOL_UNARY_PREFIX + RP_SYMBOL_PRIORITY_L,
   rp_eval_abs,
   rp_project_abs,
   NULL,
   NULL},

  /* min */
  {"min",
   RP_SYMBOL_BINARY_COMMUTE_PREFIX + RP_SYMBOL_PRIORITY_L,
   rp_eval_min,
   rp_project_min,
   NULL,
   NULL},

  /* max */
  {"max",
   RP_SYMBOL_BINARY_COMMUTE_PREFIX + RP_SYMBOL_PRIORITY_L,
   rp_eval_max,
   rp_project_max,
   NULL,
   NULL}
};

#define rp_symbol_name(s)        (rp_symbol_set[s].name)
#define rp_symbol_property(s)    (rp_symbol_set[s].property)
#define rp_symbol_eval(s)        (rp_symbol_set[s].eval)
#define rp_symbol_project(s)     (rp_symbol_set[s].project)
#define rp_symbol_deriv_num(s)   (rp_symbol_set[s].numderiv)
#define rp_symbol_deriv_symb(s)  (rp_symbol_set[s].symderiv)

#define rp_symbol_priority(s) \
  ((rp_symbol_property(s) & RP_SYMBOL_PRIORITY_MASK) \
   >> RP_SYMBOL_PRIORITY_BIT)

#define rp_symbol_unary(s) \
  (((rp_symbol_property(s) & RP_SYMBOL_ARITY_MASK) \
    >> RP_SYMBOL_ARITY_BIT) == RP_SYMBOL_ARITY_UNARY)

#define rp_symbol_binary(s) \
  (((rp_symbol_property(s) & RP_SYMBOL_ARITY_MASK) \
    >> RP_SYMBOL_ARITY_BIT) == RP_SYMBOL_ARITY_BINARY)

#define rp_symbol_commutative(s) \
  (((rp_symbol_property(s) & RP_SYMBOL_COMMUTE_MASK) \
    >> RP_SYMBOL_COMMUTE_BIT) == RP_SYMBOL_COMMUTE_YES)

#define rp_symbol_prefix(s) \
  (((rp_symbol_property(s) & RP_SYMBOL_NOTATION_MASK) \
    >> RP_SYMBOL_NOTATION_BIT) == RP_SYMBOL_NOTATION_PREFIX)

#define rp_symbol_infix(s) \
  (((rp_symbol_property(s) & RP_SYMBOL_NOTATION_MASK) \
    >> RP_SYMBOL_NOTATION_BIT) == RP_SYMBOL_NOTATION_INFIX)

#define rp_symbol_derivable(s) \
   (rp_symbol_deriv_num(s)!=NULL)

/* Used to remove warnings at compile-time */
static __inline__
int __rp_symbol_set_used(){
  return rp_symbol_priority(0);
}

#ifdef __cplusplus
}
#endif

#endif /* RP_EXPRESSION_SYMBOL_H */
