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
 * rp_constraint.h                                                          *
 ****************************************************************************/

#ifndef RP_CONSTRAINT_H
#define RP_CONSTRAINT_H 1

#ifdef __cplusplus
extern "C" {
#endif

#include "rp_memory.h"
#include "rp_constant.h"
#include "rp_variable.h"
#include "rp_expression.h"

/* --------------------- */
/* Numerical constraints */
/* --------------------- */

#define RP_RELATION_EQUAL     1
#define RP_RELATION_SUPEQUAL  2
#define RP_RELATION_INFEQUAL  3

typedef struct
{
  /* constraint: left rel right with rel in {=,<=,>=} */
  rp_expression left;
  rp_expression right;
  int rel;

  /* functional view of the constraint: func relfunc 0 */
  rp_expression func;
  int relfunc;
}
rp_ctr_num_def;

typedef rp_ctr_num_def * rp_ctr_num;

#define rp_ctr_num_left(c)     (c)->left
#define rp_ctr_num_right(c)    (c)->right
#define rp_ctr_num_rel(c)      (c)->rel
#define rp_ctr_num_func(c)     (c)->func
#define rp_ctr_num_relfunc(c)  (c)->relfunc
#define rp_ctr_num_arity(c)    rp_expression_arity((c)->func)
#define rp_ctr_num_var(c,i)    rp_expression_var((c)->func,i)
#define rp_ctr_num_occur(c,i)  rp_expression_occur_var((c)->func,i)

/* Creation of the numerical constraint (l rel r) */
void rp_ctr_num_create (rp_ctr_num * c,
			rp_erep * l, int rel, rp_erep * r);

/* Destruction */
void rp_ctr_num_destroy (rp_ctr_num * c);

/* Satisfiability tests */
int rp_ctr_numeq_unfeasible  (rp_ctr_num c, rp_box b);
int rp_ctr_numsup_unfeasible (rp_ctr_num c, rp_box b);
int rp_ctr_numinf_unfeasible (rp_ctr_num c, rp_box b);
int rp_ctr_numeq_inner       (rp_ctr_num c, rp_box b);
int rp_ctr_numsup_inner      (rp_ctr_num c, rp_box b);
int rp_ctr_numinf_inner      (rp_ctr_num c, rp_box b);

int rp_ctr_num_unfeasible    (rp_ctr_num c, rp_box b);
int rp_ctr_num_inner         (rp_ctr_num c, rp_box b);

/* Display c on out */
void rp_ctr_num_display (FILE* out, rp_ctr_num c,
			 rp_vector_variable var, int digits);

/* ----------------------- */
/* Conditional constraints */
/* ----------------------- */

/* General form: c1 and ... and ck => C1 and ... and Cp */
typedef struct
{
  rp_ctr_num * guard;  /* c1 and ... and ck */
  int guardsize;       /* k-1               */

  rp_ctr_num * conc;   /* C1 and ... and Cp */
  int concsize;        /* p-1               */
}
rp_ctr_cond_def;

typedef rp_ctr_cond_def * rp_ctr_cond;

#define rp_ctr_cond_guard(c)         (c)->guard
#define rp_ctr_cond_guardsize(c)     (c)->guardsize
#define rp_ctr_cond_guard_elem(c,i)  (c)->guard[i]
#define rp_ctr_cond_conc(c)          (c)->conc
#define rp_ctr_cond_concsize(c)      (c)->concsize
#define rp_ctr_cond_conc_elem(c,i)   (c)->conc[i]

/* Creation of an empty conditional constraint */
void rp_ctr_cond_create (rp_ctr_cond * c);

/* Destruction */
void rp_ctr_cond_destroy (rp_ctr_cond * c);

/* Insertion of a constraint in the guard */
void rp_ctr_cond_insert_guard (rp_ctr_cond c, rp_ctr_num guard);

  /* Insertion of a constraint in the conclusion */
void rp_ctr_cond_insert_conc (rp_ctr_cond c, rp_ctr_num conc);

/* Returns true if no point of b is solution of c */
int rp_ctr_cond_unfeasible (rp_ctr_cond c, rp_box b);

/* Returns true if all the points of b are solutions of c */
int rp_ctr_cond_inner (rp_ctr_cond c, rp_box b);

/* Display c on out */
void rp_ctr_cond_display (FILE* out, rp_ctr_cond c,
			  rp_vector_variable var, int digits);

/* --------------------- */
/* Piecewise constraints */
/* --------------------- */

/* General form: piecewise(x, I1:C1, ..., Ik:Ck) */
typedef struct
{
  rp_interval dom;   /* some Ij          */
  rp_ctr_num * ctr;  /* corresponding Cj */
  int size;          /* cardinal of Cj   */
}
rp_ctr_piecewise_elem;

typedef struct
{
  int var;                      /* the variable                       */
  rp_ctr_piecewise_elem * ptr;  /* the Ij:Cj                          */
  rp_union_interval guard;      /* union of Ij after bound processing */
  int arity;                    /* constraint arity                   */
}
rp_ctr_piecewise_def;

typedef rp_ctr_piecewise_def * rp_ctr_piecewise;

#define rp_ctr_piecewise_var(c)              (c)->var
#define rp_ctr_piecewise_ptr(c)              (c)->ptr
#define rp_ctr_piecewise_arity(c)            (c)->arity
#define rp_ctr_piecewise_guard(c)            (c)->guard
#define rp_ctr_piecewise_elem_dom(c,i)       (c)->ptr[i].dom
#define rp_ctr_piecewise_elem_size(c,i)      (c)->ptr[i].size
#define rp_ctr_piecewise_elem_ptr(c,i)       (c)->ptr[i].ctr
#define rp_ctr_piecewise_elem_ctrnum(c,i,j)  (c)->ptr[i].ctr[j]

/* Creation of an empty piecewise constraint for variable v */
void rp_ctr_piecewise_create (rp_ctr_piecewise * c, int v);

/* Destruction */
void rp_ctr_piecewise_destroy (rp_ctr_piecewise * c);

/* Insertion of a new domain */
/* Returns false if x stricly intersects another domain */
int rp_ctr_piecewise_insert_domain (rp_ctr_piecewise c, rp_interval x);

/* Insertion of a constraint associated with the last created domain */
void rp_ctr_piecewise_insert_constraint (rp_ctr_piecewise c, rp_ctr_num ctr);

/* Returns true if no point of b is solution of c */
int rp_ctr_piecewise_unfeasible (rp_ctr_piecewise c, rp_box b);

/* Returns true if all the points of b are solutions of c */
int rp_ctr_piecewise_inner (rp_ctr_piecewise c, rp_box b);

/* Display c on out */
void rp_ctr_piecewise_display (FILE* out, rp_ctr_piecewise c,
			       rp_vector_variable var, int digits);

/* ----------------------- */
/* Generic constraint type */
/* ----------------------- */

#define RP_CONSTRAINT_NUMERICAL    1
#define RP_CONSTRAINT_CONDITIONAL  2
#define RP_CONSTRAINT_PIECEWISE    3

/* one of the following representation */
typedef union
{
  rp_ctr_num cnum;
  rp_ctr_cond cond;
  rp_ctr_piecewise piece;
}
rp_constraint_val;

/* association type-representation */
typedef struct
{
  int type;                /* constraint type     */
  rp_constraint_val val;   /* the constraint      */
  int * vptr;              /* subset of variables */
  int vsize;               /* size of vars        */
}
rp_constraint_def;

typedef rp_constraint_def * rp_constraint;

#define rp_constraint_type(c)        (c)->type
#define rp_constraint_num(c)         (c)->val.cnum
#define rp_constraint_cond(c)        (c)->val.cond
#define rp_constraint_piece(c)       (c)->val.piece
#define rp_constraint_vptr(c)        (c)->vptr
#define rp_constraint_arity(c)       (c)->vsize
#define rp_constraint_var(c,i)       (c)->vptr[i]


/* Declare that c contains var */
void rp_constraint_insert_variable(rp_constraint c, int var);

/* Declare that c contains all the variables of cnum */
void rp_constraint_insert_variable_num(rp_constraint c, rp_ctr_num cnum);

/* Creation of a constraint representing a numerical constraint */
void rp_constraint_create_num (rp_constraint * c,
			       rp_ctr_num cnum);

/* Creation of a constraint representing a conditional constraint */
void rp_constraint_create_cond (rp_constraint * c,
			        rp_ctr_cond cond);

/* Creation of a constraint representing a piecewise constraint */
void rp_constraint_create_piece (rp_constraint * c,
				 rp_ctr_piecewise piece);

/* Destruction */
void rp_constraint_destroy (rp_constraint * c);

/* Satisfiability tests */
int rp_constraint_unfeasible (rp_constraint c, rp_box b);
int rp_constraint_inner      (rp_constraint c, rp_box b);

/* Display c on out */
void rp_constraint_display (FILE* out, rp_constraint c,
			    rp_vector_variable var, int digits);

#define rp_constraint_display_simple(c,a) \
  rp_constraint_display(stdout,c,a,8)

#define rp_constraint_display_simple_nl(c,a) \
  rp_constraint_display(stdout,c,a,8); \
  printf("\n")

/* --------------------- */
/* Vector of constraints */
/* --------------------- */

/* Equality test between constraints x and y */
int rp_constraint_vector_cmp (void * x, const void * y);

/* Destruction function for constraints in vectors */
void rp_constraint_vector_free (void * x);

/* Display function for constraints in vectors */
void rp_constraint_vector_display (FILE * out, void * x);

/* Vector type */
#define rp_vector_constraint rp_vector

/* Creation of v */
void rp_vector_constraint_create (rp_vector * v);

/* Display v on out */
void rp_vector_constraint_display (FILE * out,
				   rp_vector_constraint v,
				   rp_vector_variable vars,
				   int digits);

#ifdef __cplusplus
}
#endif

#endif /* RP_CONSTRAINT_H */
