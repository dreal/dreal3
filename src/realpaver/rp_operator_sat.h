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
 * rp_operator_sat.h                                                        *
 ****************************************************************************/

#ifndef RP_OPERATOR_SAT
#define RP_OPERATOR_SAT

#ifdef __cplusplus
extern "C" {
#endif

#include <stdio.h>
#include <stdlib.h>
#include "rp_config.h"
#include "rp_memory.h"
#include "rp_constraint.h"
#include "rp_operator_num.h"

/* ----------------------------------- */
/* Interval stack for search processes */
/* ----------------------------------- */

typedef struct
{
  int size;            /* stack size           */
  int top;             /* index of top element */
  rp_interval * ptr;   /* elements             */
}
rp_stack_interval_def;

typedef rp_stack_interval_def rp_stack_interval[1];

#define rp_stack_interval_size(s)     (s)[0].size
#define rp_stack_interval_ptr(s)      (s)[0].ptr
#define rp_stack_interval_top(s)      (s)[0].top

#define rp_stack_interval_topelem(s)  (s)[0].ptr[(s)[0].top]
#define rp_stack_interval_empty(s)    ((s)[0].top==-1)
#define rp_stack_interval_full(s)     ((s)[0].top==((s)[0].size-1))

/* Creation of an empty stack with default size */
void rp_stack_interval_create (rp_stack_interval * s, int size);

/* Destruction of stack */
void rp_stack_interval_destroy (rp_stack_interval * s);

/* Pop operation */
void rp_stack_interval_pop (rp_stack_interval s);

/* Push operation */
void rp_stack_interval_push (rp_stack_interval s, rp_interval i);

/* ----------------------------- */
/* Reduction/narrowing operators */
/* ----------------------------- */

/* Projection of c onto the variables belonging to b */
/* Returns false if an empty domain is computed      */
int rp_sat_hull_eq (rp_ctr_num c, rp_box b);

/* Projection of c onto the variables belonging to b */
/* Returns false if an empty domain is computed      */
int rp_sat_hull_inf (rp_ctr_num c, rp_box b);

/* Projection of c onto the variables belonging to b */
/* Returns false if an empty domain is computed      */
int rp_sat_hull_sup (rp_ctr_num c, rp_box b);


/* Reduction of b(x) with precision eps by box consistency onto f = 0 */
int rp_sat_box_eq (rp_expression f, rp_expression df_dx,
		   rp_box b, int x, double improve, double eps);

/* Reduction of b(x) with precision eps by box consistency onto f >= 0 */
int rp_sat_box_sup (rp_expression f, rp_expression df_dx,
		    rp_box b, int x, double improve, double eps);

/* Reduction of b(x) with precision eps by box consistency onto f <= 0 */
int rp_sat_box_inf (rp_expression f, rp_expression df_dx,
		    rp_box b, int x, double improve, double eps);

/* ------------------- */
/* Auxiliary functions */
/* ------------------- */

/* Split operations at one domain bound */
/* rem := domain \ bound                */
typedef void (*rp_opsplit)(rp_interval bound, rp_interval rem,
			   rp_interval domain, double eps);

/* let domain = [a,b] --> bound := [a,min((a+eps)+,b)] */
void rp_opsplit_lb (rp_interval bound, rp_interval rem,
		    rp_interval domain, double eps);

/* let domain = [a,b] --> bound := [max((b-eps)-,a),b] */
void rp_opsplit_rb (rp_interval bound, rp_interval rem,
		    rp_interval domain, double eps);

/* Split operation in search managing the search ordering */
typedef void (*rp_opshrink_split)(rp_stack_interval search,
				  rp_interval domain);

/* let domain=[a,b] and let c be the midpoint of [a,b]              */
/* push in search [c,b] and then [a,c] that becomes the top element */
void rp_opshrink_split_lb (rp_stack_interval search,
			   rp_interval domain);

/* let domain=[a,b] and let c be the midpoint of [a,b]              */
/* push in search [a,c] and then [c,b] that becomes the top element */
void rp_opshrink_split_rb (rp_stack_interval search,
			   rp_interval domain);

/* Search a zero of f at one bound of x with precision eps */
int rp_opshrink (rp_expression f, rp_expression df_dx,
		 rp_box b, int x, double improve, double eps,
		 rp_opsplit bsplit, rp_opshrink_split shsplit);

#ifdef __cplusplus
}
#endif

#endif /* RP_OPERATOR_SAT */
