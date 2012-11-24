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
 * rp_function.h                                                            *
 ****************************************************************************/

#ifndef RP_FUNCTION_H
#define RP_FUNCTION_H 1

#ifdef __cplusplus
extern "C" {
#endif

#include <stdio.h>
#include <stdlib.h>
#include "rp_config.h"
#include "rp_memory.h"
#include "rp_expression.h"

/* ----------------- */
/* The function type */
/* ----------------- */

typedef struct
{
  char * name;               /* function name           */
  rp_erep rep;               /* the tree-representation */
  rp_vector_variable lvars;  /* local variables         */
  int arity;                 /* size of lvars           */
}
rp_function_def;

typedef rp_function_def * rp_function;

#define rp_function_name(f)    (f)->name
#define rp_function_rep(f)     (f)->rep
#define rp_function_lvars(f)   (f)->lvars
#define rp_function_arity(f)   (f)->arity

/* i-th local variable stored as -(i+1) in the tree-representation */
/*    -> no confusion wrt. global variables                        */
#define rp_function_local_var(i) (-(i+1))

/* Creation */
void rp_function_create(rp_function * f, const char * s);

/* Destruction */
void rp_function_destroy(rp_function * f);

/* Insertion of a local variable of name s */
int rp_function_insert_var(rp_function f, const char * s);

/* Insertion of the tree-representation of f */
void rp_function_insert_expr(rp_function f, rp_erep e);

/* Vector type */
#define rp_vector_function rp_vector

#define rp_vector_function_elem(v,i) \
  (rp_function)rp_vector_elem(v,i)

/* Creation of v */
void rp_vector_function_create(rp_vector * v);

/* Returns the first occurrence of s in v, NULL if no occurrence*/
rp_function * rp_vector_function_contains(rp_vector v,
                                          const char * s,
                                          int * index);

#ifdef __cplusplus
}
#endif

#endif /* RP_FUNCTION_H */
