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
 * rp_variable.h                                                            *
 ****************************************************************************/

#pragma once

#include <stdio.h>
#include <stdlib.h>
#include "rp_config.h"
#include "rp_memory.h"
#include "rp_container.h"
#include "rp_union_interval.h"

/* ----------------- */
/* The variable type */
/* ----------------- */

typedef struct
{
  char * name;               /* variable name                                 */
  unsigned int status;       /* various information                           */
  double precision;          /* required precision of computed values         */
  int constrained;           /* number of constraints containing the variable */
  rp_union_interval domain;  /* initial domain                                */
}
rp_variable_def;

typedef rp_variable_def * rp_variable;

#define rp_variable_name(v)         (v)->name
#define rp_variable_status(v)       (v)->status
#define rp_variable_precision(v)    (v)->precision
#define rp_variable_absolute(v)     (v)->absolute
#define rp_variable_domain(v)       (v)->domain
#define rp_variable_constrained(v)  (v)->constrained

#define RP_VARIABLE_NAME_NULL "_null"

/* Characteristics of a variable defined as bit positions in status */
#define RP_VARIABLE_STATUS_DECISION       0
#define RP_VARIABLE_STATUS_INTEGER        1
#define RP_VARIABLE_STATUS_REAL           2
#define RP_VARIABLE_STATUS_PRECISION      3

#define rp_variable_init_status(v) rp_variable_status(v) = 0

#define rp_variable_set_integer(v) \
   rp_variable_status(v) += (1 << RP_VARIABLE_STATUS_INTEGER)

#define rp_variable_integer(v) \
   ((rp_variable_status(v) & (1 << RP_VARIABLE_STATUS_INTEGER)) != 0)

#define rp_variable_set_decision(v) \
   rp_variable_status(v) += (1 << RP_VARIABLE_STATUS_DECISION)

#define rp_variable_decision(v) \
   ((rp_variable_status(v) & (1 << RP_VARIABLE_STATUS_DECISION)) != 0)

#define rp_variable_set_real(v) \
   rp_variable_status(v) += (1 << RP_VARIABLE_STATUS_REAL)

#define rp_variable_real(v) \
   ((rp_variable_status(v) & (1 << RP_VARIABLE_STATUS_REAL)) != 0)

#define rp_variable_absolute_precision(v) \
   ((rp_variable_status(v) & (1 << RP_VARIABLE_STATUS_PRECISION)) == 0)

#define rp_variable_relative_precision(v) \
   ((rp_variable_status(v) & (1 << RP_VARIABLE_STATUS_PRECISION)) != 0)

#define rp_variable_set_absolute_precision(v) \
   if (rp_variable_relative_precision(v)) \
     rp_variable_status(v) -= (1 << RP_VARIABLE_STATUS_PRECISION)

#define rp_variable_set_relative_precision(v) \
   if (rp_variable_absolute_precision(v)) \
     rp_variable_status(v) += (1 << RP_VARIABLE_STATUS_PRECISION)

void rp_variable_create  (rp_variable * v, const char * s);
void rp_variable_destroy (rp_variable * v);


/* ------------------- */
/* Vector of variables */
/* ------------------- */

/* Equality test between variable x and string y */
int rp_variable_vector_cmp(void * x, const void * y);

/* Destruction function for variables in vectors */
void rp_variable_vector_free(void * x);

/* Display function for variables in vectors */
void rp_variable_vector_display(FILE * out, void * x);

/* Vector type */
#define rp_vector_variable rp_vector

#define rp_vector_variable_elem(v,i) \
  (rp_variable)rp_vector_elem(v,i)

/* Creation of v */
void rp_vector_variable_create(rp_vector * v);

/* Returns the first occurrence of s in v, NULL if no occurrence*/
rp_variable * rp_vector_variable_contains(rp_vector v,
                                          const char * s,
                                          int * index);
