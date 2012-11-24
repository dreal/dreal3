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
 * rp_constant.h                                                            *
 ****************************************************************************/

#ifndef RP_CONSTANT_H
#define RP_CONSTANT_H 1

#ifdef __cplusplus
extern "C" {
#endif

#include <stdio.h>
#include <stdlib.h>
#include "rp_config.h"
#include "rp_memory.h"
#include "rp_container.h"
#include "rp_interval.h"

/* ----------------- */
/* The constant type */
/* ----------------- */

typedef struct
{
  char * name;
  rp_interval val;
}
rp_constant_def;

typedef rp_constant_def * rp_constant;


#define rp_constant_name(c)  (c)->name
#define rp_constant_val(c)   (c)->val

void rp_constant_create  (rp_constant * c, const char * s, rp_interval i);
void rp_constant_destroy (rp_constant * c);

#define RP_CONSTANT_NAME_NULL ""

/* ------------------- */
/* Vector of constants */
/* ------------------- */

/* Equality test between constant x and string y */
int rp_constant_vector_cmp(void * x, const void * y);

/* Destruction function for constants in vectors */
void rp_constant_vector_free(void * x);

/* Display function for constants in vectors */
void rp_constant_vector_display(FILE * out, void * x);

/* Vector type */
#define rp_vector_constant rp_vector

/* Creation of v */
void rp_vector_constant_create(rp_vector * v);

/* Returns the first occurrence of s in v, NULL if no occurrence */
rp_constant * rp_vector_constant_contains(rp_vector v,
					  const char * s,
					  int * index);

#ifdef __cplusplus
}
#endif

#endif /* RP_CONSTANT_H */
