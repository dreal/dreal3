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
 * rp_container.h                                                           *
 ****************************************************************************/

#ifndef RP_CONTAINER_H
#define RP_CONTAINER_H 1

#ifdef __cplusplus
extern "C" {
#endif

#include <stdio.h>
#include <stdlib.h>
#include "rp_config.h"
#include "rp_memory.h"

/* ------------------------------- */
/* Vectors of pointers of any type */
/* ------------------------------- */

typedef int  (* rp_vector_cmp_elem)(void *, const void *);
typedef void (* rp_vector_free_elem)(void *);
typedef void (*rp_vector_display_elem)(FILE *, void *);

int rp_vector_cmp_basic      (void * p, const void * q);
void rp_vector_free_basic    (void * p);
void rp_vector_display_basic (FILE * f, void * p);

typedef struct
{
  int size;                    /* number of elements               */
  void ** ptr;                 /* elements                         */
  rp_vector_cmp_elem cmp;      /* comparison function of elements  */
  rp_vector_free_elem f;       /* destruction function of elements */
  rp_vector_display_elem dis;  /* display function of elements     */
}
rp_vector_def;

typedef rp_vector_def * rp_vector;  /* vector type */

#define rp_vector_size(v)    (v)->size
#define rp_vector_ptr(v)     (v)->ptr
#define rp_vector_elem(v,i)  (v)->ptr[i]
#define rp_vector_cmp(v)     (v)->cmp
#define rp_vector_free(v)    (v)->f
#define rp_vector_dis(v)     (v)->dis

/* Creation of a vector of elements */
void rp_vector_create (rp_vector * v,
		       rp_vector_cmp_elem cmp,
		       rp_vector_free_elem dest,
		       rp_vector_display_elem dis);

/* Creation of a vector of elements */
void rp_vector_create_basic (rp_vector * v);

/* Destruction of a vector of elements */
void rp_vector_destroy (rp_vector * v);

/* If x occurs in v then true is returned       */
/*    index := position of the first occurrence */
/* Otherwise false is returned                  */
int rp_vector_contains (rp_vector v, const void * x, int * index);

/* Insertion of an element x in v that returns its index */
int rp_vector_insert (rp_vector v, void * x);

/* Display v on out */
void rp_vector_display (FILE * out, rp_vector v);

/*-----------------*/
/* Set of integers */
/*-----------------*/

typedef struct
{
  int * ptr;
  int size;
}
rp_intset_def;

typedef rp_intset_def * rp_intset;

#define rp_intset_size(s)    (s)->size
#define rp_intset_ptr(s)     (s)->ptr
#define rp_intset_elem(s,i)  (s)->ptr[i]
#define rp_intset_empty(s)   ((s)->size==0)

/* Creation of an empty set */
void rp_intset_create(rp_intset * s);

/* Destruction */
void rp_intset_destroy(rp_intset * s);

/* Checks the existence of an element */
int rp_intset_contains(rp_intset s, int e);

/* Insertion of an element */
void rp_intset_insert(rp_intset s, int e);

#ifdef __cplusplus
}
#endif

#endif /* RP_CONTAINER_H */
