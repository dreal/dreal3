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
 * rp_union_interval.h                                                      *
 ****************************************************************************/

#ifndef RP_UNION_INTERVAL_H
#define RP_UNION_INTERVAL_H 1

#ifdef __cplusplus
extern "C" {
#endif

#include <stdio.h>
#include <stdlib.h>
#include "rp_interval.h"

/* --------------------------- */
/* The union of intervals type */
/* --------------------------- */

typedef struct
{
  int card;             /* cardinal of the union */
  int unused;           /* number of unused intervals in the union */
  rp_interval* elem;    /* ordered set of (n+unused) disjoint intervals */
}
rp_union_interval_def;  /* internal type */

/* A union of intervals is defined as an array of one struct */
/* rp_union_interval_def then it is a constant pointer       */
typedef rp_union_interval_def rp_union_interval[1];

#define rp_union_card(u)    ((u)[0]).card
#define rp_union_unused(u)  ((u)[0]).unused
#define rp_union_size(u)    ((rp_union_card(u))+(rp_union_unused(u)))
#define rp_union_ptr(u)     ((u)[0]).elem
#define rp_union_elem(u,k)  ((u)[0]).elem[k]

#define rp_union_empty(u)   (rp_union_card(u)==0)
#define rp_union_full(u)    (rp_union_unused(u)==0)

#define rp_union_binf(u)    rp_binf(rp_union_elem(u,0))
#define rp_union_bsup(u)    rp_bsup(rp_union_elem(u,rp_union_card(u)-1))

/* -------------------------------------- */
/* Functions: memory management, printing */
/* -------------------------------------- */

/* Creation of an empty union */
void rp_union_create       (rp_union_interval* u);

/* Destruction */
void rp_union_destroy      (rp_union_interval* u);

/* Creation of an empty union and allocation of size intervals */
void rp_union_create_size  (rp_union_interval* u, int size);

/* u := src */
void rp_union_copy         (rp_union_interval u, rp_union_interval src);

/* Display u on out */
void rp_union_display      (FILE *out, rp_union_interval u,
			    int digits, int mode);

#define rp_union_display_bounds(o,u,d) \
  rp_union_display(o,u,d,RP_INTERVAL_MODE_BOUND)

#define rp_union_display_midpoint(o,u,d) \
  rp_union_display(o,u,d,RP_INTERVAL_MODE_MID)

#define rp_union_display_simple(u) \
  rp_union_display(stdout,u,8,RP_INTERVAL_MODE_BOUND)

#define rp_union_display_simple_nl(u) \
  rp_union_display_simple(u); \
  printf("\n")

/* ----------- */
/* Comparisons */
/* ----------- */

/* Returns true if u1==u2 */
int rp_union_equal (rp_union_interval u1, rp_union_interval u2);

/* Returns true if u1!=u2 */
int rp_union_diff  (rp_union_interval u1, rp_union_interval u2);

/* Returns true if small is included in large */
int rp_union_included (rp_union_interval small, rp_union_interval large);

/* Returns true if x belongs to u */
int rp_union_contains (rp_union_interval u, double x);

/* Returns true if x is strictly greater than all points of u */
int rp_union_strictly_greater (rp_union_interval u, double x);

/* Returns true if x is strictly smaller than all points of u */
int rp_union_strictly_smaller (rp_union_interval u, double x);

/* Returns the smallest point of u greater than x */
double rp_union_next_double (rp_union_interval u, double x);

/* Returns the greatest point of u smaller than x */
double rp_union_prev_double (rp_union_interval u, double x);

/* Returns the index of the largest interval in u */
int rp_union_max_element(rp_union_interval u);

/* ----------------------- */
/* Set theoretic functions */
/* ----------------------- */

/* u := empty set */
void rp_union_set_empty      (rp_union_interval u);
void rp_union_set_empty_size (rp_union_interval u, int size);

/* i := interval hull ( u ) */
void rp_union_hull (rp_interval i, rp_union_interval u);

/* Insertion u := u union i */
void rp_union_insert (rp_union_interval u, rp_interval i);

/* Insertion u := u union v */
void rp_union_insert_uu (rp_union_interval u, rp_union_interval v);

/* Intersection u := u inter i and returns false if empty */
int rp_union_inter (rp_union_interval u, rp_interval i);

/* Intersection u := u inter v and returns false if empty */
int rp_union_inter_uu (rp_union_interval u, rp_union_interval v);

/* Intersection i := hull( i inter u ) and returns false if empty */
int rp_union_inter_iu (rp_interval i, rp_union_interval u);

/* ------------------------------ */
/* Non convex interval operations */
/* ------------------------------ */

/* result := i1 / i2 using the extended interval division */
/* returns the cardinal of result                         */
int rp_interval_extended_div (rp_union_interval result,
			      rp_interval i1, rp_interval i2);

#ifdef __cplusplus
}
#endif

#endif /* RP_UNION_INTERVAL_H */
