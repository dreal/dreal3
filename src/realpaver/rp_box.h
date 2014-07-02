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
 * rp_box.h                                                                 *
 ****************************************************************************/

#pragma once

#include <stdio.h>
#include <stdlib.h>
#include "rp_interval.h"

/* ------------ */
/* The box type */
/* ------------ */

typedef struct
{
  unsigned int type;
  int size;
  int split;
  int nvdec;
  int nvaux;
}
rp_box_property;

/* A box is unsafe (default type), inner if it has been       */
/* proved to be included in the solution set, safe if         */
/* it has been proved to contain a solution, or interval safe */
/* if it contains a canonical box verifying the interval test */

#define RP_BOX_TYPE_EMPTY_BIT   0
#define RP_BOX_TYPE_EMPTY_NO    0
#define RP_BOX_TYPE_EMPTY_YES   1
#define RP_BOX_TYPE_EMPTY_MASK  (1 << RP_BOX_TYPE_EMPTY_BIT)

#define RP_BOX_TYPE_SAFE_BIT    1
#define RP_BOX_TYPE_SAFE_NO     0
#define RP_BOX_TYPE_SAFE_YES    1
#define RP_BOX_TYPE_SAFE_MASK   (1 << RP_BOX_TYPE_SAFE_BIT)

#define RP_BOX_TYPE_INNER_BIT   2
#define RP_BOX_TYPE_INNER_NO    0
#define RP_BOX_TYPE_INNER_YES   1
#define RP_BOX_TYPE_INNER_MASK  (1 << RP_BOX_TYPE_INNER_BIT)

#define RP_BOX_TYPE_ISAFE_BIT   3
#define RP_BOX_TYPE_ISAFE_NO    0
#define RP_BOX_TYPE_ISAFE_YES   1
#define RP_BOX_TYPE_ISAFE_MASK  (1 << RP_BOX_TYPE_ISAFE_BIT)


typedef union
{
  rp_interval x;
  rp_box_property property;
}
rp_box_cell;

typedef rp_box_cell * rp_box;
typedef rp_box_cell const * rp_const_box;

#define RP_BOX_RESERVED_CELL 1

#define rp_box_size(b)        (b)[0].property.size
#define rp_box_elem(b,i)      (b)[i+RP_BOX_RESERVED_CELL].x

#define rp_box_split(b)       (b)[0].property.split
#define rp_box_set_split(b,i) (b)[0].property.split = i

#define rp_box_nvdec(b)       (b)[0].property.nvdec
#define rp_box_nvaux(b)       (b)[0].property.nvaux

#define rp_box_unsafe(b)				\
  ((!(rp_box_empty(b))) &&				\
   ((((b)[0].property.type & RP_BOX_TYPE_SAFE_MASK)	\
     >> RP_BOX_TYPE_SAFE_BIT) == RP_BOX_TYPE_SAFE_NO))

#define rp_box_safe(b)					\
  ((!(rp_box_empty(b))) &&				\
   ((((b)[0].property.type & RP_BOX_TYPE_SAFE_MASK)	\
     >> RP_BOX_TYPE_SAFE_BIT) == RP_BOX_TYPE_SAFE_YES))

#define rp_box_inner(b)					\
  ((!(rp_box_empty(b))) &&				\
   ((((b)[0].property.type & RP_BOX_TYPE_INNER_MASK)	\
     >> RP_BOX_TYPE_INNER_BIT) == RP_BOX_TYPE_INNER_YES))

#define rp_box_interval_safe(b)				\
  ((!(rp_box_empty(b))) &&				\
   ((((b)[0].property.type & RP_BOX_TYPE_ISAFE_MASK)		\
     >> RP_BOX_TYPE_ISAFE_BIT) == RP_BOX_TYPE_ISAFE_YES))

#define rp_box_set_empty(b)				\
  ((b)[0].property.type = 0 |				\
   (RP_BOX_TYPE_EMPTY_YES << RP_BOX_TYPE_EMPTY_BIT))

#define rp_box_set_inner(b)						\
  (b)[0].property.type |= (RP_BOX_TYPE_INNER_YES << RP_BOX_TYPE_INNER_BIT)

#define rp_box_set_safe(b)						\
  (b)[0].property.type |= (RP_BOX_TYPE_SAFE_YES << RP_BOX_TYPE_SAFE_BIT)

#define rp_box_set_unsafe(b)						\
  (b)[0].property.type |= (RP_BOX_TYPE_SAFE_NO << RP_BOX_TYPE_SAFE_BIT)

#define rp_box_set_interval_safe(b)						\
  (b)[0].property.type |= (RP_BOX_TYPE_ISAFE_YES << RP_BOX_TYPE_ISAFE_BIT)

/* --------- */
/* Functions */
/* --------- */

/* Creation of a box of n intervals */
void rp_box_create (rp_box* b, int n);

/* Enlarge the size of an already created box with n intervals */
void rp_box_enlarge_size (rp_box* b, int n);

/* Destruction of a box */
void rp_box_destroy (rp_box* b);

/* Copy of a box: b := src */
void rp_box_copy (rp_box b, rp_box src);

/* Creation of a box b equivalent to src */
void rp_box_clone (rp_box* b, rp_box src);

/* Returns true if b is equal to the empty set */
int rp_box_empty (rp_box b);

/* Compare two boxes: b1 and b2 */
bool rp_box_equal(rp_box b1, rp_box b2);

/* Returns the width of b as max_i width(b[i]) */
double rp_box_width (rp_box b);

/* Returns the volume of b as Prod_i width(b[i]) */
double rp_box_volume (rp_box b);

/* Returns the volume of b as log(Prod_i width(b[i])) */
double rp_box_volume_log (rp_box b);

/* Returns the distance between two boxes */
double rp_box_distance (rp_box b1, rp_box b2);

/* Returns true if the box is canonical */
int rp_box_canonical (rp_box b);

/* b := hull(b,src) */
void rp_box_merge (rp_box b, rp_box src);

/* Display b on out */
void rp_box_display (FILE *out, rp_box b, int digits, int mode);

#define rp_box_display_bounds(o,b,d) \
  rp_box_display(o,b,d,RP_INTERVAL_MODE_BOUND)

#define rp_box_display_midpoint(o,b,d) \
  rp_box_display(o,b,d,RP_INTERVAL_MODE_MID)

#define rp_box_display_simple(b) \
  rp_box_display(stderr,b,8,RP_INTERVAL_MODE_BOUND)

#define rp_box_display_simple_nl(b) \
  rp_box_display_simple(b); \
  fprintf(stderr, "\n")
