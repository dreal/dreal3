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
 * rp_box.c                                                                 *
 ****************************************************************************/

#include <memory.h>
#include "rp_box.h"

/* Creation of a box of n intervals */
void rp_box_create(rp_box* b, int n)
{
  if (n>=0)
  {
    rp_malloc(*b,rp_box,(n+RP_BOX_RESERVED_CELL)*sizeof(rp_box_cell));
    rp_box_size(*b) = n;
    rp_box_set_unsafe(*b);
    rp_box_nvdec(*b) = rp_box_nvaux(*b) = 0;
  }
  else
  {
    (*b) = NULL;
  }
}

/* Enlarge the size of an already created box with n intervals */
void rp_box_enlarge_size(rp_box* b, int n)
{
  if (n>0)
  {
    rp_box_size(*b) += n;
    rp_realloc(*b,rp_box,
               (rp_box_size(*b)+RP_BOX_RESERVED_CELL)*sizeof(rp_box_cell));
  }
}

/* Destruction of a box */
void rp_box_destroy(rp_box* b)
{
  rp_free(*b);
}

/* Copy of a box: b := src */
void rp_box_copy(rp_box b, rp_box src)
{
  memcpy(b,src,(RP_BOX_RESERVED_CELL +
                rp_min_num(rp_box_size(b),
                           rp_box_size(src)))*sizeof(rp_box_cell));
}

/* Creation of a box b equivalent to src */
void rp_box_clone (rp_box* b, rp_box src)
{
  rp_box_create(b,rp_box_size(src));
  rp_box_copy(*b,src);
}

/* Returns true if b is equal to the empty set */
int rp_box_empty(rp_box b)
{
  if ((rp_box_size(b)==0) ||
      ((((b)[0].property.type & RP_BOX_TYPE_EMPTY_MASK)
        >> RP_BOX_TYPE_EMPTY_BIT) == RP_BOX_TYPE_EMPTY_YES))
  {
    return( 1 );
  }
  else
  {
    int i;
    for (i=0; i<rp_box_size(b); ++i)
    {
      if (rp_interval_empty(rp_box_elem(b,i)))
      {
        rp_box_set_empty(b);  /* handling of inconsistent type */
        return( 1 );
      }
    }
    return( 0 );
  }
}

/* Returns the width of b as max_i width(b[i]) */
double rp_box_width(rp_box b)
{
  double w = rp_interval_width(rp_box_elem(b,0)), x;
  int i;
  for (i=1; i<rp_box_size(b); ++i)
  {
    if ((x=rp_interval_width(rp_box_elem(b,i)))>w)
    {
      w = x;
    }
  }
  return( w );
}

/* Returns the volume of b as Prod_i width(b[i]) */
double rp_box_volume(rp_box b)
{
  double v = 1.0;
  int i;
  for (i=0; i<rp_box_size(b); ++i)
  {
    v *= rp_interval_width(rp_box_elem(b,i));
  }
  return( v );
}

double rp_box_volume_log (rp_box b)
{
    double v = 0.0;
    int i;
    for (i=0; i<rp_box_size(b); ++i)
    {
        double w = rp_interval_width(rp_box_elem(b,i));
        if (w > 0)
            v += w;
    }
    return( v );
}

/* Returns the distance between two boxes */
double rp_box_distance(rp_box b1, rp_box b2)
{
  int i;
  double x, dist = 0.0;
  for (i=0; i<rp_box_size(b1); ++i)
  {
    if ((x = rp_interval_distance(rp_box_elem(b1,i),
                                  rp_box_elem(b2,i))) > dist)
    {
      dist = x;
    }
  }
  return( dist );
}

/* Returns true if the box is canonical */
int rp_box_canonical(rp_box b)
{
  int i;
  for (i=0; i<rp_box_size(b); ++i)
  {
    if (!rp_interval_canonical(rp_box_elem(b,i)))
      return( 0 );
  }
  return( 1 );
}


/* b := hull(b,src) */
void rp_box_merge(rp_box b, rp_box src)
{
  int i;
  rp_interval aux;
  for (i=0; i<rp_box_size(b); ++i)
  {
    rp_interval_hull(aux,rp_box_elem(b,i),rp_box_elem(src,i));
    rp_interval_copy(rp_box_elem(b,i),aux);
  }
}

/* Display b on out */
void rp_box_display(FILE *out, rp_box b, int digits, int mode)
{
  if (rp_box_empty(b))
  {
    fprintf(out,"empty");
  }
  else
  {
    int i;
    fprintf(out,"(");
    for (i=0; i<rp_box_size(b); ++i)
    {
      rp_interval_display(out,rp_box_elem(b,i),digits,mode);
      if (i<(rp_box_size(b)-1))
      {
        fprintf(out,",");
      }
    }
    fprintf(out,")");
  }
}
