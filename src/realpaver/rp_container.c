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
 * rp_container.c                                                           *
 ****************************************************************************/

#include "rp_container.h"


/* ------------------------------- */
/* Vectors of pointers of any type */
/* ------------------------------- */

/* Creation of a vector of elements */
void rp_vector_create(rp_vector * v,
                      rp_vector_cmp_elem cmp,
                      rp_vector_free_elem dest,
                      rp_vector_display_elem dis)
{
  rp_malloc(*v,rp_vector_def*,sizeof(rp_vector_def));
  rp_vector_size(*v) = 0;
  rp_vector_ptr(*v)  = NULL;
  rp_vector_cmp(*v)  = cmp;
  rp_vector_free(*v) = dest;
  rp_vector_dis(*v)  = dis;
}

int rp_vector_cmp_basic(void * p, const void * q) { return (p==q); }
void rp_vector_free_basic(void * p) {}
void rp_vector_display_basic(FILE * f, void * p) {}

/* Creation of a vector of elements */
void rp_vector_create_basic(rp_vector * v)
{
  rp_vector_create(v,
		   rp_vector_cmp_basic,
		   rp_vector_free_basic,
		   rp_vector_display_basic);
}

/* Destruction of a vector of elements */
void rp_vector_destroy(rp_vector * v)
{
  if (rp_vector_size(*v)!=0)
  {
    int i;
    for (i=0; i<rp_vector_size(*v); ++i)
    {
      rp_vector_free(*v)(rp_vector_elem(*v,i));
    }
    rp_free(rp_vector_ptr(*v));
    rp_vector_size(*v) = 0;
  }
  rp_free(*v);
}

/* If x occurs in v then true is returned       */
/*    index := position of the first occurrence */
/* Otherwise false is returned                  */
int rp_vector_contains(rp_vector v, const void * x, int * index)
{
  int i;
  for (i=0; i<rp_vector_size(v); ++i)
  {
    if (rp_vector_cmp(v)(rp_vector_elem(v,i),x))
    {
      (*index) = i;
      return( 1 );
    }
  }
  return( 0 );
}

/* Insertion of an element x in v that returns its index */
int rp_vector_insert(rp_vector v, void * x)
{
  int i;
  if (!rp_vector_contains(v,x,&i))
  {
    i = rp_vector_size(v) ++;
    if (rp_vector_ptr(v)==NULL)
    {
      rp_malloc(rp_vector_ptr(v),void**,sizeof(void*));
    }
    else
    {
      rp_realloc(rp_vector_ptr(v),void**,rp_vector_size(v)*sizeof(void*));
    }
    rp_vector_elem(v,i) = x;
  }
  return( i );
}

/* Display v on out */
void rp_vector_display(FILE * out, rp_vector v)
{
  if (rp_vector_size(v)==0)
  {
    fprintf(out,"empty vector");
  }
  else
  {
    int i;
    for (i=0; i<rp_vector_size(v); ++i)
    {
      rp_vector_dis(v)(out,rp_vector_elem(v,i));
    }
  }
}

/*-----------------*/
/* Set of integers */
/*-----------------*/

/* Creation of an empty set */
void rp_intset_create(rp_intset * s)
{
  rp_malloc(*s,rp_intset_def*,sizeof(rp_intset_def));
  rp_intset_size(*s) = 0;
  rp_intset_ptr(*s) = NULL;
}

/* Destruction */
void rp_intset_destroy(rp_intset * s)
{
  if (rp_intset_size(*s)>0)
  {
    rp_free(rp_intset_ptr(*s));
  }
  rp_free(*s);
}

/* Checks the existence of an element */
int rp_intset_contains(rp_intset s, int e)
{
  int i;
  for (i=0; i<rp_intset_size(s); ++i)
  {
    if (e==rp_intset_elem(s,i))
    {
      return( 1 );
    }
  }
  return( 0 );
}

/* Insertion of an element */
void rp_intset_insert(rp_intset s, int e)
{
  if (!rp_intset_contains(s,e))
  {
    ++rp_intset_size(s);
    if (rp_intset_size(s)==1)
    {
      rp_malloc(rp_intset_ptr(s),int*,sizeof(int));
    }
    else
    {
      rp_realloc(rp_intset_ptr(s),int*,rp_intset_size(s)*sizeof(int));
    }
    rp_intset_elem(s,rp_intset_size(s)-1) = e;
  }
}
