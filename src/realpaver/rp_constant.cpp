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
 * rp_constant.c                                                            *
 ****************************************************************************/

#include <string.h>
#include "rp_constant.h"

/* Creation of a constant */
void rp_constant_create(rp_constant * c, const char * s, rp_interval i)
{
  rp_malloc(*c,rp_constant_def*,sizeof(rp_constant_def));
  if (s!=NULL)
  {
    rp_malloc(rp_constant_name(*c),char*,1+strlen(s));
    strcpy(rp_constant_name(*c),s);
    rp_interval_copy(rp_constant_val(*c),i);
  }
  else
  {
    rp_malloc(rp_constant_name(*c),char*,1+strlen(RP_CONSTANT_NAME_NULL));
    strcpy(rp_constant_name(*c),RP_CONSTANT_NAME_NULL);
  }
    rp_interval_copy(rp_constant_val(*c),i);
}

/* Destruction of a constant */
void rp_constant_destroy(rp_constant * c)
{
  rp_free(rp_constant_name(*c));
  rp_free(*c);
}

/* Equality test between constant x and string y */
int rp_constant_vector_cmp(void * x, const void * y)
{
  return( strcmp(rp_constant_name((rp_constant)x),(const char *)y)==0 );
}

/* Destruction function for constants in vectors */
void rp_constant_vector_free(void * x)
{
  rp_constant c = (rp_constant)x;
  rp_constant_destroy(&c);
}

/* Display function for constants in vectors */
void rp_constant_vector_display(FILE * out, void * x)
{
  rp_constant c = (rp_constant)x;
  fprintf(out,"%s := ",rp_constant_name(c));
  rp_interval_display_simple_file(out, rp_constant_val(c));
  fprintf(out, "\n");
}

/* Creation of v */
void rp_vector_constant_create(rp_vector * v)
{
  rp_constant aux;
  rp_interval i;
  rp_vector_create(v,
                   rp_constant_vector_cmp,
                   rp_constant_vector_free,
                   rp_constant_vector_display);
  rp_interval_set_pi(i);
  rp_constant_create(&aux,"pi",i);
  rp_vector_insert(*v,aux);
  rp_interval_set(i,RP_INFINITY,RP_INFINITY);
  rp_constant_create(&aux,"inf",i);
  rp_vector_insert(*v,aux);
}

/* Returns the first occurrence of s in v, NULL if no occurrence*/
rp_constant * rp_vector_constant_contains(rp_vector v,
                                          const char * s,
                                          int * index)
{
  if (rp_vector_contains(v,s,index))
  {
    return( (rp_constant*)&(rp_vector_elem(v,*index)) );
  }
  else
  {
    return( NULL );
  }
}
