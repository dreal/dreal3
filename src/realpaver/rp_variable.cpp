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
 * rp_variable.c                                                            *
 ****************************************************************************/

#include <string.h>
#include "rp_variable.h"

/* Creation of a variable */
void rp_variable_create(rp_variable * v, const char * s)
{
  rp_malloc(*v,rp_variable_def*,sizeof(rp_variable_def));
  rp_variable_init_status(*v);
  rp_variable_precision(*v) = 1.0e-8;
  rp_variable_set_absolute_precision(*v);
  rp_variable_constrained(*v) = 0;
  rp_union_create(&rp_variable_domain(*v));
  if (s!=NULL)
  {
    rp_malloc(rp_variable_name(*v),char*,1+strlen(s));
    strcpy(rp_variable_name(*v),s);
  }
  else
  {
    rp_malloc(rp_variable_name(*v),char*,1+strlen(RP_VARIABLE_NAME_NULL));
    strcpy(rp_variable_name(*v),RP_VARIABLE_NAME_NULL);
  }
}

/* Destruction of a variable */
void rp_variable_destroy (rp_variable * v)
{
  rp_free(rp_variable_name(*v));
  rp_variable_init_status(*v);
  rp_union_destroy(&rp_variable_domain(*v));
  rp_free(*v);
}

/* Equality test between variable x and string y */
int rp_variable_vector_cmp(void * x, const void * y)
{
  return( strcmp(rp_variable_name((rp_variable)x),(const char *)y)==0 );
}

/* Destruction function for variables in vectors */
void rp_variable_vector_free(void * x)
{
  rp_variable v = (rp_variable)x;
  rp_variable_destroy(&v);
}

/* Display function for variables in vectors */
void rp_variable_vector_display(FILE * out, void * x)
{
  rp_variable v = (rp_variable)x;
  fprintf(out,"%s",rp_variable_name(v));
  if (rp_variable_integer(v))
  {
    fprintf(out,":int");
  }
  else if (rp_variable_real(v))
  {
    fprintf(out,":real/%.4g",rp_variable_precision(v));
  }
  fprintf(out," ~ ");
  rp_union_display_simple(out, rp_variable_domain(v));

  fprintf(out," occurs in %d constraints\n",rp_variable_constrained(v));
}

/* Creation of v */
void rp_vector_variable_create(rp_vector * v)
{
  rp_vector_create(v,
                   rp_variable_vector_cmp,
                   rp_variable_vector_free,
                   rp_variable_vector_display);
}

/* Returns the first occurrence of s in v, NULL if no occurrence*/
rp_variable * rp_vector_variable_contains(rp_vector v,
					  const char * s,
					  int * index)
{
  if (rp_vector_contains(v,s,index))
  {
    return( (rp_variable*)&(rp_vector_elem(v,*index)) );
  }
  else
  {
    return( NULL );
  }
}
