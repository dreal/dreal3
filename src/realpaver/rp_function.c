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
 * rp_function.c                                                            *
 ****************************************************************************/

#include <string.h>
#include "rp_function.h"

/* Creation */
void rp_function_create(rp_function * f, const char * s)
{
  rp_malloc(*f,rp_function_def*,sizeof(rp_function_def));
  if (s!=NULL)
  {
    rp_malloc(rp_function_name(*f),char*,1+strlen(s));
    strcpy(rp_function_name(*f),s);
  }
  rp_vector_variable_create(&rp_function_lvars(*f));
  rp_function_arity(*f) = 0;
  rp_function_rep(*f) = NULL;
}

/* Destruction */
void rp_function_destroy(rp_function * f)
{
  rp_free(rp_function_name(*f));
  rp_vector_destroy(&rp_function_lvars(*f));
  if (rp_function_rep(*f)!=NULL)
  {
    rp_erep_destroy(&rp_function_rep(*f));
  }
  rp_free(*f);
}

/* Insertion of a local variable of name s */
int rp_function_insert_var(rp_function f, const char * s)
{
  int index;
  if (rp_vector_variable_contains(rp_function_lvars(f),s,&index))
  {
    index = -1;
  }
  else
  {
    rp_variable v;
    rp_variable_create(&v,s);
    index = rp_vector_insert(rp_function_lvars(f),v);
    ++rp_function_arity(f);
  }
  return( index );
}

/* Insertion of the tree-representation of f */
void rp_function_insert_expr(rp_function f, rp_erep e)
{
  rp_function_rep(f) = e;
}

/* Equality test between function f and string y */
int rp_function_vector_cmp(void * x, const void * y)
{
  return( strcmp(rp_function_name((rp_function)x),(const char *)y)==0 );
}

/* Destruction function for functions in vectors */
void rp_function_vector_free(void * x)
{
  rp_function f = (rp_function)x;
  rp_function_destroy(&f);
}

/* Display function for functions in vectors */
void rp_function_vector_display(FILE * /*out*/, void * /*x*/)
{
}

/* Creation of v */
void rp_vector_function_create(rp_vector * v)
{
  rp_vector_create(v,
                   rp_function_vector_cmp,
                   rp_function_vector_free,
                   rp_function_vector_display);
}

/* Returns the first occurrence of s in v, NULL if no occurrence*/
rp_function * rp_vector_function_contains(rp_vector v,
                                          const char * s,
                                          int * index)
{
  if (rp_vector_contains(v,s,index))
  {
    return( (rp_function*)&(rp_vector_elem(v,*index)) );
  }
  else
  {
    return( NULL );
  }
}
