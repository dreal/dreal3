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
 * rp_problem.c                                                             *
 ****************************************************************************/

#include <string.h>
#include "rp_problem.h"

extern void rp_box_enlarge_size (rp_box* b, int n);

/* Creation of a table of symbols */
void rp_table_symbol_create(rp_table_symbol * t)
{
  rp_malloc(*t,rp_table_symbol_def*,sizeof(rp_table_symbol_def));
  rp_vector_constant_create(&rp_table_symbol_nums(*t));
  rp_vector_variable_create(&rp_table_symbol_vars(*t));
  rp_vector_function_create(&rp_table_symbol_funcs(*t));
}

/* Destruction of a table of symbols */
void rp_table_symbol_destroy(rp_table_symbol * t)
{
  rp_vector_destroy(&rp_table_symbol_funcs(*t));
  rp_vector_destroy(&rp_table_symbol_vars(*t));
  rp_vector_destroy(&rp_table_symbol_nums(*t));
  rp_free(*t);
}

/* Creation of a problem */
void rp_problem_create(rp_problem * p, char * name)
{
  rp_malloc(*p,rp_problem_def*,sizeof(rp_problem_def));
  if (name!=NULL)
  {
    rp_malloc(rp_problem_name(*p),char*,sizeof(char)*(strlen(name)+1));
    strcpy(rp_problem_name(*p),name);
  }
  else
  {
    rp_problem_name(*p) = NULL;
  }
  rp_table_symbol_create(&rp_problem_symb(*p));
  rp_vector_constraint_create(&rp_problem_ctrs(*p));
  rp_box_create(&rp_problem_box(*p),0);
}

/* Destruction of a problem */
void rp_problem_destroy(rp_problem * p)
{
  rp_box_destroy(&rp_problem_box(*p));
  rp_vector_destroy(&rp_problem_ctrs(*p));
  rp_table_symbol_destroy(&rp_problem_symb(*p));
  if (rp_problem_name(*p)!=NULL)
  {
    rp_free(rp_problem_name(*p));
  }
  rp_free(*p);
}

/* name of p := name*/
void rp_problem_set_name(rp_problem p, char * name)
{
  if (rp_problem_name(p)!=NULL)
  {
    rp_free(rp_problem_name(p));
  }
  rp_malloc(rp_problem_name(p),char*,sizeof(char)*(strlen(name)+1));
  strcpy(rp_problem_name(p),name);
}

/* Creation of the initial box from the variable domains */
/* Returns false if the box is empty                     */
int rp_problem_set_initial_box(rp_problem p)
{
  int i;
  if (rp_vector_size(rp_problem_vars(p))>=0)
  {
    rp_box_enlarge_size(&rp_problem_box(p),rp_vector_size(rp_problem_vars(p)));
    for (i=0; i<rp_vector_size(rp_problem_vars(p)); ++i)
    {
      rp_union_hull(rp_box_elem(rp_problem_box(p),i),
		    rp_variable_domain(rp_vector_variable_elem(rp_problem_vars(p),i)));
      if (rp_interval_empty(rp_box_elem(rp_problem_box(p),i)))
      {
	return( 0 );
      }
    }
    return( 1 );
  }
  else
  {
    return( 0 );
  }
}

/* Display p on out */
void rp_problem_display(FILE * out, rp_problem p)
{
  fprintf(out,"Problem %s\n",rp_problem_name(p));
  fprintf(out,"--- nums:\n");
  rp_vector_display(out,rp_problem_nums(p));
  fprintf(out,"--- vars:\n");
  rp_vector_display(out,rp_problem_vars(p));
  fprintf(out,"--- ctrs:\n");
  rp_vector_constraint_display(out,rp_problem_ctrs(p),rp_problem_vars(p),8);
}
