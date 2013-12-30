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
 * rp_problem.h                                                             *
 ****************************************************************************/

#ifndef RP_PROBLEM_H
#define RP_PROBLEM_H 1

#ifdef __cplusplus
extern "C" {
#endif

#include <stdio.h>
#include <stdlib.h>
#include "rp_config.h"
#include "rp_memory.h"
#include "rp_variable.h"
#include "rp_function.h"
#include "rp_box.h"
#include "rp_constant.h"
#include "rp_constraint.h"

class icp_solver;

/* ---------------- */
/* Table of symbols */
/* ---------------- */

typedef struct
{//s: vectors!!
  rp_vector_constant nums;
  rp_vector_variable vars;
  rp_vector_function funcs;
}
rp_table_symbol_def;

typedef rp_table_symbol_def * rp_table_symbol;

#define rp_table_symbol_nums(t)  (t)->nums
#define rp_table_symbol_vars(t)  (t)->vars
#define rp_table_symbol_funcs(t) (t)->funcs

/* Creation of a table of symbols */
void rp_table_symbol_create(rp_table_symbol * t);

/* Destruction of a table of symbols */
void rp_table_symbol_destroy(rp_table_symbol * t);

/* ---------------- */
/* The problem type */
/* ---------------- */

typedef struct
{
  rp_table_symbol symb;       /* constants and variables */
  rp_vector_constraint ctrs;  /* constraints             */
  rp_box b;                   /* initial box             */
  char * name;                /* problem name            */
  icp_solver * rp_icp_solver; /* dReal parent solver     */

  /* + non ordered covering, ordering managed by the search algorithms */
}
rp_problem_def;

typedef rp_problem_def * rp_problem;

#define rp_problem_symb(p)   (p)->symb
#define rp_problem_vars(p)   rp_table_symbol_vars((p)->symb)
#define rp_problem_nums(p)   rp_table_symbol_nums((p)->symb)
#define rp_problem_funcs(p)  rp_table_symbol_funcs((p)->symb)
#define rp_problem_ctrs(p)   (p)->ctrs
#define rp_problem_box(p)    (p)->b
#define rp_problem_name(p)   (p)->name

#define rp_problem_var(p,i) ((rp_variable)rp_vector_elem(rp_problem_vars(p),i))
#define rp_problem_nvar(p)  rp_vector_size(rp_problem_vars(p))
#define rp_problem_ctr(p,i) ((rp_constraint)rp_vector_elem(rp_problem_ctrs(p),i))
#define rp_problem_nctr(p)  rp_vector_size(rp_problem_ctrs(p))

/* Creation of a problem */
void rp_problem_create (rp_problem * p, const char * name);

/* Destruction of a problem */
void rp_problem_destroy (rp_problem * p);

/* name of p := name*/
void rp_problem_set_name (rp_problem p, char * name);

/* Creation of the initial box from the variable domains */
/* Returns false if the box is empty                     */
int rp_problem_set_initial_box (rp_problem p);

/* Display p on out */
void rp_problem_display(FILE * out, rp_problem p);

#ifdef __cplusplus
}
#endif

#endif /* RP_PROBLEM_H */
