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
 * rp_parser.h                                                              *
 ****************************************************************************/

#ifndef RP_PARSER
#define RP_PARSER 1

#ifdef __cplusplus
extern "C" {
#endif

#include <stdio.h>
#include <stdlib.h>
#include "rp_config.h"
#include "rp_memory.h"
#include "rp_lexer.h"
#include "rp_interval.h"
#include "rp_constant.h"
#include "rp_variable.h"
#include "rp_expression.h"
#include "rp_constraint.h"
#include "rp_problem.h"

/* --------------- */
/* The parser type */
/* --------------- */

#define RP_PARSER_ERRLEN 255

typedef struct
{
  rp_lexer lex;                 /* associated lexer to get tokens */
  rp_table_symbol symb;         /* table of symbols               */
  char msge[RP_PARSER_ERRLEN];  /* error message                  */
  rp_vector_variable lvars;     /* context: local variables       */
}
rp_parser_def;

typedef rp_parser_def rp_parser[1];

#define rp_parser_error_msg(p)  (p)[0].msge
#define rp_parser_lexer(p)      (p)[0].lex
#define rp_parser_symb(p)       (p)[0].symb
#define rp_parser_nums(p)       (p)[0].symb->nums
#define rp_parser_funcs(p)      (p)[0].symb->funcs
#define rp_parser_vars(p)       (p)[0].symb->vars
#define rp_parser_locvars(p)    (p)[0].lvars

/* Creation of a parser from a string */
int rp_parser_create_string (rp_parser * p,
			     char * src,
			     rp_table_symbol ts);

/* Creation of a parser from a file */
int rp_parser_create_file (rp_parser * p,
			   char * filename,
			   rp_table_symbol ts);

/* Destruction of a parser */
void rp_parser_destroy (rp_parser * p);

/* ------------------------ */
/* Grammar production rules */
/* ------------------------ */

/* variables */
int rp_rule_variable      (rp_parser p, rp_variable * out);
int rp_rule_vartype       (rp_parser p, int * is_int, double * prec,
			   int * absolute);
int rp_rule_domain        (rp_parser p, rp_union_interval u);
int rp_rule_first_domain  (rp_parser p, rp_union_interval u);
int rp_rule_interval      (rp_parser p, rp_interval i);
int rp_rule_domain_values (rp_parser p, rp_union_interval u);

/* expressions */
int rp_rule_expr            (rp_parser p, rp_erep * out);
int rp_rule_expr_aux        (rp_parser p, rp_erep * out, rp_erep left);
int rp_rule_term            (rp_parser p, rp_erep * out);
int rp_rule_term_aux        (rp_parser p, rp_erep * out, rp_erep left);
int rp_rule_fact            (rp_parser p, rp_erep * out);
int rp_rule_fact_aux        (rp_parser p, rp_erep * out, rp_erep unit);
int rp_rule_unit            (rp_parser p, rp_erep * out);
int rp_rule_unit_unary      (rp_parser p, rp_erep * out, int symbol);
int rp_rule_unit_binary     (rp_parser p, rp_erep * out, int symbol);
int rp_rule_signed_number   (rp_parser p, rp_interval i);
int rp_rule_unsigned_number (rp_parser p, rp_interval i);

/* constants */
int rp_rule_constant      (rp_parser p, rp_constant * out);
int rp_rule_constant_expr (rp_parser p, rp_interval i);

/* functions */
int rp_rule_function_def       (rp_parser p, rp_function * out);
int rp_rule_function_def_args  (rp_parser p, rp_function out);
int rp_rule_function_call      (rp_parser p, rp_function f, rp_erep * out);
int rp_rule_function_call_iter (rp_parser p, rp_function f, int i, rp_erep * out);

/* constraints */
int rp_rule_constraint    (rp_parser p, rp_constraint * c);
int rp_rule_ctr_cond      (rp_parser p, rp_ctr_cond c, int guard);
int rp_rule_ctr_num       (rp_parser p, rp_ctr_num * c);
int rp_rule_ctr_piecewise (rp_parser p, rp_ctr_piecewise * c);

/* problems */
int rp_rule_problem                  (rp_parser p, rp_problem problem);
int rp_rule_problem_def              (rp_parser p, rp_problem problem);
int rp_rule_problem_next             (rp_parser p, rp_problem problem);
int rp_rule_problem_block            (rp_parser p, rp_problem problem);
int rp_rule_problem_variable_block   (rp_parser p, rp_problem problem);
int rp_rule_problem_variable_next    (rp_parser p, rp_problem problem);
int rp_rule_problem_constant_block   (rp_parser p, rp_problem problem);
int rp_rule_problem_constant_next    (rp_parser p, rp_problem problem);
int rp_rule_problem_function_block   (rp_parser p, rp_problem problem);
int rp_rule_problem_function_next    (rp_parser p, rp_problem problem);
int rp_rule_problem_constraint_block (rp_parser p, rp_problem problem);
int rp_rule_problem_constraint_next  (rp_parser p, rp_problem problem);
int rp_rule_solve_list_var           (rp_parser p, rp_problem problem);

/* ------------------------------------------------------ */
/* Parsers: expressions, constants, constraints, problems */
/* ------------------------------------------------------ */

/* Parsing of variable from a string, return false if failure */
/* If success, the variable is added in the array var         */
int rp_parse_variable_string (rp_variable * v,
			      char * src,
			      rp_table_symbol ts);

/* Parsing of variable from a file, return false if failure */
/* If success, the variable is added in the array var       */
int rp_parse_variable_file (rp_variable * v,
			    char * filename,
			    rp_table_symbol ts);

/* Parsing of expression from a string, return false if failure */
int rp_parse_expression_string (rp_expression * e,
				char * src,
				rp_table_symbol ts);

/* Parsing of expression from a file, return false if failure */
int rp_parse_expression_file (rp_expression * e,
			      char * filename,
			      rp_table_symbol ts);

/* Parsing of constant from a string, return false if failure */
/* If success, the constant is added in the array cst         */
int rp_parse_constant_string (rp_constant * out,
			      char * src,
			      rp_table_symbol ts);

/* Parsing of constant from a file, return false if failure */
/* If success, the constant is added in the array cst       */
int rp_parse_constant_file (rp_constant * out,
			    char * filename,
			    rp_table_symbol ts);

/* Parsing of constraint from a string, return false if failure */
int rp_parse_constraint_string (rp_constraint * c,
				char * src,
				rp_table_symbol ts);

/* Parsing of constraint from a file, return false if failure */
int rp_parse_constraint_file (rp_constraint * c,
			      char * filename,
			      rp_table_symbol ts);

/* Parsing of a problem from a file, return false if failure */
int rp_parse_problem_file (rp_problem * problem,
			   char * filename);

#ifdef __cplusplus
}
#endif

#endif /* RP_PARSER */
