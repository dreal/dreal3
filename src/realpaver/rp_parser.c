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
 * rp_parser.c                                                              *
 ****************************************************************************/

#include <string.h>
#include "rp_parser.h"
#include "rp_interval.h"
#include "rp_constant.h"
#include "rp_variable.h"
#include "rp_expression_symbol.h"

/* Creation of a parser from a string */
int rp_parser_create_string(rp_parser * p,
                            const char * src,
                            rp_table_symbol ts)
{
  if (!rp_lexer_create_string(&rp_parser_lexer(*p),src))
  {
    return( 0 );
  }
  else
  {
    rp_parser_symb(*p) = ts;
    rp_vector_variable_create(&rp_parser_locvars(*p));

    /* get the first token */
    rp_lexer_get_token(rp_parser_lexer(*p));

    return( 1 );
  }
}

/* Creation of a parser from a file */
int rp_parser_create_file(rp_parser * p,
                          const char * filename,
                          rp_table_symbol ts)
{
  if (!rp_lexer_create_file(&rp_parser_lexer(*p),filename))
  {
    return( 0 );
  }
  else
  {
    rp_parser_symb(*p) = ts;
    rp_vector_variable_create(&rp_parser_locvars(*p));

    /* get the first token */
    rp_lexer_get_token(rp_parser_lexer(*p));

    return( 1 );
  }
}

/* Destruction of a parser */
void rp_parser_destroy(rp_parser * p)
{
  rp_lexer_destroy(&rp_parser_lexer(*p));
  rp_vector_destroy(&rp_parser_locvars(*p));
}

/* Parse a problem from a file */
int rp_parse_problem_file(rp_problem * problem,
                          const char * filename)
{
  rp_parser p;
  int res;
  rp_problem_create(problem,NULL);
  if ((res = rp_parser_create_file(&p,filename,rp_problem_symb(*problem))))
  {
    if (!(res = rp_rule_problem(p,*problem)))
    {
      fprintf(stderr,rp_parser_error_msg(p));
      fprintf(stderr,"\n");
    }
    else
    {
      /* creation of initial box */
      res = rp_problem_set_initial_box(*problem);
    }
    rp_parser_destroy(&p);
  }
  if (!res)
  {
    rp_problem_destroy(problem);
  }
  return( res);
}

/* Parse a constraint from a string */
int rp_parse_constraint_string(rp_constraint * c,
                               const char * src,
                               rp_table_symbol ts)
{
  rp_parser p;
  int res;
  if ((res = rp_parser_create_string(&p,src,ts)))
  {
    if (!(res = rp_rule_constraint(p,c)))
    {
      fprintf(stderr,rp_parser_error_msg(p));
      fprintf(stderr,"\n");
    }
    rp_parser_destroy(&p);
  }
  return( res );
}

/* Parse a constraint from a file */
int rp_parse_constraint_file(rp_constraint * c,
                             const char * filename,
                             rp_table_symbol ts)
{
  rp_parser p;
  int res;
  if ((res = rp_parser_create_file(&p,filename,ts)))
  {
    if (!(res = rp_rule_constraint(p,c)))
    {
      fprintf(stderr,rp_parser_error_msg(p));
      fprintf(stderr,"\n");
    }
    rp_parser_destroy(&p);
  }
  return( res);
}

/* Parse a variable from a string */ //s: here you parse the variables...
int rp_parse_variable_string(rp_variable * v,
                             const char * src,
                             rp_table_symbol ts)
{
  rp_parser p;
  int res;
  if ((res = rp_parser_create_string(&p,src,ts)))
  {
    if (!(res = rp_rule_variable(p,v)))
    {
      fprintf(stderr,rp_parser_error_msg(p));
      fprintf(stderr,"\n");
    }
    rp_parser_destroy(&p);
  }
  return( res);
}

/* Parse a variable from a file */
int rp_parse_variable_file(rp_variable * v,
                           const char * filename,
                           rp_table_symbol ts)
{
  rp_parser p;
  int res;
  if ((res = rp_parser_create_file(&p,filename,ts)))
  {
    if (!(res = rp_rule_variable(p,v)))
    {
      fprintf(stderr,rp_parser_error_msg(p));
      fprintf(stderr,"\n");
    }
    rp_parser_destroy(&p);
  }
  return( res);
}

/* Parse a constant from a string */
int rp_parse_constant_string(rp_constant * out,
                             const char * src,
                             rp_table_symbol ts)
{
  rp_parser p;
  int res;
  if ((res = rp_parser_create_string(&p,src,ts)))
  {
    if (!(res = rp_rule_constant(p,out)))
    {
      fprintf(stderr,rp_parser_error_msg(p));
      fprintf(stderr,"\n");
    }
    rp_parser_destroy(&p);
  }
  return( res);
}

/* Parse a constant from a file */
int rp_parse_constant_file(rp_constant * out,
                           const char * filename,
                           rp_table_symbol ts)
{
  rp_parser p;
  int res;
  if ((res = rp_parser_create_file(&p,filename,ts)))
  {
    if (!(res = rp_rule_constant(p,out)))
    {
      fprintf(stderr,rp_parser_error_msg(p));
      fprintf(stderr,"\n");
    }
    rp_parser_destroy(&p);
  }
  return( res);
}

/* Parse an expression from a string */
int rp_parse_expression_string(rp_expression * e,
                               const char * src,
                               rp_table_symbol ts)
{
  rp_parser p;
  int res;
  if ((res = rp_parser_create_string(&p,src,ts)))
  {
    rp_erep out;
    rp_erep_create(&out);

    if ((res = rp_rule_expr(p,&out)))
    {
      /* the memory for out is managed by e */
      rp_expression_create(e,&out);
    }
    else
    {
      rp_erep_destroy(&out);
      fprintf(stderr,rp_parser_error_msg(p));
      fprintf(stderr,"\n");
    }
    rp_parser_destroy(&p);
  }
  return( res);
}

/* Parse an expression from a file */
int rp_parse_expression_file(rp_expression * e,
                             const char * filename,
                             rp_table_symbol ts)
{
  rp_parser p;
  int res;
  if ((res = rp_parser_create_file(&p,filename,ts)))
  {
    rp_erep out;
    rp_erep_create(&out);

    if ((res = rp_rule_expr(p,&out)))
    {
      /* the memory for out is managed by e */
       rp_expression_create(e,&out);
    }
    else
    {
      rp_erep_destroy(&out);
      fprintf(stderr,rp_parser_error_msg(p));
      fprintf(stderr,"\n");
    }
    rp_parser_destroy(&p);
  }
  return( res);
}

/* Stop the parser with an error */
void rp_parser_stop(rp_parser p, const char * msg)
{
  char tmp[RP_PARSER_ERRLEN];
  if (rp_lexer_token(rp_parser_lexer(p))==RP_TOKEN_ERROR)
  {
    /* lexical analysis error */
    strcpy(rp_parser_error_msg(p),rp_lexer_error_msg(rp_parser_lexer(p)));
  }
  else
  {
    /* parser error */
    strcpy(rp_parser_error_msg(p),"PARSE ERROR: ");

    /* Position in file or string */
    rp_stream_get_position(rp_lexer_input(rp_parser_lexer(p)),tmp);
    strcat(rp_parser_error_msg(p),tmp);

    /* Error message */
    strcat(rp_parser_error_msg(p),": ");
    strcat(rp_parser_error_msg(p),msg);
  }
}

/* Read a new token if token is equal to the current token */
int rp_parser_accept(rp_parser p, int token)
{
  if (token==rp_lexer_token(rp_parser_lexer(p)))
  {
    rp_lexer_get_token(rp_parser_lexer(p));
    return( 1 );
  }
  else
  {
    return( 0 );
  }
}

/* Read a new token if token is equal to the current token */
/* Otherwise parse error                                   */
int rp_parser_expect(rp_parser p, int token, const char * msg)
{
  if (rp_parser_accept(p,token))
  {
    return( 1 );
  }
  else
  {
    char tmp[RP_PARSER_ERRLEN];
    sprintf(tmp,"%s not found",msg);
    rp_parser_stop(p,tmp);
    return( 0 );
  }
}

/* ------------------------ */
/* Grammar production rules */
/* ------------------------ */

/* Variable grammar:

   variable        ::= IDENTIFIER vartype ~ domain
   vartype         ::= : numtype | null
   numtype         ::= INT | REAL realprec
   realprec        ::= / precision | null
   precision       ::= CONSTANT | unsigned_number
   domain          ::= first_domain next_domain
   next_domain     ::= # domain | null
   first_domain    ::= [ expr , expr ] | { values }
   values          ::= (CONSTANT | signed_number) next_values
   next_values     ::= , values | null

   The null type corresponds to the real type.
   A domain is processed as a union of intervals and values.
*/

int rp_rule_variable(rp_parser p, rp_variable * out)
{
  int res = 0;
  if (rp_parser_expect(p,RP_TOKEN_IDENT,"variable name"))
  {
    int index;
    if (rp_vector_variable_contains(rp_parser_vars(p),
                                    rp_lexer_prev_text(rp_parser_lexer(p)),
                                    &index)!=NULL)
    {
      /* already existing variable */
      rp_parser_stop(p,"already existing variable");
    }
    else
    {
      char name[255];
      int is_int, absolute;
      double prec;
      strcpy(name,rp_lexer_prev_text(rp_parser_lexer(p)));

      if (rp_rule_vartype(p,&is_int,&prec,&absolute))
      {
        if (rp_parser_expect(p,RP_TOKEN_TILDE,"variable domain"))
        {
          rp_union_interval u;
          rp_union_create(&u);
          if (rp_rule_domain(p,u))
          {
            rp_variable v;
            // int index;
            rp_interval maxlong;

            if (is_int)
            {
              /* Domain bounded by the long type */
              rp_interval_set(maxlong,-RP_MAX_LONG,RP_MAX_LONG);
              rp_union_inter(u,maxlong);
            }
            if (rp_union_empty(u))
            {
              rp_parser_stop(p,"integer domain out of bounds");
            }
            else
            {
              rp_variable_create(&v,name);
              //index = rp_vector_insert(rp_parser_vars(p),v);
              rp_vector_insert(rp_parser_vars(p),v);
              /* rp_variable_set_decision(v); */
              if (is_int)
              {
                rp_variable_set_integer(v);
              }
              else
              {
                rp_variable_set_real(v);
                rp_variable_precision(v) = prec;
                if (absolute)
                {
                  rp_variable_set_absolute_precision(v);
                }
                else
                {
                  rp_variable_set_relative_precision(v);
                }
              }
              rp_union_copy(rp_variable_domain(v),u);
              (*out) = v;
              res = 1;
            }
          }
          rp_union_destroy(&u);
        }
      }
    }
  }
  return( res );
}

/* variable domain */
int rp_rule_domain(rp_parser p, rp_union_interval u)
{
  int res = 0;
  if (rp_rule_first_domain(p,u))
  {
    /* another domain element */
    if (rp_parser_accept(p,RP_TOKEN_SHARP))
    {
      res = rp_rule_domain(p,u);
    }

    /* end of domain definition */
    else if (rp_union_empty(u))
    {
      rp_parser_stop(p,"empty domain");
    }

    else
    {
      res = 1;
    }
  }
  return( res );
}

int rp_rule_first_domain(rp_parser p, rp_union_interval u)
{
  int res = 0;
  rp_interval i;

  /* interval [expr, expr] */
  if (rp_parser_accept(p,RP_TOKEN_SQLBR))
  {
    if (rp_rule_interval(p,i))
    {
      rp_union_insert(u,i);
      res = 1;
    }
  }

  /* set of values {a1, a2, ...} */
  else if (rp_parser_accept(p,RP_TOKEN_SETLBR))
  {
    res = rp_rule_domain_values(p,u);
  }

  else
  {
    rp_parser_stop(p,"unknown symbol in domain definition");
  }
  return( res );
}

int rp_rule_interval(rp_parser p, rp_interval i)
{
  /* interval [expr, expr] such that '[' has been read */
  rp_interval left, right;
  int res = 0;
  if (rp_rule_constant_expr(p,left))
  {
    if (rp_parser_expect(p,RP_TOKEN_COMMA,"comma"))
    {
      if (rp_rule_constant_expr(p,right))
      {
        if (rp_parser_expect(p,RP_TOKEN_SQRBR,"]"))
        {
          rp_interval_set(i,rp_binf(left),rp_bsup(right));
          res = 1;
        }
      }
    }
  }
  return( res );
}

/* u := a1, a2, ...} */
int rp_rule_domain_values(rp_parser p, rp_union_interval u)
{
  rp_interval i;
  int res = 0;
  if (rp_rule_constant_expr(p,i))
  {
    rp_union_insert(u,i);
    if (rp_parser_accept(p,RP_TOKEN_COMMA))
    {
      res = rp_rule_domain_values(p,u);
    }
    else if (rp_parser_accept(p,RP_TOKEN_SETRBR))
    {
      res = 1;
    }
    else
    {
      rp_parser_stop(p,"} not found");
    }
  }
  return( res );
}

/* type and precision of variables */
int rp_rule_vartype(rp_parser p, int * is_int, double * prec, int * absolute)
{
  int res = 0;
  /* : */
  if (rp_parser_accept(p,RP_TOKEN_COLON))
  {
    /* integer variable */
    if (rp_parser_accept(p,RP_TOKEN_TYPE_INT))
    {
      (*is_int) = 1;
      res = 1;
    }

    /* real variable */
    else if (rp_parser_accept(p,RP_TOKEN_TYPE_REAL))
    {
      (*is_int) = 0;
      if (rp_parser_accept(p,RP_TOKEN_DIV))
      {
        rp_interval i;

        /* precision defined by a constant */
        if (rp_parser_accept(p,RP_TOKEN_IDENT))
        {
          rp_constant * c;
          int index;
          if ((c=rp_vector_constant_contains(
                      rp_parser_nums(p),
                      rp_lexer_prev_text(rp_parser_lexer(p)),
                      &index))!=NULL)
          {
            (*prec) = rp_binf(rp_constant_val(*c));
            res = 1;
          }
          else
          {
            rp_parser_stop(p,"constant identifier not found");
          }
        }
        else if (rp_rule_unsigned_number(p,i))
        {
          (*prec) = rp_binf(i);
          res = 1;
        }
        else
        {
          rp_parser_stop(p,"variable precision not found");
        }

        if (rp_parser_accept(p,RP_TOKEN_PERCENT))
        {
          (*absolute) = 0;  /* relative precision */
        }
        else
        {
          (*absolute) = 1;  /* absolute precision */
        }
      }
      else
      {
        /* default precision */
        (*prec) = 1.0e-8;
        res = 1;
      }
    }
    else
    {
      rp_parser_stop(p,"variable type not found");
    }
  }
  else
  {
    /* default: real variable at precision 10-8 */
    (*is_int) = 0;
    (*prec) = 1.0e-8;
    res = 1;
  }
  return( res );
}

/* Problem grammar:
   problem          ::= PROBLEM IDENT problem_def
   problem_def      ::= problem_block problem_next
   problem_next     ::= problem_def | END
   problem_block    ::= BLOCK_VAR variable_block |
                        BLOCK_NUM constant_block |
                        BLOCK_FUNC function_block
                        BLOCK_CTR constraint_block |
                        SOLVE solve_list_var
   variable_block   ::= variable variable_next
   variable_next    ::= , variable_block | epsilon
   constant_block   ::= constant constant_next
   constant_next    ::= , constant_block | epsilon
   function_block   ::= function function_next
   function_next    ::= , function_block | epsilon
   constraint_block ::= constraint constraint_next
   constraint_next  ::= , constraint_block | epsilon
   constraint       ::= constraint_num constraint_tail
   constraint_tail  ::= # constraint_cond | -> constraint_cond | epsilon

   ex: problem circle
         num p  := 1.0e-8,
             D  := 2.75,
             x0 := 2,
             y0 := 1,
             R  := 1.25;

         var x : real / p ~ [-oo,+oo],
             y : real / p ~ [-oo,+oo];

         ctr (x-x0)^2 + (y-y0)^2 = R^2,
             x^2 + y^2 = D^2;
       end
 */
int rp_rule_problem(rp_parser p, rp_problem problem)
{
  int result = 0;
  if (rp_parser_expect(p,RP_TOKEN_PROBLEM,"problem definition"))
  {
    if (rp_parser_expect(p,RP_TOKEN_IDENT,"problem name"))
    {
      rp_problem_set_name(problem,rp_lexer_prev_text(rp_parser_lexer(p)));
      result = rp_rule_problem_def(p,problem);
    }
  }
  return( result );
}

int rp_rule_problem_def(rp_parser p, rp_problem problem)
{
  if (rp_rule_problem_block(p,problem))
  {
    return( rp_rule_problem_next(p,problem) );
  }
  else
  {
    return( 0 );
  }
}

int rp_rule_problem_next(rp_parser p, rp_problem problem)
{
  if (rp_parser_accept(p,RP_TOKEN_END))
  {
    return( 1 );
  }
  else
  {
    return( rp_rule_problem_def(p,problem) );
  }
}

int rp_rule_problem_block(rp_parser p, rp_problem problem)
{
  int result = 0;
  if (rp_parser_accept(p,RP_TOKEN_BLOCK_VAR))
  {
    result = rp_rule_problem_variable_block(p,problem);
  }
  else if (rp_parser_accept(p,RP_TOKEN_BLOCK_NUM))
  {
    result = rp_rule_problem_constant_block(p,problem);
  }
  else if (rp_parser_accept(p,RP_TOKEN_BLOCK_FUNC))
  {
    result = rp_rule_problem_function_block(p,problem);
  }
  else if (rp_parser_accept(p,RP_TOKEN_BLOCK_CTR))
  {
    result = rp_rule_problem_constraint_block(p,problem);
  }
  else if (rp_parser_accept(p,RP_TOKEN_SOLVE))
  {
    result = rp_rule_solve_list_var(p,problem);
  }
  else
  {
    rp_parser_stop(p,"erroneous block or block absent");
  }
  return( result );
}

int rp_rule_solve_list_var(rp_parser p, rp_problem problem)
{
  int result = 1;
  if (rp_parser_accept(p,RP_TOKEN_MUL))
  {
    /* every variable is a decision variable */
    int i;
    for (i=0; i<rp_problem_nvar(problem); ++i)
    {
      rp_variable_set_decision(rp_problem_var(p,i));
    }
  }
  else
  {
    /* list of variables */
    rp_variable * v;
    int iter = 1, index;
    do
    {
      if (rp_parser_expect(p,RP_TOKEN_IDENT,"variable name"))
      {
        if ((v=rp_vector_variable_contains(rp_parser_vars(p),
                                           rp_lexer_prev_text(rp_parser_lexer(p)),
                                           &index))!=NULL)
        {
          rp_variable_set_decision(*v);

          if (!rp_parser_accept(p,RP_TOKEN_COMMA))
          {
            iter = 0;
          }
        }
        else
        {
          rp_parser_stop(p,"variable not defined");
          iter = result = 0;
        }
      }
      else /* variable name not found */
      {
        iter = result = 0;
      }
    } while (iter);
  }

  if (result)
  {
    if (!rp_parser_accept(p,RP_TOKEN_SEMICOLON))
    {
      rp_parser_stop(p,"erroneous end of solve definition");
      result = 0;
    }
  }
  return( result );
}

int rp_rule_problem_variable_block(rp_parser p, rp_problem problem)
{
  rp_variable aux;
  if (rp_rule_variable(p,&aux))
  {
    return( rp_rule_problem_variable_next(p,problem) );
        //s: note that the parsing is done recursively.
  }
  else
  {
    return( 0 );
  }
}

int rp_rule_problem_variable_next(rp_parser p, rp_problem problem)
{
  if (rp_parser_accept(p,RP_TOKEN_COMMA))
  {
    return( rp_rule_problem_variable_block(p,problem) );
  }
  else if (rp_parser_accept(p,RP_TOKEN_SEMICOLON))
  {
    return( 1 );
  }
  else if (rp_parser_accept(p,RP_TOKEN_END))
  {
    return( 1 );
  }
  else
  {
    rp_parser_stop(p,"erroneous end of variable block");
    return( 0 );
  }
}

int rp_rule_problem_constant_block(rp_parser p, rp_problem problem)
{
  rp_constant aux;
  if (rp_rule_constant(p,&aux))
  {
    return( rp_rule_problem_constant_next(p,problem) );
  }
  else
  {
    return( 0 );
  }
}

int rp_rule_problem_constant_next(rp_parser p, rp_problem problem)
{
  if (rp_parser_accept(p,RP_TOKEN_COMMA))
  {
    return( rp_rule_problem_constant_block(p,problem) );
  }
  else if (rp_parser_accept(p,RP_TOKEN_SEMICOLON))
  {
    return( 1 );
  }
  else if (rp_parser_accept(p,RP_TOKEN_END))
  {
    return( 1 );
  }
  else
  {
    rp_parser_stop(p,"erroneous end of constant block");
    return( 0 );
  }
}

int rp_rule_problem_function_block(rp_parser p, rp_problem problem)
{
  rp_function aux;
  if (rp_rule_function_def(p,&aux))
  {
    return( rp_rule_problem_function_next(p,problem) );
  }
  else
  {
    return( 0 );
  }
}

int rp_rule_problem_function_next(rp_parser p, rp_problem problem)
{
  if (rp_parser_accept(p,RP_TOKEN_COMMA))
  {
    return( rp_rule_problem_function_block(p,problem) );
  }
  else if (rp_parser_accept(p,RP_TOKEN_SEMICOLON))
  {
    return( 1 );
  }
  else if (rp_parser_accept(p,RP_TOKEN_END))
  {
    return( 1 );
  }
  else
  {
    rp_parser_stop(p,"erroneous end of function block");
    return( 0 );
  }
}

int rp_rule_function_def(rp_parser p, rp_function * /*out*/)
{
  int res = 0, index;
  if (rp_parser_expect(p,RP_TOKEN_IDENT,"function name"))
  {
    if (rp_vector_function_contains(rp_parser_funcs(p),
                                    rp_lexer_prev_text(rp_parser_lexer(p)),
                                    &index)!=NULL)
    {
      /* already existing function */
      rp_parser_stop(p,"already existing function");
    }
    else
    {
      rp_function f;
      rp_function_create(&f,rp_lexer_prev_text(rp_parser_lexer(p)));
      //out = &f;

      /* arguments (x1,...,xn) */
      if (rp_parser_expect(p,RP_TOKEN_LBR,"("))
      {
        if (rp_rule_function_def_args(p,f))
        {
          /* := */
          if (rp_parser_expect(p,RP_TOKEN_SETVALUE,":="))
          {
            /* tree-representation */
            rp_erep e;

            /* set context of local variables */
            rp_vector_variable vsave = rp_parser_locvars(p);
            rp_parser_locvars(p) = rp_function_lvars(f);

            if (rp_rule_expr(p,&e))
            {
              rp_function_insert_expr(f,e);
              rp_vector_insert(rp_parser_funcs(p),f);
              res = 1;
            }

            /* restore context */
            rp_parser_locvars(p) = vsave;
          }
        }
      }
      if (!res) rp_function_destroy(&f);
    }
  }
  return( res );
}

int rp_rule_function_def_args(rp_parser p, rp_function out)
{
  int res = 0;
  if (rp_parser_expect(p,RP_TOKEN_IDENT,"variable name"))
  {
    rp_function_insert_var(out,rp_lexer_prev_text(rp_parser_lexer(p)));
    if (rp_parser_accept(p,RP_TOKEN_COMMA))
    {
      res = rp_rule_function_def_args(p,out);
    }
    else if (rp_parser_accept(p,RP_TOKEN_RBR))
    {
      res = 1;
    }
    else
    {
      rp_parser_stop(p,"comma or end of arguments list expected");
    }
  }
  return( res );
}

int rp_rule_problem_constraint_block(rp_parser p, rp_problem problem)
{
  rp_constraint aux;
  int i;
  if (rp_rule_constraint(p,&aux))
  {
    rp_vector_insert(rp_problem_ctrs(problem),aux);

    /* creation of relation var -> number of constraints containing var */
    for (i=0; i<rp_constraint_arity(aux); ++i)
    {
      ++rp_variable_constrained(rp_problem_var(problem,rp_constraint_var(aux,i)));
    }

    /* tail of the block */
    return( rp_rule_problem_constraint_next(p,problem) );
  }
  else
  {
    return( 0 );
  }
}

int rp_rule_problem_constraint_next(rp_parser p, rp_problem problem)
{
  if (rp_parser_accept(p,RP_TOKEN_COMMA))
  {
    return( rp_rule_problem_constraint_block(p,problem) );
  }
  else if (rp_parser_accept(p,RP_TOKEN_SEMICOLON))
  {
    return( 1 );
  }
  else if (rp_parser_accept(p,RP_TOKEN_END))
  {
    return( 1 );
  }
  else
  {
    rp_parser_stop(p,"erroneous end of constraint block");
    return( 0 );
  }
}

/* constraint */
int rp_rule_constraint(rp_parser p, rp_constraint * c)
{
  rp_ctr_num cnum;
  rp_ctr_piecewise piece;
  int result = 0;

  /* piecewise constraint */
  if (rp_parser_accept(p,RP_TOKEN_PIECEWISE))
  {
    if (rp_rule_ctr_piecewise(p,&piece))
    {
      /* intersection of the initial domain of the main variable */
      /* and the set of pieces of the given constraint           */
      int index = rp_ctr_piecewise_var(piece);
      rp_variable v = ((rp_variable)rp_vector_elem(rp_parser_vars(p),index));

      if (rp_union_inter_uu(rp_variable_domain(v),rp_ctr_piecewise_guard(piece)))
      {
        /* creation of the new constraint */
        rp_constraint_create_piece(c,piece);
        result = 1;
      }
      else
      {
        rp_ctr_piecewise_destroy(&piece);
        rp_parser_stop(p,"no piece intersects with the variable domain");
      }
    }
  }

  /* numerical or conditional constraint */
  else if (rp_rule_ctr_num(p,&cnum))
  {
    int guard = 0, conc = 0;
    if (rp_parser_accept(p,RP_TOKEN_SHARP))
    {
      guard = 1;
    }
    else if (rp_parser_accept(p,RP_TOKEN_IMPLY))
    {
      conc = 1;
    }

    if (guard || conc)
    {
      rp_ctr_cond cond;
      rp_ctr_cond_create(&cond);
      rp_ctr_cond_insert_guard(cond,cnum);
      if (rp_rule_ctr_cond(p,cond,guard))
      {
        rp_constraint_create_cond(c,cond);
        result = 1;
      }
      else
      {
        rp_ctr_cond_destroy(&cond);
      }
    }
    else
    {
      rp_constraint_create_num(c,cnum);
      result = 1;
    }
  }
  return( result );
}

/* piecewise constraint ( x , I1:C1, ..., Ik:Ck ) */
int rp_rule_ctr_piecewise(rp_parser p, rp_ctr_piecewise * c)
{
  int result = 0, index, iter;
  rp_interval itv;

  /* open bracket */
  if (!rp_parser_expect(p,RP_TOKEN_LBR,"("))
  {
    return( result );
  }

  /* the main variable */
  if (!rp_parser_expect(p,RP_TOKEN_IDENT,
                        "main variable in piecewise constraint not found"))
  {
    return( result );
  }
  if (rp_vector_variable_contains(rp_parser_vars(p),
                                  rp_lexer_prev_text(rp_parser_lexer(p)),
                                  &index)==NULL)
  {
    rp_parser_stop(p,"main variable of piecewise constraint not defined");
    return( result );
  }

  rp_ctr_piecewise_create(c,index);

  iter = 1;
  do
  {
    if (rp_parser_accept(p,RP_TOKEN_COMMA))
    {
      /* Ij : Cj */

      if (!rp_parser_expect(p,RP_TOKEN_SQLBR,"square bracket"))
      {
        iter = 0;
      }
      else if ((!rp_rule_interval(p,itv)))
      {
        iter = 0;
      }
      else
      {
        if (!rp_ctr_piecewise_insert_domain(*c,itv))
        {
          rp_parser_stop(p,"intersection of pieces having non zero width");
          iter = 0;
        }
        else if (!rp_parser_expect(p,RP_TOKEN_COLON,"colon"))
        {
          iter = 0;
        }
        else
        {
          /* list c1 # ... # cj */
          int listiter = 1;
          do
          {
            rp_ctr_num cnum;
            /* next constraint, at least one */
            if (rp_rule_ctr_num(p,&cnum))
            {
              rp_ctr_piecewise_insert_constraint(*c,cnum);
              if (!rp_parser_accept(p,RP_TOKEN_SHARP))
              {
                listiter = 0;
              }
            }
            else
            {
              listiter = 0;
            }
          }
          while (listiter);
        }
      }
    }
    else if (rp_parser_accept(p,RP_TOKEN_RBR))
    {
      iter = 0;
      result = 1;
    }
    else
    {
      char tmp[RP_PARSER_ERRLEN];
      sprintf(tmp,"unknown symbol: %s",rp_lexer_prev_text(rp_parser_lexer(p)));
      rp_parser_stop(p,tmp);
      iter = 0;
    }
  } while (iter);

  if (!result )
  {
    rp_ctr_piecewise_destroy(c);
  }
  return( result );
}


/* tail of conditional constraint */
int rp_rule_ctr_cond(rp_parser p, rp_ctr_cond c, int guard)
{
  rp_ctr_num cnum;
  int result = 0;

  /* next constraint */
  if (rp_rule_ctr_num(p,&cnum))
  {
    /* insertion of this constraint */
    if (guard)
    {
      rp_ctr_cond_insert_guard(c,cnum);
    }
    else
    {
      rp_ctr_cond_insert_conc(c,cnum);
    }

    /* tail of conditional constraint */
    if (rp_parser_accept(p,RP_TOKEN_SHARP))
    {
      result = rp_rule_ctr_cond(p,c,guard);
    }
    else if (rp_parser_accept(p,RP_TOKEN_IMPLY))
    {
      if (guard)
      {
        result = rp_rule_ctr_cond(p,c,0);
      }
      else
      {
        rp_parser_stop(p,"second implication not allowed");
        result = 0;
      }
    }
    else if (guard)
    {
      rp_parser_stop(p,"no conclusion found in conditional constraint");
      result = 0;
    }
    else
    {
      result = 1;
    }
  }
  return( result );
}

/* numerical constraint expr rel expr */
int rp_rule_ctr_num(rp_parser p, rp_ctr_num * c)
{
  rp_erep left, right;
  int rel;
  int res = 0, isrel = 0;

  if (rp_rule_expr(p,&left))
  {
    /* equation */
    if (rp_parser_accept(p,RP_TOKEN_EQUAL))
    {
      rel = RP_RELATION_EQUAL;
      isrel = 1;
    }

    /* inequality >= */
    else if (rp_parser_accept(p,RP_TOKEN_SUPEQUAL))
    {
      rel = RP_RELATION_SUPEQUAL;
      isrel = 1;
    }

    /* inequality <= */
    else if (rp_parser_accept(p,RP_TOKEN_INFEQUAL))
    {
      rel = RP_RELATION_INFEQUAL;
      isrel = 1;
    }

    /* no relation symbol */
    else
    {
      rp_parser_stop(p,"relation symbol not found");
    }

    if (isrel)
    {
      if (rp_rule_expr(p,&right))
      {
        rp_ctr_num_create(c,&left,rel,&right);


        res = 1;
        /*

        if (rp_expression_arity(rp_ctr_num_func(*c))==0)
        {
          rp_parser_stop(p,"constraint having no variable");
          rp_ctr_num_destroy(c);
        }
        else
        {
          res = 1;
        }

        */
      }
    }

    if (!res)
    {
      rp_erep_destroy(&left);
    }
  }
  return( res );
}

/* constants <name := constant expression> */
int rp_rule_constant(rp_parser p, rp_constant * out)
{
  int res = 0, index;
  if (rp_parser_expect(p,RP_TOKEN_IDENT,"constant name"))
  {
    if (rp_vector_constant_contains(rp_parser_nums(p),
                                    rp_lexer_prev_text(rp_parser_lexer(p)),
                                    &index)!=NULL)
    {
      /* already existing constant */
      rp_parser_stop(p,"already existing constant");
    }
    else
    {
      char name[255];
      strcpy(name,rp_lexer_prev_text(rp_parser_lexer(p)));
      if (rp_parser_expect(p,RP_TOKEN_SETVALUE,":="))
      {
        rp_interval i;
        if (rp_rule_constant_expr(p,i))
        {
          rp_constant c;
          // int index;
          rp_constant_create(&c,name,i);
          // index = rp_vector_insert(rp_parser_nums(p),c);
          rp_vector_insert(rp_parser_nums(p),c);
          (*out) = c;

          res = 1;
        }
      }
    }
  }
  return( res );
}

/* i := evaluation of constant expression */
int rp_rule_constant_expr(rp_parser p, rp_interval i)
{
  rp_erep f;
  int res = 0;
  if (rp_rule_expr(p,&f))
  {
    /* evaluation of f */
    if (rp_erep_is_constant(f))
    {
      rp_box b = NULL;  /* useless */
      if (rp_erep_eval(f,b))
      {
        rp_interval_copy(i,rp_erep_val(f));
        res = 1;
      }
      else
      {
        rp_parser_stop(p,"empty evaluation of constant expression");
      }
    }
    else
    {
      rp_parser_stop(p,"non constant expression");
    }
    rp_erep_destroy(&f);
  }
  return( res );
}

/* Expression grammar:

   expr ::= expr+expr | expr-expr | expr*expr | expr/expr | expr^NUMBER |
            sqrt(expr) | log(expr) | ... |
            +expr | -expr | (expr) | NUMBER | IDENTIFIER

   New grammar considering that operations are left associative and
   given the precedence (+,-) < (*,/) < (^):

   expr ::= expr+term | expr-term | term
   term ::= term*fact | term/fact | fact
   fact ::= unit^NUMBER | unit
   unit ::= sqrt(expr) | log(expr) | ... |
            +unit | -unit | (expr) | NUMBER | IDENTIFIER

   New grammar after eliminating the left recursivity in order
   to implement a recursive descent parser:

   expr     ::= term expr_aux
   expr_aux ::= + term expr_aux | - term expr_aux | epsilon
   term     ::= fact term_aux
   term_aux ::= * fact term_aux | / fact term_aux | epsilon
   fact     ::= unit fact_aux
   fact_aux ::= ^ NUMBER | epsilon
   unit     ::= sqrt(expr) | log(expr) | ... |
                +unit | -unit | (expr) | NUMBER | IDENTIFIER
*/

/* expr ::= term expr_aux */
int rp_rule_expr(rp_parser p, rp_erep * out)
{
  int res;
  rp_erep term_out;
  rp_erep_create(&term_out);

  /* term */
  if ((res = rp_rule_term(p,&term_out)))
  {
    /* expr_aux */
    res = rp_rule_expr_aux(p,out,term_out);
  }
  else
  {
    res = 0;
  }
  rp_erep_destroy(&term_out);
  return( res );
}

/* expr_aux ::= + term expr_aux | - term expr_aux | epsilon */
int rp_rule_expr_aux(rp_parser p, rp_erep * out, rp_erep left)
{
  /* + */
  if (rp_parser_accept(p,RP_TOKEN_PLUS))
  {
    /* right-hand term */
    int res;
    rp_erep right;
    rp_erep_create(&right);
    if ((res = rp_rule_term(p,&right)))
    {
      /* expr_aux */
      rp_erep plus_l_r;
      rp_erep_create_binary(&plus_l_r,RP_SYMBOL_ADD,left,right);
      res = rp_rule_expr_aux(p,out,plus_l_r);
      rp_erep_destroy(&plus_l_r);
    }
    rp_erep_destroy(&right);
    return( res );
  }
  /* - */
  else if (rp_parser_accept(p,RP_TOKEN_MINUS))
  {
    /* right-hand term */
    int res;
    rp_erep right;
    rp_erep_create(&right);
    if ((res = rp_rule_term(p,&right)))
    {
      /* expr_aux */
      rp_erep sub_l_r;
      rp_erep_create_binary(&sub_l_r,RP_SYMBOL_SUB,left,right);
      res = rp_rule_expr_aux(p,out,sub_l_r);
      rp_erep_destroy(&sub_l_r);
    }
    rp_erep_destroy(&right);
    return( res );
  }
  else
  {
    /* epsilon */
    rp_erep_set(out,left);
    return( 1 );
  }
}

/* term ::= fact term_aux */
int rp_rule_term(rp_parser p, rp_erep * out)
{
  int res;
  rp_erep fact_out;
  rp_erep_create(&fact_out);

  /* fact */
  if ((res = rp_rule_fact(p,&fact_out)))
  {
    /* term_aux */
    res = rp_rule_term_aux(p,out,fact_out);
  }
  else
  {
    res = 0;
  }
  rp_erep_destroy(&fact_out);
  return( res );
}

/* term_aux ::= * fact term_aux | / fact term_aux | epsilon */
int rp_rule_term_aux(rp_parser p, rp_erep * out, rp_erep left)
{
  /* * */
  if (rp_parser_accept(p,RP_TOKEN_MUL))
  {
    /* right-hand fact */
    int res;
    rp_erep right;
    rp_erep_create(&right);
    if ((res = rp_rule_fact(p,&right)))
    {
      /* term_aux */
      rp_erep mul_l_r;
      rp_erep_create_binary(&mul_l_r,RP_SYMBOL_MUL,left,right);
      res = rp_rule_term_aux(p,out,mul_l_r);
      rp_erep_destroy(&mul_l_r);
    }
    rp_erep_destroy(&right);
    return( res );
  }
  /* / */
  else if (rp_parser_accept(p,RP_TOKEN_DIV))
  {
    /* right-hand fact */
    int res;
    rp_erep right;
    rp_erep_create(&right);
    if ((res = rp_rule_fact(p,&right)))
    {
      /* term_aux */
      rp_erep div_l_r;
      rp_erep_create_binary(&div_l_r,RP_SYMBOL_DIV,left,right);
      res = rp_rule_term_aux(p,out,div_l_r);
      rp_erep_destroy(&div_l_r);
    }
    rp_erep_destroy(&right);
    return( res );
  }
  else
  {
    /* epsilon */
    rp_erep_set(out,left);
    return( 1 );
  }
}

/* fact ::= unit fact_aux */
int rp_rule_fact(rp_parser p, rp_erep * out)
{
  int res;
  rp_erep unit_out;
  rp_erep_create(&unit_out);

  /* unit */
  if ((res = rp_rule_unit(p,&unit_out)))
  {
    /* fact_aux */
    res = rp_rule_fact_aux(p,out,unit_out);
  }
  else
  {
    res = 0;
  }
  rp_erep_destroy(&unit_out);
  return( res );
}

/* fact_aux ::= ^ NUMBER | epsilon */
int rp_rule_fact_aux(rp_parser p, rp_erep * out, rp_erep unit)
{
  int res = 0;
  /* ^ */
  if (rp_parser_accept(p,RP_TOKEN_POW))
  {
    rp_erep exponent;
    if (rp_rule_unit(p,&exponent))
    {
      long sign, num, den;
      if (rp_erep_is_rational(exponent,&sign,&num,&den))
      {
        if (den==0)
        {
          rp_parser_stop(p,"division by zero");
        }

        /* exponent is integer */
        else if (den==1)
        {
          res = 1;

          /* positive integer => f^n */
          if (sign==1)
          {
            rp_erep exp;
            rp_interval i;
            rp_interval_set_point(i,num);
            rp_erep_create_cst(&exp,"",i);
            rp_erep_create_binary(out,RP_SYMBOL_POW,unit,exp);
            rp_erep_destroy(&exp);
          }

          /* negative integer => 1/f^n*/
          else
          {
            rp_erep exp, aux, one;
            rp_interval i;
            rp_interval_set_point(i,num);
            rp_erep_create_cst(&exp,"",i);
            rp_interval_set_point(i,1.0);
            rp_erep_create_cst(&one,"",i);
            rp_erep_create_binary(&aux,RP_SYMBOL_POW,unit,exp);
            rp_erep_create_binary(out,RP_SYMBOL_DIV,one,aux);
            rp_erep_destroy(&exp);
            rp_erep_destroy(&one);
            rp_erep_destroy(&aux);
          }
        }

        /* general case */
        else
        {
          rp_erep log_unit, mul_exp_log;
          rp_erep_create_unary(&log_unit,RP_SYMBOL_LOG,unit);
          rp_erep_create_binary(&mul_exp_log,RP_SYMBOL_MUL,exponent,log_unit);
          rp_erep_create_unary(out,RP_SYMBOL_EXP,mul_exp_log);
          rp_erep_destroy(&log_unit);
          rp_erep_destroy(&mul_exp_log);
          res = 1;
        }
      }

      /* general case: f^exponent <=> exp(exponent * log(f)) */
      else
      {
        rp_erep log_unit, mul_exp_log;
        rp_erep_create_unary(&log_unit,RP_SYMBOL_LOG,unit);
        rp_erep_create_binary(&mul_exp_log,RP_SYMBOL_MUL,exponent,log_unit);
        rp_erep_create_unary(out,RP_SYMBOL_EXP,mul_exp_log);
        rp_erep_destroy(&log_unit);
        rp_erep_destroy(&mul_exp_log);
        res = 1;
      }
      rp_erep_destroy(&exponent);
    }
  }
  else
  {
    /* epsilon */
    rp_erep_set(out,unit);
    res = 1;
  }
  return( res );
}

/* unit ::= sqrt(expr) | log(expr) | sin(expr) | ... |   */
/*          +unit | -unit | (expr) | NUMBER | IDENTIFIER */
int rp_rule_unit(rp_parser p, rp_erep * out)
{
  /* unsigned number */
  rp_interval i;
  if (rp_rule_unsigned_number(p,i))
  {
    rp_erep_create_cst(out,"",i);
    return( 1 );
  }

  /* identifier */
  else if (rp_parser_accept(p,RP_TOKEN_IDENT))
  {
    rp_constant * c;
    rp_variable * v;
    rp_function * f;
    int index;

    if ((v=rp_vector_variable_contains(
                  rp_parser_locvars(p),
                  rp_lexer_prev_text(rp_parser_lexer(p)),
                  &index))!=NULL)
    {
      /* local variable */
      rp_erep_create_var(out,rp_function_local_var(index));
      return( 1 );
    }
    else if ((c=rp_vector_constant_contains(
                  rp_parser_nums(p),
                  rp_lexer_prev_text(rp_parser_lexer(p)),
                  &index))!=NULL)
    {
      /* constant */
      rp_erep_create_cst(out,rp_constant_name(*c),rp_constant_val(*c));
      return( 1 );
    }
    else if ((f=rp_vector_function_contains(
                  rp_parser_funcs(p),
                  rp_lexer_prev_text(rp_parser_lexer(p)),
                  &index))!=NULL)
    {
      /* function */
      return( rp_rule_function_call(p,*f,out) );
    }
    else if ((v=rp_vector_variable_contains(
                  rp_parser_vars(p),
                  rp_lexer_prev_text(rp_parser_lexer(p)),
                  &index))!=NULL)
    {
      /* variable */
      rp_erep_create_var(out,index);
      return( 1 );
    }
    else
    {
      char tmp[RP_PARSER_ERRLEN];
      sprintf(tmp,"unknown symbol: %s",rp_lexer_prev_text(rp_parser_lexer(p)));
      rp_parser_stop(p,tmp);
      return( 0 );
    }
  }

  /* - term */
  else if (rp_parser_accept(p,RP_TOKEN_MINUS))
  {
    int res;
    rp_erep child;
    rp_erep_create(&child);
    if ((res = rp_rule_term(p,&child)))
    {
      rp_erep_create_unary(out,RP_SYMBOL_NEG,child);
      res = 1;
    }
    rp_erep_destroy(&child);
    return( res );
  }

  /* + term */
  else if (rp_parser_accept(p,RP_TOKEN_PLUS))
  {
    return( rp_rule_term(p,out) );
  }

  /* sqrt( expr ) */
  else if (rp_parser_accept(p,RP_TOKEN_SQRT))
  {
    return( rp_rule_unit_unary(p,out,RP_SYMBOL_SQRT) );
  }

  /* exp( expr ) */
  else if (rp_parser_accept(p,RP_TOKEN_EXP))
  {
    return( rp_rule_unit_unary(p,out,RP_SYMBOL_EXP) );
  }

  /* log( expr ) */
  else if (rp_parser_accept(p,RP_TOKEN_LOG))
  {
    return( rp_rule_unit_unary(p,out,RP_SYMBOL_LOG) );
  }

  /* sin( expr ) */
  else if (rp_parser_accept(p,RP_TOKEN_SIN))
  {
    return( rp_rule_unit_unary(p,out,RP_SYMBOL_SIN) );
  }

  /* cos( expr ) */
  else if (rp_parser_accept(p,RP_TOKEN_COS))
  {
    return( rp_rule_unit_unary(p,out,RP_SYMBOL_COS) );
  }

  /* tan( expr ) */
  else if (rp_parser_accept(p,RP_TOKEN_TAN))
  {
    return( rp_rule_unit_unary(p,out,RP_SYMBOL_TAN) );
  }

  /* cosh( expr ) */
  else if (rp_parser_accept(p,RP_TOKEN_COSH))
  {
    return( rp_rule_unit_unary(p,out,RP_SYMBOL_COSH) );
  }

  /* sinh( expr ) */
  else if (rp_parser_accept(p,RP_TOKEN_SINH))
  {
    return( rp_rule_unit_unary(p,out,RP_SYMBOL_SINH) );
  }

  /* tanh( expr ) */
  else if (rp_parser_accept(p,RP_TOKEN_TANH))
  {
    return( rp_rule_unit_unary(p,out,RP_SYMBOL_TANH) );
  }

  /* asin( expr ) */
  else if (rp_parser_accept(p,RP_TOKEN_ASIN))
  {
    return( rp_rule_unit_unary(p,out,RP_SYMBOL_ASIN) );
  }

  /* acos( expr ) */
  else if (rp_parser_accept(p,RP_TOKEN_ACOS))
  {
    return( rp_rule_unit_unary(p,out,RP_SYMBOL_ACOS) );
  }

  /* atan( expr ) */
  else if (rp_parser_accept(p,RP_TOKEN_ATAN))
  {
    return( rp_rule_unit_unary(p,out,RP_SYMBOL_ATAN) );
  }

  /* asinh( expr ) */
  else if (rp_parser_accept(p,RP_TOKEN_ASINH))
  {
    return( rp_rule_unit_unary(p,out,RP_SYMBOL_ASINH) );
  }

  /* acosh( expr ) */
  else if (rp_parser_accept(p,RP_TOKEN_ACOSH))
  {
    return( rp_rule_unit_unary(p,out,RP_SYMBOL_ACOSH) );
  }

  /* atanh( expr ) */
  else if (rp_parser_accept(p,RP_TOKEN_ATANH))
  {
    return( rp_rule_unit_unary(p,out,RP_SYMBOL_ATANH) );
  }

  /* abs( expr ) */
  else if (rp_parser_accept(p,RP_TOKEN_ABS))
  {
    return( rp_rule_unit_unary(p,out,RP_SYMBOL_ABS) );
  }

  /* min( l , r ) */
  else if (rp_parser_accept(p,RP_TOKEN_MIN))
  {
    return( rp_rule_unit_binary(p,out,RP_SYMBOL_MIN) );
  }

  /* max( l , r ) */
  else if (rp_parser_accept(p,RP_TOKEN_MAX))
  {
    return( rp_rule_unit_binary(p,out,RP_SYMBOL_MAX) );
  }

  /* ( expr ) */
  else if (rp_parser_accept(p,RP_TOKEN_LBR))
  {
    return( rp_rule_unit_unary(p,out,RP_SYMBOL_NO) );
  }

  /* matan( expr ) */
  else if (rp_parser_accept(p,RP_TOKEN_MATAN))
  {
    return( rp_rule_unit_unary(p,out,RP_SYMBOL_MATAN) );
  }

  /* safesqrt ( expr ) */
  else if (rp_parser_accept(p,RP_TOKEN_SAFESQRT))
  {
    return( rp_rule_unit_unary(p,out,RP_SYMBOL_SAFESQRT) );
  }

  /* atan2( l , r ) */
  else if (rp_parser_accept(p,RP_TOKEN_ATAN2))
  {
    return( rp_rule_unit_binary(p,out,RP_SYMBOL_ATAN2) );
  }

  /* otherwise*/
  else
  {
    rp_parser_stop(p,"token not supported in expressions");
    return( 0 );
  }
}

int rp_rule_function_call(rp_parser p, rp_function f, rp_erep * out)
{
  if (rp_parser_expect(p,RP_TOKEN_LBR,"("))
  {
    rp_erep_copy(out,rp_function_rep(f));
    return( rp_rule_function_call_iter(p,f,0,out) );
  }
  else
  {
    return( 0 );
  }
}

int rp_rule_function_call_iter(rp_parser p, rp_function f, int i, rp_erep * out)
{
  int res = 0;
  if (i<rp_function_arity(f))
  {
    rp_erep e;
    if (rp_rule_expr(p,&e))
    {
      /* i-th argument of f := e */
      rp_erep_replace(out,rp_function_local_var(i),e);
      rp_erep_destroy(&e);

      if (rp_parser_accept(p,RP_TOKEN_COMMA))
      {
        res = rp_rule_function_call_iter(p,f,i+1,out);
      }
      else if (rp_parser_accept(p,RP_TOKEN_RBR))
      {
        if (i==rp_function_arity(f)-1)
        {
          res = 1;
        }
        else
        {
          rp_parser_stop(p,"not enough arguments in a function call");
        }
      }
      else
      {
        rp_parser_stop(p,"function argument not found or wrong token");
      }
    }
  }
  else
  {
    rp_parser_stop(p,"too many arguments in a function call");
  }
  if (!res) rp_erep_destroy(out);
  return( res );
}


/* Parse an unsigned number */
int rp_rule_unsigned_number(rp_parser p, rp_interval i)
{
  int result;
  if (rp_parser_accept(p,RP_TOKEN_INTEGER) ||
      rp_parser_accept(p,RP_TOKEN_FLOAT))
  {
    rp_interval_from_str(rp_lexer_prev_text(rp_parser_lexer(p)),i);
    result = 1;
  }
  else if (rp_parser_accept(p,RP_TOKEN_INFINITY))
  {

    /*    rp_interval_set_real_line(i);*/
    rp_binf(i) = RP_MAX_DOUBLE;
    rp_bsup(i) = RP_INFINITY;
    result = 1;
  }
  else
  {
    result = 0;
  }
  return( result );
}

/* Parse a signed number */
int rp_rule_signed_number(rp_parser p, rp_interval i)
{
  int minus = 0;
  rp_interval j;

  /* sign */
  if (rp_parser_accept(p,RP_TOKEN_MINUS))
  {
    minus = 1;
  }
  else if (rp_parser_accept(p,RP_TOKEN_PLUS))
  {
    minus = 0;
  }

  if (rp_rule_unsigned_number(p,j))
  {
    if (minus)
    {
      rp_interval_neg(i,j);
    }
    else
    {
      rp_interval_copy(i,j);
    }
    return( 1 );
  }
  else
  {
    return( 0 );
  }
}

/* Parse (expr) and create symbol(expr) */
int rp_rule_unit_unary(rp_parser p, rp_erep * out, int symbol)
{
  int res = 0;
  rp_erep child;
  rp_erep_create(&child);

  if ((symbol!=RP_SYMBOL_NO) &&
      (!rp_parser_expect(p,RP_TOKEN_LBR,"("))) /* left bracket  */
  {
    rp_parser_stop(p,"left bracket not found");
  }
  else if (rp_rule_expr(p,&child))              /* expr          */
  {
    if (rp_parser_expect(p,RP_TOKEN_RBR,")"))   /* right bracket */
    {
      if (symbol==RP_SYMBOL_NO)
      {
        rp_erep_set(out,child);
      }
      else
      {
        rp_erep_create_unary(out,symbol,child);
      }
      res = 1;
    }
    else
    {
      rp_parser_stop(p,"right bracket not found");
    }
  }
  rp_erep_destroy(&child);
  return( res );
 }

/* Parse (expr, expr) and create symbol(expr, expr) */
int rp_rule_unit_binary(rp_parser p, rp_erep * out, int symbol)
{
  int res = 0;
  rp_erep left, right;
  rp_erep_create(&left);
  rp_erep_create(&right);

  if (!rp_parser_expect(p,RP_TOKEN_LBR,"("))      /* left bracket  */
  {
    rp_parser_stop(p,"left bracket not found");
  }
  else if (rp_rule_expr(p,&left))                 /* left          */
  {
    if (!rp_parser_expect(p,RP_TOKEN_COMMA,","))  /* comma */
    {
      rp_parser_stop(p,"comma not found");
    }
    else if(rp_rule_expr(p,&right))              /* right */
    {
      if (rp_parser_expect(p,RP_TOKEN_RBR,")"))  /* right bracket */
      {
        rp_erep_create_binary(out,symbol,left,right);
        res = 1;
      }
      else
      {
        rp_parser_stop(p,"right bracket not found");
      }
    }
  }
  rp_erep_destroy(&right);
  rp_erep_destroy(&left);
  return( res );
}
