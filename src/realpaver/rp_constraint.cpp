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
 * rp_constraint.c                                                          *
 ****************************************************************************/

#include <gflags/gflags.h>
#include "rp_constraint.h"

DECLARE_bool(new_exp);

/* set constraint delta */
void rp_ctr_set_delta(rp_constraint * c, double delta)
{
  rp_constraint_delta(*c) = delta;
}

/* Creation of the numerical constraint (l rel r) */
void rp_ctr_num_create(rp_ctr_num * c,
                       rp_erep * l, int rel, rp_erep * r)
{
  rp_malloc(*c,rp_ctr_num,sizeof(rp_ctr_num_def));

  /* creation of the constraint functional expression */
  if ((rp_erep_type(*l)==RP_EREP_NODE_CST) &&
      (rp_interval_zero(rp_erep_val(*l))))
  {
    /* 0 rel r */
    rp_erep rc;
    rp_erep_copy(&rc,*r);
    rp_expression_create(&rp_ctr_num_func(*c),&rc);
    switch( rel )
    {
      case RP_RELATION_EQUAL:
        rp_ctr_num_relfunc(*c) = RP_RELATION_EQUAL;
        break;

      case RP_RELATION_SUPEQUAL:
        rp_ctr_num_relfunc(*c) = RP_RELATION_INF;
        break;

      case RP_RELATION_INFEQUAL:
        rp_ctr_num_relfunc(*c) = RP_RELATION_SUP;
        break;

      case RP_RELATION_SUP:
        rp_ctr_num_relfunc(*c) = RP_RELATION_INFEQUAL;
        break;

      case RP_RELATION_INF:
        rp_ctr_num_relfunc(*c) = RP_RELATION_SUPEQUAL;
        break;
    }
  }
  else if((rp_erep_type(*r)==RP_EREP_NODE_CST) &&
          (rp_interval_zero(rp_erep_val(*r))))
  {
    /* l rel 0 */
    rp_erep lc;
    rp_erep_copy(&lc,*l);
    rp_expression_create(&rp_ctr_num_func(*c),&lc);
    rp_ctr_num_relfunc(*c) = rel;
  }
  else
  {
    /* l rel r */
    rp_erep lc, rc, f;
    rp_erep_copy(&lc,*l);
    rp_erep_copy(&rc,*r);
    rp_erep_create_binary(&f,RP_SYMBOL_SUB,lc,rc);
    rp_erep_destroy(&lc);
    rp_erep_destroy(&rc);
    rp_expression_create(&rp_ctr_num_func(*c),&f);
    rp_ctr_num_relfunc(*c) = rel;
  }

  /* creation of constraint */
  rp_expression_create(&rp_ctr_num_left(*c),l);
  rp_expression_create(&rp_ctr_num_right(*c),r);
  rp_ctr_num_rel(*c) = rel;
  rp_ctr_num_used(*c) = 0;
}

/* Destruction */
void rp_ctr_num_destroy(rp_ctr_num * c)
{
  rp_expression_destroy(&rp_ctr_num_left(*c));
  rp_expression_destroy(&rp_ctr_num_right(*c));
  rp_expression_destroy(&rp_ctr_num_func(*c));
  rp_free(*c);
}

/* Returns true if no point of b is solution of c */
int rp_ctr_numeq_unfeasible(rp_ctr_num c, rp_box b)
{
  int res = 0;
  if ((!rp_expression_eval(rp_ctr_num_left(c),b)) ||
      (!rp_expression_eval(rp_ctr_num_right(c),b))) {
    /* at least one expression has an empty range over b */
    res = 1;
  } else {
    /* unfeasible if empty intersection */
    static rp_interval i;
    rp_interval_inter(i,rp_expression_val(rp_ctr_num_left(c)),
                        rp_expression_val(rp_ctr_num_right(c)));
    res = rp_interval_empty(i);
  }
  return( res );
}

/* Returns true if no point of b is solution of c */
int rp_ctr_numsup_unfeasible(rp_ctr_num c, rp_box b)
{
  int res = 0;
  if ((!rp_expression_eval(rp_ctr_num_left(c),b)) ||
      (!rp_expression_eval(rp_ctr_num_right(c),b))) {
    /* at least one expression has an empty range over b */
    res = 1;
  } else {
    /* unfeasible if left is entirely smaller than right */
    res = (rp_bsup(rp_expression_val(rp_ctr_num_left(c))) <
           rp_binf(rp_expression_val(rp_ctr_num_right(c))));
  }
  return( res );
}

/* Returns true if no point of b is solution of c */
int rp_ctr_numinf_unfeasible(rp_ctr_num c, rp_box b)
{
  int res = 0;
  if ((!rp_expression_eval(rp_ctr_num_left(c),b)) ||
      (!rp_expression_eval(rp_ctr_num_right(c),b))) {
    /* at least one expression has an empty range over b */
    res = 1;
  } else {
    /* unfeasible if left is entirely greater than right */
    res = (rp_binf(rp_expression_val(rp_ctr_num_left(c))) >
           rp_bsup(rp_expression_val(rp_ctr_num_right(c))));
  }
  return( res );
}

/* Returns true if no point of b is solution of c */
int rp_ctr_numsup_strict_unfeasible(rp_ctr_num c, rp_box b)
{
  int res = 0;
  if ((!rp_expression_eval(rp_ctr_num_left(c),b)) ||
      (!rp_expression_eval(rp_ctr_num_right(c),b))) {
    /* at least one expression has an empty range over b */
    res = 1;
  } else {
    /* unfeasible if left is entirely smaller than right */
    res = (rp_bsup(rp_expression_val(rp_ctr_num_left(c))) <=
           rp_binf(rp_expression_val(rp_ctr_num_right(c))));
  }
  return( res );
}

/* Returns true if no point of b is solution of c */
int rp_ctr_numinf_strict_unfeasible(rp_ctr_num c, rp_box b)
{
  int res = 0;
  if ((!rp_expression_eval(rp_ctr_num_left(c),b)) ||
      (!rp_expression_eval(rp_ctr_num_right(c),b))) {
    /* at least one expression has an empty range over b */
    res = 1;
  } else {
    /* unfeasible if left is entirely greater than right */
    res = (rp_binf(rp_expression_val(rp_ctr_num_left(c))) >=
           rp_bsup(rp_expression_val(rp_ctr_num_right(c))));
  }
  return( res );
}

/* Returns true if no point of b is solution of c */
int rp_ctr_num_unfeasible(rp_ctr_num c, rp_box b)
{
  int res = 1;
  switch( rp_ctr_num_rel(c) ) {
    case RP_RELATION_EQUAL:
      res = rp_ctr_numeq_unfeasible(c,b);
      break;

    case RP_RELATION_SUPEQUAL:
      res = rp_ctr_numsup_unfeasible(c,b);
      break;

    case RP_RELATION_INFEQUAL:
      res = rp_ctr_numinf_unfeasible(c,b);
      break;

    case RP_RELATION_SUP:
      res = rp_ctr_numsup_strict_unfeasible(c,b);
      break;

    case RP_RELATION_INF:
      res = rp_ctr_numinf_strict_unfeasible(c,b);
      break;
  }
  if (FLAGS_new_exp) {
      if (res) { rp_ctr_num_used(c) = 1; }
  } else {
      rp_ctr_num_used(c) = 1;
  }
  return( res );
}

/* Returns true if all the points of b are solutions of c */
int rp_ctr_numeq_inner(rp_ctr_num c, rp_box b)
{
  int res;
  if ((!rp_expression_eval(rp_ctr_num_left(c),b))||
      (!rp_expression_eval(rp_ctr_num_right(c),b))) {
    /* at least one expression has an empty range over b */
    res = 0;
    rp_ctr_num_used(c) = 1;
  } else {
    /* inner if the value of both expressions is a number */
    res = (rp_interval_point(rp_expression_val(rp_ctr_num_left(c))) &&
           rp_interval_equal(rp_expression_val(rp_ctr_num_left(c)),
                             rp_expression_val(rp_ctr_num_right(c))));
  }
  return( res );
}

/* Returns true if all the points of b are solutions of c */
int rp_ctr_numsup_inner(rp_ctr_num c, rp_box b)
{
  int res;
  if ((!rp_expression_eval(rp_ctr_num_left(c),b)) ||
      (!rp_expression_eval(rp_ctr_num_right(c),b))) {
    /* at least one expression has an empty range over b */
    res = 0;
    rp_ctr_num_used(c) = 1;
  } else {
    /* inner if left is greater than right */
    res = (rp_binf(rp_expression_val(rp_ctr_num_left(c))) >=
           rp_bsup(rp_expression_val(rp_ctr_num_right(c))));
  }
  return( res );
}

/* Returns true if all the points of b are solutions of c */
int rp_ctr_numsup_strict_inner(rp_ctr_num c, rp_box b)
{
  int res;
  if ((!rp_expression_eval(rp_ctr_num_left(c),b)) ||
      (!rp_expression_eval(rp_ctr_num_right(c),b)))
  {
    /* at least one expression has an empty range over b */
    res = 0;
    rp_ctr_num_used(c) = 1;
  }
  else
  {
    /* inner if left is greater than right */
    res = (rp_binf(rp_expression_val(rp_ctr_num_left(c))) >
           rp_bsup(rp_expression_val(rp_ctr_num_right(c))));
  }
  return( res );
}

/* Returns true if all the points of b are solutions of c */
int rp_ctr_numinf_inner(rp_ctr_num c, rp_box b)
{
  int res;
  if (!(rp_expression_eval(rp_ctr_num_left(c),b))||
      !(rp_expression_eval(rp_ctr_num_right(c),b)))
  {
    /* at least one expression has an empty range over b */
    res = 0;
    rp_ctr_num_used(c) = 1;
  }
  else
  {
    /* inner if left is smaller than right */
    res = (rp_bsup(rp_expression_val(rp_ctr_num_left(c))) <=
           rp_binf(rp_expression_val(rp_ctr_num_right(c))));
  }
  return( res );
}

/* Returns true if all the points of b are solutions of c */
int rp_ctr_numinf_strict_inner(rp_ctr_num c, rp_box b)
{
  int res;
  if (!(rp_expression_eval(rp_ctr_num_left(c),b))||
      !(rp_expression_eval(rp_ctr_num_right(c),b)))
  {
    /* at least one expression has an empty range over b */
    res = 0;
    rp_ctr_num_used(c) = 1;
  }
  else
  {
    /* inner if left is smaller than right */
    res = (rp_bsup(rp_expression_val(rp_ctr_num_left(c))) <
           rp_binf(rp_expression_val(rp_ctr_num_right(c))));
  }
  return( res );
}

/* Returns true if all the points of b are solutions of c */
int rp_ctr_num_inner(rp_ctr_num c, rp_box b)
{
  int res = 0;
  switch( rp_ctr_num_rel(c) )
  {
    case RP_RELATION_EQUAL:
      res = rp_ctr_numeq_inner(c,b);
      break;

    case RP_RELATION_SUPEQUAL:
      res = rp_ctr_numsup_inner(c,b);
      break;

    case RP_RELATION_INFEQUAL:
      res = rp_ctr_numinf_inner(c,b);
      break;

    case RP_RELATION_SUP:
      res = rp_ctr_numsup_strict_inner(c,b);
      break;

    case RP_RELATION_INF:
      res = rp_ctr_numinf_strict_inner(c,b);
      break;
  }
  return( res );
}

/* Display c on out */
void rp_ctr_num_display(FILE* out, rp_ctr_num c,
                        rp_vector_variable var, int digits)
{
  rp_expression_display(out,rp_ctr_num_left(c),var,digits,
                        RP_INTERVAL_MODE_BOUND);
  switch( rp_ctr_num_rel(c) )
  {
    case RP_RELATION_EQUAL:
      fprintf(out,"=");
      break;

    case RP_RELATION_SUPEQUAL:
      fprintf(out,">=");
      break;

    case RP_RELATION_INFEQUAL:
      fprintf(out,"<=");
      break;

    case RP_RELATION_SUP:
      fprintf(out,">");
      break;

    case RP_RELATION_INF:
      fprintf(out,"<");
      break;
  }
  rp_expression_display(out,rp_ctr_num_right(c),var,digits,
                        RP_INTERVAL_MODE_BOUND);
  if ( rp_ctr_num_used(c) ) {
      fprintf(out, " used");
  } else {
      fprintf(out, " NOT used");
  }
}

/* Creation of an empty piecewise constraint for variable v */
void rp_ctr_piecewise_create(rp_ctr_piecewise * c, int v)
{
  rp_malloc(*c,rp_ctr_piecewise,sizeof(rp_ctr_piecewise_def));
  rp_ctr_piecewise_var(*c) = v;
  rp_ctr_piecewise_ptr(*c) = NULL;
  rp_ctr_piecewise_arity(*c) = 0;
  rp_union_create(&rp_ctr_piecewise_guard(*c));
}


/* Destruction */
void rp_ctr_piecewise_destroy(rp_ctr_piecewise * c)
{
  int i, j;
  for (i=0; i<rp_ctr_piecewise_arity(*c); ++i)
  {
    /* destruction of each element */
    for (j=0; j<rp_ctr_piecewise_elem_size(*c,i); ++j)
    {
      rp_ctr_num_destroy(&rp_ctr_piecewise_elem_ctrnum(*c,i,j));
    }
    if (rp_ctr_piecewise_elem_size(*c,i)>0)
    {
      rp_free(rp_ctr_piecewise_elem_ptr(*c,i));
    }
  }
  if (rp_ctr_piecewise_arity(*c)>0)
  {
    rp_free(rp_ctr_piecewise_ptr(*c));
  }
  rp_union_destroy(&rp_ctr_piecewise_guard(*c));
  rp_free(*c);
}

/* Insertion of a new domain */
int rp_ctr_piecewise_insert_domain(rp_ctr_piecewise c, rp_interval x)
{
  rp_union_interval aux;
  int i = rp_ctr_piecewise_arity(c) ++;
  int result = 1;
  if (i==0)
  {
    rp_malloc(rp_ctr_piecewise_ptr(c),
              rp_ctr_piecewise_elem*,
              sizeof(rp_ctr_piecewise_elem));
  }
  else
  {
    rp_realloc(rp_ctr_piecewise_ptr(c),
               rp_ctr_piecewise_elem*,
               rp_ctr_piecewise_arity(c)*sizeof(rp_ctr_piecewise_elem));
  }
  rp_interval_copy(rp_ctr_piecewise_elem_dom(c,i),x);
  rp_ctr_piecewise_elem_size(c,i) = 0;
  rp_ctr_piecewise_elem_ptr(c,i) = NULL;

  /* management of the guard */
  rp_union_create(&aux);
  rp_union_copy(aux,rp_ctr_piecewise_guard(c));
  if (rp_union_inter(aux,x))
  {
    /* non empty intersection, must be reduced to one point */
    if ((rp_union_card(aux)==1) &&
        (rp_interval_point(rp_union_elem(aux,0))))
    {
      if (rp_union_contains(rp_ctr_piecewise_guard(c),rp_binf(x)))
      {
        rp_binf(x) = rp_next_double(rp_binf(x));
      }
      else if(rp_union_contains(rp_ctr_piecewise_guard(c),rp_bsup(x)))
      {
        rp_bsup(x) = rp_prev_double(rp_bsup(x));
      }
      if (rp_interval_empty(x))
      {
        result = 0;
      }
      else
      {
        rp_union_insert(rp_ctr_piecewise_guard(c),x);
      }
    }
    else
    {
      result = 0;
    }
  }
  else
  {
    /* empty intersection */
    rp_union_insert(rp_ctr_piecewise_guard(c),x);
  }
  rp_union_destroy(&aux);
  return( result );
}

/* Insertion of a constraint associated with the last created domain */
void rp_ctr_piecewise_insert_constraint(rp_ctr_piecewise c, rp_ctr_num ctr)
{
  int i = rp_ctr_piecewise_arity(c)-1;
  int j = rp_ctr_piecewise_elem_size(c,i) ++;
  if (j==0)
  {
    rp_malloc(rp_ctr_piecewise_elem_ptr(c,i),
              rp_ctr_num*,
              sizeof(rp_ctr_num));
  }
  else
  {
    rp_realloc(rp_ctr_piecewise_elem_ptr(c,i),
               rp_ctr_num*,
               rp_ctr_piecewise_elem_size(c,i)*sizeof(rp_ctr_num));
  }
  rp_ctr_piecewise_elem_ctrnum(c,i,j) = ctr;
}

/* Returns true if no point of b is solution of c */
int rp_ctr_piecewise_unfeasible(rp_ctr_piecewise c, rp_box b)
{
  /*
   * piecewise(x, I1:C1, ..., Ik:Ck) unfeasible if for every k in 1..n
   *   - either domain(x) inter Ik is empty
   *   - or Ck is unfeasible
  */
  int k;
  for (k=0; k<rp_ctr_piecewise_arity(c); ++k)
  {
    /* domain of x and Ik intersects and Ck not unfeasible */
    if ((!rp_interval_disjoint(rp_box_elem(b,rp_ctr_piecewise_var(c)),
                               rp_ctr_piecewise_elem_dom(c,k))))
    {
      int j = 0,
          feasible = 1;
      while (feasible && (j<rp_ctr_piecewise_elem_size(c,k)))
      {
        if (rp_ctr_num_unfeasible(rp_ctr_piecewise_elem_ctrnum(c,k,j),b))
        {
          feasible = 0;
        }
        else
        {
          ++j;
        }
      }
      if (feasible)
      {
        return( 0 );  /* c is not unfeasible */
      }
    }
  }
  return( 1 );
}

/* Returns true if all the points of b are solutions of c */
int rp_ctr_piecewise_inner(rp_ctr_piecewise /*c*/, rp_box /*b*/)
{
  /* TO BE IMPLEMENTED */
  return( 0 );
}

/* Display c on out */
void rp_ctr_piecewise_display(FILE* out, rp_ctr_piecewise c,
                              rp_vector_variable var, int digits)
{
  int i, j;
  fprintf(out,"piecewise(%s, ",
          rp_variable_name(rp_vector_variable_elem(var,rp_ctr_piecewise_var(c))));
  for (i=0; i<rp_ctr_piecewise_arity(c); ++i)
  {
    rp_interval_display_bounds(out,rp_ctr_piecewise_elem_dom(c,i),digits);
    fprintf(out,": ");
    for (j=0; j<rp_ctr_piecewise_elem_size(c,i); ++j)
    {
      rp_ctr_num_display(out,rp_ctr_piecewise_elem_ctrnum(c,i,j),var,digits);
      if (j<rp_ctr_piecewise_elem_size(c,i)-1)
      {
        fprintf(out," # ");
      }
    }
    if (i<rp_ctr_piecewise_arity(c)-1)
    {
      fprintf(out," , ");
    }
  }
  fprintf(out," )");

  fprintf(out, " pieces: ");
  rp_union_display_bounds(out,rp_ctr_piecewise_guard(c),digits);
}

/* Creation of an empty conditional constraint */
void rp_ctr_cond_create(rp_ctr_cond * c)
{
  rp_malloc(*c,rp_ctr_cond,sizeof(rp_ctr_cond_def));
  rp_ctr_cond_guard(*c) = NULL;
  rp_ctr_cond_guardsize(*c) = 0;
  rp_ctr_cond_conc(*c) = NULL;
  rp_ctr_cond_concsize(*c) = 0;
}

/* Destruction */
void rp_ctr_cond_destroy(rp_ctr_cond * c)
{
  int i;
  for (i=0; i<rp_ctr_cond_guardsize(*c); ++i)
  {
    rp_ctr_num_destroy(&(rp_ctr_cond_guard_elem(*c,i)));
  }
  for (i=0; i<rp_ctr_cond_concsize(*c); ++i)
  {
    rp_ctr_num_destroy(&(rp_ctr_cond_conc_elem(*c,i)));
  }
  if (rp_ctr_cond_guard(*c)!=NULL)
  {
    rp_free(rp_ctr_cond_guard(*c));
  }
  if (rp_ctr_cond_conc(*c)!=NULL)
  {
    rp_free(rp_ctr_cond_conc(*c));
  }
  rp_free(*c);
}

/* Insertion of a constraint in the guard */
void rp_ctr_cond_insert_guard(rp_ctr_cond c, rp_ctr_num guard)
{
  ++rp_ctr_cond_guardsize(c);
  if (rp_ctr_cond_guardsize(c)==1)
  {
    rp_malloc(rp_ctr_cond_guard(c),rp_ctr_num*,sizeof(rp_ctr_num));
  }
  else
  {
    rp_realloc(rp_ctr_cond_guard(c),
               rp_ctr_num*,
               rp_ctr_cond_guardsize(c)*sizeof(rp_ctr_num));
  }
  rp_ctr_cond_guard_elem(c,rp_ctr_cond_guardsize(c)-1) = guard;
}

/* Insertion of a constraint in the conclusion */
void rp_ctr_cond_insert_conc(rp_ctr_cond c, rp_ctr_num conc)
{
  ++rp_ctr_cond_concsize(c);
  if (rp_ctr_cond_concsize(c)==1)
  {
    rp_malloc(rp_ctr_cond_conc(c),rp_ctr_num*,sizeof(rp_ctr_num));
  }
  else
  {
    rp_realloc(rp_ctr_cond_conc(c),
               rp_ctr_num*,
               rp_ctr_cond_concsize(c)*sizeof(rp_ctr_num));
  }
  rp_ctr_cond_conc_elem(c,rp_ctr_cond_concsize(c)-1) = conc;
}

/* Display c on out */
void rp_ctr_cond_display(FILE* out, rp_ctr_cond c,
                         rp_vector_variable var, int digits)
{
  int i;
  for (i=0; i<rp_ctr_cond_guardsize(c); ++i)
  {
    if (i>0) fprintf(out," # ");
    rp_ctr_num_display(out,rp_ctr_cond_guard_elem(c,i),var,digits);
  }
  fprintf(out," -> ");
  for (i=0; i<rp_ctr_cond_concsize(c); ++i)
  {
    if (i>0) fprintf(out," # ");
    rp_ctr_num_display(out,rp_ctr_cond_conc_elem(c,i),var,digits);
  }
}

/* Returns true if no point of b is solution of c */
int rp_ctr_cond_unfeasible(rp_ctr_cond c, rp_box b)
{
  /* A -> B unfeasible <=> A certainly satisfied and B unfeasible */
  /* <=> all a in A are certainly satisfied                       */
  /*     and one b is B is unfeasible                             */
  int i;
  for (i=0; i<rp_ctr_cond_guardsize(c); ++i)
  {
    if (!rp_ctr_num_inner(rp_ctr_cond_guard_elem(c,i),b))
    {
      return( 0 );
    }
  }
  /* the guard is certainly satisfied */
  for (i=0; i<rp_ctr_cond_concsize(c); ++i)
  {
    if (rp_ctr_num_unfeasible(rp_ctr_cond_conc_elem(c,i),b))
    {
      return( 1 );
    }
  }
  /* the conclusion is feasible */
  return( 0 );
}

/* Returns true if all the points of b are solutions of c */
int rp_ctr_cond_inner(rp_ctr_cond c, rp_box b)
{
  /* A -> B certainly satisfied <=> A unfeasible or B certainly satisfied */
  /* <=> one a in A is unfeasible or all b in B are certainly satisfied */
  int i;
  for (i=0; i<rp_ctr_cond_guardsize(c); ++i)
  {
    if (rp_ctr_num_unfeasible(rp_ctr_cond_guard_elem(c,i),b))
    {
      return( 1 );
    }
  }
  /* the guard is feasible */
  for (i=0; i<rp_ctr_cond_concsize(c); ++i)
  {
    if (!rp_ctr_num_inner(rp_ctr_cond_conc_elem(c,i),b))
    {
      return( 0 );
    }
  }
  /* the conclusion is certainly satisfied */
  return( 1 );
}

/* Declare that c contains var */
void rp_constraint_insert_variable(rp_constraint c, int var)
{
  /* check whether var already belongs to c */
  int found = 0, i = 0;
  while ((!found) && (i<rp_constraint_arity(c)))
  {
    if (var==rp_constraint_var(c,i))
    {
      found = 1;
    }
    else ++i;
  }
  if (!found)
  {
    ++rp_constraint_arity(c);
    if (rp_constraint_arity(c)==1)
    {
      rp_malloc(rp_constraint_vptr(c),int*,sizeof(int));
    }
    else
    {
      rp_realloc(rp_constraint_vptr(c),int*,rp_constraint_arity(c)*sizeof(int));
    }
    rp_constraint_var(c,i) = var;
  }
}

/* Declare that c contains all the variables of cnum */
void rp_constraint_insert_variable_num(rp_constraint c, rp_ctr_num cnum)
{
  int i;

  /* for every variable in the constraint */
  for (i=0; i<rp_ctr_num_arity(cnum); ++i)
  {
    rp_constraint_insert_variable(c,rp_ctr_num_var(cnum,i));
  }
}

/* Creation of a constraint representing a numerical constraint */
void rp_constraint_create_num(rp_constraint * c, rp_ctr_num cnum)
{
  rp_malloc(*c,rp_constraint,sizeof(rp_constraint_def));
  rp_constraint_type(*c) = RP_CONSTRAINT_NUMERICAL;
  rp_constraint_num(*c) = cnum;

  /* the variables */
  rp_constraint_arity(*c) = 0;
  rp_constraint_vptr(*c) = NULL;
  rp_constraint_insert_variable_num(*c,cnum);
}

/* Creation of a constraint representing a conditional constraint */
void rp_constraint_create_cond(rp_constraint * c, rp_ctr_cond cond)
{
  int i;
  rp_malloc(*c,rp_constraint,sizeof(rp_constraint_def));
  rp_constraint_type(*c) = RP_CONSTRAINT_CONDITIONAL;
  rp_constraint_cond(*c) = cond;

  /* the variables */
  rp_constraint_arity(*c) = 0;
  rp_constraint_vptr(*c) = NULL;

  /* for every constraint in the guard */
  for (i=0; i<rp_ctr_cond_guardsize(cond); ++i)
  {
    rp_constraint_insert_variable_num(*c,rp_ctr_cond_guard_elem(cond,i));
  }

  /* for every constraint in the conclusion */
  for (i=0; i<rp_ctr_cond_concsize(cond); ++i)
  {
    rp_constraint_insert_variable_num(*c,rp_ctr_cond_conc_elem(cond,i));
  }
}

/* Creation of a constraint representing a piecewise constraint */
void rp_constraint_create_piece (rp_constraint * c,
                                 rp_ctr_piecewise piece)
{
  int i, j;
  rp_malloc(*c,rp_constraint,sizeof(rp_constraint_def));
  rp_constraint_type(*c) = RP_CONSTRAINT_PIECEWISE;
  rp_constraint_piece(*c) = piece;

  /* the variables */
  rp_constraint_arity(*c) = 0;
  rp_constraint_vptr(*c) = NULL;

  /* insertion of the main variable */
  rp_constraint_insert_variable(*c,rp_ctr_piecewise_var(piece));

  for (i=0; i<rp_ctr_piecewise_arity(piece); ++i)
  {
    for (j=0; j<rp_ctr_piecewise_elem_size(piece,i); ++j)
    {
      rp_constraint_insert_variable_num(*c,rp_ctr_piecewise_elem_ctrnum(piece,i,j));
    }
  }
}

/* Destruction */
void rp_constraint_destroy (rp_constraint * c)
{
  switch (rp_constraint_type(*c))
  {
    case RP_CONSTRAINT_NUMERICAL:
      rp_ctr_num_destroy(&rp_constraint_num(*c));
      break;

    case RP_CONSTRAINT_CONDITIONAL:
      rp_ctr_cond_destroy(&rp_constraint_cond(*c));
      break;

    case RP_CONSTRAINT_PIECEWISE:
      rp_ctr_piecewise_destroy(&rp_constraint_piece(*c));
      break;
  }
  if (rp_constraint_vptr(*c)!=NULL)
  {
    /* false for variable-free constraints */
    rp_free(rp_constraint_vptr(*c));
  }
  rp_free(*c);
}

/* Display c on out */
void rp_constraint_display(FILE* out, rp_constraint c,
                           rp_vector_variable var, int digits)
{
  switch (rp_constraint_type(c))
  {
    case RP_CONSTRAINT_NUMERICAL:
      rp_ctr_num_display(out,rp_constraint_num(c),var,digits);
      break;

    case RP_CONSTRAINT_CONDITIONAL:
      rp_ctr_cond_display(out,rp_constraint_cond(c),var,digits);
      break;

    case RP_CONSTRAINT_PIECEWISE:
      rp_ctr_piecewise_display(out,rp_constraint_piece(c),var,digits);
      break;
  }
}

void rp_constraint_display_nl(FILE* out, rp_constraint c,
                              rp_vector_variable var, int digits) {
    rp_constraint_display(out, c, var, digits);
    fprintf(out, "\n");
}

/* Returns true if no point of b is solution of c */
int rp_constraint_unfeasible(rp_constraint c, rp_box b)
{
  int res = 1;
  switch( rp_constraint_type(c) )
  {
    case RP_CONSTRAINT_NUMERICAL:
      res = rp_ctr_num_unfeasible(rp_constraint_num(c),b);
      break;

    case RP_CONSTRAINT_CONDITIONAL:
      res = rp_ctr_cond_unfeasible(rp_constraint_cond(c),b);
      break;

    case RP_CONSTRAINT_PIECEWISE:
      res = rp_ctr_piecewise_unfeasible(rp_constraint_piece(c),b);
      break;
  }
  return( res );
}

/* Returns true if all the points of b are solutions of c */
int rp_constraint_inner(rp_constraint c, rp_box b)
{
  int res = 1;
  switch( rp_constraint_type(c) )
  {
    case RP_CONSTRAINT_NUMERICAL:
      res = rp_ctr_num_inner(rp_constraint_num(c),b);
      break;

    case RP_CONSTRAINT_CONDITIONAL:
      res = rp_ctr_cond_inner(rp_constraint_cond(c),b);
      break;

    case RP_CONSTRAINT_PIECEWISE:
      res = rp_ctr_piecewise_inner(rp_constraint_piece(c),b);
      break;
  }
  return( res );
}

/* Equality test between constraints x and y */
int rp_constraint_vector_cmp(void * x, const void * y)
{
  return( x==y );
}

/* Destruction function for constraints in vectors */
void rp_constraint_vector_free(void * x)
{
  rp_constraint c = (rp_constraint)x;
  rp_constraint_destroy(&c);
}

/* Display function for constraints in vectors */
void rp_constraint_vector_display(FILE * /*out*/, void * /*x*/)
{
  /* nothing here */
}

/* Creation of v */
void rp_vector_constraint_create(rp_vector * v)
{
  rp_vector_create(v,
                   rp_constraint_vector_cmp,
                   rp_constraint_vector_free,
                   rp_constraint_vector_display);
}

/* Display v on out */
void rp_vector_constraint_display(FILE * out,
                                  rp_vector_constraint v,
                                  rp_vector_variable vars,
                                  int digits)
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
      rp_constraint_display(out,(rp_constraint)rp_vector_elem(v,i),vars,digits);
      fprintf(out,"\n");
    }
  }
}
