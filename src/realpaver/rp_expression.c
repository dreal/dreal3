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
 * rp_expression.c                                                          *
 ****************************************************************************/

#include "rp_expression.h"

/* Equality test between nodes x and y */
int rp_node_vector_cmp(void * x, const void * y)
{
  return( x==y );
}

/* Destruction function for nodes in vectors */
void rp_node_vector_free(void * x)
{
  /* no destruction here */
}

/* Display function for nodes in vectors */
void rp_node_vector_display(FILE * out, void * x)
{
  /* useless function */
}

/* Creation of v */
void rp_vector_node_create(rp_vector * v)
{
  rp_vector_create(v,
                   rp_node_vector_cmp,
                   rp_node_vector_free,
                   rp_node_vector_display);
}

/* Creation of an array of local variables */
void rp_expr_args_create(rp_expr_args * a)
{
  rp_expr_args_size(*a) = 0;
  rp_expr_args_ptr(*a) = NULL;
}

/* Destruction of an array of local variables */
void rp_expr_args_destroy(rp_expr_args * a)
{
  int i;
  for (i=0; i<rp_expr_args_size(*a); ++i)
  {
    rp_erep_destroy(&rp_expr_args_node(*a,i));
    rp_vector_destroy(&rp_expr_args_dep(*a,i));
  }
  if (rp_expr_args_ptr(*a)!=NULL)
  {
    rp_free(rp_expr_args_ptr(*a));
  }
  rp_expr_args_size(*a) = 0;
}

/* Returns the index of v in the array if it is already present */
/* Otherwise returns -1                                         */
int rp_expr_args_contains(rp_expr_args a, int v)
{
  int i;
  for (i=0; i<rp_expr_args_size(a); ++i)
  {
    if (v==rp_expr_args_var(a,i))
    {
      return( i );
    }
  }
  return( -1 );
}

/* Insertion of a variable v in a that returns its index */
int rp_expr_args_insert(rp_expr_args a, int v)
{
  int i;
  if ((i = rp_expr_args_contains(a,v))==-1)
  {
    i = rp_expr_args_size(a) ++;
    if (rp_expr_args_ptr(a)==NULL)
    {
      rp_malloc(rp_expr_args_ptr(a),rp_expr_arg*,sizeof(rp_expr_arg));
    }
    else
    {
      rp_realloc(rp_expr_args_ptr(a),
		 rp_expr_arg*,
		 rp_expr_args_size(a)*sizeof(rp_expr_arg));
    }
    rp_expr_args_occur(a,i) = 1;
    rp_expr_args_var(a,i) = v;
    rp_vector_node_create(&rp_expr_args_dep(a,i));
    rp_erep_create_var(&rp_expr_args_node(a,i),v);
  }
  else
  {
    /* one more occurrence */
    ++rp_expr_args_occur(a,i);
  }
  return( i );
}

/* Recursive function that finds the variables occurrences in f */
void rp_expression_create_aux(rp_expr_args a, rp_erep * f)
{
  if ((*f)!=NULL)
  {
    if (rp_erep_type(*f)==RP_EREP_NODE_OP)
    {
      int i;
      for (i=0; i<rp_erep_arity(*f); ++i)
      {
	if (rp_erep_type(rp_erep_child(*f,i))==RP_EREP_NODE_VAR)
	{
	  int v;
	  if ((v=rp_expr_args_contains(a,rp_erep_var(rp_erep_child(*f,i))))==-1)
	  {
	    /* first occurrence encountered */
	    v = rp_expr_args_insert(a,rp_erep_var(rp_erep_child(*f,i)));
	  }
	  else
	  {
	    ++rp_expr_args_occur(a,v);
	  }
	  /* this child must point to the unique variable node */
	  rp_erep_destroy(&rp_erep_child(*f,i));
	  rp_erep_set(&rp_erep_child(*f,i),rp_expr_args_node(a,v));
	}
	else
	{
	  rp_expression_create_aux(a,&rp_erep_child(*f,i));
	}
      }
    }
    else if (rp_erep_type(*f)==RP_EREP_NODE_VAR)
    {
      /* whole expression equivalent to one variable */
      int v = rp_expr_args_insert(a,rp_erep_var(*f));
      rp_erep_destroy(f);
      rp_erep_set(f,rp_expr_args_node(a,v));
    }
  }
}

/* vec := list of nodes of f depending on x */
int rp_expression_create_depend(rp_vector_node vec, rp_erep f, int x)
{
  int result = 0;
  if (f!=NULL)
  {
    switch( rp_erep_type(f) )
    {
      case RP_EREP_NODE_VAR:
	if (rp_erep_var(f)==x)
	{
	  if (rp_vector_size(vec)==0)
	  {
	    rp_vector_insert(vec,f);
	  }
	  result = 1;
	}
	break;

    case RP_EREP_NODE_OP:
      if (rp_symbol_unary(rp_erep_symb(f)))
      {
	result = rp_expression_create_depend(vec,rp_erep_sub(f),x);
	if (result)
	{
	  rp_vector_insert(vec,f);
	}
      }
      else /* binary */
      {
	int lr, rr;
	lr = rp_expression_create_depend(vec,rp_erep_left(f),x);
	rr = rp_expression_create_depend(vec,rp_erep_right(f),x);
	result = (lr || rr);
	if (result)
	{
	  rp_vector_insert(vec,f);
	}
      }
      break;

      /* case RP_EREP_NODE_CST:*/
    }
  }
  return( result );
}

/* Creation of an expression e represented by f */
void rp_expression_create(rp_expression * e, rp_erep * f)
{
  int i;

  /* simplification of the tree-representation */
  rp_erep_simplify(f);

  /* creation of structure */
  rp_malloc(*e,rp_expression_def*,sizeof(rp_expression_def));

  /* creation of the array of variables and associated information */
  rp_expr_args_create(&rp_expression_lvar(*e));
  rp_erep_set(&rp_expression_rep(*e),*f);
  rp_expression_create_aux(rp_expression_lvar(*e),&rp_expression_rep(*e));

  rp_expression_occur(*e) = 0;

  /* creation of dependence lists for every variable */
  for (i=0; i<rp_expression_arity(*e); ++i)
  {
    rp_expression_create_depend(rp_expr_args_dep(rp_expression_lvar(*e),i),
				rp_expression_rep(*e),
				rp_expr_args_var(rp_expression_lvar(*e),i));

    rp_expression_occur(*e) += rp_expr_args_occur(rp_expression_lvar(*e),i);
  }

  /* derivability test */
  rp_expression_derivable(*e) = rp_erep_derivable(rp_expression_rep(*e));

  /* destruction of f */
  rp_erep_destroy(f);
}

/* Destruction */
void rp_expression_destroy (rp_expression * e)
{
  rp_expr_args_destroy(&rp_expression_lvar(*e));
  rp_erep_destroy(&rp_expression_rep(*e));
  rp_free(*e);
}

/* Copy */
void rp_expression_copy(rp_expression* e, rp_expression src)
{
  rp_erep aux;
  rp_erep_copy(&aux,rp_expression_rep(src));
  rp_expression_create(e,&aux);
}

/* rp_expression_val(e) := e(b)                     */
/* Returns false if the resulting interval is empty */
int rp_expression_eval(rp_expression e, rp_box b)
{
  return( rp_erep_eval(rp_expression_rep(e),b) );
}

/* rp_expression_val(e) := e(b)                     */
/* Only the nodes depending on v are evaluated      */
/* Returns false if the resulting interval is empty */
int rp_expression_eval_single(rp_expression e, rp_box b, int v)
{
  /* get the list of nodes depending on v */
  int i = 0, found = 0, j, result;
  while ((!found) && (i<rp_expression_arity(e)))
  {
    if (rp_expr_args_var(rp_expression_lvar(e),i)==v)
    {
      found = 1;
    }
    else
    {
      ++i;
    }
  }

  if (!found)
  {
    result = 0;
  }
  else
  {
    result = 1;
    /* evaluation */
    for (j=0;
	 result &&
	 j<rp_vector_size(rp_expr_args_dep(rp_expression_lvar(e),i));
	 ++j)
    {
      rp_erep f = (rp_erep)rp_vector_elem(
                                   rp_expr_args_dep(
                                          rp_expression_lvar(e),i),j);
      if (rp_erep_type(f)==RP_EREP_NODE_VAR)
      {
	rp_interval_copy(rp_erep_val(f),rp_box_elem(b,v));
      }
      else /* operation */
      {
	if (rp_symbol_unary(rp_erep_symb(f)))
	{
	  rp_interval aux;  /* useless */
	  result = rp_symbol_eval(rp_erep_symb(f))
	    (rp_erep_val(f),rp_erep_sub_val(f),aux);
	}
	else /* binary */
	{
	  result = rp_symbol_eval(rp_erep_symb(f))
	    (rp_erep_val(f),
	     rp_erep_left_val(f),
	     rp_erep_right_val(f));
	}
      }
    }
  }
  return( result );
}

/* rp_expression_val(e) := mean value(e)(b)         */
/* e(mid(b)) + sum_i (de/dxi(b)*(bi - mid(bi)))     */
/* Returns false if the resulting interval is empty */
int rp_expression_eval_center(rp_expression e, rp_box b)
{
  int i, res;
  rp_interval ec;

  if (!rp_expression_derivable(e))
  {
    return( rp_expression_eval(e,b) );
  }

  /* context saving and creation of midpoint(b) in b */
  for (i=0; i<rp_expression_arity(e); ++i)
  {
    /* global index of the i_th variable of e */
    int index = rp_expr_args_var(rp_expression_lvar(e),i);
    rp_interval_copy(rp_expr_args_domain(rp_expression_lvar(e),i),
		     rp_box_elem(b,index));
    rp_interval_set_point(rp_box_elem(b,index),
			  rp_interval_midpoint(rp_box_elem(b,index)));
  }

  /* evaluation e(mid(b)) */
  res = rp_erep_eval(rp_expression_rep(e),b);
  rp_interval_copy(ec,rp_erep_val(rp_expression_rep(e)));

  /* context restoration */
  for (i=0; i<rp_expression_arity(e); ++i)
  {
    /* global index of the i_th variable of e */
    int index = rp_expr_args_var(rp_expression_lvar(e),i);
    rp_interval_copy(rp_box_elem(b,index),
		     rp_expr_args_domain(rp_expression_lvar(e),i));
  }

  if (res)
  {
    /* computation of the partial derivatives de/dxi(b) */
    res = rp_expression_deriv_num(e,b);

    if (res)
    {
      rp_interval mid, sub, mul, aux;
      for (i=0; i<rp_expression_arity(e); ++i)
      {
	/* global index of the i_th variable of e */
	int index = rp_expr_args_var(rp_expression_lvar(e),i);
	rp_interval_set_point(mid,rp_interval_midpoint(rp_box_elem(b,index)));
	rp_interval_sub(sub,rp_box_elem(b,index),mid);
	rp_interval_mul(mul,sub,rp_erep_deriv(
                                     rp_expr_args_node(
                                         rp_expression_lvar(e),i)));
	rp_interval_copy(aux,ec);
	rp_interval_add(ec,mul,aux);
      }
      rp_interval_copy(rp_erep_val(rp_expression_rep(e)),ec);
      res = (!rp_interval_empty(ec));
    }
  }
  return( res );
}

/* rp_expression_val(e) := e(b)                     */
/* Use of Moore's theorem and monotonicity test     */
/* Returns false if the resulting interval is empty */
int rp_expression_eval_best(rp_expression e, rp_box b)
{
  int result;

  /* Moore's theorem: natural inclusion form optimal */
  if (rp_expression_arity(e)==rp_expression_occur(e))
  {
    result = rp_expression_eval(e,b);
  }

  /* Natural inclusion if e is not derivable */
  else if (!rp_expression_derivable(e))
  {
     result = rp_expression_eval(e,b);
  }

  /* Otherwise evaluation and derivation */
  else if (!rp_expression_deriv_num(e,b))
  {
    result = 0;
  }

  /* Monotonicity test if non empty derivatives */
  else
  {
    /* If 0 does not belong to de/dxi: context saving and copy in b(i)    */
    /* of the bound that must be used to compute the lower bounnd of e(b) */
    int found = 0, i;
    for (i=0; i<rp_expression_arity(e); ++i)
    {
      /* global index of the i_th variable of e */
      int index = rp_expr_args_var(rp_expression_lvar(e),i);
      if ((rp_expr_args_occur(rp_expression_lvar(e),i)>=2) &&
	  (!rp_interval_contains(rp_erep_deriv(rp_expr_args_node(rp_expression_lvar(e),i)),
				 0.0)))
      {
	found = 1;
	rp_interval_copy(rp_expr_args_domain(rp_expression_lvar(e),i),
			 rp_box_elem(b,index));

	if (rp_binf(rp_erep_deriv(rp_expr_args_node(rp_expression_lvar(e),i)))>0)
	{
	  /* derivative positive => left bound of b(i) */
	  rp_interval_set_point(rp_box_elem(b,index),
				rp_binf(rp_box_elem(b,index)));
	}
	else
	{
	  /* derivative negative => right bound of b(i) */
	  rp_interval_set_point(rp_box_elem(b,index),
				rp_bsup(rp_box_elem(b,index)));
	}
      }
    }
    if (!found)
    {
      /* evaluation already computed by rp_expression_deriv_num(e,b) */
      result = 1;
    }
    else
    {
      /* evaluation of left bound of e over b */
      if (rp_expression_eval(e,b))
      {
	int left = (int)rp_binf(rp_expression_val(e));

	/* evaluation of right bound */
	for (i=0; i<rp_expression_arity(e); ++i)
	{
	  int index = rp_expr_args_var(rp_expression_lvar(e),i);
	  if ((rp_expr_args_occur(rp_expression_lvar(e),i)>=2) &&
	      (!rp_interval_contains(rp_erep_deriv(
                                        rp_expr_args_node(
					     rp_expression_lvar(e),i)),0.0)))
	  {
	    if (rp_binf(rp_erep_deriv(rp_expr_args_node(rp_expression_lvar(e),i)))>0)
	    {
	      rp_interval_set_point(rp_box_elem(b,index),
				    rp_bsup(rp_expr_args_domain(rp_expression_lvar(e),i)));
	    }
	    else
	    {
	      rp_interval_set_point(rp_box_elem(b,index),
				    rp_binf(rp_expr_args_domain(rp_expression_lvar(e),i)));
	    }
	  }
	}
	if (rp_expression_eval(e,b))
	{
	  rp_binf(rp_expression_val(e)) = left;
	  result = 1;
	}
	else
	{
	  result = 0;
	}
      }
      else
      {
        result = 0;
      }
      /* context restoration */
      for (i=0; i<rp_expression_arity(e); ++i)
      {
	/* global index of the i_th variable of e */
	int index = rp_expr_args_var(rp_expression_lvar(e),i);
	if ((rp_expr_args_occur(rp_expression_lvar(e),i)>=2) &&
	    (!rp_interval_contains(rp_erep_deriv(rp_expr_args_node(rp_expression_lvar(e),
								   i)),0.0)))
	{
	  rp_interval_copy(rp_box_elem(b,index),
			   rp_expr_args_domain(rp_expression_lvar(e),i));
	}
      }
    }
  }
  return( result );
}

/* Projection onto every subterm of e such that inf(i)<=e<=sup(e) */
/* b is intersected with the projections onto the variables       */
/* Returns false if an empty interval is computed                 */
int rp_expression_project(rp_expression e, rp_interval i, rp_box b)
{
  rp_interval_inter(rp_erep_proj(rp_expression_rep(e)),
		    rp_erep_val(rp_expression_rep(e)),i);
  if (rp_interval_empty(rp_erep_proj(rp_expression_rep(e))))
  {
    return( 0 );
  }
  else
  {
    return( rp_erep_project(rp_expression_rep(e),b) );
  }
}

/* Computation of all the partial derivatives of e   */
/* The expression is first evaluated on b            */
/* Returns false if at least one derivative is empty */
int rp_expression_deriv_num(rp_expression e, rp_box b)
{
  if (!rp_expression_eval(e,b))
  {
    return( 0 );
  }
  else
  {
    int i;
    /* all the partial derivatives := 0 */
    for (i=0; i<rp_expression_arity(e); ++i)
    {
      rp_interval_set_point(rp_erep_deriv(
                               rp_expr_args_node(
                                  rp_expression_lvar(e),i)),0.0);
    }

    /* de / de := 1 */
    rp_interval_set_point(rp_erep_deriv(rp_expression_rep(e)),1.0);

    /* chain rule in the tree-representation */
    return( rp_erep_deriv_num(rp_expression_rep(e)) );
  }
}

/* Copy in de the value of d(e)/d(v) after the call of rp_expression_deriv_num */
/* Returns false if v does not occur in e                                      */
int rp_expression_deriv_val(rp_interval de, rp_expression e, int v)
{
  int i;
  for (i=0; i<rp_expression_arity(e); ++i)
  {
    if (v==rp_expr_args_var(rp_expression_lvar(e),i))
    {
      rp_interval_copy(de,rp_erep_deriv(rp_expr_args_node(rp_expression_lvar(e),i)));
      return( 1 );
    }
  }
  return( 0 );
}

/* de := d(e)/d(v) */
void rp_expression_deriv_symb(rp_expression * de, rp_expression e, int v)
{
  rp_erep df;
  rp_erep_deriv_symb(&df,rp_expression_rep(e),v);
  rp_expression_create(de,&df);
}

/* Display e on out */
void rp_expression_display(FILE* out, rp_expression e,
			   rp_vector_variable vars,
			   int digits, int mode)
{
  rp_erep_display(out,rp_expression_rep(e),vars,digits,mode);
}
