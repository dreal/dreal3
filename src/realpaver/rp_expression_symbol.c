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
 * rp_expression_symbol.c                                                   *
 ****************************************************************************/

#include <string.h>
#include "rp_expression_symbol.h"

/* Creation of a null expression */
void rp_erep_create (rp_erep * f)
{
  (*f) = NULL;
}

/* Creation of an expression equivalent to v */
void rp_erep_create_var(rp_erep * f, int v)
{
  rp_malloc(*f,struct rp_erep_cell*,sizeof(struct rp_erep_cell));
  rp_erep_ref(*f) = 1;
  rp_erep_type(*f) = RP_EREP_NODE_VAR;
  rp_erep_childs(*f) = NULL;
  rp_erep_arity(*f) = 0;
  rp_erep_var(*f) = v;
}

/* Creation of an expression equivalent to a number */
/* which is enclosed by i and represented by s      */
void rp_erep_create_cst(rp_erep * f, const char * s, rp_interval i)
{
  rp_malloc(*f,struct rp_erep_cell*,sizeof(struct rp_erep_cell));
  rp_erep_ref(*f) = 1;
  rp_erep_type(*f) = RP_EREP_NODE_CST;
  rp_erep_childs(*f) = NULL;
  rp_erep_arity(*f) = 0;
  rp_interval_copy(rp_erep_val(*f),i);
  if ((s==NULL) || (strcmp(s,"")==0))
  {
    rp_erep_cst(*f) = NULL;
  }
  else
  {
    rp_malloc(rp_erep_cst(*f),char*,1+strlen(s));
    strcpy(rp_erep_cst(*f),s);
  }
}

/* Creation of an expression equivalent to op(l) */
void rp_erep_create_unary(rp_erep * f, int op, rp_erep l)
{
  rp_malloc(*f,struct rp_erep_cell*,sizeof(struct rp_erep_cell));
  rp_erep_ref(*f) = 1;
  rp_erep_type(*f) = RP_EREP_NODE_OP;
  rp_malloc(rp_erep_childs(*f),struct rp_erep_cell**,sizeof(struct rp_erep_cell *));
  rp_erep_arity(*f) = 1;
  rp_erep_left(*f) = l;
  ++ rp_erep_ref(l);
  rp_erep_right(*f) = NULL;
  rp_erep_symb(*f) = op;
}

/* Creation of an expression equivalent to op(l,r) */
void rp_erep_create_binary(rp_erep * f, int op,
                           rp_erep l, rp_erep r)
{
  rp_malloc(*f,struct rp_erep_cell*,sizeof(struct rp_erep_cell));
  rp_erep_ref(*f) = 1;
  rp_erep_type(*f) = RP_EREP_NODE_OP;
  rp_malloc(rp_erep_childs(*f),struct rp_erep_cell**,
            2*sizeof(struct rp_erep_cell *));
  rp_erep_arity(*f) = 2;
  rp_erep_left(*f) = l;
  ++ rp_erep_ref(l);
  rp_erep_right(*f) = r;
  ++ rp_erep_ref(r);
  rp_erep_symb(*f) = op;
}

/* Destruction of an expression */
void rp_erep_destroy(rp_erep * f)
{
  if ((*f)!=NULL)
  {
    -- rp_erep_ref(*f);
    if (rp_erep_ref(*f)==0)
    {
      int i;
      if (rp_erep_arity(*f)>0)
      {
        for (i=0; i<rp_erep_arity(*f); ++i)
        {
          rp_erep_destroy(&rp_erep_child(*f,i));
        }
        rp_free(rp_erep_childs(*f));
      }
      else if ((rp_erep_type(*f)==RP_EREP_NODE_CST) &&
          (rp_erep_cst(*f)!=NULL))
      {
        rp_free(rp_erep_cst(*f));
      }
      rp_free(*f);
    }
  }
}

/* f := src */
void rp_erep_set(rp_erep * f, rp_erep src)
{
  /*  rp_erep_destroy(f); */
  *f = src;
  ++ rp_erep_ref(src);
}

/* f := a new expression equivalent to src */
/* nothing is shared between f and src     */
void rp_erep_copy(rp_erep * f, rp_erep src)
{
  if (src==NULL)
  {
    (*f) = NULL;
  }
  else
  {
    switch( rp_erep_type(src) )
    {
      case RP_EREP_NODE_CST:
        rp_erep_create_cst(f,rp_erep_cst(src),rp_erep_val(src));
        break; /* RP_EREP_NODE_CST */

      case RP_EREP_NODE_VAR:
        rp_erep_create_var(f,rp_erep_var(src));
        break; /* RP_EREP_NODE_VAR */

      case RP_EREP_NODE_OP:
        if (rp_symbol_unary(rp_erep_symb(src)))
        {
          rp_erep l;
          rp_erep_copy(&l,rp_erep_left(src));
          rp_erep_create_unary(f,rp_erep_symb(src),l);
          rp_erep_destroy(&l);
        }
        else
        {
          rp_erep l, r;
          rp_erep_copy(&l,rp_erep_left(src));
          rp_erep_copy(&r,rp_erep_right(src));
          rp_erep_create_binary(f,rp_erep_symb(src),l, r);
          rp_erep_destroy(&l);
          rp_erep_destroy(&r);
        }
        break; /* RP_EREP_NODE_OP */
    } /* switch */
  }
}

/* Replace every occurrence of var with a copy of src */
void rp_erep_replace(rp_erep * f, int var, rp_erep src)
{
  if ((*f)!=NULL)
  {
    switch( rp_erep_type(*f) )
    {
      case RP_EREP_NODE_CST:
        /* nothing to do */
        break; /* RP_EREP_NODE_CST */

      case RP_EREP_NODE_VAR:
        if (var==rp_erep_var(*f))
        {
          rp_erep_destroy(f);
          rp_erep_copy(f,src);
        }
        break; /* RP_EREP_NODE_VAR */

      case RP_EREP_NODE_OP:
        if (rp_symbol_unary(rp_erep_symb(*f)))
        {
          rp_erep_replace(&rp_erep_left(*f),var,src);
        }
        else
        {
          rp_erep_replace(&rp_erep_left(*f),var,src);
          rp_erep_replace(&rp_erep_right(*f),var,src);
        }
        break; /* RP_EREP_NODE_OP */
    } /* switch */
  }
}


/* Count the number of nodes in f */
int rp_erep_count_node(rp_erep f)
{
  int result;
  if (f==NULL)
  {
    result = 0;
  }
  else if ((rp_erep_type(f)==RP_EREP_NODE_VAR) ||
           (rp_erep_type(f)==RP_EREP_NODE_CST))
  {
    result = 1;
  }
  else
  {
    int i;
    result = 1;  /* the root node */
    for (i=0; i<rp_erep_arity(f); ++i)
    {
      result += rp_erep_count_node(rp_erep_child(f,i));
    }
  }
  return( result );
}

/* Returns true if v occurs in f */
int rp_erep_is_present(rp_erep f, int v)
{
  int result = 0;
  if (f!=NULL)
  {
    switch( rp_erep_type(f) )
    {
      case RP_EREP_NODE_VAR:
        if (rp_erep_var(f)==v)
        {
          result = 1;
        }
        break;

    case RP_EREP_NODE_OP:
      if (rp_symbol_unary(rp_erep_symb(f)))
      {
        result = rp_erep_is_present(rp_erep_sub(f),v);
      }
      else /* binary */
      {
        if (!(result = rp_erep_is_present(rp_erep_left(f),v)))
        {
          result = rp_erep_is_present(rp_erep_right(f),v);
        }
      }
      break;

      /* case RP_EREP_NODE_CST:*/
    }
  }
  return( result );
}

/* Returns true if f and g are equivalent */
int rp_erep_is_equal(rp_erep f, rp_erep g)
{
  int result = 0;
  if ((f==NULL) && (g==NULL))
  {
    result = 1;
  }
  else if ((f!=NULL) && (g!=NULL) && (rp_erep_type(f)==rp_erep_type(g)))
  {
    switch( rp_erep_type(f) )
    {
      case RP_EREP_NODE_CST:
        if (rp_interval_equal(rp_erep_val(f),rp_erep_val(g)))
        {
          result = 1;
        }
        break; /* RP_EREP_NODE_CST */

      case RP_EREP_NODE_VAR:
        if (rp_erep_var(f)==rp_erep_var(g))
        {
          result = 1;
        }
        break; /* RP_EREP_NODE_VAR */

      case RP_EREP_NODE_OP:
        if (rp_erep_symb(f)==rp_erep_symb(g))
        {
          if (rp_symbol_unary(rp_erep_symb(f)))
          {
            result = rp_erep_is_equal(rp_erep_sub(f),rp_erep_sub(g));
          }
          else
          {
            result = rp_erep_is_equal(rp_erep_left(f),rp_erep_left(g)) &&
                     rp_erep_is_equal(rp_erep_right(f),rp_erep_right(g));
          }
        }
        break;
    }
  }
  return( result );
}

/* Returns true if f is constant */
int rp_erep_is_constant(rp_erep f)
{
  int result = 1;
  if (f!=NULL)
  {
    switch( rp_erep_type(f) )
    {
      case RP_EREP_NODE_VAR:
        result = 0;
        break; /* RP_EREP_NODE_VAR */

      case RP_EREP_NODE_OP:
        if (rp_symbol_unary(rp_erep_symb(f)))
        {
          result = rp_erep_is_constant(rp_erep_sub(f));
        }
        else
        {
          if ((result = rp_erep_is_constant(rp_erep_left(f))))
          {
            result = rp_erep_is_constant(rp_erep_right(f));
          }
        }
        break; /* RP_EREP_NODE_OP */
    } /* switch */
  }
  return( result );
}

/* Returns true if f represents an integer */
int rp_erep_is_integer(rp_erep f, long * n)
{
  if ((rp_erep_type(f)==RP_EREP_NODE_CST) &&
      (rp_interval_point(rp_erep_val(f))) &&
      (rp_binf(rp_erep_val(f))==floor(rp_binf(rp_erep_val(f)))))
  {
    (*n) = (long)rp_binf(rp_erep_val(f));
    return( 1 );
  }
  else
  {
    return( 0 );
  }
}

/* Returns true if f represents a rational number */
int rp_erep_is_rational(rp_erep f, long * sign, long * num, long * den)
{
  int result = 0;
  if (f!=NULL)
  {
    rp_erep aux;
    if ((rp_erep_type(f)==RP_EREP_NODE_OP) &&
        (rp_erep_symb(f)==RP_SYMBOL_NEG))
    {
      (*sign) = -1;
      aux = rp_erep_sub(f);
    }
    else
    {
      (*sign) = 1;
      aux = f;
    }

    /* integer */
    if (rp_erep_is_integer(aux,num))
    {
      (*den) = 1;
      result = 1;
    }

    /* / */
    else if ((rp_erep_type(aux)==RP_EREP_NODE_OP) &&
             (rp_erep_symb(aux)==RP_SYMBOL_DIV))
    {

      if (rp_erep_is_integer(rp_erep_left(aux),num) &&
          rp_erep_is_integer(rp_erep_right(aux),den))
      {
        result = 1;
      }
      else
      {
        result = 0;
      }
    }
  }
  return( result );
}

/* Returns true if the root node of f is a multiplication */
rp_inline
int rp_erep_is_mul(rp_erep f)
{
  return( (f!=NULL) && (rp_erep_type(f)==RP_EREP_NODE_OP) &&
          ((rp_erep_symb(f)==RP_SYMBOL_MUL) ||
           (rp_erep_symb(f)==RP_SYMBOL_MUL_R_I) ||
           (rp_erep_symb(f)==RP_SYMBOL_MUL_RNEG_I) ||
           (rp_erep_symb(f)==RP_SYMBOL_MUL_RPOS_I)) );
}

/* Returns true if the root node of f is a division */
rp_inline
int rp_erep_is_div(rp_erep f)
{
  return( (f!=NULL) && (rp_erep_type(f)==RP_EREP_NODE_OP) &&
          ((rp_erep_symb(f)==RP_SYMBOL_DIV) ||
           (rp_erep_symb(f)==RP_SYMBOL_DIV_I_R) ||
           (rp_erep_symb(f)==RP_SYMBOL_DIV_I_RPOS) ||
           (rp_erep_symb(f)==RP_SYMBOL_DIV_I_RNEG) ||
           (rp_erep_symb(f)==RP_SYMBOL_DIV_R_I) ||
           (rp_erep_symb(f)==RP_SYMBOL_DIV_RPOS_I) ||
           (rp_erep_symb(f)==RP_SYMBOL_DIV_RNEG_I)) );
}

/* Returns true if the root node of f is an addition */
rp_inline
int rp_erep_is_add(rp_erep f)
{
  return( (f!=NULL) && (rp_erep_type(f)==RP_EREP_NODE_OP) &&
          ((rp_erep_symb(f)==RP_SYMBOL_ADD) ||
           (rp_erep_symb(f)==RP_SYMBOL_ADD_R_I)) );
}

/* Returns true if the root node of f is a substraction */
rp_inline
int rp_erep_is_sub(rp_erep f)
{
  return( (f!=NULL) && (rp_erep_type(f)==RP_EREP_NODE_OP) &&
          ((rp_erep_symb(f)==RP_SYMBOL_SUB) ||
           (rp_erep_symb(f)==RP_SYMBOL_SUB_R_I) ||
           (rp_erep_symb(f)==RP_SYMBOL_SUB_I_R)) );
}

/* Returns true if f is equal to 0 */
rp_inline
int rp_erep_is_zero(rp_erep f)
{
  return( (f!=NULL) && (rp_erep_type(f)==RP_EREP_NODE_CST) &&
          (rp_interval_zero(rp_erep_val(f))) );
}

/* Returns true if f is equal to 1 */
rp_inline
int rp_erep_is_one(rp_erep f)
{
  return( (f!=NULL) && (rp_erep_type(f)==RP_EREP_NODE_CST) &&
          (rp_binf(rp_erep_val(f))==1.0) &&
          (rp_bsup(rp_erep_val(f))==1.0) );
}

/* Simplification of constant subterms of f */
/* Returns true if f has been modified      */
int rp_erep_simplify_constant(rp_erep * f)
{
  int result = 0;
  if (((*f)!=NULL) && (rp_erep_type(*f)==RP_EREP_NODE_OP))
  {
    if (rp_erep_is_constant(*f))
    {
      rp_box b = NULL;   /* useless */
      rp_interval i;
      rp_erep_eval(*f,b);
      rp_interval_copy(i,rp_erep_val(*f));
      rp_erep_destroy(f);
      rp_erep_create_cst(f,"",i);
      result = 1;
    }
    else
    {
      int i;
      for (i=0; i<rp_erep_arity(*f); ++i)
      {
        result = (rp_erep_simplify_constant(&rp_erep_child(*f,i)) || result);
      }
    }
  }
  return( result );
}

/* Simplification of divisions by one   */
/* Returns true if f has been modified  */
int rp_erep_simplify_div_one(rp_erep * f)
{
  int result = 0;
  if (((*f)!=NULL) && (rp_erep_type(*f)==RP_EREP_NODE_OP))
  {
    /* recursion */
    int i;
    for (i=0; i<rp_erep_arity(*f); ++i)
    {
      result = (rp_erep_simplify_div_one(&rp_erep_child(*f,i)) || result);
    }

    /* simplification of the root node  */
    if (rp_erep_is_div(*f) && (rp_erep_is_one(rp_erep_right(*f))))
    {
      /* u / 1 -> u */
      rp_erep aux;
      rp_erep_set(&aux,rp_erep_left(*f));
      rp_erep_destroy(f);
      rp_erep_set(f,aux);
      rp_erep_destroy(&aux);
      result = 1;
    }
  }
  return( result );
}

/* Simplification of expressions (1/u)*v <=> v*(1/u) -> v/u */
/* Returns true if f has been modified                      */
int rp_erep_simplify_mul_inv(rp_erep * f)
{
  int result = 0;
  if (((*f)!=NULL) && (rp_erep_type(*f)==RP_EREP_NODE_OP))
  {
    /* recursion */
    int i;
    for (i=0; i<rp_erep_arity(*f); ++i)
    {
      result = (rp_erep_simplify_mul_inv(&rp_erep_child(*f,i)) || result);
    }

    /* simplification of the root node  */
    if (rp_erep_is_mul(*f))
    {
      if ((rp_erep_is_div(rp_erep_left(*f))) &&
          (rp_erep_type(rp_erep_left(rp_erep_left(*f)))==RP_EREP_NODE_CST) &&
          (rp_binf(rp_erep_val(rp_erep_left(rp_erep_left(*f))))==1.0) &&
          (rp_bsup(rp_erep_val(rp_erep_left(rp_erep_left(*f))))==1.0))
      {
        /* (1/u) * v -> v/u */
        rp_erep u, v;
        rp_erep_set(&u,rp_erep_right(rp_erep_left(*f)));
        rp_erep_set(&v,rp_erep_right(*f));
        rp_erep_destroy(f);
        rp_erep_create_binary(f,RP_SYMBOL_DIV,v,u);
        rp_erep_destroy(&u);
        rp_erep_destroy(&v);
        result = 1;
      }
      else if ((rp_erep_is_div(rp_erep_right(*f))) &&
               (rp_erep_type(rp_erep_left(rp_erep_right(*f)))==RP_EREP_NODE_CST) &&
               (rp_binf(rp_erep_val(rp_erep_left(rp_erep_right(*f))))==1.0) &&
               (rp_bsup(rp_erep_val(rp_erep_left(rp_erep_right(*f))))==1.0))
      {
        /* v * (1/u) -> v/u */
        rp_erep u, v;
        rp_erep_set(&u,rp_erep_right(rp_erep_right(*f)));
        rp_erep_set(&v,rp_erep_left(*f));
        rp_erep_destroy(f);
        rp_erep_create_binary(f,RP_SYMBOL_DIV,v,u);
        rp_erep_destroy(&u);
        rp_erep_destroy(&v);
        result = 1;
      }
    }
  }
  return( result );
}

/* Simplification of multiplications by one */
/* Returns true if f has been modified      */
int rp_erep_simplify_mul_one(rp_erep * f)
{
  int result = 0;
  if (((*f)!=NULL) && (rp_erep_type(*f)==RP_EREP_NODE_OP))
  {
    /* recursion */
    int i;
    for (i=0; i<rp_erep_arity(*f); ++i)
    {
      result = (rp_erep_simplify_mul_one(&rp_erep_child(*f,i)) || result);
    }

    /* simplification of the root node  */
    if (rp_erep_is_mul(*f) && (rp_erep_is_one(rp_erep_left(*f)) ||
                               (rp_erep_is_one(rp_erep_right(*f)))))
    {
      rp_erep aux;
      if (rp_erep_is_one(rp_erep_left(*f)))
      {
        rp_erep_set(&aux,rp_erep_right(*f));
      }
      else
      {
        rp_erep_set(&aux,rp_erep_left(*f));
      }
      rp_erep_destroy(f);
      rp_erep_set(f,aux);
      rp_erep_destroy(&aux);
      result = 1;
    }
  }
  return( result );
}

/* Simplification of multiplications by zero */
/* Returns true if f has been modified       */
int rp_erep_simplify_mul_zero(rp_erep * f)
{
  int result = 0;
  if (((*f)!=NULL) && (rp_erep_type(*f)==RP_EREP_NODE_OP))
  {
    /* recursion */
    int i;
    for (i=0; i<rp_erep_arity(*f); ++i)
    {
      result = (rp_erep_simplify_mul_zero(&rp_erep_child(*f,i)) || result);
    }

    /* simplification of the root node  */
    if (rp_erep_is_mul(*f) && (rp_erep_is_zero(rp_erep_left(*f)) ||
                               (rp_erep_is_zero(rp_erep_right(*f)))))
    {
      rp_interval i;
      rp_interval_set_point(i,0.0);
      rp_erep_destroy(f);
      rp_erep_create_cst(f,"",i);
      result = 1;
    }
  }
  return( result );
}

/* Simplification of divisions zero/u -> zero */
/* Returns true if f has been modified        */
int rp_erep_simplify_div_zero(rp_erep * f)
{
  int result = 0;
  if (((*f)!=NULL) && (rp_erep_type(*f)==RP_EREP_NODE_OP))
  {
    /* recursion */
    int i;
    for (i=0; i<rp_erep_arity(*f); ++i)
    {
      result = (rp_erep_simplify_div_zero(&rp_erep_child(*f,i)) || result);
    }

    /* simplification of the root node  */
    if (rp_erep_is_div(*f) && (rp_erep_is_zero(rp_erep_left(*f))))
    {
      rp_interval i;
      rp_interval_set_point(i,0.0);
      rp_erep_destroy(f);
      rp_erep_create_cst(f,"",i);
      result = 1;
    }
  }
  return( result );
}

/* Simplification of additions by zero */
/* Returns true if f has been modified */
int rp_erep_simplify_add_zero(rp_erep * f)
{
  int result = 0;
  if (((*f)!=NULL) && (rp_erep_type(*f)==RP_EREP_NODE_OP))
  {
    /* recursion */
    int i;
    for (i=0; i<rp_erep_arity(*f); ++i)
    {
      result = (rp_erep_simplify_add_zero(&rp_erep_child(*f,i)) || result);
    }

    /* simplification of the root node  */
    if (rp_erep_is_add(*f) && (rp_erep_is_zero(rp_erep_left(*f)) ||
                               (rp_erep_is_zero(rp_erep_right(*f)))))
    {
      rp_erep aux;
      if (rp_erep_is_zero(rp_erep_left(*f)))
      {
        rp_erep_set(&aux,rp_erep_right(*f));
      }
      else
      {
        rp_erep_set(&aux,rp_erep_left(*f));
      }
      rp_erep_destroy(f);
      rp_erep_set(f,aux);
      rp_erep_destroy(&aux);
      result = 1;
    }
  }
  return( result );
}

/* Simplification of substractions by zero */
/* Returns true if f has been modified     */
int rp_erep_simplify_sub_zero(rp_erep * f)
{
  int result = 0;
  if (((*f)!=NULL) && (rp_erep_type(*f)==RP_EREP_NODE_OP))
  {
    /* recursion */
    int i;
    for (i=0; i<rp_erep_arity(*f); ++i)
    {
      result = (rp_erep_simplify_sub_zero(&rp_erep_child(*f,i)) || result);
    }

    /* simplification of the root node  */
    if (rp_erep_is_sub(*f) && (rp_erep_is_zero(rp_erep_left(*f)) ||
                               (rp_erep_is_zero(rp_erep_right(*f)))))
    {
      rp_erep aux;
      if (rp_erep_is_zero(rp_erep_left(*f)))
      {
        rp_erep aux2;
        /* 0-u -> -u */
        rp_erep_set(&aux2,rp_erep_right(*f));
        rp_erep_create_unary(&aux,RP_SYMBOL_NEG,aux2);
        rp_erep_destroy(&aux2);
      }
      else
      {
        /* u-0 -> u */
        rp_erep_set(&aux,rp_erep_left(*f));
      }
      rp_erep_destroy(f);
      rp_erep_set(f,aux);
      rp_erep_destroy(&aux);
      result = 1;
    }
  }
  return( result );
}

/* Simplification of substractions u - u */
/* Returns true if f has been modified   */
int rp_erep_simplify_sub_same(rp_erep * f)
{
  int result = 0;
  if (((*f)!=NULL) && (rp_erep_type(*f)==RP_EREP_NODE_OP))
  {
    /* recursion */
    int i;
    for (i=0; i<rp_erep_arity(*f); ++i)
    {
      result = (rp_erep_simplify_sub_same(&rp_erep_child(*f,i)) || result);
    }

    /* simplification of the root node  */
    if ((rp_erep_is_sub(*f)) &&
        (rp_erep_is_equal(rp_erep_left(*f),rp_erep_right(*f))))
    {
      rp_interval i;
      rp_interval_set_point(i,0.0);
      rp_erep_destroy(f);
      rp_erep_create_cst(f,"",i);
      result = 1;
    }
  }
  return( result );
}

/* Simplification of substractions u / u */
/* Returns true if f has been modified   */
int rp_erep_simplify_div_same(rp_erep * f)
{
  int result = 0;
  if (((*f)!=NULL) && (rp_erep_type(*f)==RP_EREP_NODE_OP))
  {
    /* recursion */
    int i;
    for (i=0; i<rp_erep_arity(*f); ++i)
    {
      result = (rp_erep_simplify_div_same(&rp_erep_child(*f,i)) || result);
    }

    /* simplification of the root node  */
    if ((rp_erep_is_div(*f)) &&
        (rp_erep_is_equal(rp_erep_left(*f),rp_erep_right(*f))))
    {
      rp_interval i;
      rp_interval_set_point(i,1.0);
      rp_erep_destroy(f);
      rp_erep_create_cst(f,"",i);
      result = 1;
    }
  }
  return( result );
}

/* Simplification of pow(f, n) if n<=2 */
/* Returns true if f has been modified */
int rp_erep_simplify_pow(rp_erep * f)
{
  int result = 0;
  if (((*f)!=NULL) && (rp_erep_type(*f)==RP_EREP_NODE_OP))
  {
    /* recursion */
    int i;
    for (i=0; i<rp_erep_arity(*f); ++i)
    {
      result = (rp_erep_simplify_pow(&rp_erep_child(*f,i)) || result);
    }

    /* simplification of the root node  */
    if ((rp_erep_symb(*f)==RP_SYMBOL_POW) &&
        (rp_binf(rp_erep_right_val(*f))<=2))
    {
      if (rp_binf(rp_erep_right_val(*f))==0)
      {
        /* u^0 -> 1 */
        rp_interval i;
        rp_interval_set_point(i,1.0);
        rp_erep_destroy(f);
        rp_erep_create_cst(f,"",i);
        result = 1;
      }
      else if (rp_binf(rp_erep_right_val(*f))==1)
      {
        /* u^1 -> u */
        rp_erep aux;
        rp_erep_set(&aux,rp_erep_left(*f));
        rp_erep_destroy(f);
        rp_erep_set(f,aux);
        rp_erep_destroy(&aux);
        result = 1;
      }
      else  /* exponent 2 */
      {
        /* pow(u,2) -> sqr(u) */
        rp_erep aux;
        rp_erep_set(&aux,rp_erep_left(*f));
        rp_erep_destroy(f);
        rp_erep_create_unary(f,RP_SYMBOL_SQR,aux);
        rp_erep_destroy(&aux);
        result = 1;
      }
    }
  }
  return( result );
}

/* Simplification of f^n / f^m -> f^(n-m) */
/* Returns true if f has been modified    */
int rp_erep_simplify_div_pow(rp_erep * f)
{
  int result = 0;

  if (((*f)!=NULL) && (rp_erep_type(*f)==RP_EREP_NODE_OP))
  {
    /* recursion */
    int i;
    for (i=0; i<rp_erep_arity(*f); ++i)
    {
      result = (rp_erep_simplify_div_pow(&rp_erep_child(*f,i)) || result);
    }

    /* simplification of the root node  */
    if (rp_erep_is_div(*f))
    {
      /* u / v */
      int lexp, rexp;
      rp_erep laux, raux;


      if (rp_erep_type(rp_erep_left(*f))==RP_EREP_NODE_OP)
      {
        if (rp_erep_symb(rp_erep_left(*f))==RP_SYMBOL_SQR)
        {
          /* u <=> h^2  =>  laux := h, lexp := 2 */
          rp_erep_set(&laux,rp_erep_sub(rp_erep_left(*f)));
          lexp = 2;
        }
        else if (rp_erep_symb(rp_erep_left(*f))==RP_SYMBOL_POW)
        {
          /* u <=> h^n  =>  laux := h, lexp := n */
          rp_erep_set(&laux,rp_erep_left(rp_erep_left(*f)));
          lexp = (int)rp_binf(rp_erep_right_val(rp_erep_left(*f)));
        }
        else
        {
          /* u <=> h  =>  laux := h, lexp := 1 */
          rp_erep_set(&laux,rp_erep_left(*f));
          lexp = 1;
        }
      }
      else
      {
        /* u <=> h  =>  laux := h, lexp := 1 */
        rp_erep_set(&laux,rp_erep_left(*f));
        lexp = 1;
      }

      if (rp_erep_type(rp_erep_right(*f))==RP_EREP_NODE_OP)
      {
        if (rp_erep_symb(rp_erep_right(*f))==RP_SYMBOL_SQR)
        {
          /* v <=> g^2  =>  raux := g, rexp := 2 */
          rp_erep_set(&raux,rp_erep_sub(rp_erep_right(*f)));
          rexp = 2;
        }
        else if (rp_erep_symb(rp_erep_right(*f))==RP_SYMBOL_POW)
        {
          /* v <=> g^n  =>  raux := g, rexp := n */
          rp_erep_set(&raux,rp_erep_left(rp_erep_right(*f)));
          rexp = (int)rp_binf(rp_erep_right_val(rp_erep_right(*f)));
        }
        else
        {
          /* v <=> g  =>  raux := g, rexp := 1 */
          rp_erep_set(&raux,rp_erep_right(*f));
          rexp = 1;
        }
      }
      else
      {
        /* v <=> g  =>  raux := g, rexp := 1 */
        rp_erep_set(&raux,rp_erep_right(*f));
        rexp = 1;
      }

      if (rp_erep_is_equal(laux,raux))
      {
        /* simplification -> laux^(lexp-rexp)*/
        int n = lexp - rexp;
        result = 1;
        rp_erep_destroy(f);

        if (n==0)
        {
          /* simplification -> 1 */
          rp_interval i;
          rp_interval_set_point(i,1.0);
          rp_erep_create_cst(f,"",i);
        }
        else if (n>=1)
        {
          if (n==1)
          {
            /* simplification -> laux */
            rp_erep_set(f,laux);
          }
          else if (n==2)
          {
            /* simplification -> sqr(laux) */
            rp_erep_create_unary(f,RP_SYMBOL_SQR,laux);
          }
          else
          {
            /* simplification -> pow(laux,n) */
            rp_interval i;
            rp_erep aux;
            rp_interval_set_point(i,n);
            rp_erep_create_cst(&aux,"",i);
            rp_erep_create_binary(f,RP_SYMBOL_POW,laux,aux);
            rp_erep_destroy(&aux);
          }
        }
        else
        {
          /* simplification -> 1 / laux^n*/
          if (n==-1)
          {
            /* simplification -> 1/laux */
            rp_interval i;
            rp_erep aux;
            rp_interval_set_point(i,1.0);
            rp_erep_create_cst(&aux,"",i);
            rp_erep_create_binary(f,RP_SYMBOL_DIV,aux,laux);
            rp_erep_destroy(&aux);
          }
          else if (n==-2)
          {
            /* simplification -> 1/laux^2 */
            rp_interval i;
            rp_erep aux1, aux2;
            rp_interval_set_point(i,1.0);
            rp_erep_create_cst(&aux1,"",i);
            rp_erep_create_unary(&aux2,RP_SYMBOL_SQR,laux);
            rp_erep_create_binary(f,RP_SYMBOL_DIV,aux1,aux2);
            rp_erep_destroy(&aux1);
            rp_erep_destroy(&aux2);
          }
          else
          {
            /* simplification -> 1/pow(laux,-n) */
            rp_interval i;
            rp_erep aux1, aux2, aux3;
            rp_interval_set_point(i,1.0);
            rp_erep_create_cst(&aux1,"",i);
            rp_interval_set_point(i,-n);
            rp_erep_create_cst(&aux2,"",i);
            rp_erep_create_binary(&aux3,RP_SYMBOL_POW,laux,aux2);
            rp_erep_create_binary(f,RP_SYMBOL_DIV,aux1,aux3);
            rp_erep_destroy(&aux1);
            rp_erep_destroy(&aux2);
            rp_erep_destroy(&aux3);
          }
        }
      }

      rp_erep_destroy(&laux);
      rp_erep_destroy(&raux);
    }
  }
  return( result );
}

/* Simplification of f=f1+f2+...+fn */
void rp_erep_simplify_sum_aux(rp_erep * f, rp_interval i)
{
  if ((rp_erep_type(*f)==RP_EREP_NODE_OP) && rp_erep_is_add(*f))
  {
    if (rp_erep_left_type(*f)==RP_EREP_NODE_CST)
    {
      /* a+v -> v, i += a, and recursion in v */
      rp_interval j;
      rp_erep aux;
      rp_interval_copy(j,i);
      rp_interval_add(i,j,rp_erep_left_val(*f));
      rp_erep_set(&aux,rp_erep_right(*f));
      rp_erep_destroy(f);
      rp_erep_set(f,aux);
      rp_erep_destroy(&aux);
      rp_erep_simplify_sum_aux(f,i);
    }
    else if (rp_erep_right_type(*f)==RP_EREP_NODE_CST)
    {
      /* u+a -> u, i += a, and recursion in u */
      rp_interval j;
      rp_erep aux;
      rp_interval_copy(j,i);
      rp_interval_add(i,j,rp_erep_right_val(*f));
      rp_erep_set(&aux,rp_erep_left(*f));
      rp_erep_destroy(f);
      rp_erep_set(f,aux);
      rp_erep_destroy(&aux);
      rp_erep_simplify_sum_aux(f,i);
    }
    else
    {
      /* u+v -> recursion */
      int j;
      for (j=0; j<rp_erep_arity(*f); ++j)
      {
        rp_erep_simplify_sum_aux(&rp_erep_child(*f,j),i);
      }
    }
  }
}

/* Simplification of f1+f2+...+fn in f -> only one constant node */
/* Returns true if f has been modified                           */
int rp_erep_simplify_sum(rp_erep * f)
{
  int result = 0;
  if (((*f)!=NULL) && (rp_erep_type(*f)==RP_EREP_NODE_OP))
  {
    /* simplification of the root node  */
    if (rp_erep_is_add(*f))
    {
      rp_interval i;
      int nnode, nnodenew;
      rp_interval_set_point(i,0.0);
      nnode = rp_erep_count_node(*f);
      rp_erep_simplify_sum_aux(f,i);

      if ((rp_binf(i)!=0.0) || (rp_bsup(i)!=0.0))
      {
        /* f := i+f */
        rp_erep aux1, aux2;
        rp_erep_set(&aux1,*f);
        rp_erep_destroy(f);
        rp_erep_create_cst(&aux2,"",i);
        rp_erep_create_binary(f,RP_SYMBOL_ADD,aux2,aux1);
        nnodenew = rp_erep_count_node(*f);
        rp_erep_destroy(&aux1);
        rp_erep_destroy(&aux2);

        /* the sum is considered to be modified only if at least
           one node has been removed */
        result = (nnodenew < nnode);
      }
    }
    else
    {
      /* recursion */
      int i;
      for (i=0; i<rp_erep_arity(*f); ++i)
      {
        result = (rp_erep_simplify_sum(&rp_erep_child(*f,i)) || result);
      }
    }
  }
  return( result );
}

/* Simplification of f=f1*f2*...*fn */
void rp_erep_simplify_prod_aux(rp_erep * f, rp_interval i)
{
  if ((rp_erep_type(*f)==RP_EREP_NODE_OP) && rp_erep_is_mul(*f))
  {
    if (rp_erep_left_type(*f)==RP_EREP_NODE_CST)
    {
      /* a*v -> v, i *= a, and recursion in v */
      rp_interval j;
      rp_erep aux;
      rp_interval_copy(j,i);
      rp_interval_mul(i,j,rp_erep_left_val(*f));
      rp_erep_set(&aux,rp_erep_right(*f));
      rp_erep_destroy(f);
      rp_erep_set(f,aux);
      rp_erep_destroy(&aux);
      rp_erep_simplify_prod_aux(f,i);
    }
    else if (rp_erep_right_type(*f)==RP_EREP_NODE_CST)
    {
      /* u*a -> u, i *= a, and recursion in u */
      rp_interval j;
      rp_erep aux;
      rp_interval_copy(j,i);
      rp_interval_mul(i,j,rp_erep_right_val(*f));
      rp_erep_set(&aux,rp_erep_left(*f));
      rp_erep_destroy(f);
      rp_erep_set(f,aux);
      rp_erep_destroy(&aux);
      rp_erep_simplify_prod_aux(f,i);
    }
    else
    {
      /* u*v -> recursion */
      int j;
      for (j=0; j<rp_erep_arity(*f); ++j)
      {
        rp_erep_simplify_prod_aux(&rp_erep_child(*f,j),i);
      }
    }
  }
}

/* Simplification of f1*f2*...*fn in f -> only one constant node */
/* Returns true if f has been modified                      */
int rp_erep_simplify_prod(rp_erep * f)
{
  int result = 0;
  if (((*f)!=NULL) && (rp_erep_type(*f)==RP_EREP_NODE_OP))
  {

   /* simplification of the root node  */
    if (rp_erep_is_mul(*f))
    {
      rp_interval i;
      int nnode, nnodenew;
      rp_interval_set_point(i,1.0);
      nnode = rp_erep_count_node(*f);
      rp_erep_simplify_prod_aux(f,i);

      if ((rp_binf(i)!=1.0) || (rp_bsup(i)!=1.0))
      {
        /* f := i*f */
        rp_erep aux1, aux2;
        rp_erep_set(&aux1,*f);
        rp_erep_destroy(f);
        rp_erep_create_cst(&aux2,"",i);
        rp_erep_create_binary(f,RP_SYMBOL_MUL,aux2,aux1);
        nnodenew = rp_erep_count_node(*f);
        rp_erep_destroy(&aux1);
        rp_erep_destroy(&aux2);

        /* the product is considered to be modified only if at least
           one node has been removed */
        result = (nnodenew < nnode);
      }
    }
    else
    {
      /* recursion */
      int i;
      for (i=0; i<rp_erep_arity(*f); ++i)
      {
        result = (rp_erep_simplify_prod(&rp_erep_child(*f,i)) || result);
      }
    }
  }
  return( result );
}

/* op(u,v) -> op(v,u) */
void rp_erep_shift_child(rp_erep * f)
{
  rp_erep aux = rp_erep_left(*f);
  rp_erep_left(*f) = rp_erep_right(*f);
  rp_erep_right(*f) = aux;
}

/* Choose the more precise symbols */
void rp_erep_simplify_symbols(rp_erep * f)
{
  int i;
  if (((*f)!=NULL) && (rp_erep_type(*f)==RP_EREP_NODE_OP))
  {
    if (rp_erep_is_add(*f))
    {
      if (rp_erep_left_type(*f)==RP_EREP_NODE_CST)
      {
        /* x + v */
        rp_erep_symb(*f) = RP_SYMBOL_ADD_R_I;
      }
      else if (rp_erep_right_type(*f)==RP_EREP_NODE_CST)
      {
        /* u + x */
        rp_erep_shift_child(f);
        rp_erep_symb(*f) = RP_SYMBOL_ADD_R_I;
      }
    }
    else if (rp_erep_is_sub(*f))
    {
      if (rp_erep_left_type(*f)==RP_EREP_NODE_CST)
      {
        /* x - v */
        rp_erep_symb(*f) = RP_SYMBOL_SUB_R_I;
      }
      else if (rp_erep_right_type(*f)==RP_EREP_NODE_CST)
      {
        /* u - x */
        rp_erep_symb(*f) = RP_SYMBOL_SUB_I_R;
      }
    }
    else if (rp_erep_is_mul(*f))
    {
      if (rp_erep_left_type(*f)==RP_EREP_NODE_CST)
      {
        /* x * v */
        rp_erep_symb(*f) = RP_SYMBOL_MUL_R_I;
      }
      else if (rp_erep_right_type(*f)==RP_EREP_NODE_CST)
      {
        /* u + x */
        rp_erep_shift_child(f);
        rp_erep_symb(*f) = RP_SYMBOL_MUL_R_I;
      }
    }
    else if (rp_erep_is_div(*f))
    {
      if (rp_erep_left_type(*f)==RP_EREP_NODE_CST)
      {
        /* x / v */
        rp_erep_symb(*f) = RP_SYMBOL_DIV_R_I;
      }
      else if (rp_erep_right_type(*f)==RP_EREP_NODE_CST)
      {
        /* u / x */
        rp_erep_symb(*f) = RP_SYMBOL_DIV_I_R;
      }
    }

    /* recursion */
    for (i=0; i<rp_erep_arity(*f); ++i)
    {
      rp_erep_simplify_symbols(&rp_erep_child(*f,i));
    }
  }
}

/* Simplification of f */
void rp_erep_simplify(rp_erep * f)
{
  int cst, div_one, mul_zero, mul_one, add_zero, sub_zero,
    sub_same, div_same, pow, div_pow, prod, sum, div_zero, mul_inv;
  do
  {
    cst      = rp_erep_simplify_constant(f);
    div_one  = rp_erep_simplify_div_one(f);
    mul_zero = rp_erep_simplify_mul_zero(f);
    mul_one  = rp_erep_simplify_mul_one(f);
    add_zero = rp_erep_simplify_add_zero(f);
    sub_zero = rp_erep_simplify_sub_zero(f);
    sub_same = rp_erep_simplify_sub_same(f);
    div_same = rp_erep_simplify_div_same(f);
    div_zero = rp_erep_simplify_div_zero(f);
    pow      = rp_erep_simplify_pow(f);
    div_pow  = rp_erep_simplify_div_pow(f);
    prod     = rp_erep_simplify_prod(f);
    sum      = rp_erep_simplify_sum(f);
    mul_inv  = rp_erep_simplify_mul_inv(f);
  }
  while (cst || div_one || mul_zero || mul_one || add_zero || sub_zero ||
         sub_same || div_same || pow || div_pow || prod || sum ||
         div_zero || mul_inv);

  rp_erep_simplify_symbols(f);
}

/* Returns true if f needs to be bracketed, s.t. f is a child of g */
rp_inline
int rp_erep_bracketed(rp_erep f, rp_erep g)
{
  return( (rp_erep_type(f)==RP_EREP_NODE_OP) &&

          ((rp_symbol_priority(rp_erep_symb(f)) <
            rp_symbol_priority(rp_erep_symb(g))) ||

           ((rp_symbol_priority(rp_erep_symb(f)) ==
             rp_symbol_priority(rp_erep_symb(g))) &&
            ((!rp_symbol_commutative(rp_erep_symb(g))) ||
             (!rp_symbol_commutative(rp_erep_symb(f)))))) );
}

/* Display f on out */
void rp_erep_display(FILE* out, rp_erep f, rp_vector_variable vars,
                     int digits, int mode)
{
  if (f!=NULL)
  {
    switch( rp_erep_type(f) )
    {
      case RP_EREP_NODE_CST:
        if (rp_erep_cst(f)!=NULL)
        {
          fprintf(out,"%s",rp_erep_cst(f));
        }
        else
        {
          rp_interval_display(out,rp_erep_val(f),digits,mode);
        }
        break; /* RP_EREP_NODE_CST */

      case RP_EREP_NODE_VAR:
        if (vars==NULL)
        {
          fprintf(out,"_v(%d)",rp_erep_var(f));
        }
        else
        {
          fprintf(out,"%s",
                  rp_variable_name(rp_vector_variable_elem(vars,rp_erep_var(f))));
        }
        break; /* RP_EREP_NODE_VAR */

      case RP_EREP_NODE_OP:
        if (rp_symbol_prefix(rp_erep_symb(f)))
        {
          fprintf(out,"%s(",rp_symbol_name(rp_erep_symb(f)));
          rp_erep_display(out,rp_erep_left(f),vars,digits,mode);

          if (rp_symbol_binary(rp_erep_symb(f)))
          {
            fprintf(out,",");
            rp_erep_display(out,rp_erep_right(f),vars,digits,mode);
          }
          fprintf(out,")");
        }
        else  /* infix */
        {
          int lb = rp_erep_bracketed(rp_erep_left(f),f);
          if (lb) fprintf(out,"(");
          rp_erep_display(out,rp_erep_left(f),vars,digits,mode);
          if (lb) fprintf(out,")");
          fprintf(out,"%s",rp_symbol_name(rp_erep_symb(f)));

          if (rp_symbol_binary(rp_erep_symb(f)))
          {
            int rb = rp_erep_bracketed(rp_erep_right(f),f);
            if (rb) fprintf(out,"(");
            rp_erep_display(out,rp_erep_right(f),vars,digits,mode);
            if (rb) fprintf(out,")");
          }
        }
        break; /* RP_EREP_NODE_OP */
    } /* switch */
  }
}

/* Evaluation of f on b                             */
/* Returns false if the resulting interval is empty */
int rp_erep_eval(rp_erep f, rp_box b)
{
  int result = 0;
  if (f!=NULL)
  {
    switch( rp_erep_type(f) )
    {
      case RP_EREP_NODE_CST:
        /* nothing to do */
        result = 1;
        break;

      case RP_EREP_NODE_VAR:
        /* evaluation := variable domain */
        rp_interval_copy(rp_erep_val(f),rp_box_elem(b,rp_erep_var(f)));
        result = !rp_interval_empty(rp_erep_val(f));
        break; /* RP_EREP_NODE_VAR */

      case RP_EREP_NODE_OP:
        /* bottom-up recursion: left, right, root */
        result = rp_erep_eval(rp_erep_left(f),b);
        if (result)
        {
          if (rp_symbol_unary(rp_erep_symb(f)))
          {
            rp_interval aux;  /* useless */
            result = rp_symbol_eval(rp_erep_symb(f))
              (rp_erep_val(f),rp_erep_left_val(f),aux);
          }
          else /* binary symbol */
          {
            result = rp_erep_eval(rp_erep_right(f),b);
            if (result)
            {
              result = rp_symbol_eval(rp_erep_symb(f))
                (rp_erep_val(f),
                 rp_erep_left_val(f),
                 rp_erep_right_val(f));
            }
            else
            {
              rp_interval_set_empty(rp_erep_val(f));
            }
          }
        }
        else
        {
          rp_interval_set_empty(rp_erep_val(f));
        }
        break; /* RP_EREP_NODE_OP */
    } /* switch */
  }
  else
  {
    result = 1;
  }
  return( result );
}

/* Projection onto every subterm of f                          */
/* b is intersected with the projections onto the variables    */
/* Returns false if an empty interval is computed              */
int rp_erep_project(rp_erep f, rp_box b)
{
  int result = 0;
  if (f!=NULL)
  {
    switch( rp_erep_type(f) )
    {
      case RP_EREP_NODE_CST:
        /* nothing to do */
        result = 1;
        break;

      case RP_EREP_NODE_VAR:
        /* domain := domain inter projection                */
        /* intersection already computed at rp_erep_proj(f) */
        /* then domain := rp_erep_proj(f)                   */
        rp_interval_copy(rp_box_elem(b,rp_erep_var(f)),rp_erep_proj(f));
        if (rp_interval_empty(rp_box_elem(b,rp_erep_var(f))))
        {
          rp_box_set_empty(b);
          result = 0;
        }
        else
        {
          result = 1;
        }
        break; /* RP_EREP_NODE_VAR */

      case RP_EREP_NODE_OP:
        /* top-down recursion: root, left, right */
        result = rp_symbol_project(rp_erep_symb(f))(f);
        if (result)
        {
          result = rp_erep_project(rp_erep_left(f),b);
        }
        if (result && rp_symbol_binary(rp_erep_symb(f)))
        {
          result = rp_erep_project(rp_erep_right(f),b);
        }
        break; /* RP_EREP_NODE_OP */
    } /* switch */
  }
  else
  {
    result = 1;
  }
  return( result );
}

/* Returns true if f is derivable */
int rp_erep_derivable(rp_erep f)
{
  if ((f!=NULL) && (rp_erep_type(f)==RP_EREP_NODE_OP))
  {
    if (!rp_symbol_derivable(rp_erep_symb(f)))
    {
      return( 0 );
    }
    else
    {
      int i;
      for (i=0; i<rp_erep_arity(f); ++i)
      {
        if (!rp_erep_derivable(rp_erep_child(f,i)))
        {
          return( 0 );
        }
      }
    }
  }
  return( 1 );
}

/* Computes all the partial derivatives of f */
int rp_erep_deriv_num(rp_erep f)
{
  if ((f!=NULL) && (rp_erep_type(f)==RP_EREP_NODE_OP) && rp_erep_derivable(f))
  {
    /* derivation of the root node of f */
    if (!rp_symbol_deriv_num(rp_erep_symb(f))(f))
    {
      return( 0 );
    }
    else
    {
      int i;
      for (i=0; i<rp_erep_arity(f); ++i)
      {
        /* recursive derivation through the children */
        if ((rp_erep_type(rp_erep_child(f,i))==RP_EREP_NODE_OP) &&
            (!rp_erep_deriv_num(rp_erep_child(f,i))))
        {
          return( 0 );
        }
      }
    }
  }
  return( 1 );
}

/* df := d(f)/d(v) */
void rp_erep_deriv_symb(rp_erep * df, rp_erep f, int v)
{
  rp_interval i;
  if (f==NULL)
  {
    rp_erep_create(df);
  }
  else
  {
    switch(rp_erep_type(f))
    {
      case RP_EREP_NODE_CST:
        rp_interval_set_point(i,0.0);
        rp_erep_create_cst(df,"",i);      /* d(f)/d(v) := 0 */
        break;

      case RP_EREP_NODE_VAR:
        if (rp_erep_var(f)==v)
        {
          rp_interval_set_point(i,1.0);   /* d(f)/d(v) := 1 */
        }
        else
        {
          rp_interval_set_point(i,0.0);   /* d(f)/d(v) := 0 */
        }
        rp_erep_create_cst(df,"",i);
        break;

      case RP_EREP_NODE_OP:
        /* recursion */
        if (rp_symbol_unary(rp_erep_symb(f)))
        {
          rp_erep du;
          rp_erep dv = NULL;
          rp_erep_deriv_symb(&du,rp_erep_sub(f),v);
          rp_symbol_deriv_symb(rp_erep_symb(f))(df,f,du,dv);
          rp_erep_destroy(&du);
        }
        else
        {
          rp_erep du, dv;
          rp_erep_deriv_symb(&du,rp_erep_left(f),v);
          rp_erep_deriv_symb(&dv,rp_erep_right(f),v);
          rp_symbol_deriv_symb(rp_erep_symb(f))(df,f,du,dv);
          rp_erep_destroy(&du);
          rp_erep_destroy(&dv);
        }
        break;
    }
  }
}

/* Display the set of symbols in debugging mode */
#if RP_DEBUGGING_MODE
void rp_symbol_set_display()
{
  int i;
  printf("\n");
  for(i=0; i<=36; ++i)
  {
    printf("%5s : %2u",rp_symbol_name(i),rp_symbol_property(i));
    printf(" (P%u) ",rp_symbol_priority(i));
    if (rp_symbol_unary(i))  printf(" (unary)  ");
    if (rp_symbol_binary(i)) printf(" (binary) ");
    if (rp_symbol_prefix(i)) printf(" (prefix) ");
    if (rp_symbol_infix(i))  printf(" (infix)  ");
    if (rp_symbol_commutative(i)) printf(" (commute) ");
    printf("\n");
  }
  printf("\n");
}
#endif
