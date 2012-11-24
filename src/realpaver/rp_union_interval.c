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
 * rp_union_interval.c                                                      *
 ****************************************************************************/

#include <string.h>
#include "rp_union_interval.h"

//extern void * memcpy(void *, const void *, size_t) rp_throw;

/* u := src */
void rp_union_copy(rp_union_interval u, rp_union_interval src)
{
  if ((rp_union_size(u)!=rp_union_card(src)) && (rp_union_size(u)!=0))
  {
    rp_free(rp_union_ptr(u));
  }
  rp_malloc(rp_union_ptr(u),rp_interval*,rp_union_card(src) *
	    sizeof(rp_interval));
  rp_union_card(u) = rp_union_card(src);
  rp_union_unused(u) = 0;
  memcpy(rp_union_ptr(u),
	 rp_union_ptr(src),
	 rp_union_card(u)*sizeof(rp_interval));
}

/* Creation of an empty union */
void rp_union_create(rp_union_interval* u)
{
  rp_union_ptr(*u) = NULL;
  rp_union_card(*u) = rp_union_unused(*u) = 0;
}

/* Destruction */
void rp_union_destroy(rp_union_interval* u)
{
  if (rp_union_size(*u)!=0)
  {
    rp_free(rp_union_ptr(*u));
    rp_union_card(*u) = rp_union_unused(*u) = 0;
  }
}

/* Creation of an empty union and allocation of size intervals */
void rp_union_create_size(rp_union_interval* u, int size)
{
  if (size!=0)
  {
    rp_malloc(rp_union_ptr(*u),rp_interval*,size*sizeof(rp_interval));
  }
  else
  {
    rp_union_ptr(*u) = NULL;
  }
  rp_union_card(*u)   = 0;
  rp_union_unused(*u) = size;
}

/* Allocation of size more intervals */
void rp_union_enlarge_size(rp_union_interval u, int size)
{
  if( rp_union_size(u)==0 )
  {
    rp_malloc(rp_union_ptr(u),rp_interval*,size*sizeof(rp_interval));
    rp_union_card(u)   = 0;
    rp_union_unused(u) = size;
  }
  else
  {
    rp_union_unused(u) += size;
    rp_realloc(rp_union_ptr(u),rp_interval*,
	       rp_union_size(u)*sizeof(rp_interval));
  }
}

/* To print u on out                                           */
/* mode == RP_INTERVAL_MODE_BOUND    -> [a,b]                */     
/* mode == RP_INTERVAL_MODE_MID  -> mid + [-error,error] */
void rp_union_display(FILE *out, rp_union_interval u, int digits, int mode)
{
  if( rp_union_card(u)==0 )
  {
    fprintf(out,"empty");
  }
  else
  {
    int i;
    fprintf(out,"{");
    rp_interval_display(out,rp_union_elem(u,0),digits,mode);
    for( i=1; i<rp_union_card(u); i++ )
    {
      fprintf(out,",");
      rp_interval_display(out,rp_union_elem(u,i),digits,mode);
    }
    fprintf(out,"}");
  }
}

/* Returns true if u1==u2 */
int rp_union_equal(rp_union_interval u1, rp_union_interval u2)
{
  if (rp_union_card(u1)==rp_union_card(u2))
  {
    int i;
    for (i=0; i<rp_union_card(u1); ++i)
    {
      if (rp_interval_diff(rp_union_elem(u1,i),rp_union_elem(u2,i)))
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

/* Returns true if u1!=u2 */
int rp_union_diff(rp_union_interval u1, rp_union_interval u2)
{
  if (rp_union_card(u1)==rp_union_card(u2))
  {
    int i;
    for (i=0; i<rp_union_card(u1); ++i)
    {
      if (rp_interval_diff(rp_union_elem(u1,i),rp_union_elem(u2,i)))
      {
	return( 1 );
      }
    }
    return( 0 );
  }
  else
  {
    return( 1 );
  }
}

/* Returns true if small is included in large */
int rp_union_included(rp_union_interval small, rp_union_interval large)
{
  int i, j, found;
  /* true if for every interval of small there exists an interval
     of large that is a superset */
  for (i=0; i<rp_union_card(small); ++i)
  {
    found = j = 0;
    while ((j<rp_union_card(large)) && (!found))
    {
      if (rp_interval_included(rp_union_elem(small,i),
			       rp_union_elem(large,j)))
      {
	found = 1;
      }
      else
      {
	++j;
      }
    }
    if (!found)
    {
      return( 0 );
    }
  }
  return( 1 );
}

/* Returns true if x belongs to u */
int rp_union_contains(rp_union_interval u, double x)
{
  int k;
  for( k=0; k<rp_union_card(u); ++k )
  {
    if( rp_interval_contains(rp_union_elem(u,k),x) )
    {
      return( 1 );
    }
  }
  return( 0 );
}

/* Returns true if x is strictly greater than all points of u */
int rp_union_strictly_greater(rp_union_interval u, double x)
{
  return( x > rp_bsup(rp_union_elem(u,rp_union_card(u)-1)) );
}

/* Returns true if x is strictly smaller than all points of u */
int rp_union_strictly_smaller(rp_union_interval u, double x)
{
  return( x < rp_binf(rp_union_elem(u,0)) );
}

/* Returns the smallest point of u greater than x */
double rp_union_next_double(rp_union_interval u, double x)
{
  int i;
  for (i=0; i<rp_union_card(u); ++i)
  {
    if (x <= rp_binf(rp_union_elem(u,i)))        /* x:    |            */
    {                                            /* u[i]:    |-------| */
      return( rp_binf(rp_union_elem(u,i)) );     /*          ^         */
    }
    else if (x <= rp_bsup(rp_union_elem(u,i)))   /* u[i]:    |-------| */
    {                                            /* x:           |     */
      return( x );                               /*              ^     */
    }
    /* else x > u[i] then continue */
  }
  return( RP_INFINITY );
}

/* Returns the greatest point of u smaller than x */
double rp_union_prev_double (rp_union_interval u, double x)
{
  int i;
  for (i=rp_union_card(u)-1; i>=0; --i)
  {
    if (x >= rp_bsup(rp_union_elem(u,i)))        /* x:               | */
    {                                            /* u[i]: |-------|    */
      return( rp_bsup(rp_union_elem(u,i)) );     /*               ^    */
    }
    else if (x >= rp_binf(rp_union_elem(u,i)))   /* u[i]:    |-------| */
    {                                            /* x:           |     */
      return( x );                               /*              ^     */
    }
    /* else x < u[i] then continue */
  }
  return( -RP_INFINITY );
}

/* Returns the index of the largest interval in u */
int rp_union_max_element(rp_union_interval u)
{
  int i, wi, maxi, wmaxi;
  maxi = 0;
  wmaxi = rp_interval_width(rp_union_elem(u,0));
  for (i=1; i<rp_union_card(u); ++i)
  {
    if ((wi = rp_interval_width(rp_union_elem(u,i)))>wmaxi)
    {
      maxi = i;
      wmaxi = wi;
    }
  }
  return( maxi );
}

/* u := empty set */
void rp_union_set_empty(rp_union_interval u)
{
  if (rp_union_size(u)!=0)
  {
    rp_free(rp_union_ptr(u));
    rp_union_card(u) = rp_union_unused(u) = 0;
  }
}

/* u := empty set and fix a size */
void rp_union_set_empty_size(rp_union_interval u, int size)
{
  if (rp_union_size(u)!=size)
  {
    if (rp_union_size(u)!=0)
    {
      rp_free(rp_union_ptr(u));
    }
    if (size!=0)
    {
      rp_malloc(rp_union_ptr(u),rp_interval*,size*sizeof(rp_interval));
    }
  }
  rp_union_card(u)   = 0;
  rp_union_unused(u) = size;
}

/* i := interval hull ( u ) */
void rp_union_hull(rp_interval i, rp_union_interval u)
{
  if (rp_union_card(u)!=0)
  {
    rp_binf(i) = rp_binf(rp_union_elem(u,0));
    rp_bsup(i) = rp_bsup(rp_union_elem(u,rp_union_card(u)-1));
  }
  else
  {
    rp_interval_set_empty(i);
  }
}

/* Insertion of i in position u[j] such that card(u)>=j+1 */
/* Shift to the right of all the intervals u[j],...       */
void rp_union_insert_position(rp_union_interval u, int j, rp_interval i)
{
  int k;

  /* enlargement if not enough size */
  if (rp_union_unused(u)==0)
  {
    rp_union_enlarge_size(u,1);
  }

  /* hole making in u */
  for( k=rp_union_card(u); k>j; --k )
  {
    rp_interval_copy(rp_union_elem(u,k),rp_union_elem(u,k-1));
  }
  ++ rp_union_card(u);
  -- rp_union_unused(u);

  /* copy of i */
  rp_interval_copy(rp_union_elem(u,j),i);
}

/* Deletion of the interval u[j] */
void rp_union_delete_position(rp_union_interval u, int j)
{
  if (j < rp_union_card(u)-1)
  {
    memcpy(&(rp_union_elem(u,j)),
           &(rp_union_elem(u,j+1)),
           (rp_union_card(u)-j-1)*sizeof(rp_interval));
  }
  -- rp_union_card(u);
  ++ rp_union_unused(u);
}

/* Insertion u := u union i */
void rp_union_insert(rp_union_interval u, rp_interval i)
{
  int j;
  rp_interval aux;

  if (rp_interval_empty(i))
  {
    return;
  }

  rp_interval_copy(aux,i);

  /* the problem is to insert aux at the right place such that all the intervals
     are sorted and disjoints */
  /* loop invariant: result := (u union aux), and aux is strictly greater than
     all the intervals u[0],...u[j-1] */
  for( j=0 ;; )
  {
    /* Management of aux wrt. u[j] */
    if( j==rp_union_card(u) )                               /* insertion in last place */
    {
      if( rp_union_unused(u)==0 )
      {
        rp_union_enlarge_size(u,1);
      }
      rp_interval_copy(rp_union_elem(u,j),aux);
      ++ rp_union_card(u);
      -- rp_union_unused(u);
      return;
    }
    else if( rp_bsup(aux) < rp_binf(rp_union_elem(u,j)) )   /* insertion in place j */
    {
      rp_union_insert_position(u,j,aux);
      return;
    }
    else if( rp_interval_included(aux,rp_union_elem(u,j)) ) /* aux is included in u */
    {
      return;
    }
    else if( rp_interval_included(rp_union_elem(u,j),aux) ) /* aux contains u[j] */
    {                                                       /* then u[j] is removed */
      rp_union_delete_position(u,j);
    }
    else if( rp_binf(aux) > rp_bsup(rp_union_elem(u,j)) )   /* aux is after u[j] */
    {
      ++j;
    }
    else if( (rp_binf(rp_union_elem(u,j)) >= rp_binf(aux)) &&  /*  aux : |--------|    */
             (rp_bsup(aux) <= rp_bsup(rp_union_elem(u,j))) )   /* u[j] :    |--------| */
    {
      rp_binf(rp_union_elem(u,j)) = rp_binf(aux);              /* u[j] : |-----------| */
      return;
    }
    else if( (rp_binf(rp_union_elem(u,j)) <= rp_binf(aux)) &&  /*  aux :    |--------| */
             (rp_bsup(aux) >= rp_bsup(rp_union_elem(u,j))) )   /* u[j] : |--------|    */
    {
      rp_binf(aux) = rp_binf(rp_union_elem(u,j));              /*  aux : |-----------| */
      rp_union_delete_position(u,j);                           /* u[j] is removed      */
    }
  }
}

/* Insertion u := u union v */
void rp_union_insert_uu(rp_union_interval u, rp_union_interval v)
{
  int i;
  for (i=0; i<rp_union_card(v); ++i)
  {
    rp_union_insert(u,rp_union_elem(v,i));
  }
}

/* Intersection u := u inter i                */
/* Returns false if the intersection is empty */
int rp_union_inter(rp_union_interval u, rp_interval i)
{
  int j;
  rp_interval aux;

  if (rp_interval_empty(i))
  {
    rp_union_set_empty(u);
    return 0;
  }

  rp_interval_copy(aux,i);

  for( j=0 ;; )
  {
    if( j==rp_union_card(u) )                           /* intersection completed */
    {
      return( rp_union_card(u)>0 );
    }

    else if( rp_bsup(aux)<rp_binf(rp_union_elem(u,j)) ) /*  aux: |-----|            */
    {                                                   /* u[j]:          |-----|   */
      rp_union_unused(u) += (rp_union_card(u)-j);       /* delete u[j], u[j+1], ... */
      rp_union_card(u) = j;
      return( rp_union_card(u)>0 );
    }

    else if( rp_binf(aux)>rp_bsup(rp_union_elem(u,j)) ) /*  aux:          |-----|   */
    {                                                   /* u[j]: |-----|            */
      rp_union_delete_position(u,j);                    /* delete u[j]              */
    }

    else if( rp_interval_included(aux,rp_union_elem(u,j)) ) /* aux:    |----|       */
    {                                                       /* u[j]: |--------|     */
      rp_union_unused(u) += (rp_union_card(u)-1);           /* result := aux        */
      rp_union_card(u) = 1;
      rp_interval_copy(rp_union_elem(u,0),aux);
      return( 1 );
    }
    else if( rp_interval_included(rp_union_elem(u,j),aux) ) /* aux:  |--------|   */
    {                                                       /* u[j]:   |----|     */
      ++j;                                                  /* keep u[j] */
    }
    else if( rp_bsup(aux)<=rp_bsup(rp_union_elem(u,j)) )    /*  aux: |--------|    */
    {                                                       /* u[j]:    |--------| */
      rp_bsup(rp_union_elem(u,j)) = rp_bsup(aux);           /* u[j]:=   |-----|    */
      rp_union_unused(u) += (rp_union_card(u)-j-1);
      rp_union_card(u) = j+1;
      return( 1 );
    }

    else if( rp_bsup(aux)>=rp_bsup(rp_union_elem(u,j)) )   /*  aux:     |--------| */
    {                                                      /* u[j]:  |--------|    */
      rp_binf(rp_union_elem(u,j)) = rp_binf(aux);          /* u[j]:=    |-----|    */
      ++j;
    }
  }
}

/* Intersection u := u inter v and returns false if empty */
int rp_union_inter_uu (rp_union_interval u, rp_union_interval v)
{
  int i;
  rp_union_interval aux, save;

  /* save is a copy of u */
  rp_union_create(&save);
  rp_union_copy(save,u);

  /* u := empty */
  rp_union_set_empty(u);

  for (i=0; i<rp_union_card(v); ++i)
  {
    /* aux is used locally */
    rp_union_create(&aux);

    /* intersection u with v[i] */
    rp_union_copy(aux,save);
    rp_union_inter(aux,rp_union_elem(v,i));

    /* insertion of the intersection in u */
    rp_union_insert_uu(u,aux);

    rp_union_destroy(&aux);
  }
  rp_union_destroy(&save);
  return( rp_union_card(u)>0 );
}

/* Intersection i := hull( i inter u ) and returns false if empty */
int rp_union_inter_iu(rp_interval i, rp_union_interval u)
{
  int j = 0, k, found = 0;

  /* Reduce the left bound of i */
  while ((j<rp_union_card(u)) && (!found))
  {
    if (rp_binf(i)>rp_bsup(rp_union_elem(u,j)))        /*    i:       |----  */
    {                                                  /* u[j]: ----|        */
      ++j;
    }
    else if (rp_binf(i)<rp_binf(rp_union_elem(u,j)))   /* i:    |----       */
    {                                                  /* u[j]:        |---- */
      rp_binf(i) = rp_binf(rp_union_elem(u,j));
      found = 1;
    }
    else
    {
      /* the left bound belongs to u --> no reduction */
      found = 1;
    }
  }

  if (!found)
  {
    rp_interval_set_empty(i);
    return( 0 );
  }
  else
  {
    /* Reduce the right bound of i from u[card-1] to u[j] */
    /* The resulting interval must not be empty since the left */
    /* bound has been found                                    */
    k = rp_union_card(u) -1;
    found = 0;
    while ((k>=j) && (!found))
    {
      if (rp_bsup(i)<rp_binf(rp_union_elem(u,k)))       /*    i: -----|      */
      {                                                 /* u[k]:        |--- */
	--k;
      }
      else if (rp_bsup(i)>rp_bsup(rp_union_elem(u,k)))  /* i:        ------| */
      {                                                 /* u[k]:  -----|     */
	rp_bsup(i) = rp_bsup(rp_union_elem(u,k));
	found = 1;
      }
      else
      {
	/* the right bound belongs to u --> no reduction */
	found = 1;
      }
    }
    return( 1 );
  }
}

/* result := i1 / i2 using the extended interval division */
/* returns the cardinal of result                         */
int rp_interval_extended_div (rp_union_interval result,
			      rp_interval i1, rp_interval i2)
{
  if ((rp_binf(i2)<0.0) && (rp_bsup(i2)>0.0))
  {
    if (rp_binf(i1)>0.0)
    {
      rp_interval aux1, aux2;
      rp_binf(aux1) = (-RP_INFINITY);
      RP_ROUND_UPWARD();
      rp_bsup(aux1) = rp_binf(i1)/rp_binf(i2);

      RP_ROUND_DOWNWARD();
      rp_binf(aux2) = rp_binf(i1)/rp_bsup(i2);
      rp_bsup(aux2) = RP_INFINITY;

      rp_union_set_empty_size(result,2);
      rp_union_insert(result,aux1);
      rp_union_insert(result,aux2);
    }
    else if (rp_bsup(i1)<0.0)
    {
      rp_interval aux1, aux2;
      rp_binf(aux1) = (-RP_INFINITY);
      RP_ROUND_UPWARD();
      rp_bsup(aux1) = rp_bsup(i1)/rp_bsup(i2);

      RP_ROUND_DOWNWARD();
      rp_binf(aux2) = rp_bsup(i1)/rp_binf(i2);
      rp_bsup(aux2) = RP_INFINITY;

      rp_union_set_empty_size(result,2);
      rp_union_insert(result,aux1);
      rp_union_insert(result,aux2);
    }
    else
    {
      rp_interval aux;
      rp_interval_set_real_line(aux);
      rp_union_set_empty_size(result,1);
      rp_union_insert(result,aux);
    }
  }
  else
  {
    /* standard division */
    rp_interval aux;
    rp_interval_div(aux,i1,i2);
    rp_union_set_empty_size(result,1);
    rp_union_insert(result,aux);
  }
  return rp_union_card(result);
}
