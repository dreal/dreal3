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
 * rp_split_selector.cpp                                                    *
 ****************************************************************************/

#include "rp_split_selector.h"

// --------------------------------------------------------
// Class for managing sets of variables in split operations
// --------------------------------------------------------
rp_var_set::rp_var_set(): _a(NULL), _size(0)
{}

rp_var_set::~rp_var_set()
{
  if (_size>0)
  {
    rp_free(_a);
  }
}

int rp_var_set::size() const
{
  return( _size );
}

int rp_var_set::var(int i) const
{
  return( _a[i].index );
}

int rp_var_set::constrained(int i) const
{
  return( _a[i].constrained );
}

double rp_var_set::precision(int i) const
{
  return( _a[i].precision );
}

void rp_var_set::insert(int index, int cstr, double prec)
{
  if (!this->contains(index))
  {
    ++_size;
    if (_size==1)
    {
      rp_malloc(_a,split_var*,sizeof(split_var));
    }
    else
    {
      rp_realloc(_a,split_var*,_size*sizeof(split_var));
    }
    _a[_size-1].index = index;
    _a[_size-1].constrained = cstr;
    _a[_size-1].precision = prec;
  }
}

int rp_var_set::contains(int var) const
{
  for (int i=0; i<_size; ++i)
  {
    if (_a[i].index==var )
    {
      return( 1 );
    }
  }
  return( 0 );
}

rp_var_set::rp_var_set(const rp_var_set& s)
{
  // nothing to do
}

rp_var_set& rp_var_set::operator=(const rp_var_set& s)
{
  // nothing to do
  return( *this );
}

// -----------------------------------------
// Base class for variable choice heuristics
// -----------------------------------------
rp_selector::rp_selector(rp_problem * p):
  _problem(p),
  _var_int_dec(),
  _var_real_dec(),
  _var_int_aux(),
  _var_real_aux()
{
  for (int i=0; i<rp_problem_nvar(*p); ++i)
  {
    rp_variable v = rp_problem_var(*p,i);

    if (rp_variable_decision(v))
    {
      if (rp_variable_integer(v))
      {
	_var_int_dec.insert(i,rp_variable_constrained(v),rp_variable_precision(v));
      }
      else  /* real variable */
      {
	_var_real_dec.insert(i,rp_variable_constrained(v),rp_variable_precision(v));
      }
    }
    else  /* auxiliary variable */
    {
      if (rp_variable_integer(v))
      {
	_var_int_aux.insert(i,rp_variable_constrained(v),rp_variable_precision(v));
      }
      else  /* real variable */
	if (rp_variable_precision(v)<RP_INFINITY)
      {
	_var_real_aux.insert(i,rp_variable_constrained(v),rp_variable_precision(v));
      }
    }
  }
}

rp_selector::~rp_selector()
{}

int rp_selector::hole(rp_box b, int var) const
{
  rp_variable v = rp_problem_var(*_problem,var);
  int n = 0;

  for (int i=0; i<rp_union_card(rp_variable_domain(v)); ++i)
  {
    if (!rp_interval_disjoint(rp_union_elem(rp_variable_domain(v),i),
			      rp_box_elem(b,var)))
    {
      ++n;
    }
  }
  return( (n>=2) );
}


/*
int rp_selector::splitable(rp_box b, int var) const
{
  rp_variable v = rp_problem_var(*_problem,var);
  if (rp_variable_integer(v))
  {
    return( !rp_interval_point(rp_box_elem(b,var)) );
  }
  else
  {
    return( (!rp_interval_canonical(rp_box_elem(b,var))) &&
            ((rp_interval_width(rp_box_elem(b,var))>rp_variable_precision(v)) ||
             (this->hole(b,var))) );
  }
}
*/


int rp_selector::splitable(rp_box b, int var) const
{
  rp_variable v = rp_problem_var(*_problem,var);
  if (rp_variable_integer(v))
  {
    return( !rp_interval_point(rp_box_elem(b,var)) );
  }
  else if (rp_interval_canonical(rp_box_elem(b,var)))
  {
    return( 0 );
  }
  else if (this->hole(b,var))
  {
    return( 1 );
  }
  else if (rp_variable_absolute_precision(v))
  {
    return( rp_interval_width(rp_box_elem(b,var))>2.0*rp_variable_precision(v) );
  }
  else
  {

    double w = rp_interval_width(rp_box_elem(b,var));
    double val = (rp_interval_contains(rp_box_elem(b,var),0.0)) ?
      rp_bsup(rp_box_elem(b,var)) : rp_interval_midpoint(rp_box_elem(b,var));
    return( (w/val) > 2.0*(rp_variable_precision(v)/100.0) );
  }
}



int rp_selector::solution(rp_box b) const
{
  // Inner test
  int inner = 1, i = 0;
  while ((inner) && (i<rp_problem_nctr(*_problem)))
  {
    if (!rp_constraint_inner(rp_problem_ctr(*_problem,i),b))
    {
      inner = 0;
    }
    else
    {
      ++i;
    }
  }
  if (inner)
  {
    rp_box_set_inner(b);
    return( 1 );
  }









  for (int i=0; i<rp_problem_nvar(*_problem); ++i)
  {
    if (this->splitable(b,i))
    {
      return( 0 );
    }
  }
  return( 1 );

















  // integer and decision variables
  for (int i=0; i<_var_int_dec.size(); ++i)
  {
    if (this->splitable(b,_var_int_dec.var(i)))
    {
      return( 0 );
    }
  }

  // real and decision variables
  for (int i=0; i<_var_real_dec.size(); ++i)
  {
    if (this->splitable(b,_var_real_dec.var(i)))
    {
      return( 0 );
    }
  }

  // no decision variable can be split
  return( 1 );
}

int rp_selector::mindom_int_dec(rp_box b) const
{
  double wmin = RP_INFINITY;
  int imin = -1;
  for (int i=0; i<_var_int_dec.size(); ++i)
  {
    int var = _var_int_dec.var(i);
    if (this->splitable(b,var))
    {
      double w;
      if ((w=rp_interval_width(rp_box_elem(b,var)))<wmin)
      {
	wmin = w; imin = var;
      }
    }
  }
  return( imin );
}

int rp_selector::mindom_int_aux(rp_box b) const
{
  double wmin = RP_INFINITY;
  int imin = -1;
  for (int i=0; i<_var_int_aux.size(); ++i)
  {
    int var = _var_int_aux.var(i);
    if (this->splitable(b,var))
    {
      double w;
      if ((w=rp_interval_width(rp_box_elem(b,var)))<wmin)
      {
	wmin = w; imin = var;
      }
    }
  }
  return( imin );
}

int rp_selector::maxdom_real_dec(rp_box b) const
{
  double wmax = 0.0;
  int imax = -1;
  for (int i=0; i<_var_real_dec.size(); ++i)
  {
    int var = _var_real_dec.var(i);
    if (this->splitable(b,var))
    {
      double w;
      if ((w=rp_interval_width(rp_box_elem(b,var)))>wmax)
      {
	wmax = w; imax = var;
      }
    }
  }
  return( imax );
}

int rp_selector::maxdom_real_aux(rp_box b) const
{
  double wmax = 0.0;
  int imax = -1;
  for (int i=0; i<_var_real_aux.size(); ++i)
  {
    int var = _var_real_aux.var(i);
    if (this->splitable(b,var))
    {
      double w;
      if ((w=rp_interval_width(rp_box_elem(b,var)))>wmax)
      {
	wmax = w; imax = var;
      }
    }
  }
  return( imax );
}

int rp_selector::maxctr_int_dec(rp_box b) const
{
  double ctrmax = 0;
  int imax = -1;
  for (int i=0; i<_var_int_dec.size(); ++i)
  {
    int var = _var_int_dec.var(i);
    if (this->splitable(b,var))
    {
      int ctr = _var_int_dec.constrained(i);
      if (ctr>ctrmax)
      {
	ctrmax = ctr; imax = var;
      }
    }
  }
  return( imax );
}

int rp_selector::maxctr_int_aux(rp_box b) const
{
  double ctrmax = 0;
  int imax = -1;
  for (int i=0; i<_var_int_aux.size(); ++i)
  {
    int var = _var_int_aux.var(i);
    if (this->splitable(b,var))
    {
      int ctr = _var_int_aux.constrained(i);
      if (ctr>ctrmax)
      {
	ctrmax = ctr; imax = var;
      }
    }
  }
  return( imax );
}

int rp_selector::maxctr_real_dec(rp_box b) const
{
  double ctrmax = 0;
  int imax = -1;
  for (int i=0; i<_var_real_dec.size(); ++i)
  {
    int var = _var_real_dec.var(i);
    if (this->splitable(b,var))
    {
      int ctr = _var_real_dec.constrained(i);
      if (ctr>ctrmax)
      {
	ctrmax = ctr; imax = var;
      }
    }
  }
  return( imax );
}

int rp_selector::maxctr_real_aux(rp_box b) const
{
  double ctrmax = 0;
  int imax = -1;
  for (int i=0; i<_var_real_aux.size(); ++i)
  {
    int var = _var_real_aux.var(i);
    if (this->splitable(b,var))
    {
      int ctr = _var_real_aux.constrained(i);
      if (ctr>ctrmax)
      {
	ctrmax = ctr; imax = var;
      }
    }
  }
  return( imax );
}

int rp_selector::rr_int_dec(rp_box b) const
{
  // loop i+1,...,N,0,...,i
  int i = rp_box_split(b), n;

  for (n=0; n<rp_problem_nvar(*_problem); ++n)
  {
    // next variable
    if ((++i)>=rp_problem_nvar(*_problem))
    {
      i = 0;
    }
    rp_variable v = rp_problem_var(*_problem,i);

    if (rp_variable_integer(v) &&
	rp_variable_decision(v) &&
	this->splitable(b,i))
    {
      return( i );
    }
  }
  return( -1 );
}

int rp_selector::rr_int_aux(rp_box b) const
{
  // loop i+1,...,N,0,...,i
  int i = rp_box_split(b), n;

  for (n=0; n<rp_problem_nvar(*_problem); ++n)
  {
    // next variable
    if ((++i)>=rp_problem_nvar(*_problem))
    {
      i = 0;
    }
    rp_variable v = rp_problem_var(*_problem,i);

    if (rp_variable_integer(v) &&
	(!rp_variable_decision(v)) &&
	this->splitable(b,i))
    {
      return( i );
    }
  }
  return( -1 );
}

int rp_selector::rr_real_dec(rp_box b) const
{
  // loop i+1,...,N,0,...,i
  int i = rp_box_split(b), n;

  for (n=0; n<rp_problem_nvar(*_problem); ++n)
  {
    // next variable
    if ((++i)>=rp_problem_nvar(*_problem))
    {
      i = 0;
    }
    rp_variable v = rp_problem_var(*_problem,i);

    if (rp_variable_real(v) &&
	rp_variable_decision(v) &&
	this->splitable(b,i))
    {
      return( i );
    }
  }
  return( -1 );
}

int rp_selector::rr_real_aux(rp_box b) const
{
  // loop i+1,...,N,0,...,i
  int i = rp_box_split(b), n;

  for (n=0; n<rp_problem_nvar(*_problem); ++n)
  {
    // next variable
    if ((++i)>=rp_problem_nvar(*_problem))
    {
      i = 0;
    }
    rp_variable v = rp_problem_var(*_problem,i);

    if (rp_variable_real(v) &&
	(!rp_variable_decision(v)) &&
	this->splitable(b,i))
    {
      return( i );
    }
  }
  return( -1 );
}

rp_selector::rp_selector(const rp_selector& s):
  _problem(NULL),
  _var_int_dec(),
  _var_real_dec(),
  _var_int_aux(),
  _var_real_aux()
{}

rp_selector& rp_selector::operator=(const rp_selector& s)
{
  return( * this );
}

// -----------------------------------------------
// Variable choice heuristics
// -----------------------------------------------
rp_selector_decirdom::rp_selector_decirdom(rp_problem * p):
  rp_selector(p)
{}

rp_selector_decirdom::~rp_selector_decirdom()
{}

int rp_selector_decirdom::apply(rp_box b)
{
  int var;
  if (this->solution(b)) return( -1 );
  if ((var=mindom_int_dec(b))>=0)  return( var );
  if ((var=maxdom_real_dec(b))>=0) return( var );
  if ((var=mindom_int_aux(b))>=0)  return( var );
  if ((var=maxdom_real_aux(b))>=0) return( var );
  return( -1 );
}

rp_selector_decirdom::rp_selector_decirdom(const rp_selector_decirdom& s):
  rp_selector(s)
{}

rp_selector_decirdom&
rp_selector_decirdom::operator=(const rp_selector_decirdom& s)
{
  return( *this );
}

// ---------------------------------------------------
// Variable choice heuristics
// Decision variable first, integer first, round-robin
// with robust strategy (diversification)
// ---------------------------------------------------
rp_selector_decirrobust::rp_selector_decirrobust(rp_problem * p,
						 double ratio):
  rp_selector(p),
  _ratio(ratio)
{}

rp_selector_decirrobust::~rp_selector_decirrobust()
{}

int rp_selector_decirrobust::apply(rp_box b)
{
  int var, decfirst;

  if (this->solution(b)) return( -1 );

  if ((rp_box_nvdec(b)==0) ||
      (rp_box_nvdec(b)<=_ratio*(rp_box_nvdec(b)+rp_box_nvaux(b))))
  {
    decfirst = 1;
  }
  else
  {
    decfirst = 0;
  }

  if (decfirst)
  {
    if ((var=rr_int_dec(b))>=0)  return( var );
    if ((var=rr_real_dec(b))>=0) return( var );
    if ((var=rr_int_aux(b))>=0)  return( var );
    if ((var=rr_real_aux(b))>=0) return( var );
  }
  else
  {
    if ((var=rr_int_aux(b))>=0)  return( var );
    if ((var=rr_real_aux(b))>=0) return( var );
    if ((var=rr_int_dec(b))>=0)  return( var );
    if ((var=rr_real_dec(b))>=0) return( var );
  }
  return( -1 );
}

rp_selector_decirrobust::rp_selector_decirrobust(const rp_selector_decirrobust& s):
  rp_selector(s)
{}

rp_selector_decirrobust&
rp_selector_decirrobust::operator=(const rp_selector_decirrobust& s)
{
  return( *this );
}

// -----------------------------------------------
// Variable choice heuristics
// -----------------------------------------------
rp_selector_decirrr::rp_selector_decirrr(rp_problem * p):
  rp_selector(p)
{}

rp_selector_decirrr::~rp_selector_decirrr()
{}

int rp_selector_decirrr::apply(rp_box b)
{
  int var;
  if (this->solution(b)) return( -1 );
  if ((var=rr_int_dec(b))>=0)  return( var );
  if ((var=rr_real_dec(b))>=0) return( var );
  if ((var=rr_int_aux(b))>=0)  return( var );
  if ((var=rr_real_aux(b))>=0) return( var );
  return( -1 );
}

rp_selector_decirrr::rp_selector_decirrr(const rp_selector_decirrr& s):
  rp_selector(s)
{}

rp_selector_decirrr&
rp_selector_decirrr::operator=(const rp_selector_decirrr& s)
{
  return( *this );
}

// -----------------------------------------------
// Variable choice heuristics
// -----------------------------------------------
rp_selector_decircmax::rp_selector_decircmax(rp_problem * p):
  rp_selector(p)
{}

rp_selector_decircmax::~rp_selector_decircmax()
{}

int rp_selector_decircmax::apply(rp_box b)
{
  int var;
  if (this->solution(b)) return( -1 );
  if ((var=maxctr_int_dec(b))>=0)  return( var );
  if ((var=maxctr_real_dec(b))>=0) return( var );
  if ((var=maxctr_int_aux(b))>=0)  return( var );
  if ((var=maxctr_real_aux(b))>=0) return( var );
  return( -1 );
}

rp_selector_decircmax::rp_selector_decircmax(const rp_selector_decircmax& s):
  rp_selector(s)
{}

rp_selector_decircmax&
rp_selector_decircmax::operator=(const rp_selector_decircmax& s)
{
  return( *this );
}

// -----------------------------------------------
// Variable choice heuristics
// -----------------------------------------------
rp_selector_irdom::rp_selector_irdom(rp_problem * p):
  rp_selector(p)
{}

rp_selector_irdom::~rp_selector_irdom()
{}

int rp_selector_irdom::apply(rp_box b)
{
  int var;
  if (this->solution(b)) return( -1 );
  if ((var=mindom_int_dec(b))>=0)  return( var );
  if ((var=mindom_int_aux(b))>=0)  return( var );
  if ((var=maxdom_real_dec(b))>=0) return( var );
  if ((var=maxdom_real_aux(b))>=0) return( var );
  return( -1 );
}

rp_selector_irdom::rp_selector_irdom(const rp_selector_irdom& s):
  rp_selector(s)
{}

rp_selector_irdom&
rp_selector_irdom::operator=(const rp_selector_irdom& s)
{
  return( *this );
}

// -----------------------------------------------
// Variable choice heuristics
// -----------------------------------------------
rp_selector_ircmax::rp_selector_ircmax(rp_problem * p):
  rp_selector(p)
{}

rp_selector_ircmax::~rp_selector_ircmax()
{}

int rp_selector_ircmax::apply(rp_box b)
{
  int var;
  if (this->solution(b)) return( -1 );
  if ((var=maxctr_int_dec(b))>=0)  return( var );
  if ((var=maxctr_int_aux(b))>=0)  return( var );
  if ((var=maxctr_real_dec(b))>=0) return( var );
  if ((var=maxctr_real_aux(b))>=0) return( var );
  return( -1 );
}

rp_selector_ircmax::rp_selector_ircmax(const rp_selector_ircmax& s):
  rp_selector(s)
{}

rp_selector_ircmax&
rp_selector_ircmax::operator=(const rp_selector_ircmax& s)
{
  return( *this );
}

// -----------------------------------------------
// Variable choice heuristics
// -----------------------------------------------
rp_selector_roundrobin::rp_selector_roundrobin(rp_problem * p):
  rp_selector(p)
{}

rp_selector_roundrobin::~rp_selector_roundrobin()
{}

int rp_selector_roundrobin::apply(rp_box b)
{
  if (this->solution(b))
  {
    return( -1 );
  }

  // loop i+1,...,N,0,...,i, at least one splitable domain
  int i = rp_box_split(b);
  for ( ;; )
  {
    if ((++i)>=rp_problem_nvar(*_problem))
    {
      i = 0;
    }
    if (this->splitable(b,i) || (i==rp_box_split(b)))
    {
      return( i );
    }
  }
}

rp_selector_roundrobin::rp_selector_roundrobin(const rp_selector_roundrobin& s):
  rp_selector(s)
{}

rp_selector_roundrobin&
rp_selector_roundrobin::operator=(const rp_selector_roundrobin& s)
{
  return( *this );
}

// -----------------------------------------------
// Variable choice heuristics
// -----------------------------------------------
rp_selector_existence::rp_selector_existence(rp_problem * p):
  rp_selector(p)
{}

rp_selector_existence::~rp_selector_existence()
{}

int rp_selector_existence::apply(rp_box b)
{
  // Selection of largest domain among all the variables
  int maxi = -1;
  double wmaxi = 0.0;
  for (int i=0; i<rp_box_size(b); ++i)
  {
    if (!rp_interval_canonical(rp_box_elem(b,i)))
    {
      double wi = rp_interval_width(rp_box_elem(b,i));
      if ((maxi==-1) || (wi>wmaxi))
      {
	wmaxi = wi;
	maxi = i;
      }
    }
  }
  return( maxi );
}

rp_selector_existence::rp_selector_existence(const rp_selector_existence& s):
  rp_selector(s)
{}

rp_selector_existence&
rp_selector_existence::operator=(const rp_selector_existence& s)
{
  return( *this );
}
