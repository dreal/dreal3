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
 * rp_verification.cpp                                                      *
 ****************************************************************************/

#include "rp_verification.h"

// -----------------------------------------
// Base class for solution existence provers 
// -----------------------------------------
rp_existence_prover::rp_existence_prover()
{}

rp_existence_prover::~rp_existence_prover()
{}

rp_existence_prover::rp_existence_prover(const rp_existence_prover& p)
{}

rp_existence_prover&
rp_existence_prover::operator=(const rp_existence_prover& p)
{
  return( *this );
}

// --------------------------------------------------------------------------
// Solution existence prover using interval satisfaction over canonical boxes
// --------------------------------------------------------------------------
rp_interval_satisfaction_prover::rp_interval_satisfaction_prover(rp_problem * p,
								 int maxbox):
  rp_existence_prover(),
  _problem(p),
  _boxes(rp_problem_nvar(*p)),
  _propag(p),
  _hpropag(p),
  _maxbox(maxbox)
{
  rp_box_create(&_midpoint,rp_problem_nvar(*p));

  rp_test_factory ftest;
  ftest.apply(p,_propag);

  rp_hull_factory fhull;
  fhull.apply(p,_hpropag);

  rp_new(_select,rp_selector_existence,(p));
  rp_new(_split,rp_splitter_bisection,(p));
}

rp_interval_satisfaction_prover::~rp_interval_satisfaction_prover()
{
  rp_box_destroy(&_midpoint);
  rp_delete(_split);
  rp_delete(_select);
}

int rp_interval_satisfaction_prover::prove(rp_box b)
{
  int nbox = 0;
  _boxes.reset();
  _boxes.insert(b);
  while ((!_boxes.empty()) && ((++nbox)<=_maxbox))
  {
    if ( _hpropag.apply(_boxes.get()))
    {
      if (this->existence(_boxes.get()))
      {
	rp_box_set_interval_safe(b);
	return( 1 );
      }
      else if (this->useless_box(_boxes.get()))
      {
	_boxes.remove();
      }
      else
      {
	int i;
	if ((i=_select->apply(_boxes.get()))>=0)
	{
	  _split->apply(_boxes,i);
	}
	else
	{
	  _boxes.remove();
	}
      }
    }
    else
    {
      _boxes.remove();
    }
  }
  return( 0 );
}

int rp_interval_satisfaction_prover::existence(rp_box b)
{
  // Creation of midpoint(b)
  for (int i=0; i<rp_box_size(b); ++i)
  {
    if (rp_interval_canonical(rp_box_elem(b,i)))
    {
      rp_interval_copy(rp_box_elem(_midpoint,i),rp_box_elem(b,i));
    }
    else
    {
      double center = rp_interval_midpoint(rp_box_elem(b,i));
      rp_interval_set(rp_box_elem(_midpoint,i),rp_prev_double(center),center);
    }
  }

  // Proof
  return _propag.apply(_midpoint);
}

int rp_interval_satisfaction_prover::useless_box(rp_box b)
{
  return( rp_box_canonical(b) );
}

rp_interval_satisfaction_prover::rp_interval_satisfaction_prover(const rp_interval_satisfaction_prover& p):
  rp_existence_prover(),
  _problem(p._problem),
  _boxes(rp_problem_nvar(*(p._problem))),
  _propag(p._problem),
  _hpropag(p._problem)
{
  rp_box_create(&_midpoint,rp_problem_nvar(*(p._problem)));
}

rp_interval_satisfaction_prover&
rp_interval_satisfaction_prover::operator=(const rp_interval_satisfaction_prover& p)
{
  return (*this );
}
