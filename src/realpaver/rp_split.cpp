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
 * rp_split.cpp                                                             *
 ****************************************************************************/

#include "rp_split.h"

// --------------------------
// Class for domain splitting
// --------------------------
rp_splitter::rp_splitter(rp_problem * p):
  _problem(p)
{}

rp_splitter::~rp_splitter()
{}

void rp_splitter::observe(rp_box b, int var)
{
  rp_box_set_split(b,var);
  if (rp_variable_decision(rp_problem_var(*_problem,var)))
  {
    ++rp_box_nvdec(b);
  }
  else
  {
    ++rp_box_nvaux(b);
  }
}

int rp_splitter::integer_hole(rp_interval dom,
			      rp_union_interval init_dom,
			      rp_interval i1,
			      rp_interval i2)
{
  return( 0 );
}

int rp_splitter::real_hole(rp_interval dom,
			   rp_union_interval init_dom,
			   rp_interval i1,
			   rp_interval i2)
{
  return 0;
  rp_union_interval aux;
  int result = 0;
  rp_union_create(&aux);

  // domain inter initial_domain
  rp_union_copy(aux,init_dom);
  rp_union_inter(aux,dom);

  if (rp_union_card(aux)>=2)
  {
    int midhole = (rp_union_card(aux)-2) / 2;

    rp_binf(i1) = rp_binf(rp_union_elem(aux,0));
    rp_bsup(i1) = rp_bsup(rp_union_elem(aux,midhole));

    rp_binf(i2) = rp_binf(rp_union_elem(aux,midhole+1));
    rp_bsup(i2) = rp_bsup(rp_union_elem(aux,rp_union_card(aux)-1));

    result = 1;
  }

  rp_union_destroy(&aux);
  return( result );
}

rp_splitter::rp_splitter(const rp_splitter& ds):
  _problem(NULL)
{}

rp_splitter& rp_splitter::operator=(const rp_splitter& ds)
{
  return( *this );
}

// -------------------------------------------
// Class for domain splitting
// Enumeration of integer, bisection of reals
// -------------------------------------------
rp_splitter_mixed::rp_splitter_mixed(rp_problem * p):
  rp_splitter(p)
{}

rp_splitter_mixed::~rp_splitter_mixed()
{}

void rp_splitter_mixed::apply(rp_box_set& bs, int var)
{
  rp_interval i1, i2;
  rp_box b1 = bs.remove_insert();
  this->observe(b1,var);
  rp_box b2 = bs.insert(b1);

  if (rp_variable_integer(rp_problem_var(*_problem,var)))
  {
    if (this->integer_hole(rp_box_elem(b1,var),
			   rp_variable_domain(rp_problem_var(*_problem,var)),
			   i1,i2))
    {
      rp_interval_copy(rp_box_elem(b1,var),i1);
      rp_interval_copy(rp_box_elem(b2,var),i2);
    }
    else  // no hole found
    {
      // Integer variable: [a,b] --> [a+1,b] and [a,a]
      ++rp_binf(rp_box_elem(b1,var));
      rp_bsup(rp_box_elem(b2,var)) = rp_binf(rp_box_elem(b2,var));
    }
  }
  else
  {
    if (this->real_hole(rp_box_elem(b1,var),
			rp_variable_domain(rp_problem_var(*_problem,var)),
			i1,i2))
    {
      rp_interval_copy(rp_box_elem(b1,var),i1);
      rp_interval_copy(rp_box_elem(b2,var),i2);
    }
    else
    {
      // Real variable: [a,b] --> [center,b] and [a,center]
      rp_binf(rp_box_elem(b1,var)) =
	rp_bsup(rp_box_elem(b2,var)) =
	  rp_interval_midpoint(rp_box_elem(b1,var));
    }
  }
}

rp_splitter_mixed::rp_splitter_mixed(const rp_splitter_mixed& ds): rp_splitter(ds)
{}

rp_splitter_mixed&
rp_splitter_mixed::operator=(const rp_splitter_mixed& ds)
{
  return( *this );
}

// -------------------------------------------
// Class for domain splitting
// Bisection of every domain
// -------------------------------------------
rp_splitter_bisection::rp_splitter_bisection(rp_problem * p):
  rp_splitter(p)
{}

rp_splitter_bisection::~rp_splitter_bisection()
{}

void rp_splitter_bisection::apply(rp_box_set& bs, int var)
{
  rp_box b1 = bs.remove_insert();
  this->observe(b1,var);
  rp_box b2 = bs.insert(b1);

  // [a,b] --> [center,b] and [a,center]
  double center = rp_interval_midpoint(rp_box_elem(b1,var));

  if (rp_variable_integer(rp_problem_var(*_problem,var)))
  {
    rp_binf(rp_box_elem(b1,var)) = (int)ceil(center);
    rp_bsup(rp_box_elem(b2,var)) = (int)floor(center);

    if (rp_binf(rp_box_elem(b1,var))==rp_bsup(rp_box_elem(b2,var)))
    {
      -- rp_bsup(rp_box_elem(b2,var));
    }
  }
  else
  {
    rp_binf(rp_box_elem(b1,var)) = rp_bsup(rp_box_elem(b2,var)) = center;
  }

}

rp_splitter_bisection::rp_splitter_bisection(const rp_splitter_bisection& ds): rp_splitter(ds)
{}

rp_splitter_bisection&
rp_splitter_bisection::operator=(const rp_splitter_bisection& ds)
{
  return( *this );
}
