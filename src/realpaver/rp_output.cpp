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
 * rp_output.cpp                                                            *
 ****************************************************************************/

#include "rp_output.h"

// ----------------------------------
// Output filter of problem solutions
// ----------------------------------
// Constructor
rp_ofilter::rp_ofilter(rp_problem * p): _problem(p)
{}

// Destructor
rp_ofilter::~rp_ofilter()
{}

// Copy
rp_ofilter::rp_ofilter(const rp_ofilter& f)
{}

// Copy protection
rp_ofilter& rp_ofilter::operator=(const rp_ofilter& f)
{
  return( *this );
}

// ------------------------------------------------------
// Default output filter of problem solutions in a stream
// ------------------------------------------------------
// Constructor
rp_ofilter_text::rp_ofilter_text(rp_problem * p, std::ostream * os, int nsol):
  rp_ofilter(p),
  _os(os),
  _nsol(nsol)
{}

// Destructor
rp_ofilter_text::~rp_ofilter_text()
{}

// Output of box b for problem p
void rp_ofilter_text::apply_box(const rp_box& b, char * msg)
{
  // Width of the box on the decision variables
  double w = 0.0, vol = 1.0;
  for (int i=0; i<rp_vector_size(rp_problem_vars(*_problem)); ++i)
  {
    if (rp_variable_decision(rp_problem_var(*_problem,i)))
    {
      w = rp_max_num(w,rp_interval_width(rp_box_elem(b,i)));
      vol *= rp_interval_width(rp_box_elem(b,i));
    }
  }

  (*_os) << std::endl << "Box " << (++_nsol);
  if (strlen(msg)>0) (*_os) << " " << msg;
  (*_os) << " " << "[width " << w <<"]";
  (*_os) << " " << "[vol " << vol <<"]";
  if (rp_box_safe(b))
  {
    (*_os) << " [SAFE]";
  }
  if (rp_box_inner(b))
  {
    (*_os) << " [INNER]";
  }
  if (rp_box_interval_safe(b))
  {
    (*_os) << " [INTERVAL SAFE]";
  }
  (*_os) << std::endl;

  for (int i=0; i<rp_vector_size(rp_problem_vars(*_problem)); ++i)
  {
    if (rp_variable_decision(rp_problem_var(*_problem,i)))
    {
      (*_os) << rp_variable_name(rp_problem_var(*_problem,i));
      if (rp_interval_point(rp_box_elem(b,i)))
      {
	(*_os) << " = ";
      }
      else
      {
	(*_os) << " ~ ";
      }

      char tmp[100];
      rp_interval_print(tmp,
			rp_box_elem(b,i),
			16,
			RP_INTERVAL_MODE_BOUND);
      (*_os) << tmp << std::endl;
    }
  }
}

// Copy protection
rp_ofilter_text::rp_ofilter_text(const rp_ofilter_text& f):
  rp_ofilter(f)
{}

rp_ofilter_text& rp_ofilter_text::operator=(const rp_ofilter_text& f)
{
  return( *this );
}


// ------------------------------------------------------
// Default output filter of problem solutions in a stream
// ------------------------------------------------------
// Constructor
rp_ofilter_pstricks::rp_ofilter_pstricks(rp_problem * p, std::ostream * os):
  rp_ofilter(p),
  _os(os)
{}

// Destructor
rp_ofilter_pstricks::~rp_ofilter_pstricks()
{}

// Output of box b for problem p
void rp_ofilter_pstricks::apply_box(const rp_box& b, char * msg)
{
  rp_interval x, y;
  int i, n;

  for (i=0, n=0; i<rp_vector_size(rp_problem_vars(*_problem)) && n<2; ++i)
  {
    if (rp_variable_decision(rp_problem_var(*_problem,i)))
    {
      if ((++n)==1)
      {
	rp_interval_copy(x,rp_box_elem(b,i));
      }
      else
      {
	rp_interval_copy(y,rp_box_elem(b,i));
      }
    }
  }
  if (n==2)
  {
    (*_os) << "\\psframe[linewidth=.2pt]("
	   << rp_binf(x)
	   << ","
	   << rp_binf(y)
	   << ")("
	   << rp_bsup(x)
	   << ","
	   << rp_bsup(y)
	   << ")"
	   << std::endl;
  }
}

// Copy protection
rp_ofilter_pstricks::rp_ofilter_pstricks(const rp_ofilter_pstricks& f):
  rp_ofilter(f)
{}

rp_ofilter_pstricks&
rp_ofilter_pstricks::operator=(const rp_ofilter_pstricks& f)
{
  return( *this );
}


// ------------------------------------------
// Output filter that gathers close solutions
// ------------------------------------------
// Constructor
rp_ofilter_merge::rp_ofilter_merge(rp_problem * p,
				   std::ostream * os, double eps):
  rp_ofilter(p),
  _stack(rp_problem_nvar(*p)),
  _eps(eps),
  _os(os)
{}

// Destructor
rp_ofilter_merge::~rp_ofilter_merge()
{}

// Distance between two boxes to be merged
double rp_ofilter_merge::distance() const
{
  return( _eps );
}

// Merging until quiescence
void rp_ofilter_merge::compact()
{
  int onemerge = 0;

  // From _stack to st
  rp_box_stack st(rp_problem_nvar(*_problem));
  while (!_stack.empty())
  {
    rp_box b = _stack.get();
    st.insert(b);
    _stack.remove();
  }

  // From st to _stack
  while (!st.empty())
  {
    rp_box b = st.get();
    int merge = 0, i = 0;
    while ((!merge) && (i<_stack.size()))
    {
      rp_box sol = _stack.get(i);
      if (this->close_enough(sol,b))
      {
	rp_box_merge(sol,b);
	merge = 1;
      }
      else
      {
	++i;
      }
    }
    if (!merge)
    {
      _stack.insert(b);
    }
    else
    {
      onemerge = 1;
    }
    st.remove();
  }

  if (onemerge)
  {
    this->compact();
  }
}

// Returns true if b1 and b2 can be merged
int rp_ofilter_merge::close_enough(const rp_box& b1, const rp_box& b2)
{
  int closeenough = 1, j = 0;
  while ((closeenough) && (j<rp_box_size(b1)))
  {
    if (rp_variable_decision(rp_problem_var(*_problem,j)) &&
	rp_interval_distance(rp_box_elem(b1,j),
			     rp_box_elem(b2,j))>_eps)
    {
      closeenough = 0;
    }
    else
    {
      ++j;
    }
  }
  return( closeenough );
}


// Output of box b for problem p
void rp_ofilter_merge::apply_box(const rp_box& b, char * msg)
{
  // First try to gather b with another box
  for (int i=0; i<_stack.size(); ++i)
  {
    rp_box sol = _stack.get(i);
    if (this->close_enough(sol,b))
    {
      rp_box_merge(sol,b);
      return;
    }
  }

  // Insertion of a new solution
  _stack.insert(b);
}

// Output of all boxes using filter o
int rp_ofilter_merge::apply_all(rp_ofilter& o)
{
  int sol = 0;
  this->compact();

  while (!_stack.empty())
  {
    ++sol;
    o.apply_box(_stack.get(),"");
    _stack.remove();
  }
  return( sol );
}

// Copy protection
rp_ofilter_merge::rp_ofilter_merge(const rp_ofilter_merge& f):
  rp_ofilter(f),
  _stack(0)
{}

rp_ofilter_merge&
rp_ofilter_merge::operator=(const rp_ofilter_merge& f)
{
  return( *this );
}
