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
 * rp_operator_factory.cpp                                                  *
 ****************************************************************************/

#include "rp_operator_factory.h"

// ------------------------------------------------
// Creation of operators from problems
// ------------------------------------------------
// Constructor
rp_operator_factory::rp_operator_factory()
{}

// Destructor
rp_operator_factory::~rp_operator_factory()
{}

// Creation of a set of operators from p and insertion in the propagator
void rp_operator_factory::apply(rp_problem * p, rp_propagator& propag)
{
  rp_vector vec;
  rp_vector_create_basic(&vec);
  this->build(*p,vec);
  for (int i=0; i<rp_vector_size(vec); ++i)
  {
    propag.insert((rp_operator*)rp_vector_elem(vec,i));
  }
  rp_vector_destroy(&vec);
}

// Creation of a set of operators from p and insertion in the vector
void rp_operator_factory::build(const rp_problem& p, rp_vector& vec)
{
  /* For every constraint */
  for (int i=0; i<rp_problem_nctr(p); ++i)
  {
    this->build(p,rp_problem_ctr(p,i),vec);
  }
}

// Creation of a set of operators from c and insertion in the vector
void rp_operator_factory::build(const rp_problem& p,
				const rp_constraint& c, rp_vector& vec)
{
  switch( rp_constraint_type(c) )
  {
  case RP_CONSTRAINT_NUMERICAL:
    this->build(p,rp_constraint_num(c),vec);
    break;

  case RP_CONSTRAINT_CONDITIONAL:
    this->build(p,rp_constraint_cond(c),vec);
    break;

  case RP_CONSTRAINT_PIECEWISE:
    this->build(p,rp_constraint_piece(c),vec);
    break;
  }
}

// Creation of a set of operators from c and insertion in the vector
void rp_operator_factory::build(const rp_problem& p,
				const rp_ctr_num& c, rp_vector& vec)
{
  // For every variable occurring in the constraint
  for (int i=0; i<rp_ctr_num_arity(c); ++i)
  {
    this->build(p,c,rp_ctr_num_var(c,i),vec);
  }
}

// Creation of a set of operators from c and insertion in the vector
void rp_operator_factory::build(const rp_problem& p,
				const rp_ctr_cond& c, rp_vector& vec)
{
  // creation of the operators associated to the conclusion
  rp_vector vconc;
  rp_vector_create_basic(&vconc);
  for (int i=0; i<rp_ctr_cond_concsize(c); ++i)
  {
    this->build(p,rp_ctr_cond_conc_elem(c,i),vconc);
  }

  // creation of conditional operators
  for (int i=0; i<rp_vector_size(vconc); ++i)
  {
    rp_operator_cond * o;
    rp_new(o,rp_operator_cond,(c,(rp_operator*)rp_vector_elem(vconc,i)));
    rp_vector_insert(vec,o);
  }

  // destruction of vector
  rp_vector_destroy(&vconc);
}

// Creation of a set of operators from c and insertion in the vector
void rp_operator_factory::build(const rp_problem& p,
				const rp_ctr_piecewise& c, rp_vector& vec)
{
  // processing of each piece
  for (int i=0; i<rp_ctr_piecewise_arity(c); ++i)
  {
    // creation of the operators associated to the constraints
    // of the i-th piece
    rp_vector vconc;
    rp_vector_create_basic(&vconc);
    for (int j=0; j<rp_ctr_piecewise_elem_size(c,i); ++j)
    {
      this->build(p,rp_ctr_piecewise_elem_ctrnum(c,i,j),vconc);
    }

    // creation of piecewise operators
    for (int j=0; j<rp_vector_size(vconc); ++j)
    {
      rp_operator_condvar * o;
      rp_new(o,rp_operator_condvar,(rp_ctr_piecewise_var(c),
				    rp_ctr_piecewise_elem_dom(c,i),
				    (rp_operator*)rp_vector_elem(vconc,j)));
      rp_vector_insert(vec,o);
    }

    // destruction of vector
    rp_vector_destroy(&vconc);
  }

  // creation of an additional operator for the whole constraint
  rp_operator_piecewise * op;
  rp_new(op,rp_operator_piecewise,(c));
  rp_vector_insert(vec,op);
}

// Creation of a set of operators from c and insertion in the vector
void rp_operator_factory::build(const rp_problem& p,
				const rp_ctr_num& c, int var, rp_vector& vec)
{
  // no default implementation
}

// Copy
rp_operator_factory::rp_operator_factory(const rp_operator_factory& g)
{}

// Copy protection
rp_operator_factory&
rp_operator_factory::operator=(const rp_operator_factory& g)
{
  return( *this );
}

// ------------------------------------------------
// Factory of operators managing domains with holes
// ------------------------------------------------
// Constructor
rp_domain_factory::rp_domain_factory():
  rp_operator_factory()
{}

// Destructor
rp_domain_factory::~rp_domain_factory()
{}

// Creation of a set of operators from p and insertion in the vector
void rp_domain_factory::build(const rp_problem& p, rp_vector& vec)
{
  /* For every integer variable or every variable whose domain is a union */
  /* with cardinal >= 2 creation of a domain operator */
  for (int j=0; j<rp_problem_nvar(p); ++j)
  {
    rp_variable v = rp_problem_var(p,j);
    if ((rp_variable_integer(v)) ||
        (rp_union_card(rp_variable_domain(v))>1))
    {
      rp_operator_domain * o;
      rp_new(o,rp_operator_domain,(v,j));
      rp_vector_insert(vec,o);
    }
  }
}

// Copy
rp_domain_factory::rp_domain_factory(const rp_domain_factory& g):
  rp_operator_factory(g)
{
  // --> nothing to do
}

// Copy
rp_domain_factory&
rp_domain_factory::operator=(const rp_domain_factory& g)
{
  // --> nothing to do
  return( *this );
}

// ----------------------------------
// Propagation using hull consistency
// ----------------------------------
// Constructor
rp_hull_factory::rp_hull_factory():
  rp_operator_factory()
{}

// Destructor
rp_hull_factory::~rp_hull_factory()
{}

// Creation of a set of operators from p and insertion in vop
void rp_hull_factory::build(const rp_problem& p,
			    const rp_ctr_num& c, rp_vector& vec)
{
  rp_operator * o = NULL;
  switch( rp_ctr_num_rel(c) )
  {
  case RP_RELATION_EQUAL:
    rp_new(o,rp_operator_hull_eq,(c));
    break;

  case RP_RELATION_SUPEQUAL:
    rp_new(o,rp_operator_hull_sup,(c));
    break;

  case RP_RELATION_INFEQUAL:
    rp_new(o,rp_operator_hull_inf,(c));
    break;
  }
  rp_vector_insert(vec,o);
}

// Copy
rp_hull_factory::rp_hull_factory(const rp_hull_factory& g):
  rp_operator_factory(g)
{
  // --> nothing to do
}

// Copy
rp_hull_factory&
rp_hull_factory::operator=(const rp_hull_factory& g)
{
  // --> nothing to do
  return( *this );
}

// ---------------------------------
// Propagation using box consistency
// ---------------------------------
// Constructor
rp_box_factory::rp_box_factory(double improve):
  rp_operator_factory(), _improve(improve)
{}

// Destructor
rp_box_factory::~rp_box_factory()
{}

// Creation of a set of operators from p and insertion in the vector
void rp_box_factory::build(const rp_problem& p,
			   const rp_ctr_num& c, int var, rp_vector& vec)
{
  rp_operator * o = NULL;

  // the precision of the variable is used as a stopping parameter
  // of the dichotomous search
  double eps = rp_variable_precision(rp_problem_var(p,var));

  switch( rp_ctr_num_relfunc(c) )
  {
  case RP_RELATION_EQUAL:
    rp_new(o,rp_operator_box_eq,(rp_ctr_num_func(c),var,_improve,eps));
    break;

  case RP_RELATION_SUPEQUAL:
    rp_new(o,rp_operator_box_sup,(rp_ctr_num_func(c),var,_improve,eps));
    break;

  case RP_RELATION_INFEQUAL:
    rp_new(o,rp_operator_box_inf,(rp_ctr_num_func(c),var,_improve,eps));
    break;
  }
  rp_vector_insert(vec,o);
}

// Copy
rp_box_factory::rp_box_factory(const rp_box_factory& g):
  rp_operator_factory(g)
{
  // --> nothing to do
}

// Copy
rp_box_factory&
rp_box_factory::operator=(const rp_box_factory& g)
{
  // --> nothing to do
  return( *this );
}

// ---------------------------------------------------
// Combination of box consistency and hull consistency
// ---------------------------------------------------
// Constructor
rp_hybrid_factory::rp_hybrid_factory(double improve):
  rp_operator_factory(), _improve(improve)
{}

// Destructor
rp_hybrid_factory::~rp_hybrid_factory()
{}

// Creation of a set of operators from p and insertion in the vector
void rp_hybrid_factory::build(const rp_problem& p,
			      const rp_ctr_num& c, rp_vector& vec)
{
  int hull = 0;
  for (int i=0; i<rp_ctr_num_arity(c); ++i)
  {
    // number of occ. of the i-th variable in c
    if (rp_ctr_num_occur(c,i)==1)
    {
      hull = 1;
    }
    else
    {
      // Box consistency operator
      rp_box_factory bfact(_improve);
      bfact.build(p,c,rp_ctr_num_var(c,i),vec);
    }
  }
  if (hull)
  {
    // Hull consistency operator
    rp_hull_factory hfact;
    hfact.build(p,c,vec);
  }
}

// Copy
rp_hybrid_factory::rp_hybrid_factory(const rp_hybrid_factory& g):
  rp_operator_factory(g)
{
  // --> nothing to do
}

// Copy
rp_hybrid_factory&
rp_hybrid_factory::operator=(const rp_hybrid_factory& g)
{
  // --> nothing to do
  return( *this );
}

// ----------------------------------------
// Factory for the interval Newton operator
// ----------------------------------------
// Constructor
rp_newton_factory::rp_newton_factory(double improve):
  rp_operator_factory(), _improve(improve)
{}

// Destructor
rp_newton_factory::~rp_newton_factory()
{}

// Creation of a set of operators from p and insertion in the vector
void rp_newton_factory::build(const rp_problem& p, rp_vector& vec)
{
  rp_operator_newton * o;
  rp_new(o,rp_operator_newton,(&p,rp_problem_nvar(p),_improve));

  // Insertion of the variables
  for (int i=0; i<rp_problem_nvar(p); ++i)
  {
    o->insert_var(i);
  }

  // Insertion of the functions
  int neq = 0, i = 0;
  while ((neq<rp_problem_nvar(p)) && (i<rp_problem_nctr(p)))
  {
    rp_constraint c = rp_problem_ctr(p,i);
    if ((rp_constraint_type(c)==RP_CONSTRAINT_NUMERICAL))
    {
      rp_ctr_num cn = rp_constraint_num(c);
      if (rp_ctr_num_rel(cn)==RP_RELATION_EQUAL)
      {
	o->insert_function(rp_ctr_num_func(cn));
	++neq;
      }
    }
    ++i;
  }

  // Insertion of the operator in the vector only if existence
  // of a square system of equations on the whole variable set
  if (neq!=rp_problem_nvar(p))
  {
    rp_delete(o);
  }
  else
  {
    rp_vector_insert(vec,o);
  }
}

// Copy
rp_newton_factory::rp_newton_factory(const rp_newton_factory& g):
  rp_operator_factory(g)
{
  // --> nothing to do
}

// Copy
rp_newton_factory&
rp_newton_factory::operator=(const rp_newton_factory& g)
{
  // --> nothing to do
  return( *this );
}

// --------------
// 3B consistency
// --------------
// Constructor
rp_3b_factory::rp_3b_factory(double improve):
  rp_operator_factory(), _improve(improve)
{}

// Destructor
rp_3b_factory::~rp_3b_factory()
{}

// Creation function
void rp_3b_factory::build(const rp_problem& p, rp_vector& vec)
{
  rp_problem& p1 = const_cast<rp_problem&>(p);
  rp_hull_factory fhull;
  rp_propagator * propag;
  rp_operator_3b * o;

  // Creation of one operator for every variable
  for (int i=0; i<rp_problem_nvar(p); ++i)
  {
    // Test: improvement factor 10% to limit the propagation cost
    rp_new(propag,rp_propagator,(&p1,50.0));
    fhull.apply(&p1,*propag);
    rp_new(o,rp_operator_3b,(&p,propag,i,_improve));
    rp_vector_insert(vec,o);
  }
}

// Copy protection
rp_3b_factory::rp_3b_factory(const rp_3b_factory& g):
  rp_operator_factory(g)
{}

// Copy protection
rp_3b_factory&
rp_3b_factory::operator=(const rp_3b_factory& g)
{
  return( *this );
}

// --------------------------
// Interval satisfaction test
// --------------------------
rp_test_factory::rp_test_factory():
  rp_operator_factory()
{}

rp_test_factory::~rp_test_factory()
{}

void rp_test_factory::build(const rp_problem& p, rp_vector& vec)
{
  /* For every constraint */
  for (int i=0; i<rp_problem_nctr(p); ++i)
  {
    rp_operator_test * o;
    rp_new(o,rp_operator_test,(rp_problem_ctr(p,i)));
    rp_vector_insert(vec,o);
  }
}

rp_test_factory&
rp_test_factory::operator=(const rp_test_factory& g)
{
  return( *this );
}

rp_test_factory::rp_test_factory(const rp_test_factory& g):
  rp_operator_factory(g)
{}
