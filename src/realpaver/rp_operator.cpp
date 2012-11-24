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
 * rp_operator.cpp                                                          *
 ****************************************************************************/

#include "rp_operator.h"

// -------------------------------------
// Generic class for reduction operators
// -------------------------------------

// Construction of operator with a priority and an arity
// (number of variables potentially reduced)
rp_operator::rp_operator(int priority, int arity, int pruned_arity):
  _priority(priority),
  _arity(arity),
  _pruned(pruned_arity),
  _working(RP_OPERATOR_WORKING_INIT)
{}

// Destruction
rp_operator::~rp_operator()
{}

// Copy
rp_operator::rp_operator(const rp_operator& o):
  _priority(o._priority),
  _arity(o._arity),
  _pruned(o._pruned),
  _working(o._working)
{}

// Copy protection --> nothing to do
rp_operator& rp_operator::operator=(const rp_operator& o)
{
  return( *this );
}

// Accessors and modifiers
int rp_operator::priority() const
{
  return _priority;
}

int rp_operator::arity() const
{
  return _arity;
}

int rp_operator::pruned_arity() const
{
  return _pruned;
}

int rp_operator::working(int id) const
{
  return( _working==id);
}

void rp_operator::set_working(int id)
{
  _working = id;
}

void rp_operator::set_unworking()
{
  -- _working;
}

// ----------------------------------------------------
// Operator implementing the interval satisfaction test
// ----------------------------------------------------
rp_operator_test::rp_operator_test(rp_constraint c):
  rp_operator(RP_OPERATOR_TEST_PRIORITY,rp_constraint_arity(c),0),
  _c(c)
{}

rp_operator_test::~rp_operator_test()
{}

int rp_operator_test::var(int i) const
{
  return( rp_constraint_var(_c,i) );
}

int rp_operator_test::pruned_var(int i) const
{
  return( -1 );
}

int rp_operator_test::apply(rp_box b)
{
  return( !rp_constraint_unfeasible(_c,b) );
}

rp_operator_test::rp_operator_test(const rp_operator_test& o):
  rp_operator(0,0,0)
{
  // nothing to do
}

rp_operator_test&
rp_operator_test::operator=(const rp_operator_test& o)
{
  return( *this );
}

// -----------------------------------------------------
// Conditional operator: applied only if a guard is true
// -----------------------------------------------------

// Construction
rp_operator_cond::rp_operator_cond(rp_ctr_cond c, rp_operator * o):
  rp_operator(o->priority(),0,o->pruned_arity()),
  _c(c),
  _o(o)
{
  rp_intset_create(&_vars);

  // depends on every variable of Operator o
  for (int i=0; i<o->arity(); ++i)
  {
    rp_intset_insert(_vars,o->var(i));
  }

  // for every constraint in the guard
  for (int i=0; i<rp_ctr_cond_guardsize(c); ++i)
  {
    rp_ctr_num cnum = rp_ctr_cond_guard_elem(c,i);

    // for every variable in the constraint
    for (int j=0; j<rp_ctr_num_arity(cnum); ++j)
    {
      rp_intset_insert(_vars,rp_ctr_num_var(cnum,j));
    }
  }
}

// Destruction
rp_operator_cond::~rp_operator_cond()
{
  rp_intset_destroy(&_vars);
  rp_delete(_o);
}

// Variables on which the operator depends
int rp_operator_cond::var(int i) const
{
  return rp_intset_elem(_vars,i);
}

int rp_operator_cond::arity() const
{
  return rp_intset_size(_vars);
}

// Variables that can be pruned by the operator
int rp_operator_cond::pruned_var(int i) const
{
  return( _o->pruned_var(i) );
}

// Application of operator to reduce the box b
int rp_operator_cond::apply(rp_box b)
{
  // check whether the guard is certainly satisfied
  int sat = 1;
  int i = 0;
  while ((sat) && (i<rp_ctr_cond_guardsize(_c)))
  {
    if (!rp_ctr_num_inner(rp_ctr_cond_guard_elem(_c,i),b))
    {
      sat = 0;
    }
    else ++i;
  }

  // the operator is applied only if the guard is true
  if (sat)
  {
    return( _o->apply(b) );
  }
  else
  {
    return( 1 );
  }
}

// Copy protection
rp_operator_cond::rp_operator_cond(const rp_operator_cond& o):
  rp_operator(0,0,0)
{
  // nothing to do
}

rp_operator_cond&
rp_operator_cond::operator=(const rp_operator_cond& o)
{
  return( *this );
}

// -----------------------------------------------
// Specific conditional operator with guard x in I
// -----------------------------------------------

// Construction
rp_operator_condvar::rp_operator_condvar(int v,
					 rp_interval x,
					 rp_operator * o):
  rp_operator(o->priority(),0,o->pruned_arity()),
  _v(v),
  _o(o)
{
  rp_interval_copy(_dom,x);

  rp_intset_create(&_vars);

  // depends on every variable of Operator o
  for (int i=0; i<o->arity(); ++i)
  {
    rp_intset_insert(_vars,o->var(i));
  }
  rp_intset_insert(_vars,v);  // and on v
}

// Destruction
rp_operator_condvar::~rp_operator_condvar()
{
  rp_intset_destroy(&_vars);
  rp_delete(_o);
}

// Variables on which the operator depends
int rp_operator_condvar::var(int i) const
{
  return rp_intset_elem(_vars,i);
}

int rp_operator_condvar::arity() const
{
  return rp_intset_size(_vars);
}

// Variables that can be pruned by the operator
int rp_operator_condvar::pruned_var(int i) const
{
  return( _o->pruned_var(i) );
}

// Application of operator to reduce the box b
int rp_operator_condvar::apply(rp_box b)
{
  // check whether the guard is certainly satisfied
  if (rp_interval_included(rp_box_elem(b,_v),_dom))
  {
    return( _o->apply(b) );
  }
  else
  {
    return( 1 );
  }
}

// Copy protection
rp_operator_condvar::rp_operator_condvar(const rp_operator_condvar& o):
  rp_operator(0,0,0)
{
  // nothing to do
}

rp_operator_condvar&
rp_operator_condvar::operator=(const rp_operator_condvar& o)
{
  return( *this );
}

// -------------------------------------------
// Specific operator for piecewise constraints
// -------------------------------------------

// Construction
rp_operator_piecewise::rp_operator_piecewise(rp_ctr_piecewise c):
  rp_operator(RP_OPERATOR_DOMAIN_PRIORITY,0,1),
  _c(c)
{
  rp_intset_create(&_vars);

  // depends on every variable of c
  for (int i=0; i<rp_ctr_piecewise_arity(c); ++i)
  {
    for (int j=0; j<rp_ctr_piecewise_elem_size(c,i); ++j)
    {
      rp_ctr_num cnum = rp_ctr_piecewise_elem_ctrnum(c,i,j);
      for (int k=0; k<rp_ctr_num_arity(cnum); ++k)
      {
	rp_intset_insert(_vars,rp_ctr_num_var(cnum,k));
      }
    }
  }
  rp_intset_insert(_vars,rp_ctr_piecewise_var(c));
}

// Destruction
rp_operator_piecewise::~rp_operator_piecewise()
{
  rp_intset_destroy(&_vars);
}

// Variables on which the operator depends
int rp_operator_piecewise::var(int i) const
{
  return rp_intset_elem(_vars,i);
}

int rp_operator_piecewise::arity() const
{
  return rp_intset_size(_vars);
}

// Variables that can be pruned by the operator
int rp_operator_piecewise::pruned_var(int i) const
{
  return( rp_ctr_piecewise_var(_c) );
}

// Application of operator to reduce the box b
int rp_operator_piecewise::apply(rp_box b)
{
  // Check each piece Ij:Cj, if Cj violated then the elements of Ij
  // are removed from the domain of the main variable of _c
  for (int i=0; i<rp_ctr_piecewise_arity(_c); ++i)
  {
    int violated = 0, j = 0;
    while ((!violated) && (j<rp_ctr_piecewise_elem_size(_c,i)))
    {
      if (rp_ctr_num_unfeasible(rp_ctr_piecewise_elem_ctrnum(_c,i,j),b))
      {
	violated = 1;
      }
      else ++j;
    }
    if (violated)
    {
      // domain restriction dom(var) := dom(var) \ Ij
      rp_interval aux;
      rp_interval_copy(aux,rp_box_elem(b,rp_ctr_piecewise_var(_c)));
      rp_interval_setminus(rp_box_elem(b,rp_ctr_piecewise_var(_c)),
			   aux,
			   rp_ctr_piecewise_elem_dom(_c,i));

      if (rp_interval_empty(rp_box_elem(b,rp_ctr_piecewise_var(_c))))
      {
	return( 0 );
      }
    }
  }

  // Check whether the domain of the main variable of _c
  // intersects at least one Ij
  int intersect = 0, i = 0;
  while ((!intersect) && (i<rp_ctr_piecewise_arity(_c)))
  {
    if (!rp_interval_disjoint(rp_box_elem(b,rp_ctr_piecewise_var(_c)),
			      rp_ctr_piecewise_elem_dom(_c,i)))
    {
      intersect = 1;
    }
    else ++i;
  }
  return( intersect );
}

// Copy protection
rp_operator_piecewise::rp_operator_piecewise(const rp_operator_piecewise& o):
  rp_operator(0,0,0)
{
  // nothing to do
}

rp_operator_piecewise&
rp_operator_piecewise::operator=(const rp_operator_piecewise& o)
{
  return( *this );
}





































// --------------------------------------------------------------------
// Specific operator based on hull consistency over numerical equations
// --------------------------------------------------------------------

// Hull consistency operator over numerical equations
rp_operator_hull_eq::rp_operator_hull_eq(rp_ctr_num c):
  rp_operator(RP_OPERATOR_HULL_PRIORITY,
	      rp_ctr_num_arity(c),
	      rp_ctr_num_arity(c)),
  _c(c)
{}

// Destruction
rp_operator_hull_eq::~rp_operator_hull_eq()
{}

// Copy
rp_operator_hull_eq::rp_operator_hull_eq(const rp_operator_hull_eq& o):
  rp_operator(o), _c(o._c)
{}

// Copy protection --> nothing to do
rp_operator_hull_eq&
rp_operator_hull_eq::operator=(const rp_operator_hull_eq& o)
{
  return( *this );
}

// Application function of hull consistency operator
int rp_operator_hull_eq::apply(rp_box b)
{
  return( rp_sat_hull_eq(_c,b) );
}

// Variables on which the operator depends
int rp_operator_hull_eq::var(int i) const
{
  return( rp_ctr_num_var(_c,i) );
}

// Variables that can be pruned by the operator
int rp_operator_hull_eq::pruned_var(int i) const
{
  return( rp_ctr_num_var(_c,i) );
}

// -----------------------------------------------------------------------
// Specific operator based on hull consistency over numerical inequalities
// -----------------------------------------------------------------------

// Hull consistency operator over numerical inequalities f<=0
rp_operator_hull_inf::rp_operator_hull_inf(rp_ctr_num c):
  rp_operator(RP_OPERATOR_HULL_PRIORITY,
	      rp_ctr_num_arity(c),
	      rp_ctr_num_arity(c)),
  _c(c)
{}

// Destruction
rp_operator_hull_inf::~rp_operator_hull_inf()
{}

// Copy
rp_operator_hull_inf::rp_operator_hull_inf(const rp_operator_hull_inf& o):
  rp_operator(o), _c(o._c)
{}

// Copy protection --> nothing to do
rp_operator_hull_inf&
rp_operator_hull_inf::operator=(const rp_operator_hull_inf& o)
{
  return( *this );
}

// Application function of hull consistency operator
int rp_operator_hull_inf::apply(rp_box b)
{
  return( rp_sat_hull_inf(_c,b) );
}

// Variables on which the operator depends
int rp_operator_hull_inf::var(int i) const
{
  return( rp_ctr_num_var(_c,i) );
}

// Variables that can be pruned by the operator
int rp_operator_hull_inf::pruned_var(int i) const
{
  return( rp_ctr_num_var(_c,i) );
}

// -----------------------------------------------------------------------
// Specific operator based on hull consistency over numerical inequalities
// -----------------------------------------------------------------------

// Hull consistency operator over numerical inequalities f>=0
rp_operator_hull_sup::rp_operator_hull_sup(rp_ctr_num c):
  rp_operator(RP_OPERATOR_HULL_PRIORITY,
	      rp_ctr_num_arity(c),
	      rp_ctr_num_arity(c)),
  _c(c)
{}

// Destruction
rp_operator_hull_sup::~rp_operator_hull_sup()
{}

// Copy
rp_operator_hull_sup::rp_operator_hull_sup(const rp_operator_hull_sup& o):
  rp_operator(o), _c(o._c)
{}

// Copy protection --> nothing to do
rp_operator_hull_sup&
rp_operator_hull_sup::operator=(const rp_operator_hull_sup& o)
{
  return( *this );
}

// Application function of hull consistency operator
int rp_operator_hull_sup::apply(rp_box b)
{
  return( rp_sat_hull_sup(_c,b) );
}

// Variables on which the operator depends
int rp_operator_hull_sup::var(int i) const
{
  return( rp_ctr_num_var(_c,i) );
}

// Variables that can be pruned by the operator
int rp_operator_hull_sup::pruned_var(int i) const
{
  return( rp_ctr_num_var(_c,i) );
}

// -------------------------------------------------------------------
// Specific operator based on box consistency over numerical equations
// -------------------------------------------------------------------

// Construction
rp_operator_box_eq::rp_operator_box_eq(rp_expression f,
				       int x,
				       double improve,
				       double eps):
  rp_operator(RP_OPERATOR_BOX_PRIORITY,rp_expression_arity(f),1),
  _x(x),
  _improve(improve),
  _eps(eps)
{
  rp_expression_copy(&_f,f);
  if (rp_expression_derivable(f))
  {
    rp_expression_deriv_symb(&_df,f,x);
  }
  else
  {
    _df = NULL;
  }
}

// Destruction
rp_operator_box_eq::~rp_operator_box_eq()
{
  if (_df!=NULL)
  {
    rp_expression_destroy(&_df);
  }
  rp_expression_destroy(&_f);
}

// Copy
rp_operator_box_eq::rp_operator_box_eq(const rp_operator_box_eq& o):
  rp_operator(o),
  _x(o._x),
  _improve(o._improve),
  _eps(o._eps)
{
  rp_erep aux;
  rp_erep_copy(&aux,rp_expression_rep(o._f));
  rp_expression_create(&_f,&aux);
  if (rp_expression_derivable(_f))
  {
    rp_expression_deriv_symb(&_df,_f,_x);
  }
  else
  {
    _df = NULL;
  }
}

// Application function
int rp_operator_box_eq::apply(rp_box b)
{
  return( rp_sat_box_eq(_f,_df,b,_x,_improve,_eps) );
}

// Variables on which the operator depends
int rp_operator_box_eq::var(int i) const
{
  return( rp_expression_var(_f,i) );
}

// Variables that can be pruned by the operator
int rp_operator_box_eq::pruned_var(int i) const
{
  return( _x );
}

// Copy protection
rp_operator_box_eq&
rp_operator_box_eq::operator=(const rp_operator_box_eq& o)
{
  return( *this );
}

// ----------------------------------------------------------------------
// Specific operator based on box consistency over numerical inequalities
// ----------------------------------------------------------------------

// Construction
rp_operator_box_inf::rp_operator_box_inf(rp_expression f,
					 int x,
					 double improve,
					 double eps):
  rp_operator(RP_OPERATOR_BOX_PRIORITY,rp_expression_arity(f),1),
  _x(x),
  _improve(improve),
  _eps(eps)
{
  rp_expression_copy(&_f,f);
  if (rp_expression_derivable(f))
  {
    rp_expression_deriv_symb(&_df,f,x);
  }
  else
  {
    _df = NULL;
  }
}

// Destruction
rp_operator_box_inf::~rp_operator_box_inf()
{
  if (_df!=NULL)
  {
    rp_expression_destroy(&_df);
  }
  rp_expression_destroy(&_f);
}

// Copy
rp_operator_box_inf::rp_operator_box_inf(const rp_operator_box_inf& o):
  rp_operator(o),
  _x(o._x),
  _improve(o._improve),
  _eps(o._eps)
{
  rp_erep aux;
  rp_erep_copy(&aux,rp_expression_rep(o._f));
  rp_expression_create(&_f,&aux);
  if (rp_expression_derivable(_f))
  {
    rp_expression_deriv_symb(&_df,_f,_x);
  }
  else
  {
    _df = NULL;
  }
}

// Application function
int rp_operator_box_inf::apply(rp_box b)
{
  return( rp_sat_box_inf(_f,_df,b,_x,_improve,_eps) );
}

// Variables on which the operator depends
int rp_operator_box_inf::var(int i) const
{
  return( rp_expression_var(_f,i) );
}

// Variables that can be pruned by the operator
int rp_operator_box_inf::pruned_var(int i) const
{
  return( _x );
}

// Copy protection
rp_operator_box_inf&
rp_operator_box_inf::operator=(const rp_operator_box_inf& o)
{
  return( *this );
}

// ----------------------------------------------------------------------
// Specific operator based on box consistency over numerical inequalities
// ----------------------------------------------------------------------

// Construction
rp_operator_box_sup::rp_operator_box_sup(rp_expression f,
					 int x,
					 double improve,
					 double eps):
  rp_operator(RP_OPERATOR_BOX_PRIORITY,rp_expression_arity(f),1),
  _x(x),
  _improve(improve),
  _eps(eps)
{
  rp_expression_copy(&_f,f);
  if (rp_expression_derivable(f))
  {
    rp_expression_deriv_symb(&_df,f,x);
  }
  else
  {
    _df = NULL;
  }
}

// Destruction
rp_operator_box_sup::~rp_operator_box_sup()
{
  if (_df!=NULL)
  {
    rp_expression_destroy(&_df);
  }
  rp_expression_destroy(&_f);
}

// Copy
rp_operator_box_sup::rp_operator_box_sup(const rp_operator_box_sup& o):
  rp_operator(o),
  _x(o._x),
  _improve(o._improve),
  _eps(o._eps)
{
  rp_erep aux;
  rp_erep_copy(&aux,rp_expression_rep(o._f));
  rp_expression_create(&_f,&aux);
  if (rp_expression_derivable(_f))
  {
    rp_expression_deriv_symb(&_df,_f,_x);
  }
  else
  {
    _df = NULL;
  }
}

// Application function
int rp_operator_box_sup::apply(rp_box b)
{
  return( rp_sat_box_sup(_f,_df,b,_x,_improve,_eps) );
}

// Variables on which the operator depends
int rp_operator_box_sup::var(int i) const
{
  return( rp_expression_var(_f,i) );
}

// Variables that can be pruned by the operator
int rp_operator_box_sup::pruned_var(int i) const
{
  return( _x );
}

// Copy protection
rp_operator_box_sup&
rp_operator_box_sup::operator=(const rp_operator_box_sup& o)
{
  return( *this );
}

// -------------------------------------------------
// Intersection of current domain and initial domain
// -------------------------------------------------

// Construction from a variable and its global index
rp_operator_domain::rp_operator_domain(rp_variable x, int v):
  rp_operator(RP_OPERATOR_DOMAIN_PRIORITY,1,1),
  _x(x),
  _id(v)
{}

// Destruction
rp_operator_domain::~rp_operator_domain()
{}

// Copy
rp_operator_domain::rp_operator_domain(const rp_operator_domain& o):
  rp_operator(o),
  _x(o._x),
  _id(o._id)
{}

// Application function
// b(x) := hull (b(x) inter initial_domain)
int rp_operator_domain::apply(rp_box b)
{
  /* Rounding for discrete variables */
  if (rp_variable_integer(_x))
  {
    rp_interval_trunc(rp_box_elem(b,_id));
    if (rp_interval_empty(rp_box_elem(b,_id)))
    {
      return( 0 );
    }
  }

  /* Intersection with initial domain */
  return( rp_union_inter_iu(rp_box_elem(b,_id),rp_variable_domain(_x)) );
}

// Variables on which the operator depends
int rp_operator_domain::var(int i) const
{
  return( _id );
}

// Variables that can be pruned by the operator
int rp_operator_domain::pruned_var(int i) const
{
  return( _id );
}

// Copy protection
rp_operator_domain&
rp_operator_domain::operator=(const rp_operator_domain& o)
{
  return( *this );
}

// ----------------------------------------------------------------
// Multidimensional interval Newton method for systems of equations
// ----------------------------------------------------------------

// Construction
rp_operator_newton::rp_operator_newton(const rp_problem * p,
				       int n, double improve):
  rp_operator(RP_OPERATOR_NEWTON_PRIORITY,n,n),
  _problem(const_cast<rp_problem*>(p)),
  _improve(improve),
  _arity(n),
  _vi(0),
  _fi(0)
{
  rp_malloc(_v,int*,n*sizeof(int));
  rp_malloc(_f,rp_expression*,n*sizeof(rp_expression));
  rp_malloc(_vf,int**,n*sizeof(int*));

  rp_box_create(&_midpoint,rp_problem_nvar(*p));

  rp_interval zero;
  rp_interval_set_point(zero,0.0);
  rp_interval_matrix_create(&_jacobi,_arity,_arity);
  rp_interval_matrix_create(&_izero,_arity,_arity);
  rp_interval_matrix_set(_izero,zero);

  rp_interval_vector_create(&_negfmid,_arity);
  rp_interval_vector_create(&_unknown,_arity);

  rp_real_matrix_create(&_midjacobi,_arity,_arity);
  rp_real_matrix_create(&_precond,_arity,_arity);
  rp_real_matrix_create(&_identity,_arity,_arity);
  rp_real_matrix_setid(_identity);

  rp_interval_matrix_create(&_precond_jacobi,_arity,_arity);
  rp_interval_vector_create(&_precond_negfmid,_arity);
}

// Destruction
rp_operator_newton::~rp_operator_newton()
{
  for (int i=0; i<_fi; ++i)
  {
    rp_free(_vf[i]);
  }
  rp_free(_vf);
  rp_free(_f);
  rp_free(_v);
  rp_box_destroy(&_midpoint);
  rp_interval_matrix_destroy(&_jacobi);
  rp_interval_matrix_destroy(&_izero);
  rp_interval_vector_destroy(&_negfmid);
  rp_interval_vector_destroy(&_unknown);
  rp_real_matrix_destroy(&_midjacobi);
  rp_real_matrix_destroy(&_precond);
  rp_real_matrix_destroy(&_identity);

  rp_interval_matrix_destroy(&_precond_jacobi);
  rp_interval_vector_destroy(&_precond_negfmid);
}

// Insertion of i-th variable
void rp_operator_newton::insert_var(int v)
{
  _v[_vi++] = v;
}

// Return the local index of the variable v (global index)
int rp_operator_newton::get_local_var(int v)
{
  for (int i=0; i<_arity; ++i)
  {
    if (v==_v[i])
    {
      return( i );
    }
  }
  return( -1 );
}

// Insertion of i-th expression
void rp_operator_newton::insert_function(rp_expression e)
{
  rp_malloc(_vf[_fi],int*,rp_expression_arity(e)*sizeof(int));
  for (int i=0; i<rp_expression_arity(e); ++i)
  {
    _vf[_fi][i] = this->get_local_var(rp_expression_var(e,i));
  }
  _f[_fi++] = e;
}

void rp_operator_newton::compute_unknown(rp_box b)
{
  for (int i=0; i<_arity; ++i)
  {
    rp_interval_sub(rp_ivector_elem(_unknown,i),
		    rp_box_elem(b,_v[i]),
		    rp_box_elem(_midpoint,_v[i]));
  }
}

int rp_operator_newton::compute_negfmid()
{
  for (int i=0; i<_arity; ++i)
  {
    if (!rp_expression_eval(_f[i],_midpoint))
    {
      return( 0 );
    }
    else
    {
      rp_interval_neg(rp_ivector_elem(_negfmid,i),rp_expression_val(_f[i]));
    }
  }
  return( 1 );
}

void rp_operator_newton::compute_midpoint(rp_box b)
{
  for (int i=0; i<_arity; ++i)
  {
    rp_interval_set_point(rp_box_elem(_midpoint,_v[i]),
			  rp_interval_midpoint(rp_box_elem(b,_v[i])));
  }
}

int rp_operator_newton::compute_precond()
{
  // midpoint of Jacobian matrix
  for (int i=0; i<_arity; ++i)
  {
    for (int j=0; j<_arity; ++j)
    {
      rp_rmatrix_elem(_midjacobi,i,j) =
         rp_interval_midpoint(rp_imatrix_elem(_jacobi,i,j));
    }
  }

  // Inversion of midpoint of Jacobian matrix
  if (rp_real_matrix_inverse(_precond,_midjacobi,_identity))
  {
    rp_matrix_mul_rm_im(_precond_jacobi,_precond,_jacobi);
    rp_matrix_mul_rm_iv(_precond_negfmid,_precond,_negfmid);
    return( 1 );
  }
  else
  {
    return( 0 );
  }
}

int rp_operator_newton::compute_jacobi(rp_box b)
{
  /* Computation of the Jacobian matrix df(b) */
  rp_interval_matrix_copy(_jacobi,_izero);
  for (int i=0; i<_arity; ++i)
  {
    /* for every function  */
    if (rp_expression_deriv_num(_f[i],b))
    {
      /* for every variable of _f[i] */
      for (int j=0; j<rp_expression_arity(_f[i]); ++j)
      {
	rp_interval_copy(rp_imatrix_elem(_jacobi,i,_vf[i][j]),
			 rp_expression_deriv_local_val(_f[i],j));
      }
    }
    else
    {
      return( 0 );
    }
  }
  return( 1 );
}

int rp_operator_newton::reduce(rp_box b)
{
  bool proof = true;

  for (int i=0; i<_arity; ++i)
  {
    int v = _v[i];
    rp_interval aux, save;

    rp_interval_add(aux,rp_ivector_elem(_unknown,i),rp_box_elem(_midpoint,v));
    rp_interval_copy(save,rp_box_elem(b,v));

    if (!(rp_interval_strictly_included(aux,save))) proof = false;

    rp_interval_inter(rp_box_elem(b,v),save,aux);

    if (rp_interval_empty(rp_box_elem(b,v)))
    {
      return( 0 );
    }
  }

  if (proof) rp_box_set_safe(b);

  return( 1 );
}

// Application function
int rp_operator_newton::apply(rp_box b)
{
  if (!this->compute_jacobi(b))
  {
    return( 0 );
  }

  this->compute_midpoint(b);


  if (!this->compute_negfmid())
  {
    return( 0 );
  }

  this->compute_unknown(b);

  // preconditionning
  if (this->compute_precond())
  {
    if (!rp_num_gs(_precond_jacobi,_unknown,_precond_negfmid,0))
    {
      return( 0 );
    }
  }
  else
  {
    if (!rp_num_gs(_jacobi,_unknown,_negfmid,_improve))
    {
      return( 0 );
    }
  }

  // x := x inter (unknown + midpoint)
  return (this->reduce(b));
}

// Variables on which the operator depends
int rp_operator_newton::var(int i) const
{
  return( _v[i] );
}

// Variables that can be pruned by the operator
int rp_operator_newton::pruned_var(int i) const
{
  return( _v[i] );
}

// Copy protection
rp_operator_newton::rp_operator_newton(const rp_operator_newton& o):
  rp_operator(0,0,0)
{}

rp_operator_newton& rp_operator_newton::operator=(const rp_operator_newton& o)
{
  return( *this );
}


// -------------------------------------
// Reduction operators of 3B consistency
// -------------------------------------

// Construction of operator
rp_operator_3b::rp_operator_3b(const rp_problem * p,
			       rp_operator * o, int v, double improve):
  rp_operator(o->priority()+RP_OPERATOR_3B_PRIORITY,0,0),
  _v(v),
  _improve(0.125),  /* 12.5% */
  _o(o)
{
  if ((improve>=0.0) && (improve<=100.0))
  {
    _improve = improve/100.0;  /* user-defined */
  }
  rp_box_create(&_baux,rp_problem_nvar(*p));
}

// Destruction
rp_operator_3b::~rp_operator_3b()
{
  rp_box_destroy(&_baux);
  rp_delete(_o);
}

// Variables on which the operator depends
int rp_operator_3b::arity() const
{
  return _o->arity();
}

int rp_operator_3b::var(int i) const
{
  return _o->var(i);
}

// Variables that can be pruned by the operator
int rp_operator_3b::pruned_arity() const
{
  return _o->pruned_arity();
}

int rp_operator_3b::pruned_var(int i) const
{
  return _o->pruned_var(i);
}

// Application of operator to reduce the box b
int rp_operator_3b::apply(rp_box b)
{
  // domain to be reduced
  double u = rp_binf(rp_box_elem(b,_v));
  double v = rp_bsup(rp_box_elem(b,_v));
  double x;

  // Reduction of left bound [a,x]
  RP_ROUND_UPWARD();
  x = u + _improve * (v-u);

  if (x>=v)
  {
    // reduction of whole domain
    return _o->apply(b);
  }
  else
  {
    rp_box_copy(_baux,b);
    rp_bsup(rp_box_elem(_baux,_v)) = x;
    if (!_o->apply(_baux))
    {
      rp_binf(rp_box_elem(b,_v)) = x;
    }
  }

  // Reduction of right bound [x,b]
  RP_ROUND_DOWNWARD();
  x = v - _improve * (v-u);

  rp_box_copy(_baux,b);
  rp_binf(rp_box_elem(_baux,_v)) = x;
  if (!_o->apply(_baux))
  {
    rp_bsup(rp_box_elem(b,_v)) = x;
  }

  return( !(rp_interval_empty(rp_box_elem(b,_v))) );
}

// Copy protection
rp_operator_3b::rp_operator_3b(const rp_operator_3b& o):
  rp_operator(o)
{}

rp_operator_3b&
rp_operator_3b::operator=(const rp_operator_3b& o)
{
  return( *this );
}
