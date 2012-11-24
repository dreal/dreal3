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
 * rp_operator_factory.h                                                    *
 ****************************************************************************/

#ifndef RP_OPERATOR_FACTORY_H
#define RP_OPERATOR_FACTORY_H 1

#include "rp_config.h"
#include "rp_memory.h"
#include "rp_propagator.h"

// ------------------------------------------------
// Transition from a data model to a decision model
// Creation of operators from problems
// ------------------------------------------------
class rp_operator_factory
{
public:
  // Constructor
  rp_operator_factory();

  // Destructor
  virtual ~rp_operator_factory();

  // Creation of a set of operators from p and insertion in vop
  void apply(rp_problem * p, rp_propagator& propag);

  // Creation functions to be implemented in derived classes
  virtual void build(const rp_problem& p, rp_vector& vec);
  virtual void build(const rp_problem& p, const rp_ctr_num& c,
		     rp_vector& vec);
  virtual void build(const rp_problem& p, const rp_ctr_num& c,
		     int var, rp_vector& vec);

protected:
  // Copy
  rp_operator_factory(const rp_operator_factory& g);

private:
  // Copy protection
  rp_operator_factory& operator=(const rp_operator_factory& g);

  // Internal functions
  void build(const rp_problem& p, const rp_constraint& c, rp_vector& vec);
  void build(const rp_problem& p, const rp_ctr_cond& c, rp_vector& vec);
  void build(const rp_problem& p, const rp_ctr_piecewise& c, rp_vector& vec);
};

// ------------------------------------------------
// Factory of operators managing domains with holes
// ------------------------------------------------
class rp_domain_factory : public rp_operator_factory
{
public:
  // Constructor
  rp_domain_factory();

  // Destructor
  ~rp_domain_factory();

  // Creation of a set of operators from p and insertion in the vector
  void build(const rp_problem& p, rp_vector& vec);

private:
  // Copy protection
  rp_domain_factory(const rp_domain_factory& g);
  rp_domain_factory& operator=(const rp_domain_factory& g);
};

// ----------------------------------
// Propagation using hull consistency
// ----------------------------------
class rp_hull_factory : public rp_operator_factory
{
public:
  // Constructor
  rp_hull_factory();

  // Destructor
  ~rp_hull_factory();

  // Creation of a set of operators from p and insertion in vop
  void build(const rp_problem& p, const rp_ctr_num& c, rp_vector& vec);

private:
  // Copy protection
  rp_hull_factory(const rp_hull_factory& g);
  rp_hull_factory& operator=(const rp_hull_factory& g);
};

// ---------------------------------
// Propagation using box consistency
// ---------------------------------
class rp_box_factory : public rp_operator_factory
{
public:
  // Constructor
  rp_box_factory(double improve);

  // Destructor
  ~rp_box_factory();

  // Creation of a set of operators from p and insertion in the vector
  void build(const rp_problem& p, const rp_ctr_num& c,
	     int var, rp_vector& vec);

private:
  double _improve;    // improvement factor of iterative method

  // Copy protection
  rp_box_factory(const rp_box_factory& g);
  rp_box_factory& operator=(const rp_box_factory& g);
};

// ---------------------------------------------------
// Combination of box consistency and hull consistency
// ---------------------------------------------------
class rp_hybrid_factory : public rp_operator_factory
{
public:
  // Constructor
  rp_hybrid_factory(double improve);

  // Destructor
  ~rp_hybrid_factory();

  // Creation of a set of operators from p and insertion in the vector
  void build(const rp_problem& p, const rp_ctr_num& c, rp_vector& vec);

private:
  double _improve;    // improvement factor of iterative method

  // Copy protection
  rp_hybrid_factory(const rp_hybrid_factory& g);
  rp_hybrid_factory& operator=(const rp_hybrid_factory& g);
};

// ----------------------
// Interval Newton method
// ----------------------
class rp_newton_factory : public rp_operator_factory
{
public:
  // Constructor
  rp_newton_factory(double improve);

  // Destructor
  ~rp_newton_factory();

  // Creation of a set of operators from p and insertion in the vector
  void build(const rp_problem& p, rp_vector& vec);

private:
  double _improve;    // improvement factor of iterative method

  // Copy protection
  rp_newton_factory(const rp_newton_factory& g);
  rp_newton_factory& operator=(const rp_newton_factory& g);
};

// --------------
// 3B consistency
// --------------
class rp_3b_factory : public rp_operator_factory
{
public:
  // Constructor
  rp_3b_factory(double improve);

  // Destructor
  ~rp_3b_factory();

  // Creation function
  void build(const rp_problem& p, rp_vector& vec);

private:
  double _improve;    // improvement factor of iterative method

  // Copy protection
  rp_3b_factory(const rp_3b_factory& g);
  rp_3b_factory& operator=(const rp_3b_factory& g);
};

// --------------------------
// Interval satisfaction test
// --------------------------
class rp_test_factory : public rp_operator_factory
{
public:
  // Constructor
  rp_test_factory();

  // Destructor
  ~rp_test_factory();

  // Creation function
  void build(const rp_problem& p, rp_vector& vec);

private:
  // Copy protection
  rp_test_factory& operator=(const rp_test_factory& g);
  rp_test_factory(const rp_test_factory& g);
};

#endif /* RP_OPERATOR_FACTORY_H */
