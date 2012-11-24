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
 * rp_split.h                                                               *
 ****************************************************************************/

#ifndef RP_SPLIT_H
#define RP_SPLIT_H 1

#include "rp_problem.h"
#include "rp_box.h"
#include "rp_box_set.h"
#include "rp_split_selector.h"

// -------------------------------
// Base class for domain splitting
// -------------------------------
class rp_splitter
{
public:
  // Constructor
  rp_splitter(rp_problem * p);

  // Destructor
  virtual ~rp_splitter();

  // Split the current box from bs along dimension var
  virtual void apply(rp_box_set& bs, int var) = 0;

protected:
  rp_problem * _problem;

  // Statistics to be stored in a box
  void observe(rp_box b, int var);

  // Returns true if (dom inter init_dom) contains at least two intervals
  // given an integer variable, in this case (i1 union i2) is the result
  // of the split on the hole found
  int integer_hole(rp_interval dom,
		   rp_union_interval init_dom,
		   rp_interval i1, rp_interval i2);

  // Returns true if (dom inter init_dom) contains at least two intervals
  // given a real variable, in this case (i1 union i2) is the result
  // of the split on the hole found
  int real_hole(rp_interval dom,
		rp_union_interval init_dom,
		rp_interval i1, rp_interval i2);

  // Copy protection
  rp_splitter(const rp_splitter& ds);

private:
  // Copy protection
  rp_splitter& operator=(const rp_splitter& ds);
};

// -------------------------------------------
// Class for domain splitting
// Enumeration of integer, bisection of reals
// -------------------------------------------
class rp_splitter_mixed : public rp_splitter
{
public:
  // Constructor
  rp_splitter_mixed(rp_problem * p);

  // Destructor
  ~rp_splitter_mixed();

  // Split the current box from bs along dimension var
  void apply(rp_box_set& bs, int var);

private:
  // Copy protection
  rp_splitter_mixed(const rp_splitter_mixed& ds);
  rp_splitter_mixed& operator=(const rp_splitter_mixed& ds);
};

// -------------------------------------------
// Class for domain splitting
// Bisection of every domain
// -------------------------------------------
class rp_splitter_bisection : public rp_splitter
{
public:
  // Constructor
  rp_splitter_bisection(rp_problem * p);

  // Destructor
  ~rp_splitter_bisection();

  // Split the current box from bs along dimension var
  void apply(rp_box_set& bs, int var);

private:
  // Copy protection
  rp_splitter_bisection(const rp_splitter_bisection& ds);
  rp_splitter_bisection& operator=(const rp_splitter_bisection& ds);
};

#endif /* RP_SPLIT_H */
