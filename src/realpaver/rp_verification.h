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
 * rp_verification.h                                                        *
 ****************************************************************************/

#ifndef RP_VERIFICATION_H
#define RP_VERIFICATION_H 1

#include "rp_problem.h"
#include "rp_operator_factory.h"
#include "rp_propagator.h"
#include "rp_box_set.h"
#include "rp_split.h"

// -----------------------------------------
// Base class for solution existence provers 
// -----------------------------------------
class rp_existence_prover
{
public:
  // Constructor
  rp_existence_prover();

  // Destructor
  virtual ~rp_existence_prover();

  // Proof function
  virtual int prove(rp_box b) = 0;

protected:
  // Copy protection
  rp_existence_prover(const rp_existence_prover& p);

private:
  // Copy protection
  rp_existence_prover& operator=(const rp_existence_prover& p);
};

// --------------------------------------------------------------------------
// Solution existence prover using interval satisfaction over canonical boxes
// --------------------------------------------------------------------------
class rp_interval_satisfaction_prover : public rp_existence_prover
{
public:
  // Constructor
  rp_interval_satisfaction_prover(rp_problem * p, int maxbox = 100);

  // Destructor
  ~rp_interval_satisfaction_prover();

  // Proof function from base class
  int prove(rp_box b);

private:
  // Copy protection
  rp_interval_satisfaction_prover(const rp_interval_satisfaction_prover& p);
  rp_interval_satisfaction_prover&
  operator=(const rp_interval_satisfaction_prover& p);

  // Check the existence of a solution in a box
  int existence(rp_box b);
  rp_box _midpoint;

  // Check whether a box can be eliminated during search
  int useless_box(rp_box b);

  rp_problem * _problem;   /* problem to be checked                      */
  rp_box_queue _boxes;     /* set of boxes managed during search         */
  rp_propagator _propag;   /* propagator implementing the interval test  */
  rp_propagator _hpropag;  /* propagator implementing hull consistency   */
  rp_selector * _select;   /* selection algorithm used during search     */
  rp_splitter * _split;    /* splitting algorithm used during search     */
  int _maxbox;             /* maximum number of boxes to be tested       */
};

#endif /* RP_VERIFICATION_H */
