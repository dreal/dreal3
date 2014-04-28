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
 * rp_solver.h                                                              *
 ****************************************************************************/

#pragma once

#include <iostream>
#include "rp_clock.h"
#include "rp_problem.h"
#include "rp_operator_factory.h"
#include "rp_propagator.h"
#include "rp_box_set.h"
#include "rp_split.h"
#include "rp_verification.h"
#include "rp_output.h"

// ---------------------------------------------------------
// Branch-and-prune algorithm for solving constraint systems
// ---------------------------------------------------------
class rp_bpsolver
{
public:
  // Constructor
  rp_bpsolver(rp_problem * p,
              double improve,
              rp_selector * vs,
              rp_splitter * ds,
              rp_existence_prover * ep = 0);

  // Destructor
  ~rp_bpsolver();

  // Computation of the next solution
  rp_box compute_next();

  // Number of computed solutions
  int solution();

  // Number of boxes allocated in memory
  int nboxes();

  // Number of splitting steps
  int nsplit();

private:
  rp_problem * _problem;     /* problem to be solved                    */
  rp_propagator _propag;     /* reduction algorithm using propagation   */
  rp_box_stack _boxes;       /* the set of boxes during search          */
  rp_selector * _vselect;    /* selection of variable to be split       */
  rp_splitter * _dsplit;     /* split function of variable domain       */
  rp_existence_prover * _ep; /* existence prover                        */
  int _sol;                  /* number of computed solutions            */
  int _nsplit;               /* number of split steps                   */
  double _improve;           /* improvement factor of iterative methods */

  // Copy protection
  rp_bpsolver(const rp_bpsolver& s);
  rp_bpsolver& operator=(const rp_bpsolver& s);
};
