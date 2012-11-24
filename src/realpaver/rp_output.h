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
 * rp_output.h                                                              *
 ****************************************************************************/

#ifndef RP_OUTPUT_H
#define RP_OUTPUT_H 1

#include <iostream>
#include "rp_config.h"
#include "rp_problem.h"
#include "rp_box_set.h"
#include <string.h>

// ----------------------------------
// Output filter of problem solutions
// ----------------------------------
class rp_ofilter
{
public:
  // Constructor
  rp_ofilter(rp_problem * p);

  // Destructor
  virtual ~rp_ofilter();

  // Output of box b for problem p
  virtual void apply_box(const rp_box& b, char * msg) = 0;

protected:
  // Copy
  rp_ofilter(const rp_ofilter& f);

  rp_problem * _problem;

private:
  // Copy protection
  rp_ofilter& operator=(const rp_ofilter& f);
};

// ------------------------------------------------------
// Default output filter of problem solutions in a stream
// ------------------------------------------------------
class rp_ofilter_text : public rp_ofilter
{
public:
  // Constructor
  rp_ofilter_text(rp_problem * p, std::ostream * os, int nsol = 0);

  // Destructor
  ~rp_ofilter_text();

  // Output of box b for problem p
  void apply_box(const rp_box& b, char * msg);

private:
  std::ostream * _os;  // output stream
  int _nsol;           // number of boxes displayed

  // Copy protection
  rp_ofilter_text(const rp_ofilter_text& f);
  rp_ofilter_text& operator=(const rp_ofilter_text& f);
};

// -----------------------------------------
// Output filter for 2D problems -> PSTricks
// -----------------------------------------
class rp_ofilter_pstricks : public rp_ofilter
{
public:
  // Constructor
  rp_ofilter_pstricks(rp_problem * p, std::ostream * os);

  // Destructor
  ~rp_ofilter_pstricks();

  // Output of box b for problem p
  void apply_box(const rp_box& b, char * msg);

private:
  std::ostream * _os;  // output stream

  // Copy protection
  rp_ofilter_pstricks(const rp_ofilter_pstricks& f);
  rp_ofilter_pstricks& operator=(const rp_ofilter_pstricks& f);
};

// ------------------------------------------
// Output filter that gathers close solutions
// ------------------------------------------
class rp_ofilter_merge : public rp_ofilter
{
public:
  // Constructor
  rp_ofilter_merge(rp_problem * p, std::ostream * os, double eps = 0.0);

  // Destructor
  ~rp_ofilter_merge();

  // Distance between two boxes to be merged
  double distance() const;

  // Returns true if b1 and b2 can be merged
  int close_enough(const rp_box& b1, const rp_box& b2);

  // Merging until quiescence
  void compact();

  // Output of box b for problem p
  void apply_box(const rp_box& b, char * msg);

  // Output of all boxes using filter o
  int apply_all(rp_ofilter& o);

private:
  rp_box_stack _stack;  // the set of solutions
  double _eps;          // distance between two boxes to be merged

  std::ostream * _os;   // output stream

  // Copy protection
  rp_ofilter_merge(const rp_ofilter_merge& f);
  rp_ofilter_merge& operator=(const rp_ofilter_merge& f);
};


#endif /* RP_OUTPUT_H */
