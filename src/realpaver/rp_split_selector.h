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
 * rp_split_selector.h                                                      *
 ****************************************************************************/

#ifndef RP_SPLIT_SELECTOR_H
#define RP_SPLIT_SELECTOR_H 1

#include "rp_problem.h"
#include "rp_box.h"

// --------------------------------------------------------
// Class for managing sets of variables in split operations
// --------------------------------------------------------
class rp_var_set
{
public:
  // Constructor
  rp_var_set();

  // Destructor
  ~rp_var_set();

  // Accesors
  int size() const;
  int var(int i) const;
  int constrained(int i) const;
  double precision(int i) const;

  // Insertion of a variable
  void insert(int index, int cstr, double prec);

  // Check whether the set contains var
  int contains(int var) const;

private:
  typedef struct
  {
    int index;
    int constrained;
    double precision;
  } split_var;
  split_var * _a;      /* array of variables */
  int _size;           /* size of _a         */

  // Copy protection
  rp_var_set(const rp_var_set& s);
  rp_var_set& operator=(const rp_var_set& s);
};

// -----------------------------------------
// Base class for variable choice heuristics
// -----------------------------------------
class rp_selector
{
public:
  // Constructor
  rp_selector(rp_problem * p);

  // Destructor
  virtual ~rp_selector();

  // Selection of a variable to be split
  virtual int apply(rp_box b) = 0;

  // Return true if the domain of var in b can be split
  int splitable(rp_box b, int var) const;

  // Return true if no decision variable can be split
  int solution(rp_box b) const;

private:
  // Copy protection
  rp_selector& operator=(const rp_selector& s);

protected:
  rp_problem * _problem;     /* problem to be solved                 */
  rp_var_set _var_int_dec;   /* integer and decision variables       */
  rp_var_set _var_real_dec;  /* real and decision variables          */
  rp_var_set _var_int_aux;   /* integer and auxiliary variables      */
  rp_var_set _var_real_aux;  /* real and auxiliary variables         */

  // Return a splitable variable according to different heuristics
  // Return a negative number if no variable is found

  // Heuristics: MIN_DOM for integers, MAX_DOM for reals
  int mindom_int_dec  (rp_box b) const;
  int mindom_int_aux  (rp_box b) const;
  int maxdom_real_dec (rp_box b) const;
  int maxdom_real_aux (rp_box b) const;

  // Heuristics: MAX_CONSTRAINED
  int maxctr_int_dec  (rp_box b) const;
  int maxctr_int_aux  (rp_box b) const;
  int maxctr_real_dec (rp_box b) const;
  int maxctr_real_aux (rp_box b) const;

  // Heuristics: ROUND_ROBIN for integers, ROUND_ROBIN for reals
  int rr_int_dec  (rp_box b) const;
  int rr_int_aux  (rp_box b) const;
  int rr_real_dec (rp_box b) const;
  int rr_real_aux (rp_box b) const;

  // Returns true if (b(var) inter initial domain(var))
  // is a union of at least two intervals (a hole exists)
  int hole(rp_box b, int var) const;

  // Copy protection
  rp_selector(const rp_selector& s);
};

// ------------------------------------------------------
// Variable choice heuristics
// Decision variable first, integer first, min/max domain
// ------------------------------------------------------
class rp_selector_decirdom : public rp_selector
{
public:
  // Constructor
  rp_selector_decirdom(rp_problem * p);

  // Destructor
  ~rp_selector_decirdom();

  // Selection of a variable to be split
  int apply(rp_box b);

private:
  // Copy protection
  rp_selector_decirdom(const rp_selector_decirdom& s);
  rp_selector_decirdom& operator=(const rp_selector_decirdom& s);
};

// ---------------------------------------------------
// Variable choice heuristics
// Decision variable first, integer first, round-robin
// ---------------------------------------------------
class rp_selector_decirrr : public rp_selector
{
public:
  // Constructor
  rp_selector_decirrr(rp_problem * p);

  // Destructor
  ~rp_selector_decirrr();

  // Selection of a variable to be split
  int apply(rp_box b);

private:
  // Copy protection
  rp_selector_decirrr(const rp_selector_decirrr& s);
  rp_selector_decirrr& operator=(const rp_selector_decirrr& s);
};

// ---------------------------------------------------
// Variable choice heuristics
// Decision variable first, integer first, round-robin
// with robust strategy (diversification)
// ---------------------------------------------------
class rp_selector_decirrobust : public rp_selector
{
public:
  // Constructor
  rp_selector_decirrobust(rp_problem * p, double ratio);

  // Destructor
  ~rp_selector_decirrobust();

  // Selection of a variable to be split
  int apply(rp_box b);

private:
  double _ratio;

  // Copy protection
  rp_selector_decirrobust(const rp_selector_decirrobust& s);
  rp_selector_decirrobust& operator=(const rp_selector_decirrobust& s);
};

// ------------------------------------
// Variable choice heuristics
// Integer first, max constrained first
// ------------------------------------
class rp_selector_decircmax : public rp_selector
{
public:
  // Constructor
  rp_selector_decircmax(rp_problem * p);

  // Destructor
  ~rp_selector_decircmax();

  // Selection of a variable to be split
  int apply(rp_box b);

private:
  // Copy protection
  rp_selector_decircmax(const rp_selector_decircmax& s);
  rp_selector_decircmax& operator=(const rp_selector_decircmax& s);
};

// -----------------------------
// Variable choice heuristics
// Integer first, min/max domain
// -----------------------------
class rp_selector_irdom : public rp_selector
{
public:
  // Constructor
  rp_selector_irdom(rp_problem * p);

  // Destructor
  ~rp_selector_irdom();

  // Selection of a variable to be split
  int apply(rp_box b);

private:
  // Copy protection
  rp_selector_irdom(const rp_selector_irdom& s);
  rp_selector_irdom& operator=(const rp_selector_irdom& s);
};

// ------------------------------------
// Variable choice heuristics
// Integer first, max constrained first
// ------------------------------------
class rp_selector_ircmax : public rp_selector
{
public:
  // Constructor
  rp_selector_ircmax(rp_problem * p);

  // Destructor
  ~rp_selector_ircmax();

  // Selection of a variable to be split
  int apply(rp_box b);

private:
  // Copy protection
  rp_selector_ircmax(const rp_selector_ircmax& s);
  rp_selector_ircmax& operator=(const rp_selector_ircmax& s);
};

// -------------------------------------------
// Variable choice heuristics
// Round-robin strategy independent from types
// -------------------------------------------
class rp_selector_roundrobin : public rp_selector
{
public:
  // Constructor
  rp_selector_roundrobin(rp_problem * p);

  // Destructor
  ~rp_selector_roundrobin();

  // Selection of a variable to be split
  int apply(rp_box b);

private:
  // Copy protection
  rp_selector_roundrobin(const rp_selector_roundrobin& s);
  rp_selector_roundrobin& operator=(const rp_selector_roundrobin& s);
};

// -------------------------------------------
// Variable choice heuristics
// Used for existence proofs
// -------------------------------------------
class rp_selector_existence : public rp_selector
{
public:
  // Constructor
  rp_selector_existence(rp_problem * p);

  // Destructor
  ~rp_selector_existence();

  // Selection of a variable to be split
  int apply(rp_box b);

private:
  // Copy protection
  rp_selector_existence(const rp_selector_existence& s);
  rp_selector_existence& operator=(const rp_selector_existence& s);
};

#endif /* RP_SPLIT_SELECTOR_H */
