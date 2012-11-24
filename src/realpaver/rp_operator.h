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
 * rp_operator.h                                                            *
 ****************************************************************************/

#ifndef RP_OPERATOR_H
#define RP_OPERATOR_H 1

#include "rp_config.h"
#include "rp_memory.h"
#include "rp_problem.h"
#include "rp_operator_sat.h"

#define RP_OPERATOR_NEWTON_PRIORITY   -10000
#define RP_OPERATOR_3B_PRIORITY       -5000
#define RP_OPERATOR_BOX_PRIORITY      -1000
#define RP_OPERATOR_HULL_PRIORITY     -500
#define RP_OPERATOR_TEST_PRIORITY     -200
#define RP_OPERATOR_DOMAIN_PRIORITY   -100

#define RP_OPERATOR_WORKING_INIT     1

// -------------------------------------
// Generic class for reduction operators
// -------------------------------------
class rp_operator
{
public:
  // Construction of operator with a priority and an arity
  // (number of variables on which the operator depends)
  rp_operator(int priority, int arity, int pruned_arity);

  // Destruction
  virtual ~rp_operator();

  // Get the priority of the operator
  virtual int priority() const;

  // Variables on which the operator depends
  virtual int arity() const;
  virtual int var(int i) const = 0;

  // Variables that can be pruned by the operator
  virtual int pruned_arity() const;
  virtual int pruned_var(int i) const = 0;

  // Manage the status of the operator during propagation
  int working(int id) const;
  void set_working(int id);
  void set_unworking();

  // Application of operator to reduce the box b
  virtual int apply(rp_box b) = 0;

protected:
  // Copy
  rp_operator(const rp_operator& o);

private:
  int _priority,  /* positive integer representing the priority level        */
      _arity,     /* number of variables on which the operators depends      */
      _pruned,    /* number of variables potentially pruned by the operator  */
      _working;   /* true if the operator must be applied during propagation */

  // Copy protection
  rp_operator& operator=(const rp_operator& o);
};

// ----------------------------------------------------
// Operator implementing the interval satisfaction test
// ----------------------------------------------------
class rp_operator_test : public rp_operator
{
public:
  // Construction
  rp_operator_test(rp_constraint c);

  // Destruction
  ~rp_operator_test();

  // Variables on which the operator depends
  int var(int i) const;

  // Variables that can be pruned by the operator
  int pruned_var(int i) const;

  // Application of operator to reduce the box b
  int apply(rp_box b);

protected:
  // Copy
  rp_operator_test(const rp_operator_test& o);

private:
  rp_constraint _c;

  // Copy protection
  rp_operator_test& operator=(const rp_operator_test& o);
};

// -----------------------------------------------------
// Conditional operator: applied only if a guard is true
// ----------------------------------------------------- 
class rp_operator_cond : public rp_operator
{
public:
  // Construction
  rp_operator_cond(rp_ctr_cond c, rp_operator * o);

  // Destruction
  ~rp_operator_cond();

  // Variables on which the operator depends
  int var(int i) const;
  int arity() const;

  // Variables that can be pruned by the operator
  int pruned_var(int i) const;

  // Application of operator to reduce the box b
  int apply(rp_box b);

private:
  rp_ctr_cond _c;    /* the constraint guard -> conc                   */
  rp_operator * _o;  /* the operator to be applied, built from conc    */
  rp_intset _vars;   /* set of variables on which the operator depends */

  // Copy protection
  rp_operator_cond(const rp_operator_cond& o);
  rp_operator_cond& operator=(const rp_operator_cond& o);
};

// ------------------------------------------------------------
// Specific conditional operator used for piecewise constraints
// ------------------------------------------------------------ 
class rp_operator_condvar : public rp_operator
{
public:
  // Construction
  rp_operator_condvar(int v, rp_interval x, rp_operator * o);

  // Destruction
  ~rp_operator_condvar();

  // Variables on which the operator depends
  int var(int i) const;
  int arity() const;

  // Variables that can be pruned by the operator
  int pruned_var(int i) const;

  // Application of operator to reduce the box b
  int apply(rp_box b);

private:
  int _v;            /* variable                                       */
  rp_interval _dom;  /* variable domain                                */
  rp_operator * _o;  /* the operator to be applied if the domain of _v */
                     /* is included in _dom                            */
  rp_intset _vars;   /* set of variables on which the operator depends */

  // Copy protection
  rp_operator_condvar(const rp_operator_condvar& o);
  rp_operator_condvar& operator=(const rp_operator_condvar& o);
};

// ---------------------------------------
// Operator used for piecewise constraints
// ---------------------------------------
class rp_operator_piecewise : public rp_operator
{
public:
  // Construction
  rp_operator_piecewise(rp_ctr_piecewise c);

  // Destruction
  ~rp_operator_piecewise();

  // Variables on which the operator depends
  int var(int i) const;
  int arity() const;

  // Variables that can be pruned by the operator
  int pruned_var(int i) const;

  // Application of operator to reduce the box b
  int apply(rp_box b);

private:
  rp_ctr_piecewise _c;
  rp_intset _vars;   /* set of variables on which the operator depends */

  // Copy protection
  rp_operator_piecewise(const rp_operator_piecewise& o);
  rp_operator_piecewise& operator=(const rp_operator_piecewise& o);
};

// --------------------------------------------------------------------
// Specific operator based on hull consistency over numerical equations
// --------------------------------------------------------------------
class rp_operator_hull_eq : public rp_operator
{
public:
  // Construction
  rp_operator_hull_eq(rp_ctr_num c);

  // Destruction
  ~rp_operator_hull_eq();

  // Copy
  rp_operator_hull_eq(const rp_operator_hull_eq& o);

  // Application function
  int apply(rp_box b);

  // Variables on which the operator depends
  int var(int i) const;

  // Variables that can be pruned by the operator
  int pruned_var(int i) const;

private:
  rp_ctr_num _c;   /* the associated numerical equation f=0 */

  // Copy protection
  rp_operator_hull_eq& operator=(const rp_operator_hull_eq& o);
};

// -----------------------------------------------------------------------
// Specific operator based on hull consistency over numerical inequalities
// -----------------------------------------------------------------------
class rp_operator_hull_inf : public rp_operator
{
public:
  // Construction
  rp_operator_hull_inf(rp_ctr_num c);

  // Destruction
  ~rp_operator_hull_inf();

  // Copy
  rp_operator_hull_inf(const rp_operator_hull_inf& o);

  // Application function
  int apply(rp_box b);

  // Variables on which the operator depends
  int var(int i) const;

  // Variables that can be pruned by the operator
  int pruned_var(int i) const;

private:
  rp_ctr_num _c;   /* the associated numerical inequality f<=0 */

  // Copy protection
  rp_operator_hull_inf& operator=(const rp_operator_hull_inf& o);
};

// -----------------------------------------------------------------------
// Specific operator based on hull consistency over numerical inequalities
// -----------------------------------------------------------------------
class rp_operator_hull_sup : public rp_operator
{
public:
  // Construction
  rp_operator_hull_sup(rp_ctr_num c);

  // Destruction
  ~rp_operator_hull_sup();

  // Copy
  rp_operator_hull_sup(const rp_operator_hull_sup& o);

  // Application function
  int apply(rp_box b);

  // Variables on which the operator depends
  int var(int i) const;

  // Variables that can be pruned by the operator
  int pruned_var(int i) const;

private:
  rp_ctr_num _c;   /* the associated numerical inequality f>=0 */

  // Copy protection
  rp_operator_hull_sup& operator=(const rp_operator_hull_sup& o);
};

// -------------------------------------------------------------------
// Specific operator based on box consistency over numerical equations
// f(x,...) = 0
// -------------------------------------------------------------------
class rp_operator_box_eq : public rp_operator
{
public:
  // Construction
  rp_operator_box_eq(rp_expression f, int x,
		     double improve, double eps);

  // Destruction
  ~rp_operator_box_eq();

  // Copy
  rp_operator_box_eq(const rp_operator_box_eq& o);

  // Application function
  int apply(rp_box b);

  // Variables on which the operator depends
  int var(int i) const;

  // Variables that can be pruned by the operator
  int pruned_var(int i) const;

private:
  rp_expression _f;   /* the associated numerical expression       */
  int _x;             /* the considered variable                   */
  rp_expression _df;  /* the derivative of _f wrt. _x              */
  double _improve;    /* improvement factor of iterative algorithm */
  double _eps;        /* precision of search algorithm             */

  // Copy protection
  rp_operator_box_eq& operator=(const rp_operator_box_eq& o);
};

// ----------------------------------------------------------------------
// Specific operator based on box consistency over numerical inequalities
// f(x,...) <= 0
// ----------------------------------------------------------------------
class rp_operator_box_inf: public rp_operator
{
public:
  // Construction
  rp_operator_box_inf(rp_expression f, int x,
		      double improve, double eps);

  // Destruction
  ~rp_operator_box_inf();

  // Copy
  rp_operator_box_inf(const rp_operator_box_inf& o);

  // Application function
  int apply(rp_box b);

  // Variables on which the operator depends
  int var(int i) const;

  // Variables that can be pruned by the operator
  int pruned_var(int i) const;

private:
  rp_expression _f;   /* the associated numerical expression */
  int _x;             /* the considered variable             */
  rp_expression _df;  /* the derivative of _f wrt. _x        */
  double _improve;    /* improvement factor of iterative algorithm */
  double _eps;        /* precision of search algorithm             */

  // Copy protection
  rp_operator_box_inf& operator=(const rp_operator_box_inf& o);
};

// ----------------------------------------------------------------------
// Specific operator based on box consistency over numerical inequalities
// f(x,...) >= 0
// ----------------------------------------------------------------------
class rp_operator_box_sup : public rp_operator
{
public:
  // Construction
  rp_operator_box_sup(rp_expression f, int x,
		      double improve, double eps);

  // Destruction
  ~rp_operator_box_sup();

  // Copy
  rp_operator_box_sup(const rp_operator_box_sup& o);

  // Application function
  int apply(rp_box b);

  // Variables on which the operator depends
  int var(int i) const;

  // Variables that can be pruned by the operator
  int pruned_var(int i) const;

private:
  rp_expression _f;   /* the associated numerical expression */
  int _x;             /* the considered variable             */
  rp_expression _df;  /* the derivative of _f wrt. _x        */
  double _improve;    /* improvement factor of iterative algorithm */
  double _eps;        /* precision of search algorithm             */

  // Copy protection
  rp_operator_box_sup& operator=(const rp_operator_box_sup& o);
};

// -------------------------------------------------
// Intersection of current domain and initial domain
// -------------------------------------------------
class rp_operator_domain : public rp_operator
{
public:
  // Construction from a variable and its global index
  rp_operator_domain(rp_variable x, int v);

  // Destruction
  ~rp_operator_domain();

  // Copy
  rp_operator_domain(const rp_operator_domain& o);

  // Application function
  int apply(rp_box b);

  // Variables on which the operator depends
  int var(int i) const;

  // Variables that can be pruned by the operator
  int pruned_var(int i) const;

private:
  rp_variable _x;    /* the variable     */
  int _id;           /* its global index */

  // Copy protection
  rp_operator_domain& operator=(const rp_operator_domain& o);
};

// ----------------------------------------------------------------
// Multidimensional interval Newton method for systems of equations
// ----------------------------------------------------------------
class rp_operator_newton : public rp_operator
{
public:
  // Construction from a problem and the operator arity
  rp_operator_newton(const rp_problem * p, int n, double improve);

  // Destruction
  ~rp_operator_newton();

  // Insertion of a variable
  void insert_var(int v);

  // Insertion of a function
  void insert_function(rp_expression e);

  // Application function
  int apply(rp_box b);

  // Variables on which the operator depends
  int var(int i) const;

  // Variables that can be pruned by the operator
  int pruned_var(int i) const;

private:
  rp_problem * _problem;
  double _improve;         /* improvement factor of iterative algorithm */
  int _arity;              /* arity n         */
  int * _v;                /* v = (v1,...,vn) */
  rp_expression * _f;      /* f1(v),...,fn(v) */
  int ** _vf;              /* _vf[i,j] is the index in _v of */
                           /* the j-th variable of _f[i]     */
  int _vi, _fi;

  // Jacobian matrix
  rp_interval_matrix _jacobi;  /* Jacobian matrix */
  rp_interval_matrix _izero;   /* zero matrix used to initialize the Jacobian */
  int compute_jacobi(rp_box b);

  // midpoint(b)
  rp_box _midpoint;
  void compute_midpoint(rp_box b);

  // -f(midpoint(b))
  rp_interval_vector _negfmid;
  int compute_negfmid();

  // Vector (x-mid) to be reduced by Gauss-Seidel
  rp_interval_vector _unknown;
  void compute_unknown(rp_box b);

  // preconditionning
  rp_real_matrix _midjacobi;
  rp_real_matrix _precond;
  rp_real_matrix _identity;
  rp_interval_matrix _precond_jacobi;
  rp_interval_vector _precond_negfmid;
  int compute_precond();

  // reduction (final operation)
  int reduce(rp_box b);

  // Return the local index of the variable v (global index)
  int get_local_var(int v);

  // Copy protection
  rp_operator_newton(const rp_operator_newton& o);
  rp_operator_newton& operator=(const rp_operator_newton& o);
};


// -------------------------------------
// Reduction operators of 3B consistency
// -------------------------------------
class rp_operator_3b : public rp_operator
{
public:
  // Construction of operator
  rp_operator_3b(const rp_problem * p,
		 rp_operator * o, int v, double improve);

  // Destruction
  ~rp_operator_3b();

  // Variables on which the operator depends
  int arity() const;
  int var(int i) const;

  // Variables that can be pruned by the operator
  int pruned_arity() const;
  int pruned_var(int i) const;

  // Application of operator to reduce the box b
  int apply(rp_box b);

private:
  int _v;            /* variable to be reduced                       */
  double _improve;   /* % of the size of domain for bounds reduction */
  rp_operator * _o;  /* operator used to prove bounds inconsistency  */
  rp_box _baux;

  // Copy protection
  rp_operator_3b(const rp_operator_3b& o);
  rp_operator_3b& operator=(const rp_operator_3b& o);
};

#endif /* RP_OPERATOR_H */
