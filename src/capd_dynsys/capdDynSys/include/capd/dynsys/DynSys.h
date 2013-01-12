/// @addtogroup dynsys
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file DynSys.h
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#ifndef _CAPD_DYNSYS_DYNSYS_H_
#define _CAPD_DYNSYS_DYNSYS_H_

#include <string>
#include "capd/vectalg/Norm.h"

namespace capd{
namespace dynsys{

template<typename MatrixType>
class FlowballSet;

/*
   Class dynsys is an abstract class representing a discrete dynamical system.
   It is assumed that the generator Psi of the dynamical system decomposes into
                                 Psi=Phi+Omega
   where Phi is a polynomial and Omega is the remainder.
   A realization of the class must implement three methods:
      Phi - the interval enclosure of the polynomial part
      JacPhi -  the interval enclosure of the jacobian of Phi
      Remainder - an enclosure of the remainder Omega.
   Although the class represents a discrete dynamical system, it may be also
   used with time t translations along trajectories of an ODE.
   This is done in the class OdeNum inheriting from DynSys and defined in the
   sequel.

*/
template<typename MatrixT>
class DynSys{
public:
  typedef MatrixT MatrixType;
  typedef typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;
  typedef capd::vectalg::Norm<VectorType,MatrixType> NormType;

  virtual VectorType Phi(const VectorType &iv) = 0;
  virtual MatrixType JacPhi(const VectorType &iv) = 0;
  virtual VectorType Remainder(const VectorType &iv) = 0;
  virtual ScalarType Lipschitz(const VectorType &iv, NormType &n);

  virtual void encloseMap(
      const VectorType& x,
      const VectorType& xx,
      VectorType& o_phi,
      MatrixType& o_jacPhi,
      VectorType& o_rem
  )
  {
    o_rem = this->Remainder(xx);
    o_jacPhi = this->JacPhi(xx);
    o_phi = this->Phi(x);
  }

  //  virtual VectorType perturbations(const VectorType &iv);   ///< an interval bounds for perturbations of ODE
  virtual std::string type(void)
  {
    return "cascade";
  }
  virtual ~DynSys(){}
};

/*
   Class Ode is an abstract class representing an autonomous ODE.
   A realisation must implement three methods:
      f - the vector field itself
      df - the Jacobian of the vector field
      d2f - the Hessian of the vector field
*/

template<typename MatrixT>
class Ode{
public:
  typedef MatrixT MatrixType;
  typedef typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;

  virtual ~Ode () {}
  virtual VectorType f(const VectorType &iv) const = 0;
  virtual MatrixType df(const VectorType &iv) const = 0;
  virtual MatrixType d2f(int i,const VectorType &iv) const = 0;

protected:
  ScalarType t;
};

/*
   Class doubleton is an auxiliary class used in the methods  ...EscTime
   of the class OdeNum below.
*/

template<class Real>
class TimeDoubleton{
public:
  Real left, right;
};

/*
   Class OdeNum is an abstract class implementing the class DynSys.
   Each instance of this class represents a concrete ODE. A realization of
   this class must implement the methods Phi, JacPhi, Remainder from DynSys
*/

template<typename MatrixT>
class OdeNum: public DynSys<MatrixT>{
public:
  typedef MatrixT MatrixType;
  typedef typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;
  typedef typename ScalarType::BoundType Real;
  typedef capd::vectalg::Norm<VectorType,MatrixType> NormType;

  static const Real infty;
  OdeNum(Ode<MatrixType> &the_ode,int the_order, const ScalarType &the_step);
  VectorType Phi(const VectorType &iv) = 0;
  MatrixType JacPhi(const VectorType &iv)= 0;
  VectorType Remainder(const VectorType &iv)= 0;
  ScalarType Lipschitz(const VectorType &iv, NormType &n);

// an auxiliary method used in  enclosureGuaranteeingBounds.
// In the future may be replaced by the set of
// methods ...EscTime defined below
  ScalarType stepGuaranteeingBoundsIn(const VectorType &iv,const VectorType &y, int &dir);

// a method returning an interval enclosing phi(iv,[0,step]), i.e. the image
// of the interval vector in the flow for times not greater then step.

  VectorType enclosureGuaranteeingBounds(const VectorType &iv,int *found);
// an auxiliary method used to select the order in the methods ...EscTime.
// So far i may be 1 (linear order) or 2 (quadratic order).

  void diagBadEnlcosure(const VectorType &x) const;
  void setRoughEnclosureOrder(int i);
  std::string type(void)
  {
    return "flow";
  }

//  protected:

  Ode<MatrixType> &ode;
  int order,roughEnclosureOrder;
  ScalarType step,step_tolerance;

// the following set of methods is intended as a future replacement for
// the method stepGuaranteeingBoundsIn(...). It works with linear AND quadratic
// approximation

  static Real linEscTime(Real a, Real b, Real r);
  static Real quadEscTime(Real a, Real b, Real c, Real r);
  static TimeDoubleton<Real> linEscTime(const ScalarType &a, const ScalarType &b, const ScalarType &r);
  static TimeDoubleton<Real> quadEscTime(
      const ScalarType &a, const ScalarType &b,
      const ScalarType &c, const ScalarType &r
  );
  Real linEscTime(const VectorType &x, const VectorType &y, int &dir);
  Real quadEscTime(const VectorType &x, const VectorType &y, int &dir);
  Real escTime(const VectorType &x, const VectorType &y, int &dir);
  friend class FlowballSet<MatrixType>;
};

template<typename MatrixType>
inline OdeNum<MatrixType>::OdeNum(Ode<MatrixType> &a_ode, int a_order, const ScalarType &a_step)
  : ode(a_ode), order(a_order), step(a_step)
{
  step_tolerance=0.5*a_step;
  roughEnclosureOrder=1;
}

template<typename MatrixType>
inline void OdeNum<MatrixType>::setRoughEnclosureOrder(int i)
{
  roughEnclosureOrder=i;
}

}} // namespace capd::dynsys

#endif // _CAPD_DYNSYS_DYNSYS_H_

/// @}
