/// @addtogroup dynsys
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file FadMap.h
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2008 by the CAPD Group.
//
// Distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#ifndef _CAPD_DYNSYS_FAD_MAP_H_
#define _CAPD_DYNSYS_FAD_MAP_H_

#include "capd/fadbad/fadiff.h"
#include "capd/fadbad/tadiff.h"
#include "capd/fadbad/differentiate.h"
#include "capd/vectalg/Vector.h"
#include "capd/vectalg/Matrix.h"

namespace capd{
namespace dynsys{

// this class is usually used as a Poicnare section
// an implementation should provide operator() and gradient methods

template <class VectorT>
class FadFunction
{
public:
  typedef VectorT VectorType;
  typedef typename VectorT::ScalarType ScalarType;

  virtual ScalarType operator()(const VectorType& u) const =0;
  virtual VectorType gradient(const VectorType& u) const =0;    
  virtual ~FadFunction() {}
};

// an interface for parameter class for BasicFadTaylor
template<typename Scalar, int D>
class FadMap
{
public:
  typedef Scalar ScalarType;
  typedef fadbad::F<ScalarType,D> FScalar;
  typedef fadbad::T<FScalar> TFScalar;
  typedef capd::vectalg::Matrix<ScalarType,D,D> MatrixType;
  typedef capd::vectalg::Vector<ScalarType,D> VectorType;
  typedef capd::vectalg::Vector<FScalar,D> FVector;
  typedef capd::vectalg::Vector<TFScalar,D> TFVector;
  typedef FadFunction<VectorType> FunctionType;
  
  virtual ~FadMap() {}

  // Any inherited class must specify the following operator(). 
  // It should compute vector field on a vector u.
  template <typename AVector>
  AVector operator()(const AVector& u);
  
  // This operator should compute derivative of the vector field.
  // One can specify own implementation
  // or use in the implementation a template function
  // computeDerivative from file differentiate.h (as in the example of Lorenz system below) 
  // which performs FAD to compute derivative of a map
  virtual MatrixType operator[](const VectorType& u) const = 0;

  // this function should set parameter value of a vector fiels
  // as a Description we may use integers or strings, etc.
  template <typename Description>
  void setParameter(Description s, Scalar value){}
  
  int dimension() const {return D;}
};


// typical implementation of FadMap
// this realizes Lorenz system
template<class Scalar, int D>
class LorenzFadMap : public capd::dynsys::FadMap<Scalar,D>
{
public:
  typedef typename capd::dynsys::FadMap<Scalar,D>::MatrixType MatrixType;
  typedef typename capd::dynsys::FadMap<Scalar,D>::VectorType VectorType;
  
  LorenzFadMap() : parameters(3)
  {}

  template <typename AVector>
  AVector operator()(const AVector& in) const
  {
    AVector out(3);
    out[0] = parameters[0]*(in[1]-in[0]);
    out[1] = in[0]*(parameters[1]-in[2])-in[1];  
    out[2] = in[0]*in[1]-parameters[2]*in[2];  
    return out;
  }
  
  MatrixType operator[](const VectorType& u) const
  {
    MatrixType der(3,3);
    computeDerivative(*this,u,der);
    return der;
  }
  
  void setParameter(int i, Scalar value)
  {
    parameters[i] = value;
  }
  
  int dimension() const {return 3;}

  std::vector<Scalar> parameters;
  // s = parameters[0]
  // r = parameters[1]
  // q = parameters[2]
};

}} // the end of the namespace capd::dynsys

#endif //define _CAPD_DYNSYS_FAD_MAP_H_

/// @}
