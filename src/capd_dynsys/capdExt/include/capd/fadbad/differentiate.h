/// @addtogroup fadbad
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file differentiate.h
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2008 by the CAPD Group.
//
// Distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_FADBAD_DIFFERENTIATE_H_ 
#define _CAPD_FADBAD_DIFFERENTIATE_H_ 

#include "capd/fadbad/fadiff.h"
#include "capd/vectalg/Vector.hpp"

template <typename Scalar, unsigned D>
inline void differentiate(fadbad::F<Scalar,D>& u, int i, int /* - if DIM is known at compile time, we dont use it*/)
{
    u.diff(i);
}

template<typename Scalar>
inline void differentiate(fadbad::F<Scalar,0>& u, int i, int dimension)
{
    u.diff(i,dimension);
}

template <class T, class VectorT, class MatrixT>
void computeDerivative(T& f, const VectorT& u, MatrixT& result)
{
  typedef typename MatrixT::ScalarType ScalarT;
  typedef fadbad::F<ScalarT> FScalarT;
  typedef capd::vectalg::Vector<FScalarT,0> FVectorT;
  
  int dim = u.dimension();    
  FVectorT v(dim);
  int i;
  for(i=0;i<dim;++i)
    v[i] = u[i];
  for(i=0;i<dim;++i)
    differentiate(v[i],i,dim);
  v = f(v);
  for(i=1;i<=dim;++i)
  {
    for(int j=1;j<=dim;++j)
      result(i,j) = v[i-1].d(j-1);
  }
}

template <class T, class ScalarT, class VectorT, class MatrixT>
void computeDerivative(T& f, const ScalarT& t, const VectorT& u, MatrixT& result)
{
  typedef fadbad::F<ScalarT> FScalarT;
  typedef capd::vectalg::Vector<FScalarT,0> FVectorT;
  
  int dim = u.dimension();    
  FVectorT v(dim);
  int i;
  for(i=0;i<dim;++i)
    v[i] = u[i];
  for(i=0;i<dim;++i)
    differentiate(v[i],i,dim);
  v = f(t,v);
  for(i=1;i<=dim;++i)
  {
    for(int j=1;j<=dim;++j)
      result(i,j) = v[i-1].d(j-1);
  }
}

#endif // _CAPD_FADBAD_DIFFERENTIATE_H_ 

/// @}
