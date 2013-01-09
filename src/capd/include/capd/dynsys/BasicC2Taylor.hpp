/// @addtogroup dynsys
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file BasicC2Taylor.hpp
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#ifndef _CAPD_DYNSYS_BASICC2TAYLOR_HPP_
#define _CAPD_DYNSYS_BASICC2TAYLOR_HPP_

#include <string>
#include <stdexcept>

#include "capd/map/C2Map.hpp"
#include "capd/dynsys/BasicC2Taylor.h"

namespace capd{
namespace dynsys{

//###########################################################//

template<typename MapType, typename StepControlT>
BasicC2Taylor<MapType,StepControlT>::BasicC2Taylor(
      MapType& vectorField,
      int order,
      const ScalarType& step
  ) : BasicTaylor<MapType,StepControlT>(vectorField,order,step)
{
  m_c2MatrixCoeff = new (dimension()) C2CoeffType[getOrder()+2];
}


//###########################################################//


template<typename MapType, typename StepControlT>
void BasicC2Taylor<MapType,StepControlT>::setOrder(int newOrder)
{
  if(newOrder==getOrder())
    return;
  BasicTaylor<MapType,StepControlT>::setOrder(newOrder);
  delete [] m_c2MatrixCoeff;
  m_c2MatrixCoeff = new (dimension()) C2CoeffType[getOrder()+2];
}

//###########################################################//

template<typename MapType, typename StepControlT>
typename BasicC2Taylor<MapType,StepControlT>::VectorType BasicC2Taylor<MapType,StepControlT>::operator()(
      const VectorType& x,
      MatrixType& jac,
      C2CoeffType& hessian
   )
{
  C2CoeffType H(dimension());
  VectorType result(dimension());
  H.clear();
  hessian.clear();
  jac.clear();
  result.clear();

  VectorType* coeff = this->m_curve.getCoefficientsAtCenter();
  MatrixType* matrixCoeff = this->m_curve.getMatrixCoefficients();
  computeC2Coeff(x, MatrixType::Identity(dimension()), H, coeff, matrixCoeff, getOrder());

  ScalarType stepPower(1.);
  for(int p=0;p<=getOrder();++p)
  {
    typename C2CoeffType::iterator i1 = hessian.begin(),
                                    i2 = hessian.end(),
                                    j1 = m_c2MatrixCoeff[p].begin();
    while(i1!=i2)
    {
      *i1 += *j1 * stepPower;
      ++i1;
      ++j1;
    }
    jac += matrixCoeff[p] * stepPower;
    result += coeff[p] * stepPower;
    stepPower *= m_step;
  }
  return result;
}


// ####################################################################


template<typename MapType, typename StepControlT>
void BasicC2Taylor<MapType,StepControlT>::computeC2Coeff(
      const VectorType& x,
      const MatrixType& V,
      const C2CoeffType& H,
      VectorType* coeff, 
      MatrixType* matrixCoeff,
      int order
  )
{
  if(order<0)
  {
    throw std::out_of_range("C2Taylor error: negative index of Taylor coefficient in C2Taylor::computeC2Coeff");
  }

  int p,i,j,k,s,r,w,c;

// first we compute coefficients for x
  this->computeCoefficients(order,coeff,x);
  this->computeMatrixCoeff(order,coeff,matrixCoeff,V);

  m_c2MatrixCoeff[0]=H;
  for(i=1;i<=order;++i)
    m_c2MatrixCoeff[i].clear();
  C2CoeffType* temp = m_vField->computeSecondDerivatives(coeff,order);

// we compute coefficients of H_{ijc} up to order 'order'

  for(p=0;p<order;++p)
  {
    for(i=0;i<dimension();++i)
    {
      for(j=0;j<dimension();++j)
      {
        for(c=0;c<=j;++c)
        {
// -------------
          for(k=0;k<dimension();++k)
          {
            for(r=0;r<dimension();++r)
            {
              for(w=0;w<=p;++w)
              {
                ScalarType S1(0.);
                for(s=0;s<=w;++s)
                  S1 += temp[s](i,k,r) * matrixCoeff[w-s][r][c];

                m_c2MatrixCoeff[p+1](i,j,c) += S1 * matrixCoeff[p-w][k][j];
              }  // end of w-for
            }  // end of r-for
          }  // end of k-for

          for(k=0;k<dimension();++k)
            for(s=0;s<=p;++s)
                m_c2MatrixCoeff[p+1](i,j,c) +=  m_F[s][i][k] * m_c2MatrixCoeff[p-s](k,j,c);

          m_c2MatrixCoeff[p+1](i,j,c) = m_c2MatrixCoeff[p+1](i,j,c)/(p+1);
// -------------
        } // end of c-for
      } // end of j-for
    } //end of i-for
  }

  delete []temp;
}

}} // namespace capd::dynsys

#endif // _CAPD_DYNSYS_BASICC2TAYLOR_HPP_

/// @}
