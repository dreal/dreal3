/// @addtogroup map
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file Node_powsqr.hpp
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#ifndef _CAPD_MAP_NODE_POWSQR_HPP_
#define _CAPD_MAP_NODE_POWSQR_HPP_

#include "capd/capd/power.h"
#include "capd/interval/Interval.hpp"

namespace capd{
namespace map{


// ------------------------ operators -----------------------------------

template<class ScalarType>
ScalarType& PowNodeBase<ScalarType, false>::operator()(int i)
{
  if(i<=this->m_maxComputedDerivative)
    return this->value[i];
  this->m_maxComputedDerivative = i;

  (*(this->left))(i);
  (*(this->right))(i);

  ScalarType c=this->right->value[0];
  if (c==ScalarType(1.))
    return this->value[i] = this->left->value[i];

  if (i==0)
  {
    int cInt = toInt(c);
    if(ScalarType(cInt) == c){
        return *(this->value) = power(*(this->left->value),cInt);
    }

    ScalarType c2 = 2*c;
    int c2Int = toInt(c2);
    if(ScalarType(c2Int) == c2){
      return *(this->value) = power(sqrt(*(this->left->value)),c2Int);
    }

    ScalarType temp = c * log(*(this->left->value));
    return *(this->value) = exp(temp);
  }

  ScalarType result(0.);

  if(this->left->value[0]==0)
  {
    ScalarType *temp1 = new ScalarType[i+1];
    ScalarType *temp2 = new ScalarType[i+1];

    int j,k,p;
    for(j=0;j<=i;++j)
      temp1[j]=this->left->value[j];

    for(k=1;k<c;++k)
    {
      for(p=0;p<=i;++p)
      {
        temp2[p]=ScalarType(0.);
        for(j=0;j<=p;++j)
          temp2[p] += this->left->value[j]*temp1[p-j];
      }
      for(p=0;p<=i;++p)
        temp1[p]=temp2[p];
   }

   result = temp1[i];
   delete []temp1;
   delete []temp2;
   return this->value[i] = result;
  }

  for(int j=0;j<i;++j)
    result+= ScalarType(i*c-j*(c+1)) * this->value[j] * this->left->value[i-j];

  return this->value[i] = result / (ScalarType(i) * this->left->value[0]);
}

// specialisation for intervals only
template < typename ScalarType>
ScalarType &
PowNodeBase<ScalarType, true>::operator()(int i)
{
  if(i<=this->m_maxComputedDerivative)
    return this->value[i];
  this->m_maxComputedDerivative = i;

  (*(this->left))(i);
  (*(this->right))(i);

  if(this->right->value[0]==ScalarType(1.))
    return this->value[i] = this->left->value[i];

  ScalarType c = (this->right->value[0]);
  int cInt = toInt(c.leftBound());

  if (i==0){
    if(ScalarType(cInt) == c){
      return *(this->value) = power(*(this->left->value),cInt);
    }

    ScalarType c2 = 2*c;
    int c2Int = toInt(c2.leftBound());
    if(ScalarType(c2Int) == c2){
      return *(this->value) = power(sqrt(*(this->left->value)),c2Int);
    }

    return this->value[i] = power(this->left->value[i],this->right->value[i]);
  } // end of i = 0

  ScalarType result(0.);

  if(!(this->left->value[0].contains(0.0)))
  {
    for(int j=0;j<i;++j)
      result+= (this->right->value[0]*ScalarType(i)-(this->right->value[0]+1)*ScalarType(j))
      * this->value[j] * this->left->value[i-j];
    return this->value[i] = result/(ScalarType(i) * this->left->value[0]);
  }

  // if we get to this point it means that x contains 0 and i>0
  // therefore we can proceed only for positive integer exponents
  if((ScalarType(typename ScalarType::BoundType(cInt)) != c) || (cInt<=0))
  {
    std::ostringstream bufor;
    bufor << "function error: can not compute Taylor series for x^(" << c << ") if x contains zero";
    throw(std::runtime_error(bufor.str()));
  }

  ScalarType *temp1 = new ScalarType[i+1];
  ScalarType *temp2 = new ScalarType[i+1];
  int j,p;
  int k;
  for(j=0;j<=i;++j)
    temp1[j]=this->left->value[j];

  for(k=1;k<c;++k)
  {
    for(p=0;p<=i;++p)
    {
      temp2[p] = ScalarType(0.);
      for(j=0;j<=p;++j)
        temp2[p] += this->left->value[j]*temp1[p-j];
    }
    for(p=0;p<=i;++p)
      temp1[p]=temp2[p];
  }

  result = temp1[i];
  delete []temp1;
  delete []temp2;

  return this->value[i] = result;
}


// ----------------------------------------- SqrNode operator ----------------------------

template<typename ScalarType>
ScalarType& SqrNode<ScalarType>::operator()(int i)
{
  if(i<=this->m_maxComputedDerivative)
    return this->value[i];
  this->m_maxComputedDerivative = i;

  (*(this->left))(i);

  ScalarType result(0.);
  int k = (i >> 1); // k = i/2
  if(i%2) // in i is odd  we have result = sum_{j=0}^k 2*p[j]*p[i-j]
  {
    for(int j=0;j<=k;++j)
      result += ScalarType(2)*this->left->value[j]*this->left->value[i-j];
  }
  else
  {
    for(int j=0;j<k;++j)
      result += ScalarType(2)*this->left->value[j]*this->left->value[i-j];
    result += power(this->left->value[k],2);
  }
  return this->value[i] = result;
}

/// u^2+1   (used by atan and acot)
template<typename ScalarType>
ScalarType & Sqrp1Node<ScalarType>::operator()(int i)
{
  if(i>this->m_maxComputedDerivative) {
    this->m_maxComputedDerivative = i;
    (*(this->left))(i);
    ScalarType result(0.);
    int k = (i >> 1);
    if(i%2){ // in i is odd  we have result = sum_{j=0}^k 2*p[j]*p[i-j]

      for(int j=0;j<=k;++j)
        result += ScalarType(2)*this->left->value[j]*this->left->value[i-j];

    } else {

      for(int j=0;j<k;++j)
        result += ScalarType(2)*this->left->value[j]*this->left->value[i-j];
      result += power(this->left->value[k],2);
    }
    this->value[i] = result;
    if(i==0)
      zeroCoeff = result+1;
  }
  if(i)
    return this->value[i];
  else
    return zeroCoeff;
}

// ----------------------------------------- SqrtNode operator ----------------------------

template<typename ScalarType>
ScalarType& SqrtNode<ScalarType>::operator()(int i)
{
  if(i<=this->m_maxComputedDerivative)
    return this->value[i];
  this->m_maxComputedDerivative = i;

  (*(this->left))(i);
  if(!i)
  {
    if(!(this->left->value[0]>0))
    {
      std::ostringstream bufor;
      bufor << "function error: ScalarType sqrt error: nonpositive argument " << this->left->value[0];
      throw (std::runtime_error(bufor.str()));
    }
    return this->value[i] = sqrt(this->left->value[0]);
  }

  ScalarType result(0);
  for(int j=0;j<i;++j)
    result += ScalarType(0.5*(i-3*j)) * this->value[j] * this->left->value[i-j];

  return this->value[i] = result / (ScalarType(i) * this->left->value[0]);
}

/// sqrt1px2 = sqrt(1+x^2)
template<typename ScalarType>
ScalarType& Sqrt1px2Node<ScalarType>::operator()(int i){

  if(i>this->m_maxComputedDerivative){
   this->m_maxComputedDerivative = i;

   (*(this->left))(i);

   if(i == 0){
     ScalarType x = 1;
     if(!(this->left->value[0] > 0)) {
       std::ostringstream bufor;
       bufor << "function error: ScalarType sqrt error: nonpositive argument " << this->left->value[0];
       throw (std::runtime_error(bufor.str()));
     }
     this->value[i] = sqrt(1+this->left->value[0]);
   }

   ScalarType result(0);
   for(int j=0;j<i;++j)
     result += ScalarType(0.5*(i-3*j)) * this->value[j] * this->left->value[i-j];

    this->value[i] = result / (ScalarType(i) * this->left->value[0]);
   }
   return this->value[i];
}

/// sqrt1mx2 = sqrt(1-x^2)
template<typename ScalarType>
ScalarType& Sqrt1mx2Node<ScalarType>::operator()(int i){

  if(i>this->m_maxComputedDerivative){
    this->m_maxComputedDerivative = i;

    (*(this->left))(i);
    (*(this->right))(i);

    if(i != 0){
      // (f)_i = -1/2*((u^2)_i + \sum_{j=1}^{i-1} (f)_i * (f)_{i-j}) / (f)_0
      ScalarType result(0);
      for(int j=1;j<i;++j)
        result +=  this->value[j] * this->value[i-j];
      this->value[i] = ScalarType(-0.5)*(this->right->value[i]+result) /  this->value[0];

    } else { // i==0
      ScalarType x = this->left->value[0];
      if((!(x >= -1.0)) || (!(x <= 1.0))) {
              std::ostringstream bufor;
              bufor << "function sqrt1mx2 : argument has to be in [-1,1],  actual = " << x;
              throw (std::runtime_error(bufor.str()));
            }
      ScalarType fx = nonnegativePart(1 - power(x, 2));
      this->value[0] = sqrt(fx);
    }
  }
  return this->value[i];
}


/// sqrtx2m1 = sqrt(x^2-1)
template<typename ScalarType>
ScalarType& Sqrtx2m1Node<ScalarType> ::operator()(int i){

}


}} // namepsace capd::map

#endif // _CAPD_MAP_NODE_POWSQR_HPP_

/// @}
