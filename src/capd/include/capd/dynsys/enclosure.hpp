/// @addtogroup dynsys
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file enclosure.hpp
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

/* Author: Daniel Wilczak 2001-2004 */

#ifndef _CAPD_DYNSYS_ENCLOSURE_HPP_ 
#define _CAPD_DYNSYS_ENCLOSURE_HPP_ 

#include <sstream>
#include <string>
#include <stdexcept>

#include "capd/dynsys/enclosure.h"
#include "capd/dynsys/TaylorException.h"

namespace capd{
namespace dynsys{


// the function finds an enclosure for \varphi([0,step],x)
template<typename MapType>
typename MapType::VectorType enclosure(  MapType  & vField,
                                         typename MapType::MatrixType::RowVectorType const & x, 
                                         typename MapType::ScalarType const & step
                                      ) {
  typedef typename MapType::ScalarType ScalarType;
  typedef typename MapType::VectorType VectorType;

  ScalarType trialStep = ScalarType(-0.2,1.2)*step;
  int dimension = x.dimension();
  VectorType y(dimension),z(dimension),Small(dimension);
  
  ScalarType h = ScalarType(0,1) * step;
  
  bool found = false;
  int counter=0,
      limit=10,    // maximum numbers of tries to find enclosure
      i;
  typename ScalarType::BoundType multf = 1.5;   // factor to multiply coordinates if inclusion fails
  
  for(i=0;i<dimension;++i)
    Small[i] = ScalarType(-1,1)*1e-21;
  
  VectorType val = vField(x);
  z = x + trialStep * val;
  z += Small; // to be sure that z has noempty interior
  
  while((!found) && (counter<limit)){
    counter++;
    y = x + h * vField(z);
    found = true;
    for(i=0;i< dimension;++i){
      if(!(y[i].subsetInterior(z[i]))){
        found = false;
        z[i] = y[i];
        ScalarType s;
        z[i].split(s);
        s = multf*s;
        z[i] += s;
      } 
    }
  }
  
  if(!found)
    throw TaylorException<VectorType>("Error: cannot find enclosure guaranteeing bounds",x,step);

  return y;
}


//###########################################################//

template<typename MapType, typename NormType>
typename MapType::MatrixType jacEnclosure(
                        const MapType& vectorField, 
                        const typename MapType::ScalarType& step,
                        const typename MapType::VectorType &enc, 
                        const NormType &the_norm,
                        typename MapType::ScalarType* o_logNormOfDerivative
                        )
// the function finds enclosure for Jacobian matrix (variational part)
// source- "C^1-Lohner algorithm" by P. Zgliczynski
{
  typedef typename MapType::MatrixType MatrixType;
  typedef typename MapType::ScalarType ScalarType;

  int dimension = enc.dimension();
  MatrixType der = vectorField[enc], result(dimension,dimension);

  ScalarType l = the_norm(der).rightBound(); // computation of lagarithmic norm
  ScalarType s = ScalarType(0,1)*step;
  ScalarType w = ScalarType(-1,1)*exp(s*l);

  MatrixType W(dimension,dimension); // W_3 in paper "C^1 - Lohner algorithm"
  W = w;

  result = MatrixType::Identity(dimension) + s*der*W;

  int i,j;
  for(i=1;i<=dimension;++i)
    for(j=1;j<=dimension;++j)
    {
      ScalarType d = result(i,j);
      typename ScalarType::BoundType 
         l = (w.leftBound() > d.leftBound() ? w.leftBound() : d.leftBound()),
         r = (w.rightBound() < d.rightBound() ? w.rightBound() : d.rightBound());
      result(i,j) = ScalarType(l,r);
    }
  if(o_logNormOfDerivative)
    *o_logNormOfDerivative = l;
  return result;
}


}} //namespace capd::dynsys

#endif // _CAPD_DYNSYS_ENCLOSURE_HPP_ 

/// @}
