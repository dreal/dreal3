/// @addtogroup facade
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file ITaylor.h
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

/* Author: Daniel Wilczak 2001-2005 */

#ifndef _CAPD_ITAYLOR_H_
#define _CAPD_ITAYLOR_H_

#include "capd/IMap.h"
#include "capd/dynsys/Taylor.h"
#include "capd/map/C2Coeff.h"
#include "capd/dynset/C2Set.h"

namespace capd{

class ITaylor : public capd::dynsys::C1DynSys<IMatrix>
{
public:
  typedef IMap MapType;
  typedef capd::dynsys::Taylor<IMap> BaseTaylor;
  typedef IFunction FunctionType;
  typedef IMatrix MatrixType;
  typedef IVector VectorType;
  typedef DInterval ScalarType;
  typedef capd::vectalg::Norm<VectorType,MatrixType> NormType;
  typedef capd::map::C2Coeff<IMatrix> C2CoeffType;

  ITaylor(MapType& field, int order, const ScalarType& step)
    : m_vectorField(&field),
      m_taylor(*m_vectorField,order,step),
      m_hasOwnVectorField(false)
  {}

  ITaylor(const std::string& field, int order, const ScalarType& step)
    : m_vectorField(new MapType(field,order+1)),
      m_taylor(*m_vectorField,order,step),
      m_hasOwnVectorField(true)
  {}

  ITaylor(const char* field, int order, const ScalarType& step)
    : m_vectorField(new MapType(field,order+1)),
      m_taylor(*m_vectorField,order,step),
      m_hasOwnVectorField(true)
  {}

  VectorType Phi(const VectorType& iv) {
    return m_taylor.Phi(iv);
  }
  MatrixType JacPhi(const VectorType& iv) {
    return m_taylor.JacPhi(iv);
  }
  VectorType Remainder(const VectorType& iv) {
    return m_taylor.Remainder(iv);
  }

  void JacRemainder(
         const VectorType &vecEnclosure,
         const MatrixType &jacEnclosure,
         VectorType &vRemainder,
         MatrixType &jRemainder
      )
  {
    return m_taylor.JacRemainder(vecEnclosure,jacEnclosure,vRemainder,jRemainder);
  }

  VectorType enclosure(const VectorType& x, int* found) {
    return m_taylor.enclosure(x,found);
  }

  VectorType enclosure(const VectorType &x) {
    return m_taylor.enclosure(x);
  }

  MatrixType jacEnclosure(const VectorType& enc, const NormType& norm) {
    return m_taylor.jacEnclosure(enc,norm);
  }

  const MapType& getField() const{
    return m_taylor.getField();
  }

  int getOrder() const{
    return m_taylor.getOrder();
  }
  void setOrder(int newOrder){
    m_taylor.setOrder(newOrder);
  }

  ScalarType getStep() const{
    return m_taylor.getStep();
  }

  void setStep(const ScalarType& newStep){
    m_taylor.setStep(newStep);
  }

  void setParameter(const std::string &name, const ScalarType& value){
    m_vectorField->setParameter(name,value);
  }

  ScalarType getCoeffNorm(int i) const
  {
    return m_taylor.getCoeffNorm(i);
  }

  ~ITaylor(){
    if(m_hasOwnVectorField)
      delete m_vectorField;
  }

private:
  ITaylor& operator=(const ITaylor& a_t){return *this;}
  MapType* m_vectorField;
  BaseTaylor m_taylor;
  bool m_hasOwnVectorField;
};

} // namespace capd:

#endif // define _CAPD_ITAYLOR_H_

/// @}
