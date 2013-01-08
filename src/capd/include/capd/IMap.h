/// @addtogroup facade
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file IMap.h
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifndef _CAPD_IMAP_H_
#define _CAPD_IMAP_H_

#include "capd/map/Map.h"
#include "capd/IMatrix.h"
#include "capd/IFunction.h"

namespace capd{

class IMap
{
public:
  typedef DInterval ScalarType;
  typedef IVector VectorType;
  typedef IMatrix MatrixType;
  typedef IFunction FunctionType;

  typedef capd::map::Map<IMatrix> BaseMap;
  
  IMap(void){}
  IMap(const std::string &s, int order=0)
    : m_M(s,order)
  {}
  IMap(const char *s, int order=0) 
    : m_M(s,order)
  {}
  IMap(const IMap & s)
    : m_M(s.m_M)
  {}

  IMap &operator=(const char *s){
    m_M = s;
    return *this;
  }
  IMap &operator=(const std::string &s){
    m_M =s;
    return *this;
  }
  IMap &operator=(const IMap &s){
    m_M = s.m_M;
    return *this;
  }

  VectorType operator()(const VectorType &u, int i= 0) const{
    return m_M(u,i);
  }
  VectorType operator()(const VectorType &u, MatrixType &der) const{
    return m_M(u,der);
  }
  MatrixType operator[](const VectorType &u) const{
    return m_M[u];
  }

  void variational(VectorType u[], MatrixType der[], int i) const{
    m_M.variational(u,der,i);
  }
  std::string variables() const {
    return m_M.variables();
  }

  void setParameter(const std::string &name, const ScalarType& value){
    m_M.setParameter(name,value);
  }
  void setOrder(int the_new){
    m_M.setOrder(the_new);
  }
  int dimension() const{
    return m_M.dimension();
  }

  void differentiateTime() const
  {
    m_M.differentiateTime();
  }

  void setCurrentTime(const ScalarType& a_time) const
  {
    m_M.setCurrentTime(a_time);
  }
  
  const ScalarType& getCurrentTime() const
  {
    return m_M.getCurrentTime();
  }

protected:
  BaseMap m_M;
}; // the end of class IMap


} // the end of the namespace capd

#endif //define _CAPD_IMAP_H_

/// @}
