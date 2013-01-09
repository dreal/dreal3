/// @addtogroup facade
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file DMap.h
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifndef _CAPD_DMAP_H_
#define _CAPD_DMAP_H_

#include "capd/map/Map.h"
#include "capd/DMatrix.h"
#include "capd/DFunction.h"

namespace capd{

class DMap
{
public:
  typedef double ScalarType;
  typedef DVector VectorType;
  typedef DMatrix MatrixType;
  typedef DFunction FunctionType;

  typedef capd::map::Map<DMatrix> BaseMap;
  
  DMap(void){}
  DMap(const std::string &s, int order=0)
    : m_M(s,order)
  {}
  DMap(const char *s, int order=0) 
    : m_M(s,order)
  {}
  DMap(const DMap & s)
    : m_M(s.m_M)
  {}

  DMap &operator=(const char *s){
    m_M = s;
    return *this;
  }
  DMap &operator=(const std::string &s){
    m_M =s;
    return *this;
  }
  DMap &operator=(const DMap &s){
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

  void setParameter(const std::string &name, const ScalarType& value){
    m_M.setParameter(name,value);
  }
  void setOrder(int the_new){
    m_M.setOrder(the_new);
  }
  int dimension() const{
    return m_M.dimension();
  }

protected:
  BaseMap m_M;
}; // the end of class DMap


} // the end of the namespace capd

#endif //define _CAPD_DMAP_H_

/// @}
