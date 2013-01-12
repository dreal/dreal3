
/////////////////////////////////////////////////////////////////////////////
/// @file DFunction.h
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifndef _CAPD_FACADE_DFUNCTION_H_
#define _CAPD_FACADE_DFUNCTION_H_

#include <string>
#include "capd/map/Function.h"
#include "capd/facade/DVector.h"

namespace capd{
namespace facade{

class DFunction
{
public:
  typedef double ScalarType;
  typedef DVector VectorType;
  typedef capd::map::Function<DVector> BaseFunction;

  DFunction(const char *s, int order = 0) 
    : m_f(s,order)
  {}
  DFunction(const std::string &s, int order = 0)
    : m_f(s,order)
  {}
  DFunction(void) {}
  DFunction(const DFunction & f)
    : m_f(f.m_f)
  {}
  ~DFunction(void){}
  
  const std::string& formula(void) const {
    return m_f.formula();
  }
  const std::string& partialDerivative(int i) const{
    return m_f.partialDerivative(i);
  }
  std::string gradient(int i) const{
    return m_f.gradient(i);
  }
  VectorType gradient(const VectorType &u){
    return m_f.gradient(u);
  }
  
  void setOrder (int order){
    m_f.setOrder(order);
  }
  
  DFunction& operator= (const char *s){
    m_f=s;
    return *this;
  }
  DFunction& operator= (const std::string &s){
    m_f=s;
    return *this;
  }
  DFunction& operator= (const DFunction &s){
    m_f = s.m_f;
    return *this;
  }
  
  std::string operator[] (int i) const{
    return m_f[i];
  }
  
  ScalarType operator() (const ScalarType& v) const{
    return m_f(v);
  }
  ScalarType operator() (const VectorType &u) const{
    return m_f(u);
  }
  ScalarType operator() (const VectorType &v, int i) const{
    return m_f(v,i);
  }
  
  void setParameter(const std::string & s, ScalarType value){
    m_f.setParameter(s,value);
  }
  
  void differentiateTime(int index) const
  {
    m_f.differentiateTime(index);
  }

  void setCurrentTime(const ScalarType& a_time, int index) const
  {
    m_f.setCurrentTime(a_time,index);
  }
  
  const ScalarType& getCurrentTime(int index) const
  {
    return m_f.getCurrentTime(index);
  }

  std::string variables() const{
    return m_f.variables();
  }
  
  int dimension() const{
    return m_f.dimension();
  }
  
protected:
  BaseFunction m_f;
};

}} // namespace capd::facade

#endif //define _CAPD_FACADE_DFUNCTION_H_

