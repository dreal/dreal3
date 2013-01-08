// @addtogroup capd
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file FactorPolicy.h
///
/// @author kapela
/// Created on: Oct 21, 2009
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2009 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_FACTORPOLICY_H_
#define _CAPD_FACTORPOLICY_H_

#include <sstream>
namespace capd{
namespace dynset{

class MemberFactorPolicy{
public:
  MemberFactorPolicy(double factor=0.0) : m_sizeFactor(factor){
  }
  /// sets m_sizeFactor
  void setFactor(double A_factor){
    m_sizeFactor = A_factor;
  }
  /// return actual m_sizeFactor
  double getFactor() const{
    return m_sizeFactor;
  }
  //
  void disableReorganization(){
    m_sizeFactor = 0.0;
  }
  bool isReorganizationEnabled() const{
    return (m_sizeFactor!=0.0);
  }
  /// @deprecated
  void disableSwapping(){
    disableReorganization();
  }
  std::string toString() const {
     std::ostringstream str;
     str << " m_sizeFactor = " << m_sizeFactor;
     return str.str();
  }
protected:
  double m_sizeFactor;
};


template <typename T>
class StaticFactorPolicy{
public:
  StaticFactorPolicy(double m_sizeFactor=0.0){
  }
  /// sets m_sizeFactor
  static void setFactor(double A_factor){
    m_sizeFactor = A_factor;
  }
  /// return actual m_sizeFactor
  static double getFactor(){
    return m_sizeFactor;
  }
  //
  static void disableReorganization(){
    m_sizeFactor = 0.0;
  }
  static bool isReorganizationEnabled(){
    return ( m_sizeFactor!=0.0);
  }
  /// @deprecated
  static void disableSwapping(){
    disableReorganization();
  }
  std::string toString() const {
       std::ostringstream str;
       str << " m_sizeFactor = " << m_sizeFactor;
       return str.str();
    }
protected:
  static double m_sizeFactor;
};

template <typename T>
double StaticFactorPolicy<T>::m_sizeFactor = 0.0;

}}
#endif // _CAPD_FACTORPOLICY_H_

/// @}
