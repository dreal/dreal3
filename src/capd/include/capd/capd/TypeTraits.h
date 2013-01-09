//////////////////////////////////////////////////////////////////////////////
//   Package:          CAPD

/////////////////////////////////////////////////////////////////////////////
//
/// @file TypeTraits.h
///
/// @author Tomasz Kapela   @date 2010-03-08
//
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Tomasz Kapela 2010
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_CAPD_TYPETRAITS_H_
#define _CAPD_CAPD_TYPETRAITS_H_

//#include "capd/interval/Interval.h"
//#include "capd/vectalg/Z2.h"
#include <limits>

namespace capd {

/**
 *  Defines type traits such as their values zero, one etc.
 *
 *  CAPD types should define specialization in their header files.
 *
 *  Known specialization are in
 *    - capd/interval/Interval.h
 *    - capd/interval/IComplex.h
 *    - capd/multiPrec/MpReal.h
 *    - capd/vectalg/Z2.h
 *
 */
template <typename T>
class TypeTraits {
public:
  typedef T Real;

  /// returns object set to zero
  static inline T zero(){
    return static_cast<T>(0.0);
  }
  /// returns object set to one
  static inline T one(){
    return static_cast<T>(1.0);
  }
  /// number of decimal digits
  static inline int numberOfDigits() throw(){
    return std::numeric_limits<T>::digits10;
  }
  /// Machine epsilon (the difference between 1 and the least value greater than 1 that is representable).
  static inline T epsilon() throw(){
    return std::numeric_limits<T>::epsilon();
  }
  /// this flag is true for all interval types
  static const bool isInterval = false;
};

/// for given type returns object that represents zero
template <typename T>
inline T zero(){
  return TypeTraits<T>::zero();
}

/// for given type returns object that represents one (identity)
template <typename T>
inline T one(){
  return TypeTraits<T>::one();
}


/**
 * Traits of type int
 */
template <>
class TypeTraits<int> {
public:
  typedef int Real;

  static inline int zero(){
    return 0;
  }
  static inline int one(){
    return 1;
  }
  static inline int numberOfDigits(){
      return std::numeric_limits<int>::digits10;
  }
  /// this flag is true for all interval types
  static const bool isInterval = false;

};


} // end of namespace capd

#endif // _CAPD_CAPD_TYPETRAITS_H_
