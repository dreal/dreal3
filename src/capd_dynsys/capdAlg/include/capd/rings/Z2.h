/// @addtogroup vectalg
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file Z2.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (c) Marian  Mrozek, Krakow 2010
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#if !defined(_Z2_H_)
#define _Z2_H_

#include "capd/basicalg/TypeTraits.h"

/**********************************************************/
/*********** The field of integers modulo 2 ***************/
/**********************************************************/

#include <iostream>

class Z2{

  public:

    Z2(int k=0){
      val = (k % 2 != 0 ? 1U : 0U);
    }

    operator int(){
      return val;
    }

    friend Z2 operator-(const Z2 &v){
      return v;
    }

    friend Z2 operator+(const Z2 &v1,const Z2 &v2){
      return Z2(v1.val^v2.val);
    }
    friend Z2 operator-(const Z2 &v1,const Z2 &v2){
      return Z2(v1.val^v2.val);
    }
    friend Z2 operator*(const Z2 &v1,const Z2 &v2){
      return Z2(v1.val & v2.val);
    }
/*
    friend Z2 operator/(const Z2 &v1,const Z2 &v2){
      return Z2(v1.val / v2.val);
    }
*/


    Z2 &operator+=(const Z2 &v){
      val^=v.val;
      return *this;
    }
    Z2 &operator-=(const Z2 &v){
      val^=v.val;
      return *this;
    }
    Z2 &operator*=(const Z2 &v){
      val&=v.val;
      return *this;
    }
/*
    Z2 &operator/=(const Z2 &v){
      val/=v.val;
      return *this;
    }
*/

    Z2 &operator++(){
      val^=1U;
      return *this;
    }
    Z2 &operator--(){
      val^=1U;
      return *this;
    }

    Z2 operator++(int){
      Z2 z(*this);
      val^=1U;
      return z;
    }
    Z2 operator--(int){
      Z2 z(*this);
      val^=1U;
      return z;
    }

    friend bool operator<(const Z2 &v1,const Z2 &v2){
      return v1.val<v2.val;
    }
    friend bool operator>(const Z2 &v1,const Z2 &v2){
      return v1.val>v2.val;
    }
    friend bool operator<=(const Z2 &v1,const Z2 &v2){
      return v1.val<=v2.val;
    }
    friend bool operator>=(const Z2 &v1,const Z2 &v2){
      return v1.val>=v2.val;
    }
    friend bool operator==(const Z2 &v1,const Z2 &v2){
      return v1.val==v2.val;
    }
    friend bool operator!=(const Z2 &v1,const Z2 &v2){
      return v1.val!=v2.val;
    }

    friend std::ostream& operator<<(std::ostream &out,const Z2 &v){
      out << v.val;
      return out;
    }
    friend std::istream& operator>>(std::istream &inp, Z2 &v){
      while(' '==inp.peek()) inp.get();
      int a;
      inp >> a;
      v.val = ( a!=0 ? 1U : 0U);
      return inp;
    }

    friend inline bool isDivisible(Z2 a, Z2 b){
      return b.val!=0;
    }

    friend inline bool isInvertible(Z2 a){
      return a.val!=0;
    }

    friend inline Z2 inverse(Z2 a){
      return a;
    }

    friend inline std::string fieldStringForm(Z2){
      return "Z_2";
    }

  private:

    unsigned int val;

};// end of class Z2

namespace capd {

/**
* Traits of type Z2
*/
template <>
class TypeTraits<Z2> {
public:
  static inline int zero(){
    return 0;
  }
  static inline int one(){
    return 1;
  }
  static inline int numberOfDigits(){
    return 1;
  }
};

} // end of namespace capd

#endif //
/// @}



