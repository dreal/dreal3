/// @addtogroup vectalg
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file Zp.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (c) Marian  Mrozek, Krakow 2010
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#if !defined(_ZP_H_)
#define _ZP_H_

#include "capd/basicalg/TypeTraits.h"

/**********************************************************/
/*********** The field of integers modulo p ***************/
/**********************************************************/

#include <iostream>
#include <string>
#include "capd/auxil/stringOstream.h"

class Zp{
		static int egcd(int a,int b, int &g, int &x, int &y)
		{
			x=0,y=1;
			int u=1,v=0;
			int q,r,m,n;
			while(a!=0)
			{
				q=b/a;
				r=b%a; 
				m=x-u*q;
				n=y-v*q;
				b=a;
				a=r;
				x=u;
				y=v;
				u=m;
				v=n;
			}
			g=b;
		}
    static int normalize(int v){
      if(p){
        v%=p;
        if(v<0) v+=p;
      }
      return v;
    }
  public:

    static void setMod(int a_p){
      p=(a_p>=0 ? a_p : -a_p);
    }

    Zp(int v=0):val(v){
      if(p) val=normalize(val);
    }

    operator int(){
      return val;
    }

    friend Zp operator-(const Zp &v){
      return Zp(p-v.val);
    }

    friend Zp operator+(const Zp &v1,const Zp &v2){
      return Zp(v1.val+v2.val);
    }
    friend Zp operator-(const Zp &v1,const Zp &v2){
      return Zp(v1.val-v2.val);
    }
    friend Zp operator*(const Zp &v1,const Zp &v2){
      return Zp(v1.val * v2.val);
    }
    friend Zp operator/(const Zp &v1,const Zp &v2){
      if(p){
				int x,y,g;
				egcd(v2.val, p, g,x,y);
				return Zp(v1.val * x);
				/*
        unsigned int a=0;
        int i=1;
        for(;i<=p;++i){
          a+=v2.val;
          if(a % p == 1) break;
        }
        return Zp(v1.val * i);
				*/
      }else{
        return Zp(v1.val/v2.val);
      }
    }

    Zp &operator+=(const Zp &v){
      val=normalize(val+v.val);
      return *this;
    }
    Zp &operator-=(const Zp &v){
      val=normalize(val-v.val);
      return *this;
    }
    Zp &operator*=(const Zp &v){
      val=normalize(val*v.val);
      return *this;
    }

    Zp &operator/=(const Zp &v){
      *this=*this/v;
      return *this;
    }

    Zp &operator++(){
      val=normalize(++val);
      return *this;
    }
    Zp &operator--(){
      val=normalize(--val);
      return *this;
    }

    Zp operator++(int){
      Zp z(*this);
      val=normalize(++val);
      return z;
    }
    Zp operator--(int){
      Zp z(*this);
      val=normalize(--val);
      return z;
    }

    friend bool operator<(const Zp &v1,const Zp &v2){
      return v1.val<v2.val;
    }
    friend bool operator>(const Zp &v1,const Zp &v2){
      return v1.val>v2.val;
    }
    friend bool operator<=(const Zp &v1,const Zp &v2){
      return v1.val<=v2.val;
    }
    friend bool operator>=(const Zp &v1,const Zp &v2){
      return v1.val>=v2.val;
    }
    friend bool operator==(const Zp &v1,const Zp &v2){
      return v1.val==v2.val;
    }
    friend bool operator!=(const Zp &v1,const Zp &v2){
      return v1.val!=v2.val;
    }

    friend std::ostream& operator<<(std::ostream &out,const Zp &v){
      out << v.val;
      return out;
    }
    friend std::istream& operator>>(std::istream &inp, Zp &v){
      while(' '==inp.peek()) inp.get();
      inp >> v.val;
      v.val = normalize(v.val);
      return inp;
    }

    friend inline bool isDivisible(Zp a, Zp b){
      if(p){
        return b.val!=0;
      }else{
        return b.val!=0 && (a.val % b.val == 0);
      }
    }

    friend inline bool isInvertible(Zp a){
      if(p){
        return a.val!=0;
      }else{
        return (a.val==1 || a.val==-1);
      }
    }

    friend inline Zp inverse(Zp a){
      return Zp(1)/a;
    }

    friend inline std::string fieldStringForm(Zp){
      std::string s;
      if(p>0){
        s << "Z_" << p;
      }else{
        s << "Z";
      }
      return s;
    }
		friend inline bool isZero(const Zp& a)
		{
			return a.val == 0;
		}

  private:

    int val;
    static int p;

};// end of class Zp



namespace capd{

/**
* Traits of type Zp
*/
template <>
class TypeTraits<Zp> {
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



