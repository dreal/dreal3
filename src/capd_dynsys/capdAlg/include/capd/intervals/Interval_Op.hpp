/////////////////////////////////////////////////////////////////////////////
/// @file Interval_Op.hpp
///
/// Interval Arithmetics - operators definitions
///
/// @author Tomasz Kapela   @date 11-01-2006
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Tomasz Kapela 2006
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#ifndef _CAPD_INTERVAL_INTERVALOP_HPP_
#define _CAPD_INTERVAL_INTERVALOP_HPP_

#include "capd/intervals/IntervalError.h"
#include "capd/intervals/IntervalTraits.h"
#include <iostream>
#include <cstdio>

namespace capd{
namespace intervals{

//////////////////////////////////////////////////////////////////////////
//         ASSIGMENTS
//////////////////////////////////////////////////////////////////////////


//Operator=
template < typename T_Bound, typename T_Rnd>
__INLINE__ Interval<T_Bound, T_Rnd> & Interval<T_Bound, T_Rnd>::operator =
                                     (const Interval<T_Bound, T_Rnd>& A_iv)
{
  if(this != &A_iv)
  {
    m_left  = A_iv.m_left;
    m_right = A_iv.m_right;
  }
  return *this;
}

//Operator=
template < typename T_Bound, typename T_Rnd >
__INLINE__ Interval<T_Bound, T_Rnd> & Interval<T_Bound, T_Rnd>::operator =
                                                  (const BoundType & A_Val)
{
  T_Rnd::roundDown();
  m_left = BoundType(A_Val);
  T_Rnd::roundUp();
  m_right = BoundType(A_Val);
  return (*this);
}

//Operator +=
template < typename T_Bound, typename T_Rnd>
__INLINE__ Interval<T_Bound, T_Rnd> & Interval<T_Bound, T_Rnd>::operator +=
                                      (const Interval<T_Bound, T_Rnd>& A_iv)
{
  T_Rnd::roundDown();
  m_left  += A_iv.m_left;
  T_Rnd::roundUp();
  m_right += A_iv.m_right;
  checkInterval(" Operator += ", m_left, m_right);
  return *this;
}

//Operator  -=
template < typename T_Bound, typename T_Rnd>
__INLINE__ Interval<T_Bound, T_Rnd>& Interval<T_Bound, T_Rnd>::operator -=
                                     (const Interval<T_Bound, T_Rnd>& A_iv)
{
 // std::cout << "\n  operator -=  \nthis :" << *this << "   diam " << diam(*this) <<"\n  v " << A_iv << "   diam " << diam(A_iv);
  T_Rnd::roundDown();
  T_Bound temp = m_left - A_iv.m_right;   // in case this == &A_iv
  T_Rnd::roundUp();
  //m_right = m_right - A_iv.m_left;
  m_right -= A_iv.m_left;
  m_left = temp;
  //std::cout << "\n  result :" << *this << "   diam " << diam(*this);
  //std::cout << "  " << (A_iv.m_left == -m_right) << "   " << (A_iv.m_right == m_left);
  checkInterval(" Operator -= ", m_left, m_right);
  return *this;
}

//Operator *=
template < typename T_Bound, typename T_Rnd>
__INLINE__  Interval<T_Bound, T_Rnd>& Interval<T_Bound, T_Rnd>::operator *=
                                      (const Interval<T_Bound, T_Rnd>& A_iv)
{
  if((m_right == T_Bound(0.0)) && (m_left == T_Bound(0.0)))
    return *this;

  if((A_iv.m_right == T_Bound(0.0)) && (A_iv.m_left == T_Bound(0.0)))
  {
    m_left = T_Bound(0.0);
    m_right = T_Bound(0.0);
    return *this;
  }

  if(m_right <= 0)     // (--)
  {
    if(A_iv.m_right <= 0)   // (--)(--)
    {
      T_Rnd::roundDown();
      T_Bound temp = m_right * A_iv.m_right;
      T_Rnd::roundUp();
      m_right = m_left * A_iv.m_left;
      m_left = temp;
    }
    else
    if(A_iv.m_left >= 0)  // (--)(++)
    {
      T_Rnd::roundDown();
      m_left*=A_iv.m_right;
      T_Rnd::roundUp();
      m_right*=A_iv.m_left;
    }
    else                      // (--)(-+)
    {
      T_Rnd::roundDown();
      T_Bound temp = m_left * A_iv.m_right;
      T_Rnd::roundUp();
      m_right = m_left * A_iv.m_left;
      m_left=temp;
    }
  }
  else                // (m_right > 0)
  if(m_left >= 0)   //  (++)
  {
    if(A_iv.m_right <= 0)   // (++)(--)
    {
        T_Rnd::roundDown();
        T_Bound temp = m_right * A_iv.m_left;
        T_Rnd::roundUp();
        m_right = m_left * A_iv.m_right;
        m_left = temp;
    }
    else
    if(A_iv.m_left >= 0)   // (++)(++)
    {
      T_Rnd::roundDown();
      m_left *= A_iv.m_left;
      T_Rnd::roundUp();
      m_right *= A_iv.m_right;
    }
    else                       // (++)(-+)
    {
      T_Rnd::roundDown();
      m_left = m_right * A_iv.m_left;
      T_Rnd::roundUp();
      m_right *= A_iv.m_right;
    }
  }
  else //  m_left<=0 && m_right>=0 (-+)
  {
    if(A_iv.m_right <= 0)    // (-+)(--)
    {
        T_Rnd::roundDown();
        T_Bound temp = m_right * A_iv.m_left;
        T_Rnd::roundUp();
        m_right = m_left * A_iv.m_left;
        m_left = temp;
    }
    else
    if(A_iv.m_left >= 0 )    // (-+)(++)
    {
      T_Rnd::roundDown();
      m_left*=A_iv.m_right;
      T_Rnd::roundUp();
      m_right*=A_iv.m_right;
    }
    else                        // (-+)(-+)
    {
      T_Rnd::roundDown();
      T_Bound t1 = m_left * A_iv.m_right,
              t2 = m_right * A_iv.m_left,
              temp = (t1 > t2)? t2 : t1;
      T_Rnd::roundUp();
      t1 = m_left * A_iv.m_left;
      t2 = m_right * A_iv.m_right;
      m_right = (t1 < t2)? t2 : t1;
      //T_Rnd::roundDown();
      m_left = temp;
    }
  }
  checkInterval(" operator *= ", m_left, m_right);
  return *this;
} // operator *=

//Operator  /=
template < typename T_Bound, typename T_Rnd>
__INLINE__ Interval<T_Bound, T_Rnd>& Interval<T_Bound, T_Rnd>::operator /=
                                     (const Interval<T_Bound, T_Rnd>& A_iv)
{

  if(A_iv.m_right<0)
  {
    if(m_right<=0)             // (--)(--)
    {
      T_Rnd::roundDown();
      T_Bound temp = m_right / A_iv.m_left;
      T_Rnd::roundUp();
      m_right = m_left / A_iv.m_right;
      m_left = temp;
    }
    else    //   m_right > 0
    if(m_left >= 0)         // (++)(--)
    {
      T_Rnd::roundDown();
      T_Bound temp = m_right / A_iv.m_right;
      T_Rnd::roundUp();
      m_right = m_left / A_iv.m_left;
      m_left = temp;
    }
    else                     // (-+)(--)
    {
      T_Rnd::roundDown();
      T_Bound temp = m_right / A_iv.m_right;
      T_Rnd::roundUp();
      m_right = m_left / A_iv.m_right;
      m_left = temp;
    }
  }
  else
  if(A_iv.m_left > 0)
  {
    if(m_right <= 0)           // (--)(++)
    {
      T_Rnd::roundDown();
      m_left /= A_iv.m_left;
      T_Rnd::roundUp();
      m_right /= A_iv.m_right;
    }
    else
    if(m_left >= 0)            // (++)(++)
    {
      T_Rnd::roundDown();
      T_Bound temp = m_left / A_iv.m_right;
      T_Rnd::roundUp();
      m_right /= A_iv.m_left;
      m_left = temp;

    }
    else                      // (-+)(++)
    {
      T_Rnd::roundDown();
      m_left /= A_iv.m_left;
      T_Rnd::roundUp();
      m_right /= A_iv.m_left;
    }
  }
  else   /// (A_iv.m_left<=0 && A_iv.m_right>=0)
    throw IntervalError<T_Bound>("Error ***  Possible division by zero in operator /=", A_iv.m_left, A_iv.m_right );

  checkInterval(" Operator *= ", m_left, m_right);
  return *this;
}

//////////////////////////////////////////////////////////////////////////
//         Arithmetic operators
//////////////////////////////////////////////////////////////////////////


// operator +
template < typename T_Bound, typename T_Rnd>
__INLINE__
Interval< T_Bound, T_Rnd> operator +(const Interval< T_Bound, T_Rnd> & A_iv1,
                                     const Interval< T_Bound, T_Rnd> & A_iv2)
{
  Interval< T_Bound, T_Rnd> res;
  T_Rnd::roundDown();
  res.m_left = A_iv1.m_left + A_iv2.m_left;
  T_Rnd::roundUp();
  res.m_right = A_iv1.m_right + A_iv2.m_right;
  return res;
}// operator +

// operator -
template < typename T_Bound, typename T_Rnd>
__INLINE__
Interval< T_Bound, T_Rnd> operator -(const Interval< T_Bound, T_Rnd> & A_iv1,
                                     const Interval< T_Bound, T_Rnd> & A_iv2)
{
  Interval< T_Bound, T_Rnd> res;
  T_Rnd::roundDown();
  res.m_left = A_iv1.m_left - A_iv2.m_right;
  T_Rnd::roundUp();
  res.m_right = A_iv1.m_right - A_iv2.m_left;
  return res;
}// operator -

// operator *
template < typename T_Bound, typename T_Rnd>
__INLINE__
Interval< T_Bound, T_Rnd>  operator *(const Interval< T_Bound, T_Rnd>& A_iv1,
                                      const Interval< T_Bound, T_Rnd>& A_iv2)
{
  if(((A_iv1.m_left == 0) && (A_iv1.m_right == 0)) ||
     ((A_iv2.m_left == 0) && (A_iv2.m_right == 0)))
  {
    return (Interval< T_Bound, T_Rnd>(0.0,0.0));
  }

  T_Bound  left, right, t;

  if(A_iv1.m_left >= 0)
  {
    if(A_iv2.m_left >= 0)   // (++)(++)
    {
      T_Rnd::roundDown();
      left=A_iv1.m_left*A_iv2.m_left;
      T_Rnd::roundUp();
      right=A_iv1.m_right*A_iv2.m_right;
    }
    else
    if(A_iv2.m_right <= 0)  // (++)(--)
    {
      T_Rnd::roundDown();
      left = A_iv1.m_right * A_iv2.m_left;
      T_Rnd::roundUp();
      right = A_iv1.m_left * A_iv2.m_right;
    }
    else                      // (++)(-+)
    {
      T_Rnd::roundDown();
      left = A_iv1.m_right * A_iv2.m_left;
      T_Rnd::roundUp();
      right = A_iv1.m_right * A_iv2.m_right;
    }
  }
  else
  if(A_iv1.m_right <= 0)
  {
    if(A_iv2.m_right <= 0)  // (--)(--)
    {
      T_Rnd::roundDown();
      left=A_iv1.m_right*A_iv2.m_right;
      T_Rnd::roundUp();
      right=A_iv1.m_left*A_iv2.m_left;
    }
    else
    if(A_iv2.m_left >= 0)    // (--)(++)
    {
      T_Rnd::roundDown();
      left=A_iv1.m_left*A_iv2.m_right;
      T_Rnd::roundUp();
      right=A_iv1.m_right*A_iv2.m_left;
    }
    else                       // (--)(-+)
    {
      T_Rnd::roundDown();
      left=A_iv1.m_left*A_iv2.m_right;
      T_Rnd::roundUp();
      right=A_iv1.m_left*A_iv2.m_left;
    }
  }
  else  // (A_iv1.m_left <=0) && (A_iv1.m_right > 0) (-+)
  {
    if(A_iv2.m_right <= 0)  // (-+)(--)
    {
      T_Rnd::roundDown();
      left=A_iv1.m_right*A_iv2.m_left;
      T_Rnd::roundUp();
      right=A_iv1.m_left*A_iv2.m_left;
    }
    else
    if (A_iv2.m_left >=0)  // (-+)(++)
    {
      T_Rnd::roundDown();
      left=A_iv1.m_left*A_iv2.m_right;
      T_Rnd::roundUp();
      right=A_iv1.m_right*A_iv2.m_right;
    }
    else                     // (-+)(-+)
    {
      T_Rnd::roundDown();
      left = A_iv1.m_left * A_iv2.m_right;
      t = A_iv2.m_left * A_iv1.m_right;
      if(t < left)
        left = t;
      T_Rnd::roundUp();
      right = A_iv1.m_left * A_iv2.m_left;
      t = A_iv1.m_right * A_iv2.m_right;
      if(t > right)
        right = t;
    }
  }
  checkInterval("Error *** Fatal Interval error in operator*(Interval, Interval) .", left, right);
  return Interval< T_Bound, T_Rnd>(left,right);
} // operator *


//Operator  /
template < typename T_Bound, typename T_Rnd>
__INLINE__
Interval< T_Bound, T_Rnd> operator /(const Interval< T_Bound, T_Rnd>& A_iv1,
                                     const Interval< T_Bound, T_Rnd>& A_iv2)
{
  T_Bound left, right;

  if(A_iv2.m_right < 0)
  {
    if(A_iv1.m_right <= 0)   // (--)(--)
    {
        T_Rnd::roundDown();
        left = A_iv1.m_right / A_iv2.m_left;
        T_Rnd::roundUp();
        right= A_iv1.m_left / A_iv2.m_right;
    }
    else
    if(A_iv1.m_left >= 0)       // (++)(--)
    {
      T_Rnd::roundDown();
      left = A_iv1.m_right / A_iv2.m_right;
      T_Rnd::roundUp();
      right = A_iv1.m_left / A_iv2.m_left;
    }
    else                        // (-+)(--)
    {
      T_Rnd::roundDown();
      left = A_iv1.m_right / A_iv2.m_right;
      T_Rnd::roundUp();
      right = A_iv1.m_left / A_iv2.m_right;
    }
  }
  else
  if(A_iv2.m_left > 0)
  {
    if(A_iv1.m_right <= 0)      // (--)(++)
    {
      T_Rnd::roundDown();
      left = A_iv1.m_left / A_iv2.m_left;
      T_Rnd::roundUp();
      right = A_iv1.m_right / A_iv2.m_right;
    }
    else
    if(A_iv1.m_left >= 0)       // (++)(++)
    {
      T_Rnd::roundDown();
      left = A_iv1.m_left / A_iv2.m_right;
      T_Rnd::roundUp();
      right = A_iv1.m_right / A_iv2.m_left;
    }
    else                         // (-+)(++)
    {
      T_Rnd::roundDown();
      left = A_iv1.m_left / A_iv2.m_left;
      T_Rnd::roundUp();
      right = A_iv1.m_right / A_iv2.m_left;
    }
  }
  else //  (??) (-+)
    throw IntervalError<T_Bound>("Interval Error *** Possible division by zero.",
                                  A_iv2.m_left, A_iv2.m_right);

  checkInterval(" operator* ", left, right);
  return (Interval< T_Bound, T_Rnd>(left, right));

} // operator /


// sending an Interval to a stream
template < typename T_Bound, typename T_Rnd>
__INLINE__ std::ostream & operator << (std::ostream & s,
                                   const Interval< T_Bound, T_Rnd > & A_iv)
{
   T_Rnd::roundDown();
   s << "[" << A_iv.m_left << ",";
   T_Rnd::roundUp();
   s << A_iv.m_right << "]";
   return s;
}

// reading from the stream
template < typename T_Bound, typename T_Rnd>
__INLINE__ std::istream &operator>>(std::istream &inp, Interval< T_Bound, T_Rnd> &i)
{
  int ch;
  T_Bound ll, rr;

  while('['!=(ch=inp.get()) && ch!=EOF)
    ;
  if(ch!=EOF)
  {
    T_Rnd::roundDown();
    inp >> ll;
    // read white spaces
    inp >> std::ws;
    if(inp.get()==',')
    {
      T_Rnd::roundUp();
      inp >> rr;
      // read white spaces
      inp >> std::ws;
      if(inp.get()==']')
      {
        if(ll <= rr)
        {
          i.m_left=ll;
          i.m_right=rr;
        }
        return inp;
      }
    }
  }
  i.m_left = i.m_right = 0.0;
  return inp;
} // operator >> (istream, Interval)



template < typename T_Bound, typename T_Rnd>
std::ostream & bitWrite(std::ostream & out, const Interval< T_Bound, T_Rnd > &iv){
	 out << "[";
     IntervalIOTraits<T_Bound>::bitWrite(out, iv.leftBound());
     out << ",";
     IntervalIOTraits<T_Bound>::bitWrite(out, iv.rightBound());
	 out << "]";
	 return out;
}
template < typename T_Bound, typename T_Rnd>
std::istream & bitRead(std::istream & inp, Interval< T_Bound, T_Rnd > &iv){
	T_Bound ll, rr;
	inp >> std::ws;
	if('['==inp.get()){
		inp >> std::ws;
		IntervalIOTraits<T_Bound>::bitRead(inp, ll);
		// read white spaces
		inp >> std::ws;
		if(inp.get()==',')
		{
			inp >> std::ws;
			IntervalIOTraits<T_Bound>::bitRead(inp, rr);

			// read white spaces
			inp >> std::ws;
			if(inp.get()==']')
			{
				checkInterval(" bitRead ", ll, rr);
				iv.m_left=ll;
				iv.m_right=rr;
				return inp;
			}
		}
	}
	iv.m_left = iv.m_right = 0.0;
	return inp;
}
template < typename T_Bound, typename T_Rnd>
std::ostream & hexWrite(std::ostream & out, const Interval< T_Bound, T_Rnd > &iv){
	out << "[";
	IntervalIOTraits<T_Bound>::hexWrite(out, iv.leftBound());
	out << ",";
	IntervalIOTraits<T_Bound>::hexWrite(out, iv.rightBound());
	out << "]";
	return out;
}
template < typename T_Bound, typename T_Rnd>
std::istream & hexRead(std::istream & inp, Interval< T_Bound, T_Rnd > &iv){
	T_Bound ll, rr;
	inp >> std::ws;
	if('['==inp.get()){
		inp >> std::ws;
		IntervalIOTraits<T_Bound>::hexRead(inp, ll);
		// read white spaces
		inp >> std::ws;
		if(inp.get()==',')
		{
			inp >> std::ws;
			IntervalIOTraits<T_Bound>::hexRead(inp, rr);

			// read white spaces
			inp >> std::ws;
			if(inp.get()==']')
			{
				checkInterval(" bitRead ", ll, rr);
				iv.m_left=ll;
				iv.m_right=rr;
				return inp;
			}
		}
	}
	iv.m_left = iv.m_right = 0.0;
	return inp;
}
template < typename T_Bound, typename T_Rnd>
std::ostream & binWrite(std::ostream & out, const Interval< T_Bound, T_Rnd > &iv){
	return out.write((const char *)&iv, sizeof(Interval< T_Bound, T_Rnd >));
}
template < typename T_Bound, typename T_Rnd>
std::istream & binRead(std::istream & in, Interval< T_Bound, T_Rnd > &iv){
	return in.read((char *)&iv, sizeof(Interval< T_Bound, T_Rnd >));
}

// Interval + BoundType
template < typename T_Bound, typename T_Rnd>
__INLINE__ Interval< T_Bound, T_Rnd> add(const Interval< T_Bound, T_Rnd> & A_iv,
                                         const T_Bound &A_x)
{
  T_Rnd::roundDown();
  T_Bound left = A_iv.leftBound() + A_x;
  T_Rnd::roundUp();
  T_Bound right = A_iv.rightBound() + A_x;
  return Interval< T_Bound, T_Rnd>(left, right);
}


// Interval - BoundType
template < typename T_Bound, typename T_Rnd>
__INLINE__ Interval< T_Bound, T_Rnd> substract(const Interval< T_Bound, T_Rnd> & A_iv,
                                               const T_Bound &A_x)
{
  T_Rnd::roundDown();
  T_Bound left = A_iv.leftBound() - A_x;
  T_Rnd::roundUp();
  T_Bound right = A_iv.rightBound() - A_x;
  return Interval< T_Bound, T_Rnd>(left, right);
}

// BoundType - Interval
template < typename T_Bound, typename T_Rnd>
__INLINE__ Interval< T_Bound, T_Rnd> substract(const T_Bound  &A_x,
                                               const Interval< T_Bound, T_Rnd> & A_iv)
{
  T_Rnd::roundDown();
  T_Bound left = A_x - A_iv.rightBound();
  T_Rnd::roundUp();
  T_Bound right = A_x - A_iv.leftBound();
  return Interval< T_Bound, T_Rnd>(left, right);
}

// Interval * BoundType
template < typename T_Bound, typename T_Rnd>
__INLINE__ Interval< T_Bound, T_Rnd> multiply(const Interval< T_Bound, T_Rnd>& A_iv,
                                              const T_Bound& A_x)
{
   if(((A_iv.leftBound()==0.0) && (A_iv.rightBound()==0.0)) || (A_x==0.0))
   {
     return Interval< T_Bound, T_Rnd>(T_Bound(0),T_Bound(0));
   }

   T_Bound left, right;
   if(A_x>0)
   {
      T_Rnd::roundDown();
      left = A_iv.leftBound() * A_x;
      T_Rnd::roundUp();
      right = A_iv.rightBound() * A_x;
   }
   else
   {
      T_Rnd::roundDown();
      left = A_iv.rightBound() * A_x;
      T_Rnd::roundUp();
      right = A_iv.leftBound() * A_x;
   }
   return Interval< T_Bound, T_Rnd>(left, right);
}


// Interval / BoundType
template < typename T_Bound, typename T_Rnd>
__INLINE__ Interval< T_Bound, T_Rnd> divide(const Interval< T_Bound, T_Rnd>& A_iv,
                                            const T_Bound& A_x)
{
   if(A_x==0.0)
     throw IntervalError< T_Bound >(" Division by zero in divide(Interval, BoundType) ", A_x,A_x);

   T_Bound left, right;
   if(A_x>0)
   {
      T_Rnd::roundDown();
      left = A_iv.leftBound() / A_x;
      T_Rnd::roundUp();
      right = A_iv.rightBound() / A_x;
   }
   else
   {
      T_Rnd::roundDown();
      left = A_iv.rightBound() / A_x;
      T_Rnd::roundUp();
      right = A_iv.leftBound() / A_x;
   }
   return Interval< T_Bound, T_Rnd>(left, right);
}


//   BoundType / Interval
template < typename T_Bound, typename T_Rnd>
__INLINE__  Interval< T_Bound, T_Rnd> divide(const T_Bound& A_x,
                                             const Interval< T_Bound, T_Rnd>& A_iv)
{
   if(A_iv.contains(0.0))
     throw IntervalError< T_Bound >(" Division by zero in divide(BoundType, Interval) ",
                                    A_iv.leftBound(), A_iv.rightBound());

   T_Bound left, right;
   if(A_x>=0)
   {
      T_Rnd::roundDown();
      left = A_x / A_iv.rightBound();
      T_Rnd::roundUp();
      right = A_x / A_iv.leftBound();
   }
   else
   {
      T_Rnd::roundDown();
      left = A_x / A_iv.leftBound();
      T_Rnd::roundUp();
      right = A_x / A_iv.rightBound();
   }
   return Interval< T_Bound, T_Rnd>(left, right);
}

}} // namespace capd::intervals


#endif // _CAPD_INTERVAL_INTERVALOP_HPP_
