/// @addtogroup struct
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file integer.h
///
/// This file defines a class "integer" which represents the ring of
/// integers or the field of integers modulo a prime number "p"
/// as an Euclidean domain, with some extra features which are required
/// by the homology software.
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2008 by Pawel Pilarczyk.
//
// This file is part of the Homology Library.  This library is free software;
// you can redistribute it and/or modify it under the terms of the GNU
// General Public License as published by the Free Software Foundation;
// either version 2 of the License, or (at your option) any later version.
//
// This library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License along
// with this software; see the file "license.txt".  If not, write to the
// Free Software Foundation, Inc., 59 Temple Place - Suite 330, Boston,
// MA 02111-1307, USA.

// Started in December 1999. Last revision: July 4, 2005.


#ifndef _CHOMP_STRUCT_INTEGER_H_
#define _CHOMP_STRUCT_INTEGER_H_

#include "config.h"
#include "textfile.h"

#include <iostream>

namespace chomp {
namespace homology {


// classes defined in this module (in this order):
class primeint;
class integer;


// --------------------------------------------------
// ------------------ prime number ------------------
// --------------------------------------------------

/// This is a simple class which is a wrapper for computing
/// the smallest prime number greater or equal to the given integer.
class primeint
{
public:
	/// The constructor which computes the smallest prime number
	/// greater than or equal to the given one.
	primeint (int k = 0);

	/// The assignment operator.
	primeint &operator = (const primeint &p);

	/// The assignment operator which also rounds up to the nearest
	/// prime number.
	primeint &operator = (int k);

	/// The conversion operator to an integer number which extracts
	/// the prime number.
	operator int () const;

private:
	/// The actual prime number stored in this class.
	int n;

}; /* class primeint */

// --------------------------------------------------

inline primeint::operator int () const
{
	return n;
} /* primeint::operator int */

inline primeint &primeint::operator = (const primeint &p)
{
	n = p. n;
	return *this;
} /* primeint::operator = */

// --------------------------------------------------

/// Writes an object of the type "primeint" to an output stream.
inline std::ostream &operator << (std::ostream &out, const primeint &p)
{
	out << (int) p;
	return out;
} /* operator << */

/// Reads a prime number from an input stream. If the actual number that
/// is read is not prime then it is increased as much as necessary
/// to obtain a prime number.
inline std::istream &operator >> (std::istream &in, primeint &p)
{
	int n;
	in >> n;
	p = n;
	return in;
} /* operator >> */


// --------------------------------------------------
// -------------------- integer ---------------------
// --------------------------------------------------

/// The type of number used to store the value of an object of type
/// "integer". Note that "signed short" (or even "signed char")
/// uses less memory but limits the range of correctly stored numbers
/// which may cause to interrupt the computations in the numbers
/// become too large. Use "signed long" for large prime numbers.
typedef signed short numbertype;

/// This class defines integer numbers with overflow control
/// and with some specific properties of an Euclidean domain.
/// Note that this class has very few features which are limited
/// on purpose to optimize it for application in a chain complex class
/// for homology computation.
class integer
{
public:
	// default constructor
	//	explicit integer (int n = 0);

		// The destructor.
	//	~integer (void);

		// copying constructor
	//	integer (const integer &e);

		// assignment operator(s)
		integer &operator = (int n);
	//	integer &operator = (const integer &e);

		// initialize the integers:
		// define integers modulo p or set p to 0 (default)
		static int initialize (int n);

		// the function "delta": equal to 0 on 0,
		// equal to 1 on invertibles, otherwise > 1
		int delta (void) const;

		// a normalized number (a better representant for homology)
		integer normalized () const;

		// several operators
		integer operator - () const;
		integer &operator += (const integer &n);
		integer &operator *= (const integer &n);
		integer operator + (const integer &n) const;
		integer operator * (const integer &n) const;
		integer operator / (const integer &n) const;
		integer operator % (const integer &n) const;
		int operator == (const integer &n) const;

		static const char *ringname ();
		static const char *ringsymbol ();

		friend std::ostream &operator << (std::ostream &out, const integer &n);
		friend bool operator < (const integer &x, const integer &y);
		friend bool operator > (const integer &x, const integer &y);

	protected:
		// the number modulo which the computations are performed
		static int p;

		// the integer number
		numbertype num;

		// various additional procedures
		static int cut_down (int n);
		static int is_prime (int n);
		static int prime_number (int n);
		static unsigned invert (unsigned n, unsigned q);

}; /* class integer */

// --------------------------------------------------

inline int integer::cut_down (int n)
{
	if (n >= 0)
		if (n < p)
			return n;
		else
			return (n % p);
	else
	{
		int num = p - ((-n) % p);
		if (num == p)
			return 0;
		else
			return num;
	}
} /* cut_down */

/* inline integer::integer (int n)
{
	if (p)
		num = (numbertype) cut_down (n);
	else
	{
		num = (numbertype) n;
		if ((long) num != (long) n)
			throw "Number out of range at initialization.";
	}
	return;
} */ /* integer::integer */

/* inline integer::~integer ()
{
	return;
} */ /* integer::~integer */

/* inline integer::integer (const integer &e)
{
	num = e. num;
	return;
} */ /* integer::integer */

/* inline integer &integer::operator = (const integer &e)
{
	num = e. num;
	return *this;
} */ /* integer::operator = */

inline integer &integer::operator = (int n)
{
	if (p)
		num = (numbertype) cut_down (n);
	else
	{
		num = (numbertype) n;
		if ((long) num != (long) n)
			throw "Number out of range at assignment.";
	}
	return *this;
} /* integer::operator = */

inline integer integer::operator / (const integer &n) const
{
	integer result;
	if (p)
		result = num * (int) invert (n. num, p);
	else
		result. num = (numbertype) (num / n. num);
	return result;
} /* integer::operator / */

inline integer integer::operator % (const integer &n) const
{
	integer result;
	if (p)
		result. num = 0;
	else
		result = num % n. num;
	return result;
} /* operator % */

inline integer integer::operator - () const
{
	if (p)
	{
		integer negative;
		negative. num = (numbertype) (p - num);
		return negative;
	}
	else
	{
		numbertype result = (numbertype) -num;
		if ((long) result + (long) num != 0)
			throw "Number out of range (unary -).";
		integer intresult;
		intresult = result;
		return intresult;
	}
} /* integer::operator - (unary) */

inline integer &integer::operator += (const integer &n)
{
	if (!p)
		if (((n. num >= 0) && (num + n. num < num)) ||
			((n. num < 0) && (num + n. num > num)))
			throw "Number out of range (+).";
	num += n. num;
	if (p)
		if (num >= p)
			num -= (numbertype) p;
	return *this;
} /* integer::operator += */

inline integer &integer::operator *= (const integer &n)
{
	if (p)
	{
		long result = (long) num * (long) n. num;
		if (result >= 0)
			num = (numbertype) (result % p);
		else
		{
			num = (numbertype) (p - ((-result) % p));
			if (num == p)
				num = 0;
		}
	}
	else
	{
		long result = (long) num * (long) (n. num);
		num = (numbertype) result;
		if ((long) num != result)
			throw "Number out of range (*).";
	}
	return *this;
} /* integer::operator *= */

inline integer integer::operator + (const integer &n) const
{
	integer m (n);
	m += *this;
	return m;
} /* operator + */

inline integer integer::operator * (const integer &n) const
{
	integer m (n);
	m *= *this;
	return m;
} /* operator * */

inline int integer::operator == (const integer &n) const
{
	return (n. num == num);
} /* operator == */

inline std::ostream &operator << (std::ostream &out, const integer &n)
{
	out << (long) n. num;
	return out;
} /* operator << */

inline std::istream &operator >> (std::istream &in, integer &n)
{
	long number;
	in >> number;
	if (!in)
		return in;
	n = number;
	return in;
} /* operator >> */

inline int operator != (const integer &n, const integer &m)
{
	return (!(n == m));
} /* operator != */

inline int operator == (const integer &n, int m)
{
	integer intm;
	intm = m;
	return (n == intm);
} /* operator == */

inline int operator != (const integer &n, int m)
{
	return !(n == m);
} /* operator != */

inline integer operator - (const integer &n, const integer &m)
{
	return (n + -m);
} /* operator - */

inline int integer::initialize (int n)
{
	p = prime_number (n);
	return p;
} /* integer::initialize */

inline int integer::delta (void) const
{
	if (p)
		return (num ? 1 : 0);
	else
		return ((num >= 0) ? num : -num);
} /* integer::delta */

inline integer integer::normalized (void) const
{
	integer n;
	if (num < 0)
		n. num = (numbertype) (-num);
	else
		n. num = num;
	return n;
} /* integer::normalized */

inline bool operator < (const integer &x, const integer &y)
{
	return (x. num < y. num);
} /* operator < */

inline bool operator > (const integer &x, const integer &y)
{
	return (x. num > y. num);
} /* operator > */


} // namespace homology
} // namespace chomp

#endif // _CHOMP_STRUCT_INTEGER_H_

/// @}

