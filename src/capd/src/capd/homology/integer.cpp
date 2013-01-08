/// @addtogroup struct
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file integer.cpp
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started in December 1999. Last revision: March 11, 2003 (Oct 6, 2004).


#include "capd/homology/textfile.h"
#include "capd/homology/integer.h"

#include <sstream>
#include <cstring>

namespace capd {
namespace homology {


// --------------------------------------------------
// ------------------ prime number ------------------
// --------------------------------------------------

static int itisprime (int_t n)
// Check if the number is prime. Return: 1 = Yes, 0 = No.
{
	if (n < 2)
		return 0;

	int_t i = 2;
	while (i * i <= n)
	{
		if (!(n % i ++))
			return 0;
	}

	return 1;
} /* it is prime */

static int_t roundtoprime (int_t n)
// Return the smallest prime number greater than or equal to the given one.
{
	while (!itisprime (n))
		n ++;

	return n;
} /* round to prime number */

primeint::primeint (int_t k)
{
	n = roundtoprime (k);
	return;
} /* primeint::primeint */

primeint &primeint::operator = (int_t k)
{
	n = roundtoprime (k);
	return *this;
} /* primeint::operator = */


// --------------------------------------------------
// -------------------- integer ---------------------
// --------------------------------------------------

int integer::p = 0;

int integer::is_prime (int n)
// Check if the number is prime.
// Return: 1 = Yes, 0 = No.
{
	int i = 2;
	if (n < 2)
		return 0;
	while ((i < i * i) && (i * i <= n))
	{
		if (!(n % i ++))
			return 0;
	}
	return 1;
} /* is_prime */

int integer::prime_number (int n)
// Return the smallest prime number
// greater than or equal to the given one
// unless the given number is 0.
{
	if (!n)
		return n;
	if (n < 0)
		n = -n;
	while (!is_prime (n))
		n ++;
	return n;
} /* prime_number */

unsigned integer::invert (unsigned n, unsigned q)
// Invert a number in the modulo p arithmetic.
{
	unsigned result = 1;
	unsigned i = q - 2;

	if ((n == 1) || (n == (unsigned) (q - 1)))
		return n;

	sbug << "  (inversion of " << n << ")\n";

	while (i)
		if (i & 1)
		{
			result = (result * n) % q;
			i --;
		}
		else
		{
			n = (n * n) % q;
			i >>= 1;
		}

	return (result);
} /* invert */


// --------------------------------------------------
// -------------- ring name and symbol --------------
// --------------------------------------------------

const char *integer::ringname ()
{
	static char buf [100];
	static int previous = -1;
	if (previous != integer::p)
	{
		std::ostringstream s;
		if (integer::p)
			s << "Z modulo " << (int) integer::p;
		else
			s << "the ring of integers";
		strcpy (buf, s. str (). c_str ());
		previous = integer::p;
	}
	return buf;
} /* integer::ringname */

const char *integer::ringsymbol ()
{
	static char buf [100];
	static int previous = -1;
	if (previous != integer::p)
	{
		std::ostringstream s;
		if (integer::p)
			s << "Z_" << (int) integer::p;
		else
			s << "Z";
		strcpy (buf, s. str (). c_str ());
		previous = integer::p;
	}
	return buf;
} /* integer::ringsymbol */


} // namespace homology
} // namespace capd

/// @}

