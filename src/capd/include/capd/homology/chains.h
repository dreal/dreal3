/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file chains.h
///
/// This file contains classes and functions related to algebraic chain
/// complexes and chain maps, including homology computation.
///
/// The templates in this file are prepared for a Euclidean domain.
/// This ring type should have the following methods defined in it:
/// operator +, operator *, unary operator -, operator <<, operator >>,
/// assignment from an integer (only 0 and 1), function "normalized",
/// operators == and != (used only to compare with 0 and with 1),
/// operators / and % (for division with remainder),
/// function delta (from the definition of the Euclidean domain),
/// and a static member function "const char *euclidom::ringsymbol ()".
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started in 1997. Last revision: June 25, 2007.


#ifndef _CAPD_HOMOLOGY_CHAINS_H_ 
#define _CAPD_HOMOLOGY_CHAINS_H_ 

#include "capd/homology/config.h"
#include "capd/homology/textfile.h"

#include <iostream>
#include <fstream>
#include <cstdlib>
#include <iomanip>

namespace capd {
namespace homology {


// templates defined within this file (in this order):

// a chain, that is, a linear combination of generators
template <class euclidom>
class chain;
// a set of matrices
template <class euclidom>
class matrices;
// a sparse matrix whose entries are the given coefficients
template <class euclidom>
class mmatrix;
// a chain complex over a given Euclidean domain
template <class euclidom>
class chaincomplex;
// a chain homomorphism between two chain complexes
template <class euclidom>
class chainmap;

// templates of functions which display the homology to the output streams
template <class euclidom>
outputstream &show_homology (outputstream &out, const chain<euclidom> &c);
template <class euclidom>
std::ostream &show_homology (std::ostream &out, const chain<euclidom> &c);


// --------------------------------------------------
// --------------------- chains ---------------------
// --------------------------------------------------

// define the number of chain elements that are kept in the chain itself;
// use 1 for better memory usage (?), use more for less memory allocation;
// set to 0 to switch the 'smart' pointer space usage off
#define CHAINFIXED 0

#ifndef CHAINFIXED
#define CHAINFIXED 1
#endif

/// This class defines objects which represent chains
/// as finite sequences of elements identified by integral numbers
/// with coefficients in a given Euclidean domain.
template <class euclidom>
class chain
{
public:
	/// The default constructor.
	chain ();

	/// The copy constructor.
	chain (const chain<euclidom> &c);

	/// The assignment operator.
	chain<euclidom> &operator = (const chain<euclidom> &c);

	/// The destructor.
	~chain ();

	/// Returns the size of the chain, that is, the number of
	/// elements with non-zero coefficients.
	int size () const;

	/// Returns true if the chain is empty (zero), false otherwise.
	bool empty () const;

	/// Finds and returns the coefficient in front of the given element.
	/// If the identifier is negative, then returns the first nonzero
	/// coefficient or 0 if none.
	euclidom getcoefficient (int n = -1) const;

	/// Find the position of an element with the given identifier.
	/// Returns -1 if not found.
	int findnumber (int n) const;

	/// Returns the coefficient in front of the i-th element
	/// in the chain.
	euclidom coef (int i) const;

	/// Returns the number (identifier) of the i-th element in the chain.
	int num (int i) const;

	/// Determines if the chain contains a non-invertible coefficient.
	/// Returns true if yes, false if not.
	bool contains_non_invertible () const;

	/// Finds the best element in the chain for reduction, that is,
	/// the element with minimal value of delta.
	/// IF the given table is given, then additionally an element
	/// with the shortest chain length in the table is searched for.
	/// Returns the actual number of this element in the chain
	/// (not its identifier) or -1 if the chain is empty (zero).
	int findbest (chain<euclidom> *table = NULL) const;

	/// Adds an element algebraically to the chain.
	chain<euclidom> &add (int n, euclidom e);

	/// Removes an element with the given identifier from the chain.
	chain<euclidom> &remove (int n);

	/// Adds one chain to another with a given coefficient.
	/// If the chain is a row of a matrix, then its number and the
	/// table of columns must be given for proper modification.
	/// If this is a column, its number and columns must be given.
	chain<euclidom> &add (const chain<euclidom> &other,
		euclidom e, int number = -1,
		chain<euclidom> *table = NULL);

	/// Swaps one chain with another. If the chain is a row of a
	/// matrix, then its number, the number of the other row and the
	/// table of columns must be given for proper modification;
	/// if this is a column, its number and columns must be given
	chain<euclidom> &swap (chain<euclidom> &other,
		int number = -1, int othernumber = -1,
		chain<euclidom> *table = NULL);

	/// Takes data from another chain. Destroys the other chain.
	chain<euclidom> &take (chain<euclidom> &c);

	/// Multiplies one or all the coefficients in the chain
	/// by the given number.
	chain<euclidom> &multiply (euclidom e, int number = -1);

	/// Shows the chain to the output stream. Uses a given label
	/// for indicating identifiers of elements in the chain.
	outputstream &show (outputstream &out,
		const char *label = NULL) const;

	/// Shows the chain to the standard output stream. Uses a given label
	/// for indicating identifiers of elements in the chain.
	std::ostream &show (std::ostream &out, const char *label = NULL) const;

private:
	/// The length of the list and the length of the table.
	int len;

	/// Elements of the list sorted according to the identifier.
	/// If there are very few of them, they are kept in the space
	/// normally reserved for the addresses. Otherwise, an array
	/// is allocated in the memory.
	union
	{
		struct
		{
			int *n;
			euclidom *e;
		} t;
		struct
		{
			#if CHAINFIXED
			int n [CHAINFIXED];
			euclidom e [CHAINFIXED];
			#else
			int *n;
			euclidom *e;
			#endif
		} x;
	};

	/// Inserts one chain element at the given position.
	chain<euclidom> &insertpair (int i, int n, euclidom e);

	/// Removes one chain element at the given position.
	chain<euclidom> &removepair (int i);

	/// Swaps two numbers (identifiers) in the chain.
	chain<euclidom> &swapnumbers (int number1, int number2);

	/// Checks if the tables have been allocated depending
	/// on the value of their length. Only tables longer than
	/// some limit are allocated.
	bool allocated () const;

}; /* class chain */

// --------------------------------------------------

template <class euclidom>
inline bool chain<euclidom>::allocated () const
{
	if (len <= static_cast<int> (CHAINFIXED))
		return false;
//	return (sizeof (int *) < ((sizeof (int) < sizeof (euclidom)) ?
//		sizeof (euclidom) : sizeof (int)) * len);
	else
		return true;
} /* chain<euclidom>::allocated */

template <class euclidom>
inline chain<euclidom>::chain ()
{
	len = 0;
	return;
} /* chain<euclidom>::chain */

template <class euclidom>
inline chain<euclidom>::chain (const chain<euclidom> &c)
{
	// copy the length of the chain
	len = c. len;

	// allocate new tables if necessary and copy the data
	if (allocated ())
	{
		t. n = new int [len];
		t. e = new euclidom [len];
		if (!t. n || !t. e)
			throw "Not enough memory to create a chain copy.";
		for (int i = 0; i < len; ++ i)
		{
			t. n [i] = c. t. n [i];
			t. e [i] = c. t. e [i];
		}
	}
	else
	{
		for (int i = 0; i < len; ++ i)
		{
			x. n [i] = c. x. n [i];
			x. e [i] = c. x. e [i];
		}
	}
	return;
} /* chain<euclidom>::chain */

template <class euclidom>
inline chain<euclidom> &chain<euclidom>::operator =
	(const chain<euclidom> &c)
{
	// first release allocated tables if any
	if (allocated ())
	{
		delete [] t. n;
		delete [] t. e;
	}

	// copy the length of the chain
	len = c. len;

	// allocate new tables if necessary and copy the data
	if (allocated ())
	{
		t. n = new int [len];
		t. e = new euclidom [len];
		if (!t. n || !t. e)
			throw "Not enough memory to create a chain copy =.";
		for (int i = 0; i < len; ++ i)
		{
			t. n [i] = c. t. n [i];
			t. e [i] = c. t. e [i];
		}
	}
	else
	{
		for (int i = 0; i < len; ++ i)
		{
			x. n [i] = c. x. n [i];
			x. e [i] = c. x. e [i];
		}
	}
	return *this;
} /* chain<euclidom>::operator = */

template <class euclidom>
inline chain<euclidom>::~chain ()
{
	if (allocated ())
	{
		delete [] t. n;
		delete [] t. e;
	}
	return;
} /* chain<euclidom>::~chain */

template <class euclidom>
inline int chain<euclidom>::size () const
{
	return len;
} /* chain<euclidom>::size */

template <class euclidom>
inline bool chain<euclidom>::empty () const
{
	return !len;
} /* chain<euclidom>::empty */

template <class euclidom>
/*inline*/ euclidom chain<euclidom>::getcoefficient (int n) const
{
	bool a = allocated ();
	const euclidom *tetab = a ? t. e : x. e;
	if (n < 0)
	{
		if (len > 0)
			return tetab [0];
		else
		{
			euclidom zero;
			zero = 0;
			return zero;
		}
	}

	const int *tntab = a ? t. n : x. n;
	int i = 0;
	while ((i < len) && (tntab [i] < n))
		++ i;
	if ((i >= len) || (tntab [i] != n))
	{
		euclidom zero;
		zero = 0;
		return zero;
	}
	return tetab [i];
} /* chain<euclidom>::getcoefficient */

template <class euclidom>
inline int chain<euclidom>::findnumber (int n) const
{
	bool a = allocated ();
	const int *tntab = a ? t. n : x. n;
	for (int i = 0; i < len; ++ i)
	{
		if (tntab [i] == n)
			return i;
		else if (tntab [i] > n)
			return -1;
	}
	return -1;
} /* chain<euclidom>::findnumber */

template <class euclidom>
inline euclidom chain<euclidom>::coef (int i) const
{
	if (i >= len)
		throw "Wrong coefficient requested from a chain.";
	return (allocated () ? t. e : x. e) [i];
} /* chain<euclidom>::coef */

template <class euclidom>
inline int chain<euclidom>::num (int i) const
{
	if (i >= len)
		throw "Wrong number requested from a chain.";
	return (allocated () ? t. n : x. n) [i];
} /* chain<euclidom>::num */

template <class euclidom>
inline bool chain<euclidom>::contains_non_invertible () const
{
	if (allocated ())
	{
		for (int i = 0; i < len; ++ i)
		{
			if (t. e [i]. delta () > 1)
				return true;
		}
	}
	else
	{
		for (int i = 0; i < len; ++ i)
		{
			if (x. e [i]. delta () > 1)
				return true;
		}
	}
	return false;
} /* chain<euclidom>::contains_non_invertible */

template <class euclidom>
inline int chain<euclidom>::findbest (chain<euclidom> *table) const
{
	// if the chain is so short that the answer is obvious, return it
	if (len <= 1)
		return (len - 1);

	// find the number which has the smallest delta function value
	int this_delta, best_delta = -1;
	int best_i = 0;

	// go through the whole table
	bool a = allocated ();
	const int *tntab = a ? t. n : x. n;
	const euclidom *tetab = a ? t. e : x. e;
	int i;
	for (i = 0; i < len; ++ i)
	{
		// compute the value of the function delta
		this_delta = tetab [i]. delta ();

		// if the value is the smallest possible
		// and no further analysis was required, finish here
		if (!table && (this_delta == 1))
			return i;

		// if this delta is better, remember it
		if (!i || (this_delta < best_delta))
		{
			best_delta = this_delta;
			best_i = i;
		}
	}

	// if no further analysis is required, return the result just now
	if (!table)
		return best_i;

	// analyse which element has the shortest corresponding chain
	int this_length, best_length =
		table [tntab [best_i]]. size ();
	for (i = best_i + 1; i < len; ++ i)
	{
		if (tetab [i]. delta () == best_delta)
		{
			this_length =
				table [tntab [i]]. size ();
			if (best_length > this_length)
			{
				best_length = this_length;
				best_i = i;
			}
		}
	}

	return best_i;
} /* chain<euclidom>::findbest */

// --------------------------------------------------

template <class euclidom>
inline chain<euclidom> &chain<euclidom>::insertpair
	(int i, int n, euclidom e)
{
	// remember if the table was previously allocated or not
	bool a = allocated ();

	// increase the length
	++ len;

	// determine if the new table should be allocated or not
	bool na = allocated ();

	// if a new table has to be allocated, do it
	if (na)
	{
		// allocate a new table
		int *newntab = new int [len];
		euclidom *newetab = new euclidom [len];
		if (!newntab || !newetab)
			throw "Cannot add an element to a chain.";

		// determine the addresses of the old tables
		int *oldntab = a ? t. n : x. n;
		euclidom *oldetab = a ? t. e : x. e;

		// copy the old data and insert the new pair
		int j;
		for (j = 0; j < i; ++ j)
		{
			newntab [j] = oldntab [j];
			newetab [j] = oldetab [j];
		}
		newntab [i] = n;
		newetab [i] = e;
		for (j = i + 1; j < len; ++ j)
		{
			newntab [j] = oldntab [j - 1];
			newetab [j] = oldetab [j - 1];
		}

		// release the previous tables if they were allocated
		if (a)
		{
			delete [] t. n;
			delete [] t. e;
		}

		// take the new tables to the data structure
		t. n = newntab;
		t. e = newetab;
	}

	// otherwise just insert the new element at the appropriate position
	else // if (!na && !a)
	{
		for (int j = len - 1; j > i; -- j)
		{
			x. n [j] = x. n [j - 1];
			x. e [j] = x. e [j - 1];
		}
		x. n [i] = n;
		x. e [i] = e;
	}

	return *this;
} /* chain<euclidom>::insertpair */

template <class euclidom>
inline chain<euclidom> &chain<euclidom>::removepair (int i)
{
	// remember if the table was previously allocated or not
	bool a = allocated ();

	// decrease the length
	if (len)
		-- len;

	// determine if the new table should be allocated or not
	bool na = allocated ();

	// allocate the new tables if necessary
	if (na)
	{
		int *newntab = new int [len];
		euclidom *newetab = new euclidom [len];
		if (!newntab || !newetab)
			throw "Cannot remove a pair from a chain.";

		// copy the data form the previous tables
		int j;
		for (j = 0; j < i; ++ j)
		{
			newntab [j] = t. n [j];
			newetab [j] = t. e [j];
		}
		for (j = i; j < len; ++ j)
		{
			newntab [j] = t. n [j + 1];
			newetab [j] = t. e [j + 1];
		}
		delete [] t. n;
		delete [] t. e;
		t. n = newntab;
		t. e = newetab;
	}

	// otherwise, copy the data from the previous tables
	else
	{
		int *oldntab = a ? t. n : x. n;
		euclidom *oldetab = a ? t. e : x. e;

		// copy the data form the previous tables
		int j;
		for (j = 0; a && (j < i); ++ j)
		{
			x. n [j] = oldntab [j];
			x. e [j] = oldetab [j];
		}
		for (j = i; j < len; ++ j)
		{
			x. n [j] = oldntab [j + 1];
			x. e [j] = oldetab [j + 1];
		}

		// release the old tables if necessary
		if (a)
		{
			delete [] oldntab;
			delete [] oldetab;
		}
	}

	return *this;
} /* chain<euclidom>::removepair */

template <class euclidom>
inline chain<euclidom> &chain<euclidom>::swapnumbers (int number1,
	int number2)
{
	// if the numbers are the same, do nothing
	if (number1 == number2)
		return *this;

	// force the first number be less than the second number
	if (number1 > number2)
	{
		int tempnumber = number1;
		number1 = number2;
		number2 = tempnumber;
	}

	// determine the true tables to be processed
	bool a = allocated ();
	int *tntab = a ? t. n : x. n;
	euclidom *tetab = a ? t. e : x. e;

	// find both numbers or the positions they should be at
	int i1 = 0, i2 = 0;
	while ((i1 < len) && (tntab [i1] < number1))
		++ i1;
	while ((i2 < len) && (tntab [i2] < number2))
		++ i2;

	// if the first number was found...
	if ((i1 < len) && (tntab [i1] == number1))
	{
		// if both numbers were found, exchange their coefficients
		if ((i2 < len) && (tntab [i2] == number2))
			swapelements (tetab [i1], tetab [i2]);
		// if only the first was found, move it to the new position
		else
		{
			euclidom temp = tetab [i1];
			for (int i = i1 + 1; i < i2; ++ i)
			{
				tntab [i - 1] = tntab [i];
				tetab [i - 1] = tetab [i];
			}
			tntab [i2 - 1] = number2;
			tetab [i2 - 1] = temp;
		}
	}

	// otherwise if the second number only was found, move it to its pos.
	else if ((i2 < len) && (tntab [i2] == number2))
	{
		euclidom temp = tetab [i2];
		for (int i = i2; i > i1; -- i)
		{
			tntab [i] = tntab [i - 1];
			tetab [i] = tetab [i - 1];
		}
		tntab [i1] = number1;
		tetab [i1] = temp;
	}

	return *this;
} /* chain<euclidom>::swapnumbers */

// --------------------------------------------------

template <class euclidom>
inline chain<euclidom> &chain<euclidom>::add (int n, euclidom e)
{
	// if the coefficient is zero, ignore the pair
	if (e == 0)
		return *this;
	bool a = allocated ();
	int *tntab = a ? t. n : x. n;
	euclidom *tetab = a ? t. e : x. e;

	// find the position in the table for adding this pair
	int i = 0;
	while ((i < len) && (tntab [i] < n))
		++ i;

	// if an element with this identifier was found, add the coefficients
	if ((i < len) && (tntab [i] == n))
	{
		// add the coefficient
		tetab [i] += e;

		// if the coefficient became zero, remove this pair
		if (tetab [i] == 0)
			return removepair (i);

		// otherwise we are done
		else
			return *this;
	}

	// otherwise insert this pair into the chain
	return insertpair (i, n, e);

} /* chain<euclidom>::add */

template <class euclidom>
chain<euclidom> &chain<euclidom>::remove (int n)
{
	bool a = allocated ();
	int *tntab = a ? t. n : x. n;

	// find the element of the chain to be removed
	int i = 0;
	while ((i < len) && (tntab [i] < n))
		++ i;

	// if found, then remove it
	if ((i < len) && (tntab [i] == n))
		return removepair (i);

	return *this;
} /* chain<euclidom>::remove */

template <class euclidom>
inline chain<euclidom> &chain<euclidom>::add (const chain<euclidom> &other,
	euclidom e, int number, chain<euclidom> *table)
{
	// if the coefficient is zero or the other chain is zero,
	// then there is nothing to do
	if ((e == 0) || !other. len)
		return *this;

	// prepare big tables for the new chain
	int tablen = len + other. len;
	int *bigntab = new int [tablen];
	euclidom *bigetab = new euclidom [tablen];
	if (!bigntab || !bigetab)
		throw "Not enough memory to add chains.";

	// prepare the counters of elements of the two input chains
	// and of the output chain
	int i = 0, j = 0, k = 0;

	// determine the actual tables to be processed
	bool a = allocated ();
	bool oa = other. allocated ();
	const int *tntab = a ? t. n : x. n;
	const euclidom *tetab = a ? t. e : x. e;
	const int *ontab = oa ? other. t. n : other. x. n;
	const euclidom *oetab = oa ? other. t. e : other. x. e;

	// go through both input chains and compute the output chain
	while ((i < len) || (j < other. len))
	{
		if (i >= len)
		{
			bigntab [k] = ontab [j];
			bigetab [k] = e * oetab [j ++];
			if (table)
			{
				table [bigntab [k]]. add (number,
					bigetab [k]);
			}
			++ k;
		}
		else if ((j >= other. len) || (tntab [i] < ontab [j]))
		{
			bigntab [k] = tntab [i];
			bigetab [k ++] = tetab [i ++];
		}
		else if (tntab [i] > ontab [j])
		{
			bigntab [k] = ontab [j];
			bigetab [k] = e * oetab [j ++];
			if (table)
			{
				table [bigntab [k]]. add (number,
					bigetab [k]);
			}
			++ k;
		}
		else // if (tntab [i] == ontab [j])
		{
			bigntab [k] = tntab [i];
			euclidom addelem = e * oetab [j ++];
			bigetab [k] = tetab [i ++] + addelem;
			euclidom zero;
			zero = 0;
			if (bigetab [k] != zero)
			{
				if (table)
				{
					table [bigntab [k]]. add (number,
						addelem);
				}
				++ k;
			}
			else if (table)
			{
				table [bigntab [k]]. remove (number);
			}
		}
	}

	// release the old tables if they are useless now
	if (a && ((k != len) || (k == tablen)))
	{
		delete [] t. n;
		delete [] t. e;
	}

	// use the previous tables and release the big table if beneficial
	if (a && (k == len) && (k != tablen))
	{
		for (int i = 0; i < len; ++ i)
		{
			t. n [i] = bigntab [i];
			t. e [i] = bigetab [i];
		}
		delete [] bigntab;
		delete [] bigetab;
		return *this;
	}

	len = k;

	// if the new tables don't have to be allocated, only copy the data
	if (!allocated ())
	{
		for (int i = 0; i < len; ++ i)
		{
			x. n [i] = bigntab [i];
			x. e [i] = bigetab [i];
		}
		delete [] bigntab;
		delete [] bigetab;
		return *this;
	}

	// if the big tables cannot be used, allocate new tables
	if (len != tablen)
	{
		t. n = new int [len];
		t. e = new euclidom [len];
		if (!t. n || !t. e)
			throw "Cannot shorten a sum of chains.";
		for (int i = 0; i < len; ++ i)
		{
			t. n [i] = bigntab [i];
			t. e [i] = bigetab [i];
		}
		delete [] bigntab;
		delete [] bigetab;
	}

	// otherwise, simply use the big tables
	else
	{
		t. n = bigntab;
		t. e = bigetab;
	}

	return *this;
} /* chain<euclidom>::add */

template <class euclidom>
inline chain<euclidom> &chain<euclidom>::swap (chain<euclidom> &other,
	int number, int othernumber, chain<euclidom> *table)
{
	// check which chains where allocated
	bool a = allocated ();
	bool oa = other. allocated ();

	// swap the data of the chains
	if (a && oa)
	{
		swapelements (t. n, other. t. n);
		swapelements (t. e, other. t. e);
	}
	else if (!a && !oa)
	{
		// common variable for interations (required by MSVC++)
		int i;

		// swap the data in the common area of both chains
		for (i = 0; (i < len) && (i < other. len); ++ i)
		{
			swapelements (x. n [i], other. x. n [i]);
			swapelements (x. e [i], other. x. e [i]);
		}

		// copy the remaining portion of the data
		for (i = len; i < other. len; ++ i)
		{
			x. n [i] = other. x. n [i];
			x. e [i] = other. x. e [i];
		}
		for (i = other. len; i < len; ++ i)
		{
			other. x. n [i] = x. n [i];
			other. x. e [i] = x. e [i];
		}
	}
	else if (a) // && !oa
	{
		int *tempn = t. n;
		euclidom *tempe = t. e;
		for (int i = 0; i < other. len; ++ i)
		{
			x. n [i] = other. x. n [i];
			x. e [i] = other. x. e [i];
		}
		other. t. n = tempn;
		other. t. e = tempe;
	}
	else // if (oa) // && !a
	{
		int *tempn = other. t. n;
		euclidom *tempe = other. t. e;
		for (int i = 0; i < len; ++ i)
		{
			other. x. n [i] = x. n [i];
			other. x. e [i] = x. e [i];
		}
		t. n = tempn;
		t. e = tempe;
	}

	// swap the lengths of the chains (do not swap 'a' with 'oa')
	swapelements (len, other. len);

	if (!table)
		return *this;

	// change the numbers in every relevant entry of the table
	int *tntab = oa ? t. n : x. n;
	int *ontab = a ? other. t. n : other. x. n;
	int i = 0, j = 0;
	while ((i < len) || (j < other. len))
	{
		// determine which table entry should be modified
		int n;
		if (i >= len)
			n = ontab [j ++];
		else if (j >= other. len)
			n = tntab [i ++];
		else if (tntab [i] < ontab [j])
			n = tntab [i ++];
		else if (ontab [j] < tntab [i])
			n = ontab [j ++];
		else
		{
			n = tntab [i ++];
			++ j;
		//	++ i;
		//	++ j;
		//	continue;
		}

		// swap numbers in that table entry
		table [n]. swapnumbers (othernumber, number);
	}

	return *this;
} /* chain<euclidom>::swap */

template <class euclidom>
inline chain<euclidom> &chain<euclidom>::take (chain<euclidom> &c)
{
	// release the current tables if they were allocated
	if (allocated ())
	{
		delete [] t. n;
		delete [] t. e;
	}

	// if the other tables were allocated, take them
	if (c. allocated ())
	{
		t. n = c. t. n;
		t. e = c. t. e;
	}

	// otherwise copy the data from the internal other tables
	else
	{
		for (int i = 0; i < c. len; ++ i)
		{
			x. n [i] = c. x. n [i];
			x. e [i] = c. x. e [i];
		}
	}

	// copy the length and reset the other length
	len = c. len;
	c. len = 0;

	return *this;
} /* chain<euclidom>::take */

template <class euclidom>
inline chain<euclidom> &chain<euclidom>::multiply (euclidom e, int number)
{
	// check if the tables have been allocated or not
	bool a = allocated ();
	int *tntab = a ? t. n : x. n;
	euclidom *tetab = a ? t. e : x. e;

	// if there is only one element to be multiplied, find it and do it
	if (number >= 0)
	{
		for (int i = 0; i < len; ++ i)
		{
			if (tntab [i] == number)
			{
				if (e == 0)
					removepair (i);
				else
				{
					tetab [i] *= e;
				//	if (tetab [i] == 0)
				//		removepair (i);
				}
				return *this;
			}
		}
	}

	// if the entire chain has to be multiplied by a non-zero number...
	else if (e != 0)
	{
		for (int i = 0; i < len; ++ i)
		{
			tetab [i] *= e;
			if (tetab [i] == 0)
				removepair (i);
		}
	}

	// otherwise, if the chain has to be made zero, clean it
	else
	{
		if (a)
		{
			delete [] t. n;
			delete [] t. e;
		}
		len = 0;
	}

	return *this;
} /* chain<euclidom>::multiply */

template <class euclidom>
inline outputstream &chain<euclidom>::show (outputstream &out,
	const char *label) const
{
	if (len <= 0)
		out << "0";
	bool a = allocated ();
	const int *tntab = a ? t. n : x. n;
	const euclidom *tetab = a ? t. e : x. e;
	for (int i = 0; i < len; ++ i)
	{
		euclidom e = tetab [i];
		int n = tntab [i] + 1;

		if (e == 1)
			out << (i ? " + " : "") <<
				(label ? label : "") << n;
		else if (-e == 1)
			out << (i ? " - " : "-") <<
				(label ? label : "") << n;
		else
			out << (i ? " + " : "") << e << " * " <<
				(label ? label : "") << n;
	}
	return out;
} /* chain<euclidom>::show */

template <class euclidom>
inline std::ostream &chain<euclidom>::show (std::ostream &out, const char *label) const
{
	outputstream tout (out);
	show (tout, label);
	return out;
} /* chain<euclidom>::show */

// --------------------------------------------------

/// Outputs the given chain to a standard output stream in the text mode.
/// Warning: The operators >> and << are not symmetric for chains.
template <class euclidom>
inline std::ostream &operator << (std::ostream &out, const chain<euclidom> &c)
{
	c. show (out);
	return out;
} /* operator << */

/// Reads a chain from a standard input stream in the text mode.
/// Warning: The operators >> and << are not symmetric for chains.
template <class euclidom>
inline std::istream &operator >> (std::istream &in, chain<euclidom> &c)
{
	ignorecomments (in);
	int closing = readparenthesis (in);

	ignorecomments (in);
	while (in. peek () != closing)
	{
		// read the coefficient
		euclidom e (1);
		in >> e;

		// read the multiplication symbol
		ignorecomments (in);
		if (in. peek () != '*')
			throw "The multiplication sign '*' while reading a chain.";
		in. get ();

		// read the identifier
		ignorecomments (in);
		int n;
		in >> n;
		-- n;

		// if the coefficient is zero, then this is wrong
		if (e == 0)
			throw "A zero coefficient in a chain detected.";

		// add this element to the chain
		c. add (e, n);

		// prepare for the next pair to read
		ignorecomments (in);

		// read a comma or a plus between two elements of the chain
		if ((in. peek () == ',') || (in. peek () == '+'))
		{
			in. get ();
			ignorecomments (in);
		}
	}

	if (closing != EOF)
		in. get ();

	return in;
} /* operator >> */


// --------------------------------------------------
// ------------------- simplelist -------------------
// --------------------------------------------------

/// This class defines a simple list of pointers to objects
/// of the given type. It is a helper class used in chain complex.
template <class element>
class simplelist
{
public:
	/// The default constructor of an empty list.
	simplelist ();

	/// The destructor.
	~simplelist ();

	/// Adds an element to the list.
	void add (element &m);

	/// Remove an element from the list.
	void remove (element &m);

	/// A simple internal iterator of the list. A call to this function
	/// returns an element from the list, but does not remove it from the
	/// list, and sets the internal iterator for the next element.
	/// After the last element has been taken, returns 0 and rewinds
	/// the iterator to the beginning of the list.
	element *take ();

private:
	/// The copy constructor is not implemented.
	simplelist (const simplelist<element> &s)
	{
		throw "Copying constructor not implemented "
			"for a simple list.";
		return;
	}

	/// The assignment operator is not implemented.
	simplelist<element> &operator = (const simplelist<element> &s)
	{
		throw "Operator = not implemented "
			"for a simple list.";
		return *this;
	}

	/// The number of element pointers stored in the list.
	int num;

	/// The current element in the table.
	int cur;

	/// A table of element pointers.
	element **elem;

}; /* class simplelist */

// --------------------------------------------------

template <class element>
inline simplelist<element>::simplelist (): num (0), cur (0), elem (NULL)
{
	return;
} /* simplelist::simplelist */

template <class element>
inline simplelist<element>::~simplelist ()
{
	if (elem)
		delete [] elem;
	return;
} /* simplelist::~simplelist */

template <class element>
inline void simplelist<element>::add (element &m)
{
	element **newelem = new element * [num + 1];
	for (int i = 0; i < num; ++ i)
		newelem [i] = elem [i];
	newelem [num ++] = &m;
	delete [] elem;
	elem = newelem;
	return;
} /* simplelist::add */

template <class element>
inline void simplelist<element>::remove (element &m)
{
	int pos = 0;
	while ((pos < num) && (elem [pos] != &m))
		++ pos;
	-- num;
	while (pos < num)
	{
		elem [pos] = elem [pos + 1];
		++ pos;
	}
	return;
} /* simplelist::remove */

template <class element>
inline element *simplelist<element>::take ()
{
	if (cur >= num)
	{
		cur = 0;
		return NULL;
	}
	else
	{
		return elem [cur ++];
	}
} /* simplelist::take */


// --------------------------------------------------
// -------------------- mmatrix ---------------------
// --------------------------------------------------

/// A class for representing sparse matrices containing elements
/// of the 'euclidom' type. This class has very specific functionality
/// to be used mainly for the purpose of homology computation.
template <class euclidom>
class mmatrix
{
public:
	/// The default constructor.
	mmatrix ();

	/// The copy constructor.
	/// Added by Marcin Zelawski and fixed by Pawel Pilarczyk.
	mmatrix (const mmatrix<euclidom> &m);

	/// The assignment operator.
	/// Added by Marcin Zelawski and fixed by Pawel Pilarczyk.
	mmatrix<euclidom> &operator = (const mmatrix<euclidom> &s);

	/// The destructor of a matrix.
	~mmatrix ();

	/// Defines the number of rows and columns and increases the internal
	/// tables if necessary. Useful for creating large zero matrices.
	void define (int numrows, int numcols);

	/// Defines the matrix to be the identity of the given size.
	void identity (int size);

	/// Adds a value to the given element of the matrix.
	void add (int row, int col, const euclidom &e);

	/// Returns the value at the desired location of the matrix.
	/// If 'row' or 'col' is set to -1, gets the first element
	/// in it or returns 0 if the colum/row is empty.
	euclidom get (int row, int col) const;

	/// Returns a reference to the entire row stored as a chain.
	const chain<euclidom> &getrow (int n) const;

	/// Returns a reference to the entire column stored as a chain.
	const chain<euclidom> &getcol (int n) const;

	/// Returns the number of rows in the matrix.
	int getnrows () const;

	/// Returns the number of columns in the matrix.
	int getncols () const;

	/// Adds one row to another with a given coefficient.
	/// Updates all the matrices which are linked to this one.
	void addrow (int dest, int source, const euclidom &e);

	/// Adds one column to another with a given coefficient.
	/// Updates all the matrices which are linked to this one.
	void addcol (int dest, int source, const euclidom &e);

	/// Swaps two rows of the matrix.
	void swaprows (int i, int j);

	/// Swaps two columns of the matrix.
	void swapcols (int i, int j);

	/// Multiplies the row by the given coefficient and updates columns.
	void multiplyrow (int n, const euclidom &e);

	/// Multiplies the column by the given coefficient and updates rows.
	void multiplycol (int n, const euclidom &e);

	/// Finds a row containing at least the required number of nonzero
	/// elements, starting at the given row.
	/// If 'req_elements' is set to -1 then looks for a zero row.
	/// Returns the number of the row satisfying the desired property,
	/// or -1 if not found.
	int findrow (int req_elements = 1, int start = -1) const;

	/// Finds a column containing at least the required number of nonzero
	/// elements, starting at the given column.
	/// If 'req_elements' is set to -1 then looks for a zero column.
	/// Returns the number of the column satisfying the desired property,
	/// or -1 if not found.
	int findcol (int req_elements = 1, int start = -1) const;

	/// Reduces the given row of the matrix and updates its columns.
	/// A preferred number of a column to leave is given.
	/// Returns the number of the column to be reduced next,
	/// or -1 if done.
	int reducerow (int n, int preferred);

	/// Reduces the given column of the matrix and updates its rows.
	/// A preferred number of a row to leave is given.
	/// Returns the number of the row to be reduced next,
	/// or -1 if done.
	int reducecol (int n, int preferred);

	/// Runs some random simple reductions.
	/// It is recommended to run this function
	/// before running the 'simple_form' procedure.
	void simple_reductions (bool quiet = false);

	/// Transforms the matrix to a simple form (nearly SNF).
	void simple_form (bool quiet = false);

	/// Inverts the matrix. Throws an error message on failure.
	void invert (void);

	/// Computes the product of the two given matrices.
	/// The matrix is replaced with the product.
	void multiply (const mmatrix<euclidom> &m1,
		const mmatrix<euclidom> &m2);

	/// This is a list of matrices to be updated together with the
	/// changes to the columns or rows of the current matrix.
	/// These matrices may have these spaces as their domains or
	/// ranges (codomains, images).
	/// For instance, "dom_img" is a list of matrices such that the
	/// domain of the current matrix is the image of each of them.
	simplelist<mmatrix<euclidom> > dom_dom, dom_img, img_dom,
		img_img;

	/// Extracts a submatrix from the given matrix. Uses the
	/// positions in the 'domain' and 'range' chains as the column
	/// and row numbers for the coefficients in the new matrix.
	void submatrix (const mmatrix<euclidom> &matr,
		const chain<euclidom> &domain,
		const chain<euclidom> &range);

	/// Writes a column with only these coefficients which exist
	/// in 'range', and shows their positions in that chain.
	outputstream &show_hom_col (outputstream &out, int col,
		const chain<euclidom> &range,
		const char *txt = NULL) const;

	/// Writes a column with only these coefficients which exist
	/// in 'range', and shows their positions in that chain.
	std::ostream &show_hom_col (std::ostream &out, int col,
		const chain<euclidom> &range,
		const char *txt = NULL) const;

	/// Writes the matrix to an output stream by its rows or columns.
	outputstream &showrowscols (outputstream &out,
		chain<euclidom> *table, int tablen,
		int first = 0, int howmany = 0,
		const char *label = NULL) const;

	/// Writes the matrix to an output stream by its rows.
	outputstream &showrows (outputstream &out, int first = 0,
		int howmany = 0, const char *label = "Row ") const;

	/// Writes the matrix to an output stream by its rows.
	std::ostream &showrows (std::ostream &out, int first = 0,
		int howmany = 0, const char *label = "Row ") const;
		
	/// Writes the matrix to an output stream by its rows.
	outputstream &showcols (outputstream &out, int first = 0,
		int howmany = 0, const char *label = "Col ") const;

	/// Writes the matrix to an output stream by its rows.
	std::ostream &showcols (std::ostream &out, int first = 0,
		int howmany = 0, const char *label = "Col ") const;

	/// Writes the matrix as a linear map on generators.
	outputstream &showmap (outputstream &out,
		const char *maplabel = NULL,
		const char *xlabel = NULL, const char *ylabel = NULL)
		const;

	/// Writes the matrix as a linear map on generators.
	std::ostream &showmap (std::ostream &out, const char *maplabel = NULL,
		const char *xlabel = NULL, const char *ylabel = NULL)
		const;

private:
	/// The number of rows in the matrix.
	int nrows;

	/// The number of columns in the matrix.
	int ncols;

	/// The number of allocated rows.
	int allrows;

	/// The number of allocated columns.
	int allcols;

	/// The rows of the matrix.
	chain<euclidom> *rows;

	/// The columns of the matrix.
	chain<euclidom> *cols;

	/// An internal procedure for both findrow and findcol.
	int findrowcol (int req_elements, int start, int which) const;

	/// Increases tables to be enough to keep the given number of
	/// columns and rows. This function does not set 'nrows' and 'ncols'.
	void increase (int numrows, int numcols);

	/// Increases tables to be enough to keep the given number of rows.
	void increaserows (int numrows);

	/// Increases tables to be enough to keep the given number of
	/// columns.
	void increasecols (int numcols);

}; /* class mmatrix */

// --------------------------------------------------

template <class euclidom>
inline mmatrix<euclidom>::mmatrix (): nrows (0), ncols (0),
	allrows (0), allcols (0), rows (NULL), cols (NULL)
{
	return;
} /* mmatrix<euclidom>::mmatrix */

template <class euclidom>
inline mmatrix<euclidom>::~mmatrix ()
{
	if (rows)
		delete [] rows;
	if (cols)
		delete [] cols;
	return;
} /* mmatrix<euclidom>::~mmatrix */

template <class euclidom>
inline void mmatrix<euclidom>::define (int numrows, int numcols)
{
	// verify that no nonzero entry will be thrown away
	if ((nrows > numrows) || (ncols > numcols))
		throw "Trying to define a matrix smaller than it really is";

	// increase the size of the matrix to fit the defined one
	increase (numrows, numcols);

	// set the number of rows and the number of columns as requested
	nrows = numrows;
	ncols = numcols;

	return;
} /* mmatrix<euclidom>::define */

template <class euclidom>
inline mmatrix<euclidom>::mmatrix (const mmatrix<euclidom> &m)
{
	nrows = m.nrows; 
	ncols = m.ncols;
	allrows = m.allrows;
	allcols = m.allcols;

	rows = NULL;
	cols = NULL;
	if (m. allrows > 0)
	{
		chain<euclidom> *newrows = new chain<euclidom> [m. allrows];
		if (!newrows)
			throw "Not enough memory for matrix rows.";
		for (int i = 0; i < m. allrows; ++ i)
			newrows [i] = m. rows [i];
		rows = newrows;
	}

	if (m. allcols > 0)
	{
		chain<euclidom> *newcols = new chain<euclidom> [m. allcols];
		if (!newcols)
			throw "Not enough memory for matrix columns.";
		for (int i = 0; i < m.allcols; ++ i)
			newcols [i] = m. cols [i];
		cols = newcols;
	}
} /* mmatrix<euclidom>::mmatrix */

template <class euclidom>
inline mmatrix<euclidom> &mmatrix<euclidom>::operator =
	(const mmatrix<euclidom> &m)
{
	// first release allocated tables if any
	if (rows)
		delete [] rows;
	if (cols)
		delete [] cols;

	nrows = m. nrows; 
	ncols = m. ncols;
	allrows = m. allrows;
	allcols = m. allcols;

	rows = NULL;
	cols = NULL;
	if (m. allrows > 0)
	{
		chain<euclidom> *newrows = new chain<euclidom> [m. allrows];
		if (!newrows)
			throw "Not enough memory for matrix rows.";
		for (int i = 0; i < m. allrows; ++ i)
			newrows [i] = m. rows [i];
		rows = newrows;
	}

	if (m. allcols > 0)
	{
		chain<euclidom> *newcols = new chain<euclidom> [m. allcols];
		if (!newcols)
			throw "Not enough memory for matrix columns.";
		for (int i = 0; i < m.allcols; ++ i)
			newcols [i] = m. cols [i];
		cols = newcols;
	}

        return *this;
} /* mmatrix<euclidom>::operator = */

template <class euclidom>
inline void mmatrix<euclidom>::identity (int size)
{
	if (!nrows && !ncols)
		increase (size, size);
	else if ((size > nrows) || (size > ncols))
		size = (nrows < ncols) ? nrows : ncols;
	for (int i = 0; i < size; ++ i)
	{
		euclidom one;
		one = 1;
		add (i, i, one);
	}
	return;
} /* mmatrix<euclidom>::identity */

template <class euclidom>
inline void mmatrix<euclidom>::add (int row, int col, const euclidom &e)
// A [r] [c] += e;
{
	if (row < 0)
		throw "Incorrect row number.";
	if (col < 0)
		throw "Incorrect column number.";
	if (row >= nrows)
	{
		if (row >= allrows)
			increaserows (row + row / 2 + 1);
		nrows = row + 1;
	}
	if (col >= ncols)
	{
		if (col >= allcols)
			increasecols (col + col / 2 + 1);
		ncols = col + 1;
	}
	if (e == 0)
		return;
	cols [col]. add (row, e);
	rows [row]. add (col, e);
	return;
} /* mmatrix<euclidom>::add */

template <class euclidom>
inline euclidom mmatrix<euclidom>::get (int row, int col) const
// return (A [r] [c]);
{
	if ((row >= nrows) || (col >= ncols))
	{
		euclidom zero;
		zero = 0;
		return zero;
	}
	if (row >= 0)
		return rows [row]. getcoefficient (col);
	else if (col >= 0)
		return cols [col]. getcoefficient (row);
	else
	{
		euclidom zero;
		zero = 0;
		return zero;
	}
} /* mmatrix<euclidom>::get */

template <class euclidom>
inline const chain<euclidom> &mmatrix<euclidom>::getrow (int n) const
{
	if ((n < 0) || (n >= nrows))
		throw "Incorrect row number.";
	return rows [n];
} /* mmatrix<euclidom>::getrow */

template <class euclidom>
inline const chain<euclidom> &mmatrix<euclidom>::getcol (int n) const
{
	if ((n < 0) || (n >= ncols))
		throw "Incorrect column number.";
	return cols [n];
} /* mmatrix<euclidom>::getcol */

template <class euclidom>
inline int mmatrix<euclidom>::getnrows () const
{
	return nrows;
} /* mmatrix<euclidom>::getnrows */

template <class euclidom>
inline int mmatrix<euclidom>::getncols () const
{
	return ncols;
} /* mmatrix<euclidom>::getncols */

template <class euclidom>
inline void mmatrix<euclidom>::addrow (int dest, int source,
	const euclidom &e)
{
	// check if the parameters are not out of range
	if ((dest < 0) || (dest >= nrows) || (source < 0) ||
		(source >= nrows))
		throw "Trying to add rows out of range.";

	// add this row
	rows [dest]. add (rows [source], e, dest, cols);

	// update the other matrices
	mmatrix<euclidom> *m;
	while ((m = img_img. take ()) != NULL)
		if (m -> rows)
			m -> rows [dest]. add (m -> rows [source], e,
				dest, m -> cols);

	while ((m = img_dom. take ()) != NULL)
		if (m -> cols)
			m -> cols [source]. add (m -> cols [dest], -e,
				source, m -> rows);

	return;
} /* mmatrix<euclidom>::addrow */

template <class euclidom>
inline void mmatrix<euclidom>::addcol (int dest, int source,
	const euclidom &e)
{
	// check if the parameters are not out of range
	if ((dest < 0) || (dest >= ncols) || (source < 0) ||
		(source >= ncols))
		throw "Trying to add columns out of range.";

	// add this column
	cols [dest]. add (cols [source], e, dest, rows);

	// update the other matrices
	mmatrix<euclidom> *m;
	while ((m = dom_dom. take ()) != NULL)
		if (m -> cols)
			m -> cols [dest]. add (m -> cols [source], e,
				dest, m -> rows);

	while ((m = dom_img. take ()) != NULL)
		if (m -> rows)
			m -> rows [source]. add (m -> rows [dest], -e,
				source, m -> cols);

	return;
} /* mmatrix<euclidom>::addcol */

template <class euclidom>
inline void mmatrix<euclidom>::swaprows (int i, int j)
{
	// in the trivial case nothing needs to be done
	if (i == j)
		return;

	// check if the parameters are not out of range
	if ((i < 0) || (i >= nrows) || (j < 0) || (j >= nrows))
		throw "Trying to swap rows out of range.";

	// swap the rows
	rows [i]. swap (rows [j], i, j, cols);

	// update the other matrices
	mmatrix<euclidom> *m;
	while ((m = img_img. take ()) != NULL)
		if ((m -> rows) && (m -> nrows))
			m -> rows [i]. swap (m -> rows [j], i, j, m -> cols);

	while ((m = img_dom. take ()) != NULL)
		if ((m -> cols) && (m -> ncols))
			m -> cols [i]. swap (m -> cols [j], i, j, m -> rows);

	return;
} /* mmatrix<euclidom>::swaprows */

template <class euclidom>
inline void mmatrix<euclidom>::swapcols (int i, int j)
{
	// in the trivial case nothing needs to be done
	if (i == j)
		return;

	// check if the parameters are not out of range
	if ((i < 0) || (i >= ncols) || (j < 0) || (j >= ncols))
		throw "Trying to swap cols out of range.";

	// swap the columns
	cols [i]. swap (cols [j], i, j, rows);

	// update the other matrices
	mmatrix<euclidom> *m;
	while ((m = dom_dom. take ()) != NULL)
		if ((m -> cols) && (m -> ncols))
			m -> cols [i]. swap (m -> cols [j], i, j, m -> rows);

	while ((m = dom_img. take ()) != NULL)
		if ((m -> rows) && (m -> nrows))
			m -> rows [i]. swap (m -> rows [j], i, j, m -> cols);

	return;
} /* mmatrix<euclidom>::swapcols */

template <class euclidom>
inline void mmatrix<euclidom>::multiplyrow (int n, const euclidom &e)
{
	// retrieve the row
	chain<euclidom> &therow = rows [n];

	// multiply the row
	therow. multiply (e);

	// multiply the corresponding entries in all the columns
	for (int i = 0; i < therow. size (); ++ i)
		cols [therow. num (i)]. multiply (e, n);

	return;
} /* mmatrix<euclidom>::multiplyrow */

template <class euclidom>
inline void mmatrix<euclidom>::multiplycol (int n, const euclidom &e)
{
	// retrieve the row
	chain<euclidom> &thecol = cols [n];

	// multiply the row
	thecol. multiply (e);

	// multiply the corresponding entries in all the rows
	for (int i = 0; i < thecol. size (); ++ i)
		rows [thecol. num (i)]. multiply (e, n);

	return;
} /* mmatrix<euclidom>::multiplycol */

template <class euclidom>
inline int mmatrix<euclidom>::findrowcol (int req_elements, int start,
	int which) const
// which: row = 1, col = 0
{
	// start at the starting point
	int i = start;
	int random_i = -1;

	// set loop to none
	int loopcounter = 0;

	// if a random start is requested, initialize it and set loop to 1
	if (start < 0)
	{
		i = random_i = std::rand () % (which ? nrows : ncols);
		loopcounter = 1;
	}

	// select some candidates
	int candidate = -1;
	int candidates_left = 3;

	// if the table has one of its dimensions trivial, return the result
	if (which ? !ncols : !nrows)
		return (((req_elements > 0) ||
			(i >= (which ? nrows : ncols))) ? -1 : i);

	// while the current position has not gone beyond the table
	while (i < (which ? nrows : ncols))
	{
		// if there is an appropriate row/column, return its number
		int l = (which ? rows : cols) [i]. size ();
		if ((req_elements >= 0) && (l >= req_elements))
			return i;
		else if ((req_elements < 0) && !l)
		{
			if (!candidates_left || !(which ? rows : cols) [i].
				contains_non_invertible ())
				return i;
			else
			{
				candidate = i;
				-- candidates_left;
				if (start < 0)
				{
					random_i = std::rand () %
						(which ? nrows : ncols);
					i = random_i - 1;
					loopcounter = 1;
				}
			}
		}

		// otherwise increase the counter and rewind to 0 if needed
		if (++ i >= (which ? nrows : ncols))
			if (loopcounter --)
				i = 0;

		// if the searching was started at a random position,
		// finish earlier
		if ((random_i >= 0) && !loopcounter && (i >= random_i))
			break;
	}

	// if not found, return the recent candidate (or -1 if none)
	return candidate;
} /* mmatrix<euclidom>::findrowcol */

template <class euclidom>
inline int mmatrix<euclidom>::findrow (int req_elements, int start) const
{
	return findrowcol (req_elements, start, 1);
} /* mmatrix<euclidom>::findrow */

template <class euclidom>
inline int mmatrix<euclidom>::findcol (int req_elements, int start) const
{
	return findrowcol (req_elements, start, 0);
} /* mmatrix<euclidom>::findcol */

template <class euclidom>
inline int mmatrix<euclidom>::reducerow (int n, int preferred)
{
	if (n >= nrows)
		throw "Trying to reduce a row out of range.";

	int the_other = -1;

	// repeat until the row contains at most one nonzero entry
	int len;
	while ((len = rows [n]. size ()) > 1)
	{
		// copy the row to a local structure
		chain<euclidom> local (rows [n]);

		// find the best element in this row
		int best_i = local. findbest (cols);

		// find the number of the preferred element in the row
		int preferred_i = (preferred < 0) ? -1 :
			local. findnumber (preferred);

		// check if the element in the preferred column
		// is equally good as the one already chosen
		if ((preferred_i >= 0) &&
			(local. coef (preferred_i). delta () ==
			local. coef (best_i). delta ()))
			best_i = preferred_i;

		// remember the column number containing this element
		the_other = local. num (best_i);

		// for each column
		for (int i = 0; i < len; ++ i)
		{
			// if this column is the chosen one, do nothing
			if (i == best_i)
				continue;

			// compute the quotient of two elements
			euclidom quotient = local. coef (i) /
				local. coef (best_i);

			// subtract the chosen column from the other one
			addcol (local. num (i), local. num (best_i),
				-quotient);
		}
	}

	return the_other;
} /* mmatrix<euclidom>::reducerow */

template <class euclidom>
inline int mmatrix<euclidom>::reducecol (int n, int preferred)
{
	if (n >= ncols)
		throw "Trying to reduce a column out of range.";

	int the_other = -1;

	// repeat until the column contains at most one nonzero entry
	int len;
	while ((len = cols [n]. size ()) > 1)
	{
		// copy the column to a local structure
		chain<euclidom> local (cols [n]);

		// find the best element in this column
		int best_i = local. findbest (rows);

		// find the number of the preferred element in the row
		int preferred_i = (preferred < 0) ? -1 :
			local. findnumber (preferred);

		// check if the element in the preferred column
		// is equally good as the one already chosen
		if ((preferred_i >= 0) &&
			(local. coef (preferred_i). delta () ==
			local. coef (best_i). delta ()))
			best_i = preferred_i;

		// remember the row number containing this element
		the_other = local. num (best_i);

		// for each row
		for (int i = 0; i < len; ++ i)
		{
			// if this row is the chosen one, do nothing
			if (i == best_i)
				continue;

			// compute the quotient of two elements
			euclidom quotient = local. coef (i) /
				local. coef (best_i);

			// subtract the chosen row from the other one
			addrow (local. num (i), local. num (best_i),
				-quotient);
		}
	}

	return the_other;
} /* mmatrix<euclidom>::reducecol */

template <class euclidom>
inline outputstream &mmatrix<euclidom>::showrowscols (outputstream &out,
	chain<euclidom> *table, int tablen, int first, int howmany,
	const char *label) const
{
	if ((first < 0) || (first >= tablen))
		first = 0;
	if ((howmany <= 0) || (first + howmany > tablen))
		howmany = tablen - first;
	for (int i = 0; i < howmany; ++ i)
		out << (label ? label : "") << (first + i + 1) << ": " <<
			table [first + i] << '\n';
	out << '\n';
	return out;
} /* matrix<euclidom>::showrowscols */

template <class euclidom>
inline outputstream &mmatrix<euclidom>::showrows (outputstream &out,
	int first, int howmany, const char *label) const
{
	return showrowscols (out, rows, nrows, first, howmany, label);
} /* mmatrix<euclidom>::showrows */

template <class euclidom>
inline std::ostream &mmatrix<euclidom>::showrows (std::ostream &out,
	int first, int howmany, const char *label) const
{
	outputstream tout (out);
	showrows (tout, first, howmany, label);
	return out;
} /* mmatrix<euclidom>::showrows */

template <class euclidom>
inline outputstream &mmatrix<euclidom>::showcols (outputstream &out,
	int first, int howmany, const char *label) const
{
	return showrowscols (out, cols, ncols, first, howmany, label);
} /* mmatrix<euclidom>::showcols */

template <class euclidom>
inline std::ostream &mmatrix<euclidom>::showcols (std::ostream &out,
	int first, int howmany, const char *label) const
{
	outputstream tout (out);
	showcols (tout, first, howmany, label);
	return out;
} /* mmatrix<euclidom>::showcols */

template <class euclidom>
inline outputstream &mmatrix<euclidom>::showmap (outputstream &out,
	const char *maplabel, const char *xlabel, const char *ylabel) const
{
	if (ncols <= 0)
	{
		if (maplabel && (maplabel [0] == '\t'))
 			out << "\t0\n";
 		else
			out << "0\n";
	}
	for (int i = 0; i < ncols; ++ i)
	{
		out << (maplabel ? maplabel : "f") << " (" <<
			(xlabel ? xlabel : "") << (i + 1) << ") = ";
		cols [i]. show (out, ylabel) << '\n';
	}
	return out;
} /* mmatrix<euclidom>::showmap */

template <class euclidom>
inline std::ostream &mmatrix<euclidom>::showmap (std::ostream &out,
	const char *maplabel, const char *xlabel, const char *ylabel) const
{
	outputstream tout (out);
	showmap (tout, maplabel, xlabel, ylabel);
	return out;
} /* mmatrix<euclidom>::showmap */

template <class euclidom>
inline void mmatrix<euclidom>::simple_reductions (bool quiet)
{
	// if the matrix has no rows or no columns,
	// simple reductions make no sense
	if (!nrows || !ncols)
		return;

	// prepare counters
	long countreduced = 0;
	long count = 4 * ((nrows > ncols) ? ncols : nrows);

	// prepare quazi-random numbers
	int nr = std::rand () % nrows;
	int nr_count = 0;
	int nr_add = 0;

	// try quazi-random reductions
	while (count --)
	{
		// try a simple reduction
		if ((rows [nr]. size () == 1) &&
			(rows [nr]. coef (0). delta () == 1) &&
			(cols [rows [nr]. num (0)]. size () > 1))
		{
			++ countreduced;
			reducecol (rows [nr]. num (0), -1);
		}

		// try a new semi-random position
		if (nr_count)
			-- nr_count;
		else
		{
			nr_add = ((std::rand () >> 2) + 171) % nrows;
			if (nr_add < 1)
				nr_add = 1;
			nr_count = 100;
		}
		nr += nr_add;
		if (nr >= nrows)
			nr -= nrows;

		// display a counter
		if (!quiet && !(count % 373))
			scon << std::setw (12) << count <<
				"\b\b\b\b\b\b\b\b\b\b\b\b";
	}

	if (!quiet)
		sout << countreduced << " +";

	return;
} /* mmatrix<euclidom>::simple_reductions */

template <class euclidom>
inline void mmatrix<euclidom>::simple_form (bool quiet)
{
	// if the matrix has no rows or columns, it is already in simple form
	if (!nrows || !ncols)
		return;

	// make some random simple reductions before proceeding
	simple_reductions (quiet);

	// prepare a counter
	long count = 0;

	// prepare variables for chosen row and column numbers
	int row, col, prev_row, prev_col;

	// find a row or a column with at least two nonzero entries
	row = -1;
	col = findcol (2);
	prev_row = -1, prev_col = -1;
	if (col < 0)
		row = findrow (2);

	// repeat while such a row or a column can be found
	while ((row >= 0) || (col >= 0))
	{
		// reduce rows and columns until a single entry remains
		while ((row >= 0) || (col >= 0))
			if (row >= 0)
			{
				col = reducerow (row, prev_col);
				prev_row = row;
				row = -1;
			}
			else if (col >= 0)
			{
				row = reducecol (col, prev_row);
				prev_col = col;
				col = -1;
			}

		// update the counter and display it if requested to
		++ count;
		if (!quiet && !(count % 373))
			scon << std::setw (12) << count <<
				"\b\b\b\b\b\b\b\b\b\b\b\b";

		// find another row or column with at least 2 nonzero entries
		col = findcol (2);
		if (col < 0)
			row = findrow (2);
	}

	if (!quiet)
		sout << " " << count << " reductions made. ";

	return;
} /* mmatrix<euclidom>::simple_form */

template <class euclidom>
inline void mmatrix<euclidom>::invert (void)
{
	// check if the matrix is square
	if (nrows != ncols)
		throw "Trying to invert a non-square matrix.";

	// if the matrix is trivial, nothing needs to be done
	if (!nrows)
		return;

	// create the identity matrix of the appropriate size
	mmatrix<euclidom> m;
	m. identity (ncols);
	
	// transform the matrix to the identity
	// by row operations (swapping and adding)
	// and apply the same operations to the matrix 'm'
	for (int col = 0; col < ncols; ++ col)
	{
		// find an invertible element in the column
		int len = cols [col]. size ();
		if (len <= 0)
		{
			throw "Matrix inverting: Zero column found.";
		}
		int chosen = 0;
		while ((chosen < len) &&
			((cols [col]. num (chosen) < col) ||
			(cols [col]. coef (chosen). delta () != 1)))
		{
			++ chosen;
		}
		if (chosen >= len)
		{
			throw "Matrix inverting: "
				"No invertible element in a column.";
		}

		// make the leading entry equal 1 in the chosen row
		euclidom invcoef;
		invcoef = 1;
		invcoef = invcoef / cols [col]. coef (chosen);
		m. multiplyrow (cols [col]. num (chosen), invcoef);
		multiplyrow (cols [col]. num (chosen), invcoef);

		// move the chosen row to the diagonal position
		m. swaprows (col, cols [col]. num (chosen));
		swaprows (col, cols [col]. num (chosen));

		// zero the column below and above the chosen entry
		invcoef = -1;
		for (int i = 0; i < len; ++ i)
		{
			if (cols [col]. num (i) == col)
				continue;
			euclidom coef = invcoef * cols [col]. coef (i);
			m. addrow (cols [col]. num (i), col, coef);
			addrow (cols [col]. num (i), col, coef);
			-- i;
			-- len;
		}
	}

	// take the matrix 'm' as the result
	for (int i = 0; i < ncols; ++ i)
	{
		cols [i]. take (m. cols [i]);
		rows [i]. take (m. rows [i]);
	}

	return;
} /* mmatrix<euclidom>::invert */

template <class euclidom>
inline void mmatrix<euclidom>::multiply (const mmatrix<euclidom> &m1,
	const mmatrix<euclidom> &m2)
{
	if (m1. ncols != m2. nrows)
		throw "Trying to multiply matrices of wrong sizes.";
	int K = m1. ncols;
	define (m1. nrows, m2. ncols);
	for (int i = 0; i < nrows; ++ i)
	{
		for (int j = 0; j < ncols; ++ j)
		{
			euclidom e;
			e = 0;
			for (int k = 0; k < K; ++ k)
				e += m1. get (i, k) * m2. get (k, j);
			add (i, j, e);
		}
	}
	return;
} /* mmatrix<euclidom>::multiply */

template <class euclidom>
inline void mmatrix<euclidom>::submatrix (const mmatrix<euclidom> &matr,
	const chain<euclidom> &domain, const chain<euclidom> &range)
{
	for (int i = 0; i < domain. size (); ++ i)
	{
		for (int j = 0; j < range. size (); ++ j)
		{
			euclidom e = matr. get (domain. num (i),
				range. num (j));
			if (!(e == 0))
				add (i, j, e);
		}
	}

	return;
} /* mmatrix<euclidom>::submatrix */

template <class euclidom>
inline outputstream &mmatrix<euclidom>::show_hom_col (outputstream &out,
	int col, const chain<euclidom> &range, const char *txt) const
{
	// keep current position in 'range'
	int j = 0;

	// remember if this is the first displayed element
	int first = 1;

	// go through the column of the matrix
	for (int i = 0; i < cols [col]. size (); ++ i)
	{
		// find the current element in the range
		while ((j < range. size ()) &&
			(range. num (j) < cols [col]. num (i)))
		{
			++ j;
		}

		// if this element was found in the range, display it
		if ((j < range. size ()) &&
			(range. num (j) == cols [col]. num (i)))
		{
			if (first)
				first = 0;
			else
				out << " + ";
			if (-cols [col]. coef (i) == 1)
				out << "-";
			else if (cols [col]. coef (i) != 1)
				out << cols [col]. coef (i) << " * ";
			if (txt)
				out << txt;
			out << (j + 1);
		}
	}

	// if nothing was shown, display 0
	if (first)
		out << 0;

	return out;
} /* mmatrix<euclidom>::show_hom_col */

template <class euclidom>
inline std::ostream &mmatrix<euclidom>::show_hom_col (std::ostream &out, int col,
	const chain<euclidom> &range, const char *txt) const
{
	outputstream tout (out);
	show_hom_col (tout, col, range, txt);
	return out;
} /* mmatrix<euclidom>::show_hom_col */

// --------------------------------------------------

template <class euclidom>
inline void mmatrix<euclidom>::increase (int numrows, int numcols)
{
	increaserows (numrows);
	increasecols (numcols);
	return;
} /* mmatrix<euclidom>::increase */

template <class euclidom>
inline void mmatrix<euclidom>::increaserows (int numrows)
{
	if (allrows >= numrows)
		return;
	chain<euclidom> *newrows = new chain<euclidom> [numrows];
	if (!newrows)
		throw "Not enough memory for matrix rows.";
	for (int i = 0; i < nrows; ++ i)
		newrows [i]. take (rows [i]);
	if (rows)
		delete [] rows;
	rows = newrows;
	allrows = numrows;
	return;
} /* mmatrix<euclidom>::increaserows */

template <class euclidom>
inline void mmatrix<euclidom>::increasecols (int numcols)
{
	if (allcols >= numcols)
		return;
	chain<euclidom> *newcols = new chain<euclidom> [numcols];
	if (!newcols)
		throw "Not enough memory for matrix columns.";
	for (int i = 0; i < ncols; ++ i)
		newcols [i]. take (cols [i]);
	if (cols)
		delete [] cols;
	cols = newcols;
	allcols = numcols;

	return;
} /* mmatrix<euclidom>::increasecols */

// --------------------------------------------------

/// Writes a matrix to the output stream as a map in terms of columns.
/// Warning: The operators >> and << are not symmetric for matrices.
template <class euclidom>
inline std::ostream &operator << (std::ostream &out,
	const mmatrix<euclidom> &m)
{
	return m. showcols (out);
} /* operator << */


// --------------------------------------------------
// ------------------ chaincomplex ------------------
// --------------------------------------------------

/// This is an implementation of a chain complex over an arbitrary ring.
/// The dimension of the chain complex must be known apriori.
/// If there are elements not used in boundaries, use "def_gen" to set
/// the true number of generators at each level.
template <class euclidom>
class chaincomplex
{
public:
	/// The default constructor. The dimension must be defined
	/// apriori and cannot be modified later. If requested,
	/// additional matrices are created to trace homology generators.
	chaincomplex (int d, int trace_generators = 0);

	/// The destructor.
	~chaincomplex ();

	/// Defines the number of generators in the given dimension.
	/// This number is automatically increased while boundary formulas
	/// are added. However, it must be used if some generators do not
	/// appear in the boundaries or have zero boundaries.
	void def_gen (int q, int n);

	/// Adds a coefficient to the structure: D_q [m, n] += e.
	/// In other words, boundary of element n += e * element m.
	void add (int q, int m, int n, const euclidom &e);

	/// Returns an element from the boundary matrix
	/// for the given dimension.
	euclidom get (int q, int row, int col) const;

	/// Returns a reference to the given boundary matrix.
	const mmatrix<euclidom> &getboundary (int i) const;

	/// Returns the number of generators at the given level.
	int getnumgen (int i) const;

	/// Returns the dimension of the chain complex.
	int dim () const;

	/// Returns the given homology generator at level q.
	/// Note: 'i' must be the number of chain generator.
	const chain<euclidom> &gethomgen (int q, int i) const;

	/// Reduces of the given boundary matrix in the chain complex
	/// for the purpose of homology computation.
	void simple_form (int which, bool quiet);

	/// Runs the reduction of all the boundary matrices
	/// in the chain complex. If the array of levels is given,
	/// computes only simple forms necessary for homology levels
	/// for which the entries in the array are nonzero.
	void simple_form (const int *level, bool quiet);

	/// Computes the given level of homology of the chain complex,
	/// provided it has been transformed into the simple form previously.
	/// Encodes this homology group as a chain which is a combination
	/// generator numbers together with their torsion coefficients
	/// (or with 1's if none).
	int simple_homology (chain<euclidom> &result, int which) const;

	/// Computes the homology of the chain complex, provided it has
	/// been transformed into the simple form previously.
	/// Encodes the homology as a table of chains (one chain for each
	/// dimension) which are combinations of generator numberss together
	/// with their torsion coefficients (or with 1's if none).
	/// Returns the dimension of the chain complex.
	/// If a table of levels is given, computes only these levels
	/// of homology for which the table's entry is nonzero.
	int simple_homology (chain<euclidom> *&result,
		const int *level = NULL) const;

	/// Creates a chain complex containing exactly one generator
	/// for each homology generator. This function is used for
	/// extracting the map induced in homology by a chain map.
	void take_homology (const chain<euclidom> *hom_chain);

	/// Writes the homology module of the chain complex to an output
	/// stream. If a table of levels is given, shows only these levels
	/// for which the table's entry is nonzero.
	outputstream &show_homology (outputstream &out,
		const chain<euclidom> *hom,
		const int *level = NULL) const;

	/// Writes the homology module of the chain complex to an output
	/// stream. If a table of levels is given, shows only these levels
	/// for which the table's entry is nonzero.
	std::ostream &show_homology (std::ostream &out,
		const chain<euclidom> *hom,
		const int *level = NULL) const;

	/// Writes the homology generators of the homology module to an
	/// output stream. Each generator as a combination of the original
	/// ones is shown on a separate line.
	outputstream &show_generators (outputstream &out,
		const chain<euclidom> &list, int q) const;

	/// Writes the homology generators of the homology module to an
	/// output stream. Each generator as a combination of the original
	/// ones is shown on a separate line.
	std::ostream &show_generators (std::ostream &out,
		const chain<euclidom> &list, int q) const;

	/// Computes the homology and shows the result.
	outputstream &compute_and_show_homology (outputstream &out,
		chain<euclidom> *&hom, const int *level = NULL);

	/// Computes the homology and shows the result.
	std::ostream &compute_and_show_homology (std::ostream &out,
		chain<euclidom> *&hom, const int *level = NULL);

	/// The class "chainmap" is a friend class which has access
	/// to the internal data of the chain complex class.
	friend class chainmap<euclidom>;

private:
	/// The copy constructor is not implemented.
	chaincomplex (const chaincomplex<euclidom> &m)
		{throw "Copying constructor not implemented "
		"for a chain complex.";}

	/// The assignment operator is not implemented.
	chaincomplex<euclidom> &operator =
		(const chaincomplex<euclidom> &s)
		{throw "Operator = not implemented "
		"for a chain complex."; return *this;}

	/// The length of the chain complex (i.e., its dimension + 1).
	int len;

	/// The matrices of the boundary homomorphism.
	/// "D_q" is stored in "boundary [q]".
	mmatrix<euclidom> *boundary;

	/// Matrices which store actual combinations of generators.
	/// Used for the extraction of generators of homology.
	mmatrix<euclidom> *generators;

	/// Have the generator tracing matrices been initialized
	/// to the identity (of suitable size each)?
	int *generators_initialized;

	/// The numbers of generators in each dimension,
	/// or -1's if not defined yet.
	int *numgen;

}; /* class chaincomplex */

// --------------------------------------------------

template <class euclidom>
inline chaincomplex<euclidom>::chaincomplex (int d, int trace_generators)
{
	// set the number of tables to be sufficient for 0 to d inclusive
	len = (d >= 0) ? (d + 1) : 0;

	// create a table of empty matrices
	boundary = len ? new mmatrix<euclidom> [len] : NULL;

	// create a table of matrices for tracing generators of homology
	generators = (trace_generators && len) ?
		new mmatrix<euclidom> [len] : NULL;
	if (generators)
		generators_initialized = new int [len];
	else
        	generators_initialized = NULL;

	// create a table of generator numbers
	numgen = len ? new int [len] : NULL;

	// link the boundary matrices to each other and to the generators
	for (int i = 0; i < len; ++ i)
	{
		numgen [i] = -1;
		if (i < len - 1)
			boundary [i]. dom_img. add (boundary [i + 1]);
		if (i > 0)
			boundary [i]. img_dom. add (boundary [i - 1]);
		if (generators)
		{
			boundary [i]. dom_dom. add (generators [i]);
			if (i > 0)
				boundary [i]. img_dom. add
					(generators [i - 1]);
			generators_initialized [i] = 0;
		}
	}

	return;
} /* chaincomplex<euclidom>::chaincomplex */

template <class euclidom>
inline chaincomplex<euclidom>::~chaincomplex ()
{
	if (boundary)
		delete [] boundary;
	if (generators)
		delete [] generators;
	if (numgen)
		delete [] numgen;
	if (generators_initialized)
		delete [] generators_initialized;
	return;
} /* chaincomplex<euclidom>::~chaincomplex */

template <class euclidom>
inline void chaincomplex<euclidom>::def_gen (int q, int n)
{
	if ((q < 0) || (q >= len))
		return;

	if (numgen [q] < n)
		numgen [q] = n;

	if (q == 0)
		boundary [0]. define (0, numgen [q]);
	if ((q > 0) && (numgen [q - 1] >= 0))
		boundary [q]. define (numgen [q - 1], numgen [q]);
	if ((q < dim ()) && (numgen [q + 1] >= 0))
		boundary [q + 1]. define (numgen [q], numgen [q + 1]);

	return;
} /* chaincomplex<euclidom>::def_gen */

template <class euclidom>
inline void chaincomplex<euclidom>::add (int q, int m, int n,
	const euclidom &e)
{
	if ((q <= 0) || (q >= len))
		throw "Trying to add a boundary for dimension out of range";

	if (numgen [q] <= n)
		numgen [q] = n + 1;
	if (numgen [q - 1] <= m)
		numgen [q - 1] = m + 1;

	boundary [q]. add (m, n, e);
	return;
} /* chaincomplex<euclidom>::add */

template <class euclidom>
inline euclidom chaincomplex<euclidom>::get (int q, int row, int col) const
{
	if ((q <= 0) || (q >= len))
		throw "Boundary coefficient out of range from chain cplx.";

	return boundary [q]. get (row, col);
} /* chaincomplex<euclidom>::get */

template <class euclidom>
inline const mmatrix<euclidom> &chaincomplex<euclidom>::getboundary (int i)
	const
{
	if ((i <= 0) || (i >= len))
		throw "Boundary matrix out of range from chain complex.";

	return boundary [i];
} /* chaincomplex<euclidom>::getboundary */

template <class euclidom>
inline int chaincomplex<euclidom>::getnumgen (int i) const
{
	if ((i < 0) || (i >= len))
	//	throw "Level for the number of generators out of range.";
		return 0;

	if (numgen [i] < 0)
		return 0;
	else
		return numgen [i];
} /* chaincomplex<euclidom>::getnumgen */

template <class euclidom>
inline int chaincomplex<euclidom>::dim () const
{
	return len - 1;
} /* chaincomplex<euclidom>::dim */

template <class euclidom>
inline const chain<euclidom> &chaincomplex<euclidom>::gethomgen (int q,
	int i) const
{
	if ((q < 0) || (q >= len))
		throw "Level for homology generators out of range.";
	if (!generators_initialized [q])
		throw "Trying to get non-existent homology generators.";
	return generators [q]. getcol (i);
} /* chaincomplex<euclidom>::getgen */

template <class euclidom>
inline void chaincomplex<euclidom>::simple_form (int which, bool quiet)
{
//	if ((which < 0) || (which >= len))
//		throw "Trying to find the simple form of a wrong matrix.";

	// if the generator tracing matrices are not initialized, do it now
	if (generators)
	{
		if (!generators_initialized [which])
			generators [which]. identity (numgen [which]);
		generators_initialized [which] = 1;
		if ((which > 0) && (!generators_initialized [which - 1]))
		{
			generators [which - 1]. identity
				(numgen [which - 1]);
			generators_initialized [which - 1] = 1;
		}
	}

	// verify that the adjacent matrices have sufficient size
	if (which > 0)
	{
		int n = boundary [which]. getnrows ();
		mmatrix<euclidom> &other = boundary [which - 1];
		if (other. getncols () < n)
			other. define (other. getnrows (), n);
	}
	if (which < len - 1)
	{
		int n = boundary [which]. getncols ();
		mmatrix<euclidom> &other = boundary [which + 1];
		if (other. getnrows () < n)
			other. define (n, other. getncols ());
	}

	// compute simple form of the desired boundary matrix
	if (!quiet && which)
		sout << "Reducing D_" << which << ": ";
	boundary [which]. simple_form (quiet);
	if (!quiet && which)
		sout << '\n';

	return;
} /* chaincomplex<euclidom>::simple_form */

template <class euclidom>
inline void chaincomplex<euclidom>::simple_form (const int *level,
	bool quiet)
{
	for (int i = len - 1; i >= 0; -- i)
	{
		if (!level || level [i] || (i && level [i - 1]))
			simple_form (i, quiet);
	}
	return;
} /* chaincomplex<euclidom>::simple_form */

template <class euclidom>
inline int chaincomplex<euclidom>::simple_homology (chain<euclidom> &result,
	int which) const
{
	int g = boundary [which]. findcol (-1, 0);
	while (g >= 0)
	{
		euclidom e;
		if (which == dim ())
			e = 0;
		else
			e = boundary [which + 1]. get (g, -1);
		if (e == 0)
		{
			e = 1;
			result. add (g, e);
		}
		else if (e. delta () > 1)
			result. add (g, e. normalized ());
		g = boundary [which]. findcol (-1, g + 1);
	}

	return which;
} /* chaincomplex<euclidom>::simple_homology */

template <class euclidom>
inline int chaincomplex<euclidom>::simple_homology (chain<euclidom> *&result,
	const int *level) const
{
	// if the chain complex is empty, then just set the result to NULL
	if (!len)
	{
		result = NULL;
		return dim ();
	}

	result = new chain<euclidom> [len];
	if (!result)
		throw "Not enough memory to create homology chains.";

	for (int q = 0; q < len; ++ q)
	{
		if (!level || level [q])
			simple_homology (result [q], q);
	}

	return dim ();
} /* chaincomplex<euclidom>::simple_homology */

template <class euclidom>
inline void chaincomplex<euclidom>::take_homology
	(const chain<euclidom> *hom_chain)
{
	if (!hom_chain)
		return;
	for (int q = 0; q < len; ++ q)
		def_gen (q, hom_chain [q]. size ());
	return;
} /* chaincomplex<euclidom>::take_homology */

template <class euclidom>
inline outputstream &chaincomplex<euclidom>::show_homology
	(outputstream &out, const chain<euclidom> *hom, const int *level)
	const
{
	int max_level = len - 1;
	while ((max_level >= 0) && !hom [max_level]. size ())
		-- max_level;
	++ max_level;
	for (int q = 0; q < max_level; ++ q)
	{
		if (!level || level [q])
		{
			out << "H_" << q << " = ";
			capd::homology::show_homology (out, hom [q]);
			out << '\n';
		}
	}
	return out;
} /* chaincomplex<euclidom>::show_homology */

template <class euclidom>
inline std::ostream &chaincomplex<euclidom>::show_homology (std::ostream &out,
	const chain<euclidom> *hom, const int *level) const
{
	outputstream tout (out);
	show_homology (tout, hom, level);
	return out;
} /* chaincomplex<euclidom>::show_homology */

template <class euclidom>
inline outputstream &chaincomplex<euclidom>::show_generators
	(outputstream &out, const chain<euclidom> &list, int q) const
{
	if (!generators || (q < 0) || (q >= len))
		return out;
	for (int i = 0; i < list. size (); ++ i)
		out << gethomgen (q, list. num (i)) << '\n';
	return out;
} /* chaincomplex<euclidom>::show_generators */

template <class euclidom>
inline std::ostream &chaincomplex<euclidom>::show_generators (std::ostream &out,
	const chain<euclidom> &list, int q) const
{
	outputstream tout (out);
	show_generators (tout, list, q);
	return out;
} /* chaincomplex<euclidom>::show_generators */

template <class euclidom>
inline outputstream &chaincomplex<euclidom>::compute_and_show_homology
	(outputstream &out, chain<euclidom> *&hom, const int *level)
{
	simple_form (level, false);
	simple_homology (hom, level);
	show_homology (out, hom, level);
	return out;
} /* chaincomplex<euclidom>::compute_and_show_homology */

template <class euclidom>
inline std::ostream &chaincomplex<euclidom>::compute_and_show_homology
	(std::ostream &out, chain<euclidom> *&hom, const int *level)
{
	outputstream tout (out);
	compute_and_show_homology (tout, hom, level);
	return out;
} /* chaincomplex<euclidom>::compute_and_show_homology */

// --------------------------------------------------

/// Writes a chain complex to an output stream in the text format.
template <class euclidom>
inline std::ostream &operator << (std::ostream &out,
	const chaincomplex<euclidom> &c)
{
	out << "chain complex" << '\n';
	out << "max dimension " << c. dim () << '\n';
	out << "dimension 0: " << c. getnumgen (0) << '\n';
	for (int i = 1; i <= c. dim (); ++ i)
	{
		out << "dimension " << i << ": " << c. getnumgen (i) << '\n';
		for (int j = 0; j < c. getnumgen (i); ++ j)
		{
			if (c. getboundary (i). getcol (j). size ())
			{
				out << "\t# " << (j + 1) << " = " <<
					c. getboundary (i). getcol (j) <<
						'\n';
			}
		}
	}
	return out;
} /* operator << */


// --------------------------------------------------
// -------------------- chainmap --------------------
// --------------------------------------------------

/// This class defines a chain map between two chain complexes.
/// The chain complexes must exist and not change durign the existence
/// of the chain map.
template <class euclidom>
class chainmap
{
public:
	/// The default constructor of a chain map between the two given
	/// chain complexes.
	chainmap (const chaincomplex<euclidom> &domain,
		const chaincomplex<euclidom> &range);

	/// Copy constructor.
	chainmap (const chainmap<euclidom> &c);
	
	/// The assignment operator.
	chainmap<euclidom> &operator = (const chainmap<euclidom> &c);

	/// The destructor.
	~chainmap ();

	/// Returns the dimension of the chain map.
	int dim () const;

	/// Returns the matrix of the chain map at the given level.
	const mmatrix<euclidom> &operator [] (int i) const;

	/// Adds a coefficient to the selected matrix of the map:
	/// M_q [m, n] += e. In other words, the image of n += e * m.
	void add (int q, int m, int n, euclidom e);

	/// Inverts the chain map.
	void invert (void);

	/// Composes two given chain maps. The chain map is replaced
	/// by the result of this composition.
	void compose (const chainmap<euclidom> &m1,
		const chainmap<euclidom> &m2);

	/// Writes the chain map to an output stream in the text format
	/// using specified labels for the map and elements in the domain
	/// and in the codomain of the map.
	outputstream &show (outputstream &out,
		const char *maplabel = "f", const char *xtxt = NULL,
		const char *ytxt = NULL, const int *level = NULL) const;

	/// Writes the chain map to an output stream in the text format
	/// using specified labels for the map and elements in the domain
	/// and in the codomain of the map.
	std::ostream &show (std::ostream &out,
		const char *maplabel = "f", const char *xtxt = NULL,
		const char *ytxt = NULL, const int *level = NULL) const;

	/// Creates a chain map that represents the map induced in homology
	/// by the chain map between the two given chain complexes
	/// which have been previously transformed to the simple form.
	void take_homology (const chainmap<euclidom> &m,
		const chain<euclidom> *hom_domain,
		const chain<euclidom> *hom_range);

	/// Writes to an output stream the map induced in homology.
	/// If the array of levels is provided, only these homology levels
	/// are displayed for which the array has a nonzero entry.
	outputstream &show_homology (outputstream &out,
		const chain<euclidom> *hom_domain,
		const chain<euclidom> *hom_range, const int *level = NULL,
		const char *xtxt = NULL, const char *ytxt = NULL) const;

	/// Writes to an output stream the map induced in homology.
	/// If the array of levels is provided, only these homology levels
	/// are displayed for which the array has a nonzero entry.
	std::ostream &show_homology (std::ostream &out,
		const chain<euclidom> *hom_domain,
		const chain<euclidom> *hom_range,
		const int *level = NULL,
		const char *xtxt = NULL, const char *ytxt = NULL)
		const;

private:
	/// The number of matrices (dimension of the chain map + 1).
	int len;

	/// The matrices in each dimension.
	mmatrix<euclidom> *map;

}; /* class chainmap */

// --------------------------------------------------

template <class euclidom>
inline chainmap<euclidom>::chainmap (const chaincomplex<euclidom> &domain,
	const chaincomplex<euclidom> &range)
{
	// set the dimension
	len = domain. len;
	if (range. len < domain. len)
		len = range. len;

	// allocate new matrices
	if (len)
		map = new mmatrix<euclidom> [len];
	else
		map = NULL;

	for (int i = 0; i < len; ++ i)
	{
		// define the size of the matrix (number of rows and columns)
		map [i]. define (range. getnumgen (i),
			domain. getnumgen (i));

		// link the matrices to the ones in the chain complexes
		domain. boundary [i]. dom_dom. add (map [i]);
		range. boundary [i]. dom_img. add (map [i]);
		if (i < domain. len - 1)
			domain. boundary [i + 1]. img_dom. add (map [i]);
		if (i < range. len - 1)
			range. boundary [i + 1]. img_img. add (map [i]);
	}

	return;
} /* chainmap<euclidom>::chainmap */

template <class euclidom>
inline chainmap<euclidom>::chainmap (const chainmap<euclidom> &c)
{
	len = c. len;
	if (len)
		map = new mmatrix<euclidom> [len];
	else
		map = 0;

	for (int i = 0; i < len; ++ i)
		map [i] = c. map [i];

	return;
} /* chainmap<euclidom>::chainmap */

template <class euclidom>
inline chainmap<euclidom> &chainmap<euclidom>::operator =
	(const chainmap<euclidom> &c)
{
	if (map)
		delete [] map;

	len = c. len;
	if (len)
		map = new mmatrix<euclidom> [len];
	else
		map = 0;

	for (int i = 0; i < len; ++ i)
		map [i] = c. map [i];

	return;
} /* chainmap<euclidom>::operator = */

template <class euclidom>
inline chainmap<euclidom>::~chainmap ()
{
	if (map)
		delete [] map;
	return;
} /* chainmap<euclidom>::~chainmap */

template <class euclidom>
inline int chainmap<euclidom>::dim () const
{
	return len - 1;
} /* chainmap<euclidom>::dim */

template <class euclidom>
inline const mmatrix<euclidom> &chainmap<euclidom>::operator [] (int i) const
{
//	if ((i < 0) || (i >= len))
//		throw "Chain map level out of range.";
	return map [i];
} /* chainmap<euclidom>::operator [] */

template <class euclidom>
inline void chainmap<euclidom>::add (int q, int m, int n, euclidom e)
{
	map [q]. add (m, n, e);
	return;
} /* chainmap<euclidom>::add */

template <class euclidom>
inline void chainmap<euclidom>::take_homology (const chainmap<euclidom> &m,
	const chain<euclidom> *hom_domain, const chain<euclidom> *hom_range)
{
	if (!hom_domain || !hom_range)
		return;

	for (int q = 0; q < len; ++ q)
	{
		int dlen = hom_domain [q]. size ();
		const chain<euclidom> &r = hom_range [q];
		int rlen = r. size ();
		map [q]. define (rlen, dlen);
		// go through the homology generators in the domain
		for (int i = 0; i < dlen; ++ i)
		{
			// retrieve the real number of the homology generator
			int x = hom_domain [q]. num (i);

			// get the image of this element by the chain map
			const chain<euclidom> &img = m [q]. getcol (x);

			// transform numbers in this image to hom. generators
			int j = 0;
			for (int k = 0; k < img. size (); ++ k)
			{
				// find the current element in the range
				while ((j < rlen) &&
					(r. num (j) < img. num (k)))
					++ j;

				// if found in the range, add it
				if ((j < rlen) &&
					(r. num (j) == img. num (k)))
					map [q]. add (j, i, img. coef (k));
			}
		}
	}
	return;
} /* chainmap<euclidom>::take_homology */

template <class euclidom>
inline void chainmap<euclidom>::invert (void)
{
	for (int q = 0; q < len; ++ q)
		map [q]. invert ();
	return;
} /* chainmap<euclidom>::invert */

template <class euclidom>
inline void chainmap<euclidom>::compose (const chainmap<euclidom> &m1,
	const chainmap<euclidom> &m2)
{
	for (int q = 0; q < len; ++ q)
		map [q]. multiply (m1. map [q], m2. map [q]);
	return;
} /* chainmap<euclidom>::compose */

template <class euclidom>
inline outputstream &chainmap<euclidom>::show (outputstream &out,
	const char *maplabel, const char *xtxt, const char *ytxt,
	const int *level) const
{
	for (int q = 0; q < len; ++ q)
	{
		if (level && !level [q])
			continue;
		out << "Dim " << q << ":";
		map [q]. showmap (out, maplabel, xtxt, ytxt);
	}
	return out;
} /* chainmap<euclidom>::show */

template <class euclidom>
inline std::ostream &chainmap<euclidom>::show (std::ostream &out,
	const char *maplabel, const char *xtxt, const char *ytxt,
	const int *level) const
{
	outputstream tout (out);
	show (tout, maplabel, xtxt, ytxt, level);
	return out;
} /* chainmap<euclidom>::show */

template <class euclidom>
inline outputstream &chainmap<euclidom>::show_homology (outputstream &out,
	const chain<euclidom> *hom_domain,
	const chain<euclidom> *hom_range, const int *level,
	const char *xtxt, const char *ytxt) const
{
	int max_len = len - 1;
	while ((max_len >= 0) && !hom_domain [max_len]. size ())
		-- max_len;
	++ max_len;
	for (int q = 0; q < max_len; ++ q)
	{
		if (!level || level [q])
		{
			out << "Dim " << q << ":";
			int hlen = hom_domain [q]. size ();
			if (!hlen)
				out << "\t0" << '\n';
			for (int i = 0; i < hlen; ++ i)
			{
				out << "\tf (";
 				if (xtxt)
					out << xtxt;
				out << (i + 1) << ") = ";
				map [q]. show_hom_col (out,
					hom_domain [q]. num (i),
					hom_range [q], ytxt);
				out << '\n';
			}
		}
	}
	return out;
} /* chainmap<euclidom>::show_homology */

template <class euclidom>
inline std::ostream &chainmap<euclidom>::show_homology (std::ostream &out,
	const chain<euclidom> *hom_domain,
	const chain<euclidom> *hom_range, const int *level,
	const char *xtxt, const char *ytxt) const
{
	outputstream tout (out);
	show_homology (tout, hom_domain, hom_range, level, xtxt, ytxt);
	return out;
} /* chainmap<euclidom>::show_homology */

// --------------------------------------------------

/// Writes a chain map to an output stream in the text format.
template <class euclidom>
inline std::ostream &operator << (std::ostream &out,
	const chainmap<euclidom> &m)
{
	out << "chain map" << '\n';
	for (int i = 0; i <= m. dim (); ++ i)
	{
		out << "dimension " << i << '\n';
		for (int j = 0; j < m [i]. getncols (); ++ j)
		{
			if (m [i]. getcol (j). size ())
			{
				out << "\t# " << (j + 1) << " = " <<
					m [i]. getcol (j) << '\n';
			}
		}
	}
	return out;
} /* operator << */


// --------------------------------------------------
// -------------- displaying homology ---------------
// --------------------------------------------------

/// Shows a chain as a list of generators of one level
/// of a homology module.
template <class euclidom>
inline outputstream &show_homology (outputstream &out,
	const chain<euclidom> &c)
{
	int countfree = 0;
	bool writeplus = false;
	for (int i = 0; i < c. size (); ++ i)
	{
		if (c. coef (i). delta () == 1)
			++ countfree;
		else
		{
			out << (writeplus ? " + " : "") <<
				euclidom::ringsymbol () << "_" <<
				c. coef (i);
			writeplus = true;
		}

		if (countfree && ((i == c. size () - 1) ||
			(c. coef (i + 1). delta () != 1)))
		{
			out << (writeplus ? " + " : "") <<
				euclidom::ringsymbol ();
			if (countfree > 1)
				out << "^" << countfree;
			countfree = 0;
			writeplus = true;
		}
	}

	// if there was nothing to show, then just show zero
	if (!c. size ())
		out << "0";

	return out;
} /* show_homology */

/// Shows a chain as a list of generators of one level
/// of a homology module.
template <class euclidom>
inline std::ostream &show_homology (std::ostream &out,
	const chain<euclidom> &c)
{
	outputstream tout (out);
	show_homology (tout, c);
	return out;
} /* show_homology */


} // namespace homology
} // namespace capd

#endif // _CAPD_HOMOLOGY_CHAINS_H_ 

/// @}

