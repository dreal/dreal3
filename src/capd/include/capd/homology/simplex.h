/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file simplex.h
///
/// This file contains the definition of a class which represents a simplex.
/// The definition complies with the requirements of the homology software
/// so that simplices can be used as cells in a geometric complex, and also
/// in algorithms for homology computation.
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started on March 12, 2003. Last revision: May 24, 2010.


#ifndef _CAPD_HOMOLOGY_SIMPLEX_H_ 
#define _CAPD_HOMOLOGY_SIMPLEX_H_ 

#include "capd/homology/config.h"
#include "capd/homology/textfile.h"
#include "capd/homology/integer.h"
#include "capd/homology/gcomplex.h"

#include <iostream>
#include <fstream>
#include <cstdlib>

namespace capd {
namespace homology {


// classes defined within this header file (in this order)
class Simplex;

/// The type of a simplicial complex.
typedef gcomplex<Simplex,integer> SimplicialComplex;

/// The type of a set of simplices.
typedef hashedset<Simplex> SetOfSimplices;

/// A lower-case name for a simplex [deprecated].
typedef Simplex simplex;

/// A lower-case name for a simplicial complex [deprecated].
typedef gcomplex<simplex,integer> simplicialcomplex;

/// An alternative name for a set of simplices [deprecated].
typedef hashedset<simplex> simplices;


// --------------------------------------------------
// -------------------- Simplex ---------------------
// --------------------------------------------------

/// This class defines a simplex as a geometric cell that can be used
/// as a member of a geometric complex.
class Simplex
{
public:
	/// The maximal dimension of a simplex. Note that practically
	/// the maximal dimension in use should not exceed 20 or so.
	static const int MaxDim = 2048;

	/// The default constructor of the empty simplex.
	Simplex ();

	/// The constructor of a simplex from an array of its vertices.
	Simplex (const int *v, int dim);

	/// The constructor of a boundary simplex.
	Simplex (const Simplex &s, int n);

	/// The destructor.
	~Simplex ();

	/// The copy constructor.
	Simplex (const Simplex &s);

	/// The assignment operator.
	Simplex &operator = (const Simplex &s);

	/// Returns the dimension of the simplex.
	/// The empty simplex has the dimension of -1.
	int dim () const;

	/// Retrieves the vertices of the simplex to the given array.
	void vertices (int *table) const;

	/// The first hashing key required by the hashing set template.
	int_t hashkey1 () const;

	/// The second hashing key required by the hashing set template.
	int_t hashkey2 () const;

	/// The singular name of the objects represented by this class.
	static const char *name ();

	/// The plural name of the objects represented by this class.
	static const char *pluralname ();

	// friends
	friend int operator == (const Simplex &s, const Simplex &t);
	friend std::ostream &operator << (std::ostream &out, const Simplex &s);

private:
	/// The array that keeps the vertices of the simplex.
	/// The first entry contains the dimension of the simplex.
	int *tab;

}; /* class Simplex */

// --------------------------------------------------

inline Simplex::Simplex ()
{
	tab = NULL;
	return;
} /* Simplex::Simplex */

inline Simplex::~Simplex ()
{
	if (tab)
		delete [] tab;
	return;
} /* Simplex::~Simplex */

inline const char *simplex::name ()
{
	return "simplex";
} /* simplex::name */

inline const char *simplex::pluralname ()
{
	return "simplices";
} /* simplex::pluralname */

inline int Simplex::dim () const
{
	if (!tab)
		return -1;
	else
		return (*tab);
} /* Simplex::dim */

inline void Simplex::vertices (int *table) const
{
	int d = dim ();
	for (int i = 0; i <= d; ++ i)
		table [i] = tab [i + 1];
	return;
} /* Simplex::dim */

inline Simplex::Simplex (const int *v, int d)
{
	if (d < 0)
		throw "Negative dimension of a simplex.";
	tab = new int [d + 2];
	if (!tab)
		throw "Not enough memory for a simplex.";
	tab [0] = d;
	for (int i = 0; i <= d; ++ i)
		tab [i + 1] = v [i];
	return;
} /* Simplex::Simplex */

inline Simplex::Simplex (const Simplex &s, int n)
{
	int d = s. dim () - 1;
	if (d < 0)
		throw "Undefined boundary simplex.";
	tab = new int [d + 2];
	if (!tab)
		throw "Not enough memory for a boundary simplex.";
	tab [0] = d;
	int i;
	for (i = 1; i <= n; ++ i)
		tab [i] = s. tab [i];
	for (i = n + 1; i < d + 2; ++ i)
		tab [i] = s. tab [i + 1];
	return;
} /* Simplex::Simplex */

inline Simplex::Simplex (const Simplex &s)
{
	int d = s. dim ();
	if (d < 0)
		tab = NULL;
	else
	{
		tab = new int [d + 2];
		if (!tab)
			throw "Not enough memory to copy a simplex.";
		for (int i = 0; i < d + 2; ++ i)
			tab [i] = s. tab [i];
	}
	return;
} /* Simplex::Simplex */

inline Simplex &Simplex::operator = (const Simplex &s)
{
	int d = s. dim ();
	if (d < 0)
	{
		if (tab)
			delete [] tab;
		tab = NULL;
	}
	else if (d == dim ())
	{
		for (int i = 0; i < d + 2; ++ i)
			tab [i] = s. tab [i];
	}
	else
	{
		if (tab)
			delete [] tab;
		tab = new int [d + 2];
		if (!tab)
			throw "Not enough memory to assign a simplex.";
		for (int i = 0; i < d + 2; ++ i)
			tab [i] = s. tab [i];
	}
	return *this;
} /* Simplex::operator = */

inline int_t Simplex::hashkey1 () const
{
	int d = dim ();
	if (d < 0)
		return 0;
	else if (d == 0)
		return static_cast<int_t> (tab [1]) << 2;
	else if (d == 1)
	{
		return ((static_cast<int_t> (tab [1])
			^ 0x55555555u) << 16) ^
			((static_cast<int_t> (tab [2])
			^ 0xAAAA00AAu) << 4);
	}
	else
	{
		return ((static_cast<int_t> (tab [1]) ^
			0x55555555u) << 16) ^
			((static_cast<int_t> (tab [2]) ^
			0xAA00AAAAu) << 4) ^
			((static_cast<int_t> (tab [3]) ^
			0xAA55AA55u) >> 6);
	}
} /* Simplex::hashkey1 */

inline int_t Simplex::hashkey2 () const
{
	int d = dim ();
	if (d < 0)
		return 0;
	else if (d == 0)
		return static_cast<int_t> (tab [1]) << 2;
	else if (d == 1)
	{
		return ((static_cast<int_t> (tab [1]) ^
			0xAAAAAAAAu) >> 1) ^
			((static_cast<int_t> (tab [2]) ^
			0x55555555u) << 13);
	}
	else
	{
		return ((static_cast<int_t> (tab [d + 1]) ^
			0x55555555u) << 13) ^
			((static_cast<int_t> (tab [d]) ^
			0xAA00AA00u) >> 1) ^
			((static_cast<int_t> (tab [d - 1]) ^
			0xAA0055AAu) << 7);
	}
} /* Simplex::hashkey2 */

// --------------------------------------------------

/// The operator == that compares whether the two simplices are the same,
/// that is, have the same vertices in the same order.
inline int operator == (const Simplex &s, const Simplex &t)
{
	int sd = s. dim ();
	int td = t. dim ();
	if (sd != td)
		return 0;
	for (int i = 1; i < sd + 2; ++ i)
		if (s. tab [i] != t. tab [i])
			return 0;
	return 1;
} /* operator == */

/// The operator != verifies if the two simplices are different.
inline int operator != (const Simplex &s, const Simplex &t)
{
	return !(s == t);
} /* operator != */

// --------------------------------------------------

/// Returns the length of the boundary of a simplex.
inline int boundarylength (const Simplex &s)
{
	int d = s. dim ();
	return (d ? (d + 1) : 0);
} /* boundarylength */

/// Returns the i-th coefficient in the boundary of a simplex.
inline int boundarycoef (const Simplex &, int i)
{
	if (i & 1)
		return -1;
	else
		return 1;
} /* boundarycoef */

/// Returns the i-th boundary face of a simplex.
inline Simplex boundarycell (const Simplex &s, int i)
{
	return Simplex (s, i);
} /* boundarycell */

/// Returns the i-th boundary face of a simplex.
inline Simplex boundarycell (const Simplex &s, int i, bool)
{
	return boundarycell (s, i);
} /* boundarycell */

// --------------------------------------------------

/// Writes a simplex to the output stream in the text format.
inline std::ostream &operator << (std::ostream &out, const Simplex &s)
{
	out << '(';
	if (s. tab)
	{
		int d = s. dim ();
		out << s. tab [1];
		for (int i = 2; i < d + 2; ++ i)
			out << ',' << s. tab [i];
	}
	out << ')';
	return out;
} /* operator << */

/// Reads a simplex from an imput stream from a text format.
/// Throws an error message in case of failure.
inline std::istream &operator >> (std::istream &in, Simplex &s)
{
	// check if an opening parenthesis is waiting at the input
	ignorecomments (in);
	int closing = closingparenthesis (in. peek ());
	if (closing == EOF)
		throw "Cannot read a simplex: No opening parenthesis.";

	// read the opening parenthesis
	in. get ();
	ignorecomments (in);

	// read the vertices of the simplex
	int v [Simplex::MaxDim];
	int dim = -1;
	while (in && (in. peek () != closing))
	{
		// read the vertex
		in >> v [++ dim];
		if (!in)
			throw "Unable to read a vertex of a simplex.";

		// read the separating comma if any
		ignorecomments (in);
		if (in. peek () == ',')
		{
			in. get ();
			ignorecomments (in);
		}

		// if there are too many vertices...
		if (dim >= Simplex::MaxDim)
			throw "Too many vertices of a simplex.";
	}

	// sort the numbers of the vertices of the simplex
	if (sortelements (v, dim + 1) != dim + 1)
		throw "A repeated vertex in a simplex detected.";

	// read the closing parenthesis and define the simplex
	in. get ();
	s = Simplex (v, dim);

	return in;
} /* operator >> */


} // namespace homology
} // namespace capd

#endif // _CAPD_HOMOLOGY_SIMPLEX_H_ 

/// @}

