/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file pointbas.h
///
/// This file contains the definition of a point base class which is used
/// for indexing all the points (n-tuples of integer coordinates) which
/// are used in the program. This technique helps saving a lot of memory
/// if the same points are stored many times, because the integer numbers
/// representing the points are used, and the arrays of their coordinates
/// are stored only once, in this data structure.
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started in January 2002. Last revision: January 23, 2010.


#ifndef _CAPD_HOMOLOGY_POINTBAS_H_ 
#define _CAPD_HOMOLOGY_POINTBAS_H_ 

#include "capd/homology/config.h"
#include "capd/homology/textfile.h"
#include "capd/homology/pointset.h"

#include <iostream>
#include <fstream>
#include <cstdlib>


namespace capd {
namespace homology {


// classes defined within this header file (in this order):
template <class coordtype>
class tPointBase;

template <class coordtype>
class tPointBaseInitializer;

/// The default type of the point base class.
typedef tPointBase<coordinate> PointBase;

/// The number of signed bits to store the dimension (i.e., 6: max 31).
/// The maximal allowed dimension in the program is less than what follows
/// from the number of bits (i.e., max 30 for 6 bits).
const int DimBits = (sizeof (int_t) > 4) ? 7 : 6;

/// The number of bits in an integer number that remain to be used for other
/// purposes, because the high 'DimBits' bits are used for the dimension.
const int NumBits = (sizeof (int_t) << 3) - DimBits;

/// The sign bit of the int_t number.
const int_t SignBit = static_cast<int_t> (1) << ((sizeof (int_t) << 3) - 1);

/// The mask of the bits remaining after the dimension bits are excluded.
const int_t NumMask = (~(static_cast<int_t> (0) ^ SignBit)) >> (DimBits - 1);

/// The maximal dimension that can be represented using 'DimBits' bits.
const int MaxBasDim1 = static_cast<int> (1u << (DimBits - 1));

/// The maximal dimension which still leaves enough bits in the integer
/// to have one bit for each direction.
const int MaxBasDim2 = static_cast<int> ((sizeof (int_t) << 3) - DimBits);

/// The maximal dimension that can be used if the high bits of an integer
/// store the value of the dimension, and the number of remaining bits
/// is at least as large as the dimension.
const int MaxBasDim = (MaxBasDim1 < MaxBasDim2) ? MaxBasDim1 : MaxBasDim2;


// --------------------------------------------------
// ------------------- Point Base -------------------
// --------------------------------------------------

/// This class keeps a common set of points which are indexed
/// for the use of other classes, like cubes or cubical cells.
/// This base is used to give each n-dimensional point its unique number.
/// The consecutive numbers for each dimension begin with 1.
template <class coordtype>
class tPointBase
{
public:
	/// Returns the number of the point with given coordinates.
	/// Points for each dimension get numbers starting at 1.
	static int_t number (const coordtype *c, int d);

	/// Checks whether this point is already included in the list.
	/// Return false if not, true if yes.
	/// Does not add the point to the structure.
	static bool check (const coordtype *c, int d);

	/// Retrieves the coordinates of the given point.
	static const coordtype *coord (int_t number, int d);

	/// Determines the default dimension of points.
	static int defaultdimension (void);

	/// Sets the point base to be quiet or not. If not quiet,
	/// it displays some usage statistics when the data is reset.
	static void quiet (bool what = true);
	
	/// Sets space wrapping for all the dimensions in the range
	/// starting with 'mindim' and strictly smaller than 'maxdim'.
	/// The space wrapping in each direction can be different.
	static void setwrapping (const coordtype *c,
		int mindim = 1, int maxdim = MaxBasDim);

	/// Sets space wrapping for all the dimensions in the range
	/// starting with 'mindim' and strictly smaller than 'maxdim'.
	/// The space wrapping in each direction is the same.
	static void setwrapping (coordtype c,
		int mindim = 1, int maxdim = MaxBasDim);

	/// Returns the space wrapping for the given dimension.
	static const coordtype *getwrapping (int d);

	/// Wraps the given coordinates if necessary.
	static void wrapcoord (coordtype *c, int dim);

	/// Copies the coordinates and wraps them if necessary.
	static void wrapcopy (coordtype *dest, const coordtype *src,
		int dim);

	/// Resets the internal data. Note: Cubes and cells created before
	/// resetting may be unusable after the reset.
	static void reset (void);

	/// Forgets the base points, frees memory and makes this data
	/// structure ususable: An exception is thrown if this data is used.
	static void forget (void);

	/// Shows the number of vertices stored for all the dimensions.
	static outputstream &showused (outputstream &out);

	/// Shows the number of vertices stored for all the dimensions.
	static std::ostream &showused (std::ostream &out);

	/// Friendship class which shows the statistics in its destructor.
	friend class tPointBaseInitializer<coordtype>;

protected:
	/// The sets of points from which numbers are taken.
	static tPointset<coordtype> **p;

	/// The number of allocated sets of points.
	static int n;

	/// Should the summary of points' usage be displayed?
	static bool show;

	/// Were the base points forgotten?
	static bool forgotten;

	/// An object responsible for deleting the pointsets at exit.
	static tPointBaseInitializer<coordtype> pointBaseInitializer;

}; /* class tPointBase */

// --------------------------------------------------

template <class coordtype>
inline const coordtype *tPointBase<coordtype>::coord (int_t nr, int d)
{
	if (forgotten)
		throw "Trying to retrieve forgotten coordinates.";
	if ((d > n) || (d <= 0) || (p [d - 1] == NULL))
		return NULL;
	else
		return (*(p [d - 1])) [nr];
} /* tPointBase::coord */

template <class coordtype>
inline bool tPointBase<coordtype>::check (const coordtype *c, int d)
{
	if (forgotten)
		throw "Trying to check forgotten coordinates.";
	if ((d > n) || (d <= 0) || (p [d - 1] == NULL))
		return 0;
	return p [d - 1] -> check (c);
} /* tPointBase::check */

template <class coordtype>
inline void tPointBase<coordtype>::quiet (bool what)
{
	show = !what;
	return;
} /* tPointBase::quiet */

template <class coordtype>
inline int_t tPointBase<coordtype>::number (const coordtype *c, int d)
{
	if (forgotten)
		throw "Trying to find the number of forgotten coordinates.";

	if (d < 0)
		return -1;
	if (d >= MaxBasDim)
		throw "Dimension too high.";

	// enhance the table of sets of points if necessary
	if (d > n)
	{
		tPointset<coordtype> **newtable =
			new tPointset<coordtype> * [d];
		for (int i = 0; i < d; ++ i)
			newtable [i] = (i < n) ? p [i] : NULL;
		if (p)
			delete [] p;
		p = newtable;
		n = d;
	}

	if (!p [d - 1])
	{
		p [d - 1] = new tPointset<coordtype> (1024);
		p [d - 1] -> dimension (d);
	}

	int_t number = p [d - 1] -> add (c);
	if (number > NumMask)
		throw "Too many points.";

	return number;
} /* tPointBase::number */

template <class coordtype>
inline void tPointBase<coordtype>::setwrapping (const coordtype *c,
	int mindim, int maxdim)
{
	if (forgotten)
		throw "Trying to wrap forgotten coordinates.";

	// correct the left and right bound for dimensions
	if (mindim < 1)
		mindim = 1;
	if (maxdim > MaxBasDim)
		maxdim = MaxBasDim;

	// enhance the table of sets of points if necessary
	if (maxdim > n)
	{
		tPointset<coordtype> **newtable =
			new tPointset<coordtype> * [maxdim];
		for (int i = 0; i < maxdim; ++ i)
			newtable [i] = (i < n) ? p [i] : NULL;
		if (p)
			delete [] p;
		p = newtable;
		n = maxdim;
	}

	// set wrapping coordinates and allocate sets of points if needed
	for (int d = mindim; d < maxdim; ++ d)
	{
		if (!p [d - 1])
		{
			p [d - 1] = new tPointset<coordtype>;
			p [d - 1] -> dimension (d);
		}
		p [d - 1] -> wrapspace (c);
	}

	return;
} /* tPointBase::setwrapping */

template <class coordtype>
inline void tPointBase<coordtype>::setwrapping (coordtype c,
	int mindim, int maxdim)
{
	coordtype wraptable [MaxBasDim];
	for (int i = 0; i < MaxBasDim; ++ i)
		wraptable [i] = c;
	setwrapping (wraptable, mindim, maxdim);
	return;
} /* tPointBase::setwrapping */

template <class coordtype>
inline const coordtype *tPointBase<coordtype>::getwrapping (int d)
{
	if (forgotten)
		throw "Trying to get wrapping of forgotten coordinates.";

	if ((d <= 0) || (d - 1 >= n) || !p [d - 1])
		return NULL;
	else
		return p [d - 1] -> wrapspace ();
} /* tPointBase::getwrapping */

template <class coordtype>
inline void tPointBase<coordtype>::wrapcoord (coordtype *c, int dim)
{
	if ((dim > n) || (dim <= 0) || (p [dim - 1] == NULL))
		return;
	const coordtype *cw = p [dim - 1] -> wrapspace ();
	if (cw)
		capd::homology::wrapcoord (c, c, cw, dim);
	return;
} /* tPointBase::wrapcoord */

template <class coordtype>
inline void tPointBase<coordtype>::wrapcopy (coordtype *dest,
	const coordtype *src, int dim)
{
	const coordtype *cw;
	if ((dim > n) || (dim <= 0) || (p [dim - 1] == 0))
		cw = 0;
	else
		cw = p [dim - 1] -> wrapspace ();
	if (cw)
		capd::homology::wrapcoord (dest, src, cw, dim);
	else
		copycoord (dest, src, dim);
	return;
} /* tPointBase::wrapcopy */

template <class coordtype>
inline void tPointBase<coordtype>::reset (void)
{
	for (int i = 0; i < n; ++ i)
	{
		if (p [i])
		{
			delete p [i];
			p [i] = NULL;
		}
	}
	delete [] p;
	p = NULL;
	n = 0;
	forgotten = false;
	return;
} /* tPointBase::reset */

template <class coordtype>
inline void tPointBase<coordtype>::forget (void)
{
	if (forgotten)
		throw "Trying to forget already forgotten coordinates.";

	reset ();
	forgotten = true;
	return;
} /* tPointBase::forget */

// --------------------------------------------------

template <class coordtype>
tPointset<coordtype> **tPointBase<coordtype>::p = NULL;

template <class coordtype>
int tPointBase<coordtype>::n = 0;

template <class coordtype>
bool tPointBase<coordtype>::show = true;

template <class coordtype>
bool tPointBase<coordtype>::forgotten = false;

template <class coordtype>
int tPointBase<coordtype>::defaultdimension (void)
{
	static int dim = 0;
	if (dim)
		return dim;
	for (int d = 1; d <= n; ++ d)
	{
		if (!p [d - 1])
			continue;
		if (p [d - 1] -> empty ())
			continue;
		return d;
	}
	return 0;
} /* tPointBase::defaultdimension */

template <class coordtype>
outputstream &tPointBase<coordtype>::showused (outputstream &out)
{
	if (forgotten)
		throw "Trying to show forgotten coordinates.";

	bool shown = false;
	for (int i = 0; i < n; ++ i)
	{
		if (!p [i])
			continue;
		const tPointset<coordtype> &pset = *(p [i]);
		if (pset. empty ())
			continue;
		out << (shown ? ", " : "Vertices used: ") <<
			pset. size () << " of dim " << (i + 1);
		shown = true;
	}
	if (shown)
		out << ".\n";
	return out;
} /* tPointBase::showused */

template <class coordtype>
std::ostream &tPointBase<coordtype>::showused (std::ostream &out)
{
	outputstream tout (out);
	showused (tout);
	return out;
} /* tPointBase::showused */


// --------------------------------------------------
// ------------- Point Base Initializer -------------
// --------------------------------------------------

/// This class is used to deallocate memory kept in the static variables
/// of the corresponding class "tPointBase" upon program exit, and also
/// to show the information on how many points were in use.
template <class coordtype>
class tPointBaseInitializer
{
public:
	/// Deallocates memory kept in the static variables
	/// of the corresponding class "tPointBase" and shows
	/// relevant messages.
	~tPointBaseInitializer ();

}; /* PointBaseInitializer */

template <class coordtype>
tPointBaseInitializer<coordtype> tPointBase<coordtype>::pointBaseInitializer;

template <class coordtype>
tPointBaseInitializer<coordtype>::~tPointBaseInitializer<coordtype> ()
{
	if (tPointBase<coordtype>::forgotten)
		return;
	if (tPointBase<coordtype>::show && tPointBase<coordtype>::n)
		tPointBase<coordtype>::showused (sout);
	tPointBase<coordtype>::forget ();
	return;
} /* PointBaseInitializer::~PointBaseInitializer */


// --------------------------------------------------
// ------------------- Wrap Base --------------------
// --------------------------------------------------

/// This class is a simplified version of the point base class
/// used only for the space wrapping support.
template <class coordtype>
class tWrapBase: public tPointBase<coordtype>
{
public:
	/// No coord to number translation is available.
	static int_t number (const coordtype *, int)
		{throw "Trying to get a point number.";}

	/// Always says that the point exists.
	static bool check (const coordtype *, int)
		{return true;}

	/// No number to coord translation is available.
	static const coordtype *coord (int_t, int)
		{throw "Trying to get the coordinates of a point.";}

	static void quiet (bool = true) {return;}

	static void reset (void) {return;}

	static void forget (void) {return;}

	static outputstream &showused (outputstream &out) {return out;}

	static std::ostream &showused (std::ostream &out) {return out;}

}; /* class tWrapBase */

// --------------------------------------------------


} // namespace homology
} // namespace capd

#endif // _CAPD_HOMOLOGY_POINTBAS_H_ 

/// @}

