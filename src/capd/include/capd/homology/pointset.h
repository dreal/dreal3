/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file pointset.h
///
/// This file contains the definition of a set of n-dimensional points
/// with integer coordinates and several operations on such a set.
/// The access to individual points is the same as to an array, with the
/// operator []. However, the hashing tables are used for fast searching
/// for specific points.
///
/// The type of coordinates is a template of the
/// classes and functions defined in this file. It must be some integer-like
/// type, e.g., short int or long int.
///
/// Additional data structures and functions related to the sets of points
/// are also defined in this file, including classes for iterating
/// neighborhoods of points and points in a specific rectangular range.
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started in December 1997. Last revision: May 24, 2010.


#ifndef _CAPD_HOMOLOGY_POINTSET_H_ 
#define _CAPD_HOMOLOGY_POINTSET_H_ 

#include "capd/homology/config.h"
#include "capd/homology/textfile.h"

#include <iostream>
#include <fstream>
#include <ctime>
#include <cstdlib>
#include <cctype>

namespace capd {
namespace homology {


/// The default type of coordinates.
typedef short int coordinate;

// a class for gathering hashing statistics in a set of points
class psethashstat;

// a template for a set of points with 'integer' coordinates
template <class coordtype>
class tPointset;

// a template for a class used to list all the neighbors of a given point
template <class coordtype>
class tNeighbors;

// a template for a class used to list all the points in a given scope
template <class coordtype>
class tRectangle;

/// The pointset class with the default type of coordinates.
typedef tPointset<coordinate> pointset;

/// The neighbors class with the default type of coordinates.
typedef tNeighbors<coordinate> neighbors;

/// The rectangle class with the default type of coordinates.
typedef tRectangle<coordinate> rectangle;


// --------------------------------------------------
// ---------------- various functions ---------------
// --------------------------------------------------
// Various small or large functions used by
// or manipulating with the class 'pointset'.

/// Compare two points. Returns true iff they have the same coordinates.
template <class coordtype>
inline int thesame (const coordtype *c1, const coordtype *c2, int dim)
{
	for (int i = 0; i < dim; ++ i)
		if (c1 [i] != c2 [i])
			return 0;
	return 1;
} /* thesame */

/// Copies the coordinates of one point to another.
template <class coordtype>
inline void copycoord (coordtype *destination, const coordtype *source,
	int dim)
{
	for (int i = 0; i < dim; ++ i)
		destination [i] = source [i];
	return;
} /* copycoord */

/// Wraps coordinates stored in 'c' accordint to the wrap table 'wrap'
/// and store the result in the table called 'result'.
template <class coordtype>
inline void wrapcoord (coordtype *destination, const coordtype *source,
	const coordtype *wrap, int dim)
{
	if (!destination || !source)
		throw "Trying to wrap NULL coordinates.";

	for (int i = 0; i < dim; ++ i)
		if (wrap [i])
		{
			destination [i] =
				(coordtype) (source [i] % wrap [i]);
			if (destination [i] < 0)
				destination [i] += wrap [i];
		}
		else
			destination [i] = source [i];

	return;
} /* wrapcoord */

/// Verifies if the given number is a prime number.
/// Returns: true = Yes, false = No.
inline bool numberisprime (unsigned n)
{
	if (n < 2)
		return false;

	unsigned i = 2;
	while (i * i <= n)
		if (!(n % i ++))
			return false;

	return true;
} /* numberisprime */

/// Computes the smallest prime number greater than or equal
/// to the given number. Returns the computed prime number.
inline unsigned ceilprimenumber (unsigned n)
{
	while (!numberisprime (n))
		++ n;

	return n;
} /* prime number */

/// Generates the main hashing key for points.
template <class coordtype>
int_t pointhashkey (const coordtype *c, int dim, int_t hashsize)
{
	int_t key = 13;
	for (int i = 0; i < dim; ++ i)
	{
		key ^= static_cast<int_t> ((c [i] > 0) ? c [i] : -c [i]) <<
			((i << 3) % 19);
	}
	if (key < 0)
		key = -(key + 1);

	// return the key reduced to the given size
	return (key % hashsize);

} /* pointhashkey */

/// Generates the second hashing key for points.
template <class coordtype>
int_t pointhashadd (const coordtype *c, int dim, int_t hashsize)
{
	int_t add = 1313;
	for (int i = 0; i < dim; ++ i)
		add ^= static_cast<int_t> ((c [i] > 0) ? c [i] : -c [i]) <<
			(((i << 4) + 3) % 21);
	if (add < 0)
		add = -(add + 1);

	// return the key reduced to the given size
	return (add % (hashsize - 1) + 1);

} /* pointhashadd */

/// Rounds down the given real number to an integral type.
template <class coordtype>
inline coordtype rounddown (double x)
{
	if ((x >= 0) || ((double) (coordtype) x == x))
		return (coordtype) x;
	else
		return -(coordtype) (-x) - 1;
} /* rounddown */

/// Rounds down the double coordinates of a point to integer ones.
/// If the grid is provided (not NULL), then uses this grid
/// instead of the integral lattice.
template <class coordtype>
inline void roundpoint (const double *p, coordtype *c, const double *grid,
	int dim)
{
	if (grid)
	{
		for (int i = 0; i < dim; ++ i)
			c [i] = rounddown<coordtype> (p [i] / grid [i]);
	}
	else
	{
		for (int i = 0; i < dim; ++ i)
			c [i] = rounddown<coordtype> (p [i]);
	}
	return;
} /* roundpoint */

/// Computes the middle of a cube with its left lower etc. corner
/// represented by the given point with respect to the given grid.
template <class coordtype>
inline void cubemiddle (coordtype *c, double *p, double *grid, int dim)
{
	if (grid)
	{
		for (int i = 0; i < dim; ++ i)
			p [i] = (c [i] + 0.5) * grid [i];
	}
	else
	{
		for (int i = 0; i < dim; ++ i)
			p [i] = c [i] + 0.5;
	}
	return;
} /* cubemiddle */

/// Allocate a point with 'new'. In case of failure throw an error message.
template <class coordtype>
inline coordtype *allocatepoint (int dim, char *errormessage = NULL)
{
	coordtype *temp = new coordtype [dim];
	if (!temp)
	{
		throw (errormessage ? errormessage :
			"Can't allocate memory for a temporary point.");
	}
	return temp;
} /* allocatepoint */

#define INSIDE 1
#define OUTSIDE 0

/// Counts how many neighbors of the point there are in the set,
/// depending on 'which': 1 = in the set, 0 = out of the set.
/// If 'maxcount' > 0 then counts up to this number and quits.
/// Use countneighbors (c, OUTSIDE, 1) to check for a boundary point
/// or countneighbors (c, INSIDE, 1) to check if the point is not isolated.
template <class coordtype>
int countneighbors (const tPointset<coordtype> &p, const coordtype *c,
	int which = INSIDE, int maxcount = 0);

/// Counts neighbors with respect to the union of the sets 'p' and 'q'.
template <class coordtype>
int countneighbors (const tPointset<coordtype> &p,
	const tPointset<coordtype> &q, const coordtype *c,
	int which = INSIDE, int maxcount = 0);

/// Verifies if the point is at the border of a given set.
template <class coordtype>
int attheborder (const tPointset<coordtype> &p, const coordtype *c);

/// Finds a boundary point starting at the given one.
/// Call with n = 0 to find the first boundary point.
/// Direction: 1 - in ascending order, -1 - in descending order.
/// Returns -1 if not found.
template <class coordtype>
int_t findboundarypoint (tPointset<coordtype> &p, int_t n,
	int direction = 1);

/// Finds a point in 'p' at the boundary of the union of 'p' and 'q'.
template <class coordtype>
int_t findboundarypoint (tPointset<coordtype> &p,
	tPointset<coordtype> &q, int_t n, int direction = 1);

/// Creates the set of all the boundary points with the 'new' operator.
template <class coordtype>
tPointset<coordtype> *computeboundary (tPointset<coordtype> &p);

/// Computes the boundary points of the given set and adds them
/// to the other set of points.
template <class coordtype>
void computeboundary (tPointset<coordtype> &p, tPointset<coordtype> &b);

/// Enhances the set by adding the neighborhood of the point with given
/// coordinates.
template <class coordtype>
void enhancepoint (tPointset<coordtype> &p, coordtype *c);

/// Enhances the set by adding the neighborhood of the point with given
/// number.
template <class coordtype>
void enhancepoint (tPointset<coordtype> &p, int_t n);

/// Enhances the set of points by adding to it all the neighbors
/// of all the points in the set.
template <class coordtype>
void enhance (tPointset<coordtype> &p);


/// Reads a point from a text file and removes a pair of parentheses, braces
/// or brackets if present. Returns the number of coordinates read.
/// If the maximal dimension is reached, no more coordinates are read.
/// Note: The first input character should be the opening parenthesis.
/// This is an old version, use "readcoordinates" instead.
template <class coordtype>
int read (textfile &f, coordtype *c, int maxdim);

/// Reads a point from a text file and removes a pair of parentheses, braces
/// or brackets if present. Returns the number of coordinates read.
/// If the maximal dimension is reached, no more coordinates are read.
/// Note: The first input character should be the opening parenthesis.
/// This is an old version, use "readcoordinates" instead.
template <class coordtype>
int read (std::istream &in, coordtype *c, int maxdim);

// write a point to a text file; the coordinates are separated with commas,
// and a pair of parentheses, braces or brackets is added (use 0 for none);
// no end-of-line character is added after the point has been written
template <class coordtype>
int write (std::ostream &out, const coordtype *c, int dim,
	char parenthesis = 40, char closing = 0);

#define CELL 0
#define CUBE 1

/// Reads a cube or a cell from a text file.
/// Ignores any preceding text lines.
/// Returns the dimension of the object read and sets the type accordingly.
/// Returns 0 in the case of the end of a file or a file error.
/// Throws an error message on failure.
template <class coordtype>
int readcubeorcell (std::istream &in, coordtype *left, coordtype *right,
	int maxdim, int *type = NULL);


/// Reads a set of points from an input stream (starting at the point given).
/// Returns the number of points read or -1 (and show a message) if failed.
template <class coordtype>
int_t read (textfile &f, tPointset<coordtype> &p,
	int_t first = 0, int_t howmany = -1,
	coordtype *wrap = NULL, int maxdim = 0, int quiet = 0,
	tPointset<coordtype> *notthese = NULL);

/// Reads a set of points from an input stream (starting at the point given).
/// Returns the number of points read or -1 (and show a message) if failed.
template <class coordtype>
int_t read (std::istream &in, tPointset<coordtype> &p,
	int_t first = 0, int_t howmany = -1,
	coordtype *wrap = NULL, int maxdim = 0, int quiet = 0,
	tPointset<coordtype> *notthese = NULL);

/// Reads a set of points from an input stream (starting at the point given).
/// Returns the number of points read or -1 (and show a message) if failed.
template <class coordtype>
int_t read (textfile &f, tPointset<coordtype> &p,
	coordtype *wrap, int maxdim,
	int quiet = 0, tPointset<coordtype> *notthese = NULL);

/// Reads a set of points from an input stream (starting at the point given).
/// Returns the number of points read or -1 (and show a message) if failed.
template <class coordtype>
int_t read (std::istream &in, tPointset<coordtype> &p,
	coordtype *wrap, int maxdim,
	int quiet = 0, tPointset<coordtype> *notthese = NULL);

/// Reads a set of points from an input stream (starting at the point given).
template <class coordtype>
textfile &operator >> (textfile &f, tPointset<coordtype> &p);

/// Reads a set of points from an input stream (starting at the point given).
template <class coordtype>
std::istream &operator >> (std::istream &in, tPointset<coordtype> &p);

/// Writes a set of points to a file (starting at the point given).
/// Returns the number of points written or -1 (and show a message)
/// in case of failure.
template <class coordtype>
int_t write (std::ostream &out, tPointset<coordtype> &p,
	int_t first = 0, int_t howmany = -1, int quiet = 0);

/// Writes a set of points to a file (starting at the point given).
template <class coordtype>
std::ostream &operator << (std::ostream &out, tPointset<coordtype> &p);


// --------------------------------------------------
// ----------------- pset hash stat -----------------
// --------------------------------------------------

/// This is a small class used only to collect and display statistics
/// on how successful the hashing procedures were.
class psethashstat
{
public:
	/// The constructor.
	psethashstat ();

	/// A variable which stores the creation time of each object.
	std::time_t creationtime;

	/// The number of successful attempts to identify an object
	/// in a hashing table.
	unsigned long hashhits;

	/// The number of unsuccessful attempts to identify an object
	/// in a hashing table.
	unsigned long hashmisses;

	/// The number of times the size of the hashing table was changed
	/// and all the elements had to be put in the table again.
	unsigned long rehashcount;

}; /* class psethashstat */

// --------------------------------------------------

inline psethashstat::psethashstat ()
{
	std::time (&creationtime);
	hashhits = 0;
	hashmisses = 0;
	rehashcount = 0;
	return;
} /* psethashstat::psethashstat */

// --------------------------------------------------

/// Writes the information gathered in a hashing statistics collector
/// object to an output stream.
inline std::ostream &operator << (std::ostream &out, const psethashstat &s)
{
	if (!s. hashhits)
		return out;
	out << "hashing: " << s. hashhits << " hits, avg " <<
		((s. hashhits + s. hashmisses) / s. hashhits) << "." <<
		((s. hashhits + s. hashmisses) * 10 / s. hashhits) % 10 <<
		" attempts (" << s. rehashcount << " times rehashed)";
	return out;
} /* operator << */


// --------------------------------------------------
// -------------------- POINTSET --------------------
// --------------------------------------------------

/// This class represents a set of points in R^n with integer coordinates.
template <class coordtype>
class tPointset
{
public:

	// CONSTRUCTORS AND DESTRUCTORS OF THE SET OF POINTS

	/// Default constructor for a set of points
	/// with the initial size of the set defined here
	/// if an upper bound for the size of the set is known
	/// and thus it is smart to allocate less memory.
	/// If dimension, grid size and space wrapping was defined
	/// for any pointset, these values are automatically copied
	/// to all the pointsets created further (until changed).
	tPointset (int_t initialsize = 0, int bequiet = 1);

	/// The copy constructor.
	tPointset (const tPointset<coordtype> &p);

	/// The assignment operator.
	tPointset &operator = (const tPointset<coordtype> &p);

	/// The destructor.
	~tPointset ();


	// METHODS FOR SETTING BASIC PROPERTIES OF THE SET OF POINTS

	/// Sets the dimension of points.
	int dimension (int d);

	/// Returns the dimension of points.
	int dimension () const;

	/// Sets or gets the default dimension of points.
	static int defaultdimension (int d = 0);

	/// Gets or sets the size of the grid in R^n.
	double *gridsize (double *g = 0);

	/// Sets the grid size (if the same in all the directions).
	double *gridsize (double g);

	/// Sets the grid size in one particular direction.
	double *gridsize (int direction, double g);

	// get or set space wrapping;
	// use '0' for no space wrapping in a particular direction
	const coordtype *wrapspace (const coordtype *w = NULL);
	// set space wrapping (if the same in all the directions)
	const coordtype *wrapspace (coordtype w);
	// set space wrapping in one particular direction
	const coordtype *wrapspace (int direction, coordtype w);


	// METHODS FOR ADDING, FINDING, CHECKING AND REMOVING POINTS

	// Note: Real coordinates are rounded down with 'floor'.
	// Integer coordinates are internally wrapped if needed.

	// check if a point is in the set; return: 1 = Yes, 0 = No
	int check (int_t n) const;
	int check (const coordtype *c) const;
	int check (const double *c) const;

	// find a point in the set;
	// return its number or -1 if not found
	int_t getnumber (const coordtype *c) const;
	int_t getnumber (const double *c) const;

	// get a pointer to the coordinates (stored in internal
	// tables) of the point which has the number or the
	// coordinates given; if the last case, fill in the coords
	coordtype *operator [] (int_t n) const;
	coordtype *getpoint (int_t n) const;
	coordtype *getpoint (coordtype *c) const;
	coordtype *getpoint (double *c) const;
	coordtype *getpoint (int_t n, double *c) const;

	// add a point (if not in the set, yet); return its number
	int_t add (const coordtype *c);
	int_t add (double *c);
	// add an entire set
	tPointset &add (const tPointset<coordtype> &p);

	// remove the point with the given number or coordinates;
	// return 0 if removed or -1 if does not belong to the set;
	// warning: the order of the points in the set changes if
	// a point other than the last one in the set is removed
	int remove (int_t n);
	int remove (const coordtype *c);
	int remove (const double *c);
	// remove an entire set
	int remove (const tPointset<coordtype> &p);


	// OTHER

	/// Returns the number of points in the set.
	int_t size () const;

	/// Returns true if and only if the set of points is empty.
	bool empty () const;

	/// Returns the number of points by simply projecting the set onto an
	/// integer number.
	/// WARNING: This function is DEPRECATED! Use the functions "size"
	/// and "empty" instead.
//	operator int () const;

	// run quietly (or show many unnecessary messages otherwise)
	int quiet;

	// get the size of the hashing table (you may need this
	// if you are curious about memory usage or so)
	int_t gethashsize () const;


	// OPTIONAL STATISTICS (entirely public for easy access)

	// hash statistics
	psethashstat *stat;

	// point scope statistics
	coordtype *minimal, *maximal;

	// were there any points removed from the set?
	// note: this variable is used only for generate an output
	// warning and to modify statistics notice, that's why
	// it may be public for instant access
	int wereremoved;


protected:

	// INTERNAL DATA OF THE SET OF POINTS

	// dimension of the points; '0' if not set yet
	int dim;

	// the number of points in the set
	int_t npoints;

	// the number of tables containing points' coordinates
	int_t ntables;

	// the number of points stored in a single table
	int tablepoints;

	// the table of tables for points' coordinates;
	// note: some tables may not be allocated (these are NULLs)
	coordtype **tables;

	// the size of the grid in R^n (a pointer to a table)
	double *grid;
	
	// space wrapping
	coordtype *wrap;

	// a point for temporary usage while adding or checking:
	// its coordinates are wrapped if needed
	coordtype *temp;

	// the default parameters used for new pointsets
	static int defaultdim;
	static double *defaultgrid;
	static coordtype *defaultwrap;

	// protected functions for initialization and deallocation
	void initialize (int_t initialsize, int bequiet);
	void deallocate ();


	// HASHING

	// the size of the hashing table
	int_t hashsize;

	// the number of cleared entries in the hashing table
	int_t hashcleared;

	// hashing table (if any): -1 = free entry, -2 = cleared
	int_t *hashtable;

	// the expected number of points in the set (0 if unknown)
	unsigned initsize;

	// find an entry corresponding to the point in the hashing
	// table; may fill in a position at which a new point should
	// be added; 'wrapped' says if the coordinates have already
	// been wrapped
	int_t hashfindpoint (const coordtype *c,
		int_t *addposition = NULL, int wrapped = 0) const;

	// replace the old hashing table with a new one;
	// a desired size may be given, otherwise an optimal size
	// is determined and the new table is made bigger or smaller
	void rehash (int_t newsize = 0);

}; /* class tPointset */

// --------------------------------------------------

template <class coordtype>
int tPointset<coordtype>::defaultdim = 0;

template <class coordtype>
double *tPointset<coordtype>::defaultgrid = NULL;

template <class coordtype>
coordtype *tPointset<coordtype>::defaultwrap = NULL;

// --------------------------------------------------

template <class coordtype>
inline int tPointset<coordtype>::defaultdimension (int d)
{
	// set the default dimension if needed
	if (d > 0)
	{
		// remove the two tables if the new dimension is higher
		if (d > defaultdim)
		{
			if (defaultgrid)
				delete [] defaultgrid;
			defaultgrid = NULL;
			if (defaultwrap)
				delete [] defaultwrap;
			defaultwrap = NULL;
		}

		// store the default dimension in the global variable
		defaultdim = d;
	}

	// return the default dimension of points
	return defaultdim;
} /* tPointset::defaultdimension */

template <class coordtype>
inline double *tPointset<coordtype>::gridsize (int direction, double g)
{
	// if this is a question or wrong parameters are given,
	// return the grid
	if ((direction < 0) || (direction >= dim) || !dim || (g <= 0))
		return grid;

	// allocate memory for a new grid table if needed
	if (!grid)
	{
		grid = new double [dim];
		if (!grid)
			throw "Can't allocate memory for the grid.";
		for (int i = 0; i < dim; ++ i)
			grid [i] = 1.0;
	}

	// update the dimension if it was different
	if (dim != defaultdim)
		defaultdimension (dim);

	// create a new default grid table if needed
	if (!defaultgrid)
	{
		defaultgrid = new double [dim];
		if (!defaultgrid)
			throw "Can't alloc mem for the default grid.";
		for (int i = 0; i < dim; ++ i)
			defaultgrid [i] = grid [i];
	}

	// set the grid and the default grid coordinates
	grid [direction] = g;
	defaultgrid [direction] = g;

	// return the new grid
	return grid;
} /* point::gridsize */

template <class coordtype>
inline double *tPointset<coordtype>::gridsize (double g)
{
	// set all the directions of the grid
	for (int i = 0; i < dim; ++ i)
		gridsize (i, g);

	// return the new grid
	return grid;
} /* point::gridsize */

template <class coordtype>
inline double *tPointset<coordtype>::gridsize (double *g)
{
	// if this is only a question, return the current grid
	if (!g)
		return grid;

	// set all the directions of the grid
	for (int i = 0; i < dim; ++ i)
		gridsize (i, g [i]);

	// return the new grid
	return grid;
} /* point::gridsize */

template <class coordtype>
inline const coordtype *tPointset<coordtype>::wrapspace
	(int direction, coordtype w)
{
	// if this is a question or wrong parameters are given,
	// return the wrap table
	if ((direction < 0) || (direction >= dim) || !dim || (w < 0))
		return wrap;

	// allocate memory for a new wrap table if needed
	if (!wrap)
	{
		wrap = new coordtype [dim];
		if (!wrap)
			throw "Can't alloc mem for the wrap table.";
		for (int i = 0; i < dim; ++ i)
			wrap [i] = 0;
	}

	// update the dimension if it was different
	if (dim != defaultdim)
		defaultdimension (dim);

	// create a new default wrap table if needed
	if (!defaultwrap)
	{
		defaultwrap = new coordtype [dim];
		if (!defaultwrap)
			throw "Can't alloc mem for the def. WrapTab.";
		for (int i = 0; i < dim; ++ i)
			defaultwrap [i] = wrap [i];
	}

	// set the wrap and the default wrap coordinates
	wrap [direction] = w;
	defaultwrap [direction] = w;

	// return the new wrap table
	return wrap;
} /* point::wrapspace */

template <class coordtype>
inline const coordtype *tPointset<coordtype>::wrapspace (coordtype w)
{
	// set all the directions of the wrap table
	for (int i = 0; i < dim; ++ i)
		wrapspace (i, w);

	// return the new wrap table
	return wrap;
} /* point::wrapspace */

template <class coordtype>
inline const coordtype *tPointset<coordtype>::wrapspace (const coordtype *w)
{
	// if this is only a question, return the current wrap
	if (!w)
		return wrap;

	// set all the directions of the wrap table
	for (int i = 0; i < dim; ++ i)
		wrapspace (i, w [i]);

	// return the new wrap table
	return wrap;
} /* point::wrapspace */

template <class coordtype>
inline int tPointset<coordtype>::dimension (int d)
{
	// set the default dimension if needed
	if (d > 0)
		defaultdimension (d);

	// change the dimension if the set is empty and not a subset
	if (!npoints && (d > 0))
	{
		// remove allocated tables if the new dimension is higher
		if (d > dim)
		{
			if (grid)
				delete [] grid;
			grid = NULL;
			gridsize (defaultgrid);
			if (wrap)
				delete [] wrap;
			wrap = NULL;
			wrapspace (defaultwrap);
			if (temp)
				delete [] temp;
			temp = NULL;
		}

		// store the dimension in the structure
		dim = d;
	}

	// return the dimension of points
	return dim;
} /* tPointset::dimension */

template <class coordtype>
inline int tPointset<coordtype>::dimension () const
{
	return dim;
} /* tPointset::dimension */

template <class coordtype>
inline int_t tPointset<coordtype>::size () const
{
	return npoints;
} /* tPointset::size */

template <class coordtype>
inline bool tPointset<coordtype>::empty () const
{
	return !npoints;
} /* tPointset::empty */

//template <class coordtype>
//inline tPointset<coordtype>::operator int () const
//{
//	return npoints;
//} /* tPointset::operator int */

template <class coordtype>
inline coordtype *tPointset<coordtype>::operator [] (int_t n) const
{
	if ((n < 0) || (n >= npoints))
		return NULL;

	return (tables [n / tablepoints] + (n % tablepoints) * dim);
} /* tPointset::operator [] */

template <class coordtype>
inline int_t tPointset<coordtype>::hashfindpoint (const coordtype *c,
	int_t *addpos, int wrapped) const
{
	// if there are no points or there is no hashing table, return NULL
	if (!hashsize)
		return -1;

	// wrap coordinates if needed
	if (!wrapped && wrap)
	{
		if (!temp)
			throw "Unable to wrap point's coordinates.";
		wrapcoord (temp, c, wrap, dim);
		c = temp;
	}

	// prepare hashing keys
	int_t pos = pointhashkey (c, dim, hashsize);
	int_t add = 0;

	// start updating hashing statistics
	++ (stat -> hashhits);

	// find the position of the point in the hashing table
	int_t number;
	while ((number = hashtable [pos]) != -1)
	{
		if ((number >= 0) && thesame ((*this) [number], c, dim))
			return (pos);
		if (addpos && (*addpos < 0) && (number == -2))
			*addpos = pos;
		if (!add)
			add = pointhashadd (c, dim, hashsize);
		pos = (pos + add) % hashsize;
		++ (stat -> hashmisses);
	}

	// return the position in the hashing table
	return (pos);
} /* hashfindpoint */

template <class coordtype>
inline void tPointset<coordtype>::rehash (int_t newsize)
{
	// adjust the size of the hashing table if needed
	if (newsize)
		newsize = ceilprimenumber (newsize);
	else if (!npoints && initsize && !hashsize)
		newsize = ceilprimenumber (initsize);

	// if the new size is too small, make it bigger
	if (newsize <= npoints + npoints / 5)
	{
		// compute an optimal new size for adding points
		newsize = ceilprimenumber ((npoints << 1) + 131);

		// check if it is not too large for 16-bit programs
		int x = 0xFFFF;
		if ((x < 0) && (newsize >= 16384))
			throw "Pointset too large for a 16-bit prog.";
	}

	// show a message if needed
	if (hashsize && !quiet)
		sout << "(Changing the hashing table from " << hashsize <<
			" to " << newsize << " at " << npoints << " points) ";
	else if (!quiet)
		sout << "(Using a hashing table for " << newsize << " ";

	// remove the old hashing table and allocate a new one
	hashsize = newsize;
	if (hashtable)
		delete [] hashtable;
	hashtable = new int_t [hashsize];
	if (!hashtable)
		throw "Can't allocate memory for a hashing table.";
	for (int_t i = 0; i < hashsize; ++ i)
		hashtable [i] = -1;
	hashcleared = 0;

	// build a new hashing table
	for (int_t j = 0; j < npoints; ++ j)
	{
		int_t n = hashfindpoint ((*this) [j], NULL, 1);
		if (hashtable [n] != -1)
			throw "A repeated point found in the hashing table.";
		hashtable [n] = j;
	}

	++ (stat -> rehashcount);

	if (!quiet)
		sout << "points.)\n";

	return;
} /* tPointset::rehash */

template <class coordtype>
inline int_t tPointset<coordtype>::add (const coordtype *c)
{
	// prevent from adding a 'NULL' point
	if (!c)
		return -1;

	// check if the dimension of the point is known
	if (!dim)
		throw "Trying to add a point of unknown dimension.";

	// wrap the point's coordinates if needed
	if (wrap)
	{
		if (!temp)
			temp = allocatepoint<coordtype> (dim);
		wrapcoord (temp, c, wrap, dim);
		c = temp;
	}

	// increase the size of the hashing table if needed
	if (hashsize - hashcleared <= npoints + npoints / 5)
		rehash ();

	// find a place for the new point
	int_t addpos = -1;
	int_t pos = hashfindpoint (c, &addpos, 1);

	// if the point is already in the set, return its number
	if (hashtable [pos] >= 0)
		return hashtable [pos];

	// update the range of coordinates for statistical purposes
	if (minimal)
	{
		for (int i = 0; i < dim; ++ i)
			if (minimal [i] > c [i])
				minimal [i] = c [i];
	}
	else
	{
		minimal = allocatepoint<coordtype> (dim);
		copycoord (minimal, c, dim);
	}

	if (maximal)
	{
		for (int i = 0; i < dim; ++ i)
			if (maximal [i] < c [i])
				maximal [i] = c [i];
	}
	else
	{
		maximal = allocatepoint<coordtype> (dim);
		copycoord (maximal, c, dim);
	}

	// write the point's number into the hashing table
	if (addpos >= 0)
	{
		pos = addpos;
		if (hashtable [pos] == -2)
			-- hashcleared;
	}
	hashtable [pos] = npoints;

	// compute the number of the table in which the point's coordinates
	// should be stored
	int_t tablenumber = npoints / tablepoints;

	// if there are not enough tables, add some
	if (tablenumber >= ntables)
	{
		int_t moretables = (ntables << 1) + 13;
		coordtype **newtables = new coordtype * [moretables];
		if (!newtables)
			throw "Unable to alloc a table for tables.";
		for (int_t i = 0; i < moretables; ++ i)
			newtables [i] = (i < ntables) ? (tables [i]) :
				(coordtype *) NULL;
		if (tables)
			delete [] tables;
		tables = newtables;
		ntables = moretables;
	}

	// if the appropriate table has not been allocate yet, allocate it
	if (tables [tablenumber] == NULL)
	{
		tables [tablenumber] = new coordtype [tablepoints * dim];
		if (!tables [tablenumber])
			throw "Unable to alloc a table for coords.";
	}

	// copy the point's coordinates into the table
	copycoord (tables [tablenumber] +
		((npoints % tablepoints) * dim), c, dim);

	// return the point's number and increase the number of points
	// in the set
	return (npoints ++);
} /* tPointset::add */

template <class coordtype>
inline int_t tPointset<coordtype>::add (double *c)
{
	// prevent from adding a 'NULL' point
	if (!c)
		return -1;

	if (!dim)
		throw "Trying to add a point of unknown dimension.";
	if (!temp)
		temp = allocatepoint<coordtype> (dim);
	roundpoint (c, temp, grid, dim);
	return add (temp);
} /* tPointset::add */

template <class coordtype>
inline tPointset<coordtype> &tPointset<coordtype>::add
	(const tPointset<coordtype> &p)
{
	int_t size = p. size ();
	for (int_t i = 0; i < size; ++ i)
		this -> add (p [i]);
	return *this;
} /* tPointset::add */

template <class coordtype>
inline void tPointset<coordtype>::initialize (int_t initialsize, int bequiet)
{
	// set the 'quiet' variable
	quiet = bequiet;

	// correct the initial size if wrong
	if (initialsize < 0)
		initialsize = 0;

	// initialize the point tables
	npoints = 0;
	ntables = 0;
	if (initialsize <= 0)
		tablepoints = 3000;
	else if (initialsize > 10000)
		tablepoints = 10000;
	else
		tablepoints = static_cast<int> (initialsize);
	tables = NULL;

	// initialize default parameters
	dim = 0;
	grid = NULL;
	wrap = NULL;
	temp = NULL;
	wereremoved = 0;
	dimension (defaultdimension ());
	gridsize (defaultgrid);
	wrapspace (defaultwrap);

	// initialize hashing
	hashsize = 0;
	hashcleared = 0;
	hashtable = NULL;
	if (initialsize)
		initsize = initialsize + initialsize / 5 + 3;
	else
		initsize = 0;

	// optional statistic data
	stat = new psethashstat;
	minimal = NULL;
	maximal = NULL;

	return;
} /* tPointset::initialize */

template <class coordtype>
inline tPointset<coordtype>::tPointset (int_t initialsize, int bequiet)
{
	initialize (initialsize, bequiet);
	return;
} /* tPointset::tPointset */

template <class coordtype>
inline tPointset<coordtype>::tPointset (const tPointset<coordtype> &p)
{
	initialize (p. size (), p. quiet);
	add (p);
	return;
} /* tPointset::tPointset */

template <class coordtype>
inline void tPointset<coordtype>::deallocate ()
{
	// free the point tables
	for (int_t i = 0; i < ntables; ++ i)
	{
		if (tables [i])
			delete [] (tables [i]);
	}
	if (tables)
		delete [] tables;

	// remove the grid and wrap tables
	if (grid)
		delete [] grid;
	if (wrap)
		delete [] wrap;

	// remove the temporary point table
	if (temp)
		delete [] temp;

	// remove the minimal and maximal coordinates
	if (minimal)
		delete [] minimal;
	if (maximal)
		delete [] maximal;

	// turn off hashing
	if (hashtable)
		delete [] hashtable;

	if (stat)
		delete stat;

	return;
} /* tPointset::deallocate */

template <class coordtype>
inline tPointset<coordtype> &tPointset<coordtype>::operator =
	(const tPointset<coordtype> &p)
{
	deallocate ();
	initialize (p. size (), p. quiet);
	add (p);
	return *this;
} /* tPointset::operator = */

template <class coordtype>
inline tPointset<coordtype>::~tPointset<coordtype> ()
{
	deallocate ();
	return;
} /* tPointset::~tPointset */

template <class coordtype>
inline int_t tPointset<coordtype>::getnumber (const coordtype *c) const
{
	// prevent from looking for a 'NULL' point
	if (!c)
		return -1;

	// find the position corresponding to this point in the hashing table
	int_t pos = hashfindpoint (c);

	// return the point's number found in the table
	return ((pos >= 0) ? hashtable [pos] : static_cast<int_t> (-1));
} /* tPointset::getnumber */

template <class coordtype>
inline int_t tPointset<coordtype>::getnumber (const double *c) const
{
	if (!npoints)
		return -1;
	if (!temp)
		throw "Cannot round point's coordinates.";
	roundpoint (c, temp, grid, dim);
	int_t pos = hashfindpoint (temp);
	return ((pos >= 0) ? hashtable [pos] : static_cast<int_t> (-1));
} /* tPointset::getnumber */

template <class coordtype>
inline int tPointset<coordtype>::check (int_t n) const
{
	return ((n >= 0) && (n < npoints));
} /* tPointset::check */

template <class coordtype>
inline int tPointset<coordtype>::check (const coordtype *c) const
{
	return (getnumber (c) != -1);
} /* tPointset::check */

template <class coordtype>
inline int tPointset<coordtype>::check (const double *c) const
{
	return (getnumber (c) != -1);
} /* tPointset::check */

template <class coordtype>
inline coordtype *tPointset<coordtype>::getpoint (int_t n) const
{
	return (*this) [n];
} /* tPointset::getpoint */

template <class coordtype>
inline coordtype *tPointset<coordtype>::getpoint (coordtype *c) const
{
	return (*this) [getnumber (c)];
} /* tPointset::getpoint */

template <class coordtype>
inline coordtype *tPointset<coordtype>::getpoint (double *c) const
{
	return (*this) [getnumber (c)];
} /* tPointset::getpoint */

template <class coordtype>
inline coordtype *tPointset<coordtype>::getpoint (int_t n, double *c) const
{
	coordtype *coord = (*this) [n];
	if (coord && c)
	{
		for (int i = 0; i < dim; ++ i)
			c [i] = (grid ? grid [i] : 1.0) * (0.5 + coord [i]);
	}

	return coord;
} /* tPointset::getpoint */

template <class coordtype>
inline int tPointset<coordtype>::remove (int_t n)
{
	if ((n < 0) || (n >= npoints))
		return -1;
	wereremoved = 1;

	// find the point's place in the hashing table
	coordtype *coord = (*this) [n];
	int_t pos = hashfindpoint (coord);

	// fill in this entry in the hashing table with -2 (cleared)
	hashtable [pos] = -2;

	// copy the last point in the set to replace the point being removed
	if (n != npoints - 1)
	{
		coordtype *lastcoord = (*this) [npoints - 1];
		int_t lastpos = hashfindpoint (lastcoord);
		hashtable [lastpos] = n;
		copycoord (coord, lastcoord, dim);
	}

	// free an unused table with points' coordinates if it is sensible
	int_t tablenumber = npoints / tablepoints;
	if ((tablenumber + 2 < ntables) && tables [tablenumber + 2])
	{
		delete [] (tables [tablenumber + 2]);
		tables [tablenumber + 2] = NULL;
	}

	// decrease the number of points in the set
	-- npoints;

	// update the number of cleared entries in the hashing table
	++ hashcleared;

	// rehash if recommended
	if (hashcleared > npoints + 13)
		rehash (13);

	return (0);
} /* tPointset::remove */

template <class coordtype>
inline int tPointset<coordtype>::remove (const coordtype *c)
{
	return remove (getnumber (c));
} /* tPointset::remove */

template <class coordtype>
inline int tPointset<coordtype>::remove (const double *c)
{
	return remove (getnumber (c));
} /* tPointset::remove */

template <class coordtype>
inline int tPointset<coordtype>::remove (const tPointset<coordtype> &p)
{
	int_t size = p. size ();
	for (int_t i = 0; i < size; ++ i)
		remove (p [i]);
	return 0;
} /* tPointset::remove */

template <class coordtype>
inline int_t tPointset<coordtype>::gethashsize () const
{
	return hashsize;
} /* tPointset::gethashsize */


// --------------------------------------------------
// ------------------- NEIGHBORS --------------------
// --------------------------------------------------

/// This class can be used for iterating point's neighbors.
/// The source point must exist all the time you
/// use this structure for this point.
template <class coordtype>
class tNeighbors
{
public:
	/// The only possible constructor for new objects.
	tNeighbors (const coordtype *_source = NULL, int _dim = 0,
		const coordtype *_wrap = NULL);

	/// The copy constructor.
	tNeighbors (const tNeighbors<coordtype> &r);

	/// The assignment operator.
	tNeighbors &operator = (const tNeighbors<coordtype> &r);

	/// The destructor.
	~tNeighbors ();

	/// Returns the next neighbor. If no more neighbors are available
	/// then returns 0 and rewinds to the first neighbor.
	coordtype *get ();

	/// Resets the neighbors to the first one.
	void reset ();

	/// Redefines the source (and doesn't change other variables).
	void set (coordtype *_source);

private:
	/// The dimension of the space.
	int dim;

	/// A pointer to the source point (not allocated!).
	const coordtype *source;

	/// The coordinates of a created neighbor.
	coordtype *neighbor;

	/// The current counters.
	signed char *counters;

	/// The space wrapping (if needed).
	const coordtype *wrap;

	/// Initializes the internal data of an object of this class.
	void initialize (const coordtype *_source = NULL,
		int _dim = 0, const coordtype *_wrap = NULL);

	/// Deallocates any memory previously allocated for this object.
	void deallocate ();

}; /* class tNeighbors */

// --------------------------------------------------

template <class coordtype>
void tNeighbors<coordtype>::initialize (const coordtype *_source, int _dim,
	const coordtype *_wrap)
{
	source = _source;
	wrap = _wrap;
	dim = _dim;
	if (dim <= 0)
	{
		dim = 0;
		neighbor = NULL;
		counters = NULL;
		return;
	}
	neighbor = new coordtype [dim];
	counters = new signed char [dim];
	if (!neighbor || !counters)
		throw "Can't allocate memory for neighbors.";
	reset ();
	return;
} /* tNeighbors::initialize */

template <class coordtype>
tNeighbors<coordtype>::tNeighbors (const coordtype *_source, int _dim,
	const coordtype *_wrap)
{
	initialize (_source, _dim, _wrap);
	return;
} /* tNeighbors::tNeighbors */

template <class coordtype>
tNeighbors<coordtype>::tNeighbors (const tNeighbors<coordtype> &n)
{
	initialize (n. source, n. dim, n. wrap);
	return;
} /* tNeighbors::tNeighbors */

template <class coordtype>
tNeighbors<coordtype> &tNeighbors<coordtype>::operator =
	(const tNeighbors<coordtype> &n)
{
	deallocate ();
	initialize (n. source, n. dim, n. wrap);
	return *this;
} /* tNeighbors::operator = */

template <class coordtype>
void tNeighbors<coordtype>::deallocate ()
{
	if (neighbor)
		delete [] neighbor;
	if (counters)
		delete [] counters;
	return;
} /* tNeighbors::deallocate */

template <class coordtype>
tNeighbors<coordtype>::~tNeighbors<coordtype> ()
{
	deallocate ();
	return;
} /* tNeighbors::~tNeighbors */

template <class coordtype>
void tNeighbors<coordtype>::reset ()
{
	if (counters)
	{
		for (int i = 0; i < dim; ++ i)
			counters [i] = 0;
	}
	return;
} /* tNeighbors::reset */

template <class coordtype>
void tNeighbors<coordtype>::set (coordtype *_source)
{
	source = _source;
	return;
} /* tNeighbors::set */

template <class coordtype>
coordtype *tNeighbors<coordtype>::get ()
{
	// if the initialization was incorrect, return NULL
	if (!dim || !counters || !neighbor || !source)
		return NULL;

	// compute the next set of counters
	// and return NULL if this is the end
	int cur = 0;
	while ((cur < dim) && (counters [cur] == -1))
		counters [cur ++] = 0;
	if (cur >= dim)
		return NULL;
	counters [cur] = counters [cur] ?
		(signed char) -1 : (signed char) 1;

	// compute the neighbor corresponding to these counters
	for (int i = 0; i < dim; ++ i)
		neighbor [i] = (coordtype) (source [i] + counters [i]);

	// wrap the neighbor's coordinates if required
	if (wrap)
		wrapcoord (neighbor, neighbor, wrap, dim);

	// return the neighbor's coordinates
	return neighbor;

} /* tNeighbors::get */


// --------------------------------------------------
// ------------------- RECTANGLE --------------------
// --------------------------------------------------

/// This class can be used for iterating a rectangular set
/// of points, given its left and right bound.
/// The source points must exist all the time you
/// use this structure for these points, because they are not copied,
/// only the addresses of their coordinate tables are stored.
/// Example: "rectangle ([0,0], [2,2], 2)" represents a set
/// of four points: [0,0], [0,1], [1,0] and [1,1].
template <class coordtype>
class tRectangle
{
public:
	/// The only possible constructor for new objects.
	tRectangle (const coordtype *_left = NULL,
		const coordtype *_right = NULL, int _dim = 0);

	/// The copy constructor.
	tRectangle (const tRectangle<coordtype> &r);

	/// The assignment operator.
	tRectangle &operator = (const tRectangle<coordtype> &r);

	/// The destructor.
	~tRectangle ();

	/// Returns the next point in the recatngle. If no more points
	/// are available then returns 0 and rewinds to the first point.
	const coordtype *get ();

	/// Resets the current point to the first one in the range.
	void reset ();

private:
	/// The dimension of the space.
	int dim;

	/// A pointer to the left point (not allocated!).
	const coordtype *left;

	/// A pointer to the right point (not allocated!).
	const coordtype *right;

	/// The coordinates of a created point.
	coordtype *point;

	/// Should the 0 pointer be returned after the last point?
	int firstpoint;

	/// Initializes the internal data of an object of this class.
	void initialize (const coordtype *_left = NULL,
		const coordtype *_right = NULL, int _dim = 0);

	/// Deallocates any memory previously allocated for this object.
	void deallocate ();

}; /* class tRectangle */

// --------------------------------------------------

template <class coordtype>
void tRectangle<coordtype>::initialize (const coordtype *_left,
	const coordtype *_right, int _dim)
{
	firstpoint = 0;
	left = _left;
	right = _right;
	dim = _dim;
	if (dim <= 0)
	{
		dim = 0;
		point = NULL;
		return;
	}
	point = new coordtype [dim];
	if (!point)
		throw "Can't allocate memory for a rectangle.";
	reset ();

	return;
} /* tRectangle::initialize */

template <class coordtype>
tRectangle<coordtype>::tRectangle (const coordtype *_left, const coordtype *_right,
	int _dim)
{
	initialize (_left, _right, _dim);
	return;
} /* tRectangle::tRectangle */

template <class coordtype>
tRectangle<coordtype>::tRectangle (const tRectangle<coordtype> &r)
{
	initialize (r. left, r. right, r. dim);
	return;
} /* tRectangle::tRectangle */

template <class coordtype>
tRectangle<coordtype> &tRectangle<coordtype>::operator = (const tRectangle<coordtype> &r)
{
	deallocate ();
	initialize (r. left, r. right, r. dim);
	return *this;
} /* tRectangle::operator = */

template <class coordtype>
void tRectangle<coordtype>::deallocate ()
{
	if (point)
		delete [] point;
	return;
} /* tRectangle::deallocate */

template <class coordtype>
tRectangle<coordtype>::~tRectangle<coordtype> ()
{
	deallocate ();
	return;
} /* tRectangle::~tRectangle */

template <class coordtype>
void tRectangle<coordtype>::reset ()
{
	for (int i = 0; i < dim; ++ i)
		point [i] = left [i];
	firstpoint = 1;
	return;
} /* tRectangle::reset */

template <class coordtype>
const coordtype *tRectangle<coordtype>::get ()
{
	// if this is the first point, check if the rectangle is nonempty
	if (firstpoint)
	{
		firstpoint = 0;
		for (int i = 0; i < dim; ++ i)
			if (left [i] >= right [i])
				return NULL;
		return point;
	}

	// compute the next point of the rectangle
	int cur = 0;
	while ((cur < dim) && (++ (point [cur]) >= right [cur]))
	{
		point [cur] = left [cur];
		++ cur;
	}

	// if the iterator has run out of points, return NULL
	if (cur >= dim)
	{
		firstpoint = 1;
		return NULL;
	}

	// return the point's coordinates
	return point;

} /* tRectangle::get */


// --------------------------------------------------
// ---------------- various functions ---------------
// --------------------------------------------------

/// Returns the number of neighbors of the given point in a given set.
template <class coordtype>
int countneighbors (const tPointset<coordtype> &p, const coordtype *c,
	int which, int maxcount)
{
	if (p. empty ())
	{
		if (which == INSIDE)
			return 0;
		else
			return maxcount;
	}

	int count = 0;
	tNeighbors<coordtype> neigh (c, p. dimension ());
	while ((c = neigh. get ()) != NULL)
	{
		if (which == INSIDE)
		{
			if (p. check (c))
				++ count;
		}
		else if (which == OUTSIDE)
		{
			if (!p. check (c))
				++ count;
		}

		if (maxcount && (count >= maxcount))
			return count;
	}

	return count;
} /* countneighbors */

template <class coordtype>
int countneighbors (const tPointset<coordtype> &p,
	const tPointset<coordtype> &q, coordtype *c,
	int which, int maxcount)
{
	if ((q. empty ()) || (p. dimension () != q. dimension ()))
		return countneighbors (p, c, which, maxcount);
	else if (p. empty ())
		return countneighbors (q, c, which, maxcount);

	int count = 0;
	tNeighbors<coordtype> neigh (c, p. dimension ());
	while ((c = neigh. get ()) != NULL)
	{
		if (which == INSIDE)
		{
			if (p. check (c) || q. check (c))
				++ count;
		}
		else if (which == OUTSIDE)
		{
			if (!p. check (c) && !q. check (c))
				++ count;
		}

		if (maxcount && (count >= maxcount))
			return count;
	}

	return count;
} /* countneighbors */

template <class coordtype>
int attheborder (const tPointset<coordtype> &p, const coordtype *c)
{
	return (countneighbors (p, c, OUTSIDE, 1));

} /* attheborder */

template <class coordtype>
int_t findboundarypoint (tPointset<coordtype> &p, int_t n, int direction)
{
	if (direction >= 0)
	{
		if (n >= p. size ())
			return -1;
		if (n < 0)
			n = 0;
		int_t size = p. size ();
		while (n < size)
		{
			if (attheborder (p, p [n]))
				return n;
			else
				++ n;
		}
		return -1;
	}
	else
	{
		if (n < 0)
			return -1;
		if (n >= p. size ())
			n = p. size () - 1;
		while (n >= 0)
		{
			if (attheborder (p, p [n]))
				return n;
			else
				-- n;
		}
		return -1;
	}
} /* findboundarypoint */

template <class coordtype>
int_t findboundarypoint (tPointset<coordtype> &p, tPointset<coordtype> &q,
	int_t n, int direction)
{
	if (direction >= 0)
	{
		if (n >= p. size ())
			return -1;
		if (n < 0)
			n = 0;
		while (n < p. size ())
		{
			if (countneighbors (p, q, p [n], OUTSIDE, 1))
				return n;
			else
				++ n;
		}
		return -1;
	}
	else
	{
		if (n < 0)
			return -1;
		if (n >= p. size ())
			n = p. size () - 1;
		while (n >= 0)
		{
			if (countneighbors (p, q, p [n], OUTSIDE, 1))
				return n;
			else
				-- n;
		}
		return -1;
	}
} /* findboundarypoint */

template <class coordtype>
void computeboundary (const tPointset<coordtype> &p, tPointset<coordtype> &b)
{
	// add all the points which are at the border
	int_t size = p. size ();
	for (int_t i = 0; i < size; ++ i)
	{
		coordtype *c = p [i];
		if (attheborder (p, c))
			b. add (c);
	}
	return;
} /* computeboundary */

template <class coordtype>
tPointset<coordtype> *computeboundary (tPointset<coordtype> &p)
{
	// create a new set of points
	tPointset<coordtype> *boundary = new tPointset<coordtype>;

	// if cannot allocate memory for it, return nothing
	if (!boundary)
		return NULL;

	// copy the global parameters (the defaults may be different)
	boundary -> dimension (p. dimension ());
	boundary -> gridsize (p. gridsize ());
	boundary -> wrapspace (p. wrapspace ());

	// compute the boundary
	computeboundary (p, *boundary);

	return boundary;
} /* computeboundary */

template <class coordtype>
void enhancepoint (tPointset<coordtype> &p, coordtype *c)
{
	tNeighbors<coordtype> neigh (c, p. dimension ());

	while ((c = neigh. get ()) != NULL)
		p. add (c);

	return;
} /* enhancepoint */

template <class coordtype>
void enhancepoint (tPointset<coordtype> &p, int_t n)
{
	enhancepoint (p, p [n]);

	return;
} /* enhancepoint */

template <class coordtype>
void enhance (tPointset<coordtype> &p)
{
	int_t size = p. size ();
	for (int_t i = 0; i < size; ++ i)
		enhancepoint (p, p [i]);

	return;
} /* enhance */

template <class coordtype>
int read (textfile &f, coordtype *c, int maxdim)
{
	// ignore lines until you can find an opening parenthesis,
	// brace or bracket and read this character
	int ready = 0;
	while (!ready)
	{
		switch (f. checkchar ())
		{
			case '(':
			case '[':
			case '{':
			case '"':
			case '\'':
				f. readchar ();
				ready = 1;
				break;
			case '+':
			case '-':
				break;
			case EOF:
				return 0;
			default:
				f. ignoreline ();
				break;
		}
	}

	// read the coordinates
	int n = 0;
	while (1)
	{
		// read the current coordinate of the point
		c [n ++] = (coordtype) f. readnumber ();

		// read a comma between the coordinates
		// or the closing parenthesis, brace or bracket if any
		switch (f. checkchar ())
		{
			case ')':
			case ']':
			case '}':
			case '"':
			case '\'':
				f. readchar ();
				return n;
			case ',':
				f. readchar ();
				break;
			case '-':
			case '+':
				break;
			default:
				if ((f. checkchar () < '0') ||
					(f. checkchar () > '9'))
					return n;
		}

		// check if the maximal dimension allowed has been reached
		if (n >= maxdim)
			return n;
	}
} /* read */

template <class coordtype>
int read (std::istream &in, coordtype *c, int maxdim)
{
	textfile f (in);
	return read (f, c, maxdim);
} /* read */

/// Reads the coordinates of a point. The point must begin with an opening
/// parenthesis, brace or bracket (unless a closing parenthesis is different
/// from EOF), then the coordinates must be separated by spaces or commas,
/// and must end with a corresponding closing parenthesis, brace or bracket
/// (or the given one). The closing parenthesis may also be defined as '\n'.
/// Interrupts if the number of coordinates reaches the maximal dimension.
/// Returns the number of coordinates read or -1 on error.
template <class coordtype>
inline int readcoordinates (std::istream &in, coordtype *coord, int maxdim,
	int closing)
{
	// read the opening parenthesis
	if (closing == EOF)
		closing = readparenthesis (in);
	if (closing == EOF)
		return -1;

	int cur = 0;

	ignorecomments (in);
	while ((in. peek () != closing) && (cur < maxdim))
	{
		// ignore a plus before the number if necessary
		if (in. peek () == '+')
			in. get ();

		// finish if there is no number at the input
		if ((in. peek () != '-') && !std::isdigit (in. peek ()))
			break;

		// read the number as 'long' (just in case)
		long number;
		in >> number;
	//	if (!in)
	//		return -1;

		// transform this number to a coordtype
		coord [cur] = (coordtype) number;
		if (coord [cur] != number)
			return -1;

		// move to the next coordtype position
		++ cur;
		if (closing == '\n')
		{
			while ((in. peek () == ' ') ||
				(in. peek () == '\t') ||
				(in. peek () == '\r'))
				in. get ();
		}
		else
			ignorecomments (in);

		// one more thing: read the following comma if any
		if (in. peek () == ',')
		{
			in. get ();
			ignorecomments (in);
		}
	}

	// verify that the coordinates were read successfully
//	if (!in)
//		return -1;

	// read the closing parenthesis
	if (in. peek () == closing)
		in. get ();
	else if ((closing == '\n') && (in. peek () == EOF))
		;
	else
		return -1;

	return cur;
} /* readcoordinates */

template <class coordtype>
inline int readcoordinates (std::istream &in, coordtype *coord, int maxdim)
{
	return readcoordinates (in, coord, maxdim, EOF);
} /* readcoordinates */

template <class coordtype>
int write (std::ostream &out, const coordtype *c, int dim, char parenthesis,
	char closing)
{
	// write the opening parenthesis, brace or bracket
	if (parenthesis != 0)
		out << parenthesis;

	// output the point's coordinates
	for (int i = 0; i < dim; ++ i)
	{
		if (i)
			out << ",";
		out << c [i];
	}

	// write an appropriate closing parenthesis, brace or bracket
	if (closing)
		out << closing;
	else if (parenthesis)
	{
		int ch = closingparenthesis (parenthesis);
		if (ch == EOF)
			closing = parenthesis;
		else
			closing = (char) ch;
		out << closing;
	}

	return dim;
} /* write */

template <class coordtype>
int readcubeorcell (std::istream &in, coordtype *left, coordtype *right,
	int maxdim, int *type)
{
	// ignore all the texts that appear before the actual cell or cube
	int closing;
	while ((closing = closingparenthesis (in. peek ())) == EOF)
	{
		ignoreline (in);
		ignorecomments (in);
		if (!in)
			return 0;
	}

	// try reading the coordinates of the cube
	int dim = readcoordinates (in, left, maxdim);

	// if successful, then both parentheses are read
	if (dim > 0)
	{
		// check if this is not a product of intervals
		ignorecomments (in);
		if (((in. peek () != 'x') && (in. peek () != 'X')) ||
			(dim > 2))
		{
			// set the right coordinates accordingly
			for (int i = 0; i < dim; ++ i)
				right [i] = (coordtype) (left [i] + 1);
			if (type)
				*type = CUBE;
			return dim;
		}

		// read the remaining intervals
		right [0] = (dim < 2) ? left [0] : left [1];
		dim = 1;
		coordtype temp [2];
		while ((in. peek () == 'x') || (in. peek () == 'X'))
		{
			if (dim >= maxdim)
				throw "Too many intervals in a product.";
			in. get ();
			ignorecomments (in);
			int d = readcoordinates (in, temp, 2);
			if ((d <= 0) || !in)
				throw "Can't read a product of intervals.";
			left [dim] = temp [0];
			right [dim] = (d < 2) ? temp [0] : temp [1];
			++ dim;
			ignorecomments (in);
		}
		if (type)
			*type = CELL;
		return dim;
	}

	// otherwise, this is a cubical cell
	else
	{
		// if an error is set for the input stream, clear it
		in. clear (in. rdstate () & ~std::ios::failbit);
		ignorecomments (in);

		// read two points for the cell
		int leftdim = readcoordinates (in, left, maxdim);
		ignorecomments (in);
		int rightdim = readcoordinates (in, right, maxdim);
		ignorecomments (in);

		// compare the dimensions
		if (!leftdim || !rightdim)
			throw "Can't read a cell.";
		else if (leftdim != rightdim)
			throw "Different dim of left & right point.";
		else
			dim = leftdim;

		// read the closing bracket of the cell
		if (in. get () != closing)
			throw "Can't read the closing bracket of a cell.";
		ignorecomments (in);
		if (type)
			*type = CELL;
	}
	return dim;
} /* readcubeorcell */

template <class coordtype>
int_t read (textfile &f, tPointset<coordtype> &p,
	int_t first, int_t howmany,
	coordtype *wrap, int maxdim, int quiet,
	tPointset<coordtype> *notthese)
{
	// prepare a temporary point of maximal dimension
	if (maxdim <= 0)
	{
		if (wrap)
			wrap = NULL;
		maxdim = 100;
	}
	coordtype *temp = allocatepoint<coordtype> (maxdim + 1);

	int_t count = 0;
	int dim = p. empty () ? 0 : p. dimension ();

	if (notthese && !notthese -> empty ())
	{
		if (!dim)
			dim = notthese -> dimension ();
		else if (dim != notthese -> dimension ())
		{
			if (!quiet)
				sout << "Error: Dimensions not the same.\n";
			return -1;
		}
	}

	while (1)
	{
		// stop reading if it is already enough
		if ((howmany >= 0) && (count >= howmany))
		{
			delete [] temp;
			return count;
		}

		// ignore all the lines which do not start
		// with an opening parenthesis
		while ((f. checkchar () != 40) && (f. checkchar () != 91) &&
			(f. checkchar () != 123) && (f. checkchar () != EOF))
			f. ignoreline ();

		// if this is the end of the file, finish successfully
		if (f. checkchar () == EOF)
		{
			delete [] temp;
			return count;
		}

		// read a point
		int n = read (f, temp, maxdim + 1);
		if (n > maxdim)
		{
			if (!quiet)
				sout << "Line " << f. linenumber () <<
					": The point has too many " <<
					"coordinates.\n";
			delete [] temp;
			return -1;
		}

		// check if the number of coordinates is the same
		// as the dimension of the points in the set
		if (!first && dim && n && (n != dim))
		{
			if (!quiet)
				sout << "Line " << f. linenumber () <<
					": Incorrect point dimension.\n";
			delete [] temp;
			return -1;
		}

		// set the dimension to be the number of coordinates
		if (!first && !dim)
		{
			dim = n;
			if (p. dimension () != dim)
				p. dimension (dim);
		}

		// add the read point to the set
		if (first)
			-- first;
		else
		{
			if (wrap)
			{
				p. wrapspace (wrap);
				wrap = NULL;
			}
			if (!notthese || !notthese -> check (temp))
				p. add (temp);
			++ count;
		}
	}
} /* read */

template <class coordtype>
int_t read (std::istream &in, tPointset<coordtype> &p,
	int_t first, int_t howmany, coordtype *wrap, int maxdim,
	int quiet, tPointset<coordtype> *notthese)
{
	textfile f (in);
	return read (f, p, first, howmany, wrap, maxdim, quiet, notthese);
} /* read */

template <class coordtype>
int_t read (textfile &f, tPointset<coordtype> &p,
	coordtype *wrap, int maxdim,
	int quiet, tPointset<coordtype> *notthese)
{
	return read (f, p, 0, -1, wrap, maxdim, quiet, notthese);
} /* read */

template <class coordtype>
int_t read (std::istream &in, tPointset<coordtype> &p, coordtype *wrap,
	int maxdim, int quiet, tPointset<coordtype> *notthese)
{
	textfile f (in);
	return read (f, p, wrap, maxdim, quiet, notthese);
} /* read */

template <class coordtype>
textfile &operator >> (textfile &f, tPointset<coordtype> &p)
{
	read (f, p);
	return f;
} /* operator >> */

template <class coordtype>
std::istream &operator >> (std::istream &in, tPointset<coordtype> &p)
{
	textfile f (in);
	read (f, p);
	return in;
} /* operator >> */

template <class coordtype>
int_t write (std::ostream &out, tPointset<coordtype> &p,
	int_t first, int_t howmany, int)
{
	int_t count = 0;
	int dim = p. dimension ();

	// write the number of points in the set
	out << "; The set contains " << p. size () << " points.\n";
	if (first)
		out << "; Not writing first " << first << " points.\n";
	if (howmany >= 0)
		out << "; Writing at most " << howmany << " points.\n";

	// write the size of the grid
	if (dim && p. gridsize ())
	{
		for (int i = 0; i < dim; ++ i)
			out << (i ? ", " : "; Grid size: ") <<
				p. gridsize () [i];
		out << '\n';
	}

	// write statistical information if it has been gathered
	if (p. gethashsize ())
		out << "; Hashing table size: " <<
			p. gethashsize () << " entries.\n";

	if (p. stat -> hashhits)
		out << "; Hashing statistics: " <<
			((p. stat -> hashhits + p. stat -> hashmisses) /
			p. stat -> hashhits) << '.' <<
			((p. stat -> hashhits + p. stat -> hashmisses) * 10 /
			p. stat -> hashhits) % 10 << " trials per point, " <<
			p. stat -> rehashcount << " times rehashed.\n";

	if (p. minimal && p. maximal)
	{
		out << "; The coordinates " <<
			(p. wereremoved ? "varied" : "vary") << " from ";
		write (out, p. minimal, dim);
		out << " to ";
		write (out, p. maximal, dim);
		out << ".\n";
	}

	std::time_t tm;
	std::time (&tm);
	out << "; Work time: " << (tm - p. stat -> creationtime) <<
		" seconds.\n";

	// add a warning if any points were removed
	if (p. wereremoved)
		out << "; Warning: Points were removed, " <<
			"so their original order may be distorted.\n";

	// write out the dimension of the points (for compatibility
	// with the older versions of 'pointset')
	out << "dimension " << p. dimension () << '\n';

	// output all the points
	int_t size = p. size ();
	for (int_t i = first; i < size; ++ i)
	{
		if ((howmany >= 0) && (count >= howmany))
			return count;
		write (out, p [i], dim);
		out << '\n';
		++ count;
	}

	return count;
} /* write */

template <class coordtype>
std::ostream &operator << (std::ostream &out, tPointset<coordtype> &p)
{
	write (out, p);
	return out;
} /* operator << */


} // namespace homology
} // namespace capd

#endif // _CAPD_HOMOLOGY_POINTSET_H_ 

/// @}

