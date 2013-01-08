/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file bincube.h
///
/// This file contains the definition of a cubical set represented
/// as a bitmap. This is an experimental class, it has many limitations,
/// e.g., the size of the bitmap must be a power of 2 and the same in all
/// directions. It is recommended for usage only in very specialized
/// applications.
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started on November 17, 2005. Last revision: November 22, 2005.


#ifndef _CAPD_HOMOLOGY_BINCUBE_H_ 
#define _CAPD_HOMOLOGY_BINCUBE_H_ 

#include "capd/homology/config.h"
#include "capd/homology/bitcount.h"
#include "capd/homology/hashsets.h"

#include <iostream>
#include <fstream>
#include <ctime>
#include <cstdlib>
#include <cstring>
#include <queue>

namespace capd {
namespace homology {


// --------------------------------------------------
// ---------------------- n^k -----------------------
// --------------------------------------------------

/// This is a helper class which makes the compiler compute n^k
/// during the compilation of the program.
template <int number, int power>
class Power
{
public:
	static const int value = Power<number,power-1>::value * number;
}; /* Power */

/// This is a specialization which defines n^0, necessary to stop
/// the recursion defined in the "Power" template.
template <int number>
class Power<number,0>
{
public:
	static const int value = 1;
}; /* Power */


// --------------------------------------------------
// --------------- SET OF FULL CUBES ----------------
// --------------------------------------------------

/// This is an abstract class which defines a set of full cubes
/// represented as a bitmap for the purpose of the class "bincube".
class SetOfFullCubes
{
public:
	/// This class defines an error type which is caused by using
	/// coordinates of a cube out of range with respect to the given
	/// set of cubes represented as a bitmap.
	class OutOfRange
	{
	};
};


// --------------------------------------------------
// --------------------- BITMAP ---------------------
// --------------------------------------------------

/// A fixed-dimensional bitmap of the size 2^n in each direction.
/// The memory buffer for the map can be borrowed from another source
/// or allocated and then deallocated by the bitmap itself.
/// CURRENTLY UNDER CONSTRUCTION
template <int Dim, int twoPower>
class FixDimBitmap
{
public:
protected:
}; /* class FixDimBitmap */


// --------------------------------------------------
// -------------------- BINCUBE ---------------------
// --------------------------------------------------

/// A binary n-dimensional hypercube for storing cubes as bits.
/// The size of the hypercube is given as a power of 2 (8 => 256).
template <int Dim, int twoPower>
class bincube: public FixDimBitmap<Dim,twoPower>, public SetOfFullCubes
{
public:
	/// The default constructor.
	bincube ();
	
	/// The constructor to use a given memory buffer.
	/// This memory buffer will not be released with delete[].
	bincube (char *buffer);
	
	/// The copying constructor.
	bincube (const bincube<Dim,twoPower> &b);

	/// The assignment operator.
	bincube<Dim,twoPower> &operator = (const bincube<Dim,twoPower> &b);

	/// The destructor.
	~bincube ();

	/// Retrieve the dimension of the cube.
	static int dimension ();
	static const int MaxDim;

	/// Finds the first existing cube beginning at the given number.
	/// The range of 'start' is not verified; must be >= 0, < maxcount.
	/// Returns the number of the cube found or maxcount if failed.
	int findcube (int start = 0) const;

	/// The iterator of the set of cubes within a bitmap.
	class iterator
	{
		friend class bincube<Dim,twoPower>;
	public:
		/// The type of coordinates.
		typedef int CoordType;

		/// The default constructor.
		iterator (bincube<Dim,twoPower> *bcub = 0, int num = -1);

		/// The preincrement operator.
		/// Searches for the next cube in the set.
		iterator &operator ++ ();

		/// The postincrement operator.
		iterator &operator ++ (int);

		/// Conversion of an iterator to int (temporarily).
		operator int () const;

		/// The maximal possible dimension of the cube.
		static const int MaxDim;
		
		/// The dimension of the cube.
		static int dim ();

		/// The coordinates of the cube.
		const int *coord () const;

		/// The coordinates of the cube.
		template <class intType>
		intType *coord (intType *tab) const;

//	protected:
		/// The binary cube in which the cube is contained.
		bincube<Dim,twoPower> *b;

		/// The number of the current bit in the set.
		int n;

	}; /* class iterator */

	/// Returns the iterator that points at the first cube in the set.
	iterator begin ();
	
	/// Returns the iterator that points beyond the end of the set.
	iterator end ();

	/// The maximal possible number of neighbors of a cube
	static const int max_neighbors;

	/// The neighborhood of a cube.
	class neighborhood_iterator: public iterator
	{
	public:
		/// The default constructor.
		neighborhood_iterator (bincube<Dim,twoPower> *bcub = 0,
			int n = -1, int inicur = -1);

		/// The preincrement operator.
		/// Searches for the next cube in the neighborhood.
		neighborhood_iterator &operator ++ ();

		/// The postincrement operator.
		neighborhood_iterator &operator ++ (int);

		/// Conversion to the number of the neighbor cube (temp!).
		operator int () const;

		/// Conversion to a cube iterator.
	//	operator iterator () const;

		/// Operator == to compare two neighborhood iterators.
//		friend bool operator ==
//			(const bincube<Dim,twoPower>::neighborhood_iterator &x1,
//			const bincube<Dim,twoPower>::neighborhood_iterator &x2);

	protected:
		/// The binary cube in which the neighborhood is contained.
		bincube<Dim,twoPower> *b;

		/// The coordinates of the middle cube in the neighborhood.
		int coord [Dim];

		/// The coordinates of the current neighbor.
		int ncoord [Dim];

		/// The number of the current neighbor in the binary cube.
		int curnum;

		/// The neighbor counter (up to max_neighbors).
		int cur;

	}; /* class neighborhood_iterator */

	/// Creates a neighborhood iterator for the specified cube
	/// and sets it at the first cube.
	neighborhood_iterator neighborhood_begin (int number) const;

	/// Creates a one-behind-the-end iterator for the given cube.
	neighborhood_iterator neighborhood_end (int number) const;

	/// Sets the bit corresponding to the given cube (by number).
	/// Warning: The range of the number is not verified.
	void add (int number);

	/// Sets the bit corresponding to the given cube (by number).
	/// Note: The range of the coordinates is corrected if necessary.
	template <class intType>
	void add (const intType *coord);

	/// Checks if the given cube belongs to the set or not.
	/// Warning: The range of the number is not verified.
	bool check (int number) const;

	/// Checks if the given cube belongs to the set or not.
	/// Note: The range of the coordinates is corrected if necessary.
	template <class intType>
	bool check (const intType *coord) const;

	/// Clears the bit corresponding to the given cube (by number).
	/// Warning: The range of the number is not verified.
	void remove (int number);

	/// Clears the bit corresponding to the given cube (by number).
	/// Note: The range of the coordinates is corrected if necessary.
	template <class intType>
	void remove (const intType *coord);

	/// Gets the binary buffer for reading only.
	const char *getbuffer () const;

	/// Gets the binary buffer for reading only.
	operator const char * () const;

	/// Gets the buffer size.
	static int getbufsize ();

	/// Reads the binary buffer from an input stream.
	std::istream &read (std::istream &in);

	/// Verifies whether the space is wrapped in the given direction.
	static bool wrapped (int dir);

	/// Turns on wrapping in the given direction.
	static void wrap (int dir);

	/// Turns off wrapping in the given direction.
	static void dontwrap (int dir);

	/// Wraps the coordinate in the given direction if necessary.
	template <class intType>
	static intType wrap (intType coord, int dir);

	/// Determines the number of the cube with given coordinates.
	/// Verifies the range of the coordinates and uses wrapping.
	template <class intType>
	static int coord2num (const intType *coord);

	/// Determines the coordinates of the cube with given number.
	template <class intType>
	static intType *num2coord (int number, intType *coord);

	/// Determines the coordinates of the cube with given number.
	/// Returns 0 if this function is inavailable.
	/// One must use the other function in that case.
	template <class intType>
	static const intType *num2coord (int number);

	/// Get the number of cubes in the set.
	int count () const;
	operator int () const;

	/// Verifies whether the set is empty or not.
	bool empty () const;

	/// Makes the set empty.
	void clear ();

	/// The maximal number of cubes that can be stored in the set.
	static const int maxcount;

protected:
	/// The memory for storing the hypercubes.
	char *buf;
	
	/// Was the memory for the buffer allocated?
	bool allocated;
	
	/// The number of cubes in the set (or -1 if unknown)
	mutable int cardinality;

	/// The size of the buffer in bytes.
	static const int bufsize;
	
	/// The mask for extracting one coordinate from the number.
	static const int twoMask;

	/// The width of the set in each direction (in cubes).
	static const int width;

	/// Wrapping in each direction.
	static int wrapping;

}; /* class bincube */

template <int Dim, int twoPower>
const int bincube<Dim,twoPower>::bufsize = 1 << (Dim * twoPower - 3);

template <int Dim, int twoPower>
const int bincube<Dim,twoPower>::maxcount = 1 << (Dim * twoPower);

template <int Dim, int twoPower>
const int bincube<Dim,twoPower>::twoMask = ~0u >> (32 - twoPower);

template <int Dim, int twoPower>
const int bincube<Dim,twoPower>::width = 1 << twoPower;

template <int Dim, int twoPower>
int bincube<Dim,twoPower>::wrapping = 0;

template <int Dim, int twoPower>
const int bincube<Dim,twoPower>::MaxDim = Dim;

template <int Dim, int twoPower>
const int bincube<Dim,twoPower>::iterator::MaxDim = Dim;

template <int Dim, int twoPower>
const int bincube<Dim,twoPower>::max_neighbors = Power<3,Dim>::value - 1;


// --------------------------------------------------

template <int Dim, int twoPower>
inline bincube<Dim,twoPower>::bincube ()
{
	buf = new char [bufsize];
	allocated = true;
	memset (buf, 0, bufsize);
	cardinality = 0;
	return;
} /* bincube::bincube */

template <int Dim, int twoPower>
inline bincube<Dim,twoPower>::bincube (char *buffer)
{
	buf = buffer;
	allocated = false;
	cardinality = -1;
	return;
} /* bincube::bincube */

template <int Dim, int twoPower>
inline bincube<Dim,twoPower>::bincube (const bincube<Dim,twoPower> &b)
{
	buf = new char [bufsize];
	allocated = true;
	memcpy (buf, b. buf, bufsize);
	cardinality = b. cardinality;
	return;
} /* bincube::bincube */

template <int Dim, int twoPower>
inline bincube<Dim,twoPower> &
	bincube<Dim,twoPower>::operator = (const bincube<Dim,twoPower> &b)
{
	memcpy (buf, b. buf, bufsize);
	cardinality = b. cardinality;
	return;
} /* bincube::bincube */

template <int Dim, int twoPower>
inline bincube<Dim,twoPower>::~bincube ()
{
	if (allocated)
		delete [] buf;
	return;
} /* bincube::~bincube */

// --------------------------------------------------

template <int Dim, int twoPower>
inline int bincube<Dim,twoPower>::dimension ()
{
	return Dim;
} /* bincube::dimension */

template <int Dim, int twoPower>
inline bool bincube<Dim,twoPower>::wrapped (int dir)
{
	return bincube<Dim,twoPower>::wrapping & (1 << dir);
} /* bincube::wrapped */

template <int Dim, int twoPower>
inline void bincube<Dim,twoPower>::wrap (int dir)
{
	bincube<Dim,twoPower>::wrapping |= (1 << dir);
	return;
} /* bincube::wrap */

template <int Dim, int twoPower>
inline void bincube<Dim,twoPower>::dontwrap (int dir)
{
	bincube<Dim,twoPower>::wrapping &= ~(1 << dir);
	return;
} /* bincube::dontwrap */

template <int Dim, int twoPower>
template <class intType>
inline intType bincube<Dim,twoPower>::wrap (intType coord, int dir)
{
	if (wrapped (dir))
	{
		// this is fast but can be very slow if the
		// coordinates are far from the actual binary cube
		while (coord < 0)
			coord += width;
		while (coord >= width)
			coord -= width;
	}
	return coord;
} /* bincube::wrap */

// --------------------------------------------------

template <int Dim, int twoPower>
template <class intType>
inline int bincube<Dim,twoPower>::coord2num (const intType *coord)
{
	int number = 0;
	for (int i = Dim - 1; i >= 0; -- i)
	{
		int c = coord [i];
		if (wrapped (i))
		{
			// this is fast but can be very slow if the
			// coordinates are far from the actual binary cube
			while (c < 0)
				c += width;
			while (c >= width)
				c -= width;
		}
		else if ((c < 0) || (c >= width))
			throw SetOfFullCubes::OutOfRange ();
		number <<= twoPower;
		number |= c;
	}
	return number;
} /* bincube::coord2num */

template <int Dim, int twoPower>
template <class intType>
inline intType *bincube<Dim,twoPower>::num2coord (int number, intType *coord)
{
	for (int i = 0; i < Dim; ++ i)
	{
		coord [i] = number & bincube<Dim,twoPower>::twoMask;
		number >>= twoPower;
	}
	return coord;
} /* bincube::num2coord */

template <int Dim, int twoPower>
template <class intType>
inline const intType *bincube<Dim,twoPower>::num2coord (int /*number*/)
{
	return 0;
} /* bincube::num2coord */

// --------------------------------------------------

template <int Dim, int twoPower>
inline int bincube<Dim,twoPower>::findcube (int start) const
{
	// determine the offset of the byte containing the cube
	int offset = start >> 3;

	// don't look for cubes outside the valid range
	if (offset >= bufsize)
		return maxcount;

	// look for a cube within this byte
	if (buf [offset])
	{
		int bitnumber = start & 7;
		while (bitnumber < 8)
		{
			if (buf [offset] & (1 << bitnumber))
				return (offset << 3) + bitnumber;
			++ bitnumber;
		}
	}

	// search for a non-zero byte
	while (1)
	{
		++ offset;
		if (offset >= bufsize)
			return maxcount;
		if (buf [offset])
			break;
	}

	// retrieve the cube with the non-zero bit within this byte
	int bitnumber = 0;
	while (1)
	{
		if (buf [offset] & (1 << bitnumber))
			return (offset << 3) + bitnumber;
		++ bitnumber;
	}
} /* bincube::findcube */

// --------------------------------------------------

template <int Dim, int twoPower>
inline bool bincube<Dim,twoPower>::check (int number) const
{
	return buf [number >> 3] & (1 << (number & 7));
} /* bincube::check */

template <int Dim, int twoPower>
template <class intType>
inline bool bincube<Dim,twoPower>::check (const intType *coord) const
{
	return check (coord2num (coord));
} /* bincube::check */

template <int Dim, int twoPower>
inline void bincube<Dim,twoPower>::add (int number)
{
	if ((cardinality >= 0) && !check (number))
		++ cardinality;
	buf [number >> 3] |= (char) (1 << (number & 7));
	return;
} /* bincube::add */

template <int Dim, int twoPower>
template <class intType>
inline void bincube<Dim,twoPower>::add (const intType *coord)
{
	return add (coord2num (coord));
} /* bincube::add */

template <int Dim, int twoPower>
inline void bincube<Dim,twoPower>::remove (int number)
{
	if ((cardinality > 0) && check (number))
		-- cardinality;
	buf [number >> 3] &= (char) (~(1 << (number & 7)));
	return;
} /* bincube::remove */

template <int Dim, int twoPower>
template <class intType>
inline void bincube<Dim,twoPower>::remove (const intType *coord)
{
	return remove (coord2num (coord));
} /* bincube::remove */

// --------------------------------------------------

template <int Dim, int twoPower>
inline bincube<Dim,twoPower>::iterator::iterator
	(bincube<Dim,twoPower> *bcub, int num): b (bcub), n (num)
{
	return;
} /* bincube::iterator::iterator */

template <int Dim, int twoPower>
inline typename bincube<Dim,twoPower>::iterator &
	bincube<Dim,twoPower>::iterator::operator ++ ()
{
	if (!b || (n >= bincube<Dim,twoPower>::maxcount))
		return *this;
	n = b -> findcube (n + 1);
	return *this;
} /* bincube::iterator::operator ++ */

template <int Dim, int twoPower>
inline typename bincube<Dim,twoPower>::iterator &
	bincube<Dim,twoPower>::iterator::operator ++ (int)
{
	iterator prev = *this;
	++ *this;
	return prev;
} /* bincube::iterator::operator ++ */

template <int Dim, int twoPower>
inline bincube<Dim,twoPower>::iterator::operator int () const
{
	return n;
} /* bincube::iterator::operator int */

template <int Dim, int twoPower>
inline int bincube<Dim,twoPower>::iterator::dim ()
{
	return Dim;
} /* bincube::iterator::dim */

template <int Dim, int twoPower>
inline const int *bincube<Dim,twoPower>::iterator::coord () const
{
	return 0;
} /* bincube::coord */

template <int Dim, int twoPower>
template <class intType>
inline intType *bincube<Dim,twoPower>::iterator::coord (intType *tab) const
{
	return bincube<Dim,twoPower>::num2coord (n, tab);
} /* bincube::coord */

// --------------------------------------------------

template <class coordinate>
inline void bit2neighborAlg (int number, const coordinate *src,
	coordinate *dest, int Dim)
{
	++ number;
	for (int i = Dim - 1; i >= 0; -- i)
	{
		dest [i] = src [i];
		switch (number % 3)
		{
			case 2:
				-- (dest [i]);
				break;
			case 1:
				++ (dest [i]);
				break;
			case 0:
				break;
			default:
				throw "Erratic neighbor.";
		}
		number /= 3;
	}

	return;
} /* bit2neighborAlg */

template <class settype>
typename settype::iterator bit2neighborAlg
	(const typename settype::iterator &q, int n)
{
	const int Dim = settype::MaxDim;
	int coord [Dim];
	q. b -> num2coord (q, coord);
	bit2neighborAlg (n, coord, coord, Dim);
	try
	{
		return typename settype::iterator (q. b,
			q. b -> coord2num (coord));
	}
	catch (...)
	{
	}
	return q;
} /* bit2neighborAlg */

// --------------------------------------------------

template <int Dim, int twoPower>
inline bincube<Dim,twoPower>::neighborhood_iterator::neighborhood_iterator
	(bincube<Dim,twoPower> *bcub, int num, int inicur):
	b (bcub), curnum (-1), cur (inicur)
{
	if (b && (num >= 0))
		b -> num2coord (num, coord);
	if (num == bincube<Dim,twoPower>::max_neighbors)
	{
		for (int i = 0; i < Dim; ++ i)
			ncoord [i] = 0;
	}
	return;
} /* bincube::neighborhood_iterator::neighborhood_iterator */

template <int Dim, int twoPower>
inline typename bincube<Dim,twoPower>::neighborhood_iterator &
	bincube<Dim,twoPower>::neighborhood_iterator::operator ++ ()
{
	if (!b || (cur >= bincube<Dim,twoPower>::max_neighbors))
		return *this;
	while (1)
	{
		++ cur;
		if (cur >= bincube<Dim,twoPower>::max_neighbors)
		{
			for (int i = 0; i < Dim; ++ i)
				ncoord [i] = 0;
			curnum = -1;
			return *this;
		}
		bit2neighborAlg (cur, coord, ncoord, Dim);
		try
		{
			curnum = b -> coord2num (ncoord);
			if (b -> check (curnum))
				return *this;
		}
		catch (...)
		{
		}
	}
	return *this;
} /* bincube::iterator::operator ++ */

template <int Dim, int twoPower>
inline typename bincube<Dim,twoPower>::neighborhood_iterator &
	bincube<Dim,twoPower>::neighborhood_iterator::operator ++ (int)
{
	if (!b || (cur >= bincube<Dim,twoPower>::maxcount))
		return *this;
	neighborhood_iterator prev = *this;
	++ (*this);
	return prev;
} /* bincube::neighborhood_iterator::operator ++ */

template <int Dim, int twoPower>
inline bincube<Dim,twoPower>::neighborhood_iterator::operator int () const
{
	return curnum;
} /* bincube::neighborhood_iterator::operator int */

template <int Dim, int twoPower>
inline bool operator ==
	(const typename bincube<Dim,twoPower>::neighborhood_iterator &x1,
	const typename bincube<Dim,twoPower>::neighborhood_iterator &x2)
{
//	sout << "DEBUG ==\n";
	return ((x1. b == x2. b) && (x1. cur == x2. cur));
} /* bincube::neighborhood_iterator::operator == */

template <int Dim, int twoPower>
inline bool operator !=
	(const typename bincube<Dim,twoPower>::neighborhood_iterator &x1,
	const typename bincube<Dim,twoPower>::neighborhood_iterator &x2)
{
//	sout << "DEBUG !=\n";
	return !(x1 == x2);
} /* bincube::neighborhood_iterator::operator != */

// --------------------------------------------------

template <int Dim, int twoPower>
inline typename bincube<Dim,twoPower>::neighborhood_iterator
	bincube<Dim,twoPower>::neighborhood_begin (int n) const
{
	typename bincube<Dim,twoPower>::neighborhood_iterator iter
		(const_cast<bincube<Dim,twoPower> *> (this), n);
	return ++ iter;
} /* bincube::neighborhood_begin */

template <int Dim, int twoPower>
inline typename bincube<Dim,twoPower>::neighborhood_iterator
	bincube<Dim,twoPower>::neighborhood_end (int n) const
{
	return neighborhood_iterator
		(const_cast<bincube<Dim,twoPower> *> (this), n,
		max_neighbors);
} /* bincube::neighborhood_end */

// --------------------------------------------------

template <int Dim, int twoPower>
inline typename bincube<Dim,twoPower>::iterator
	bincube<Dim,twoPower>::begin ()
{
	return iterator (this, findcube ());
} /* bincube::begin */

template <int Dim, int twoPower>
inline typename bincube<Dim,twoPower>::iterator
	bincube<Dim,twoPower>::end ()
{
	return iterator (this, maxcount);
} /* bincube::end */

// --------------------------------------------------

template <int Dim, int twoPower>
inline const char *bincube<Dim,twoPower>::getbuffer () const
{
	return buf;
} /* bincube::getbuffer */

template <int Dim, int twoPower>
inline bincube<Dim,twoPower>::operator const char * () const
{
	return buf;
} /* bincube::operator const char * */

template <int Dim, int twoPower>
inline int bincube<Dim,twoPower>::getbufsize ()
{
	return bufsize;
} /* bincube::getbufsize */

template <int Dim, int twoPower>
inline std::istream &bincube<Dim,twoPower>::read (std::istream &in)
{
	in. read (buf, bufsize);
	cardinality = -1;
	return in;
} /* bincube::read */

// --------------------------------------------------

template <int Dim, int twoPower>
inline int bincube<Dim,twoPower>::count () const
{
	if (cardinality >= 0)
		return cardinality;
	char *byte = buf;
	char *end = byte + bufsize;
	int c = 0;
	while (byte != end)
	{
		c += bitcountbyte (*byte);
		++ byte;
	}
	cardinality = c;
	return cardinality;
} /* bincube::count */

template <int Dim, int twoPower>
inline bincube<Dim,twoPower>::operator int () const
{
	return count ();
} /* bincube::operator int */

template <int Dim, int twoPower>
inline bool bincube<Dim,twoPower>::empty () const
{
	return !count ();
} /* bincube::empty */

template <int Dim, int twoPower>
inline void bincube<Dim,twoPower>::clear ()
{
	memset (buf, 0, bufsize);
	cardinality = 0;
	return;
} /* bincube::clear */

// --------------------------------------------------

template <int Dim, int twoPower>
inline std::ostream &operator << (std::ostream &out,
	const bincube<Dim,twoPower> & b)
{
	return out. write (static_cast<const char *> (b), b. getbufsize ());
} /* operator << */

template <int Dim, int twoPower>
inline std::istream &operator >> (std::istream &in,
	bincube<Dim,twoPower> & b)
{
	return b. read (in);
} /* operator >> */

// --------------------------------------------------

/// This is a class used by the classes "Acyclic1d", "Acyclic2d", and
/// "Acyclic3d" to use binary decision diagrams for the verification
/// if a cubical neighborhood of a cube in the class "bincube" is acyclic.
template <class cubetype, class settype>
class NeighborsBdd
{
public:
	// the default constructor
	NeighborsBdd (const cubetype &middle, const settype &cset):
		q (middle), s (cset) {};

	// the procedure for checking whether the given neighbor exists;
	// the number of the neighbor is consistent with the "bit2neighbor"
	// and "neighbor2bit" procedures
	bool check (int n) const
	{
		cubetype neighbor = bit2neighborAlg<settype> (q, n);
		if (neighbor == q)
			return false;
		return (s. check (neighbor));
	}

private:
	// the cube whose neighbors are verified
	const cubetype &q;

	// the set of cubes in which the neighbors of the cube are sought
	const settype &s;

}; /* class NeighborsBdd */

/// This class defines a procedure for verifying if a full-cubical
/// neighborhood in a given set of a full cube of dimension 1 is acyclic.
template <class SetT>
class Acyclic1d
{
public:
	static bool check (typename SetT::iterator q, const SetT &s)
	{
		NeighborsBdd<typename SetT::iterator,SetT> n (q, s);
		return acyclic1d (n);
	}
	static bool check (int n, const SetT &s)
	{
		// FIX const cast!
		typename SetT::iterator q (const_cast<SetT *> (&s), n);
		return check (q, s);
	}
}; /* Acyclic1d */

/// This class defines a procedure for verifying if a full-cubical
/// neighborhood in a given set of a full cube of dimension 2 is acyclic.
template <class SetT>
class Acyclic2d
{
public:
	static bool check (typename SetT::iterator q, const SetT &s)
	{
		NeighborsBdd<typename SetT::iterator,SetT> n (q, s);
		return acyclic2d (n);
	}
	static bool check (int n, const SetT &s)
	{
		// FIX const cast!
		typename SetT::iterator q (const_cast<SetT *> (&s), n);
		return check (q, s);
	}
}; /* Acyclic2d */

/// This class defines a procedure for verifying if a full-cubical
/// neighborhood in a given set of a full cube of dimension 3 is acyclic.
template <class SetT>
class Acyclic3d
{
public:
	static bool check (typename SetT::iterator q, const SetT &s)
	{
		NeighborsBdd<typename SetT::iterator,SetT> n (q, s);
		return acyclic3d (n);
	}
	static bool check (int n, const SetT &s)
	{
		// FIX const cast!
		typename SetT::iterator q (const_cast<SetT *> (&s), n);
		return check (q, s);
	}
}; /* Acyclic3d */

// --------------------------------------------------

/// A class of numbers that can be used in a hashed set.
template <class Number>
class hashNumber
{
public:
	/// The default constructor.
	hashNumber (Number n = 0): number (n) {return;}

	/// The conversion to the number.
	operator Number () const {return number;}

protected:
	int number;
}; /* hashNumber */

/// The first hashing key.
template <class Number>
inline int_t hashkey1 (const hashNumber<Number> &n)
{
	return static_cast<int_t> (static_cast<Number> (n));
} /* hashkey1 */

/// The second hashing key.
template <class Number>
inline int_t hashkey2 (const hashNumber<Number> &n)
{
	return static_cast<int_t> (static_cast<Number> (n) ^
		0xFA5A75A7ul) << 5;
} /* hashkey2 */

typedef hashedset<hashNumber<int> > hashIntQueue;

// --------------------------------------------------

/// Adds the neighbors of the cube 'c' in the set 's' to the set 'q'.
template <class SetT, class QueueT>
void addneighbors (const int &c, const SetT &s, QueueT &q)
{
	typename SetT::neighborhood_iterator cur = s. neighborhood_begin (c),
		end = s. neighborhood_end (c);
	while (cur != end)
	{
		q. add (hashNumber<int> (cur));
		++ cur;
	}
	return;
} /* addneighbors */

/// Reduces the set of full cubes.
/// The class 'Acyclic' provides the function for checking if a cube
/// can be removed from a full cubical set (the 'acyclicity' criterion).
/// A queue in which each element should appear only once is used.
template <typename SetT, typename Acyclic, typename QueueT>
int reduceFullCubesAlg (SetT &X, bool quiet)
{
	// prepare the set of cubes to consider next time
	QueueT Q;

	// scan the entire set until very few cubes are removed
	int count = 0;
	bool exitloop = false;
	bool lastrun = false;
	while (!exitloop)
	{
		// remember to exit the loop after the last run
		if (lastrun)
			exitloop = true;

		int countremoved = 0, countleft = 0;
		typename SetT::iterator cur = X. begin (), end = X. end ();
		while (cur != end)
		{
			if (Acyclic::check (cur, X))
			{
				X. remove (cur);
				++ countremoved;
				if (lastrun)
					addneighbors (cur, X, Q);
			}
			else
				++ countleft;
			++ cur;
	
			// show progress indicator
			if (!quiet && !(count % 5273))
				scon << std::setw (10) << count <<
					"\b\b\b\b\b\b\b\b\b\b";
			++ count;
		}
		if (!quiet)
			sout << ".";

		if (!lastrun && (countremoved - 10 < (countleft >> 2)))
			lastrun = true;
	}
	
	if (!quiet)
		sout << " ";
	count = 0;
	while (!Q. empty ())
	{
		typename QueueT::value_type elem = Q. front ();
		Q. pop ();
		if (Acyclic::check (elem, X))
		{
			X. remove (elem);
			addneighbors (elem, X, Q);
		}

		// show progress indicator
		if (!quiet && !(count % 5273))
			scon << std::setw (10) << count <<
				"\b\b\b\b\b\b\b\b\b\b";
		count ++;
	}

	return 0;
} /* reduceFullCubesAlg */

/*
/// Reduces the set of full cubes.
template <int Dim, int twoPower>
inline int reduceFullCubes (bincube<Dim,twoPower> &X, bool quiet = false)
{
	throw "Binary cube reduction not implemented "
		"for dimension > 3.";
}

/// Reduces the set of full cubes.
template <int twoPower>
inline int reduceFullCubes<3,twoPower> (bincube<3,twoPower> &X, bool quiet = false)
{
	return reduceFullCubesAlg<bincube<3,twoPower>,
		Acyclic3d<bincube<3,twoPower> >,hashIntQueue> (X, quiet);
}

/// Reduces the set of full cubes.
template <int twoPower>
inline int reduceFullCubes<2,twoPower> (bincube<2,twoPower> &X, bool quiet = false)
{
	return reduceFullCubesAlg<bincube<2,twoPower>,
		Acyclic2d<bincube<2,twoPower> >,hashIntQueue> (X, quiet);
}

/// Reduces the set of full cubes.
template <int twoPower>
inline int reduceFullCubes<1,twoPower> (bincube<1,twoPower> &X, bool quiet = false)
{
	return reduceFullCubesAlg<bincube<1,twoPower>,
		Acyclic1d<bincube<1,twoPower> >,hashIntQueue> (X, quiet);
}
*/

/// Reduces the set of full cubes.
template <class FullCubSet>
inline int reduceFullCubes (FullCubSet &X, bool quiet = false)
{
	switch (X. dimension ())
	{
		case 3:
			return reduceFullCubesAlg<FullCubSet,
				Acyclic3d<FullCubSet>,hashIntQueue> (X, quiet);
		case 2:
			return reduceFullCubesAlg<FullCubSet,
				Acyclic2d<FullCubSet>,hashIntQueue> (X, quiet);
		case 1:
			return reduceFullCubesAlg<FullCubSet,
				Acyclic1d<FullCubSet>,hashIntQueue> (X, quiet);
		default:
			throw "Binary cube reduction not implemented "
				"for dimension > 3.";
	}
} /* reduceFullCubes */


} // namespace homology
} // namespace capd

#endif // _CAPD_HOMOLOGY_BINCUBE_H_ 

/// @}

