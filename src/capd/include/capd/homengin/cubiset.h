/// @addtogroup HomologyEngines
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file cubiset.h
///
/// This file defines an very simple interface to manipulating a full cubical
/// set represented as a bitmap for the purpose of homology computation.
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started on March 19, 2006. Last revision: July 27, 2007.


#ifndef _CAPD_HOMENGIN_CUBISET_H_ 
#define _CAPD_HOMENGIN_CUBISET_H_ 

#include <string>
#include <cstring>
#include "capd/homengin/homology.h"


// --------------------------------------------------
// ------------------ CUBICAL SET -------------------
// --------------------------------------------------

/// This class stores a full cubical set and implements some basic
/// operations on such a set, like adding or removing cubes
/// with given coordinates.
class CubicalSet
{
public:
	/// The only constructor allowed: Creates an empty cubical bitmap
	/// of the given size.
	CubicalSet (const int *left_coords, const int *right_coords,
		int dim = EMBEDDING_DIM, const int *space_wrapping = 0);

	/// The destructor.
	~CubicalSet ();

	/// The copy constructor.
	CubicalSet (const CubicalSet &c);

	/// The assignment operator.
	CubicalSet &operator = (const CubicalSet &c);

	/// Computes the Betti numbers of the cubical set.
	/// Note: The size of the result table must be at least dim+1.
	void ComputeBettiNumbers (int *result, const char *engine = 0,
		bool quiet = false) const;

	/// Adds a cube to the set unless the cube is outside the box.
	/// Returns 0 if the cube is within the box or -1 otherwise.
	int Add (const int *coords);

	/// Deletes a cube from the set.
	/// Returns 0 if deleted or -1 if the cube is outside the box.
	int Delete (const int *coords);

	/// Verifies whether the given cube is contained in the cubical set.
	/// Returns 'true' if yes, 'false' if not.
	bool Contains (const int *coords) const;

	/// Clears the bitmap and makes the cubical set empty.
	void Clear ();

private:
	/// Computes the right word offset in the buffer.
	int ByteOffset (const int *coords) const;

	/// Computes the mask for the bit in the right word.
	int BitMask (const int *coords) const;

	/// Verifies whether the cube is within the bounding box.
	bool Inside (const int *coords);

	/// The binary buffer for storing the cubes.
	unsigned char *buffer;

	/// The actual size of the buffer.
	int bufsize;

	/// The dimension of the embedding space.
	int dim;

	/// The sizes of the binary data in the buffer.
	int *sizes;

	/// The coordinates of the minimal vertex of the buffer box.
	int *minimal;

	/// The space wrapping in each direction, if defined.
	int *wrapping;

}; /* class CubicalComples */

// --------------------------------------------------

inline CubicalSet::CubicalSet (const int *left_coords,
	const int *right_coords, int dim, const int *space_wrapping)
{
	if (dim <= 0)
		throw "Non-positive dimension of a cubical complex.";
	this -> dim = dim;
	this -> sizes = new int [dim];
	this -> minimal = new int [dim];
	this -> wrapping = space_wrapping ? new int [dim] : 0;
	this -> bufsize = 0;
	for (int i = 0; i < dim; ++ i)
	{
		minimal [i] = left_coords [i];
		sizes [i] = right_coords [i] - left_coords [i];
		if (sizes [i] <= 0)
			throw "Non-positive size of a cubical complex.";
		if (!i)
		{
			sizes [0] = (sizes [0] + 63) & ~63;
			bufsize = sizes [0] >> 3;
		}
		else
			bufsize *= sizes [i];
	}
	if (space_wrapping)
	{
		for (int i = 0; i < dim; ++ i)
		{
			wrapping [i] = space_wrapping [i];
			if (wrapping [i] < 0)
				wrapping [i] = -space_wrapping [i];
		}
	}
	if (bufsize <= 0)
		throw "Wrong buffer size in a cubical complex.";
	buffer = new unsigned char [bufsize];
	std::memset (buffer, 0, bufsize);
	return;
} /* CubicalSet::CubicalSet */

inline CubicalSet::~CubicalSet ()
{
	delete [] sizes;
	delete [] minimal;
	delete [] buffer;
	if (wrapping)
		delete [] wrapping;
	return;
} /* CubicalSet::~CubicalSet */

inline CubicalSet::CubicalSet (const CubicalSet &c)
{
	dim = c. dim;
	bufsize = c. bufsize;
	sizes = new int [dim];
	minimal = new int [dim];
	for (int i = 0; i < dim; ++ i)
	{
		minimal [i] = c. minimal [i];
		sizes [i] = c. sizes [i];
	}
	buffer = new unsigned char [bufsize];
	std::memcpy (buffer, c. buffer, bufsize);
	return;
} /* CubicalSet::CubicalSet */

inline CubicalSet &CubicalSet::operator = (const CubicalSet &c)
{
	delete [] sizes;
	delete [] minimal;
	delete [] buffer;

	dim = c. dim;
	bufsize = c. bufsize;
	sizes = new int [dim];
	minimal = new int [dim];
	for (int i = 0; i < dim; ++ i)
	{
		minimal [i] = c. minimal [i];
		sizes [i] = c. sizes [i];
		if (i > 0)
			bufsize *= sizes [i];
	}
	buffer = new unsigned char [bufsize];
	std::memcpy (buffer, c. buffer, bufsize);
	return *this;
} /* CubicalSet::operator = */

inline int CubicalSet::ByteOffset (const int *coords) const
{
	int offset = (coords [0] - minimal [0]) >> 3;
	int multiply = ((sizes [0] + 31) >> 5) << 2;
	for (int i = 1; i < dim; ++ i)
	{
		offset += multiply * (coords [i] - minimal [i]);
		multiply *= sizes [i];
	}
	return offset;
} /* CubicalSet::ByteOffset */

inline int CubicalSet::BitMask (const int *coords) const
{
	return 1 << ((coords [0] - minimal [0]) & 0x07);
} /* CubicalSet::BitMask */

inline bool CubicalSet::Inside (const int *coords)
{
	for (int i = 0; i < dim; ++ i)
	{
		if (coords [i] < minimal [i])
			return false;
		if (coords [i] >= minimal [i] + sizes [i])
			return false;
	}
	return true;
} /* CubicalSet::Inside */

inline int CubicalSet::Add (const int *coords)
{
	if (!Inside (coords))
		return -1;
	buffer [ByteOffset (coords)] |= BitMask (coords);
	return 0;
} /* CubicalSet::Add */

inline int CubicalSet::Delete (const int *coords)
{
	if (!Inside (coords))
		return -1;
	buffer [ByteOffset (coords)] &= ~(BitMask (coords));
	return 0;
} /* CubicalSet::Delete */

inline bool CubicalSet::Contains (const int *coords) const
{
	return buffer [ByteOffset (coords)] & BitMask (coords);
} /* CubicalSet::Contains */

inline void CubicalSet::Clear ()
{
	std::memset (buffer, 0, bufsize);
	return;
} /* CubicalSet::Clear */

inline void CubicalSet::ComputeBettiNumbers (int *result,
	const char *engine, bool quiet) const
{
	::ComputeBettiNumbers (buffer, sizes, dim, result, engine,
		wrapping, quiet);
	return;
} /* CubicalSet::ComputeBettiNumbers */

/// Computes the Betti numbers of a full cubical set represented
/// by an object of the class "CubicalSet".
inline void ComputeBettiNumbers (const CubicalSet &s, int *result,
	const char *engine = 0, bool quiet = false)
{
	s. ComputeBettiNumbers (result, engine, quiet);
	return;
} /* ComputeBettiNumbers */


#endif // _CAPD_HOMENGIN_CUBISET_H_ 

/// @}

