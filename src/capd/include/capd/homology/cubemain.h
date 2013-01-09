/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file cubemain.h
///
/// This file contains the definition of some functions that are common
/// for all types of cubes, independent of the details of their
/// implementation, mainly the text input/output procedures.
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started in January 2002. Last revision: June 4, 2007.


#ifndef _CAPD_HOMOLOGY_CUBEMAIN_H_ 
#define _CAPD_HOMOLOGY_CUBEMAIN_H_ 


#include "capd/homology/config.h"
#include "capd/homology/textfile.h"
#include "capd/homology/pointset.h"
#include "capd/homology/bitfield.h"
#include "capd/homology/integer.h"
#include "capd/homology/hashsets.h"

#include <iostream>
#include <fstream>
#include <cstdlib>
#include <cstring>


namespace capd {
namespace homology {


/// Converts one cube into another.
template <class dest_cube, class src_cube>
inline dest_cube cube_cast (const src_cube &src)
{
	typename dest_cube::CoordType tab [src_cube::MaxDim];
	src. coord (tab);
	return dest_cube (tab, src. dim ());
} /* cube_cast */

// --------------------------------------------------

/// Writes a cube to the output stream in the text mode.
template <class cubetype>
inline std::ostream &WriteCube (std::ostream &out, const cubetype &c)
{
	typename cubetype::CoordType coord [cubetype::MaxDim];
	c. coord (coord);
	int dim = c. dim ();
	out << "(";
	for (int i = 0; i < dim; ++ i)
	{
		if (i)
			out << ",";
		out << coord [i];
	}
	out << ")";
	return out;
} /* WriteCube */

// --------------------------------------------------

/// Reads a cube from the input text stream.
/// The fixed dimension is forced, unless set to -1.
template <class cubetype>
std::istream &ReadCubeFix (std::istream &in, cubetype &c, int dimfix)
{
	// retrieve the type of coordinates of the cube to read
	typedef typename cubetype::CoordType coordtype;

	// ignore any comments, spaces, tabs and new-line characters
	ignorecomments (in);

	// if there is a number in the input, then there are apparently
	// no parentheses used for the coords or the cube is defined
	// by its number (also indicated with '#')
	if (((in. peek () >= '0') && (in. peek () <= '9')) ||
		(in. peek () == '-') || (in. peek () == '+') ||
		(in. peek () == '#'))
	{
		bool cubenumber = false;
		if (in. peek () == '#')
		{
			in. get ();
			ignorecomments (in);
			cubenumber = true;
		}
		if (in. peek () == '+')
			in. get ();
		int n = -1;
		in >> n;
		while ((in. peek () == ' ') || (in. peek () == '\t'))
			in. get ();

		// if the next coordinate of the cube follows,
		// read the coordinates until end-of-line is encountered
		if (!cubenumber &&
			(((in. peek () >= '0') && (in. peek () <= '9')) ||
			(in. peek () == '-') || (in. peek () == '+')))
		{
			// read the coords and determine the space dimension
			coordtype coord [cubetype::MaxDim];
			coord [0] = n;
			int dim = -1;
			if (in. peek () != '\n')
			{
				dim = readcoordinates (in, coord + 1,
					cubetype::MaxDim - 1, '\n');
				if (dim < 0)
					throw "Unable to read a cube: "
						"Dim too high.";
			}
			++ dim;

			// if could not read the cube, throw an error message
			if ((dimfix >= 0) && (dim != dimfix))
				throw "Unable to read a cube: Wrong dim.";

			// create a cube with the given coordinates
			c = cubetype (coord, dim);

			return in;
		}

		// if the cube is given by its number, read it this way
		else
		{
			int dim = cubetype::PointBase::defaultdimension ();
			const typename cubetype::CoordType *coord = 0;
			if ((n > 0) && (dim > 0))
			{
				coord = cubetype::PointBase::coord
					(n - 1, dim);
			}
			if (!coord)
				throw "Cube no. out of range while reading.";
			c = cubetype (n - 1, dim);
			return in;
		}
	}

	// read the coordinates and determine the space dimension
	typename cubetype::CoordType coord [cubetype::MaxDim];
	int dim = readcoordinates (in, coord, cubetype::MaxDim);
	if (dim < 0)
		throw "Unable to read a cube: Dimension too high.";

	// if could not read the cube, throw an error message
	if ((dimfix >= 0) && (dim != dimfix))
		throw "Unable to read a cube: Wrong dimension.";

	// create the cube with the given coordinates
	c = cubetype (coord, dim);

	return in;
} /* ReadCubeFix */

/// Reads a cube from the input text stream.
template <class cubetype>
inline std::istream &ReadCube (std::istream &in, cubetype &c)
{
	return ReadCubeFix (in, c, -1);
} /* ReadCube */

/// Reads a set of cubes and ignores the line at the beginning of the file
/// which starts with the letter 'd' (like "dimension 2").
/// For compatibility with previous versions of my software.
template <class cubsettype>
std::istream &ReadCubes (std::istream &in, cubsettype &s)
{
	// ignore any comments at the beginning of the file
	ignorecomments (in);

	// if the word "dimension" found, ignore the entire line
	if (in. peek () == 'd')
	{
		in. ignore (20000, '\n');
		ignorecomments (in);
	}

	// read the set of cubes using the standard procedure
	return read (in, s, LARGE_SIZE);
} /* ReadCubes */

/// Reads a combinatorial cubical multivalued map from an input text stream.
template <class tCube>
std::istream &ReadCubicalMap (std::istream &in, mvmap<tCube,tCube> &m)
{
	// process the entire input file and read the map line-by-line
	ignorecomments (in);
	while (in. peek () != EOF)
	{
		// ignore all the lines which do not define a map assignment
		while ((closingparenthesis (in. peek ()) == EOF) &&
			((in. peek () < '0') || (in. peek () > '9')) &&
			(in. peek () != EOF))
		{
			ignoreline (in);
			ignorecomments (in);
		}

		// if the end of the file has been reached, exit the loop
		if (in. peek () == EOF)
			break;
	
		// determine the closing parenthesis corresp. to this one
		int closing = closingparenthesis (in. peek ());

		// if the opening parenthesis is valid, read it and
		// check the next character to determine the assignment type
		if (closing != EOF)
		{
			in. get ();
			ignorecomments (in);
		}

		// if the assignment is in the general form, decode the line
		if ((closing == EOF) ||
			(closingparenthesis (in. peek ()) == EOF))
		{
			// read the domain element
			tCube e;
			// if it is given as a number, read it directly
			if (closing == EOF)
			{
				in >> e;
				if (!in)
					throw "Can't read cube's number.";
			}
			// otherwise read the coordinates of the cube
			else
			{
				typename tCube::CoordType coord
					[tCube::MaxDim];
				int dim = readcoordinates (in, coord,
					tCube::MaxDim, closing);
				if (!in || (dim <= 0))
					throw "Unable to read a cube.";
				e = tCube (coord, dim);
			}
			ignorecomments (in);

			// read the assignment arrow
			while (in. peek () == '-')
				in. get ();
			if (in. peek () == '>')
				in. get ();
			ignorecomments (in);

			// read the image of the cube
			read (in, m [e], SMALL_SIZE);
			ignorecomments (in);
		}

		// otherwise read the assignment in the Jacek & Marcin format
		else
		{
			// read the argument cell
			typename tCube::CoordType argleft [tCube::MaxDim];
			typename tCube::CoordType argright [tCube::MaxDim];
			int dim = readcoordinates (in, argleft,
				tCube::MaxDim);
			ignorecomments (in);
			int d1 = readcoordinates (in, argright,
				tCube::MaxDim);
			ignorecomments (in);

			// read the closing and opening brackets
			in. get ();
			ignorecomments (in);
			in. get ();
			ignorecomments (in);

			// read the value cell
			typename tCube::CoordType vleft [tCube::MaxDim];
			typename tCube::CoordType vright [tCube::MaxDim];
			int d2 = readcoordinates (in, vleft, tCube::MaxDim);
			ignorecomments (in);
			int d3 = readcoordinates (in, vright, tCube::MaxDim);
			ignorecomments (in);

			// if there was an I/O error, interrupt reading here
			if (!in || (in. peek () == EOF))
				throw "Cannot read a map assignment line.";

			// read the closing bracket
			in. get ();
			ignorecomments (in);

			// check that all the dimensions are the same
			if ((d1 != dim) || (d2 != dim) || (d3 != dim))
				throw "Wrong dimensions of vertices.";

			// verify that the argument cube is of the right size
			for (int i = 0; i < dim; ++ i)
			{
				if (argright [i] - argleft [i] != 1)
					throw "Wrong size of an argument.";
			}

			// add the argument cube to the map's domain
			hashedset<tCube> &v = m [tCube (argleft, dim)];

			// form a rectangle from this value cell
			tRectangle<typename tCube::CoordType> r
				(vleft, vright, dim);

			// add all the value cubes to the image of this element
			const typename tCube::CoordType *c;
			while ((c = r. get ()) != NULL)
				v. add (tCube (c, dim));
		}
	}
	
	return in;
} /* ReadCubicalMap */


} // namespace homology
} // namespace capd

#endif // _CAPD_HOMOLOGY_CUBEMAIN_H_ 

/// @}

