/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file bitcode.cpp
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started on November 12, 2001. Last revision: August 16, 2007.


#include "capd/homology/config.h"
#include "capd/homology/textfile.h"
#include "capd/homology/pointset.h"
#include "capd/homology/bitcode.h"

#include <iostream>
#include <fstream>
#include <ctime>
#include <math.h>
#include <cstdlib>

namespace capd {
namespace homology {


// --------------------------------------------------
// ------------------ BITCODE READ ------------------
// --------------------------------------------------
// Read a pointset encoded by bit codes.

int power (int n, int k)
{
        int m = 1;
        while (k --)
                m *= n;
        return (m);
} /* power */

int readbitpoints (std::istream &in, pointset &p, int *bitcode_depth)
{
        // the first number in the file is the dimension of the space
        ignorecomments (in);
        int dim = 0;
        in >> dim;
        if ((dim <= 0) || (p. dimension (dim) != dim))
        {
                sout << "Wrong space dimension.\n";
                return -1;
        }

        // the next number is 2^depth
        ignorecomments (in);
        int nbits = 0;
        in >> nbits;
        int depth = 1;
        if (nbits >= 0)
                depth = nbits / dim;
        if (dim * depth != nbits)
                sout << "Warning: Wrong number of bits.\n";
	if (bitcode_depth)
		*bitcode_depth = depth;

        // the next number is the number of points (to be ignored)
        ignorecomments (in);
        int npoints = -1;
        in >> npoints;
        if (npoints < 0)
                sout << "Warning: the declared number of points "
                        "is negative.\n";

	sout << "Reading " << npoints << " points of dimension " <<
		dim << " with depth " << depth << " (" <<
		nbits << " bits)...\n";

        // read all the points
        coordinate *left = new coordinate [dim];
        coordinate *right = new coordinate [dim];
        int points_read = 0;
        ignorecomments (in);
        while ((in. peek () == '0') || (in. peek () == '1'))
        {
		// reset the interval for the point
		int i;
		for (i = 0; i < dim; i ++)
		{
			left [i] = 0;
			right [i] = (coordinate) (1 << depth);
		}

		// read the bits and narrow the point's coordinates
		for (i = 0; i < depth; i ++)
		{
			for (int d = 0; d < dim; d ++)
			{
				ignorecomments (in);
				if (in. get () == '1')
					left [d] = (coordinate) (left [d] +
						(right [d] - left [d]) / 2);
				else
					right [d] = (coordinate) (left [d] +
						(right [d] - left [d]) / 2);
			}
		}

		// add the point
		p. add (left);

		// update statistics
		points_read ++;

		// go to the next character in the file
		ignorecomments (in);
	}

	// warn if the number of points read is wrong
	if ((npoints >= 0) && (points_read != npoints))
		sout << "Warning: Read " << points_read << " points "
			"instead of declared " << npoints << ".\n";

	// free the temporary tables
	delete [] left;
        delete [] right;

	sout << "Done.\n";

        return 0;
} /* readbitpoints */


// --------------------------------------------------
// ------------------ BITCODE WRITE -----------------
// --------------------------------------------------
// Write a pointset encoded by bit codes.

int writebitcode (std::ostream &out, unsigned char *buf, int nbits)
{
	for (int i = 0; i < nbits; i ++)
	{
		if (i)
			out << ' ';
		if ((buf [i >> 3]) & (0x80u >> (i & 7)))
			out << '1';
		else
			out << '0';
	}
	return 0;
} /* writebitcode */

int comparebitcodes (unsigned char *b1, unsigned char *b2, int nbits)
{
	if (!nbits)
		return 0;
	if (nbits > 7)
	{
		if (*b1 == *b2)
			return comparebitcodes (b1 + 1, b2 + 1, nbits - 8);
		else if (*b1 < *b2)
			return -1;
		else
			return 1;
	}
	unsigned char mask [] = {0, 0x80, 0xC0, 0xE0, 0xF0, 0xF8, 0xFC, 0xFE};
	int v1 = (*b1) & mask [nbits];
	int v2 = (*b2) & mask [nbits];
	if (v1 < v2)
		return -1;
	else if (v1 > v2)
		return 1;
	else
		return 0;
} /* comparebitcodes */

int swapbitcodes (unsigned char *b1, unsigned char *b2, int nbytes)
{
	while (nbytes --)
	{
		unsigned char tmp = *b1;
		*b1 = *b2;
		*b2 = tmp;
		b1 ++;
		b2 ++;
	}
	return 0;
} /* swapbitcodes */

int qsortbitcodes (unsigned char *table, int nbits, int length)
{
	if (length <= 1)
		return 0;
	int i = 0, j = length - 1;
	int nbytes = (nbits + 7) >> 3;
//	int mid = (j - i) / 2;
	unsigned char *middle = table + (length - 1) * nbytes;

	while (i < j)
	{
		// find the first element from the left which is too large
		while ((i < j) && (comparebitcodes (table + i * nbytes,
			middle, nbits) <= 0))
			i ++;
		// find the first element from the right which is too small
		while ((j > i) && (comparebitcodes (table + (j - 1) * nbytes,
			middle, nbits) >= 0))
			j --;
		// swap these elements if they are distinct and shift cursors
		if (i < j)
		{
			// (note: j - i > 1)
			swapbitcodes (table + i * nbytes,
				table + (j - 1) * nbytes, nbytes);
			i ++;
			j --;
		}
	}
	swapbitcodes (table + i * nbytes, middle, nbytes);
	qsortbitcodes (table, nbits, i);
	qsortbitcodes (table + (i + 1) * nbytes, nbits, length - i - 1);
	return 0;
} /* qsortbitcodes */

int sortbitcodes (unsigned char *table, int nbits, int ncodes)
{
	// check whether the table is already sorted; if not, sort it
	int nbytes = (nbits + 7) / 8;
	unsigned char *previous = table, *current = table + nbytes;
	for (int i = 1; i < ncodes; i ++)
		if (comparebitcodes (previous, current, nbits) > 0)
			return qsortbitcodes (table, nbits, ncodes);
		else
		{
			previous = current;
			current += nbytes;
		}
	return 0;
} /* sortbitcodes */

int writebitpoints (std::ostream &out, pointset &p, bool sorted,
	int fixed_depth, coordinate *fixed_corner)
{
        // get the dimension of the points
        int dim = p. dimension ();
        if (dim <= 0)
        {
		sout << "Warning: No points defined.\n";
                return 0;
        }
	int npoints = p. size ();

        // find the minimal and maximal coordinates of the points
        coordinate *minimal = p. minimal;
        coordinate *maximal = p. maximal;

	// fix the lower left corner for the coordinate shift
	coordinate *corner;
	if (fixed_corner)
	{
		corner = fixed_corner;
		for (int i = 0; i < dim; i ++)
			if (minimal [i] > corner [i])
			{
				sout << "Warning: some points are to the " <<
					"left of the origin.\n";
				i = dim;
			}
	}
	else
		corner = minimal;

        // determine the maximal size in all of the directions
        int max_size = 0;
        for (int i = 0; i < dim; i ++)
        {
                int dist = maximal [i] - corner [i] + 1;
                if (max_size < dist)
                        max_size = dist;
        }

        // calculate the necessary depth and number of bits for each point
        int depth = 1;
        while ((1 << depth) < max_size)
                depth ++;
	int nbits = dim * depth;

	// make a correction to the alternative depth if needed
	if (fixed_depth > 0)
	{
		if (depth <= fixed_depth)
			depth = fixed_depth;
		else
			sout << "Warning: Requested depth " << fixed_depth <<
				" is smaller than necessary depth " <<
				depth << ". Using the latter.\n";
	}

	// create a table of all the points encoded in bits
	int nbytes = (nbits + 7) >> 3;
	unsigned char *table = new unsigned char [nbytes * npoints];
	if (!table)
		throw "Not enough memory for a table of bitcodes.";
	else
		sout << "Creating a table of bit codes...\n";

	// fill in the table of bitcodes
	coordinate *left = new coordinate [dim];
	coordinate *right = new coordinate [dim];
	unsigned char *current = table;
	for (int n = 0; n < npoints; n ++)
	{
		// reset the interval for the point
		int i;
		for (i = 0; i < dim; i ++)
		{
			left [i] = corner [i];
			right [i] = (coordinate) (corner [i] + (1 << depth));
		}

		// analyze the point's coordinates and record the bits
		int bit = 0;
		for (i = 0; i < depth; i ++)
		{
			for (int d = 0; d < dim; d ++)
			{
				if (!(bit & 7))
				{
					if (bit)
						current ++;
					(*current) = 0;
				}
                                coordinate mid = (coordinate) (left [d] +
					(right [d] - left [d]) / 2);
                                if (p [n] [d] < mid)
                                        right [d] = mid;
                                else
				{
                                        left [d] = mid;
					(*current) |= (coordinate)
						(0x80 >> (bit & 7));
                                }
				bit ++;
                        }
                }

		// take the next available position in the table
		current ++;
	}

	// sort the table
	if (sorted)
	{
		sout << "Sorting the bitcodes...\n";
		sortbitcodes (table, nbits, npoints);
	}

	// say that you are writing the data to a file
	sout << "Writing " << npoints << " bitcodes for dimension " << dim <<
		" with depth " << depth << " (" << nbits << " bits)...\n";

	// write the initial data to the bitcode file
	out << dim << '\n';
	out << nbits << '\n';
	out << npoints << '\n';

	// write all the points
	current = table;
	for (int j = 0; j < npoints; j ++)
	{
		writebitcode (out, current, nbits);
		out << '\n';
		current += nbytes;
	}

	// finalize
	delete [] table;
	return 0;
} /* writebitpoints */


} // namespace homology
} // namespace capd

/// @}

