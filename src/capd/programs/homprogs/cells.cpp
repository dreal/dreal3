/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file cells.cpp
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started in April 1999. Last revision: November 19, 2002.


#include "capd/homology/config.h"
#include "capd/homology/textfile.h"
#include "cells.h"

#include <iostream>
#include <fstream>
#include <cstdlib>

using namespace capd::homology;


// --------------------------------------------------
// --------------------- POINT ----------------------
// --------------------------------------------------

int point::spacedim = 0;
int point::numberofpoints = 0;
coordinate *point::space_wrapping = NULL;

point::point (textfile &in, int removebrackets)
{
	if (spacedim <= 0)
		throw "Can't create a point of unknown dimension.";
	coord = new coordinate [spacedim];
	if (!coord)
		throw "Not enough memory to create a point.";
	numberofpoints ++;

	if (removebrackets)
		if (in. checkchar () == '[')
			in. readchar ();

	if (in. checkchar () != 40)
		throw "Can't read a point: no opening parenthesis.";
	else
		in. readchar ();
	for (int i = 0; i < spacedim; i ++)
	{
		coord [i] = (coordinate) in. readnumber ();
		wrap (coord [i], i);
		if (in. checkchar () == ',')
			in. readchar ();
	}

	if (in. checkchar () != 41)
		throw "Can't read a point: no closing parenthesis.";
	else
		in. readchar ();

	if (removebrackets)
		if (in. checkchar () == ']')
			in. readchar ();

	return;
} /* point::point */

point::point (point &p, int axis, int diff)
{
	if (spacedim <= 0)
		throw "Can't create a point of unknown dimension.";
	coord = new coordinate [spacedim];
	if (!coord)
		throw "Not enough memory to create a point.";
	numberofpoints ++;

	for (int i = 0; i < spacedim; i ++)
		coord [i] = p. coord [i];
	if ((axis < 0) && (diff != 0))
	{
		for (int j = 0; j < spacedim; j ++)
		{
			coord [j] += (coordinate) diff;
			wrap (coord [j], j);
		}
		return;
	}
	if ((axis < 0) || (axis >= spacedim))
		return;
	coord [axis] += (coordinate) diff;
	wrap (coord [axis], axis);
	return;
} /* point::point */

point::point (coordinate *c)
{
	if (spacedim <= 0)
		throw "Can't create a point of unknown dimension.";
	coord = new coordinate [spacedim];
	if (!coord)
		throw "Not enough memory to create a point.";
	numberofpoints ++;

	for (int i = 0; i < spacedim; i ++)
	{
		coord [i] = c [i];
		wrap (coord [i], i);
	}

	return;
} /* point::point */

void point::wrap_space (int axis, int n)
{
	if (!n)
		return;
	if ((axis < 0) || (axis >= MAXDIM))
		throw "Improper axis for space wrapping requested.";
	if (n < 0)
		throw "Negative space wrapping requested.";
	if (!space_wrapping)
	{
		space_wrapping = new coordinate [MAXDIM];
		if (!space_wrapping)
			throw "Not enough memory for space wrapping.";
		for (int i = 0; i < MAXDIM; i ++)
			space_wrapping [i] = 0;
	}
	space_wrapping [axis] = (coordinate) n;
} /* point::wrap_space */

void point::wrap (coordinate &c, int axis)
{
	if (space_wrapping && space_wrapping [axis])
	{
		c %= space_wrapping [axis];
		if (c < 0)
			c += space_wrapping [axis];
	}
} /* point::wrap */

point::~point ()
{
	numberofpoints --;
	delete [] coord;
	coord = NULL;
	return;
} /* point::~point */

coordinate *point::coordinates ()
{
	return coord;
} /* point::coordinates */

int point::spacedimension (int dim)
{
	if (dim > 0)
	{
//		if (numberofpoints)
//			throw "Can't change space dim: points exist.";
		spacedim = dim;
	}
	return spacedim;
} /* point::spacedimension */

int operator == (point &p1, point &p2)
{
	coordinate *c1 = p1. coordinates ();
	coordinate *c2 = p2. coordinates ();
	if (!c1 || !c2)
		throw "Trying to compare non-existing points.";
	int i = p1. spacedimension ();
	while (i --)
		if (*(c1 ++) != *(c2 ++))
			return 0;
	return 1;
} /* operator == */

void sortcoordinates (point &left, point &right)
{
	coordinate *c1 = left. coordinates ();
	coordinate *c2 = right. coordinates ();
	if (!c1 || !c2)
		throw "Trying to compare non-existing points.";
	int i = left. spacedimension ();
	while (i --)
	{
		if (*c1 > *c2)
		{
			coordinate c0 = *c2;
			*c2 = *c1;
			*c1 = c0;
		}
		c1 ++;
		c2 ++;
	}
	return;
} /* sort coordinates */

std::ostream &operator << (std::ostream &out, const point &p)
{
	for (int i = 0; i < p. spacedim; i ++)
		out << (i ? "," : "(") << p. coord [i];
	out << ")";
	return out;
} /* operator << */


// --------------------------------------------------
// ---------------------- CELL ----------------------
// --------------------------------------------------

int cell::numberofcells = 0;
int *cell::cellcounter = NULL;

cell::cell (textfile &in): left (in, 1), right (in, 1)
{
	// sortcoordinates (left, right);
	numberofcells ++;
	if (!cellcounter)
	{
		cellcounter = new int [left. spacedimension () + 1];
		if (!cellcounter)
			throw "Can't create a cell counter table.";
		for (int i = 0; i <= left. spacedimension (); i ++)
			cellcounter [i] = 0;
	}
	cellcounter [dimension ()] ++;
	return;
} /* cell::cell */

cell::cell (point &p): left (p), right (p, -1, 1)
{
	// sortcoordinates (left, right);	// for space wrapping ?
	numberofcells ++;
	if (!cellcounter)
	{
		cellcounter = new int [left. spacedimension () + 1];
		if (!cellcounter)
			throw "Can't create a cell counter table.";
		for (int i = 0; i <= left. spacedimension (); i ++)
			cellcounter [i] = 0;
	}
	cellcounter [left. spacedimension ()] ++;
}

cell::cell (point &p1, point &p2): left (p1), right (p2)
{
	// sortcoordinates (left, right);	// is it really needed here?
	numberofcells ++;
	if (!cellcounter)
	{
		cellcounter = new int [left. spacedimension () + 1];
		if (!cellcounter)
			throw "Can't create a cell counter table.";
		for (int i = 0; i <= left. spacedimension (); i ++)
			cellcounter [i] = 0;
	}
	cellcounter [dimension ()] ++;
}

cell::cell (cell *c, int axis, int sign):
	left (c -> left, axis, (sign <= 0) ? 0 : 1),
	right (c -> right, axis, (sign >= 0) ? 0 : -1)
{
	// sortcoordinates (left, right); // required if space wrapped?
	numberofcells ++;
	cellcounter [dimension ()] ++;
	return;
} /* cell::cell */

cell::~cell ()
{
	numberofcells --;
	return;
} /* cell::~cell */

int cell::dimension ()
{
	int dim = 0;
	for (int i = 0; i < left. spacedimension (); i ++)
		if (left. coordinates () [i] != right. coordinates () [i])
			dim ++;
	return dim;
} /* cell::cimension */

int cell::thick (int axis)
{
	return (left. coordinates () [axis] < right. coordinates () [axis]);
} /* cell::thick */

coordinate *cell::leftcoord ()
{
	return left. coordinates ();
} /* left coord */

coordinate *cell::rightcoord ()
{
	return right. coordinates ();
} /* right coord */

int operator == (cell &c1, cell &c2)
{
	if (!(c1. left == c2. left))
		return 0;
	return (c1. right == c2. right);
} /* operator == */

std::ostream &operator << (std::ostream &out, const cell &c)
{
	out << "[" << c. left << " " << c. right << "]";
	return out;
} /* operator << */

unsigned cell::hashkey (unsigned hashsize)
{
	unsigned key = 13;
	coordinate *c = leftcoord ();
	int x = 0xFFFF;
	for (int i = 0; i < point::spacedimension (); i ++)
		if (x < 0)
			key += c [i] << ((6 * i) % 14);
		else
			key += c [i] << ((6 * i) % 30);

	return (key % hashsize);
} /* cell::hashkey */

unsigned cell::hashadd (unsigned hashsize)
{
	unsigned add = 1313;
	coordinate *c = rightcoord ();
	for (int i = 0; i < point::spacedimension (); i ++)
		add += c [i] << ((3 * i + 1) % 13);
	return (add % (hashsize - 1) + 1);
} /* cell::hashadd */


// --------------------------------------------------
// ------------------ CELL ELEMENT ------------------
// --------------------------------------------------

cellelement::cellelement (int _number, cell *_c)
{
	number = _number;
	c = _c;
	boundary = NULL;
	next = NULL;
	maplength = 0;
	mapcoeff = NULL;
	mapcell = NULL;
	return;
} /* cellelement::cellelement */

cellelement::~cellelement ()
{
	if (c)
		delete c;
	c = NULL;
	if (boundary)
		delete [] boundary;
	boundary = NULL;
	if (next)
		delete next;
	next = NULL;
	return;
} /* cellelement::~cellelement */

class cellelement **cellelement::nextcelladdress ()
{
return &next;
} /* cellelement::nextcelladdress */

class cellelement *cellelement::nextcell ()
{
return next;
} /* cellelement::nextcell */

int cellelement::addtomap (coefficient coeff, int cellnumber)
{
	// increase map length
	maplength ++;
	// create new tables
	coefficient *newmapcoeff = new coefficient [maplength];
	int *newmapcell = new int [maplength];
	// mix the coefficients and cell numbers in ascending order
	int i = 0, j = 0, ok = 0;
	while (j < maplength)
	{
		if ((!ok) &&
			((j == maplength - 1) || (cellnumber < mapcell [i])))
		{
			newmapcoeff [j] = coeff;
			newmapcell [j] = cellnumber;
			ok = 1;
		}
		else
		{
			newmapcoeff [j] = mapcoeff [i];
			newmapcell [j] = mapcell [i];
			i ++;
		}
		j ++;
	}
	// replace old tables with the new ones
	delete [] mapcoeff;
	delete [] mapcell;
	mapcoeff = newmapcoeff;
	mapcell = newmapcell;
	// return the length of the new map value
	return maplength;
} /* cellelement::addtomap */


// --------------------------------------------------
// ------------------ CELL COMPLEX ------------------
// --------------------------------------------------

cellcomplex::cellcomplex ()
{
	for (int i = 0; i < MAXDIM; i ++)
	{
		numbers [i] = 0;
		cells [i] = NULL;
		next [i] = &cells [i];
		newnumbers [i] = NULL;
		newmaxnumbers [i] = 0;
	}
	hashsize = 0;
	hashused = 0;
	hashtable = NULL;
	return;
} /* cellcomplex::cellcomplex */

cellcomplex::~cellcomplex ()
{
	if (hashtable)
		delete [] hashtable;
	for (int i = 0; i < MAXDIM; i ++)
		// This produces too many recursive calls:
		// delete cells [i];
		// That's why the following should be used instead:
	{
		cellelement *cur = cells [i];
		while (cur)
		{
			cellelement *tmp = cur -> nextcell ();
			*(cur -> nextcelladdress ()) = NULL;
			delete cur;
			cur = tmp;
		}
	}
	return;
} /* cellcomplex::~cellcomplex */

cellelement *cellcomplex::findcell (cell *c, int dim)
{
	if (dim < 0)
		dim = c -> dimension ();
	if (dim >= MAXDIM)
		throw "Cell dimension too high. Recompile the prog!";
	int number = hashfind (c);
	if (number < 0)
		return NULL;
	else
		return hashtable [number];
//	cellelement *elem = cells [dim];
//	while (elem)
//		if (*(elem -> c) == *c)
//			return (elem);
//		else
//			elem = elem -> next;
//	return NULL;
} /* cellcomplex::findcell */

cellelement *cellcomplex::addcell (cell *c, int newcell)
{
	int dim = c -> dimension ();
	if (dim >= MAXDIM)
		throw "Cell dimension too high. Recompile the prog!";
	cellelement *elem;
	if (!newcell)
		if ((elem = findcell (c, dim)) != NULL)
			return elem;
	elem = new cellelement (++ (numbers [dim]), c);
	*(next [dim]) = elem;
	next [dim] = &(elem -> next);
	hashtableadd (-13, elem);
	return elem;
} /* cellcomplex::addcell */

int cellcomplex::makeboundaries (int dim)
{
	if ((dim >= MAXDIM) || (dim <= 0))
		return -1;
	int sum = 0;
	cellelement *elem = cells [dim];
	while (elem)
	{
		for (int axis = 0; axis < point::spacedimension (); axis ++)
		{
			if (elem -> c -> thick (axis))
			{
				for (int sign = -1; sign <= 1; sign += 2)
				{
					cell *b = new cell (elem -> c, axis,
						sign);
					if (findcell (b, dim - 1))
						delete b;
					else
					{
						addcell (b, 1);
						sum ++;
					}
				}
			}
		}
		elem = elem -> next;
	}
	return sum;
} /* cellcomplex::makeboundaries */

int cellcomplex::makeallboundaries ()
{
	int sum = 0;
	for (int dim = MAXDIM - 1; dim > 0; dim --)
		sum += makeboundaries (dim);
	return sum;
} /* cellcomplex::makeallboundaries */

int cellcomplex::makenewnumbers (cellcomplex &ignore)
{
	for (int dim = 0; dim < MAXDIM; dim ++)
	{
		cellelement *elem = cells [dim];
		newnumbers [dim] = new int [numbers [dim] + 1];
		if (!(newnumbers [dim]))
			throw "Cannot create new numbers.";
		newnumbers [dim] [0] = -13;
		while (elem)
		{
			if (ignore. findcell (elem -> c, dim))
				newnumbers [dim] [elem -> number] = 0;
			else
				newnumbers [dim] [elem -> number] =
					++ (newmaxnumbers [dim]);
			elem = elem -> next;
		}
	}
	return 0;
} /* cellcomplex::makenewnumbers */


// -------------------
// --- HASH TABLES ---
// -------------------

int cellcomplex::hashfind (cell *c)
// Returns the position of the cell element address in the hashing table.
// If there is NULL there, then the cell was not found.
// If returns -1, then the hashing table does not exist.
{
	if (!hashtable)
		return -1;
	unsigned pos = c -> hashkey (hashsize);
	unsigned add = 0;

	// find the position of the point in the hashing table
	while (hashtable [pos])
	{
		if (*(hashtable [pos] -> c) == *c)
			return (pos);
		if (!add)
			add = c -> hashadd (hashsize);
		pos = (pos + add) % hashsize;
	}

	return (pos);
} /* cellcomplex::hashfind */

static int isprime (unsigned n)
// Checks if the number is prime.
// Returns: 1 = Yes, 0 = No.
{
	unsigned i = 2;
	if (n < 2)
		return 0;
	while (i * i <= n)
		if (!(n % i ++))
			return 0;
	return 1;
} /* is prime */

static unsigned primenumber (unsigned n)
// Returns the smallest prime number
// greater than or equal to the given one.
{
	while (!isprime (n))
		n ++;
	return n;
} /* prime number */

void cellcomplex::inchashtable (void)
{
	// remove the old table
	if (hashtable)
		delete [] hashtable;

	// compute a new size
	int x = 0xFFFF;
	if ((x < 0) && (hashsize > 4000))
		throw "You should use a 32-bit compiler.";
	hashsize = primenumber (hashsize + hashsize + 400);

	// allocate a new table
	hashtable = new cellelement * [hashsize];
	if (!hashtable)
		throw "Not enough memory for a hashing table.";

	// fill this table with init values
	for (unsigned i = 0; i < hashsize; i ++)
		hashtable [i] = NULL;

	// rehash all the cells existing so far
	for (int dim = 0; dim < MAXDIM; dim ++)
	{
		cellelement *current = cells [dim];
		while (current)
		{
			hashtable [hashfind (current -> c)] = current;
			current = current -> next;
		}
	}
	// that's all
	return;
} /* cellcomplex::inchashtable */

void cellcomplex::hashtableadd (int pos, cellelement *c)
{
	if (hashsize * 3 / 4 <= hashused)
		inchashtable ();
	else
	{
		if (pos < 0)
			pos = hashfind (c -> c);
		hashtable [pos] = c;
		hashused ++;
	}
	return;
} /* cellcomplex::hashtableadd */


// ----------------------
// --- READ AND WRITE ---
// ----------------------

int cellcomplex::read (char *filename)
{
	textfile f;
	if (f. open (filename) < 0)
		return -1;
	return (read (f));
} /* cellcomplex::read */

int cellcomplex::write (char *filename)
{
	std::ofstream f (filename);
	if (!f)
		return -1;
	return (write (f));
} /* cellcomplex::write */

int cellcomplex::readwithmap (char *filename, cellcomplex &c)
{
	textfile f;
	if (f. open (filename) < 0)
		return -1;
	return (readwithmap (f, c));
} /* cellcomplex::readwithmap */

int cellcomplex::writemap (char *filename, cellcomplex *other)
{
	std::ofstream f (filename);
	if (!f)
		return -1;
	return (this -> writemap (f, other));
} /* cellcomplex::writemap */

int cellcomplex::writeprojectionmap (char *filename, cellcomplex &c,
	int ydim)
{
	std::ofstream f (filename);
	if (!f)
		return -1;
	return (this -> writeprojectionmap (f, c, ydim));
} /* cellcomplex::writemap */

int cellcomplex::read (textfile &in)
{
	do
	{
		// find the next cell;
		// ignore lines starting with "Arg" and "This"
		while ((in. checkchar () != EOF) &&
			(in. checkchar () != '['))
			switch (in. checkchar ())
			{
				case 'A':
				case 'a':
				case 'T':
				case 't':
				case 'D':
				case 'd':
				case 'G':
				case 'g':
					in. ignoreline ();
					break;
				default:
					in. readchar ();
					break;
			}
		// if the file has not run out,
		// read the cell and add it if needed
		if (in. checkchar () != EOF)
		{
			cell *c = new cell (in);
			if (!findcell (c))
				addcell (c, 1);
			else
				delete c;
		}
	} while (in. checkchar () != EOF);
	return 0;
} /* cellcomplex::read */

int cellcomplex::readwithmap (textfile &in, cellcomplex &c)
{
	// ignore the first line starting with "This"
	while ((in. checkchar () != 'A') && (in. checkchar () != 'a'))
		in. ignoreline ();

	while (in. checkchar () != EOF)
	{
		// ignore the line with "dimension"
		if ((in. checkchar () | 0x20) == 'd')
			in. ignoreline ();

		// read the phrase "argument"
		if (in. readphrase ("argument:") < 0)
			return -1;

		// read the argument cell
		cell *arg = new cell (in);

		// add this cell to the cell complex
		cellelement *elem = findcell (arg);
		if (!elem)
			elem = addcell (arg, 1);
		else
			delete arg;

		// read the phrase "value"
		if (in. readphrase ("value:") < 0)
			return -1;

		// read the value of the map
		if (in. checkchar () == '0')
			in. readchar ();
		while (((in. checkchar () | 0x20) != 'a') &&
			((in. checkchar () | 0x20) != 'd') &&
			(in. checkchar () != EOF))
		{
			// read the coefficient
			coefficient coeff = 1;
			if (in. checkchar () != '[')
			{
				coeff = (coefficient) in. readnumber ();
				if (in. checkchar () == '*')
					in. readchar ();
			}

			// read the cell
			if (in. checkchar () != '[')
			{
				sout << "ERROR in line " <<
					in. linenumber () <<
					": can't read the formula " <<
					"for the map value.\n";
			}
			cell *vcell = new cell (in);

			// find the cell and add it if necessary
			cellelement *velem = c. findcell (vcell);
			if (!velem)
				velem = c. addcell (vcell, 1);
			else
				delete vcell;

			// add an appropriate combination to the map
			elem -> addtomap (coeff, velem -> number);

			// read any signs indicating a sum of cells
			if (in. checkchar () == 'o')
				in. readchar ();
			if (in. checkchar () == 'o')
				in. readchar ();
			if (in. checkchar () == '+')
				in. readchar ();
		}
	}
	return 0;
} /* cellcomplex::readwithmap */

int cellcomplex::write (std::ostream &out)
{
	// compute the maximal dimension where there are any cells
	int maxdim = MAXDIM - 1;
	while ((maxdim > 0) &&
		!(newnumbers [maxdim] ? newmaxnumbers [maxdim] :
		numbers [maxdim]))
		maxdim --;

	// output header information
	out << "chaincomplex\n\n";
	out << "maxdimension = " << maxdim << '\n';

	// output each dimension separately
	out << "\ndimension 0: " << (newnumbers [0] ?
		newmaxnumbers [0] : numbers [0]) << '\n';
	for (int dim = 1; dim <= maxdim; dim ++)
	{
		out << "\ndimension " << dim << ": " <<
			(newnumbers [dim] ? newmaxnumbers [dim] :
			numbers [dim]) << '\n';
		if (!(newnumbers [dim - 1] ? newmaxnumbers [dim - 1] :
			numbers [dim - 1]))
			continue;
		cellelement *elem = cells [dim];
		if (newnumbers [dim])
			while (elem && !(newnumbers [dim] [elem -> number]))
				elem = elem -> next;
		while (elem)
		{
			out << "\t# " << (newnumbers [dim] ?
				newnumbers [dim] [elem -> number] :
				elem -> number) << " =";
			int nonzero = 0;
			int axescounter = 0;
			for (int axis = 0; axis < point::spacedimension ();
				axis ++)
			{
				if (elem -> c -> thick (axis))
				{
					for (int sign = -1; sign <= 1;
						sign += 2)
					{
						cell *b = new cell (elem ->
							c, axis, sign);
						int positive =
							axescounter & 1;
						if (sign == -1)
							positive =
								1 - positive;
						cellelement *belem =
							findcell (b,
							dim - 1);
						if (!belem)
							throw "FBC.";
						if (!(newnumbers [dim - 1]) ||
							newnumbers [dim - 1]
							[belem -> number])
						{
							nonzero = 1;
							if (positive)
								out << " +";
							else
								out << " -";
							if (!(newnumbers
								[dim - 1]))
								out << belem
								-> number;
							else
								out <<
								newnumbers
								[dim - 1]
								[belem ->
								number];
						}
						delete b;
					}
					axescounter ++;
				}
			}
			if (!nonzero)
				out << " 0";
			out << '\n';
			elem = elem -> next;
			if (newnumbers [dim])
				while (elem && !(newnumbers [dim] [elem ->
					number]))
					elem = elem -> next;
		}
	}

	return 0;
} /* cellcomplex::write */

int cellcomplex::writemap (std::ostream &out, cellcomplex *other)
{
	// output header information
	out << "chainmap\n";

	// output each dimension separately
	int lastdisplayed = -1;
	for (int dim = 0; dim < MAXDIM; dim ++)
	{
		int truenumbers = !other || !other -> newnumbers [dim];
		if (newnumbers [dim] ? newmaxnumbers [dim] : numbers [dim])
			while (lastdisplayed < dim)
				out << "\ndimension " <<
					(++ lastdisplayed) << '\n';
		cellelement *elem = cells [dim];
		if (newnumbers [dim])
			while (elem && !newnumbers [dim] [elem -> number])
				elem = elem -> next;
		while (elem)
		{
			out << "\t# " << (newnumbers [dim] ?
				newnumbers [dim] [elem -> number] :
				elem -> number) << " =";
			int nonzero = 0;
			for (int i = 0; i < elem -> maplength; i ++)
			{
				if (truenumbers || other -> newnumbers [dim]
					[elem -> mapcell [i]])
				{
					int m = (elem -> mapcoeff [i] > 0) ?
						(elem -> mapcoeff [i]) :
						-(elem -> mapcoeff [i]);
					while (m --)
					{
						out << ((elem ->
							mapcoeff [i] > 0) ?
							" +" : " -") <<
							(truenumbers ?
							elem -> mapcell [i] :
							other ->
							newnumbers [dim]
							[elem ->
							mapcell [i]]);
					}
					nonzero = 1;
				}
			}
			if (!nonzero)
				out << " 0";
			out << '\n';
			elem = elem -> next;
			if (newnumbers [dim])
				while (elem &&
					!newnumbers [dim] [elem -> number])
					elem = elem -> next;
		}
	}

	return 0;
} /* cellcomplex::writemap */

int cellcomplex::writeprojectionmap (std::ostream &out, cellcomplex &c, int ydim)
{
	// remember the dimension of space
	int fulldim = point::spacedimension ();
	int xdim = fulldim - ydim;

	// output header information
	out << "chainmap\n";

	// output each dimension separately
	int lastdisplayed = -1;
	for (int dim = 0; dim <= ydim; dim ++)
	{
		if (numbers [dim])
			while (lastdisplayed < dim)
				out << "\ndimension " <<
					(++ lastdisplayed) << '\n';
		cellelement *elem = cells [dim];
		while (elem)
		{
			out << "\t# " << elem -> number << " = ";
			int nonzero = 1;
			for (int i = 0; i < xdim; i ++)
				if (elem -> c -> thick (i))
					nonzero = 0;
			if (nonzero)
			{
				point::spacedimension (ydim);
				point p1 (elem -> c -> leftcoord () + xdim);
				point p2 (elem -> c -> rightcoord () + xdim);
				cell cl (p1, p2);
				out << (c. findcell (&cl) -> number);
				point::spacedimension (fulldim);
			}
			else
				out << "0";
			out << '\n';
			elem = elem -> next;
		}
	}

	return 0;
} /* cellcomplex::writeprojectionmap */

/// @}

