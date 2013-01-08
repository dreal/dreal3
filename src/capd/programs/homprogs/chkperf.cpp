/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file chkperf.cpp
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started on July 17, 1999. Last revision: November 23, 2002.

// Note on space wrapping (with no guarantee that it is correct):
// If you need to verify if a map on a wrapped space is almost perfect,
// repeat the map's values on one line of cubes beyond the domain.
// E.g. if the X space is identified every 100 cubes, repeat the 0'th row
// of the domain as the 100'th one and repeat the values of the map.
// The images of cells should not be in the quotient space.


#include "capd/homology/config.h"
#include "capd/homology/textfile.h"
#include "capd/homology/timeused.h"
#include "cells.h"
#include "capd/homology/arg.h"

#include <exception>
#include <new>
#include <iostream>
#include <fstream>
#include <ctime>
#include <cstdlib>

using namespace capd::homology;


// --------------------------------------------------
// -------------------- OVERTURE --------------------
// --------------------------------------------------

const char *title = "\
Check Perfect, ver. 0.01. Copyright (C) 1997-2010 by Pawel Pilarczyk.\n\
This is free software. No warranty. Consult 'license.txt' for details.";

const char *helpinfo = "\
Call with: filename.map (or -h for this brief help info).\n\
This program checks if a given cubical map is almost perfect.\n\
More precisely: For each vertex it checks if the intersection of all the\n\
cubes having this vertex as one of their corners is not empty.\n\
The input map must be in the format used in 'chmap' by Mazur and Szybowski:\n\
\tSpace Dimension: 3\n\
\t[(-214,-2,2) (-213,-1,3)] [(-111,-203,2) (-108,-200,3)]\n\
\t[(-214,-3,2) (-213,-2,3)] [(-110,-203,2) (-107,-200,3)]\n\
Lines not starting with \"Space Dimension\", \"[\" or \"(\" are ignored.\n\
For more information ask the author at http://www.PawelPilarczyk.com/.";


// --------------------------------------------------
// --------------------- CORNERS --------------------
// --------------------------------------------------
// This is a definition of a set of corners (points in R^n)
// which remember a list of cubical cells they were in and
// the intersection of these cell's images.

class corners
{
public:
	// the only constructor: the dimension should be given
	corners (int _dim);

	// destructor (free up all the allocated space)
	~corners ();

	// add all the corners of the cell to the structure;
	// the second paramter is this cell's image
	int addcellcorners (cell *c, cell *m);

	// get the number of all the corners in the data structure
	operator int ();

	// remember if the map was detected not to be almost perfect
	int notperfect;

protected:
	// add a corner with image of a cell containing it
	int addcorner (coordinate *c, cell *cc, cell *m);

	// show a message that the given intersection is empty
	void showempty (int nr, cell *cc);

	// the dimension of the space
	int dim;

	// the table of points' coordinates (each point uses
	// 'dim' elements of the table)
	coordinate *points;
	// number of points actually stored in the table
	int npoints;
	// maximal number of points to fit in the coordinate table
	int maxpoints;

	// intersections of cells corresponding to the corners
	cell **intersections;

	// chains of cells pointed to by the points:
	// cell pointers
	cell **cells;
	// numbers of the first cell corresponding to a point
	int *cellchains;
	// numbers of following cells, -1 means the end of a chain
	int *nextcell;
	// actual number of cell pointers stored in 'cells'
	int ncells;
	// maximal number of cells that may be stored at the moment
	int maxcells;

	// hashing table for the points: numbers of points, -1 = none
	int *hashtable;
	// the actual size of the hashing table
	unsigned hashsize;

	// two hashing keys (the second is non-zero)
	// generated for points of the current dimension
	unsigned hashkey (coordinate *c);
	unsigned hashadd (coordinate *c);

	// find position of point's number in the hash table;
	// return -1 if there is no haash table allocated yet;
	// if the value in the table is -1, the point is new
	int hashfind (coordinate *c);

	// check if two points are the same (the dimension is known)
	int thesame (coordinate *c1, coordinate *c2);

	// increase the hash table size at least twice + a constant
	void inchashtable (void);

	// add a point to the hash table at the desired position
	// computed with 'hashfind' (& call 'inchashtable'
	// if needed);
	// the point should be already added to the table
	// if it is new and the number of points should be increased
	void hashtableadd (int pos, int nr);
};

// --------------------------------------------------

corners::corners (int _dim): dim (_dim)
// Default constructor: check the dimension and reset all the values.
{
	if (dim < 1)
		throw "Incorrect dimension of corner points.";
	points = NULL;
	npoints = 0;
	maxpoints = 0;
	intersections = NULL;
	cells = NULL;
	cellchains = NULL;
	nextcell = NULL;
	ncells = 0;
	maxcells = 0;
	hashtable = NULL;
	hashsize = 0;
	notperfect = 0;
} /* corners::corners */

corners::~corners ()
// Destructor: free up all the space allocated so far for the structure.
{
	if (points)
	{
		delete [] points;
		points = NULL;
	}
	if (intersections)
	{
		for (int i = 0; i < npoints; i ++)
			if (intersections [i])
				delete intersections [i];
		delete [] intersections;
		intersections = NULL;
	}
	if (cells)
	{
		delete [] cells;
		cells = NULL;
	}
	if (cellchains)
	{
		delete [] cellchains;
		cellchains = NULL;
	}
	if (nextcell)
	{
		delete [] nextcell;
		nextcell = NULL;
	}
	if (hashtable)
	{
		delete [] hashtable;
		hashtable = NULL;
	}
} /* corners::~corners */

corners::operator int ()
// Projection onto the integer number: number of corners.
{
	return npoints;
} /* corners::operator int */


// - - - - - - - - - - - - - - -
// - - - - hasing tables - - - -
// - - - - - - - - - - - - - - -

int corners::thesame (coordinate *c1, coordinate *c2)
// Compare two points and return 1 iff they are the same.
{
	for (int i = 0; i < dim; i ++)
		if (c1 [i] != c2 [i])
			return 0;
	return 1;
} /* corners::thesame */

unsigned corners::hashkey (coordinate *c)
{
	unsigned key = 13;

	int x = 0xFFFF;
	for (int i = 0; i < dim; i ++)
		if (x < 0)
			key += c [i] << ((6 * i) % 14);
		else
			key += c [i] << ((6 * i) % 30);

	return (key % hashsize);
} /* corners::hashkey */

unsigned corners::hashadd (coordinate *c)
{
	unsigned add = 1313;
	for (int i = 0; i < dim; i ++)
		add += c [i] << ((3 * i + 1) % 13);
	return (add % (hashsize - 1) + 1);
} /* corners::hashadd */

int corners::hashfind (coordinate *c)
// Returns the position of the number in the hashing table.
// If there is -1 there, then the point was not found.
// If returns -1, then the hashing table does not exist.
{
	if (!hashtable)
		return -1;
	unsigned pos = hashkey (c);
	unsigned add = 0;

	// find the position of the point in the hashing table
	while (hashtable [pos] != -1)
	{
		if (thesame (points + dim * hashtable [pos], c))
			return (pos);
		if (!add)
			add = hashadd (c);
		pos = (pos + add) % hashsize;
	}

	return (pos);
} /* corners::hashfind */

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

void corners::inchashtable (void)
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
	hashtable = new int [hashsize];
	if (!hashtable)
		throw "Not enough memory for a hashing table.";
	// fill this table with init values
	for (unsigned i = 0; i < hashsize; i ++)
		hashtable [i] = -1;
	// rehash all the points existing so far
	coordinate *current = points;
	for (int n = 0; n < npoints; n ++)
	{
		hashtable [hashfind (current)] = n;
		current += dim;
	}
	// that's all
	return;
} /* corners::inchashtable */

void corners::hashtableadd (int pos, int nr)
{
	if (hashsize * 3 / 4 <= (unsigned) npoints)
		inchashtable ();
	else
		hashtable [pos] = nr;
	return;
} /* corners::hashtableadd */


// - - - - - - - - - - - - - - -
// - - -  say it is empty  - - -
// - - - - - - - - - - - - - - -

void corners::showempty (int nr, cell *cc)
{
	if (!notperfect)
	{
		sout << "*************************************\n";
		sout << "*** THE MAP IS NOT ALMOST PERFECT ***\n";
		sout << "*************************************\n";
		notperfect = 1;
	}

	sout << "At the point ";
	for (int i = 0; i < dim; i ++)
		sout << (i ? "," : "(") << (int) points [dim * nr + i];
	sout << ") the intersection of images " <<
		"of the following cells is empty: ";
	sout << (*cc);
	int c = cellchains [nr];
	while (c >= 0)
	{
		sout << " with " << *(cells [c]);
		c = nextcell [c];
	}
	sout << '\n';
	return;
} /* corners::showempty */


// - - - - - - - - - - - - - - -
// - - - -  add corners  - - - -
// - - - - - - - - - - - - - - -

static coordinate minimum (coordinate c1, coordinate c2)
{
	return ((c1 < c2) ? c1 : c2);
} /* minimum */

static coordinate maximum (coordinate c1, coordinate c2)
{
	return ((c1 > c2) ? c1 : c2);
} /* maximum */

int corners::addcorner (coordinate *c, cell *cc, cell *m)
{
	// prepare a variable to store current corner number
	int currentcorner;

	// try to find this corner in the hashing table
	int pos = hashfind (c);

	// if the table does not exist yet or the point was not found there:
	if ((pos < 0) || (hashtable [pos] < 0))
	{
		// if needed, increase the table of coordinates,
		// intersections and cell chain beginnings
		if (maxpoints <= npoints)
		{
			// test if the numbers will not be too large
			int x = 0xFFFF;
			if ((x < 0) && (dim * maxpoints > 4000))
				throw "Use a 32-bit compiler.";

			// increase the maximal number of points
			maxpoints = maxpoints + maxpoints + 400;

			// prepare new tables
			coordinate *newpoints = new coordinate
				[dim * maxpoints];
			cell **newintersections = new cell * [maxpoints];
			int *newcellchains = new int [maxpoints];

			// check if there was enough memory
			if (!newpoints || !newintersections ||
				!newcellchains)
				throw "Too little memory.";

			// copy points' coordinates
			coordinate *cold = points, *cnew = newpoints;
			for (int i = dim * npoints; i > 0; i --)
				* (cnew ++) = * (cold ++);
			// replace the old table with the new one
			if (points)
				delete [] points;
			points = newpoints;

			// copy intersections' pointers
			cell **iold = intersections;
			cell **inew = newintersections;
			for (int i = npoints; i > 0; i --)
				* (inew ++) = * (iold ++);
			// replace the old table with the new one
			if (intersections)
				delete [] intersections;
			intersections = newintersections;

			// copy cell chain beginnings
			int *ccold = cellchains, *ccnew = newcellchains;
			for (int i = npoints; i > 0; i --)
				* (ccnew ++) = * (ccold ++);
			// replace the old table with the new one
			delete [] cellchains;
			cellchains = newcellchains;
		}

		// write the point's coordinates to the common table
		coordinate *addr = points + dim * npoints;
		for (int i = 0; i < dim; i ++)
			addr [i] = c [i];

		// initialize the cell chain beginning number
		cellchains [npoints] = -1;

		// copy the whole cell as the intersection
		intersections [npoints] = new cell (m);

		// increase the number of points after adding the point
		currentcorner = npoints ++;

		// add the point to the hash table
		hashtableadd (pos, currentcorner);
	}
	// otherwise, if this corner already exists in the list:
	else
	{
		// extract current corner's number
		currentcorner = hashtable [pos];

		// intersect the image of the corner if it is not empty yet
		if (intersections [currentcorner])
		{
			// extract coordinate pointers
			coordinate *left = intersections [currentcorner] ->
				leftcoord ();
			coordinate *right = intersections [currentcorner] ->
				rightcoord ();
			coordinate *left1 = m -> leftcoord ();
			coordinate *right1 = m -> rightcoord ();

			// compute the intersection
			for (int i = 0; i < dim; i ++)
			{
				left [i] = maximum (left [i], left1 [i]);
				right [i] = minimum (right [i], right1 [i]);
			}

			// check if it is not an empty set
			for (int i = 0; i < dim; i ++)
				if (left [i] > right [i])
				{
					showempty (currentcorner, cc);
					delete intersections [currentcorner];
					intersections [currentcorner] = NULL;
					i = dim;
				}
		}
	}

	// and now add the pointer to the current cell to the chain:
	// first of all, increase the chain table if needed
	if (maxcells <= ncells)
	{
		// test if the numbers will not be too large
		int x = 0xFFFF;
		if ((x < 0) && (maxcells > 4000))
			throw "You'd better use a 32-bit compiler.";

		// prepare a new maximal number of cells
		maxcells = maxcells + maxcells + 400;

		// prepare new tables
		cell **newcells = new cell * [maxcells];
		int *newnext = new int [maxcells];
		if (!newcells || !newnext)
			throw "Not enough memory for cell chains.";

		// copy cells' tables
		for (int i = 0; i < ncells; i ++)
		{
			newcells [i] = cells [i];
			newnext [i] = nextcell [i];
		}

		// replace the old tables with the new ones
		delete [] cells;
		cells = newcells;
		delete [] nextcell;
		nextcell = newnext;
	}

	// add the current corner's cell to the chain of cells:
	nextcell [ncells] = cellchains [currentcorner];
	cells [ncells] = cc;
	cellchains [currentcorner] = ncells;
	ncells ++;

	return 0;
} /* corners::addcorner */

int corners::addcellcorners (cell *c, cell *m)
{
	// extract corners' coordinates
	coordinate *left = c -> leftcoord ();
	coordinate *right = c -> rightcoord ();

	// prepare a new table for a point and for a counter of corners
	coordinate *point = new coordinate [dim];
	int *counter = new int [dim];
	if (!point || !counter)
		throw "Not enough memory to analyze a cell.";

	// initialize corner counters
	for (int i = 0; i < dim; i ++)
		counter [i] = 0;

	// go through all the corners and add them
	int cur;
	do
	{
		// prepare a corner
		for (int i = 0; i < dim; i ++)
			point [i] = counter [i] ? left [i] : right [i];

		// add the corner
		addcorner (point, c, m);

		// prepare the next set of counters
		cur = 0;
		while (counter [cur] == 1)
			counter [cur ++] = 0;
		if (cur < dim)
			counter [cur] = 1;
	} while (cur < dim);

	// free up memory
	delete [] counter;
	delete [] point;

	// quit
	return 0;
} /* corners::addcellcorners */


// --------------------------------------------------
// -------------- CHECK ALMOST PERFECT --------------
// --------------------------------------------------

int checkalmostperfect (char *inname)
{
	// say what you are now going to do
	sout << "Reading a cubical map from '" << inname << "'...\n";

	// open the input file
	textfile in;
	if (in. open (inname) < 0)
	{
		sout << "ERROR: Can't open the input file.\n";
		return -1;
	}

	// read the dimension from the input file
	while (((in. checkchar () | 0x20) != 's') &&
		(in. checkchar () != EOF))
		in. ignoreline ();
	if ((in. readphrase ("space") < 0) ||
		(in. readphrase ("dimension") < 0))
		return -1;
	int dim = (int) in. readnumber (0, 1);
	if (dim <= 0)
	{
		sout << "ERROR: Incorrect dimension: " << dim << ".\n";
		return -1;
	}
	point::spacedimension (dim);
	sout << "* The space dimension is " << dim << ".\n";

	// ignore the introduction and go to the map definition area
	while ((in. checkchar () != '[') && (in. checkchar () != EOF))
		in. ignoreline ();

	// read the cubical map line by line
	int ncells = 0;
	cell **cells = NULL;
	int cellsready = 0;
	while ((in. checkchar () == '[') || (in. checkchar () == '('))
	{
		// allocate a bigger table if needed
		if (cellsready <= ncells)
		{
			int newsize = cellsready + cellsready + 400;
			if (newsize <= 0)
				throw "Oh, use a 32-bit compiler!";
			cell **newcells = new cell * [newsize];
			if (!newcells)
				throw "No memory to read the map.";
			for (int i = 0; i < cellsready; i ++)
				newcells [i] = cells [i];
			delete [] cells;
			cells = newcells;
			cellsready = newsize;
		}

		// read a new cell to the table
		cells [ncells ++] = new cell (in);

		if (!(ncells % 373))
			scon << (ncells >> 1) << "\r";
	}
	if (ncells & 1)
		throw "Odd number of cells read.";
	sout << "* " << (ncells >> 1) << " pairs of cells read.\n\n";

	// create the list of corners and check intersections
	sout << "Checking corners of each cell " <<
		"for \"almost perfectness\"...\n";
	corners c (dim);
	for (int n = 0; n < ncells; n ++)
	{
		c. addcellcorners (cells [n], cells [n + 1]);
		n ++;

		if (!((n >> 1) % 57))
			scon << (n >> 1) << "\r";
	}
	sout << "* " << (int) c << " corners of " << (ncells / 2) <<
		" cells checked.\n\n";

	// remove the table of cells
	for (int i = 0; i < ncells; i ++)
		delete cells [i];
	delete [] cells;

	// if the map is almost perfect, report it
	if (!c. notperfect)
		sout << "The map is almost perfect.\n\n";

	// say something kind at the end
	sout << "Hope you are satisfied with the results. Thank you.\n";

	return 0;
} /* check almost perfect */


// --------------------------------------------------
// ---------------------- MAIN ----------------------
// --------------------------------------------------

int main (int argc, char *argv [])
// Return: 0 = Ok, -1 = Error, 1 = Help displayed, 2 = Wrong arguments.
{
	char *inname = NULL;

	// interprete the command-line parameters
	arguments a;
	arg (a, NULL, inname);
	arghelp (a);

	argstreamprepare (a);
	int argresult = a. analyze (argc, argv);
	argstreamset ();

	// show the program's main title
	if (argresult >= 0)
		sout << title << '\n';

	// if something was incorrect, show an additional message and exit
	if (argresult < 0)
	{
		sout << "Call with '--help' for help.\n";
		return 2;
	}

	// if help requested or no filenames present, show help information
	if (!inname || (argresult > 0))
	{
		sout << helpinfo << '\n';
		return 1;
	}

	// try running the main function and catch an error message if thrown
	try
	{
		checkalmostperfect (inname);
		program_time = 1;
		return 0;
	}
	catch (const char *msg)
	{
		sout << "ERROR: " << msg << '\n';
		return -1;
	}
	catch (const std::exception &e)
	{
		sout << "ERROR: " << e. what () << '\n';
		return -1;
	}
	catch (...)
	{
		sout << "ABORT: An unknown error occurred.\n";
		return -1;
	}
} /* main */

/// @}

