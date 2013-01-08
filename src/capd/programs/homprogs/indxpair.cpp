/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file indxpair.cpp
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started on April 4, 2000. Last revision: October 22, 2003 (Sep 16, 2004).


#include "capd/homology/config.h"
#include "capd/homology/textfile.h"
#include "capd/homology/pointset.h"
#include "capd/homology/timeused.h"
#include "capd/homology/arg.h"

#include <exception>
#include <cstdlib>
#include <math.h>
#include <new>
#include <iostream>
#include <fstream>
#include <iomanip>

using namespace capd::homology;


// --------------------------------------------------
// -------------------- OVERTURE --------------------
// --------------------------------------------------

const char *title = "\
INDXPAIR, ver. 0.05. Copyright (C) 1997-2010 by Pawel Pilarczyk.\n\
This is free software. No warranty. Consult 'license.txt' for details.";

const char *helpinfo ="\
Call with: domain.cub function.map Q1.cub Q0.cub [-wn] [-f].\n\
This program performs Szymczak's algorithm for finding an index pair.\n\
Note: If space wrapping is enabled, only the image is wrapped while\n\
reading (the domain should be already wrapped in an appropriate way).\n\
Parameters:\n\
-wn - wrap space (use for each coordinate separately),\n\
-f  - create a full exit set, not just its intersection with d(N),\n\
--seq filename - save the sequence of removed cubes in a text file,\n\
-h  - display this brief help information only and exit.\n\
For more information ask the author at http://www.PawelPilarczyk.com/.";


// --------------------------------------------------
// ----------------- SMALL FUNCTIONS ----------------
// --------------------------------------------------
// Several small functions and definitions used further.

#define MAX_DIM 200

int write_pointset (char *filename, pointset *pset, const char *info)
// Write the set of points to a file with appropriate comments.
{
	sout << "Writing " << (info ? info : "pointset") <<
		" to '" << filename << "'... ";

	std::ofstream out (filename);
	if (!out)
	{
		sout << "Can't create the file for output.\n";
		return -1;
	}

	if (info)
		out << "; This is the set " << info << ".\n";
	out << *pset;
	out. close ();

	sout << "OK\n";
	return 0;
} /* write_pointset */


// --------------------------------------------------
// --------------------- MVMAP ----------------------
// --------------------------------------------------
// A class for using a multivalued cubical map.
// Note: the corresponding domain set of points
// must exist all the time this map exists.

class mapelement;
class mvmap;

class mapelement
{
public:
	// a default constructor of an empty map element
	mapelement ();

	// a destructor which would release memory
	~mapelement ();

	// read the image of a cube from a text file
	// and remove braces "{}" if needed;
	void readimage (textfile &f, pointset *pdom);

protected:

	// a pointer to the coordinates of the cube in the domain
	coordinate *dom;

	// a table of pointers to the coordinates of cubes
	// in the image
	coordinate **img;

	// number of cubes in the image
	int_t n;

	// declare a friendly class to allow access to protected data
	friend class mvmap;

}; /* class mapelement */

mapelement::mapelement ()
{
	dom = NULL;
	img = NULL;
	n = 0;
    return;
} /* mapelement::mapelement */

mapelement::~mapelement ()
{
	if (img)
		delete [] img;
	img = NULL;
	return;
} /* mapelement::~mapelement */

void mapelement::readimage (textfile &f, pointset *pdom)
{
	static coordinate *point = NULL;
	static int dim = -1;
	
	if (dim != pdom -> dimension ())
	{
		dim = pdom -> dimension ();
		if (point)
			delete [] point;
		point = new coordinate [dim];
		if (!point)
			throw "No memory to read image points.";
	}

	coordinate **table = NULL;
	int_t tabsize = 0;
	n = 0;

	// read the opening brace
	if (f. checkchar () == '{')
		f. readchar ();

	while (f. checkchar () == '(')
	{
		// read the point
		read (f, point, pdom -> dimension ());

		// check if this point belongs to the domain
		// and get its address
		coordinate *c = pdom -> getpoint (point);

		// add this point to the table only if it belongs
		// to the map domain
		if (c)
		{
			// increase the table if needed
			if (n >= tabsize)
			{
				int_t newsize = 100 + 2 * tabsize;
				if (newsize <= tabsize)
					throw "Use a 32bit compiler.";
				coordinate **newtable = new coordinate *
					[newsize];
				if (!newtable)
					throw "No mem to read image.";
				for (int_t i = 0; i < n; i ++)
					newtable [i] = table [i];
				delete [] table;
				table = newtable;
				tabsize = newsize;
			}

			// add the pointer to the table
			table [n ++] = c;
		}

		// read the comma after reading the point
		if (f. checkchar () == ',')
			f. readchar ();
	}

	// read the closing brace
	if (f. checkchar () == '}')
		f. readchar ();

	// copy the table to a smaller one
	if (n)
	{
		img = new coordinate * [n];
		if (!img)
			throw "Not enough memory to cut an image.";
		for (int_t i = 0; i < n; i ++)
			img [i] = table [i];
		delete [] table;
	}

	return;
} /* mapelement::readimage */


// --------------------------------------------------

class mvmap
{
public:
	// the only constructor: read the map from a file
	mvmap (char *filename, pointset &domain);

	// a destructor
	~mvmap ();

	// set 'allright' to 0 if there was an unsuccessful operation
	int allright;

	// extract the image of the given cube and return the number
	// of cubes in this image or -1 if the cube is not
	// in the domain
	int_t image (coordinate *c, coordinate ***table = NULL);

protected:
	// a table of map elements
	mapelement *map;

	// the size of the table of map elements
	unsigned n;

	// a pointer to the domain of the map
	pointset *dom;

	// find the map element corresponding to the given domain
	// cube; if this cube is not in the structure yet,
	// find the position at which it should be entered
	int_t findelement (coordinate *c);

}; /* class mvmap */

mvmap::mvmap (char *filename, pointset &domain)
{
	// set 'all right' to OK and change it later in case of an error
	allright = 1;

	// open a text file to read the map from
	sout << "Reading a map from '" << filename << "'... ";

	textfile f;
	if (f. open (filename) < 0)
	{
		sout << "Can't open the file for reading.\n";
		allright = 0;
		return;
	}

	// prepare a hashing table for the map
	dom = &domain;
	n = ceilprimenumber (dom -> size () + dom -> size () / 5);
	map = new mapelement [n];
	if (!map)
	{
		sout << "Can't allocate memory for the map table.\n";
		allright = 0;
		return;
	}

	// ignore the beginning of the file
	while ((f. checkchar () != '(') && (f. checkchar () != EOF))
		f. ignoreline ();

	coordinate *point = new coordinate [dom -> dimension ()];
	while (f. checkchar () == '(')
	{
		// read the point from the input file
		read (f, point, dom -> dimension ());

		// check if this point is in the domain of the map
		coordinate *c = dom -> getpoint (point);
		if (!c)
		{
			sout << "Line " << f. linenumber () <<
				": Cube not in the domain " <<
				"of the map.\n";
			allright = 0;
			return;
		}

		// ignore an arrow in the input file
		if (f. checkchar () == '-')
			f. readchar ();
		if (f. checkchar () == '>')
			f. readchar ();

		// make sure this point has not been defined yet
		int_t pos = findelement (point);
		if (map [pos]. dom)
		{
			sout << "Line " << f. linenumber () <<
				": Repeated definition " <<
				"of cube's image.\n";
			allright = 0;
			return;
		}

		// read the image of the cube from the input file
		map [pos]. dom = c;
		map [pos]. readimage (f, dom);
	}

	sout << "OK\n";

	delete [] point;
	return;
} /* mvmap::mvmap */

mvmap::~mvmap ()
{
	if (map)
		delete [] map;
	map = NULL;
} /* mvmap::~mvmap */

int_t mvmap::findelement (coordinate *c)
{
	int_t pos = pointhashkey (c, dom -> dimension (), n);
	int_t add = 0;

	while (map [pos]. dom)
	{
		if (thesame (map [pos]. dom, c, dom -> dimension ()))
			return (pos);
		if (!add)
			add = pointhashadd (c, dom -> dimension (), n);
		pos = (pos + add) % n;
	}

	return (pos);
} /* mvmap::findelement */

int_t mvmap::image (coordinate *c, coordinate ***table)
{
	int_t pos = findelement (c);
	if (!map [pos]. dom)
		return -1;
	if (table)
		*table = map [pos]. img;
	return map [pos]. n;
} /* mvmap::image */


// --------------------------------------------------
// ------------------- INDEX PAIR -------------------
// --------------------------------------------------
// The Szymczak's algorithm.

int invariant_part (pointset *&b, int delete_b, pointset *removed,
	mvmap &map, std::ofstream *seq = NULL)
// Compute the invariant part of the set 'b' minus 'removed' and replace
// the pointer 'b' with the new set. The set 'removed' contains points
// which do not belong to 'b'. This set will be 'delete'd.
// Note: 'removed' must be a subset of 'b'.
// The variable 'delete_b' says if the old set pointed by 'b' should be
// 'delete'd or not.
{
	// say what you are doing
	sout << "Computing the invariant part... ";

	// prepare a variable storing the information if the set has changed
	int changed;

	// if there is no set of removed points, create an empty one
	if (!removed)
		removed = new pointset;

	// intersect 'b' with its image and counterimage
	int seqcolor = 3;
	int stage = 1;
	do
	{
		if (seq)
			*seq << "C \"Computing INV - stage " << stage <<
				" (starting with " << b -> size () <<
				" squares)...\"\n";

		// show the size of 'b'
		sout << b -> size () << ' ';

		// reset the 'changed' variable to indicate no changes
		// made so far
		changed = 0;

		// prepare a pointset for the image of 'b' minus 'removed'
		// intersected with 'b' minus the 'removed' which changes
		// continually
		pointset *g = new pointset;

		// prepare the new version of the 'removed' pointset
		pointset *newremoved = new pointset;

		// take the first point in 'b' but not in the removed part
	//	int_t point = 0;
	//	while ((point < (int_t) *b) && removed -> check ((*b) [point]))
	//		point ++;

		// repeat for all points in 'b' \ 'removed'
		for (int_t point = 0; point < b -> size (); ++ point)
		{
			coordinate *c = (*b) [point];
			if (removed -> check (c))
				continue;

			// extract the image of this cube
			int empty_image_in_b = 1;
			coordinate **img;
			int_t n_img = map. image (c, &img);

			// add to 'g' cubes from the image of 'c'
			// which are in 'b' \ 'removed' \ 'newremoved'
			for (int_t i = 0; i < n_img; i ++)
				if (b -> check (img [i]) &&
					!removed -> check (img [i]) &&
					!newremoved -> check (img [i]))
				{
					if (seq && !g -> check (img [i]))
					{
						*seq << seqcolor << ' ';
						write (*seq, img [i],
							g -> dimension ());
						*seq << '\n';
					}
					g -> add (img [i]);
					empty_image_in_b = 0;
				}

			// if no cube from the image of 'c' fell
			// into 'b' \ 'removed', remove this cube
			// from 'b', i.e., add it to 'removed'
			// or to 'newremoved'
			if (empty_image_in_b)
			{
				if (g -> check (c))
					newremoved -> add (c);
				else
					removed -> add (c);
				changed = 1;

				if (seq)
				{
					*seq << "9 ";
					write (*seq, c, g -> dimension ());
					*seq << '\n';
				}
			}
	//
	//		// take the next point in 'b' \ 'removed'
	//		point ++;
	//		while ((point < (int_t) *b) &&
	//			removed -> check ((*b) [point]))
	//			point ++;
		}

		// replace the pair (b,removed) with (g,newremoved)
		if (!removed -> empty () || !newremoved -> empty () ||
			(b -> size () != g -> size ()))
		{
			// erase cubes which will be removed in a moment
			if (seq)
			{
				for (int_t i = 0; i < b -> size (); ++ i)
				{
					if (g -> check ((*b) [i]))
						continue;
					*seq << "9 ";
					write (*seq, (*b) [i],
						b -> dimension ());
					*seq << '\n';
				}
			}

			// if nothing was removed from 'g'
			// (otherwise already 'chg == 1')
			if (newremoved -> empty ())
				// if 'g' does not fully cover
				// 'b' \ 'removed'
				if (b -> size () != g -> size () + removed -> size ())
					changed = 1;
			if (delete_b)
				delete b;
			else
				delete_b = 1;
			b = g;
			delete removed;
			removed = newremoved;
		}

		// change the color the cubes are written to the seq. file
		if (seq)
		{
			seqcolor ++;
			if (seqcolor > 8)
				seqcolor = 2;
			*seq << "P \"INV stage " << (stage ++) <<
				" finished with " << b -> size () <<
				" squares (" << (changed ? "" : "not ") <<
				"changed)\"\n";
		}
	} while (changed);

	// delete the 'removed' set because it is now empty
	delete removed;

	// say how large this invariant part is
	sout << b -> size () << " points.\n";

	return 0;
} /* invariant part */

pointset *compute_exit_set (pointset *b, mvmap &map, bool fullexitset,
	std::ofstream *seq = NULL)
// Store in the set 'e' all the cubes from the image of 'b'
// which do not belong to 'b' but have at least one neighbor in 'b'.
{
	sout << "Computing the exit set... ";
	if (seq)
		*seq << "C \"Computing the exit set...\"\n";

	pointset *e = new pointset;
	for (int_t point = 0; point < b -> size (); ++ point)
	{
		coordinate **img;
		int_t n_img = map. image ((*b) [point], &img);
		for (int_t i = 0; i < n_img; i ++)
			if (!b -> check (img [i]) && !e -> check (img [i]) &&
				(fullexitset ||
				countneighbors (*b, img [i], INSIDE, 1)))
			{
				e -> add (img [i]);
				if (seq)
				{
					*seq << "1 ";
					write (*seq, img [i],
						b -> dimension ());
					*seq << '\n';
				}
			}
	}

	sout << e -> size () << " points.\n";
	if (seq)
		*seq << "P \"There are " << b -> size () << " squares "
			"in P1\\\\P0 and " << e -> size () << " squares "
			"in P0.\"\n";
	return e;
} /* compute exit set */

coordinate *find_boundary_element (pointset *b, pointset &domain)
// Find an element in 'b' which touches the boundary of 'domain'.
// Return NULL if not found.
{
	sout << "Finding a boundary element... ";

	int_t point = -1;
	while ((point = findboundarypoint (*b, point + 1)) >= 0)
		if (countneighbors (domain, (*b) [point], OUTSIDE, 1))
		{
			sout << "Found.\n";
			return (*b) [point];
		}
	sout << "Not found.\n";
	return NULL;
} /* find boundary element */

pointset *extract_connected_component (pointset *b, coordinate *c,
	std::ofstream *seq = NULL)
// Creates an empty pointset with 'new' and adds to it all the points
// which belong to the connected component of 'c' in 'b'.
{
	if (!b || !c)
		return NULL;

	// show a message what you are doing
	sout << "Extracting the entire connected component... ";

	// prepare the component containing only the given point at first
	pointset *component = new pointset;
	component -> add (c);
	if (seq)
	{
		*seq << "C \"Extracting a connected component...\"\n";
		*seq << "9 ";
		write (*seq, c, component -> dimension ());
		*seq << '\n';
	}

	// prepare a set of neighbors to iterate
	neighbors nb (NULL, b -> dimension (), b -> wrapspace ());

	for (int_t point = 0; point < component -> size (); ++ point)
	{
		// set the middle point for the neighbors
		nb. set ((*component) [point]);

		// go through all the neighbors of the point
		// and add each of them to the component if it belongs to 'b'
		coordinate *c;
		while ((c = nb. get ()) != NULL)
			if (b -> check (c))
			{
				component -> add (c);
				if (seq)
				{
					*seq << "9 ";
					write (*seq, c,
						component -> dimension ());
					*seq << '\n';
				}
			}
	}

	// say how large this component is
	sout << component -> size () << " points.\n";

	if (seq)
		*seq << "P \"A connected component of " <<
			component -> size () << " squares removed.\"\n";

	// return the component
	return component;
} /* extract connected component */

int index_pair (char *domname, char *mapname, char *out1name, char *out0name,
	bool fullexitset, coordinate *space_wrapping,
	const char *seqfilename)
{
	// open the sequence file name if requested to
	std::ofstream seq;
	if (seqfilename)
	{
		seq. open (seqfilename);
		if (!seq)
		{
			sout << "WARNING: Can't create the sequence file. "
				"Ignoring it.\n";
			seqfilename = NULL;
		}
		else
		seq << "D 0\n";
	}

	// read the domain of the map (i.e. the guess for an isol. nbhd)
	pointset domain (5000);
	{
		sout << "Reading a set of cubes from '" << domname <<
			"'... ";

		std::ifstream in (domname);
		if (!in)
		{
			sout << "Can't open the file for reading.";
			return -1;
		}
		in >> domain;
		domain. wrapspace (space_wrapping);

		sout << domain. size () << " points.\n";

		if (seqfilename)
		{
			seq << "C \"Reading the initial set...\"\n";
			for (int_t i = 0; i < domain. size (); i ++)
			{
				seq << "1 ";
				write (seq, domain [i],
					domain. dimension ());
				seq << '\n';
			}
			seq << "P \"The initial set contains " <<
				domain. size () << " squares.\"\n";
		}
	}
	if (domain. empty ())
	{
		sout << "The domain is empty.\n";
		return -1;
	}

	// check if there is no problem with wrapping this
	// domain (if wrapping)
	if (space_wrapping && (domain. dimension () >= MAX_DIM))
		throw "Too large domain dimension for wrapping.";

	// read the multivalued cubical map
	mvmap map (mapname, domain);
	if (!map. allright)
		return -1;

	// perform the Szymczak's algorithm
	pointset *b = &domain;
	pointset *removed = NULL;
	coordinate *c;
	do
	{
		// replace 'b' with the invariant part of 'b' \ 'removed'
		// note: the pointset allocated for 'removed' is swallowed
		invariant_part (b, b != &domain, removed, map,
			seqfilename ? &seq : NULL);

		// find in 'b' any element at the boundary of the domain
		c = find_boundary_element (b, domain);

		// extract the connected component containing this elem.
		if (c)
			removed = extract_connected_component (b, c,
				seqfilename ? &seq : NULL);

	} while (c);

	// if no boundary element could be found, output the index pair
	// and quit

	// write Q1\Q0
	if (write_pointset (out1name, b, "Q1\\Q0") < 0)
		return -1;

	// compute the exit set
	pointset *exit_set = compute_exit_set (b, map, fullexitset,
		seqfilename ? &seq : NULL);

	// free the allocated set of points
	if (b != &domain)
		delete b;

	// write the exit set Q0
	if (write_pointset (out0name, exit_set, "Q0") < 0)
		return -1;

	// free the other allocated set of points
	delete exit_set;

	// bye!
	return 0;

} /* index_pair */


// --------------------------------------------------
// ---------------------- MAIN ----------------------
// --------------------------------------------------

int main (int argc, char *argv [])
// Return: 0 = Ok, -1 = Error, 1 = Help displayed, 2 = Wrong arguments.
{
	char *domname = NULL, *mapname = NULL, *out1name = NULL,
		*out0name = NULL;
	coordinate space_wrapping [MAX_DIM];
	for (int d = 0; d < MAX_DIM; d ++)
		space_wrapping [d] = 0;
	int wrapped_space = 0;
	bool fullexitset = false;

	arguments a;
	arg (a, NULL, domname);
	arg (a, NULL, mapname);
	arg (a, NULL, out1name);
	arg (a, NULL, out0name);
	arg (a, "w", space_wrapping, wrapped_space, MAX_DIM);
	argswitch (a, "f", fullexitset, true);
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
	if (!out0name || (argresult > 0))
	{
		sout << helpinfo << '\n';
		return 1;
	}

	// try running the main function and catch an error message if thrown
	try
	{
		index_pair (domname, mapname, out1name, out0name,
			fullexitset, (wrapped_space ? space_wrapping :
			(coordinate *) NULL), arg_seqfilename);
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

