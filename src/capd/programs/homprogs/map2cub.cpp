/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file map2cub.cpp
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started on October 27, 1999. Last revision: March 5, 2003.

// Former name(s) of this program: MAPGRAPH, MAP2PSET.


#include "capd/homology/config.h"
#include "capd/homology/textfile.h"
#include "capd/homology/pointset.h"
#include "capd/homology/cubisets.h"
#include "capd/homology/timeused.h"
#include "capd/homology/arg.h"

#include <exception>
#include <new>
#include <iostream>
#include <fstream>
#include <cstdlib>
#include <ctime>

using namespace capd::homology;


// --------------------------------------------------
// -------------------- OVERTURE --------------------
// --------------------------------------------------

const char *title = "\
MAP2CUB, ver. 0.03. Copyright (C) 1997-2010 by Pawel Pilarczyk.\n\
This is free software. No warranty. Consult 'license.txt' for details.";

const char *helpinfo = "\
Call with: f.map [-d domain.cub] [-i image.cub] [-g graph.cub]\n\
This program reads a combinatorial cubical multivalued map from the input\n\
text file and writes its domain, image and/or graph to text files.\n\
For the input map, each line should have the following form:\n\
either \"(-1,-42) -> {(1,12) (2,12) (2,13) (3,13)}\",\n\
or \"[(-1,-42,295) (0,-41,296)] [(-15,-46,149) (-13,-43,154)]\".\n\
In the first form, the domain and/or image elements can be cubical cells.\n\
Switches and additional arguments:\n\
-m n - multiply the coordinates of vertices of the output cell by n,\n\
-h - display this brief help information only and exit.\n\
For more information ask the author at http://www.PawelPilarczyk.com/.";


// --------------------------------------------------
// -------------------- MAP2CUB ---------------------
// --------------------------------------------------

int map2cub (const char *mapname, const char *domname, const char *imgname,
	const char *graphname, int /*multiply*/)
{
	// open the map file
	std::ifstream map (mapname);
	if (!map)
		fileerror (mapname);

	// open the domain file if applicable
	std::ofstream dom;
	if (domname)
	{
		dom. open (domname);
		dom << "; This is the domain of a multivalued cubical map\n";
		dom << "; stored in the file '" << mapname << "'.\n";
		if (!dom)
			fileerror (domname, "create");
	}

	// open the graph file if applicable
	std::ofstream graph;
	if (graphname)
	{
		graph. open (graphname);
		graph << "; This is the graph of a multivalued "
			"cubical map\n";
		graph << "; stored in the file '" << mapname << "'.\n";
		if (!graph)
			fileerror (graphname, "create");
	}

	std::ofstream img;
	if (imgname)
	{
		img. open (imgname);
		img << "; This is the image of a multivalued cubical map\n";
		img << "; stored in the file '" << mapname << "'.\n";
		if (!img)
			fileerror (imgname, "create");
	}

	// prepare an empty set of points to store the image of the map
	pointset imagecubes;
	cubicalcomplex imagecells;

	// remember the dimensions of spaces
	int domdim = 0, imgdim = 0;

	// prepare a counter
	int count = 0;

	// say what you are doing
	sout << "Reading a multivalued cubical map from '" << mapname <<
		"'...\n";
	if (domname)
		sout << "- and writing the domain of this map to '" <<
			domname << "'...\n";
	if (graphname)
		sout << "- and writing the graph of this map to '" <<
			graphname << "'...\n";

	// read the map and process it
	ignorecomments (map);
	while (1)
	{
		// read the next point or cell in the domain of the map
		coordinate left [2 * qcell::MaxDim];
		coordinate right [2 * qcell::MaxDim];
		int domtype;
		int dim = readcubeorcell (map, left, right, qcell::MaxDim,
			&domtype);
		if (!map || (dim <= 0))
			break;

		// verify the dimension of the cube or cell
		if (!domdim)
		{
			domdim = dim;
		//	if (domname)
		//		dom << "dimension " << domdim << '\n';
		}
		else if (dim != domdim)
			throw "Wrong dimension of a domain cube or cell.";

		// check if there is an arrow and read it
		bool setofvalues = false;
		while (map. peek () == '-')
		{
			map. get ();
			ignorecomments (map);
		}
		if (map. peek () == '>')
		{
			setofvalues = true;
			map. get ();
			ignorecomments (map);
		}

		// process the set of values if this is a multivalued map
		if (setofvalues)
		{
			// read the opening parenthesis of the list
			int closing = readparenthesis (map);
			ignorecomments (map);
			if (closing == EOF)
				throw "Unexpected end of file.";

			// go through the list of image cubes or cells
			while ((map. peek () != closing) &&
				(map. peek () != EOF))
			{
				// read the cube or cell
				int imgtype;
				int d = readcubeorcell (map, left + dim,
					right + dim, qcell::MaxDim, &imgtype);

				// check its dimension
				if (d <= 0)
					throw "Can't read an image point.";
				if (!imgdim)
				{
					imgdim = d;
					imagecubes. dimension (d);
				//	if (graphname)
				//		graph << "dimension " <<
				//			(domdim + imgdim) <<
				//			'\n';
				}
				else if (d != imgdim)
					throw "Wrong dim of image point.";

				// add this cube to suitable sets
				if (imgname && (imgtype == CUBE))
					imagecubes. add (left + dim);
				else if (imgname && (imgtype == CELL))
				{
				/*	img << '[';
					write (img, left + dim, d);
					img << ' ';
					write (img, right + dim, d);
					img << "]\n";
				*/	imagecells. add (qcell (left + dim,
						right + dim, d));
				}

				if (graphname && (imgtype == CUBE))
				{
					write (graph, left, dim + d);
					graph << '\n';
				}
				else if (graphname && (imgtype == CELL))
				{
					graph << '[';
					write (graph, left, dim + d);
					graph << ' ';
					write (graph, right, dim + d);
					graph << "]\n";
				}

				// move to the next cube
				ignorecomments (map);

				// ignore a comma if there is one
				if (map. peek () == ',')
				{
					map. get ();
					ignorecomments (map);
				}
			}

			// read the closing parenthesis
			if (map. get () != closing)
				throw "Closing parenthesis missing.";
			ignorecomments (map);

			// write the domain cube or cell if necessary
			if (domname && (domtype == CUBE))
			{
				write (dom, left, domdim);
				dom << '\n';
			}
			else if (domname && (domtype == CELL))
			{
				dom << '[';
				write (dom, left, domdim);
				dom << ' ';
				write (dom, right, domdim);
				dom << "]\n";
			}
		}

		// otherwise process the image cell
		else
		{
			// read the image cell
			int d = readcubeorcell (map, left + domdim,
				right + domdim, qcell::MaxDim);

			// check its dimension
			if (d <= 0)
				throw "Can't read an image cell.";
			if (!imgdim)
			{
				imgdim = d;
				imagecubes. dimension (imgdim);
			//	if (graphname)
			//		graph << "dimension " <<
			//			(domdim + imgdim) << '\n';
			}
			else if (imgdim != d)
				throw "Wrong dimension of an image cell.";

			// check if the domain cell is of full size
			for (int i = 0; i < domdim; i ++)
				if (left [i] + 1 != right [i])
					throw "Wrong size of the dom cell.";

			// check if the image cell coordinates are good
			for (int i = 0; i < imgdim; i ++)
				if (left [domdim + i] >= right [domdim + i])
					throw "Wrong size of the img cell.";

			// go through the list of image cubes
			rectangle rec (left, right, domdim + imgdim);
			const coordinate *c;
			while ((c = rec. get ()) != NULL)
			{
				// add this cube to suitable sets
				if (imgname)
					imagecubes. add (c + domdim);
				if (graphname)
				{
					write (graph, c, domdim + imgdim);
					graph << '\n';
				}
			}

			// write the domain cube if necessary
			if (domname)
			{
				write (dom, left, domdim);
				dom << '\n';
			}
		}

		// update the domain counter
		count ++;
		if (!(count % 4373))
			scon << std::setw (10) << count <<
				"\b\b\b\b\b\b\b\b\b\b";
	}

	sout << "A total of " << count << " assignments processed.\n";

	if (imgname && !imagecubes. empty ())
	{
		sout << "Saving the image (" << imagecubes. size () <<
			" cubes) to '" << imgname << "'...\n";
		img << imagecubes;
	}
	else if (imgname && !imagecells. empty ())
	{
		sout << "Saving the image (" << imagecells. size () <<
			" cells) to '" << imgname << "'...\n";
		img << imagecells;
	}

	sout << "That's all. Thank you.\n";
	return 0;
} /* map2cub */


// --------------------------------------------------
// ---------------------- MAIN ----------------------
// --------------------------------------------------

int main (int argc, char *argv [])
// Return: 0 = Ok, -1 = Error, 1 = Help displayed.
{
	// prepare user-configurable variables
	char *inname = NULL, *outname = NULL;
	char *domname = NULL, *imgname = NULL, *graphname = NULL;
	int multiply = 1;

	// interprete the command-line arguments
	arguments a;

	arg (a, NULL, inname);
	arg (a, NULL, outname);
	arg (a, "d", domname);
	arg (a, "i", imgname);
	arg (a, "g", graphname);
	arg (a, "m", multiply);
	arghelp (a);

	argstreamprepare (a);
	int argresult = a. analyze (argc, argv);
	argstreamset ();

	// show the program's main title
	if (argresult >= 0)
		sout << title << '\n';

	// make corrections to the variables read
	if (multiply <= 0)
	{
		sout << "The multiplication number must be positive.\n";
		argresult = -1;
	}
	if (outname && !graphname && !domname && !imgname)
	{
		graphname = outname;
		outname = NULL;
	}
	if (outname)
	{
		sout << "Too many file names. "
			"Use -d, -i or -g for each file separately.\n";
		argresult = -1;
	}

	// if there were errors, inform about it end exit
	if (argresult < 0)
	{
		sout << "Call with '--help' for help.\n";
		return -1;
	}

	// display help info if necessary
	if (argresult || !inname)
	{
		sout << helpinfo << '\n';
		return 1;
	}

	try
	{
		map2cub (inname, domname, imgname, graphname, multiply);
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

