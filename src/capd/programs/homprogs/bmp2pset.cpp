/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file bmp2pset.cpp
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started on June 15, 1998. Last revision: May 25, 2007.

// Former name(s) of this program: bmpcubes.cpp.


#include "capd/homology/config.h"
#include "capd/homology/bitmaps.h"
#include "capd/homology/textfile.h"
#include "capd/homology/timeused.h"
#include "capd/homology/arg.h"

#include <exception>
#include <new>
#include <iostream>
#include <fstream>
#include <iomanip>
#include <stdio.h>
#include <cstdlib>

using namespace capd::homology;


// --------------------------------------------------
// -------------------- OVERTURE --------------------
// --------------------------------------------------

const char *title = "\
BMP2PSET, ver. 0.04, Copyright (C) 1997-2010 by Pawel Pilarczyk.\n\
This is free software. No warranty. Consult 'license.txt' for details.";

const char *helpinfo = "\
Call with: file.bmp file1.cub [file2.cub file3.cub ...]\n\
This program creates a list of points stored in a gray-scale BMP picture\n\
(color or b/w images are converted automatically to gray scale).\n\
The thresholding levels are determined automatically, unless the -t option\n\
is used. The first set contains the darkest pixels, and the last one -\n\
the brightest, but still not white. The output data format is as follows:\n\
\"dimension 2 <newline> (x1, y1) <newline> (x2, y2) <newline>...\",\n\
with a few lines of comments at the beginning (preceded with ';').\n\
Additional arguments:\n\
-tn - threshold gray level (can be repeated; auto-determined if none),\n\
-xX - assume the leftmost pixel's coordinate is X (default: 0),\n\
-yY - assume the lowest pixel's coordinate is Y (default: 0),\n\
-i  - include the previous sets in the next ones,\n\
-r  - reverse the graylevel scale (extract bright pixels, not dark),\n\
-mn/-Mn - color range in hexadecimal (deprecated arguments),\n\
-h  - show only this help information and exit.\n\
For more information ask the author at http://www.PawelPilarczyk.com/.";


// --------------------------------------------------
// --------------------- TOOLS ----------------------
// --------------------------------------------------

/// Reads a hexadecimal long integer from a text string.
static long readlonghex (char *longhex)
{
	long num = 0;

	while (1)
	{
		switch (*longhex)
		{
			case 'a':
			case 'b':
			case 'c':
			case 'd':
			case 'e':
			case 'f':
				num <<= 4;
				num += (*longhex) - 'a' + 0x0A;
				break;
			case 'A':
			case 'B':
			case 'C':
			case 'D':
			case 'E':
			case 'F':
				num <<= 4;
				num += (*longhex) - 'A' + 0x0A;
				break;
			case 'x':
			case 'X':
				break;
			case '0':
			case '1':
			case '2':
			case '3':
			case '4':
			case '5':
			case '6':
			case '7':
			case '8':
			case '9':
				num <<= 4;
				num += (*longhex) - '0';
				break;
			default:
				return num;
		}
	++ longhex;
	}
} /* readlonghex */

/// Converts an RGB color to gray level.
inline int long2gray (long color)
{
	return (77 * ((color & 0xFF0000) >> 16) +
		154 * ((color & 0xFF00) >> 8) + 25 * (color & 0xFF)) >> 8;
} /* long2gray */

/// Sort the array and eliminate duplicate entries.
void sortunique (int *tab, int &n)
{
	for (int i = 0; i < n; ++ i)
	{
		for (int j = i + 1; j < n; ++ j)
		{
			if (tab [i] > tab [j])
			{
				int tmp = tab [i];
				tab [i] = tab [j];
				tab [j] = tmp;
			}
		}
		for (int j = i + 1; j < n; ++ j)
		{
			if (tab [i] == tab [j])
			{
				tab [j] = tab [n - 1];
				-- n;
			}
		}
	}
	return;
} /* sortunique */

void showtable (const int *tab, int n)
{
	sout << "[";
	for (int i = 0; i < n; ++ i)
	{
		if (i)
			sout << ", ";
		sout << tab [i];
	}
	sout << "]\n";
	return;
} /* showtable */

// --------------------------------------------------
// -------------------- BMP2PSET --------------------
// --------------------------------------------------

/// Creates text files with lists of pixels stored in the BMP file.
/// Returns: 0 = Ok, -1 = Error (and show the error message).
int bmp2pset (char *bmpname, char **outnames, int countnames,
	int *thresholds, int countthresholds, int x0, int y0,
	bool inclusive, bool reversegray)
{
	// say what you are doing
	sout << "Analyzing the bitmap file '" << bmpname << "'...\n";

	// prepare a bitmap file with the vertical axis like in mathematics
	bmpfile bmp;
	bmp. invertedpicture ();

	// open the bitmap file
	if (bmp. open (bmpname) < 0)
		return -1;

	// sort the thresholds obtained from the user
	sortunique (thresholds, countthresholds);

	// determine thresholds unless they are already given
	if (!countthresholds)
	{
		// prepare an array for counting pixels
		int graycount [256];
		for (int i = 0; i < 256; ++ i)
			graycount [i] = 0;

		// scan the picture and count the number of pixels
		// at each level of gray
		for (int y = 0; y < bmp. picture_height (); y ++)
		{
			for (int x = 0; x < bmp. picture_width (); x ++)
			{
				int gray = long2gray (bmp. getpixel (x, y));
				++ graycount [gray];
			}
		}

		// count the total number of pixels
		int allcount = 0;
		for (int i = 0; i < 256; ++ i)
			allcount += graycount [i];

		// count the number of nonempty sets
		int setcount = 0;
		for (int i = 0; i < 256; ++ i)
		{
			if (graycount [i])
				++ setcount;
		}

		// calculate the cumulative numbers of pixels
	//	for (int i = 256; i > 0; -- i)
	//		graycount [i - 1] += graycount [i];

		// determine the maximal set of thresholding levels
		int counts [256];
		for (int i = 0; i < 256; ++ i)
		{
			if (graycount [i])
			{
				counts [countthresholds] = graycount [i];
				thresholds [countthresholds] = i;
				++ countthresholds;
			}
		}

		// reduce the thresholding levels if necessary
		if (countthresholds > countnames + 1)
		{
			// define the borders in such a way that the first
			// intervals have one section, and the last
			// interval gets the remaining portion
			int borders [256];
			int bcounts [256];
			int nborders = countnames + 1;
			for (int i = 0; i < nborders; ++ i)
			{
				borders [i] = i;
				bcounts [i] = counts [i];
			}
			for (int i = nborders; i < countthresholds; ++ i)
				bcounts [nborders - 1] += counts [i];

			// move the borders if a more balanced thresholding
			// can be easily obtained
			while (1)
			{
				bool found = false;
				for (int i = 1; i < nborders; ++ i)
				{
					if (borders [i] + 1 >= countthresholds)
						continue;
					if ((i < nborders) && (borders [i] ==
						borders [i + 1] - 1))
						continue;
					int rightcount = bcounts [i] -
						counts [borders [i]];
					int leftcount = bcounts [i - 1] +
						counts [borders [i]];
					if (leftcount > rightcount)
						continue;
					bcounts [i] = rightcount;
					bcounts [i - 1] = leftcount;
					++ borders [i];
					found = true;
				}
				if (!found)
					break;
			}

			// set the new thresholds according to the borders
			for (int i = 0; i < nborders; ++ i)
				thresholds [i] = thresholds [borders [i]];
			countthresholds = nborders;
		}

		// add the other border threshold if necessary
		if (reversegray)
		{
			for (int i = 1; i < countthresholds; ++ i)
				thresholds [i - 1] = thresholds [i];
			thresholds [countthresholds - 1] = 256;
		}
	}

	// if the lower threshold is not set to 0, then add it if relevant
	if (countthresholds && (thresholds [0] > 0) &&
		(countthresholds < countnames + 2) &&
		((countthresholds < countnames + 1) || !reversegray))
	{
		for (int i = countthresholds; i > 0; -- i)
			thresholds [i] = thresholds [i - 1];
		thresholds [0] = 0;
		++ countthresholds;
	}

	// if the upper threshold is not set to 256, then add it if relevant
	if (countthresholds && (thresholds [countthresholds - 1] < 256) &&
		(countthresholds < countnames + 2) &&
		((countthresholds < countnames + 1) || reversegray))
	{
		thresholds [countthresholds ++] = 256;
	}

	// warn if there are too few thresholds available
	if (countthresholds < countnames + 1)
	{
		countnames = countthresholds - 1;
		sout << "WARNING: Too few thresholds given. Only " <<
			countnames << " files will be saved.\n";
	}

	// warn if there are too many thresholds given
	if (countthresholds > countnames + 1)
	{
		sout << "WARNING: There are too many thresholds (" <<
			countthresholds << "). Only " <<
			(countnames + 1) << " will be used.\n";
	}

	// save the files
	for (int i = 0; i < countnames; ++ i)
	{
		// determine the gray shade range to extract
		int mincolor, maxcolor;
		if (reversegray)
		{
			int maxindex = countthresholds - 1;
			mincolor = thresholds [maxindex - i - 1];
			maxcolor = inclusive ? thresholds [maxindex] :
				thresholds [maxindex - i];
		}
		else
		{
			mincolor = inclusive ? thresholds [0] :
				thresholds [i];
			maxcolor = thresholds [i + 1];
		}

		// say which file is being saved
		sout << "Saving '" << outnames [i] << "' (" <<
			mincolor << "-" << (maxcolor - 1) << ")... ";

		// open the output stream to write the list of squares to
		std::ofstream out (outnames [i]);
		if (!out)
			fileerror (outnames [i], "create");

		// write the intro at the beginning of the output file
		out << "; This is a list of pixels generated by BMP2PSET "
			"from '" << bmpname << ".\n" <<
			"; Gray level scope: from " << mincolor <<
			" to " << (maxcolor - 1) << "." << "\n" <<
			"dimension 2\n";

		// count the points extracted
		int count = 0;

		// scan the picture and produce the list of hypercubes
		for (int y = 0; y < bmp. picture_height (); y ++)
		{
			for (int x = 0; x < bmp. picture_width (); x ++)
			{
				int p = long2gray (bmp. getpixel (x, y));
				if ((p >= mincolor) && (p < maxcolor))
				{
					out << "(" << (x + x0) << "," <<
							(y + y0) << ")\n";
					++ count;
				}
			}
		}
		out << "; " << count << " pixels.\n\n";

		// say the statistics
		sout << count << " pixels.\n";
	}

	return 0;
} /* bmp2pset */


// --------------------------------------------------
// ---------------------- MAIN ----------------------
// --------------------------------------------------

int main (int argc, char **argv)
// Return: 0 = Ok, -1 = Error, 1 = Help displayed, 2 = Wrong arguments.
{
	char *bmpname = 0;
	char *outnames [256];
	int countnames = 0;
	int thresholds [257];
	int countthresholds = 0;
	long mincolor = 0, maxcolor = 0x7F7F7FL;
	char *txtmin = 0, *txtmax = 0;
	int x0 = 0, y0 = 0;
	bool inclusive = false;
	bool reversegray = false;

	// analyze the command line arguments
	arguments a;
	arg (a, 0, bmpname);
	arg (a, 0, outnames, countnames, 256);
	arg (a, "t", thresholds, countthresholds, 257);
	arg (a, "m", txtmin);
	arg (a, "M", txtmax);
	arg (a, "x", x0);
	arg (a, "y", y0);
	argswitch (a, "i", inclusive, true);
	argswitch (a, "r", reversegray, true);
	arghelp (a);

	argstreamprepare (a);
	int argresult = a. analyze (argc, argv);
	argstreamset ();

	// show the program's main title
	if (argresult >= 0)
		sout << title << '\n';

	// extract the color scope
	if (txtmin || txtmax)
	{
		if (txtmin)
			mincolor = readlonghex (txtmin);
		if (txtmax)
			maxcolor = readlonghex (txtmax);
		thresholds [0] = long2gray (mincolor);
		thresholds [1] = long2gray (maxcolor);
		countthresholds = 2;
	}

	// if something was incorrect, show an additional message and exit
	if (argresult < 0)
	{
		sout << "Call with '--help' for help.\n";
		return 2;
	}

	// if help requested or no filenames present, show help information
	if (!bmpname || !countnames || (argresult > 0))
	{
		sout << helpinfo << '\n';
		return 1;
	}

	// try running the main function and catch an error message if thrown
	try
	{
		bmp2pset (bmpname, outnames, countnames,
			thresholds, countthresholds, x0, y0,
			inclusive, reversegray);
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

