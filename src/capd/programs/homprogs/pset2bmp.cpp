/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file pset2bmp.cpp
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started on September 5, 1998. Last revision: April 24, 2008.


#include "capd/homology/config.h"
#include "capd/homology/bitmaps.h"
#include "capd/homology/colorpal.h"
#include "capd/homology/textfile.h"
#include "capd/homology/pointset.h"
#include "capd/homology/timeused.h"
#include "capd/homology/arg.h"

#include <exception>
#include <new>
#include <iostream>
#include <iomanip>
#include <fstream>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <ctime>

using namespace capd::homology;


// --------------------------------------------------
// -------------------- OVERTURE --------------------
// --------------------------------------------------

const char *title = "\
Pointset -> BitMaP. Copyright (C) 1997-2010 by Pawel Pilarczyk.\n\
This is free software. No warranty. Consult 'license.txt' for details.";

const char *helpinfo = "\
Call with: file1.cub [... fileN.cub] file.bmp [-xn] [-yn]\n\
This program reads a set of points and plots these points in a BMP file.\n\
Call with the name of the set of points to read and with the name of the\n\
BMP file to write. Multiple file names (at most 254) are allowed\n\
and will result in the sets of points plotted in different colors.\n\
Use the word 'skip' instead of a file name to skip the given color,\n\
unless the file 'skip' exists.\n\
Additional arguments:\n\
-xn - the number of the coordinate assigned to the X axis (default: 1),\n\
-yn - as above, but to the vertical axis Y (default: 2; range: 1 to dim),\n\
-zn - the number of the coordinate assigned to the Z axis (default: 3),\n\
-rn - the resolution of the bitmap picture in dots per inch (default: 0),\n\
-sn - the size of squares in pixels (default: 1),\n\
-pn - pause between the squares corresponding to the points (default: 0),\n\
-mn - margins left at each side of the picture in squares (default: 0),\n\
-gn - add a grid line every 'n' squares (default: 0 for no grid),\n\
--gray - use shades of gray instead of colors for plotting cubes,\n\
--bar[n] - add a color bar of size n at the bottom (no n => auto size),\n\
-fn - fill the background with the shade of gray: 0=white, 255=black,\n\
-lN - set the left corner of the picture (minimum X coordinate),\n\
-bN - set the bottom corner of the picture (minimum Y coordinate),\n\
-wN - set the minimal width of the plotting area in the picture in pixels,\n\
-hN - set the minimal height of the plotting area in pixels,\n\
-c - add the copyright message encoded in the source code,\n\
--slice N - plot a slice of a 3-dim picture with the given Z coordinate,\n\
--old - use the old-style color palette (for backwards compatibility),\n\
--help - display this brief help information only and exit.\n\
For more information ask the author at http://www.PawelPilarczyk.com/.";

#define MAXNAMES 254

#ifndef MAXDIM
#define MAXDIM 128
#endif


// --------------------------------------------------
// ------------------- COPYRIGHT --------------------
// --------------------------------------------------

// The copyright message defined as a bitmap: the X and Y coordinates
// of black pixels follow. Minimal coordinates must be (0,0),
// maximal coordinates are determined automatically.
// The last two numbers must be (-1,-1) to mark the end of the list.
const coordinate copyright [] = {11,0,15,0,16,0,26,0,27,0,28,0,77,0,78,0,
	143,0,144,0,11,1,17,1,29,1,79,1,145,1,1,2,2,2,3,2,7,2,8,2,11,2,
	12,2,13,2,17,2,21,2,24,2,27,2,28,2,29,2,31,2,34,2,36,2,37,2,43,2,
	44,2,45,2,50,2,51,2,52,2,53,2,56,2,57,2,61,2,62,2,66,2,73,2,74,2,
	75,2,79,2,86,2,93,2,94,2,95,2,98,2,102,2,106,2,107,2,108,2,111,2,
	116,2,122,2,124,2,127,2,128,2,129,2,131,2,135,2,136,2,139,2,140,2,
	141,2,142,2,145,2,149,2,152,2,0,3,4,3,6,3,9,3,11,3,14,3,17,3,18,3,
	21,3,24,3,26,3,29,3,31,3,34,3,36,3,42,3,46,3,50,3,55,3,58,3,60,3,
	63,3,66,3,73,3,76,3,79,3,80,3,86,3,92,3,95,3,98,3,102,3,105,3,
	111,3,116,3,122,3,124,3,126,3,129,3,131,3,134,3,137,3,139,3,145,3,
	146,3,149,3,151,3,0,4,6,4,9,4,11,4,14,4,16,4,19,4,21,4,24,4,26,4,
	29,4,31,4,34,4,36,4,41,4,44,4,45,4,47,4,51,4,55,4,58,4,60,4,63,4,
	67,4,73,4,76,4,78,4,81,4,86,4,93,4,94,4,95,4,97,4,99,4,101,4,103,4,
	105,4,106,4,107,4,108,4,111,4,116,4,122,4,124,4,127,4,128,4,129,4,
	131,4,134,4,140,4,141,4,144,4,147,4,149,4,150,4,0,5,6,5,9,5,11,5,
	14,5,16,5,19,5,21,5,24,5,26,5,29,5,31,5,34,5,36,5,41,5,43,5,47,5,
	52,5,55,5,58,5,60,5,63,5,67,5,73,5,76,5,78,5,81,5,86,5,87,5,88,5,
	89,5,95,5,97,5,100,5,103,5,105,5,108,5,110,5,111,5,116,5,117,5,
	118,5,119,5,122,5,124,5,129,5,131,5,134,5,137,5,142,5,144,5,147,5,
	149,5,151,5,0,6,7,6,8,6,11,6,12,6,13,6,16,6,19,6,21,6,22,6,24,6,
	27,6,28,6,29,6,31,6,32,6,33,6,36,6,37,6,41,6,44,6,45,6,47,6,53,6,
	55,6,58,6,60,6,63,6,67,6,73,6,74,6,75,6,78,6,81,6,86,6,90,6,92,6,
	93,6,94,6,97,6,100,6,103,6,106,6,107,6,111,6,112,6,116,6,120,6,
	122,6,124,6,126,6,127,6,128,6,131,6,132,6,135,6,136,6,139,6,140,6,
	141,6,142,6,144,6,147,6,149,6,152,6,0,7,4,7,31,7,36,7,42,7,46,7,
	50,7,53,7,55,7,58,7,60,7,63,7,68,7,73,7,86,7,90,7,111,7,116,7,
	120,7,124,7,149,7,1,8,2,8,3,8,24,8,31,8,43,8,44,8,45,8,51,8,52,8,
	56,8,57,8,61,8,62,8,65,8,66,8,67,8,68,8,73,8,86,8,87,8,88,8,89,8,
	111,8,116,8,117,8,118,8,119,8,122,8,124,8,149,8,-1,-1};

static int copywidth (void)
{
	static int width = 0;
	if (width > 0)
		return width;
	const coordinate *c = copyright;
	while (*c >= 0)
	{
		if (width < *c)
			width = *c;
		++ c;
		++ c;
	}
	return ++ width;
} /* copywidth */

static int copyheight (void)
{
	static int height = 0;
	if (height > 0)
		return height;
	const coordinate *c = copyright + 1;
	while (*c >= 0)
	{
		if (height < *c)
			height = *c;
		++ c;
		++ c;
	}
	return ++ height;
} /* copyheight */


// --------------------------------------------------
// -------------------- PSET2BMP --------------------
// --------------------------------------------------

int pointset2bitmap (char *names [], int namecount, char *outname, int x,
	int y, int z, int slice, int resolution,
	int size, int pause, int margin, int grid,
	bool gray, int colorbar, int fillshade,
	bool addcopyright, bool oldpalette,
	int req_left, int req_bottom, int req_width, int req_height)
// Note: x >= 0, y >= 0 (command-line parameters minus 1).
// Returns: 0 = Ok, -1 = error (shows msg).
{
	// set up the background fill color shade
	int32 fillcolor = (0xFF - fillshade) | ((0xFF - fillshade) << 8) |
		((0xFF - fillshade) << 16);

	// check if the values of parameters are sensible
	if (margin < 0)
		margin = 0;
	if ((x == y) || (x < 0) || (y < 0))
	{
		sout << "ERROR: Improper values of parameters: -x" <<
			(x + 1) << " -y" << (y + 1) << ".\n";
		throw "Unable to continue.";
	}
	if ((size <= 0) || (pause < 0))
	{
		sout << "ERROR: Improper values of parameters: -s" << size <<
			" -p" << pause << ".\n";
		throw "Unable to continue.";
	}

	// read a set of points from a file
	sout << "Reading selected coordinates of points to paint...\n";
	pointset p;
	p. dimension (2);
	int dim = 0;
	int_t firstpoint [MAXNAMES + 1];
	for (int i = 0; i < namecount; i ++)
	{
		sout << names [i] << ' ';
		firstpoint [i] = p. size ();
		std::ifstream f (names [i]);
		if (!f)
		{
			if (std::strcmp (names [i], "skip") &&
				std::strcmp (names [i], "SKIP"))
			{
				fileerror (names [i]);
			}
			continue;
		}
		coordinate point [MAXDIM], temp_point [2];
		ignorecomments (f);
		while (f. peek () != EOF)
		{
			while ((f. peek () != EOF) &&
				(closingparenthesis (f. peek ()) == EOF))
			{
				ignoreline (f);
				ignorecomments (f);
			}
			if (f. peek () == EOF)
				break;
			int current_dim = readcoordinates (f, point, MAXDIM);
			ignorecomments (f);
			if (current_dim >= MAXDIM)
				throw "Dimension of a point too high.";
			if (current_dim <= 0)
				throw "Can't read coordinates of a point.";
			if (dim != current_dim)
			{
				dim = current_dim;
				sout << "[dim " << dim << "] ";
				if ((dim <= x) || (dim <= y))
					throw "Dimension too small for the "
						"requested coordinates.";
			}
			temp_point [0] = point [x];
			temp_point [1] = point [y];
			if ((slice == 0xFFFFFFF) || (z < 0) || (z >= dim) ||
				(point [z] == slice))
			{
				p. add (temp_point);
			}
		}
		sout << '(' << (p. size () - firstpoint [i]) << ") ";
	}
	sout << p. size () << " points total.\n";
	firstpoint [namecount] = p. size ();

	if (p. empty ())
		throw "Can't read any point from the file.\n";

	sout << "There are " << p. size () << " pixels to paint.\n";

	// compute the scopes of the coordinates
	coordinate min [2], max [2];
	for (int_t pt = 0; pt < p. size (); pt ++)
	{
		coordinate *c = p [pt];
		if (!pt)
		{
			min [0] = max [0] = c [0];
			min [1] = max [1] = c [1];
		}
		else
		{
			if (min [0] > c [0])
				min [0] = c [0];
			if (max [0] < c [0])
				max [0] = c [0];
			if (min [1] > c [1])
				min [1] = c [1];
			if (max [1] < c [1])
				max [1] = c [1];
		}
	}
	sout << "The coordinates of the pixels vary in the following " <<
		"ranges:\n";
	for (int i = 0; i < 2; i ++)
	{
		sout << (i ? ", " : " (") << min [i] << " to " << max [i];
		min [i] -= (coordinate) margin;
		max [i] += (coordinate) margin;
	}
	sout << ")\n";

	// adjust the coordinate scopes if requested to
	if ((req_left != 0xFFFFFFF) && (min [0] > req_left))
	{
		sout << "Adjusting the left corner from " << min [0];
		min [0] = req_left;
		sout << " to " << min [0] << ".\n";
	}
	if ((req_bottom != 0xFFFFFFF) && (min [1] > req_bottom))
	{
		sout << "Adjusting the bottom corner from " << min [1];
		min [1] = req_bottom;
		sout << " to " << min [1] << ".\n";
	}
	if (max [0] - min [0] + 1 < req_width)
	{
		sout << "Adjusting the right corner from " << max [0];
		max [0] = min [0] + req_width - 1;
		sout << " to " << max [0] << ".\n";
	}
	if (max [1] - min [1] + 1 < req_height)
	{
		sout << "Adjusting the top corner from " << max [1];
		max [1] = min [1] + req_height - 1;
		sout << " to " << max [1] << ".\n";
	}

	// compute bitmap's width and height and check if they are appropriate
	int p_width = max [0] - min [0] + 1;
	int p_height = max [1] - min [1] + 1;
	int width = p_width * size + (p_width - 1) * pause;
	int marg_width = margin * (size + pause);
	int main_width = width - 2 * marg_width;
	int height = p_height * size + (p_height - 1) * pause;
//	int main_height = height;
	if ((p_width <= 0) || (p_height <= 0) || (width <= 0) ||
		(height <= 0))
		throw "The ranges of coordinates are too large.\n";
	int vshift = 0;

	// determine the width and height of color bars
	// and adjust the size of the bitmap accordingly
	if (namecount <= 1)
		colorbar = 0;
	int bar_width = colorbar;
	int bar_height = colorbar;
	if (colorbar < 0)
	{
		bar_width = main_width / namecount;
		if (bar_width <= 0)
			bar_width = 1;
		bar_height = bar_width;
	}
	// set the position of the color bar
	int bar_left = marg_width;
	int bar_bottom = 0;
	// adjust the width of the picture with the color bar
	if (bar_width * namecount > main_width + marg_width)
		width += bar_width * namecount - main_width - marg_width;
	// adjust the height of the picture to cover the color bar
	if (colorbar)
	{
		height += bar_height + 2;
		vshift += bar_height + 2;
	}

	// adjust the picture size to include the copyright message
	int c_left = 1, c_bottom = 1;
	if (addcopyright)
	{
		if (width < copywidth () + 2)
			width = copywidth () + 2;
		c_left = width - copywidth () - 1;
		if (!colorbar)
		{
			height += copyheight () + 2;
			vshift += copyheight () + 2;
		}
		if (colorbar &&
			(bar_left + bar_width * namecount + 1 > c_left))
		{
			height += copyheight () + 2;
			vshift += copyheight () + 2;
			c_bottom += bar_height;
		}
	}

	// create a bitmap image
	bmpfile bmp (height);
	// set the resolution of the image if desired
	if (resolution)
	{
		bmp. x_resolution = (int32) (resolution / 0.0254);
		bmp. y_resolution = (int32) (resolution / 0.0254);
	}
	// the vertical coordinate should go as in mathematics
	bmp. invertedpicture ();

	// prepare a 16-color palette to use if 2-15 sets are to plot
	int32 palette16 [] = {0x000000, 0x0000FF, 0xFF0000, 0x00FF00,
		0xFFFF00, 0xFF00FF, 0x00FFFF, 0x7F7F7F,
		0x007F00, 0x00007F, 0x7F0000, 0x7F7F00,
		0x7F007F, 0x007F7F, 0xCEB505, 0xFFFFFF};
	if (gray)
	{
		for (int i = 0; i < namecount; ++ i)
		{
			int shade = 0xFF * i / namecount;
			palette16 [i] = shade | (shade << 8) | (shade << 16);
		}
		for (int i = namecount; i < 16; ++ i)
			palette16 [i] = (i << 4) | (i << 12) || (i << 20);
		palette16 [14] = 0xCEB505;
		palette16 [15] = 0xFFFFFF;
	}
	palette16 [15] = fillcolor;

	// prepare a multi-color palette for more than 14 sets of points
	int32 palette256 [256];
	if (namecount >= 15)
	{
		if (gray)
		{
			for (int i = 0; i < namecount; ++ i)
			{
				int shade = 0xFF * i / namecount;
				palette256 [i] = shade | (shade << 8) |
					(shade << 16);
			}
		}
		else
		{
			int nshades = (namecount - 7 + 5) / 6 + 1;
			int palnamecount = (namecount + 5) / 6 * 6;
			std::cout << "debug: nshades = " << nshades << "\n";
			for (int i = 0; i < namecount; ++ i)
			{
				int color = 0;
				int shade = 0xFF;
				if (i > 6)
				{
					int n = (palnamecount - (i - 6)) / 6;
					shade = n * 0xFF / nshades;
				}
				int which = i ? ((i - 1) % 6 + 1) : 0;
				if (which & 0x01)
					color |= shade;
				if (which & 0x02)
					color |= shade << 8;
				if (which & 0x04)
					color |= shade << 16;
				palette256 [i] = color;
			}
		}
		for (int i = namecount; i < 256; ++ i)
			palette256 [i] = i | (i << 8) | (i << 16);
		palette256 [254] = 0xCEB505;
		palette256 [255] = 0xFFFFFF;
	}
	palette256 [255] = fillcolor;

	// replace the initial entries of the computed palette with the
	// new style palette colors unless requested to use the old ones
	// or plotting in shades of gray
	if (!oldpalette && !gray)
	{
		ColorPalette pal (namecount);
		int32 *palette = (namecount < 15) ? palette16 : palette256;
		for (int i = 0; i < namecount; ++ i)
			palette [i] = static_cast<int32> (pal [i]);
	}

	// create a disk file containing the picture
	if (namecount == 1)
		if (bmp. create (outname, width, height, 1) < 0)
			return -1;
		else;
	else if (namecount < 15)
		if (bmp. create (outname, width, height, 4, 16,
			palette16) < 0)
			return -1;
		else;
	else
		if (bmp. create (outname, width, height, 8, 256,
			palette256) < 0)
			return -1;

	// plot the points
	sout << "Plotting squares of size " << size << "x" << size <<
		" with the pause " << pause << " between them...\n";
	int s_p = size + pause;
	for (int i = 0; i < namecount; i ++)
	{
		for (int_t pt = firstpoint [i]; pt < firstpoint [i + 1]; pt ++)
		{
			coordinate *c = p [pt];
			int c_x = (c [0] - min [0]) * s_p;
			int c_y = (c [1] - min [1]) * s_p;
			for (int i_y = 0; i_y < size; i_y ++)
			{
				for (int i_x = 0; i_x < size; i_x ++)
					bmp. putpixel (c_x + i_x,
						vshift + c_y + i_y,
						i, namecount > 1);
			}
		}
	}

	if (grid)
	{
		sout << "Plotting the grid every " << grid <<
			" squares...\n";
		int gcolor = (namecount > 14) ? 254 :
			((namecount > 1) ? 14 : 0);
		for (int coord = 0; coord < 2; coord ++)
		{
			int line = min [coord];
			do
				line ++;
			while ((line <= max [coord]) && (line % grid));
			while ((line <= max [coord]) && !(line % grid))
			{
				int where = (line - min [coord]) *
					(size + pause) - (pause + 1) / 2;
				if (coord)
					bmp. drawsegment (0, where + vshift,
						marg_width + main_width - 1,
						where + vshift, 1, gcolor,
						namecount > 1);
				else
					bmp. drawsegment (where, vshift, where,
						height - 1, 1, gcolor,
						namecount > 1);
				do
					line ++;
				while ((line <= max [coord]) &&
					(line % grid));
			}
		}
	}

	if (colorbar)
	{
		for (int col = 0; col < namecount; ++ col)
		{
			int offset = bar_left + col * bar_width;
			for (int i = offset; i < offset + bar_width; ++ i)
			{
				for (int j = bar_bottom; j < bar_bottom +
					bar_height; ++ j)
				{
					bmp. putpixel (i, j, col,
						namecount > 1);
				}
			}
		}
	}

	if (addcopyright)
	{
		sout << "Adding the copyright notice...\n";
		int ccolor = 0;
		const coordinate *c = copyright;
		while (*c >= 0)
		{
			int x = c_left + *(c ++);
			int y = c_bottom + *(c ++);
			bmp. putpixel (x, y, ccolor, namecount > 1);
		}
	}
	
	sout << "Done!\n";
	return 0;
} /* pointset to bitmap */


// --------------------------------------------------
// ---------------------- MAIN ----------------------
// --------------------------------------------------

int main (int argc, char *argv [])
// Return: 0 = Ok, -1 = Error, 1 = Help displayed, 2 = Wrong arguments.
{
	// prepare user-configurable data
	char *names [MAXNAMES + 1], *outname = NULL;
	int namecount = 0;
	// numbers of coordinates
	int x = 1, y = 2, z = 3;
	// width and height of squares, and space between them
	int resolution = 0, size = 1, pause = 0, grid = 0, margin = 0;
	bool gray = false;
	int colorbar = 0;
	int fillshade = 0;
	bool addcopyright = false;
	bool oldpalette = false;
	int left = 0xFFFFFFF, bottom = 0xFFFFFFF, width = 0, height = 0;
	int slice = 0xFFFFFFF;

	// analyze the command line
	arguments a;
	arg (a, NULL, names, namecount, MAXNAMES + 1);
	arg (a, "x", x);
	arg (a, "y", y);
	arg (a, "y", z);
	arg (a, "s", size);
	arg (a, "r", resolution);
	arg (a, "p", pause);
	arg (a, "m", margin);
	arg (a, "g", grid);
	arg (a, "f", fillshade);
	arg (a, "l", left);
	arg (a, "b", bottom);
	arg (a, "w", width);
	arg (a, "h", height);
	arg (a, "-bar", colorbar, -1);
	arg (a, "-slice", slice);
	argswitch (a, "c", addcopyright, true);
	argswitch (a, "-gray", gray, true);
	argswitch (a, "-grey", gray, true);
	argswitch (a, "-old", oldpalette, true);
	arghelp (a);

	argstreamprepare (a);
	int argresult = a. analyze (argc, argv);
	argstreamset ();

	// show the program's main title
	if (argresult >= 0)
		sout << title << '\n';

	// extract the output file name
	if (namecount > 1)
		outname = names [-- namecount];

	// if something was incorrect, show an additional message and exit
	if (argresult < 0)
	{
		sout << "Call with '--help' for help.\n";
		return 2;
	}

	// if help requested or no filenames present, show help information
	if (!outname || (argresult > 0))
	{
		sout << helpinfo << '\n';
		return 1;
	}

	// try running the main function and catch an error message if thrown
	try
	{
		pointset2bitmap (names, namecount, outname,
			x - 1, y - 1, z - 1, slice,
			resolution, size, pause, margin, grid, gray,
			colorbar, fillshade, addcopyright, oldpalette,
			left, bottom, width, height);
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

