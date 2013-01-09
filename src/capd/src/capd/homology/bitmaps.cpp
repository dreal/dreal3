/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file bitmaps.cpp
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started in June 1998. Last revision: March 15, 2010.


#include "capd/homology/config.h"
#include "capd/homology/textfile.h"
#include "capd/homology/bitmaps.h"

#include <iostream>
#include <iomanip>
#include <stdio.h>
#include <cstdlib>

namespace capd {
namespace homology {


// --------------------------------------------------
// -------------- Auxiliary functions ---------------
// --------------------------------------------------

static void long2char (char *c, int32 n)
{
	c [0] = (char) (n & 0xFFl);
	c [1] = (char) ((n & 0xFF00l) >> 8);
	c [2] = (char) ((n & 0xFF0000l) >> 16);
	c [3] = (char) ((n & 0xFF000000l) >> 24);
	return;
} /* long2char */

static void short2char (char *c, int16 n)
{
	c [0] = (char) (n & 0xFFl);
	c [1] = (char) ((n & 0xFF00l) >> 8);
	return;
} /* short2char */

static int32 char2long (char *c)
{
	unsigned char *d = (unsigned char *) c;
	int32 n = d [0];
	n |= (int32) (d [1]) << 8;
	n |= (int32) (d [2]) << 16;
	n |= (int32) (d [3]) << 24;
	return n;
} /* char2long */

static short char2short (char *c)
{
	unsigned char *d = (unsigned char *) c;
	short n = d [0];
	n |= (short) (d [1] << 8);
	return n;
} /* char2short */


// --------------------------------------------------
// -------------------- bmpfile ---------------------
// --------------------------------------------------

static void mem_set (unsigned char *buf, unsigned char value, int howmany)
{
	while (howmany --)
		* (buf ++) = value;
	return;
}

int bmpfile::writerow (int row)
{
	if (defined)
		defined [rownumber [row] >> 3] |= (unsigned char)
			(0x01 << (rownumber [row] & 0x07));
	int32 writeoffset = (int32) bmpstart +
		(int32) (rownumber [row]) * (int32) rowlength;
	if (writeoffset <= firstundefinedbyte)
		fseek (fbmp, writeoffset, SEEK_SET);
	//	fbmp. seekp (writeoffset, ios::beg);
	else
	{
		fseek (fbmp, firstundefinedbyte, SEEK_SET);
	//	fbmp. seekp (firstundefinedbyte, ios::beg);
		int32 bytestowrite = writeoffset - firstundefinedbyte;
		while (bytestowrite --)
			fputc (fillbyte, fbmp);
		//	fbmp. put (fillbyte);
	}
	fwrite (rowbuf [row], rowlength, 1, fbmp);
//	fbmp. write (rowbuf [row], rowlength);
	changed [row] = 0;
	rows_written ++;

	if (ferror (fbmp))
//	if (!fbmp)
		return -1;

	if (firstundefinedbyte < writeoffset + (int32) rowlength)
		firstundefinedbyte = writeoffset + rowlength;

	if (firstundefinedrow <= rownumber [row])
		firstundefinedrow = rownumber [row] + 1;

	return 0;
} /* bmpfile::writerow */

int bmpfile::readrow (int row)
{
	fseek (fbmp, bmpstart + (int32) (rownumber [row]) *
		(int32) rowlength, SEEK_SET);
//	fbmp. seekg (bmpstart + (int32) (rownumber [row]) *
//		(int32) rowlength, ios::beg);
	if (fread (rowbuf [row], rowlength, 1, fbmp) != 1)
		return -1;;
//	fbmp. read (rowbuf [row], rowlength);
	rows_read ++;

	if (ferror (fbmp))
//	if (!fbmp)
		return -1;
	else
		return 0;
} /* bmpfile::readrow */

unsigned char *bmpfile::getrow (int row)
{
	if (!rowbuf)
		return NULL;
	getpixel (0, row);
	if (!inverted)
		row = height - 1 - row;
	for (int i = 0; i < rows; i ++)
		if (rownumber [i] == row)
			return rowbuf [i];
	if (rowbuf)
		throw "Row not found.";
	return NULL;
} /* bmpfile::getrow */

unsigned bmpfile::getrowlength () const
{
	return rowlength;
} /* bmpfile::getrowlength */

bmpfile::bmpfile (int _rows)
{
	rows = _rows;
	if (rows < 1)
		rows = 1;
	header = NULL;
	palette = NULL;
	palette_allocated = false;
	defined = NULL;
	fillbyte = 0xFF;
	rowbuf = new unsigned char * [rows];
	rownumber = new int [rows];
	changed = new char [rows];
	if (rowbuf && rownumber && changed)
	{
		for (int row = 0; row < rows; row ++)
		{
			rowbuf [row] = NULL;
			rownumber [row] = -1;
			changed [row] = 0;
		}
	}
	inverted = 0;
	current = 0;
	width = 0;
	height = 0;
	firstundefinedrow = 0;
	firstundefinedbyte = 0;
	fileinuse = 0;
	x_resolution = 0;
	y_resolution = 0;
	rows_read = 0;
	rows_written = 0;
	return;
} /* bmpfile::bmpfile */

void bmpfile::flush (void)
{
	if (!(fileinuse & 2))
		return;
	if (rownumber && rowbuf && changed)
	{
		for (int row = 0; row < rows; row ++)
			if (rowbuf [row] && changed [row])
				writerow (row);
	}
	fflush (fbmp);
//	fbmp. flush ();
	return;
} /* bmpfile::flush */

bmpfile::~bmpfile ()
{
	// write any rows still waiting in the memory
	flush ();

	// if writing to the file was allowed and not the whole bitmap
	// has been written and no error occurred, write the rest of the picture
	if (rownumber && (fileinuse & 2) && (firstundefinedrow != height))
	{
		int32 writeoffset = (int32) bmpstart +
			(int32) height * (int32) rowlength;
		int32 bytestowrite = writeoffset - firstundefinedbyte;
		if (bytestowrite > 0)
		{
			fseek (fbmp, firstundefinedbyte, SEEK_SET);
		//	fbmp. seekp (firstundefinedbyte, ios::beg);
			while (bytestowrite --)
				fputc (fillbyte, fbmp);
			//	fbmp. put (fillbyte);
		}
		fflush (fbmp);
	}

	if (rownumber && rowbuf && changed)
	{
		for (int row = 0; row < rows; row ++)
		{
			if (rowbuf [row])
			{
				delete [] (rowbuf [row]);
				rowbuf [row] = NULL;
			}
		}
	}
	if (rownumber)
		delete [] rownumber;
	if (rowbuf)
		delete [] rowbuf;
	if (changed)
		delete [] changed;
	if (header)
		delete [] header;
	if (palette && palette_allocated)
		delete [] palette;
	if (defined)
		delete [] defined;
	if (fileinuse && fbmp)
		fclose (fbmp);
	//	fbmp. close ();
} /* bmpfile::~bmpfile */

int bmpfile::getbitsperpixel (void)
{
	return bitsperpixel;
} /* bmpfile::getbitsperpixel */

static int roundint (double x)
{
	if (x >= 0)
		return (int) (x + 0.5);
	else
		return -(int) (-x + 0.5);
} /* roundint */

int bmpfile::open (const char *filename, int mode, int quiet)
{
	// check the buffers if they have been allocated properly
	if (!rownumber || !rowbuf || !changed)
		return -6;

	// if the file has already been opened, don't allow to repeat it
	if (fileinuse)
		return -1;
	fileinuse = 1;

	// allocate memory for the header
	header = new char [54 + 8];
	if (!header)
	{
		if (!quiet)
			sout << "Can't allocate memory for the header.\n";
		return -6;
	}

	// open the BMP file in the binary mode if not under Unix
	#ifdef ppDOS
	fbmp = fopen (filename, mode ? "rb+" : "rb");
	#else
	fbmp = fopen (filename, mode ? "r+" : "r");
	#endif
//	#ifdef ppDOS
//	fbmp. open (filename, ios::binary | ios::in |
//		(mode ? (ios::out) : 0));
//	#else
//	fbmp. open (filename, ios::in | (mode ? (ios::out) : 0));
//	#endif
	if (!fbmp)
	{
		if (!quiet)
			sout << "Can't open the BMP file '" << filename <<
				"'.\n";
		return -1;
	}

	// read the header (and check if it is an appropriate BMP file)
	fseek (fbmp, 0, SEEK_SET);
//	fbmp. seekp (0, ios::beg);
	int nread = fread (header, 54, 1, fbmp);
//	fbmp. read (header, 54);
	if (ferror (fbmp) || (nread != 1))
//	if (!fbmp || (fbmp. gcount () != 54))
	{
		if (!quiet)
			sout << "Can't read the header from the "
				"BMP file '" << filename << "'.\n";
		return -2;
	}

	// check if the header begins with "BM"
	if ((header [0] != 'B') || (header [1] != 'M'))
	{
		if (!quiet)
			sout << "The file '" << filename <<
				"' does not contain a Windows bitmap.\n";
		return -4;
	}

	// calculate where the bitmap starts
	bmpstart = char2long (header + 10);

	// read the palette if any
	pallength = (int) (char2long (header + 10) - 14 -
		char2long (header + 14)) / 4;
	if (pallength)
	{
		char *palettebytes = new char [pallength << 2];
		palette = new int32 [pallength];
		palette_allocated = true;
		bool error_read = false;
		if (palettebytes)
		{
			if (fread (palettebytes, pallength << 2, 1, fbmp)
				!= 1)
				//!= static_cast<size_t> (pallength << 2))
			{
				error_read = true;
			}
	//		fbmp. read ((char *) palettebytes, pallength << 2);
		}
		if (!palette || error_read || ferror (fbmp))
	//	if (!palette || !fbmp)
		{
			if (!quiet)
				sout << "Can't read the palette from '" <<
					filename << "'.\n";
			return -3;
		}
		for (int i = 0; i < pallength; i ++)
			palette [i] = char2long (palettebytes + (i << 2));
		delete [] palettebytes;
	}
	else
		palette = NULL;

	// make sure that the file is not compressed
	if (char2long (header + 30) != 0)
	{
		if (!quiet)
			sout << "The file '" << filename <<
				"' contains a compressed bitmap.\n";
		return -5;
	}

	// get the resolution of the picture
	x_resolution = char2long (header + 38);
	y_resolution = char2long (header + 42);

	// get width and height of the bitmap (16- or 32-bit integer numbers Ok)
	width = char2short (header + 18);
	height = char2short (header + 22);
	firstundefinedrow = height;

	// if the picture is empty, it can't be a proper BMP file
	if ((width <= 0) || (height <= 0))
	{
		if (!quiet)
			sout << "Oh dear, the bitmap in '" << filename <<
				"' is empty!\n";
		return -4;
	}

	// get the number of bits per pixel
	bitsperpixel = char2short (header + 28);
	if ((bitsperpixel != 1) && (bitsperpixel != 4) &&
		(bitsperpixel != 8) && (bitsperpixel != 24))
	{
		if (!quiet)
			sout << "The bitmap in '" << filename <<
				"' contains " << bitsperpixel <<
				" bits per pixel.\n";
		return -5;
	}

	// calculate the length of rows in the picture
	fseek (fbmp, 0, SEEK_END);
//	fbmp. seekg (0, ios::end);
	firstundefinedbyte = ftell (fbmp);
//	firstundefinedbyte = fbmp. tellg ();
	rowlength = (unsigned) ((firstundefinedbyte - bmpstart) / height);

	// allocate memory for the rows
	for (int row = 0; row < rows; row ++)
	{
		rowbuf [row] = new unsigned char [rowlength];
		if (!rowbuf [row])
		{
			if (!quiet)
				sout << "Can't allocate " << rowlength <<
					" bytes to store a row of pixels "
					"no. " << (row + 1) <<
					" out of " << rows << ".\n";
			return -6;
		}
	}

	if (!quiet)
	{
		sout << "* Read BitMaP: " << bitsperpixel << "-bit, " <<
			width << "x" << height;
		if (x_resolution || y_resolution)
		{
			sout << " with " << roundint (0.0254 * x_resolution);
			if (x_resolution != y_resolution)
				sout << "x" << roundint (0.0254 * y_resolution);
			sout << " dpi";
		}
	//	sout << " (" << rowlength << " bytes per row).";
		sout << " (" << ((long) rowlength * (long) height +
			54 + 4 * pallength) << " bytes).";
		if (pallength)
			sout << " " << pallength << " colors.";
		sout << '\n';
	}

	return 0;
} /* bmpfile::open */

int bmpfile::writeheader (void)
{
	// if no header or the file has not been opened for writing, break
	if (!header || !(fileinuse & 2))
		return -1;

	// fill in the header
	* (char *) (header + 0) = 'B';
	* (char *) (header + 1) = 'M';
	long2char (header + 2,
		54 + 4 * pallength + (int32) rowlength * (int32) height);
	long2char (header + 6, 0);
	long2char (header + 10, 54 + 4 * pallength);
	long2char (header + 14, 40);
	long2char (header + 18, width);
	long2char (header + 22, height);
	short2char (header + 26, 1);
	short2char (header + 28, bitsperpixel);
	long2char (header + 30, 0);
	long2char (header + 34, (int32) rowlength * (int32) height);
	long2char (header + 38, x_resolution);
	long2char (header + 42, y_resolution);
	long2char (header + 46, 0);
	long2char (header + 50, 0);

	// write the header to the file
	fseek (fbmp, 0, SEEK_SET);
//	fbmp. seekp (0, ios::beg);
	fwrite (header, 54, 1, fbmp);
//	fbmp. write (header, 54);

	// write the palette if needed
	if (pallength)
	{
		for (int i = 0; i < pallength; i ++)
		{
			fputc ((int) (palette [i] & 0xFF), fbmp);
			fputc ((int) ((palette [i] >> 8) & 0xFF), fbmp);
			fputc ((int) ((palette [i] >> 16) & 0xFF), fbmp);
			fputc (0, fbmp);
		//	fbmp. put (palette [i] & 0xFF);
		//	fbmp. put ((palette [i] >> 8) & 0xFF);
		//	fbmp. put ((palette [i] >> 16) & 0xFF);
		//	fbmp. put (0);
		}
	}

	// update the number of the first undefined byte in the picture
	if (firstundefinedbyte < ftell (fbmp))
		firstundefinedbyte = ftell (fbmp);
//	if (firstundefinedbyte < fbmp. tellp ())
//		firstundefinedbyte = fbmp. tellp ();

	// return the appropriate code
	if (ferror (fbmp))
//	if (!fbmp)
		return -1;
	return 0;
} /* bmpfile::writeheader */

int bmpfile::create (const char *filename, int _width, int _height,
	int _bitsperpixel, int _pallength, int32 *_palette, int quiet)
{
	static int32 bwpalette [2];
	bwpalette [0] = 0;
	bwpalette [1] = (int32) 0xFFFFFFL;

	// check the buffers if they have been allocated properly
	if (!rownumber || !rowbuf || !changed)
		return -6;

	// if the file has already been opened, don't allow to repeat it
	if (fileinuse)
		return -1;
	fileinuse = 3;

	// check parameters if they are Ok
	if ((_bitsperpixel != 1) && (_bitsperpixel != 4) &&
		(_bitsperpixel != 8) && (_bitsperpixel != 24))
	{
		if (!quiet)
			sout << "No idea how to manage a " <<
				_bitsperpixel << "-bit picture.\n";
		return -4;
	}

	// allocate memory for the header
	header = new char [54 + 8];
	if (!header)
	{
		if (!quiet)
			sout << "Can't allocate memory for the header.\n";
		return -6;
	}

	// compute the actual parameters of the BMP file
	width = _width;
	height = _height;
	bitsperpixel = _bitsperpixel;
	firstundefinedrow = 0;

	switch (bitsperpixel)
	{
		case 1:
			if (_pallength || _palette)
			{
				pallength = _pallength;
				palette = _palette;
			}
			else
			{
				pallength = 2;
				palette = bwpalette;
			}
			bmpstart = 54 + 4 * pallength;
			rowlength = ((width + 7) / 8 + 3) / 4 * 4;
			break;
		case 4:
			pallength = _pallength;
			palette = _palette;
			bmpstart = 54 + 4 * pallength;
			rowlength = ((width + 1) / 2 + 3) / 4 * 4;
			if (pallength)
			{
				int byte = pallength - 1;
				fillbyte = byte | (byte << 4);
			}
			break;
		case 8:
			pallength = _pallength;
			palette = _palette;
			bmpstart = 54 + 4 * pallength;
			rowlength = (width + 3) / 4 * 4;
			if (pallength)
				fillbyte = pallength - 1;
			break;
		case 24:
			pallength = 0;
			palette = NULL;
			bmpstart = 54;
			rowlength = (3 * width + 3) / 4 * 4;
			break;
	}

	defined = new unsigned char [(height + 7) / 8];
	if (!defined)
	{
		if (!quiet)
			sout << "Can't allocate " << (height + 7) / 8 <<
				" bytes row defined for flags.\n";
		return -6;
	}
	mem_set (defined, 0, (height + 7) / 8);

	// create the BMP file in the binary mode if not under Unix
	#ifdef ppDOS
	fbmp = fopen (filename, "wb+");
	#else
	fbmp = fopen (filename, "w+");
	#endif
//	#ifdef ppDOS
//	fbmp. open (filename, ios::binary | ios::out | ios::trunc);
//	#else
//	fbmp. open (filename, ios::out | ios::trunc);
//	#endif
	if (!fbmp)
	{
		if (!quiet)
			sout << "Can't create the BMP file '" << filename <<
				"'.\n";
		return -1;
	}

	// create the header (and write the palette if any)
	if (writeheader () < 0)
	{
		if (!quiet)
			sout << "Can't write the header to the new "
				"BMP file '" << filename << "'.\n";
		return -2;
	}

	// allocate memory for the rows
	for (int row = 0; row < rows; row ++)
	{
		rowbuf [row] = new unsigned char [rowlength];
		if (!rowbuf [row])
		{
			if (!quiet)
				sout << "Can't allocate " << rowlength <<
					" bytes to store a row of pixels "
					"no. " << (row + 1) <<
					" out of " << rows << ".\n";
			return -6;
		}
		mem_set (rowbuf [row], fillbyte, rowlength);
	}

	if (!quiet)
	{
		sout << "* Write BitMaP: " << bitsperpixel << "-bit, " <<
			width << "x" << height;
		if (x_resolution || y_resolution)
		{
			sout << " with " << roundint (0.0254 * x_resolution);
			if (x_resolution != y_resolution)
				sout << "x" <<
				roundint (0.0254 * y_resolution);
			sout << " dpi";
		}
		sout << " (" << ((int32) rowlength * (int32) height +
			54 + 4 * pallength) << " bytes).";
		if (pallength)
			sout << " " << pallength << " colors.";
		sout << '\n';
	}

	return 0;
} /* bmpfile::create */

int32 bmpfile::getpixel (int x, int y, bool index)
{
	if ((x < 0) || (x >= width) || (y < 0) || (y >= height) ||
		!(fileinuse & 1))
		return -1;

	// the picture in the BMP file is flipped upside down,
	// so the true coordinate Y should be inverted
	// unless the inverted picture is being processed directly
	if (!inverted)
		y = height - 1 - y;

	int row = current;
	int emptyrow = -1;
	while (rownumber [row] != y)
	{
		if ((emptyrow == -1) && (rownumber [row] == -1))
			emptyrow = row;
		row ++;
		if (row >= rows)
			row = 0;
		if (row == current)
		{
			row ++;
			if (row >= rows)
				row = 0;
			if (emptyrow != -1)
				row = emptyrow;
			if (changed [row])
				writerow (row);
			rownumber [row] = y;
			if (!defined || (defined [y >> 3] & (0x01 << (y & 0x07))))
				readrow (row);
			else
				mem_set (rowbuf [row], fillbyte, rowlength);
		}
	}
	current = row;

	int32 pixel;
	switch (bitsperpixel)
	{
		case 1:
			pixel = (rowbuf [row] [x >> 3] >> (7 - (x & 7))) & 1;
			break;
		case 4:
			if (x & 1)
				pixel = rowbuf [row] [x >> 1] & 0x0F;
			else
				pixel = rowbuf [row] [x >> 1] >> 4;
			break;
		case 8:
			pixel = rowbuf [row] [x];
			break;
		case 24:
			return ((int32) rowbuf [row] [3 * x]) |
				(((int32) rowbuf [row] [3 * x + 1]) << 8) |
				(((int32) rowbuf [row] [3 * x + 2]) << 16);
		default:
			return -1;
	}

	// transform the pixel to its color if needed
	if (palette && !index && (pixel < pallength))
		return palette [(int) pixel];
	else
		return pixel;
} /* bmpfile::getpixel */

int32 bmpfile::putpixel (int x, int y, long color, bool index)
{
	if ((x < 0) || (x >= width) || (y < 0) || (y >= height) ||
		!(fileinuse & 2))
		return -1;

	// the picture in the BMP file is flipped upside down,
	// so the true coordinate Y should be inverted
	// unless the inverted picture is being processed directly
	if (!inverted)
		y = height - 1 - y;

	int row = current;
	int emptyrow = -1;
	while (rownumber [row] != y)
	{
		if ((emptyrow == -1) && (rownumber [row] == -1))
			emptyrow = row;
		row ++;
		if (row >= rows)
			row = 0;
		if (row == current)
		{
			row ++;
			if (row >= rows)
				row = 0;
			if (emptyrow != -1)
				row = emptyrow;
			if (changed [row])
				writerow (row);
			rownumber [row] = y;
			if (!defined || (defined [y >> 3] & (0x01 << (y & 7))))
				readrow (row);
			else
				mem_set (rowbuf [row], fillbyte, rowlength);
		}
	}
	current = row;
	changed [row] = 1;

	switch (bitsperpixel)
	{
		case 1:
			if (color)
				rowbuf [row] [x >> 3] |= (unsigned char)
					(0x80 >> (x & 7));
			else
				rowbuf [row] [x >> 3] &= (unsigned char)
					~(0x80 >> (x & 7));
			return color;
		case 4:
			if (!index)
				return -1;
			if (x & 1)
				rowbuf [row] [x >> 1] = (unsigned char)
					((rowbuf [row] [x >> 1] & 0xF0) |
					color);
			else
				rowbuf [row] [x >> 1] = (unsigned char)
					((rowbuf [row] [x >> 1] & 0x0F) |
					(color << 4));
			if (color < pallength)
				return palette [(int) color];
			else
				return color;
		case 8:
			if (!index)
				return -1;
			rowbuf [row] [x] = (unsigned char) color;
			if (color < pallength)
				return palette [(int) color];
			else
				return color;
		case 24:
			rowbuf [row] [3 * x] = (unsigned char)
				(color & 0xFF);
			rowbuf [row] [3 * x + 1] = (unsigned char)
				((color >> 8) & 0xFF);
			rowbuf [row] [3 * x + 2] = (unsigned char)
				((color >> 16) & 0xFF);
			return color;
		default:
			return -1;
	}
} /* bmpfile::putpixel */

int difference (int x, int y)
{
	if (x > y)
		return x - y;
	else
		return y - x;
} /* difference */

int corner (int i, int j, int t)
{
	if (i < 0)
		i = -i;
	if (j < 0)
		j = -j;
	t --;
	if ((i == t) && (j == t))
		return 1;
	return 0;
} /* corner */

void bmpfile::drawpixel (int x, int y, int thickness, long color, bool index)
{
	if (thickness <= 1)
	{
		putpixel (x, y, color, index);
		return;
	}
	for (int t1 = -thickness + 1; t1 < thickness; t1 ++)
	{
		for (int t2 = -thickness + 1; t2 < thickness; t2 ++)
			if (!corner (t1, t2, thickness))
				putpixel (x + t1, y + t2, color, index);
	}
	return;
} /* draw pixel */

void bmpfile::drawsegment (int x1, int y1, int x2, int y2,
	int thickness, long color, bool index)
{
	int x, y;

	if ((x1 == x2) && (y1 == y2))
	{
		drawpixel (x1, y1, thickness, color, index);
		return;
	}

	if (difference (x2, x1) >= difference (y2, y1))
	{
		if (x1 > x2)
		{
			x = x1; x1 = x2; x2 = x;
			y = y1; y1 = y2; y2 = y;
		}
		for (x = x1; x <= x2; x ++)
			drawpixel (x, y1 + (unsigned)
				((long) (y2 - y1) * (x - x1) / (x2 - x1)),
				thickness, color, index);
	}
	else
	{
		if (y1 > y2)
		{
			x = x1; x1 = x2; x2 = x;
			y = y1; y1 = y2; y2 = y;
		}
		for (y = y1; y <= y2; y ++)
			drawpixel (x1 + (unsigned)
				((long) (x2 - x1) * (y - y1) / (y2 - y1)), y,
				thickness, color, index);
	}
	return;
} /* draw segment */


} // namespace homology
} // namespace capd

/// @}

