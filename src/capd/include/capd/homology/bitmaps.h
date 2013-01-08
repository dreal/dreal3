/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file bitmaps.h
///
/// This file contains the definition of a class which can be used
/// as a simple interface to read and write Windows Bitmap files
/// (BMP pictures). The functionality of this class is quite limited.
/// Only uncompressed bitmap files are supported.
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started in June 1998. Last revision: September 3, 2003 (Nov 13, 2003).

// WARNING: This version of the module has very limited capabilities,
// e.g. it can normally write only 1-bit B/W and 24-bit true color bitmaps,
// and operates improperly if the entire output bitmap is not stored
// in the memory or is not written row by row.


#ifndef _CAPD_HOMOLOGY_BITMAPS_H_ 
#define _CAPD_HOMOLOGY_BITMAPS_H_ 

#include "capd/homology/config.h"
#include "capd/homology/textfile.h"

#include <iostream>
#include <stdio.h>
#include <cstdlib>

namespace capd {
namespace homology {


// classes defined within this header file:
class bmpfile;


// --------------------------------------------------
// -------------------- bmpfile ---------------------
// --------------------------------------------------

/// The class 'bmpfile' is an elementary interface that can be used to read
/// or create and write images in the uncompressed Windows BMP format.
/// It supports black-and-white as well as color bitmap images.
class bmpfile
{
public:
	/// The only allowed constructor. Defines the number of rows
	/// that are stored in the memory. For optimal performance,
	/// this should be set to the height of the picture (if known).
	bmpfile (int _rows = 20);

	/// The destructor.
	~bmpfile ();

#ifndef ReadOnly
#define ReadOnly 0
#endif

#ifndef ReadWrite
#define ReadWrite 1
#endif
	/// Opens a bmp file for reading (mode = ReadOnly)
	/// or editing (mode = ReadWrite).
	/// Returns: 0 = Ok, -1 = Not found, -2 = Can't read header,
	/// -3 = Can't read palette, -4 = Not BMP, -5 = Not supported,
	/// -6 = Memory allocation error occurred.
	/// Displays a message in case of error.
	int open (const char *filename, int mode = ReadOnly,
		int quiet = 0);

	/// Create a bmp file (only 1- and 24-bit supported - sorry!).
	/// Set "x_resolution" and "y_resolution" before or 0 will be
	/// assumed. If you change these parameters later, you must
	/// rewrite the header;.
	/// Returns: 0 = Ok, -1 = Can't create,
	/// -2 = Can't write header, -3 = Can't write palette,
	/// -4 = Bad params, -5 = Not supported,
	/// -6 = Memory allocation error occurred.
	/// Displays a message in case of error.
	int create (const char *filename, int _width, int _height,
		int _bitsperpixel = 24, int _pallength = 0,
		int32 *_pallette = NULL, int quiet = 0);

	/// Sets processing of the invertec picture, as stored in the file.
	/// This results in the Y axis running from bottom to top, like in
	/// mathematics, unlike in computers.
	inline void invertedpicture (int _inverted = 1)
		{inverted = _inverted;};

	/// Writes the header to the file.
	/// Returns: 0 = Ok, -1 = Error (no messages displayed).
	int writeheader (void);

	/// Reads the true color of a pixel or its index if 'index = true'.
	/// Note: The coordinates start with (0,0).
	int32 getpixel (int x, int y, bool index = false);

	/// Writes a pixel and returns its true color.
	int32 putpixel (int x, int y, long color = 0,
		bool index = false);

	/// Writes a thick pixel and returns its true color.
	void drawpixel (int x, int y, int thickness = 1,
		long color = 0, bool index = false);

	/// Draws a segment built of pixels, with the desired thickness.
	void drawsegment (int x1, int y1, int x2, int y2,
		int thickness = 1, long color = 0,
		bool index = false);

	/// Returns the width of the picture.
	inline int picture_width (void) { return width; };

	/// Returns the height of the picture.
	inline int picture_height (void) { return height; };

	/// The X resolution of the picture (in dpi).
	int32 x_resolution;

	/// The Y resolution of the picture (in dpi).
	int32 y_resolution;

	/// The counter of rows read from a BMP file.
	long rows_read;

	/// The counter of rows written to a BMP file.
	long rows_written;

	/// Flushes the buffers to update the contents BMP file.
	void flush (void);

	/// Returns the current number of bits per pixel in the picture.
	int getbitsperpixel (void);

	/// Returns the pointer to the given row stored in the memory.
	/// Please, use this function with caution!
	unsigned char *getrow (int row);
	
	/// Returns the length of a row stored in the memory.
	unsigned getrowlength () const;

	/// Returns a pointer to the current color palette (if any).
	inline int32 *getpalette (void) { return palette; };

	/// Returns the length of the current color palette (if any).
	inline int getpallength (void) { return pallength; };

private:
	/// The header of the bitmap file.
	char *header;

	/// Palette length (in 32-bit words).
	int pallength;

	/// The palette buffer.
	int32 *palette;

	/// Has the palette memory been allocated?
	bool palette_allocated;

	/// The numbers of rows stored in the memory.
	int *rownumber;

	/// The rows of the picture stored in the memory.
	unsigned char **rowbuf;

	/// Flags that indicate which rows have been changed.
	char *changed;

	/// Flags that indicate which rows have been defined.
	unsigned char *defined;

	/// The current row.
	int current;

	/// Reads the current row from the file to the memory.
	int readrow (int row);

	/// Writes the current row from the memory to the file.
	int writerow (int row);

	/// The offset of the bitmap beginning in the file.
	int bmpstart;

	/// The length of a row in the bitmap (in bytes)
	unsigned rowlength;

	/// The number of bits per pixel in the bitmap file.
	int bitsperpixel;

	/// The actual width of the picture stored in the file.
	int width;

	/// The actual height of the picture stored in the file.
	int height;

	/// The binary stream containing the picture file.
	FILE *fbmp;

	/// The type of the bitmap file: 0 = none, 1 = read,
	/// 2 = write, 3 = r/w.
	int fileinuse;

	/// The number of the first row undefined in the picture.
	/// Normally it will be the height of the picture, since
	/// rows are numbered starting with 0. It is important
	/// while creating a BMP picture so that the program knows
	/// where to begin writing the empty rows if any.
	int firstundefinedrow;

	/// The number of the first undefined byte in the BMP file
	/// that has not yet been written after creating the file.
	int firstundefinedbyte;

	/// The number of rows allocated in the memory.
	int rows;

	/// The value of the byte to fill empty lines (background).
	unsigned char fillbyte;

	/// A flag that remembers whether the inverted picture should be
	/// processed. This is the order of rows as stored in the file,
	/// with the vertical axis Y running from the bottom to the top
	/// of the screen.
	int inverted;

}; /* class bmpfile */


} // namespace homology
} // namespace capd

#endif // _CAPD_HOMOLOGY_BITMAPS_H_ 

/// @}

