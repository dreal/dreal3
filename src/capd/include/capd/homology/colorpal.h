/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file colorpal.h
///
/// This file contains the definition of a simple class "ColorPalette".
/// This class provides a specified number of distinct colors, for example,
/// for the purpose of plotting cubical sets with different colors.
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started on February 14, 2007. Last revision: February 14, 2008.


#ifndef _CAPD_HOMOLOGY_COLORPAL_H_ 
#define _CAPD_HOMOLOGY_COLORPAL_H_ 

#include "capd/homology/config.h"

namespace capd {
namespace homology {


// --------------------------------------------------
// ----------------- Color Palette ------------------
// --------------------------------------------------

/// Provides a palette of distinct RGB colors. The first color is black.
/// White is considered a background color and thus is not provided.
class ColorPalette
{
public:
	/// The constructor of a palette of a prescribed size.
	ColorPalette (int _n, bool grays = false);

	/// The destructor.
	~ColorPalette ();

	/// Returns the color with the given number.
	/// The color is encoded as 0xRRGGBB.
	int operator [] (int i) const;

private:
	/// The copy constructor is not allowed.
	ColorPalette (const ColorPalette &src);

	/// The assignment operator is not allowed.
	ColorPalette &operator = (const ColorPalette &src);

	/// Generates a color component based on the bit mask.
	/// The nonzero bits are every 3 locations in the mask.
	static int generateComponent (int bitMask);

	/// The number of colors in the palette.
	int n;

	/// The RBG colors in the palette.
	int *colors;

}; /* ColorPalette */

// --------------------------------------------------

inline int ColorPalette::generateComponent (int bitMask)
{
	int mask = 0x100;
	int result = 1;
	while (mask && bitMask)
	{
		if (bitMask & 1)
			result = mask;
		mask >>= 1;
		bitMask >>= 3;
	}
	return (result - 1) & 0xFF;
} /* ColorPalette::generateComponent */

inline ColorPalette::ColorPalette (int _n, bool grays):
	n (_n), colors (0)
{
	if (n <= 0)
		return;
	colors = new int [n];

	if (grays)
	{
		for (int i = 0; i < n; ++ i)
		{
			int shade = i * 255 / n;
			colors [i] = shade | (shade << 8) | (shade << 16);
		}
		return;
	}

	const int niceCount = 14;
	int niceColors [niceCount] = {
		0x000000, 0x0000FF, 0xFF0000, 0x00FF00,
		0x00FFFF, 0xFF00FF, 0x7F007F, 0xFF7F00,
		0x007F00, 0x7F7F7F, 0xAFAFAF, 0x00007F,
		0x7F00FF, 0xFFFF00,
	};

	int counter = 1;
	int pos = 0;
	while (pos < n)
	{
		// take a nice color if possible
		if (pos < niceCount)
		{
			colors [pos] = niceColors [pos];
			++ pos;
			continue;
		}

		// create a color based on the current counter
		int red = generateComponent (counter >> 1);
		int green = generateComponent (counter >> 2);
		int blue = generateComponent (counter);
		int color = (red << 16) | (green << 8) | blue;

		// check whether this color has already appeared before
		bool repeated = false;
		for (int i = 0; i < pos; ++ i)
		{
			if (colors [i] == color)
			{
				repeated = true;
				break;
			}
		}

		// if the color is not repeated and it is not white then ok
		if (!repeated && (color != 0xFFFFFF) && (color != 0xFFFF7F))
			colors [pos ++] = color;
		++ counter;
	}

	return;
} /* ColorPalette::ColorPalette */

inline ColorPalette::~ColorPalette ()
{
	if (colors)
		delete [] colors;
	return;
} /* ColorPalette::~ColorPalette */

inline ColorPalette::ColorPalette (const ColorPalette &)
{
	return;
} /* ColorPalette::ColorPalette */

inline ColorPalette &ColorPalette::operator = (const ColorPalette &)
{
	return *this;
} /* ColorPalette::operator = */

inline int ColorPalette::operator [] (int i) const
{
	if ((i < 0) || (i >= n))
		return 0;
	else
		return colors [i];
} /* ColorPalette::operator [] */


} // namespace homology
} // namespace capd

#endif // _CAPD_HOMOLOGY_COLORPAL_H_ 

/// @}

