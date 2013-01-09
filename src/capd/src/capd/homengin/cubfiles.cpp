/// @addtogroup HomologyEngines
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file cubfiles.cpp
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// This file copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file is part of the "chomp" program. It is free software;
// you can redistribute it and/or modify it under the terms of the GNU
// General Public License as published by the Free Software Foundation;
// either version 2 of the License, or (at your option) any later version.
//
// This library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License along
// with this software; see the file "license.txt".  If not, write to the
// Free Software Foundation, Inc., 59 Temple Place - Suite 330, Boston,
// MA 02111-1307, USA.

// Started in March 2006. Last revision: July 6, 2007.

#include <fstream>
#include <cctype>
#include <cstring>

#include "capd/homengin/cubfiles.h"
#include "capd/homology/bitmaps.h"
#include "capd/homology/bitcount.h"

using namespace std;

namespace capd {
namespace homengin {

// --------------------------------------------------
// -------------- ABSTRACT CUBICAL SET --------------
// --------------------------------------------------

int cubfile::volume (int chunk, bool power2) const
{
	// update the bounding box and the dimension if necessary
	boundingbox (0, 0);
	dim ();

	// align the sizes up to a power of 2 if requested to
	int forcewidth = 0;
	if (power2)
	{
		int maxwidth = 0;
		for (int i = 0; i < _dim; ++ i)
		{
			int width = _max [i] - _min [i];
			if (maxwidth < width)
				maxwidth = width;
		}
		forcewidth = 1;
		while (forcewidth < maxwidth)
			forcewidth <<= 1;
	}

	// count the volume of the set of cubes (in bits)
	int size = 1;
	double dsize = 1.0;
	if (chunk)
		dsize /= chunk;
	for (int i = 0; i < _dim; ++ i)
	{
		int width = forcewidth ? forcewidth : (_max [i] - _min [i]);
		size *= width;
		if (chunk && (size > chunk))
		{
			size /= chunk;
			chunk = 0;
		}
		dsize *= width;
	}
	if (dsize >= (65536.0 - 1.0) * 32768.0)
		return -1;
	return size;
} /* cubfile::volume */


// --------------------------------------------------
// ------------- TYPES OF CUBICAL SETS --------------
// --------------------------------------------------

cubtype::cubtypelist cubtype::cubtypes;

class Compare_Types
{
public:
	int operator () (const cubtype *t1, const cubtype *t2) const
	{
		return (std::strcmp (t1 -> name (), t2 -> name ()) < 0);
	}
}; /* class Compare_Types */

std::ostream &cubtype::showlist (std::ostream &out,
	const cubtype::cubtypelist &_types)
{
	// sort the list of types in the alphabetical order
	cubtype::cubtypelist types (_types);
	std::sort (types. begin (), types. end (), Compare_Types ());

	out << "Available types of cubical sets "
		"(listed in the alphabetical order):\n";
	for (cubtype::cubtypelist::const_iterator x = types. begin ();
		x != types. end (); ++ x)
	{
		out << '\n';
		const cubtype *e = *x;
		out << "<<< " << e -> name () << " >>>\n";
		e -> describe (out);
	}
	return out;
} /* cubtype::showlist */

cubfile *cubtype::newfile (const char *filename,
	const cubtype::cubtypelist &types)
{
	using capd::homology::sout;
	sout << "Analyzing the type of '" << filename << "'... ";
	for (cubtype::cubtypelist::const_iterator x = types. begin ();
		x != types. end (); ++ x)
	{
		const cubtype *e = *x;
		if (!e -> compatible (filename))
			continue;
		sout << e -> name () << ".\n";
		return e -> newcubfile (filename);
	}
	sout << "Failed.\n";
	throw "Unable to determine the type of a cubical file.";
} /* newfile */


// --------------------------------------------------
// --------------- BIG/LITTLE ENDIAN ----------------
// --------------------------------------------------

inline static bool bigendian ()
{
	static short int test = 1;
	return !(*reinterpret_cast<char *> (&test));
} /* bigendian */

inline static bool littleendian ()
{
	static short int test = 1;
	return !!(*reinterpret_cast<char *> (&test));
} /* littleendian */

#if (__LONG_MAX__ > 2147483647)
inline static void flipwords (unsigned long *words, int nwords)
{
	while (nwords --)
	{
		unsigned long word = *words;
		word = ((word & 0xFFul) << 56) |
			((word & 0xFF00ul) << 40) |
			((word & 0xFF0000ul) << 24) |
			((word & 0xFF000000ul) << 8) |
			((word & 0xFF00000000ul) >> 8) |
			((word & 0xFF0000000000ul) >> 24) |
			((word & 0xFF000000000000ul) >> 40) |
			((word & 0xFF00000000000000ul) >> 56);
		*words = word;
		++ words;
	}
	return;
} /* flipwords */
#else
inline static void flipwords (unsigned long *words, int nwords)
{
	while (nwords --)
	{
		unsigned long word = *words;
		word = ((word & 0xFF) << 24) |
			((word & 0xFF00) << 8) |
			((word & 0xFF0000) >> 8) |
			((word & 0xFF000000) >> 24);
		*words = word;
		++ words;
	}
	return;
} /* flipwords */
#endif

unsigned char fliptable [] = {
	0,128,64,192,32,160,96,224,16,144,80,208,48,176,112,240,
	8,136,72,200,40,168,104,232,24,152,88,216,56,184,120,248,
	4,132,68,196,36,164,100,228,20,148,84,212,52,180,116,244,
	12,140,76,204,44,172,108,236,28,156,92,220,60,188,124,252,
	2,130,66,194,34,162,98,226,18,146,82,210,50,178,114,242,
	10,138,74,202,42,170,106,234,26,154,90,218,58,186,122,250,
	6,134,70,198,38,166,102,230,22,150,86,214,54,182,118,246,
	14,142,78,206,46,174,110,238,30,158,94,222,62,190,126,254,
	1,129,65,193,33,161,97,225,17,145,81,209,49,177,113,241,
	9,137,73,201,41,169,105,233,25,153,89,217,57,185,121,249,
	5,133,69,197,37,165,101,229,21,149,85,213,53,181,117,245,
	13,141,77,205,45,173,109,237,29,157,93,221,61,189,125,253,
	3,131,67,195,35,163,99,227,19,147,83,211,51,179,115,243,
	11,139,75,203,43,171,107,235,27,155,91,219,59,187,123,251,
	7,135,71,199,39,167,103,231,23,151,87,215,55,183,119,247,
	15,143,79,207,47,175,111,239,31,159,95,223,63,191,127,255
};

inline static void flipbytes (unsigned char *bytes, int nbytes)
{
	while (nbytes --)
	{
		*bytes = fliptable [*bytes];
		++ bytes;
	}
	return;
} /* flipbytes */


// --------------------------------------------------
// --------------- TEXT LIST OF CUBES ---------------
// --------------------------------------------------

int cublistfile::readcubes (capd::homology::CubicalComplex &s) const
{
	using namespace capd::homology;

	const char *name = _filename. c_str ();
	std::ifstream in (name);
	ignorecomments (in);
	if (in. peek () == 'd')
	{
		ignoreline (in);
		ignorecomments (in);
	}

	Cube q;
	while (!in. eof ())
	{
		in >> q;
		s. add (CubicalCell (q));
		ignorecomments (in);
	}

	return 0;
} /* cublistfile::readcubes */

int cublistfile::readcubes (capd::homology::SetOfCubes &s) const
{
	using namespace capd::homology;

	const char *name = _filename. c_str ();
	std::ifstream in (name);
	ignorecomments (in);
	if (in. peek () == 'd')
	{
		ignoreline (in);
		ignorecomments (in);
	}

	in >> s;
	return 0;
} /* cublistfile::readcubes */

static inline void createbitmap (int *&sizes, char *&bytes, int padding,
	std::vector<int> &offsetmult, int _dim,
	const std::vector<int> &_min, const std::vector<int> &_max,
	bool power2)
{
	// force the width in all the directions to be a power of 2
	int forcewidth = 0;
	if (power2)
	{
		int maxwidth = padding;
		for (int i = 0; i < _dim; ++ i)
		{
			int width = _max [i] - _min [i];
			if (maxwidth < width)
				maxwidth = width;
		}
		forcewidth = 1;
		while (forcewidth < maxwidth)
			forcewidth <<= 1;
	}

	sizes = new int [_dim];
	int pad8 = padding << 3;
	sizes [0] = forcewidth ? forcewidth : (_max [0] - _min [0]);
	int nbytes = (padding <= 1) ? ((sizes [0] + 7) >> 3) :
		((sizes [0] + pad8 - 1) / pad8 * padding);
	int size0 = nbytes << 3;
	capd::homology::sbug << "size [0] = " << size0 << "\n";
	offsetmult. push_back (0);
	offsetmult. push_back (nbytes);
	double check_bytes = nbytes;
	for (int d = 1; d < _dim; ++ d)
	{
		sizes [d] = forcewidth ? forcewidth : (_max [d] - _min [d]);
		capd::homology::sbug << "size [" << d << "] = " << sizes [d] << "\n";
		nbytes *= sizes [d];
		check_bytes *= sizes [d];
		offsetmult. push_back (offsetmult. back () * sizes [d]);
	}
	capd::homology::sbug << "Allocating " << nbytes << " bytes.\n";
	if (check_bytes >= (65536.0 - 1.0) * 32768.0)
	{
		throw "The size of the bitmap for storing the cubical set "
			"exceeds 2 GB.";
	}
	bytes = new char [nbytes];
	std::memset (bytes, 0, nbytes);
	return;
} /* createbitmap */

static inline void markbit (const int *coord,
	const std::vector<int> &offsetmult, int _dim,
	int padding, bool little, char *bytes)
{
	int bit = coord [0];
	int bytenumber = bit >> 3;
	for (int i = 1; i < _dim; ++ i)
		bytenumber += offsetmult [i] * coord [i];
	if (little || (padding <= 1))
	{
		bytes [bytenumber] |= 1 << (bit & 7);
	}
	else
	{
		int remainder = bytenumber % padding;
		int byteoffset = padding - 1 - remainder;
		bytes [bytenumber - remainder + byteoffset] |=
			1 << (bit & 7);
		// for a true big endian data representation,
		// the last line should be 1 << (7 - (bit & 7));
	}
	return;
} /* markbit */

int cublistfile::readcubes (int *&sizes, char *&bytes, int padding,
	bool power2) const
{
	using namespace capd::homology;

	// analyze the file to determine the dimension and bitmap size
	if ((_dim <= 0) || !_min. size ())
		analyze ();
	if (_dim <= 0)
		throw "Unable to determine the dimension of the cubes.";

	// compute the size and allocate memory for all the variables
	std::vector<int> offsetmult;
	createbitmap (sizes, bytes, padding, offsetmult, _dim, _min, _max,
		power2);

	// read the cubes from the file and mark them in the bitmap
	std::ifstream in (_filename. c_str ());
	ignorecomments (in);
	if (in. peek () == 'd')
	{
		ignoreline (in);
		ignorecomments (in);
	}
	int coord [tCubeVar<int>::MaxDim];
	bool little = littleendian ();
	while (!in. eof ())
	{
		tCubeVar<int> q;
		in >> q;
		q. coord (coord);
		for (int i = 0; i < _dim; ++ i)
			coord [i] -= _min [i];
		markbit (coord, offsetmult, _dim, padding, little, bytes);
		ignorecomments (in);
	}
	return 0;
} /* cublistfile::readcubes */

int cublistfile::dim () const
{
	using namespace capd::homology;

	// if the dimension is known then return it
	if (_dim)
		return _dim;

	// open the file to determine the dimension
	std::ifstream in (filename ());

	// ignore the line "dimension N" if present
	ignorecomments (in);
	while (in. peek () == 'd')
	{
		ignoreline (in);
		ignorecomments (in);
	}

	// read one cube from the file
	tCubeVar<int> q;
	in >> q;
	in. close ();
	int d = q. dim ();
	if (d <= 0)
		throw "Unable to determine the dimension of cubes.";
	_dim = d;
	return d;
} /* cublistfile::dim */

void cublistfile::analyze () const
{
	using namespace capd::homology;

	// reset the analyzed data (just in case)
	_count = 0;
	_min. clear ();
	_max. clear ();

	// open the file and say what you are doing
	sout << "Scanning '" << filename () << "'...\n";
	std::ifstream in (filename ());
	ignorecomments (in);

	int coord [tCubeVar<int>::MaxDim];
	while (!in. eof ())
	{
		// ignore the line "dimension N"
		if (in. peek () == 'd')
		{
			ignoreline (in);
			ignorecomments (in);
			continue;
		}
			
		// read a cube
		capd::homology::tCubeVar<int> q;
		in >> q;
		ignorecomments (in);

		// make sure the cube has a nonzero dimension
		int d = q. dim ();
		if (d <= 0)
			continue;

		// update the dimension or verify its consistency
		if (!_dim)
			_dim = d;
		else if (_dim != d)
			throw "Inconsistent dimension of cubes.";

		// count the cube
		++ _count;

		// extract the coordinates of the cube
		q. coord (coord);
		
		// create the min/max coordinates if not defined, yet
		if (!_min. size ())
		{
			_min. assign (coord, coord + _dim);
			_max. assign (coord, coord + _dim);
			for (int i = 0; i < _dim; ++ i)
				++ (_max [i]);
		}
		
		// update the min/max coordinates otherwise
		else
		{
			for (int i = 0; i < _dim; ++ i)
			{
				if (_min [i] > coord [i])
					_min [i] = coord [i];
				if (_max [i] <= coord [i])
					_max [i] = coord [i] + 1;
			}
		}
	}

	// show the result of the analysis of the set of cubes
	sout << _count << " cubes of dim " << _dim << " in ";
	for (int i = 0; i < _dim; ++ i)
	{
		if (i)
			sout << "x";
		sout << "[" << _min [i] << "," << _max [i] << "]";
	}
	sout << ".\n";

	return;
} /* cublistfile::analyze */

std::ostream &cublistfile::describe (std::ostream &out)
{
	out << "\
The CUBE file format allows one to define sets of cubes in a human-readable\n\
and intuitive way. Each n-dimensional cube is defined as an n-tuple of\n\
integers which correspond to the coordinates of the lower left vertex\n\
of the cube with respect to the integral lattice. Each cube is assumed\n\
to have edges of length 1. The coordinates should be written in parentheses,\n\
e.g. (1,-2,0) corresponds to the cube [1,2]x[-2,-1]x[0,1] in R^3.\n\
The maximal supported dimension is " << capd::homology::Cube::MaxDim << ".\n";
	return out;
} /* cublistfile::describe */

bool cublistfile::compatible (const char *filename)
{
	using namespace capd::homology;

	// open the file
	std::ifstream f;
	f. open (filename, std::ios::in | std::ios::binary);
	if (!f)
		fileerror (filename);
	ignorecomments (f);

	// ignore the line with the word "dimension", if present
	if (f. peek () == 'd')
	{
		const char buf [] = "dimension";
		int pos = 0;
		while (buf [pos])
			if (f. get () != buf [pos ++])
				return false;
		ignoreline (f);
		ignorecomments (f);
	}
	
	// if there is nothing left in the file, ignore it
	if (f. eof ())
		return false;

	// if there is a bare number, check the first four cubes
	if (std::isdigit (f. peek ()) || (f. peek () == '-'))
	{
		const int maxdim = 128;
		coordinate coord [maxdim];
		int dim = -1;
		for (int i = 0; (i < 4) && !f. eof (); ++ i)
		{
			int d = readcoordinates (f, coord, maxdim, '\n');
			if ((d < 0) || (d >= maxdim))
				return false;
			if ((dim > 0) && (d != dim))
				return false;
			dim = d;
			ignorecomments (f);
		}
		return true;
	}

	// if there is an opening parenthesis, check if this is a cube
	int closing = closingparenthesis (f. peek ());
	if (closing != EOF)
	{
		// read the parenthesis
		f. get ();
		ignorecomments (f);
		if (!std::isdigit (f. peek ()) && (f. peek () != '-'))
			return false;
		while (std::isdigit (f. peek ()) || (f. peek () == '-') ||
			(f. peek () == ',') || (f. peek () == ' '))
			f. get ();
		if (f. peek () != closing)
			return false;
		f. get ();
		ignorecomments (f);
		if (!f. eof () && (closingparenthesis (f. peek ()) == EOF))
			return false;
		return true;
	}

	return false;
} /* cublistfile::compatible */

cubfile_traits<cublistfile> cublistfile::t;


// --------------------------------------------------
// --------------- TEXT LIST OF CELLS ---------------
// --------------------------------------------------

int cellistfile::readcubes (capd::homology::CubicalComplex &s) const
{
	using namespace capd::homology;

	const char *name = _filename. c_str ();
	std::ifstream in (name);

	in >> s;
	return 0;
} /* cellistfile::readcubes */

int cellistfile::dim () const
{
	using namespace capd::homology;

	// if the dimension is known then return it
	if (_dim)
		return _dim;

	// open the file to determine the dimension
	std::ifstream in (filename ());

	// read one cell from the file
	CubicalCell q;
	in >> q;
	in. close ();
	int d = q. spacedim ();
	if (d <= 0)
		throw "Unable to determine the dimension of cubes.";
	_dim = d;
	return d;
} /* cellistfile::dim */

void cellistfile::analyze () const
{
	using namespace capd::homology;

	// reset the analyzed data (just in case)
	_count = 0;
	_min. clear ();
	_max. clear ();

	// open the file and say what you are doing
	sout << "Scanning '" << filename () << "'...\n";
	std::ifstream in (filename ());
	ignorecomments (in);

	coordinate left [CubicalCell::MaxDim];
	coordinate right [CubicalCell::MaxDim];
	while (!in. eof ())
	{
		// read a cubical cell
		capd::homology::CubicalCell q;
		in >> q;
		ignorecomments (in);

		// make sure the underlying space has a nonzero dimension
		int d = q. spacedim ();
		if (d <= 0)
			continue;

		// update the dimension or verify its consistency
		if (!_dim)
			_dim = d;
		else if (_dim != d)
			throw "Inconsistent dimension of cubes.";

		// count the cubical cell
		++ _count;

		// extract the coordinates of the cubical cell
		q. leftcoord (left);
		q. rightcoord (right);
		
		// create the min/max coordinates if not defined, yet
		if (!_min. size ())
		{
			_min. assign (left, left + _dim);
			_max. assign (right, right + _dim);
		}
		
		// update the min/max coordinates otherwise
		else
		{
			for (int i = 0; i < _dim; ++ i)
			{
				if (_min [i] > left [i])
					_min [i] = left [i];
				if (_max [i] < right [i])
					_max [i] = right [i];
			}
		}
	}

	// show the result of the analysis of the set of cubical cells
	sout << _count << " cells in R^" << _dim << " in ";
	for (int i = 0; i < _dim; ++ i)
	{
		if (i)
			sout << "x";
		sout << "[" << _min [i] << "," << _max [i] << "]";
	}
	sout << ".\n";

	return;
} /* cellistfile::analyze */

std::ostream &cellistfile::describe (std::ostream &out)
{
	out << "\
The CELL file format allows one to define sets of cubical cells in a\n\
human-readable and intuitive way. Each k-dimensional cubical cell\n\
embedded in R^n is defined as a product of n intervals, either of length\n\
zero (degenerate intervals), or of length 1, with integral endpoints.\n\
In the text format, the product is written with the letter 'x', e.g.\n\
[1,2]x[1]x[-2,-1]. The cells can also be defined by specifying a pair of\n\
opposite corners, one with the minimal coordinates, and the other one\n\
with the maximal ones, e.g. [(1,1,-2)(2,1,-1)].\n\
The maximal supported dimension is " <<
capd::homology::CubicalCell::MaxDim << ".\n";
	return out;
} /* cellistfile::describe */

bool cellistfile::compatible (const char *filename)
{
	using namespace capd::homology;

	std::ifstream f;
	f. open (filename, std::ios::in | std::ios::binary);
	if (!f)
		fileerror (filename);
	ignorecomments (f);

	// make sure there is some parenthesis at the beginning
	int closing = closingparenthesis (f. peek ());
	if (closing == EOF)
		return false;
	f. get ();

	// check if this cell is defined by two opposite corners
	if (closingparenthesis (f. peek ()) != EOF)
	{
		f. get ();
		ignorecomments (f);
		if (std::isdigit (f. peek ()) || (f. peek () == '-'))
			return true;
		else
			return false;
	}
	
	// check if this is a product of intervals
	if (std::isdigit (f. peek ()) || (f. peek () == '-'))
	{
		// read the first end of the interval
		int left = 0;
		f >> left;
		
		// check for expected characters at the input
		if ((f. peek () != ' ') && (f. peek () != ',') &&
			(f. peek () != closing))
			return false;
		ignorecomments (f);
		
		// check if this is a non-degenerate interval
		if (f. peek () != closing)
		{
			// skip the comma if it is there
			if (f. peek () == ',')
			{
				f. get ();
				ignorecomments (f);
			}

			// read the right end of the interval
			if (!std::isdigit (f. peek ()) &&
				(f. peek () != '-'))
				return false;
			int right = 0;
			f >> right;
			ignorecomments (f);
		
			// verify that the interval is of length one
			if (right - left != 1)
				return false;
		}
		
		// read the closing parenthesis and check for 'x'
		f. get ();
		ignorecomments (f);
		if (f. peek () != 'x')
			return false;
		return true;
	}

	return false;
} /* cellistfile::compatible */

cubfile_traits<cellistfile> cellistfile::t;


// --------------------------------------------------
// -------------- BILL KALIES' BITCODE --------------
// --------------------------------------------------

static inline void readbitheader (istream &in, int &dim, int &depth,
	int &count)
{
	in >> dim;
	if (dim <= 0)
		throw "Incorrect bitcode dimension.";
	int nbits;
	in >> nbits;
	depth = nbits / dim;
	if (dim * depth != nbits)
		throw "Wrong number of bits in the bitcode file.";
	in >> count;
	capd::homology::ignorecomments (in);
	return;
} /* readbitheader */

template<class intType>
static inline void readbitcode (std::istream &in,
	intType *left, intType *right, int dim, int depth, intType maxcoord)
{
	using namespace capd::homology;

	// reset the interval for the point
	for (int i = 0; i < dim; ++ i)
	{
		left [i] = 0;
		right [i] = maxcoord;
	}

	// read the bits and narrow the point's coordinates
	for (int i = 0; i < depth; ++ i)
	{
		for (int d = 0; d < dim; ++ d)
		{
			int ch = in. get ();
			if (ch == '1')
				left [d] = (left [d] +
					((right [d] - left [d]) >> 1));
			else
				right [d] = (left [d] +
					((right [d] - left [d]) >> 1));
			ignorecomments (in);
		}
	}
	return;
} /* readbitcode */

int bitcodefile::readcubes (capd::homology::CubicalComplex &s) const
{
	using namespace capd::homology;

	// analyze the file to determine the dimension and coordinate scope
	if ((_dim <= 0) || !_min. size ())
		analyze ();
	if (_dim <= 0)
		throw "Unable to determine the dimension of the cubes.";

	// open the bitcode file and read its features
	std::ifstream in (_filename. c_str ());
	int dim, depth, count;
	readbitheader (in, dim, depth, count);

	// read the bit codes from the file and add them to the set
	coordinate *left = new coordinate [dim];
	coordinate *right = new coordinate [dim];
	const coordinate maxcoord = static_cast <coordinate> (1 << depth);
	while ((in. peek () == '0') || (in. peek () == '1'))
	{
		readbitcode (in, left, right, dim, depth, maxcoord);
		s. add (CubicalCell (Cube (left, dim)));
	}

	// deallocate memory and exit
	delete [] right;
	delete [] left;
	return 0;
} /* bitcodefile::readcubes */

int bitcodefile::readcubes (capd::homology::SetOfCubes &s) const
{
	using namespace capd::homology;

	// analyze the file to determine the dimension and coordinate scope
	if ((_dim <= 0) || !_min. size ())
		analyze ();
	if (_dim <= 0)
		throw "Unable to determine the dimension of the cubes.";

	// open the bitcode file and read its features
	std::ifstream in (_filename. c_str ());
	int dim, depth, count;
	readbitheader (in, dim, depth, count);

	// read the bit codes from the file and mark them in the bitmap
	coordinate *left = new coordinate [dim];
	coordinate *right = new coordinate [dim];
	const coordinate maxcoord = static_cast <coordinate> (1 << depth);
	while ((in. peek () == '0') || (in. peek () == '1'))
	{
		readbitcode (in, left, right, dim, depth, maxcoord);
		s. add (Cube (left, dim));
	}

	// deallocate memory and exit
	delete [] right;
	delete [] left;
	return 0;
} /* bitcodefile::readcubes */

int bitcodefile::readcubes (int *&sizes, char *&bytes, int padding,
	bool power2) const
{
	using namespace capd::homology;

	// analyze the file to determine the dimension and coordinate scope
	if ((_dim <= 0) || !_min. size ())
		analyze ();
	if (_dim <= 0)
		throw "Unable to determine the dimension of the cubes.";

	// compute the size and allocate memory for all the variables
	std::vector<int> offsetmult;
	createbitmap (sizes, bytes, padding, offsetmult, _dim, _min, _max,
		power2);

	// open the bitcode file and read its features
	std::ifstream in (_filename. c_str ());
	int dim, depth, count;
	readbitheader (in, dim, depth, count);

	// read the bit codes from the file and mark them in the bitmap
	int *left = new int [dim];
	int *right = new int [dim];
	const int maxcoord = 1 << depth;
	bool little = littleendian ();
	while ((in. peek () == '0') || (in. peek () == '1'))
	{
		readbitcode (in, left, right, dim, depth, maxcoord);
		markbit (left, offsetmult, _dim, padding, little, bytes);
	}

	// deallocate memory and exit
	delete [] right;
	delete [] left;
	return 0;
} /* bitcodefile::readcubes */

void bitcodefile::analyze () const
{
	using namespace capd::homology;

	// reset the analyzed data (just in case)
	_dim = 0;
	_count = 0;
	_min. clear ();
	_max. clear ();

	// open the file and read the information
	std::ifstream in (filename ());
	in >> _dim;
	int nbits = 0;
	in >> nbits;
	int depth = nbits / _dim;
	in >> _count;
	if (!in. good ())
		throw "Can't analyze the bitcode file.";
	in. close ();

	// compute the bounding box based on this information
	_min. assign (_dim, 0);
	_max. assign (_dim, 1 << depth);

	return;
} /* bitcodefile::analyze */

std::ostream &bitcodefile::describe (std::ostream &out)
{
	out << "\
The BITCODE file format contains the definition of a set of full cubes encoded\n\
in a binary tree as bit codes. At the beginning of the file, there are\n\
three numbers, indicating the space dimension, the depth of the bitcodes,\n\
and the number of cubes. Please, refer to the work by Bill Kalies for the\n\
details on the bit-code encoding of the cubes.\n";
	return out;
} /* bitcodefile::describe */

bool bitcodefile::compatible (const char *filename)
{
	using namespace capd::homology;

	// open the file
	std::ifstream f;
	f. open (filename, std::ios::in | std::ios::binary);
	if (!f)
		fileerror (filename);
	ignorecomments (f);

	// make sure that there are three lines with reasonable numbers:
	// dimension, depth, number of cubes (0 for no limit)
	int minimum [] = {1, 1, 1};
	int maximum [] = {128, 10240, 0};
	for (int i = 0; i < 3; ++ i)
	{
		if (!std::isdigit (f. peek ()))
			return false;
		int number = 0;
		f >> number;
		if (minimum [i] && (number < minimum [i]))
			return false;
		if (maximum [i] && (number > maximum [i]))
			return false;
		while (f. peek () != '\n')
		{
			int ch = f. get ();
			if (!std::isspace (ch) || (ch == EOF))
				return false;
		}
		ignorecomments (f);
	}

	// check if the next line is a sequence of 1's and 0's
	while ((f. peek () != '\n') && (f. peek () != EOF))
	{
		int ch = f. get ();
		if (!std::isspace (ch) && (ch != '0') && (ch != '1'))
			return false;
	}

	return true;
} /* bitcodefile::compatible */

cubfile_traits<bitcodefile> bitcodefile::t;


// --------------------------------------------------
// ----------------- WINDOWS BITMAP -----------------
// --------------------------------------------------

int winbmpfile::count () const
{
	if (_count >= 0)
		return _count;
	capd::homology::bmpfile f;
	if (f. open (_filename. c_str (), ReadOnly, 1) < 0)
		throw "Unable to open the BMP file.";
	_count = 0;
	f. invertedpicture ();
	int height = f. picture_height ();
	int width = f. picture_width ();
	for (int y = 0; y < height; ++ y)
	{
		for (int x = 0; x < width; ++ x)
		{
			if (f. getpixel (x, y) < 0x800000)
				++ _count;
		}
	}
	if (!_min. size ())
	{
		_min. push_back (0);
		_min. push_back (0);
		_max. push_back (width);
		_max. push_back (height);
	}
	return _count;
} /* winbmpfile::count */

int winbmpfile::boundingbox (int *mincoord, int *maxcoord) const
{
	if (_min. size ())
		return cubfile::boundingbox (mincoord, maxcoord);

	capd::homology::bmpfile f;
	if (f. open (_filename. c_str (), ReadOnly, 1) < 0)
		throw "Unable to open the BMP file.";
	_min. clear ();
	_max. clear ();
	_min. push_back (0);
	_min. push_back (f. picture_width ());
	_max. push_back (0);
	_max. push_back (f. picture_height ());
	return cubfile::boundingbox (mincoord, maxcoord);
} /* winbmpfile::boundingbox */

int winbmpfile::readcubes (capd::homology::SetOfCubes &s) const
{
	using namespace capd::homology;

	capd::homology::bmpfile f;
	if (f. open (_filename. c_str ()) < 0)
		throw "Unable to open the BMP file.";
	int c = 0;
	f. invertedpicture ();
	capd::homology::coordinate coord [2];
	int height = f. picture_height ();
	int width = f. picture_width ();
	for (int y = 0; y < height; ++ y)
	{
		for (int x = 0; x < width; ++ x)
		{
			if (f. getpixel (x, y) < 0x800000)
			{
				coord [0] = static_cast<coordinate> (x);
				coord [1] = static_cast<coordinate> (y);
				s. add (Cube (coord, 2));
				++ c;
			}
		}
	}

	// update the number of cubes and the bounding box if not known, yet
	if (_count != c)
		_count = c;
	if (!_min. size ())
	{
		_min. push_back (0);
		_min. push_back (f. picture_width ());
		_max. push_back (0);
		_max. push_back (f. picture_height ());
	}
	return 0;
} /* winbmpfile::readcubes */

int winbmpfile::readcubes (int *&sizes, char *&bytes, int padding,
	bool power2) const
{
	// set the default padding value
	if (padding <= 0)
		padding = 1;
	const int MaxPadding = sizeof (long) << 2;
	if (padding > MaxPadding)
		throw "Too large byte padding requested.";

	// open the bitmap file using the 'bmpfile' data structure
	capd::homology::bmpfile f;
	if (f. open (_filename. c_str ()) < 0)
		throw "Unable to open the BMP file.";
	f. invertedpicture ();

	// fill out the table of sizes
	sizes = new int [2];
	sizes [0] = f. picture_width ();
	sizes [1] = f. picture_height ();

	// verify if the size of the bitmap is a power of 2 if necessary
	if (power2)
	{
		if (((sizes [0] + 31) / 32) * 32 != sizes [1])
			throw "Non-square bitmap cannot be used "
				"with this homology engine.";
		int size = 1;
		while (size < sizes [1])
			size <<= 1;
		if (size != sizes [1])
			throw "The bitmap size should be "
				"a power of 2 for this homology engine.";
	}

	// the number of bytes per row and the total number of bytes
//	int bmprowbytes = ((sizes [0] + 0x1F) & ~0x1F) >> 3;
	const int mask = (padding << 3) - 1;
	int rowbytes = ((sizes [0] + mask) & ~mask) >> 3;
	int nbytes = rowbytes * sizes [1];

	// allocate memory for the bitmap buffer
	bytes = new char [nbytes];

	// if this is a 1-bit bmp image, transfer bits directly
	if (f. getbitsperpixel () == 1)
	{
		// should the bitmap be inverted so that the nonzero bits
		// actually correspond to the darker color?
		int32 *palette = f. getpalette ();
		bool invert = palette && (palette [0] < palette [1]);

		// compute the mask for the last bytes of each row
		int lastbyte = padding - 1 -
			(rowbytes - ((sizes [0] + 0x07) >> 3));
		unsigned char rowmask [MaxPadding];
		for (int i = 0; i < padding; ++ i)
			rowmask [i] = (i < lastbyte) ? '\xFF' : '\0';
		int lastbits = (((rowbytes << 3) - sizes [0])) & 0x07;
		rowmask [lastbyte] = '\xFF' << lastbits;
		bool usemask = (lastbyte != (padding - 1)) || (lastbits != 0);
		if (invert)
		{
			for (int i = 0; i < padding; ++ i)
				rowmask [i] = ~rowmask [i];
		}

		unsigned rowlength = f. getrowlength ();
		int nrows = sizes [1];
		unsigned char *curbytes =
			reinterpret_cast<unsigned char *> (bytes);
		for (int i = 0; i < nrows; ++ i)
		{
			// copy the row of pixels
			memcpy (curbytes, f. getrow (i), rowlength);
			// make sure the extra pixels are reset to background
			if (usemask)
			{
				curbytes += (rowbytes - padding);
				const unsigned char *rowmaskbyte = rowmask;
				if (invert)
				{
					for (int j = 0; j < padding; ++ j)
						*(curbytes ++) |=
							*(rowmaskbyte ++);
				}
				else
				{
					for (int j = 0; j < padding; ++ j)
						*(curbytes ++) &=
							*(rowmaskbyte ++);
				}
			}
			// otherwise merely count this row (in bytes)
			else
				curbytes += rowlength;
		}

	//	std::ofstream df;
	//	df. open ("debug.bin", std::ios::binary | std::ios::out);
	//	df. write (bytes, nbytes);
	//	df. close ();

		if (invert)
		{
			int32 *words = reinterpret_cast<int32 *> (bytes);
			int nwords = nbytes >> 2;
			while (nwords --)
			{
				*words = ~*words;
				++ words;
			}
		}
		flipbytes (reinterpret_cast<unsigned char *> (bytes), nbytes);
	}

	// if a more than 1-bit bitmap, get each pixel separately
	else
	{
		std::memset (bytes, 0, nbytes);
		int width = sizes [0];
		int height = sizes [1];
		int rowwidth = rowbytes << 3;
		for (int y = 0; y < height; ++ y)
		{
			for (int x = 0; x < width; ++ x)
			{
				if (f. getpixel (x, y) < 0x800000)
				{
					int bit = y * rowwidth + x;
					bytes [bit >> 3] |= 1 << (bit & 7);
				}
			}
		}
	}

	// flip byte order in words if necessary
	if (!littleendian ())
		flipwords (reinterpret_cast<unsigned long *> (bytes),
			nbytes / sizeof (unsigned long));

	return 0;
} /* winbmpfile::readcubes */

std::ostream &winbmpfile::describe (std::ostream &out)
{
	out << "\
In the popular Windows BMP file format, a set of cubes (actually, squares)\n\
is defined as the set of all the black pixels in the picture. If the bitmap\n\
is not black-and-white, then the red component is tested only, and all the\n\
pixels which are darker than 128 (50%) are treated as black.\n";
	return out;
} /* winbmpfile::describe */

bool winbmpfile::compatible (const char *filename)
{
	std::ifstream f;
	f. open (filename, std::ios::in | std::ios::binary);
	if (!f)
		capd::homology::fileerror (filename);
	int ch1 = f. get ();
	int ch2 = f. get ();
	if ((ch1 == 'B') && (ch2 == 'M'))
		return true;
	return false;
} /* winbmpfile::compatible */

cubfile_traits<winbmpfile> winbmpfile::t;


// --------------------------------------------------
// ----------------- MROZEK'S BITMAP -----------------
// --------------------------------------------------

int bmdheader::readbytes (std::istream &f, int n) const
{
	int number = 0;
	if (little)
	{
		for (int i = 0; i < n; ++ i)
			number |= f. get () << (i << 3);
	}
	else
	{
		for (int i = 0; i < n; ++ i)
		{
			number <<= 8;
			number |= f. get ();
		}
	}
	return number;
} /* bmdheader::readbytes */

bmdheader::bmdheader (const char *filename)
{
	ifstream f;
	f. open (filename, std::ios::in | std::ios::binary);
	if (!f)
		capd::homology::fileerror (filename);
	int byte1 = f. get ();
	int byte2 = f. get ();
	if ((byte1 == 'B') && (byte2 == 'D'))
		little = true;
	else if ((byte1 == 'D') && (byte2 == 'B'))
		little = false;
	else
		throw "Wrong identifier of a BMD file.";
	dim = readbytes (f, 4);
	length = readbytes (f, 4);
	width. push_back (readbytes (f, 4));
	zerowidth = readbytes (f, 4);
	for (int i = 1; i < dim; ++ i)
		width. push_back (readbytes (f, 4));
	offset = 2 + 4 * (dim + 3);
	return;
} /* bmdheader::bmdheader */

std::ostream &operator << (std::ostream &out, const bmdheader &header)
{
	out << "BMD Header (" << (header. little ? "little" : "big") <<
		" endian):\n";
	out << "\tdim = " << header. dim << "\n";
	for (int i = 0; i < header. dim; ++ i)
		out << (i ? " x " : "\tsize = ") << header. width [i];
	out << "\n";
	out << "\tpadded zero width = " << header. zerowidth << "\n";
	out << "\tdata offset = " << header. offset << "\n";
	out << "\tdata length (in words) = " << header. length << "\n";
	return out;
} /* opeartor << */


// --------------------------------------------------

int bmdfile::count () const
{
	if (_count >= 0)
		return _count;
	_count = 0;
	std::ifstream f;
	f. open (_filename. c_str (), std::ios::in | std::ios::binary);
	f. seekg (header. offset, std::ios_base::beg);
	int ch;
	while ((ch = f. get ()) != EOF)
		_count += capd::homology::bitcountbyte (ch);
	return _count;
} /* bmdfile::count */

std::ostream &bmdfile::describe (std::ostream &out)
{
	out << "\
In the BMD format, a set of cubes is defined as the black pixels in a\n\
multi-dimensional bitmap format designed by M. Mrozek.\n\
WARNING: The data is interpreted in a different way on different\n\
processors (big/little endian), and it depends on the template\n\
parameters that appear in the code which was saving the bitmap.\n";
	return out;
} /* bmdfile::describe */

int bmdfile::readcubes (capd::homology::SetOfCubes &s) const
{
	using namespace capd::homology;

	if (_dim > Cube::MaxDim)
		throw "Space dimension too high for PP cubes.";
	// line length in 32-bit words
	const int linelength = (header. zerowidth + 31) >> 5;
	if (!linelength)
		throw "Trying to read a BMD file with padding < 32-bit.";
	coordinate coord [Cube::MaxDim];
	for (int i = 1; i < _dim; ++ i)
		coord [i] = 0;

	std::ifstream f;
	f. open (_filename. c_str (), std::ios::in | std::ios::binary);
	f. seekg (header. offset, std::ios_base::beg);

	// process all the lines from the input file
	for (int offset = 0; offset < header. length; offset += linelength)
	{
		// correct coordinate overflow if any
		int c = 1;
		while (coord [c] >= header. width [c])
		{
			coord [c] = 0;
			++ (coord [++ c]);
		}

		// process one line from the input file
		for (int j = 0; j < linelength; ++ j)
		{
			// process one word from the line
			long word = header. readbytes (f, 4);
			if (!f)
			{
				// there was an error in an early version
				// of the "cub2bmd" program by M. Mrozek
				if (offset == 4 * header. length)
					return 0;
				fileerror (filename (), "read");
			}
			if (!word)
				continue;
			for (int bit = 0; bit < 32; ++ bit)
			{
				if (!(word & (1 << bit)))
					continue;
				coord [0] = (j << 5) + bit;
				s. add (Cube (coord, _dim));
			}
		}

		// update the first coordinate to correspond to the next line
		// (overflow is corrected at the beginning of the loop)
		++ coord [1];
	}

	return 0;
} /* bmdfile::readcubes */

int bmdfile::readcubes (int *&sizes, char *&bytes, int padding,
	bool power2) const
{
	// WARNING: This function does not verify if the data is consistent!

	// copy the sizes from the header
	sizes = new int [_dim];
	std::copy (header. width. begin (), header. width. end (), sizes);

	// open the BMD file
	std::ifstream in;
	in. open (_filename. c_str (), std::ios::in | std::ios::binary);
	in. seekg (header. offset, std::ios_base::beg);

	// compute the length of each line in the file and in the memory
	int fileline = 0;
	int memoryline = 0;
	if (padding > 4)
	{
		fileline = ((sizes [0] + 0x1F) & ~0x1F) >> 3;
		const int mask = (padding << 3) - 1;
		memoryline = ((sizes [0] + mask) & ~mask) >> 3;
	}
	
	// compute the preliminary number of bytes for the buffer
	int nbytes = header. length << 2;

	// if the line length in the file equals the line length
	// in the memory, then the file can be read directly
	if (fileline == memoryline)
	{
		bytes = new char [nbytes];
		in. read (bytes, header. length << 2);
	}
	// otherwise, each line should be read separately to the memory
	else
	{
		// adjust the size of the memory buffer and allocate memory
		nbytes = (int) (nbytes * (long) memoryline / fileline);
		bytes = new char [nbytes];

		// read the bits from the file
		int offset = 0;
		while (offset < nbytes)
		{
			in. read (bytes + offset, fileline);
			memset (bytes + offset + fileline, 0,
				memoryline - fileline);
			offset += memoryline;
		}
	}
	in. close ();

	// flip byte order in words if necessary
	if (header. little != littleendian ())
		flipwords (reinterpret_cast<unsigned long *> (bytes),
			nbytes / sizeof (unsigned long));

	return 0;
} /* bmdfile::readcubes */

bool bmdfile::compatible (const char *filename)
{
	std::ifstream f;
	f. open (filename, std::ios::in | std::ios::binary);
	if (!f)
		capd::homology::fileerror (filename);
	int ch1 = f. get ();
	int ch2 = f. get ();
	if ((ch1 == 'B') && (ch2 == 'D'))
		return true;
	if ((ch1 == 'D') && (ch2 == 'B'))
		return true;
	return false;
} /* bmdfile::compatible */

cubfile_traits<bmdfile> bmdfile::t;


// --------------------------------------------------
// ----------------- BITMAP BUFFER ------------------
// --------------------------------------------------

int cubitmap::count () const
{
	if (_count >= 0)
		return _count;
	_count = 0;
	const char *bufend = buf + buflength;
	for (const char *ptr = buf; ptr != bufend; ++ ptr)
		_count += capd::homology::bitcountbyte (*ptr);
	return _count;
} /* cubitmap::count */

std::ostream &cubitmap::describe (std::ostream &out)
{
	out << "\
This class is a wrapper for a memory bitmap buffer.\n";
	return out;
} /* cubitmap::describe */

int cubitmap::readcubes (capd::homology::SetOfCubes &s) const
{
	using namespace capd::homology;

	if (_dim > Cube::MaxDim)
		throw "Space dimension too high for PP cubes.";
	const int linelength = (_max [0]) >> 3; // in bytes
	if (!linelength)
		throw "Trying to analyze a buffer with padding < 8-bit.";
	if (buflength % linelength)
		throw "Buffer length is not a multiple of line length.";
	coordinate coord [Cube::MaxDim];
	for (int i = 1; i < _dim; ++ i)
		coord [i] = 0;

	// process all the lines from the memory buffer
	const char *bufend = buf + buflength;
	for (const char *ptr = buf; ptr != bufend; /* sic! */)
	{
		// correct coordinate overflow if any
		int c = 1;
		while (coord [c] >= _max [c])
		{
			coord [c] = 0;
			++ (coord [++ c]);
		}

		// process one line from the buffer
		for (int j = 0; j < linelength; ++ j)
		{
			// process one byte from the line
			int ch = *ptr;
			++ ptr;
			if (!ch)
				continue;
			for (int bit = 0; bit < 8; ++ bit)
			{
				if (!(ch & (1 << bit)))
					continue;
				coord [0] = (j << 3) + bit;
				s. add (Cube (coord, _dim));
			}
		}

		// update the first coordinate to correspond to the next line
		// (overflow is corrected at the beginning of the loop)
		++ (coord [1]);
	}
	
	return 0;
} /* cubitmap::readcubes */

int cubitmap::readcubes (int *&sizes, char *&bytes, int /* padding */,
	bool /* power2 */) const
{
	// WARNING: This function does not verify if the data is consistent!

	// copy the sizes from the header
	sizes = new int [_dim];
	std::copy (_max. begin (), _max. end (), sizes);

	// copy the data buffer
	bytes = new char [buflength];
	std::memcpy (bytes, buf, buflength);

	// flip byte order in words if necessary
	if (!littleendian ())
		flipwords (reinterpret_cast<unsigned long *> (bytes),
			buflength / sizeof (unsigned long));

	return 0;
} /* cubitmap::readcubes */


} // namespace homengin
} // namespace capd

/// @}

