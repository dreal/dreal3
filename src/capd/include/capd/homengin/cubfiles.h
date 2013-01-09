/// @addtogroup HomologyEngines
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file cubfiles.h
///
/// This file defines various types of cubical sets whose homology can be
/// computed by homology engines.
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


#ifndef _CAPD_HOMENGIN_CUBFILES_H_ 
#define _CAPD_HOMENGIN_CUBFILES_H_ 

#include "capd/homology/config.h"
#include "capd/homology/textfile.h"
#include "capd/homology/timeused.h"
#include "capd/homology/arg.h"
#include "capd/homology/homtools.h"

#include <cstdlib>
#include <ctime>
#include <new>
#include <exception>
#include <iostream>
#include <fstream>
#include <iomanip>
#include <vector>
#include <sstream>
#include <algorithm>

namespace capd {
namespace homengin {

// --------------------------------------------------
// -------------- ABSTRACT CUBICAL SET --------------
// --------------------------------------------------

/// An abstract class that is inherited by all the cubical sets.
class cubfile
{
public:
	/// The default constructor.
	cubfile (const char *_filename);

	/// The destructor.
	virtual ~cubfile ();

/*	/// Copy constructor.
	cubfile (const cubfile &c);

	/// Assignment operator.
	cubfile &operator = (const cubfile &c);
*/
	/// What is the name of the associated disk file?
	const char *filename () const
	{
		return _filename. c_str ();
	}
	
	/// What is the dimension of the set of cubes?
	virtual int dim () const
	{
		if (_dim > 0)
			return _dim;
		throw "Undefined dimension of a set of cubes.";
	}
	
	/// How many cubes are there in the set?
	virtual int count () const
	{
		if (_count >= 0)
			return _count;
		throw "Undefined number of cubes in a set.";
	}

	/// Is this a bitmap type of set of cubes?
	virtual bool bitmaptype () const
	{
		throw "Undefined bitmapness of a set of cubes.";
	}

	/// Is this a set of elementary cubes, as opposed to full cubes?
	virtual bool elementary () const
	{
		throw "Undefined type of a set of cubes.";
	}
	
	/// Does this set include the definition of space wrapping?
	virtual bool spacewrapping () const
	{
		return (_wrapping. size () != 0);
	}

	/// Fills in the space wrapping table if applicable.
	/// Returns the address of the table.
	virtual int *spacewrapping (int *table) const
	{
		if (_wrapping. size ())
		{
			std::copy (_wrapping. begin (), _wrapping. end (),
				table);
			return table;
		}
		throw "Unknown space wrapping of a set of cubes.";
	}

	/// Sets the space wrapping according to the given table.
	virtual void setwrapping (const int *table, int count = 0)
	{
		_wrapping. clear ();
		int d = count ? count : dim ();
		_wrapping. assign (table, table + d);
		return;
	}

	/// Determines the bounding box of the set of cubes.
	/// All the coordinates of cubes are at least 'min',
	/// and strictly smaller than 'max'.
	/// Returns 0.
	virtual int boundingbox (int *mincoord, int *maxcoord) const
	{
		if (_min. size () && _max. size ())
		{
			if (mincoord)
				std::copy (_min. begin (), _min. end (),
					mincoord);
			if (maxcoord)
				std::copy (_max. begin (), _max. end (),
					maxcoord);
			return 0;
		}
		throw "Undefined bounding box of a set of cubes.";
	}

	/// Determine the volume of the bounding box of the set of cubes.
	/// The volume is measured in cubes or in chunks of cubes
	/// (e.g., chunk = 8 measures the bitmap size in bytes).
	/// If requested, the width in each direction is rounded up
	/// to the nearest power of 2 while calculating the volume.
	int volume (int chunk = 0, bool power2 = false) const;

	/// The name of this type of a cubical set.
	static const char *name ()
	{
		return "unknown set of cubes";
	}

	/// Describes this particular type of a set of cubes.
	static std::ostream &describe (std::ostream &out)
	{
		out << "This is an unknown set of cubes.";
		return out;
	}
	
	/// Verifies if the file format is compatible with this cubfile type.
	static bool compatible (const char *filename)
	{
		return false;
	}

	/// Reads a set of cubical cells from the file.
	virtual int readcubes (capd::homology::CubicalComplex &s) const
	{
		throw "Unable to read a set of cells.";
	}

	/// Reads a set of cubes from the file.
	virtual int readcubes (capd::homology::SetOfCubes &s) const
	{
		throw "Unable to read a set of cubes.";
	}

	/// Reads a bitmap from a file. Allocates memory for the table
	/// of sizes, and for the bytes of the bitmap. If padding > 0,
	/// then padds the lines to a multiple of the given number of bytes.
	/// If requested, additionally rounds the sizes in each direction
	/// up to the nearest power of 2.
	virtual int readcubes (int *&sizes, char *&bytes, int padding = 0,
		bool power2 = false) const
	{
		throw "Unable to read a bitmap set of cubes.";
	}

protected:
	/// The name of the corresponding disk file.
	std::string _filename;

	/// The dimension of the space, 0 if unknown.
	mutable int _dim;

	/// The number of cubes in the set, -1 if unknown.
	mutable int _count;

	/// The minimal coordinates of the cubes' corners (bounding box).
	mutable std::vector<int> _min;

	/// The maximal coordinates of the cubes' corners (bounding box).
	mutable std::vector<int> _max;

	/// The space wrapping information if any.
	mutable std::vector<int> _wrapping;

}; /* class cubfile */

// --------------------------------------------------

inline cubfile::cubfile (const char *filename): _filename (filename),
	_dim (0), _count (-1), _min (), _max (), _wrapping ()
{
	return;
} /* cubfile::cubfile */

inline cubfile::~cubfile ()
{
	return;
} /* cubfile::~cubfile */


// --------------------------------------------------
// ------------- TYPES OF CUBICAL SETS --------------
// --------------------------------------------------

/// A class that holds pointers to the traits of all the cubical file types.
class cubtype
{
public:
	/// The type of a list of engines.
	typedef std::vector<const cubtype *> cubtypelist;

	/// A list of all the engines that have been defined so far.
	static cubtypelist cubtypes;

protected:
	/// The constructor: Add the cubical file traits to the list.
	cubtype ()
	{
		cubtypes. push_back (this);
		return;
	}

	/// The destructor: Remove the cubical file traits from the list.
	virtual ~cubtype ()
	{
		cubtypelist::iterator it = find (cubtypes. begin (),
			cubtypes. end (), this);
		if (it != cubtypes. end ())
			cubtypes. erase (it);
		return;
	}

public:
	/// The name of the set of cubes.
	virtual const char *name () const = 0;

	/// Describe the given type of cubical sets.
	virtual std::ostream &describe (std::ostream &out) const = 0;
	
	/// Verifies if the file format is compatible with this cubfile type.
	virtual bool compatible (const char *filename) const = 0;

	/// Creates a new cubfile object of the desired type.
	virtual cubfile *newcubfile (const char *filename) const = 0;

	/// Shows a list of available cubical set types with descriptions.
	static std::ostream &showlist (std::ostream &out,
		const cubtype::cubtypelist &types = cubtype::cubtypes);

	/// Creates an appropriate cubical set corresponding to the given file.
	/// Returns the address of a new object.
	/// Throws an exception in case of failure.
	static cubfile *newfile (const char *filename,
		const cubtype::cubtypelist &types = cubtype::cubtypes);

}; /* class cubtypes */

/// This class defines some common properties of the corresponding
/// classes which define various types of sets of cubes.
template <class cubfileT>
class cubfile_traits: public cubtype
{
public:
	/// The default constructor.
	cubfile_traits ()
	{
		return;
	}

	/// The destructor.
	~cubfile_traits ()
	{
		return;
	}

	/// The name of the corresponding cubical set.
	const char *name () const
	{
		return cubfileT::name ();
	}

	/// Describe the given type of cubical sets.
	std::ostream &describe (std::ostream &out) const
	{
		return cubfileT::describe (out);
	}

	/// Verifies if the file format is compatible with this cubfile type.
	bool compatible (const char *filename) const
	{
		return cubfileT::compatible (filename);
	}

	/// Creates a new cubfile object of the desired type.
	cubfile *newcubfile (const char *filename) const
	{
		return new cubfileT (filename);
	}

}; /* class cubfile_traits */


// --------------------------------------------------
// --------------- TEXT LIST OF CUBES ---------------
// --------------------------------------------------

/// Text list of cubes.
class cublistfile: public cubfile
{
public:
	/// The constructor.
	cublistfile (const char *filename);

	/// What is the dimension of the set of cubes?
	int dim () const;
	
	/// How many cubes are there in the set?
	int count () const
	{
		if (_count < 0)
			analyze ();
		return _count;
	}

	/// Is this a bitmap type of set of cubes?
	bool bitmaptype () const
	{
		return false;
	}

	/// Is this a set of elementary cubes, as opposed to full cubes?
	bool elementary () const
	{
		return false;
	}
	
	/// Determines the bounding box of the set of cubes.
	int boundingbox (int *mincoord, int *maxcoord) const
	{
		if (!_min. size ())
			analyze ();
		return cubfile::boundingbox (mincoord, maxcoord);
	}

	/// The name of this type of a cubical set.
	static const char *name ()
	{
		return "text list of cubes";
	}

	/// Describes this particular type of a set of cubes.
	static std::ostream &describe (std::ostream &out);

	/// Verifies if the file format is compatible with this cubfile type.
	static bool compatible (const char *filename);

	/// Reads a set of cubical cells from the file.
	int readcubes (capd::homology::CubicalComplex &s) const;

	/// Reads a cubical set from the file.
	int readcubes (capd::homology::SetOfCubes &s) const;

	/// Reads a bitmap from a file.
	int readcubes (int *&sizes, char *&bytes, int padding = 0,
		bool power2 = false) const;

private:
	/// Analyzes the file to determine the number of cubes
	/// and the scope of their coordinates.
	void analyze () const;

	/// Add this type of a cubical set to the list.
	static cubfile_traits<cublistfile> t;

}; /* class cublistfile */

// --------------------------------------------------

inline cublistfile::cublistfile (const char *filename): cubfile (filename)
{
	return;
} /* cublistfile::cublistfile */


// --------------------------------------------------
// --------------- TEXT LIST OF CELLS ---------------
// --------------------------------------------------

/// Text list of cubical cells.
class cellistfile: public cubfile
{
public:
	/// The constructor.
	cellistfile (const char *filename);

	/// What is the dimension of the set of cubes?
	int dim () const;

	/// How many cubes are there in the set?
	int count () const
	{
		if (_count < 0)
			analyze ();
		return _count;
	}

	/// Is this a bitmap type of set of cubes?
	bool bitmaptype () const
	{
		return false;
	}

	/// Is this a set of elementary cubes, as opposed to full cubes?
	bool elementary () const
	{
		return true;
	}

	/// Determines the bounding box of the set of cubical cells.
	int boundingbox (int *mincoord, int *maxcoord) const
	{
		if (!_min. size ())
			analyze ();
		return cubfile::boundingbox (mincoord, maxcoord);
	}

	/// The name of this type of a cubical set.
	static const char *name ()
	{
		return "text list of cubical cells";
	}

	/// Describes this particular type of a set of cubes.
	static std::ostream &describe (std::ostream &out);

	/// Verifies if the file format is compatible with this cubfile type.
	static bool compatible (const char *filename);

	/// Reads a set of cubical cells from the file.
	int readcubes (capd::homology::CubicalComplex &s) const;

	/// Reads a cubical set from the file.
	int readcubes (capd::homology::SetOfCubes &s) const
	{
		throw "Trying to read cubical cells as a set of full cubes.";
	}

	/// Reads a bitmap from a file.
	int readcubes (int *&sizes, char *&bytes, int padding = 0,
		bool power2 = false) const
	{
		throw "Trying to read cubical cells as a bitmap.";
	}

private:
	/// Analyzes the file to determine the number of cubes
	/// and the scope of their coordinates.
	void analyze () const;

	/// Add this type of a cubical set to the list.
	static cubfile_traits<cellistfile> t;

}; /* class cellistfile */

// --------------------------------------------------

inline cellistfile::cellistfile (const char *filename): cubfile (filename)
{
	return;
} /* cellistfile::cellistfile */


// --------------------------------------------------
// -------------- BILL KALIES' BITCODE --------------
// --------------------------------------------------

/// Text-encoded bitcodes.
class bitcodefile: public cubfile
{
public:
	/// The constructor.
	bitcodefile (const char *filename);

	/// What is the dimension of the set of cubes?
	int dim () const
	{
		if (_dim <= 0)
			analyze ();
		return _dim;
	}

	/// How many cubes are there in the set?
	int count () const
	{
		if (_count < 0)
			analyze ();
		return _count;
	}

	/// Is this a bitmap type of set of cubes?
	bool bitmaptype () const
	{
		return false;
	}

	/// Is this a set of elementary cubes, as opposed to full cubes?
	bool elementary () const
	{
		return false;
	}

	/// The name of this type of a cubical set.
	static const char *name ()
	{
		return "text bitcodes";
	}

	/// Describes this particular type of a set of cubes.
	static std::ostream &describe (std::ostream &out);

	/// Verifies if the file format is compatible with this cubfile type.
	static bool compatible (const char *filename);

	/// Reads a set of cubical cells from the file.
	int readcubes (capd::homology::CubicalComplex &s) const;

	/// Reads a cubical set from the file.
	int readcubes (capd::homology::SetOfCubes &s) const;

	/// Reads a bitmap from a file.
	int readcubes (int *&sizes, char *&bytes, int padding = 0,
		bool power2 = false) const;

private:
	/// Analyzes the file to determine the number of cubes
	/// and the scope of their coordinates.
	void analyze () const;

	/// Add this type of a cubical set to the list.
	static cubfile_traits<bitcodefile> t;

}; /* class bitcodefile */

// --------------------------------------------------

inline bitcodefile::bitcodefile (const char *filename): cubfile (filename)
{
	return;
} /* bitcodefile::bitcodefile */


// --------------------------------------------------
// ----------------- WINDOWS BITMAP -----------------
// --------------------------------------------------

/// Windows bitmap as a set of full cubes.
class winbmpfile: public cubfile
{
public:
	/// The constructor.
	winbmpfile (const char *filename);

	/// How many cubes are there in the set?
	int count () const;

	/// Is this a bitmap type of set of cubes?
	bool bitmaptype () const
	{
		return true;
	}

	/// Is this a set of elementary cubes, as opposed to full cubes?
	bool elementary () const
	{
		return false;
	}

	/// Determine the bounding box of the set of cubes.
	int boundingbox (int *mincoord, int *maxcoord) const;
	
	/// The name of this type of a cubical set.
	static const char *name ()
	{
		return "windows bitmap";
	}

	/// Describes this particular type of a set of cubes.
	static std::ostream &describe (std::ostream &out);

	/// Verifies if the file format is compatible with this cubfile type.
	static bool compatible (const char *filename);

	/// Reads a set of cubical cells from the file.
	int readcubes (capd::homology::CubicalComplex &s) const
	{
		throw "Trying to read a set of cells from a Win BMP file.";
	}

	/// Read a cubical set from the file.
	int readcubes (capd::homology::SetOfCubes &s) const;

	/// Reads a bitmap from a file.
	int readcubes (int *&sizes, char *&bytes, int padding = 0,
		bool power2 = false) const;

private:
	/// Add this type of a cubical set to the list.
	static cubfile_traits<winbmpfile> t;

}; /* class winbmpfile */

// --------------------------------------------------

inline winbmpfile::winbmpfile (const char *filename): cubfile (filename)
{
	_dim = 2;
	return;
} /* winbmpfile::winbmpfile */


// --------------------------------------------------
// ----------------- MROZEK'S BITMAP -----------------
// --------------------------------------------------

/// This class helps interpret files in the BMD format defined
/// by Marian Mrozek. In the constructor, the header of a BMD file
/// is read and analyzed. Based on the information from the header,
/// a procedure for reading an n-byte integer is provided, which is
/// useful for reading the actual bitmap data.
class bmdheader
{
public:
	/// The only allowed constructor.
	bmdheader (const char *filename);

	/// Is this little endian data?
	bool little;
	
	/// The offset of binary data in the file.
	int offset;
	
	/// The dimension of the bitmap.
	int dim;

	/// The length of the bitmap in the file.
	int length;

	/// The width of the actual bitmap in the first direction.
	int zerowidth;
	
	/// The size of the picture in each direction.
	std::vector<int> width;

	/// Reads an n-byte integer from the file.
	int readbytes (std::istream &f, int n) const;

}; /* class bmdheader */

// --------------------------------------------------

/// Writes the information collected in the BMD header class
/// to an output stream.
std::ostream &operator << (std::ostream &out, const bmdheader &header);

// --------------------------------------------------


/// Marian Mrozek's BMD binary file as a set of full cubes.
class bmdfile: public cubfile
{
public:
	/// The constructor.
	bmdfile (const char *filename);

	/// How many cubes are there in the set?
	int count () const;

	/// Is this a bitmap type of set of cubes?
	bool bitmaptype () const
	{
		return true;
	}

	/// Is this a set of elementary cubes, as opposed to full cubes?
	bool elementary () const
	{
		return false;
	}

	/// The name of this type of a cubical set.
	static const char *name ()
	{
		return "multi-dimensional bitmap";
	}

	/// Describes this particular type of a set of cubes.
	static std::ostream &describe (std::ostream &out);

	/// Verifies if the file format is compatible with this cubfile type.
	static bool compatible (const char *filename);

	/// Reads a set of cubical cells from the file.
	int readcubes (capd::homology::CubicalComplex &s) const
	{
		throw "Trying to read a set of cells from a BMD file.";
	}

	/// Read a cubical set from the file.
	int readcubes (capd::homology::SetOfCubes &s) const;

	/// Reads a bitmap from a file.
	int readcubes (int *&sizes, char *&bytes, int padding = 0,
		bool power2 = false) const;

private:
	/// The header of the file.
	bmdheader header;

	/// Add this type of a cubical set to the list.
	static cubfile_traits<bmdfile> t;

}; /* class bmdfile */

// --------------------------------------------------

inline bmdfile::bmdfile (const char *filename): cubfile (filename),
	header (filename)
{
	_dim = header. dim;
	_min. assign (_dim, 0);
	_max. assign (header. width. begin (), header. width. end ());
	return;
} /* bmdfile::bmdfile */


// --------------------------------------------------
// ----------------- BITMAP BUFFER ------------------
// --------------------------------------------------

/// A bitmap buffer stored in the memory, not in a file.
class cubitmap: public cubfile
{
public:
	/// The constructor.
	cubitmap (const char *buffer, const int *sizes, int dim);

	/// How many cubes are there in the set?
	int count () const;

	/// Is this a bitmap type of set of cubes?
	bool bitmaptype () const
	{
		return true;
	}

	/// Is this a set of elementary cubes, as opposed to full cubes?
	bool elementary () const
	{
		return false;
	}

	/// The name of this type of a cubical set.
	static const char *name ()
	{
		return "bitmap buffer (memory)";
	}

	/// Describes this particular type of a set of cubes.
	static std::ostream &describe (std::ostream &out);

	/// Verifies if the file format is compatible with this cubfile type.
	static bool compatible (const char */*filename*/)
	{
		return false;
	}

	/// Reads a set of cubical cells from the file.
	int readcubes (capd::homology::CubicalComplex &s) const
	{
		throw "Trying to read a set of cells from a bitmap buffer.";
	}

	/// Read a cubical set from the file.
	int readcubes (capd::homology::SetOfCubes &s) const;

	/// Reads a bitmap from a file.
	int readcubes (int *&sizes, char *&bytes, int padding = 0,
		bool power2 = false) const;

private:
	/// The actual bitmap buffer.
	const char *buf;

	/// The length of the buffer in bytes.
	int buflength;

}; /* class cubitmap */

// --------------------------------------------------

inline cubitmap::cubitmap (const char *buffer, const int *sizes, int dim):
	cubfile ("(memory)"), buf (buffer)
{
	_dim = dim;
	_min. assign (_dim, 0);
	_max. assign (sizes, sizes + _dim);
	if (sizes [0] & 0x1F)
		throw "The x-size of a bitmap must be a multiple of 32.";
	buflength = sizes [0] >> 3;
	for (int i = 1; i < _dim; ++ i)
		buflength *= sizes [i];
	if (buflength <= 0)
		throw "Non-positive buffer size - something went wrong.";
	return;
} /* cubitmap::cubitmap */


} // namespace homengin
} // namespace capd

#endif // _CAPD_HOMENGIN_CUBFILES_H_ 

/// @}

