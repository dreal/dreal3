/// @addtogroup HomologyEngines
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file engines.h
///
/// This file defines several engines for the homology computation
/// of cubical sets.
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

// Started in March 2006. Last revision: April 14, 2006.


#ifndef _CAPD_HOMENGIN_ENGINES_H_ 
#define _CAPD_HOMENGIN_ENGINES_H_ 

#include "capd/homology/config.h"
#include "capd/homology/textfile.h"
#include "capd/homology/timeused.h"
#include "capd/homology/arg.h"
#include "capd/homology/homology.h"
#include "capd/homology/homtools.h"

#include "capd/homologicalAlgebra/embeddingDim.h"
#include "capd/chom/dim.hpp"
#include "capd/auxil/ofstreamcout.h"
/// An output stream defined by M. Mrozek in the CAPD library.
extern ofstreamcout fcout;

#include "capd/homengin/cubfiles.h"
#include "capd/homengin/algstruct.h"

#include <cstdlib>
#include <ctime>
#include <cstring>
#include <new>
#include <exception>
#include <iostream>
#include <fstream>
#include <iomanip>
#include <vector>
#include <sstream>


namespace capd {

/// This namespace contains a multi-engine interface to the homology
/// computation procedures. Each homology algorithm is called an engine,
/// and the interface defined here allows one to use various algorithms
/// in a uniform way to compute the the homology of cubical sets.
namespace homengin {

// --------------------------------------------------
// ---------------- ABSTRACT ENGINE -----------------
// --------------------------------------------------

/// An abstract class that is inherited by all the homology engines.
class engine
{
public:
	/// The type of a list of engines.
	typedef std::vector<const engine *> enginelist;

	/// A list of all the engines that have been defined so far.
	static enginelist engines;

protected:
	/// The default constructor: Add the engine to the list.
	engine ()
	{
		engines. push_back (this);
		return;
	}

	/// The destructor: Remove the engine from the list.
	virtual ~engine ()
	{
		enginelist::iterator it = std::find (engines. begin (),
			engines. end (), this);
		if (it != engines. end ())
			engines. erase (it);
		return;
	}

public:
	/// The speed of the engine: The higher the number, the better.
	virtual int speed () const
	{
		return 0;
	}

	/// Is this dimension supported by this engine?
	virtual bool dimsupported (int dim) const
	{
		return false;
	}

	/// Rough memory usage estimate for a single set of cubes.
	/// Returns 0 if unknown, -1 if not enough memory.
	virtual int memory (const cubfile &X) const
	{
		return 0;
	}

	/// Does this engine compute relative homology?
	virtual bool relative () const
	{
		return false;
	}

	/// Is this engine capable of processing elementary cubes?
	virtual bool elementary () const
	{
		return false;
	}

	/// Does this engine support space wrapping?
	virtual bool spacewrapping () const
	{
		return false;
	}

	/// Compute the homology of the given set of cubes.
	virtual void homology (const cubfile &x,
		algstruct<capd::homology::integer> &h) const
	{
		throw "Homology computation not supported.";
	}

	/// Compute the relative homology of the given pair of sets of cubes.
	virtual void homology (const cubfile &x, const cubfile &y,
		algstruct<capd::homology::integer> &h) const
	{
		throw "Relative homology computation not supported.";
	}

	/// The name of the engine to be used in the command line.
	virtual const char *name () const
	{
		return "";
	}

	/// Describes this particular engine.
	virtual std::ostream &describe (std::ostream &out) const
	{
		out << "This is an unknown homology engine.\n";
		return out;
	}

	/// Shows a list of available homology engines with descriptions.
	static std::ostream &showlist (std::ostream &out,
		const engine::enginelist &elist = engine::engines);

	/// Finds the most appropriate homology engine.
	/// Throws an exception if none can be found.
	static const engine *find (const cubfile *X, const cubfile *Y,
		const engine::enginelist &elist = engine::engines);

	/// Finds the most appropriate homology engine for just one set.
	/// Throws an exception if none can be found.
	static const engine *find (const cubfile *X,
		const engine::enginelist &elist = engine::engines)
	{
		return find (X, 0, elist);
	}

	/// Finds a homology engine with the given name.
	/// Throws an exception if none can be found.
	static const engine *find (const char *name,
		const engine::enginelist &elist = engine::engines);

private:
}; /* class engine */


// --------------------------------------------------
// ------------------- PP ENGINE --------------------
// --------------------------------------------------

/// The homology engine that uses lists of cubes (Pawel Pilarczyk).
class PPengine: public engine
{
protected:
	/// The default constructor.
	PPengine ()
	{
		return;
	}

	/// The destructor.
	~PPengine ()
	{
		return;
	}

public:
	/// The speed of the engine: The higher the number, the better.
	int speed () const
	{
		return 100;
	}

	/// Is this dimension supported by this engine?
	bool dimsupported (int dim) const
	{
		return (dim > 0) && (dim <= capd::homology::Cube::MaxDim);
	}

	/// Rough memory usage estimate for a single set of cubes.
	/// Returns 0 if unknown, -1 if not enough memory.
	int memory (const cubfile &X) const;

	/// Does this engine compute relative homology?
	bool relative () const
	{
		return true;
	}

	/// Is this engine capable of processing elementary cubes?
	bool elementary () const
	{
		return true;
	}

	/// Does this engine support space wrapping?
	bool spacewrapping () const
	{
		return true;
	}

	/// Compute the homology of the given set of cubes.
	void homology (const cubfile &x,
		algstruct<capd::homology::integer> &h) const;

	/// Compute the relative homology of the given pair of sets of cubes.
	void homology (const cubfile &x, const cubfile &y,
		algstruct<capd::homology::integer> &h) const;

	/// The name of the engine to be used in the command line.
	const char *name () const
	{
		return "PP";
	}

	/// Describes this particular engine.
	std::ostream &describe (std::ostream &out) const;

	/// One instance of this engine.
	static PPengine eng;

}; /* class PPengine */


// --------------------------------------------------
// ------------------- BK ENGINE --------------------
// --------------------------------------------------

/// The homology engine that uses the Bill Kalies' engine.
class BKengine: public engine
{
protected:
	/// The default constructor.
	BKengine (): useLookupTable (false)
	{
		return;
	}

	/// The destructor.
	~BKengine ()
	{
		return;
	}

public:
	/// The speed of the engine: The higher the number, the better.
	int speed () const
	{
		return 250;
	}

	/// Is this dimension supported by this engine?
	bool dimsupported (int dim) const
	{
		return (dim == DIM);
	}

	/// Rough memory usage estimate for a single set of cubes.
	/// Returns 0 if unknown, -1 if not enough memory.
	int memory (const cubfile &X) const;

	/// Does this engine compute relative homology?
	bool relative () const
	{
		return false;
	}

	/// Is this engine capable of processing elementary cubes?
	bool elementary () const
	{
		return false;
	}

	/// Does this engine support space wrapping?
	bool spacewrapping () const
	{
		return false;
	}

	/// Compute the homology of the given set of cubes.
	void homology (const cubfile &x,
		algstruct<capd::homology::integer> &h) const;

	/// Compute the relative homology of the given pair of sets of cubes.
	void homology (const cubfile &x, const cubfile &y,
		algstruct<capd::homology::integer> &h) const
	{
		throw "The BK engine cannot compute relative homology.";
	}

	/// The name of the engine to be used in the command line.
	const char *name () const
	{
		return "BK";
	}

	/// Describes this particular engine.
	std::ostream &describe (std::ostream &out) const;

	/// One instance of this engine.
	static BKengine eng;

protected:
	/// Should the lookup table be used prior to the homology computation?
	bool useLookupTable;

}; /* class BKengine */


// --------------------------------------------------
// ------------------ BK_LT ENGINE ------------------
// --------------------------------------------------

/// The homology engine that uses the Bill Kalies' engine:
/// the version which uses the lookup table for reduction.
class BK_LTengine: public BKengine
{
protected:
	/// The default constructor.
	BK_LTengine ()
	{
		useLookupTable = true;
		return;
	}

	/// The destructor.
	~BK_LTengine ()
	{
		return;
	}

public:
	/// The speed of the engine: The higher the number, the better.
	int speed () const
	{
		return 260;
	}

	/// The name of the engine to be used in the command line.
	const char *name () const
	{
		return "BK_LT";
	}

	/// Describes this particular engine.
	std::ostream &describe (std::ostream &out) const;

	/// One instance of this engine.
	static BK_LTengine eng;

}; /* class BK_LTengine */


// --------------------------------------------------
// -------------- A GENERAL MM ENGINE ---------------
// --------------------------------------------------

/// A general class for the MM* bitmap-based engines.
class MMengine: public engine
{
protected:
	/// The default constructor.
	MMengine ()
	{
		return;
	}

	/// The destructor.
	~MMengine ()
	{
		return;
	}

public:
	/// The speed of the engine: The higher the number, the better.
	virtual int speed () const = 0;

	/// Is this dimension supported by this engine?
	bool dimsupported (int dim) const
	{
		return (dim == embeddingDim);
	}

	/// Rough memory usage estimate for a single set of cubes.
	/// Returns 0 if unknown, -1 if not enough memory.
	int memory (const cubfile &X) const;

	/// Does this engine compute relative homology?
	bool relative () const
	{
		return false;
	}

	/// Is this engine capable of processing elementary cubes?
	bool elementary () const
	{
		return false;
	}

	/// Does this engine support space wrapping?
	bool spacewrapping () const
	{
		return false;
	}

	/// Compute the homology of the given set of cubes.
	virtual void homology (const cubfile &x,
		algstruct<capd::homology::integer> &h) const = 0;

	/// Compute the relative homology of the given pair of sets of cubes.
	void homology (const cubfile &x, const cubfile &y,
		algstruct<capd::homology::integer> &h) const
	{
		throw "The MM* engines do not support relative homology.";
	}

	/// The name of the engine to be used in the command line.
	virtual const char *name () const = 0;

	/// Describes this particular engine.
	virtual std::ostream &describe (std::ostream &out) const = 0;

protected:
}; /* class MMengine */


// --------------------------------------------------
// ------------------ MM_CR ENGINE ------------------
// --------------------------------------------------

/// The MM_CR engine.
class MM_CRengine: public MMengine
{
protected:
	/// The default constructor.
	MM_CRengine ()
	{
		return;
	}

	/// The destructor.
	~MM_CRengine ()
	{
		return;
	}

public:
	/// The speed of the engine: The higher the number, the better.
	int speed () const
	{
		return 5000;
	}

	/// Is this dimension supported by this engine?
	bool dimsupported (int dim) const
	{
		return ((dim == embeddingDim) || ((dim >= 2) && (dim <= 4)));
	}

	/// Compute the homology of the given set of cubes.
	void homology (const cubfile &x,
		algstruct<capd::homology::integer> &h) const;

	/// The name of the engine to be used in the command line.
	const char *name () const
	{
		return "MM_CR";
	}

	/// Describes this particular engine.
	std::ostream &describe (std::ostream &out) const;

	/// One instance of this engine.
	static MM_CRengine eng;

}; /* class MM_CRengine */


// --------------------------------------------------
// ------------------ MM_AR ENGINE ------------------
// --------------------------------------------------

/// The MM_AR engine.
class MM_ARengine: public MMengine
{
protected:
	/// The default constructor.
	MM_ARengine ()
	{
		return;
	}

	/// The destructor.
	~MM_ARengine ()
	{
		return;
	}

public:
	/// The speed of the engine: The higher the number, the better.
	int speed () const
	{
		return 70;
	}

	/// Is this dimension supported by this engine?
	bool dimsupported (int dim) const
	{
		return ((dim == embeddingDim) || ((dim >= 2) && (dim <= 4)));
	}

	/// Compute the homology of the given set of cubes.
	void homology (const cubfile &x,
		algstruct<capd::homology::integer> &h) const;

	/// The name of the engine to be used in the command line.
	const char *name () const
	{
		return "MM_AR";
	}

	/// Describes this particular engine.
	std::ostream &describe (std::ostream &out) const;

	/// One instance of this engine.
	static MM_ARengine eng;

}; /* class MM_ARengine */


// --------------------------------------------------
// ----------------- MM_ASLT ENGINE -----------------
// --------------------------------------------------

/// The MM_ASLT engine.
class MM_ASLTengine: public MMengine
{
protected:
	/// The default constructor.
	MM_ASLTengine ()
	{
		return;
	}

	/// The destructor.
	~MM_ASLTengine ()
	{
		return;
	}

public:
	/// The speed of the engine: The higher the number, the better.
	int speed () const
	{
		return 1000;
	}

	/// Compute the homology of the given set of cubes.
	void homology (const cubfile &x,
		algstruct<capd::homology::integer> &h) const;

	/// The name of the engine to be used in the command line.
	const char *name () const
	{
		return "MM_ASLT";
	}

	/// Describes this particular engine.
	std::ostream &describe (std::ostream &out) const;

	/// One instance of this engine.
	static MM_ASLTengine eng;

}; /* class MM_ASLTengine */


} // namespace homengin
} // namespace capd

#endif // _CAPD_HOMENGIN_ENGINES_H_ 

/// @}

