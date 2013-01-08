/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file homchain.cpp
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started in July 1997. Last revision: November 14, 2006.


#include "capd/homology/config.h"
#include "capd/homology/textfile.h"
#include "capd/homology/integer.h"
#include "capd/homology/chains.h"
#include "capd/homology/words.h"
#include "capd/homology/timeused.h"
#include "capd/homology/arg.h"

#include <exception>
#include <cstdlib>
#include <ctime>
#include <ctype.h>
#include <new>
#include <iostream>
#include <fstream>
#include <iomanip>
#include <string>
#include <sstream>

using namespace capd::homology;


// --------------------------------------------------
// -------------------- OVERTURE --------------------
// --------------------------------------------------

const char *title = "\
HOMCHAIN, ver. 2.08, 10/07/04. Copyright (C) 1997-2010 by Pawel Pilarczyk.\n\
This is free software. No warranty. Consult 'license.txt' for details.";

const char *helpinfo = "\
Call with: X.chn [Y.chn] map1.chm map2.chm map3.chm...\n\
This program computes the homology module of a finitely generated free\n\
chain complex and the homology of maps between two such complexes.\n\
It is based on computation of Smith normal form of bouhdary homomorphisms.\n\
It is a generalization of an algorithm by Kaczynski, Mrozek & Slusarek.\n\
The program reads chain complexes and chain maps from input files,\n\
performs computations and outputs the results to the screen ('cout').\n\
Invoked with only one chain complex, the program computes the homology\n\
of this chain complex and all the maps treated as endomorphisms.\n\
Optional arguments:\n\
-p n - fix the ring of coefficients as Z_n (by default the ring is Z),\n\
-g filename - write the generators of homology to the given file(s),\n\
-d - digital names of generators only (1-N; an old version; faster),\n\
-h - show this brief help information and exit.\n\
For more details ask the author at http://www.PawelPilarczyk.com/.";

//-s prefix - save partial results after the time limit exceeded,

// set the maximal number of maps that can be computed simultaneously
#define MAXMAPS 20

// set the maximan number of chain complexes; only 2 is currently supported
#define MAXCOMPL 2


// --------------------------------------------------
// ------------------ DIGITAL READ ------------------
// --------------------------------------------------
// This is an old code kept here only for its speed.
// Please forward to the section "symbolic read."

chaincomplex<integer> *read_chain_complex_digital (std::istream &in,
	int trace_generators)
{
	textfile f (in);

	// read the phrase starting the definition of the chain complex
	if (f. readphrase ("ChainComplex") < 0)
		return NULL;

	// read and set the dimension of the chain complex
	if (f. readphrase ("MaxDimension") < 0)
		return NULL;
	int maxdimension = (int) f. readnumber (0, 1);
	if (maxdimension < 0)
		return NULL;

	// prepare an empty chain complex
	chaincomplex<integer> *c = new chaincomplex<integer>
		(maxdimension, trace_generators);

	// current dimension
	int dim = 0;

	// read what is in the file
	while (f. checkchar () != EOF)
	{
		if ((f. checkchar () == 'd') || (f. checkchar () == 'D'))
		{
			// read the number of currently interpreted dimension
			if (f. readphrase ("Dimension") < 0)
			{
				delete c;
				return NULL;
			}
			dim = (int) f. readnumber (0, 1);
			if ((dim < 0) || (dim > maxdimension))
				return c;

			// ignore a character if needed
			if ((f. checkchar () == ':') || (f. checkchar () == '='))
				f. readchar ();

			// read the number of cells in this dimension
			int ncells = (int) f. readnumber (0, 1);
			if (ncells < 0)
			{
				sout << "ERROR (line " << f. linenumber () << "): ";
				sout << "Incorrect number of cells (" << ncells << ") ";
				sout << "in dimension " << dim << ".\n";
				delete c;
				return NULL;
			}

			// define the number of generators in this dimension
			c -> def_gen (dim, ncells);
		}
		else if ((f. checkchar () == 'b') || (f. checkchar () == 'B') ||
			(f. checkchar () == '#'))
		{
			// ignore the word "b", "bound" or "boundary"
			while ((f. checkchar () != EOF) &&
				((f. checkchar () < '0') || (f. checkchar () > '9')))
				f. readchar ();

			// read the number of the cell
			int cell = (int) f. readnumber (0, 1);

			// ignore the next character
			if ((f. checkchar () == ':') || (f. checkchar () == '='))
				f. readchar ();

			// read the boundary of this cell
			int wait_number = 0;
			int go_on = 1;
			do
			{
				switch (f. checkchar ())
				{
					case '-':
					case '+':
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
						if (wait_number)
						{
							integer e;
							e = (wait_number > 0) ? 1 : -1;
							c -> add (dim, (wait_number > 0) ?
								(wait_number - 1) : (-wait_number - 1),
								cell - 1, e);
						}
						wait_number = (int) f. readnumber ();
						break;
					case '*':
					{
						if (!wait_number)
						{
							sout << "ERROR (line " << f. linenumber () <<
								"):\n   Misplaced '*'.\n";
							delete c;
							return NULL;
						}
						f. readchar ();
						int number = (int) f. readnumber ();
						integer e;
						e = wait_number;
						c -> add (dim, number - 1, cell - 1, e);
						wait_number = 0;
						break;
					}
					default:
						if (wait_number)
						{
							integer e;
							e = (wait_number > 0) ? 1 : -1;
							c -> add (dim, (wait_number > 0) ?
								(wait_number - 1) : (-wait_number - 1),
								cell - 1, e);
						}
						go_on = 0;
						break;
				}
			} while (go_on);
		}
		else if ((f. checkchar () == 'e') || (f. checkchar () == 'E'))
			break;
		else
		{
			sout << "Warning: unknown char: '" <<
				(char) f. checkchar () << "'\n";
			f. ignoreline ();
		}
	}

	return c;
} /* read_chain_complex_digital */

chainmap<integer> *read_chain_map_digital (std::ifstream &in,
	chaincomplex<integer> &domain, chaincomplex<integer> &range)
{
	textfile f (in);

	// read the phrase starting the definition of the chain map
	if (f. readphrase ("ChainMap") < 0)
		return NULL;

	// prepare an empty chain map
	chainmap<integer> *m = new chainmap<integer> (domain, range);

	// current dimension
	int dim = 0;

	// read what is in the file
	while (f. checkchar () != EOF)
	{
		if ((f. checkchar () == 'd') || (f. checkchar () == 'D'))
		{
			// read the number of currently interpreted dimension
			if (f. readphrase ("Dimension") < 0)
			{
				delete m;
				return NULL;
			}
			dim = (int) f. readnumber (0, 1);
			if (dim < 0)
				return m;
		}
		else if ((f. checkchar () == 'f') || (f. checkchar () == 'F') ||
			(f. checkchar () == 'i') || (f. checkchar () == 'I') ||
			(f. checkchar () == '#'))
		{
			// ignore the word "f"
			while ((f. checkchar () != EOF) &&
				((f. checkchar () < '0') || (f. checkchar () > '9')))
				f. readchar ();

			// read the number of the cell
			int cell = (int) f. readnumber (0, 1);

			// ignore the next character
			if ((f. checkchar () == ':') || (f. checkchar () == '='))
				f. readchar ();

			// read the image of this cell
			int wait_number = 0;
			int go_on = 1;
			do
			{
				switch (f. checkchar ())
				{
					case '-':
					case '+':
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
						if (wait_number)
						{
							integer e;
							e = (wait_number > 0) ? 1 : -1;
							m -> add (dim, (wait_number > 0) ?
								(wait_number - 1) : (-wait_number - 1),
								cell - 1, e);
						}
						wait_number = (int) f. readnumber ();
						break;
					case '*':
					{
						if (!wait_number)
						{
							sout << "ERROR (line " << f. linenumber () <<
								"):\n   Misplaced '*'.\n";
							delete m;
							return NULL;
						}
						f. readchar ();
						int number = (int) f. readnumber ();
						integer e;
						e = wait_number;
						m -> add (dim, number - 1, cell - 1, e);
						wait_number = 0;
						break;
					}
					default:
						if (wait_number)
						{
							integer e;
							e = (wait_number > 0) ? 1 : -1;
							m -> add (dim, (wait_number > 0) ?
								(wait_number - 1) : (-wait_number - 1),
								cell - 1, e);
						}
						go_on = 0;
						break;
				}
			} while (go_on);
		}
		else if ((f. checkchar () == 'e') || (f. checkchar () == 'E'))
			break;
		else
		{
			sout << "Warning: unknown char: '" <<
				(char) f. checkchar () << "'\n";
			f. ignoreline ();
		}
	}

	return m;
} /* read_chain_map_digital */


// --------------------------------------------------
// ----------------- SYMBOLIC READ ------------------
// --------------------------------------------------
// Read a chain complex or a chain map.
// Allow generators to be named with words.

chaincomplex<integer> *read_chain_complex_symbolic (std::istream &in,
	int trace_generators, words *&names)
{
	// read the phrase starting the definition of the chain complex
	word w;
	ignorecomments (in);
	in >> w;
	ignorecomments (in);
	if (w == "chain")
	{
		in >> w;
		ignorecomments (in);
	}
	if ((w != "complex") && (w != "chaincomplex"))
		throw "The file should begin with the phrase "
			"'chain complex'.";

	// read the phrase "max dimension" (or something similar)
	in >> w;
	ignorecomments (in);
	if ((w == "max") || (w == "maximal"))
	{
		word v;
		in >> v;
		ignorecomments (in);
		w += v;
	}
	if ((w != "maxdimension") && (w != "maximaldimension") &&
		(w != "maxdim") && (w != "maximaldim"))
		throw "Missing maximal dimension definition.";

	// ignore a character if needed
	while ((in. peek () == ':') || (in. peek () == '='))
	{
		in. get ();
		ignorecomments (in);
	}

	// read the number for the maximal dimension
	int maxdimension = -1;
	in >> maxdimension;
	ignorecomments (in);
	if (maxdimension < 0)
		throw "Unable to read the maximal dimension.";

	// prepare an empty chain complex
	chaincomplex<integer> *c = new chaincomplex<integer>
		(maxdimension, trace_generators);
	if (names)
		throw "Cell names should not be defined earlier.";
	names = new words [maxdimension + 1];
	int *ncells = new int [maxdimension + 1];
	for (int i = 0; i <= maxdimension; i ++)
		ncells [i] = 0;

	// prepare a variable to keep the current dimension
	int dim = -1;

	// read the first word in the file to be analyzed
	in >> w;
	ignorecomments (in);
	if (w != "dimension")
		throw "The first dimension declaration is missing.";

	// read the chain complex
	while (w != "")
	{
		if (w == "dimension")
		{
			// read the number of currently interpreted dimension
			in >> dim;
			ignorecomments (in);
			if (!in)
				throw "Unable to read the dimension.";
			if ((dim < 0) || (dim > maxdimension))
				throw "Dimension out of range.";

			// ignore a character if needed
			if ((in. peek () == ':') || (in. peek () == '='))
			{
				in. get ();
				ignorecomments (in);
			}

			// read the number of cells in this dimension if any
			if (isdigit (in. peek ()))
			{
				in >> ncells [dim];
				ignorecomments (in);
				if (ncells [dim] < 0)
					throw "Negative number of cells.";

				// define the number of cells at this level
				c -> def_gen (dim, ncells [dim]);
			}

			// read the next word in the file to be analyzed
			w = "";
			in >> w;
			ignorecomments (in);

			continue;
		}
		else if ((w != "#") && (w != "boundary"))
		{
			ERRORMSG << "Unknown word: '" << w << "'." << THROW
		}

		// get the name and the number of this cell whose boundary
		// will be defined in a while
		word name;
		in >> name;
		ignorecomments (in);
		static bool warned = false;
		if (!warned && names [dim]. check (name))
		{
			sout << "Warning: Names of some cells seem to be "
				"repeated, e.g. '" << name << "'.\n";
			warned = true;
		}
		int cell = names [dim]. add (name);

		// ignore the next character
		if ((in. peek () == ':') || (in. peek () == '='))
		{
			in. get ();
			ignorecomments (in);
		}

		// remember the sign outside the loop as it can be read
		// for the next cell already at the end of the previous loop
		int sign = 1;

		// check for the sign for the next cell
		while ((in. peek () == '+') || (in. peek () == '-'))
		{
			if (in. peek () == '-')
				sign = -sign;
			in. get ();
			ignorecomments (in);
		}

		// read the first cell's name (or the next keyword)
		w = "";
		in >> w;
		ignorecomments (in);

		// if this is just zero, then ignore it
		if (w == "0")
		{
			w = "";
			in >> w;
			ignorecomments (in);
		}

		// read the boundary of this cell
		while ((w != "dimension") && (w != "#") &&
			(w != "boundary") && (w != ""))
		{
			// if the dimension is 0, then this is wrong
			if (dim == 0)
				throw "A non-zero boundary of a "
					"zero-dimensional cell.";

			// if this word contains only a sign, read the rest
			while ((w == "-") || (w == "+"))
			{
				if (w == "-")
					sign = -sign;
				in >> w;
				ignorecomments (in);
			}

			// if this word contains a coefficient, retrieve it
			int coefficient = 1;
			if (in. peek () == '*')
			{
				coefficient = (int) w;
				in. get ();
				ignorecomments (in);
				in >> w;
				ignorecomments (in);
			}

			// get the number of the boundary cell
			int bcell = names [dim - 1]. add (w);

			// add this coefficient to the boundary matrix
			integer e;
			e = sign * coefficient;
			c -> add (dim, bcell, cell, e);

			// check for the sign for the next cell
			sign = 1;
			while ((in. peek () == '+') || (in. peek () == '-'))
			{
				if (in. peek () == '-')
					sign = -sign;
				in. get ();
				ignorecomments (in);
			}

			// read the next word in the file to be analyzed
			w = "";
			in >> w;
			ignorecomments (in);
		}
	}

	// make sure that no cells were lost
	for (int i = 0; i <= maxdimension; i ++)
		if (ncells [i] < names [i]. size ())
			c -> def_gen (i, names [i]. size ());
	delete [] ncells;

	// debug:
/*	sout << "Generators:\n";
	for (int i = 0; i <= maxdimension; i ++)
		write (sout, names [i], SMALL_SIZE) << '\n';
	sout << *c << '\n';
*/
	return c;
} /* read_chain_complex_symbolic */

chainmap<integer> *read_chain_map_symbolic (std::ifstream &in,
	chaincomplex<integer> &domain, chaincomplex<integer> &range,
	words *&cxnames, words *&cynames)
{
	// read the phrase starting the definition of the chain complex
	word w;
	ignorecomments (in);
	in >> w;
	ignorecomments (in);
	if (w == "chain")
	{
		in >> w;
		ignorecomments (in);
	}
	if ((w != "map") && (w != "chainmap"))
		throw "The file should begin with the phrase 'chain map'.";

	// read the first word in the file to be analyzed
	in >> w;
	ignorecomments (in);
	if (w != "dimension")
		throw "The first dimension declaration is missing.";

	// prepare an empty chain map
	chainmap<integer> *m = new chainmap<integer> (domain, range);

	// prepare a variable to keep the current dimension
	int dim = -1;

	// detect the maximal allowable dimension
	int maxdimension = domain. dim ();

	// read the chain complex
	while (w != "")
	{
		if (w == "dimension")
		{
			// read the number of currently interpreted dimension
			in >> dim;
			ignorecomments (in);
			if (!in)
				throw "Unable to read the dimension.";
			if ((dim < 0) || (dim > maxdimension))
				throw "Dimension out of range.";

			// read the next word in the file to be analyzed
			w = "";
			in >> w;
			ignorecomments (in);

			continue;
		}
		else if ((w != "#") && (w != "image"))
		{
			ERRORMSG << "Unknown word: '" << w << "'." << THROW
		}

		// get the name and the number of this cell whose image
		// will be defined in a while
		word name;
		in >> name;
		ignorecomments (in);
		static bool cxwarned = false;
		if (!cxwarned && !cxnames [dim]. check (name))
		{
			sout << "Warning: Some argument cells are not "
				"in the domain, e.g. '" << name << "'.\n";
			cxwarned = true;
		}
		int cell = cxnames [dim]. add (name);

		// ignore the next character
		if ((in. peek () == ':') || (in. peek () == '='))
		{
			in. get ();
			ignorecomments (in);
		}

		// remember the sign outside the loop as it can be read
		// for the next cell already at the end of the previous loop
		int sign = 1;

		// check for the sign for the next cell
		while ((in. peek () == '+') || (in. peek () == '-'))
		{
			if (in. peek () == '-')
				sign = -sign;
			in. get ();
			ignorecomments (in);
		}

		// read the first cell's name (or the next keyword)
		w = "";
		in >> w;
		ignorecomments (in);

		// if this is just zero, then ignore it
		if (w == "0")
		{
			w = "";
			in >> w;
			ignorecomments (in);
		}

		// read the image of this cell
		while ((w != "dimension") && (w != "#") && (w != "image") &&
			(w != ""))
		{
			// if this word contains only a sign, read the rest
			while ((w == "-") || (w == "+"))
			{
				if (w == "-")
					sign = -sign;
				in >> w;
				ignorecomments (in);
			}

			// if this word contains a coefficient, retrieve it
			int coefficient = 1;
			if (in. peek () == '*')
			{
				coefficient = (int) w;
				in. get ();
				ignorecomments (in);
				in >> w;
				ignorecomments (in);
			}

			// warn if this cell did not appear in the codomain
			static bool cywarned = false;
			if (!cywarned && !cynames [dim]. check (w))
			{
				sout << "Warning: Some image cells are not "
					"in the codomain, e.g. '" << w <<
					"'.\n";
				cywarned = true;
			}

			// get the number of the image cell
			int imgcell = cynames [dim]. add (w);

			// add this coefficient to the map matrix
			integer e;
			e = sign * coefficient;
			m -> add (dim, imgcell, cell, e);

			// check for the sign for the next cell
			sign = 1;
			while ((in. peek () == '+') || (in. peek () == '-'))
			{
				if (in. peek () == '-')
					sign = -sign;
				in. get ();
				ignorecomments (in);
			}

			// read the next word in the file to be analyzed
			w = "";
			in >> w;
			ignorecomments (in);
		}
	}

	return m;
} /* read_chain_map_symbolic */


// --------------------------------------------------
// ---------------------- READ ----------------------
// --------------------------------------------------

chaincomplex<integer> *read_chain_complex (const char *filename,
	int trace_generators, words *&names, bool symbolic)
{
	std::ifstream in (filename);
	if (!in)
		fileerror (filename);
	if (symbolic)
		return read_chain_complex_symbolic (in, trace_generators,
			names);
	else
		return read_chain_complex_digital (in, trace_generators);
} /* read_chain_complex */

chainmap<integer> *read_chain_map (const char *filename,
	chaincomplex<integer> &domain, chaincomplex<integer> &range,
	words *&cxnames, words *&cynames, bool symbolic)
{
	std::ifstream in (filename);
	if (!in)
		fileerror (filename);
	if (symbolic)
		return read_chain_map_symbolic (in, domain, range,
			cxnames, cynames);
	else
		return read_chain_map_digital (in, domain, range);
} /* read_chain_map */


// --------------------------------------------------
// ---------------- SHOW GENERATORS -----------------
// --------------------------------------------------

std::ostream &show_generators (std::ostream &out, const chaincomplex<integer> &c,
	const chain<integer> &list, int q, const words *names)
// Show symbolic homology generators.
// Do not verify the correctness of the data.
{
	for (int i = 0; i < list. size (); i ++)
	{
		const chain<integer> &ch = c. gethomgen (q, list. num (i));
		if (ch. size () <= 0)
			out << "0";
		for (int i = 0; i < ch. size (); i ++)
		{
			integer coef = ch. coef (i);
			if (coef == 1)
				out << (i ? " + " : "");
			else if (coef == -1)
				out << (i ? " - " : "-");
			else
				out << (i ? " + " : "") << coef << " * ";
			if (names)
			{
				int n = ch. num (i);
				if ((n >= 0) && (n < names [q]. size ()))
					out << names [q] [n];
				else
					out << '<' << (n + 1) << '>';
			}
			else
				out << (ch. num (i) + 1);
				
		}
		out << '\n';
	}
	return out;
} /* show_generators */


// --------------------------------------------------
// -------------------- HOMCHAIN --------------------
// --------------------------------------------------

struct filetype
{
	enum name {unknown, wrong, chaincomplex, chainmap};

}; /* struct filetype */

static filetype::name detectfiletype (const char *name)
{
	// open the input file
	std::ifstream in (name);
	if (!in)
		fileerror (name);
	ignorecomments (in);

	// check the first word(s) in the file
	word w;
	in >> w;
	if (w == "chain")
	{
		ignorecomments (in);
		in >> w;
	}
	if ((w == "chaincomplex") || (w == "complex"))
		return filetype::chaincomplex;
	else if ((w == "chainmap") || (w == "map"))
		return filetype::chainmap;
	else
		return filetype::unknown;
} /* detectfiletype */

int saveresults (const char *prefix, chaincomplex<integer> *cx [],
	int complcount, chainmap<integer> *maps [], int mapcount)
{
	if (!prefix)
		return 0;

	for (int i = 0; i < complcount; i ++)
	{
		std::string s;
		if (prefix)
			s += std::string (prefix);
		s += (char) ('x' + i);
		s += ".chn";
		const char *name = s. c_str ();
		std::ofstream f (name);
		if (f)
		{
			sout << "Saving C" << (char) ('X' + i) <<
				" to '" << name << "'... ";
			f << *(cx [i]);
			f << "; The End.\n";
			sout << "Done.\n";
		}
		if (!f)
			sout << "WARNING: Can't save C" <<
				(char) ('X' + i) << " to '" << name << "'\n";
	}
	for (int i = 0; i < mapcount; i ++)
	{
		std::ostringstream s;
		if (prefix)
			s << prefix;
		s << 'f' << (i + 1) << ".chm";
		const char *name = s. str (). c_str ();
		std::ofstream f (name);
		if (f)
		{
			sout << "Saving F" << (i + 1) <<
				" to '" << name << "'... ";
			f << *(maps [i]);
			f << "; The End.\n";
			sout << "Done.\n";
		}
		if (!f)
			sout << "WARNING: Can't save the map no. " <<
				(i + 1) << " to '" << name << "'\n";
	}
	return 0;
} /* savepartialresults */

int homchain (char *filenames [], int filecount,
	char *generators [], int gencount, bool symbolic,
	const char *prefix)
{
	// prepare pointers to the algebraic data structures
	chaincomplex<integer> *ccompl [MAXCOMPL];
	char *complnames [2];
	int complcount = 0;
	chainmap<integer> *maps [MAXMAPS];
	char *mapnames [MAXMAPS];
	int mapcount = 0;

	// determine file types
	for (int i = 0; i < filecount; i ++)
	{
		// if there is no legitimate file name, just skip it
		if (!filenames [i] || !*filenames [i])
			continue;

		// check the type of the file
		filetype::name type = detectfiletype (filenames [i]);
		if (type == filetype::chaincomplex)
		{
			if (complcount >= MAXCOMPL)
				throw "Too many chain complexes.";
			complnames [complcount ++] = filenames [i];
		}
		else if (type == filetype::chainmap)
		{
			if (mapcount >= MAXMAPS)
				throw "Too many chain maps.";
			mapnames [mapcount ++] = filenames [i];
		}
		else
			fileerror (filenames [i],
				"determine the contents of");
	}

	// make sure that at least one chain complex is given
	if (!complcount)
		throw "None of the given files contains a chain complex.";

	// make sure that if two complexes are given, then a map is present
	if ((complcount > 1) && !mapcount)
		throw "Both files contain chain complexes "
			"and no map is given.";

	// read the chain complexes from the input text files
	words *names [MAXCOMPL];
	for (int i = 0; i < complcount; i ++)
	{
		sout << "Reading a chain complex from '" <<
			complnames [i] << "'...\n";
		names [i] = NULL;
		ccompl [i] = read_chain_complex (complnames [i],
			!!generators [i], names [i], symbolic);
		if (!ccompl [i])
			return -1;
	}

	for (int i = 0; i < mapcount; i ++)
	{
		sout << "Reading a chain map from '" << mapnames [i] <<
			"'...\n";
		maps [i] = read_chain_map (mapnames [i], *(ccompl [0]),
			((complcount > 1) ? *(ccompl [1]) : *(ccompl [0])),
			names [0], names [(complcount > 1) ? 1 : 0],
			symbolic);
		if (!maps [i])
			return -1;
	}

	// show the amount of time used for reading the data from files
	program_time. show ("Time used so far:");

	// compute the homology groups of the read chain complex
	sout << "The ring of coefficients is " << integer::ringname () <<
		".\n";

	// compute and show homology of all the chain complexes (and maps)
	chain<integer> *hom [MAXCOMPL];
	for (int i = 0; i < complcount; i ++)
	{
		// say which homology is being computed at the moment
		sout << "Computing the homology of the chain complex";
		if (complcount > 1)
			sout << " no. " << (i + 1);
		sout << "...\n";

		// compute the homology of the given chain complex;
		// if the time limit is exceeded, save partial results
		hom [i] = NULL;
		ccompl [i] -> compute_and_show_homology (sout, hom [i]);
	}

	for (int i = 0; i < mapcount; i ++)
	{
		sout << "The map ";
		if (mapcount > 1)
			sout << "no. " << (i + 1) << ' ';
		sout << "in homology is as follows:\n";
		maps [i] -> show_homology (sout, hom [0],
			(complcount > 1) ? hom [1] : hom [0], NULL,
			symbolic ? "x" : NULL,
			symbolic ? ((complcount > 1) ? "y" : "x") : NULL);
	}

	// save generators of the homology groups if requested
	for (int i = 0; i < gencount; i ++)
	{
		if (!generators [i] || !*(generators [i]))
			continue;
		sout << "Writing the homology generators of C" <<
			(char) ('X' + i) << " to '" <<
			generators [i] << "'...\n";
		std::ofstream out (generators [i]);
		if (!out)
			sout << "WARNING: Can't create the file.\n";
		else
		{
			out << "; This file contains the generators "
				"of the homology module\n"
				"; of the chain complex read from "
				" the file '" << complnames [i] << "'.\n";
			for (int q = 0; q <= ccompl [i] -> dim (); q ++)
			{
				out << "\n[H_" << q << "]\n";
				show_generators (out, *(ccompl [i]),
					hom [i] [q], q, names [i]);
			}
		}
	}

	// show the total time used until this moment
	program_time. show ("Total time used:");
	program_time = 0;
	scon << "[Press Ctrl-C to exit.]\r";

	// free memory used for the chain complexes and the chain map
	for (int i = 0; i < mapcount; i ++)
		delete maps [i];
	for (int i = 0; i < complcount; i ++)
	{
		delete ccompl [i];
		if (names [i])
			delete [] names [i];
	}
	return 0;
} /* homchain */


// --------------------------------------------------
// ---------------------- MAIN ----------------------
// --------------------------------------------------

int main (int argc, char *argv [])
// Return: 0 = Ok, -1 = Error, 1 = Help etc. displayed, 2 = Wrong arguments.
{
	// turn on message that will appear if the program is aborted
	program_time = "Aborted after";

	char *filenames [MAXMAPS + MAXCOMPL];
	int filecount = 0;
	char *generators [MAXCOMPL];
	int gencount = 0;
	int p = 0;
	int ignoredargument;
	bool symbolic = true;
	char *prefix = NULL;

	arguments a;
	arg (a, NULL, filenames, filecount, MAXMAPS + MAXCOMPL);
	arg (a, "a", ignoredargument, 0);
	arg (a, "g", generators, gencount, MAXCOMPL);
	arg (a, "s", prefix);
	arg (a, "p", p);
	argswitch (a, "d", symbolic, false);
	arghelp (a);

	argstreamprepare (a);
	int argresult = a. analyze (argc, argv);
	argstreamset ();

	// show the program's main title
	if (argresult >= 0)
		sout << title << '\n';

	// show some debug info
	if (argresult >= 0)
		sout << "[Tech info: chain " << sizeof (chain<integer>) <<
			", addr " << sizeof (int *) <<
			", intgr " << sizeof (integer) << ".]\n";

	// if something was incorrect, show an additional message and exit
	if (argresult < 0)
	{
		sout << "Call with '--help' for help.\n";
		return 2;
	}

	// if help requested or no filenames present, show help information
	if (!filecount || (argresult > 0))
	{
		sout << helpinfo << '\n';
		return 1;
	}

	// initialize the field of integers modulo p if desired
	if (p > 0)
		integer::initialize (p);

	// try running the main function and catch an error message if thrown
	try
	{
		homchain (filenames, filecount, generators, gencount,
			symbolic, prefix);
		scon << "Thank you for using this software. "
			"We appreciate your business.\n";
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


// --------------------------------------------------
// -------------------- HISTORY ---------------------
// --------------------------------------------------

// 0.01 (July 1997)
//      - the first version of the program
// 1.00 (May 27, 1999)
//      - final version (part of my master dissertation)
// 2.00 (December 26, 1999)
//      - a new version of "chains" (coefficients in a Euclidean ring)
// 2.03 (October 11, 2000)
//      - a bug in simple_form fixed (the program is now much faster)
// 2.04 (November 22, 2000)
//      - tracing of the generators of the homology module added
// 2.05 (March 7, 2002)
//      - templates in "chains.h", arguments from "arg.h"
// 2.06 (Sep/Nov, 2002)
//      - symbolic input (generators with names)
// 2.07 (March 4, 2003)
//      - support for multiple maps added

/// @}

