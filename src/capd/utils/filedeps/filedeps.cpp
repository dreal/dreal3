/// @addtogroup utils
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file filedeps.cpp
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2008 by Pawel Pilarczyk.
//
// This file is part of the Homology Library.  This library is free software;
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

// Started on February 22, 2003. Last revision: November 11, 2008.


#include "config.h"
#include "textfile.h"
#include "hashsets.h"
#include "words.h"
#include "timeused.h"
#include "arg.h"

#include <iostream>
#include <fstream>
#include <ctime>
#include <sstream>
#include <string>
#include <string.h>

using namespace chomp::homology;


// --------------------------------------------------
// -------------------- OVERTURE --------------------
// --------------------------------------------------

const char *title = "\
FILEDEPS, ver. 0.08. Copyright (C) 2003-2008 by Pawel Pilarczyk.\n\
This is free software. No warranty. Consult 'license.txt' for details.";

const char *helpinfo = "\
This program creates my 'makedeps.*' files.\n\
Call with the name of 'makedeps' and a list of names of the programs\n\
to be included in that file.\n\
Switches and additional arguments:\n\
-I dir - include this directory to search for files (can be repeated),\n\
-x file - exclude the specific file from the lists,\n\
-l file - add the path to this file as a library source component,\n\
-w file - this program must be linked with the wxWindows library,\n\
-c file - this program must be linked with the CAPD library,\n\
-g file - this program must be linked with the graphics version of CAPD,\n\
-s prefix - strip this directory prefix from each source file name,\n\
-d - keep directories for the object files,\n\
-f - flat sources (.cpp files in one dir, even if .h in subdirs),\n\
-v - verbose output (a lot of debugging details),\n\
-o - use '${OBJEXT}' instead of '.o' as an extension of the OBJ files,\n\
-h - display this brief help information only and exit.\n\
For more information consult the accompanying documentation (if available)\n\
or ask the program's author at http://www.PawelPilarczyk.com/.";

// set a limit for the maximum allowable number of file names to process
#define MAXN 1024

// set a limit for the maximum length of the name of an included file
#define MAXBUF 1024


// --------------------------------------------------
// --------------------- TOOLS ----------------------
// --------------------------------------------------

outputstream &indent (outputstream &s, int depth)
{
	while (depth --)
		s << "   ";
	return s;
} /* indent */

words &sortwords (words &w)
{
	words srt;
	while (w. size ())
	{
		int minimal = 0;
		for (int i = 1; i < w. size (); i ++)
			if (w [minimal] > w [i])
				minimal = i;
		srt. add (w [minimal]);
		w. removenum (minimal);
	}
	w = srt;
	return w;
} /* sortwords */

word strip_prefix (const word &w, const words &strip)
{
	for (int i = 0; i < strip. size (); i ++)
	{
		int len = strip [i]. length ();
		if (!strncmp (strip [i], w, len))
			return word ((const char *) w + len);
	}
	return w;
} /* strip_prefix */

word no_path (const word &w)
{
	const char *s = (const char *) w;
	int pos = w. length ();
	while (-- pos > 0)
	{
		if (s [pos] == '/')
			return word (s + pos + 1);
	}
	return w;
} /* no_path */

word no_ext (const word &w)
{
	const char *s = (const char *) w;
	int pos = w. length ();
	while (-- pos > 0)
	{
		if (s [pos] == '/')
			return w;
		if (s [pos] == '.')
			break;
	}
	if (!pos)
		return w;
	char *tmp = new char [pos + 1];
	strncpy (tmp, s, pos);
	tmp [pos] = '\0';
	word w1 = word (tmp);
	delete [] tmp;
	return w1;
} /* no_ext */



// --------------------------------------------------
// -------------------- FILEDEPS --------------------
// --------------------------------------------------

int getincluded (std::istream &f, words &included)
// Get the list of all the files included directly from this file.
{
	char buf [MAXBUF + 1];
	int ch = f. get ();
	while (ch != EOF)
		if ((ch == '/') && (f. peek () == '/'))
		{
			ignoreline (f);
			ch = f. get ();
		}
		else if ((ch == '/') && (f. peek () == '*'))
		{
			ch = f. get ();
			ch = f. get ();
			while ((ch != '*') && (f. peek () != '/') &&
				(ch != EOF))
				ch = f. get ();
			ch = f. get ();
			ch = f. get ();
		}
		else if (ch == '#')
		{
			const char *include = "include";
			while (f. peek () == ' ')
				f. get ();
			int i = 0;
			while (include [i] && (f. get () == include [i]))
				i ++;
			while (f. peek () == ' ')
				f. get ();
			if (include [i] || (f. peek () != '"'))
				ignoreline (f);
			else
			{
				f. get ();
				i = 0;
				while ((f. peek () != '"') && (i < MAXBUF) &&
					(f. peek () != EOF))
					buf [i ++] = f. get ();
				buf [i] = 0;
				ignoreline (f);
				included. add (word (buf));
			}
			ch = f. get ();
		}
		else
			ch = f. get ();

	return 0;
} /* getincluded */

int getincluded (const word &filename, words &included, const words &dirs)
// Get the list of all the files included directly from the file
// whose name and possible directories are given.
// Return 0 on success or -1 on error (e.g., file not found).
{
	for (int i = -1; i < dirs. size (); i ++)
	{
		std::ifstream f ((const char *) ((i < 0) ? filename :
			(dirs [i] + filename)));
		if (f)
			return getincluded (f, included);
	}

	return -1;
} /* getincluded */

int getdeps (word name, mvmap<word,word> &headers, const words &dirs,
	const words &excludes, int recdepth, bool flatobjects, bool verbose)
// Create a list of all the header files ".h" included in the given file.
// Skip files already known. Use recursion.
{
	// if this file has already been analyzed, ignore it
	if (recdepth && headers. getdomain (). check (name))
		return 0;

	// if this is the first call to this procedure, set file extension
	words included;
	bool notfound = false;
	if (recdepth)
		notfound = getincluded (name, included, dirs);
	else if (!getincluded (name + word (".cpp"), included, dirs))
		name = name + word (".cpp");
	else if (!getincluded (name + word (".c"), included, dirs))
		name = name + word (".c");
	else
	{
		name = name + word (".cpp' or '") + name + word (".c");
		notfound = true;
	}

	if (verbose)
		indent (sout, recdepth) << "begin '" << name << "'\n";
	if (notfound)
	{
		if (verbose)
			indent (sout, recdepth + 1) <<
				"FILE NOT FOUND.\n";
		else
			sout << "Warning: File '" << name << "' not found. "
				"Ignoring its contents.\n";
	}
	included. remove (excludes);
	headers [name]. add (included);
	for (int i = 0; i < included. size (); i ++)
	{
		if (!headers. getdomain (). check (included [i]))
			getdeps (included [i], headers, dirs, excludes,
				recdepth + 1, flatobjects, verbose);
		headers [name]. add (headers (included [i]));
	}
	sortwords (headers [name]);
	if (verbose)
		indent (sout, recdepth) << "*end* '" << name <<
			"' (" << headers [name]. size () << " included)\n";

	return 0;
} /* getdeps */

void getobjects (const word &name, mvmap<word,word> &objects,
	const words &names, const mvmap<word,word> &headers,
	const words &strip, bool flatobjects)
// Determine on which objects the given one is dependent. Recursive.
{
	// if the dependencies for this object are known, then do nothing
	if (objects. getdomain (). check (name))
		return;

	// create the list of all the dependent objects
	words dependent;

	// determine the actual suffix of this object source file
	word suffix;
	if (headers. getdomain (). check (name + word (".c")))
		suffix = ".c";
	else
		suffix = ".cpp";

	// gather all the dependencies based on header files
	const words &depnames = headers (name + suffix);
	for (int i = 0; i < names. size (); i ++)
	{
		if (depnames. check (strip_prefix (names [i], strip) +
			word (".h")) && (names [i] != name))
			dependent. add (names [i]);
	}
	for (int i = 0; (i < depnames. size ()) && flatobjects; ++ i)
	{
		word bare = no_ext (no_path (depnames [i]));
		if (names. check (bare))
			dependent. add (bare);
	}

	// add the dependencies of all the dependent objects to this one
	objects [name]. add (dependent);
	for (int i = 0; i < dependent. size (); i ++)
	{
		getobjects (dependent [i], objects, names, headers, strip,
			flatobjects);
		objects [name]. add (objects (dependent [i]));
	}
	sortwords (objects [name]);
	return;
} /* getobjects */

void writelines (std::ostream &f, const std::string &s, int width = 77)
{
	int pos0 = 0, pos = pos0, spc = -1, col = 0, len = s. length ();

	while (true)
	{
		// analyze the current character
		switch (s [pos])
		{
		case '\t':
			col = (col + 8) / 8 * 8;
			break;
		case '\n':
			col = 0;
			spc = -1;
			break;
		case ' ':
			spc = pos;
		default:
			++ col;
		}
		++ pos;

		// write the end of a string if relevant
		if (pos >= len)
		{
			f << std::string (s, pos0) << "\n\n";
			return;
		}

		// write a portion of a line if necessary
		if ((spc >= 0) && (col >= width))
		{
			pos = spc + 1;
			f << std::string (s, pos0, pos - pos0) << "\\\n\t";
			pos0 = pos;
			col = 8;
		}
	}
	return;
} /* writelines */

void dep_compile (std::ostream &f, const word &name, const word &suffix,
	const words &headers, bool srclib, const char *objext, bool keepdirs)
// Write the compilation dependencies for the given .cpp module.
{
	word srcname = (srclib ? word ("${SRCLIB}") : word ("${SRC}")) + name;
	std::ostringstream fstr;
	fstr << "${OBJ}" << (keepdirs ? name : no_path (name)) <<
		objext << ": " << srcname << suffix;
	for (int i = 0; i < headers. size (); i ++)
		fstr << " " << headers [i];
	fstr << "\n\t${CCI} -o ${OBJ}" <<
		(keepdirs ? name : no_path (name)) << objext <<
		" -c " << srcname << suffix;
	writelines (f, fstr. str ());
	return;
} /* dep_compile */

void dep_link (std::ostream &f, const word &name, const words &objects,
	bool addwxlibs, bool addcapdlibs, bool addcapdglibs,
	const char *objext, bool keepdirs)
// Write the link dependencies for the given executable.
{
	std::ostringstream fstr;
	fstr << "${BIN}" << no_path (name) << "${EXE}: " << "${OBJ}" <<
		no_path (name) << objext;
	for (int i = 0; i < objects. size (); i ++)
		fstr << " ${OBJ}" << no_path (objects [i]) << objext;
	fstr << "\n\t${CC} -o ${BIN}" << no_path (name) <<
		"${EXE} \\\n\t${OBJ}" <<
		(keepdirs ? name : no_path (name)) << objext;
	for (int i = 0; i < objects. size (); i ++)
		fstr << " ${OBJ}" <<
			(keepdirs ? objects [i] : no_path (objects [i])) <<
			objext;
	fstr << " ${CCLIB}";
	if (addcapdlibs)
		fstr << " ${CAPDLIB}";
	if (addcapdglibs)
		fstr << " ${CAPDGLIB}";
	if (addwxlibs)
		fstr << " ${WXLIB}";
	writelines (f, fstr. str ());
	return;
} /* dep_link */

int filedeps (const char *depsname, const words &prognames,
	const words &wxprognames, const words &capdprognames,
	const words &capdgprognames, const words &libnames,
	const words &excludes, const words &dirs,
	const words &strip, bool keepdirs, bool flatobjects,
	bool verbose, const char *objext)
// Create the "filedeps" file. Return 0 on success or -1 on error.
{
	// prepare the union of all the names
	words allnames;
	allnames. add (prognames);
	allnames. add (libnames);

	// prepare lists of headers and libraries for each file
	mvmap<word,word> headers;

	// analyze the files and compute the dependencies
	for (int i = 0; i < allnames. size (); i ++)
		getdeps (allnames [i], headers, dirs, excludes, 0,
			flatobjects, verbose);
	if (flatobjects)
	{
		int n = headers. getdomain (). size ();
		for (int i = 0; i < n; ++ i)
		{
			word name = headers. getdomain () [i];
			word basename = no_path (name);
			if (basename == name)
				continue;
			if (headers. getdomain (). check (basename))
				continue;
			if (!libnames. check (no_ext (basename)))
				continue;
			headers [basename]. add (headers (name));
		}
	}

	// create the contents of the dependencies file
	std::ostringstream s;
	s << "# This file has been generated automatically "
		"by File Dependencies Tracer.\n";
	s << "# Do not edit this file! It will be overwritten "
		"without warning.\n";
//	s << "# Created on " << currenttime () << "\n";

	if (!allnames. empty ())
	{
		s << "\n# ==============================================="
			"============================\n"
			"# Rules for MAKE on how to build object files "
			"(with suitable paths).\n"
			"# ==============================================="
			"============================\n\n";
	}
	for (int i = 0; i < allnames. size (); i ++)
	{
		word suffix;
		if (headers. getdomain (). check (allnames [i] +
			word (".cpp")))
			suffix = ".cpp";
		else
			suffix = ".c";
		dep_compile (s, strip_prefix (allnames [i], strip), suffix,
			headers (allnames [i] + suffix),
			libnames. check (allnames [i]), objext, keepdirs);
	}

	// prepare a list of objects files on which each object file depends
	mvmap<word,word> objects;

	// create a list of the actual programs
//	words prognames;
//	for (int i = 0; i < names. size (); i ++)
//		if (!headers. getdomain (). check (names [i] + word (".h")))
//			prognames. add (names [i]);

	// find the dependencies recursively
	for (int i = 0; i < prognames. size (); i ++)
	{
		getobjects (prognames [i], objects, allnames, headers,
			strip, flatobjects);
	}

	if (!prognames. empty ())
	{
		s << "\n# ==============================================="
			"============================\n"
			"# Rules for MAKE on how to build executables "
			"with paths and extensions.\n"
			"# ==============================================="
			"============================\n\n";
	}
	for (int i = 0; i < prognames. size (); i ++)
	{
		dep_link (s, prognames [i], objects [prognames [i]],
			wxprognames. check (prognames [i]),
			capdprognames. check (prognames [i]),
			capdgprognames. check (prognames [i]),
			objext, keepdirs);
	}
	s << "# The end.\n\n";
	std::string deps = s. str ();

	// werify if the depencencies are up to date
	bool exists = false;
	bool differs = false;
	std::ifstream f_cur (depsname);
	if (f_cur)
	{
		// remember that the file exists
		exists = true;

		// read the contents of the file to a memory buffer
		int depslen = deps. size ();
		char *buffer = new char [depslen + 50000];
		f_cur. read (buffer, depslen + 50000);
		int curlen = f_cur. gcount ();
		f_cur. close ();

		// check if the file differs from the expected contents
		if (curlen != depslen)
		{
		//	sout << "DEBUG: Different size: " <<
		//		f_cur. gcount () << " and " <<
		//		depslen << "\n";
			differs = true;
		}
		else for (int i = 0; i < depslen; ++ i)
		{
			if (buffer [i] == deps [i])
				continue;
		//	sout << "DEBUG: Different char no. " << i <<
		//		": " << buffer [i] << " and " <<
		//		deps [i] << ".\n";
			differs = true;
			break;
		}

		// release the buffer
		delete [] buffer;
	}
	else
	{
		differs = true;
	}

	if (differs)
	{
		// write the dependencies to the output file
		sout << (exists ? "Updating the dependencies in '" :
			"Creating '") << depsname << "'... ";
		std::ofstream f (depsname);
		if (!f)
			fileerror (depsname, "create");
		f << deps;
		f. close ();
		sout << "Done.\n";
	}
	else
	{
		// say that the dependencies are up to date
		sout << "The dependencies in '" << depsname <<
			"' are up-to-date.\n";

		// touch the file to make sure that the date
		// of the dependencies is newer than the dates of the files
		// (Note: I couldn't come up with a better solution than
		// writing one byte to the file, it seems that C++ doesn't
		// support a platform-independent method for changing
		// file attributes.)
	//	std::fstream f (depsname, std::ios::in | std::ios::out);
	//	f. put (deps [0]);
	//	f. close ();
	}

	return 0;
} /* filedeps */


// --------------------------------------------------
// ---------------------- MAIN ----------------------
// --------------------------------------------------

int main (int argc, char *argv [])
{
	// turn on the program timing message
	program_time = 1;

	// prepare user-configurable data
	char *depsname = NULL;
	char *prognames [MAXN], *wxprognames [MAXN],
		*capdprognames [MAXN], *capdgprognames [MAXN],
		*libnames [MAXN];
	char *dirs [MAXN], *excludes [MAXN], *strip [MAXN];
	int nprognames = 0, nwxprognames = 0, ncapdprognames = 0,
		ncapdgprognames = 0, nlibnames = 0;
	int ndirs = 0, nexcludes = 0, nstrip = 0;
	bool keepdirs = false;
	bool verbose = false;
	bool setobjext = false;
	bool flatobjects = false;

	// analyze the command line
	arguments a;
	arg (a, NULL, depsname);
	arg (a, NULL, prognames, nprognames, MAXN);
	arg (a, "w", wxprognames, nwxprognames, MAXN);
	arg (a, "c", capdprognames, ncapdprognames, MAXN);
	arg (a, "g", capdgprognames, ncapdgprognames, MAXN);
	arg (a, "l", libnames, nlibnames, MAXN);
	arg (a, "I", dirs, ndirs, MAXN);
	arg (a, "x", excludes, nexcludes, MAXN);
	arg (a, "s", strip, nstrip, MAXN);
	argswitch (a, "d", keepdirs, true);
	argswitch (a, "v", verbose, true);
	argswitch (a, "o", setobjext, true);
	argswitch (a, "f", flatobjects, true);
	arghelp (a);

	argstreamprepare (a);
	int argresult = a. analyze (argc, argv);
	argstreamset ();

	// show the program's title
	if (argresult >= 0)
		sout << title << '\n';

	// if something was incorrect, show an additional message and exit
	if (argresult < 0)
	{
		sout << "Call with '--help' for help.\n";
		return 2;
	}

	// if help requested or no filenames present, show help information
	if ((argresult > 0) || !depsname || (!nprognames &&
		!nwxprognames && !ncapdprognames && !ncapdgprognames &&
		!nlibnames))
	{
		sout << helpinfo << '\n';
		return 1;
	}

	// set the right extension for object files
	const char *objext = setobjext ? "${OBJEXT}" : ".o";

	// transform the lists of names into sets of words
	words wprognames, wwxprognames, wcapdprognames, wcapdgprognames,
		wlibnames, wdirs, wexcludes, wstrip;
	for (int i = 0; i < nprognames; i ++)
		wprognames. add (word (prognames [i]));
	for (int i = 0; i < nwxprognames; i ++)
		wwxprognames. add (word (wxprognames [i]));
	for (int i = 0; i < ncapdprognames; i ++)
		wcapdprognames. add (word (capdprognames [i]));
	for (int i = 0; i < ncapdgprognames; i ++)
		wcapdgprognames. add (word (capdgprognames [i]));
	for (int i = 0; i < nstrip; i ++)
		wstrip. add (word (strip [i]));
	// make the prognames contain also wxprognames and capdprognames
	wprognames. add (wwxprognames);
	wprognames. add (wcapdprognames);
	wprognames. add (wcapdgprognames);
	for (int i = 0; i < nlibnames; i ++)
		wlibnames. add (word (libnames [i]));
	for (int i = 0; i < ndirs; i ++)
		wdirs. add (word (dirs [i]));
	for (int i = 0; i < nexcludes; i ++)
		wexcludes. add (word (excludes [i]));

	// try running the main function and catch an error message if thrown
	int result = 0;
	try
	{
		filedeps (depsname, sortwords (wprognames),
			sortwords (wwxprognames), sortwords (wcapdprognames),
			sortwords (wcapdgprognames), sortwords (wlibnames),
			wexcludes, wdirs, wstrip, keepdirs, flatobjects,
			verbose, objext);
	}
	catch (const char *msg)
	{
		sout << "ERROR: " << msg << '\n';
		result = -1;
	}
	catch (...)
	{
		sout << "ABORT: An unknown error occurred.\n";
		result = -1;
	}

	return result;
} /* main */

/// @}

