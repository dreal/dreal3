/// @addtogroup system
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file textfile.h
///
/// This file contains some useful functions related to the text
/// input/output procedures. It also contains the definition of some output
/// streams that can be used instead the standard ones (sout, serr)
/// which support logging to a file or suppressing messages to the screen.
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

// Started in July 1997. Last revision: March 5, 2008.


#ifndef _CHOMP_SYSTEM_TEXTFILE_H_
#define _CHOMP_SYSTEM_TEXTFILE_H_

#include "config.h"

#include <ctime>
#include <iostream>
#include <fstream>
#include <sstream>
#include <iomanip>

namespace chomp {
namespace homology {


// classes defined within this header file:
class textfile;
class outputstream;


// --------------------------------------------------
// ----------------- OUTPUT STREAM ------------------
// --------------------------------------------------

/// This class defines an output stream for replacing the standard 'cout'.
/// It has the additional features of flushing the output after every
/// operation, suppressing the output, or logging the output to a file.
class outputstream
{
public:
	/// The default constructor.
	outputstream (std::ostream &_out = std::cout,
		bool _show = true, bool _flush = false);

	/// The destructor.
	~outputstream ();

	/// Turns on logging to a file.
	/// If the file exists, its contents is ereased.
	void logfile (const char *filename);

	/// Turns on logging to the same file as some other stream.
	void logfile (const outputstream &other);

	/// If this variable is set to true then everything that is
	/// written to this stream is also written to 'cout'.
	/// If this variable is set to false then the screen output
	/// is suppressed, while logging can still be turned on.
	bool show;

	/// If this variable is set to true then everything that is
	/// written to this stream is also written to the log file.
	bool log;

	/// If this variable is set to true then both the output stream
	/// 'cout' and the log file are flashed after every write operation.
	/// Note that this may slow down the output significantly if the
	/// log file is located on a network drive.
	bool flush;

	/// Returns a pointer to the stream which is working as a log file.
	/// Returns 0 if no such stream is bound with this output stream.
	std::ofstream *getlogstream (void);

	/// A reference to the main output stream bound with this stream.
	std::ostream &out;

	/// Makes this stream keep the allocated file open for ever, and not
	/// close it even in the destructor. It is assumed then that the
	/// file will be closed automatically by the operating system.
	void keepforever (void);

	/// Local mute of the stream.
	/// This class defines an object which makes the stream mute
	/// by suppressing output to both the screen and the log file
	/// and restores its setting when the object is destroyed.
	struct mute
	{
		mute (outputstream &_stream): stream (_stream),
			show (_stream. show), log (_stream. log)
			{stream. show = false; stream. log = false; return;}
		~mute () {stream. show = show;
			stream. log = log; return;}
		outputstream &stream;
		bool show;
		bool log;
	};

protected:
	/// A pointer to the log file stream.
	std::ofstream *logstream;

	/// This variable is set to true if this log file pointer was copied
	/// from another output stream, and therefore it should not be
	/// deleted by this stream.
	bool copied;

}; /* class outputstream */

// --------------------------------------------------

inline outputstream::outputstream (std::ostream &_out, bool _show,
	bool _flush): out (_out)
{
	show = _show;
	flush = _flush;
	log = false;
	logstream = NULL;
	copied = false;
	return;
} /* outputstream::outputstream */

inline void outputstream::logfile (const char *filename)
{
	if (logstream && !copied)
		delete logstream;
	copied = false;
	logstream = new std::ofstream (filename);
	if (!logstream || !*logstream)
	{
		out << "WARNING: Can't create '" << filename <<
			"'. Logging to a file has been turned off." <<
			std::endl;
		if (logstream)
			delete logstream;
		logstream = NULL;
	}
	else
		log = true;
	return;
} /* outputstream::logfile */

inline void outputstream::logfile (const outputstream &other)
{
	if (!copied && logstream)
		delete logstream;
	logstream = other. logstream;
	if (logstream)
	{
		copied = true;
		log = true;
	}
	return;
} /* outputstream::logfile */

inline outputstream::~outputstream ()
{
	if (!copied && logstream)
		delete logstream;
	return;
} /* outputstream::~outputstream */

inline std::ofstream *outputstream::getlogstream (void)
{
	return logstream;
} /* outputstream::getlogstream */

inline void outputstream::keepforever (void)
{
	copied = true;
	return;
} /* outputstream::getlogstream */

/// The operator << for writing any kind of object to the output stream.
/// This object is written using the operator << of the standard stream.
template<typename type>
inline outputstream &operator << (outputstream &out, const type &object)
{
	if (out. flush)
	{
		if (out. show)
			out. out << object << std::flush;
		if (out. log && out. getlogstream ())
			(*(out. getlogstream ())) << object << std::flush;
	}
	else
	{
		if (out. show)
			out. out << object;
		if (out. log && out. getlogstream ())
			(*(out. getlogstream ())) << object;
	}
	return out;
} /* operator << */

/// A specialization of the operator << for writing a C-style string
/// to the output stream.
inline outputstream &operator << (outputstream &out, const char *object)
{
	if (out. flush)
	{
		if (out. show)
			out. out << object << std::flush;
		if (out. log && out. getlogstream ())
			(*(out. getlogstream ())) << object << std::flush;
	}
	else
	{
		if (out. show)
			out. out << object;
		if (out. log && out. getlogstream ())
			(*(out. getlogstream ())) << object;
	}
	return out;
} /* operator << */

/// A specialization of the operator << for putting manipulators
/// (like std::endl, std::flush) to the output stream.
inline outputstream &operator << (outputstream &out,
	std::ostream& (*object)(std::ostream&))
{
	if (out. flush)
	{
		if (out. show)
			out. out << object << std::flush;
		if (out. log && out. getlogstream ())
			(*(out. getlogstream ())) << object << std::flush;
	}
	else
	{
		if (out. show)
			out. out << object;
		if (out. log && out. getlogstream ())
			(*(out. getlogstream ())) << object;
	}
	return out;
} /* operator << */

// --------------------------------------------------

#ifndef OUTPUTSTREAM
/// This symbol is defined if the "outputstream" class is available,
/// and the basic streams like "sout" are defined.
#define OUTPUTSTREAM
#endif

/// A replacement for standard output stream, with optional logging
/// and other features provided by the class 'outputstream'.
extern outputstream sout;

/// The console output stream to which one should put all the junk that
/// spoils the log file, like progress indicators.
extern outputstream scon;

/// A wrapper for the standard error stream.
extern outputstream serr;

/// The output stream to which one can send messages for logging only.
/// Those messages are not shown to the standard output and are ignored
/// if the log file is not in use.
extern outputstream slog;

/// An output stream for writing additional debug messages.
/// This stream is turned off by default.
extern outputstream sbug;

/// An auxiliary stream which captures sequences of processed data.
/// This stream is used by some programs in the CHomP package.
extern outputstream sseq;


// --------------------------------------------------
// ----------------- various tools ------------------
// --------------------------------------------------

/// A simple template for swapping two elements with the use of a temporary
/// variable of the same type and the assignment operator.
template <class type>
inline void swapelements (type &x, type &y)
{
	type z = x;
	x = y;
	y = z;
	return;
} /* swapelements */

/// A simple template that sorts an array using the bubble sort method,
/// removes repeated elements and returns the new number of the elements.
template <class type>
inline int sortelements (type *tab, int n)
{
	switch (n)
	{
	case 0:
		return 0;
	case 1:
		return 1;
	case 2:
		if (tab [0] == tab [1])
			return 1;
		else if (tab [0] > tab [1])
			swapelements (tab [0], tab [1]);
		return 2;
	default:
		for (int i = 0; i < n - 1; i ++)
		{
			for (int j = i + 1; j < n; j ++)
				if (tab [i] > tab [j])
					swapelements (tab [i],
						tab [j]);

			if (tab [i] == tab [i + 1])
			{
				n --;
				for (int j = i + 1; j < n; j ++)
					tab [j] = tab [j + 1];
			}
		}
		break;
	}
	return n;
} /* sortelements */

/// Ignores the input characters until the end of a line, including this
/// end of the line.
inline void ignoreline (std::istream &in)
{
	in. ignore (0x7FFFFFFFl, '\n');
	return;
} /* ignoreline */

/// Ignores white characters (spaces, tabulators, CRs and LFs),
/// as well as comments from the input text file. The comment
/// begins with a semicolon and ends with the end of the line.
inline void ignorecomments (std::istream &in)
{
	int ch = in. peek ();
	while (true)
	{
		switch (ch)
		{
		case ';':
			ignoreline (in);
			ch = in. peek ();
			break;
		case ' ':
		case '\t':
		case '\r':
		case '\n':
			in. get ();
			ch = in. peek ();
			break;
		default:
			return;
		}
	}	
} /* ignorecomments */

/// Returns the matching closing parenthesis for the given opening one
/// or EOF if none.
inline int closingparenthesis (int ch)
{
	switch (ch)
	{
		case '(':
			return ')';
		case '{':
			return '}';
		case '[':
			return ']';
		case '<':
			return '>';
		case '/':
			return '/';
		default:
			return EOF;
	}
} /* closingparenthesis */

/// Reads an opening parenthesis from the input file.
/// Return a corresponding closing parenthesis or EOF if none was found.
inline int readparenthesis (std::istream &in)
{
	int closing = closingparenthesis (in. peek ());
	if (closing != EOF)
		in. get ();
	return closing;
} /* readparenthesis */

/// Returns the entire command line as a single string.
inline std::string commandline (int argc, char *argv [])
{
	std::string s;
	for (int i = 0; i < argc; i ++)
	{
		if (i)
			s += ' ';
		s += argv [i];
	}
	return s;
} /* commandline */

/// Retrieves the current time as a pointer to a C-style string.
inline const char *currenttime (void)
{
	std::time_t t;
	std::time (&t);
	return std::asctime (std::localtime (&t));
} /* currenttime */

/// Writes the given object to a file whose name is a concatenation
/// of the prefix and the given file name.
/// If the prefix is 0 thenthe prefix is treated as an empty string.
/// Displays a warning if unsuccessful, does not throw any exception.
/// This procedure can be applied to any data type which has the operator <<
/// for writing it to a text output stream (std::ostream) defined.
template <class settype>
static void savetheset (const settype &c, const char *prefix,
	const char *filename, const char *name)
{
	// if there is no prefix given, do not save the file
	if (!prefix)
		return;

	// prepare the full file name
	std::string str;
	if (prefix)
		str = std::string (prefix) + std::string (filename);
	else
		str = filename;
	const char *s = str. c_str ();

	// create the output file
	std::ofstream out (s);
	if (!out)
	{
		sout << "WARNING: Cannot save the file '" << s << "'.\n";
		return;
	}

	// write the cubes to the output file
	sout << "Saving " << name << " to '" << s << "'... ";
	out << "; This is " << name << ".\n";
	out << c;
	sout << "Done.\n";

	return;
} /* savetheset */


// --------------------------------------------------
// ----------------- ERROR MESSAGE ------------------
// --------------------------------------------------

/// The first macro in a pair of macrodefinitions for throwing
/// an error message. In order to throw an error message of the type
/// std::string, one can type something like the following:
///
///	ERRORMSG << "Wrong number: " << n << " instead of 0." << THROW
///
/// Note that there is no semicolon at the end. This is important
/// especially in the setting like below:
///
///	if (n != 0)
///		ERRORMSG << .......... << THROW
///	else
///		..........
///
/// In some cases this pair of macros may probably not work properly,
/// but at the moment I couldn't come up with anything better.
#define ERRORMSG {std::ostringstream error_msg_string; error_msg_string

/// The second macro in a pair of macrodefinitions for throwing an error
/// message. See the description at the ERRORMSG macro.
#define THROW ""; throw error_msg_string. str (). c_str (); }

// --------------------------------------------------

/// Throws a message about the inability to do something with a file.
/// By default this is a problem with opening the file, but another name of
/// this action may be provided.
inline void fileerror (const char *filename, const char *what = "open")
{
	ERRORMSG << "Cannot " << what << " the file '" <<
		filename << "'." << THROW
	return;
} /* fileerror */


// --------------------------------------------------
// -------------------- TEXTFILE --------------------
// --------------------------------------------------

/// The maximal length of a phrase read at a time from the input
/// text file by the class textfile.
#define MAXTEXTLENGTH 200

/// A class for reading text data from a text file.
/// All blank characters and comments are ignored.
/// NOTE: This class is deprecated, it is recommended to use
/// the class std::istream directly.
class textfile
{
public:
	/// The default constructor.
	textfile ();

	/// A constructor for an opened file.
	textfile (std::istream &in);

	// a constructor which opens a file
//	textfile (char *filename);

	/// Opens a file with the given name.
	/// Returns 1 if a file associated with this object has already been
	/// opened before, 0 on success, -1 in case of an error (no message
	/// is displayed).
	int open (const char *filename);

	/// Closes the file.
	void close ();

	/// The destructor.
	~textfile ();

	/// Read an integer number from the input file.
	/// If none can be read, returns the suggested default value.
	/// If requested, ignores a preceding ':', '=' or ',' if any.
	long readnumber (long defaultnumber = 0, int ignorecolons = 0);

	/// Returns the first non-white character waiting to be read.
	/// Returns EOF if end-of-file has been reached.
	int checkchar ();

	/// Read one non-white character from the file.
	/// Return EOF if end-of-file has been reached.
	int readchar ();

	/// Reads one word from the file and returns its actual length.
	int readword (char *buf, int maxlength);

	/// Reads a strongly expected phrase from the file.
	/// Ignores white characters before the phrase and inside it.
	/// Returns 0 on success, -1 if the phrase was not present
	/// in the input (shows an error message in that case).
	int readphrase (const char *phrase);

	/// Ignore the current line from the current position to the end
	/// of line, including the end of line character.
	void ignoreline ();

	/// Returns the current line number.
	long linenumber ();

	/// Returns the text file's status: 0 = not opened,
	/// 1 = opened, 13 = initialized with an input stream.
	operator int ();

private:
	/// The character already read and waiting to be interpreted.
	int ch;

	/// The current line number.
	long line;

	/// The true file if it was opened.
	std::ifstream *fs;

	/// A pointer to an input stream (usually equal to 'fs').
	std::istream *s;

	/// Ignores white characters and fills in the variable 'ch'
	/// with the first non-white character.
	void ignorespaces ();

}; /* class textfile */


} // namespace homology
} // namespace chomp

#endif // _CHOMP_SYSTEM_TEXTFILE_H_

/// @}

