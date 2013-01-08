/// @addtogroup system
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file textfile.cpp
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started in December 1997. Last revision: April 12, 2006.


#include "capd/homology/config.h"
#include "capd/homology/textfile.h"

#include <cstdlib>
#include <ctime>
#include <cstring>
#include <iostream>
#include <fstream>
#include <sstream>

namespace capd {
namespace homology {


// --------------------------------------------------
// ----------------- OUTPUT STREAM ------------------
// --------------------------------------------------

outputstream scon (std::cout, true, true);
outputstream sout (std::cout, true, true);
outputstream serr (std::cout, true, true);
outputstream slog (std::cout, false, true);
outputstream sbug (std::cout, false, true);
outputstream sseq (std::cout, false, false);


// --------------------------------------------------
// -------------------- TEXTFILE --------------------
// --------------------------------------------------

textfile::textfile ()
{
	fs = NULL;
	s = fs;
	return;
} /* textfile::textfile */

int textfile::open (const char *filename)
{
	// open the file only if it has not been opened yet
	if (s)
		return 1;

	// try to open the file
	fs = new std::ifstream;
	if (fs)
		fs -> open (filename, std::ios::in);

	// in the case of failure return -1 and prepare for another trial
	if (!fs || !*fs)
	{
		if (fs)
			delete fs;
		fs = NULL;
		s = fs;
		return -1;
	}

	// initialize the other internal variables
	s = fs;
	line = 1;
	ch = s -> peek ();

	return 0;
} /* textfile::open */

/*
textfile::textfile (char *filename)
{
	fs = NULL;
	s = fs;
	open (filename);
	return;
}*/ /* textfile::textfile */

textfile::textfile (std::istream &in)
{
	// remember the pointer to this file
	fs = NULL;
	s = &in;

	// reset the other internal variables
	line = 1;
	ch = s -> peek ();

	return;
} /* textfile::textfile */

void textfile::close ()
{
	if (fs)
	{
		fs -> close ();
		delete fs;
		fs = NULL;
	}
	s = NULL;
	return;
} /* textfile::close */

textfile::~textfile ()
{
	close ();
	return;
} /* textfile::~textfile */

// --------------------------------------------------

static int space (int ch)
// Return 1 iff the given character is a blank one.
{
	switch (ch)
	{
		case '\n':
		case '\r':
		case '\t':
		case ' ':
			return 1;
		default:
			return 0;
	}
} /* space */

long textfile::linenumber ()
{
	if (!s)
		return 0;
	else
		return line;
} /* line number */

void textfile::ignorespaces ()
{
	if (!s)
		return;

	while (1)
		switch (ch)
		{
			case EOF:
				return;
			case ';':
				ignoreline ();
				break;
			case '\n':
				line ++;
			default:
				if (space (ch))
				{
					s -> get ();
					ch = s -> peek ();
				}
				else
					return;
				break;
		}
} /* textfile::ignorespaces */

int textfile::checkchar (void)
{
	if (!s)
		return EOF;

	ignorespaces ();

	return ch;
} /* textfile::checkchar */

void textfile::ignoreline ()
{
	if (!s)
		return;
	if (ch == EOF)
		return;
	if (ch == '\n')
		line ++;

	capd::homology::ignoreline (*s);
	ch = s -> peek ();

	return;
} /* textfile::ignoreline */

int textfile::readchar ()
{
	if (!s)
		return EOF;

	int result = checkchar ();
	s -> get ();
	ch = s -> peek ();

	return result;
} /* textfile::readchar */

long textfile::readnumber (long defaultnumber, int ignorecolons)
{
	if (!s)
		return 0;

	if (ignorecolons)
		while ((checkchar () == ':') || (checkchar () == '=') ||
			(checkchar () == ','))
			readchar ();

	if (checkchar () == '+')
		readchar ();

	int minus = (checkchar () == '-');
	if (minus)
		readchar ();

	if ((checkchar () < '0') || (checkchar () > '9'))
		return defaultnumber;

	int number = 0;
	while ((ch >= '0') && (ch <= '9'))
	{
		number = 10 * number + ch - '0';
		s -> get ();
		ch = s -> peek ();
	}

	return (minus ? -number : number);
} /* textfile::readnumber */

int textfile::readphrase (const char *phrase)
{
	if (!s)
		return 0;

	// find the first non-white character in the phrase
	int pos = 0;
	while (phrase [pos] && space (phrase [pos]))
		pos ++;

	while (phrase [pos])
	{
		// read a character from the input file and make it lowercase
		int c = readchar ();
		if ((c >= 'A') && (c <= 'Z'))
			c += 'a' - 'A';

		// take a character from the phrase and make it lowercase
		int d = phrase [pos];
		if ((d >= 'A') && (d <= 'Z'))
			d += 'a' - 'A';

		// compare the two characters
		if (c != d)
		{
			sout << "Error (line " << line << "): ";
			sout << "\"" << phrase << "\" expected.\n";

			// debug:
			sout << "Letter '" << (char) c <<
				"' found instead.\n";

			return -1;
		}

		// take the next non-white character
		pos ++;
		while (phrase [pos] && space (phrase [pos]))
			pos ++;
	}

	return 0;
} /* textfile::readphrase */

int textfile::readword (char *buf, int maxlength)
{
	if (!s)
		return 0;

	ignorespaces ();
	int pos = 0;
	while (!space (ch) && (ch != EOF) && (pos < maxlength - 1))
	{
		if (buf)
			buf [pos] = (char) ch;
		pos ++;
		s -> get ();
		ch = s -> peek ();
	}
	if (buf)
		buf [pos] = 0;
	pos ++;

	return pos;
} /* textfile::readword */

textfile::operator int (void)
{
	if (fs)
		return 1;
	else if (s)
		return 13;
	else
		return 0;
} /* textfile::operator int */


} // namespace homology
} // namespace capd

/// @}

