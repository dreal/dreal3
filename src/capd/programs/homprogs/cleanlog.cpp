/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file cleanlog.cpp
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2008 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started on May 1, 2000. Last revision: March 23, 2002.


#include "capd/homology/config.h"
#include "capd/homology/arg.h"

#include <iostream>
#include <fstream>
#include <cstdlib>


using namespace capd::homology;
using std::cout;
using std::endl;


const char *title = "\
CleanLog, ver. 0.01. Copyright (C) 2000-2002 by Pawel Pilarczyk.\n\
This is free software. No warranty. Consult 'license.txt' for details.";

const char *helpinfo = "\
Call with: <nothing> <OR> filename <OR> infile outfile <OR> -h for help.\n\
It is a program for cleaning a log file created simply by re-directing\n\
an output stream of a program to a file. It removes from the log text\n\
normally erased from the screen with '\\r' (CR) and '\\b' (BackSpace).\n\
If no file name is given, the standard input and standard output are\n\
assumed. If a single file name is given, this file will be replaced\n\
with the new log file, otherwise... you can work it out, I hope.\n\
Note: In this version the entire log file is kept in the memory.\n\
For more information ask the author at http://www.PawelPilarczyk.com/.";


char *readlog (std::istream &in, int &length)
{
	int linebeg = 0;
	length = 0;
	int ch = in. get ();
	char *buf = NULL;
	int size = 0;
	int already_read = 0;
	while (ch != EOF)
	{
		switch (ch)
		{
			case '\b':
				if (linebeg < length)
					length --;
				break;
			case '\r':
				ch = in. get ();
				already_read = 1;
				if (ch == '\n')
					break;
				length = linebeg;
				break;
			case '\n':
				linebeg = length + 1;
			default:
				if (length >= size)
				{
					int newsize = 2 * size + 13;
					char * newbuf = new char [newsize];
					if (!newbuf || (newsize < size))
					{
						cout << "File too long." <<
							endl;
						length = -1;
						return NULL;
					}
					for (int i = 0; i < length; i ++)
						newbuf [i] = buf [i];
					delete [] buf;
					size = newsize;
					buf = newbuf;
				}
				buf [length ++] = (char) ch;
				break;
		}
		if (already_read)
			already_read = 0;
		else
			ch = in. get ();
	}
	return buf;
} /* readlog */


// --------------------------------------------------
// ---------------------- MAIN ----------------------
// --------------------------------------------------

int main (int argc, char *argv [])
// Return: 1 = help displayed, -1 - error, 0 - Ok.
{
	// show the program's title
//	cout << title << endl;

	char *inname = NULL, *outname = NULL;

	arguments a;
	arg (a, NULL, inname);
	arg (a, NULL, outname);
	arghelp (a);

	int argresult = a. analyze (argc, argv);

	if (inname && !outname)
		outname = inname;

	// if something was incorrect, show an additional message and exit
	if (argresult < 0)
	{
		cout << "Call with -h for help." << endl;
		return -1;
	}

	// if help requested, show help information
	if (argresult > 0)
	{
		cout << title << endl << helpinfo << endl;
		return 1;
	}

	// open the input file if the file name was given
	std::ifstream *in = NULL;
	if (inname)
	{
		in = new std::ifstream;
		if (in)
			#ifdef ppDOS
			in -> open (inname, std::ios::in | std::ios::binary);
			#else
			in -> open (inname, std::ios::in);
			#endif
		if (!in || !*in)
		{
			cout << "Unable to open the input file '" <<
				inname << "'." << endl;
			return -1;
		}
	}

	// read the input file and create the log file in the memory
	int length = 0;
	char *log;
	if (in)
		log = readlog (*in, length);
	else
		log = readlog (std::cin, length);

	// close the input file if it was opened
	if (in)
		delete in;

	// if an error occurred, write an error message
	if (length < 0)
		return -1;

	// open the output file if the file name was given
	std::ofstream *out = NULL;
	if (outname)
	{
		out = new std::ofstream (outname);
	//	out. open (outname, std::ios::out | std::ios::trunc);
		if (!out || !*out)
		{
			cout << "Unable to create the output file '" <<
				outname << "'." << endl;
			return -1;
		}
	}

	// write the log
	for (int i = 0; i < length; i ++)
		if (out)
			out -> put (log [i]);
		else
			cout. put (log [i]);

	// close the output file if it was opened
	if (out)
		delete out;

	delete [] log;
	return 0;
} /* main */

/// @}

