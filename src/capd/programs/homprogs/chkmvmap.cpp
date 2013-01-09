/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file chkmvmap.cpp
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started on March 30, 2002. Last revision: April 24, 2007.


#include "capd/homology/config.h"
#include "capd/homology/textfile.h"
#include "capd/homology/pointset.h"
#include "capd/homology/cubisets.h"
#include "capd/homology/timeused.h"
#include "capd/homology/arg.h"

#include <exception>
#include <new>
#include <iostream>
#include <iomanip>
#include <fstream>
#include <cstdlib>

using namespace capd::homology;


// --------------------------------------------------
// -------------------- OVERTURE --------------------
// --------------------------------------------------

const char *title = "\
CHKMVMAP, ver. 0.08. Copyright (C) 1997-2010 by Pawel Pilarczyk.\n\
This is free software. No warranty. Consult 'license.txt' for details.";

const char *helpinfo = "\
Call with: F.map [X.cub] A.cub Y.cub B.cub <OR> F.map [[X.cub] Y.cub]\n\
<OR> -i [[X.cub] A.cub].\n\
This program verifies if the multivalued cubical F: (X,A) -> (Y,B)\n\
is appropriate for homology computation with the program 'homcubes'.\n\
Switches and additional arguments:\n\
-i - this is an index map (for the discrete Conley index),\n\
-w n - wrap the space (repeat for each axis, use 0 for no space wrapping),\n\
-s [chkmvmap.cub] - save all the 'bad' cubes/cells which cause problems,\n\
-a0 - don't check, -a1 - only check the acyclicity of the map.\n\
For more information ask the author at http://www.PawelPilarczyk.com/.";


// --------------------------------------------------
// --------------- error/warning bits ---------------
// --------------------------------------------------
// Bits indicating specific errors or warnings.
// In this notation, X and A (as well as Y and B) are disjoint.

#define errXinY 0x0001
#define errAinB 0x0002
#define errAoutY 0x0004
#define errFdefX 0x0008
#define errFdefA 0x0010
#define errFXoutYB 0x0020
#define errFAinY 0x0040
#define errFAoutY 0x0080
#define errFacyclX 0x0100
#define errFacyclA 0x0200


// --------------------------------------------------
// -------------- CHKMVMAP subroutines --------------
// --------------------------------------------------

int readfiles (char *Fname, char *Xname, char *Aname, char *Yname,
	char *Bname, cubicalmap &F, cubes &X, cubes &A, cubes &Y, cubes &B)
{
	// read the map
	if (Fname)
	{
		sout << "Reading F from '" << Fname << "'... ";
		std::ifstream in (Fname);
		if (!in)
			fileerror (Fname);
		in >> F;
		sout << F. getdomain (). size () << " images read.\n";
	}

	// read the map's domain if any
	if (Xname)
	{
		sout << "Reading X from '" << Xname << "'... ";
		std::ifstream in (Xname);
		if (!in)
			fileerror (Xname);
		in >> X;
		sout << X. size () << " cubes read.\n";
	}

	// read A if any
	if (Aname)
	{
		sout << "Reading A from '" << Aname << "'... ";
		std::ifstream in (Aname);
		if (!in)
			fileerror (Aname);
		in >> A;
		sout << A. size () << " cubes read.\n";
	}

	// read the map's codomain if any
	if (Yname)
	{
		sout << "Reading Y from '" << Yname << "'... ";
		std::ifstream in (Yname);
		if (!in)
			fileerror (Yname);
		in >> Y;
		sout << Y. size () << " cubes read.\n";
	}

	// read B if any
	if (Bname)
	{
		sout << "Reading B from '" << Bname << "'... ";
		std::ifstream in (Bname);
		if (!in)
			fileerror (Bname);
		in >> B;
		sout << B. size () << " cubes read.\n";
	}

	return 0;
} /* readfiles */

void checkinclXYB (const cubes &X, const cubes &Y, const cubes &B,
	int &errcount, int &/*warncount*/, int &badbits,
	std::ostream *savethem)
{
	sout << "Checking the inclusion of X\\A in Y... ";
	cubes bad;
	for (int_t i = 0; i < X. size (); i ++)
		if ((!Y. check (X [i])) && (!B. check (X [i])))
			bad. add (X [i]);
	if (!bad. empty ())
	{
		sout << "Failed.\n--- Error: " << bad. size () <<
			" cubes from X\\A are not in Y. ---\n";
		if (savethem)
			(*savethem) << "; Cubes from X\\A that are "
				"not in Y:\n" << bad << '\n';
		errcount ++;
		badbits |= errXinY;
	}
	else
		sout << "Passed.\n";
	return;
} /* checkinclXYB */

void checkinclAB (const cubes &A, const cubes &Y, const cubes &B,
	int &errcount, int &warncount, int &badbits, std::ostream *savethem)
{
	sout << "Checking the inclusion of A in B... ";
	cubes badA, badY;
	for (int_t i = 0; i < A. size (); i ++)
	{
		if (!B. check (A [i]))
		{
			if (Y. check (A [i]))
				badY. add (A [i]);
			else
				badA. add (A [i]);
		}
	}

	if (badA. empty () && badY. empty ())
	{
		sout << "Passed.\n";
		return;
	}

	sout << "Failed.\n";
	if (!badA. empty ())
	{
		sout << "--- Error: " << badA. size () <<
			" cubes from A are in Y\\B. ---\n";
		if (savethem)
			(*savethem) << "; Cubes from A that are "
				"in Y\\B:\n" << badA << '\n';
		errcount ++;
		badbits |= errAinB;
	}
	if (!badY. empty ())
	{
		sout << "--- Warning: " << badY. size () <<
			" cubes from A are outside Y. ---\n";
		if (savethem)
			(*savethem) << "; Cubes from A that are "
				"outside Y:\n" << badY << '\n';
		warncount ++;
		badbits |= errAoutY;
	}
	return;
} /* checkinclAB */

void checkdomain (const cubicalmap &F, const cubes &X,
	const char *Xname, int errbit, int &errcount,
	int &/*warncount*/, int &badbits, std::ostream *savethem)
{
	sout << "Checking if F is defined on " << Xname << "... ";
	const cubes &dom = F. getdomain ();
	cubes bad;
	for (int_t i = 0; i < X. size (); i ++)
		if (!dom. check (X [i]))
			bad. add (X [i]);
	if (!bad. empty ())
	{
		sout << "Failed.\n--- Error: "
			"There are " << bad. size () <<
			" cubes in " << Xname << " on which F "
			"is not defined. ---\n";
		if (savethem)
			(*savethem) << "; Cubes from " << Xname <<
				" on which F is not defined:\n" <<
				bad << '\n';
		errcount ++;
		badbits |= errbit;
	}
	else
		sout << "Passed.\n";
	return;
} /* checkdomain */

void checkimageX (const cubicalmap &F, const cubes &X, const cubes &Y,
	const cubes &B, int &/*errcount*/, int &warncount, int &badbits,
	std::ostream *savethem)
{
	sout << "Verifying that F(X\\A) is contained in Y... ";
	cubes bad;
	const cubes &dom = F. getdomain ();
	for (int_t i = 0; i < X. size (); i ++)
	{
		if (!dom. check (X [i]))
			continue;
		const cubes &cset = F (X [i]);
		for (int_t i = 0; i < cset. size (); i ++)
			if (!Y. check (cset [i]) &&
				!B. check (cset [i]))
				bad. add (cset [i]);
	}

	if (!bad. empty ())
	{
		sout << "Failed.\n--- Warning: " <<
			bad. size () << " cubes from F(X\\A) are "
			"outside Y. ---\n";
		if (savethem)
			(*savethem) << "; Cubes from F(X\\A) that are "
				"outside Y:\n" << bad << '\n';
		warncount ++;
		badbits |= errFXoutYB;
	}
	else
		sout << "Passed.\n";
	return;
} /* checkimageX */

void checkimageA (const cubicalmap &F, const cubes &A, const cubes &Y,
	const cubes &B,
	int &errcount, int &warncount, int &badbits, std::ostream *savethem)
{
	sout << "Verifying that A is mapped into B... ";

	// prepare a set of cubes from A whose images are not
	// fully contained in B
	cubes bad;

	// prepare a set of cubes from F(A) which are not in Y
	cubes outside;

	// go through all the cubes in A
	for (int_t i = 0; i < A. size (); i ++)
	{
		// if the image of this cube is not defined...
		if (!F. getdomain (). check (A [i]))
			continue;

		// check that the image of this cube
		// is disjoint with Y\B
		const cubes &cset = F (A [i]);
		for (int_t j = 0; j < cset. size (); j ++)
			if (Y. check (cset [j]))
				bad. add (cset [j]);
			else if (!B. check (cset [j]))
				outside. add (cset [j]);
	}

	if (bad. empty () && outside. empty ())
	{
		sout << "Passed.\n";
		return;
	}
	sout << "Failed.\n";

	if (!bad. empty ())
	{
		sout << "--- Error: " << bad. size () <<
			" cubes from F(A) are in Y\\B. ---\n";
		if (savethem)
			(*savethem) << "; Cubes from F(A) that are "
				"in Y\\B:\n" << bad << '\n';
		errcount ++;
		badbits |= errFAinY;
	}

	if (!outside. empty ())
	{
		sout << "--- Warning: " <<
			outside. size () << " cubes from F(A) "
			"are outside Y. ---\n";
		if (savethem)
			(*savethem) << "; Cubes from F(A) that are "
				"not in Y:\n" << outside << '\n';
		warncount ++;
		badbits |= errFAoutY;
	}
	return;
} /* checkimageA */

void checkacyclic (const cubicalmap &F, const cubes &X, const cubes &A,
	const char *Xname, int errbit, int &errcount, int &/*warncount*/,
	int &badbits, std::ostream *savethem)
{
	const int maxsize = 1000;
	int_t sizes [maxsize];
	int_t maxfoundsize = 0;
	for (int i = 0; i < maxsize; i ++)
		sizes [i] = 0;

	// transform the set of cubes X+A into a set of cubical cells
	cubicalcomplex Xcompl;
	sout << "Creating a cell complex of " << Xname << "... ";
	for (int_t i = 0; i < X. size (); i ++)
		if (F. getdomain (). check (X [i]))
			Xcompl. add (qcell (X [i]));
	for (int_t i = 0; i < A. size (); i ++)
		if (F. getdomain (). check (A [i]))
			Xcompl. add (qcell (A [i]));
	Xcompl. addboundaries ();
	sout << Xcompl. size () << " cells.\n";

	// prepare variables for average size (now: the sum of sizes)
	// and for the number of cells processed (i.e., sizes added)
	double averagesize = 0;
	int_t countsizes = 0;

	// verify that the image of each cube is acyclic
	sout << "Verifying that images are acyclic... ";
	bool shown = false;
	cubicalcomplex bad;
	cubes empty;
	const cubes &Fdom = F. getdomain ();

	// first check cubes of maximal dimension
	for (int_t i = 0; i < (X. size () + A. size ()); i ++)
	{
		const cube &c = (i < X. size ()) ? X [i] :
			A [i - X. size ()];
		if (!Fdom. check (c))
			continue;
		cubes cset = F (c);
		int_t size = cset. size ();
		if (size > maxfoundsize)
			maxfoundsize = size;
		if (size < maxsize)
			sizes [static_cast<int> (size)] ++;
		else
		{
			averagesize += size;
			countsizes ++;
		}
		cubreducequiet (cset, empty, empty);
		if (cset. size () != 1)
		{
			if (!shown)
			{
				scon << ":( ";
				shown = true;
			}
			bad. add (qcell (c));
		}
	}

	// then check cubical cells of other dimensions
	coordinate leftb [qcell::MaxDim], rightb [qcell::MaxDim];
	int spacedim = X [0]. dim ();
	shown = false;
	for (int d = 0; d < Xcompl. dim (); d ++)
	{
		sout << std::setw (2) << d << ' ';
		const hashedset<qcell> &cellset = Xcompl [d];
		for (int_t i = 0; i < cellset. size (); i ++)
		{
			coordinate left [qcell::MaxDim];
			cellset [i]. leftcoord (left);
			coordinate right [qcell::MaxDim];
			cellset [i]. rightcoord (right);
			for (int j = 0; j < spacedim; j ++)
			{
				leftb [j] = (coordinate) (left [j] -
					(left [j] == right [j]));
				rightb [j] = (coordinate) (right [j]
					+ (left [j] == right [j]));
			}
			cubes cset;
			rectangle r (leftb, rightb, spacedim);
			const coordinate *c;
			int_t countimages = 0;
			while ((c = r. get ()) != NULL)
			{
				if (!PointBase::check (c, spacedim))
					continue;
				cube q (c, spacedim);
				if (Fdom. check (q) &&
					(X. check (q) || A. check (q)))
				{
					cset. add (F (q));
					countimages ++;
				}
			}

			int_t size = cset. size ();
			if (size > maxfoundsize)
				maxfoundsize = size;
			if (size < maxsize)
				sizes [static_cast<int> (size)] ++;
			else
			{
				averagesize += size;
				countsizes ++;
			}

			if (countimages != 1)
				cubreducequiet (cset, empty, empty);
			if ((countimages != 1) && (cset. size () != 1))
			{
				if (!shown)
				{
					sout << ":( " << std::setw (2) <<
						d << ' ';
					shown = true;
				}
				bad. add (cellset [i]);
			}
			if (!(i % 373))
				scon << std::setw (10) <<
					(cellset. size () - i) <<
					"\b\b\b\b\b\b\b\b\b\b";
		}
		scon << "\b\b\b";
	}

	if (!bad. empty ())
	{
		sout << "Failed.       \n--- Error: " <<
			bad. size () << " images of cells from " << Xname <<
			" are not acyclic. ---\n";
		if (savethem)
			(*savethem) << "; The images of the following cells "
				"from " << Xname << " are not acyclic:\n" <<
				bad << '\n';
		errcount ++;
		badbits |= errbit;
	}
	else
		sout << "Passed.       \n";

	// compute image size statistics and display it
	int minfoundsize = -1;
	for (int i = 0; (i < maxsize) && (i <= maxfoundsize); i ++)
	{
		if (!sizes [i])
			continue;
		if (minfoundsize < 0)
			minfoundsize = i;
		averagesize += (double) i * (double) (sizes [i]);
		countsizes += sizes [i];
	}
	if (countsizes)
		averagesize /= countsizes;
	sout << "(" << countsizes << " images of size " <<
		minfoundsize << " to " << maxfoundsize <<
		", average " << averagesize <<
		", were processed.)\n";
	return;
} /* checkacyclic */


// --------------------------------------------------
// ------------ CHKMVMAP main procedure -------------
// --------------------------------------------------

int chkmvmap (char *Fname, char *Xname, char *Aname, char *Yname,
	char *Bname, bool indexmap, char *savename, int acycliccheck)
{
	cubicalmap F;
	cubes X, A, Y, B;

	// read the files from the disk
	readfiles (Fname, Xname, Aname, (acycliccheck == 1) ? NULL : Yname,
		(acycliccheck == 1) ? NULL : Bname, F, X, A, Y, B);

	// if no map has been read, finish here
	if (F. getdomain (). empty ())
	{
		sout << "No map could be read from the file '" <<
			Fname << "'.\n"
			"Make sure the text data format is correct.\n";
		return 0;
	}

	// if no explicit domain is given, compute it
	if (!Xname)
	{
		sout << "Extracting the domain of F... ";
		X = F. getdomain ();
		sout << X. size () << " cubes.\n";
	}

	// make the sets X and A disjoint
	if (!A. empty ())
	{
		sout << "Computing X\\A... ";
		X. remove (A);
		sout << X. size () << " cubes left in X.\n";
	}

	// if there is nothing to verify, finish here
	if (X. empty ())
	{
		sout << "The set X\\A is empty. The map is trivial.\n";
		return 0;
	}

	// if the index map is being analyzed, adjust Y and B if necessary
	if (indexmap && (acycliccheck != 1))
	{
		if (Y. empty ())
			Y = X;
		if (B. empty ())
			B = A;
	}

	// if no explicit codomain is given, compute it if necessary
	if (Y. empty () && (acycliccheck != 1))
	{
		sout << "Extracting the range of F... ";
		for (int_t i = 0; i < X. size (); i ++)
			Y. add (F (X [i]));
		sout << Y. size () << " cubes.\n";
	}

	// make the sets Y and B disjoint
	if (!B. empty () && (acycliccheck != 1))
	{
		sout << "Computing Y\\B... ";
		Y. remove (B);
		sout << Y. size () << " cubes left in Y.\n";
	}

	// count warnings and errors
	int warncount = 0, errcount = 0;

	// indicate errors and warning by setting appropriate bits
	int badbits = 0;

	// prepare a file to save bad cubes to
	std::ofstream *savethem = NULL;
	if (savename)
	{
		savethem = new std::ofstream (savename);
		if (!savethem || !(*savethem))
			fileerror (savename, "create");
	}

	if (acycliccheck == 1)
		goto acyclicity_verification;

	// check if this is an index map
	if (indexmap)
	{
		checkinclXYB (X, Y, B, errcount, warncount, badbits,
			savethem);
		checkinclAB (A, Y, B, errcount, warncount, badbits,
			savethem);
	}

	// check that the domain of F contains X\A
	checkdomain (F, X, "X\\A", errFdefX, errcount, warncount,
		badbits, savethem);

	// check that the domain of F contains A
	checkdomain (F, A, "A", errFdefA, errcount, warncount,
		badbits, savethem);

	// verify that the image of each cube is contained in Y
	checkimageX (F, X, Y, B, errcount, warncount, badbits, savethem);

	// verify that A is mapped into B
	if (Aname)
		checkimageA (F, A, Y, B,
			errcount, warncount, badbits, savethem);

acyclicity_verification:

	// allocate bitfields and display an appropriate message
	knownbits [X [0]. dim ()];

	// verify that the image of each cubical cell is acyclic
	if (acycliccheck)
	{
		// warn the user that the following computations are long
		sout << "<The following computations may take "
			"a lot of time. Press Ctrl-C to interrupt.>\n";
		checkacyclic (F, X, A, "X", errFacyclX,
			errcount, warncount, badbits, savethem);
	}
	if (acycliccheck && !A. empty ())
	{
		cubes empty;
		checkacyclic (F, A, empty, "A", errFacyclA,
			errcount, warncount, badbits, savethem);
	}

	// close the file with bad cubes/cells
	if (savethem)
		delete savethem;

	// inform the user about the results of the verifications
	if (acycliccheck == 1)
	{
		if (badbits & (errFacyclA || errFacyclX))
			sout << "\nNO! The map is NOT acyclic.\n\n";
		else
			sout << "\nYES! The map is acyclic.\n\n";
		return 0;
	}

	// show a summary
	sout << errcount << " errors, " << warncount << " warnings.\n";

	if (!errcount)
		if (acycliccheck)
			if (!warncount)
				sout << "\nYES! The homomorphism induced "
					"in homology by this map "
					"can be computed reliably.\n\n";
			else
				sout << "\nWell... The homomorphism induced "
					"in homology by this map "
					"can be computed,\n"
					"but you must be very cautious, "
					"because some assumptions "
					"are not satisfied.\n\n";
		else
			sout << "\nYES! The homomorphism induced "
				"in homology by this map can be computed,\n"
				"provided the map is acyclic.\n\n";
	else
		sout << "\nNO! This is NOT a valid map "
			"for homology computation by 'homcubes'.\n\n";

	return 0;
} /* chkmvmap */


// --------------------------------------------------
// ---------------------- MAIN ----------------------
// --------------------------------------------------

int main (int argc, char *argv [])
// Return: 0 = Ok, -1 = Error, 1 = Help displayed, 2 = Wrong arguments.
{
	// prepare user-configurable data
	char *Fname /*= NULL*/, *Xname = NULL, *Aname = NULL,
		*Yname = NULL, *Bname = NULL;
	char *names [5];
	int namecount = 0;
	bool indexmap = false;
	char *savename = NULL;
	int acycliccheck = -1; // -1 = yes, 0 = no, 1 = only
	coordinate wrap [Cube::MaxDim];
	int wrapcount = 0;

	// analyze the command line
	arguments a;
	arg (a, NULL, names, namecount, 5);
	arg (a, "s", savename, "chkmvmap.cub");
	arg (a, "a", acycliccheck, -1);
	arg (a, "w", wrap, wrapcount, Cube::MaxDim);
	argswitch (a, "i", indexmap, true);
	arghelp (a);

	argstreamprepare (a);
	int argresult = a. analyze (argc, argv);
	argstreamset ();

	// show the program's main title
	if (argresult >= 0)
		sout << title << '\n';

	// set the space wrapping if necessary
	if (wrapcount == 1)
		PointBase::setwrapping (wrap [0]);
	else if (wrapcount)
		PointBase::setwrapping (wrap);

	// assign the names as necessary
	Fname = names [0];
	switch (namecount)
	{
		case 5:
			Xname = names [1];
			Aname = names [2];
			Yname = names [3];
			Bname = names [4];
			break;
		case 4:
			Aname = names [1];
			Yname = names [2];
			Bname = names [3];
			break;
		case 3:
			Xname = names [1];
			if (indexmap)
				Aname = names [2];
			else
				Yname = names [2];
			break;
		case 2:
			if (indexmap)
				Aname = names [1];
			else
				Yname = names [1];
			break;
	}

	// if something was incorrect, show an additional message and exit
	if (argresult < 0)
	{
		sout << "Call with '--help' for help.\n";
		return 2;
	}

	// if help requested or no filenames present, show help information
	if (!namecount || (argresult > 0))
	{
		sout << helpinfo << '\n';
		return 1;
	}

	// try running the main function and catch an error message if thrown
	try
	{
		chkmvmap (Fname, Xname, Aname, Yname, Bname, indexmap,
			savename, acycliccheck);
		program_time = 1;
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

/// @}

