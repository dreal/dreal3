/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file cells.h
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started in April 1999. Last revision: November 19, 2002.

// WARNING: THIS FILE IS DEPRECATED!
// Please, use the data types defined in CUBISETS.H instead.


#ifndef _CAPD_HOMOLOGY_CELLS_H_ 
#define _CAPD_HOMOLOGY_CELLS_H_ 

#include "capd/homology/config.h"
#include "capd/homology/textfile.h"

#include <iostream>
#include <fstream>
#include <cstdlib>

using namespace capd::homology;


// classes defined within this header file
class point;
class cell;
class cellelement;
class cellcomplex;


// --------------------------------------------------
// --------------------- POINT ----------------------
// --------------------------------------------------

typedef short coordinate;

class point
// a point in the space R^n
{
public:
	// constructor for reading a point from a text file
	point (textfile &in, int removebrackets = 0);

	// constructor for creating a translated point;
	// use axis = -1 and diff != 0 to change all the coordinates
	point (point &p, int axis = -1, int diff = 0);

	// constructor for a point by its coordinates
	point (coordinate *c);

	// destructor for a point
	~point ();

	// set or get the dimension of the space
	static int spacedimension (int dim = 0);

	// define space wrapping
	static void wrap_space (int axis, int n);

	// get the table of coordinates of the point
	coordinate *coordinates ();

	// write the point to an output stream
	friend std::ostream &operator << (std::ostream &out, const point &p);

	// wrapp given coordinate if needed
	void wrap (coordinate &c, int axis);

protected:
	// coordinates of the point
	coordinate *coord;

	// the dimension of the space
	static int spacedim;

	// number of existing points
	static int numberofpoints;

	// space wrapping - the coordinates of points
	// are taken modulo this number if it is different from 0
	static coordinate *space_wrapping;

}; /* class point */

// --------------------------------------------------

// Check wheather two points are equal:
int operator == (point &p1, point &p2);

// Make the coordinates of the first point less than of the second one:
void sortcoordinates (point &left, point &right);


// --------------------------------------------------
// ---------------------- CELL ----------------------
// --------------------------------------------------

class cell
// a rectangular cell in R^n, defined by its two corners
{
public:
	// constructor for reading a cell from a file
	cell (textfile &in);

	// constructor for creating a boundary cell
	cell (cell *c, int axis = -1, int sign = 0);

	// constructor of a full-dimensional cell
	cell (point &p);

	// constructor of a cell with given vertices
	cell (point &p1, point &p2);

	// destructor of a cell
	~cell ();

	// compute cell's dimension
	int dimension ();

	// check if the cell is not 'thin' in this dimension
	int thick (int axis);

	// get left and right point coordinates
	coordinate *leftcoord ();
	coordinate *rightcoord ();

	friend int operator == (cell &c1, cell &c2);
	friend std::ostream &operator << (std::ostream &out, const cell &c);

	// two hashing keys (the latter is non-zero)
	unsigned hashkey (unsigned hashsize);
	unsigned hashadd (unsigned hashsize);

protected:
	// total number of existing cells
	static int numberofcells;

	// numbers of cells of each dimension
	static int *cellcounter;

	// the left lower corner of the cell and the right upper one
	point left, right;

}; /* class cell */

int operator == (cell &c1, cell &c2);


// --------------------------------------------------
// ------------------ CELL ELEMENT ------------------
// --------------------------------------------------

#ifndef MAXDIM
#define MAXDIM 50
#endif

typedef signed char coefficient;

class cellelement
// an element of a list of cells of one dimension
{
	friend class cellcomplex;

public:
	// constructor for a cell element with its number
	// and cell given as a parameter
	cellelement (int _number, cell *_c);

	// destructor for a cell element;
	// it removes the rest of the list, too
	~cellelement ();

	// get the address where the address of the next cell
	// is stored
	class cellelement **nextcelladdress ();

	// get the address of the next cell
	class cellelement *nextcell ();

	// add one element to the map value on this cell
	int addtomap (coefficient coeff, int cellnumber);

	// create the boundary of the cell
	int createboundary (class cellcomplex lowerdim);

protected:
	// number of the cell
	int number;

	// cell coordinates
	cell *c;

	// formula for cell's boundary
	int *boundary;

	// length of the map value
	int maplength;

	// coefficients in the map value
	coefficient *mapcoeff;

	// cell numbers in the map value
	int *mapcell;

	// pointer to the next cell element in the list
	class cellelement *next;

}; /* class cell element */


// --------------------------------------------------
// ------------------ CELL COMPLEX ------------------
// --------------------------------------------------

class cellcomplex
{
public:
	// constructor for creating an empty cell complex
	cellcomplex ();

	// destructor of a cell complex
	~cellcomplex ();

	// add a cell; if it is a new cell for sure,
	// set 'newcell' to 1;
	// return cell's number no matter whether added or not
	cellelement *addcell (cell *c, int newcell = 0);

	// find a cell and return address of an element
	// which contains it
	cellelement *findcell (cell *c, int dim = -1);

	// create cells which will be needed in the boundaries;
	// return the number of cells added
	int makeboundaries (int dim);
	int makeallboundaries ();

	// create new numbers of cells without these in 'ignore'
	int makenewnumbers (cellcomplex &ignore);

	// read from a file and write to a file
	int read (textfile &in);
	int read (char *filename);
	int write (std::ostream &out);
	int write (char *filename);
	int readwithmap (textfile &in, cellcomplex &c);
	int readwithmap (char *filename, cellcomplex &c);
	int writemap (std::ostream &out, cellcomplex *other = NULL);
	int writemap (char *filename, cellcomplex *other = NULL);

	// write a projection map
	int writeprojectionmap (std::ostream &out, cellcomplex &c,
		int ydim);
	int writeprojectionmap (char *filename, cellcomplex &c,
		int ydim);

protected:
	// numbers of cells in each dimension
	int numbers [MAXDIM];

	// addresses of list beginnings for each dimension
	cellelement *cells [MAXDIM];

	// addresses of a place in the last list element
	// where an address of a new list element should be written
	cellelement **next [MAXDIM];

	// new numbers after removing cells from the 2nd pair
	// required for computation of relative homology
	int *newnumbers [MAXDIM];

	// new numbers of cells of each dimension
	int newmaxnumbers [MAXDIM];

	// hashing table size, number of used entries
	// and the table itself
	unsigned hashsize;
	unsigned hashused;
	cellelement **hashtable;

	// find an appropriate position in the table
	// or return -1 if no table in use
	int hashfind (cell *c);

	// increase the hashing table
	void inchashtable (void);

	// add an entry to the table;
	// note: before calling this function, numbers []
	// and an appropriate list should be already updated
	void hashtableadd (int pos, cellelement *c);

}; /* class cellcomplex */

#endif // _CAPD_HOMOLOGY_CELLS_H_ 

/// @}

