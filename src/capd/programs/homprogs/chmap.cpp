/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file chmap.cpp
///
/// @author Jacek Szybowski and Marcin Mazur
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1998-2003 by Jacek Szybowski and Marcin Mazur.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started in 1998. Last revision: February 17, 2003.


#include "capd/homology/config.h"	// added by PwP on Nov 11, 2003
#include "capd/homology/timeused.h"	// added by PwP on Sep 12, 2003

#include <new>
#include <exception>
#include <iostream>
#include <fstream>
#include <sstream>	// modified by PwP on Nov 11, 2003
#include <cstdlib>	// for atoi function
#include <math.h>	// for fmod function
#include <cstring>	// for strcat function // fatalerror

using namespace capd::homology;
using namespace std;
//#include <curses.h>
//#include <cursesBSD.h>
//#include <conio.h>	// for gotoxy, wherex and wherey functions
//#include <dos.h>	// for delay function

//#include "chmap.h"	// removed by PwP on Feb 17, 2003

//WINDOW *scr;

const char *title = "\
CHAINMAP. Copyright (C) 1998-2003 by Marcin Mazur and Jacek Szybowski.\n\
This is free software. No warranty. Consult 'license.txt' for details.";

const char *helpinfo = "\
This program creates chain maps (over Zp) from (almost) perfect\n\
multivalued representable maps F: 2^(R^n) -> 2^(R^n).\n\
Call this program with input and output file names and (optionally)\n\
rank of the ring (without this argument calculations are made over Z)\n\
or call it with -h for help info.\n\
Input data format: chmap [-a | -g] map.dat chmap.dat chCY.dat [integer].\n\
Use '-a' for the algebraical algorithm and -g for the geometrical one.\n\
The multivalued representable map is read from the file 'map.dat'\n\
the result of calculations is written to the file 'chmap.dat'.\n\
The primitive generators of the chain complex CY are written to 'chCY.dat'.\n\
e.g.: chmap map.dat chmap.dat chCY.dat makes the same but over Z\n\
e.g.: chmap -h showes help info.\n\
For more information see documentation or ask the authors:\n\
mazur@im.uj.edu.pl\n\
szybowsk@uci.agh.edu.pl";


// **************************************************
// **************************************************
// ********** The contents of the original **********
// ********** file "chmap.h" follows.      **********
// ********** This file was included here  **********
// ********** by PwP on February 16, 2003, **********
// ********** because this is not really   **********
// ********** a header file.               **********
// **************************************************
// **************************************************


// This file was written by Jacek Szybowski and Marcin Mazur.
// This is a version dated August 26, 1999.
// Adjusted by PwP for various compilers: Dec 3, 2001 - Sep 10, 2003.

int max (int, int);     // return maximum of two integers
int min (int, int);     // return minimum of two integers
int twoto (int);        // calculate the power of 2



//classes

class Zp;
class point;
class reprconvexset;
class cell;
class ppair;
class fixdimpairs;
class multivalmap;
class numberlistelement;
class numberlist;
class fixdimcells;
class domain;
class chainelement;
class chain;
class chainmappair;
class fixdimchainmappairs;
class chainmap;
class vector;
class matrix;
class celllistelement;
class celllist;
class txtfile;

cell decodenumber (int, const reprconvexset &);

//extern WINDOW *scr = initscr ();

#define argument        cell
#define value           reprconvexset

// -------------------------------------------------------------
// --------------------------- Zp ------------------------------
// -------------------------------------------------------------

class Zp
{
public:

	// default constructor
	Zp ();

	// another constructor
	Zp (int q);

	// default destructor
	~Zp ();

	// operator '=' to assign a Zp number
	Zp &operator = (const Zp &q);

	// operator '+' to add a Zp number
	Zp operator + (const Zp &q);

	// operator '-' to subtract a Zp number
	Zp operator - (const Zp &q);

	// operator '*' to multiply by a Zp number
	Zp operator * (const Zp &q);

	// operator '/' to divide by a Zp number
	Zp operator / (const Zp &q);

	// operator '-' to make the opposite number in Zp
	Zp operator - ();

	// operator '==' for comparison
	//int operator == (const Zp &q) const;

	// set the rank of Zp
	static void setrank (int r);

	// calculate k mod m
	int modulo (int k, int m);

	// convert the Z_p number to integer
	operator int () const;

protected:

	// rank of Zp
	static int p;

	// number (mod p)
	signed char n;
};

// --------------------------------------------------

inline Zp::Zp ()
{
}

inline Zp::Zp (int q)
{
	if (!p) n = (char) q;      // if p = 0: Zp = Z
	else n = (char) modulo (q , p);
}

inline Zp::~Zp ()
{
}

inline Zp &Zp::operator = (const Zp &q)
{
	n = q.n;
	return *this;
}

inline void Zp::setrank (int r)
{
	p = r;
}

inline Zp::operator int () const
{
	return n;
}

/*
inline int Zp::operator == (const Zp &q) const
{
	return (n == q. n);
}
*/


// -------------------------------------------------------------
// ------------------------- POINT  ----------------------------
// -------------------------------------------------------------

class point
{
public:

	// default constructor
	point ();

	// default destructor
	~point ();

	// copying constructor
	point (const point &p);

	// operator '=' to assign a point
	point &operator = (const point &p);

	// operator '==' to compare two points
	int operator == (const point &p) const;

	// operator '[]' to return j-th coordinate of the point
	int &operator [] (int j) const;

	// set the dimension of the space
	static void spacedimension (int n);

	// return the dimension of the space
	int spdim () const;

	// read the point from the stream
	int read (txtfile &f);

	// write the point to the stream
	int write (ofstream &out);

protected:

	// dimension of the space (should be equal to at least one)
	static int spacedim;

	// coordinates of the point
	int *coordinates;
};

// --------------------------------------------------

inline point::point ()
{
	coordinates = new int [spacedim];

	if (!coordinates)
		throw "Can't allocate memory to create a new point.";
}

inline point::~point ()
{
	if (!coordinates)
		throw "Trying to delete already deleted point";

		delete [] coordinates;

		coordinates = NULL;
}

inline point::point (const point &p)
{
	coordinates = new int [spacedim];

	if (!coordinates)
		throw "Can't allocate memory to copy a point.";

	memcpy (coordinates, p.coordinates, spacedim * sizeof (int));
}

inline int point::operator == (const point &p) const
{
	if (!memcmp (coordinates, p.coordinates, spacedim * sizeof (int)))
		return 1;
	return 0;
}

// operator '[]' to return j-th coordinate of the point
inline int &point::operator [] (int j) const
{
	return (coordinates [j]);
}

inline void point::spacedimension (int n)
{
	spacedim = n;
}

// return the dimension of the space
inline int point::spdim () const
{
	return (spacedim);
}



// -------------------------------------------------------------
// ---------------- REPRESENTABLE CONVEX SET  ------------------
// -------------------------------------------------------------

class reprconvexset
{
	friend class chainmap;
	friend class chain;
	friend class vector;
	friend class cell;
	friend class celllist;
	friend class domain;
	friend class numberlist;

public:

	// default constructor
	reprconvexset ();

	// default destructor
	~reprconvexset ();

	// copying constructor
	reprconvexset (const reprconvexset &rcs);

	// operator '=' to assign a represantable convex set
	reprconvexset &operator = (const reprconvexset &z);

	// operator '==' to compare two representable convex sets
	int operator == (const reprconvexset &z) const;

	// set product operator
	// return error when the result is an empty set
	reprconvexset &operator *= (const reprconvexset &z);

	// count the dimension of the set
	int dim () const;

	// count the first dimension of the set in which the edge is longer than 1
	// if there are no such edges - return (-1)
	int firstlarge () const;

	// find first nontrivial dimension in R (if all are trivial: return -1)
	int firstnottrivial ();

	// write the set to the stream
	int write (ofstream &out);

	friend cell decodenumber (int, const reprconvexset &);
	friend multivalmap *readfromfile (ifstream &, ofstream &);

protected:

	point ll; //left, lower, ... vertex of a convex set
	point ru; //right, upper, ... vertex of a convex set
};

// --------------------------------------------------

inline reprconvexset::reprconvexset (): ll(), ru()
{
}

inline reprconvexset::~reprconvexset ()
{
}

inline reprconvexset::reprconvexset (const reprconvexset &rcs): ll(rcs.ll), ru(rcs.ru)
{
}

inline reprconvexset &reprconvexset::operator = (const reprconvexset &z)
{
	ll = z.ll;
	ru = z.ru;
	return *this;
}

inline int reprconvexset::operator == (const reprconvexset &z) const
{
	if ((ll == z.ll) && (ru == z.ru))
		return 1;
	return 0;
}

// write the set to the stream
inline int reprconvexset::write (ofstream &out)
{
	out << "[";
	ll.write (out);
	out << " ";
	ru.write (out);
	out << "]";

	return 1;
}



// -------------------------------------------------------------
// ------------------------- CELL  -----------------------------
// -------------------------------------------------------------

class cell : public reprconvexset
{
	friend class celllist;

public:

	// default constructor
	cell ();

	// default destructor
	~cell ();

	// copying constructor
	// if crd < 0 put s in place of -crd coordinate of ll
	// if crd > 0 put s in place of  crd coordinate of ru
	cell (const cell &c , int s = 0 , int crd = 0);

	// operator '=' to assign a cell
	cell &operator = (const cell &z);

	// operator '<=' to check if the cell is a face of another cell
	int operator <= (const cell &z) const;

	// operator '<=' to check if the cell is a face of representable convex set
	int operator <= (const reprconvexset &z) const;

	// operator '==' to compare two cells
	int operator == (const cell &z) const;

	// find the k-th projection of the cell (k-th coordinate = m)
	cell pi (int k, int m);

	// find the intersection of images of primitive cells
	// from domain of multivalued map
	// for which the given cell is a face
	reprconvexset A (const multivalmap &f);

	// boundary operator
	chain bd();

	// write the cell to the stream
	int write (ofstream &out);

};

// --------------------------------------------------

inline cell::cell (): reprconvexset()
{
}

inline cell::~cell ()
{
}

inline cell::cell (const cell &c , int s , int crd): reprconvexset(c)
{
	if (crd)
	{
		if (crd < 0)
			ll [- crd -1] = s;
		else
			ru [crd -1] = s;
	}
}

inline cell &cell::operator = (const cell &z)
{
	ll = z.ll;
	ru = z.ru;
	return *this;
}

inline int cell::operator == (const cell &z) const
{
	if ((ll == z.ll) && (ru == z.ru))
		return 1;
	return 0;
}

// write the cell to the stream
inline int cell::write (ofstream &out)
{
	out << "[";
	ll.write (out);
	out << " ";
	ru.write (out);
	out << "]";

	return 1;
}



// -------------------------------------------------------------
// ------------------- NUMBERLISTELEMENT -----------------------
// -------------------------------------------------------------

class numberlistelement
{
	friend class numberlist;

public:

	// default constructor
	numberlistelement (int num);

	// default destructor
	~numberlistelement ();

	// set the number
	void setnumber (int num);

protected:

	// number - appropriate coordinate of point
	int number;

	// pointer to next element on list
	numberlistelement *next;

	// pointer to next list
	numberlistelement *nextlist;
};

// --------------------------------------------------

inline numberlistelement::numberlistelement (int num)
 {
	number = num;
	next = NULL;
	nextlist = NULL;
}

inline numberlistelement::~numberlistelement ()
{
	if (next)
	{
		delete next;
		next = NULL;
	}

	if (nextlist)
	{
		delete nextlist;
		nextlist = NULL;
	}
}

inline void numberlistelement::setnumber (int num)
{
	number = num;
}



// -------------------------------------------------------------
// ----------------------- NUMBERLIST --------------------------
// -------------------------------------------------------------

class numberlist
{
public:

	// default constructor
	numberlist ();

	// default destructor
	~numberlist ();

	// insert a cell to the list
	int insert (cell c);

protected:

	// pointer to first element of list of second coordinates
	numberlistelement *head;
};

// --------------------------------------------------

inline numberlist::numberlist ()
{
	head = NULL;
}

inline numberlist::~numberlist ()
{
	if (head)
	{
		delete head;
		head = NULL;
	}
}



// -------------------------------------------------------------
// ---------------------- FIXDIMCELLS --------------------------
// -------------------------------------------------------------

class fixdimcells
{
	friend class domain;

public:

	// default constructor
	fixdimcells ();

	// another constructor
	fixdimcells (int l);

	// default destructor
	~fixdimcells ();

	// operator '=' to assign fixdimcells
	fixdimcells &operator = (const fixdimcells &f);

	// operator '[]' to return j-th cell
	argument &operator [] (int j);

	// return the length of the list
	int l ();

	// if not in list - add new argument to the end of it
	void addarg (argument &a);

protected:

	// length of the list
	int length;

	// actual pointer
	int pointer;

	// list of arguments
	argument *fdc;

	// hashing table of left vertices' first coordinates
	numberlist *hash;
};

// --------------------------------------------------

inline fixdimcells::fixdimcells ()
{
	pointer = 0;
	length = 0;
	fdc = NULL;
	hash = NULL;
}

inline fixdimcells::fixdimcells (int l)
{
	pointer = 0;
	length = l;
	fdc = new argument [l];
	hash = NULL;

	if (!fdc)
		throw "Can't allocate memory to create a list of arguments.";
}

inline fixdimcells::~fixdimcells ()
{
	if (!fdc)
		throw "Trying to delete already deleted list of arguments.";

	delete [] fdc;

	fdc = NULL;

	if (hash)
	{
		delete [] hash;
		hash = NULL;
	}
}

// operator '[]' to return j-th cell
inline argument &fixdimcells::operator [] (int j)
{
	return (fdc [j]);
}

// return the length of the list
inline int fixdimcells::l ()
{
	return (length);
}



// -------------------------------------------------------------
// -------------------------- DOMAIN ---------------------------
// -------------------------------------------------------------

class domain
{
public:

	// default constructor
	domain (int maxdim);

	// copying constructor
	domain (domain &dom, int maxdim);

	// default destructor
	~domain ();

	// operator '[]' to return j-th list of cells
	fixdimcells &operator [] (int j);

	// calculate the convex envelope of the domain
	void envelope (int maxdim);

	// completion of the domain
	void completion (int maxdim);

protected:

	// convex envelope of domain
	reprconvexset convenv;

	// table of fixed dimension lists of domain cells
	fixdimcells *D;
};

// --------------------------------------------------

inline domain::domain (int maxdim):convenv ()
{
	if (maxdim + 1)
	{
		D = new fixdimcells [maxdim + 1];
		if (!D)
			throw "Can't allocate memory to create a new domain.";
	}
	else
		D = NULL;
}

inline domain::~domain ()
{
	if (!D)
		throw "Trying to delete already deleted domain.";

	delete [] D;

	D = NULL;
}

// operator '[]' to return j-th list of cells
inline fixdimcells &domain::operator [] (int j)
{
	return (D [j]);
}



// -------------------------------------------------------------
// -------------------------- PAIR -----------------------------
// -------------------------------------------------------------
// Note: The name of this class changed by PwP from "pair" to "ppair"
// on January 17, 2002 because of some problems with the PGI compiler.

class ppair
{
public:

	// default constructor
	ppair ();

	// default destructor
	~ppair ();

	// copying constructor
	ppair (ppair &p);

	// operator '==' to compare two pairs
	int operator == (ppair &p);

	// operator '=' to assign a ppair
	ppair &operator = (const ppair &p);

	friend reprconvexset cell::A (const multivalmap &f);
	friend multivalmap *readfromfile (ifstream &, ofstream &);

protected:

	// argument (primitive cell)
	argument x;

	// value (representable convex set)
	value y;
};

// --------------------------------------------------

inline ppair::ppair (): x(), y()
{
}

inline ppair::~ppair ()
{
}

inline ppair::ppair (ppair &p): x(p.x), y(p.y)
{
}

inline int ppair::operator == (ppair &p)
{
	if ((x == p.x) && (y == p.y))
		return 1;
	return 0;
}

inline ppair &ppair::operator = (const ppair &p)
{
	x = p.x;
	y = p.y;
	return *this;
}



// -------------------------------------------------------------
// ---------------------- FIXDIMPAIRS --------------------------
// -------------------------------------------------------------

class fixdimpairs
{
public:

	// default constructor
	fixdimpairs ();

	// another constructor
	fixdimpairs (int l);

	// default destructor
	~fixdimpairs ();

	// operator '=' to assign fixdimpairs
	fixdimpairs &operator = (const fixdimpairs &f);

	// operator '[]' to return j-th ppair
	ppair &operator [] (int j);

	// return the length of the list
	int l ();

	// if not in list - add new ppair to the end of it
	void addpair (ppair &p);

protected:

	// length of the list
	int length;

	// actual pointer
	int pointer;

	// list of pairs
	ppair *fdp;
};

// --------------------------------------------------

inline fixdimpairs::fixdimpairs ()
{
	pointer = 0;
	length = 0;
	fdp = NULL;
}

inline fixdimpairs::fixdimpairs (int l)
{
	pointer = 0;
	length = l;
	fdp = new ppair [l];
	if (!fdp)
		throw "Can't allocate memory to create a list of pairs.";
}

inline fixdimpairs::~fixdimpairs ()
{
	if (fdp)
	{
		delete [] fdp;
		fdp = NULL;
	}
}

// operator '[]' to return j-th ppair
inline ppair &fixdimpairs::operator [] (int j)
{
	return (fdp [j]);
}

// return the length of the list
inline int fixdimpairs::l ()
{
	return (length);
}



// -------------------------------------------------------------
// ------------------------ MULTIVALMAP ------------------------
// -------------------------------------------------------------

class multivalmap
{
public:

	// default constructor
	multivalmap ();

	// default destructor
	~multivalmap ();

	// operator '[]' to return j-th list of pairs
	fixdimpairs &operator [] (int j) const;

	// set maximum dimension of domain cells
	static void setmaxdim (int _maxdim);

	// return maximum dimension of domain cells
	int dim () const;

	// return j-th list of pairs
	fixdimpairs &Fn (int j);

	// return j-th list of domain elements
	fixdimcells &domn (int j);

	// completion of the domain
	void completedomain (int dim);

	// write chain complex CY to file
	void writeCYtofile (celllist &cll, ofstream &outCY);

protected:

	// maximal dimension of domain cells
	static int maxdim;

	// table of fixed dimension lists of pairs
	fixdimpairs *F;

	// domain of the map
	domain dom;
};

// --------------------------------------------------

inline multivalmap::multivalmap (): dom (maxdim)
{
	if (maxdim + 1)
	{
		F = new fixdimpairs [maxdim + 1];
		if (!F)
			throw "Can't allocate memory to create a new map.";
	}
	else
		F = NULL;
}

inline multivalmap::~multivalmap ()
{
	if (!F)
		throw "Trying to delete already deleted multivalued map.";

	delete [] F;

	F = NULL;
}

inline void multivalmap::setmaxdim (int _maxdim)
{
	maxdim = _maxdim;
}

// return maximum dimension of domain cells
inline int multivalmap::dim () const
{
	return (maxdim);
}

// operator '[]' to return j-th list of pairs
inline fixdimpairs &multivalmap::operator [] (int j) const
{
	return (F [j]);
}

// return j-th list of pairs
inline fixdimpairs &multivalmap::Fn (int j)
{
	return (F [j]);
}

// return j-th list of domain elements
inline fixdimcells &multivalmap::domn (int j)
{
	return (dom [j]);
}

// completion of the domain
inline void multivalmap::completedomain (int dim)
{
	dom.completion (dim);
}



// -------------------------------------------------------------
// ------------------------- VECTOR ----------------------------
// -------------------------------------------------------------

class vector
{
public:

	// default constructor
	vector ();

	// another constructor
	vector (int vdim);

	// another constructor
	vector (const chain &sigma, const reprconvexset &A);

	// copying constructor
	vector (const vector &vec);

	// default destructor
	~vector ();

	// operator '=' to assign a vector
	vector &operator = (const vector &v);

	// operator '[]' to return j-th coordinate of vector
	Zp &operator [] (int j);

	// return the dimension of vector
	int vdim ();

	// calculate number of a given cell in A ("-1" - error)
	int number (const cell &c, const reprconvexset &A);

	// return the chain coded by the vector
	chain decodevector (const reprconvexset &A);

	// set the dimension of the vector
	void setdim (int n);

	// set default dimension of the vector
	void setdefdim (const reprconvexset &A);

protected:

	// dimension of the vector
	int vectordim;

	// coordinates of the vector
	Zp *coordinates;
};

// --------------------------------------------------

inline vector::vector ()
{
	vectordim = 0;
	coordinates = NULL;
}

inline vector::vector (int vdim)
{
	vectordim = vdim;

	if (vectordim)
	{
		coordinates = new Zp [vectordim];
		if (!coordinates)
			throw "Can't allocate memory to create a new vector.";
	}
	else
		coordinates = NULL;
}

inline vector::~vector ()
{
	if (coordinates)
	{
		delete [] coordinates;

		coordinates = NULL;
	}
}

// operator '[]' to return j-th coordinate of vector
inline Zp &vector::operator [] (int j)
{
	return (coordinates [j]);
}

// return the dimension of vector
inline int vector::vdim ()
{
	return (vectordim);
}

inline void vector::setdim (int n)
{
	vectordim = n;
}



// -------------------------------------------------------------
// ---------------------- CHAINELEMENT -------------------------
// -------------------------------------------------------------

class chainelement
{
	friend class chainmap;
	friend class chain;
	friend class domain;

public:

	// default constructor
	chainelement (Zp k = 1);

	// constructor
	chainelement (Zp _k, const cell &_c);

	// default destructor
	~chainelement ();

	// copying constructor
	chainelement (const chainelement &ce);

	// operator '=' to assign a chain element
	chainelement &operator = (const chainelement &ce);

	// operator '==' to compare two chain elements
	int operator == (const chainelement &ce) const;

	friend vector::vector (const chain &, const reprconvexset &);

protected:

	// cell
	cell c;

	// coefficient
	Zp k;
};

// --------------------------------------------------

inline chainelement::~chainelement ()
{
}

inline chainelement::chainelement (const chainelement &ce): c(ce.c)
{
	k = ce.k;
}

inline chainelement &chainelement::operator = (const chainelement &ce)
{
	c = ce.c;
	k = ce.k;
	return *this;
}

inline int chainelement::operator == (const chainelement &ce) const
{
	if ((c == ce.c) && ((int) k == (int) ce.k))
		return 1;
	return 0;
}



// -------------------------------------------------------------
// -------------------------- CHAIN ----------------------------
// -------------------------------------------------------------

class chain
{
public:

	// default constructor
	chain ();

	// another constructor
	chain (int l);

	// default destructor
	~chain ();

	// copying constructor
	//chain (const chain &c);

	// copying constructor (if s: shorten new chain to the pointer length)
	chain (const chain &c, int s = 0);

	// add new chain element
	void addchainelement (const chainelement &ce);

	// count the dimension of the chain
	int dim () const;

	// find the convex envelope of the chain
	reprconvexset conv ();

	// find the k-th projection of the chain (k-th coordinate = m)
	chain pi (int k, int m);

	// find the temporary chain
	chain projection (int k, int m);

	// operator to compare two chains
	int operator == (const chain &c) const;

	// operator to assign a chain
	chain &operator = (const chain &c);

	// operator '+=' to add a chain element (with controll of the coefficients)
	chain &operator += (const chainelement &ce);

	// operator '+' to add a chain
	chain operator + (const chain &c) const;

	// operator '[]' to return j-th chain element
	chainelement &operator [] (int j) const;

	// find coboundary of a given zero dimensionel chain
	chain cob ();

	// find the coboundary of the chain (q = dimension of the input chain)
	chain cob (int q);


	// return the length of the chain
	int l () const;

	// write the chain to the stream
	int write (ofstream &out);

protected:

	// length of chain
	int length;

	// actual pointer
	int pointer;

	// list of chain elements
	chainelement *ch;
};

// --------------------------------------------------

inline chain::chain ()
{
	length = 0;
	pointer = 0;
	ch = NULL;
}

inline chain::chain (int l)
{
	length = l;

	pointer = 0;

	ch = new chainelement [length];

	if (!ch)
		throw "Can't allocate memory to create a chain.";
}

inline chain::~chain ()
{
	length = 0;
	pointer = 0;

	if (ch)
	{
		delete [] ch;
		ch = NULL;
	}
}

inline int chain::dim () const
{
	return (ch [0].c.dim ());
}

inline int chain::operator == (const chain &c) const
{
	if ((length == c.length) && (*ch == *c.ch))
		return 1;
	return 0;
}

// operator '[]' to return j-th chain element
inline chainelement &chain::operator [] (int j) const
{
	return (ch [j]);
}

// return the length of the chain
inline int chain::l () const
{
	return (length);
}



// -------------------------------------------------------------
// ---------------------- CHAINMAPPAIR -------------------------
// -------------------------------------------------------------

class chainmappair
{
	friend class chainmap;

public:

	// default constructor
	chainmappair ();

	// another constructor (l = length of value)
	chainmappair (int l);

	// default destructor
	~chainmappair ();

	// copying constructor
	chainmappair (chainmappair &cmp);

	// operator '==' to compare two chain map pairs
	int operator == (chainmappair &cmp);

	// operator '=' to assign a chain map ppair
	chainmappair &operator = (const chainmappair &cmp);

	friend int writetofile (ofstream &, chainmap &);

protected:

	// argument (cell)
	argument x;

	// value (chain)
	chain y;
};

// --------------------------------------------------

inline chainmappair::chainmappair (): x (), y ()
{
}

inline chainmappair::chainmappair (int l): x (), y (l)
{
}

inline chainmappair::~chainmappair ()
{
}

inline chainmappair::chainmappair (chainmappair &cmp): x(cmp.x), y(cmp.y)
{
}

inline chainmappair &chainmappair::operator = (const chainmappair &cmp)
{
	x = cmp.x;
	y = cmp.y;
	return *this;
}

inline int chainmappair::operator == (chainmappair &cmp)
{
	if ((x == cmp.x) && (y == cmp.y))
		return 1;
	return 0;
}



// -------------------------------------------------------------
// ------------------ FIXDIMCHAINMAPPAIRS ----------------------
// -------------------------------------------------------------

class fixdimchainmappairs
{
public:

	// default constructor
	fixdimchainmappairs ();

	// another constructor (l = length)
	fixdimchainmappairs (int l);

	// default destructor
	~fixdimchainmappairs ();

	// operator '=' to assign fixdimchainmappairs
	fixdimchainmappairs &operator = (const fixdimchainmappairs &fcm);

	// operator '[]' to return j-th chain map ppair
	chainmappair &operator [] (int j);

	// return the length of the list
	int l ();

	// add new chain map ppair to the end of list
	void addchainmappair (chainmappair &cmp);

protected:

	// length of the list
	int length;

	// actual pointer
	int pointer;

	// list of chain map pairs
	chainmappair *fdcmp;
};

// --------------------------------------------------

inline fixdimchainmappairs::fixdimchainmappairs ()
{
	length = 0;
	pointer = 0;
	fdcmp = NULL;
}

inline fixdimchainmappairs::fixdimchainmappairs (int l)
{
	length = l;

	pointer = 0;

	fdcmp = new chainmappair [length];

	if (!fdcmp)
		throw "Can't allocate memory to create a new list of chain map pairs.";
}

inline fixdimchainmappairs::~fixdimchainmappairs ()
{
	if (!fdcmp)
		throw "Trying to delete already deleted list of chain map pairs.";

	delete [] fdcmp;

	fdcmp = NULL;
}

// operator '[]' to return j-th chain map pair
inline chainmappair &fixdimchainmappairs::operator [] (int j)
{
	return (fdcmp [j]);
}

// return the length of the list
inline int fixdimchainmappairs::l ()
{
	return (length);
}



// -------------------------------------------------------------
// ------------------------- CHAINMAP --------------------------
// -------------------------------------------------------------

class chainmap
{
public:

	// default constructor - creates a chain map for a given multivalued map
	chainmap (multivalmap *mvm, int alg);

	// default destructor
	~chainmap ();

	// first continuation of default constructor
	void chainmapalg (multivalmap *mvm);

	// second continuation of default constructor
	void chainmapgeom (multivalmap *mvm);

	// operator '[]' to return j-th list of chain map pairs
	fixdimchainmappairs &operator [] (int j);

	// return the maximal dimension of domain cells
	int dim ();

	// calculate the value of the chain map on a given chain
	chain _value (const chain &sigma);

protected:

	// maximal dimension of domain cells
	int maxdim;

	// table of fixed dimension lists of chain map pairs
	fixdimchainmappairs *fi;
};

// --------------------------------------------------

inline chainmap::~chainmap ()
{
	if (!fi)
		throw "Trying to delete already deleted chain map.";

	delete [] fi;

	fi = NULL;
}

// operator '[]' to return j-th list of chain map pairs
inline fixdimchainmappairs &chainmap::operator [] (int j)
{
	return (fi [j]);
}

// return the maximal dimension of domain cells
inline int chainmap::dim ()
{
	return (maxdim);
}



// -------------------------------------------------------------
// ------------------------- MATRIX ----------------------------
// -------------------------------------------------------------

class matrix
{
public:

	// default constructor
	matrix (chain &chn, int q);

	// default destructor
	~matrix ();

	// check if matrix is nonempty
	int nonempty ();

	// find required coefficients a_i
	vector solve ();

	// set number of columns
	void setcolnum (int n);

	// delete all 0's columns (except the last one)
	// and verses of the matrix
	void reduction ();

	// triangulation of the matrix
	void triangulation ();

protected:

	// number of columns
	int colnum;

	// number of non zeros columns (without the last one)
	int nzcolnum;

	// number of non zeros verses
	int nzvernum;

	// list of columns of the matrix
	vector *columns;

	// columns permutation table
	int *colpertbl;

	// verses permutation table
	int *verpertbl;
};

// --------------------------------------------------

inline matrix::~matrix ()
{
	if (columns)
	{
		delete [] columns;
		columns = NULL;
	}

	if (colpertbl)
	{
		delete [] colpertbl;
		colpertbl = NULL;
	}

	if (verpertbl)
	{
		delete [] verpertbl;
		verpertbl = NULL;
	}
}

// check if matrix is nonempty
inline int matrix::nonempty ()
{
	if (colnum) return 1;
	return 0;
}

inline void matrix::setcolnum (int n)
{
	colnum = n;
}



// -------------------------------------------------------------
// ----------------------- CELLLIST ----------------------------
// -------------------------------------------------------------

class celllist
{
public:

	// default constructor (create an empty celllist)
	celllist ();

	// default destructor
	~celllist ();

	// add a cell to the celllist
	void addcell (const cell &c);

	// add all cells from the given reprconvexset to the celllist
	void addreprconvexset (const reprconvexset &r);

	// return the length of celllist
	int l ();

	// return the pointer to the first celllistelement
	celllistelement *&first ();

protected:

	// length of the celllist
	int length;

	// pointer to the first celllistelement
	celllistelement *cllist;
};

// --------------------------------------------------

inline celllist::celllist ()
{
	length = 0;
	cllist = NULL;
}

// return the length of celllist
inline int celllist::l ()
{
	return (length);
}

// return the pointer to the first celllistelement
inline celllistelement *&celllist::first ()
{
	return (cllist);
}



// -------------------------------------------------------------
// ------------------- CELLLISTELEMENT -------------------------
// -------------------------------------------------------------

class celllistelement
{
	friend class celllist;
	friend class domain;

public:

	// default constructor
	celllistelement (const cell &cl);

	// default destructor
	~celllistelement ();

	// return the cell
	cell &box ();

	// return the pointer to the next element of the list of cells
	celllistelement *nxt ();

	// assign
	celllistelement &operator = (const celllistelement &cll);

protected:

	// current cell
	cell c;

	// next cell
	celllistelement *next;
};

// --------------------------------------------------

inline celllistelement::celllistelement (const cell &cl):c ()
{
	c = cl;
	next = NULL;
}

inline celllistelement::~celllistelement ()
{
}

// return the cell
inline cell &celllistelement::box ()
{
	return (c);
}

// return the pointer to the next element of the list of cells
inline celllistelement *celllistelement::nxt ()
{
	return (next);
}


// **************************************************
// **************************************************
// ********** This is the end of the file  **********
// ********** "chmap.h". The original con- **********
// ********** tents of "chmap.cpp" follows.**********
// **************************************************
// **************************************************


// the names of files from which the multivalued map is read
// and to which the chain map and chain complex CY is written
char *inputfilename = NULL;
char *outputfilename = NULL;
char *outputCYfilename = NULL;

// 1 for algebraic algorithm
int alg = 1;

// --------------------------------------------------
// ------------------- TEXT FILE --------------------
// --------------------------------------------------
// This class contains a definition of a text file
// from which the chain complex definition is read.
// Note: The original name of this class was "textfile" - changed by PwP.

class txtfile
{
	friend class point;
public:

	// constructor
	txtfile (ifstream &_in);

	// put to the structure the first non-white character from the file
	int readchar ();

	// read a number
	// and get the next character from the file to the structure
	int readnumber ();

	// read the phrase from the file
	// (ignore white chars before & inside and one special character '*')
	// and get the next character from the file to the structure
	// and return: 0 = OK, -1 = not found (show a message)
	int readphrase (const char *phrase);

protected:

	// file stream to read from
	ifstream &in;

	// character to be read
	int ch;
};

// --------------------------------------------------

inline txtfile::txtfile (ifstream &_in): in (_in)
{
	readchar ();
}

int txtfile::readchar ()
{
	ch = in.get ();
	// ignore white characters
	while ((ch == ' ') || (ch == '\t') || (ch=='\n'))
	{
		ch = in.get ();
	}
	return ch;
} /* read char */

int txtfile::readnumber ()
{
	// read the number
	int minus = 0;
	if (ch == '-')
	{
		minus = 1;
		readchar ();
	}

	int number = 0;
	while ((ch >= '0') && (ch <= '9'))
	{
		number = 10 * number + ch - '0';
		readchar ();
	}

	if (minus)
		return -number;
	else
		return number;
} /* read number */

int txtfile::readphrase (const char *phrase)
{
	// calculate the length of the phrase
	int length = 0;
	while (phrase [length])
		length ++;

	// allocate memory for the read buffer
	char *buf = new char [length + 1];
	if (!buf)
		throw "Can't allocate few bytes to read from the input file.";

	// fill the buffer with zeroes and read the first character
	for (int j = 0; j <= length; j ++)
		buf [j] = 0;

	// read the phrase from the input file
	int i = 0;
	while (i < length)
	{
		if ((ch == EOF))
			throw "Can't read the phrase from the input file!";
		buf [i++] = (char) ch;
		readchar ();
	}

//	if (((buf [0] | 0x20) == 'E') || ((buf [0] | 0x20) == 'e')) // if this is the end of file
//	{
//		delete [] buf;
//		return -1;
//	}

	// compare the two strings ingnoring case and one special character '*'
	int k = 0;
	while ((((phrase [k] | 0x20) == (buf [k] | 0x20)) ||
		((phrase [k] | 0x20) == '*')) && (k <= length))
		k ++;
	if (k > length)
	{
		delete [] buf;
		return 0;
	}
	else
	{
		delete [] buf;
		return -1;
	}
} /* read phrase */



// -------------------------------------------------------------
// --------------------------- Zp ------------------------------
// -------------------------------------------------------------

Zp Zp::operator + (const Zp &q)
{
	Zp t;

	if (!p)
	{
		t.n = (char) (n + q.n);
	}
	else
	{
		t.n = (char) modulo (n + q.n , p);
	}
	return t;
}

Zp Zp::operator - (const Zp &q)
{
	Zp t;

	if (!p)
	{
		t.n = (char) (n - q.n);
	}
	else
	{
		t.n = (char) modulo (n - q.n , p);
	}
	return t;
}

Zp Zp::operator * (const Zp &q)
{
	Zp t;

	if (!p)
	{
		t.n = (char) (n * q.n);
	}
	else
	{
		t.n = (char) modulo (n * q.n , p);
	}
	return t;
}

Zp Zp::operator / (const Zp &q)
{
	if (q.n == 0)
	throw "Can't divide by zero!";

	Zp t;

	t.n = (char) div (n, q.n).quot;

	return t;
}

Zp Zp::operator - ()
{
	Zp t;

	if (!p)
	{
		t.n = (char) -n;
	}
	else
	{
		t.n = (char) modulo (-n , p);
	}
	return t;
}

int Zp::modulo (int k, int m)
{
	while (k < 0) k += p;

	return ((int) fmod ((double) k , (double) m));
}



// -------------------------------------------------------------
// --------------------------- POINT ---------------------------
// -------------------------------------------------------------

point &point::operator = (const point &p)
{
	if (coordinates)
	{
		delete [] coordinates;
		coordinates = NULL;
	}

	coordinates = new int [spacedim];

	if (!coordinates)
		throw "Can't allocate memory to assign a point.";

	for (int i = 0; i < spacedim; i++)
		coordinates[i] = p.coordinates[i];
	return *this;
}

int point::read (txtfile &f)
{
	// the first character should be '('
	if (f.ch != '(')
		return 0;

	f.readchar ();

	// read the coordinates
	for (int i = 0; i < spacedim; i ++)
	{

		// read the i-th coordinate
		coordinates [i] = f.readnumber ();

		// read the comma between the coordinates or ')' at the end
		if (i < spacedim - 1)
		{
			if (f.ch != ',')
				return 0;
		}

		else if (f.ch != ')')
			return 0;

		f.readchar ();
	}

	return 1;
}

// write the point to the stream
int point::write (ofstream &out)
{
	out << "(";
	for (int i = 0; i < spacedim; i ++)
	{
		out << coordinates [i];
		if (i != spacedim - 1) out << ", ";
	}
	out << ")";

	return 1;
}



// -------------------------------------------------------------
// ---------------- REPRESENTABLE CONVEX SET  ------------------
// -------------------------------------------------------------

reprconvexset &reprconvexset::operator *= (const reprconvexset &z)
{
	for (int i = 0; i < ll.spdim (); i++)
	{
		ll [i] = max(ll [i] , z.ll [i]);
		ru [i] = min(ru [i] , z.ru [i]);
		if (ll [i] > ru [i])
		throw "Intersection shouldn't be empty!";
	}
	return *this;
}

int reprconvexset::dim () const
{
	int k = 0;

	for (int i = 0; i < ll.spdim (); i++)
		if (ll [i] < ru [i]) k++;
	return (k);
}

int reprconvexset::firstnottrivial ()
{
	int k;

	for (k = 0; k < ll.spdim (); k++)
		if (ll [k] < ru [k]) return (k);

	return -1;
}

// count the first dimension of the set in which the edge is longer than 1
// if there are no such edges - return (-1) 
int reprconvexset::firstlarge () const
{
	int i;

	for (i = 0; i < ll.spdim (); i++)
		if (ll [i] + 1 < ru [i]) return (i);
	return (-1);
}



// -------------------------------------------------------------
// ------------------------- CELL  -----------------------------
// -------------------------------------------------------------

// operator '<=' to check if the cell is a face of another cell
int cell::operator <= (const cell &z) const
{
	for (int i = 0; i < ll.spdim (); i++)
	{
		if ((ll [i] < z.ll [i])
			|| (ru [i] > z.ru [i])) return 0;
	}
	return 1;
}

// operator '<=' to check if the cell is a face of representable convex set
int cell::operator <= (const reprconvexset &z) const
{
	for (int i = 0; i < ll.spdim (); i++)
	{
		if ((ll [i] < z.ll [i])
			|| (ru [i] > z.ru [i])) return 0;
	}
	return 1;
}

// find the intersection of images of primitive cells
// from domain of multivalued map
// for which the given cell is a face
reprconvexset cell::A (const multivalmap &f)
{
	int A_is_empty = 1; //the result is empty

	int i = 0;
	int j;

	reprconvexset R;

	// for all primitive cells from domain check if the cell is their face
	// return the intersection of their images
	while ((i <= f.dim ()) && (!f [i].l ()) || (!i)) i++;
	if (i > f.dim ()) i = 0;

	for (j = 0; j < f [i].l (); j++)
	{
		if (*this <= f [i] [j].x)
		{
			if (A_is_empty)
			{
				R = f [i] [j].y;
				A_is_empty = 0;
			}
			else
				R *= f [i] [j].y;
		}
	}

	if (A_is_empty)
		throw "Set A shouldn't be empty !";

	return (R);
}

// find the k-th projection of the cell (k-th coordinate = m)
cell cell::pi (int k, int m)
{
	cell S (*this);

	if (ll [k] == ru [k])
	{
		S.ll [k] = m;
		S.ru [k] = m;
	}
	else
	{
		S.ll [0] = 1;
		S.ru [0] = 0;
	}

	return (S);
}

// boundary operator
chain cell::bd()
{
	chain chn (2 * dim ());	// create a chain for boundary of cell

	Zp k = -1;

	for (int i = 0; i < ll.spdim (); i++)
		if (ll [i] < ru [i])
		{
			k = -k;

			// put larger i-th coordinate to ll
			// (collapse the dimension of cell)
			cell c (*this , ru [i] , -i-1);
			chainelement ce (k , c);

			// add to a boundary chain
			// chn.cn [2 * i] = ce;
			chn.addchainelement (ce);

			// put smaller i-th coordinate to ru
			// (collapse the dimension of cell)
			cell c2 (*this , ll [i] , i+1);
			chainelement ce2 (-k , c2);

			// add to a boundary chain
			// chn.cn [2 * i + 1] = ce;
			chn.addchainelement (ce2);
		}

	return (chn);
}



// -------------------------------------------------------------
// ----------------------- NUMBERLIST --------------------------
// -------------------------------------------------------------

int numberlist::insert (cell c)
{
	int i, s = 1;
	int t = c.ll.spdim ();
	int *coordinates;
	numberlistelement *pt;
//	numberlistelement * pt1;
	int ins = 0;

	coordinates = new int [2*t];

	for (i = 0; i < t; i ++)
	{
		coordinates [i] = c.ll [i];
		coordinates [t+i] = c.ru [i];
	}


	if (!head)
	{
		head = new numberlistelement (coordinates [s]);
		ins = 1;
	}

	pt = head;

	while (s < 2*t)
	{
	//	cout << pt->number << ", ";
	//	cout << coordinates [s] << "\n";

		while (!(pt -> number == coordinates [s]) && (pt -> next))
			pt = pt -> next;
		if (!(pt -> number == coordinates [s]))
		{
			pt -> next = new numberlistelement (coordinates [s]);
			pt = pt -> next;
			ins = 1;
		}

		s++;

		if (!(pt -> nextlist) && (s < 2*t))
		{
			pt -> nextlist = new numberlistelement (coordinates [s]);
			ins = 1;
		}

		pt = pt -> nextlist;


	}

	delete [] coordinates;
	return (ins);
}



// -------------------------------------------------------------
// ---------------------- FIXDIMCELLS --------------------------
// -------------------------------------------------------------

fixdimcells &fixdimcells::operator = (const fixdimcells &f)
{
	length = f.length;
	pointer = f.pointer;
	fdc = new argument [length];

	if (!fdc)
		throw "Can't allocate memory to assign a list of cells.";

	for (int i = 0; i < length; i++) fdc [i] = f.fdc [i];

	return *this;
}

// if not in list - add new argument to the end of it
void fixdimcells::addarg (argument &a)
{
	//int add = 1;	// add the argument or not?

	if (pointer >= length)
		throw "Trying to add one argument too many.";

	//for (int j = 0; j < pointer; j++)
	//	if (fdc [j] == a) add = 0;

	//if (add)
		fdc [pointer++] = a;
}



// -------------------------------------------------------------
// ------------------------- DOMAIN ----------------------------
// -------------------------------------------------------------

domain::domain (domain &dom, int maxdim)
{
	if (maxdim + 1)
	{
		D = new fixdimcells [maxdim + 1];
		if (!D)
			throw "Can't allocate memory to copy domain.";

		for (int i = 0; i < maxdim + 1; i ++)
			D [i] = dom.D [i];
	}
	else
		D = NULL;
}

// calculate the convex envelope of the domain
void domain::envelope (int maxdim)
{
	int i, j;

	convenv = D [maxdim].fdc [0];
	for (i = 1; i < D [maxdim].length; i ++)
		for (j = 0; j < convenv.ll.spdim (); j ++)
		{
			convenv.ll [j] = min (D [maxdim] [i].ll [j], convenv.ll [j]);
			convenv.ru [j] = max (D [maxdim] [i].ru [j], convenv.ru [j]);
		}
} 

// completion of the domain
void domain::completion (int maxdim)
{
	int i,j,k;

	envelope (maxdim);

//	D [maxdim].hash = new numberlistelement [convenv.ru [0] - convenv.ll [0] + 1];

//	for (j = 0; j < convenv.ru [0] - convenv.ll [0] + 1; j ++)
//		hash [j].number = convenv.ll [1] - 10;

//	for (j = 0; j < D [maxdim].l (); j ++)
//		D [maxdim].hash.insert (D [maxdim] [j]);

	for (i = maxdim; i > 0; i --)
	{
		// another temporary structure
		celllist cl;
		int z = i - 1;
		int quot, prev_quot;

		cout << "\n\nCompleting dimension " << z << "...\n";
		cout.flush ();
		cout << "    Calculating domain...  0 % ";
		cout.flush ();


		D [i-1].hash = new numberlist [convenv.ru [0] - convenv.ll [0] + 1];


		prev_quot = 0;
		for (j = 0; j < D [i].l (); j ++)
		{
			chain ch = chain (D [i] [j].bd());
			for (k = 0; k < ch.l (); k ++)
				if (D [i-1].hash [ch [k].c.ll [0] - convenv.ll [0]].insert (ch [k].c))
					cl.addcell (ch [k].c);

			//wmove (scr,y,x);
			quot = (int) (((float) (j + 1) / (float) D [i].l ()) * 100);
			if (quot != prev_quot)
			{
				cout << "\r    Calculating domain...  " << (int) quot << " % ";
				cout.flush ();
				prev_quot = quot;
			}
			//delay (100);

		}

		cout << "\n";
		cout.flush ();
		cout << "    Completing domain...   0 % ";
		cout.flush ();


		// set length of the list of arguments of (i-1)'th dimension
		D [i-1] = fixdimcells (cl.l ());
		// add all boundary cells to the list of arguments of (i-1)'th dimension
		prev_quot = 0;
		for (j = 0; j < cl.l (); j ++)
		{
			D [i-1].addarg (cl.first () ->c );
			cl.first () = (cl.first () -> next);
			//wmove (scr,y,x);
			quot = (int) (((float) (j + 1) / (float) cl.l ()) * 100);
			if (quot != prev_quot)
			{
				cout << "\r    Completing domain...   " << quot << " % ";
				cout.flush ();
				prev_quot = quot;
			}

			//delay (100);

		}
	}
}



// -------------------------------------------------------------
// ---------------------- FIXDIMPAIRS --------------------------
// -------------------------------------------------------------

fixdimpairs &fixdimpairs::operator = (const fixdimpairs &f)
{
	length = f.length;
	pointer = f.pointer;
	fdp = new ppair [length];

	if (!fdp)
		throw "Can't allocate memory to assign a list of pairs.";

	for (int i = 0; i < length; i++) fdp [i] = f.fdp [i];

	return *this;
}

// if not in list - add new pair to the end of it
void fixdimpairs::addpair (ppair &p)
{
	int add = 1;	// add the pair or not?

	if (pointer >= length)
		throw "Trying to add one pair too many.";

	for (int j = 0; j < pointer; j++)
		if (fdp [j] == p) add = 0;

	if (add)
		fdp [pointer++] = p;
}



// -------------------------------------------------------------
// ------------------------ MULTIVALMAP ------------------------
// -------------------------------------------------------------

// write chain complex CY to file
void multivalmap::writeCYtofile (celllist &cll, ofstream &outCY)
{
	int i;
	int quot, prev_quot;

	cout << "\n\n";
	cout.flush ();
	cout << "Writing a chain complex... 0 % ";
	cout.flush ();

	prev_quot = 0;
	for (i = 0; i < cll.l (); i++)
	{
		if (! (cll.first () -> box ().write (outCY)))
			throw "Can't write the chain complex.";
		outCY << endl;
		cll.first () = cll.first () -> nxt ();

		//wmove (scr,y,x);
		quot = (int) (((float) (i + 1) / (float) cll.l ()) * 100);
		if (quot != prev_quot)
		{
			cout << "\rWriting a chain complex... " << quot << " % ";
			cout.flush ();
			prev_quot = quot;
		}

		 //delay (100);

	}
}



// -------------------------------------------------------------
// ---------------------- CHAINELEMENT -------------------------
// -------------------------------------------------------------

chainelement::chainelement (Zp _k): c()
{
	k = _k;
}

chainelement::chainelement (Zp _k, const cell &_c)
{
	k = _k;
	c = _c;
}



// -------------------------------------------------------------
// -------------------------- CHAIN ----------------------------
// -------------------------------------------------------------


// copying constructor

chain::chain (const chain &c, int s)
{
	if (s)
		length = c.pointer;
	else
		length = c.length;
	pointer = c.pointer;
	if (!c.ch) ch = NULL;
	else
	{
		ch = new chainelement [length];

		if (!ch)
			throw "Can't allocate memory to create a new chain.";

		for (int i = 0; i < length; i++)
			ch [i] = c.ch [i];
	}
}

// copying constructor

/* chain::chain (const chain &c)
{
	length = c.length;
	pointer = c.pointer;
	if (!c.ch) ch = NULL;
	else
	{
		ch = new chainelement [length];

		if (!ch)
			throw "Can't allocate memory to create a new chain.";

		for (int i = 0; i < length; i++)
			ch [i] = c.ch [i];
	}
} */

// find the k-th projection of the chain (k-th coordinate = m)
chain chain::pi (int k, int m)
{
	chain temp (length);
	int i;

	for (i = 0; i < length; i++)
	{
		chainelement ce = chainelement (ch [i].k , ch [i].c.pi (k , m));
		if (ce.c.ll [0] <= ce.c.ru [0]) // if k-th projection of the cell is nontrivial
			temp += ce;
	}

	chain chn = chain (temp, 1);  // cut what's redundant

	return (chn);
}

// find the temporary chain
chain chain::projection (int k, int m)
{
	int i,l = 0;
	for (i = 0; i < length; i++)
		if (ch [i].c.ll [k] == ch [i].c.ru [k])
			l += (ch [i].c.ru [k] - m);
	chain temp (l);

	for (i = 0; i < length; i++)
		if (ch [i].c.ll [k] == ch [i].c.ru [k])
			for (l = m; l < ch [i].c.ru [k]; l++)
			{
				cell S = cell (ch [i].c);
				S.ll [k] = l;
				S.ru [k] = l + 1;
				chainelement ce = chainelement (ch [i].k, S);
				temp += ce;
			}
	chain chn = chain (temp, 1);

	return (chn);
}

// assign a chain
chain &chain::operator = (const chain &c)
{
	length = c.length;
	pointer = c.pointer;
	if (!c.ch)
		ch = NULL;
	else
	{
		ch = new chainelement [length];
		if (!ch)
			throw "Can't allocate memory to asssign a chain.";
		for (int i = 0; i < length; i++) ch [i] = c.ch [i];
	}

	return *this;
}

// operator '+=' to add a chain element (with controll of the coefficients)
chain &chain::operator += (const chainelement &ce)
{
	int add = 1;	// add the chain element or not?
	int sub = 0;	// substract the chain element or not? (in case of the opposite coefficient)
	int j = 0;

	if (pointer >= length)
		throw "Trying to add one chain element too many.";

	while ((j < pointer) && (add))
	{
		if (ch [j].c == ce.c)
		{
			add = 0;
			ch [j].k = ch [j].k + ce.k;
			if (ch [j].k == 0) // if adding the chain element caused reduction of the cell
			sub = 1;           // mark it for reduction
		}
		j ++;
	}

	if (sub)
	{
		for (add = j; add < pointer; add ++)
			ch [add - 1] = ch [add];
		pointer --;
	}
	else
		if (add)
			ch [pointer++] = ce;

	return (*this);
}

// operator '+' to add a chain
chain chain::operator + (const chain &c) const
{
	chain temp (length + c.length);
	temp.pointer = length;
	int i;

	for (i = 0; i < length; i++)
		temp.ch [i] = ch [i];
	for (i = 0; i < c.length; i++)
		temp += c.ch [i];
	chain chn = chain (temp, 1);

	return (chn);
}

// find the coboundary of the chain
chain chain::cob (int q)
{
	chain chn;
	reprconvexset R = conv ();     // find the convex envelope of the chain

	int d = R.dim ();
	if (d > q)
	{
		int k = R.firstnottrivial (); // find first nontrivial dimension in R
	int m = R.ll [k];             // ... and its lower coordinate
	chn = pi (k , m).cob (q) + projection (k , m);
	}

	return chn;
}


// find the coboundary of a given zero dimensional chain
chain chain::cob ()
{
	int i,j,l;
	int chlength = 0;

	if (!ch)
	{
		chain chn;
		return (chn);
	}

	// calculate the length of the coboundary 
	for (l = 0; l < ch [0].c.ll.spdim (); l ++)
		chlength = chlength + abs (ch [0].c.ll [l] - ch [1].c.ll [l]);

	chain chn (chlength);

	chainelement chnel;

	for (l = 0; l < ch [0].c.ll.spdim (); l ++)
	{
		// calculate a part of the coboundary in dimnesion l
		if (ch [0].c.ll [l] < ch [1].c.ll [l])
		{
			if (ch [0].k == 1)	chnel.k = (Zp) 1;
			else chnel.k = (Zp) -1;

			for (i = l + 1; i < ch [0].c.ll.spdim (); i ++)
			{
				chnel.c.ll [i] = ch [0].c.ll [i];
				chnel.c.ru [i] = ch [0].c.ll [i];
			}

			for (j = ch [0].c.ll [l] + 1; j <= ch [1].c.ll [l]; j ++)
			{
				chnel.c.ll [l] = j - 1;
				chnel.c.ru [l] = j;
				chn.addchainelement (chnel);
			}

			chnel.c.ll [l] = j - 1;

		}
		else if (ch [0].c.ll [l] > ch [1].c.ll [l])
		{
			if (ch [0].k == 1)	chnel.k = (Zp) -1;
			else chnel.k = (Zp) 1;

			for (i = l + 1; i < ch [0].c.ll.spdim (); i ++)
			{
				chnel.c.ll [i] = ch [0].c.ll [i];
				chnel.c.ru [i] = ch [0].c.ll [i];
			}

			for (j = ch [1].c.ll [l] + 1; j <= ch [0].c.ll [l]; j ++)
			{
				chnel.c.ll [l] = j - 1;
				chnel.c.ru [l] = j;
				chn.addchainelement (chnel);
			}

			chnel.c.ll [l] = ch [1].c.ll [l];
			chnel.c.ru [l] = ch [1].c.ll [l];

		}
		else
		{
			chnel.c.ll [l] = ch [1].c.ll [l];
			chnel.c.ru [l] = ch [1].c.ll [l];

		}
	}

	return (chn);

}

// find the convex envelope of the chain
reprconvexset chain::conv ()
{
	int i,j,l;
	reprconvexset S;
	if (length)
	{
		// result = first cell in the chain
		S.ll = ch [0].c.ll;
		S.ru = ch [0].c.ru;
		l = S.ll.spdim ();

		for (i = 1; i < length; i++)
			// if any of of other cells in the chain is bigger than result: extend the result
			for (j = 0; j < l; j ++)
			{
				if (ch [i].c.ll [j] < S.ll [j])
					S.ll [j] = ch [i].c.ll [j];
				if (ch [i].c.ru [j] > S.ru [j])
					S.ru [j] = ch [i].c.ru [j];
			}
	}

	return (S);
}

// add new chain element
void chain::addchainelement (const chainelement &ce)
{
	if (pointer >= length)
		throw "Trying to add one chain element too many.";

	ch [pointer++] = ce;
}

// write the chain to the stream
int chain::write (ofstream &out)
{
	if (! length)
		out << "0";
	else
		for (int i = 0; i < length; i ++)
		{
			out << ch [i].k << "*";
			ch [i].c.write (out);
			if (i != length - 1) out << " + ";
		}

	return 1;
}



// -------------------------------------------------------------
// ------------------ FIXDIMCHAINMAPPAIRS ----------------------
// -------------------------------------------------------------

fixdimchainmappairs &fixdimchainmappairs::operator = (const fixdimchainmappairs &fcm)
{
	length = fcm.length;
	pointer = fcm.pointer;
	fdcmp = new chainmappair [length];

	if (!fdcmp)
		throw "Can't allocate memory to assign a list of chain map pairs.";

	for (int i = 0; i < length; i++) fdcmp [i] = fcm.fdcmp [i];

	return *this;
}

// add new chain map pair to the end of list
void fixdimchainmappairs::addchainmappair (chainmappair &cmp)
{
	int add = 1;	// add the chain map pair or not?

	if (pointer >= length)
		throw "Trying to add one chain map pair too many.";

	for (int j = 0; j < pointer; j++)
		if (fdcmp [j] == cmp) add = 0;

	if (add)
		fdcmp [pointer++] = cmp;
}



// -------------------------------------------------------------
// ------------------------- CHAINMAP --------------------------
// -------------------------------------------------------------

// default constructor
chainmap::chainmap (multivalmap *mvm, int alg)
{
	maxdim = mvm -> dim ();

	if (maxdim + 1)
	{
		fi = new fixdimchainmappairs [maxdim + 1];
		if (!fi)
			throw "Can't allocate memory to create a new chain map.";
	}
	else
		fi = NULL;

	int j;
	int quot, prev_quot;

	// zero dimension
	chain chn (1);

	cout << "\n\n";
	cout.flush ();
	cout << "Calculating dimension 0... 0 % ";
	cout.flush ();


	fi [0] = fixdimchainmappairs (mvm -> domn (0).l ());

	prev_quot = 0;
	for (j = 0; j < fi [0].l (); j ++)
	{
		// value = left lower vertex of A(argument)
		fi [0] [j].x = mvm -> domn (0) [j];
		chn [0].c.ll = fi [0] [j].x.A (*mvm).ll;
		chn [0].c.ru = chn [0].c.ll;
		fi [0] [j].y = chn;

		//wmove (scr,y,x);
		quot = (int) (((float) (j + 1) / (float) fi [0].l ()) * 100);
		if (quot != prev_quot)
		{
			cout << "\rCalculating dimension 0... " << (int) quot << " % ";
			cout.flush ();
			prev_quot = quot;
		}

		//delay (100);

	}

	if (alg) chainmapalg (mvm);
	else chainmapgeom (mvm);

}


// first continuation of default constructor
void chainmap::chainmapalg (multivalmap *mvm)
{
	int i, j;//, l;
	int quot, prev_quot;

	//first dimension
	cout << "\n\n";
	cout.flush ();
	cout << "Calculating dimension 1... 0 % ";
	cout.flush ();

	fi [1] = fixdimchainmappairs (mvm -> domn (1).l ());

	prev_quot = 0;
	for (j = 0; j < fi [1].l (); j ++)
	{
		fi [1] [j].x = mvm -> domn (1) [j];

		fi [1] [j].y = _value (fi [1] [j].x.bd ()).cob ();


/*			cout << "Argument: [(";			        //DEL
			for (l = 0; l < fi [1] [j].x.ll.spdim (); l++)
				cout << fi [1] [j].x.ll [l] << " ";
			cout << ") (";
			for (l = 0; l < fi [1] [j].x.ru.spdim (); l++)
				cout << fi [1] [j].x.ru [l] << " ";
			cout << ")] ";
			cout << endl;

			cout << "Value: ";
			for (int s = 0; s < fi[1] [j].y.l (); s++)
			{
				cout << fi [1] [j].y [s].k << " * ";
				cout << "[(";
				for (l = 0; l < fi [1] [j].y [s].c.ll.spdim (); l++)
					cout << fi [1] [j].y [s].c.ll [l] << " ";
				cout << ") (";
				for (l = 0; l < fi [1] [j].y [s].c.ru.spdim (); l++)
					cout << fi [1] [j].y [s].c.ru [l] << " ";
				cout << ")] ";
			}
			cout << endl; */

		//wmove (scr,y,x);
		quot = (int) ((float) (j + 1) / (float) fi [1].l ()) * 100;
		if (quot != prev_quot)
		{
			cout << "\rCalculating dimension 1... " << (int) quot << " % ";
			cout.flush ();
			prev_quot = quot;
		}
		//delay (100);

	}

	// other dimensions

	// temporary variable

	for (i = 2; i <= maxdim; i ++)
	{
		cout << "\n\n";
		cout.flush ();
		cout << "Calculating dimension " << i << "... 0 % ";
		cout.flush ();

		fi [i] = fixdimchainmappairs (mvm -> domn (i).l ());

		prev_quot = 0;
		for (j = 0; j < fi [i].l (); j ++)
		{
			fi [i] [j].x = mvm -> domn (i) [j];


			chain chn = _value (fi [i] [j].x.bd ());

			if (chn.l ())							  // if fi of boundary is nontrivial
			{
				// create a matrix of bounaries of all i-dimensional cells in convex envelope
				// of the support of value (boundary (argument)) ...
				matrix mtrx (chn, i);

				// ... forget its zero columns and verses ...
				if (mtrx.nonempty ())
				{
					mtrx.reduction ();

					// ... triangulate ...
					mtrx.triangulation ();

					// ... and solve it! value (argument) = solution
					fi [i] [j].y = mtrx.solve ().decodevector (chn.conv ());
				}
		 }


/*			cout << "Argument: [(";			        //DEL
			for (l = 0; l < fi [i] [j].x.ll.spdim (); l++)
				cout << fi [i] [j].x.ll [l] << " ";
			cout << ") (";
			for (l = 0; l < fi [i] [j].x.ru.spdim (); l++)
				cout << fi [i] [j].x.ru [l] << " ";
			cout << ")] ";
			cout << endl;

			cout << "Value: ";
			for (int s = 0; s < fi[i] [j].y.l (); s++)
			{
				cout << fi [i] [j].y [s].k << " * ";
				cout << "[(";
				for (l = 0; l < fi [i] [j].y [s].c.ll.spdim (); l++)
					cout << fi [i] [j].y [s].c.ll [l] << " ";
				cout << ") (";
				for (l = 0; l < fi [i] [j].y [s].c.ru.spdim (); l++)
					cout << fi [i] [j].y [s].c.ru [l] << " ";
				cout << ")] ";
			}
			cout << endl;  */

			//wmove (scr,y,x);
			quot = (int) (((float) (j + 1) / (float) fi [i].l ()) * 100);
			if (quot != prev_quot)
			{
				cout << "\rCalculating dimension " << i << "... " << (int) quot << " % ";
				cout.flush ();
				prev_quot = quot;
			}
			//delay (100);

		}
	}
}

// second continuation of default constructor
void chainmap::chainmapgeom (multivalmap *mvm)
{
	int i, j;
	int quot, prev_quot;

	// other dimensions

	for (i = 1; i <= maxdim; i ++)
	{
		cout << "\n\n";
		cout.flush ();
		cout << "Calculating dimension " << i << "... 0 % ";
		cout.flush ();

		fi [i] = fixdimchainmappairs (mvm -> domn (i).l ());

		for (j = 0; j < fi [i].l (); j ++)
		{
			fi [i] [j].x = mvm -> domn (i) [j];

			chain chn = _value (fi [i] [j].x.bd ());

			prev_quot = 0;
			if (chn.l ())							  // if fi of boundary is nontrivial
				fi [i] [j].y = chn.cob (i - 1); // find its coboundary

/*			cout << "Argument: [(";			        //DEL
			for (l = 0; l < fi [i] [j].x.ll.spdim (); l++)
				cout << fi [i] [j].x.ll [l] << " ";
			cout << ") (";
			for (l = 0; l < fi [i] [j].x.ru.spdim (); l++)
				cout << fi [i] [j].x.ru [l] << " ";
			cout << ")] ";
			cout << endl;

			cout << "Value: ";
			for (int s = 0; s < fi[i] [j].y.l (); s++)
			{
				cout << fi [i] [j].y [s].k << " * ";
				cout << "[(";
				for (l = 0; l < fi [i] [j].y [s].c.ll.spdim (); l++)
					cout << fi [i] [j].y [s].c.ll [l] << " ";
				cout << ") (";
				for (l = 0; l < fi [i] [j].y [s].c.ru.spdim (); l++)
					cout << fi [i] [j].y [s].c.ru [l] << " ";
				cout << ")] ";
			}
			cout << endl; */
			
			quot = (int) (((float) (j + 1) / (float) fi [i].l ()) * 100);
			if (quot != prev_quot)
			{
				cout << "\rCalculating dimension " << i << "... " << quot << " % ";
				cout.flush ();
				prev_quot = quot;
			}

		}
	}
}



// calculate the value of the chain map on a given chain
chain chainmap::_value (const chain &sigma)
{
	int i,j,k = 0;
	int lgth = 0;
	int q = sigma.dim ();

	int *fixedpair;
	int *erase;

	if (!sigma.l ())
	{
		chain tau;
		return (tau);
	}

	fixedpair = new int [sigma.l ()];

	if (!fixedpair)
		throw "Can't allocate memory to create a list of integers.";

	// find where the cells from given chain are situated in the chain map
	for (i = 0; i < fi [q].l (); i++)
		for (j = 0; j < sigma.l (); j++)
			if (fi [q] [i].x == sigma [j].c)
				fixedpair [j] = i;

	// calculate the initial length of result
	for (i = 0; i < sigma.l (); i++)
		lgth += fi [q] [fixedpair [i]].y.l ();

	if (!lgth)
	{
		chain tau;
		return (tau);
	}

	chain tau (lgth);

	// calculate the initial result
	for (i = 0; i < sigma.l (); i++)
		for (j = 0; j < fi [q] [fixedpair [i]].y.l (); j++)
		{
			tau [k].c = fi [q] [fixedpair [i]].y [j].c;
			tau [k++].k = sigma [i].k
				* fi [q] [fixedpair [i]].y [j].k;
		}

	erase = new int [lgth];

	if (!erase)
		throw "Can't allocate memory to create a list of integers.";

	k = lgth;

	// check which chain elements of the result should be deleted
	for (i = 0; i < lgth; i++)
		if (tau [i].k == 0)
		{
			erase [i] = 1;                 // 1 - delete
			k--;
		}
		else erase [i] = 0;               // 0 - don't delete


	// add all chain elements with the same cells and mark the redundant ones for deletion
	for (i = 0; i < lgth; i++)
		if (!erase [i])
		{
			for (j = i + 1; j < lgth; j++)
				if ((tau [i].c == tau [j].c) && (!(erase [j])))
				{
					tau [i].k = tau [i].k + tau [j].k;
					tau [j].k = (Zp) 0;
					erase [j] = 1;
					k--;
				}

			if (tau [i].k == 0)
			{
				k--;
				erase [i] = 1;
			}
		}


	if (!k)
	{
		chain theta;
		return (theta);
	}

	chain theta (k);

	j = 0;

	// result = all chain elements with nonzero coefficients
	for (i = 0; i < lgth; i++)
		if (!erase [i])
		{
			theta [j].c = tau [i].c;
			theta [j++].k = tau [i].k;

		}

	delete [] erase;
	delete [] fixedpair;

	return (theta);
}



// -------------------------------------------------------------
// ------------------------- VECTOR ----------------------------
// -------------------------------------------------------------

// create a vector of the coefficients of these chain elements that are
// in the given chain
// write the appropriate coefficient in the appropriate cell's number's
// coordinate of the vector
vector::vector (const chain &sigma, const reprconvexset &A)
{
	int i;

	setdefdim (A);

	if ((sigma.l ()) && (vectordim))
	{
		coordinates = new Zp [vectordim];

		if (!coordinates)
			throw "Can't allocate memory to create a new vector.";

		for (i = 0; i < vectordim; i++)
			coordinates [i] = (Zp) 0;

		for (i = 0; i < sigma.l (); i++)
			coordinates [number (sigma [i].c, A)] = sigma [i].k;
	}
	else
	{
		vectordim = 0;
		coordinates = NULL;
	}
}

vector::vector (const vector &vec)
{
	int i;

	vectordim = vec.vectordim;
	coordinates = new Zp [vectordim];

	if (!coordinates)
		throw "Can't allocate memory to copy a vector.";

	for (i = 0; i < vectordim; i++)
		coordinates [i] = vec.coordinates [i];
}

// operator '=' to assign a vector
vector &vector::operator = (const vector &v)
{
	vectordim = v.vectordim;

	if (vectordim)
	{
		coordinates = new Zp [vectordim];

		if (!coordinates)
			throw "Can't allocate memory to assign a vector.";

		for (int i = 0; i < vectordim; i++)
			coordinates[i] = v.coordinates[i];
	}
	else coordinates = NULL;

	return *this;
}

// calculate the cells number in a given set
int vector::number (const cell &c, const reprconvexset &A)
{
	int i;
	int num = 0;
	int factor = 1;

	if (A.dim () < c.dim ())
		return -1;

	for (i = 0; i < A.ll.spdim (); i++)
	{
		num += ((c.ll [i] - A.ll [i]) * factor);
		factor *= (A.ru [i] - A.ll [i] + 1);
	}

	num = num * twoto (A.dim ()) + twoto (A.dim ()) - 1;

	factor = 1;

	for (i = 0; i < A.ll.spdim (); i++)
		if (A.ru [i] - A.ll [i])
		{
			num -= (c.ru [i] - c.ll [i]) * factor;
			factor *= 2;
		}

	return (num);
}

// decode a vector of coefficients to a corresponding chain
chain vector::decodevector (const reprconvexset &A)
{
	int i;
	int chlgth = 0;

	for (i = 0; i < vectordim; i++)
		if (!(coordinates [i] == 0)) chlgth++;

	if (!chlgth)
	{
		chain ch;
		return ch;
	}

	chain ch (chlgth);

	for (i = 0; i < vectordim; i ++) // add all the appropriate chain elements to the chain
		if (!(coordinates [i] == 0))
			ch.addchainelement (chainelement (coordinates [i], decodenumber (i, A)));

	return (ch);
}

void vector::setdefdim (const reprconvexset &A)
{

	int i;

	vectordim = 1;

	// calculate number of points
	for (i = 0; i < A.ll.spdim (); i++)
		vectordim = vectordim * (A.ru [i] - A.ll [i] + 1);

	// calculate number of cells (a little bit more)
	vectordim = vectordim * twoto (A.dim ());
}



// -------------------------------------------------------------
// ------------------------- MATRIX ----------------------------
// -------------------------------------------------------------

// create a matrix of bounaries of all q-dimensional cells in convex envelope
// of the support of a given chain
matrix::matrix (chain &chn, int q)
{
	// calculate the support of a given chain
	reprconvexset convexsupport = chn.conv ();
	// calculate the last column of matrix
	vector b = vector (chn, convexsupport);

	if (b.vdim ())
	{
		int i;
		int v = b.vdim ();
		colnum = v + 1;
		nzcolnum = colnum - 1;
		nzvernum = v;


		colpertbl = new int [colnum - 1];

		if (!colpertbl)
			throw "Can't allocate memory to create a list of integers.";

		verpertbl = new int [v];

		if (!verpertbl)
			throw "Can't allocate memory to create a list of integers.";

		columns = new vector [colnum];

		if (!columns)
			throw "Can't allocate memory to create a new matrix.";

		// calculate the rest of columns
		for (i = 0; i < colnum - 1; i++)
		{
			colpertbl [i] = i;
			verpertbl [i] = i;

			cell c = cell (decodenumber (i, convexsupport));
			if ((c <= convexsupport) && (c.dim () == q))
				columns [i] = vector (c.bd (), convexsupport);
		}

		columns [colnum - 1] = b;
	}
	else
	{
		colnum = 0;
		columns = NULL;
	}
}

// solve the system of equations given by the triangulated matrix
vector matrix::solve ()
{
	vector a (columns [colpertbl [0]].vdim ());
	int i,k;


	for (i = 0; i < a.vdim (); i++) a [i] = (Zp) 0;

	for (i = 0; i < min (nzvernum, nzcolnum); i++)
	{
		if (!(columns [colpertbl [i]] [verpertbl [i]] == 0))
		{
			for (k = 0; k < i; k++)
				a [colpertbl [i]] = a [colpertbl [i]] + a [colpertbl [k]] * columns [colpertbl [k]] [verpertbl [i]];

			if ((columns [colpertbl [i]] [verpertbl [i]] == 1) ||
				(columns [colpertbl [i]] [verpertbl [i]] == -1))
					a [colpertbl [i]] = (columns [colnum - 1] [verpertbl [i]] - a [colpertbl [i]]) * columns [colpertbl [i]] [verpertbl [i]];
			else
			{
				cout << "AJJJJJJJJJJJJJJJJ!!!!!!";
//				exit(1);
				a [colpertbl [i]] = (columns [colnum - 1] [verpertbl [i]] - a [colpertbl [i]]) / columns [colpertbl [i]] [verpertbl [i]];
			}

		}
	}

	return (a);
}

// delete zero columns and verses
void matrix::reduction ()
{
	int i = 0;
	int j,k,s;
	int del = 1;
	int temp;



	// delete all zero columns (except the last one)
	for (s = 0; s < colnum - 1; s++)
	{
		if (!columns [colpertbl [i]].vdim ())
		{
			nzcolnum --;
			temp = colpertbl [i];
			for (k = i; k < colnum - 2; k++) colpertbl [k] = colpertbl [k + 1];
			colpertbl [colnum - 2] = temp;
		}
		else
		{
			i++;
		}
	}

	i = 0;

	// delete all zero verses
	for (s = 0; s < colnum - 1; s++)
	{
		for (j = 0; j < colnum - 1; j++)
			if (columns [colpertbl [j]].vdim ())
				if (!(columns [colpertbl [j]] [verpertbl [i]] == 0)) del = 0;

		if (del)
		{
			nzvernum --;
			temp = verpertbl [i];
			for (k = i; k < colnum - 2; k++) verpertbl [k] = verpertbl [k + 1];
			verpertbl [colnum - 2] = temp;
		}
		else
		{
			del = 1;
			i++;
		}
	}
}

// triangulation of reduced matrix
void matrix::triangulation ()
{
	int i,j,k,l,lastcolumn;

	if (nzvernum < nzcolnum)
		lastcolumn = nzcolnum - nzvernum;
	else lastcolumn = 0;

	// i - number of column; j - number of verse
	for (i = nzcolnum - 1; i > lastcolumn; i--)
	// make zeros over the diagonal in the i-th column
	{
		j = nzvernum - (nzcolnum - i);
		k = j;

		while ((k >= 0) &&
			(columns [colpertbl [i]] [verpertbl [k]] == 0)) k--;

		if ((k >= 0) && (k != j))
		{
			l = verpertbl [k];
			verpertbl [k] = verpertbl [j];
			verpertbl [j] = l;
		}
		else
		{
			k = i;
			while ((k >= 0) &&
				(columns [colpertbl [k]] [verpertbl [j]] == 0)) k--;

			if ((k >= 0) && (k != i))
			{
				l = colpertbl [k];
				colpertbl [k] = colpertbl [i];
				colpertbl [i] = l;
			}

		}

		if (k >= 0)
		{
			for (l = j - 1; l >= 0; l--)
			{
				if (!(columns [colpertbl [i]] [verpertbl [l]] == 0))
				{
					if ((columns [colpertbl [i]] [verpertbl [j]] == 1)||
						(columns [colpertbl [i]] [verpertbl [j]] == -1))
					{
						if (!(columns [colnum - 1] [verpertbl [j]] == 0))
							columns [colnum - 1] [verpertbl [l]]
							= columns [colnum - 1] [verpertbl [l]]
							- columns [colnum - 1] [verpertbl [j]]
							* columns [colpertbl [i]] [verpertbl [l]]
							* columns [colpertbl [i]] [verpertbl [j]];
						for (k = 0; k < i + 1; k++)
							if (!(columns [colpertbl [k]] [verpertbl [j]] == 0))
								columns [colpertbl [k]] [verpertbl [l]]
								= columns [colpertbl [k]] [verpertbl [l]]
								- columns [colpertbl [k]] [verpertbl [j]]
								* columns [colpertbl [i]] [verpertbl [l]]
								* columns [colpertbl [i]] [verpertbl [j]];
					}
					else
					{
						cout << "AJJJJJJJJJJJJJJJ111111111111";
//						if (!(columns [colnum - 1] [verpertbl [j]] == 0))
						columns [colnum - 1] [verpertbl [l]]
						= columns [colnum - 1] [verpertbl [l]]
						* columns [colpertbl [i]] [verpertbl [j]]
						- columns [colnum - 1] [verpertbl [j]]
						* columns [colpertbl [i]] [verpertbl [l]];

						for (k = 0; k < i + 1; k++)
//						if (!(columns [colpertbl [k]] [verpertbl [j]] == 0))
							columns [colpertbl [k]] [verpertbl [l]]
							= columns [colpertbl [k]] [verpertbl [l]]
							* columns [colpertbl [i]] [verpertbl [j]]
							- columns [colpertbl [k]] [verpertbl [j]]
							* columns [colpertbl [i]] [verpertbl [l]];
					}
				}
			}
		}
	}

	if (nzvernum < nzcolnum)
		// shift the last nzvernum columns to the left part of matrix
		for (i = 0; i < nzvernum; i++)
		{
			l = colpertbl [i];
			colpertbl [i] = colpertbl [i + nzcolnum - nzvernum];
			colpertbl [i + nzcolnum - nzvernum] = l;
		}
	else
		// shift the last nzcolnum verses to the upper part of matrix
		for (i = 0; i < nzcolnum; i++)
		{
			l = verpertbl [i];
			verpertbl [i] = verpertbl [i + nzvernum - nzcolnum];
			verpertbl [i + nzvernum - nzcolnum] = l;
		}

}



// -------------------------------------------------------------
// ----------------------- CELLLIST ----------------------------
// -------------------------------------------------------------

celllist::~celllist ()
{
	celllistelement *tempcllist;

	while (cllist)
	{
		tempcllist = cllist;
		cllist = cllist->next;
		delete [] tempcllist;
	}
}

// add a cell to the celllist
void celllist::addcell (const cell &c)
{
	celllistelement *pt;

	pt = cllist;

	length ++;
	cllist = new celllistelement (c);
	cllist -> next = pt;
	
/*	if (pt)
	{
		while ((pt->next) && (!(pt->c == c))) pt = pt->next;
			if (!(pt->c == c))
			{
				length ++;
				pt->next = new celllistelement (c);
			}
	}
	else
	{
		length ++;
		cllist = new celllistelement (c);
	} */
}

// add all cells from the given reprconvexset to the celllist
void celllist::addreprconvexset (const reprconvexset &r)
{
	int x;
	cell c;
	int dim = r.firstlarge (); // first dimension in which r's edges are longer than 1

	if (dim < 0) // if this is already a cell
	{
		c.ll = r.ll;
		c.ru = r.ru;
		addcell (c);
	}
	else         // if this is still a collection of cells
		for (x = r.ll [dim]; x < r.ru [dim]; x++)
		// cut the set in the dim's dimension and repeat the procedure for all its pieces
		{
			reprconvexset s (r);
			s.ll [dim] = x;
			s.ru [dim] = x + 1;
			addreprconvexset (s);
		}
}



// -------------------------------------------------------------
// -------------------- CELLLISTELEMENT ------------------------
// -------------------------------------------------------------

celllistelement &celllistelement::operator = (const celllistelement &cll)
{
	c = cll.c;
	if (cll.next) *next = celllistelement (cll.next->c);
	else next = NULL;
	return *this;
}



// -------------------------------------------------------------
// ------------------------- FUNCTIONS -------------------------
// -------------------------------------------------------------

// return maximum of two integers
int max (int m, int n)
{
	if (m < n) return n;
	return m;
}

// return minimum of two integers
int min (int m, int n)
{
	if (m > n) return n;
	return m;
}

// return the n-th power of 2
int twoto (int n)
{
	int s = 1;

	for (int i = 0; i < n; i++)
		s *= 2;

	return s;
}

// return the n-th cell in A
cell decodenumber (int n, const reprconvexset &A)
{
	cell c;
	int i;
	div_t num, x;

	num = div (n, twoto (A.dim ()));
	num.rem = twoto (A.dim ()) - num.rem - 1;

	for (i = 0; i < A.ll.spdim (); i++)
	{
		x = div (num.quot, A.ru [i] - A.ll [i] + 1);
		c.ll [i] = A.ll [i] + x.rem;
		num.quot = x.quot;
	}

	for (i = 0; i < A.ll.spdim (); i++)
		if (A.ru [i] - A.ll [i])
		{
			x = div (num.rem, 2);
			c.ru [i] = c.ll [i] + x.rem;
			num.rem = x.quot;
		}
		else c.ru [i] = c.ll [i];

	return c;
}

// read a map from the text file and record the chain complex CY.
// return: 0 = OK, -1 = mistake
multivalmap *readfromfile (ifstream &in, ofstream &outCY)
{
	// temporary variables
	int i,j,k,jj = 0;
	int quot, prev_quot;
	int firsttime = 1;

	// create the structure to read from the file
	txtfile f (in);

	// read the phrase
	if (f. readphrase ("SpaceDimension:") < 0)
		throw "Wrong phrase in the input file!";
	int spdim = f. readnumber ();
	if (spdim <= 0)
		throw "Dimension should be equal at least 1!";

	// read the next phrase
	if (f. readphrase ("NumberOfPrimitiveArguments:") < 0)
		throw "Wrong phrase in the input file!";
	int primargnum = f. readnumber ();
	if (primargnum < 0)
		throw "Wrong number of primitive arguments!";

	// set the dimension of the space
	point::spacedimension (spdim);
	multivalmap::setmaxdim (spdim);

	multivalmap *mvm = new multivalmap;

	// create temporary pair structure;
	ppair p;

	//create a temporary list of cells
	celllist CY;

	// read the next phrase
	if (f. readphrase ("Map:") < 0)
		throw "Wrong phrase in the input file!";

	cout << "\n\n";
	cout.flush ();
	cout << "Reading multivalued map" << "... 0 % ";
	cout.flush ();

	// read the next phrase
	if (f. readphrase ("Almost*") >= 0) // almost perfect map
	{
		// read the next phrase
		if (f. readphrase ("******PrimitiveArgumentValue") < 0)
			throw "Wrong phrase in the input file!";


		// read all pairs of multivalue representable map
		// with primitive arguments
		prev_quot = 0;
		while (f. readphrase ("[") >= 0)
		{
			// read the argument
			if (!p.x.ll.read (f))
				throw "Can't read the point!";

			if (!p.x.ru.read (f))
				throw "Can't read the point!";

			// read the next phrase
			if (f. readphrase ("]") < 0)
				throw "Wrong phrase in the input file!";

			// read the next phrase
			if (f. readphrase ("[") < 0)
				throw "Wrong phrase in the input file!";

			// read the value
			if (!p.y.ll.read (f))
				throw "Can't read the point!";

			if (!p.y.ru.read (f))
				throw "Can't read the point!";

			// read the next phrase
			if (f. readphrase ("]") < 0)
				throw "Wrong phrase in the input file!";

			// set maximal dimension of domain cells
			// and length of the list of pairs of maximal dimension
			// as well as length of the list of arguments of maximal dimension
			if (firsttime > 0)
			{
				mvm -> Fn (mvm -> dim ()) = fixdimpairs (primargnum);

				mvm -> domn (mvm -> dim()) = fixdimcells (primargnum);

				firsttime = 0;
			}

			// add the read pair into the multivalue map structure
			mvm -> Fn (mvm -> dim ()).addpair (p);

			// add the read argument to the domain structure
			mvm -> domn (mvm -> dim ()).addarg (p.x);

			// add all cells from the read value to CY
			CY.addreprconvexset (p.y);

			//wmove (scr,y,x);
			quot = (int) (((float) ++jj / (float) primargnum) * 100);
			if (quot != prev_quot)
			{
				cout << "\rReading multivalued map" << "... " << quot << " % ";
				cout.flush ();
				prev_quot = quot;
			}
			//delay (100);

		} // while

	} else // perfect map
	{
		// read the next phrase
		if (f. readphrase ("NumberOfVertexArguments:") < 0)
			throw "Wrong phrase in the input file!";
		int vertargnum = f. readnumber ();
		if (vertargnum < 0)
			throw "Wrong number of vertices!";

		// set length of the list of pairs of zero dimension
		// as well as length of the list of arguments of zero dimension
		mvm -> Fn (0) = fixdimpairs (vertargnum);
		mvm -> domn (0) = fixdimcells (vertargnum);

		// read the next phrase
		if (f. readphrase ("VertexArgumentValue") < 0)
			throw "Wrong phrase in the input file!";

		// read all pairs of multivalue representable map
		// with vertex arguments
		prev_quot = 0;
		while (f. readphrase ("[") >= 0)
		{
			// read the argument
			if (!p.x.ll.read (f))
				throw "Can't read the point!";

			p.x.ru = p.x.ll;

			// read the next phrase
			if (f. readphrase ("]") < 0)
				throw "Wrong phrase in the input file!";

			// read the next phrase
			if (f. readphrase ("[") < 0)
				throw "Wrong phrase in the input file!";

			// read the value
			if (!p.y.ll.read (f))
				throw "Can't read the point!";

			if (!p.y.ru.read (f))
				throw "Can't read the point!";

			// read the next phrase
			if (f. readphrase ("]") < 0)
				throw "Wrong phrase in the input file!";

			// add the read pair into the multivalue map structure
			mvm -> Fn (0).addpair (p);

			// add the read argument to the domain structure
			mvm -> domn (0).addarg (p.x);

			//wmove (scr,y,x);
			quot = (int) (((float) ++jj / (float) vertargnum) * 100);
			if (quot != prev_quot)
			{
				cout << "\rReading multivalued map" << "... " << (int) quot << " % ";
				cout.flush ();
				prev_quot = quot;
			}
			//delay (100);

		} // while

		cout << "\n\n";
		cout.flush ();
		cout << "Reading domain from the file" << "... 0 % ";
		cout.flush ();
		
		// read primitive arguments
		if (primargnum > 0)
		{
			jj = 0;

			// read the next phrase
			if (f. readphrase ("********Arguments") < 0)
				throw "Wrong phrase in the input file!";

			// temporary variable
			point pt;

			prev_quot = 0;
			while (f. readphrase ("[") >= 0)
			{
				// read the argument...
				if (!p.x.ll.read (f))
					throw "Can't read the point!";

				if (!p.x.ru.read (f))
					throw "Can't read the point!";

				// ...and calculate the value
				for (i = 0; i < twoto (p.x.dim ()); i ++)
				{
					int temp = i;
					j = 0;
					k = twoto (p.x.dim () - 1);

					while (j < spdim)
					{
						if (p.x.ru [j] != p.x.ll [j])
							{
								pt [j] = p.x.ll [j] + div (temp, k).quot;
								temp = div (temp, k).rem;
								k = k / 2;
							}
						else pt [j] = p.x.ll [j];

						j ++;
					}

					// check the value on the last calculated vertex
					// and intersect it with the set calculated before
					for (j = 0; j < vertargnum; j ++)
						if (mvm -> Fn (0) [j].x.ll == pt) break;

					if (!i)
						p.y = mvm -> Fn (0) [j].y;
					else p.y *= mvm -> Fn (0) [j].y;

				} // for


				// read the next phrase
				if (f. readphrase ("]") < 0)
					throw "Wrong phrase in the input file!";

				// set maximal dimension of domain cells
				// and length of the list of arguments of maximal dimension
				if (firsttime > 0)
				{
					multivalmap::setmaxdim (p.x.dim ());

					mvm -> Fn (mvm -> dim ()) = fixdimpairs (primargnum);

					mvm -> domn (mvm -> dim ()) = fixdimcells (primargnum);

					firsttime = 0;
				}

				// add the read and calculate pair into the multivalue map structure
				mvm -> Fn (mvm -> dim ()).addpair (p);

				// add the read argument to the domain structure
				mvm -> domn (mvm -> dim ()).addarg (p.x);

				// add all cells from the read value to CY
				CY.addreprconvexset (p.y);



				//wmove (scr,y,x);
				quot = (int) (((float) ++jj / (float) primargnum) * 100);
				if (quot != prev_quot)
				{
					cout << "\rReading domain from the file" << "... " << (int) quot << " % ";
					cout.flush ();
					prev_quot = quot;
				}
				//delay (100);

			} // while
		} // if

	} // else

	// calculate convex envelope of the domain
//	mvm -> domain.envelope (mvm -> dim ());

	// completion of the domain
	mvm -> completedomain (mvm -> dim ());

	// write chain complex CY to file outCY
	mvm -> writeCYtofile (CY, outCY);

	return (mvm);
}

// write a chain map to the text file.
// return: 0 = OK, -1 = mistake
int writetofile (ofstream &out, chainmap &cm)
{
	int i,j;
	int quot, prev_quot;

	cout << "\n\n";
	cout.flush ();
	cout << "Writing a chain map...     ";
	cout.flush ();

	prev_quot = 0;
	for (i = 0; i <= cm.dim (); i ++)
	{
		cout << "\n";
		cout.flush ();
		cout << "    Writing dimension " << i << "... 0 % ";
		cout.flush ();

		out << endl << "Dimension " << i << ":" << endl;

		for (j = 0; j < cm [i].l (); j ++)
		{
			out << "Argument: ";
			if (!cm [i] [j].x.write (out))
				throw "Can't write the chain map to the file.";
			out << endl;

			out << "Value: ";
			if (!cm [i] [j].y.write (out))
				throw "Can't write the chain map to the file.";
			out << endl;

			//wmove (scr,y,x);
			quot = (int) (((float) (j + 1) / (float) cm [i].l ()) * 100);
			if (quot != prev_quot)
			{
				cout << "\r    Writing dimension " << i << "... " << (int) quot << " % ";
				cout.flush ();
				prev_quot = quot;
			}
			//delay (100);

			
		}
	}
	cout << "\n\n";
	cout.flush ();
	
	return 0;
}

// the main procedure
// return: 0 = OK, -1 = error (show messages).
int chainmapp (ifstream &in, ofstream &out, ofstream &outCY)
{

	multivalmap *mvm = readfromfile (in, outCY); // read data from the input file
	chainmap cm (mvm, alg);                           // calculate the chainmap
	delete mvm;

	if (writetofile (out , cm))            // write the result to the output file
		throw "Error during writing to the output file!";
	return 0;
}

int Zp::p;
int point::spacedim;
int multivalmap::maxdim;

// -------------------------------------------------------------
// --------------------------- MAIN ----------------------------
// -------------------------------------------------------------

int main (int argc, char *argv [])
// return: 0 = OK, 1 = help shown, -1 = error.
{
	// the rank of the ring from which the coefficients are taken
	// p = 0 <=> this ring = Z
	int p1 = 0;

	// the names of files from which the multivalued map is read
	// and to which the chain map is written
	// char *inputfilename = NULL, *outputfilename = NULL, *outputCYfilename = NULL;

	int showhelp = 0;

	program_time = 0;	// added by PwP on Sep 12, 2003

	// set the algebraic algorithm as default
	alg = 1;

	// show program's title
	cout << title << endl;

	// interprete the command-line parameters
	for (int i = 1; i < argc; i ++)
		if (argv [i] [0] == '-')
			switch (argv [i] [1])
			{
				case 'h':
				case 'H':
				case '?':
					showhelp = 1;
					break;
				case 'a':
					break;
				case 'g':
					alg = 0;
					break;
			}
		else if (!inputfilename)
			inputfilename = argv [i];
		else if (!outputfilename)
			outputfilename = argv [i];
		else if (!outputCYfilename)
			outputCYfilename = argv [i];
		else if ((argc >= 5) && (!p1))
			p1 = atoi (argv [i]);
		else
			showhelp = 1;

	// show help info if any file name is missing
	if (!inputfilename || !outputfilename || !outputCYfilename)
		showhelp = 1;

	// show help info if it should be shown
	if (showhelp)
	{
		cout << helpinfo << endl;
		return 1;
	}

	if (alg)
		cout << "\nThe algebraic algorithm was chosen"; // changed by PwP
	else
		cout << "\nThe geometric algorithm was chosen"; // changed by PwP

	cout.flush ();

	Zp::setrank (p1);    // set the rank of Zp

	// open the input file and check the result
	ifstream in (inputfilename);
	if (!in)
	{
		cout << "Sorry, can't open the input file: ";
		cout << inputfilename << endl;
		return -1;
	}

	// open the output file and check the result
	ofstream out (outputfilename);
	if (!out)
	{
		cout << "Sorry, can't open the output file: ";
		cout << outputfilename << endl;
		return -1;
	}

	out << "This is a chain map generated by CHAINMAP from " <<
		inputfilename << ":" << endl;

	// open the output file for chain complex CY and check the result
	ofstream outCY (outputCYfilename);
	if (!outCY)
	{
		cout << "Sorry, can't open the output file for chain complex CY: ";
		cout << outputCYfilename << endl;
		return -1;
	}

	outCY << "These are the primitive generators of the chain complex CY, \ngenerated by CHAINMAP from " <<
		inputfilename << ":" << endl;

	int result;
	// try running the main function and catch an error message if thrown
	try
	{
		program_time = "Aborted after";	// added by PwP on Sep 12, 2003

		result = chainmapp (in, out, outCY);

		// added by PwP on Sep 12, 2003
		program_time = "Total time used:";
		program_time = 1;
		return (result);
	}
	catch (const char *msg)
	{
		cout << "ERROR: " << msg << endl;
		return -1;
	}
	catch (const std::exception &e)
	{
		cout << "ERROR: " << e. what () << endl;
		return -1;
	}
	catch (...)
	{
		cout << "ABORT: An unknown error occurred." << endl;
		return -1;
	}
} // main

/// @}

