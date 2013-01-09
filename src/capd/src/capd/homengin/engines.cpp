/// @addtogroup HomologyEngines
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file engines.cpp
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


#include <algorithm>
#include <typeinfo>
#include "capd/homengin/engines.h"
#include "capd/multiEngHom/MultiEngHomT.h"

using namespace capd::homology;


// variables from the "chom" library
// (this is ugly, but I couldn't find them in any headear file)
extern int periodic;
extern int SUBDIVISIONS;
void reduce (char *cubits, unsigned long xmax, unsigned long ymax,
 unsigned long zmax);
void compute_homology (char *cubits, unsigned long xmax, unsigned long ymax,
 unsigned long zmax, int Betti []);


namespace capd {
namespace homengin {

// --------------------------------------------------
// ---------------- ABSTRACT ENGINE -----------------
// --------------------------------------------------

engine::enginelist engine::engines;

// --------------------------------------------------

class Compare_Engines
{
public:
 int operator () (const engine *e1, const engine *e2) const
 {
  return (std::strcmp (e1 -> name (), e2 -> name ()) < 0);
 }
}; /* class Compare_Engines */

std::ostream &engine::showlist (std::ostream &out,
 const engine::enginelist &_elist)
{
 // sort the list of engines in the alphabetical order
 engine::enginelist elist (_elist);
 std::sort (elist. begin (), elist. end (), Compare_Engines ());

 out << "Available homology engines "
  "(listed in the alphabetical order):\n";
 for (engine::enginelist::const_iterator x = elist. begin ();
  x != elist. end (); ++ x)
 {
  out << '\n';
  const engine *e = *x;
  out << "<<< " << e -> name () << " >>>\n";
  e -> describe (out);
 }
 return out;
} /* engine::showlist */

const engine *engine::find (const cubfile *X, const cubfile *Y,
 const engine::enginelist &elist)
{
 sout << "Determining the most appropriate homology engine...\n";

 // first run: find all the engines that can possibly be used
 engine::enginelist candidates;
 for (engine::enginelist::const_iterator x = elist. begin ();
  x != elist. end (); ++ x)
 {
  const engine *e = *x;
  if (!e -> dimsupported (X -> dim ()))
  {
   slog << "- " << e -> name () <<
    " does not support dimension " <<
    X -> dim () << ".\n";
   continue;
  }
  if (Y && !e -> relative ())
  {
   slog << "- " << e -> name () <<
    " does not support relative homology.\n";
   continue;
  }
  if (X -> spacewrapping () && !e -> spacewrapping ())
  {
   slog << "- " << e -> name () <<
    " does not support space wrapping.\n";
   continue;
  }
  if (X -> elementary () && !e -> elementary ())
  {
   slog << "- " << e -> name () <<
    " does not support elementary cubes.\n";
   continue;
  }
  candidates. push_back (e);
 }

 slog << "The engine(s) upon consideration are:";
 for (engine::enginelist::const_iterator x = candidates. begin ();
  x != candidates. end (); ++ x)
 {
  const engine *e = *x;
  slog << ' ' << e -> name ();
 }
 slog << ".\n";

 // second run: find the best engine from all the candidates
 int countgood = candidates. size ();
 const engine *best = 0;
 int bestmem = 0;
 for (engine::enginelist::const_iterator x = candidates. begin ();
  x != candidates. end (); ++ x)
 {
  const engine *e = *x;

  // if there is only one engine suitable, don't verify it
  if (!best && (countgood == 1))
  {
   slog << "+ " << e -> name () <<
    " is the only choice.\n";
   best = e;
   break;
  }

  // analyze the memory usage of this engine
  int mem = e -> memory (*X);
  if ((mem < 0) || (mem > 1024 * 1024 * 1024))
  {
   slog << "- " << e -> name () <<
    " needs too much memory";
   if (mem < 0)
    slog << " (over 2GB).\n";
   else
    slog << " (" << mem << " bytes).\n";
   -- countgood;
   continue;
  }

  // if no engine was good so far, take this one
  if (!best)
  {
   slog << "+ " << e -> name () << " is the first "
    "choice (estim. memory usage: " << mem <<
    " bytes).\n";
   best = e;
   bestmem = mem;
   continue;
  }

  // if this engine uses far more memory, discard it
  if (mem && bestmem && (((mem / 2 > bestmem) &&
   (bestmem >= 256 * 1024 * 1024)) ||
   (mem / 128 > bestmem)))
  {
   slog << "- " << e -> name () <<
    " would use much more memory (approx. " <<
    mem << " bytes).\n";
   continue;
  }

  // if this engine is much faster, use it
  if (best -> speed () < e -> speed ())
  {
   slog << "+ " << e -> name () << " is faster (estim. "
    "memory usage: " << mem << " bytes).\n";
   best = e;
   bestmem = mem;
   continue;
  }

  // if this engine uses far less memory, use it
  if (mem && bestmem && (((mem < bestmem / 8) &&
   (bestmem >= 256 * 1024 * 1024)) ||
   (mem < bestmem / 128)))
  {
   slog << "+ " << e -> name () <<
    " uses much less memory (approx. " <<
    mem << " bytes).\n";
   best = e;
   bestmem = mem;
   continue;
  }

  // reject this engine
  slog << "- " << e -> name () << " would be slower "
   "(estim. memory usage: " << mem << " bytes).\n";
 }

 // return the best homology engine found
 if (best)
 {
  sout << "Using the homology engine '" <<
   best -> name () << "'.\n";
  return best;
 }

 // if no good homology engine found, throw an exception
 sout << "Failed.\n";
 throw "Unable to find a suitable homology engine.";
} /* engine::find */

const engine *engine::find (const char *name, const engine::enginelist &elist)
{
 for (engine::enginelist::const_iterator x = elist. begin ();
  x != elist. end (); ++ x)
 {
  const engine *e = *x;
  if (!strcmp (e -> name (), name))
  {
   sout << "Using the homology engine '" <<
    e -> name () << "'.\n";
   return e;
  }
 }
 throw "Unable to find a homology engine with the requested name.";
} /* engine::find */


// --------------------------------------------------
// ------------------- PP ENGINE --------------------
// --------------------------------------------------

static void setwrapping (const cubfile &x)
{
 // create a temporary wrapping table
 const int d = Cube::MaxDim;
 int iwraptable [d];
 int dim = x. dim ();
 if (dim > d)
  throw "Space dimension too high for wrapping.";

 // retrieve the wrapping information and translate integers
 x. spacewrapping (iwraptable);
 coordinate wraptable [d];
 for (int i = 0; i < d; ++ i)
  wraptable [i] = (i < dim) ?
   static_cast<coordinate> (iwraptable [i]) : 0;

 // set the space wrapping as requested to
 PointBase::setwrapping (wraptable);
 return;
} /* setwrapping */

int PPengine::memory (const cubfile &X) const
{
 try
 {
  const cublistfile &Y =
   dynamic_cast<const cublistfile &> (X);
  std::ifstream test (Y. filename ());
  test. seekg (0, std::ios_base::end);
  return static_cast<int> (test. tellg () + test. tellg () +
   test. tellg ());
 }
 catch (std::bad_cast)
 {
 }
 return X. count () * (X. dim () *
  sizeof (coordinate) + 8);
} /* PPengine::memory */

void PPengine::homology (const cubfile &x, algstruct<integer> &h) const
{
 // set space wrapping if necessary
 if (x. spacewrapping ())
  setwrapping (x);

 // prepare the data structures to store the computed homology
 Chain *hom = 0;
 int maxlevel = -1;

 if (x. elementary ())
 {
  // read the set of cubical cells and compute its homology
  CubicalComplex X;
  sout << "Reading cubical cells from '" << x. filename () <<
   "'...\n";
  x. readcubes (X);
  sout << "Adding faces of cells to create "
   "a cellular complex...\n";
  X. addboundaries ();
  sout << "Time used so far: " << program_time << ".\n";
  sout << "Computing homology...\n";
  maxlevel = Homology (X, "X", hom);
 }
 else
 {
  // read the set of cubes and compute its homology
  SetOfCubes X;
  sout << "Reading cubes from '" << x. filename () << "'...\n";
  x. readcubes (X);

  sout << "Time used so far: " << program_time << ".\n";
  sout << "Computing homology...\n";
  maxlevel = Homology (X, "X", hom);
 }

 // translate the result and exit
 hom2struct (hom, maxlevel, h);
 delete [] hom;
 return;
} /* PPengine::homology */

void PPengine::homology (const cubfile &x, const cubfile &y,
 algstruct<integer> &h) const
{
 // set space wrapping if necessary
 if (y. spacewrapping ())
  setwrapping (y);
 if (x. spacewrapping ())
  setwrapping (x);

 // read the sets of cubes from the corresponding files
 sout << "Reading cubes from '" << x. filename () << "'...\n";
 SetOfCubes X;
 x. readcubes (X);
 sout << "Reading cubes from '" << y. filename () << "'...\n";
 SetOfCubes Y;
 y. readcubes (Y);
 sout << "Time used so far: " << program_time << ".\n";

 // compute homology
 Chain *hom;
 sout << "Computing homology...\n";
 int maxlevel = Homology (X, "X", Y, "Y", hom);

 // translate the result and exit
 hom2struct (hom, maxlevel, h);
 delete [] hom;
 return;
} /* PPengine::homology */

std::ostream &PPengine::describe (std::ostream &out) const
{
 out << "\
This is the homology engine programmed in 1997-2009 by Pawel Pilarczyk.\n\
It is optimized for small memory usage, and turns out to be especially\n\
suitable for medium-sized sets of cubes scattered widely in the space.\n\
It is capable of computing relative homology, and the dimensions supported\n\
range from 1 to " << Cube::MaxDim <<
", although practically one shouldn't use dim > 10.\n\
The coordinates of the cubes must fit in " <<
sizeof (coordinate) << "-byte signed integers.\n\
This engine supports space wrapping, a.k.a. periodic boundary conditions.\n\
The homology is computed over the ring of integers, so the torsion\n\
information is not lost (which may be important for dim > 3).\n\
In addition to full cubical sets, this engine also supports cubical sets\n\
built of lower-dimensional cubical cells (faces of full cubes).\n";
 return out;
} /* PPengine::describe */

PPengine PPengine::eng;


// --------------------------------------------------
// ------------------- BK ENGINE --------------------
// --------------------------------------------------

int BKengine::memory (const cubfile &X) const
{
 // return the volume of the set of cubes (in bytes)
 int vol = X. volume (8, true);
 if (vol < 0)
  return -1;
 else
  return (vol);
} /* BKengine::memory */

void BKengine::homology (const cubfile &x, algstruct<integer> &h) const
{
 // make sure that the embedding dimension is correct
 if (x. dim () != DIM)
  throw "Wrong dimension for the BK* engine, as compiled.";

 // set space wrapping if necessary
 if (x. spacewrapping ())
 {
  serr << "WARNING: Space wrapping may not work correctly "
   "for the BK engine.\n";
  periodic = 1;
 }

 // read the set of cubes from the corresponding file
 int *sizes = 0;
 char *bytes = 0;
 sout << "Reading cubes from '" << x. filename () << "'...\n";
 x. readcubes (sizes, bytes, sizeof (long), true);

 // round the first size up to the size of long int measured in bits
 const int mask = (sizeof (long) << 3) - 1;
 if (sizes [0] & mask)
  sout << "NOTE: Increasing the X-size to a multiple of " <<
   (sizeof (long) << 3) << ".\n";
 sizes [0] += mask;
 sizes [0] &= ~mask;

 // determine the maximal size
 int maxsize = sizes [0];
 for (int i = 1; i < x. dim (); ++ i)
  if (sizes [0] < sizes [i])
   sizes [0] = sizes [i];

 // determine the level of subdivisions
 int depth = 1;
 while ((1 << depth) < maxsize)
  ++ depth;
 SUBDIVISIONS = depth;

 // make sure that the size of the set is the same in each direction
 if (maxsize != (1 << depth))
  sout << "WARNING: The size of the set of cubes is not "
   "a power of 2.\n";
 for (int i = 1; i < x. dim (); ++ i)
 {
  if (sizes [i] != sizes [0])
  {
   sout << "NOTE: The size of the cube box is ";
   for (int j = 0; j < x. dim (); ++ j)
    sout << (j ? " x " : "") << sizes [j];
   sout << ".\n";
   throw "The size of the set of cubes must be "
    "the same in all directions.";
  }
 }
 sout << "Time used so far: " << program_time << ".\n";

 // reduce the set of cubes with the use of the lookup table
 if (useLookupTable)
 {
  readAcyclicConfigs ();
  sout << "Reducing the set of cubes with the use "
   "of a lookup table...\n";
  reduce (bytes, sizes [0], sizes [1], sizes [2]);
 }

 // prepare the data structures to store the computed homology
 sout << "Computing homology...\n";
 int betti [DIM + 1];
 compute_homology (bytes, sizes [0], sizes [1], sizes [2], betti);

 // translate the result and exit
 for (int i = 0; i <= DIM; ++ i)
  h. setBetti (i, betti [i]);
 return;
} /* BKengine::homology */

std::ostream &BKengine::describe (std::ostream &out) const
{
 out << "\
This is the homology engine programmed by Bill Kalies.\n\
It is optimized for very small memory usage, and processes full cubes\n\
encoded in the form of a binary tree (sorted bitcodes).\n\
This engine supports space wrapping a.k.a. periodic boundary conditions,\n\
but only if the wrapping size corresponds to the binary cube area.\n\
In this program, it is available for dimension " << DIM <<
" only (to support\n\
other dimensions, one must re-compile the program).\n\
Note: The version of the engine used here works directly with bitmaps.\n";
 return out;
} /* BKengine::describe */

BKengine BKengine::eng;


// --------------------------------------------------
// ------------------ BK_LT ENGINE ------------------
// --------------------------------------------------

std::ostream &BK_LTengine::describe (std::ostream &out) const
{
 out << "\
This is the homology engine programmed by Bill Kalies.\n\
This version uses the lookup table for cubical neighborhoods (programmed\n\
by Marcio Gameiro and Vidit Nanda) to reduce the set of cubes\n\
prior to homology computation with the BK engine.\n\
In this program, it is available for dimension " << DIM <<
" only (to support\n\
other dimensions, one must re-compile the program).\n";
 return out;
} /* BK_LTengine::describe */

BK_LTengine BK_LTengine::eng;


// --------------------------------------------------
// -------------- A GENERAL MM ENGINE ---------------
// --------------------------------------------------

// specific types of cubical sets
typedef CubSetT <EuclBitSetT <BitSetT <BitmapT <unsigned long int> >, 2> >
 BCubSet2;
typedef CubSetT <EuclBitSetT <BitSetT <BitmapT <unsigned long int> >, 3> >
 BCubSet3;
typedef CubSetT <EuclBitSetT <BitSetT <BitmapT <unsigned long int> >, 4> >
 BCubSet4;

// specific types of cellular sets
typedef CubCellSetT <EuclBitSetT <BitSetT <BitmapT <unsigned long int> >, 2> >
 BCubCelSet2;
typedef CubCellSetT <EuclBitSetT <BitSetT <BitmapT <unsigned long int> >, 3> >
 BCubCelSet3;
typedef CubCellSetT <EuclBitSetT <BitSetT <BitmapT <unsigned long int> >, 4> >
 BCubCelSet4;

int MMengine::memory (const cubfile &X) const
{
 // return the volume of the set of cubes (in bytes)
 int vol = X. volume (8);
 if (vol < 0)
  return -1;
 else
  return (vol);
} /* MMengine::memory */

// --------------------------------------------------

// The type of a typical function that computes homology.
//typedef CRef<HomologySignature<int> > (*homfunction) (CRef<BCubSet>);
//typedef CRef<HomologySignature<int> > (*homfunction2) (CRef<BCubSet2>);
//typedef CRef<HomologySignature<int> > (*homfunction3) (CRef<BCubSet3>);
//typedef CRef<HomologySignature<int> > (*homfunction4) (CRef<BCubSet4>);

/// A wrapper for the above-defined typical function call.
template <class BCubSet>
void MMhomology (const cubfile &x, algstruct<integer> &h,
 CRef<HomologySignature<int> > (*f) (CRef<BCubSet>))
{
 // make sure that the embedding dimension is correct
// if (x. dim () != embeddingDim)
//  throw "Wrong dimension for the MM* engine, as compiled.";

 // read the set of cubes from the corresponding file
 int *sizes = 0;
 char *bytes = 0;
 sout << "Reading cubes from '" << x. filename () << "'...\n";
 x. readcubes (sizes, bytes, sizeof (long));
 const int mask = (sizeof (long) << 3) - 1;

 // round the first size up to the size of long measured in bits
 sizes [0] += mask;
 sizes [0] &= ~mask;

 // create a corresponding binary set of cubes
 CRef<BCubSet> cubSetCR (new BCubSet (sizes, bytes));

 // show the cumulative computation time used up to this point
 sout << "Time used so far: " << program_time << ".\n";

 // compute homology
 sout << "Computing homology...\n";
 CRef<HomologySignature<int> > homSignCR = f (cubSetCR);

 // release memory allocated for the sizes and bytes
// delete [] bytes;
// delete [] sizes;

 // translate the result and exit
 sign2struct (homSignCR, h);
 return;
} /* MMhomology */


// --------------------------------------------------
// ------------------ MM_CR ENGINE ------------------
// --------------------------------------------------

void MM_CRengine::homology (const cubfile &x, algstruct<integer> &h) const
{
 // warn the user that space wrapping is not supported
 if (x. spacewrapping ())
 {
  capd::homology::sout << "WARNING: Space wrapping "
   "is not supported by the MM_CR engine.\n";
 }

/*
 The modifications (marked // MM) in this method caused by the fact                  // MM
 that the updated CubSetFunctors class has two overloaded methods                    // MM
 named HomologyViaRepSetReductions  (MM)                                             // MM
*/
 typedef CRef<HomologySignature<int> > (*homSignViaRepSetReductions2Type) (CRef<BCubSet2>); // MM
 homSignViaRepSetReductions2Type homSignViaRepSetReductions2Ptr=                      // MM
  CubSetFunctors<BCubSet2,BCubCelSet2>::HomSignViaRepSetReductions;            // MM
 typedef CRef<HomologySignature<int> > (*homSignViaRepSetReductions3Type) (CRef<BCubSet3>); // MM
 homSignViaRepSetReductions3Type homSignViaRepSetReductions3Ptr=                      // MM
  CubSetFunctors<BCubSet3,BCubCelSet3>::HomSignViaRepSetReductions;            // MM
 typedef CRef<HomologySignature<int> > (*homSignViaRepSetReductions4Type) (CRef<BCubSet4>); // MM
 homSignViaRepSetReductions4Type homSignViaRepSetReductions4Ptr=                      // MM
  CubSetFunctors<BCubSet4,BCubCelSet4>::HomSignViaRepSetReductions;            // MM

 if (x. dim () > 3)
  capd::homology::sout << "Warning: The torsion coefficients "
   "will not be computed.\n";
 if (x. dim () == embeddingDim)
 {
  typedef CRef<HomologySignature<int> > (*homSignViaRepSetReductionsType) (CRef<BCubSet>);  // MM
  homSignViaRepSetReductionsType homSignViaRepSetReductionsPtr=                       // MM
   CubSetFunctors<BCubSet,BCubCelSet>::HomSignViaRepSetReductions;             // MM
  MMhomology (x, h, homSignViaRepSetReductionsPtr);                                   // MM
/*
  MMhomology (x, h, CubSetFunctors <BCubSet, BCubCelSet>::
   HomologyViaRepSetReductions);
*/
 }
 else switch (x. dim ())
 {
 case 2:
  MMhomology (x, h, homSignViaRepSetReductions2Ptr);                                  // MM
/*                                                                                                  // MM
  MMhomology (x, h, CubSetFunctors <BCubSet2, BCubCelSet2>::                          // MM
   HomologyViaRepSetReductions);                                               // MM
*/
  break;
 case 3:
  MMhomology (x, h, homSignViaRepSetReductions3Ptr);                                  // MM
/*                                                                                                  // MM
  MMhomology (x, h, CubSetFunctors <BCubSet3, BCubCelSet3>::                          // MM
   HomologyViaRepSetReductions);                                               // MM
*/
  break;
 case 4:
  MMhomology (x, h, homSignViaRepSetReductions4Ptr);                                  // MM
/*                                                                                                  // MM
  MMhomology (x, h, CubSetFunctors <BCubSet4, BCubCelSet4>::                          // MM
   HomologyViaRepSetReductions);                                               // MM
*/
  break;
 }
 return;
} /* MM_CRengine::homology */

std::ostream &MM_CRengine::describe (std::ostream &out) const
{
 out << "\
This is the homology engine that uses the coreduction algorithm,\n\
programmed in 2006 by Marian Mrozek.\n\
It works directly with bitmaps and is extremely fast, but may use\n\
quite a lot of memory. It turns out to be especially suitable for\n\
sets of cubes packed densely within the boundaries of a medium-sized box.\n\
In this program, it is available for dimensions ";
 if (embeddingDim < 2)
  out << embeddingDim << ", ";
 out << "2, 3, 4";
 if (embeddingDim > 4)
  out << ", " << embeddingDim;
 out << " \
(to support\n\
other dimensions, one must change the constant 'embeddingDim' in the file\n\
include/homologicalAlgebra/embeddingDim.h and re-compile the program).\n";
 return out;
} /* MM_CRengine::describe */

MM_CRengine MM_CRengine::eng;


// --------------------------------------------------
// ------------------ MM_AR ENGINE ------------------
// --------------------------------------------------

void MM_ARengine::homology (const cubfile &x, algstruct<integer> &h) const
{
 // warn the user that space wrapping is not supported
 if (x. spacewrapping ())
 {
  capd::homology::sout << "WARNING: Space wrapping "
   "is not supported by the MM_AR engine.\n";
 }

 if (x. dim () > 3)
  capd::homology::sout << "Warning: The torsion coefficients "
   "will not be computed.\n";
 if (x. dim () == embeddingDim)
 {
  MMhomology (x, h, CubSetFunctors <BCubSet, BCubCelSet>::
   HomologyViaAlgebraicReductions);
 }
 else switch (x. dim ())
 {
 case 2:
  MMhomology (x, h, CubSetFunctors <BCubSet2, BCubCelSet2>::
   HomologyViaAlgebraicReductions);
  break;
 case 3:
  MMhomology (x, h, CubSetFunctors <BCubSet3, BCubCelSet3>::
   HomologyViaAlgebraicReductions);
  break;
 case 4:
  MMhomology (x, h, CubSetFunctors <BCubSet4, BCubCelSet4>::
   HomologyViaAlgebraicReductions);
  break;
 }
 return;
} /* MM_ARengine::homology */

std::ostream &MM_ARengine::describe (std::ostream &out) const
{
 out << "\
This is the homology engine that uses the algebraic reductions algorithm\n\
(Kaczynski-Mrozek-Slusarek), programmed in 2006 by Marian Mrozek.\n\
It works directly with bitmaps, but it is relatively slow, because it does\n\
not perform any geometric reductions. Nevertheless, this engine is useful\n\
as a reference algorithm for speed improvement comparisons.\n\
In this program, it is available for dimension " << embeddingDim <<
" only (to support\n\
other dimensions, one must re-compile the program).\n";
 return out;
} /* MM_ARengine::describe */

MM_ARengine MM_ARengine::eng;


// --------------------------------------------------
// ----------------- MM_ASLT ENGINE -----------------
// --------------------------------------------------

void MM_ASLTengine::homology (const cubfile &x, algstruct<integer> &h) const
{
 // warn the user that space wrapping is not supported
 if (x. spacewrapping ())
 {
  capd::homology::sout << "WARNING: Space wrapping "
   "is not supported by the MM_ASLT engine.\n";
 }

 if (x. dim () != 3)
  throw "Trying to use the ASLT engine "
   "in dimension different from 3.";
 readAcyclicConfigs ();
 typedef CRef<HomologySignature<int> > (*HomologyViaAcyclicSubspaceLTD3Type) (CRef<BCubSet3>); // MM
 HomologyViaAcyclicSubspaceLTD3Type HomologyViaAcyclicSubspaceLTD3Ptr=                   // MM
  CubSetFunctors<BCubSet3,BCubCelSet3>::HomologyViaAcyclicSubspaceLTD3;           // MM
 MMhomology (x, h, HomologyViaAcyclicSubspaceLTD3Ptr);
 return;
} /* MM_ASLTengine::homology */

std::ostream &MM_ASLTengine::describe (std::ostream &out) const
{
 out << "\
This is the homology engine that uses the acyclic subset construction\n\
to reduce the size of the set of cubes, and also makes use of the\n\
lookup tables for 3-dimensional neighborhood configurations of cubes.\n\
It works directly with bitmaps and is quite fast.\n\
It is available for dimension 3 only.\n";
 return out;
} /* MM_ASLTengine::describe */

MM_ASLTengine MM_ASLTengine::eng;


} // namespace homengin
} // namespace capd

/// @}

