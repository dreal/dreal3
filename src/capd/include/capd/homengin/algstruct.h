/// @addtogroup HomologyEngines
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file algstruct.h
///
/// This file defines an algebraic data structure which is used to store
/// the information about computed homology groups.
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

// Started in March 2006. Last revision: April 19, 2006.


#ifndef _CAPD_HOMENGIN_ALGSTRUCT_H_
#define _CAPD_HOMENGIN_ALGSTRUCT_H_

#include "capd/homology/config.h"
#include "capd/homology/textfile.h"
#include "capd/homology/timeused.h"
#include "capd/homology/arg.h"
#include "capd/homology/homtools.h"

#include "capd/auxil/CRef.h"
#include "capd/homologicalAlgebra/HomologySignature.h"

#include <cstdlib>
#include <ctime>
#include <new>
#include <exception>
#include <iostream>
#include <fstream>
#include <iomanip>
#include <vector>
#include <sstream>


namespace capd {
namespace homengin {

// --------------------------------------------------
// -------------- ALGEBRAIC STRUCTURE ---------------
// --------------------------------------------------

/// An algebraic structure that represents a finitely generated
/// Abelian group with gradation.
template<class euclidom>
class algstruct
{
public:
 /// The default constructor.
 algstruct ();

 /// The destructor
 ~algstruct ();

 /// Returns the number of levels of gradation stored
 /// in the structure.
 int countLevels () const;

 /// Sets a specific Betti number.
 void setBetti (int level, int number);

 /// Increases a specific Betti number.
 void addBetti (int level, int howmuch);

 /// Returns a specific Betti number.
 int getBetti (int level) const;

 /// Adds a torsion coefficient.
 void addTorsion (int level, euclidom coef);

 /// Returns a torsion coefficient.
 const euclidom &getTorsion (int level, int n) const;

 /// Says how many torsion coefficients exist at the given level.
 int countTorsion (int level) const;

 /// Describes the homology group in a human-readable way.
 std::ostream &describe (std::ostream &out) const;

 /// Shows the Betti numbers as a space-sperated sequence.
 std::ostream &showBetti (std::ostream &out) const;

private:
 /// The Betti numbers.
 std::vector<int> betti;

 /// The torsion coefficients.
 std::vector<std::vector<euclidom> > torsion;
}; /* class algstruct */

// --------------------------------------------------

template <class euclidom>
inline algstruct<euclidom>::algstruct ()
{
 return;
} /* algstruct::algstruct */

template <class euclidom>
inline algstruct<euclidom>::~algstruct ()
{
 return;
} /* algstruct::~algstruct */

// --------------------------------------------------

template <class euclidom>
inline int algstruct<euclidom>::countLevels () const
{
 int nBetti = betti. size ();
 int nTorsion = torsion. size ();
 return (nBetti > nTorsion) ? nBetti : nTorsion;
} /* algstruct::countLevels */

template <class euclidom>
inline void algstruct<euclidom>::setBetti (int level, int number)
{
 if (level < 0)
  return;
 if (number <= 0)
  return;
 for (int nBetti = betti. size (); nBetti < level; ++ nBetti)
  betti. push_back (0);
 if (static_cast<unsigned> (level) < betti. size ())
  betti [level] = number;
 else
  betti. push_back (number);
 return;
} /* algstruct::setBetti */

template <class euclidom>
inline void algstruct<euclidom>::addBetti (int level, int howmuch)
{
 if (level < 0)
  return;
 if (static_cast<unsigned> (level) < betti. size ())
  betti [level] += howmuch;
 else
  setBetti (level, howmuch);
 return;
} /* algstruct::addBetti */

template <class euclidom>
inline int algstruct<euclidom>::getBetti (int level) const
{
 if (level < 0)
  return 0;
 if (static_cast<unsigned> (level) < betti. size ())
  return betti [level];
 else
  return 0;
} /* algstruct::getBetti */

template <class euclidom>
inline void algstruct<euclidom>::addTorsion (int level, euclidom coef)
{
 if (level < 0)
  return;
 std::vector<euclidom> empty;
 for (int nTorsion = torsion. size (); nTorsion <= level; ++ nTorsion)
  torsion. push_back (empty);
 torsion [level]. push_back (coef);
 return;
} /* algstruct::addTorsion */

template <class euclidom>
inline const euclidom &algstruct<euclidom>::getTorsion (int level, int n)
 const
{
 static euclidom e;

 if ((level < 0) || (n < 0))
  return e;
 if ((static_cast<unsigned> (level) < torsion. size ()) &&
  (static_cast<unsigned> (n) < torsion [level]. size ()))
  return torsion [level] [n];
 else
  return e;
} /* algstruct::getTorsion */

template <class euclidom>
inline int algstruct<euclidom>::countTorsion (int level) const
{
 if (level < 0)
  return 0;
 if (static_cast<unsigned> (level) < torsion. size ())
  return torsion [level]. size ();
 return;
} /* algstruct::countTorsion */


// --------------------------------------------------

template <class euclidom>
inline const char *ringsymbol ()
{
 return euclidom::ringsymbol ();
} /* ringsymbol */

template <>
inline const char *ringsymbol<int> ()
{
 return "Z";
} /* ringsymbol */

template <class euclidom>
std::ostream &algstruct<euclidom>::describe (std::ostream &out) const
{
 int nBetti = betti. size ();
 int nTorsion = torsion. size ();
 for (int i = 0; (i < nBetti) || (i < nTorsion); ++ i)
 {
  if (i)
   out << ", ";
  else
   out << '(';
  bool zero = true;
  if ((i < nBetti) && (betti [i] > 0))
  {
   zero = false;
   out << ringsymbol<euclidom> ();
   if (betti [i] > 1)
    out << '^' << betti [i];
   if ((i < nTorsion) && (torsion [i]. size ()))
    out << " + ";
  }
  if (i < nTorsion)
  {
   std::vector<euclidom> tor = torsion [i];
   for (unsigned j = 0; j < tor. size (); ++ j)
   {
    zero = false;
    if (j)
     out << " + ";
    out << ringsymbol<euclidom> () <<
     '_' << tor [j];
   }
  }
  if (zero)
   out << 0;
 }
 if (nBetti || nTorsion)
  out << ')';
 else
  out << '0';
 return out;
} /* algstruct::describe */

template <class euclidom>
std::ostream &algstruct<euclidom>::showBetti (std::ostream &out) const
{
 bool first = true;
 for (std::vector<int>::const_iterator it = betti. begin ();
  it != betti. end (); ++ it)
 {
  if (first)
   first = false;
  else
   out << ' ';
  out << *it;
 }
 return out;
} /* algstruct::showBetti */

/// Outputs the structure to the output stream in a human-readable form.
template <class euclidom>
inline std::ostream &operator << (std::ostream &out,
 const algstruct<euclidom> &s)
{
 return s. describe (out);
} /* operator << */

/// Translates the PP's homology representation to the algebraic structure.
template <class euclidom>
void hom2struct (const capd::homology::chain<euclidom> *hom, int maxlevel,
 algstruct<euclidom> &h)
{
 for (int q = 0; q <= maxlevel; ++ q)
 {
  const capd::homology::chain<euclidom> &c = hom [q];
  for (int i = 0; i < c. size (); ++ i)
  {
   const euclidom &e = c. coef (i);
   if (e. delta () == 1)
    h. addBetti (q, 1);
   else
    h. addTorsion (q, e);
  }
 }
 return;
} /* hom2struct */

template <class euclidom>
void sign2struct (const CRef<HomologySignature<int> > &homSignCR,
 algstruct<euclidom> &h)
{
 int dim = (*homSignCR). topDim ();
 for (int i = 0; i <= dim; ++ i)
 {
  h. setBetti (i, (*homSignCR). bettiNumber (i));
  FGAGrpSignature<int> &s = (*homSignCR) [i];
  for (int j = 0; j < s. numberOfTorsionCoefs (); ++ j)
  {
   euclidom e;
   e = s. torsionCoef (j);
   h. addTorsion (i, e);
  }
 }
 return;
} /* sign2struct */


} // namespace homengin
} // namespace capd

#endif // _CAPD_HOMENGIN_ALGSTRUCT_H_

/// @}

