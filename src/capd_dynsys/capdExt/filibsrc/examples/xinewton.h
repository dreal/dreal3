/*                                                                           
**  fi_lib++  --- A fast interval library (Version 2.0)                     
**                                                                  
**  Copyright (C) 2001:                                                        
**                                                     
**  Werner Hofschuster, Walter Kraemer                               
**  Wissenschaftliches Rechnen/Softwaretechnologie (WRSWT)  
**  Universitaet Wuppertal, Germany                                           
**  Michael Lerch, German Tischler, Juergen Wolff von Gudenberg       
**  Institut fuer Informatik                                         
**  Universitaet Wuerzburg, Germany                                           
** 
**  This library is free software; you can redistribute it and/or
**  modify it under the terms of the GNU Library General Public
**  License as published by the Free Software Foundation; either
**  version 2 of the License, or (at your option) any later version.
**
**  This library is distributed in the hope that it will be useful,
**  but WITHOUT ANY WARRANTY; without even the implied warranty of
**  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
**  Library General Public License for more details.
**
**  You should have received a copy of the GNU Library General Public
**  License along with this library; if not, write to the Free
**  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307 USA
*/
//
// TODO
//
// Def.Param. für ForwardContainer = vector<interval>
//
// Interface für allZeros so, daß autodiff verwendendet werden kann, aber 
// gleichzeitig auch Fkt.zeiger
//
//

#ifndef _XINEWTON_H
#define _XINEWTON_H

#include <limits.h>
#include <stack>
#include <vector>

#include "xinterval.h"

using std::stack;
using std::vector;
using std::ostream;
using std::endl;
using std::cout;

namespace xinewton 
{

// -------------------------------------------------------------------------
// DEBUGGING
// 
// If XINEWTON_DEBUG is defined, details of the computations in
// allZeros is written to the file 'xinewto.deb'
// -------------------------------------------------------------------------
#ifdef XINEWTON_DEBUG
#include <fstream>
ofstream dout("xinewton.deb");
#endif



// -------------------------------------------------------------------------
// Class Enclosure<interval>
//
// Class to describe general enclosures.
// -------------------------------------------------------------------------
template <typename interval>
class Enclosure 
{
public:
  interval x;  // the enclosure
  bool unique; // uniqueness information
};



// -------------------------------------------------------------------------
// Function verificationStep(f, df, zero)
//
// Try to verify a found enclosure 'zero'.
// -------------------------------------------------------------------------
template <class UnaryFunction1, 
          class UnaryFunction2,
          class interval>
void verificationStep(UnaryFunction1 f, UnaryFunction2 df,
		      Enclosure<interval> &zero) 
{
  const int kmax = 10; 
  int k = 0;

  interval xIn = zero.x;
  interval xOld, dfx;
  
  double c;
  double eps = 0.25;
  
  while (!zero.unique && k < kmax) {
    xOld = blow(zero.x, eps);
    dfx = df(zero.x); 
    if (in(0.0, dfx)) 
      break;
    k++;
    c = mid(xOld);
    zero.x = c - f(c) / dfx;
    if (disjoint(zero.x, xOld)) 
      break;
    zero.unique = interior(zero.x, xOld);
    zero.x = intersect(zero.x, xOld);
    if (zero.x == xOld) 
      eps=eps*8.0;
  }
  
  if (!zero.unique) 
    zero.x = xIn;
}



// -------------------------------------------------------------------------
// Function tryBisect(x, y, c) 
//
// Try to bisect interval 'x' at its midpoint 'c'. Returns true iff the 
// bisection was actually performed.
//
// The bisection
//   x = [ inf(x), c ]
//   y = [ c, sup(x) ]
// is performed only if c lies in the interior of x.
// -------------------------------------------------------------------------

template <class interval>
bool tryBisect(interval &x, interval &y, double c) {
  if (c == x.inf() || c == x.sup())
    return false;
  else {
    y = interval(c, x.sup());
    x = interval(x.inf(), c);
    return true;
  }
}



// -------------------------------------------------------------------------
// Function allZeros(f, df, x, eps, list, maxZeros)
//
// Takes an interval function 'f' and its derivative 'df' and tries to 
// enclose all zeros of 'f' in the start interval 'x'. The enclosures are 
// stored in increasing order in 'list'. The relative accuracy of the 
// method is given by the parameter 'eps'. An upper bound 'maxZeros' of 
// zeros to be found can be given.
//
// The function returns an error code:
//   xinNoError: no error occured.
//   xinNotAllZerosFound: method stopped due to the user limit 'maxZeros'.
//   xinAccuracyUnfeasable: the given accuracy could not be reached.
// Several errors are combined with logical and.
// -------------------------------------------------------------------------

enum XINewtonError { xinNoError, xinNotAllZerosFound, 
		     xinAccuracyUnfeasable };


template <class UnaryFunction1, 
          class UnaryFunction2, 
          class interval, 
          class ForwardContainer>
XINewtonError allZeros(UnaryFunction1 f, UnaryFunction2 df,
		       interval x, double eps,
		       ForwardContainer &list,
		       unsigned int maxZeros = UINT_MAX) 
{
#ifdef XINEWTON_DEBUG
  dout << endl
       << "----------------------" << endl
       << "Start of newton method" << endl
       << "----------------------" << endl << endl;
#endif

  XINewtonError errorCode = xinNoError;

  bool stop, maxAccuracy;

  unsigned int numZeros = 0;

  interval V1, V2;
  ExtIntersectInfo info;  
  Xinterval<interval> z;
  double c;

  Enclosure<interval> zero;
  bool unique;

  // initialize stack of work intervals with starting interval x
  stack<interval> work;
  work.push(x);

  // adjust eps if necessary
  if (eps <= 0.0) {
    eps = 1e-15;

#ifdef XINEWTON_DEBUG
    dout << "eps <= 0.0 ! Adjusting it to 1e-15." << endl << endl;
#endif
  
  }
  
  
  // main loop
  while (!work.empty()) {

    if (numZeros == maxZeros) {
      
#ifdef XINEWTON_DEBUG
      dout << "Maximum number of " << maxZeros << " zeros reached. " 
	   << "Method stopped." << endl << endl;
#endif    

      errorCode = xinNotAllZerosFound;
      break;
    }
    

    stop = false;
    maxAccuracy = false;
    unique = false;

#ifdef XINEWTON_DEBUG
    bool stagnated = false;
#endif
    
    // get next interval from stack
    x = work.top();
    work.pop();

#ifdef XINEWTON_DEBUG
    dout << endl
	 << endl << "New search interval from stack" << endl
	 << "------------------------------" << endl
	 << "x = " << x << endl;
    x.bitImage(dout);
    dout << endl;
#endif

    // Newton iteration
    while (in(0.0, f(x)) && relDiam(x) > eps && !stop && !maxAccuracy) {
	
      // Newton step
      c = mid(x);
      z = c - f(c) % df(x);
      info = extIntersect(x, z, V1, V2);

#ifdef XINEWTON_DEBUG
      dout << endl << "Next Newton step:" << endl
	   << "-----------------" << endl
	   << "x        = " << x << endl
	   << "mid(x)   = " << c << endl;
      Double::bitImage(c, dout);
      dout << "f(mid(x))= " << f(c) << endl
	   << "df(x)    = " << df(x) << endl
	   << "N(x) & x = V1 | V2 with" << endl
	   << "V1       = ";
      if (info == EmptyIntv)
	dout << "[ EMPTY ]" << endl;
      else
	dout << V1 << endl;
      dout << "V2       = ";
      if (info != DoubleIntv)
	dout << "[ EMPTY ]" << endl;
      else
	dout << V2 << endl;
#endif

      // stagnation => try bisection
      if (info != eiEmptyinterval) {
	if (V1 == x) {

#ifdef XINEWTON_DEBUG
	  stagnated = true;
#endif
	  maxAccuracy = !tryBisect(V1, V2, c);
	  if (!maxAccuracy)
	    info = eiDoubleinterval;
	}

	else if (info != eiSingleinterval && V2 == x) {

#ifdef XINEWTON_DEBUG
	  stagnated = true;
#endif

	  maxAccuracy = !tryBisect(V2, V1, c);
	  if (!maxAccuracy)
	    info = eiDoubleinterval;
	}
      }
	
      else {

	// V1 and V2 are empty. Nevertheless, x may contain a zero, if x
	// is (partially) outside the domain of f 
	  
	if (in(0.0, f(x))) {
	  // Try bisection then.
	    
#ifdef XINEWTON_DEBUG
	  dout << endl 
	       << "V1 and V2 are empty, but 0.0 in f(x). Trying bisection."
	       << endl;
#endif	    

	  V1 = x;
	  if (tryBisect(V1, V2, c)) {
	    info = eiDoubleinterval;

#ifdef XINEWTON_DEBUG
	    dout << endl
		 << "Bisection succsessfull. New values:" << endl
		 << "V1 = " << V1 << endl 
		 << "V2 = " << V2 << endl;
#endif

	  }
	  else
	    maxAccuracy = true;
	}
      }
	

#ifdef XINEWTON_DEBUG
      if (stagnated)
	dout << endl 
	     <<"Newton iteration stagnated. Trying bisection." << endl;
#endif

      // stop iteration if maximum accuracy is reached
      if (maxAccuracy) {
#ifdef XINEWTON_DEBUG
	dout << endl
	     << "STOP: bisection not successfull because maximum accuracy "
	     << "is reached." << endl;
	stagnated = false;
#endif
	errorCode = xinAccuracyUnfeasable;
	continue;
      }

      else {

#ifdef XINEWTON_DEBUG
	if (stagnated) {
	  dout << endl
	       << "Bisection successfull. New values:" << endl
	       << "V1 = " << V1 << endl 
	       << "V2 = " << V2 << endl;
	  stagnated = false;
	}
#endif
	  
      }
	
      if (info == eiEmptyinterval) {
	// both V1 and V2 are empty !
	stop = true;

#ifdef XINEWTON_DEBUG
	dout << endl 
	     << "STOP: no zero found since both V1 and V2 are empty." 
	     << endl << "f(x) = " << f(x)
	     << endl;
#endif	  

      }

      else {
	if (info == eiDoubleinterval) {

#ifdef XINEWTON_DEBUG
	  dout << endl 
	       << "Pushing V2 on work stack." << endl;
	    
#endif

	  work.push(V2);
	  unique = false;
	}

	else 
	  unique = unique || interior(V1, x);
	  
	x = V1;
      }
	
#ifdef XINEWTON_DEBUG
      if (relDiam(x) <= eps)
	dout << endl 
	     << "STOP: desired accuracy reached." << endl;
#endif

    }
      
    // if a zero was found, add to the list 
    if (!stop && in(0.0, f(x))) {

#ifdef XINEWTON_DEBUG
      dout << endl
	   << "Zero found in x = " << x << endl;
      x.bitImage(dout);
      dout << "f(x) = " << f(x) << endl;
#endif

      zero.x = x;
      zero.unique = unique;
	
      if (list.empty()) {
	list.push_back(zero);
	numZeros++;

#ifdef XINEWTON_DEBUG
	dout << endl << "First zero in list." << endl;
#endif
      }
	
      else {

#ifdef XINEWTON_DEBUG
	dout << endl << "Trying to absorb new zero." << endl;
#endif
	  
	// try to absorb x by the last element in list
	if (!disjoint(list.back().x, zero.x)) {
	  list.back().x = hull(list.back().x, zero.x);
	  list.back().unique = false;
	    
#ifdef XINEWTON_DEBUG
	  dout << "Absorbed." << endl
	       << "new last zero: " << list.back().x << endl;
#endif
	}
	  
	else {
	  list.push_back(zero);
	  numZeros++;

#ifdef XINEWTON_DEBUG
	  dout << endl << "Not absorbed." << endl;
#endif

	}
	  
      }
    }

#ifdef XINEWTON_DEBUG
    else 
      dout << endl
	   << x << " contains no zero." << endl;
#endif

  }

  // verification
  typename ForwardContainer::iterator iter = list.begin();
  while (iter != list.end()) {
    if (!iter->unique) 
      verificationStep(f, df, *iter);
    iter++;
  }

  return errorCode;
}


// -------------------------------------------------------------------------
// Function reduceEnclosures(list, redList)
//
// Takes a 'list' of enclosures and produces a reduced list 'redList' in  
// which redundant enclosures are removed.
// A unique enclosure x is redundant if there exists a unique enclosure y
// and y is a subset of x.
//
// The function returns the number of unique enclosures in 'redList'.
// -------------------------------------------------------------------------  
template <class List>
int reduceEnclosures(const List &list, List &redList) 
{
  int unique = 0;

  typename List::const_iterator iter, redIter;
 
  bool isSuperSet;
  
  iter = list.begin();
  while (iter != list.end()) {
    if (iter->unique) {
      isSuperSet = false;
      redIter = list.begin();
      while (redIter != list.end()) {
	if (redIter != iter && redIter->unique)
	  isSuperSet = isSuperSet || superset(iter->x, redIter->x);
	redIter++;
      }
      if (!isSuperSet) {
	redList.push_back(*iter);
	unique++;
      }
    }
    else 
      redList.push_back(*iter);
    iter++;
  }

  return unique;
}


template <class interval>
class XINewton 
{
public:
  typedef std::vector<Enclosure<interval> > EnclosureList;

  // ----------------------------------------------------------------------
  // Default ctor
  // ----------------------------------------------------------------------
  XINewton() 
    : errorCode(xinNoError), unique(0) { }

  // ----------------------------------------------------------------------
  // Computes all zeros of an interval function 'f' with derivative 'df'
  // in the interval 'start' with relative accuracy 'eps'.
  // ----------------------------------------------------------------------
  template<class UnaryFunction1, class UnaryFunction2>
  void allZeros(UnaryFunction1 f, UnaryFunction2 df, 
		interval start, double eps = 1e-15,
		unsigned int maxZeros = UINT_MAX) 
  {
    list.clear();
    EnclosureList tmpList;
    errorCode = xinewton::allZeros(f, df, start, eps, tmpList, maxZeros);
    unique = reduceEnclosures(tmpList, list);
  }

  // ----------------------------------------------------------------------
  // Returns the list of computed enclosures.
  // ----------------------------------------------------------------------
  EnclosureList &getEnclosures()
  {
    return list;
  }

  // ----------------------------------------------------------------------
  // Returns the number of computed enclosures.
  // ----------------------------------------------------------------------
  int getNumEnclosures() 
  {
    return list.size();
  }
  
  // ----------------------------------------------------------------------
  // Returns the number of computed unique enclosures.
  // ----------------------------------------------------------------------
  int getNumUniqueEnclosures() 
  {
    return unique;
  }
  
  // ----------------------------------------------------------------------
  // Prints the computed enclosures.
  // ----------------------------------------------------------------------
  void printZeros(bool showBits = false, ostream &os = cout) const 
  {
    typename vector<Enclosure<interval> >::const_iterator iter;
    
    os << endl;

    int i=1;
    for (iter = list.begin(); iter != list.end(); iter++) {
      os << i++ << ": " << iter->x;
      os << endl;
      (iter->x).bitImage(os);
      if (iter->unique) 
	os << " contains a unique zero." << endl;
      else 
	os << " may contain a zero." << endl;
    }
    cout << endl;
    printDiagnostic(os);
  }

  // ----------------------------------------------------------------------
  // Prints a diagnostic message.
  // ----------------------------------------------------------------------
  void printDiagnostic(ostream &os = cout) const
  {
    os << list.size() << " enclosure(s) computed." << endl;
    
    if (list.size() == 0)
      os << endl 
	 << "The function is prooved to contain no zero "
	 << "in the search interval." << endl;
    else
      os << unique << " prooved unique zero(s) found." << endl;
    
    if (errorCode & xinNotAllZerosFound)
      os << endl 
	 << "Not all zeros were found due to the given user limit." << endl;
    if (errorCode & xinAccuracyUnfeasable)
      os << endl 
	 <<"The given accuracy could not be reached for all enclosures."
	 << endl;
    
    os  << endl;
  }

private:
  EnclosureList list;
  XINewtonError errorCode;
  int unique;  
  
};


  
  
}



#endif
