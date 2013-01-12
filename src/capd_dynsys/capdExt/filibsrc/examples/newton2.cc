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
#include <stack>
#include <vector>
#include <iomanip>

#include <climits> // for UINT_MAX

#include "../bench/Timer.h"
#include "xinterval2.h"

#include "interval.h"


//#define XINEWTON_DEBUG

#ifdef XINEWTON_DEBUG
#include <fstream>
ofstream dout("xinewton.out");
#endif


template <class List>
void printList(List list, ostream &os) 
{
  int i=1;
  
  typename List::iterator iter = list.begin();
  while (iter != list.end()) {
    os << i << ": " << iter->x;
    if (iter->unique)
      os << " (unique)";
    os << endl;
    //iter->x.bitImage(os);
    //os << endl;
    iter++;
    i++;
  }
}



template <typename interval>
struct Enclosure 
{
  interval x;
  bool unique;
};


/*
template <typename interval, 
          template <typename T> class ForwardContainer = std::vector> 
class EnclosureList
{
  typedef Enclosure<interval> enclosureT;
  
public:
  void add(enclosureT x) 
  {
    list.push_back(x);
  }
 
private:
  ForwardContainer<Enclosure<interval> > list;
};
*/



// -------------------------------------------------------------------------
// Try to bisect interval x at its midpoint c. Returns true iff the 
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


enum XINewtonError { xinNoError, xinNotAllZerosFound, 
		     xinAccuracyUnfeasable };


template <class UnaryFunction1, 
          class UnaryFunction2, 
          class interval, 
          class List>
XINewtonError allZeros(UnaryFunction1 f, UnaryFunction2 df,
		       interval x, double eps,
		       List &list,
		       unsigned int maxZeros = UINT_MAX) 
{
#ifdef XINEWTON_DEBUG
  dout << endl
       << "----------------------" << endl
       << "Start of newton method" << endl
       << "----------------------" << endl << endl;
#endif

  bool stop, maxAccuracy;

  interval V1, V2;
  extIntersectInfo info;  
  Xinterval<interval> z;
  double c;

  Enclosure<interval> zero;
  
  bool unique;

  // initialize stack of intervals with starting interval x
  stack<interval> work;
  work.push(x);

  // adjust eps if necessary
  if (eps <= 0.0) {
    eps = 1e-15;

#ifdef XINEWTON_DEBUG
    dout << "eps <= 0.0 ! Adjusting it to 1e-15." << endl << endl;
#endif
  
  }
  

  unsigned int numZeros = 0;
  
  // main loop
  while (!work.empty()) {

    if (numZeros == maxZeros) {
      
#ifdef XINEWTON_DEBUG
      dout << "Maximum number of " << maxZeros << " zeros reached. " 
	   << "Method stopped." << endl << endl;
#endif    

      break;
    }
    

    stop = false;
    maxAccuracy =false;
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
	 << "==============================" << endl
	 << "x = " << x << endl;
    x.bitImage(dout);
    dout << endl;
#endif

    // start Newton iteration if f(x) contains a zero
    //if (in(0.0, f(x))) {

#ifdef XINEWTON_DEBUG
    //dout << "0 in f(x) => starting Newton iteration" << endl;
#endif

      while (in(0.0, f(x)) && relDiam(x) > eps && !stop && !maxAccuracy) {
	
	// Newton step
	c = mid(x);
	z = c - f(c) % df(x);
	extIntersect(x, z, V1, V2, info);

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
	if (info != EmptyIntv) {
	  if (V1 == x) {
#ifdef XINEWTON_DEBUG
	    stagnated = true;
#endif
	    maxAccuracy = !tryBisect(V1, V2, c);
	    if (!maxAccuracy)
	      info = DoubleIntv;
	  }
	  else if (info != SingleIntv && V2 == x) {
#ifdef XINEWTON_DEBUG
	    stagnated = true;
#endif
	    maxAccuracy = !tryBisect(V2, V1, c);
	    if (!maxAccuracy)
	      info = DoubleIntv;
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
	      info = DoubleIntv;
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
	
	if (info == EmptyIntv) {
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
	  if (info == DoubleIntv) {

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

#ifdef XINEWTON_DEBUG
  //    else 
  //      dout << "0.0 not in f(x) = " << f(x) << endl;
#endif    
    
  //}

  // verification
  typename List::iterator iter = list.begin();
  while (iter != list.end()) {
    if (!iter->unique) 
      verificationStep(f, df, *iter);
    iter++;
  }

}

template <class List>
void reduceEnclosures(const List &list, List &redList) 
{
  typename List::const_iterator iter, redIter;
 
  bool isSuperSet;
  
  iter = list.begin();
  while (iter != list.end()) {
    if (iter->unique) {
      isSuperSet = false;
      redIter = list.begin();
      while (redIter != list.end()) {
	if (redIter != iter && redIter->unique)
	  isSuperSet = isSuperSet || sp(iter->x, redIter->x);
	redIter++;
      }
      if (!isSuperSet)
	redList.push_back(*iter);
    }
    else 
      redList.push_back(*iter);
    iter++;
  }
}
    

/*
interval f(interval x) {
  return sin(1/x);  
}

interval df(interval x) {
  return -cos(1/x)/sqr(x);  
}
*/


/*
struct F 
{
  interval operator()(interval x) 
  {
    return sin(1/x);
  }
};
*/

/*
struct DF 
{
  interval operator()(interval x) 
  {
    return -cos(1/x)/sqr(x);  
  }
};
*/

/*
// Zeros at -2, 1 and 3
interval f(interval x) {
  return power(x,3) - 2*sqr(x) - 5*x + 6;
}

interval df(interval x) {
  return 3*sqr(x) - 4*x - 5;
}
*/

/*
interval f(interval x) 
{
  return sqr(x)-2;
}

interval df(interval x) 
{
  return 2*x;
}
*/


/*
// zeros at 0, 3, 4 and 5 (see C-XSC Toolbox p.111)
interval f(interval x) {
  return power(x,4) - 12*power(x,3) + 47*sqr(x) - 60*x;
}

interval df(interval x) {
  return 4*power(x, 3) - 36*sqr(x) + 94*x - 60;
}
*/

/*
// zeros at 1 and 0.888305... (see C-XSC Toolbox p.111)
interval f(interval x) {
  return power(x,4) - 12*power(x,3) + 47*sqr(x) - 60*x + 24;
}

interval df(interval x) {
  return 4*power(x, 3) - 36*sqr(x) + 94*x - 60;
}
*/

/*
// no real zeros
interval f(interval x) {
  return power(x,4) - 12*power(x,3) + 47*sqr(x) - 60*x + 24.1;
}

interval df(interval x) {
  return 4*power(x, 3) - 36*sqr(x) + 94*x - 60;
}
*/

/*
// no zero (see Toolbox p. 110)
interval f(interval x) {
  return sqrt(1+x*x);
}

interval df(interval x) {
  return (x+x)/(2*sqrt(1+x*x));
}
*/


/*
// defined for |x| >= 1 with zeros -1 and 1 (not differentiable in -1, 1 !)
interval f(interval x) {
  return sqrt(sqr(x)-1);
}

interval df(interval x) {
  return x / (sqrt(sqr(x)-1));
}
*/

/*
interval f(interval x) {
  return sqrt(sqr(x-1.1)-0.1) * (x-1.42);
}

interval df(interval x) {
  return sqrt(sqr(x-1.1)-0.1) + 
    ((x-1.1)*(x-1.42)) / (sqrt(sqr(x-1.1)-0.1));
}
*/


/*
interval f(interval x) {
  return log(x-1)*sin(x*x-(1.0+1e-15));
}

interval df(interval x) {
  return log(x-1)*cos(x*x-(1.0+1e-15))*2*x + sin(x*x-(1.0+1e-15))/(x-1);
}
*/

/*
// double zeros at k*pi
interval f(interval x) {
  return sqr(sin(x));
}

interval df(interval x) {
  return 2*sin(x)*cos(x);
}
*/

interval f(interval x) {
  return sqr(sin(1/x));
}

interval df(interval x) {
    return (-2*sin(1/x)*cos(1/x))/sqr(x);
}

/*
interval f(interval x) {
  return sqr(sin(1/x));
}

interval df(interval x) {
  return (-2*sin(1/x)*cos(1/x))/sqr(x);
}
*/

typedef std::vector<Enclosure<interval> > List;


template <class List>
void checkDisjoint(const List &list) 
{
  typename List::const_iterator iter1 = list.begin(), iter2;
  int i=1, j=1;

  cout << endl;
  while (iter1 != list.end()) {
    iter2 = iter1;
    iter2++;
    j = i+1;
    while (iter2 != list.end()) {
      if (!disjoint(iter1->x, iter2->x)) {
  	cout << i << " and " << j << " not disjoint." << endl; 
	if (iter1->x <= iter2->x)
	  cout << i << " is subset of " << j << endl;
	if (iter2->x <= iter1->x)
	  cout << j << " is subset of " << i << endl;
      }
	  
      iter2++;
      j++;
    }
    iter1++;
    i++;
  }
}


int main() 
{
  filib::fp_traits<double>::setup();

  interval::precision(15);
  cout << setprecision(15);
  
  interval start;
  double eps;
  unsigned int k;
    
  cout << "Search interval: ( e.g. [-10, 2.3] ): ";
  cin >> start;
  cout << "Relative tolerance: ( e.g. 1e-10 ): ";
  cin >> eps;
  cout << "Iterations: ";
  cin >> k;
  
  List list;
  
  Timer timer;
  timer.Start();
  for (int i=0; i<k; i++) {
    list.clear();
    allZeros(f, df, start, eps, list, 40000000UL);
  }
  timer.Stop();

  cout << endl << "Computation time: " << timer.SecsElapsed() << " sec." 
       << endl << endl;

  //checkDisjoint(list);

  timer.Start();
  List list2;
  reduceEnclosures(list, list2);
  timer.Stop();

  cout << "Reduction time: " << timer.SecsElapsed() << " sec." << endl << endl;

  // count unique zeros
  int uniqueCount = 0;
  for (List::const_iterator iter=list2.begin(); iter != list2.end(); iter++)
    if (iter->unique)
      uniqueCount++;

  //printList(list2, cout);

  cout << endl << list2.size() << " zero(s) found, " 
       << uniqueCount << " verified as unique." << endl
       << list.size() - list2.size() << " reduced." << endl;
  
  return 0;
  
}










