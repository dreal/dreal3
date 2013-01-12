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
#include <fstream>
#include <stack>
#include <vector>

#include "interval.h"
#include "xinterval2.h"

#include "Timer.h"

#ifdef DEBUG
ofstream fileOut("tst.out");
ostream &out = fileOut;
#else
ostream &out = cout;
#endif


/*
interval f(interval x) {
  return sqr(sin(x));
}

interval df(interval x) {
  return 2*sin(x)*cos(x);
}
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
interval f(interval x) {
  return sqr(x-2);  
}

interval df(interval x) {
  return 2*x-4;
}
*/

/*
inline
interval f(interval x) {
  return sin(1/x);  
}

inline
interval df(interval x) {
  return -cos(1/x)/sqr(x);  
}
*/

interval f(interval x) 
{
  return sqr(x)-2;
}

interval df(interval x) 
{
  return 2*x;
}


typedef std::vector<interval> IntvList;
typedef std::stack<interval> IntvStack;

typedef std::vector<bool> InfoList;

inline
void addZero(IntvList &list, interval zero) 
{
  /*
  IntvList::iterator iter=list.begin();
  bool absorbed = false;
  
  while (iter != list.end() && !absorbed) {
    if (!disjoint(*iter, zero)) {
      *iter = hull(*iter, zero);
      absorbed = true;
      cnt++;

      if (++iter == list.end())
	cntEnd++;
    }
    iter++;
  }
  
  if (!absorbed)
    list.push_back(zero);
  */

  // absorption only at the end of the list !
  // -> zeros are found in ascending order !
  if (list.empty())
    list.push_back(zero);
  
  else {
    interval &x = list.back();
    if (!disjoint(x, zero)) 
      x = hull(x, zero);
    else
      list.push_back(zero);
  }
}


bool verify(interval &y) 
{
  const int kmax= 10;
  interval yIn, yOld, fc, dfy;
  double c,eps;
  int k;
  
  k = 0; 
  yIn = y; 
  eps = 0.25; 
  bool unique = false;
  
  while (!unique && (k < kmax) ) {
    yOld = blow(y,eps);
    dfy = df(y); 
    if (in(0.0,dfy)) break;
    k++;
    c = mid(yOld);
    fc=f(interval(c));
    y = c - fc / dfy;
    if (disjoint(y, yOld)) break;
    unique = interior(y,yOld);
    y = intersect(y, yOld);
    if (y == yOld) eps=eps*8.0;
  }
  if (!unique) y = yIn;
  return unique;
}

inline bool tryBisect(interval &x, interval &y) {
#ifdef DEBUG
  out << "Bisection: ";
#endif
  double c = x.mid();
  if (c == x.inf() || c == x.sup()) {
#ifdef DEBUG
    out << "Impossible." << endl;
#endif
    return false;
  }
  
  else {
#ifdef DEBUG
    out << "Ok." << endl;
#endif
    y = interval(c, x.sup());
    x = interval(x.inf(), c);
    return true;
  }
}


int main()
{
  filib::fp_traits<double>::setup();

  interval::precision(15);

  interval start;
  cout << "Search interval: ";
  cin >> start;
  
  double eps;  
  cout << "eps = ";
  cin >> eps;


  Timer timer;
  timer.Start();
    
  bool stop, maxAccuracy;
  interval x;
  double c;
  xinterval z;
  interval V1, V2;
    
  IntvStack U;
  IntvList C;
  C.reserve(1024);

  InfoList info;
  
  U.push(start);
  
  while (!U.empty()) {
    stop = false;
    maxAccuracy =false;
    
    x = U.top();
    U.pop();

#ifdef DEBUG
    int i=0;
    out << endl;    
    for (int j=0; j<75; j++)
      out << "-";
    out << endl;

    out << "Getting new x from stack: x = " << x << endl;
    x.bitImage(out);
#endif    

    if (in(0.0, f(x))) {

#ifdef DEBUG
       out << "Starting iteration:" << endl;
#endif
     
      while (diam(x) > eps && !stop && !maxAccuracy) {

#ifdef DEBUG
	out << endl << "Step " << i++ << endl;
	out << "x = " << x << endl;
	x.bitImage(out);
#endif

	c = mid(x);
	z = c - f(c) % df(x);
	extIntersect(x, z, V1, V2);

#ifdef DEBUG
	out << "V1 = " << V1 << endl;
	V1.bitImage(out);
	out << "V2 = " << V2 << endl;
	V2.bitImage(out);

	if (V1 == x && V2 != EmptyIntval()) {
	  out << "**************" << endl;
	  if (!sb(V2, V1))
	    out << "+++++++++++++++++" << endl;
	}
#endif
	
	if (V1 == x) {
	  maxAccuracy = !tryBisect(V1, V2);
	  cout << "FALL 1111111111111111111111111" << endl;
	}
	else if (V2 == x) {
	  maxAccuracy = !tryBisect(V2, V1);
	  cout << "FALL 2222222222222222222222222" << endl;
	}
	
	if (maxAccuracy) {
	  cout << "Further bisection impossible!" << endl;
	  //exit(-1);
	  continue;
	} 

	if (V1 == EmptyIntval())
	  // both V1 and V2 are empty !
	  stop = true;
	else {
	  if (V2 != EmptyIntval()) {
#ifdef DEBUG
	    out << "Pushing V2." << endl;
#endif
	    U.push(V2);
	  }
#ifdef DEBUG
	  out << "x := V1" << endl;
#endif
	  x = V1;
	}
      }
      
#ifdef DEBUG
      out << endl << "Iteration finished: ";
      if (stop)
	out << "both V1 and V2 were empty." << endl;
      else if (diam(x) <= eps)
	out << "stopping criterion diam(x) <= eps reached.";
      else
	out << "desired accuracy cannot be reached.";
#endif      
      
      if (!stop && in(0, f(x))) {
	addZero(C, x);
      }
      
      else {
	
#ifdef DEBUG	
	out << "x contains no zero !" << endl;
	if (!stop) {
	  if (maxAccuracy)
	    out << "Accuracy Problem !" << endl;
	  else
	    out << "This shouldn't be the case !" << endl;
	  out << "f(x) = " << f(x) << endl;
	}
#endif
	
      }
      
    }
    
#ifdef DEBUG   
    else {
      out << "Contains no zero !" << endl;
      out << "f(x) = " << f(x) << endl;
    }
#endif
  }
  
  
  out << endl << endl << "Found zeros:" << endl;
  for (int i=0; i < C.size(); i++) {    
    out << endl << "x" << i+1 << " = " << C[i];
#ifdef DEBUG
    out << endl;
    C[i].bitImage(out);
#endif
    out << " f(x) = " << f(C[i]) << endl;
    
    if (verify(C[i]))
      out << "-> verified." << endl;
    else
      out << "-> not verified." << endl;
    
  }

  timer.Stop();
  
  out << C.size() << " zeros found in " << timer.SecsElapsed() << " sec."<< endl;
  
  return 0;
}

