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

#define DEBUG

#include "xinterval.h" 
#include <iostream> 
#include <cstdio>         // for function sprintf
#include "../bench/Timer.h"

#include <vector>

template <class interval>
class Zero {
public:
  interval x;
  bool unique;

  friend class XINewtion;
public:
  Zero(interval enclosure, bool isUnique)
    : x(enclosure), unique(isUnique)
  { }

  interval getinterval() const
  {
    return x;
  }

  bool isUnique() const {
    return unique;
  }
};

template <class interval, class List = std::vector<Zero<interval> > >
class XINewton {
public:
  enum errCode{NoError, IllMaxZeroNo, NotAllZeros};

  int err;
  List zeros;
  int numZeros;
  int maxNumZeros;

  template <class UnaryFunction1, class UnaryFunction2>
  void allZeros(UnaryFunction1 f, UnaryFunction2 df, 
		interval start, double eps, unsigned int maxZeros)
  {
    err = NoError;
    zeros.clear();
    zeros.reserve(maxZeros);
    numZeros = 0;
    maxNumZeros = maxZeros;

    double minEps = Double::ulp(1.0);
    eps = eps < minEps ? minEps : eps;
      
    xinewton(f, df, start, eps, 0);
      
    if (numZeros > maxZeros) {	
      err = NotAllZeros; 
      numZeros = maxZeros;
    }

    verificationStep(f, df);
  }

private:

  template <class UnaryFunction1, class UnaryFunction2>
  void xinewton(UnaryFunction1 f, UnaryFunction2 df,
		interval y, double eps, int yUnique)
  {

#ifdef DEBUG
    cout << "---------------------------------------------------------------"
         << endl
         << "y = " << y << endl;
#endif

    if (numZeros > maxNumZeros)
      return;

    interval fy = f(y);

#ifdef DEBUG
    cout << "f(y) = " << fy << endl;
#endif

    if (!in(0.0, fy))
      return;

#ifdef DEBUG
    cout << "0 in fy" << endl;
#endif
    
    interval* V;
    xinterval z;
    double c;
    interval ci;
    int i;
    
#ifdef DEBUG
    cout << "df(y) = " << df(y) << endl;
#endif

    c  = mid(y);
    ci = interval(c);
    z  = c - f(ci) % df(y);
    V  = y & z;

#ifdef DEBUG
    cout << "V[1] = " << V[1] << endl
         << "V[2] = " << V[2] << endl;
#endif

    if (V[1] == y) {    // bisection
      //      if (!interior(c, y)) return;      
      V[1] = interval(inf(y),c);
      V[2] = interval(c,sup(y));

#ifdef DEBUG
      cout << "bisection:"
           << endl
           << cout << "V[1] = " << V[1] << endl
           << "V[2] = " << V[2] << endl;
#endif
    }

    if ( (V[1] != EmptyIntval() ) && (V[2] == EmptyIntval()))
      yUnique = yUnique || interior(V[1], y);
    else
      yUnique = 0;

    for (i=1; i<=2; i++) {
      if (V[i] == EmptyIntval())  
        continue; 
#ifdef DEBUG
      cout << "relDiam: " << relDiam(V[i]) << endl;
      cout << "diam   : " << diam(V[i]) << endl;
      cout << "mig    : " << mig(V[i]) << endl;
      cout << "diam/mig: " << diam(V[i]) / mig(V[i]) << endl;
      
#endif
      if (relDiam(V[i]) <= eps) {
#ifdef DEBUG
	cout << "Genauigkeit erreicht !" << endl;
#endif
	fy = f(V[i]);
#ifdef DEBUG
	cout << "Neues f(y): " << fy << endl;
#endif	
	if ( in(0.0, fy) ) {
#ifdef DEBUG
	  cout << ".. und NS gefunden" << endl;
#endif	  
	  numZeros ++;
	  if (numZeros > maxNumZeros) 
	    return;

	  bool absorbed = false;
	  //- Try to absorb V[i] by an already computed element of list -
	  typename List::iterator iter = zeros.begin();
	  while (iter != zeros.end() && !absorbed) {
	    absorbed = !( (sup(V[i])<inf(iter->x)) ||
	  		  (sup(iter->x)<inf(V[i]) ));
	    if (absorbed) { 
	      iter->x = hull((iter->x), V[i]);
	      iter->unique = false;
	      numZeros --;
	    }
	    iter++;
	  }
	  
	  if (!absorbed)   // Store x in the resulting list
	    zeros.push_back(*(new Zero<interval>(V[i], yUnique)));
	}	
      }
      else 
      xinewton(f, df, V[i], eps, yUnique); 
    }
  }

  template <class UnaryFunction1, class UnaryFunction2>
  void verificationStep(UnaryFunction1 f, UnaryFunction2 df)
  {
    const int kmax= 10;
    interval yIn, yOld, fc, dfy;
    double c,eps;
    int k;
    
   

    typename List::iterator iter = zeros.begin();
    while (iter != zeros.end()) {
    
      k = 0; 
      yIn = iter->x; 
      eps = 0.25; 

      while (!iter->unique && (k < kmax) ) {
	yOld = blow(iter->x, eps);
	dfy = df(iter->x); 
	if (in(0.0,dfy)) break;
	k++;
	c = mid(yOld);
	fc=f(interval(c));
	iter->x = c - fc / dfy;
	if (disjoint(iter->x, yOld)) break;
	iter->unique = interior(iter->x, yOld);
	iter->x = intersect(iter->x, yOld);
	if (iter->x == yOld) eps=eps*8.0;
      }
      if (!iter->unique) iter->x = yIn;

      iter++;
    }
  }

};


//----------------------------------------------------------------------------
// Definition of the function f(x) and the derivate df(x)
//     Test function f = cosh(x) + 10 * x^2 * sin(x)^2 - 34                    
//----------------------------------------------------------------------------

/*
interval f(interval x) {
  return ( cosh(x)+10*sqr(x)*sqr(sin(x))-34 );
}

interval df(interval x) {
  return( sinh(x)+20*x*sqr(sin(x))+20*sqr(x)*sin(x)*cos(x) );
}
*/

/*
interval f(interval x) {
  return power(x,4) - 12*power(x,3) + 47*sqr(x) - 60*x;
}

interval df(interval x) {
  return 4*power(x, 3) - 36*sqr(x) + 94*x - 60;
}
*/

/*
interval f(interval x) {
  return power(x,3) - 199.01*sqr(x) + 9900.99*x - 99;
}

interval df(interval x) {
  return 3*sqr(x) - 398.02*x + 9900.99;
}
*/

/*
interval f(interval x) {
  return cos(x);
}

interval df(interval x) {
  return -sin(x);
}
*/

/*
interval f(interval x) {
  return sqr(sin(x));
}

interval df(interval x) {
  return 2*sin(x)*cos(x);
}
*/


/*
interval f(interval x) {
  return sqr(x-2);
}

interval df(interval x) {
  return 2*(x-2);
}
*/

template <class T>
class Cos {
public:
  T operator()(T t) {
    return cos(t);
  }
};

template <class T>
class dCos {
public:
  T operator()(T t) {
    return -sin(t);
  }
};

interval f(interval x) {
  return sqrt(sqr(x)-1);
}

interval df(interval x) {
  return x / (sqrt(sqr(x)-1));
}


// --------------------------------------------------------------------
// ---   function main                                              ---
// --------------------------------------------------------------------

int main ()
{
  filib::fp_traits<double>::setup();

  interval::precision(15);
  
  interval Searchinterval;
  double Tolerance;

  cout << "Extended-interval-Newton method in C++ with fi_lib++" << endl;
  cout << "====================================================" << endl << endl;
 
  cout << "Search interval (e.g. '[-10 10]'): " ;
  cin >> Searchinterval;
  cout << endl << "Search interval = " << Searchinterval << endl;
  cout << "Tolerance (relative) (e.g. '1e-3' or '1e-15'): ";
  cin >> Tolerance;
  cout << endl;
  

  XINewton<interval> newton;

  Timer timer;
  timer.Start();
  newton.allZeros(f, df, 
		  Searchinterval, Tolerance, 10000);
  timer.Stop();
  

  if (newton.zeros.size() == 0)
    cout << "Function contains no zeros in the search interval!" << endl;
  else {
    cout << "Ranges for zeros:" << endl;
    std::vector<Zero<interval> >::iterator iter = newton.zeros.begin();
    while (iter != newton.zeros.end()) {
      cout << iter->getinterval() << endl;
      if (iter->isUnique())
	cout << " encloses a locally unique zero !" << endl;
      else
	cout << " may contain a zero (not verified unique)!"<< endl;
      iter++;
    }
  }
  cout << endl << newton.numZeros << " interval enclosure(s)" << endl;
  if (newton.err) 
    cout << endl << "SOME ERROR !" << endl;
  //cout << endl << AllZerosErrMsg(Error) << endl;
  
  cout << endl << "Time: " << timer.SecsElapsed() << " sec." << endl;
  

  return 0;
}






