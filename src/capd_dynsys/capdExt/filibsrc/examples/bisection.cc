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

#include "interval/interval.hpp"
#include <iostream>

using std::cin;
using std::endl;
using std::cout;

typedef filib::interval<double> interval;

// --------------------------------------------------------------------
// ---   Test function f1 = e^(-3x) - (sin x)^3                     ---
// --------------------------------------------------------------------

interval f1(interval x) {
  return ( exp(-3.0*x) - sin(x)*sin(x)*sin(x) );
}

// --------------------------------------------------------------------
// ---   Test function f2 = - \sum_k=1^5 (k*sin((k+1)x+k))          ---
// --------------------------------------------------------------------

interval f2(interval x) {
  int k;
  interval res=interval(0.0);
  
  for (k=1; k<=5; k++)
    res = res - static_cast<double>(k) * sin( static_cast<double>(k+1)*x + static_cast<double>(k) ); 
  return ( res );
}

// --------------------------------------------------------------------
// ---   Test function f3 = x^3 - 2x^2 +  x                         ---
// --------------------------------------------------------------------

interval f3(interval x) {
  return ( x*sqr(x) - 2.0*sqr(x) + x);
}

// --------------------------------------------------------------------
// ---   Test function f4 = 0                                       ---
// --------------------------------------------------------------------

interval f4(interval x) {
  return interval(0.0);
}

// --------------------------------------------------------------------
// ---   Test function f5 = 1                                       ---
// --------------------------------------------------------------------

interval f5(interval x) {
  return interval(1.0);
}

// --------------------------------------------------------------------
// ---   Test function f6 = (sin x)^2 - (1-cos 2x)/2 = 0            ---
// --------------------------------------------------------------------

interval f6(interval x) {
  return ( sqr(sin(x)) - ( 1.0 - cos(2.0*x) ) / 2.0 );
}

// --------------------------------------------------------------------
// ---   Test function f7 = x^3-x^2-17x-15 = (x-5)(x+1)(x+3)        ---
// --------------------------------------------------------------------

interval f7(interval x) {
  return( x*sqr(x) - sqr(x) - 17.0*x - 15.0 );
}

interval f8(interval x) {
  return sin(x);
}


// --------------------------------------------------------------------
// ---   Initialisation, data type list	                            ---
// --------------------------------------------------------------------

const int MaxDepth = 10000;  // Maximum number of bisection steps

struct list                  // Data type for resulting list
{
  interval intval;
  list* next;
  
  list() {intval=interval(0.0); next=NULL;}
};

     
// --------------------------------------------------------------------
// ---   a special sign function (for verification test)            ---
// --------------------------------------------------------------------

int VZ( interval (*fct) (interval), interval x) {
  return ( sup( (*fct)(interval(inf(x))) * (*fct)(interval(sup(x))) ) < 0 );
}

// --------------------------------------------------------------------
// ---   function PrintZeros (output and verfication)               ---
// --------------------------------------------------------------------

void PrintZeros( interval (*fct) (interval), list* reslist, int Depth) {

  int k=0;

  if (reslist==NULL)
     cout << "Function contains no zeros in the search interval!" << endl;
  else {
    cout << "Ranges for zeros:" << endl;
    while (reslist != NULL) {
       cout << " k=" << ++k << " " << reslist->intval << " verified: ";
       if (VZ((*fct),reslist->intval)) cout << "Yes" << endl;
       else                            cout << "No" << endl;
       (reslist->intval).bitImage(cout);
       reslist=reslist->next;
    }
  }
  cout << "Number of bisection steps: " << Depth << endl << endl;
}

// --------------------------------------------------------------------
// ---   function Bisect (bisection-method)                         ---
// --------------------------------------------------------------------

void Bisect( interval (*fct) (interval), interval x, double eps, 
                                          list* &reslist, int &Depth) {

  interval fx, x1, x2;
  double infx, supx, m;
  int absorbed;
  list* pointer;
  pointer = reslist;

  Depth++;
  fx = (*fct)(x);
  
  if (in(0.0, fx)) {
    infx = inf(x);
    supx = sup(x);
    m = mid(x);
    if ((diam(x)<eps) || (m==infx) || (m==supx) || (Depth > MaxDepth) ) {
      /* int k=1; */
      absorbed=0;
      //- Try to absorb x by an already computed element of resulting list -
      if (reslist != NULL) while ((pointer != NULL) && (!absorbed)) {
        absorbed = (    (inf(pointer->intval)<=sup(x) && 
                                                sup(x)<=sup(pointer->intval)) 
                     || (inf(pointer->intval)<=inf(x) && 
                                                inf(x)<=sup(pointer->intval))
                     || (inf(x)<=sup(pointer->intval) && 
                                                sup(pointer->intval)<=sup(x))
                     || (inf(x)<=inf(pointer->intval) && 
                                                inf(pointer->intval)<=sup(x))
                   );
        if (absorbed) pointer->intval = hull(pointer->intval, x);
        pointer = pointer -> next;
      }

      if (!absorbed) {   // Store x in the resulting list
         pointer=reslist;
         if (reslist != NULL) {
           while (pointer->next != NULL) pointer = pointer->next;
           list* insert = new list;
           pointer->next = insert;
           insert->next = NULL;
           insert->intval = x; 
         } else {
           reslist = new list;
           reslist->next = NULL;
           reslist->intval = x;         
         }
      }
      if (Depth> MaxDepth) 
         cout << "Maximal number of bisection steps is reached!" << endl;
    } else {
      x1 = interval(infx,m);
      Bisect( (*fct), x1, eps, reslist, Depth);
      x2 = interval(m,supx);
      Bisect( (*fct), x2, eps, reslist, Depth);
    }
  }
}

// --------------------------------------------------------------------
// ---   function PrintAllZeros (root finding and output)           ---
// --------------------------------------------------------------------

void PrintAllZeros( interval (*fct) (interval), interval x, double eps) {

  int Depth = 0;
  list* reslist;
  reslist = NULL;
  Bisect( (*fct), x, eps, reslist, Depth );
  PrintZeros( (*fct), reslist, Depth );
}

// --------------------------------------------------------------------
// ---   function main                                              ---
// --------------------------------------------------------------------

int main() {
  filib::fp_traits<double>::setup();
   
  double eps;
  interval y;

  interval::precision(15);

  cout << endl;
  cout << "Bisection method in C++ with fi_lib++" << endl;
  cout << "===================================" << endl << endl;
 

  cout << "tolerance (relative): (e.g. 'eps = 1e-3' or 'eps = 1e-8') \n eps = ";
  cin >> eps;
  cout << endl;

  cout << "Test function f1 = e^(-3x) - (sin x)^3:" << endl;
  y = interval(  0, 20);
  cout << "Search interval: " << y << endl;
  PrintAllZeros( f1, y, eps);

  cout << "Test function f2 = - sum_k=1^5 (k*sin((k+1)x+k)):" << endl;
  y = interval(  -5, 5);
  cout << "Search interval: " << y << endl;
  PrintAllZeros( f2, y, eps);

  cout << "Test function f3 = x^3 - 2x^2 +  x = x(x-1)^2:" << endl;
  y = interval(  -1, 2);
  cout << "Search interval: " << y << endl;
  PrintAllZeros( f3, y, eps);

  cout << "Test function f4 = 0:" << endl;
  y = interval(  1, 2);
  cout << "Search interval: " << y << endl;
  PrintAllZeros( f4, y, eps);

  cout << "Test function f5 = 1:" << endl;
  y = interval(  1, 2);
  cout << "Search interval: " << y << endl;
  PrintAllZeros( f5, y, eps);

  cout << "Test function f6 = (sin x)^2 - (1-cos 2x)/2 = 0:" << endl;
  y = interval(  -1, 1);
  cout << "Search interval: " << y << endl;
  PrintAllZeros( f6, y, eps);

  cout << "Test function f7 = x^3-x^2-17x-15 = (x-5)(x+1)(x+3):" << endl;
  y = interval( -10, 10);
  cout << "Search interval: " << y << endl;
  PrintAllZeros( f7, y, eps);

  cout << "Test function f8 = sin(x):" << endl;
  y = interval( 2, 4);
  cout << "Search interval: " << y << endl;
  PrintAllZeros( f8, y, eps);

  return 0;
}



/* ---------------------------  output  -------------------------------

Toleranz (relativ): (e.g. 'eps = 1e-3' or 'eps = 1e-8') 
 eps = 1e-3

Test function f1 = e^(-3x) - (sin x)^3:
Search interval: [-9.881312916824931e-324,  2.000000000000001e+01 ]
Ranges for zeros:
 k=1 [  5.883789062499998e-01,  5.889892578125002e-01 ] verified: Yes
 k=2 [  3.096313476562499e+00,  3.096923828125001e+00 ] verified: Yes
 k=3 [  6.284790039062498e+00,  6.285400390625002e+00 ] verified: Yes
 k=4 [  9.424438476562496e+00,  9.425048828125004e+00 ] verified: Yes
 k=5 [  1.256591796875000e+01,  1.256652832031250e+01 ] verified: Yes
 k=6 [  1.570739746093750e+01,  1.570800781250000e+01 ] verified: Yes
 k=7 [  1.884948730468749e+01,  1.885009765625001e+01 ] verified: Yes
Number of bisection steps: 191

Test function f2 = - sum_k=1^5 (k*sin((k+1)x+k)):
Search interval: [ -5.000000000000002e+00,  5.000000000000002e+00 ]
Ranges for zeros:
 k=1 [ -4.946289062500002e+00, -4.945068359374998e+00 ] verified: Yes
 k=2 [ -4.488525390625002e+00, -4.486083984374998e+00 ] verified: Yes
 k=3 [ -3.977050781250001e+00, -3.975219726562499e+00 ] verified: Yes
 k=4 [ -3.505859375000001e+00, -3.504028320312499e+00 ] verified: Yes
 k=5 [ -3.015136718750001e+00, -3.013916015624999e+00 ] verified: Yes
 k=6 [ -2.511596679687501e+00, -2.510375976562499e+00 ] verified: Yes
 k=7 [ -2.055664062500001e+00, -2.054443359374999e+00 ] verified: Yes
 k=8 [ -1.455078125000000e+00, -1.454467773437500e+00 ] verified: Yes
 k=9 [ -7.861328125000002e-01, -7.855224609374998e-01 ] verified: Yes
 k=10 [ -1.470947265625001e-01, -1.464843749999999e-01 ] verified: Yes
 k=11 [  3.521728515624999e-01,  3.527832031250001e-01 ] verified: Yes
 k=12 [  8.209228515624998e-01,  8.221435546875002e-01 ] verified: Yes
 k=13 [  1.336669921875000e+00,  1.338500976562500e+00 ] verified: Yes
 k=14 [  1.795043945312500e+00,  1.796875000000000e+00 ] verified: Yes
 k=15 [  2.305908203124999e+00,  2.308349609375001e+00 ] verified: Yes
 k=16 [  2.777099609374999e+00,  2.778930664062501e+00 ] verified: Yes
 k=17 [  3.268432617187499e+00,  3.269653320312501e+00 ] verified: Yes
 k=18 [  3.771362304687499e+00,  3.772583007812501e+00 ] verified: Yes
 k=19 [  4.227905273437498e+00,  4.228515625000002e+00 ] verified: Yes
 k=20 [  4.827880859374998e+00,  4.828491210937502e+00 ] verified: Yes
Number of bisection steps: 811

Test function f3 = x^3 - 2x^2 +  x = x(x-1)^2:
Search interval: [ -1.000000000000000e+00,  2.000000000000001e+00 ]
Ranges for zeros:
 k=1 [ -2.441406250000001e-04,  4.882812500000002e-04 ] verified: Yes
 k=2 [  9.460449218749998e-01,  1.054443359375000e+00 ] verified: No
Number of bisection steps: 709

Test function f4 = 0:
Search interval: [  9.999999999999998e-01,  2.000000000000001e+00 ]
Ranges for zeros:
 k=1 [  9.999999999999998e-01,  2.000000000000001e+00 ] verified: No
Number of bisection steps: 2047

Test function f5 = 1:
Search interval: [  9.999999999999998e-01,  2.000000000000001e+00 ]
Function contains no zeros in the search interval!
Number of bisection steps: 1

Test function f6 = (sin x)^2 - (1-cos 2x)/2 = 0:
Search interval: [ -1.000000000000000e+00,  1.000000000000000e+00 ]
Ranges for zeros:
 k=1 [ -1.000000000000000e+00,  1.000000000000000e+00 ] verified: No
Number of bisection steps: 4095

Test function f7 = x^3-x^2-17x-15 = (x-5)(x+1)(x+3):
Search interval: [ -1.000000000000000e+01,  1.000000000000000e+01 ]
Ranges for zeros:
 k=1 [ -3.001098632812501e+00, -2.999267578124999e+00 ] verified: Yes
 k=2 [ -1.000366210937500e+00, -9.991455078124998e-01 ] verified: Yes
 k=3 [  4.999389648437498e+00,  5.000610351562502e+00 ] verified: Yes
Number of bisection steps: 179

--------------------------------------------------------------------------*/
