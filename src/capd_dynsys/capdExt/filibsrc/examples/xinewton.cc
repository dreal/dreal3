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

#include "xinterval.h" 
#include "interval/interval.hpp"
#include <iostream> 
#include <cstdio>
/* #include "../bench/Timer.h" */
#include "benchmark/aribench_timer.hpp"

using filib::interval;
using std::cout;
using std::cin;
using std::endl;
typedef interval<double,filib::native_switched,filib::i_mode_extended> (*fun)(interval<double,filib::native_switched,filib::i_mode_extended>);

// --------------------------------------------------------------------
// ---   Initialisation, data type list	                            ---
// --------------------------------------------------------------------

struct list                  // Data type for resulting list
{
  interval<double,filib::native_switched,filib::i_mode_extended> intval;
  int info;
  list* next;
  
  list() {intval=interval<double,filib::native_switched,filib::i_mode_extended>(0.0); next=NULL;}
  ~list() {if (next) delete next; }
  
      
};

static int MaxZeroNo=10;
const  int NoError = 0,    // Error constants 
       IllMaxZeroNo = 1, 
       NotAllZeros = 2;
const  int MaxCount = 400000;

//----------------------------------------------------------------------------
// Definition of the function f(x) and the derivate df(x)
//     Test function f = cosh(x) + 10 * x^2 * sin(x)^2 - 34                    
//----------------------------------------------------------------------------

/*
interval<double,filib::native_switched,filib::i_mode_extended> f(interval<double,filib::native_switched,filib::i_mode_extended> x) {
  return sin(1/x);  
}

interval<double,filib::native_switched,filib::i_mode_extended> df(interval<double,filib::native_switched,filib::i_mode_extended> x) {
  return -cos(1/x)/sqr(x);  
}
*/


// Zeros at -2, 1 and 3
interval<double,filib::native_switched,filib::i_mode_extended> f(interval<double,filib::native_switched,filib::i_mode_extended> x) {
  return power(x,3) - 2.0*sqr(x) - 5.0*x + 6.0;
}

interval<double,filib::native_switched,filib::i_mode_extended> df(interval<double,filib::native_switched,filib::i_mode_extended> x) {
  return 3.0*sqr(x) - 4.0*x - 5.0;
}


/*
interval<double,filib::native_switched,filib::i_mode_extended> f(interval<double,filib::native_switched,filib::i_mode_extended> x) {
  return ( cosh(x)+10*sqr(x)*sqr(sin(x))-34 );
}

interval<double,filib::native_switched,filib::i_mode_extended> df(interval<double,filib::native_switched,filib::i_mode_extended> x) {
  return( sinh(x)+20*x*sqr(sin(x))+20*sqr(x)*sin(x)*cos(x) );
}
*/

/*
interval<double,filib::native_switched,filib::i_mode_extended> f(interval<double,filib::native_switched,filib::i_mode_extended> x) {
  return power(x,4) - 12*power(x,3) + 47*sqr(x) - 60*x;
}

interval<double,filib::native_switched,filib::i_mode_extended> df(interval<double,filib::native_switched,filib::i_mode_extended> x) {
  return 4*power(x, 3) - 36*sqr(x) + 94*x - 60;
}
*/

/*
interval<double,filib::native_switched,filib::i_mode_extended> f(interval<double,filib::native_switched,filib::i_mode_extended> x) {
  return power(x,3) - 199.01*sqr(x) + 9900.99*x - 99;
}

interval<double,filib::native_switched,filib::i_mode_extended> df(interval<double,filib::native_switched,filib::i_mode_extended> x) {
  return 3*sqr(x) - 398.02*x + 9900.99;
}
*/
/*
interval<double,filib::native_switched,filib::i_mode_extended> f(interval<double,filib::native_switched,filib::i_mode_extended> x) {
  return cos(x);
}

interval<double,filib::native_switched,filib::i_mode_extended> df(interval<double,filib::native_switched,filib::i_mode_extended> x) {
  return -sin(x);
}
*/

/*
interval<double,filib::native_switched,filib::i_mode_extended> f(interval<double,filib::native_switched,filib::i_mode_extended> x) {
  return power(x,3) - 2*sqr(x) - 5*x + 6;
}

interval<double,filib::native_switched,filib::i_mode_extended> df(interval<double,filib::native_switched,filib::i_mode_extended> x) {
  return 3*sqr(x) - 4*x - 5;
}
*/
/*
interval<double,filib::native_switched,filib::i_mode_extended> f(interval<double,filib::native_switched,filib::i_mode_extended> x) {
  return sqr(sin(x));
}

interval<double,filib::native_switched,filib::i_mode_extended> df(interval<double,filib::native_switched,filib::i_mode_extended> x) {
  return 2*sin(x)*cos(x);
}
*/

/*
interval<double,filib::native_switched,filib::i_mode_extended> f(interval<double,filib::native_switched,filib::i_mode_extended> x) 
{
  return sqr(x)-2;
}

interval<double,filib::native_switched,filib::i_mode_extended> df(interval<double,filib::native_switched,filib::i_mode_extended> x) 
{
  return 2*x;
}
*/

//----------------------------------------------------------------------------
// main function xinewton
//----------------------------------------------------------------------------

void xinewton(fun f, fun df,
	      interval<double,filib::native_switched,filib::i_mode_extended> fy, interval<double,filib::native_switched,filib::i_mode_extended> y, double eps, int yUnique, 
	      list* &zerolist, int& zerono)
{
   if (zerono > MaxZeroNo) return;
   interval<double,filib::native_switched,filib::i_mode_extended>* V[3];
   Xinterval< interval<double,filib::native_switched,filib::i_mode_extended> > z;
   double c;
   interval<double,filib::native_switched,filib::i_mode_extended> ci;
   int i;
   int absorbed;
   list* pointer;
   pointer = zerolist;

   if (!in(0.0,fy)) return;

   c = mid(y);
   ci=interval<double,filib::native_switched,filib::i_mode_extended>(c);
   z = c - f(ci)%df(y);

   interval<double,filib::native_switched,filib::i_mode_extended> V1, V2;
   // V = y & z;
   extIntersect(y,z,V1,V2);
   V[1] = &V1;
   V[2] = &V2;

   if (V1 == y) {                      // bisection
      V1 = interval<double,filib::native_switched,filib::i_mode_extended>(inf(y),c);
      V2 = interval<double,filib::native_switched,filib::i_mode_extended>(c,sup(y));
   }

   if ( (!V1.isEmpty() ) && (V2.isEmpty()))
      yUnique = yUnique || interior(V1, y);
   else
      yUnique = 0;

   for (i=1;i<=2;i++) {
      if (V[i]->isEmpty())  continue; 
      if (relDiam(*V[i])<=eps) {
         fy=f(*V[i]);
         if (in(0.0,fy)) {
            zerono ++;
            if (zerono > MaxZeroNo) return;
	    
            absorbed=0;
            pointer=zerolist;
            //- Try to absorb V[i] by an already computed element of list -
            if (zerolist != NULL) {
               while ((pointer != NULL) && (!absorbed)) {
                  absorbed = !( (sup(*V[i])<inf(pointer->intval)) ||
                                (sup(pointer->intval)<inf(*V[i]) ));
                  if (absorbed) { 
                     pointer->intval = hull((pointer->intval), *V[i]);
                     pointer->info = 0;
                     zerono --;
                  }
                  pointer = pointer -> next;
               }
            }

            if (!absorbed) {   // Store x in the resulting list
               pointer=zerolist;
               if (zerolist != NULL) {
                  while (pointer->next != NULL) pointer = pointer->next;
                  list* insert = new list;
                  pointer->next = insert;
                  insert->next = NULL;
                  insert->intval = *V[i];
                  insert->info = yUnique; 
               } else {
                  zerolist = new list;
                  zerolist->next = NULL;
                  zerolist->intval = *V[i];
                  zerolist->info = yUnique;         
               }
            }

         }
       } else {	
         xinewton(f, df, f(*V[i]),*V[i],eps,yUnique,zerolist,zerono); 
       }
   }
}

// --------------------------------------------------------------------
// ---   function AllZerosErrMsg (error message)                    ---
// --------------------------------------------------------------------

char* AllZerosErrMsg (int Err)
{ 
   static char Msg[80] = "";

   switch (Err) {
      case NoError:      break;
      case IllMaxZeroNo: sprintf(Msg,"Error: Parameter for maximum number of zeros must lie in 1,...,%1d!", MaxCount); 
                         break;
      case NotAllZeros:  sprintf(Msg,"Warning: Not all zeros found due to the user limit of %l1d zero(s)!",MaxZeroNo);
                         break;
      default:           sprintf(Msg,"Error Code not defined");
   }

   return (Msg);
}

// --------------------------------------------------------------------
// ---   function VerificationStep                                  ---
// --------------------------------------------------------------------

static void VerificationStep(fun f, fun df,
			     interval<double,filib::native_switched,filib::i_mode_extended>& y, int& unique)
{
   const int kmax= 10;
   interval<double,filib::native_switched,filib::i_mode_extended> yIn, yOld, fc, dfy;
   double c,eps;
   int k;

   k = 0; 
   yIn = y; 
   eps = 0.25; 
   unique = 0;

   while (!unique && (k < kmax) ) {
      yOld = blow(y,eps);
      dfy = df(y); 
      if (in(0.0,dfy)) break;
      k++;
      c = mid(yOld);
      fc=f(interval<double,filib::native_switched,filib::i_mode_extended>(c));
      y = c - fc / dfy;
      if (disjoint(y, yOld)) break;
      unique = interior(y,yOld);
      y = intersect(y, yOld);
      if (y == yOld) eps=eps*8.0;
   }
   if (!unique) y = yIn;
}

// --------------------------------------------------------------------
// ---   function AllZeros (root finding and verification)          ---
// --------------------------------------------------------------------


void AllZeros(fun f, fun df,
	      interval<double,filib::native_switched,filib::i_mode_extended> Start, double Epsilon, list* &zerolist, 
	      int& NumberOfZeros, int& Err, int MaxNumberOfZeros) 
{

   double MinEpsilon;
   list* pointer;

   if (1<=MaxNumberOfZeros && MaxNumberOfZeros <= MaxCount) {
      MaxZeroNo = MaxNumberOfZeros;
      Err = NoError; 
      NumberOfZeros = 0;
      MinEpsilon = filib::primitive::succ(1.0)-1.0;			// 1ulp
      if (Epsilon < MinEpsilon)
         Epsilon = MinEpsilon;

      xinewton(f, df, f(Start), Start, Epsilon, 0 , zerolist, NumberOfZeros);
      
      if (NumberOfZeros > MaxNumberOfZeros) {	
	Err = NotAllZeros; 
	NumberOfZeros = MaxNumberOfZeros;
      }
   } else {
     Err = IllMaxZeroNo;
     NumberOfZeros = 0;
   }
   
   pointer = zerolist;
   while (pointer != NULL) {
     if (pointer->info==0) {
       VerificationStep(f, df, pointer->intval,pointer->info); 
     }
     pointer = pointer->next;
   }
}

// --------------------------------------------------------------------
// ---   function main                                              ---
// --------------------------------------------------------------------

int main ()
{
  filib::fp_traits<double>::setup();

  unsigned int k;
  interval<double,filib::native_switched,filib::i_mode_extended>::precision(15);
  
   interval<double,filib::native_switched,filib::i_mode_extended> Searchinterval;
   double Tolerance;
   int NumberOfZeros, Error;
   list* Zero;
   Zero = NULL;

   cout << "Extended-interval<double,filib::native_switched,filib::i_mode_extended>-Newton method in C++ with fi_lib++" << endl;
   cout << "====================================================" << endl << endl;
 
   cout << "Computing all zeros of the function f(x) = power(x,3) - 2.0*sqr(x) - 5.0*x + 6.0" 
        << endl;
   cout << "Search interval<double,filib::native_switched,filib::i_mode_extended> (e.g. '[-10, 10]'): " ;
   cin >> Searchinterval;
   cout << endl << "Search interval<double,filib::native_switched,filib::i_mode_extended> = " << Searchinterval << endl;
   cout << "Tolerance (relative) (e.g. '1e-3' or '1e-15'): ";
   cin >> Tolerance;
   cout << endl;
   cout << "Iterations: ";
   cin >> k;
      

   timer thetimer;
   thetimer.start();
   for (int i=0; i<k; i++) {

     if (Zero != 0) {
       delete Zero;
       Zero = 0;
     }
     
     AllZeros(f,df,Searchinterval, Tolerance, Zero, NumberOfZeros, Error, 40000);
   }
   
   thetimer.stop();


   if (Zero==NULL)
     cout << "Function contains no zeros in the search interval<double,filib::native_switched,filib::i_mode_extended>!" << endl;
   else {
     cout << "Ranges for zeros:" << endl;
     while (Zero != NULL) {
       cout << Zero->intval << endl;
       if (Zero->info)
          cout << " encloses a locally unique zero !" << endl;
       else
          cout << " may contain a zero (not verified unique)!"<< endl;
       Zero = Zero->next;
     }
   }
   cout << endl << NumberOfZeros << " interval<double,filib::native_switched,filib::i_mode_extended> enclosure(s)" << endl;
   if (Error) cout << endl << AllZerosErrMsg(Error) << endl;

   cout << endl << "Time: " << thetimer.secs_elapsed() << " sec." << endl;

   return 0;
}






