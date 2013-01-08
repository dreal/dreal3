/*
   author: Tomasz Kapela, Sept. 2007
   the file provides a quick tutorial on using template class Interval
*/

#include <iostream>
#include <iomanip>

#include "capd/interval/Interval.hpp"
#include "capd/rounding/DoubleRounding.h"
#include "capd/rounding/IntRounding.h"

// template class Interval has two parameters
// type of endpoints and class that switches rounding modes
// The following lines defines new names for intervals with endpoints type: double, int, MpfrClass correspondigly
typedef capd::intervals::Interval< double, capd::rounding::DoubleRounding>  DInterval;
typedef capd::intervals::Interval< int, capd::rounding::IntRounding> ZInterval;

// For the next line to work you need CAPD library compiled with Multiple Precission support 
//typedef capd::intervals::Interval< capd::multiPrec::MpfrClass> MPInterval;

// Because most of the functions are common for intervals with arbitrary endpoints 
// we use general type interval in the following sections. 
 typedef DInterval interval;

using namespace std;

void basicsTest()
{  
  // We construct five intervals 
   interval a,
            b(1.0),
            c(2.0, 3.0),
            d(c),
            e(2.5, 3.0);
            
  cout <<"\n\n Basic functions: \n ======================== \n * constructors,\n";
  cout << " a() = " << a << "\n b(1.0) = " << b << "    c(2.0,3.0) = " << c 
        << "    d(c) = " << d << "   e(2.5,3) = " << e;
         
  // These functions return endpoints of an interval as double or as zero width interval
  cout << "\n\n * acces to interval bounds,"
        << "\n c.leftBound() = "  << c.leftBound() 
        << "   c.left() = "   << c.left()
        << "   left(c) = "  << left(c)
         << "\n c.rightBound() = "  << c.rightBound()       
        << "   c.right = "   << c.right()
        << "   right = "  << right(c);
   
  // These funtions compare two intervals or an interval and a number 
   cout << "\n\n * inclusions, relations (values 1 = true, 0 = false) "
        << "\n b==c : " << (b==c)  << "  b!=c : " << (b!=c) 
        << "  b>c : " << (b>c)    << "  b>=c : " << (b>=c) 
        << "  b<c : " << (b<c)    << "  b<=c : " << (b<=c) 
        << "\n\n b==1.0 : " << (b==1.0)  << "  b!=1.0 : " << (b!=1.0) 
        << "  b>1.0 : " << (b>1.0)    << "  b>=1.0 : " << (b>=1.0) 
        << "  b<1.0 : " << (b<1.0)    << "  b<=1.0 : " << (b<=1.0);
   
   //These functions check inclusions between intervals
   cout << "\n\n " <<  c <<" contains " << e <<" :  " << c.contains(e)
        << "     "<<c <<" containsInInterior " << e << " : " << c.containsInInterior(e)
        << "\n "<<c << " contains 2.5 : " << c.contains(2.5)
        << "\n "<<d << " subset " << c << " : " << d.subset(c)
        << "          " << d << " subsetInterior " << c << " : " << d.subsetInterior(c)
         ;
         
   // You can read interval from a given stream (in this case from stringstream, 
   //  but the same aply to standard input stream cin)
   std::istringstream myStr("[3.21312312, 4.324324324]");
   myStr >> a;
   cout << "\n\n interval read from string \"[3.21312312, 4.324324324]\" = " << a;
   
   // We split interval c into two intervals: center a and zero centered interval b,
   // so that c is subset of a + b 
   c.split(a,b);
   cout << "\n\n " << d << " = "  << a << "+" << b;
   
   // We can also split interval into center and radius 
   double r;
   c = d;
   split(c, r);
   cout << "\n " << d << " = K(" << c << "," <<  r << ")";
   cout << endl;

}
 
void arithmeticOperatorsTest()
{
  cout <<"\n\n Arithmetic operations \n ===============================\n";
  interval  b(1.0,2.0), 
            c(2.0, 3.0),
            d(c);
  // We can do all arithmetic operations on intervals exactly in the same way as on doubles.
  interval result = (c - d) * b / 3.0;
  cout << "\n (c - d) * b / 3.0 = " << result;
  
  result += b * c;
  cout << "\n result = " << result;
}

void functionsTest()
{
   /* These functions do not work with ZInterval (i.e. intervals with integer end points) */

   cout << "\n\n Elementary funtions : \n============================";
   double PI = interval::pi().leftBound();
   interval x(PI/6, PI/4);
   cout << setprecision(16) << "\n\n x = [pi/6,pi/4] = " << x
     << "\n sin x = " << sin(x)
     << "\n cos x = " << cos(x)
     << "\n tan x = " << tan(x)
     << "\n cot x = " << cot(x);
   interval y(1.0, 2.0);
   cout << setprecision(16) << "\n\n y = " << y
     << "\n exp(y)= " << exp(y)
     << "\n log(y)= " << log(y)
     << "\n y^[2,3] = " << power(y, interval(2,3));
   y = interval(-3, -2);
   cout << "\n\n y = " << y
     << "\n y^3 = " << (y^3)
    << "\n y^2 = " << (y^2);
   y = interval(4, 9);
   cout << "\n\n y = " << y
     << "\n y^-1.5 = " << (power(y,interval(-1.5)));
   cout << endl;
}



int main(int, char**)
{
  try{
   basicsTest();
   arithmeticOperatorsTest();
   functionsTest();
    
   } catch(capd::intervals::IntervalError<double> &e){
     
      cout <<" interval Error : " << e.what();
   }
   catch(std::runtime_error &e){
     
      cout << e.what();
   }

   return 0;
}


