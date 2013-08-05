/*
   author: Tomasz Kapela, Sept. 2007
   the file provides a quick tutorial on using template class Interval
*/
#include <iostream>
#include <iomanip>
#include "capd/intervals/Interval.hpp"
#include "capd/rounding/DoubleRounding.h"
#include "capd/rounding/IntRounding.h"

// template class Interval has two parameters
// type of endpoints and class that switches rounding modes
// The following lines defines new names for intervals with endpoints type: double, int, MpFloat correspondigly
typedef capd::intervals::Interval< double, capd::rounding::DoubleRounding>  DInterval;
typedef capd::intervals::Interval< int, capd::rounding::IntRounding> ZInterval;
// For the next line to work you need CAPD library compiled with Multiple Precission support 
// typedef capd::DIntervals::Interval< capd::MpFloat> MPInterval;
// Because most of the functions are common for intervals with arbitrary endpoints 
// we use as an example  DInterval in the following sections.
using namespace std;
void basicsTest(){
  // We construct five intervals
  DInterval a;                   // a = [0.0, 0.0] (*)
  DInterval b(1.0);              // b = [1.0, 1.0]
  DInterval c(2.0, 3.0);         // c = [2.0, 3.0]
  DInterval d(c);                // d = [2.0, 3.0]
  DInterval e("2.5","3.0");      // e = [2.4999999999999996, 3.0000000000000004]              cout <<"\n\n Basic functions: \n ======================== \n * constructors,\n";  cout << " a() = " << a << " b(1.0) = " << b << "    c(2.0,3.0) = " << c        << "\n d(c) = " << d << "   e(\"2.5\",\"3\") = " << e ;  cout << "\n diam([1.0,1.0]) " << diam(DInterval("1.0", "1.0")) ;
  // These functions return endpoints of an DInterval as double or as zero width DInterval  cout << "\n\n * acces to interval bounds,"        << "\n c.leftBound() = "  << c.leftBound()         << "   c.left() = "   << c.left()        << "   left(c) = "  << left(c)         << "\n c.rightBound() = "  << c.rightBound()               << "   c.right = "   << c.right()        << "   right = "  << right(c);  // These funtions compare two DIntervals or an DInterval and a number   cout << "\n\n * inclusions, relations (values 1 = true, 0 = false) "        << "\n b==c : " << (b==c)  << "  b!=c : " << (b!=c)         << "  b>c : " << (b>c)    << "  b>=c : " << (b>=c)         << "  b<c : " << (b<c)    << "  b<=c : " << (b<=c)         << "\n\n b==1.0 : " << (b==1.0)  << "  b!=1.0 : " << (b!=1.0)         << "  b>1.0 : " << (b>1.0)    << "  b>=1.0 : " << (b>=1.0)         << "  b<1.0 : " << (b<1.0)    << "  b<=1.0 : " << (b<=1.0);   //These functions check inclusions between DIntervals   cout << std::boolalpha << "\n\n " <<  c <<" contains " << e <<" :  " << c.contains(e)        << "     "<<c <<" containsInInterior " << e << " : " << c.containsInInterior(e)        << "\n "<<c << " contains 2.5 : " << c.contains(2.5)        << "\n "<<d << " subset " << c << " : " << d.subset(c)        << "          " << d << " subsetInterior " << c << " : " << d.subsetInterior(c);
   // The output depends on parameters of a stream e.g precision.
   // Interval bounds are rounded to the nearest floating point with given
   // number of decimal places
   cout << "\n\n Output with various precisions : ";
   DInterval x(1.0, 2.0);
   cout << x << "  ";                          // output: [1,2]
   cout << fixed << setprecision(6) << x;      // output: [1.000000,2.000000]
   // You can read interval from a given stream (in this case from stringstream,   //  but the same aply to standard input stream cin)   std::istringstream myStr("[3.21312312, 4.324324324]");   myStr >> a;   cout << "\n\n Interval read from string \"[3.21312312, 4.324324324]\" = " << a;
   // To save and then restore the same interval you can set high enough precision (at least 17 for doubles)
   // or use bit or hex format for text streams or binary format.

   x = DInterval(-1.0,2.0);
   cout << "\n\n [-1,2] in bit format : ";
   bitWrite(cout, x);
   cout << "\n [-1,2] in hex format : ";
   hexWrite(cout, x) << endl;

   std::stringstream inout("", ios::binary | ios::in | ios::out );
   binWrite(inout, x);
   binRead(inout, a);
   cout << "\n [-1,2] written and read from binary stream : " << a;


   DInterval ia(1.0, 10.0), ib(3.0, 5.0);
   cout << "\n\n imin([1,10],[3,5]) = " << imin(ia,ib);                  // result:  [1.0, 5.0]
   cout << "\n imax([1,10],[3,5]) = " << imax(ia,ib);                  // result:  [3.0, 10.0]


   // We split DInterval c into two intervals: center a and zero centered DInterval b,   // so that c is subset of a + b    c.split(a,b);   cout << "\n\n " << d << " = "  << a << "+" << b;
   // We can also split interval into center and radius   double r;   c = d;   split(c, r);   cout << "\n " << d << " = K(" << c << "," <<  r << ")";   cout << endl;
}
 
void arithmeticOperatorsTest(){  cout <<"\n\n Arithmetic operations \n ===============================\n";  DInterval  b(1.0,2.0),            c(2.0, 3.0),            d(c);  // We can do all arithmetic operations on intervals exactly in the same way as on doubles.  DInterval result = (c - d) * b / 3.0;  cout << "\n (c - d) * b / 3.0 = " << result;  result += b * c;  cout << "\n result = " << result;}
void functionsTest(){   /* These functions do not work with ZInterval (i.e. intervals with integer end points) */   cout << "\n\n Elementary funtions : \n============================";   double PI = DInterval::pi().leftBound();   DInterval x(PI/6, PI/4);   cout << setprecision(16) << "\n\n x = [pi/6,pi/4] = " << x     << "\n sin x = " << sin(x)     << "\n cos x = " << cos(x)     << "\n tan x = " << tan(x)     << "\n cot x = " << cot(x);
   DInterval y(1.0, 2.0);   cout << setprecision(16) << "\n\n y = " << y     << "\n exp(y)= " << exp(y)     << "\n log(y)= " << log(y)     << "\n y^[2,3] = " << power(y, DInterval(2,3));
   y = DInterval(-3, -2);   cout << "\n\n y = " << y     << "\n y^3 = " << (y^3)    << "\n y^2 = " << (y^2);
   y = DInterval(4, 9);   cout << "\n\n y = " << y     << "\n y^-1.5 = " << (power(y,DInterval(-1.5)));   cout << endl;}
int main(int, char**){  try{   basicsTest();   arithmeticOperatorsTest();   functionsTest();
  } catch(capd::intervals::IntervalError<double> &e){      cout <<" Interval Error : " << e.what();  } catch(std::runtime_error &e){      cout << e.what();  }   return 0;}


