
#include <cstdlib>
#include <iostream>
#include <iomanip>
#include <cmath>



#include "capd/rounding/DoubleRounding.h"
#include "capd/interval/DoubleInterval.h"
#include "capd/interval/IntervalError.h"

using namespace std;


namespace capd{
namespace test{


void basicsTest()
{
   interval a,
            b(1.0),
            c(2.0, 3.0),
            d(c),
            e(2.5, 3.0);
            
   cout <<"\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n Base functions: constructors, acces to interval bounds, inclusions, relations";
   cout << " a() = " << a << "\n b(1.0) = " << b << " c(2.0,3.0) = " << c 
        << " d(c) = " << d << " e(2.5,3) = " << e 
        << "\n\n c.leftBound() = "  << c.leftBound() 
        << "   c.left() = "   << c.left()
        << "   left(c) = "  << left(c)
         << "\n c.rightBound() = "  << c.rightBound()       
        << "   c.right = "   << c.right()
        << "   right = "  << right(c)
        << "\n\n b==c : " << (b==c)  << "  b!=c : " << (b!=c) 
        << "  b>c : " << (b>c)    << "  b>=c : " << (b>=c) 
        << "  b<c : " << (b<c)    << "  b<=c : " << (b<=c) 
        << "\n\n b==1.0 : " << (b==1.0)  << "  b!=1.0 : " << (b!=1.0) 
        << "  b>1.0 : " << (b>1.0)    << "  b>=1.0 : " << (b>=1.0) 
        << "  b<1.0 : " << (b<1.0)    << "  b<=1.0 : " << (b<=1.0)
        << "\n\n " <<  c <<" contains " << e <<" :  " << c.contains(e)
        << "     "<<c <<" containsInInterior " << e << " : " << c.containsInInterior(e)
        << "\n "<<c << " contains 2.5 : " << c.contains(2.5)
        << "\n "<<d << " subset " << c << " : " << d.subset(c)
        << "   " << d << " subsetInterior " << c << " : " << d.subsetInterior(c)
         ;
   std::istringstream myStr("[3.21312312, 4.324324324]");
   myStr >> a;
   cout << "\n\n interval read from string \"[3.21312312, 4.324324324]\" = " << a;
   
   c.split(c,b);

   cout << "\n\n " << d << " = "  << c << "+" << b;
   double r;
   c = d;
   split(c, r);
   cout << "\n " << d << " = K(" << c << "," <<  r << ")";
   cout << endl;

}
 
void operatorsTest()
{
  interval a,
            b(1.0), 
            c(2.0, 3.0),
            d(c),
            e(-1.0, 4.0),
            f(4.0, 5.0);
   cout <<"\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n";
  
   cout << " a = " << a << "\n b = " << b << " c = " << c 
        << " d = " << d << " e = " << e << " f = " << f;
   
   cout << "\n c += e " << (c += e);
   cout << "   c -= e " << (c -= e);
   cout << "\n c *= e " << (c *= e);
   cout << "   c /= f " << (c /= f);
   cout << "\n b *(c+(-d)) / f - e = " << (b *(c+(-d))/ f  - e); 
   interval y = interval(-3, -2);
   cout << "\n y+3 = " << y+3 << " y-3 = " << y-3 << " y*3 = " << y*3<< " y/3 = " << y/3
        << "\n 3+y = " << 3+y << " 3-y = " << 3-y << " 3*y = " << y*3<< " 3/y = " << 3/y;

   cout << endl;
}

void functionsTest()
{
  interval a,
            b(1.0),
            c(2.0, 3.0),
            d(c),
            e(-1.0, 4.0),
            f(4.0, 5.0);

   cout <<"\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n";
   cout << " a = " << a << "\n b = " << b << " c = " << c 
        << " d = " << d << " e = " << e << " f = " << f;

   double PI = interval::pi().leftBound();
   interval x(PI/6, PI/4);
   cout << setprecision(16) << "\n\n x = [pi/6,pi/4] = " << x
        << "\n sin = " << sin(x)
        << "\n cos = " << cos(x)
        << "\n tan = " << tan(x)
        << "\n cot = " << cot(x);
   x = interval(1.0/3, 1.0/2);
   cout << setprecision(16) << "\n\n x = [1/3,1/2] = " << x
        << "\n atan = " << atan(x)
        << "\n asin = " << asin(x)
        << "\n acos = " << acos(x);
   interval y(1.0, 2.0);
   cout << setprecision(16) << "\n\n y = " << y
        << "\n exp = " << exp(y)
        << "\n log = " << log(y)
        << "\n y^[2,3] = " << power(y, interval(2,3));
   y = interval(-3, -2);
   cout << "\n\n y = " << y
        << "\n y^3 = " << (y^3)
        << "\n y^2 = " << (y^2)
          << "\n e^2 = " << (e^2);
   y = interval(4, 9);
   cout << "\n\n y = " << y
        << "\n y^-1.5 = " << (power(y,interval(-1.5)));

   cout << endl;
}

bool multiplicationTest()
{
  interval a(1.0, 2.0);
  
  cout << "\n a = " << a;
  cout << "\n ++ a * [1,2] = "  << a * interval(1., 2.);
  cout << "\n +- a * [-2,-1] = " << a * interval(-2., -1.);
  cout << "\n +? a * [-3,2] " << a * interval(-3., 2.);

   a = interval(-2.0, -1.0);
  cout << "\n a = " << a;
  cout << "\n -+ a * [1,2] = "  << a * interval(1., 2.);
  cout << "\n -- a * [-2,-1] = " << a * interval(-2., -1.);
  cout << "\n -? a * [-3,2] " << a * interval(-3., 2.);
 
  a = interval(-1.0, 3.);
  cout << "\n a = " << a;
  cout << "\n ?+ a * [1,2] = "  << a * interval(1., 2.);
  cout << "\n ?- a * [-2,-1] = " << a * interval(-2., -1.);
  cout << "\n ?? a * [-3,2] " << a * interval(-3., 2.);
  
  return true;
}

bool multiplicationTest2()
{
  interval a(1.0, 2.0);
  
  cout << "\n a = " << a;
  cout << "\n ++ a *= [1,2] = "  << (a *= interval(1., 2.));

 a=interval(1.0, 2.0);
  cout << "\n +- a *= [-2,-1] = " << (a *= interval(-2., -1.));
 a=interval(1.0, 2.0);
  cout << "\n +? a *= [-3,2] " << (a *= interval(-3., 2.));

   a = interval(-2.0, -1.0);
  cout << "\n a = " << a;
  cout << "\n -+ a * [1,2] = "  << (a *= interval(1., 2.));
   a = interval(-2.0, -1.0);
  cout << "\n -- a * [-2,-1] = " << (a *= interval(-2., -1.));
   a = interval(-2.0, -1.0);
  cout << "\n -? a * [-3,2] " << (a *= interval(-3., 2.));
 
  a = interval(-1.0, 3.);
  cout << "\n a = " << a;
  cout << "\n ?+ a *= [1,2] = "  << (a *= interval(1., 2.));
  a = interval(-1.0, 3.);
  cout << "\n ?- a *= [-2,-1] = " << (a *= interval(-2., -1.));
  a = interval(-1.0, 3.);
  cout << "\n ?? a *= [-3,2] " << (a *= interval(-3., 2.));
  
  return true;
}

bool scalarTest()
{
  interval a(1.0, 2.0);
  
  cout << "\n a = " << a;
  cout << "\n  a * 2 = "  << (a * 2.);
  cout << "\n  a * 2 = "  << (a * 2);
  cout << "\n  2 * a = "  << (2. * a);

  cout << "\n  a / 2 = "  << (a / 2.);
  cout << "\n  a / 2 = "  << (a / 2);
  cout << "\n  2 / a = "  << (2. / a);

  cout << "\n  a + 2 = "  << (a + 2.);
  cout << "\n  a + 2 = "  << (a + 2);
  cout << "\n  2 + a = "  << (2. + a);

  cout << "\n  a - 2 = "  << (a - 2.);
  cout << "\n  a - 2 = "  << (a - 2);
  cout << "\n  2 - a = "  << (2. - a);


  return true;
}

bool divisionTest()
{
  interval a(1.0, 2.0);
  
  cout << "\n a = " << a;
  cout << "\n ++ a / [1,2] = "  << a / interval(1., 2.);
  cout << "\n +- a / [-2,-1] = " << a / interval(-2., -1.);

   a = interval(-2.0, -1.0);
  cout << "\n a = " << a;
  cout << "\n -+ a / [1,2] = "  << a / interval(1., 2.);
  cout << "\n -- a / [-2,-1] = " << a / interval(-2., -1.);
 
  a = interval(-1.0, 3.);
  cout << "\n a = " << a;
  cout << "\n ?+ a / [1,2] = "  << a / interval(1., 2.);
  cout << "\n ?- a / [-2,-1] = " << a / interval(-2., -1.);
  cout <<"\n";
  return true;
}

bool divisionTest2()
{
  interval a(1.0, 2.0);
  
  cout << "\n a = " << a;
  cout << "\n ++ a /= [1,2] = "  << (a /= interval(1., 2.));
   a = interval(1.0, 2.0);
  cout << "\n +- a /= [-2,-1] = " << (a /= interval(-2., -1.));

   a = interval(-2.0, -1.0);
  cout << "\n a = " << a;
  cout << "\n -+ a /= [1,2] = "  << (a /= interval(1., 2.));
   a = interval(-2.0, -1.0);
  cout << "\n -- a /= [-2,-1] = " << (a /= interval(-2., -1.));
 
  a = interval(-1.0, 3.);
  cout << "\n a = " << a;
  cout << "\n ?+ a /= [1,2] = "  << (a /= interval(1., 2.));
  a = interval(-1.0, 3.);
  cout << "\n ?- a /= [-2,-1] = " << (a /= interval(-2., -1.));
  cout <<"\n";
  return true;
}



int main()
{
  try{
   basicsTest();
   operatorsTest();
   functionsTest();
   interval a(3, -1);
   scalarTest();
   multiplicationTest();
   multiplicationTest2();

   divisionTest();
   divisionTest2();
   } catch(capd::intervals::IntervalError<double> &e)
   {
      cout <<" interval Error : " << e.what();
   }

   catch(std::runtime_error &e)
   {
      cout << e.what();
   }

   return 0;
}


}}// namespace capd::test

int main()
{
   return capd::test::main();
}
