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
#include <iomanip>
#include <vector>
#include <iostream>
#include <ctime>

#include "xinewton.h"
#include "interval/interval.hpp"

using namespace xinewton;

using std::setprecision;

typedef filib::interval<double,filib::native_switched,filib::i_mode_extended_flag> interval;

interval f0(interval x) {
  return sqr(x)-3.0*x;
}

interval df0(interval x) {
  return 2.0*x - 3.0;
}


// zeros at 0, 3, 4 and 5 (see C-XSC Toolbox p.111)
interval f1(interval x) {
  return power(x,4) - 12.0*power(x,3) + 47.0*sqr(x) - 60.0*x;
}

interval df1(interval x) {
  return 4.0*power(x, 3) - 36.0*sqr(x) + 94.0*x - 60.0;
}


// Zeros at -2, 1 and 3
interval f2(interval x) {
  return power(x,3) - 2.0*sqr(x) - 5.0*x + 6.0;
}

interval df2(interval x) {
  return 3.0*sqr(x) - 4.0*x - 5.0;
}


interval f3(interval x) {
  return ( cosh(x)+10.0*sqr(x)*sqr(sin(x))-34.0 );
}

interval df3(interval x) {
  return( sinh(x)+20.0*x*sqr(sin(x))+20.0*sqr(x)*sin(x)*cos(x) );
}


interval f4(interval x) {
  return sqr(sin(x)) - cos(sqr(x));  
}

interval df4(interval x) {
  return 2.0*cos(x)*sin(x) + 2.0*x*sin(sqr(x));
}


interval f5(interval x) {
  return power(x,7)-power(x,4)-12.0;
}

interval df5(interval x) {
  return 7.0*power(x,6)-4.0*power(x,3);
}

interval f6(interval x) {
  return (power(x,4)-10.0*power(x,3)-13.0*sqr(x)+118.0*x+120.0)/(sqr(x)+2.0);
}



interval df6(interval x) {
  return (4.0*power(x,3)-30.0*sqr(x)-26.0*x+118.0 - ((power(x,4)-10.0*power(x,3)-13.0*sqr(x)+118.0*x+120.0)/(sqr(x)+2.0))*2.0*x)/(sqr(x)+2.0);
}

// algebraisch vereinfachte Form:
//  interval df6(interval x) {
//    return (2*power(x,5)-10.0*power(x,4)+8.0*power(x,3)-178.0*sqr(x)-292.0*x+236.0)/(power(x,4)+4.0*sqr(x)+4.0);
//  }



interval f7(interval x) {
  return (sqr(x)-1.0)/(sqr(x)+1.0);
}

interval df7(interval x) {
  return (2.0*x - (sqr(x)-1.0)/(sqr(x)+1.0) * 2.0*x) / (sqr(x)+1.0);
}

interval f8(interval x)
{
  return sin(x);
}

interval df8(interval x) {
  return cos(x);
}

int main() 
{
  filib::fp_traits<double>::setup();

  using std::cout;

  interval::precision(15);
  cout << setprecision(15);

  try
  {
        struct testCase {
		XINewton<interval> xnewton;
		interval (*f)(interval);
		interval (*df)(interval);
		interval initial;
		double eps;
		unsigned int iterations;

		testCase(
			XINewton<interval> Rxnewton,
			interval (*Rf)(interval),
			interval (*Rdf)(interval),
			interval Rinitial,
			double Reps,
			unsigned int Riterations
			)
		: xnewton(Rxnewton), f(Rf), df(Rdf), initial(Rinitial), eps(Reps),
		iterations(Riterations)
		{}

		void exec()
		{
			xnewton.allZeros(f,df,initial,eps);
		}
		void print()
		{
			xnewton.printZeros();
		}
	};

	testCase cases[] =
	{
		testCase(XINewton<interval>(),f0,df0,interval(-100,100),1e-15,1000),
		testCase(XINewton<interval>(),f1,df1,interval(-100,100),1e-15,1000),
		testCase(XINewton<interval>(),f2,df2,interval(-100,100),1e-15,1000),
		testCase(XINewton<interval>(),f3,df3,interval(-100,100),1e-15,1000),
		testCase(XINewton<interval>(),f4,df4,interval(-10 ,10 ),1e-15,1000),
		testCase(XINewton<interval>(),f5,df5,interval(-100,100),1e-15,1000),
		testCase(XINewton<interval>(),f6,df6,interval(-100,100),1e-15,1000),
		testCase(XINewton<interval>(),f7,df7,interval(-100,100),1e-15,1000),
		testCase(XINewton<interval>(),f8,df8,interval(-100,100),1e-100,1000)
	};

	for ( size_t k = 0; k < sizeof(cases)/sizeof(cases[0]); ++k )
	{
		std::clock_t before = std::clock();

		testCase & curCase = cases[k];

		for (unsigned int i=0; i< curCase.iterations; i++)
			curCase.exec();

		std::clock_t after = std::clock();

		cout << "Clocks ticks:              " << (after-before) << endl;
		cout << "Ticks per second:          " << CLOCKS_PER_SEC << endl;
		cout << "Total CPU time:            " << static_cast<double>(after-before)/
			static_cast<double>(CLOCKS_PER_SEC) << " seconds" << endl;
		cout << "Iterations:                " << curCase.iterations << endl;
		cout << "Mean time for 1 iteration: " << (static_cast<double>(after-before)/
			static_cast<double>(CLOCKS_PER_SEC))/static_cast<double>(curCase.iterations) << " seconds" << endl;
	
		curCase.print();
	}
  }
  catch(std::exception const & ex)	
  {
	std::cerr << "Caught exception: " << ex.what() << std::endl;
        return EXIT_FAILURE;
  }

  return 0;
}
