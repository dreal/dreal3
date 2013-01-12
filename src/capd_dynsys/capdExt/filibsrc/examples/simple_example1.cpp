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

/* filib include */
#include <interval/interval.hpp>

/* standard headers */
#include <iostream>
#include <string>

/* simplify instantiation */
typedef filib::interval<double,filib::native_switched,filib::i_mode_extended> interval;

using std::cout;
using std::cerr;
using std::cin;
using std::endl;
using std::string;
using std::exception;
using std::flush;

/* read an interval from cin */
interval readInterval(string s)
{
	interval A;

	while ( true )
	{
		/* ask for input */
		cout << s << flush;

		/* try to read interval, exception on error */
		try
		{
			cin >> A;
			break;
		}
		/* more precisely filib::interval_io_exception,
		   which is derived from std::exception */
		catch(exception const & ex)
		{
			/* print diagnostic */
			cerr << ex.what() << endl;
			/* clear stream flags */
			cin.clear();
			/* get rest of the input line */
			string s;
			getline(cin,s);
		}
	}

	return A;
}

/* print description and interval as number tuple and bitimage */
void output(string s, interval A)
{
	cout << s << " = " << A << " = " << endl;
	A.bitImage(cout);
}

/* read two intervals and perform a few operations */
int main()
{
	filib::fp_traits<double>::setup();

	/* read intervals A and B */
	interval A = readInterval("Please enter first interval A: ");
	interval B = readInterval("Please enter second interval B: ");

	/* print intervals A and B */
	output("A",A);
	output("B",B);

	/* do some operations */
	output("A+B",A+B);
	output("A-B",A-B);
	output("A*B",A*B);

	/* perform interval division if possible */
	output("A/B",A/B);

	/* use a few standard functions */
	output("1/(1+A^2)",1.0/(1.0+sqr(A)));
	output("sin(A)",sin(A));
	output("tan(A)",tan(A));
	output("atan(A)",atan(A));
}
