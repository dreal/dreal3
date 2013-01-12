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
// example usage of the template library

#include <interval/interval.hpp>
#include <vector>
#include <iostream>

using filib::interval;

/* Evaluation of a Polynomial  */
/* using Horner's rule */
interval<double> horner
(
	/*  interval coefficients in STL container vector*/
	std::vector< interval<double> > const & v, 
	/* interval argument */
	interval<double> A
)
{
	/* result */
	interval<double> R = interval<double>();

	std::vector< interval<double> >::const_iterator
		a = v.begin(), b = v.end();

	while ( a != b )
	{
		R *= A;
		R += *(a++);
	}

	return R;
}

int main()
{
	filib::fp_traits<double>::setup();
	interval<double> a (5,8), b ("5","5");
	std::vector< interval<double> > v;
	v.push_back(a); v.push_back(b);
	std::cout << horner(v,a) << std::endl;
}
