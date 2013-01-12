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
#include <interval/interval.hpp>

#include <ctime>
#include <cmath>
#include <iostream>
#include <functional>
#include <string>
#include <typeinfo>

enum aritype { ari_plus, ari_minus, ari_multiplies, ari_divides };

template<class interval_t>
void iterate_plus(size_t const & iterations,interval_t const & a,interval_t const & b)
{
	for ( size_t j = iterations; j--; )
		a+b;
}
template<class interval_t>
void iterate_minus(size_t const & iterations,interval_t const & a,interval_t const & b)
{
	for ( size_t j = iterations; j--; )
		a-b;
}
template<class interval_t>
void iterate_multiplies(size_t const & iterations,interval_t const & a,interval_t const & b)
{
	for ( size_t j = iterations; j--; )
		a*b;
}
template<class interval_t>
void iterate_divides(size_t const & iterations,interval_t const & a,interval_t const & b)
{
	for ( size_t j = iterations; j--; )
		a/b;
}

template<class interval_t>
void performance_op(
	size_t const & iterations,
	interval_t const & a,
	interval_t const & b,
	aritype const & atype
	)
{
	clock_t before, after;
	
	before = clock();

	switch ( atype )
	{
		case ari_plus:
			iterate_plus(iterations,a,b);
			break;
		case ari_minus:
			iterate_minus(iterations,a,b);
			break;			
		case ari_multiplies:
			iterate_multiplies(iterations,a,b);
			break;			
		case ari_divides:
			iterate_divides(iterations,a,b);
			break;			
	}

	after = clock();

	clock_t clocks = after-before;

	double secs = 
		static_cast<double>(clocks)/
		static_cast<double>(CLOCKS_PER_SEC)*1000000.0;

	std::string aris;

	switch ( atype )
	{
		case ari_plus:
			aris = "+";
			break;
		case ari_minus:
			aris = "-";
			break;			
		case ari_multiplies:
			aris = "*";
			break;			
		case ari_divides:
			aris = "/";
			break;			
	}
	
	size_t oldprecision = std::cout.precision();

	std::cout 
		<< "binary operator " << aris;

	std::cout
		<< "(" << std::endl
		<< "\t";

	filib::corebench_out(std::cout,a);

	std::cout
		<< "," << std::endl
		<< "\t";

	filib::corebench_out(std::cout,a);

	std::cout
		<< ")" << std::endl
		<< iterations
		<< " it., usecs: " 
		<< static_cast<unsigned long>(ceil(secs))
		<< " Mops: "
		<< (static_cast<double>(iterations))/secs 
		<< std::endl;

	std::cout.precision(oldprecision);
}

template<class interval_t>
void performance_subrow(
	size_t const & iterations,
	interval_t const & a,
	interval_t const & b)
{
	performance_op(iterations,a,b,ari_plus);
	performance_op(iterations,a,b,ari_minus);
	performance_op(iterations,a,b,ari_multiplies);
	performance_op(iterations,a,b,ari_divides);
}

template<class N>
void performance_testrow(
	size_t const & iterations,
	N const & inf_0,
	N const & sup_0,
	N const & inf_1,
	N const & sup_1
	)
{
	filib::fp_traits<N,filib::native_switched>::reset();

	filib::interval<N,filib::native_directed,filib::i_mode_extended> a0f(inf_0,sup_0);
	filib::interval<N,filib::native_directed,filib::i_mode_extended> b0f(inf_1,sup_1);
	performance_subrow(iterations,a0f,b0f);

	filib::interval<N,filib::native_switched,filib::i_mode_extended> a0t(inf_0,sup_0);
	filib::interval<N,filib::native_switched,filib::i_mode_extended> b0t(inf_1,sup_1);
	performance_subrow(iterations,a0t,b0t);

	filib::interval<N,filib::multiplicative,filib::i_mode_extended> a1f(inf_0,sup_0);
	filib::interval<N,filib::multiplicative,filib::i_mode_extended> b1f(inf_1,sup_1);
	performance_subrow(iterations,a1f,b1f);

	filib::interval<N,filib::no_rounding,filib::i_mode_extended> a2f(inf_0,sup_0);
	filib::interval<N,filib::no_rounding,filib::i_mode_extended> b2f(inf_1,sup_1);
	performance_subrow(iterations,a2f,b2f);

	filib::fp_traits<N,filib::native_switched>::reset();
	filib::interval<N,filib::pred_succ_rounding,filib::i_mode_extended> a5f(inf_0,sup_0);
	filib::interval<N,filib::pred_succ_rounding,filib::i_mode_extended> b5f(inf_1,sup_1);
	performance_subrow(iterations,a5f,b5f);
}

void otter(std::ostream & out, double const & num)
{
	unsigned int a0,a1,a2,a3;

	filib::primitive::decompose(num,a0,a1,a2,a3);

	out << "[" << a0 << "," << a1 << "," << a2 << "," << a3 << "]" << std::endl;
}

template <typename N1, typename N2>
void call_unary_function(filib::unary_virtual_fo<N1,N2> const & fun, N2 const & arg)
{
	std::cout << fun(arg) << std::endl;
}

int main(int argc, char **argv)
{
	if ( argc == 1 )
	{
		std::cerr << "usage: " << argv[0] << " <number of iterations>" << std::endl;
		return EXIT_FAILURE;
	}
	else if ( argc < 1 )
		return EXIT_FAILURE;

	filib::fp_traits<double,filib::native_switched>::setup();

	try
	{
		size_t const iterations = static_cast<size_t>(atoi(argv[1]));

		double const pi=4.0*atan(1.0);

		double lower_0 = -2*pi, upper_0 = -pi;

		for ( unsigned int i = 0; i < 3; ++i, lower_0 += 1.5*pi, upper_0 += 1.5*pi )
		{
			double lower_1 = -2.0*pi, upper_1 = -pi;


			for ( unsigned int j = 0; j < 3; ++j, lower_1 += 1.5*pi, upper_1 += 1.5*pi )
				performance_testrow(iterations,lower_0,upper_0,lower_1,upper_1);
		}
	}
	catch(std::runtime_error const & ex)
	{
		std::cerr << ex.what() << std::endl;
	}
	catch(std::exception const & ex)
	{
		std::cerr << ex.what() << std::endl;		
	}
}
