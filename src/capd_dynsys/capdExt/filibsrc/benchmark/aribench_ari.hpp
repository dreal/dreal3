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
#if ! defined(HAVE_BOOST)
#include "random/uniform.h"
#else
#include "boost/random.hpp"
#endif

#include "benchmark/aribench_timer.hpp"

#include <iostream>
#include <vector>
#include <cstdlib>
#include <cfloat>
#include <ctime>

template <class interval_t>
class time_ari 
{
	private:
		class random_interval 
		{
			private:
				#if ! defined(HAVE_BOOST)
				ranlib::UniformOpenClosed<double> * rng;
				#else
				boost::uniform_real<> generator;
				boost::minstd_rand brand;
				boost::variate_generator< boost::minstd_rand, boost::uniform_real<> > vargen;
				#endif
				
			public:
				enum kind {gtZero, geZero, contZero, leZero, ltZero, kind_limit};
				
				random_interval() 
				: 
					#if ! defined(HAVE_BOOST)
					rng(0)
					#else
					generator(0.0,1.0),
					brand(),
					vargen(brand,generator)
					#endif
				{
					srand(time(0));

					#if ! defined(HAVE_BOOST)
					rng = new ranlib::UniformOpenClosed<double>;
					#endif
				}
				
				~random_interval()
				{
					#if !defined(HAVE_BOOST)
					delete rng;
					#endif
				}

				interval_t random(kind const & k) 
				{
					double inf, sup;

					switch (k) {
						#if !defined(HAVE_BOOST)
						case gtZero:
							inf = rng->random();
							sup = rng->random();
							break;
						case geZero:
							inf = 0.0; 
							sup = rng->random();
							break;
						case contZero:
							inf = -rng->random(); 
							sup = rng->random();
							break;
						case leZero:
							inf = -rng->random(); 
							sup = 0.0;
							break;
						case ltZero:
							inf = -rng->random();
							sup = -rng->random();
							break;
						#else
						case gtZero:
							inf = vargen();
							sup = vargen();
							break;
						case geZero:
							inf = 0.0; 
							sup = vargen();
							break;
						case contZero:
							inf = -vargen(); 
							sup = vargen();
							break;
						case leZero:
							inf = -vargen(); 
							sup = 0.0;
							break;
						case ltZero:
							inf = -vargen();
							sup = -vargen();
							break;
						#endif
						default:
							inf = 0;
							sup = 0;
							break;
					}
	
					if (inf <= sup)
						return interval_t(inf, sup);
					else
						return interval_t(sup, inf);
				}

				interval_t random() 
				{
					int k = ::std::rand()%static_cast<unsigned long>(kind_limit);
					return random(static_cast<kind>(k));
				}
  
		};

	public:
		~time_ari()
		{
			delete [] gtZero;
			delete [] geZero;
			delete [] contZero;
			delete [] leZero;
			delete [] ltZero;
			delete [] resI;    
			delete [] res;    	
		}
		time_ari(
			unsigned int const & n,
			unsigned int const & iterations, 
			std::ostream &os = std::cout)
		:
			dim(n),
			iter(iterations),
			out(os),
			rig()
	{
		/**
		 * initialize random interval data
		 **/
		gtZero = new interval_t[dim];
		geZero = new interval_t[dim];
		contZero = new interval_t[dim];
		leZero = new interval_t[dim];
		ltZero = new interval_t[dim];
		resI = new interval_t[dim];    
		res  = new interval_t[dim];    
			
		for (unsigned int i=0; i < dim; ++i )
		{
			gtZero[i] = rig.random(random_interval::gtZero);
			geZero[i] = rig.random(random_interval::geZero);
			contZero[i] = rig.random(random_interval::contZero);
			leZero[i] = rig.random(random_interval::leZero);
			ltZero[i] = rig.random(random_interval::ltZero);
		}

		all.push_back(gtZero);
		all.push_back(geZero);
		all.push_back(contZero);
		all.push_back(leZero);
		all.push_back(ltZero);

		noZero.push_back(gtZero);
		noZero.push_back(ltZero);
	}
	
	double timePlus() 
	{
		time_measure.start();

		size_t const n = all.size();

		for (size_t i=0; i < n; ++i)
			for (size_t j=0; j < n; ++j )
				timePlus(all[i], all[j]);

		time_measure.stop();

		double const time = time_measure.secs_elapsed();
		
		if ( time == 0 )
		{
			std::cerr << "WARNING: Measured time is zero !" << std::endl;
			return 0;
		}

		return (n*n*dim*iter) / time;
	}

	double timeMinus() 
	{
		time_measure.start();

		size_t const n = all.size();

		for (size_t i=0; i < n; ++i)
			for (size_t j=0; j < n; ++j )
				timeMinus(all[i], all[j]);

		time_measure.stop();

		double const time = time_measure.secs_elapsed();

		if ( time == 0 )
		{
			std::cerr << "WARNING: Measured time is zero !" << std::endl;
			return 0;
		}

		return (n*n*dim*iter) / time;
	}

	double timeMultiply() 
	{
		time_measure.start();

		size_t const n = all.size();

		for (size_t i=0; i < n; ++i)
			for (size_t j=0; j < n; ++j )
				timeMultiply(all[i], all[j]);

		time_measure.stop();

		double const time = time_measure.secs_elapsed();

		if ( time == 0 )
		{
			std::cerr << "WARNING: Measured time is zero !" << std::endl;
			return 0;
		}
    
		return (n*n*dim*iter) / time;
	}

	double timeDivide() 
	{
		time_measure.start();

		size_t const n = all.size();
		size_t const m = noZero.size();

		for (size_t i=0; i < n; ++i )
			for (size_t j=0; j < m; ++j )
				timeDivide(all[i], noZero[j]);

		time_measure.stop();

		double const time = time_measure.secs_elapsed();

		if ( time == 0 )
		{
			std::cerr << "WARNING: Measured time is zero !" << std::endl;
			return 0;
		}

		return (n*m*iter*dim)/time;
	}
  
	private:
		unsigned int const dim;
		unsigned int const iter;
  
		std::ostream &out;
    
		random_interval rig;

		timer time_measure;
  
		interval_t 
			* gtZero, 
			* geZero, 
			* contZero, 
			* leZero, 
			* ltZero, 
			* resI, 
			* res;
			
		std::vector< interval_t * > all;
		std::vector< interval_t * > noZero;
  
		void timePlus(
			interval_t const * const x,
			interval_t const * const y) 
		{    
			for (unsigned int i=iter; i; --i ) {
				interval_t const * x_iter = x;
				interval_t const * y_iter = y;
				interval_t * res_iter = resI;    
				
				for ( size_t j = dim; j; j-- )
					*res_iter++ = *x_iter++ + *y_iter++;
			}
		}

		void timeMinus(
			interval_t const * const x,
			interval_t const * const y) 
		{
			for (unsigned int i=iter; i; --i )
			{
				interval_t const * x_iter = x;
				interval_t const * y_iter = y;
				interval_t * res_iter = resI;    

				for ( size_t j = dim; j; j-- )
					*res_iter++ = *x_iter++ - *y_iter++;
			}
		}
		
		void timeMultiply(
				interval_t const * const x,
				interval_t const * const y) 
		{
			for (unsigned int i=iter; i; --i )
			{
				interval_t const * x_iter = x;
				interval_t const * y_iter = y;
				interval_t * res_iter = resI;    
				
				for ( size_t j = dim; j; j-- )
					*res_iter++ = *x_iter++ * *y_iter++;
			}
		}

		void timeDivide(
				interval_t const * const x, 
				interval_t const * const y) 
		{
			for (unsigned int i=iter; i; --i )
			{
				interval_t const * x_iter = x;
				interval_t const * y_iter = y;
				interval_t * res_iter = resI;    

				for ( size_t j = dim; j; j-- )
					*res_iter++ = *x_iter++ / *y_iter++;
			}
		}
};
