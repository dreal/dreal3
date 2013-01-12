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
#include <string>
#include <fstream>
#include <vector>
#include <numeric>

#include "benchmark/aribench_ari.hpp"

template <class interval_t>
class AriBench 
{
	private:
		std::string const lib;
		std::string const variant;
		std::string const compiler;
	public:
		AriBench(std::string rlib, std::string rcompiler, std::string rvariant)
		: lib(rlib), variant(rvariant), compiler(rcompiler) {}
		
		void exec() const
		{
			std::string fileBase = lib + "_" + variant + "_" + compiler;
			std::string logprefix = "log/";
			
			std::cout << "Library: " << lib << std::endl;
			std::cout << "Variant: " << variant << std::endl;

			std::string fileName;
    
			fileName = logprefix + "plus_" + fileBase;
			std::ofstream plusOut(fileName.c_str());
			if ( ! plusOut.is_open() ) { std::cerr << "Failed to open logfile " << fileName << std::endl; }

			fileName = logprefix + "minus_" + fileBase;
			std::ofstream minusOut(fileName.c_str());
			if ( ! minusOut.is_open() ) { std::cerr << "Failed to open logfile " << fileName << std::endl; }

			fileName = logprefix + "multiply_" + fileBase;
			std::ofstream multiplyOut(fileName.c_str());
			if ( ! multiplyOut.is_open() ) { std::cerr << "Failed to open logfile " << fileName << std::endl; }

			fileName = logprefix + "divide_" + fileBase;
			std::ofstream divideOut(fileName.c_str());
			if ( ! divideOut.is_open() ) { std::cerr << "Failed to open logfile " << fileName << std::endl; }

			std::vector<double> plus_op_s, minus_op_s, multiply_op_s, divide_op_s;

			unsigned int k=0;

			unsigned int const MAXDIM = 500;

			for (unsigned int dim=1; dim<=MAXDIM; dim+=1)
			{
				std::cout << "\r                                     \rPercentage done: " << static_cast<double>(dim)/static_cast<double>(MAXDIM)*100.0 << std::flush;
				unsigned int const MAX_ITER = 300000;
				unsigned int const iter = MAX_ITER / dim;
				
				time_ari< interval_t > timeAri(dim, iter);
				
				double pops = timeAri.timePlus();
				plusOut << dim << "\t\t" << pops/1e6 << std::endl;
				plus_op_s.push_back(pops);

				double mops = timeAri.timeMinus();
				minusOut << dim << "\t\t" << mops/1e6 << std::endl;
				minus_op_s.push_back(mops);

				double mups = timeAri.timeMultiply();
				multiplyOut << dim << "\t\t" << mups/1e6 << std::endl;
				multiply_op_s.push_back(mups);

				double dops = timeAri.timeDivide();
				divideOut << dim << "\t\t" << dops/1e6 << std::endl;
				divide_op_s.push_back(dops);

				// std::cout << "." << std::flush;

				k++;
			}

			std::cout << std::endl << std::endl;
    
			double paverage = 
				std::accumulate(plus_op_s.begin(), plus_op_s.end(), 0.0) 
				/ static_cast<double>(plus_op_s.size())
				/ 1.0e6;
			std::cout << "Average for +: " << paverage << std::endl;

			double maverage = 
				std::accumulate(minus_op_s.begin(), minus_op_s.end(), 0.0) 
				/ static_cast<double>(minus_op_s.size())
				/ 1.0e6;
			std::cout << "Average for -: " << maverage << std::endl;

			double muverage = 
				std::accumulate(multiply_op_s.begin(), multiply_op_s.end(), 0.0) 
				/ static_cast<double>(multiply_op_s.size())
				/ 1.0e6;
			std::cout << "Average for *: " << muverage << std::endl;

			double daverage = 
				std::accumulate(divide_op_s.begin(), divide_op_s.end(), 0.0) 
				/ static_cast<double>(divide_op_s.size())
				/ 1.0e6;
			std::cout << "Average for /: " << daverage << std::endl;
		}
};
