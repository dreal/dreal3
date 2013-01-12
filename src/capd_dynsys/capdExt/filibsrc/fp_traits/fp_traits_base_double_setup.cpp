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
#include "fp_traits/fp_traits.hpp"

#include <ieee/primitive.hpp>
#include <cmath>

#if defined(_MSC_VER)
double const filib::fp_traits_base<double>::min_val = 
	filib::primitive::compose(0,0x1,0,0);

double const filib::fp_traits_base<double>::max_val = 
	filib::primitive::compose(0,0x7FE,(1 << 21)-1,0xffffffff);

double const filib::fp_traits_base<double>::nan_val = 
	filib::primitive::compose(0,0x7FF,1 << 19,0);

double const filib::fp_traits_base<double>::inf_val  = 
	filib::primitive::compose(0,0x7FF,0,0);

double const filib::fp_traits_base<double>::ninf_val =
	filib::primitive::compose(1,0x7FF,0,0);

double const filib::fp_traits_base<double>::l_pi_val  = 
	filib::constructFromBitSet<double>(
	"0:10000000000:1001001000011111101101010100010001000010110100011000");
double const filib::fp_traits_base<double>::u_pi_val  = 
	filib::constructFromBitSet<double>(
	"0:10000000000:1001001000011111101101010100010001000010110100011001");
#else
TEMPLATE_EMPTY
double const filib::fp_traits_base<double>::min_val = 
	filib::primitive::compose(0,0x1,0,0);

TEMPLATE_EMPTY
double const filib::fp_traits_base<double>::max_val = 
	filib::primitive::compose(0,0x7FE,(1 << 21)-1,0xffffffff);

TEMPLATE_EMPTY
double const filib::fp_traits_base<double>::nan_val = 
	filib::primitive::compose(0,0x7FF,1 << 19,0);

TEMPLATE_EMPTY
double const filib::fp_traits_base<double>::inf_val  = 
	filib::primitive::compose(0,0x7FF,0,0);

TEMPLATE_EMPTY
double const filib::fp_traits_base<double>::ninf_val =
	filib::primitive::compose(1,0x7FF,0,0);

TEMPLATE_EMPTY
double const filib::fp_traits_base<double>::l_pi_val  = 
	filib::constructFromBitSet<double>(
	"0:10000000000:1001001000011111101101010100010001000010110100011000");
TEMPLATE_EMPTY
double const filib::fp_traits_base<double>::u_pi_val  = 
	filib::constructFromBitSet<double>(
	"0:10000000000:1001001000011111101101010100010001000010110100011001");
#endif
