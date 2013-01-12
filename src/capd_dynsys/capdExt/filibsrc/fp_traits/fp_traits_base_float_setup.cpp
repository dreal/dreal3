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
#include <ieee/primitive.hpp>
#include <cmath>
#include <cfloat>

#include "fp_traits/fp_traits.hpp"

#if defined(_MSC_VER)
float const filib::fp_traits_base<float>::min_val = 
	filib::primitive::composef(0,0xFE,(1 << 23)-1);

float const filib::fp_traits_base<float>::max_val = 
	filib::primitive::composef(0,0xFE,(1 << 23)-1);

float const filib::fp_traits_base<float>::nan_val = 
	filib::primitive::composef(0,0xFF,0x80);

float const filib::fp_traits_base<float>::inf_val  = 
	filib::primitive::composef(0,0xFF,0);

float const filib::fp_traits_base<float>::ninf_val =
	filib::primitive::composef(1,0xFF,0);

float const filib::fp_traits_base<float>::l_pi_val  =
	primitive::composef(0,126,(1<<23)-1)*
	static_cast<float>
	(filib::constructFromBitSet<double>("0:10000000000:1001001000011111101101010100010001000010110100011000"));
float const filib::fp_traits_base<float>::u_pi_val  =
	primitive::composef(0,127,1)*
	static_cast<float>
	(filib::constructFromBitSet<double>("0:10000000000:1001001000011111101101010100010001000010110100011001"));
#else
TEMPLATE_EMPTY
float const filib::fp_traits_base<float>::min_val = 
	filib::primitive::composef(0,0xFE,(1 << 23)-1);

TEMPLATE_EMPTY
float const filib::fp_traits_base<float>::max_val = 
	filib::primitive::composef(0,0xFE,(1 << 23)-1);

TEMPLATE_EMPTY
float const filib::fp_traits_base<float>::nan_val = 
	filib::primitive::composef(0,0xFF,0x80);

TEMPLATE_EMPTY
float const filib::fp_traits_base<float>::inf_val  = 
	filib::primitive::composef(0,0xFF,0);

TEMPLATE_EMPTY
float const filib::fp_traits_base<float>::ninf_val =
	filib::primitive::composef(1,0xFF,0);

TEMPLATE_EMPTY
float const filib::fp_traits_base<float>::l_pi_val  =
	primitive::composef(0,126,(1<<23)-1)*
	static_cast<float>
	(filib::constructFromBitSet<double>("0:10000000000:1001001000011111101101010100010001000010110100011000"));
TEMPLATE_EMPTY
float const filib::fp_traits_base<float>::u_pi_val  =
	primitive::composef(0,127,1)*
	static_cast<float>
	(filib::constructFromBitSet<double>("0:10000000000:1001001000011111101101010100010001000010110100011001"));
#endif
