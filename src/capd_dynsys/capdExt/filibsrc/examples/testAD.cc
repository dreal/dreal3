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
#include "interval.h"
#include "autodiff.h"


template<>
class MCT<interval, interval>
{
public:
  typedef interval value_type;
};

template<>
class MCT<interval, double>
{
public:
  typedef interval value_type;
};


template<>
class MCT<double, interval>
{
public:
  typedef interval value_type;
};

template<> 
class TypePrinter<interval>
{
public:
  static void printType(ostream &os) 
  {
    os << "interval";
  }
};


inline double sqr(double x) 
{
  return x*x;
}


varType(interval, ivar);
varType(double, dvar);


int main() 
{
  filib::fp_traits<double>::setup();

  interval a(-0.1, 0.1);
  
  ivar x; 
  dvar y,z;
  

  cout << (y).evalDeriv(a) << endl;
  
  
  (((x-1.0)*a) / -(a-sqr(x)+1.5/x)).evalDeriv(1.0);
  (((x-1.0)*a) / -(a-sqr(x)+1.5/x)).evalDeriv(a);
  (((y-1.0)*a) / -(a-sqr(y)+1.5/y)).evalDeriv(1.0);
  (((y-1.0)*a) / -(a-sqr(y)+1.5/y)).evalDeriv(a);

  return 0;
}
