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

#include<iostream>
#include"interval/interval.hpp"

typedef filib::interval<double> interval;

using std::cout;
using std::cin;
using std::endl;

/* --- main program ------------------------------------------------------ */

int main()
{
  filib::fp_traits<double>::setup();

  interval x;

  interval::precision(15);

  cout << endl;
  cout << "Computation of the sine function in C++ with fi_lib++" << endl;
  cout << "=====================================================" << endl;
  cout << endl;
  cout << "Insert an interval argument (e.g. '[1, 1]' or '[1.01, 1.02]')" << endl;
  cout << "x = ";
  cin >> x;
  cout << "Argument x = " << x << endl;
  cout << "    sin(x) = " << sin(x) << endl;
  cout << endl;

  return 0;
}
