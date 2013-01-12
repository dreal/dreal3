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
#include<iomanip>
#include"interval/interval.hpp"

typedef filib::interval<double> interval;

using std::cout;
using std::cin;
using std::endl;
using std::setw;

/* --- main program ------------------------------------------------------ */

int main()
{
  filib::fp_traits<double>::setup();

  interval coeff[16];
  interval p, x, res;
  int i;

  interval::precision(15);
  
  /* --- Computation of the coefficients -------------------------------- */
  coeff[0] = interval(1.0);
  coeff[1] = interval(1.0);
  p = interval(1.0);
  for (i=2; i<=15; i++){
    p *= (double)i;
    coeff[i] = 1.0/p;
  }
  cout << "interval Horner's scheme in C++ with fi_lib++" << endl;
  cout << "=============================================" << endl;
  cout << endl;
  cout << "Computation of the polynom (sum_i=0^15 1/i! x^i)," << endl;
  cout << "that means the first terms of the taylor series" << endl;
  cout << "of the exponential function." << endl;
  cout << endl;
  cout << "Enclosures for the polynom coefficients:" << endl;

  for (i=0; i<=15; i++)
    cout << "   coeff[" << setw(2) << i << "] = " << coeff[i] << endl;
  cout << endl;

  cout << "Now, you can choose an interval argument (e.g. '[1, 1]'," << endl;
  cout << "'[1.01, 1.02]', 'x= [-1, -1]' or 'x= [-2.0, -1.99]' ...): "<< endl;
  cout << endl;
  cout << "x = ";
  cin >> x;

  /* --- interval Horner's scheme ---------------------------------------- */
  res = coeff[15];
  for (i=14; i>=0; i--)
    res = res * x + coeff[i];

  cout << "Result: " << res << endl; 

  return 0;
}

