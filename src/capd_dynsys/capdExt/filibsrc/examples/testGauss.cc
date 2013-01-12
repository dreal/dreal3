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
#include <cassert>

#include "interval/interval.hpp"
#include "Matrix.h"
#include "Vector.h"
#include "igauss.h"

typedef filib::interval<double> interval;

template <class Matrix>
void genTestMatrix(Matrix &A)
{
   unsigned int i,j;
   unsigned int n = A.rows();

   for(i=0;i<n;++i)
   {
      for(j=0;j<n;++j)
      {
         switch(i-j)
         {
            case 0:
               A(i,j)=2.0;
               break;
            case -1:
            case 1:
               A(i,j)=-1.0;
               break;
            default:
               A(i,j)=0.0;
               break;
         }
      }
   }
}

template <class Matrix, class Vector>
Vector operator *(const Matrix &A, const Vector &x) 
{
  assert(A.cols() == x.size());
  
  unsigned int n = A.rows();
  unsigned int m = A.cols();
  
  Vector y(n);
  
  typename Matrix::value_type sum;

  for (unsigned int i=0; i<n; i++) {
    sum = 0.0;
    for (unsigned int j=0; j<m; j++)
      sum += A(i,j) * x[j];
    y[i] = sum;
  }
  
  return y;
}


int main() 
{
  filib::fp_traits<double>::setup();

  const unsigned int n=1000;
  
  Matrix<interval> A(n,n);

  genTestMatrix(A);


  /*
  A(0,0) = 6.0;
  A(0,1) = 2.0;
  A(0,2) = 1.0;
  A(0,3) = -1.0;
  A(1,0) = 2.0;
  A(1,1) = 4.0;
  A(1,2) = 1.0;
  A(1,3) = 0.0;
  A(2,0) = 1.0;
  A(2,1) = 1.0;
  A(2,2) = 4.0;
  A(2,3) = -1.0;
  A(3,0) = -1.0;
  A(3,1) = 0.0;
  A(3,2) = -1.0;
  A(3,3) = 3.0;
  */
  
  /*
  A(0,0) = interval(8.0);
  A(0,1) = interval(1,4);
  A(0,2) = interval(0,3);
  A(1,0) = interval(1,2);
  A(1,1) = interval(9.0);
  A(1,2) = interval(0,6);
  A(2,0) = interval(2,3);
  A(2,1) = interval(2,5);
  A(2,2) = interval(9.0);  
  */  

  //cout << "A: " << endl << A << endl;

  Matrix<interval> B = A;

  Vector<interval> b(n), x(n);

  for (unsigned int i=0; i<n; i++)
    b[i] = interval(1e100, 1.001e100);
  
  /*
  b[0] = interval(1.0, 1.1);
  b[1] = interval(1.0);
  b[2] = interval(1.0);  
  b[2] = interval(1.0);  
  */

  //cout << "b: " << endl << b << endl;
  
  lu_factor(A);

  //cout << A << endl;
  
  lu_solve(A, b, x);  
  
  std::cout << "x: " << std::endl << x << std::endl;

  //cout << "A*x:" << endl << B*x << endl;
  

  return 0;
}

  



