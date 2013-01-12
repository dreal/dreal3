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
#include <assert.h>

// --------------------------------------------------
// LU factorisation of nxn Matrix A without pivoting.
// A is overwritten !
// --------------------------------------------------

template <class Matrix>
void lu_factor(Matrix &A) 
{
  assert(A.rows() == A.cols());
  
  unsigned int n = A.rows();

  typename Matrix::value_type sum;  
  
  for (unsigned int i=0; i<n; i++) {

    // compute i-th row of U
    for (unsigned int j=i; j<n; j++) {
      sum = 0.0;
      for (unsigned int k=0; k<i; k++)
	sum += A(i,k)*A(k,j);
      A(i,j) -= sum;
      //cout << i << " " << j << ": " << A(i,j) << endl;
      
    }

    // compute i-th column of L
    for (unsigned int j=i+1; j<n; j++) {
      sum = 0.0;
      for (unsigned int k=0; k<i; k++)
	sum += A(j,k)*A(k,i);
      A(j,i) = (A(j,i) - sum)/A(i,i);
      //cout << j << " " << i << ": " << A(j,i) << endl;
    }
  }
  
}


template <class Matrix, class Vector>
void lu_solve(const Matrix &LU, const Vector &b, Vector &x)
{
  assert(LU.rows() == LU.cols());
  assert(b.size() == LU.rows());
  assert(x.size() == LU.rows());  

  unsigned int n = LU.rows();

  Vector y(n);
  typename Matrix::value_type sum;
  
  // forward substitution
  for (unsigned int i=0; i<n; i++) {
    sum = 0.0;
    for (unsigned j=0; j<i; j++)
      sum += LU(i,j) * y[j];
    y[i] = b[i] - sum;
  }
  
  // backward substitution
  for (int i=n-1; i>=0; i--) {
    sum = 0.0;
    for (unsigned j=i+1; j<n; j++)
      sum += LU(i,j) * x[j];
    x[i] = (y[i] - sum) / LU(i,i);
  }
}






