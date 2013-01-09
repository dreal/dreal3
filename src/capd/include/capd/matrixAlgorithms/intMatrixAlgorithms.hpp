/// @addtogroup matrixAlgorithms
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file intMatrixAlgorithms.hpp
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#ifndef _CAPD_MATRIXALGORITHMS_INTMATRIXALGORITHMS_HPP_
#define _CAPD_MATRIXALGORITHMS_INTMATRIXALGORITHMS_HPP_


#include "capd/capd/minmax.h"
#include "capd/capd/debuger.h"
#include "capd/vectalg/MatrixSlice.h"
#include "capd/vectalg/Matrix.hpp"
#include <cmath>

namespace capd{
  namespace matrixAlgorithms{

/* ------------------------  ------------------------ */
template<typename intType>
inline bool isDivisible(intType a, intType b){
  return a % b == intType(0);
}

/* ------------------------  ------------------------ */
template<typename intType>
inline bool isInvertible(intType a){
  return (a == intType(1)) || (a == -intType(1));
}

/* ------------------------  ------------------------ */
template<typename intType>
inline intType inverse(intType a){
  return intType(1)/a;
}


    /* Elementary row and column operations */

/* ------------------------  ------------------------ */
template<class matrix>
void rowExchange(matrix& A,int i,int j){
  if(i==j) return;
  MatrixIterator<matrix> it(A),it2(A);
  for(
    it=A.beginOfRow(i),it2=A.beginOfRow(j);
    it<A.endOfRow(i);
    it.moveToNextColumn(),it2.moveToNextColumn()
  ){
    typename matrix::ScalarType s=*it;
    *it=*it2;
    *it2=s;
  }
}

/* ------------------------  ------------------------ */
template<class matrix>
void rowMultiply(matrix& A,int i,typename matrix::ScalarType s){
  MatrixIterator<matrix> it(A);
  for(
    it=A.beginOfRow(i);
    it<A.endOfRow(i);
    it.moveToNextColumn()
  ){
    *it*=s;
  }
}

/* ------------------------  ------------------------ */
template<class matrix>
void rowAdd(matrix& A,int i,int j,typename matrix::ScalarType s){
  MatrixIterator<matrix> it(A),it2(A);
  for(
    it=A.beginOfRow(i),it2=A.beginOfRow(j);
    it<A.endOfRow(i);
    it.moveToNextColumn(),it2.moveToNextColumn()
  ){
    *it+=s**it2;
  }
}

/* ------------------------  ------------------------ */
template<class matrix>
void columnExchange(matrix& A,int i,int j){
  if(i==j) return;
  MatrixIterator<matrix> it(A),it2(A);
  for(
    it=A.beginOfColumn(i),it2=A.beginOfColumn(j);
    it<A.endOfColumn(i);
    it.moveToNextRow(),it2.moveToNextRow()
  ){
    typename matrix::ScalarType s=*it;
    *it=*it2;
    *it2=s;
  }
}

/* ------------------------  ------------------------ */
template<class matrix>
void columnMultiply(matrix& A,int j,typename matrix::ScalarType s){
  MatrixIterator<matrix> it2(A);
  for(
    it2=A.beginOfColumn(j);
    it2<A.endOfColumn(j);
    it2.moveToNextRow()
  ){
    *it2*=s;
  }
}

/* ------------------------  ------------------------ */
template<class matrix>
void columnAdd(matrix& A,int i,int j,typename matrix::ScalarType s){
  MatrixIterator<matrix> it(A),it2(A);
  for(
    it=A.beginOfColumn(i),it2=A.beginOfColumn(j);
    it<A.endOfColumn(i);
    it.moveToNextRow(),it2.moveToNextRow()
  ){
    *it2+=s**it;
  }
}

    /* Elementary row and column operations on matrix and matrices of bases */

/* ------------------------  ------------------------ */

template<class matrix, class sqMatrix>
void rowExchange(matrix& B,sqMatrix& Q,sqMatrix& Qinv,int i,int j){
  rowExchange(B,i,j);
  rowExchange(Qinv,i,j);
  columnExchange(Q,i,j);
}

/* ------------------------  ------------------------ */
template<class matrix, class sqMatrix>
void rowMultiply(matrix& B,sqMatrix& Q,sqMatrix& Qinv,int i,typename matrix::ScalarType q){
  rowMultiply(B,i,q);
  rowMultiply(Qinv,i,q);
  columnMultiply(Q,i,q);
}

/* ------------------------  ------------------------ */
template<class matrix, class sqMatrix>
void rowAdd(matrix& B,sqMatrix& Q,sqMatrix& Qinv,int i,int j,typename matrix::ScalarType q){
  rowAdd(B,i,j,q);
  rowAdd(Qinv,i,j,q);
  columnAdd(Q,i,j,-q);
}

/* ------------------------  ------------------------ */
template<class matrix, class sqMatrix>
void columnExchange(matrix& B,sqMatrix& R,sqMatrix& Rinv,int i,int j){
  columnExchange(B,i,j);
  columnExchange(R,i,j);
  rowExchange(Rinv,i,j);
}

/* ------------------------  ------------------------ */
template<class matrix, class sqMatrix>
void columnMultiply(matrix& B,sqMatrix& R,sqMatrix& Rinv,int i,typename matrix::ScalarType q){
  columnMultiply(B,i,q);
  columnMultiply(R,i,q);
  rowMultiply(Rinv,i,q);
}

/* ------------------------  ------------------------ */
template<class matrix, class sqMatrix>
void columnAdd(matrix& B,sqMatrix& R,sqMatrix& Rinv,int i,int j,typename matrix::ScalarType q){
  columnAdd(B,i,j,q);
  columnAdd(R,i,j,q);
  rowAdd(Rinv,i,j,-q);
}

            // *** partial reduction *** //

/* ------------------------  ------------------------ */

template<class matrix, class sqMatrix>
void partRowReduce(matrix& B,sqMatrix& Q,sqMatrix& Qinv,int k,int l){
  int m=B.numberOfRows();
  for(int i=k+1;i<=m;i++){
    typename matrix::ScalarType q=B(i,l)/B(k,l);
    rowAdd(B,Q,Qinv,i,k,-q);
  }
}

/* ------------------------  ------------------------ */
template<class matrix, class sqMatrix>
void partColumnReduce(matrix& B,sqMatrix& R,sqMatrix& Rinv,int k,int l){
  int n=B.numberOfColumns();
  for(int j=l+1;j<=n;j++){
    typename matrix::ScalarType q=B(k,j)/B(k,l);
    columnAdd(B,R,Rinv,l,j,-q);
  }
}

      // *** Test for nonzero matrices *** /

/* ------------------------  ------------------------ */
template<class matrix>
void smallestNonZero(const matrix& A,typename matrix::ScalarType& s, int& iOpt, int& jOpt){
  typedef typename matrix::ScalarType ScalarType;
  s=ScalarType(0);
  const_MatrixIterator<matrix> it(A),itOpt(A);
  for(int i=1;i<=A.numberOfRows();++i){
    it=A.beginOfRow(i);
    for(int j=1;j<=A.numberOfColumns();++j){
      ScalarType t=*it;
      if(t<ScalarType(0)) t=-t;
      if( s==ScalarType(0) || (s>t && t>ScalarType(0)) ){
        s=t;itOpt=it;
      }
      it.moveToNextColumn();
    }
  }
  std::pair<int,int> p=itOpt.rowAndColumn();
  iOpt=p.first;
  jOpt=p.second;
}

/* ------------------------  ------------------------ */
template<class matrix>
bool nonZero(const matrix& A){
  typedef typename matrix::ScalarType ScalarType;
  const_MatrixIterator<matrix> it(A);
  for(int i=1;i<=A.numberOfRows();++i){
    it=A.beginOfRow(i);
    for(int j=1;j<=A.numberOfColumns();++j){
      if(*it!=ScalarType(0)) return true;
      it.moveToNextColumn();
    }
  }
  return false;
}

          // *** row echelon form *** //

/* ------------------------  ------------------------ */
template<class matrix, class sqMatrix>
void rowPrepare(matrix& B,sqMatrix& Q,sqMatrix& Qinv,int k,int l){
  typedef typename matrix::ScalarType ScalarType;
  int m=B.numberOfRows();
  ScalarType s;
  int i,j;
  ;
  smallestNonZero(MatrixSlice<matrix>(B,k,m,l,l),s,i,j);
  i+=k-1;
  rowExchange(B,Q,Qinv,k,i);
}

/* ------------------------  ------------------------ */
template<class matrix, class sqMatrix>
void rowReduce(matrix& B,sqMatrix& Q,sqMatrix& Qinv,int k,int l){
  typedef typename matrix::ScalarType ScalarType;
  int m=B.numberOfRows();
  while( nonZero(MatrixSlice<matrix>(B,k+1,m,l,l)) ){
    rowPrepare(B,Q,Qinv,k,l);
    partRowReduce(B,Q,Qinv,k,l);
  }
}

/* ------------------------  ------------------------ */
template<class matrix, class sqMatrix>
void rowEchelon(matrix& B,sqMatrix& Q,sqMatrix& Qinv,int &k){
  typedef typename matrix::ScalarType ScalarType;
  int m=B.numberOfRows();
  int n=B.numberOfColumns();
  Q.setToIdentity();
  Qinv.setToIdentity();
  k=0;
  int l=1;
  do{
    while(l<=n && !nonZero(MatrixSlice<matrix>(B,k+1,m,l,l))) l++;
    if(l==n+1) break;
    rowReduce(B,Q,Qinv,++k,l);
  }while(k<m);
}

// *** column echelon form *** //
// *** not tested *** //

/* ------------------------  ------------------------ */

template<class matrix, class sqMatrix>
void columnPrepare(matrix& B,sqMatrix& R,sqMatrix& Rinv,int k,int l){
  typedef typename matrix::ScalarType ScalarType;
  int n=B.numberOfColumns();
  ScalarType s;
  int i,j;
  smallestNonZero(MatrixSlice<matrix>(B,k,k,l,n),s,i,j);
  j+=l-1;
  columnExchange(B,R,Rinv,l,j);
}

/* ------------------------  ------------------------ */
template<class matrix, class sqMatrix>
void columnReduce(matrix& B,sqMatrix& R,sqMatrix& Rinv,int k,int l){
  typedef typename matrix::ScalarType ScalarType;
  int n=B.numberOfColumns();
  while( nonZero(MatrixSlice<matrix>(B,k,k,l+1,n)) ){
    columnPrepare(B,R,Rinv,k,l);
    partColumnReduce(B,R,Rinv,k,l);
  }
}

/* ------------------------  ------------------------ */
template<class matrix, class sqMatrix>
void columnEchelon(matrix& B,sqMatrix& R,sqMatrix& Rinv,int &l){
  typedef typename matrix::ScalarType ScalarType;
  int m=B.numberOfRows();
  int n=B.numberOfColumns();
  R.setToIdentity();
  Rinv.setToIdentity();
  l=0;
  int k=1;
  do{
    while(k<=m && !nonZero(MatrixSlice<matrix>(B,k,k,l+1,n)) ) k++;
    if(k==m+1) break;
    columnReduce(B,R,Rinv,k,++l);
  }while(l<n);
}

/* ------------------------  ------------------------ */
template<class matrix>
void kernelImage(matrix& B,matrix& kernel,matrix& image){
  int m=B.numberOfRows();
  int n=B.numberOfColumns();
  matrix R=matrix::Identity(n);
  matrix Rinv=matrix::Identity(n);
  int k;
  columnEchelon(B,R,Rinv,k);
  kernel=MatrixSlice<matrix>(R,1,n,k+1,n);
  image=MatrixSlice<matrix>(B,1,m,1,k);
}

// *** Smith diagonalization *** //

/* ------------------------  ------------------------ */
template<class matrix, class sqMatrix1, class sqMatrix2>
void moveMinNonzero(matrix& B,sqMatrix1& Q,sqMatrix1& Qinv,sqMatrix2& R,sqMatrix2& Rinv,int k){
  typedef typename matrix::ScalarType ScalarType;
  int m=B.numberOfRows();
  int n=B.numberOfColumns();
  int i,j;
  ScalarType s;
  smallestNonZero(MatrixSlice<matrix>(B,k,m,k,n),s,i,j);
  i+=k-1;
  j+=k-1;
  rowExchange(B,Q,Qinv,k,i);
  columnExchange(B,R,Rinv,k,j);
}

/* ------------------------  ------------------------ */
template<class matrix>
bool checkForDivisibility(matrix& B,int k,int& i,int& j,typename matrix::ScalarType &q){
  int m=B.numberOfRows();
  int n=B.numberOfColumns();
  for(i=k+1;i<=m;++i)
  for(j=k+1;j<=n;++j){
    q=B(i,j)/B(k,k);
    if(q*B(k,k)!=B(i,j)) return false;
  }
  return true;
}

/* ------------------------  ------------------------ */
template<class matrix, class sqMatrix1, class sqMatrix2>
void partSmithForm(matrix& B,sqMatrix1& Q,sqMatrix1& Qinv,sqMatrix2& R,sqMatrix2& Rinv,int k){
  typedef typename matrix::ScalarType ScalarType;
  int m=B.numberOfRows();
  int n=B.numberOfColumns();
  bool divisible=false;
  do{
    moveMinNonzero(B,Q,Qinv,R,Rinv,k);
    partRowReduce(B,Q,Qinv,k,k);
    if(nonZero(MatrixSlice<matrix>(B,k+1,m,k,k))) continue;
    partColumnReduce(B,R,Rinv,k,k);
    if(nonZero(MatrixSlice<matrix>(B,k,k,k+1,n))) continue;
    int i,j;
    ScalarType q=ScalarType(0);
    divisible=checkForDivisibility(B,k,i,j,q);
    if(!divisible){
      rowAdd(B,Q,Qinv,i,k,ScalarType(1));
      columnAdd(B,R,Rinv,k,j,-q);
    }
  }while(!divisible);
}

/* ------------------------  ------------------------ */
template<class matrix, class sqMatrix1, class sqMatrix2>
void smithForm(matrix& B,sqMatrix1& Q,sqMatrix1& Qinv,sqMatrix2& R,sqMatrix2& Rinv,int &s,int &t){
  typedef typename matrix::ScalarType ScalarType;
  int m=B.numberOfRows();
  int n=B.numberOfColumns();
  Q=Qinv=matrix::Identity(m);
  R=Rinv=matrix::Identity(n);
  s=t=0;
  while(nonZero(MatrixSlice<matrix>(B,t+1,m,t+1,n))){
    t++;
    partSmithForm(B,Q,Qinv,R,Rinv,t);
    if(B(t,t)<ScalarType(0)) rowMultiply(B,Q,Qinv,t,-ScalarType(1));
    if(isInvertible(B(t,t))) rowMultiply(B,Q,Qinv,t,inverse(ScalarType(B(t,t))));
    if(B(t,t)==ScalarType(1)) s++;
  };
}

/* ------------------------  ------------------------ */
template<class matrix, class vector, class colVector>
bool solveLinearEquation(const matrix& A,const colVector& b,vector& x){
  typedef typename matrix::ScalarType ScalarType;
  int m=A.numberOfRows();
  int n=A.numberOfColumns();
  matrix B(A);
  matrix Q(m,m);
  matrix Qinv(m,m);
  matrix R(n,n);
  matrix Rinv(n,n);
  int s,t;
  smithForm(B,Q,Qinv,R,Rinv,s,t);
  vector c=Qinv*b;
  x=vector(n);
  for(int i=1;i<=t;++i){
//    if(c(i)%B(i,i) == ScalarType(0)){
    if(isDivisible(c(i),B(i,i))){
      x(i)=c(i)/B(i,i);
    }else{
      return false;
    }
  }
  for(int i=t+1;i<=m;++i){
    if(c(i) == typename matrix::ScalarType(0) ){
      if(i<=n) x(i)=0;
    }else{
      return false;
    }
  }
  x=R*x;
  return true;
}

/* ------------------------  ------------------------ */
template<class matrix>
bool invert(const matrix& A,matrix& Ainv){
  typedef typename matrix::ScalarType ScalarType;
  int m=A.numberOfRows();
  int n=A.numberOfColumns();
  if(m!=n) return false;
  matrix B(A);
  matrix Q(m,m);
  matrix Qinv(m,m);
  matrix R(n,n);
  matrix Rinv(n,n);
  int s,t;
  smithForm(B,Q,Qinv,R,Rinv,s,t);
  for(int i=1;i<=n;++i) if(B(i,i)!=ScalarType(1)) return false;
  Ainv=R*Qinv;
  return true;
}


/* ------------------------  ------------------------ */
template<class matrix,class IntVector>
void quotientBaseMatrix(
  const matrix& A_W,                       // input: basis of G \subset Z^p as columns of A_W,
  const matrix& A_V,                       // input: basis of H\subset G \subset Z^p as columns of A_V,
  matrix& A_U,                             // output: pseudobasis of G/H as columns of A_U,
  IntVector& A_orders                      // output: IntVector of finite orders
                                           // of elements of pseudobasis A_U
){
   typedef typename matrix::ColumnVectorType VectorType;
   int p=A_W.numberOfRows();
   int m=A_W.numberOfColumns();
   int n=A_V.numberOfColumns();
   VectorType a;
   matrix B(m,n);

   for(int j=0;j<n;++j){
     solveLinearEquation(A_W,A_V.column(j),a);
     for(int i=0;i<m;++i) B[i][j]=a[i];
   }
   matrix Q,Qinv,R,Rinv;
   int s,t;
   smithForm(B,Q,Qinv,R,Rinv,s,t);


   matrix WQ=A_W*Q;
   A_U=MatrixSlice<matrix>(WQ,1,p,s+1,m);
   A_orders=IntVector(n-s);    // finite orders greater than one
   for(int i=s;i<n;++i) A_orders[i-s]=B[i][i];
}
/* ------------------------  ------------------------ */


  } // end of namespace matrixAlgorithms

} // end of namespace capd;
#endif // _CAPD_MATRIXALGORITHMS_INTMATRIXALGORITHMS_HPP_

/// @}
