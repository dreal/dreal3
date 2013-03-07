/// @addtogroup matrixAlgorithms
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file floatMatrixAlgorithms.hpp
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifndef _CAPD_MATRIXALGORITHMS_FLOATMATRIXALGORITHMS_HPP_ 
#define _CAPD_MATRIXALGORITHMS_FLOATMATRIXALGORITHMS_HPP_ 

#include <vector>
#include <stdexcept>
#include <iostream>
#include "capd/auxil/minmax.h"
#include "capd/basicalg/power.h"
#include "capd/matrixAlgorithms/floatMatrixAlgorithms.h"
#include "capd/basicalg/TypeTraits.h"
#include "capd/basicalg/doubleFun.h"

namespace capd{
namespace matrixAlgorithms{

/**
 * Computes determinant of a matrix A by LU decomposition.
 *
 * @remark Singular matrix case is not fully implemented.
 *
 * @param A given matrix
 * @return determinant of A
 */
template<typename MatrixType>
typename MatrixType::ScalarType det(MatrixType A)
{
  typedef typename MatrixType::ScalarType ScalarType;

  int i,j,k;
  int dimension = A.numberOfRows();

  // permutation of rows
  int *p = new int[dimension];
  for(i=0;i<dimension;++i)
    p[i]=i;

  // sign of a permutation
  int sgn = 1;

  for(j=0;j<dimension-1;++j)
  {
    // we search for the biggest entry in the column below or on the diagonal
    ScalarType a_max = capd::abs(A[p[j]][j]);
    int i_max = j;
    for(i=j+1;i<dimension;++i){
      ScalarType a_max_temp = capd::abs(A[p[i]][j]);
      if( a_max_temp > a_max) {
        a_max = a_max_temp;
        i_max = i;
      }
    }
    // we move max entry to the diagonal by suitable row permutation
    if(j!=i_max){
      sgn = -sgn;
      std::swap(p[j], p[i_max]);
    }

    ScalarType divisor = A[p[j]][j];
    if( isSingular(divisor) ) {
      delete[] p;
      // return capd::TypeTraits<ScalarType>::zero();
      throw std::runtime_error( "det: determinant contains zero but result can not be validated!\n");
    }
    // we make subdiagonal terms equal to zero by subtracting suitable multiply of current 'diagonal' row.
    for(i=j+1;i<dimension;++i) {
      ScalarType factor = A[p[i]][j]/A[p[j]][j];
      A[p[i]][j] = static_cast<ScalarType>(0);
      for(k=j+1;k<dimension;++k) {
        A[p[i]][k] -= factor*A[p[j]][k];
      }
    }
  }

  // we compute determinant by multiplying diagonal terms
  ScalarType determinant = capd::TypeTraits<ScalarType>::one();
  for(i=0; i<dimension; ++i) {
    determinant *= A[p[i]][i];
  }
  delete[] p;
  return sgn*determinant;
}

// ------------- Gauss elimination - auxiliary function ------------------------------- //

template<typename MatrixType, typename ResultType>
void gauss(MatrixType a, ResultType b, ResultType& result)
{
  typedef typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;

  int i,j,k;
  int dimension = a.numberOfRows();
  int *p = new int[dimension];
  for(i=0;i<dimension;++i) 
    p[i]=i;

  for(j=0;j<dimension-1;++j)
  {
    ScalarType a_max,a_max_temp;
    int i_max,temp;
    a_max = capd::abs(a[p[j]][j]);
    i_max = j;
    temp = p[j];
    for(i=j+1;i<dimension;++i)
    {
      if( (a_max_temp = capd::abs(a[p[i]][j])) > a_max)
      {
        a_max = a_max_temp;
        i_max = i;
      }
    }
    p[j] = p[i_max];
    p[i_max] = temp;

    ScalarType divisor = a[p[j]][j];
    if( isSingular(divisor) )
    {
      throw std::runtime_error( "Gauss elimination: singular matrix\n");
    }
    for(i=j+1;i<dimension;++i)
    {
      ScalarType factor = a[p[i]][j]/a[p[j]][j];
      a[p[i]][j] = static_cast<ScalarType>(0);
      b[p[i]] -= factor*b[p[j]];
      for(k=j+1;k<dimension;++k)
      {
        a[p[i]][k] -= factor*a[p[j]][k];
      }
    }
  }
  if( isSingular(a[p[dimension-1]][dimension-1]) )
  {
    throw std::runtime_error( "Gauss elimination: singular matrix\n");
  }
  for(int i=dimension-1;i>=0;--i)
  {
    result[i] = b[p[i]];
    for(int j=i+1;j<dimension;++j)
      result[i] -= a[p[i]][j]*result[j];
    result[i] /= a[p[i]][i];
  }
  delete[] p;
}

/**
 *  Gauss elimination
 *
 * this function solves equaiton A*x=b for x
 * where A is nonsingular matrix
 */
template<typename MatrixType, typename VectorType>
VectorType gauss(const MatrixType& A, const VectorType& b)
{
// on output result = a^-1 b
  int dimension = b.dimension();
  if(A.numberOfRows()!=A.numberOfColumns() || A.numberOfRows()!=dimension)
    throw std::runtime_error("Call gauss elimination for nonsquare matrix");

  VectorType result(A.numberOfRows());
  gauss(A,b,result);
   
  return result;
}

//-------------------------------------------------------------------------
///
/// computes sorting permutation according to sizes of
/// the set in the direction of the base vectors
///
template<typename MatrixType, typename VectorType, typename IntVectorType>
void computeSortingPermutation(
         const MatrixType& Q,         ///<  @param  Q     matrix of base vectors (in columns)
         const VectorType & v,        ///<  @param  v     set in given coordinates
         IntVectorType & permutation  ///<  @param[out] permutation
){
  //typedef typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;
  //typedef typename VectorType::template rebind<int>::other IntVectorType;
  typedef typename MatrixType::RefColumnVectorType ColumnVectorType;

  VectorType norm(Q.numberOfColumns(),true);

  int i=0;

  typename MatrixType::const_iterator e=Q.end();
  typename VectorType::iterator bn = norm.begin(), en=norm.end();
  while(bn!=en)
  {
    ScalarType s(0);
    typename MatrixType::const_iterator b=Q.begin()+i;
    while(b!=e)
    {
      s += power(*b,2).rightBound();
      b += Q.rowStride();
    }
    *bn = s*(ScalarType(1e-50)+(power(v[i],2).rightBound()));
    ++bn;
    ++e;
    ++i;
  }

  norm.sorting_permutation(permutation);
}

// -------------------------------- orthonormalize -------------------------

template<typename MatrixType>
void orthonormalize(MatrixType& Q, const typename MatrixType::RowVectorType& v)
{
  typedef typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;
  typedef typename VectorType::template rebind<int>::other IntVectorType;
  typedef typename MatrixType::RefColumnVectorType ColumnVectorType;


  IntVectorType p(Q.numberOfColumns(),true);
  computeSortingPermutation(Q, v, p);
  typename IntVectorType::iterator bp = p.begin(), ep = p.end();
  while(bp!=ep)
  {
    ColumnVectorType qi = Q.column(*bp);
    if(qi.normalize())
    {
      typename IntVectorType::iterator bj = ++bp;
      while(bj!=ep)
      {
        ColumnVectorType qj = Q.column(*bj);
        qj -= (qj * qi) * qi;
        ++bj;
      }
    }else{
      throw std::runtime_error("Failed to decompose matrix");
    }
  }
}

// -------------------------------- orthonormalize -------------------------

template<typename MatrixType>
void orthonormalize(MatrixType& Q, const MatrixType& v)
{
  typedef typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;
  typedef typename VectorType::template rebind<int>::other IntVectorType;
  typedef typename MatrixType::RefColumnVectorType ColumnVectorType;


//  VectorType columnNorms(v.numberOfRows(),true);
//  typename VectorType::iterator bn = columnNorms.begin(), en=columnNorms.end();
//  int i=0;
//  while(bn!=en){
//    *bn = v.row(i).euclNorm();
//    bn++; i++;
//  }
//  IntVectorType p(Q.numberOfColumns(),true);
//  computeSortingPermutation(Q, columnNorms, p);

  /// TODO: check and replace with the above
  //---------------------------------------------
  VectorType norm(v.numberOfRows(),true);
  IntVectorType p(Q.numberOfColumns(),true);

  int i=0;
    typename MatrixType::iterator e=Q.end();
    typename VectorType::iterator bn = norm.begin(), en=norm.end();
    while(bn!=en)
    {
      ScalarType s(0);
      typename MatrixType::iterator b=Q.begin()+i;
      while(b!=e)
      {
        s += power(*b,2);
        b += Q.rowStride();
      }
      *bn = s*(ScalarType(1e-50)+v.row(i).euclNorm().rightBound());
      ++bn;
      ++e;
      ++i;
    }

    norm.sorting_permutation(p);
 // ------- end ------------------
  typename IntVectorType::iterator bp = p.begin(), ep = p.end();
  while(bp!=ep)
  {
    ColumnVectorType qi = Q.column(*bp);
    if(qi.normalize())
    {
      typename IntVectorType::iterator bj = ++bp;
      while(bj!=ep)
      {
        ColumnVectorType qj = Q.column(*bj);
        qj -= (qj * qi) * qi;
        ++bj;
      }
    }else{
      throw std::runtime_error("Failed to decompose matrix");
    }
  }
}
// Gramm-Schmit column orthonormalization
// with permutation of columns
template<typename MatrixType>
void orthonormalize(MatrixType& Q)
{
  typedef typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;
  typedef typename VectorType::template rebind<int>::other IntVectorType;
  typedef typename MatrixType::RefColumnVectorType ColumnVectorType;

  VectorType norm(Q.numberOfColumns(),true);
  IntVectorType p(Q.numberOfColumns(),true);

  int i=0;
  typename MatrixType::iterator e=Q.end();
  typename VectorType::iterator bn = norm.begin(), en=norm.end();
  while(bn!=en)
  {
    ScalarType s(0);
    typename MatrixType::iterator b=Q.begin()+i;
    while(b!=e)
    {
      s += power(*b,2);
      b += Q.rowStride();
    }
    *bn = s;
    ++bn;
    ++e;
    ++i;
  }

  norm.sorting_permutation(p);
  typename IntVectorType::iterator bp = p.begin(), ep = p.end();
  while(bp!=ep)
  {
    ColumnVectorType qi = Q.column(*bp);
    if(qi.normalize())
    {
      typename IntVectorType::iterator bj = ++bp;
      while(bj!=ep)
      {
        ColumnVectorType qj = Q.column(*bj);
        qj -= (qj * qi) * qi;
        ++bj;
      }
    }else{
      throw std::runtime_error("Failed to decompose matrix");
    }
  }
}

// -------------------------------- QR_decompose -------------------------

template<typename MatrixType>
void QR_decompose(const MatrixType& A, MatrixType& Q, MatrixType& R)
{
  Q = A;
  int i,j, dimension = A.numberOfColumns();
  R.clear();
  for(i=0;i<dimension;++i)
  {
    typename MatrixType::RefColumnVectorType iColumn = Q.column(i);
    typename MatrixType::ScalarType diag = R(i+1,i+1) = iColumn.euclNorm();
    if(!isSingular(diag))
    {
      iColumn /= diag;
      for(j=i+1;j<dimension;++j)
      {
        diag = R(i+1,j+1) = Q.column(j)*iColumn;
        Q.column(j) -= diag * Q.column(i);
      }
    }else{
      throw std::runtime_error("Failed to decompose A");
    }
  }
}
// -------------------------------- QR_with_pivoting_and_weights -------------------------

template<typename MatrixType, typename IntVectorType>
void QRdecomposeWithPivoting(
    const MatrixType & A,
    const typename MatrixType::RowVectorType& v,
    MatrixType& Q,
    MatrixType& R,
    typename MatrixType::RowVectorType & sizes,
    IntVectorType & p
){
  typedef typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;
  typedef typename MatrixType::RefColumnVectorType ColumnVectorType;
  //IntVectorType (Q.numberOfColumns(),true);
  if(&Q != &A)
    Q = A;
  computeSortingPermutation(Q,v,p);

  int i,j, dimension = Q.numberOfColumns();
  R.clear();
  int d = 0 ;    // which canonical vector to use if original is linearly dependent
  typename IntVectorType::iterator it = p.begin(), ep = p.end();
  while( it!=ep )
  {
    sizes[*it] = capd::TypeTraits<ScalarType>::zero();
    bool isColumnOryginal = true;
    // we try to do Gramm-Schmidt step as long as we finally find orthogonal vector
    do{

      typename MatrixType::RefColumnVectorType Qi = Q.column(*it);
      typename IntVectorType::iterator j = p.begin();
      // we project Qi into subspace spanned by the previous base vectors
      while( j!=it ){
        typename MatrixType::RefColumnVectorType Qj = Q.column(*j);
        ScalarType product = R(*j + 1, *it +1) = Qi * Qj;
        Qi -= product * Qj;
        ++j;
      }
      typename MatrixType::ScalarType diag = R(*it+1,*it+1) = Qi.euclNorm();
      if( isColumnOryginal )
          sizes[*it] = (!isSingular(diag) ? abs(diag).left() : capd::TypeTraits<ScalarType>::zero());

      // we check if current column is linearly independent
      if( !isSingular(diag) ) {
        Qi /= diag;
        ++it;
        break;
      }else{
        for(int k=0; k<dimension; ++k){
          Qi[k] = (d==k)? capd::TypeTraits<ScalarType>::one() : capd::TypeTraits<ScalarType>::zero();
        }
        d++;
        isColumnOryginal = false;
      }
    } while(d<=dimension);
  }
  if(d>dimension){
    throw  std::runtime_error("Failed to QR decompose A");
  }
}

// -------------------------------- diagonalize -------------------------

template<typename MatrixType>
int symMatrixDiagonalize(const MatrixType& A, MatrixType& D, typename MatrixType::ScalarType diagonalizingRelTolerance = typename MatrixType::ScalarType(1e-5))
{
  typedef typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;
  int dimension = A.numberOfRows();
  MatrixType lastD = A;//(dimension,dimension);

  ScalarType last_sum_of_squares(10000000000000000.0);
  D=A;
  if(dimension == 1) return 1;
  ScalarType s(0), d(0);
  int i,j,p=0,q=0;
  for(i=1;i<dimension;++i)
    for(j=0;j<i;++j)
      s += power(D[i][j],2);
  for(i=0;i<dimension;++i)
    d += power(D[i][i],2);
//  if( !(d>0) )
//    return 1;

  while( !(s<d*diagonalizingRelTolerance) )
  {
    if(!(right(s)<right(last_sum_of_squares)))
    {
      D = lastD;
      break;
    }
    ScalarType dominant(0);
    for(i=1;i<dimension;++i)
      for(j=0;j<i;++j)
      {
        ScalarType element = left(capd::abs(D[i][j]));
        if( element > dominant )
        {
          p = i;
          q = j;
          dominant = element;
        }
      }

    if( isSingular(dominant) ) break;  //procceeding with iteration can only worsen things

    ScalarType alpha = (mid(D[q][q]) - mid(D[p][p]))/(ScalarType(2)*mid(D[p][q]));
    ScalarType beta = (alpha>0 ? alpha + sqrt(power(alpha,2)+1) : alpha - sqrt(power(alpha,2)+1));
    ScalarType sinth = (alpha>0 ? ScalarType(1)/sqrt(power(beta,2)+ScalarType(1))
                                : ScalarType(-1)/sqrt(power(beta,2)+ScalarType(1))
         );
    ScalarType costh = beta*sinth;
    VectorType ap = D[p];
    VectorType aq = D[q];
    lastD = D;
    D[p][p] = aq[q]*power(sinth,2) - ScalarType(2)*ap[q]*sinth*costh + ap[p]*power(costh,2);
    D[q][q] = aq[q]*power(costh,2) + ScalarType(2)*ap[q]*sinth*costh + ap[p]*power(sinth,2);
    D[p][q] = D[q][p] = ap[q]*(power(costh,2) - power(sinth,2)) + (ap[p]-aq[q])*sinth*costh;
    for(j=0;j<dimension;++j)
      if(j!=p && j!=q)
        D[p][j] = D[j][p] = -aq[j]*sinth+ap[j]*costh;
    for(j=0;j<dimension;++j)
      if(j!=p && j!=q)
        D[q][j] = D[j][q] = aq[j]*costh+ap[j]*sinth;

// last_sum_of_squares=s+d;
    last_sum_of_squares = s;
    d = ScalarType(0);
    for(i=0;i<dimension;++i) d += power(D[i][i],2);

//    if( isSingular(d) )
//      return 0;

    s=ScalarType(0);
    for(i=1;i<dimension;++i)
      for(j=0;j<i;++j)
        s += power(D[i][j],2);

    if( isSingular(s) ) break;  //procceeding with iteration can only worsen things
  }
  return 1;
}

/// this function computes upper bound for spectral radius of a symmetric matrix
/// first it computes matrix which has the same eigenvalues and which is close to diagonal,
/// next upper bound is computed from Gerschgorin theorem
template<typename MatrixType>
typename MatrixType::ScalarType spectralRadiusOfSymMatrix(const MatrixType &A, typename MatrixType::ScalarType diagonalizingRelTolerance = typename MatrixType::ScalarType(1e-5))
{
  typedef typename MatrixType::ScalarType ScalarType;
  int dimension = A.numberOfRows();
  MatrixType D(dimension,dimension);
  if(!symMatrixDiagonalize(A,D,diagonalizingRelTolerance))
  {
    std::runtime_error("spectralRadius::Failed to diagonalize a matrix");
  }
  ScalarType dominant(0);
  for(int i=0;i<dimension;++i)
  {
    ScalarType diam(0);
    for(int j=0;j<dimension;++j)
      if( i != j )
        diam += capd::abs(D[i][j]);
    ScalarType elem = capd::abs(right(D[i][i]+diam));
    if(i==0) dominant=elem;
    else if(!(elem<dominant)) dominant = elem;
  }
  return dominant;
}


/// this function computes upper bound for maximal eigenvalue of a symmetric matrix
/// first it computes matrix which has the same eigenvalues and which is close to diagonal,
/// next upper bound is computed from Gerschgorin theorem
template<typename MatrixType>
typename MatrixType::ScalarType maxEigenValueOfSymMatrix(const MatrixType &A, typename MatrixType::ScalarType diagonalizingRelTolerance = typename MatrixType::ScalarType(1e-5))
{
  typedef typename MatrixType::ScalarType ScalarType;
  int dimension = A.numberOfRows();
  MatrixType D(dimension,dimension);
  if(!symMatrixDiagonalize(A,D,diagonalizingRelTolerance))
  {
    throw std::runtime_error("maxEigenValue::Failed to diagonalize a matrix");
  }
  ScalarType dominant(0);
  for(int i=0;i<dimension;++i)
  {
    ScalarType diam(0);
    for(int j=0;j<dimension;++j)
      if( i != j )
        diam += capd::abs(D[i][j]);
    ScalarType elem = right(D[i][i]+diam);
    if(i==0) dominant=elem;
    else if(!(elem<dominant)) dominant = elem;
  }
  return dominant;
}

/**
  Crout Decomposition of a matrix
  As a result matrix D is a lower triangle
  and G is an upper triangle with 1 on diagonal
*/
template<typename MatrixType>
void croutDecomposition(const MatrixType &A, MatrixType &D, MatrixType &G)
{
  D.clear();
  G.clear();
  int i,j,k;
  for(j=0;j<D.numberOfRows();j++)
  {
    for(i=j;i<D.numberOfColumns();i++)
    {
      D[i][j] = A[i][j];
      for(k=0;k<=j-1;k++)
        D[i][j] -= D[i][k]*G[k][j];
    }
    G[j][j]= TypeTraits<typename MatrixType::ScalarType>::one();
    for(i=j+1;i<G.numberOfRows();i++)
    {
      G[j][i] = A[j][i];
      for(k=0;k<=j-1;k++)
        G[j][i] -= D[j][k]*G[k][i];
      if(!(D[j][j]!=TypeTraits<typename MatrixType::ScalarType>::zero() ))
      {
        throw std::runtime_error("Crout Decomposition: cannot decompose singular matrix");
      }
      G[j][i] /= D[j][j];
    }
  }
}

template<typename MatrixType>
MatrixType invLowerTriangleMatrix(const MatrixType &A)
{
  MatrixType result(A.numberOfRows(),A.numberOfColumns());
  typedef typename MatrixType::ScalarType Scalar;
  for(int i=0;i<result.numberOfRows();++i)
  {
    if(!(A[i][i]<0 || A[i][i]>0))
    {
      throw std::runtime_error("cannot inverse lower triangle matrix - zero at diagonal");
    }
    result[i][i] = Scalar(1) / A[i][i];
    for(int j=0;j<i;++j)
    {
      for(int k=j;k<i;++k)
        result[i][j] += A[i][k] * result[k][j];
      result[i][j] *= -result[i][i];
    }
  }
  return result;
}

template<typename MatrixType>
MatrixType invUpperTriangleMatrix(const MatrixType &A)
{
  int dim = A.numberOfRows();
  MatrixType result(dim,A.numberOfColumns());
  typedef typename MatrixType::ScalarType Scalar;
  for(int i=0;i<result.numberOfRows();++i)
  {
    if(!(A[i][i]<0 || A[i][i]>0))
    {
      throw std::runtime_error("cannot inverse upper triangle matrix - zero at diagonal");
    }
    result[i][i] = Scalar(1) / A[i][i];
    for(int j=0;j<i;++j)
    {
      for(int k=j;k<i;++k)
        result[j][i] += A[k][i] * result[j][k];
      result[j][i] *= -result[i][i];
    }
  }
  return result;
}


template<typename MatrixType>
MatrixType inverseMatrix(const MatrixType &A)
{
  if(A.numberOfRows()!=A.numberOfColumns())
  {
    throw std::runtime_error("Cannot inverse nonsquare matrix!");
  }
  MatrixType Q(A.numberOfRows(),A.numberOfColumns()),
            R(A.numberOfRows(),A.numberOfColumns());
  QR_decompose(A,Q,R);
  R = invUpperTriangleMatrix(R);
  Q.Transpose();
  return R*Q;
}

template<typename MatrixType>
MatrixType gaussInverseMatrix(const MatrixType& A)
{
  if(A.numberOfRows()!=A.numberOfColumns())
  {
    throw std::runtime_error("Cannot inverse nonsquare matrix!");
  }
  int dim = A.numberOfRows();
  MatrixType result(dim, dim);
  MatrixType b = MatrixType::Identity(dim);

  gauss(A,b,result);

  return result;
}

template<class MatrixType>
void krawczykCorrection(const MatrixType& A, MatrixType& invA)
{
  MatrixType C = midMatrix(invA);
  // compute T = C*A-Id
  MatrixType T = C*A;
  for(int i=1;i<=T.numberOfRows();++i)
    T(i,i) -= TypeTraits<typename MatrixType::ScalarType>::one();
  invA = intersection(C - T*invA,invA);
}

template<class MatrixType>
MatrixType krawczykInverse(const MatrixType& A)
{
  MatrixType invA = gaussInverseMatrix(A);
  krawczykCorrection(A,invA);
  return invA;
}

}} // namespace capd::matrixAlgorithms

#endif // _CAPD_MATRIXALGORITHMS_FLOATMATRIXALGORITHMS_HPP_ 

/// @}
