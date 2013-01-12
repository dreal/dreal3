/////////////////////////////////////////////////////////////////////////////
/// @file EllipsoidSet.hpp
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details. 

#include "capd/auxil/minmax.h"

#ifndef _CAPD_DYNSET_ELLIPSOIDSET_HPP_ 
#define _CAPD_DYNSET_ELLIPSOIDSET_HPP_ 

#include "capd/dynset/EllipsoidSet.h"
#include "capd/matrixAlgorithms/floatMatrixAlgorithms.hpp"

namespace capd{
namespace dynset{

template<typename FlVectorType, typename MatrixType>
typename EllipsoidSet<FlVectorType,MatrixType>::ScalarType EllipsoidSet<FlVectorType,MatrixType>::size(void)
{
  return capd::vectalg::size(boxInterval());
}

template<typename FlVectorType, typename MatrixType>
EllipsoidSet<FlVectorType,MatrixType>::EllipsoidSet(
    const VectorType& the_z,
    FlScalar the_r,
    const MatrixType& the_L
  ):m_z(the_z),
    m_L(the_L),
    m_r(the_r)
{}

template<typename FlVectorType, typename MatrixType>
typename EllipsoidSet<FlVectorType,MatrixType>::ScalarType
  EllipsoidSet<FlVectorType,MatrixType>::mz_euclNorm(const VectorType& a)
{
  int j;
  ScalarType sum(0.0);
  for(j=0;j<a.dimension();++j)
    sum += power(a[j],2);
  if(sum.leftBound()<0)
    return sqrt(ScalarType(0,sum.rightBound()));
  else
    return sqrt(sum);
}

template<typename FlVectorType, typename MatrixType>
typename EllipsoidSet<FlVectorType,MatrixType>::ScalarType
  EllipsoidSet<FlVectorType,MatrixType>::Hybrid_norm_eucl(const MatrixType& a,int i)
{
  int j;
  ScalarType sum(0.0);
  for(j=0;j<a.numberOfColumns();++j)
    sum += power(a[i-1][j],2);
  if(sum.leftBound()<0)
    return sqrt(ScalarType(0,sum.rightBound()));
  else
    return sqrt(sum);
}

template<typename FlVectorType, typename MatrixType>
typename EllipsoidSet<FlVectorType,MatrixType>::ScalarType
  EllipsoidSet<FlVectorType,MatrixType>::Hybrid_norm_eucl(const VectorType& a,const VectorType& b)
{
  int j, dim = a.dimension();
  ScalarType sum(0.0);
  for(j=0;j<dim;j++)
    sum+=power(a[j],2);
  for(j=0;j<dim;j++)
    sum+=power(b[j],2);
  if(sum.leftBound()<0)
    return sqrt(ScalarType(0,sum.rightBound()));
  else
    return sqrt(sum);
}

template<typename FlVectorType, typename MatrixType>
typename EllipsoidSet<FlVectorType,MatrixType>::ScalarType
  EllipsoidSet<FlVectorType,MatrixType>::Hybrid_norm_eucl(const MatrixType& a, const MatrixType& b,int i)
{
  return Hybrid_norm_eucl(a.row(i-1),b.row(i-1));
}

template<typename FlVectorType, typename MatrixType>
typename EllipsoidSet<FlVectorType,MatrixType>::VectorType
  EllipsoidSet<FlVectorType,MatrixType>::Hybrid_norm_eucl(const MatrixType& a)
{
  VectorType temp(a.numberOfRows());
  for(int i=0;i<temp.dimension();++i)
    temp[i] = Hybrid_norm_eucl(a,i+1);
  return temp;
}

template<typename FlVectorType, typename MatrixType>
typename EllipsoidSet<FlVectorType,MatrixType>::ScalarType
  EllipsoidSet<FlVectorType,MatrixType>::MatrixEuclNormUp(MatrixType &a)
{
//
// szacujemy norme euklidesowa przez norme Frobeniusa
//  IntervalType temp=0;
//  for(int i=0; i<DIM; i++)
//    for(int j=0; j<DIM; j++)
//  temp+=power(a[i][j],2);
//  return sqrt(temp.rightBound());
// szacowanie norma Frobeniusa "za grube"
// duzo lepsze oszacowanie:
// n_e(A)^2 <= n_n(At*A)
// gdzie A-macierz, At- A transponowane
// n_e-norma euklidesowa, n_n-norma "nieskonczonosc" (max. suma modulow w wierszu)
// (Fortuna,Macukow,Wasowski "Metody numeryczne", str. 191)
  MatrixType at = Transpose(a);
  MatrixType aat = at*a;
  typename ScalarType::BoundType max_sum=0;
  for(int i=0; i<aat.numberOfRows(); ++i)
  {
    ScalarType sum(0.); // IntervalType
    for(int j=0; j<aat.numberOfColumns(); ++j)
    {
      sum += abs(aat[i][j]);
    }
    max_sum=capd::max(max_sum, sum.rightBound());
  }

  return sqrt(ScalarType(0,max_sum));
}

// QR decomposition
template<typename FlVectorType, typename MatrixType>
void EllipsoidSet<FlVectorType,MatrixType>::QR_decompose_t_mz(
    const MatrixType& A1,
    const MatrixType& A2,
    MatrixType& R
  )
{
  // CO TA FUNKCJA ROBI: co jest wejsciem , a co wyjsciem  <-
  // wyglada na to, ze R jest jakims wynikiem <- P. Zgliczynski
  // wprowadzilem te const , bo mnie kompilator meczylo o to

  int dim = R.numberOfRows();
  MatrixType Q1(dim,dim), Q2(dim,dim), Q1t(dim,dim), Q2t(dim,dim);
  VectorType r(dim), p1(dim), p2(dim);
  ScalarType norm;
  ScalarType s;
  int i,j;

  norm = Hybrid_norm_eucl(A1,A2,1);
  Q1[0] = A1[0]/norm;
  Q2[0] = A2[0]/norm;
  R[0][0] = norm;

  for(i=1; i<dim; ++i)
  {
    r = Q1*A1[i]+Q2*A2[i];
    Q1t = Transpose(Q1);
    Q2t = Transpose(Q2);
    p1 = A1[i]-Q1t*r;
    p2 = A2[i]-Q2t*r;

    s = Hybrid_norm_eucl(p1,p2);
    Q1[i] = p1/s;
    Q2[i] = p2/s;

    for(j=1; j<=i; j++)
      R[j-1][i]=r[j-1];
    R[i][i]=s;
  }
}


template<typename FlVectorType, typename MatrixType>
void EllipsoidSet<FlVectorType,MatrixType>::Solve_gauss(MatrixType& A, MatrixType& X, MatrixType& B)
{
  MatrixType B_tr=Transpose(B);
  for(int i=0; i<A.numberOfRows(); i++)
    X[i] = capd::matrixAlgorithms::gauss(A,VectorType(B_tr[i]));
  X.Transpose();
}

template<typename FlVectorType, typename MatrixType>
void EllipsoidSet<FlVectorType,MatrixType>::N_move(MatrixType& A,VectorType& b)
{
  int dim = b.dimension();
  MatrixType D(dim,dim),
             D_odwr(dim,dim),
             C(dim,dim),
             R(dim,dim);
  ScalarType q,gamma,delta,r_;
  int i;

  VectorType zi_= A*m_z+b;
  VectorType z_ = capd::vectalg::midVector(zi_);
  VectorType d = abs(zi_-z_);
  d = rightVector(d);

  MatrixType Bi=A*m_L;
  MatrixType B = capd::vectalg::midMatrix(Bi);
  VectorType dp=Hybrid_norm_eucl(Bi-B);
  dp = rightVector(dp);

  for(i=0; i<dim; i++)
    D[i][i] = d[i] + dp[i]*m_r;

  for(i=0; i<dim; i++)
    D_odwr[i][i] = ScalarType(1.)/D[i][i];
  q = mz_euclNorm(D_odwr*d) + mz_euclNorm(D_odwr*dp)*m_r;
  q = q.rightBound();

  MatrixType M1 = ScalarType(m_r)*B;
  MatrixType M2 = q*D;
  QR_decompose_t_mz(midMatrix(M1),midMatrix(M2),R);
  MatrixType L_ = Transpose(R);

  Solve_gauss(L_,C,B);
//bb=L_*C;
  gamma = MatrixEuclNormUp(C);
  Solve_gauss(L_,C,D);
//dd=L_*C;
  delta = MatrixEuclNormUp(C);

  r_=gamma*m_r + delta*q;

// podmien na nowe wartosci
  m_z = z_;
  m_L = L_;
  m_r = r_.rightBound();
}

template<typename FlVectorType, typename MatrixType>
void EllipsoidSet<FlVectorType,MatrixType>::move(capd::dynsys::DynSys<MatrixType>& dynsys)
{
  VectorType b(m_z.dimension());

  VectorType xx = boxInterval();
  VectorType y = dynsys.Phi(m_z);
  split(y,b);
  b += dynsys.Remainder(xx);
  m_z.clear();
  MatrixType A = dynsys.JacPhi(xx);
//   double scale = 2.0;   A[0][0] = scale;   A[0][1] = 0;   A[0][2] = 0;   A[1][0] = 0;   A[1][1] = scale;   A[1][2] = 0;   A[2][0] = 0;   A[2][1] = 0;   A[2][2] = scale;   b = 0;
  N_move(A,b);

  m_z += y;
}

template<typename FlVectorType, typename MatrixType>
void EllipsoidSet<FlVectorType,MatrixType>::move(capd::dynsys::DynSys<MatrixType>& dynsys, EllipsoidSet& result) const
{
// just for compatibility.
  result = *this;
  result.move(dynsys);
}

template<typename FlVectorType, typename MatrixType>
typename EllipsoidSet<FlVectorType,MatrixType>::VectorType
  EllipsoidSet<FlVectorType,MatrixType>::boxInterval()
{
  VectorType ksi(m_z.dimension());
  for(int i=0; i<ksi.dimension(); ++i)
    ksi[i] = ScalarType(-m_r,m_r);
  return m_z + m_L*ksi;
// Neumayer - Theorem 3
//   return z+IntervalType(-r,r)*Hybrid_norm_eucl(L);
}

// DW: this works for DIM=3 only?
template<typename FlVectorType, typename MatrixType>
typename EllipsoidSet<FlVectorType,MatrixType>::VectorType
  EllipsoidSet<FlVectorType,MatrixType>::sBoxInterval(EllipsoidSet &p, FlScalar mdev)
{
  VectorType iv1 = boxInterval();
  VectorType iv2 = p.boxInterval();
  ScalarType i1 = ball(intervalHull(iv1[0],iv2[0]), mdev);
  ScalarType i2 = ball(intervalHull(iv1[1],iv2[1]), mdev);
  ScalarType i3 = ball(intervalHull(iv1[2],iv2[2]), mdev);
  return VectorType(i1,i2,i3);
}

template<typename FlVectorType, typename MatrixType>
FlVectorType EllipsoidSet<FlVectorType,MatrixType>::getCenter()
{
  VectorType xx = boxInterval();
  FlVectorType temp(m_z.dimension());
  for(int i=0;i<temp.dimension();++i)
    temp[i]=xx[i].mid().rightBound();
  return temp;
}

template<typename FlVectorType, typename MatrixType>
std::string EllipsoidSet<FlVectorType,MatrixType>::show() const
{
  std::ostringstream descriptor;
  descriptor << "EllipsoidSet: z=";
  descriptor << m_z << "\n L=";
  descriptor << m_L << "\n r=" << m_r <<" ";
  return descriptor.str();
}

template<typename FlVectorType, typename MatrixType>
typename EllipsoidSet<FlVectorType,MatrixType>::VectorType
  EllipsoidSet<FlVectorType,MatrixType>::affineTransformation(
    const MatrixType& A_M, const VectorType& A_C
  ) const
{
  VectorType ksi(m_z.dimension());
  for(int i=0; i<ksi.dimension(); i++)
    ksi[i] = ScalarType(-m_r,m_r);

  return A_M*(m_z-A_C) + (A_M*m_L)*ksi;
}

}} // namespace capd::dynset

#endif // _CAPD_DYNSET_ELLIPSOIDSET_HPP_ 
