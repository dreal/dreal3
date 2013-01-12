/// @addtogroup dynsys
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file OdeNumTaylor.hpp
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#ifndef _CAPD_DYNSYS_ODENUMTAYLOR_HPP_
#define _CAPD_DYNSYS_ODENUMTAYLOR_HPP_

#include <vector>
#include <stdexcept>

#include "capd/dynsys/DynSys.hpp"
#include "capd/basicalg/factrial.h"
#include "capd/dynsys/OdeNumTaylor.h"

namespace capd{
namespace dynsys{

template <typename MatrixType>
void OdeNumTaylor<MatrixType>::tabulateCoefficients(const VectorType &x, int upto, VectorType coefs[]) const
{
// funtion computes Taylor coefficients for solution x'=ode.f(x)
// up to order <upto>
// x - initial condition
// upto - maximal order
// on output: coefs[r][i] is equal to x_i^{r+1}

  int dim = x.dimension();
  MatrixType *d2f_tab = new (dim,dim) MatrixType[dim]; // d2f_tab[i][j][k]=d^2f_i/dx_jdx_k

  MatrixType df_tab = ode.df(x); // df_tab[i][j]=df_i/dx_j
  for(int i=0;i<dim;i++)
    d2f_tab[i] = ode.d2f(i,x);

  coefs[0] = ode.f(x);  // 1-st order x'=ode.f(x)
  coefs[1] = df_tab*coefs[0];  // 2-nd order x^{2}=df*x'


  for (int r=2;r<upto;r++)
  {
    VectorType u(dim);
    MatrixType sum2(dim,dim);
    for(int j=0;j<dim;j++)
      for(int k=0;k<dim;k++)
      {
        ScalarType t(0.);
        for(int s=0;s<=r-2;s++)
          t += newton(r-1,s)*coefs[r-2-s][k]*coefs[s][j];
        sum2[j][k]=t;
      }
    for(int i=0;i<dim;i++)
    {
      ScalarType sum(0.);
      for(int j=0;j<dim;j++)
        for(int k=0;k<dim;k++)
        {
          sum += d2f_tab[i][j][k]*sum2[j][k];
        }
      u[i]=sum;
    }
    coefs[r] = df_tab*coefs[r-1]+u;
  }
  delete [] d2f_tab;
}

// -------------------------------------------------------------------------

template <typename MatrixType>
typename OdeNumTaylor<MatrixType>::VectorType OdeNumTaylor<MatrixType>::Phi(const VectorType &x)
{
  VectorType *coefs = new (x.dimension()) VectorType[order];

  tabulateCoefficients(x,order,coefs);
  VectorType result=x;
  ScalarType step_power(1);
  for(int r=0;r<order;r++)
  {
    step_power*=step;
    ScalarType factor = step_power/factorial(r+1);
    result += factor*coefs[r];
  }
  delete []coefs;
  return result;
}

// -------------------------------------------------------------------------

template <typename MatrixType>
typename OdeNumTaylor<MatrixType>::VectorType OdeNumTaylor<MatrixType>::Remainder(const VectorType &x)
{
  int ok;
  VectorType enclosure = this->enclosureGuaranteeingBounds(x,&ok);
  if(!ok)
  {
    std::runtime_error("OdeNumTaylor::Remainder  error - enclosure not found\n");
  }
  VectorType *coefs = new (x.dimension()) VectorType[order+1];
  tabulateCoefficients(enclosure,order+1,coefs);
  VectorType result = coefs[order]*(step^(order+1))/factorial(order+1);
  delete []coefs;
  return result;
}

// -------------------------------------------------------------------------

template <typename MatrixType>
MatrixType OdeNumTaylor<MatrixType>::JacPhi(const VectorType &x)
{
  int dim = x.dimension();
  MatrixType *d2f_tab = new (dim,dim) MatrixType[dim];  // d2f_tab[i][j][k]=d^2f_i/dx_jdx_k
  VectorType *coefs = new (dim) VectorType[order];
              // coefs[r][i]= \frac{d^{r+1}\varphi_i}{d^{r+1}t}
  MatrixType *dcoefs = new (dim,dim) MatrixType[order];
      //  dcoefs[r][i][l]= \frac{d^{r+1}  (\partial_l \varphi_i)}{d^{r+1}t}
  int i,j,k,l,r,s;

  MatrixType result = MatrixType::Identity(dim);
  MatrixType df_tab = ode.df(x);
  for(i=0;i<dim;i++)
    d2f_tab[i] = ode.d2f(i,x);

  tabulateCoefficients(x,order,coefs);
  dcoefs[0] = df_tab;

  for(i=0;i<dim;++i)
    for(l=0;l<dim;++l)
    {
      dcoefs[1][i][l] = ScalarType(0);
      for(k=0;k<dim;++k)
      {
        dcoefs[1][i][l] += d2f_tab[i][l][k]*coefs[0][k] + df_tab[i][k]*dcoefs[0][k][l];
//            d2f_tab[i][l]*coefs[0] + df_tab[i]*dcoefs[0].column(l);
      }
    }
  for (r=2;r<order;r++)
  {
    for(l=0;l<dim;l++)
    {
      MatrixType sum2(dim,dim);
      for(j=0;j<dim;j++)
      {
        for(k=0;k<dim;k++)
        {
          ScalarType t(0.);
          for(s=0;s<=r-2;s++)
            t+=newton(r-1,s) * ( dcoefs[r-2-s][k][l]*coefs[s][j] + coefs[r-2-s][k]*dcoefs[s][j][l] );
               sum2[j][k]=t;
        } // k - for
      } // j - for
      for(i=0;i<dim;i++)
      {
        ScalarType sum(0.);
        for(j=0;j<dim;j++)
          for(k=0;k<dim;k++)
            sum+=d2f_tab[i][j][k]*sum2[j][k];
        dcoefs[r][i][l] = ScalarType(0);
        for(k=0;k<dim;++k)
          dcoefs[r][i][l] += d2f_tab[i][l][k]*coefs[r-1][k] + df_tab[i][k]*dcoefs[r-1][k][l] + sum;
//            dcoefs[r][i][l] = d2f_tab[i][l]*coefs[r-1] + df_tab[i]*dcoefs[r-1].column(l) + sum;
      } // i - for
    } // l - for
  } // r - for

  ScalarType step_power(1.);
  for(r=0;r<order;r++)
  {
    step_power*=step;
    ScalarType factor = step_power/factorial(r+1);
    result = result+factor*dcoefs[r];
  }
  delete [] coefs;
  delete [] dcoefs;
  delete [] d2f_tab;
  return result;
}

}} // namespace capd::dynsys

#endif // _CAPD_DYNSYS_ODENUMTAYLOR_HPP_

/// @}
