/// @addtogroup vecttst
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file vecttst.cpp
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#include <fstream>
#include <stdexcept>
#include "capd/intervals/DoubleInterval.h"
#include "capd/vectalg/Vector.hpp"
#include "capd/vectalg/Matrix.hpp"
#include "capd/vectalg/Norm.hpp"

const int DIM = 3;
using capd::interval;
typedef capd::vectalg::Vector<double,3> DVector;
typedef capd::vectalg::Matrix<double,3,3> DMatrix;
typedef capd::vectalg::Vector<interval,3> IVector;
typedef capd::vectalg::Matrix<interval,3,3> IMatrix;
typedef capd::vectalg::Norm<IVector,IMatrix> Norm;
typedef capd::vectalg::EuclNorm<IVector,IMatrix> EuclNorm;
typedef capd::vectalg::MaxNorm<IVector,IMatrix> MaxNorm;
typedef capd::vectalg::SumNorm<IVector,IMatrix> SumNorm;
typedef capd::vectalg::EuclLNorm<IVector,IMatrix> EuclLNorm;
typedef capd::vectalg::MaxLNorm<IVector,IMatrix> MaxLNorm;
typedef capd::vectalg::SumLNorm<IVector,IMatrix> SumLNorm;

using namespace capd::matrixAlgorithms;

void test_gauss(void)
{
  std::ifstream inp("matrix.txt");
  if(!inp)
    throw std::runtime_error("Failed to open inp");

  std::cout << "\n\n============================\n";
  std::cout << "Gauss test\n";
  std::cout << "============================\n\n";

  DVector v,r;
  DMatrix a,b;
  IVector iv,ir;
  IMatrix ia;

  inp >> v;
  inp >> a >> b;

  iv = IVector(v);
  ia = IMatrix(a);

  r = gauss(a,v);

  capd::rounding::DoubleRounding::roundUp();
  ir = gauss(ia,iv);
  capd::rounding::DoubleRounding::roundNearest();

  std::cout << "v=" << v << " iv=" << iv << std::endl;
  std::cout << "a=" << a << " ia=" << ia << std::endl;
  std::cout << "r=" << r << std::endl;
  std::cout << "ir=" << ir << std::endl;
  for(int i=0;i<ir.dimension();i++)
    std::cout << diam(ir[i]) << std::endl;
}

void QRdecomp_test(void)
{
  std::cout << "\n\n============================\n";
  std::cout << "QR decompose test\n";
  std::cout << "============================\n\n";

  std::ifstream inp("qrdane.txt");
  if(!inp)
    throw std::runtime_error("Failed to open inp\n");

  DMatrix a;
  IMatrix ia,iq,ir;
  inp >> a;
  ia = IMatrix(a);

  std::cout << "ia=" << ia << "\n";

  QR_decompose(ia,iq,ir);
  for(int i=0;i<iq.numberOfRows();i++)
    for(int j=0;j<iq.numberOfColumns();j++)
    {
      interval sp=iq[i]*iq[j];
      std::cout << sp << std::endl;
    }
}

void diagonalize_test(void)
{
  std::cout << "diagonalize test\n";
  std::ifstream inp("../tests/vecttst/diagdane.txt", std::ios::in);
  if(!inp) std::cout << "Failed to open inp\n";

  DMatrix a;
  IMatrix ia,id;

  inp >> a;

  ia = IMatrix(a);

  std::cout << "a=" << a << "\n";
  std::cout << "ia=" << ia << "\n";

  symMatrixDiagonalize(ia,id);
  for(int i=0;i<DIM;i++)
  {
    std::cout << "id[" << i << "]=" << id[i] << "\n";
  }
  std::cout << "Spectral radius= " << spectralRadiusOfSymMatrix(ia) << "\n";
}

void norm_test(void)
{
  std::cout << "norm test\n";
  std::ifstream inp("../tests/vecttst/normdane.txt");
  if(!inp) std::cout << "Failed to open inp\n";

  DMatrix a;
  IMatrix ia;

  inp >> a;

  ia = IMatrix(a);

  std::cout << "a=" << a << "\n";
  std::cout << "ia=" << ia << "\n";

  EuclNorm en;
  MaxNorm mn;
  SumNorm sn;
  EuclLNorm eln;
  MaxLNorm mln;
  SumLNorm sln;

  std::cout << "Euclidean norm = " << en(ia) << " \n";
  std::cout << "Maximum norm = " << mn(ia) << " \n";
  std::cout << "Sum norm = " << sn(ia) << " \n";
  std::cout << "Euclidean logarithmic norm = " << eln(ia) << " \n";
  std::cout << "Maximum logarithmic norm = " << mln(ia) << " \n";
  std::cout << "Sum logarithmic norm = " << sln(ia) << " \n";
}


void matrix_test(void)
{
  std::cout << "matrix test\n";
  std::ifstream inp("../tests/vecttst/matrix.txt");
  if(!inp) std::cout << "Failed to open inp\n";

  DVector v;
  DMatrix a,b;
  IVector iv;
  IMatrix ia;

  inp >> v;
  inp >> a >> b;

  iv = IVector(v);
  ia = IMatrix(a);

  std::cout << "v=" << v << " iv=" << iv << "\n";
  std::cout << "a=" << a << " ia=" << ia << "\n";
  for(int i=0;i<DIM;i++)
  {
    std::cout << "ia[" << i << "]=" << ia[i] << "\n";
  }
}


void ztest_gauss(void)
{
  std::cout << "(z) Gauss test\n";

  IVector iv,r;
  IMatrix ia;

   /*
   iv[0]=interval(-7.45037e-16,-5.4116e-16);
   iv[1]=interval(-2.12588e-15,-9.94006e-16);
   iv[2]=interval(-4.44089e-21,4.44089e-21);
   */
  iv[0]=5.0;

  ia[0][0]=-0.237304;
  ia[0][1]= -1.18286;
  ia[0][2]=8.49793e-322;

  ia[1][0]=1.18286;
  ia[1][1]=-0.000731345;
  ia[1][2]=-5.7114e-321;

  ia[2][0]=-6.81317e-321;
  ia[2][1]=-1.34386e-321;
  ia[2][2]=1.0;

  r = gauss(ia,iv);

  IVector res;
  res=ia*r - iv;

  std::cout << "ia*r - iv = " << res << "\n";
  std::cout << "iv = " << iv << "\n";

  std::cout << "ia*r - iv = " << midVector(res) << "\n";
  std::cout << "iv = " << midVector(iv) << "\n";
}


int main(int , char* [])
{
  try
  {
    QRdecomp_test();
    diagonalize_test();
    norm_test();
    matrix_test();
    ztest_gauss();
    test_gauss();
  }
  catch (const std::exception &event)
  {
    std::cout << "Error: " << event. what () << "\n";
  }

  capd::rounding::DoubleRounding::roundNearest();
  return 0;
}

/// @}
