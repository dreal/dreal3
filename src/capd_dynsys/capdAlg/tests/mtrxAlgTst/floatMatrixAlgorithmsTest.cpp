/// @addtogroup vecttst
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file floatMatrixAlgorithmsTest.cpp
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#include <fstream>
#include <sstream>
#include "capd/vectalg/Norm.hpp"
#include "capd/vectalg/lib.h"
#include "capd/rounding/DoubleRounding.h"
using namespace capd;
using namespace capd::matrixAlgorithms;

void test_gauss(void)
{
   std::ifstream inp("DMatrix.txt");

   std::cout << "\n\nGauss test\n";
   std::cout << "==========\n";
   if(!inp) std::cout << "Failed to open inp\n";

   DVector v;
   DMatrix a,b;

   inp >> v;
   inp >> a >> b;

   IVector iv(v);
   IMatrix ia(a);

   DVector r = gauss(a,v);

   capd::rounding::DoubleRounding::roundUp();
   IVector ir = gauss(ia,iv);
   capd::rounding::DoubleRounding::roundNearest();

   std::cout << "v=" << v << " iv=" << iv << std::endl;
   std::cout << "a=" << a << " ia=" << ia << std::endl;
   std::cout << "r=" << r << std::endl;
   std::cout << "ir=" << ir << std::endl;
   for(int i=0;i<ir.dimension();i++)
   {
      std::cout << "     " << diam(ir[i]) << std::endl;
   }
}

void QRdecomp_test(void)
{
   std::cout << "\n\nQRdecomp test\n";
   std::cout << "=============\n";

   std::ifstream inp("qrdane.txt");
   if(!inp) std::cout << "Failed to open inp\n";

   DMatrix a;
   inp >> a;

   IMatrix ia(a);
   IMatrix iq(a.numberOfRows(),a.numberOfColumns()), ir(a.numberOfRows(),a.numberOfColumns());

   std::cout << "ia=" << ia << "\n";

   QR_decompose(ia,iq,ir);
   std::cout << "iq=" << iq << "\n";
   std::cout << "ir=" << ir << "\n";
   std::cout << "iq*ir=" << iq*ir << "\n\n";
   for(int i=0;i<iq.numberOfRows();i++)
   {
      for(int j=0;j<iq.numberOfRows();j++)
      {
         interval sp=iq.row(i)*iq.row(j);
         std::cout  << sp << " ";
      }
      std::cout << std::endl;
   }
}

void diagonalize_test(void)
{
   std::cout << "\n\ndiagonalize test\n";
   std::cout << "================\n";
   std::ifstream inp("diagdane.txt", std::ios::in);
   if(!inp) std::cout << "Failed to open inp\n";

   DMatrix a;
   inp >> a;

   IMatrix ia(a), id(a.numberOfRows(),a.numberOfColumns());

   std::cout << "a=" << a << "\n";
   std::cout << "ia=" << ia << "\n";

   symMatrixDiagonalize(ia,id);
   for(int i=0;i<id.numberOfRows();i++)
   {
      std::cout  << "id[" << i << "]=" << id.row(i) << "\n";
   }
   std::cout  << "Spectral radius= " << spectralRadiusOfSymMatrix(ia) << "\n";
}

void norm_test(void)
{
   std::cout << "\n\nnorm test\n";
   std::cout << "============================\n";
   std::ifstream inp("normdane.txt");
   if(!inp) std::cout << "Failed to open inp\n";

   DMatrix a;
   inp >> a;

   IMatrix ia(a);

   std::cout << "a=" << a << "\n";
   std::cout << "ia=" << ia << "\n";

   IEuclNorm en;
   IMaxNorm mn;
   ISumNorm sn;
   IEuclLNorm eln;
   IMaxLNorm mln;
   ISumLNorm sln;

   std::cout << "Euclidean norm = " << en(ia) << " \n";
   std::cout << "Maximum norm = " << mn(ia) << " \n";
   std::cout << "Sum norm = " << sn(ia) << " \n";
   std::cout << "Euclidean logarithmic norm = " << eln(ia) << " \n";
   std::cout << "Maximum logarithmic norm = " << mln(ia) << " \n";
   std::cout << "Sum logarithmic norm = " << sln(ia) << " \n";
}


void matrix_test(void)
{
   std::cout << "\n\nmatrix test\n";
   std::cout << "===========\n";
   std::ifstream inp("DMatrix.txt");
   if(!inp) std::cout << "Failed to open inp\n";

   DVector v;
   DMatrix a,b;

   inp >> v;
   inp >> a >> b;

   IVector iv(v);
   IMatrix ia(a);

   std::cout << "v=" << v << " iv=" << iv << std::endl;
   std::cout << "a=" << a << " ia=" << ia<< std::endl;
   for(int i=0;i<ia.numberOfRows();i++)
   {
      std::cout  << "ia[" << i << "]=" << ia.row(i) << "\n";
   }
}


void ztest_gauss(void)
{
   std::cout << "\n\n(z) Gauss test\n";
   std::cout << "==============\n";

   IVector iv(3);
   IMatrix ia(3,3);


// iv[0]=interval(-7.45037e-16,-5.4116e-16);
// iv[1]=interval(-2.12588e-15,-9.94006e-16);
// iv[2]=interval(-4.44089e-21,4.44089e-21);

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

   IVector r = gauss(ia,iv);
   IVector res = ia*r - iv;

   std::cout << "ia*r - iv = " << res << "\n";
   std::cout << "iv = " << iv << "\n";

   std::cout << "ia*r - iv = " << midVector(res) << "\n";
   std::cout << "iv = " << midVector(iv) << "\n";
}

int main(int , char* [])
{
   //init_fpunit();

   try{
      if((CAPD_DEFAULT_DIMENSION !=0) && (CAPD_DEFAULT_DIMENSION!=3)) throw std::runtime_error(
         " Wrong dimension!  \n dimension in file vectalg/dimension.h should be 3.\n Change and recompile!"
         );
      QRdecomp_test();
      diagonalize_test();
      norm_test();
      matrix_test();
      ztest_gauss();
      test_gauss();
   }catch(std::exception& e)
   {
      std::cout << e.what();
   }
   catch(...)
   {
      std::cout << "Unknown exception!\n";
   }
   capd::rounding::DoubleRounding::roundNearest();
   return 0;
}

/// @}
