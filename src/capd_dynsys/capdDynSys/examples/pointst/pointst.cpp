/// @addtogroup poincare
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file pointst.cpp
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#include <stdexcept>
#include <cmath>

#include "capd/krak/krak.h"
#include "capd/capdlib.h"
#include "capd/poincare/PoincareMap.hpp"

using namespace capd;

const int DIMENSION=3;
double minx=-2.2;
double maxx=1.6;
double miny=-2.6;
double maxy=2.;

Frame fr, txt;

// -----------------------------------------------------------------

void initGraphics()
{
   openGW(900,700,WHITE,BLACK);
   rootFrame.Clear();
   txt = Frame(0,0,595,130);
   fr = Frame(5,135,555,585,WHITE,BLACK);
   fr.setWorldCoord(minx,miny,maxx,maxy);
   fr.line(0.0,miny,0.0,maxy,BLACK);
   fr.line(minx,0.0,maxx,0.0,BLACK);
}

// -----------------------------------------------------------------

void C0Test()
{
   double grid = 30;
   double step = 0.3;
   int order = 20;
   IMap f = "par:c;var:x,y,z;fun:y,z,c^2-y-0.5*x*x;";
   IFunction s ="var:x,y,z,d;fun:z;";
   ITaylor T(f,order,step);
   IPoincareMap pm(T,s);
   f.setParameter("c",interval(1.0));

   DMap ff= "var:x,y,z,c;fun:y,z,c^2-y-0.5*x*x;";
   DFunction fs ="var:x,y,z,d;fun:z;";
   DTaylor ft(ff,order,step);
   DPoincareMap flpm(ft,fs);
   ff.setParameter("c",1.0);

   IVector iv(3);
   iv[0] = iv[2] = interval(0.0);
   iv[1] = interval(15,16)/interval(10);

   fr << At(11,55) << "y";
   fr << At(0,33) << "y'";
   txt << "Test of class \"PoincareMap\".\n";
   txt << "ODE: Kura-Siva, order:" << order
      << ", Poincare section: y\"=0" <<"\n\n";
   txt << "P - Poincare return map,    The set s=" << iv << "\n";
   txt << "We compute P(s) and P^2(s)\n";

   int c = RED;
   txt.SetFgColor(c);
   txt << "using set arithmetic and class PoincareMap\n";
   fr << At(7,20) << "P^2(s)";
   fr << At(26,26) << "P(s)";

   interval part = interval(iv[1].rightBound()-iv[1].leftBound())/interval(grid);
   pm.setFactor(0.3);

   for(int i=0;i<grid;i++){
      IVector w;
      w.clear();
      w[1]=iv[1].leftBound() + i*part + interval(0,1)*part;
      IVector r=w-midVector(w);

      C0Rect2Set rec(midVector(w),r);
      w = pm(rec);
      fr.boxFill(w[0].leftBound(),w[1].leftBound(),w[0].rightBound(),w[1].rightBound(),c);
      fr.box(w[0].leftBound(),w[1].leftBound(),w[0].rightBound(),w[1].rightBound());

      w = pm(rec);
      fr.boxFill(w[0].leftBound(),w[1].leftBound(),w[0].rightBound(),w[1].rightBound(),c);
      fr.box(w[0].leftBound(),w[1].leftBound(),w[0].rightBound(),w[1].rightBound());
   }

   c = GREEN;
   txt.SetFgColor(c);
   txt << "using vector arithmetic and class PoincareMap\n";
   grid *= 30;

   for(int i=0;i<=grid;i++){
      DVector v(0,1.5,0.);
      v[1] += 0.1*i/grid ;
      v = flpm(v);
      fr.dot(v[0],v[1],c);
      v = flpm(v);
      fr.dot(v[0],v[1],c);
   }

   waitBt();
}



// -----------------------------------------------------------------

void C1Test()
{
   rootFrame.Clear();
   rootFrame.precision(10);
   rootFrame << BgColor(BLACK) << FgColor(GREEN);
   rootFrame << "Rigorous proof of the existence of a periodic orbit in the Kuramoto-Sivashinsky equations\n\n";

   double step = 0.1;
   int order = 20;
   IMap f = "var:x,y,z;fun:y,z,1-y-0.5*x*x;";
   IFunction s ="var:x,y,z;fun:z;";
   ITaylor T(f,order,step);
   IPoincareMap pm(T,s);

   IEuclLNorm N;
   IVector x(interval(0.),interval(1.5259617305037),interval(0.));
   interval size = interval(-1.,1.)*interval(1e-7);
   IVector r(size,size,interval(0.));

   C0Rect2Set R(x); // this set represents center of a set
   C1Rect2Set S(x,r,N); // this set represents whole set

   IVector V=IVector(S);
   rootFrame << BgColor(WHITE) << FgColor(BLACK);
   rootFrame << "We compute the Poincare map and its derivative on the set:\nS = {"
            << V[0] << "," << V[1] << "}";

   // second iteration of Poincare Map
   pm(R);
   IVector imageInCenter = pm(R);
   rootFrame << "\n\nThe bound of the Poincare image P^2(center(S)):\n{"
            << imageInCenter[0] << "," << imageInCenter[1] << "}";
   imageInCenter[0] -= x[0];
   imageInCenter[1] -= x[1];


   IMatrix der(3,3);
   // second iteration of Poincare Map
   pm(S);
   IVector iv = pm(S,der);

   IVector im = f(iv);
   interval a = -im[0]/im[2] * der[2][0] + der[0][0];
   interval b = -im[0]/im[2] * der[2][1] + der[0][1];
   interval c = -im[1]/im[2] * der[2][0] + der[1][0];
   interval d = -im[1]/im[2] * der[2][1] + der[1][1];

   rootFrame << "\n\nDerivative of the Poincare map DP^2(S):\n";
   rootFrame << a << Tab(30) << b << "\n" << c  << Tab(30) << d;

// we compute the inverse matrix

   rootFrame << "\n\nWe compute the Interval Newton Operator of P^2-Id on S:";
   a -= interval(1.);
   d -= interval(1.);
   interval determinant = a*d - b*c;

   interval A = d/determinant;
   interval B = -b/determinant;
   interval C = -c/determinant;
   interval D = a/determinant;

   rootFrame << "\n\nThe inverse matrix D(P^2-Id)^(-1)(S):\n";
   rootFrame << A << Tab(30) << B << "\n" << C  << Tab(30) << D;

   interval x1 = x[0] - A*imageInCenter[0] - B*imageInCenter[1];
   interval x2 = x[1] - C*imageInCenter[0] - D*imageInCenter[1];
   rootFrame << "\n\nThe interval Newton operator N(S):\n{" << x1 << "," << x2 << "}\n";
   if(   x1.leftBound()>V[0].leftBound() && x1.rightBound()<V[0].rightBound() &&
      x2.leftBound()>V[1].leftBound() && x2.rightBound()<V[1].rightBound()
   )
   {
      rootFrame << BgColor(BLACK) << FgColor(GREEN);
      rootFrame << "is a subset of the set S, therefore there exists the unique periodic orbit in S!";
   }
   else
   {
      rootFrame << BgColor(BLACK) << FgColor(RED);
      rootFrame << "Fatal error: N(S) is not a subset of S!";
   }
   waitBt();
}

// ------------------------------------------------------------------

void computePoincare(IC2PoincareMap &PM, IVector &X, IMatrix &DP, IMatrix *D2P)
{
   IMatrix::setDefaultDimension(IMatrix::Dimension(3,3));
   IMatrix derivativeOfFlow;
   IMatrix hessianOfFlow[DIMENSION];

   C2Rect2Set theSet(X,IEuclLNorm());
   X = PM(theSet,derivativeOfFlow,hessianOfFlow);

   IVector dT = PM.computeDT(X,derivativeOfFlow);
   DP = PM.computeDP(X,derivativeOfFlow,dT);
   std::cout << "\n dP " << size(DP) << "\n derOfFlow " << size(derivativeOfFlow) << std::endl;
   IMatrix d2T = PM.computeD2T(X,derivativeOfFlow,dT,DP,hessianOfFlow);
   PM.computeD2P(X,derivativeOfFlow,dT,DP,hessianOfFlow,d2T,D2P);
}

// -----------------------------------------------------------------

void C2Test()
{
   IMatrix::setDefaultDimension(IMatrix::Dimension(3,3));
   IVector::setDefaultDimension(3);
   rootFrame << BgColor(WHITE) << FgColor(BLACK);
   rootFrame.Clear();
   rootFrame.precision(10);
   double step = 0.02;
   int order = 6;
   IC2Map f = "var:x,y,z;fun:y,z,1-y-0.5*x*x;";
   IFunction s ="var:x,y,z;fun:z;";
   IC2Taylor T(f,order,step);
   IC2PoincareMap PM(T,s);
//   PM.turnOffStepControl();

   IMatrix DQ, DP1, DP2;
   IMatrix D2P1[3], D2P2[3];
   IVector X(interval(0.1),interval(1.5259617305037),interval(0.));
   IVector copyOfX (X);

   rootFrame << BgColor(BLACK) << FgColor(GREEN);
   rootFrame << "C^0 - Test\n";
   rootFrame << "The Kuramoto-Sivashinsky equation satisfies condition Q(X):=S(P(S(P(X))))=X\n";
   rootFrame << "wherever the left side is well defined. Take";
   rootFrame << BgColor(WHITE) << FgColor(BLACK);
   rootFrame << "\n            X={" << X[0] << "," << X[1] << "}";
   computePoincare(PM,X,DP1,D2P1);
   rootFrame << "\n         P(X)={" << X[0] << "," << X[1] << "}";
   X[2] = 0.;
   X[0] = -X[0];
   computePoincare(PM,X,DP2,D2P2);
   rootFrame << "\n   P(S(P(X)))={" << X[0] << "," << X[1] << "}";
   X[0] = -X[0];
   rootFrame << "\nS(P(S(P(X))))={" << X[0] << "," << X[1] << "}\n";
   if(copyOfX[0].subset(X[0]) && copyOfX[1].subset(X[1]))
   {
      rootFrame << BgColor(BLACK) << FgColor(YELLOW);
      rootFrame << "OK: X is a subset of Q(X)!\n\n";
   }
   else
   {
      rootFrame << BgColor(BLACK) << FgColor(RED);
      rootFrame << "Fatal error: X is not a subset of Q(X)!\n\n";
   }
   rootFrame << BgColor(WHITE) << FgColor(BLACK);
   rootFrame << "------------------------------------------------------";

// C^1 test on Identity
   rootFrame << BgColor(BLACK) << FgColor(GREEN);
   rootFrame << "\n\nC^1 - Test\n";
   rootFrame << BgColor(WHITE) << FgColor(BLACK);
   int j, k, i, c, ss;

   for(i=0;i<2;i++)
      for(j=0;j<2;j++)
         for(k=0;k<2;k++)
            DQ[i][j]  += power(-1,i+k) *DP2[i][k]*DP1[k][j];

   rootFrame << DQ[0][0] << " " << DQ[0][1] << "\n" << DQ[1][0] << " " << DQ[1][1] << "\n";
   if(DQ[0][0].contains(1.) && DQ[0][1].contains(0.) && DQ[0][1].contains(0.) && DQ[1][1].contains(1.))
   {
      rootFrame << BgColor(BLACK) << FgColor(YELLOW);
      rootFrame << "OK: The derivative DQ(X) contains the Identity matrix!";
   }
   else
   {
      rootFrame << BgColor(BLACK) << FgColor(RED);
      rootFrame << "Fatal error: The derivative of SPSP do not contain the Identity matrix!";
   }
   rootFrame << BgColor(WHITE) << FgColor(BLACK);
   rootFrame << "\n\n------------------------------------------------------";

// C^2 test
   rootFrame << BgColor(BLACK) << FgColor(GREEN);
   rootFrame << "\n\nC^2 - Test";
   rootFrame << BgColor(WHITE) << FgColor(BLACK);
   rootFrame << "\nD^2P_1(X) =\n" << D2P1[0][0][0] << " " << D2P1[0][0][1] << "\n";
   rootFrame << D2P1[0][1][0] << " " << D2P1[0][1][1] << "\n";
   rootFrame << "\nD^2P_2(X) =\n" << D2P1[1][0][0] << " " << D2P1[1][0][1] << "\n";
   rootFrame << D2P1[1][1][0] << " " << D2P1[1][1][1] << "\n";

   interval temp;
   int ok1 = intersection(D2P1[0][0][1],D2P1[0][1][0],temp);
   int ok2 = intersection(D2P1[1][0][1],D2P1[1][1][0],temp);
   if(ok1 && ok2)
   {
      rootFrame << BgColor(BLACK) << FgColor(YELLOW);
      rootFrame << "OK: The hessian matrices D^2P_1(X) and D^2P_2(X) contain symmetric matrices!\n\n";
   }
   else
   {
      rootFrame << BgColor(BLACK) << FgColor(RED);
      rootFrame << "Fatal error: The hessian matrices D^2P_1(X) and D^2P_2(X) are not symmetric!\n\n";
   }
   IMatrix D2Q[2]; D2Q[0].clear(); D2Q[1].clear();

   bool status = true;
   for(i=0;i<2;i++)
   {
      for(j=0;j<2;j++)
      {
         for(c=0;c<2;c++)
         {
            for(k=0;k<2;k++)
            {
               D2Q[i][j][c] += power(-1,i+k) * DP2[i][k] * D2P1[k][j][c];
               for(ss=0;ss<2;ss++)
               {
                  D2Q[i][j][c] += power(-1,i+k+ss+1) * D2P2[i][k][ss] * DP1[ss][c]*DP1[k][j];
               }
            }
            if(!(D2Q[i][j][c].contains(0.))) status = false;
         }
      }
   }
   rootFrame << BgColor(WHITE) << FgColor(BLACK);
   rootFrame << "D^2Q_1(X) =\n" << D2Q[0][0][0] << " " << D2Q[0][0][1] << "\n";
   rootFrame << D2Q[0][1][0] << " " << D2Q[0][1][1] << "\n";
   rootFrame << "\nD^2Q_2(X) =\n" << D2Q[1][0][0] << " " << D2Q[1][0][1] << "\n";
   rootFrame << D2Q[1][1][0] << " " << D2Q[1][1][1] << "\n";
   if(status)
   {
      rootFrame << BgColor(BLACK) << FgColor(YELLOW);
      rootFrame << "OK: The hessian matrices D^2Q_1 and D^2Q_2 contain zero matrices!";
   }
   else{
      rootFrame << BgColor(BLACK) << FgColor(RED);
      rootFrame << "Fatal error: The hessian matrices D^2Q_1(X) or D^2Q_2(X) are nonzero!\n\n";
   }
   waitBt();
}

// -----------------------------------------------------------------

int main(int , char *[])
{
   initGraphics();
   try{
      C0Test();
      C1Test();
      C2Test();
   } catch(std::exception& e)
   {
      rootFrame << "\n" << e.what();
      waitBt();
   }

   closeGW();
   return 0;
}

/// @}
