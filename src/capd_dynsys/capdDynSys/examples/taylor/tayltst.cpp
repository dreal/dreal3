/// @addtogroup taylor
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file tayltst.cpp
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#include <cmath>
#include <stdexcept>
#include <fstream>

#include "capd/krak/krak.h"
#include "capd/capdlib.h"

using namespace capd;

const int DIMENSION = 3;

double minx=-2.6;
double maxx=2.6;
double miny=-2.6;
double maxy=2.6;

Frame fr, txt;

void axes(Frame &fr)
{
   fr.line(0.0,miny,0.0,maxy,BLACK);
   fr.line(minx,0.0,maxx,0.0,BLACK);
}

// -------------------------------------------------------------------------

void initGraph(double step, int order)
{
   openGW(860,600,WHITE,BLACK);
   fr = Frame(5,115,345,455,WHITE,BLACK);
   txt = Frame(0,460,860,580,WHITE,BLACK);
   fr.setWorldCoord(minx,miny,maxx,maxy);
   rootFrame.Clear();
   axes(fr);
   rootFrame << "Test of set arithemtic using class \n\"Map\"and \"Taylor\".\n";
   rootFrame << "Evaluation of the set and its projection\n";
   rootFrame << "onto plane y\"=0.\n\n";
   rootFrame << "ODE: Kura-Siva\n";
   rootFrame << "time step: " << step << ",  order: " << order << "\n";
}

// -------------------------------------------------------------------------

void computeRigorousTrajectory(C0Set &S, IC2Taylor &T, int color, frstring description)
{
   int length=static_cast<int>( (8./T.getStep().rightBound()));

   txt.SetFgColor(color);
   txt << "interval test: " << description;

   int i;
   for(i=0;i<length;i++)
   {
      IVector w = IVector(S);
      fr.boxFill(w[0].leftBound(),w[1].leftBound(),w[0].rightBound(),w[1].rightBound(),color);
      fr.box(w[0].leftBound(),w[1].leftBound(),w[0].rightBound(),w[1].rightBound());
      S.move(T);
   }
   IVector w(S);
   txt.SetFgColor(BLACK);
   txt << ", diam:" << diam(w) << "\n"; 
}

// -------------------------------------------------------------------------

void computeNonrigorousTrajectory(const DVector &center, double sizeOfSet, int grid)
{
   DMap f = "var:x,y,z;fun:y,z,1-y-0.5*x*x;";
   DTaylor T(f,20,0.1);
   int length= static_cast<int>( (8./T.getStep()));

   txt.SetFgColor(BLUE);
   txt << "vector test: nonrigorous trajectory";
   int i,j;
   DVector left = center + DVector(0.,-sizeOfSet,0.);
   double step = 2*sizeOfSet/(double)grid;

   for(j=0;j<=grid;j++)
   {
      DVector P = left + DVector(0.,j*step,0.);
      for(i=0;i<length;i++)
      {
         fr.dot(P[0],P[1],BLUE);
         P = T(P);
      }
   }
}

// -------------------------------------------------------------------------

void C012Tests()
{
   rootFrame.Clear();
   rootFrame.precision(10);
   rootFrame << BgColor(BLACK) << FgColor(GREEN);
   rootFrame << "C^0 - Test\n";
   rootFrame << "The Kuramoto-Sivashinsky equation satisfies condition Q(t,X):=S(phi(t,S(phi(t,X))))= X\n";
   rootFrame << "wherever the left side is well defined. Take";

   interval step = 0.01;
   int order = 4;
   IC2Map f = "var:x,y,z;fun:y,z,1-y-0.5*x*x;";
   IC2Taylor DS(f,order,step);
// C^0 - test
   IVector X(interval(0.1),interval(1.5259617305037),interval(0.2));
   C2Rect2Set S1(X,IEuclLNorm());
   int i,j,c,k,ss, numberOfSteps = 300;
   for(i=0;i<numberOfSteps;i++)
      S1.move(DS);

   IVector FX(S1);
   rootFrame << BgColor(WHITE) << FgColor(BLACK);
   rootFrame << "\n                    X=" << X << ", t=" << numberOfSteps*step;
   rootFrame << "\n             phi(t,X)=" << FX;
   FX[0] = -FX[0];
   FX[2] = -FX[2];
   rootFrame << "\n          S(phi(t,X))=" << FX;
   C2Rect2Set S2(FX,IEuclLNorm());
   for(i=0;i<numberOfSteps;i++)
      S2.move(DS);
   FX = IVector(S2);
   rootFrame << "\n   phi(t,S(phi(t,X)))=" << FX;
   FX[0] = -FX[0];
   FX[2] = -FX[2];
   rootFrame << "\nS(phi(t,S(phi(t,X))))=" << FX;
   if(X[0].subset(FX[0]) && X[1].subset(FX[1]) && X[2].subset(FX[2]))
   {
      rootFrame << BgColor(BLACK) << FgColor(YELLOW);
      rootFrame << "\nOK: X is a subset of Q(t,X)!";
   }
   else
   {
      rootFrame << BgColor(BLACK) << FgColor(RED);
      rootFrame << "\nFatal error: X is not a subset of Q(t,X)!";
   }
// C^1 - test
   rootFrame << BgColor(WHITE) << FgColor(BLACK);
   rootFrame << "\n\n-------------------------------------\n\n";
   rootFrame << BgColor(BLACK) << FgColor(GREEN);
   rootFrame << "C^1 - Test\n";
   rootFrame << BgColor(WHITE) << FgColor(BLACK);
   IMatrix DP1 = IMatrix(S1);
   IMatrix DP2 = IMatrix(S2);
   IMatrix DQ; DQ.clear();

   bool ok = true;
   for(i=0;i<DIMENSION;i++)
      for(j=0;j<DIMENSION;j++)
      {
         for(k=0;k<DIMENSION;k++)
         {
            DQ[i][j]  += power(-1,k+1) * DP2[i][k] * DP1[k][j] ;
         }
         DQ[i][j] *= power(-1,i+1);
         if(i==j && !(DQ[i][j]).contains(1.)) ok = false;
         if(i!=j && !(DQ[i][j]).contains(0.)) ok = false;
      }
   rootFrame << DQ[0] << "\n";
   rootFrame << DQ[1] << "\n";
   rootFrame << DQ[2] << "\n";
   if(ok)
   {
      rootFrame << BgColor(BLACK) << FgColor(YELLOW);
      rootFrame << "OK: DQ(t,X) contains the Identity matrix!";
   }
   else
   {
      rootFrame << BgColor(BLACK) << FgColor(RED);
      rootFrame << "Fatal error: DQ(t,X) do not contain the Identity matrix!";
   }

// C^2 - test
   rootFrame << BgColor(WHITE) << FgColor(BLACK);
   rootFrame << "\n\n-------------------------------------\n\n";
   rootFrame << BgColor(BLACK) << FgColor(GREEN);
   rootFrame << "C^2 - Test";
   rootFrame << BgColor(WHITE) << FgColor(BLACK);

   IMatrix D2Q[3];
   D2Q[0].clear(); D2Q[1].clear(); D2Q[2].clear();
   ok = true;
   for(i=0;i<DIMENSION;i++)
   {
      rootFrame << "\n";
      for(j=0;j<DIMENSION;j++)
      {
         for(c=0;c<DIMENSION;c++)
           {
            for(k=0;k<DIMENSION;k++)
            {
               D2Q[i][j][c] += power(-1,i+k) * DP2[i][k] * S1(k,j,c);
               for(ss=0;ss<DIMENSION;ss++)
               {
                  D2Q[i][j][c] += power(-1,i+k+ss+1) * S2(i,k,ss) * DP1[ss][c]*DP1[k][j];
               }
            }
            if(!D2Q[i][j][c].contains(0.)) ok = false;
         }
         rootFrame << D2Q[i][j] << "\n";
      }
   }

   if(ok)
   {
      rootFrame << BgColor(BLACK) << FgColor(YELLOW);
      rootFrame << "OK: The hessian matrices D^2Q(t,X) contain the zero matrix!";
   }
   else
   {
      rootFrame << BgColor(BLACK) << FgColor(RED);
      rootFrame << "Fatal error: The hessian matrices D^2Q(t,X) do not contain the zero matrix!";
   }
}

// -------------------------------------------------------------------------

int main(int, char *[])
{
   double step=0.1;
   int order = 8;
   initGraph(step,order);
   //init_fpunit();

   try
   {
      DVector z(0.,1.563,0.);
      IVector v(0.,1.563,0.);
      double sizeOfSet = 0.005;

      interval iv(-sizeOfSet,sizeOfSet);
      IVector r(0.,iv,0.);

      C0RectSet rect(v,r);
      C0Rect2Set rect2(v,r);
      Intv2Set intv2(v,r);

      IC2Map f="par:c;var:x,y,z;fun:y,z,c^2-y-0.5*x*x;";
      IC2Taylor T(f,order,step);
      f.setParameter("c",interval(1.0));

      computeRigorousTrajectory(intv2,T,RED,"intv2Set");
      computeRigorousTrajectory(rect,T,MAGENTA,"rectSet");
      computeRigorousTrajectory(rect2,T,GREEN,"rect2Set");
      computeNonrigorousTrajectory(z,sizeOfSet,4);
      waitBt();

      C012Tests();
      waitBt();
   }catch(std::exception& e)
   {

      std::ofstream fileStream;
      fileStream.open("report");
      fileStream << e.what();
      fileStream.close();

      rootFrame << "\n\nException caught! See 'report' file for details.";
      waitBt();
   }
   closeGW();
   return 0;
}


/// @}
