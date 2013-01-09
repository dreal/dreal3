/////////////////////////////////////////////////////////////////////////////
//
/// @file encloseMonodromyMatrixBetweenTimeSteps.cpp
///
/// @author Daniel Wilczak
//
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) CAPD group
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.


#include "capd/capdlib.h"

using namespace capd;
using namespace std;

int main()
{
  try{
    cout.precision(12);
    // This is the vector field for the Planar Restricted Circular 3 Body Problem
    IMap vectorField("par:mu,mj;var:x,y,dx,dy;fun:dx,dy,x-mj*(x+mu)*sqrt((x+mu)^2+y^2)^(-3)-mu*(x-mj)*sqrt((x-mj)^2+y^2)^(-3)+2*dy,y*(1-mj*sqrt((x+mu)^2+y^2)^(-3)-mu*sqrt((x-mj)^2+y^2)^(-3))-2*dx;");

    // mass ratio
    interval mu=interval(123.0)/interval(10000.0);
    interval mj=1.0-mu;

    // set parameter values
    vectorField.setParameter("mu",mu);
    vectorField.setParameter("mj",mj);

    // The solver uses high order enclosure method to verify the existence of the solution. 
    // The order will be set to 20.
    // The time step (when step control is turned off) will be 0.1.
    // The time step control is turned on by default but the solver must know if we want to 
    // integrate forwards or backwards (then put negative number).
    ITaylor solver(vectorField,20,.1);

    ITimeMap timeMap(solver);
    // This is our initial condition
    IVector x(4);
    x[0]=0.9928634178;
    x[1]=0.0;
    x[2]=0.0;
    x[3]=2.129213043;

    // Define a doubleton representation of the interval vector x
    // and the derivative wrt initial condition.
    IEuclLNorm N;
    C1Rect2Set s(x,N);

    // Here we start to integrate. The time of integration is set to T=3. 
    double T=3;
    timeMap.stopAfterStep(true);
    interval prevTime(0.);
    IMatrix prevMatrix = IMatrix::Identity(4);
    do 
    {
      timeMap(T,s);
      interval stepMade = solver.getStep();
      cout << "\nstep made: " << stepMade;

      // This is how we can extract an information 
      // about the trajectory between time steps.
      // The type CurveType is a function defined
      // on the interval [0,stepMade].
      // It can be evaluated at a point (or interval).
      // The curve can be also differentiated wrt to time.
      // We can also extract from it the 1-st order derivatives wrt.
      const ITaylor::CurveType& curve = solver.getCurve();
      interval domain = interval(0,1)*stepMade;
   
      // Here we use a uniform grid of last time step made
      // to enclose the trajectory between time steps.
      // You can use your own favourite subdivision, perhaps nonuniform,
      // depending on the problem you want to solve.
      int grid=10;
      for(int i=0;i<grid;++i)
      {
        interval subsetOfDomain = interval(i,i+1)*stepMade/grid;
        // The above interval does not need to be a subset of domain.
        // This is due to rounding to floating point numbers.
        // We take the intersection with the domain.
        intersection(domain,subsetOfDomain,subsetOfDomain);

        // Here we evaluated curve at the interval subsetOfDomain.
        // v will contain rigorous bound for the trajectory for this time interval.
        IVector v = curve(subsetOfDomain);
        std::cout << "\nenclosure for t=" << prevTime + subsetOfDomain << ":  " << v;      
        std::cout << "\ndiam(enclosure): " << diam(v);

        // Here we evaluated derivative wrt x of the curve at the interval subsetOfDomain.
        // M will contain rigorous bound for the monodromy matrix when integrate with with initial conditions 
        // x = x(prevTime) and d/dx x(prevTime) = Id.
        // To obtain d/dx x(0) with multiply M by d/dx(prevTime).
        
        IMatrix M = curve[subsetOfDomain]*prevMatrix;
        std::cout << "\nenclosure of monodromy matrix for t=" << prevTime + subsetOfDomain << ":  " << M;
        std::cout << "\ndiam(enclosure of monodromy matrix): " << diam(M);
      }
      prevTime = timeMap.getCurrentTime();
      cout << "\ncurrent time: " << prevTime << endl << endl;
      
      // here we update prev matrix
      prevMatrix = IMatrix(s);

    }while(!timeMap.completed());
  }catch(exception& e)
  {
    cout << "\n\nException caught!\n" << e.what() << endl << endl;
  }
}  // END
