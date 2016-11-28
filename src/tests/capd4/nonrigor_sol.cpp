/////////////////////////////////////////////////////////////////////////////
//
/// @file encloseTrajectoryBetweenTimeSteps.cpp
///
/// @author Daniel Wilczak
//
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) CAPD group
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#include <iostream>

#include "capd/capdlib.h"

using namespace capd;
using namespace std;

int main() {
    cout.precision(17);
    // define an instance of class IMap that describes the vector field
    DMap pendulum(
        "var:lambda_0_0, p_0_0, t_0_0, theta_0_0, thetaI_0_0, w_0_0;par:fc_0_0, i_0_0, pe_0_0, "
        "tau_0_0;fun:(4*(((0.9*((((-0.366)+((0.08979*w_0_0)*p_0_0))+((((-0.0337)*w_0_0)*p_0_0)*p_0_"
        "0))+(((0.0001*w_0_0)*w_0_0)*p_0_0)))/(1*fc_0_0))+((-1)*lambda_0_0))), "
        "(0.41328*(((2*(((2.821+((-0.05231)*theta_0_0))+((0.10299*theta_0_0)*theta_0_0))+((((-0."
        "00063)*theta_0_0)*theta_0_0)*theta_0_0)))*((((p_0_0/1)+((-1)*(((p_0_0/"
        "1))^(2)))))^(0.5)))+((-1)*(0.9*((((-0.366)+((0.08979*w_0_0)*p_0_0))+((((-0.0337)*w_0_0)*p_"
        "0_0)*p_0_0))+(((0.0001*w_0_0)*w_0_0)*p_0_0)))))), 1, (10*(thetaI_0_0+((-1)*theta_0_0))), "
        "(100.000000000000000000000000000000*cos((10*t_0_0))), "
        "(50.000000000000000000000000000000*cos((10*t_0_0)));");
    pendulum.setParameter("fc_0_0", 0.6537);
    pendulum.setParameter("i_0_0", 0);
    pendulum.setParameter("pe_0_0", 0);
    pendulum.setParameter("tau_0_0", 0);
    int order = 20;
    DOdeSolver solver(pendulum, order);
    DTimeMap timeMap(solver);
    // specify initial condition
    DVector u(6);
    u[0] = 14.7;
    u[1] = 0.9833;
    u[2] = 0.0;
    u[3] = 8.8;
    u[4] = 80;
    u[5] = 110;
    double initTime = 0;
    double finalTime = 10;
    // define functional object
    cerr << "before solution";
    DTimeMap::SolutionCurve solution(initTime);
    cerr << "after solution";
    // and integrate
    timeMap(finalTime, u, solution);
    cerr << "after integrate";
    // then you can ask for any intermediate point on the trajectory
    cout << "domain = [" << solution.getLeftDomain() << "," << solution.getRightDomain() << "]\n";
    cout << "solution(0.5) =" << solution(0.5) << endl;
    cout << "solution(4) =" << solution(4) << endl;
    cout << "solution(5) = " << solution(5) << endl;
    cout << "solution(8) =" << solution(8) << endl;
    cout << "solution(10)=" << solution(10) << endl;
    return 0;
}

// #include <cstdio>
// #include "capd/capdlib.h"
// using namespace capd;
// int main(){
//   // define an instance of class DMap that describes the vector field
//   DMap pendulum("time:t;par:omega;var:x,dx;fun:dx,sin(omega*t)-sin(x);");
//   pendulum.setParameter("omega",1.);
//   int order = 30;
//   DOdeSolver solver(pendulum,order);
//   DTimeMap timeMap(solver);
//   // specify initial condition
//   DVector u(2);
//   u[0] = 1.;
//   u[1] = 2.;
//   double initTime = 4;
//   double finalTime = 8;
//   // use Taylor method with step control to integrate
//   timeMap.stopAfterStep(true);
//   do{
//     u = timeMap(finalTime,u,initTime);
//     printf("t=%6f, x=%6f, dx=%6f\n",initTime,u[0],u[1]);
//   }while(!timeMap.completed());
//   return 0;
// }
// /* output:
// t=4.343750, x=1.584065, dx=1.379298
// t=4.718750, x=1.964273, dx=0.649367
// t=5.171875, x=2.065724, dx=-0.190317
// t=5.703125, x=1.723517, dx=-1.077336
// t=6.125000, x=1.143133, dx=-1.641492
// t=6.500000, x=0.469677, dx=-1.898192
// t=6.875000, x=-0.234645, dx=-1.793385
// t=7.234375, x=-0.809953, dx=-1.363382
// t=7.609375, x=-1.202215, dx=-0.706059
// t=8.000000, x=-1.329739, dx=0.056758
// */
