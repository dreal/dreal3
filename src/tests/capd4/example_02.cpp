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

#include <exception>
#include <iostream>

#include "capd/capdlib.h"

using namespace capd;
using namespace std;

int main() {
    try {
        cout.precision(12);

        IMap vectorField(
            "var:z_2_0, y_2_0, x_2_0, tau_2_0, omega2_2_0, "
            "omega1_2_0;fun:-((((-0.800000)*sin(((omega2_2_0+2.000000)*tau_2_0)))*cos(omega1_2_0))*"
            "2.000000), "
            "-((((-1.200000)*sin(((omega1_2_0+1.000000)*tau_2_0)))*sin(omega2_2_0))*2.000000), "
            "-((-1.000000)*sin((3.140000*tau_2_0))), -1.000000, -(0.000000+((-1)*omega2_2_0)), "
            "-(0.000000+((-1)*(0.500000*omega1_2_0)));");

        IOdeSolver solver(vectorField, 20);

        ITimeMap timeMap(solver);
        // This is our initial condition
        IVector x(6);
        x[0] = Interval(-1.45631, -0.698834);
        x[1] = Interval(-1.13174, -1.12578);
        x[2] = Interval(-0.298225, -0.138388);
        x[3] = 4;
        x[4] = Interval(-6.16636e-06, -2.25737e-06);
        x[5] = Interval(2.50198e-05, 6.83455e-05);

        // define a doubleton representation of the interval vector x
        C0Rect2Set s(x);

        // Here we start to integrate. The time of integration is set to T=5.

        double T = 4;
        timeMap.stopAfterStep(true);
        interval prevTime(0.);
        cout << "Initial: " << x;
        do {
            timeMap(T, s);
            interval stepMade = solver.getStep();
            cout << "\nstep made: " << stepMade;

            // This is how we can extract an information
            // about the trajectory between time steps.
            // The type CurveType is a function defined
            // on the interval [0,stepMade].
            // It can be evaluated at a point (or interval).
            // The curve can be also differentiated wrt to time.
            // We can also extract from it the 1-st order derivatives wrt.
            const IOdeSolver::SolutionCurve & curve = solver.getCurve();
            interval domain = interval(0, 1) * stepMade;

            // Here we use a uniform grid of last time step made
            // to enclose the trajectory between time steps.
            // You can use your own favorite subdivision, perhaps nonuniform,
            // depending on the problem you want to solve.
            int grid = 2;
            for (int i = 0; i < grid; ++i) {
                interval subsetOfDomain = interval(i, i + 1) * stepMade / grid;
                // The above interval does not need to be a subset of domain.
                // This is due to rounding to floating point numbers.
                // We take the intersection with the domain.
                intersection(domain, subsetOfDomain, subsetOfDomain);

                // Here we evaluated curve at the interval subsetOfDomain.
                // v will contain rigorous bound for the trajectory for this time interval.
                IVector v = curve(subsetOfDomain);
                std::cout << "\nenclosure for t=" << prevTime + subsetOfDomain << ":  " << v;
                std::cout << "\ndiam(enclosure): " << diam(v);
            }
            prevTime = timeMap.getCurrentTime();
            cout << "\ncurrent time: " << prevTime << endl << endl;
        } while (!timeMap.completed());
    } catch (exception & e) {
        cout << "\n\nException caught!\n" << e.what() << endl << endl;
    }
}  // END
