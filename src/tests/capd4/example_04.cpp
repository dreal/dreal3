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
#include <string>

#include "capd/capdlib.h"

using namespace capd;
using namespace std;

int main() {
    try {
        cout.precision(12);

        string capd_str =
            "var:x_0, P_0;"
            "fun:1.0,"
            "(1.0/(6.283185307180000123139507195447^(0.5))*exp(((-1)*(x_0^2))/2));";

        IMap vectorField(capd_str);

        IOdeSolver solver(vectorField, 20);

        ITimeMap timeMap(solver);
        // This is our initial condition
        IVector x(2);

        // {[-20,-20],[0,0]
        x[0] = -20;
        x[1] = 0;

        // define a doubleton representation of the interval vector x
        C0Rect2Set s(x);

        // Here we start to integrate. The time of integration is set to T=5.

        double T = 40;
        timeMap.stopAfterStep(true);
        interval prevTime(0.);
        cout << "Initial: " << x;
        do {
            // solver.setStep(0.001);
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
