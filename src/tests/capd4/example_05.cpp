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

#include <string>
#include <iostream>
#include "capd/capdlib.h"

using namespace capd;
using namespace std;

int main() {
    try {
        cout.precision(12);

        string capd_str = "var:x1_2_0, x2_2_0, tau_2_0;"
            "fun:-(5+((-1)*((0.5*(19.613299999999998846078597125597^(0.5)))*(x1_2_0^(0.5)))))/2,"
            "-((0.5*(19.613299999999998846078597125597^(0.5)))*((x1_2_0^(0.5))+((-1)*(x2_2_0^(0.5)))))/4,"
            "-1;";

        IMap vectorField(capd_str);

        IOdeSolver solver(vectorField, 20);

        ITimeMap timeMap(solver);
        // This is our initial condition
        IVector x(3);

        // X_0 : {[2.67942,5],[5.16944,9.89842],[0,0]}

        // X_t : {[3.10689,5],[4.65776,5],[1,1]}
        x[0] = Interval(3.10689, 5);
        x[1] = Interval(4.65776, 5);
        x[2] = 1.0;

        // define a doubleton representation of the interval vector x
        C0Rect2Set s(x);

        // T   : [0.980469,1]
        double T = 1.0;
        timeMap.stopAfterStep(true);
        interval prevTime(0.);
        cout << "Initial: " << x << endl << endl;
        do {
            // solver.setStep(0.001);
            timeMap(T, s);
            interval stepMade = solver.getStep();
            cout << "step made: " << stepMade << endl;

            // This is how we can extract an information
            // about the trajectory between time steps.
            // The type CurveType is a function defined
            // on the interval [0,stepMade].
            // It can be evaluated at a point (or interval).
            // The curve can be also differentiated wrt to time.
            // We can also extract from it the 1-st order derivatives wrt.
            const IOdeSolver::SolutionCurve& curve = solver.getCurve();
            interval domain = interval(0, 1) * stepMade;

            // Here we use a uniform grid of last time step made
            // to enclose the trajectory between time steps.
            // You can use your own favorite subdivision, perhaps nonuniform,
            // depending on the problem you want to solve.
            int grid = 1024;
            for (int i = 0; i < grid; ++i) {
                interval subsetOfDomain = interval(i, i + 1) * stepMade / grid;
                // The above interval does not need to be a subset of domain.
                // This is due to rounding to floating point numbers.
                // We take the intersection with the domain.
                cerr << "before subsetOfDomain : " << subsetOfDomain << endl;
                intersection(domain, subsetOfDomain, subsetOfDomain);
                cerr << "after subsetOfDomain  : " << subsetOfDomain << endl;

                // Here we evaluated curve at the interval subsetOfDomain.
                // v will contain rigorous bound for the trajectory for this time interval.
                IVector v = curve(Interval(subsetOfDomain.rightBound(), subsetOfDomain.rightBound()));
                cout << "enclosure for t=" << prevTime + subsetOfDomain << ":  " << v << endl;;
                cout << "diam(enclosure): " << diam(v) << endl;
            }
            prevTime = timeMap.getCurrentTime();
            cout << "current time: " << prevTime << endl
                 << "==============" << endl << endl;
        } while (!timeMap.completed());
    } catch(exception& e) {
        cout << "Exception caught! - " << e.what() << endl;
    }
}  // END
