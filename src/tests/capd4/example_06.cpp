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
            "var:x, v;"
            "fun:v,"
            "-9.8 + (- 0.45 * v ^ 1);";
        IMap vectorField(capd_str);
        IOdeSolver solver(vectorField, 20);
        ITimeMap timeMap(solver);
        // This is our initial condition
        IVector x(2);
        x[0] = 10;  // x0 = 10
        x[1] = 0;   // v0 = 0
        C0Rect2Set s(x);
        double T = 1.0;
        timeMap.stopAfterStep(true);
        interval prevTime(0.);
        cout << "Initial: " << x << endl << endl;
        do {
            timeMap(T, s);
            interval stepMade = solver.getStep();
            cout << "step made: " << stepMade << endl;
            const IOdeSolver::SolutionCurve & curve = solver.getCurve();
            interval domain = interval(0, 1) * stepMade;
            int grid = 16;
            for (int i = 0; i < grid; ++i) {
                interval subsetOfDomain = interval(i, i + 1) * stepMade / grid;
                cerr << "before subsetOfDomain : " << subsetOfDomain << endl;
                intersection(domain, subsetOfDomain, subsetOfDomain);
                cerr << "after subsetOfDomain  : " << subsetOfDomain << endl;
                IVector v =
                    curve(Interval(subsetOfDomain.rightBound(), subsetOfDomain.rightBound()));
                cout << "enclosure for t=" << prevTime + subsetOfDomain << ":  " << v << endl;
                cout << "diam(enclosure): " << diam(v) << endl;
            }
            prevTime = timeMap.getCurrentTime();
            cout << "current time: " << prevTime << endl << "==============" << endl << endl;
        } while (!timeMap.completed());
    } catch (exception & e) {
        cout << "Exception caught! - " << e.what() << endl;
    }
}
