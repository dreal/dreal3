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
            "var:b, x, y;"
            "par:k1, k2, k3, k4;"
            "fun: k1*x*y + k2*x*y - k3*x*b - k4*b*y,"
            "- k2*x*y + k3*x*b,"
            "- k1*x*y +k4*b*y;";

        // set_param: k1 ==> [0,1]
        // set_param: k2 ==> [0,1]
        // set_param: k3 ==> [0,1]
        // set_param: k4 ==> [0,1]
        // X_0 : {[0,0],[0,0],[0.3,0.3],[0.7,0.7]}

        IMap vectorField(capd_str);
        IOdeSolver solver(vectorField, 60);
        ITimeMap timeMap(solver);
        // This is our initial condition
        IVector x(3);
        x[0] = 0;
        x[1] = 0.3;
        x[2] = 0.7;

        vectorField.setParameter("k1", interval(0, 1));
        vectorField.setParameter("k2", interval(0, 1));
        vectorField.setParameter("k3", interval(0, 1));
        vectorField.setParameter("k4", interval(0, 1));

        solver.setAbsoluteTolerance(1e-40);
        solver.setRelativeTolerance(1e-40);
        C0HOTripletonSet s(x);
        double T = 4.0;
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
