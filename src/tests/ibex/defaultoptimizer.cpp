/* ============================================================================
 * I B E X
 * ============================================================================
 * License     : This program can be distributed under the terms of the GNU LGPL.
 *               See the file COPYING.LESSER.
 *
 * Author(s)   : IBEX Team
 * Copyright 2015 IBEX Team
 * ---------------------------------------------------------------------------- */

#include <iostream>
#include <sstream>
#include "ibex/ibex.h"

using std::stringstream;
using std::cout;
using std::endl;

double convert(const char* argname, const char* arg) {
    char* endptr;
    double val = strtod(arg, &endptr);
    if (endptr != arg+strlen(arg)*sizeof(char)) {
        stringstream s;
        s << "\"" << argname << "\" must be a real number";
        ibex::ibex_error(s.str().c_str());
    }
    return val;
}

int main(int argc, char** argv) {
    try {
        // check the number of arguments
        if (argc < 5) {
            ibex::ibex_error("usage: defaultoptimizer filename prec goal_prec timelimit");
        }

        // Load a system of equations
        ibex::System sys(argv[1]);

        cout << "load file " << argv[1] << "." << endl;

        double prec       = convert("prec", argv[2]);
        double goal_prec  = convert("goal_prec", argv[3]);  // the required precision for the objective
        double time_limit = convert("timelimit", argv[4]);

        if (!sys.goal) {
            ibex::ibex_error(" input file has not goal (it is not an optimization problem).");
        }

        // Build the default optimizer
        ibex::DefaultOptimizer o(sys, prec, goal_prec);

        // This option limits the search time
        o.timeout = time_limit;

        // This option prints each better feasible point when it is found
        o.trace = 0;

        // display solutions with up to 12 decimals
        cout.precision(12);

        // Search for the optimum
        o.optimize(sys.box);

        // Report some information (computation time, etc.)
        o.report();

        return 0;
    }
    catch(ibex::SyntaxError& e) {
        cout << e << endl;
    }
}
