/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>

dReal -- Copyright (C) 2013 - 2015, Soonho Kong, Sicun Gao, and Edmund Clarke

dReal is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

dReal is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with dReal. If not, see <http://www.gnu.org/licenses/>.
*********************************************************************/

#include <nlopt.hpp>
#include <iostream>
#include <vector>

using std::vector;
using std::cout;
using std::cerr;
using std::endl;

double obj(unsigned, const double* x, double*, void*) {
    double const ret = sin(x[0]) * cos(x[1]);
    cerr << "sin(" << x[0] << ")" << " * "
         << "cos(" << x[1] << ") = "
         << ret << endl;
    return ret;
}

int main() {
    nlopt::opt opt(nlopt::LN_COBYLA, 2);

    // lower bound
    //    0 <= x[0]
    //    0 <= x[1]
    vector<double> lb(2);
    lb[0] = 0; lb[1] = 0;
    opt.set_lower_bounds(lb);

    // upper bound
    //    x[0] <= 10
    //    x[1] <= 10
    vector<double> ub(2);
    ub[0] = 10; ub[1] = 10;
    opt.set_upper_bounds(ub);

    // set objective function
    opt.set_min_objective(obj, nullptr);

    // set tollerance
    opt.set_xtol_abs(0.0001);

    // set initial point
    //    init[0] = 5.0
    //    init[1] = 5.0
    vector<double> init;
    init.push_back(5.0);
    init.push_back(5.0);

    // Call optimization
    vector<double> output = opt.optimize(init);

    // Print result
    cout << "output: x0 = " << output[0] << endl;
    cout << "output: x1 = " << output[1] << endl;
    return 0;
}
