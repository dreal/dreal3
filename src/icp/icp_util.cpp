/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>
        Sicun Gao <sicung@mit.edu>

dReal -- Copyright (C) 2013 - 2016, the dReal Team

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

#include "icp/icp_util.h"

#include <stdlib.h>
#include <iostream>
#include <memory>

#include "contractor/contractor.h"
#include "contractor/contractor_exception.h"
#include "smtsolvers/SMTConfig.h"
#include "util/box.h"

namespace dreal {
class contractor_status;
}  // namespace dreal

using std::cout;
using std::endl;
using std::ofstream;

namespace dreal {
void output_solution(box const & b, SMTConfig & config, unsigned i) {
    if (i > 0) {
        cout << i << "-th ";
    }
    cout << "Solution:" << endl;
    cout << b << endl;
    if (config.nra_model && !config.nra_model_out.is_open()) {
        config.nra_model_out.open(config.nra_model_out_name.c_str(),
                                  ofstream::out | ofstream::trunc);
        if (config.nra_model_out.fail()) {
            cout << "Cannot create a file: " << config.nra_model_out_name << endl;
            exit(1);
        }
    }
    display(config.nra_model_out, b, false, true);
}

void prune(contractor & ctc, contractor_status & s) {
    try {
        ctc.prune(s);
    } catch (contractor_exception & e) {
        // Do nothing
    }
}
}  // namespace dreal
