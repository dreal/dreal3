/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>
        Sicun Gao <sicung@cs.cmu.edu>


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

#include "util/proof.h"

#include "contractor/contractor_status.h"
#include "smtsolvers/SMTConfig.h"
#include "util/box.h"

using std::endl;

namespace dreal {
using std::string;
void output_pruning_step(box const & old_box, contractor_status & cs,
                         std::string const & constraint) {
    std::ostream & out = cs.m_config.nra_proof_out;
    box const & new_box = cs.m_box;
    bool const readable_proof = cs.m_config.nra_readable_proof;
    if (old_box != new_box) {
        out << "[before pruning]" << endl;
        dreal::display(out, old_box, !readable_proof);
        if (new_box.is_empty()) {
            out << "[conflict detected]";
        } else {
            out << "[after pruning]";
        }
        if (constraint.length() > 0) {
            out << " by " << constraint;
        }
        out << endl;
        if (!new_box.is_empty()) {
            dreal::display(out, new_box, !readable_proof);
        }
    }
}
}  // namespace dreal
