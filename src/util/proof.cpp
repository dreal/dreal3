/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>
        Sicun Gao <sicung@cs.cmu.edu>
        Edmund Clarke <emc@cs.cmu.edu>

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

#include "util/proof.h"

namespace dreal {
void proof_write_pruning_step(ostream & out, box const & old_box, box const & new_box, bool const readable_proof) {
    if (old_box != new_box) {
        out << "[before pruning] " << endl;
        dreal::display(out, old_box, !readable_proof);
        if (new_box.is_empty()) {
            out << "[conflict detected] " << endl;
        } else {
            out << "[after pruning] " << endl;
            dreal::display(out, new_box, !readable_proof);
        }
    }
}
}  // namespace dreal
