/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>
        Sicun Gao <sicung@cs.cmu.edu>
        Edmund Clarke <emc@cs.cmu.edu>

dReal -- Copyright (C) 2013 - 2014, Soonho Kong, Sicun Gao, and Edmund Clarke

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

#include <unordered_map>
#include "opensmt/egraph/Enode.h"
#include "util/interval.h"
#include "util/var.h"
#include "util/box.h"
#include "util/contractor.h"

namespace dreal {

char const * contractor_exception::what() const throw() {
    return "Contractor Exception";
}

box contractor::prune(box b) const {
    return m_ptr->prune(b);
};

contractor_seq::contractor_seq(std::initializer_list<contractor> l) : m_vec(l) { }
box contractor_seq::prune(box b) const {
    for(contractor const & c : m_vec) {
        b = c.prune(b);
    }
    return b;
}

contractor_or::contractor_or(contractor const & c1, contractor const & c2)
    : m_c1(c1), m_c2(c2) { }
box contractor_or::prune(box b) const {
    try {
        return m_c1.prune(b);
    } catch (contractor_exception & e) {
        return m_c2.prune(b);
    }
}

contractor_ite::contractor_ite(std::function<bool(box const &)> guard, contractor const & c_then, contractor const & c_else)
    : m_guard(guard), m_c_then(c_then), m_c_else(c_else) { }
box contractor_ite::prune(box b) const {
    if (m_guard(b)) {
        return m_c_then.prune(b);
    } else {
        return m_c_else.prune(b);
    }
}

contractor_while::contractor_while(std::function<bool(box const &, box const &)> guard, contractor const & c)
    : m_guard(guard), m_c(c) { }
box contractor_while::prune(box b) const {
    box new_b = m_c.prune(b);
    if (m_guard(b, new_b)) {
        return prune(new_b);
    } else {
        return new_b;
    }
}
}
