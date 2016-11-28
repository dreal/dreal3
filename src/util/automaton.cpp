/*********************************************************************
Author: Sicun Gao <sicung@mit.edu>

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

#include "util/automaton.h"

#include <assert.h>
#include <iostream>
#include <unordered_map>
#include <utility>
#include <vector>

class Enode;
class OpenSMTContext;

using std::cerr;
using std::endl;
using std::vector;
using std::unordered_map;
using std::ostream;

namespace dreal {

automaton::automaton(OpenSMTContext & c) : m_ctx(&c) { assert(m_ctx); }

mode * automaton::new_mode(double ind) {
    mode * m = new mode(ind);
    m_modes.push_back(m);
    return m;
}

void automaton::add_mode(double ind, vector<Enode *> & invts,
                         unordered_map<Enode *, Enode *> & flows,
                         unordered_map<double, Enode *> & guards,
                         unordered_map<double, Enode *> & resets) {
    mode * m = find_mode(ind);

    // need to copy the Enodes because the maps are temporary holders
    for (auto inv : invts) {
        m->add_invt(inv);
    }
    for (auto flow : flows) {
        m->add_flow(flow.first, flow.second);
    }
    for (auto guard : guards) {
        m->add_guard(find_mode(guard.first), guard.second);
    }
    for (auto reset : resets) {
        m->add_reset(find_mode(reset.first), reset.second);
    }
}

mode * automaton::find_mode(double ind) {
    for (auto m : m_modes) {
        if (m->get_index() == ind) return m;
    }
    return new_mode(ind);
}

void automaton::add_init(double ind, Enode * e) { m_inits.emplace(find_mode(ind), e); }

void automaton::add_goal(double ind, Enode * e) { m_goals.emplace(find_mode(ind), e); }
}
