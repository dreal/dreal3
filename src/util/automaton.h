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

#pragma once

#include <iostream>
#include <unordered_map>
#include <vector>

#include "api/OpenSMTContext.h"
#include "egraph/Enode.h"
#include "util/box.h"
#include "util/flow.h"

class Enode;
class OpenSMTContext;

namespace dreal {

class mode {
public:
    inline explicit mode(double d) : m_index(d) { m_flow = new flow; }
    inline ~mode() { delete m_flow; }
    inline double get_index() const { return m_index; }
    inline void add_invt(Enode * e) { m_invts.push_back(e); }
    inline void add_flow(Enode * x, Enode * f) { m_flow->add(x, f); }
    inline void add_guard(mode * m, Enode * e) { m_guards.emplace(m, e); }
    inline void add_reset(mode * m, Enode * e) { m_resets.emplace(m, e); }
    bool check_def();

private:
    const double m_index;
    std::vector<Enode *> m_invts;  // mode invariants
    flow * m_flow;
    std::unordered_map<mode *, Enode *> m_guards;  // guard conditions
    std::unordered_map<mode *, Enode *> m_resets;  // reset conditions
    std::vector<Enode *> m_x0;                     // initial states
    std::vector<Enode *> m_xt;                     // states after flow
    std::vector<Enode *> m_xp;                     // states after jump
};

class automaton {
public:
    explicit automaton(OpenSMTContext &);
    inline ~automaton() {}
    void add_mode(double, std::vector<Enode *> &, std::unordered_map<Enode *, Enode *> &,
                  std::unordered_map<double, Enode *> &, std::unordered_map<double, Enode *> &);
    void add_init(double, Enode *);
    void add_goal(double, Enode *);
    bool check_def();     // light type checking
    box sample(Enode *);  // Return a random point that satisfies the Enode
private:
    OpenSMTContext * m_ctx;
    std::vector<mode *> m_modes;
    std::unordered_map<mode *, Enode *> m_inits;  // assuming each mode only has one formula here
    std::unordered_map<mode *, Enode *> m_goals;
    mode * new_mode(double);
    mode * find_mode(double);  // returns mode of the index; create a new mode if not in table
};
}
