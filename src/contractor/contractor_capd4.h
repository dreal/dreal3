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

#pragma once
#include <unordered_map>
#include <vector>
#include <initializer_list>
#include <stdexcept>
#include <string>
#include <memory>
#include <utility>
#include "opensmt/egraph/Enode.h"
#include "util/box.h"
#include "json/json.hpp"
#include "capd/capdlib.h"
#include "contractor/contractor_basic.h"

namespace dreal {
class contractor_capd_fwd_simple : public contractor_cell {
private:
    ode_constraint const * const m_ctr;

public:
    contractor_capd_fwd_simple(box const & box, ode_constraint const * const ctr);
    box prune(box b, SMTConfig & config) const;
    std::ostream & display(std::ostream & out) const;
};

class contractor_capd_fwd_full : public contractor_cell {
private:
    ode_constraint const * const m_ctr;
    unsigned const m_taylor_order;
    unsigned const m_grid_size;

    capd::IMap * m_vectorField = nullptr;
    capd::IOdeSolver * m_solver = nullptr;
    capd::ITimeMap * m_timeMap = nullptr;
    bool inner_loop(capd::IOdeSolver & solver, capd::interval const & prevTime, capd::interval const T, std::vector<std::pair<capd::interval, capd::IVector>> & enclosures) const;

public:
    contractor_capd_fwd_full(box const & box, ode_constraint const * const ctr, unsigned const taylor_order, unsigned const grid_size);
    ~contractor_capd_fwd_full();
    box prune(box b, SMTConfig & config) const;
    nlohmann::json generate_trace(box b, SMTConfig & config) const;
    std::ostream & display(std::ostream & out) const;
};

class contractor_capd_bwd_simple : public contractor_cell {
private:
    ode_constraint const * const m_ctr;

public:
    contractor_capd_bwd_simple(box const & box, ode_constraint const * const ctr);
    box prune(box b, SMTConfig & config) const;
    std::ostream & display(std::ostream & out) const;
};

class contractor_capd_bwd_full : public contractor_cell {
private:
    ode_constraint const * const m_ctr;
    unsigned const m_taylor_order;
    unsigned const m_grid_size;

    capd::IMap * m_vectorField  = nullptr;
    capd::IOdeSolver * m_solver = nullptr;
    capd::ITimeMap * m_timeMap  = nullptr;

public:
    contractor_capd_bwd_full(box const & box, ode_constraint const * const ctr, unsigned const taylor_order, unsigned const grid_size);
    ~contractor_capd_bwd_full();
    box prune(box b, SMTConfig & config) const;
    std::ostream & display(std::ostream & out) const;
};
contractor mk_contractor_capd_fwd_simple(box const & box, ode_constraint const * const ctr, unsigned const taylor_order = 20, unsigned const grid_size = 16);
contractor mk_contractor_capd_fwd_full(box const & box, ode_constraint const * const ctr, unsigned const taylor_order = 20, unsigned const grid_size = 16);
contractor mk_contractor_capd_bwd_simple(box const & box, ode_constraint const * const ctr, unsigned const taylor_order = 20, unsigned const grid_size = 16);
contractor mk_contractor_capd_bwd_full(box const & box, ode_constraint const * const ctr, unsigned const taylor_order = 20, unsigned const grid_size = 16);
}  // namespace dreal
