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
#include "contractor/contractor_common.h"
#include "contractor/contractor_basic.h"

namespace dreal {
class contractor_capd_simple : public contractor_cell {
private:
    ode_direction const m_dir;
    std::shared_ptr<ode_constraint> const m_ctr;

public:
    contractor_capd_simple(box const & box, std::shared_ptr<ode_constraint> const ctr, ode_direction const dir);
    void prune(box & b, SMTConfig & config) const;
    std::ostream & display(std::ostream & out) const;
};

class contractor_capd_full : public contractor_cell {
private:
    ode_direction const m_dir;
    std::shared_ptr<ode_constraint> const m_ctr;
    unsigned const m_taylor_order;
    unsigned const m_grid_size;
    double const m_timeout;  // unit: msec
    std::vector<Enode *> m_vars_0;
    std::vector<Enode *> m_vars_t;
    bool m_need_to_check_inv;
    contractor m_inv_ctc;
    std::unique_ptr<capd::IMap> m_vectorField;
    std::unique_ptr<capd::IOdeSolver> m_solver;
    std::unique_ptr<capd::ITimeMap> m_timeMap;

    std::string build_capd_string(integral_constraint const & ic, ode_direction const dir = ode_direction::FWD) const;
    bool inner_loop(capd::IOdeSolver & solver, capd::interval const & prevTime, capd::interval const T, std::vector<std::pair<capd::interval, capd::IVector>> & enclosures) const;
    bool check_invariant(capd::IVector & v, box b, SMTConfig & config) const;
    template<typename Rect2Set>
    bool check_invariant(Rect2Set & s, box const & b, SMTConfig & config) const {
        thread_local static capd::IVector v;
        v = s;
        bool r = check_invariant(v, b, config);
        s = Rect2Set(v);
        return r;
    }
    bool compute_enclosures(capd::interval const & prevTime,
                            capd::interval const T,
                            box const & b,
                            std::vector<std::pair<capd::interval, capd::IVector>> & enclosures,
                            SMTConfig & config,
                            bool const add_all = false) const;


public:
    contractor_capd_full(box const & box, std::shared_ptr<ode_constraint> const ctr, ode_direction const dir, unsigned const taylor_order, unsigned const grid_size, double const timeout = 0.0);
    void prune(box & b, SMTConfig & config) const;
    nlohmann::json generate_trace(box b, SMTConfig & config) const;
    std::ostream & display(std::ostream & out) const;
};

contractor mk_contractor_capd_simple(box const & box, std::shared_ptr<ode_constraint> const ctr, ode_direction const dir);
contractor mk_contractor_capd_full(box const & box, std::shared_ptr<ode_constraint> const ctr, ode_direction const dir, unsigned const taylor_order = 20, unsigned const grid_size = 16, bool const use_cache = false, double const timeout = 0.0);
}  // namespace dreal
