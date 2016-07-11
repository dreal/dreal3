/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>

dReal -- Copyright (C) 2013 - 2015, the dReal Team

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
#include <functional>
#include <initializer_list>
#include <memory>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>
#include "capd/capdlib.h"
#include "contractor/contractor.h"
#include "json/json.hpp"
#include "opensmt/egraph/Enode.h"
#include "util/box.h"
#include "util/hash_combine.h"

namespace std {
template<>
struct hash<capd::Interval> {
    size_t operator () (const capd::Interval & v) const {
        size_t seed = 23;
        dreal::hash_combine<double>(seed, v.leftBound());
        dreal::hash_combine<double>(seed, v.rightBound());
        return seed;
    }
};
template<>
struct equal_to<capd::Interval> {
    bool operator() (const capd::Interval & v1, const capd::Interval & v2) const {
        return v1.leftBound() == v2.leftBound() && v1.rightBound() == v2.rightBound();
    }
};

template<>
struct hash<capd::IVector> {
    size_t operator () (const capd::IVector & v) const {
        size_t seed = 23;
        for (capd::Interval const & iv : v) {
            dreal::hash_combine<capd::Interval>(seed, iv);
        }
        return seed;
    }
};

template<>
struct equal_to<capd::IVector> {
    bool operator() (const capd::IVector & v1, const capd::IVector & v2) const {
        if (v1.dimension() != v2.dimension()) {
            return false;
        }
        for (unsigned i = 0; i < v1.dimension(); i++) {
            if (v1[i] != v2[i]) {
                return false;
            }
        }
        return true;
    }
};
}  // namespace std

namespace dreal {
class contractor_capd_simple : public contractor_cell {
private:
    ode_direction const m_dir;
    std::shared_ptr<ode_constraint> const m_ctr;

public:
    contractor_capd_simple(box const & box, std::shared_ptr<ode_constraint> const ctr, ode_direction const dir);
    void prune(contractor_status & s);
    std::ostream & display(std::ostream & out) const;
};

class contractor_capd_point : public contractor_cell {
private:
    ode_direction const m_dir;
    std::shared_ptr<ode_constraint> const m_ctr;
    contractor m_eval_ctc;
    unsigned const m_taylor_order;
    double const m_timeout;  // unit: msec
    std::vector<Enode *> m_vars_0;
    std::vector<Enode *> m_vars_t;
    bool m_need_to_check_inv;
    std::vector<contractor> m_inv_ctcs;
    std::unique_ptr<capd::DMap> m_vectorField;
    std::unique_ptr<capd::DOdeSolver> m_solver;
    std::unique_ptr<capd::DTimeMap> m_timeMap;

public:
    contractor_capd_point(box const & box, std::shared_ptr<ode_constraint> const ctr,
                          contractor const & eval_ctc, ode_direction const dir, SMTConfig const & config, double const timeout = 0.0);
    void prune(contractor_status & s);
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
    std::vector<contractor> m_inv_ctcs;
    std::unique_ptr<capd::IMap> m_vectorField;
    std::unique_ptr<capd::IOdeSolver> m_solver;
    std::unique_ptr<capd::ITimeMap> m_timeMap;

    bool inner_loop(capd::IOdeSolver & solver, capd::interval const & prevTime, capd::interval const T,
                    std::vector<std::pair<capd::interval, capd::IVector>> & enclosures) const;
    bool check_invariant(capd::IVector const & v, contractor_status cs);
    template<typename Rect2Set>
    bool check_invariant(Rect2Set const & rs, contractor_status const & s) {
        thread_local static capd::IVector v;
        v = rs;
        return check_invariant(v, s);
    }
    bool compute_enclosures(capd::interval const & prevTime,
                            capd::interval const T,
                            contractor_status const & s,
                            std::vector<std::pair<capd::interval, capd::IVector>> & enclosures,
                            bool const add_all = false);


public:
    contractor_capd_full(box const & box, std::shared_ptr<ode_constraint> const ctr,
                         ode_direction const dir, SMTConfig const & config, double const timeout = 0.0);
    void prune(contractor_status & s);
    nlohmann::json generate_trace(contractor_status s);
    std::ostream & display(std::ostream & out) const;
};

contractor mk_contractor_capd_simple(box const & box, std::shared_ptr<ode_constraint> const ctr, ode_direction const dir);
contractor mk_contractor_capd_full(box const & box, std::shared_ptr<ode_constraint> const ctr, ode_direction const dir,
                                   SMTConfig const & config, bool const use_cache = false, double const timeout = 0.0);
contractor mk_contractor_capd_point(box const & box, std::shared_ptr<ode_constraint> const ctr, contractor const & eval_ctc,
                                    ode_direction const dir, SMTConfig const & config, bool const use_cache = false, double const timeout = 0.0);
}  // namespace dreal
