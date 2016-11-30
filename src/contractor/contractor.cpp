/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>

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

#include "contractor/contractor.h"

#include <stdlib.h>
#include <functional>
#include <initializer_list>
#include <iostream>
#include <iterator>
#include <memory>
#include <queue>
#include <set>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "./dreal_config.h"
#include "contractor/contractor_basic.h"
#include "contractor/contractor_capd4.h"
#include "contractor/contractor_fixpoint.h"
#include "contractor/contractor_ibex.h"
#include "contractor/contractor_parallel_all.h"
#include "contractor/contractor_parallel_any.h"
#include "util/box.h"
#include "util/logging.h"
#include "util/thread_local.h"

class Enode;
namespace dreal {
class constraint;
class nonlinear_constraint;
class ode_constraint;
}  // namespace dreal
struct SMTConfig;

using std::back_inserter;
using std::cerr;
using std::cout;
using std::endl;
using std::function;
using std::initializer_list;
using std::make_pair;
using std::make_shared;
using std::ostream;
using std::ostringstream;
using std::pair;
using std::queue;
using std::set;
using std::string;
using std::shared_ptr;
using std::unordered_map;
using std::unordered_set;
using std::vector;

namespace dreal {

#ifdef SUPPORT_ODE
std::ostream & operator<<(std::ostream & out, ode_direction const & d) {
    switch (d) {
        case ode_direction::FWD:
            out << "FWD";
            break;
        case ode_direction::BWD:
            out << "BWD";
            break;
    }
    return out;
}
#endif

ostream & operator<<(ostream & out, contractor_cell const & c) { return c.display(out); }

void contractor::prune_with_assert(contractor_status & cs) {
    assert(m_ptr != nullptr);
    DREAL_THREAD_LOCAL static box old_box(cs.m_box);
    old_box = cs.m_box;
    m_ptr->prune(cs);
    if (!cs.m_box.is_subset(old_box)) {
        ostringstream ss;
        ss << "Pruning Violation: " << (*m_ptr) << endl
           << "Old Box" << endl
           << "==============" << endl
           << old_box << endl
           << "New Box" << endl
           << "==============" << endl
           << cs.m_box << endl
           << "==============" << endl;
        display_diff(ss, old_box, cs.m_box);
        ss << "==============" << endl;
        DREAL_LOG_FATAL << ss.str();
        exit(1);
    }
}

contractor mk_contractor_id() { return contractor(make_shared<contractor_id>()); }
contractor mk_contractor_debug(string const & s) {
    return contractor(make_shared<contractor_debug>(s));
}
contractor mk_contractor_seq(initializer_list<contractor> const & l) {
    if (l.size() == 0) {
        return mk_contractor_id();
    }
    return contractor(make_shared<contractor_seq>(l));
}
contractor mk_contractor_seq(vector<contractor> const & v) {
    if (v.size() == 0) {
        return mk_contractor_id();
    }
    return contractor(make_shared<contractor_seq>(v));
}
contractor mk_contractor_try(contractor const & c) {
    return contractor(make_shared<contractor_try>(c));
}
contractor mk_contractor_try_or(contractor const & c1, contractor const & c2) {
    return contractor(make_shared<contractor_try_or>(c1, c2));
}
contractor mk_contractor_empty() { return contractor(make_shared<contractor_empty>()); }
contractor mk_contractor_throw() { return contractor(make_shared<contractor_throw>()); }
contractor mk_contractor_throw_if_empty(contractor const & c) {
    return contractor(make_shared<contractor_throw_if_empty>(c));
}
contractor mk_contractor_join(contractor const & c1, contractor const & c2) {
    return contractor(make_shared<contractor_join>(c1, c2));
}
contractor mk_contractor_ite(function<bool(box const &)> guard, contractor const & c_then,
                             contractor const & c_else) {
    return contractor(make_shared<contractor_ite>(guard, c_then, c_else));
}
contractor mk_contractor_fixpoint(function<bool(box const &, box const &)> guard,
                                  contractor const & c) {
    return contractor(make_shared<contractor_fixpoint>(guard, c));
}
contractor mk_contractor_fixpoint(function<bool(box const &, box const &)> guard,
                                  initializer_list<contractor> const & clist) {
    if (clist.size() == 0) {
        return mk_contractor_id();
    }
    return contractor(make_shared<contractor_fixpoint>(guard, clist));
}
contractor mk_contractor_fixpoint(function<bool(box const &, box const &)> guard,
                                  vector<contractor> const & cvec) {
    if (cvec.size() == 0) {
        return mk_contractor_id();
    }
    return contractor(make_shared<contractor_fixpoint>(guard, cvec));
}
contractor mk_contractor_int(box const & b) { return contractor(make_shared<contractor_int>(b)); }
contractor mk_contractor_eval(shared_ptr<nonlinear_constraint> const ctr, bool const use_cache) {
    if (!use_cache) {
        return contractor(make_shared<contractor_eval>(ctr));
    }
    static unordered_map<shared_ptr<nonlinear_constraint>, contractor> eval_ctc_cache;
    auto const it = eval_ctc_cache.find(ctr);
    if (it == eval_ctc_cache.end()) {
        contractor ctc(make_shared<contractor_eval>(ctr));
        eval_ctc_cache.emplace(ctr, ctc);
        return ctc;
    } else {
        return it->second;
    }
}
contractor mk_contractor_cache(contractor const & ctc) {
    return contractor(make_shared<contractor_cache>(ctc));
}
contractor mk_contractor_sample(box const & b, unsigned const n,
                                vector<shared_ptr<constraint>> const & ctrs) {
    return contractor(make_shared<contractor_sample>(b, n, ctrs));
}
contractor mk_contractor_aggressive(unsigned const n, vector<shared_ptr<constraint>> const & ctrs) {
    return contractor(make_shared<contractor_aggressive>(n, ctrs));
}

contractor mk_contractor_ibex_fwdbwd(shared_ptr<nonlinear_constraint> const ctr,
                                     bool const use_cache) {
    if (!use_cache) {
        return contractor(make_shared<contractor_ibex_fwdbwd>(ctr));
    }
    static unordered_map<shared_ptr<nonlinear_constraint>, contractor> ibex_fwdbwd_ctc_cache;
    auto const it = ibex_fwdbwd_ctc_cache.find(ctr);
    if (it == ibex_fwdbwd_ctc_cache.end()) {
        contractor ctc(make_shared<contractor_ibex_fwdbwd>(ctr));
        ibex_fwdbwd_ctc_cache.emplace(ctr, ctc);
        return ctc;
    } else {
        return it->second;
    }
}

contractor mk_contractor_ibex_newton(box const & box, shared_ptr<nonlinear_constraint> const ctr) {
    return contractor(make_shared<contractor_ibex_newton>(box, ctr));
}
contractor mk_contractor_ibex_hc4(vector<Enode *> const & vars,
                                  vector<shared_ptr<nonlinear_constraint>> const & ctrs) {
    return contractor(make_shared<contractor_ibex_hc4>(vars, ctrs));
}
#ifdef USE_CLP
contractor mk_contractor_ibex_polytope(double const prec, vector<Enode *> const & vars,
                                       vector<shared_ptr<nonlinear_constraint>> const & ctrs) {
    return contractor(make_shared<contractor_ibex_polytope>(prec, vars, ctrs));
}
#endif

contractor mk_contractor_parallel_any(initializer_list<contractor> const & l) {
    return contractor(make_shared<contractor_parallel_any>(l));
}
contractor mk_contractor_parallel_any(vector<contractor> const & v) {
    return contractor(make_shared<contractor_parallel_any>(v));
}
contractor mk_contractor_parallel_any(contractor const & c1, contractor const & c2) {
    return contractor(make_shared<contractor_parallel_any>(c1, c2));
}

contractor mk_contractor_parallel_all(initializer_list<contractor> const & l) {
    return contractor(make_shared<contractor_parallel_all>(l));
}
contractor mk_contractor_parallel_all(vector<contractor> const & v) {
    return contractor(make_shared<contractor_parallel_all>(v));
}
contractor mk_contractor_parallel_all(contractor const & c1, contractor const & c2) {
    return contractor(make_shared<contractor_parallel_all>(c1, c2));
}

#ifdef SUPPORT_ODE
contractor mk_contractor_capd_simple(box const & box, shared_ptr<ode_constraint> const ctr,
                                     ode_direction const dir) {
    return contractor(make_shared<contractor_capd_simple>(box, ctr, dir));
}

contractor mk_contractor_capd_full(box const & box, shared_ptr<ode_constraint> const ctr,
                                   ode_direction const dir, SMTConfig const & config,
                                   bool const use_cache, double const timeout) {
    if (!use_cache) {
        return contractor(make_shared<contractor_capd_full>(box, ctr, dir, config, timeout));
    }
    if (dir == ode_direction::FWD) {
        static unordered_map<shared_ptr<ode_constraint>, contractor> capd_full_fwd_ctc_cache;
        auto it = capd_full_fwd_ctc_cache.find(ctr);
        if (it == capd_full_fwd_ctc_cache.end()) {
            contractor ctc(make_shared<contractor_capd_full>(box, ctr, dir, config, timeout));
            capd_full_fwd_ctc_cache.emplace(ctr, ctc);
            return ctc;
        } else {
            return it->second;
        }
    } else {
        static unordered_map<shared_ptr<ode_constraint>, contractor> capd_full_bwd_ctc_cache;
        auto it = capd_full_bwd_ctc_cache.find(ctr);
        if (it == capd_full_bwd_ctc_cache.end()) {
            contractor ctc(make_shared<contractor_capd_full>(box, ctr, dir, config, timeout));
            capd_full_bwd_ctc_cache.emplace(ctr, ctc);
            return ctc;
        } else {
            return it->second;
        }
    }
}
contractor mk_contractor_capd_point(box const & box, shared_ptr<ode_constraint> const ctr,
                                    contractor const & eval_ctc, ode_direction const dir,
                                    SMTConfig const & config, bool const use_cache,
                                    double const timeout) {
    if (!use_cache) {
        return contractor(
            make_shared<contractor_capd_point>(box, ctr, eval_ctc, dir, config, timeout));
    }
    if (dir == ode_direction::FWD) {
        static unordered_map<shared_ptr<ode_constraint>, contractor> capd_point_fwd_ctc_cache;
        auto it = capd_point_fwd_ctc_cache.find(ctr);
        if (it == capd_point_fwd_ctc_cache.end()) {
            contractor ctc(
                make_shared<contractor_capd_point>(box, ctr, eval_ctc, dir, config, timeout));
            capd_point_fwd_ctc_cache.emplace(ctr, ctc);
            return ctc;
        } else {
            return it->second;
        }
    } else {
        static unordered_map<shared_ptr<ode_constraint>, contractor> capd_point_bwd_ctc_cache;
        auto it = capd_point_bwd_ctc_cache.find(ctr);
        if (it == capd_point_bwd_ctc_cache.end()) {
            contractor ctc(
                make_shared<contractor_capd_point>(box, ctr, eval_ctc, dir, config, timeout));
            capd_point_bwd_ctc_cache.emplace(ctr, ctc);
            return ctc;
        } else {
            return it->second;
        }
    }
}
#endif

ostream & operator<<(ostream & out, contractor const & c) {
    if (c.m_ptr) {
        out << *(c.m_ptr);
    }
    return out;
}

}  // namespace dreal
