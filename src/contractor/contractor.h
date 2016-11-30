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

#pragma once

#include <algorithm>
#include <cassert>
#include <cstddef>
#include <functional>
#include <initializer_list>
#include <iosfwd>
#include <memory>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

#include "./dreal_config.h"
#include "constraint/constraint.h"
#include "contractor/contractor_cell.h"
#include "contractor/contractor_kind.h"
#include "contractor/contractor_status.h"
#include "ibex/ibex.h"
#include "opensmt/egraph/Enode.h"
#include "opensmt/smtsolvers/SMTConfig.h"
#include "util/box.h"
#include "util/stat.h"

namespace dreal {

#ifdef SUPPORT_ODE
enum class ode_direction { FWD, BWD };
std::ostream & operator<<(std::ostream & out, ode_direction const & d);
#endif

/// Wrapper on contractor_cell and its derived classes
class contractor {
public:
    contractor() = default;
    explicit contractor(std::shared_ptr<contractor_cell> const c) : m_ptr(c) {
        assert(m_ptr != nullptr);
    }
    ibex::BitSet const & get_input() const { return m_ptr->get_input(); }
    ibex::BitSet get_input() { return m_ptr->get_input(); }
    void prune(contractor_status & cs) {
        if (m_ptr) {
            // by default, clear output vector and used constraints.
            m_ptr->prune(cs);
            if (cs.m_config.nra_use_stat) {
                cs.m_config.nra_stat.increase_prune();
                if (!cs.m_output.empty()) {
                    cs.m_config.nra_stat.increase_non_trivial_prune();
                }
            }
        }
    }
    void prune_with_assert(contractor_status & cs);
    bool operator==(contractor const & c) const { return m_ptr == c.m_ptr; }
    bool operator<(contractor const & c) const { return m_ptr < c.m_ptr; }
    size_t hash() const { return reinterpret_cast<uintptr_t>(m_ptr.get()); }
    friend std::ostream & operator<<(std::ostream & out, contractor const & c);

private:
    std::shared_ptr<contractor_cell> m_ptr{nullptr};
};

contractor mk_contractor_id();
contractor mk_contractor_debug(std::string const & s);
contractor mk_contractor_seq(std::initializer_list<contractor> const & l);
contractor mk_contractor_seq(std::vector<contractor> const & v);
contractor mk_contractor_try(contractor const & c);
contractor mk_contractor_try_or(contractor const & c1, contractor const & c2);
contractor mk_contractor_empty();
contractor mk_contractor_throw();
contractor mk_contractor_throw_if_empty(contractor const & c);
contractor mk_contractor_join(contractor const & c1, contractor const & c2);
contractor mk_contractor_ite(std::function<bool(box const &)> guard, contractor const & c_then,
                             contractor const & c_else);
contractor mk_contractor_fixpoint(std::function<bool(box const &, box const &)> term_cond,
                                  contractor const & c);
contractor mk_contractor_fixpoint(std::function<bool(box const &, box const &)> term_cond,
                                  std::initializer_list<contractor> const & clist);
contractor mk_contractor_fixpoint(std::function<bool(box const &, box const &)> term_cond,
                                  std::vector<contractor> const & cvec);
contractor mk_contractor_int(box const & b);
contractor mk_contractor_eval(std::shared_ptr<nonlinear_constraint> const ctr,
                              bool const use_cache = false);
contractor mk_contractor_cache(contractor const & ctc);
contractor mk_contractor_sample(box const & b, unsigned const n,
                                std::vector<std::shared_ptr<constraint>> const & ctrs);
contractor mk_contractor_aggressive(unsigned const n,
                                    std::vector<std::shared_ptr<constraint>> const & ctrs);

contractor mk_contractor_ibex_fwdbwd(std::shared_ptr<nonlinear_constraint> const ctr,
                                     bool const use_cache = false);
contractor mk_contractor_ibex_newton(box const & box,
                                     std::shared_ptr<nonlinear_constraint> const ctr);
contractor mk_contractor_ibex_hc4(std::vector<Enode *> const & vars,
                                  std::vector<std::shared_ptr<nonlinear_constraint>> const & ctrs);
#ifdef USE_CLP
contractor mk_contractor_ibex_polytope(
    double const prec, std::vector<Enode *> const & vars,
    std::vector<std::shared_ptr<nonlinear_constraint>> const & ctrs);
#endif

contractor mk_contractor_forall(box const & box, std::shared_ptr<forall_constraint> const ctr);

contractor mk_contractor_parallel_any(std::initializer_list<contractor> const & l);
contractor mk_contractor_parallel_any(std::vector<contractor> const & v);
contractor mk_contractor_parallel_any(contractor const & c1, contractor const & c2);

contractor mk_contractor_parallel_all(std::initializer_list<contractor> const & l);
contractor mk_contractor_parallel_all(std::vector<contractor> const & v);
contractor mk_contractor_parallel_all(contractor const & c1, contractor const & c2);

#ifdef SUPPORT_ODE
contractor mk_contractor_capd_simple(box const & box, std::shared_ptr<ode_constraint> const ctr,
                                     ode_direction const dir);
contractor mk_contractor_capd_full(box const & box, std::shared_ptr<ode_constraint> const ctr,
                                   ode_direction const dir, SMTConfig const & config,
                                   bool const use_cache = false, double const timeout = 0.0);
contractor mk_contractor_capd_point(box const & box, std::shared_ptr<ode_constraint> const ctr,
                                    contractor const & eval_ctc, ode_direction const dir,
                                    SMTConfig const & config, bool const use_cache = false,
                                    double const timeout = 0.0);
#endif

std::ostream & operator<<(std::ostream & out, contractor const & c);
}  // namespace dreal

namespace std {
template <>
struct hash<dreal::contractor> {
    std::size_t operator()(dreal::contractor const & c) const { return c.hash(); }
};
}  // namespace std
