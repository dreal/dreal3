/*********************************************************************
nAuthor: Soonho Kong <soonhok@cs.cmu.edu>

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
#include <initializer_list>
#include <iosfwd>
#include <memory>
#include <stdexcept>
#include <string>
#include <thread>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "./dreal_config.h"
#include "constraint/constraint.h"
#include "contractor/contractor.h"
#include "contractor/contractor_cell.h"
#include "ibex/ibex.h"
#include "opensmt/egraph/Enode.h"
#include "util/box.h"
#include "util/logging.h"

class Enode;
namespace ibex {
class CtcNewton;
class ExprSymbol;
template <class T>
class Array;
}  // namespace ibex

namespace dreal {

class box;
class contractor_status;

class contractor_ibex_fwdbwd : public contractor_cell {
public:
    explicit contractor_ibex_fwdbwd(std::shared_ptr<nonlinear_constraint> const ctr);
    void prune(contractor_status & cs);
    std::ostream & display(std::ostream & out) const;

private:
    std::shared_ptr<nonlinear_constraint> m_ctr;
    std::shared_ptr<ibex::NumConstraint const> m_numctr;
    std::unordered_map<std::thread::id, std::shared_ptr<ibex::CtcFwdBwd>> m_ctc_map;
    std::vector<ibex::Function> m_func_store;
    std::shared_ptr<ibex::CtcFwdBwd> get_ctc(std::thread::id const tid, bool const need_to_clone) {
        // non-const version: look up m_ctc_map
        // if found, return one in the map
        // if not found, create one. Depending on the value of need_to_clone,
        //               use m_numctr or clone one to create ibex::CtcFwdBwd
        auto const it = m_ctc_map.find(tid);
        if (it == m_ctc_map.end()) {
            // not found, make one
            if (m_ctr->is_neq()) {
                m_ctc_map.emplace(tid, nullptr);
            } else {
                if (need_to_clone) {
                    // Since ibex::CtcFwdBwd takes a reference of a
                    // ibex::Function. If we don't store a function
                    // inside of a vector(store), it will be destroyed
                    // after this scope and m_ctc will point to that
                    // destroyed function.
                    m_func_store.emplace_back(m_numctr->f, ibex::Function::COPY);
                    ibex::CmpOp const op = m_numctr->op;
                    m_ctc_map.emplace(tid,
                                      std::make_shared<ibex::CtcFwdBwd>(m_func_store.back(), op));
                } else {
                    m_ctc_map.emplace(tid, std::make_shared<ibex::CtcFwdBwd>(*m_numctr));
                }
            }
            return m_ctc_map[tid];
        } else {
            // found
            return it->second;
        }
    }
    std::shared_ptr<ibex::CtcFwdBwd> get_ctc(std::thread::id const tid) const {
        // const version, simply look up m_ctc_map
        return m_ctc_map.at(tid);
    }

    static ibex::BitSet extract_bitset(std::shared_ptr<nonlinear_constraint> const ctr);
};

class contractor_ibex_newton : public contractor_cell {
public:
    contractor_ibex_newton(box const & box, std::shared_ptr<nonlinear_constraint> const ctr);
    void prune(contractor_status & cs);
    std::ostream & display(std::ostream & out) const;

private:
    std::shared_ptr<nonlinear_constraint> m_ctr;
    std::shared_ptr<ibex::NumConstraint> m_numctr;
    ibex::Array<ibex::ExprSymbol const> const & m_var_array;
    std::shared_ptr<ibex::CtcNewton> m_ctc;

    static ibex::BitSet extract_bitset(box const & box,
                                       std::shared_ptr<nonlinear_constraint> const ctr);
};

// contractor_ibex_hc4 : contractor using IBEX HC4
class contractor_ibex_hc4 : public contractor_cell {
public:
    contractor_ibex_hc4(std::vector<Enode *> const & vars,
                        std::vector<std::shared_ptr<nonlinear_constraint>> const & ctrs);
    void prune(contractor_status & cs);
    std::ostream & display(std::ostream & out) const;

private:
    std::unordered_set<Enode *> m_vars_in_ctrs;
    std::vector<std::shared_ptr<nonlinear_constraint>> m_ctrs;
    std::unique_ptr<ibex::Ctc> m_ctc{nullptr};
    static ibex::BitSet extract_bitset(
        std::vector<Enode *> const & vars,
        std::vector<std::shared_ptr<nonlinear_constraint>> const & ctrs);
};

#ifdef USE_CLP
// contractor_ibex_polytope : contractor using ibex polytope
class contractor_ibex_polytope : public contractor_cell {
public:
    contractor_ibex_polytope(double const prec, std::vector<Enode *> const & vars,
                             std::vector<std::shared_ptr<nonlinear_constraint>> const & ctrs);
    ~contractor_ibex_polytope();
    void prune(contractor_status & cs);
    std::ostream & display(std::ostream & out) const;

private:
    std::unordered_set<Enode *> m_vars_in_ctrs;
    std::vector<std::shared_ptr<nonlinear_constraint>> m_ctrs;
    double const m_prec;
    std::unordered_map<Enode *, ibex::ExprSymbol const *> m_var_cache;
    std::unordered_map<Enode *, ibex::ExprCtr const *> m_exprctr_cache_pos;
    std::unordered_map<Enode *, ibex::ExprCtr const *> m_exprctr_cache_neg;

    // TODO(soonhok): this is a hack to avoid const problem, we need to fix them
    std::unique_ptr<ibex::SystemFactory> m_sf{nullptr};
    std::unique_ptr<ibex::System> m_sys{nullptr};
    ibex::System * m_sys_eqs{nullptr};
    std::unique_ptr<ibex::LinearRelaxCombo> m_lrc{nullptr};
    std::vector<std::unique_ptr<ibex::Ctc>> m_sub_ctcs;
    std::unique_ptr<ibex::Ctc> m_ctc{nullptr};
    ibex::SystemFactory * build_system_factory(
        std::vector<Enode *> const & vars,
        std::vector<std::shared_ptr<nonlinear_constraint>> const & ctrs);

    static ibex::BitSet extract_bitset(
        std::vector<Enode *> const & vars,
        std::vector<std::shared_ptr<nonlinear_constraint>> const & ctrs);
};
#endif
}  // namespace dreal
