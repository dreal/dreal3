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
#include <algorithm>
#include <unordered_map>
#include <vector>
#include <cassert>
#include <initializer_list>
#include <stdexcept>
#include <string>
#include <memory>
#include <utility>
#include "./config.h"
#include "opensmt/egraph/Enode.h"
#include "opensmt/smtsolvers/SMTConfig.h"
#include "util/box.h"
#include "constraint/constraint.h"

namespace dreal {
enum class contractor_kind { ID, SEQ, OR, ITE, FP,
        PARALLEL_ALL, PARALLEL_ANY, PSEQ,
        TIMEOUT, TRY, TRY_OR, JOIN,
        IBEX_FWDBWD, IBEX_NEWTON, IBEX_HC4, IBEX_POLYTOPE,
        INT, EVAL, CACHE, SAMPLE, AGGRESSIVE, FORALL,
        THROW, THROW_IF_EMPTY, EMPTY,
        DEBUG,
#ifdef SUPPORT_ODE
        CAPD_FULL, CAPD_SIMPLE, CAPD_POINT,
#endif
        };

enum class ode_direction { FWD, BWD };

std::ostream & operator<<(std::ostream & out, ode_direction const & d);

class contractor_exception : public std::runtime_error {
public:
    explicit contractor_exception(const std::string& what_arg) : runtime_error(what_arg) { }
    explicit contractor_exception(const char* what_arg) : runtime_error(what_arg) { }
};

class contractor_status {
public:
    box m_box;
    // "m_output[i] == 1" means that the value of the i-th variable is
    // changed after running the contractor.
    ibex::BitSet m_output;
    std::unordered_set<std::shared_ptr<constraint>> m_used_constraints;
    SMTConfig & m_config;

public:
    explicit contractor_status(SMTConfig & config)
        : m_box({}), m_config(config) { }
    contractor_status(box const & b, SMTConfig & config)
        : m_box(b), m_output(ibex::BitSet::empty(b.size())), m_config(config) { }
    contractor_status(box const & b,
                      ibex::BitSet const & output,
                      std::unordered_set<std::shared_ptr<constraint>> const & used_constraints,
                      SMTConfig & config)
        : m_box(b), m_output(output), m_used_constraints(used_constraints), m_config(config) { }

    // reset
    void reset(contractor_status & cs) {
        m_box = cs.m_box;
        m_output = cs.m_output;
        m_used_constraints = cs.m_used_constraints;
    }
    void join(contractor_status const & cs) {
        m_output.union_with(cs.m_output);
        std::unordered_set<std::shared_ptr<constraint>> const & used_ctrs = cs.m_used_constraints;
        m_used_constraints.insert(used_ctrs.begin(), used_ctrs.end());
        m_box.hull(cs.m_box);
    }
};

class contractor_status_guard {
private:
    contractor_status & m_cs_ref;
    ibex::BitSet m_old_output;
    std::unordered_set<std::shared_ptr<constraint>> m_old_used_constraints;

public:
    // Save output and used_constraints, and clear them
    explicit contractor_status_guard(contractor_status & cs)
        : m_cs_ref(cs), m_old_output(cs.m_output), m_old_used_constraints(cs.m_used_constraints) {
        cs.m_output.clear();
        cs.m_used_constraints.clear();
    }
    ~contractor_status_guard() {
        // Add saved output and used_constraints back to the m_cs_ref
        m_cs_ref.m_output.union_with(m_old_output);
        m_cs_ref.m_used_constraints.insert(m_old_used_constraints.begin(), m_old_used_constraints.end());
    }
};

// Base Cell
class contractor_cell {
protected:
    contractor_kind m_kind;
    // Static overapproximation of the input vector, which should be
    // computed in construction time.
    //
    // "m_input[i] == 1" means that the i-th varialbe is an input to
    // the contractor. It implies that any changes on i-th variable
    // should trigger another run of the contractor in the fixpoint
    // computation.
    ibex::BitSet m_input;

public:
    explicit contractor_cell(contractor_kind kind) : m_kind(kind) { }
    contractor_cell(contractor_kind kind, unsigned n)
        : m_kind(kind), m_input(ibex::BitSet::empty(n)) { }
    virtual ~contractor_cell() noexcept { }
    ibex::BitSet get_input() const { return m_input; }
    virtual void prune(contractor_status & cs) = 0;
    virtual std::ostream & display(std::ostream & out) const = 0;
};

std::ostream & operator<<(std::ostream & out, contractor_cell const & c);

// Wrapper on contractor_cell and its derived classes
class contractor {
private:
    std::shared_ptr<contractor_cell> m_ptr;

public:
    contractor() : m_ptr(nullptr) { }
    explicit contractor(std::shared_ptr<contractor_cell> const c) : m_ptr(c) {
        assert(m_ptr != nullptr);
    }
    contractor(contractor const & c) : m_ptr(c.m_ptr) {
        assert(m_ptr);
    }
    contractor(contractor && c) noexcept : m_ptr(std::move(c.m_ptr)) {}
    ~contractor() noexcept { }

    friend void swap(contractor & c1, contractor & c2) {
        using std::swap;
        swap(c1.m_ptr, c2.m_ptr);
    }

    contractor& operator=(contractor c) {
        swap(*this, c);
        return *this;
    }

    ibex::BitSet get_input() const { return m_ptr->get_input(); }

    void prune(contractor_status & cs) {
        if (m_ptr) {
            // by default, clear output vector and used constraints.
            m_ptr->prune(cs);
        }
    }
    void prune_with_assert(contractor_status & cs);
    bool operator==(contractor const & c) const { return m_ptr == c.m_ptr; }
    bool operator<(contractor const & c) const { return m_ptr < c.m_ptr; }
    std::size_t hash() const { return (std::size_t) m_ptr.get(); }
    friend std::ostream & operator<<(std::ostream & out, contractor const & c);
};

}  // namespace dreal

namespace std {
template <>
struct hash<dreal::contractor> {
    std::size_t operator()(dreal::contractor const & c) const { return c.hash(); }
};
}  // namespace std
