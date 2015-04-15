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
#include "config.h"
#include "util/constraint.h"
#include "opensmt/smtsolvers/SMTConfig.h"
#include "opensmt/egraph/Enode.h"
#include "util/box.h"

namespace dreal {

enum class contractor_kind { SEQ, OR, ITE, FP, PARALLEL_FIRST,
        PARALLEL_ALL, TIMEOUT, REALPAVER,
        TRY, TRY_OR, IBEX_POLYTOPE, IBEX_FWDBWD, INT, EVAL, CACHE,
        SAMPLE, AGGRESSIVE
#ifdef SUPPORT_ODE
        ,CAPD_FWD, CAPD_BWD
#endif
        };

class contractor_exception : public std::runtime_error {
public:
    explicit contractor_exception(const std::string& what_arg) : runtime_error(what_arg) { }
    explicit contractor_exception(const char* what_arg) : runtime_error(what_arg) { }
};

// Base Cell
class contractor_cell {
protected:
    contractor_kind m_kind;
    mutable ibex::BitSet m_input;
    mutable ibex::BitSet m_output;
    mutable std::unordered_set<constraint const *> m_used_constraints;
public:
    explicit contractor_cell(contractor_kind kind) : m_kind(kind) { }
    contractor_cell(contractor_kind kind, unsigned n)
        : m_kind(kind), m_input(ibex::BitSet::empty(n)), m_output(ibex::BitSet::all(n)) { }
    virtual ~contractor_cell() { }
    inline ibex::BitSet input()  const { return m_input; }
    inline ibex::BitSet output() const { return m_output; }
    inline std::unordered_set<constraint const *> used_constraints() const { return m_used_constraints; }
    virtual box prune(box b, SMTConfig & config) const = 0;
    virtual std::ostream & display(std::ostream & out) const = 0;
};

std::ostream & operator<<(std::ostream & out, contractor_cell const & c);

// Wrapper on contractor_cell and its derived classes
class contractor {
private:
    std::shared_ptr<contractor_cell const> m_ptr;

public:
    contractor() : m_ptr(nullptr) { }
    explicit contractor(std::shared_ptr<contractor_cell> const c) : m_ptr(c) {
            assert(m_ptr != nullptr);
    }
    contractor(contractor const & c) : m_ptr(c.m_ptr) {
        assert(m_ptr);
    }
    // contractor(contractor && c) : m_id(c.m_id), m_ptr(std::move(c.m_ptr)) {}
    ~contractor() { m_ptr.reset(); }

    inline ibex::BitSet input() const { return m_ptr->input(); }
    inline ibex::BitSet output() const { return m_ptr->output(); }
    inline std::unordered_set<constraint const *> used_constraints() const { return m_ptr->used_constraints(); }
    inline box prune(box const & b, SMTConfig & config) const {
        assert(m_ptr != nullptr);
        return m_ptr->prune(b, config);
    }
    inline bool operator==(contractor const & c) const { return m_ptr == c.m_ptr; }
    inline bool operator<(contractor const & c) const { return m_ptr < c.m_ptr; }

    friend contractor mk_contractor_ibex_polytope(double const prec, std::vector<nonlinear_constraint const *> const & ctrs);
    friend contractor mk_contractor_ibex_fwdbwd(box const & box, nonlinear_constraint const * const ctr);
    friend contractor mk_contractor_seq(std::initializer_list<contractor> const & l);
    friend contractor mk_contractor_try(contractor const & c);
    friend contractor mk_contractor_try_or(contractor const & c1, contractor const & c2);
    friend contractor mk_contractor_ite(std::function<bool(box const &)> guard, contractor const & c_then, contractor const & c_else);
    friend contractor mk_contractor_fixpoint(std::function<bool(box const &, box const &)> guard, contractor const & c);
    friend contractor mk_contractor_fixpoint(std::function<bool(box const &, box const &)> guard, std::initializer_list<contractor> const & clist);
    friend contractor mk_contractor_fixpoint(std::function<bool(box const &, box const &)> guard, std::vector<contractor> const & cvec);
    friend contractor mk_contractor_int();
    friend contractor mk_contractor_eval(box const & box, nonlinear_constraint const * const ctr);
    friend contractor mk_contractor_cache(contractor const & ctc);
    friend contractor mk_contractor_sample(unsigned const n, vector<constraint *> const & ctrs);
    friend contractor mk_contractor_aggressive(unsigned const n, vector<constraint *> const & ctrs);
#ifdef SUPPORT_ODE
    friend contractor mk_contractor_capd_fwd_simple(box const & box, ode_constraint const * const ctr, unsigned const taylor_order, unsigned const grid_size);
    friend contractor mk_contractor_capd_fwd_full(box const & box, ode_constraint const * const ctr, unsigned const taylor_order, unsigned const grid_size);
    friend contractor mk_contractor_capd_bwd_simple(box const & box, ode_constraint const * const ctr, unsigned const taylor_order, unsigned const grid_size);
    friend contractor mk_contractor_capd_bwd_full(box const & box, ode_constraint const * const ctr, unsigned const taylor_order, unsigned const grid_size);
#endif
    std::size_t hash() const { return (std::size_t) m_ptr.get(); }
    friend std::ostream & operator<<(std::ostream & out, contractor const & c);
};

// contractor_seq : Run C1, C2, ... , Cn sequentially.
class contractor_seq : public contractor_cell {
private:
    std::vector<contractor> m_vec;
public:
    contractor_seq(std::initializer_list<contractor> const & l);
    box prune(box b, SMTConfig & config) const;
    std::ostream & display(std::ostream & out) const;
};

// contractor_try : Try C1 if it fails, return id.
class contractor_try : public contractor_cell {
private:
    contractor const m_c;
public:
    contractor_try(contractor const & c);
    box prune(box b, SMTConfig & config) const;
    std::ostream & display(std::ostream & out) const;
};

// contractor_try_or : Try C1 if it fails, do C2.
class contractor_try_or : public contractor_cell {
private:
    contractor const m_c1;
    contractor const m_c2;
public:
    contractor_try_or(contractor const & c1, contractor const & c2);
    box prune(box b, SMTConfig & config) const;
    std::ostream & display(std::ostream & out) const;
};

// contractor_ite : If then else
class contractor_ite : public contractor_cell {
private:
    std::function<bool(box)> m_guard;
    contractor const m_c_then;
    contractor const m_c_else;
public:
    contractor_ite(std::function<bool(box const &)> guard, contractor const & c_then, contractor const & c_else);
    box prune(box b, SMTConfig & config) const;
    std::ostream & display(std::ostream & out) const;
};

// contractor_fixpoint
// Repeatedly applying the contractor while the condition is met
class contractor_fixpoint : public contractor_cell {
private:
    std::function<bool(box const &, box const &)> m_term_cond;
    std::vector<contractor> m_clist;

    // Naive fixedpoint algorithm
    box naive_fixpoint_alg(box old_b, SMTConfig & config) const;
    // Worklist fixedpoint algorithm
    box worklist_fixpoint_alg(box old_b, SMTConfig & config) const;

public:
    contractor_fixpoint(std::function<bool(box const &, box const &)> term_cond, contractor const & c);
    contractor_fixpoint(std::function<bool(box const &, box const &)> term_cond, std::initializer_list<contractor> const & clist);
    contractor_fixpoint(std::function<bool(box const &, box const &)> term_cond, std::vector<contractor> const & cvec);
    contractor_fixpoint(std::function<bool(box const &, box const &)> term_cond,
                        std::vector<contractor> const & cvec1, std::vector<contractor> const & cvec2);
    contractor_fixpoint(std::function<bool(box const &, box const &)> term_cond,
                        std::vector<contractor> const & cvec1, std::vector<contractor> const & cvec2, std::vector<contractor> const & cvec3);
    box prune(box b, SMTConfig & config) const;
    std::ostream & display(std::ostream & out) const;
};

class contractor_int : public contractor_cell {
private:
public:
    contractor_int();
    box prune(box b, SMTConfig & config) const;
    std::ostream & display(std::ostream & out) const;
};

class contractor_eval : public contractor_cell {
private:
    nonlinear_constraint const * const m_nl_ctr;
public:
    contractor_eval(box const & box, nonlinear_constraint const * const ctr);
    box prune(box b, SMTConfig & config) const;
    std::ostream & display(std::ostream & out) const;
};

class contractor_cache : public contractor_cell {
private:
    contractor const m_ctc;
public:
    explicit contractor_cache(contractor const & ctc);
    box prune(box b, SMTConfig & config) const;
    std::ostream & display(std::ostream & out) const;
};

class contractor_sample : public contractor_cell {
private:
    unsigned const m_num_samples;
    vector<constraint *> m_ctrs;
public:
    explicit contractor_sample(unsigned const n, vector<constraint *> const & ctrs);
    box prune(box b, SMTConfig & config) const;
    std::ostream & display(std::ostream & out) const;
};

class contractor_aggressive : public contractor_cell {
private:
    unsigned const m_num_samples;
    vector<constraint *> m_ctrs;
public:
    explicit contractor_aggressive(unsigned const n, vector<constraint *> const & ctrs);
    box prune(box b, SMTConfig & config) const;
    std::ostream & display(std::ostream & out) const;
};


contractor mk_contractor_seq(std::initializer_list<contractor> const & l);
contractor mk_contractor_try(contractor const & c);
contractor mk_contractor_try_or(contractor const & c1, contractor const & c2);
contractor mk_contractor_ite(std::function<bool(box const &)> guard, contractor const & c_then, contractor const & c_else);
contractor mk_contractor_fixpoint(std::function<bool(box const &, box const &)> guard, contractor const & c);
contractor mk_contractor_fixpoint(std::function<bool(box const &, box const &)> guard, std::initializer_list<contractor> const & clist);
contractor mk_contractor_fixpoint(std::function<bool(box const &, box const &)> guard, std::vector<contractor> const & cvec);
contractor mk_contractor_fixpoint(std::function<bool(box const &, box const &)> guard,
                                  std::vector<contractor> const & cvec1, std::vector<contractor> const & cvec2);
contractor mk_contractor_fixpoint(std::function<bool(box const &, box const &)> guard,
                                  std::vector<contractor> const & cvec1, std::vector<contractor> const & cvec2, std::vector<contractor> const & cvec3);
contractor mk_contractor_int();
contractor mk_contractor_eval(box const & box, nonlinear_constraint const * const ctr);
contractor mk_contractor_cache(contractor const & ctc);
contractor mk_contractor_sample(unsigned const n, vector<constraint *> const & ctrs);
contractor mk_contractor_aggressive(unsigned const n, vector<constraint *> const & ctrs);
std::ostream & operator<<(std::ostream & out, contractor const & c);

}  // namespace dreal

namespace std {
template <>
struct hash<dreal::contractor> {
    std::size_t operator()(dreal::contractor const & c) const { return c.hash(); }
};
}  // namespace std
