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
#include "capd/capdlib.h"

namespace dreal {

enum class contractor_kind { SEQ, OR, ITE, FP, PARALLEL_FIRST,
        PARALLEL_ALL, TIMEOUT, REALPAVER, CAPD_FWD, CAPD_BWD,
        TRY, IBEX, IBEX_FWDBWD, INT, EVAL};

class contractor;

class contractor_exception : public std::exception {
    virtual const char* what() const throw();
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
    virtual box prune(box b) const = 0;
    virtual std::ostream & display(std::ostream & out) const = 0;
};

std::ostream & operator<<(std::ostream & out, contractor_cell const & c);

class contractor_ibex_fwdbwd : public contractor_cell {
private:
    algebraic_constraint const * m_ctr;
    ibex::NumConstraint const * m_numctr;
    ibex::Array<ibex::ExprSymbol const> const & m_var_array;
    ibex::CtcFwdBwd * m_ctc = nullptr;

public:
    contractor_ibex_fwdbwd(box const & box, algebraic_constraint const * const ctr);
    ~contractor_ibex_fwdbwd();
    box prune(box b) const;
    std::ostream & display(std::ostream & out) const;
};

// contractor_IBEX : contractor using IBEX
class contractor_ibex : public contractor_cell {
private:
    double const                     m_prec;
    ibex::Array<ibex::NumConstraint> m_numctrs;
    ibex::SystemFactory              m_sf;
    ibex::System                     m_sys;
    ibex::System *                   m_sys_eqs = nullptr;
    ibex::LinearRelaxCombo *         m_lrc = nullptr;
    std::vector<ibex::Ctc *>         m_sub_ctcs;
    ibex::Ctc *                      m_ctc = nullptr;

public:
    contractor_ibex(double const prec, box const & box, std::vector<algebraic_constraint const *> const & ctrs);
    ~contractor_ibex();
    box prune(box b) const;
    std::ostream & display(std::ostream & out) const;
};

// contractor_seq : Try C1, C2, ... , Cn sequentially.
class contractor_seq : public contractor_cell {
private:
    std::vector<contractor> m_vec;
public:
    contractor_seq(std::initializer_list<contractor> const & l);
    box prune(box b) const;
    std::ostream & display(std::ostream & out) const;
};

// contractor_try : Try C1 if it fails, try C2.
class contractor_try : public contractor_cell {
private:
    contractor const & m_c1;
    contractor const & m_c2;
public:
    contractor_try(contractor const & c1, contractor const & c2);
    box prune(box b) const;
    std::ostream & display(std::ostream & out) const;
};

// contractor_ite : If then else
class contractor_ite : public contractor_cell {
private:
    std::function<bool(box)> m_guard;
    contractor const & m_c_then;
    contractor const & m_c_else;
public:
    contractor_ite(std::function<bool(box const &)> guard, contractor const & c_then, contractor const & c_else);
    box prune(box b) const;
    std::ostream & display(std::ostream & out) const;
};

// contractor_fixpoint
// Repeatedly applying the contractor while the condition is met
class contractor_fixpoint : public contractor_cell {
private:
    double const m_prec;
    std::function<bool(box const &, box const &)> m_term_cond;
    std::vector<contractor> m_clist;

    // Naive fixedpoint algorithm
    box naive_fixpoint_alg(box old_b) const;
    // Worklist fixedpoint algorithm
    box worklist_fixpoint_alg(box old_b) const;

public:
    contractor_fixpoint(double const prec, std::function<bool(box const &, box const &)> term_cond, contractor const & c);
    contractor_fixpoint(double const prec, std::function<bool(box const &, box const &)> term_cond, std::initializer_list<contractor> const & clist);
    contractor_fixpoint(double const prec, std::function<bool(box const &, box const &)> term_cond, std::vector<contractor> const & cvec);
    contractor_fixpoint(double const prec, std::function<bool(box const &, box const &)> term_cond,
                        std::vector<contractor> const & cvec1, std::vector<contractor> const & cvec2);
    contractor_fixpoint(double const prec, std::function<bool(box const &, box const &)> term_cond,
                        std::vector<contractor> const & cvec1, std::vector<contractor> const & cvec2, std::vector<contractor> const & cvec3);
    box prune(box b) const;
    std::ostream & display(std::ostream & out) const;
};

class contractor_int : public contractor_cell {
private:
public:
    contractor_int();
    box prune(box b) const;
    std::ostream & display(std::ostream & out) const;
};

class contractor_eval : public contractor_cell {
private:
    algebraic_constraint const * const m_alg_ctr;
public:
    contractor_eval(box const & box, algebraic_constraint const * const ctr);
    box prune(box b) const;
    std::ostream & display(std::ostream & out) const;
};

class contractor_capd_fwd_simple : public contractor_cell {
private:
    ode_constraint const * const m_ctr;

public:
    contractor_capd_fwd_simple(box const & box, ode_constraint const * const ctr);
    box prune(box b) const;
    std::ostream & display(std::ostream & out) const;
};

class contractor_capd_fwd_full : public contractor_cell {
private:
    ode_constraint const * const m_ctr;
    unsigned const m_taylor_order;
    unsigned const m_grid_size;

    bool inner_loop(capd::IOdeSolver & solver, capd::interval const & prevTime, capd::interval const T, vector<pair<capd::interval, capd::IVector>> & enclosures) const;
    bool prune(std::vector<pair<capd::interval, capd::IVector>> & enclosures, capd::IVector & X_t, capd::interval & T) const;

public:
    contractor_capd_fwd_full(box const & box, ode_constraint const * const ctr, unsigned const taylor_order, unsigned const grid_size);
    box prune(box b) const;
    std::ostream & display(std::ostream & out) const;
};

class contractor_capd_bwd_simple : public contractor_cell {
private:
    ode_constraint const * const m_ctr;

public:
    contractor_capd_bwd_simple(box const & box, ode_constraint const * const ctr);
    box prune(box b) const;
    std::ostream & display(std::ostream & out) const;
};

class contractor_capd_bwd_full : public contractor_cell {
private:
    ode_constraint const * const m_ctr;
    unsigned const m_taylor_order;
    unsigned const m_grid_size;
public:
    contractor_capd_bwd_full(box const & box, ode_constraint const * const ctr, unsigned const taylor_order, unsigned const grid_size);
    box prune(box b) const;
    std::ostream & display(std::ostream & out) const;
};


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
    inline box prune(box const & b) const {
        assert(m_ptr != nullptr);
        return m_ptr->prune(b);
    }
    inline bool operator==(contractor const & c) const { return m_ptr == c.m_ptr; }
    inline bool operator<(contractor const & c) const { return m_ptr < c.m_ptr; }

    friend contractor mk_contractor_ibex(double const prec, box const & box, std::vector<algebraic_constraint const *> const & ctrs);
    friend contractor mk_contractor_ibex_fwdbwd(box const & box, algebraic_constraint const * const ctr);
    friend contractor mk_contractor_seq(std::initializer_list<contractor> const & l);
    friend contractor mk_contractor_try(contractor const & c1, contractor const & c2);
    friend contractor mk_contractor_ite(std::function<bool(box const &)> guard, contractor const & c_then, contractor const & c_else);
    friend contractor mk_contractor_fixpoint(std::function<bool(box const &, box const &)> guard, contractor const & c);
    friend contractor mk_contractor_fixpoint(std::function<bool(box const &, box const &)> guard, std::initializer_list<contractor> const & clist);
    friend contractor mk_contractor_fixpoint(std::function<bool(box const &, box const &)> guard, std::vector<contractor> const & cvec);
    friend contractor mk_contractor_int();
    friend contractor mk_contractor_eval(box const & box, algebraic_constraint const * const ctr);
    friend contractor mk_contractor_capd_fwd_simple(box const & box, ode_constraint const * const ctr, unsigned const taylor_order, unsigned const grid_size);
    friend contractor mk_contractor_capd_fwd_full(box const & box, ode_constraint const * const ctr, unsigned const taylor_order, unsigned const grid_size);
    friend contractor mk_contractor_capd_bwd_simple(box const & box, ode_constraint const * const ctr, unsigned const taylor_order, unsigned const grid_size);
    friend contractor mk_contractor_capd_bwd_full(box const & box, ode_constraint const * const ctr, unsigned const taylor_order, unsigned const grid_size);
    std::size_t hash() const { return (std::size_t) m_ptr.get(); }
    friend std::ostream & operator<<(std::ostream & out, contractor const & c);
};

contractor mk_contractor_ibex(double const prec, box const & box, std::vector<algebraic_constraint const *> const & ctrs);
contractor mk_contractor_ibex_fwdbwd(box const & box, algebraic_constraint const * const ctr);
contractor mk_contractor_seq(std::initializer_list<contractor> const & l);
contractor mk_contractor_try(contractor const & c1, contractor const & c2);
contractor mk_contractor_ite(std::function<bool(box const &)> guard, contractor const & c_then, contractor const & c_else);
contractor mk_contractor_fixpoint(double const p, std::function<bool(box const &, box const &)> guard, contractor const & c);
contractor mk_contractor_fixpoint(double const p, std::function<bool(box const &, box const &)> guard, std::initializer_list<contractor> const & clist);
contractor mk_contractor_fixpoint(double const p, std::function<bool(box const &, box const &)> guard, std::vector<contractor> const & cvec);
contractor mk_contractor_fixpoint(double const p, std::function<bool(box const &, box const &)> guard,
                                  std::vector<contractor> const & cvec1, std::vector<contractor> const & cvec2);
contractor mk_contractor_fixpoint(double const p, std::function<bool(box const &, box const &)> guard,
                                  std::vector<contractor> const & cvec1, std::vector<contractor> const & cvec2, std::vector<contractor> const & cvec3);
contractor mk_contractor_int();
contractor mk_contractor_eval(box const & box, algebraic_constraint const * const ctr);
contractor mk_contractor_capd_fwd_simple(box const & box, ode_constraint const * const ctr, unsigned const taylor_order = 20, unsigned const grid_size = 16);
contractor mk_contractor_capd_fwd_full(box const & box, ode_constraint const * const ctr, unsigned const taylor_order = 20, unsigned const grid_size = 16);
contractor mk_contractor_capd_bwd_simple(box const & box, ode_constraint const * const ctr, unsigned const taylor_order = 20, unsigned const grid_size = 16);
contractor mk_contractor_capd_bwd_full(box const & box, ode_constraint const * const ctr, unsigned const taylor_order = 20, unsigned const grid_size = 16);
std::ostream & operator<<(std::ostream & out, contractor const & c);

}  // namespace dreal

namespace std {
template <>
struct hash<dreal::contractor> {
    std::size_t operator()(dreal::contractor const & c) const { return c.hash(); }
};
}  // namespace std
