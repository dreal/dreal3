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
#include <cassert>
#include <initializer_list>
#include <memory>
#include <stdexcept>
#include <string>
#include <tuple>
#include <unordered_map>
#include <utility>
#include <vector>
#include "./config.h"
#include "constraint/constraint.h"
#include "contractor/contractor.h"
#include "opensmt/egraph/Enode.h"
#include "opensmt/smtsolvers/SMTConfig.h"
#include "util/box.h"
#include "util/ibex_interval_hash.h"

namespace dreal {

// contractor_id : identity
class contractor_id : public contractor_cell {
private:
public:
    contractor_id();
    void prune(contractor_status & cs);
    std::ostream & display(std::ostream & out) const;
};

// contractor_debug : debug
class contractor_debug : public contractor_cell {
private:
    std::string m_msg;
public:
    explicit contractor_debug(std::string const & s);
    void prune(contractor_status & cs);
    std::ostream & display(std::ostream & out) const;
};

// contractor_seq : Run C1, C2, ... , Cn sequentially.
class contractor_seq : public contractor_cell {
private:
    std::vector<contractor> m_vec;
    void init();
public:
    explicit contractor_seq(std::initializer_list<contractor> const & l);
    explicit contractor_seq(std::vector<contractor> const & v);
    contractor_seq(contractor const & c1, contractor const & c2);
    void prune(contractor_status & cs);
    void prune_naive(contractor_status & cs);
    std::ostream & display(std::ostream & out) const;
};

// contractor_try : Try C1 if it fails, return id.
class contractor_try : public contractor_cell {
private:
    contractor m_c;
public:
    explicit contractor_try(contractor const & c);
    void prune(contractor_status & cs);
    std::ostream & display(std::ostream & out) const;
};

// contractor_try_or : Try C1 if it fails, do C2.
class contractor_try_or : public contractor_cell {
private:
    contractor m_c1;
    contractor m_c2;
public:
    contractor_try_or(contractor const & c1, contractor const & c2);
    void prune(contractor_status & cs);
    std::ostream & display(std::ostream & out) const;
};

// contractor_throw : throw an exception, always
class contractor_throw : public contractor_cell {
public:
    contractor_throw() : contractor_cell(contractor_kind::THROW, 1) { }
    void prune(contractor_status &) {
        throw contractor_exception("contractor_throw");
    }
    std::ostream & display(std::ostream & out) const {
        out << "contractor_throw()";
        return out;
    }
};

// contractor_empty : always prune to an empty box
class contractor_empty : public contractor_cell {
public:
    contractor_empty() : contractor_cell(contractor_kind::EMPTY) { }
    void prune(contractor_status & cs) {
        cs.m_box.set_empty();
    }
    std::ostream & display(std::ostream & out) const {
        out << "contractor_empty()";
        return out;
    }
};

// contractor_throw : throw an exception, always
class contractor_throw_if_empty : public contractor_cell {
private:
    contractor m_c;
public:
    explicit contractor_throw_if_empty(contractor const & c);
    void prune(contractor_status & cs);
    std::ostream & display(std::ostream & out) const;
};

// contractor_join : Run C1 and C2, join the result (take a hull of the two results)
class contractor_join : public contractor_cell {
private:
    contractor m_c1;
    contractor m_c2;
public:
    contractor_join(contractor const & c1, contractor const & c2);
    void prune(contractor_status & cs);
    std::ostream & display(std::ostream & out) const;
};

// contractor_ite : If then else
class contractor_ite : public contractor_cell {
private:
    std::function<bool(box)> m_guard;
    contractor m_c_then;
    contractor m_c_else;
public:
    contractor_ite(std::function<bool(box const &)> guard, contractor const & c_then, contractor const & c_else);
    void prune(contractor_status & cs);
    std::ostream & display(std::ostream & out) const;
};

// contractor_fixpoint
// Repeatedly applying the contractor while the condition is met
class contractor_fixpoint : public contractor_cell {
private:
    std::function<bool(box const &, box const &)> m_term_cond;
    std::vector<contractor> m_clist;
    box m_old_box;
    std::unordered_map<int, std::unordered_set<int>> m_dep_map;  // m_dep_map[v] = set of contractors depending on v (input)

    void init();
    // Naive fixedpoint algorithm
    void naive_fixpoint_alg(contractor_status & cs);
    // Worklist fixedpoint algorithm
    void worklist_fixpoint_alg(contractor_status & cs);
    void build_deps_map();

public:
    contractor_fixpoint(std::function<bool(box const &, box const &)> term_cond, contractor const & c);
    contractor_fixpoint(std::function<bool(box const &, box const &)> term_cond, std::initializer_list<contractor> const & clist);
    contractor_fixpoint(std::function<bool(box const &, box const &)> term_cond, std::vector<contractor> const & cvec);
    contractor_fixpoint(std::function<bool(box const &, box const &)> term_cond,
                        std::vector<contractor> const & cvec1, std::vector<contractor> const & cvec2);
    contractor_fixpoint(std::function<bool(box const &, box const &)> term_cond,
                        std::vector<contractor> const & cvec1, std::vector<contractor> const & cvec2, std::vector<contractor> const & cvec3);
    contractor_fixpoint(std::function<bool(box const &, box const &)> term_cond,
                        std::vector<contractor> const & cvec1, std::vector<contractor> const & cvec2,
                        std::vector<contractor> const & cvec3, std::vector<contractor> const & cvec4);
    contractor_fixpoint(std::function<bool(box const &, box const &)> term_cond, std::initializer_list<std::vector<contractor>> const & cvec_list);
    void prune(contractor_status & cs);
    std::ostream & display(std::ostream & out) const;
};

class contractor_int : public contractor_cell {
public:
    explicit contractor_int(box const & b);
    void prune(contractor_status & cs);
    std::ostream & display(std::ostream & out) const;
};

class contractor_eval : public contractor_cell {
private:
    std::shared_ptr<nonlinear_constraint> const m_nl_ctr;
public:
    explicit contractor_eval(std::shared_ptr<nonlinear_constraint> const ctr);
    void prune(contractor_status & cs);
    std::ostream & display(std::ostream & out) const;
};

class contractor_cache : public contractor_cell {
private:
    contractor m_ctc;
    unsigned m_num_hit;
    unsigned m_num_nohit;
    std::unordered_map<std::vector<ibex::Interval>,
                       std::tuple<std::vector<ibex::Interval>,
                                  ibex::BitSet,
                                  std::unordered_set<std::shared_ptr<constraint>>,
                                  bool>> m_cache;

public:
    explicit contractor_cache(contractor const & ctc);
    ~contractor_cache();
    void prune(contractor_status & cs);
    std::ostream & display(std::ostream & out) const;
};

class contractor_sample : public contractor_cell {
private:
    unsigned const m_num_samples;
    std::vector<std::shared_ptr<constraint>> m_ctrs;
public:
    contractor_sample(box const & b, unsigned const n, std::vector<std::shared_ptr<constraint>> const & ctrs);
    void prune(contractor_status & cs);
    std::ostream & display(std::ostream & out) const;
};

class contractor_aggressive : public contractor_cell {
private:
    unsigned const m_num_samples;
    std::vector<std::shared_ptr<constraint>> m_ctrs;
public:
    contractor_aggressive(unsigned const n, std::vector<std::shared_ptr<constraint>> const & ctrs);
    void prune(contractor_status & cs);
    std::ostream & display(std::ostream & out) const;
};

contractor mk_contractor_id();
contractor mk_contractor_debug(std::string const & s);
contractor mk_contractor_seq(std::initializer_list<contractor> const & l);
contractor mk_contractor_seq(std::vector<contractor> const & v);
contractor mk_contractor_seq(contractor const & c1, contractor const & c2);
contractor mk_contractor_try(contractor const & c);
contractor mk_contractor_try_or(contractor const & c1, contractor const & c2);
contractor mk_contractor_empty();
contractor mk_contractor_throw();
contractor mk_contractor_throw_if_empty(contractor const & c);
contractor mk_contractor_join(contractor const & c1, contractor const & c2);
contractor mk_contractor_ite(std::function<bool(box const &)> guard, contractor const & c_then, contractor const & c_else);
contractor mk_contractor_fixpoint(std::function<bool(box const &, box const &)> term_cond, contractor const & c);
contractor mk_contractor_fixpoint(std::function<bool(box const &, box const &)> term_cond, std::initializer_list<contractor> const & clist);
contractor mk_contractor_fixpoint(std::function<bool(box const &, box const &)> term_cond, std::vector<contractor> const & cvec);
contractor mk_contractor_fixpoint(std::function<bool(box const &, box const &)> term_cond, std::initializer_list<std::vector<contractor>> const & cvec_list);
contractor mk_contractor_int(box const & b);
contractor mk_contractor_eval(std::shared_ptr<nonlinear_constraint> const ctr, bool const use_cache = false);
contractor mk_contractor_cache(contractor const & ctc);
contractor mk_contractor_sample(box const & b, unsigned const n, std::vector<std::shared_ptr<constraint>> const & ctrs);
contractor mk_contractor_aggressive(unsigned const n, std::vector<std::shared_ptr<constraint>> const & ctrs);
std::ostream & operator<<(std::ostream & out, contractor const & c);

}  // namespace dreal
