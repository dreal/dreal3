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
#include <functional>
#include <initializer_list>
#include <memory>
#include <ostream>
#include <stdexcept>
#include <string>
#include <tuple>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "./dreal_config.h"
#include "constraint/constraint.h"
#include "contractor/contractor.h"
#include "contractor/contractor_cell.h"
#include "contractor/contractor_exception.h"
#include "contractor/contractor_kind.h"
#include "contractor/contractor_status.h"
#include "ibex/ibex.h"
#include "opensmt/egraph/Enode.h"
#include "opensmt/smtsolvers/SMTConfig.h"
#include "util/box.h"
#include "util/ibex_interval_hash.h"

namespace dreal {

/// contractor_id : identity
class constraint;
class nonlinear_constraint;

class contractor_id : public contractor_cell {
public:
    contractor_id();
    void prune(contractor_status & cs);
    std::ostream & display(std::ostream & out) const;
};

/// contractor_debug : debug
class contractor_debug : public contractor_cell {
public:
    explicit contractor_debug(std::string const & s);
    void prune(contractor_status & cs);
    std::ostream & display(std::ostream & out) const;

private:
    std::string m_msg;
};

/// contractor_seq : Run C1, C2, ... , Cn sequentially.
class contractor_seq : public contractor_cell {
public:
    explicit contractor_seq(std::vector<contractor> const & v);
    void prune(contractor_status & cs);
    void prune_naive(contractor_status & cs);
    std::ostream & display(std::ostream & out) const;

private:
    std::vector<contractor> m_vec;
};

// contractor_try : Try C1 if it fails, return id.
class contractor_try : public contractor_cell {
public:
    explicit contractor_try(contractor const & c);
    void prune(contractor_status & cs);
    std::ostream & display(std::ostream & out) const;

private:
    contractor m_c;
};

// contractor_try_or : Try C1 if it fails, do C2.
class contractor_try_or : public contractor_cell {
public:
    contractor_try_or(contractor const & c1, contractor const & c2);
    void prune(contractor_status & cs);
    std::ostream & display(std::ostream & out) const;

private:
    contractor m_c1;
    contractor m_c2;
};

// contractor_throw : throw an exception, always
class contractor_throw : public contractor_cell {
public:
    contractor_throw() : contractor_cell(contractor_kind::THROW, 1) {}
    void prune(contractor_status &) { throw contractor_exception("contractor_throw"); }
    std::ostream & display(std::ostream & out) const {
        out << "contractor_throw()";
        return out;
    }
};

// contractor_empty : always prune to an empty box
class contractor_empty : public contractor_cell {
public:
    contractor_empty() : contractor_cell(contractor_kind::EMPTY) {}
    void prune(contractor_status & cs) { cs.m_box.set_empty(); }
    std::ostream & display(std::ostream & out) const {
        out << "contractor_empty()";
        return out;
    }
};

// contractor_throw : throw an exception, always
class contractor_throw_if_empty : public contractor_cell {
public:
    explicit contractor_throw_if_empty(contractor const & c);
    void prune(contractor_status & cs);
    std::ostream & display(std::ostream & out) const;

private:
    contractor m_c;
};

// contractor_join : Run C1 and C2, join the result (take a hull of the two results)
class contractor_join : public contractor_cell {
public:
    contractor_join(contractor const & c1, contractor const & c2);
    void prune(contractor_status & cs);
    std::ostream & display(std::ostream & out) const;

private:
    contractor m_c1;
    contractor m_c2;
};

// contractor_ite : If then else
class contractor_ite : public contractor_cell {
public:
    contractor_ite(std::function<bool(box const &)> guard, contractor const & c_then,
                   contractor const & c_else);
    void prune(contractor_status & cs);
    std::ostream & display(std::ostream & out) const;

private:
    std::function<bool(box)> m_guard;
    contractor m_c_then;
    contractor m_c_else;
};

class contractor_int : public contractor_cell {
public:
    explicit contractor_int(box const & b);
    void prune(contractor_status & cs);
    std::ostream & display(std::ostream & out) const;

private:
    static ibex::BitSet extract_bitset(box const & b);
};

class contractor_eval : public contractor_cell {
public:
    explicit contractor_eval(std::shared_ptr<nonlinear_constraint> const ctr);
    void prune(contractor_status & cs);
    std::ostream & display(std::ostream & out) const;

private:
    std::shared_ptr<nonlinear_constraint> const m_nl_ctr;
    static ibex::BitSet extract_bitset(std::shared_ptr<nonlinear_constraint> const ctr);
};

class contractor_cache : public contractor_cell {
public:
    explicit contractor_cache(contractor const & ctc);
    void prune(contractor_status & cs);
    std::ostream & display(std::ostream & out) const;

private:
    contractor m_ctc;
    unsigned m_num_hit{};
    unsigned m_num_nohit{};
    std::unordered_map<std::vector<ibex::Interval>,
                       std::tuple<std::vector<ibex::Interval>, ibex::BitSet,
                                  std::unordered_set<std::shared_ptr<constraint>>, bool>>
        m_cache;
};

class contractor_sample : public contractor_cell {
public:
    contractor_sample(box const & b, unsigned const n,
                      std::vector<std::shared_ptr<constraint>> const & ctrs);
    void prune(contractor_status & cs);
    std::ostream & display(std::ostream & out) const;

private:
    unsigned const m_num_samples;
    std::vector<std::shared_ptr<constraint>> m_ctrs;
};

class contractor_aggressive : public contractor_cell {
public:
    contractor_aggressive(unsigned const n, std::vector<std::shared_ptr<constraint>> const & ctrs);
    void prune(contractor_status & cs);
    std::ostream & display(std::ostream & out) const;

private:
    unsigned const m_num_samples;
    std::vector<std::shared_ptr<constraint>> m_ctrs;
};
}  // namespace dreal
