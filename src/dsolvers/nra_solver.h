/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>
        Sicun Gao <sicung@cs.cmu.edu>
        Edmund Clarke <emc@cs.cmu.edu>

dReal -- Copyright (C) 2013 - 2014, Soonho Kong, Sicun Gao, and Edmund Clarke

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
#include <set>
#include <map>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>
#include "./config.h"
#include "ibex/ibex.h"
#include "opensmt/egraph/Egraph.h"
#include "opensmt/tsolvers/TSolver.h"
#include "util/box.h"
#include "util/constraint.h"
#include "contractor/contractor.h"
#include "util/logging.h"
#include "util/scoped_vec.h"
#include "util/stat.h"

namespace std {
template<>
struct hash<ibex::Variable> {
    size_t operator () (const ibex::Variable & v) const {
        int h = 0;
        char const * str = v.symbol->name;
        while (*str)
            h = h << 1 ^ *str++;
        return h;
    }
};
template<>
struct equal_to<ibex::Variable> {
    bool operator() (const ibex::Variable & v1, const ibex::Variable & v2) const {
        return strcmp(v1.symbol->name, v2.symbol->name) == 0;
    }
};
}  // namespace std

namespace dreal {
class nra_solver : public OrdinaryTSolver {
public:
    nra_solver(const int, const char *, SMTConfig &, Egraph &, SStore &, std::vector<Enode *> &,
               std::vector<Enode *> &, std::vector<Enode *> &);
    ~nra_solver();
    lbool inform(Enode * e);
    bool  assertLit(Enode * e, bool = false);
    void  pushBacktrackPoint();
    void  popBacktrackPoint();
    bool  check(bool c);
    bool  belongsToT(Enode * e);
    void  computeModel();

private:
    // std::unordered_map<std::string, ibex::Variable const> m_var_map;
    // std::unordered_map<Enode*, ibex::ExprCtr const *> m_lit_ctr_map;
    // std::unordered_map<Enode*, ibex::Ctc *> m_lit_ctc_map;
    // std::unordered_set<Enode *> m_var_set;
    // std::vector<Enode *> m_var_vec;  // unsigned int -> Enode* (Variable)
    bool m_need_init = true;
    std::vector<Enode *> m_lits;
    scoped_vec<constraint *>  m_stack;
    scoped_vec<constraint const *>  m_used_constraint_vec;
    scoped_vec<box> m_boxes;
    std::vector<constraint *> m_ctrs;
    std::map<std::pair<Enode*, bool>, constraint *> m_ctr_map;

    contractor m_ctc;
    box m_box;
    stat m_stat;

    contractor build_contractor(box const & box, scoped_vec<constraint *> const & ctrs, bool const complete);
    std::vector<constraint *> initialize_constraints();
    std::vector<Enode *> generate_explanation(scoped_vec<constraint const *> const & ctr_vec);
    void handle_sat_case(box const & b) const;
};
}  // namespace dreal
