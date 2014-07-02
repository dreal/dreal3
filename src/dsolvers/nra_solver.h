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
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>
#include "config.h"
#include "util/scoped_env.h"
#include "util/scoped_vec.h"
#include "opensmt/egraph/Egraph.h"
#include "opensmt/tsolvers/TSolver.h"
#include "realpaver/realpaver.h"

namespace dreal {
class nra_solver : public OrdinaryTSolver {
public:
    nra_solver(const int, const char *, SMTConfig &, Egraph &, SStore &, std::vector<Enode *> &,
               std::vector<Enode *> &, std::vector<Enode *> &);
    ~nra_solver();
    lbool inform(Enode * e);
    bool  assertLit(Enode * e, bool = false);
    void  pushBacktrackPoint ();
    void  popBacktrackPoint ();
    bool  check(bool c);
    bool  belongsToT(Enode * e);
    void  computeModel();

private:
    std::vector<Enode *> _vars;
    std::vector<Enode *> _lits;
    std::vector<rp_box> _boxes;
    scoped_vec<Enode *> _stack;
    scoped_vec<std::pair<Enode *, bool>> _deductions_stack;
    scoped_vec<std::vector<bool>> _used_constraints_stack;
    rp_problem _rp_problem;
    unsigned int _stat_check_incomplete;
    unsigned int _stat_check_complete;

    std::unordered_map<Enode *, int> _enode_to_rp_id;
    std::unordered_map<Enode *, rp_variable> _enode_to_rp_var;
    std::unordered_map<Enode *, rp_constraint> _enode_to_rp_ctr_pos;
    std::unordered_map<Enode *, rp_constraint> _enode_to_rp_ctr_neg;
    std::unordered_map<int, Enode *> _rp_id_to_enode;

    void get_explanation();
    vector<bool> get_used_constraints();
    void set_used_constraints(vector<bool> const & v);
    void get_deductions();
    bool prop();
    bool solve();
    void create_rp_var(Enode * const v);
    void create_rp_ctr(Enode * const l);
};
}
