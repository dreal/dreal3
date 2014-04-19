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
    // fields
    scoped_env m_env;
    scoped_vec m_stack;
};
