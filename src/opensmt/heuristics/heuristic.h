/*********************************************************************
Author: Daniel Bryce <dbryce@sift.net>
        Soonho Kong <soonhok@cs.cmu.edu>
        Sicun Gao <sicung@cs.cmu.edu>

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
#include <limits.h>
#include <map>
#include <set>
#include <utility>
#include <vector>

#include "minisat/core/SolverTypes.h"
#include "opensmt/egraph/Egraph.h"
#include "opensmt/smtsolvers/SMTConfig.h"
#include "opensmt/tsolvers/THandler.h"
#include "util/scoped_vec.h"

class Egraph;
class Enode;
class THandler;
struct SMTConfig;
template <class T> class vec;

namespace dreal {
class heuristic {
  public:
  heuristic() : m_is_initialized(false), backtracked(false), lastTrailEnd(2) {}
    virtual ~heuristic();
    virtual void initialize(SMTConfig &, Egraph &, THandler* thandler,
                    vec<Lit> *trail, vec<int> *trail_lim);
    virtual void inform(Enode * e);
    virtual void backtrack();
    virtual Lit getSuggestion();
    virtual Clause* getConflict();

  protected:
    virtual bool getSuggestions();
    virtual void pushTrailOnStack();

    bool isStackConsistentWithSuggestion();
    void displayTrail();
    void displayStack(int bt_point = INT_MAX);

    THandler *theory_handler;
    bool m_is_initialized;
    bool backtracked;
    std::vector<std::pair<Enode*, bool>*> m_suggestions;
    std::vector < std::pair<Enode*, bool>* > m_stack;
    std::vector<int> m_stack_lim;
    vec<Lit> *trail;
    vec<int> *trail_lim;
    int lastTrailEnd;
    int m_depth;
    Egraph * m_egraph;
    std::set<Enode*> stack_literals;
    SMTConfig *m_config;
  };
}
