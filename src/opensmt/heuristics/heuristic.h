/*********************************************************************
Author: Daniel Bryce <dbryce@sift.net>
        Soonho Kong <soonhok@cs.cmu.edu>
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
#include "opensmt/smtsolvers/SMTConfig.h"
#include "opensmt/egraph/Egraph.h"
#include "opensmt/tsolvers/THandler.h"
#include "util/scoped_vec.h"

#include <map>

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

  protected:
    virtual void getSuggestions();
    virtual void pushTrailOnStack();

    bool isStackConsistentWithSuggestion();
    void displayTrail();
    void displayStack();

    THandler *theory_handler;
    bool m_is_initialized;
    bool backtracked;
    vector<std::pair<Enode*, bool>*> m_suggestions;
    vector < std::pair<Enode*, bool>* > m_stack;
    vector<int> m_stack_lim;
    vec<Lit> *trail;
    vec<int> *trail_lim;
    int lastTrailEnd;
    int m_depth;
    Egraph * m_egraph;
    set<Enode*> stack_literals;
  };
}
