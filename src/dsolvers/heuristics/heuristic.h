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
#include "util/scoped_vec.h"

namespace dreal {
  class heuristic {
  public:
    heuristic(){}
    void initialize(SMTConfig &);
    ~heuristic() {
      for (auto i : predecessors)
        delete *i;
      for (auto p : mode_literals)
        delete p.second;
      for (auto d : m_decision_stack)
        delete d;
      for (auto t : time_mode_enodes)
        delete t;
    }

    void resetSuggestions() { m_suggestions.clear(); }
    bool is_initialized() { return m_is_initialized; }
    void getSuggestions(vector< Enode * > & suggestions, scoped_vec & m_stack);
    static bool subgoal_compare(int i, int  j);
    void inform(Enode * e);

    // Is mode1 a predecessor of mode2
    bool predecssor(int mode1, int mode2) {
      set<int>* i = predecessors[mode2-1];
      return i->find(mode1) != i->end();
    }

    double getCost(int i) { return m_cost[i];  }

  private:
    vector<set<int>*> predecessors;
    vector< double >  m_cost;
    vector< Enode * > m_suggestions;
    int m_init_mode;
    vector<int> m_goal_modes;
    bool m_is_initialized;
    vector<vector<int>*> m_decision_stack;
    int m_depth;
    map< Enode *, pair<int, int>* > mode_literals;
    vector< vector< Enode* >* > time_mode_enodes;
    // vector<int> * last_decision;

    bool expand_path(scoped_vec &);
    bool unwind_path(scoped_vec &);

  public:
    struct SubgoalCompare {
        SubgoalCompare(heuristic& c) : myHeuristic(c) {}
        bool operator () (const int & i, const int & j) {
          return myHeuristic.getCost(i-1) > myHeuristic.getCost(j-1);
        }
        heuristic& myHeuristic;
    };
  };
}
