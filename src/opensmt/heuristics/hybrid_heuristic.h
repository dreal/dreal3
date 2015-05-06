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
#include "util/scoped_vec.h"
#include "heuristic.h"
#include <map>

namespace dreal {

  typedef pair<set<int>*, int> labeled_transition;

class hybrid_heuristic : public heuristic {
public:
 hybrid_heuristic() : heuristic(), num_labels(0) {}
  ~hybrid_heuristic() {
      for (auto i : predecessors){
	for (auto j : *i){
	  for (auto k : *j){
	    delete k->first;
	    delete k;
	  }
	  delete j;
	}
	delete i;
      }
	
      for (auto p : mode_literals){
	for (auto j : *p){
	  delete j.second;
	}
	delete p;
      }
      for (auto d : m_decision_stack){
	delete d->second;
	delete d;
      }
      for (auto t : time_mode_enodes){
	for (auto j : *t){
	  delete j;
	}
	delete t;
      }
    }
  void initialize(SMTConfig & c, Egraph & egraph, THandler* thandler,
		  vec<Lit> *trail, vec<int> *trail_lim);
  void backtrack();
    void resetSuggestions() { m_suggestions.clear(); }
    bool is_initialized() { return m_is_initialized; }
    
    static bool subgoal_compare(int i, int  j);
    void inform(Enode * e);

    // Is mode1 a predecessor of mode2
    bool predecessor(int autom, int mode1, int mode2) {
      vector<labeled_transition*>* i = (*predecessors[autom])[mode2-1];
      for(auto lt : (*i)){
	if(lt->second == mode1)
	  return true;
      }
      return false;
    }

    double getCost(int autom, int i) { return (*m_cost[autom])[i];  }

 protected:
    void getSuggestions();
    void pushTrailOnStack();

 private:
    int num_autom;
    int num_labels;
    map<string, int> label_indices;
    vector<vector<vector<labeled_transition*>*>*> predecessors;
    vector<vector< double >*>  m_cost;
    vector<int> m_init_mode;
    vector<vector<int>*> m_goal_modes;
    vector<pair<int, vector<labeled_transition*>*>*> m_decision_stack;
    int m_depth;
    vector<Enode*> default_false_suggestions;
    vector<Enode*> default_true_suggestions;
    vector<map< Enode *, pair<int, int>* >*> mode_literals;
    vector<vector< vector< Enode* >* >*> time_mode_enodes;
    vector<vector< vector< Enode* >* >*> time_mode_integral_enodes;
    vector<set<int>*> m_aut_labels;

    set<Enode*> mode_enodes;

    Egraph * m_egraph;
    // vector<int> * last_decision;

    bool expand_path();
    bool unwind_path();
    bool pbacktrack();

    bool can_synchronize(vector<pair<int, labeled_transition*>*>& parallel_transitions,
					 pair<int, labeled_transition*> &trans);

public:
    struct SubgoalCompare {
    SubgoalCompare(int a, hybrid_heuristic& c) : myHeuristic(c), autom(a) {}
        bool operator () (const labeled_transition  *i, const labeled_transition *j) {
          return myHeuristic.getCost(autom, (i->second)-1) < myHeuristic.getCost(autom, (j->second)-1);
        }
      hybrid_heuristic& myHeuristic;
      int autom;
    };
};
}
