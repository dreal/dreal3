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
#include <stdlib.h>
#include <time.h>

#include <iosfwd>
#include <map>
#include <set>
#include <utility>
#include <vector>

#include "heuristic.h"
#include "json/json.hpp"
#include "opensmt/egraph/Egraph.h"
#include "opensmt/smtsolvers/SMTConfig.h"
#include "util/scoped_vec.h"

class Clause;
class Egraph;
class Enode;
class Lit;
class THandler;
struct SMTConfig;
template <class T> class vec;

namespace dreal {

typedef std::pair<std::set<int>*, int> labeled_transition;

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
    Clause* getConflict();

    static bool subgoal_compare(int i, int  j);
    void inform(Enode * e);

    // Is mode1 a predecessor of mode2
    bool predecessor(int autom, int mode1, int mode2) {
      std::vector<labeled_transition*>* i = (*predecessors[autom])[mode2-1];
      for(auto lt : (*i)){
        if(lt->second == mode1)
          return true;
      }
      return false;
    }

    double getCost(int autom, int i) { return (*m_cost[autom])[i];  }
    bool is_noop(labeled_transition* t) { return noops.find(t) != noops.end(); }

 protected:
    bool getSuggestions();
    void pushTrailOnStack();

 private:
    int num_autom;
    int num_labels;
    std::map<std::string, int> label_to_indices;
    std::map<int, std::string> label_from_indices;
    std::vector<std::vector<std::vector<labeled_transition*>*>*> predecessors;
    std::vector<std::vector<std::vector<labeled_transition*>*>*> successors;
    std::vector<std::vector< double >*>  m_cost;
    std::vector<std::vector<labeled_transition*>*> m_init_mode;
    std::vector<std::vector<labeled_transition*>*> m_goal_modes;
    std::vector<std::pair<int, std::vector<labeled_transition*>*>*> m_decision_stack;
    int m_depth;
    std::vector<Enode*> default_false_suggestions;
    std::vector<Enode*> default_true_suggestions;
    std::vector<std::map< Enode *, std::pair<int, int>* >*> mode_literals;
    std::vector<std::vector< std::vector< Enode* >* >*> time_mode_enodes;
    std::vector<std::vector< std::vector< Enode* >* >*> time_mode_integral_enodes;
    std::vector<std::vector<Enode*>* > time_label_enodes;
    std::map<Enode*, int> label_enode_indices;
    std::vector<std::set<int>*> m_aut_labels;

    std::set<Enode*> mode_enodes;
    std::set<Enode*> label_enodes;
    std::set<const labeled_transition*> noops;
    Egraph * m_egraph;
    // std::vector<int> * last_decision;
    nlohmann::json hinfo;
    bool expand_path(bool first_expansion);
    bool unwind_path();
    bool pbacktrack();
    std::string pathStackToString();
    void removeImpossibleTransitions(std::vector<labeled_transition*>* dec, int time, int autom);
    bool can_synchronize(std::vector<std::pair<int, labeled_transition*>*>& parallel_transitions,
                                         std::pair<int, labeled_transition*> &trans);
    std::string network_to_string();
    int lastDecisionStackEnd;
public:
    struct SubgoalCompare {
    SubgoalCompare(int a, hybrid_heuristic& c) : myHeuristic(c), autom(a) { srand(time(NULL));}
        bool operator () (const labeled_transition  *i, const labeled_transition *j) {
    bool noopi = myHeuristic.noops.find(i) != myHeuristic.noops.end();
    bool noopj = myHeuristic.noops.find(j) != myHeuristic.noops.end();

    if(noopi == noopj){
      return myHeuristic.getCost(autom, (i->second)-1) > myHeuristic.getCost(autom, (j->second)-1);
    } else if (noopi){
      return true;
    } else{
      return false;
    }

        }
      hybrid_heuristic& myHeuristic;
      int autom;
    };
};
}
