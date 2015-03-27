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
#include "opensmt/tsolvers/THandler.h"
#include "opensmt/egraph/Egraph.h"
#include "util/scoped_vec.h"
#include "heuristic.h"
#include <map>
#include <set>
#include <string>
#include <utility>

namespace dreal {
class plan_heuristic : public heuristic {
public:
 plan_heuristic() : heuristic(), choice_index(0), first_path(true) {}
    void initialize(SMTConfig &, Egraph &, THandler* thandler, vec<Lit> *trail, vec<int> *trail_lim);
    ~plan_heuristic() {
      for (auto t : time_process_enodes)
           delete t;
      for (auto t : time_event_enodes)
           delete t;
    }

    void resetSuggestions() { m_suggestions.clear(); }
    bool is_initialized() { return m_is_initialized; }
    void getSuggestions();
    void inform(Enode * e);
    void backtrack();
    void assertLits();



private:
    void pushTrailOnStack();
    void completeSuggestionsForTrail();
    int getChoiceIndex(Enode*);
    bool expand_path();
    bool unwind_path();
    bool pbacktrack();
    
    vector<string> m_actions;
    vector<string> m_events;
    vector<string> m_processes;
    vector<string> m_durative_actions;
    // vector< std::pair<Enode*, bool>* > m_suggestions;
    vector<pair<Enode*, vector<bool>*>*> m_decision_stack;
    
    set< Enode * > m_atoms;
    int num_choices_per_happening;
    int choice_index;
    bool first_path;
    
    //     map< Enode *, pair<int, int>* > process_literals;
    vector< map<string, Enode* >* > time_process_enodes;
    vector< map<string, Enode* >* > time_event_enodes;
    vector< map<string, Enode* >* > time_act_enodes;
    vector< map<string, Enode* >* > time_duract_enodes;
    vector<Enode*> choices;
    map<Enode*, int> choice_indices;
    map<string, int> schoice_indices;
    set<Enode*> process_enodes;
    set<Enode*> act_enodes;
    set<Enode*> duract_enodes;
    set<Enode*> event_enodes;
    vector< Enode* > time_enodes;
    
   
};
}
