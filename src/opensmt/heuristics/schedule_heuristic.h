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

typedef std::pair<int, std::vector<int>*> schedule_decision;
  
class schedule_heuristic : public heuristic {
public:
 schedule_heuristic() : heuristic(), choice_index(0), first_path(true), num_acts(0) {}
    bool initialize(SMTConfig &, Egraph &, THandler* thandler, vec<Lit> *trail, vec<int> *trail_lim);
    ~schedule_heuristic() {
    }

    void resetSuggestions() { m_suggestions.clear(); }
    bool is_initialized() { return m_is_initialized; }
    bool getSuggestions();
    void inform(Enode * e);
    void backtrack();
    void assertLits();
    Clause* getConflict() {return NULL;}


private:
    void pushTrailOnStack();
    void completeSuggestionsForTrail();
    int getChoiceIndex(Enode*);
    bool unwind_path();
    bool pbacktrack();
    bool expand_path(bool first_expansion);
    void displayDecisions();

    std::map<std::string, int> at_id; //not used
    std::vector<std::vector<Enode*>*> at_time_enodes;
    std::set<Enode*> at_enodes;
    std::vector<int>* get_possible_decisions(int act);
    std::pair<Enode*, bool>* on_stack(Enode* act);
        
    std::vector<schedule_decision*> m_decision_stack;

    std::set< Enode * > m_atoms;
    int num_choices_per_happening;
    int choice_index;
    bool first_path;
    int num_acts;

    std::vector< std::vector<Enode*>* > time_act_enodes;
    std::vector<Enode*> choices;
    std::map<Enode*, int> choice_indices;
    std::map<std::string, int> schoice_indices;
    
    std::vector< Enode* > time_enodes;

};
}
