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
#include <stddef.h>
#include <iosfwd>
#include <map>
#include <set>
#include <string>
#include <utility>
#include <vector>

#include "heuristic.h"
#include "opensmt/egraph/Egraph.h"
#include "opensmt/smtsolvers/SMTConfig.h"
#include "opensmt/tsolvers/THandler.h"
#include "util/scoped_vec.h"

class Clause;
class Egraph;
class Enode;
class Lit;
class THandler;
struct SMTConfig;
template <class T> class vec;

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
    bool getSuggestions();
    void inform(Enode * e);
    void backtrack();
    void assertLits();
    Clause* getConflict() {return NULL;}


private:
    void pushTrailOnStack();
    void completeSuggestionsForTrail();
    int getChoiceIndex(Enode*);
    bool expand_path();
    bool unwind_path();
    bool pbacktrack();

    std::vector<std::string> m_actions;
    std::vector<std::string> m_events;
    std::vector<std::string> m_processes;
    std::vector<std::string> m_durative_actions;
    // std::vector< std::std::pair<Enode*, bool>* > m_suggestions;
    std::vector<std::pair<Enode*, std::vector<bool>*>*> m_decision_stack;

    std::set< Enode * > m_atoms;
    int num_choices_per_happening;
    int choice_index;
    bool first_path;

    //     std::map< Enode *, std::pair<int, int>* > process_literals;
    std::vector< std::map<std::string, Enode* >* > time_process_enodes;
    std::vector< std::map<std::string, Enode* >* > time_event_enodes;
    std::vector< std::map<std::string, Enode* >* > time_act_enodes;
    std::vector< std::map<std::string, Enode* >* > time_duract_enodes;
    std::vector<Enode*> choices;
    std::map<Enode*, int> choice_indices;
    std::map<std::string, int> schoice_indices;
    std::set<Enode*> process_enodes;
    std::set<Enode*> act_enodes;
    std::set<Enode*> duract_enodes;
    std::set<Enode*> event_enodes;
    std::vector< Enode* > time_enodes;


};
}
