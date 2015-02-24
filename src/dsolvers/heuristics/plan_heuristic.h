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
#include <map>
#include <string>

namespace dreal {
class plan_heuristic {
public:
    plan_heuristic(){}
    void initialize(SMTConfig &, Egraph &);
    ~plan_heuristic() {
      for (auto t : time_process_enodes)
           delete t;
      for (auto t : time_event_enodes)
           delete t;
    }

    void resetSuggestions() { m_suggestions.clear(); }
    bool is_initialized() { return m_is_initialized; }
    void getSuggestions(vector< Enode * > & suggestions, scoped_vec & m_stack);
    void inform(Enode * e);

private:
    vector<string> m_actions;
    vector<string> m_events;
    vector<string> m_processes;
    vector<string> m_durative_actions;
    vector< Enode * > m_suggestions;
    bool m_is_initialized;
    int m_depth;
     map< Enode *, pair<int, int>* > process_literals;
     vector< map<string, Enode* >* > time_process_enodes;
     vector< map<string, Enode* >* > time_event_enodes;
     vector< Enode* > time_enodes;
    Egraph * m_egraph;
};
}
