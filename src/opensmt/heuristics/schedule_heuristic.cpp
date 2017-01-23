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

#include <sstream>
#include <string>
#include <unordered_set>
#include <utility>
#include "schedule_heuristic.h"
#include "json/json.hpp"
#include "opensmt/egraph/Egraph.h"
#include "opensmt/tsolvers/TSolver.h"
#include "util/logging.h"

using namespace std;
using nlohmann::json;

namespace dreal {

  extern string get_file_contents(const char* filename);
  extern int get_mode(Enode* e);

  bool schedule_heuristic::initialize(SMTConfig & c, Egraph & egraph, THandler* thandler, vec<Lit> *trl, vec<int> *trl_lim)  {
    DREAL_LOG_INFO << "schedule_heuristic::initialize() " << (thandler == NULL);
    m_egraph = &egraph;
    theory_handler = thandler;
    trail = trl;
    trail_lim = trl_lim;
    m_config = &c;
    m_is_initialized = true;

    m_depth = 10;
    num_choices_per_happening = 20; //num actions * 2

    for(int i = 0; i < m_depth+1; i++){
      at_time_enodes.push_back(new vector<Enode*>(num_choices_per_happening, NULL));
    }

    
    // if (c.nra_schedule_heuristic.compare("") != 0) {
    //     const string heuristic_string = get_file_contents(c.nra_schedule_heuristic.c_str());
    //     string err;
    //     auto json = json::parse(heuristic_string);
    //     //  auto hinfo = json.array_items();


    //    //   BMC depth
    //     m_depth = json["steps"];
    //     DREAL_LOG_INFO << "schedule_heuristic::initialize() #steps = " << m_depth;


    //     //   get acts
    //     for (auto a : json["actions"]) {
    //       m_actions.push_back(a);
    //       DREAL_LOG_INFO << "schedule_heuristic::initialize() Action = " << a;
    //     }

    //     //   get events
    //     for (auto a : json["events"]) {
    //       m_events.push_back(a);
    //       DREAL_LOG_INFO << "schedule_heuristic::initialize() Event = " << a;
    //     }

    //     //   get processes
    //     for (auto a : json["processes"]) {
    //       m_processes.push_back(a);
    //       DREAL_LOG_INFO << "schedule_heuristic::initialize() Process = " << a;
    //     }

    //     //   get durative_acts
    //     for (auto a : json["durative_actions"]) {
    //       m_durative_actions.push_back(a);
    //       DREAL_LOG_INFO << "schedule_heuristic::initialize() Durative Action = " << a;
    //     }

    //     for (int i = 0; i < m_depth+1; i++) {
    //       map< string, Enode* > * en = new map< string, Enode* >();
    //       time_process_enodes.push_back(en);

    //       en = new map< string, Enode* >();
    //       time_event_enodes.push_back(en);

    //       en = new map< string, Enode* >();
    //       time_act_enodes.push_back(en);

    //       en = new map< string, Enode* >();
    //       time_duract_enodes.push_back(en);
    //     }

    //     time_enodes.assign(static_cast<int>(m_depth+1), NULL);

    //     choices.assign(num_choices_per_happening*(m_depth+1), NULL);

    //     DREAL_LOG_DEBUG << "num_choices_per_happening = " << num_choices_per_happening;

    //     // vector<bool> *first_decision = new vector<bool>();
    //     // first_decision->push_back(true);
    //     // first_decision->push_back(false);
    //     // m_decision_stack.push_back(new pair<Enode*, vector<bool>*>( ,first_decision));
    // }
    return true;
}

void schedule_heuristic::inform(Enode * e) {
  if (m_atoms.find(e) != m_atoms.end())
    return;
  m_atoms.insert(e);

  //  DREAL_LOG_INFO << "schedule_heuristic::inform(): " << e << endl;
  // if (!e->isTAtom() && !e->isNot()) {
  //   unordered_set<Enode *> const & vars = e->get_vars();
  //   //unordered_set<Enode *> const & consts = e->get_constants();
  //   for (auto const & v : vars) {
  //     stringstream ss;
  //     ss << v;
  //     string var = ss.str();
  //     // if (var.find("process") != string::npos) {
  //     //   int time = atoi(var.substr(var.find_last_of("_")+1).c_str());
  //     //   int spos = var.find_first_of("_")+1;
  //     //   int epos = var.find_last_of("_")-1;
  //     //   string proc = var.substr(spos, epos-spos).c_str();

  //     //   //  for (auto const & c : consts) {
  //     //   //    stringstream css;
  //     //   //    css << c;
  //     //   //    int cs = atoi(css.str().c_str());
  //     //   //    if (cs == 1){
  //     //       DREAL_LOG_INFO << "process = " << proc << " time = " << time << endl;
  //     //       (*time_process_enodes[time])[proc] = e;
  //     //       process_enodes.insert(e);
  //     //       //          }
  //     //       //         }
  //     // } else  if (var.find("event") != string::npos) {
  //     //   int time = atoi(var.substr(var.find_last_of("_")+1).c_str());
  //     //   int spos = var.find_first_of("_")+1;
  //     //   int epos = var.find_last_of("_")-1;
  //     //   string proc = var.substr(spos, epos-spos).c_str();

  //     //   //  for (auto const & c : consts) {
  //     //   //    stringstream css;
  //     //   //    css << c;
  //     //   //    int cs = atoi(css.str().c_str());
  //     //   //    if (cs == 1){
  //     //       DREAL_LOG_INFO << "event = " << proc << " time = " << time << endl;
  //     //       (*time_event_enodes[time])[proc] = e;
  //     //       event_enodes.insert(e);
  //     //   //    }
  //     //   //  }
  //     // } else
  //     // if (var.find("duract") == 0 && var.find("_at") > 0) {
  //     //   int time = atoi(var.substr(var.find_last_of("_")+1).c_str());
  //     //   int spos = var.find_first_of("_")+1;
  //     //   int epos = var.find_last_of("_")-1;
  //     //   string proc = var.substr(spos, epos-spos).c_str();

  //     //   //  for (auto const & c : consts) {
  //     //   //    stringstream css;
  //     //   //    css << c;
  //     //   //    int cs = atoi(css.str().c_str());
  //     //   //    if (cs == 1) {
  //     //       DREAL_LOG_INFO << "action = " << proc << " time = " << time << endl;
  //     //       (*time_act_enodes[time])[proc] = e;
  //     //       act_enodes.insert(e);
  //     //       int choice = getChoiceIndex(e);
  //     //       DREAL_LOG_INFO << "index = " << choice;
  //     //       choices[num_choices_per_happening*(time)+choice] = e;

  //     //   //    }
  //     //   //  }
  //     // }
  //     // else  if (var.find("duract") == 0) {
  //     //   int time = atoi(var.substr(var.find_last_of("_")+1).c_str());
  //     //   int spos = var.find_first_of("_")+1;
  //     //   int epos = var.find_last_of("_")-1;
  //     //   string proc = var.substr(spos, epos-spos).c_str();

  //     //   //  for (auto const & c : consts) {
  //     //   //    stringstream css;
  //     //   //    css << c;
  //     //   //    int cs = atoi(css.str().c_str());
  //     //   //    if (cs == 1) {
  //     //       DREAL_LOG_INFO << "durative action = " << proc << " time = " << time << endl;
  //     //       (*time_duract_enodes[time])[proc] = e;
  //     //       duract_enodes.insert(e);
  //     //       int choice = getChoiceIndex(e);
  //     //       DREAL_LOG_INFO << "index = " << choice;
  //     //       choices[num_choices_per_happening*(time)+choice] = e;
  //     //   //    }
  //     //   //  }
  //     // }
  //   }
  // } else
  if (e->isEq()) {
    unordered_set<Enode *> const & vars = e->get_vars();
    unordered_set<Enode *> const & consts = e->get_constants();
    for (auto const & v : vars)  {
      stringstream ss;
      ss << v;
      string var = ss.str();
      if (var.find("time") != string::npos) {
        int time = atoi(var.substr(var.find_last_of("_")+1).c_str());
        for (auto const & c : consts) {
          stringstream css;
          css << c;
          int cs = atoi(css.str().c_str());
          if (cs == 0) { //  only care about assinging time if wait is possible
            DREAL_LOG_INFO << "time time = " << time << endl;
            time_enodes[time] = e;
          }
        }
      } else if (var.find("duract") == 0 && var.find("_at") != string::npos){
	DREAL_LOG_INFO << "var = " << var;
        for (auto const & c : consts) {
          stringstream css;
          css << c;
          int time = atoi(css.str().c_str());
	  DREAL_LOG_INFO << "time  = " << time << endl;
	  auto at = at_id.find(var);
	  if(at == at_id.end()){
	    at_id[var] = num_acts++;
	    at = at_id.find(var);
	  }

	  DREAL_LOG_INFO << "index = " << (*at).second;
	  (*at_time_enodes[time])[(*at).second] = e;
	  at_enodes.insert(e);
	  DREAL_LOG_INFO << "Got = " << (*at_time_enodes[time])[(*at).second];
	  
	}
      }
    }
  }
}

  int schedule_heuristic::getChoiceIndex(Enode *e) {
    int index = -1;
    map<Enode*, int>::iterator i = choice_indices.find(e);
    if(i == choice_indices.end()) {
      DREAL_LOG_INFO << "Generating new time choice index for " << e;
      unordered_set<Enode *> const & vars = e->get_vars();
      for (auto const & v : vars) {
        stringstream ss;
        ss << v;
        string var = ss.str();
        if (var.find("duract_") != string::npos ||
            var.find("act_") != string::npos) {

          int spos = var.find_first_of("_")+1;
          int epos = var.find_last_of("_")-1;
          string proc = var.substr(spos, epos-spos).c_str();
          map<string, int>::iterator j = schoice_indices.find(proc);
          if(j == schoice_indices.end()) {
            DREAL_LOG_INFO << "Generating new choice index for " << e;
            index = choice_index++;
            schoice_indices[proc] = index;
            break;
          } else {
            index = (*j).second;
            break;
          }
        }
      }
      assert(index >= 0);
      choice_indices[e] = index;
      return index;
    } else {
      return (*i).second;
    }
  }

  // Lit schedule_heuristic::getSuggestion() {
  //   DREAL_LOG_INFO << "schedule_heuristic::getSuggestion()";
  //   if (!m_is_initialized || m_suggestions.empty()) {
  //     getSuggestions();
  //   }
  //   if (!m_suggestions.empty()) {
  //     std::pair<Enode *, bool> *s = m_suggestions.back();
  //     m_suggestions.pop_back();
  //     Enode *e = s->first;


  //   if ( e == NULL )
  //     return lit_Undef;



  //   DREAL_LOG_INFO << "schedule_heuristic::getSuggestion() " << e;
  //   if (theory_handler == NULL)
  //     DREAL_LOG_INFO << "schedule_heuristic::getSuggestion() NULL";
  //   Var v = theory_handler->enodeToVar(e);
  //   delete s;
  //   return Lit( v, !s->second );
  //   } else {
  //     return lit_Undef;
  //
  // }

  void schedule_heuristic::backtrack() {
  if(!m_is_initialized) {
      return;
    }

    DREAL_LOG_DEBUG << "schedule_heuristic::backtrack()";
    lastTrailEnd = trail->size();
    DREAL_LOG_DEBUG << "schedule_heuristic::backtrack() lastTrailEnd = " << lastTrailEnd;

    for(auto a : m_suggestions) {
      delete a;
    }
    m_suggestions.clear();
    backtracked = true;

    displayTrail();
    displayStack();

    int bt_point = (((unsigned long)trail_lim->size() < m_stack_lim.size()  //&& trail_lim->size() > 0
          )
             ? m_stack_lim[trail_lim->size()]
             : m_stack.size());
    DREAL_LOG_DEBUG << "level = " << trail_lim->size() << " pt = " << bt_point;

    while(m_stack_lim.size() > (unsigned int) trail_lim->size())
      m_stack_lim.pop_back();

    for (int i = m_stack.size(); i > bt_point; i--) {
      std::pair<Enode *, bool> *s = m_stack.back();
      m_stack.pop_back();
      stack_literals.erase(s->first);
      delete s;
      // lastTrailEnd--;
    }
 displayStack();

  //   DREAL_LOG_DEBUG << "schedule_heuristic::backtrack()";
  //   m_suggestions.clear();
  //   lastTrailEnd = trail->size();

  //   for (int i = m_stack.size(); i > (trail->size()-2); i--) {
  //     std::pair<Enode *, bool> *s = m_stack.back();
  //     m_stack.pop_back();
  //     stack_literals.erase(s->first);
  //     delete s;
  //     lastTrailEnd--;
  //   }
  //   backtracked = true;
  //   // displayTrail();
  // }

  // void schedule_heuristic::assertLits() {
  //   DREAL_LOG_DEBUG << "schedule_heuristic::assertLits()";
  //   displayTrail();
  //   getSuggestions();
  }


  void schedule_heuristic::pushTrailOnStack() {
    DREAL_LOG_INFO << "schedule_heuristic::pushTrailOnStack() lastTrailEnd = "
                   << lastTrailEnd << " trail->size() = " << trail->size();
     displayTrail();
     if((unsigned int) trail_lim->size() > m_stack_lim.size() //&&
        //m_stack.size() > 0
	) //track start of levels after the first level
      m_stack_lim.push_back(m_stack.size());

    for (int i = lastTrailEnd; i < trail->size(); i++) {
      Enode *e = theory_handler->varToEnode(var((*trail)[i]));
      bool msign = !sign((*trail)[i]);
      //   DREAL_LOG_INFO << "schedule_heuristic::pushTrailOnStack() " << e;
      // if (process_enodes.find(e) != process_enodes.end()) {
      //   DREAL_LOG_INFO << "schedule_heuristic::pushTrailOnStack() " << e << " " << msign;
      //   m_stack.push_back(new std::pair<Enode *, bool>(e, msign));
      //   stack_literals.insert(e);
      // } else if (event_enodes.find(e) != event_enodes.end()) {
      //   DREAL_LOG_INFO << "schedule_heuristic::pushTrailOnStack() " << e << " " << msign;
      //   m_stack.push_back(new std::pair<Enode *, bool>(e, msign));
      //   stack_literals.insert(e);
      // } else
        if (at_enodes.find(e) != at_enodes.end()) {
        DREAL_LOG_INFO << "schedule_heuristic::pushTrailOnStack() " << e << " " << msign;
        m_stack.push_back(new std::pair<Enode *, bool>(e, msign));
        stack_literals.insert(e);
      }
	// else if (duract_enodes.find(e) != duract_enodes.end()) {
      //   DREAL_LOG_INFO << "schedule_heuristic::pushTrailOnStack() " << e << " " << msign;
      //   m_stack.push_back(new std::pair<Enode *, bool>(e, msign));
      //   stack_literals.insert(e);
      // }
    }
    lastTrailEnd = trail->size();


    displayStack();
  }

  void schedule_heuristic::completeSuggestionsForTrail() {
    DREAL_LOG_INFO << "schedule_heuristic::completeSuggestionsForTrail()";
    for( int i = m_decision_stack.size()-1; i >= 0; i--) {
      schedule_decision* decision = m_decision_stack[i];
      DREAL_LOG_DEBUG << "Suggesting: " << decision->first << " " << decision->second->back();
      for(int time = 0; time <= m_depth; time++){
	Enode* decision_enode = (*at_time_enodes[time])[decision->first];
	DREAL_LOG_DEBUG << "Suggesting: " << decision_enode << " = " << (time == decision->second->back());
	if (time == decision->second->back()){
	  m_suggestions.push_back(new std::pair<Enode *, bool>(decision_enode, true));
	} else {
	  m_suggestions.push_back(new std::pair<Enode *, bool>(decision_enode, false));
	}
      }      
    }

    DREAL_LOG_INFO << "schedule_heuristic::completeSuggestionsForTrail()";
    // for (int time = m_depth; time >= 0; time--) {
    //   DREAL_LOG_INFO << "schedule_heuristic::completeSuggestionsForTrail() time = " << time;
    //   // // suggest processes
    //   // map<string, Enode*> *process_at_time = time_process_enodes[time];
    //   // for (auto p : *process_at_time) {
    //   //   if (stack_literals.find(p.second) == stack_literals.end()) {
    //   //     DREAL_LOG_INFO << "schedule_heuristic::completeSuggestionsForTrail() suggesting = " << p.second;
    //   //     // p.second->setDecPolarity(true);
    //   //     m_stack.push_back(new std::pair<Enode *, bool>(p.second, true));
    //   //     m_suggestions.push_back(new std::pair<Enode *, bool>(p.second, true));
    //   //   }
    //   // }

    //   // // suggest events
    //   // map<string, Enode*> *event_at_time = time_event_enodes[time];
    //   // for (auto p : *event_at_time) {
    //   //   if (stack_literals.find(p.second) == stack_literals.end()) {
    //   //     DREAL_LOG_INFO << "schedule_heuristic::completeSuggestionsForTrail() suggesting = " << p.second;
    //   //     // p.second->setDecPolarity(false);
    //   //     m_stack.push_back(new std::pair<Enode *, bool>(p.second, false));
    //   //     m_suggestions.push_back(new std::pair<Enode *, bool>(p.second, false));
    //   //   }
    //   // }

    //   // suggest acts
    //   map<string, Enode*> *act_at_time = time_act_enodes[time];
    //   for (auto p : *act_at_time) {
    //     if (stack_literals.find(p.second) == stack_literals.end()) {
    //       DREAL_LOG_INFO << "schedule_heuristic::completeSuggestionsForTrail() suggesting = " << p.second;
    //       // p.second->setDecPolarity(true);
    //       m_stack.push_back(new std::pair<Enode *, bool>(p.second, true));
    //       m_suggestions.push_back(new std::pair<Enode *, bool>(p.second, true));
    //     }
    //   }


    //   // suggest duracts
    //   map<string, Enode*> *duract_at_time = time_duract_enodes[time];
    //   for (auto p : *duract_at_time) {
    //     if (stack_literals.find(p.second) == stack_literals.end()) {
    //       DREAL_LOG_INFO << "schedule_heuristic::completeSuggestionsForTrail() suggesting = " << p.second;
    //       // p.second->setDecPolarity(true);
    //       m_stack.push_back(new std::pair<Enode *, bool>(p.second, true));
    //       m_suggestions.push_back(new std::pair<Enode *, bool>(p.second, true));
    //     }
    //   }
    // }
  }
  
std::pair<Enode*, bool>* schedule_heuristic::on_stack(Enode* act) {

  auto e = stack_literals.find(act);
  if (e != stack_literals.end()) {
  for (auto d : m_stack) {
    if (act == d->first){
      return d;
    }
  }
  }
  return NULL;
}
    
  std::vector<int>* schedule_heuristic::get_possible_decisions(int act) {
  std::vector<int>* decisions = new vector<int>();
  for (int i = m_depth-1; i >= 0; i--) {
    Enode* act_at_step = (*at_time_enodes[i])[act];
    pair<Enode*, bool>* on = on_stack(act_at_step);
    if (on == NULL) { //no decisions for act on stack
      decisions->push_back(i);
      DREAL_LOG_DEBUG << "depth = " << i << " enode = " << act_at_step;
    } else if (on->second == true) { //already assigned
      decisions->clear();
      decisions->push_back(i);
      DREAL_LOG_DEBUG << "only depth = " << i << " enode = " << act_at_step;
      break;
    } else { // assigned false
    }
  }
  return decisions;
}


// Assume that m_decision_stack matches m_stack
// and need to suggest next decision
bool schedule_heuristic::expand_path(bool first_expansion) {
    DREAL_LOG_INFO << "schedule_heuristic::expand_path()" << endl;
    DREAL_LOG_INFO << "[" << num_choices_per_happening << " " << m_depth << " " << m_decision_stack.size() << "]";

    displayDecisions();
    
    // cannot expand path if out of choices
    if (m_decision_stack.size() == 0 && !first_expansion){
      DREAL_LOG_INFO << "out of choices";
        return false;
    }

    // path already expanded by SAT solver, and already pushed on m_stack
    if (m_decision_stack.size() == (unsigned long)(num_choices_per_happening)){
      DREAL_LOG_INFO << "path already full"; 
        return true;
    }

    int steps_to_add = (num_choices_per_happening) - static_cast<int>(m_decision_stack.size());
    DREAL_LOG_INFO << "Adding #steps: " << steps_to_add << endl;
    for (int i = 0; i < steps_to_add; i++){
      int act = (static_cast<int>(m_decision_stack.size()));
      DREAL_LOG_DEBUG << "Adding decisions for act id " << act;
      vector<int> *current_decision = get_possible_decisions(act);

      for(auto d : *current_decision) {
	DREAL_LOG_DEBUG << "Decision: " << d;
      }

      
      // DREAL_LOG_INFO << "step = " << step << " act = " << act;
      //      Enode* current_enode = (*at_time_enodes[step])[act];

      
      
      // bool found_existing_value = false;
      // // prune out choices that are negated in m_stack
      // for (auto e : m_stack) {
      // 	auto a = at_enodes.find(e);
      // 	if(a != at_enodes.end()){
      // 	  // is an at literal
	  
      // 	}
	
      // 	if(e->first == current_enode) {
      // 	  current_decision->push_back(e->second);
      // 	  found_existing_value = true;
      // 	  break;
      // 	}
      // }

      
      
      // if(!found_existing_value) {
      // 	current_decision->push_back(false);
      // 	current_decision->push_back(true);
      // } 

        // // remove choices that are too costly for time
        // for (auto c : *current_decision)  {
        //   if ((*m_cost[autom])[ c-1 ] > time)  {
        //         DREAL_LOG_INFO << "Removing too costly " << c << endl;
        //         auto e = current_decision_copy.find(c);
        //         if (e != current_decision_copy.end()) {
        //             current_decision_copy.erase(e);
        //         }
        //     }
        // }

        // current_decision->clear();
        // current_decision->insert(current_decision->begin(), current_decision_copy.begin(), current_decision_copy.end());

        if (current_decision->size() == 0) {
            DREAL_LOG_INFO << "No decisions left at time " << act << endl;
            return false;
        }

        //    sort (current_decision->begin(), current_decision->end(), SubgoalCompare(autom, *this));

        m_decision_stack.push_back(new schedule_decision(act, current_decision));

        // for (auto d : *current_decision) {
        //     DREAL_LOG_INFO << "dec = " << d << endl;
        // }
        // }
    }
      DREAL_LOG_DEBUG << "After Expand, stack size = " << m_decision_stack.size();
      

    return static_cast<int>(m_decision_stack.size()) ==
      num_choices_per_happening; // successfully found a full path
}

  // undo choices on m_decision_stack until earliest violated decision
bool schedule_heuristic::unwind_path() {
  // vector<int> path;
  // path.assign(num_autom*(m_depth+1), -1);
  // int actual_path_size = 0;
  // for (auto e : m_stack) {
  //   DREAL_LOG_INFO << "Checking path " << e->first << " = " << e->second;
  //   auto i = (*tim_act_enodeserals[a]).find(e->first);
  //    if (i != (*mode_literals[a]).end()) {
  //      DREAL_LOG_DEBUG << "setting path[" << (((*i).second->second*num_autom)+(num_autom-a)-1) << "] = "
  //                       << (*i).second->first;
  //      path[((*i).second->second*num_autom)+(num_autom-a-1)] = (*i).second->first;
  //      actual_path_size++;
  //      break;
  //    }
  //     }
  //   }

  //int earliest_disagreement = m_decision_stack.size();
  DREAL_LOG_INFO << "schedule_heuristic::unwind_path()";
  bool need_bt_to_decision = false;
  for(unsigned int i = 0 ; i < m_decision_stack.size(); i++) {
    schedule_decision *decision = m_decision_stack[i];
    Enode* decision_enode = (*at_time_enodes[decision->second->back()])[decision->first];
    DREAL_LOG_INFO << "schedule_heuristic::unwind_path() " << decision_enode << " at " << i;

    // bool found_decision = false;
    for(unsigned int j = 0; j < m_stack.size(); j++) {
      pair<Enode*, bool>* sdecision = m_stack[j];
      if(decision_enode == sdecision->first) {
        // found_decision = true;

        //decision disagrees w/ m_stack
        if(!sdecision->second) {
	  DREAL_LOG_INFO << "schedule_heuristic::unwind_path() " << decision_enode << " is false";
          //found possibly earliest disagreement, clear decision stack to this point
          for(unsigned int k = m_decision_stack.size()-1; k > i; k--) {
            delete m_decision_stack[k]->second;
            delete m_decision_stack[k];
            m_decision_stack.pop_back();
          }
          need_bt_to_decision = false; //backtracked over any empty decisions

          //clear conflicting decision
          m_decision_stack[i]->second->pop_back();
          if(m_decision_stack[i]->second->empty()) {
            need_bt_to_decision = true;
          }
        }
      }
    }
  }

  if(need_bt_to_decision) {
    //clean up decision stack so that there are no levels with no decisions
    pbacktrack();
  }



  // bool paths_agree = true;
  // int agree_depth = 0;
  // for (int j = static_cast<int>(path.size() - 1); j > -1; j--) {
  //   DREAL_LOG_INFO << "Path (" << j << ") = " << path[j] << endl;
  //   int stack_index_for_path_index = static_cast<int>(path.size() - j - 1);
  //   if (stack_index_for_path_index < static_cast<int>(m_decision_stack.size()))
  //     DREAL_LOG_INFO << "Stack(" << stack_index_for_path_index << ") = a"
  //                 << (m_decision_stack[stack_index_for_path_index]->first+1)
  //                 << " m"
  //                 << m_decision_stack[stack_index_for_path_index]->second->back();
  //   else
  //     DREAL_LOG_INFO << "Stack(" << stack_index_for_path_index << ") = *";

  //   if (stack_index_for_path_index <  static_cast<int>(m_decision_stack.size())) {
  //     if (m_decision_stack[stack_index_for_path_index]->second->back() != path[j]) {
  //    if (paths_agree) {
  //      agree_depth = stack_index_for_path_index-1;
  //      DREAL_LOG_INFO << "Last Agreed at: " << agree_depth << endl;
  //    }
  //    paths_agree = false;
  //     }
  //   } else {
  //     if (paths_agree) {
  //    agree_depth = stack_index_for_path_index-1;
  //    DREAL_LOG_INFO << "Last Agreed at: " << agree_depth << endl;
  //     }
  //     paths_agree = false;
  //   }
  // }

  // // only unwind if decision stack needs to be
  // int num_backtrack_steps = m_decision_stack.size() - agree_depth-1; // actual_path_size;
  // DREAL_LOG_DEBUG << "Backtracking, # steps = " << num_backtrack_steps;
  // if (// static_cast<int>(m_decision_stack.size()) > actual_path_size ||
  //     !paths_agree && num_backtrack_steps > 0) {

  //   for (int i = 0; i <  num_backtrack_steps; i++) {
  //     DREAL_LOG_INFO << "Backtracking " << i << endl;
  //     if (i == num_backtrack_steps-1) {
  //    //choose sibling of at this level if it exists
  //    int path_index_for_stack_pos = i;//((m_depth+1)*num_autom) - m_decision_stack.size()+1;
  //    // if SAT solver already chose a sibling, then choose it, otherwise take the last
  //    if (path[path_index_for_stack_pos] != -1) {
  //      DREAL_LOG_DEBUG << "Moving to back " << path[path_index_for_stack_pos];
  //      m_decision_stack.back()->second->pop_back();
  //      for (vector<int>::iterator e = m_decision_stack.back()->second->begin();
  //           e != m_decision_stack.back()->second->end(); ) {
  //        if (*e == path[path_index_for_stack_pos]) {
  //          DREAL_LOG_DEBUG << "ReMoving " << *e;
  //          m_decision_stack.back()->second->erase(e);
  //          e = m_decision_stack.back()->second->begin();
  //        } else {
  //          e++;
  //        }
  //      }
  //      m_decision_stack.back()->second->push_back(path[path_index_for_stack_pos]);
  //    } else {
  //      m_decision_stack.back()->second->pop_back();
  //      if( m_decision_stack.back()->second->empty()) {
  //        delete m_decision_stack.back()->second;
  //        delete m_decision_stack.back();
  //        m_decision_stack.pop_back();
  //      }
  //    }
  //     } else {
  //      // the parent choice was unassigned too, so this decision no longer needed
  //      delete m_decision_stack.back()->second;
  //      delete m_decision_stack.back();
  //      m_decision_stack.pop_back();
  //    }

  //     // there is only a decision to backtrack if m_decision_stack.size() > m_depth - i
  //     //if (static_cast<int>(m_decision_stack.size()) > 0) { // ((m_depth+1)*num_autom)-1 - i) {
  //    // if (i == 0) {
  //    //   // remove decision for time zero, which must be initial node
  //    //   // this is never to blame for the backtrack, but must be backtracked over
  //    //   delete m_decision_stack.back()->second;
  //    //   delete m_decision_stack.back();
  //    //   m_decision_stack.pop_back();
  //    // } else if (m_decision_stack.back() != NULL &&
  //    //         m_decision_stack.back()->second->size() > 1) {
  //    //   // there is an unexplored sibling at this level
  //    //   // remove current choice at time and choose a sibling

  //    //   int path_index_for_stack_pos = ((m_depth+1)*num_autom) - m_decision_stack.size()+1;
  //    //   // if SAT solver already chose a sibling, then choose it, otherwise take the last
  //    //   if (path[path_index_for_stack_pos] != -1) {
  //    //     DREAL_LOG_DEBUG << "Moving to back " << path[path_index_for_stack_pos];
  //    //     m_decision_stack.back()->second->pop_back();
  //    //     for (vector<int>::iterator e = m_decision_stack.back()->second->begin();
  //    //       e != m_decision_stack.back()->second->end(); ) {
  //    //       if (*e == path[path_index_for_stack_pos]) {
  //    //      DREAL_LOG_DEBUG << "ReMoving " << *e;
  //    //      m_decision_stack.back()->second->erase(e);
  //    //      e = m_decision_stack.back()->second->begin();
  //    //       } else {
  //    //      e++;
  //    //       }
  //    //     }
  //    //     m_decision_stack.back()->second->push_back(path[path_index_for_stack_pos]);
  //    //   } else {
  //    //     m_decision_stack.back()->second->pop_back();
  //    //   }
  //    //   break;
  //    // } else  {
  //    //   // the parent choice was unassigned too, so this decision no longer needed
  //    //   delete m_decision_stack.back()->second;
  //    //   delete m_decision_stack.back();
  //    //   m_decision_stack.pop_back();
  //    // }
  //     // }
  //   }
  // }

  // for (int j = static_cast<int>(path.size() - 1); j > -1; j--) {
  //   DREAL_LOG_INFO << "Path (" << j << ") = " << path[j] << endl;
  //   int stack_index_for_path_index = static_cast<int>(path.size() - j - 1);
  //   if (stack_index_for_path_index < static_cast<int>(m_decision_stack.size()))
  //     DREAL_LOG_INFO << "Stack(" << stack_index_for_path_index << ") = "
  //                 << m_decision_stack[stack_index_for_path_index]->second->back();
  //   else  {
  //     DREAL_LOG_INFO << "No choices left!";
  //   }
  // }

  return m_decision_stack.size() > 0;
}

  bool schedule_heuristic::pbacktrack() {
    DREAL_LOG_INFO << "schedule_heuristic::pbacktrack()";

    bool found_sibling = false;
    DREAL_LOG_INFO << "Starting backtrack from level " << m_decision_stack.size()
                   << " lastDecisionStackEnd = " << lastDecisionStackEnd << endl;

    while (!found_sibling && m_decision_stack.size() > 0 &&
           m_decision_stack.size() > (unsigned long)lastDecisionStackEnd) {
        DREAL_LOG_INFO << "Backtracking at level " << m_decision_stack.size() << endl;
    
	schedule_decision *decision = m_decision_stack.back();
      if(decision->second->size() <= 1) {
        delete decision->second;
        delete decision;
        m_decision_stack.pop_back();
      } else  {
        decision->second->pop_back();
	found_sibling = true;
        break;
      }
    }

    // //      int num_backtrack_steps = 1; // actual_path_size;
    // bool found_sibling = false;
    // while (!found_sibling && m_decision_stack.size() > 1) {
    //   DREAL_LOG_INFO << "Backtracking at level "
    //               << m_decision_stack.size() << endl;

    //   if (m_decision_stack.back()->second != NULL &&
    //    m_decision_stack.back()->second->size() > 1) {
    //  // there is an unexplored sibling at this level
    //  // remove current choice at time and choose a sibling
    //  m_decision_stack.back()->second->pop_back();
    //  found_sibling = true;
    //  break;
    //   } else  {
    //  // the parent choice was unassigned too, so this decision no longer needed
    //  delete m_decision_stack.back()->second;
    //  delete m_decision_stack.back();
    //  m_decision_stack.pop_back();
    //   }
    // }

    // DREAL_LOG_DEBUG << "After BT stack:";
    // int i = 0;
    // for (std::size_t time = (m_depth+1)*num_autom ;
    //   time > (m_depth+1)-m_decision_stack.size(); time--)  {
    //   DREAL_LOG_DEBUG << "Stack(" << time << ") =" << m_decision_stack[i++]->second->back();
    // }
    return m_decision_stack.size() > (unsigned long)lastDecisionStackEnd;
  }



  bool schedule_heuristic::getSuggestions()  {
    DREAL_LOG_INFO << "schedule_heuristic::getSuggestions()";
    //displayTrail();
    bool suggestion_consistent = isStackConsistentWithSuggestion();

    m_is_initialized = true;
    bool found_path = false;
    bool path_possible = true;

   if (!m_suggestions.empty() && suggestion_consistent) {
     return true;
   } else if (!suggestion_consistent || backtracked) {
     unwind_path();
   }

  lastDecisionStackEnd = m_decision_stack.size();

  bool first_expansion = true;
  while (!found_path && path_possible){
    if (path_possible){
      found_path = expand_path(first_expansion);
      first_expansion = false;
    }
    if (!found_path){
      path_possible = pbacktrack();
    }
  }
  if (m_config->nra_use_stat) { m_config->nra_stat.increase_heuristic_paths(); }

  if (m_decision_stack.size() <= (unsigned long)lastDecisionStackEnd &&
      m_decision_stack.size() < (unsigned long)num_choices_per_happening){
    DREAL_LOG_INFO << "Ran out of suggestions, subtree is unsat!";
    //generate conflict clause
    return false;
  }

 if (m_stack.size() == (unsigned int)(m_depth+1)*num_choices_per_happening){
    DREAL_LOG_INFO << "Made all the suggestions";
    return true;
  }


    completeSuggestionsForTrail();

  //  for (int time = m_depth; time >= 0; time--) {
  //    DREAL_LOG_DEBUG << "Depth = " << time;
  //      for (auto & p : *time_event_enodes[time]) {
  //        Enode* ev = p.second;
  //        // ev->setDecPolarity(l_True);
  //        m_suggestions.push_back(ev);
  //      }
  //    }

  //    for (int time = 0; time <= m_depth; time++) {
  //      for (auto & p : *time_process_enodes[time]) {
  //        Enode* proc = p.second;
  //        // proc->setDecPolarity(l_True);
  //        m_suggestions.push_back(proc);
  //      }
  //    }

  //    for (int time = 0; time <= m_depth; time++) {
  //      for (auto & p : *time_act_enodes[time]) {
  //        Enode* proc = p.second;
  //        // proc->setDecPolarity(l_True);
  //        m_suggestions.push_back(proc);
  //      }
  //    }
  //    for (int time = 0; time <= m_depth; time++) {
  //      for (auto & p : *time_duract_enodes[time]) {
  //        Enode* proc = p.second;
  //        // proc->setDecPolarity(l_True);
  //        m_suggestions.push_back(proc);
  //      }
  //    }

      //  for (auto e : m_suggestions)  {
    DREAL_LOG_INFO << "schedule_heuristic::getSuggestions(): Suggesting ";
      //                   << (e->getPolarity() == l_True ? "     " : "(not ")
      //                   << e
      //                   << (e->getPolarity() == l_True ? "" : ")")
      //                   << " = "
      //                   << (e->getDecPolarity() == l_True ?
      //                       " True" :
      //                       (e->getDecPolarity() == l_False ? " False" : " Unknown"))
      //                   << endl;
      //  }
    return true;
}

void schedule_heuristic::displayDecisions(){
  DREAL_LOG_INFO << "Decision Stack:";
  stringstream s;
  for(auto d : m_decision_stack){
    s << d << ": [";
    for(auto v : *d->second){
      s <<  v << " ";
    }
    s << "]" << endl;
  }
  DREAL_LOG_INFO << s.str();
  
}
}
