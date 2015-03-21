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
#include "plan_heuristic.h"
#include "json11/json11.hpp"
#include "opensmt/egraph/Egraph.h"
#include "opensmt/tsolvers/TSolver.h"
#include "util/logging.h"

using std::string;
using std::ifstream;
using std::unordered_set;
using std::ios;
using std::sort;

namespace dreal{

  extern string get_file_contents(const char* filename);
  extern int get_mode(Enode* e);

  void plan_heuristic::initialize(SMTConfig & c, Egraph & egraph, THandler* thandler, vec<Lit> *trl, vec<int> *trl_lim)  {
    DREAL_LOG_INFO << "plan_heuristic::initialize() " << (thandler == NULL);
    m_egraph = &egraph;
    theory_handler = thandler;
    trail = trl;
    trail_lim = trl_lim;
    m_is_initialized = false; //   Have we computed suggestions yet?  Does not happen here.
    if (c.nra_plan_heuristic.compare("") != 0){
        const string heuristic_string = get_file_contents(c.nra_plan_heuristic.c_str());
        string err;
        auto json = json11::Json::parse(heuristic_string, err);
        //  auto hinfo = json.array_items();


       //   BMC depth
        m_depth = json["steps"].int_value();
        DREAL_LOG_INFO << "plan_heuristic::initialize() #steps = " << m_depth;


        //   get acts
        for (auto a : json["actions"].array_items()){
          m_actions.push_back(a.string_value());
          DREAL_LOG_INFO << "plan_heuristic::initialize() Action = " << a.string_value();
        }

        //   get events
        for (auto a : json["events"].array_items()){
          m_events.push_back(a.string_value());
          DREAL_LOG_INFO << "plan_heuristic::initialize() Event = " << a.string_value();
        }

        //   get processes
        for (auto a : json["processes"].array_items()){
          m_processes.push_back(a.string_value());
          DREAL_LOG_INFO << "plan_heuristic::initialize() Process = " << a.string_value();
        }

        //   get durative_acts
        for (auto a : json["durative_actions"].array_items()){
          m_durative_actions.push_back(a.string_value());
          DREAL_LOG_INFO << "plan_heuristic::initialize() Durative Action = " << a.string_value();
        }

        for (int i = 0; i < m_depth+1; i++){
          map< string, Enode* > * en = new map< string, Enode* >();
          time_process_enodes.push_back(en);

          en = new map< string, Enode* >();
          time_event_enodes.push_back(en);

          en = new map< string, Enode* >();
          time_act_enodes.push_back(en);

          en = new map< string, Enode* >();
          time_duract_enodes.push_back(en);
        }

        time_enodes.assign(static_cast<int>(m_depth+1), NULL);
    }
}

void plan_heuristic::inform(Enode * e){
  if (m_atoms.find(e) != m_atoms.end())
    return;
  m_atoms.insert(e);

  //  DREAL_LOG_INFO << "plan_heuristic::inform(): " << e << endl;
  if (!e->isTAtom() && !e->isNot()){
    unordered_set<Enode *> const & vars = e->get_vars();
    unordered_set<Enode *> const & consts = e->get_constants();
    for (auto const & v : vars) {
      stringstream ss;
      ss << v;
      string var = ss.str();
      if (var.find("process") != string::npos) {
        int time = atoi(var.substr(var.find_last_of("_")+1).c_str());
        int spos = var.find_first_of("_")+1;
        int epos = var.find_last_of("_")-1;
        string proc = var.substr(spos, epos-spos).c_str();

        //  for (auto const & c : consts) {
        //    stringstream css;
        //    css << c;
        //    int cs = atoi(css.str().c_str());
        //    if (cs == 1){
            DREAL_LOG_INFO << "process = " << proc << " time = " << time << endl;
            (*time_process_enodes[time])[proc] = e;
            process_enodes.insert(e);
            //          }
            //         }
      } else  if (var.find("event") != string::npos) {
        int time = atoi(var.substr(var.find_last_of("_")+1).c_str());
        int spos = var.find_first_of("_")+1;
        int epos = var.find_last_of("_")-1;
        string proc = var.substr(spos, epos-spos).c_str();

        //  for (auto const & c : consts) {
        //    stringstream css;
        //    css << c;
        //    int cs = atoi(css.str().c_str());
        //    if (cs == 1){
            DREAL_LOG_INFO << "event = " << proc << " time = " << time << endl;
            (*time_event_enodes[time])[proc] = e;
            event_enodes.insert(e);
        //    }
        //  }
      } else  if (var.find("act") == 0) {
        int time = atoi(var.substr(var.find_last_of("_")+1).c_str());
        int spos = var.find_first_of("_")+1;
        int epos = var.find_last_of("_")-1;
        string proc = var.substr(spos, epos-spos).c_str();

        //  for (auto const & c : consts) {
        //    stringstream css;
        //    css << c;
        //    int cs = atoi(css.str().c_str());
        //    if (cs == 1){
            DREAL_LOG_INFO << "action = " << proc << " time = " << time << endl;
            (*time_act_enodes[time])[proc] = e;
            act_enodes.insert(e);
        //    }
        //  }
      } else  if (var.find("duract") == 0) {
        int time = atoi(var.substr(var.find_last_of("_")+1).c_str());
        int spos = var.find_first_of("_")+1;
        int epos = var.find_last_of("_")-1;
        string proc = var.substr(spos, epos-spos).c_str();

        //  for (auto const & c : consts) {
        //    stringstream css;
        //    css << c;
        //    int cs = atoi(css.str().c_str());
        //    if (cs == 1){
            DREAL_LOG_INFO << "durative action = " << proc << " time = " << time << endl;
            (*time_duract_enodes[time])[proc] = e;
            duract_enodes.insert(e);
        //    }
        //  }
      }
    }
  } else if (e->isEq()){
    unordered_set<Enode *> const & vars = e->get_vars();
    unordered_set<Enode *> const & consts = e->get_constants();
    for (auto const & v : vars) {
      stringstream ss;
      ss << v;
      string var = ss.str();
      if (var.find("time") != string::npos) {
        int time = atoi(var.substr(var.find_last_of("_")+1).c_str());
        for (auto const & c : consts) {
          stringstream css;
          css << c;
          int cs = atoi(css.str().c_str());
          if (cs == 0){ //  only care about assinging time if wait is possible
            DREAL_LOG_INFO << "time time = " << time << endl;
            time_enodes[time] = e;
          }
        }
      }
    }
  }
}

  // Lit plan_heuristic::getSuggestion(){
  //   DREAL_LOG_INFO << "plan_heuristic::getSuggestion()";
  //   if (!m_is_initialized || m_suggestions.empty()){
  //     getSuggestions();
  //   }
  //   if (!m_suggestions.empty()){
  //     std::pair<Enode *, bool> *s = m_suggestions.back();
  //     m_suggestions.pop_back();
  //     Enode *e = s->first;


  //   if ( e == NULL )
  //     return lit_Undef;



  //   DREAL_LOG_INFO << "plan_heuristic::getSuggestion() " << e;
  //   if (theory_handler == NULL)
  //     DREAL_LOG_INFO << "plan_heuristic::getSuggestion() NULL";
  //   Var v = theory_handler->enodeToVar(e);
  //   delete s;
  //   return Lit( v, !s->second );
  //   } else {
  //     return lit_Undef;
  //   }
  // }

  void plan_heuristic::backtrack(){
    DREAL_LOG_DEBUG << "plan_heuristic::backtrack()";
    m_suggestions.clear();
    lastTrailEnd = trail->size();

    for (int i = m_stack.size(); i > (trail->size()-2); i--){
      std::pair<Enode *, bool> *s = m_stack.back();
      m_stack.pop_back();
      stack_literals.erase(s->first);
      delete s;
      lastTrailEnd--;
    }
    // displayTrail();
  }

  void plan_heuristic::assertLits(){
    DREAL_LOG_DEBUG << "plan_heuristic::assertLits()";
    displayTrail();
    getSuggestions();
  }

  void plan_heuristic::displayTrail(){
    int indx_low = 0;
    int indx_high;
    DREAL_LOG_INFO << "Trail size = " << trail->size();
    for (int level = 0; level <= trail_lim->size(); level++){
      if (level > 0){
        indx_low = (*trail_lim)[level-1];
      }
      indx_high = (*trail_lim)[level];

      DREAL_LOG_INFO << " -- LEVEL " << level << " (" << indx_low << ", " << indx_high << ") -- ";
      for (int i = indx_low; i <= indx_high; i++){
        // DREAL_LOG_INFO << i << " " << var((*trail)[i]);
        if (var((*trail)[i]) > 1) // 0 and 1 are false and true
          DREAL_LOG_INFO << theory_handler->varToEnode(var((*trail)[i]));
      }
    }
  }

  void plan_heuristic::pushTrailOnStack(){
    DREAL_LOG_INFO << "plan_heuristic::pushTrailOnStack() lastTrailEnd = "
                   << lastTrailEnd << " trail->size() = " << trail->size();
    for (int i = lastTrailEnd; i < trail->size(); i++){
      Enode *e = theory_handler->varToEnode(var((*trail)[i]));
      bool msign = sign((*trail)[i]);
      //   DREAL_LOG_INFO << "plan_heuristic::pushTrailOnStack() " << e;
      if (process_enodes.find(e) != process_enodes.end()){
        DREAL_LOG_INFO << "plan_heuristic::pushTrailOnStack() " << e << " " << msign;
        m_stack.push_back(new std::pair<Enode *, bool>(e, msign));
        stack_literals.insert(e);
      } else if (event_enodes.find(e) != event_enodes.end()){
        DREAL_LOG_INFO << "plan_heuristic::pushTrailOnStack() " << e << " " << msign;
        m_stack.push_back(new std::pair<Enode *, bool>(e, msign));
        stack_literals.insert(e);
      } else if (act_enodes.find(e) != act_enodes.end()){
        DREAL_LOG_INFO << "plan_heuristic::pushTrailOnStack() " << e << " " << msign;
        m_stack.push_back(new std::pair<Enode *, bool>(e, msign));
        stack_literals.insert(e);
      } else if (duract_enodes.find(e) != duract_enodes.end()){
        DREAL_LOG_INFO << "plan_heuristic::pushTrailOnStack() " << e << " " << msign;
        m_stack.push_back(new std::pair<Enode *, bool>(e, msign));
        stack_literals.insert(e);
      }
    }
    lastTrailEnd = trail->size();
  }

  void plan_heuristic::completeSuggestionsForTrail(){
    for (int time = m_depth; time >= 0; time--){
      DREAL_LOG_INFO << "plan_heuristic::completeSuggestionsForTrail() time = " << time;
      // suggest processes
      map<string, Enode*> *process_at_time = time_process_enodes[time];
      for (auto p : *process_at_time){
        if (stack_literals.find(p.second) == stack_literals.end()){
          DREAL_LOG_INFO << "plan_heuristic::completeSuggestionsForTrail() suggesting = " << p.second;
          // p.second->setDecPolarity(true);
          m_stack.push_back(new std::pair<Enode *, bool>(p.second, true));
          m_suggestions.push_back(new std::pair<Enode *, bool>(p.second, true));
        }
      }

      // suggest events
      map<string, Enode*> *event_at_time = time_event_enodes[time];
      for (auto p : *event_at_time){
        if (stack_literals.find(p.second) == stack_literals.end()){
          DREAL_LOG_INFO << "plan_heuristic::completeSuggestionsForTrail() suggesting = " << p.second;
          // p.second->setDecPolarity(false);
          m_stack.push_back(new std::pair<Enode *, bool>(p.second, false));
          m_suggestions.push_back(new std::pair<Enode *, bool>(p.second, false));
        }
      }

      // suggest acts
      map<string, Enode*> *act_at_time = time_act_enodes[time];
      for (auto p : *act_at_time){
        if (stack_literals.find(p.second) == stack_literals.end()){
          DREAL_LOG_INFO << "plan_heuristic::completeSuggestionsForTrail() suggesting = " << p.second;
          // p.second->setDecPolarity(true);
          m_stack.push_back(new std::pair<Enode *, bool>(p.second, true));
          m_suggestions.push_back(new std::pair<Enode *, bool>(p.second, true));
        }
      }


      // suggest duracts
      map<string, Enode*> *duract_at_time = time_duract_enodes[time];
      for (auto p : *duract_at_time){
        if (stack_literals.find(p.second) == stack_literals.end()){
          DREAL_LOG_INFO << "plan_heuristic::completeSuggestionsForTrail() suggesting = " << p.second;
          // p.second->setDecPolarity(true);
          m_stack.push_back(new std::pair<Enode *, bool>(p.second, true));
          m_suggestions.push_back(new std::pair<Enode *, bool>(p.second, true));
        }
      }
    }
  }


  void plan_heuristic::getSuggestions() {
    if (!m_suggestions.empty()){
      return;
    }
    DREAL_LOG_INFO << "plan_heuristic::getSuggestions()";

    m_is_initialized = true;


    if (trail->size() > lastTrailEnd)
      pushTrailOnStack();

    completeSuggestionsForTrail();

  //  for (int time = m_depth; time >= 0; time--){
  //    DREAL_LOG_DEBUG << "Depth = " << time;
  //      for (auto & p : *time_event_enodes[time]){
  //        Enode* ev = p.second;
  //        // ev->setDecPolarity(l_True);
  //        m_suggestions.push_back(ev);
  //      }
  //    }

  //    for (int time = 0; time <= m_depth; time++){
  //      for (auto & p : *time_process_enodes[time]){
  //        Enode* proc = p.second;
  //        // proc->setDecPolarity(l_True);
  //        m_suggestions.push_back(proc);
  //      }
  //    }

  //    for (int time = 0; time <= m_depth; time++){
  //      for (auto & p : *time_act_enodes[time]){
  //        Enode* proc = p.second;
  //        // proc->setDecPolarity(l_True);
  //        m_suggestions.push_back(proc);
  //      }
  //    }
  //    for (int time = 0; time <= m_depth; time++){
  //      for (auto & p : *time_duract_enodes[time]){
  //        Enode* proc = p.second;
  //        // proc->setDecPolarity(l_True);
  //        m_suggestions.push_back(proc);
  //      }
  //    }

      //  for (auto e : m_suggestions) {
    DREAL_LOG_INFO << "plan_heuristic::getSuggestions(): Suggesting ";
      //                   << (e->getPolarity() == l_True ? "     " : "(not ")
      //                   << e
      //                   << (e->getPolarity() == l_True ? "" : ")")
      //                   << " = "
      //                   << (e->getDecPolarity() == l_True ?
      //                       " True" :
      //                       (e->getDecPolarity() == l_False ? " False" : " Unknown"))
      //                   << endl;
      //  }
}
}
