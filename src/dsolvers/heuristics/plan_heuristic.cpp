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
#include "dsolvers/heuristics/plan_heuristic.h"
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

  void plan_heuristic::initialize(SMTConfig & c, Egraph & egraph)  {
    m_egraph = &egraph;
    m_is_initialized = false; //  Have we computed suggestions yet?  Does not happen here.
    if (c.nra_plan_heuristic.compare("") != 0){
        const string heuristic_string = get_file_contents(c.nra_plan_heuristic.c_str());
        string err;
        auto json = json11::Json::parse(heuristic_string, err);
        // auto hinfo = json.array_items();


       //  BMC depth
        m_depth = json["steps"].int_value();
        DREAL_LOG_INFO << "plan_heuristic::initialize() #steps = " << m_depth;


        //  get acts
        for (auto a : json["actions"].array_items()){
          m_actions.push_back(a.string_value());
          DREAL_LOG_INFO << "plan_heuristic::initialize() Action = " << a.string_value();
        }

        //  get events
        for (auto a : json["events"].array_items()){
          m_events.push_back(a.string_value());
          DREAL_LOG_INFO << "plan_heuristic::initialize() Event = " << a.string_value();
        }

        //  get processes
        for (auto a : json["processes"].array_items()){
          m_processes.push_back(a.string_value());
          DREAL_LOG_INFO << "plan_heuristic::initialize() Process = " << a.string_value();
        }

        //  get durative_acts
        for (auto a : json["durative_actions"].array_items()){
          m_durative_actions.push_back(a.string_value());
          DREAL_LOG_INFO << "plan_heuristic::initialize() Durative Action = " << a.string_value();
        }

        for (int i = 0; i < m_depth+1; i++){
          map< string, Enode* > * en = new map< string, Enode* >();
          time_process_enodes.push_back(en);
        }

        for (int i = 0; i < m_depth+1; i++){
          map< string, Enode* > * en = new map< string, Enode* >();
          time_event_enodes.push_back(en);
        }

        time_enodes.assign(static_cast<int>(m_depth+1), NULL);
    }
}

void plan_heuristic::inform(Enode * e){
  DREAL_LOG_INFO << "plan_heuristic::inform(): " << e << endl;
  if (e->isEq()){
    unordered_set<Enode *> const & vars = e->get_vars();
    unordered_set<Enode *> const & consts = e->get_constants();
    for (auto const & v : vars) {
      stringstream ss;
      ss << v;
      string var = ss.str();
      if (var.find("process") != string::npos) {
        int time = atoi(var.substr(var.find_last_of("_")+1).c_str());
        int spos = var.find_first_of("_")+1;
        int epos = var.find_last_of("_");
        string proc = var.substr(spos, epos-spos).c_str();

        for (auto const & c : consts) {
          stringstream css;
          css << c;
          int cs = atoi(css.str().c_str());
          if (cs == 1){
            DREAL_LOG_INFO << "process = " << proc << " time = " << time << endl;
            (*time_process_enodes[time])[proc] = e;
          }
        }
      } else  if (var.find("event") != string::npos) {
        int time = atoi(var.substr(var.find_last_of("_")+1).c_str());
        int spos = var.find_first_of("_")+1;
        int epos = var.find_last_of("_");
        string proc = var.substr(spos, epos-spos).c_str();

        for (auto const & c : consts) {
          stringstream css;
          css << c;
          int cs = atoi(css.str().c_str());
          if (cs == 1){
            DREAL_LOG_INFO << "event = " << proc << " time = " << time << endl;
            (*time_event_enodes[time])[proc] = e;
          }
        }
      } else if (var.find("time") != string::npos) {
        int time = atoi(var.substr(var.find_last_of("_")+1).c_str());
        for (auto const & c : consts) {
          stringstream css;
          css << c;
          int cs = atoi(css.str().c_str());
          if (cs == 0){ // only care about assinging time if wait is possible
            DREAL_LOG_INFO << "time time = " << time << endl;
            time_enodes[time] = e;
          }
        }
      }
    }
  }
}

void plan_heuristic::getSuggestions(vector< Enode * > & suggestions, scoped_vec & m_stack) {
  DREAL_LOG_INFO << "plan_heuristic::getSuggestions()";
    if (m_suggestions.size() > 0){
        suggestions.assign(m_suggestions.begin(), m_suggestions.end());
        return;
    }

    m_is_initialized = true;


  for (int time = m_depth; time >= 0; time--){
      for (auto & p : *time_event_enodes[time]){
        Enode* ev = p.second;
        ev->setDecPolarity(l_True);
        suggestions.push_back(ev);
      }
    }

    for (int time = 0; time <= m_depth; time++){
      for (auto & p : *time_process_enodes[time]){
        Enode* proc = p.second;
        proc->setDecPolarity(l_True);
        suggestions.push_back(proc);
      }
    }




      for (auto e : suggestions) {
        DREAL_LOG_INFO << "plan_heuristic::getSuggestions(): Suggesting "
                       << (e->getPolarity() == l_True ? "     " : "(not ")
                       << e
                       << (e->getPolarity() == l_True ? "" : ")")
                       << " = "
                       << (e->getDecPolarity() == l_True ?
                           " True" :
                           (e->getDecPolarity() == l_False ? " False" : " Unknown"))
                       << endl;
      }

      m_suggestions.assign(suggestions.begin(), suggestions.end());
}
}
