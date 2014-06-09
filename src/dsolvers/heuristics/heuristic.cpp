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

#include <float.h>
#include <stdlib.h>
#include <utility>
#include <sstream>
#include <string>
#include <unordered_set>
#include "opensmt/egraph/Egraph.h"
#include "opensmt/tsolvers/TSolver.h"
#include "util/logging.h"
#include "dsolvers/heuristics/heuristic.h"
#include "json11.hpp"

namespace dreal{
  std::string get_file_contents(const char *filename) {
    std::ifstream in(filename, std::ios::in | std::ios::binary);
    if (in) {
      std::string contents;
      in.seekg(0, std::ios::end);
      contents.resize(in.tellg());
      in.seekg(0, std::ios::beg);
      in.read(&contents[0], contents.size());
      in.close();
      return(contents);
    }
    throw(errno);
  }

  // Get mode index in literal assignment
  int get_mode(Enode * lit) {
    std::unordered_set<Enode *> const & vars = lit->get_constants();
    for (auto const & v : vars) {
      stringstream ss;
      ss << v;
      string var = ss.str();
      int index = atoi(var.c_str());
      return static_cast<int>(index);
    }
    return -1;
  }

  void heuristic::initialize(SMTConfig & c){
    m_is_initialized = false; // Have we computed suggestions yet?  Does not happen here.
    if (c.nra_bmc_heuristic.compare("") != 0){
      const string heuristic_string = get_file_contents(c.nra_bmc_heuristic.c_str());
      string err;
      auto json = json11::Json::parse(heuristic_string, err);
      auto hinfo = json.array_items();

      // get init
      m_init_mode = hinfo[0].array_items()[0].int_value();

      // BMC depth
      m_depth = hinfo[0].array_items()[2].int_value();

      DREAL_LOG_INFO << "Init = " << m_init_mode << " Steps = " << m_depth << endl;

      // get goals
      for (auto g : hinfo[0].array_items()[1].array_items()){
        m_goal_modes.push_back(g.int_value());
      }
      for (auto g : m_goal_modes){
        DREAL_LOG_INFO << "Goal: " << g << endl;
      }


      // get mode costs
      m_cost.assign(hinfo[1].object_items().size(), 0.0);
      for (auto object :  hinfo[1].object_items()){
        m_cost[atoi(object.first.c_str())-1] = atof(object.second.dump().substr(1, object.second.dump().size()-1).c_str());
      }

      // build reverse adjanceny map (succ -> set(predecessors))
      for (unsigned int i = 0; i < hinfo[2].array_items().size(); i++){
        predecessors.push_back(new set< int > ());
      }
      int from = 1;
      for (auto adj :  hinfo[2].array_items()){
        for (auto a : adj.array_items()) {
          int to = atoi(a.dump().c_str());
          predecessors[to-1]->insert (from);
        }
        from++;
      }

      // initialize decision stack
      vector<int> *dec = new vector<int>();

      dec->insert(dec->begin(), m_goal_modes.begin(), m_goal_modes.end());
      std::sort (dec->begin(), dec->end(), SubgoalCompare(*this));
      m_decision_stack.push_back(dec);

      // complete_decision_stack_path();

      for (int i = 0; i < m_depth+1; i++){
        vector< Enode* > * en = new vector< Enode* >();
        en->assign(static_cast<int>(predecessors.size()), NULL);
        time_mode_enodes.push_back(en);
      }
    }
  }

  void heuristic::inform(Enode * e){
    DREAL_LOG_INFO << "heuristic::inform(): " << e << endl;
    std::unordered_set<Enode *> const & vars = e->get_vars();
    for (auto const & v : vars) {
      stringstream ss;
      ss << v;
      string var = ss.str();
      if (var.find("mode") != string::npos) {
        int time = atoi(var.substr(var.find("_")+1).c_str());
        int mode = get_mode(e);
        // DREAL_LOG_INFO << "mode = " << mode << " time = " << time << endl;
        mode_literals[ e ] = new pair<int, int>(mode, time);
        // DREAL_LOG_INFO << "Mode_lit[" << e << "] = " << mode << " " << time << endl;
        (*time_mode_enodes[time])[mode-1] = e;
      }
    }
  }


  // Assume that m_decision_stack matches m_stack
  // and need to suggest next decision
  bool heuristic::expand_path(scoped_vec & m_stack){
    DREAL_LOG_INFO << "heuristic::expand_path()" << endl;

    // cannot expand path if out of choices
    if (m_decision_stack.size() == 0)
      return false;

    int steps_to_add = m_depth-static_cast<int>(m_decision_stack.size())+1;
    DREAL_LOG_INFO << "Adding #steps: " << steps_to_add << endl;
    for (int i = 0; i < steps_to_add; i++){
      int time = m_depth - static_cast<int>(m_decision_stack.size());



      vector<int> * current_decision = new vector<int>();
      int parent = m_decision_stack.back()->back();

      DREAL_LOG_INFO << "Adding decision at time " << time  << " to reach " << parent << endl;

      set<int> * preds = predecessors[parent-1];
      current_decision->insert(current_decision->begin(), preds->begin(), preds->end());

      set<int> current_decision_copy (current_decision->begin(), current_decision->end());
      // prune out choices that are negated in m_stack
      for (auto e : m_stack) {
        if (e->getPolarity() != l_True){
          //      DREAL_LOG_INFO << "Checking removal of " << e << endl;
          auto p = mode_literals.find(e);
          if (p != mode_literals.end()){
            // DREAL_LOG_INFO << "Removing negated " << p->second->first << endl;
            if (p->second->second == time){
              DREAL_LOG_INFO << "Removing negated " << p->second->first << endl;
              auto e = current_decision_copy.find(p->second->first);
              if (e != current_decision_copy.end()){
                current_decision_copy.erase(e);
              }
            }
          }
        }
      }

      // remove choices that are too costly for time
      for (auto c : *current_decision) {
        if (m_cost[ c-1 ] > time) {
          DREAL_LOG_INFO << "Removing too costly " << c << endl;
          auto e = current_decision_copy.find(c);
          if (e != current_decision_copy.end()){
            current_decision_copy.erase(e);
          }
        }
      }

      current_decision->clear();
      current_decision->insert(current_decision->begin(), current_decision_copy.begin(), current_decision_copy.end());

      if (current_decision->size() == 0){
        DREAL_LOG_INFO << "No decisions left at time " << time << endl;
        return false;
      }

      std::sort (current_decision->begin(), current_decision->end(), SubgoalCompare(*this));

      m_decision_stack.push_back(current_decision);

      for (auto d : *current_decision){
        DREAL_LOG_INFO << "dec = " << d << endl;
      }
    }

    return static_cast<int>(m_decision_stack.size()) == m_depth + 1; // successfully found a full path
  }





  // Get the literal for assigning mode at time
  // side effect is to set the last_decision (a branch point to continue)
  Enode * getLiteral(int mode, int time, scoped_vec & m_literals){
    for (auto e : m_literals){
      std::unordered_set<Enode *> const & vars = e->get_vars();
      for (auto const & v : vars) {
        stringstream ss;
        ss << v;
        string var = ss.str();
        if (var.find("mode") != string::npos) {
          int t = atoi(var.substr(var.find("_")+1).c_str());
          int m = get_mode(e);
          if (m == mode && time == t){
            return e;
          }
        }
      }
    }
    return NULL;
  }



  bool mode_literal_compare (Enode *  i, Enode *  j) {
    // order positive literals first
    return (i->getDecPolarity() == l_False && j->getDecPolarity() != l_False);
  }


  // backtrack the path.  The SMT solver path may be less defined than here
  // because it backtracked much further.  In next set of assignments, the SMT
  // solver will reconstruct parts of this path
  bool heuristic::unwind_path(scoped_vec & m_stack) {
    vector<int> path;
    path.assign(m_depth+1, -1);
    for (auto e : m_stack) {
      DREAL_LOG_INFO << "Checking path " << (e->getDecPolarity() == l_True ? "     " : "(not ")
                     << e
                     << (e->getDecPolarity() == l_True ? "" : ")") << endl;

      if (e->getPolarity() == l_True){
        auto i = mode_literals.find(e);
        if (i != mode_literals.end()){
          path[(*i).second->second] = (*i).second->first;
        }
      }
    }

    int j = 0;
    for (auto p : path) {
      DREAL_LOG_INFO << "Path(" << j++ << ") = " << p << endl;
    }
    j = 0;
    for (auto d : m_decision_stack){
      DREAL_LOG_INFO << "Stack(" << j++ << ") = " << d->back() << endl;
    }

    // only unwind if decision stack needs to be
    if (m_decision_stack.size() > 1){
      for (int i = 0; i < static_cast<int>(path.size()); i++){
        DREAL_LOG_INFO << "Backtracking at time " << i << endl;

        // there is only a decision to backtrack if m_decision_stack.size() > m_depth - i
        if (static_cast<int>(m_decision_stack.size()) > m_depth - i){
          if (i == 0){
            // remove decision for time zero, which must be initial node
            // this is never to blame for the backtrack, but must be backtracked over
            delete m_decision_stack.back();
            m_decision_stack.pop_back();
          } else if (m_decision_stack.back() != NULL &&
                   m_decision_stack.back()->size() > 1){
            // there is an unexplored sibling at this level
            // remove current choice at time and choose a sibling
            m_decision_stack.back()->pop_back();
            break;
          } else {
            // the parent choice was unassigned too, so this decision no longer needed
            delete m_decision_stack.back();
            m_decision_stack.pop_back();
          }
        }
      }
    }
    return m_decision_stack.size() > 0;
  }

  // unwind current current path to match stack
  // complete path
  // make suggestions for path
  void heuristic::getSuggestions(vector< Enode * > & suggestions, scoped_vec & m_stack) {
    if (m_suggestions.size() > 0){
      suggestions.assign(m_suggestions.begin(), m_suggestions.end());
      return;
    }

    m_is_initialized = true;

    bool found_path = false;
    bool path_possible = true;
    while (!found_path && path_possible){
      path_possible = unwind_path(m_stack);
      if (path_possible){
        found_path = expand_path(m_stack);
      }
    }

    DREAL_LOG_INFO << "Generating suggestions " << m_depth << " " << m_decision_stack.size() << endl;
    if (m_decision_stack.size() == 0)
      return;

    for (int time = m_depth - m_decision_stack.size()+1; time <= m_depth; time++) {
      DREAL_LOG_INFO << "Suggesting at time " << time << endl;
      int mode = m_decision_stack[m_depth-time]->back();
      DREAL_LOG_INFO << "mode = " << mode << endl;
      Enode * s = (*time_mode_enodes[time])[mode-1];
      DREAL_LOG_INFO << "enode = " << s << endl;
      if (!s->hasPolarity() && !s->isDeduced()){
        s->setDecPolarity(l_True);
        suggestions.push_back(s);
        DREAL_LOG_INFO << "Suggested Pos: " << s << endl;
      }

      if (time_mode_enodes[time]->size() > 0){
        for (int i = 0; i < static_cast<int>(predecessors.size()); i++){
          if (i != mode - 1){
            s = (*time_mode_enodes[time])[i];
            if (s && !s->hasPolarity() && !s->isDeduced()){
              s->setDecPolarity(l_False);
              suggestions.push_back(s);
              DREAL_LOG_INFO << "Suggested Neg: " << s << endl;
            }
          }
        }
      }
    }

    for (auto e : suggestions) {
      DREAL_LOG_INFO << "heuristic::getSuggestions(): Suggesting "
                     << (e->getDecPolarity() == l_True ? "     " : "(not ")
                     << e
                     << (e->getDecPolarity() == l_True ? "" : ")") << endl;
    }

    m_suggestions.assign(suggestions.begin(), suggestions.end());

    int i = 0;
    for (auto d : m_decision_stack){
      DREAL_LOG_INFO << "Decision Stack(" << i++ << ") = " << endl;
      for (auto d1 : (*d))
        DREAL_LOG_INFO << d1 << endl;
    }
  }
}
