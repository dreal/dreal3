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
#include "hybrid_heuristic.h"
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
string get_file_contents(const char *filename) {
    ifstream in(filename, ios::in | ios::binary);
    if (in) {
        string contents;
        in.seekg(0, ios::end);
        contents.resize(in.tellg());
        in.seekg(0, ios::beg);
        in.read(&contents[0], contents.size());
        in.close();
        return(contents);
    }
    throw(errno);
}

// Get mode index in literal assignment
int get_mode(Enode * lit) {
    unordered_set<Enode *> const & vars = lit->get_constants();
    for (auto const & v : vars) {
        stringstream ss;
        ss << v;
        string var = ss.str();
        int index = atoi(var.c_str());
        return static_cast<int>(index);
    }
    return -1;
}
  
  void hybrid_heuristic::initialize(SMTConfig & c, Egraph & egraph, THandler* thandler,
				    vec<Lit> *trl, vec<int> *trl_lim)  {
    DREAL_LOG_DEBUG << "hybrid_heuristic::initialize()";
    m_egraph = &egraph;
    theory_handler = thandler;
    trail = trl;
    trail_lim = trl_lim;
    m_is_initialized = true; // Have we computed suggestions yet?  Does not happen here.
    if (c.nra_bmc_heuristic.compare("") != 0){ 
      const string heuristic_string = get_file_contents(c.nra_bmc_heuristic.c_str());
      string err;
      auto hinfo = json11::Json::parse(heuristic_string, err);
      //auto hinfo = json.array_items();
      auto init_list = hinfo[0][0];
      auto goal_list = hinfo[0][1];

   
      // get init
      for(auto i : init_list.array_items()){
	m_init_mode.push_back(i.int_value());
      }

      // BMC depth
      m_depth = hinfo[0][2].int_value();

      // DREAL_LOG_INFO << "Init = " << m_init_mode << " Steps = " << m_depth << endl;
      num_autom = hinfo[0][0].array_items().size();
      
      // get goals
      for (auto gs : goal_list.array_items()){
	vector<int> *mg = new vector<int>();
	for (auto g : gs.array_items()){
	  mg->push_back(g.int_value());
	}
	m_goal_modes.push_back(mg);
      }

      // get mode costs
      for(auto i : hinfo[1].array_items()){
	vector<double> *mc = new vector<double>();
	mc->assign(i.object_items().size(), 0.0);
	for (auto object :  i.object_items()){
	  (*mc)[atoi(object.first.c_str())-1] = atof(object.second.dump().substr(1, object.second.dump().size()-1).c_str());
	  DREAL_LOG_DEBUG << (atoi(object.first.c_str())-1) << " = " << (*mc)[atoi(object.first.c_str())-1];
	}
	m_cost.push_back(mc);
      }
      for(auto j : hinfo[2].array_items()){
	// build reverse adjanceny map (succ -> set(predecessors))
	vector<set<int>*>* mp = new vector<set<int>*>();
	for (unsigned int i = 0; i < j.array_items().size(); i++){
            mp->push_back(new set< int > ());
	}
	int from = 1;
	for (auto adj :  j.array_items()){
	  for (auto a : adj.array_items()) {
	    int to = atoi(a.dump().c_str());
	    (*mp)[to-1]->insert(from);
	  }
	  from++;
	}
	predecessors.push_back(mp);


      }

	// initialize decision stack
	pair<int, vector<int>*>* astack = new pair<int, vector<int>*>();
	m_decision_stack.push_back(astack);

	vector<int> *dec = new vector<int>();
	dec->insert(dec->begin(), m_goal_modes[0]->begin(), m_goal_modes[0]->end());

	sort (dec->begin(), dec->end(), SubgoalCompare(0, *this));
	astack->first = 0;
	astack->second = dec;
	


	for(int a = 0; a < num_autom; a++){
	  mode_literals.push_back(new map<Enode*, pair<int,int>*>());

	  vector<vector<Enode*>*>* tme = new vector<vector<Enode*>*>();
	  vector<vector<Enode*>*>* tmi = new vector<vector<Enode*>*>();
	  time_mode_enodes.push_back(tme);
	  time_mode_integral_enodes.push_back(tmi);
	  for (int i = 0; i < m_depth+1; i++){
	    vector< Enode* > * en = new vector< Enode* >();
	    en->assign(static_cast<int>(predecessors[a]->size()), NULL);
	    tme->push_back(en);
	    // if (m_egraph->stepped_flows){
	    en = new vector< Enode* >();
	    en->assign(static_cast<int>(predecessors.size()), NULL);
	    tmi->push_back(en);
	    // }
	  }
	}

    }
}


void hybrid_heuristic::inform(Enode * e){

    if (e->isEq() && !e->isNot()){
    DREAL_LOG_INFO << "hybrid_heuristic::inform(): " << e << endl;
    unordered_set<Enode *> const & vars = e->get_vars();
    bool found_mode_literal = false;
    for (auto const & v : vars) {
        stringstream ss;
        ss << v;
        string var = ss.str();
        if (var.find("mode") != string::npos) {
	  int autom_pos = var.find("_")+1;
	  int time_pos = var.rfind("_")+1;
	  int time = atoi(var.substr(time_pos).c_str());
	  int autom = (predecessors.size() == 1 ? 
		       0 : 
		       atoi(var.substr(autom_pos, time_pos-1).c_str()));
	  int mode = get_mode(e);

	  DREAL_LOG_INFO << "autom = " << autom << " mode = " << mode << " time = " << time << endl;
	  (*mode_literals[autom-1])[ e ] = new pair<int, int>(mode, time);
	  DREAL_LOG_INFO << "Mode_lit[" <<  (e->getPolarity() == l_True ? "     " : "(not ")
			 << e
			 << (e->getPolarity() == l_True ? "" : ")")
			 << "] = " << mode << " " << time << endl;

	  (*(*time_mode_enodes[autom-1])[time])[mode-1] = e;
	  found_mode_literal = true;
	  mode_enodes.insert(e);
        }
    }
    if (!found_mode_literal){
      // add to default false suggestions
      default_false_suggestions.push_back(e);
    }
  // } else if (e->isIntegral() && m_egraph->stepped_flows){
  //   int m_mode = static_cast<int>(e->getCdr()->getCar()->getValue());
  //   DREAL_LOG_DEBUG << "mode = " << m_mode;
  //   Enode* m_time = e->getCdr()->getCdr()->getCdr()->getCar();
  //   string time_str = m_time->getCar()->getName();                       // i.e. "time_1"
  //   int m_step = stoi(time_str.substr(time_str.find_last_of("_") + 1));      // i.e. 1
  //   DREAL_LOG_DEBUG << "step = " << m_step;
  //   (*time_mode_integral_enodes[m_step])[m_mode-1] = e;
  // } else if (e->isIntegral() && !m_egraph->stepped_flows){
  //   int m_mode = static_cast<int>(e->getCdr()->getCar()->getValue());
  //   DREAL_LOG_DEBUG << "mode = " << m_mode;
  //   // Enode* m_time = e->getCdr()->getCdr()->getCdr()->getCar();
  //   // string time_str = m_time->getCar()->getName();                       // i.e. "time_1"
  //   // int m_step = stoi(time_str.substr(time_str.find_last_of("_") + 1));      // i.e. 1
  //   // DREAL_LOG_DEBUG << "step = " << m_step;
  //   (*time_mode_integral_enodes[0])[m_mode-1] = e;
  } else if (e->isForallT()){
    default_true_suggestions.push_back(e);
  } else {
    default_true_suggestions.push_back(e);
  }
}

  void hybrid_heuristic::backtrack(){

    if(!m_is_initialized){
      return;
    }

    DREAL_LOG_DEBUG << "hybrid_heuristic::backtrack()";
    for(auto a : m_suggestions){
      delete a;
    }
    m_suggestions.clear();
    backtracked = true;

    lastTrailEnd = trail->size();
    displayTrail();
    displayStack();

    int bt_point = (trail_lim->size() == 0 ? 0 : (m_stack_lim.size() == trail_lim->size() ? m_stack.size() : m_stack_lim[trail_lim->size()]-1));
    DREAL_LOG_DEBUG << "level = " << trail_lim->size() << " pt = " << bt_point;

    while(m_stack_lim.size() != trail_lim->size()) m_stack_lim.pop_back();

    for (int i = m_stack.size(); i > bt_point; i--){
      std::pair<Enode *, bool> *s = m_stack.back();
      m_stack.pop_back();
      stack_literals.erase(s->first);
      delete s;
      lastTrailEnd--;
    }
 displayStack();

  }
  
  // Lit hybrid_heuristic::getSuggestion(){
  //   return lit_Undef;
  // }

// Assume that m_decision_stack matches m_stack
// and need to suggest next decision
bool hybrid_heuristic::expand_path(){
    DREAL_LOG_INFO << "hybrid_heuristic::expand_path()" << endl;

    // cannot expand path if out of choices
    if (m_decision_stack.size() == 0)
        return false;

    int steps_to_add = (num_autom*(m_depth+1))-static_cast<int>(m_decision_stack.size());
    DREAL_LOG_INFO << "Adding #steps: " << steps_to_add << endl;
    for (int i = 0; i < steps_to_add; i++){
      int time = m_depth - ((static_cast<int>(m_decision_stack.size()))/num_autom);
      int autom = (static_cast<int>(m_decision_stack.size()))%num_autom;

      vector<int> * current_decision = new vector<int>();

      int parent_index = (static_cast<int>(m_decision_stack.size()))-num_autom;
      
      if (parent_index < 0){
	DREAL_LOG_INFO << "Adding goal at time " << time << " for a" << autom;
	pair<int, vector<int>*>* astack = new pair<int, vector<int>*>();
	m_decision_stack.push_back(astack);

	vector<int> *dec = new vector<int>();
	dec->insert(dec->begin(), m_goal_modes[autom]->begin(), m_goal_modes[autom]->end());
	sort (dec->begin(), dec->end(), SubgoalCompare(autom, *this));
	astack->first = autom;
	astack->second = dec;

      } else {
	int parent = m_decision_stack[parent_index]->second->back();
      
        DREAL_LOG_INFO << "Adding decision at time " << time  << " to reach " << parent << " in a" << autom;

        set<int> * preds = (*predecessors[autom])[parent-1];

	if (time == 0){
	  //intersect initial state with current_decision
	  int init_mode = m_init_mode[autom];
	  
	  if (preds->find(init_mode) == preds->end()){
            DREAL_LOG_INFO << "No decisions left at time " << time << endl;
            return false;
	  }
	  current_decision->insert(current_decision->begin(), init_mode);
	} else {
	  current_decision->insert(current_decision->begin(), preds->begin(), preds->end());
	}


        set<int> current_decision_copy (current_decision->begin(), current_decision->end());
        // prune out choices that are negated in m_stack
        for (auto e : m_stack) {
            if (e->first->getPolarity() != l_True){
                //      DREAL_LOG_INFO << "Checking removal of " << e << endl;
	      auto p = (*mode_literals[autom]).find(e->first);
                if (p != (*mode_literals[autom]).end()){
                    // DREAL_LOG_INFO << "Removing negated " << p->second->first << endl;
                    if (p->second->second == time){
                        DREAL_LOG_INFO << "Removing negated " << p->second->first << endl;
                        auto e1 = current_decision_copy.find(p->second->first);
                        if (e1 != current_decision_copy.end()){
                            current_decision_copy.erase(e1);
                        }
                    }
                }
            }
        }

        // remove choices that are too costly for time
        for (auto c : *current_decision) {
	  if ((*m_cost[autom])[ c-1 ] > time) {
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

        sort (current_decision->begin(), current_decision->end(), SubgoalCompare(autom, *this));

        m_decision_stack.push_back(new pair<int, vector<int>*>(autom, current_decision));

        for (auto d : *current_decision){
            DREAL_LOG_INFO << "dec = " << d << endl;
        }
      }
    }

    return static_cast<int>(m_decision_stack.size()) == num_autom*(m_depth + 1); // successfully found a full path
}

// Get the literal for assigning mode at time
// side effect is to set the last_decision (a branch point to continue)
Enode * getLiteral(int mode, int time, scoped_vec & m_literals){
    for (auto e : m_literals){
        unordered_set<Enode *> const & vars = e->get_vars();
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
bool hybrid_heuristic::unwind_path() {
  vector<int> path;
  path.assign(num_autom*(m_depth+1), -1);
  int actual_path_size = 0;
  for (auto e : m_stack) {
    // if (e->getDecPolarity() != l_Undef){
    DREAL_LOG_INFO << "Checking path " << e->first << " = " << e->second;
    // }

    if (e->second && !e->first->isNot()){
      for(int a = 0; a < num_autom; a++){
	DREAL_LOG_DEBUG << "Find " << e->first << " for autom " << (a+1);
	auto i = (*mode_literals[a]).find(e->first);
	if (i != (*mode_literals[a]).end()){
	  DREAL_LOG_DEBUG << "setting path[" << (((*i).second->second*num_autom)+(num_autom-a)-1) << "] = "
			   << (*i).second->first;
	  path[((*i).second->second*num_autom)+(num_autom-a-1)] = (*i).second->first;
	  actual_path_size++;
	  break;
	}
      }
    }
  }

  bool paths_agree = true;
  int agree_depth = 0;
  for (int j = static_cast<int>(path.size() - 1); j > -1; j--){
    DREAL_LOG_INFO << "Path (" << j << ") = " << path[j] << endl;
    int stack_index_for_path_index = static_cast<int>(path.size() - j - 1);
    if (stack_index_for_path_index < static_cast<int>(m_decision_stack.size()))
      DREAL_LOG_INFO << "Stack(" << stack_index_for_path_index << ") = a" 
		     << (m_decision_stack[stack_index_for_path_index]->first+1)
		     << " m"
		     << m_decision_stack[stack_index_for_path_index]->second->back();
    else
      DREAL_LOG_INFO << "Stack(" << stack_index_for_path_index << ") = *";

    if (stack_index_for_path_index <  static_cast<int>(m_decision_stack.size())){
      if (m_decision_stack[stack_index_for_path_index]->second->back() != path[j]){
	if (paths_agree){
	  agree_depth = stack_index_for_path_index-1;
	  DREAL_LOG_INFO << "Last Agreed at: " << agree_depth << endl;
	}
	paths_agree = false;
      }
    } else{
      if (paths_agree){
	agree_depth = stack_index_for_path_index-1;
	DREAL_LOG_INFO << "Last Agreed at: " << agree_depth << endl;
      }
      paths_agree = false;
    }
  }

  // only unwind if decision stack needs to be
  int num_backtrack_steps = m_decision_stack.size() - agree_depth-1; // actual_path_size;
  DREAL_LOG_DEBUG << "Backtracking, # steps = " << num_backtrack_steps;
  if (// static_cast<int>(m_decision_stack.size()) > actual_path_size ||
      !paths_agree && num_backtrack_steps > 0){

    for (int i = 0; i <  num_backtrack_steps; i++){
      DREAL_LOG_INFO << "Backtracking " << i << endl;
      if (i == num_backtrack_steps-1){
	//choose sibling of at this level if it exists
	int path_index_for_stack_pos = i;//((m_depth+1)*num_autom) - m_decision_stack.size()+1;
	// if SAT solver already chose a sibling, then choose it, otherwise take the last
	if (path[path_index_for_stack_pos] != -1){
	  DREAL_LOG_DEBUG << "Moving to back " << path[path_index_for_stack_pos];
	  m_decision_stack.back()->second->pop_back();
	  for (vector<int>::iterator e = m_decision_stack.back()->second->begin();
	       e != m_decision_stack.back()->second->end(); ){
	    if (*e == path[path_index_for_stack_pos]){
	      DREAL_LOG_DEBUG << "ReMoving " << *e;
	      m_decision_stack.back()->second->erase(e);
	      e = m_decision_stack.back()->second->begin();
	    } else{
	      e++;
	    }
	  }
	  m_decision_stack.back()->second->push_back(path[path_index_for_stack_pos]);
	} else{
	  m_decision_stack.back()->second->pop_back();
	  if( m_decision_stack.back()->second->empty()){
	    delete m_decision_stack.back()->second;
	    delete m_decision_stack.back();
	    m_decision_stack.pop_back();
	  }
	}
      } else {
	  // the parent choice was unassigned too, so this decision no longer needed
	  delete m_decision_stack.back()->second;
	  delete m_decision_stack.back();
	  m_decision_stack.pop_back();
	}

      // there is only a decision to backtrack if m_decision_stack.size() > m_depth - i
      //if (static_cast<int>(m_decision_stack.size()) > 0){ // ((m_depth+1)*num_autom)-1 - i){
	// if (i == 0){
	//   // remove decision for time zero, which must be initial node
	//   // this is never to blame for the backtrack, but must be backtracked over
	//   delete m_decision_stack.back()->second;
	//   delete m_decision_stack.back();
	//   m_decision_stack.pop_back();
	// } else if (m_decision_stack.back() != NULL &&
	// 	   m_decision_stack.back()->second->size() > 1){
	//   // there is an unexplored sibling at this level
	//   // remove current choice at time and choose a sibling

	//   int path_index_for_stack_pos = ((m_depth+1)*num_autom) - m_decision_stack.size()+1;
	//   // if SAT solver already chose a sibling, then choose it, otherwise take the last
	//   if (path[path_index_for_stack_pos] != -1){
	//     DREAL_LOG_DEBUG << "Moving to back " << path[path_index_for_stack_pos];
	//     m_decision_stack.back()->second->pop_back();
	//     for (vector<int>::iterator e = m_decision_stack.back()->second->begin();
	// 	 e != m_decision_stack.back()->second->end(); ){
	//       if (*e == path[path_index_for_stack_pos]){
	// 	DREAL_LOG_DEBUG << "ReMoving " << *e;
	// 	m_decision_stack.back()->second->erase(e);
	// 	e = m_decision_stack.back()->second->begin();
	//       } else{
	// 	e++;
	//       }
	//     }
	//     m_decision_stack.back()->second->push_back(path[path_index_for_stack_pos]);
	//   } else{
	//     m_decision_stack.back()->second->pop_back();
	//   }
	//   break;
	// } else {
	//   // the parent choice was unassigned too, so this decision no longer needed
	//   delete m_decision_stack.back()->second;
	//   delete m_decision_stack.back();
	//   m_decision_stack.pop_back();
	// }
      // }
    }
  }

  for (int j = static_cast<int>(path.size() - 1); j > -1; j--){
    DREAL_LOG_INFO << "Path (" << j << ") = " << path[j] << endl;
    int stack_index_for_path_index = static_cast<int>(path.size() - j - 1);
    if (stack_index_for_path_index < static_cast<int>(m_decision_stack.size()))
      DREAL_LOG_INFO << "Stack(" << stack_index_for_path_index << ") = " 
		     << m_decision_stack[stack_index_for_path_index]->second->back();
    else {
      DREAL_LOG_INFO << "No choices left!";
    }
  }

  return m_decision_stack.size() > 0;
}

  bool hybrid_heuristic::pbacktrack(){
    //      int num_backtrack_steps = 1; // actual_path_size;
    bool found_sibling = false;
    while (!found_sibling && m_decision_stack.size() > 1){
      DREAL_LOG_INFO << "Backtracking at level " 
		     << m_decision_stack.size() << endl;
      
      if (m_decision_stack.back()->second != NULL &&
	  m_decision_stack.back()->second->size() > 1){
	// there is an unexplored sibling at this level
	// remove current choice at time and choose a sibling
	m_decision_stack.back()->second->pop_back();
	found_sibling = true;
	break;
      } else {
	// the parent choice was unassigned too, so this decision no longer needed
	delete m_decision_stack.back()->second;
	delete m_decision_stack.back();
	m_decision_stack.pop_back();
      }
    }

    DREAL_LOG_DEBUG << "After BT stack:";
    //    int i = 0;
    for (int i = 0; i < m_decision_stack.size(); i++){

// std::size_t time = (m_depth+1)*num_autom ; 
// 	 time > (m_depth+1)-m_decision_stack.size(); time--) {
      DREAL_LOG_DEBUG << "Stack[" << i << "] =" << m_decision_stack[i]->second->back();
    }
    return m_decision_stack.size() > 0;
  }

 
  void hybrid_heuristic::pushTrailOnStack(){
    DREAL_LOG_INFO << "hybrid_heuristic::pushTrailOnStack() lastTrailEnd = "
                   << lastTrailEnd << " trail->size() = " << trail->size();
    if(trail_lim->size() > m_stack_lim.size() ) //track start of levels after the first level
      m_stack_lim.push_back(m_stack.size());
    for (int i = lastTrailEnd; i < trail->size(); i++){
      Enode *e = theory_handler->varToEnode(var((*trail)[i]));
      bool msign = !sign((*trail)[i]);
      //   DREAL_LOG_INFO << "hybrid_heuristic::pushTrailOnStack() " << e;
      if (mode_enodes.find(e) != mode_enodes.end()){
        DREAL_LOG_INFO << "hybrid_heuristic::pushTrailOnStack() " << e << " " << msign;
        m_stack.push_back(new std::pair<Enode *, bool>(e, msign));
        stack_literals.insert(e);
      } 
    }
    lastTrailEnd = trail->size();
 displayStack();

  }

// unwind current current path to match stack
// complete path
// make suggestions for path
void hybrid_heuristic::getSuggestions() {
  DREAL_LOG_INFO << "hybrid_heuristic::getSuggestions()";
  displayTrail();
  // if (m_suggestions.size() > 0){
  //   suggestions.assign(m_suggestions.begin(), m_suggestions.end());
  //   return;
  // }


  bool suggestion_consistent = isStackConsistentWithSuggestion();



  m_is_initialized = true;
  bool suggest_false = true;
  bool suggest_integral = false;
  bool found_path = false;
  bool path_possible = true;
  // bool suggest_defaults = true;

  if(!m_suggestions.empty() && suggestion_consistent) {
    return;
  } else if(!suggestion_consistent || backtracked) {
    path_possible = unwind_path();
  }


  while (!found_path && path_possible){
    if (path_possible){
      found_path = expand_path();
    }
    if (!found_path){
      path_possible = pbacktrack();
    }
  }

  if (m_decision_stack.size() == 0)
    return;

    // suggest default guesses at other literals
    // if(suggest_defaults){
    //   for(auto e : default_true_suggestions){
    //  e->setDecPolarity(l_True);
    //  suggestions.push_back(e);
    //   }
    //   for(auto e : default_false_suggestions){
    //  e->setDecPolarity(l_False);
    //  suggestions.push_back(e);
    //   }
    // }


    // Suggest integral literals
  if (suggest_integral){
    for (int time = ((m_depth+1)*num_autom) - m_decision_stack.size()+1; 
	 time <= ((m_depth+1)*num_autom); time++) {
      DREAL_LOG_INFO << "Suggesting at time " << time << endl;
      int mode = m_decision_stack[((m_depth+1)*num_autom)-time]->second->back();
      int autom =  m_decision_stack[((m_depth+1)*num_autom)-time]->first;
      DREAL_LOG_INFO << "autom = " << autom << " mode = " << mode << endl;
      //      DREAL_LOG_INFO << "size = " << time_mode_integral_enodes[time]->size()  << endl;
      // Enode * s = (*time_mode_enodes[time])[mode-1];
      // DREAL_LOG_INFO << "enode = " << s << endl;
      // if (s->getDecPolarity() == l_Undef && !s->isDeduced()){
      //     s->setDecPolarity(l_True);
      //     suggestions.push_back(s);
      //     DREAL_LOG_INFO << "Suggested Pos: " << s << endl;
      // }
      
      if (suggest_false && time_mode_enodes[time]->size() > 0){
	for (int i = 0; i < static_cast<int>(predecessors[autom]->size()); i++){
	  if (i != mode - 1){
	    // s = (*time_mode_enodes[time])[i];
	    // if (s && s->getDecPolarity() == l_Undef && !s->isDeduced()){
	    //     s->setDecPolarity(l_False);
	    //     suggestions.push_back(s);
	    //     DREAL_LOG_INFO << "Suggested Neg: " << s << endl;
	    // }
	    Enode*  s = (*(*time_mode_integral_enodes[autom])[time])[i];
	    if (s && // s->getDecPolarity() == l_Undef &&
		!s->isDeduced()){
	      //s->setDecPolarity(l_False);
	      m_suggestions.push_back(new pair<Enode*, bool>(s, false));
	      DREAL_LOG_INFO << "Suggested Neg: " << s << endl;
	    }
	  }
	}        
      }

      if (time_mode_integral_enodes[time]->size() >=
	  static_cast<unsigned int>(mode)){
	Enode* s;
	if ( m_egraph->stepped_flows)
	  s = (*(*time_mode_integral_enodes[autom])[time])[mode-1];
	else
	  s = (*(*time_mode_integral_enodes[autom])[0])[mode-1];
        if (s != NULL){
          DREAL_LOG_INFO << "enode = " << s << endl;
          if (// s->getDecPolarity() == l_Undef &&
              !s->isDeduced()){
            //s->setDecPolarity(l_True);
            m_suggestions.push_back(new pair<Enode*, bool>(s, true));
            DREAL_LOG_INFO << "Suggested Pos: " << s << endl;
          }
        }
      }
    }
  }

  // Suggest mode literals
  for (int sl = m_decision_stack.size()-1; sl >= 0; sl--){
    int time = m_depth - (((sl)/num_autom));
    int mode = m_decision_stack[sl]->second->back();
    int autom =  m_decision_stack[sl]->first;
    DREAL_LOG_INFO << "stack level = " << sl 
		   << " time = " << time 
		   << " a" << autom 
		   << " m" << mode;

    Enode * s;
    if ((*time_mode_enodes[autom])[time]->size() > 0){
      if (suggest_false){
	for (int i = 0; i < static_cast<int>(predecessors[autom]->size()); i++){
	  if (i != mode - 1){
	    s = (*(*time_mode_enodes[autom])[time])[i];
	    if (suggest_false && s && // s->getDecPolarity() == l_Undef &&
		!s->hasPolarity() &&
		!s->isDeduced()){
	      //s->setDecPolarity(l_False);
	      m_suggestions.push_back(new pair<Enode*, bool>(s, false));
	      //DREAL_LOG_INFO << "Suggested Neg: " << s << endl;
	    }
	  }
	}
      }

      s = (*(*time_mode_enodes[autom])[time])[mode-1];
      DREAL_LOG_INFO << "enode = " << s << endl;
      if (// s->getDecPolarity() == l_Undef &&
	  !s->isDeduced()){
	//	s->setDecPolarity(l_True);
	m_suggestions.push_back(new pair<Enode*, bool>(s, true));
	//DREAL_LOG_INFO << "Suggested Pos: " << s << endl;
      }
    }
  }

  // // Suggest time 0 and time k mode literals
  // for (int time = 0; time < 2; time++) {
  //   DREAL_LOG_INFO << "Suggesting at time " << (m_depth*time) << endl;
  //   int mode = m_decision_stack[m_depth-(m_depth*time)]->back();
  //       DREAL_LOG_INFO << "mode = " << mode << endl;
  //       Enode * s;
  //      if (time_mode_enodes[(m_depth*time)]->size() > 0){
  //        if (suggest_false){
  //           for (int i = 0; i < static_cast<int>(predecessors.size()); i++){
  //               if (i != mode - 1){
  //                   s = (*time_mode_enodes[(m_depth*time)])[i];
  //                   if (suggest_false && s && // s->getDecPolarity() == l_Undef &&
  //                       !s->hasPolarity() &&
  //                       !s->isDeduced()){
  //                       s->setDecPolarity(l_False);
  //                       suggestions.push_back(s);
  //                       DREAL_LOG_INFO << "Suggested Neg: " << s << endl;
  //                   }
  //               }
  //           }
  //        }

        //  s = (*time_mode_enodes[time])[mode-1];
        // DREAL_LOG_INFO << "enode = " << s << endl;
        // if (// s->getDecPolarity() == l_Undef &&
        //     !s->isDeduced()){
        //     s->setDecPolarity(l_True);
        //     suggestions.push_back(s);
        //     DREAL_LOG_INFO << "Suggested Pos: " << s << endl;
        // }
    //     }
    // }


    // for (int time = m_depth - m_decision_stack.size()+1; time <= m_depth; time++) {
    //     DREAL_LOG_INFO << "Suggesting at time " << time << endl;
    //     int mode = m_decision_stack[m_depth-time]->back();
    //     DREAL_LOG_INFO << "mode = " << mode << endl;
    //     Enode * s = (*time_mode_enodes[time])[mode-1];
    //     DREAL_LOG_INFO << "enode = " << s << endl;
    //     if (// s->getDecPolarity() == l_Undef &&
    //         !s->isDeduced()){
    //         s->setDecPolarity(l_True);
    //         suggestions.push_back(s);
    //         DREAL_LOG_INFO << "Suggested Pos: " << s << endl;
    //     }
    //      s = (*time_mode_integral_enodes[time])[mode-1];
    //      DREAL_LOG_INFO << "enode = " << s << endl;
    //      if (s->getDecPolarity() == l_Undef && !s->isDeduced()){
    //          s->setDecPolarity(l_True);
    //          suggestions.push_back(s);
    //          DREAL_LOG_INFO << "Suggested Pos: " << s << endl;
    //      }

    //     if (time_mode_enodes[time]->size() > 0){
    //         for (int i = 0; i < static_cast<int>(predecessors.size()); i++){
    //             if (i != mode - 1){
    //               s = (*time_mode_enodes[time])[i];
    //               if (suggest_false && s && // s->getDecPolarity() == l_Undef &&
    //                   !s->isDeduced()){
    //                 s->setDecPolarity(l_False);
    //                 suggestions.push_back(s);
    //                 DREAL_LOG_INFO << "Suggested Neg: " << s << endl;
    //               }
    //                s = (*time_mode_integral_enodes[time])[i];
    //                if (s && s->getDecPolarity() == l_Undef && !s->isDeduced()){
    //                    s->setDecPolarity(l_False);
    //                    suggestions.push_back(s);
    //                    DREAL_LOG_INFO << "Suggested Neg: " << s << endl;
    //                }
    //             }
    //         }
    //     }
    // }

  for (auto e : m_suggestions) {
    DREAL_LOG_INFO << "hybrid_heuristic::getSuggestions(): Suggesting "
		   << (e->first->getPolarity() == l_True ? "     " : "(not ")
		   << e->first
		   << (e->first->getPolarity() == l_True ? "" : ")")
		   << " = " 
		   << e->second;
  }

  //m_suggestions.assign(suggestions.begin(), suggestions.end());

    int i = 0;
    for (auto d : m_decision_stack){
        DREAL_LOG_INFO << "Decision Stack(" << i++ << ") = " << endl;
        for (auto d1 : (*d->second))
            DREAL_LOG_INFO << d1 << endl;
    }
    stringstream ss;
    for (int i =  m_decision_stack.size()-1; i > -1; i--){
      ss << "(a" << (m_decision_stack[i]->first+1) << ",m" 
	 << m_decision_stack[i]->second->back() << ")";
      if (i != 0)
        ss << ",";
    }
    DREAL_LOG_INFO << "Suggesting the Path: [" << ss.str() << "]";
    //    cout << "Suggesting the Path: [" << ss.str() << "]" << endl;
}
}
