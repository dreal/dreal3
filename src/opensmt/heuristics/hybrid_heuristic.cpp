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

#include "opensmt/egraph/Egraph.h"
#include "opensmt/tsolvers/TSolver.h"
#include "util/logging.h"
#include "util/scoped_vec.h"

using std::string;
using std::ifstream;
using std::unordered_set;
using std::ios;
using std::sort;
using nlohmann::json;

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
      hinfo = json::parse(heuristic_string);
      //auto hinfo = json.array_items();
      auto init_list = hinfo[0][0];
      auto goal_list = hinfo[0][1];
      DREAL_LOG_DEBUG << "hybrid_heuristic::initialize() init";
      // get init
      for(auto i : init_list){
        m_init_mode.push_back(i);
      }

       DREAL_LOG_DEBUG << "hybrid_heuristic::initialize() depth ";
      // BMC depth
       m_depth = hinfo[0][2];

      // DREAL_LOG_INFO << "Init = " << m_init_mode << " Steps = " << m_depth << endl;
      num_autom = hinfo[0][0].size();

      DREAL_LOG_DEBUG << "hybrid_heuristic::initialize() goals";
      // get goals
      for (auto gs : goal_list){
        vector<labeled_transition*> *mg = new vector<labeled_transition*>();
        for (auto g : gs){
          mg->push_back(new labeled_transition(new set<int>(),g));
	  DREAL_LOG_DEBUG << "goal: " << g;
        }
	DREAL_LOG_DEBUG << "";
        m_goal_modes.push_back(mg);
      }

      DREAL_LOG_DEBUG << "hybrid_heuristic::initialize() costs";
      // get mode costs
      for(auto i : hinfo[1]){
        vector<double> *mc = new vector<double>();
        mc->assign(i.size(), 0.0);
        for (json::iterator object = i.begin(); object!= i.end(); object++){
          (*mc)[atoi(object.key().c_str())-1] = atof(object.value().dump().substr(1, object.value().dump().size()-1).c_str());
          DREAL_LOG_DEBUG << (atoi(object.key().c_str())-1) << " = " << (*mc)[atoi(object.key().c_str())-1];
        }
        m_cost.push_back(mc);
      }

      // build reverse adjanceny map (succ -> set(predecessors))      
      for(unsigned int j = 0; j < hinfo[2].size(); j++){ // loop over automata
	DREAL_LOG_DEBUG << "Getting Transitions For Autom ";
	vector<vector<labeled_transition*>*>* aut_predecessors = new vector<vector<labeled_transition*>*>();
	for (unsigned int i = 0; i < hinfo[2][j].size(); i++){ // loop over modes
	  // DREAL_LOG_DEBUG << "Getting Transitions From " << i;
	  vector<labeled_transition*>* mp = new vector<labeled_transition*>();  
	  aut_predecessors->push_back(mp);
	}	
	for (unsigned int src = 0; src < hinfo[2][j].size(); src++){
	  //DREAL_LOG_DEBUG << "Getting Transitions From " << src << " " << hinfo[2][j][src].dump();
	  m_aut_labels.push_back(new set<int>());
	  auto adj = hinfo[2][j][src]; // transitions from src
	  for(auto adj_trans : adj){ // loop over transitions
	    //DREAL_LOG_DEBUG << "Getting Transition " << adj_trans.dump();
	    labeled_transition *trans = new labeled_transition();
	    set<int>* trans_labels = new set<int>();
	    trans->first = trans_labels;
	    trans->second = src+1;

	    auto labels = adj_trans[0];
	    stringstream labels_string;
	    for(auto l : labels){
	      
	      string label_string = l.dump().c_str();
	      string label_string_s = label_string.substr(1,label_string.size()-2);
	      auto li = label_to_indices.find(label_string_s);
	      int ind;
	      if(li == label_to_indices.end()){
		label_to_indices[label_string_s] = num_labels++;
		ind = num_labels-1;
		//DREAL_LOG_DEBUG << "label_to_indices[" << label_string_s << "] = " << ind;
		
		label_from_indices[ind] = label_string_s;
		DREAL_LOG_DEBUG << "label_from_indices[" << ind << "] = " << label_from_indices[ind];
	      } else {
		ind = li->second;
	      }
	      //DREAL_LOG_DEBUG << "m_aut_labels[" << j << "].insert(" << ind <<")";
	      m_aut_labels[j]->insert(ind);
	      trans_labels->insert(ind);
	      labels_string << ind << " ";
	    }

	    int dest = adj_trans[1];
	    (*aut_predecessors)[dest-1]->push_back(trans);

	    if(adj_trans[2] == 1){
	      noops.insert(trans);
	    }
	    
	    DREAL_LOG_DEBUG << "Got Transition a" << j << " " << (src+1) << "--[" << labels_string.str() << "]--> " << dest;
	  }

	}
	predecessors.push_back(aut_predecessors);
      }


        // // initialize decision stack
        // pair<int, vector<labeled_transition*>*>* astack = new pair<int, vector<labeled_transition*>*>();
        // m_decision_stack.push_back(astack);

        // vector<labeled_transition*>*dec = new vector<labeled_transition*>();

        // for (auto goalm : *m_goal_modes[0]){
	//   if ((*m_cost[0])[ (goalm)-1 ] <=  m_depth) {
	//     dec->push_back(new labeled_transition(NULL, goalm));
	//   }
        // }
	// 	set<labeled_transition*> toRemove;
        // for (auto e : m_stack) {
        //     if (e->first->getPolarity() != l_True){
        //         //      DREAL_LOG_INFO << "Checking removal of " << e << endl;
        //       auto p = (*mode_literals[0]).find(e->first);
        //         if (p != (*mode_literals[0]).end()){
        //             // DREAL_LOG_INFO << "Removing negated " << p->second->first << endl;
        //             if (p->second->second == m_depth){
        //                 DREAL_LOG_INFO << "Removing negated " << p->second->first << endl;
        //                 for (auto e1 : *dec){
        //                   if (e1->second == p->second->first){
        //                     toRemove.insert(e1);
        //                   }
        //                 }
        //             }
        //         }
        //     }
        // }

	// for(auto tr : toRemove){
        //   for(vector<labeled_transition*>::iterator tri = dec->begin();
        //       tri != dec->end(); tri++){
        //     if(*tri == tr){
        //       dec->erase(tri);
        //       break;
        //     }
        //   }
        // }

        // //dec->insert(dec->begin(), m_goal_modes[autom]->begin(), m_goal_modes[autom]->end());
        // sort (dec->begin(), dec->end(), SubgoalCompare(0, *this));
        // astack->first = 0;
        // astack->second = dec;

      for (int i = 0; i < m_depth+1; i++){
	vector<Enode*>* en = new vector<Enode*>();
	en->assign(num_labels, NULL);
	time_label_enodes.push_back(en);
      }

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
	    en->assign(static_cast<int>(predecessors[a]->size()), NULL);
	    tmi->push_back(en);
	    // }
	  }
	}

    }
    //    DREAL_LOG_DEBUG << network_to_string();
}


void hybrid_heuristic::inform(Enode * e){
  DREAL_LOG_INFO << "hybrid_heuristic::inform()" ;
  //      DREAL_LOG_INFO << network_to_string();
  if (!e->isTAtom() && !e->isNot()) {
    unordered_set<Enode *> const & vars = e->get_vars();
    //unordered_set<Enode *> const & consts = e->get_constants();
    for (auto const & v : vars) {
      stringstream ss;
      ss << v;
      string var = ss.str();
      if (var.find("sync") != string::npos) {
	  //int autom_pos = var.find("_")+1;
	  int time_pos = var.rfind("_")+1;
	  int time = atoi(var.substr(time_pos).c_str());
	  string name = var.substr(5, time_pos-1-5);
	  int label_index = label_to_indices[name] ;
	  DREAL_LOG_DEBUG << "Got label " << e << " time = " << time << " index = " << label_index << " name = " << name;
	  (*time_label_enodes[time])[label_index] = e;
	  label_enodes.insert(e);
	  label_enode_indices[e] = label_index;
        }
    }
  } else if (e->isEq() && !e->isNot()){
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
		       1 : 
		       atoi(var.substr(autom_pos, time_pos-1).c_str()));
	  int mode = get_mode(e);

	  if(mode > -1){
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

    if( m_stack_lim.size() < (unsigned long)trail_lim->size())
      return;

    for(auto a : m_suggestions){
      delete a;
    }
    m_suggestions.clear();
    backtracked = true;

    lastTrailEnd = trail->size();
     displayTrail();
    // displayStack();


    //end of m_stack level corresponding to end of trail
     int bt_point = ((trail_lim->size() < m_stack_lim.size() && trail_lim->size() > 0)  ?
		     m_stack_lim[trail_lim->size()] :
		     m_stack.size());

     //      (m_stack_lim->size() ==  0 ? m_stack.size() : (m_stack_lim.size() == (unsigned long)trail_lim->size() ? m_stack.size() : m_stack_lim[m_stack_lim.size()-1]));
    DREAL_LOG_DEBUG << "stack size = " << m_stack_lim.size() << " level = " << trail_lim->size() << " pt = " << bt_point;

    while(m_stack_lim.size() > (unsigned long)trail_lim->size()) m_stack_lim.pop_back();

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


  void hybrid_heuristic::removeImpossibleTransitions(vector<labeled_transition*>* dec, int time, int autom){
    DREAL_LOG_INFO << "hybrid_heuristic::removeImpossibleTransitions() time = " << time << " autom = " << autom
		   << " |dec| = " << dec->size();
    set<labeled_transition*> toRemove;
    for (auto e : m_stack) {
      if (!e->second){
	//	DREAL_LOG_INFO << "Checking removal of " << e->first << endl;
	auto p = (*mode_literals[autom]).find(e->first);
	if (p != (*mode_literals[autom]).end()){
	  //DREAL_LOG_INFO << "Removing negated " << p->second->first << endl;
	  if (p->second->second == time){
	    for (auto e1 : *dec){
	      if (e1->second == p->second->first){
		DREAL_LOG_INFO << "Removing negated mode " << e1->second << " " << e->first;
		toRemove.insert(e1);
	      }
	    }
	  }
	}
	if(time < m_depth){ // goal modes don't have transitions
	  for (auto e1 : *dec){
	    if(e->first){
	    auto q = e1->first->find(label_enode_indices[e->first]);
	    if (q != e1->first->end()){
	      for(auto s : (*time_label_enodes[time])){
		if(s == e->first){ //e is literal for sync at this time
		  DREAL_LOG_INFO << "Removing negated label " << label_enode_indices[e->first] << " for " << e1->second << " " << e->first;
		  toRemove.insert(e1);
		}
	      }
	    }
	  }
	  }
	}
      }
    }

    // for(auto tr : toRemove){
    //   for(vector<labeled_transition*>::iterator tri = dec->begin();
    // 	  tri != dec->end(); tri++){
    // 	if(*tri == tr){
    // 	  dec->erase(tri);
    // 	  break;
    // 	}
    //   }
    // }

    // remove choices that are too costly for time
    for (auto c : *dec) {
      //DREAL_LOG_INFO << "cost[" << (c->second) << "] = "  << (*m_cost[autom])[ (c->second)-1 ];
      if ((*m_cost[autom])[ (c->second)-1 ] > time) {
	DREAL_LOG_INFO << "Removing too costly " << (c->second) << endl;
	toRemove.insert(c);
      }
    }

    for(auto tr : toRemove){
      for(vector<labeled_transition*>::iterator tri = dec->begin();
	  tri != dec->end(); tri++){
	if(*tri == tr){
	  dec->erase(tri);
	  break;
	}
      }
    }
    toRemove.clear();

    //remove choices that do not synchronize
    if(time < m_depth && autom > 0 && !dec->empty()){
      vector<pair<int, labeled_transition*>*> parallel_transitions;
      for(int k = 0; k < autom; k++){
	DREAL_LOG_DEBUG << "checking sync with a" << k;
	parallel_transitions.push_back(new pair<int, labeled_transition*>(k, m_decision_stack[m_decision_stack.size()-(autom-k)]->second->back()));
      }
      for (auto c : *dec) {
	pair<int, labeled_transition*> pr (autom, c);
	if (!can_synchronize(parallel_transitions, pr)) {
	  DREAL_LOG_INFO << "Removing non-synchronous " << (c->second) << endl;
	  toRemove.insert(c);
	}
      }
    }
    
    for(auto tr : toRemove){
      for(vector<labeled_transition*>::iterator tri = dec->begin();
	  tri != dec->end(); tri++){
	if(*tri == tr){
	  dec->erase(tri);
	  break;
	}
      }
    }
    DREAL_LOG_INFO << "hybrid_heuristic::removeImpossibleTransitions() time = " << time << " autom = " << autom
		   << " |dec| = " << dec->size();
  }

  string hybrid_heuristic::network_to_string(){
    stringstream out;
    for(int a = 0; a < num_autom; a++){
      DREAL_LOG_DEBUG << "a = " << a;
      out << "Automata: a" << a << endl;
      out << "Goals: ";
      for(int g = 0; g < m_goal_modes[a]->size(); g++){
	out << (*m_goal_modes[a])[g]->second << " ";
      }
      out << endl;
      out << "Labels: ";
     for(set<int>::iterator l = m_aut_labels[a]->begin(); l != m_aut_labels[a]->end(); l++)
	    out << *l << " ";
      out << endl;
      for(int m = 0; m < predecessors[a]->size(); m++){
	//DREAL_LOG_DEBUG << "m = " << m;
	for(int t = 0; t < (*predecessors[a])[m]->size(); t++){
	  //DREAL_LOG_DEBUG << "t = " << t;
	  labeled_transition* tr = (*(*predecessors[a])[m])[t];
	  out << tr->second << "--[";
	  for(set<int>::iterator l = tr->first->begin(); l != tr->first->end(); l++)
	    out << *l << " ";
	  out << "]--> " << (m+1) << endl;
	}
      }
    }
    return out.str();
  }
  
// Assume that m_decision_stack matches m_stack
// and need to suggest next decision
bool hybrid_heuristic::expand_path(bool first_expansion){
    DREAL_LOG_INFO << "hybrid_heuristic::expand_path()" << endl;
    //    DREAL_LOG_INFO << network_to_string();
    // cannot expand path if out of choices
    if (m_decision_stack.size() == 0 && !first_expansion){
      DREAL_LOG_INFO << "out of choices";
        return false;
    }

    // path already expanded by SAT solver, and already pushed on m_stack
    if (m_stack.size() == (num_autom*(m_depth+1))){
      DREAL_LOG_INFO << "path already full"; 
        return true;
    }

    
    int steps_to_add = (num_autom*(m_depth+1))-static_cast<int>(m_decision_stack.size());
    DREAL_LOG_INFO << "Adding #steps: " << steps_to_add << endl;
    for (int i = 0; i < steps_to_add; i++){
      int time = m_depth - ((static_cast<int>(m_decision_stack.size()))/num_autom);
      int autom = (static_cast<int>(m_decision_stack.size()))%num_autom;

      vector<labeled_transition*> * current_decision = new vector<labeled_transition*>();

      int parent_index = (static_cast<int>(m_decision_stack.size()))-num_autom;

      if (parent_index < 0){
        DREAL_LOG_INFO << "Adding goal at time " << time << " for a" << autom;
        pair<int, vector<labeled_transition*>*>* astack = new pair<int, vector<labeled_transition*>*>();
        m_decision_stack.push_back(astack);

        vector<labeled_transition*>*dec = new vector<labeled_transition*>();

        for (auto goalm : *m_goal_modes[autom]){
	  dec->push_back(goalm);
	  DREAL_LOG_INFO << "possible goal: " << goalm->second;	  
        }
	removeImpossibleTransitions(dec, m_depth, autom);

        //dec->insert(dec->begin(), m_goal_modes[autom]->begin(), m_goal_modes[autom]->end());
        sort (dec->begin(), dec->end(), SubgoalCompare(autom, *this));
        astack->first = autom;
        astack->second = dec;

	 if (dec->size() == 0){
	  DREAL_LOG_INFO << "No decisions left at time " << time << " for a" << autom << endl;
            return false;
        }


      } else {
        labeled_transition* parent = m_decision_stack[parent_index]->second->back();

        DREAL_LOG_INFO << "Adding decision at time " << time  << " to reach " << parent->second << " in a" << autom << " parent_index = " << parent_index;

        vector<labeled_transition*> * preds = (*predecessors[autom])[(parent->second)-1];
	DREAL_LOG_INFO << "|preds| = " << preds->size();
	for (labeled_transition* pred : *preds){
	  stringstream labels;

	  DREAL_LOG_DEBUG << pred->second;
	  if(pred->first){
	  for(int lab : *(pred->first)) {
	    DREAL_LOG_DEBUG << lab;
	    labels //<< 	label_from_indices[lab]<< ":"
		   << lab << " ";
	  }
	  }
	  DREAL_LOG_DEBUG << "Checking predecessor a" << autom << " "
			  << pred->second << "--[" << labels.str() << "]--> " << parent->second;
	}
	//	DREAL_LOG_DEBUG << "HI";
	if (time == 0){
          //intersect initial state with current_decision
          int init_mode = m_init_mode[autom];
          for (auto pred : *preds){
            // DREAL_LOG_DEBUG << "Checking predecessor " << pred->second << " = " << init_mode;
            if(pred->second == init_mode){
              current_decision->insert(current_decision->begin(), pred);
            }
          }
          // if (current_decision->empty()){
          //   DREAL_LOG_INFO << "No decisions left at time " << time << endl;
          //   return false;
          // }
        } else {
          current_decision->insert(current_decision->begin(), preds->begin(), preds->end());
        }


        //vector<labeled_transition*> current_decision_copy (current_decision->begin(), current_decision->end());
        // prune out choices that are negated in m_stack
	removeImpossibleTransitions(current_decision, time, autom);
	
        if (current_decision->size() == 0){
	  DREAL_LOG_INFO << "No decisions left at time " << time << " for a" << autom << endl;
            return false;
        }

        sort (current_decision->begin(), current_decision->end(), SubgoalCompare(autom, *this));

        m_decision_stack.push_back(new pair<int, vector<labeled_transition*>*>(autom, current_decision));

        for (auto d : *current_decision){
	  stringstream labels;
	  if(d->first){
	    for(auto lab : *(d->first)) {
	      labels << lab;
	    }
	  }
	  DREAL_LOG_INFO << "dec = " << d->second << " [" << labels.str() << "]";
        }
      }
    }
    DREAL_LOG_DEBUG << "Done expand_path()";
    return static_cast<int>(m_decision_stack.size()) == num_autom*(m_depth + 1); // successfully found a full path
}

// // Get the literal for assigning mode at time
// // side effect is to set the last_decision (a branch point to continue)
// Enode * getLiteral(int mode, int time, scoped_vec & m_literals){
//     for (auto const e : m_literals){
//         unordered_set<Enode *> const & vars = e->get_vars();
//         for (auto const & v : vars) {
//             stringstream ss;
//             ss << v;
//             string var = ss.str();
//             if (var.find("mode") != string::npos) {
//                 int t = atoi(var.substr(var.find("_")+1).c_str());
//                 int m = get_mode(e);
//                 if (m == mode && time == t){
//                     return e;
//                 }
//             }
//         }
//     }
//     return NULL;
// }

  bool hybrid_heuristic::can_synchronize(vector<pair<int, labeled_transition*>*>& parallel_transitions,
                                         pair<int, labeled_transition*> &trans){

   

    set<int> *trans_aut_labels = m_aut_labels[trans.first];
    set<int> sync_trans;//(static_cast<int>(trans_aut_labels->size());
    bool trans_noop = is_noop(trans.second);


     DREAL_LOG_DEBUG << "can_synchronize a" << trans.first << " src " << trans.second->second << (trans_noop ? " noop" : "");
     if(trans.second->first){
    for(auto lab : *trans.second->first){
      DREAL_LOG_DEBUG << "lab = " << label_from_indices[lab]<< ":" << lab;
    }
     }
    
    DREAL_LOG_DEBUG << "aut_labels:";
    for(auto lab : *trans_aut_labels){
      DREAL_LOG_DEBUG << "lab = " << label_from_indices[lab]<< ":" << lab;
    }


    //set sync(trans)
    // set_intersection(trans_aut_labels->begin(), trans_aut_labels->end(),
    //               trans.second->first->begin(), trans.second->first->end(),
    //               sync_trans.begin());
    for(auto l : *trans_aut_labels){
      if(trans.second->first->find(l) != trans.second->first->end())
        sync_trans.insert(l);
    }


    DREAL_LOG_DEBUG << "sync_trans labels:";
    for(auto lab : sync_trans){
      DREAL_LOG_DEBUG << "lab = " << label_from_indices[lab]<< ":" << lab;
    }


    for(unsigned long i = 0; i < parallel_transitions.size(); i++){
      pair<int, labeled_transition*> *trans_i = parallel_transitions[i];
      set<int> sync_trans_i;
      set<int> *trans_i_aut_labels = m_aut_labels[trans_i->first];
      bool trans_i_noop = is_noop(trans_i->second);

      DREAL_LOG_DEBUG << "with a" << trans_i->first << " src " << trans_i->second->second << (trans_i_noop ? " noop" : "");
      if(trans_i->second->first){
      for(auto lab : *trans_i->second->first){
        DREAL_LOG_DEBUG << "lab = " << label_from_indices[lab]<< ":" << lab;
      }
      }
      DREAL_LOG_DEBUG << "aut_labels:";
      for(auto lab : *trans_i_aut_labels){
        DREAL_LOG_DEBUG << "lab = " << label_from_indices[lab]<< ":" << lab;
      }


      //set sync(trans_i)
      for(auto l : *trans_i_aut_labels){
        if(trans_i->second->first->find(l) != trans_i->second->first->end())
          sync_trans_i.insert(l);
      }
      DREAL_LOG_DEBUG << "sync_trans_i labels:";
      for(auto lab : sync_trans_i){
        DREAL_LOG_DEBUG << "lab = " << label_from_indices[lab]<< ":" << lab;
      }

      // set_intersection(trans_i_aut_labels->begin(), trans_i_aut_labels->end(),
      //                       trans_i->second->first->begin(), trans_i->second->first->end(),
      //                       sync_trans_i.begin());

      set<int> lhs, rhs;

      //set sync(trans) \cap train_i_aut_labels
      // set_intersection(trans_i_aut_labels->begin(), trans_i_aut_labels->end(),
      //                       sync_trans.begin(), sync_trans.end(),
      //                       lhs.begin());

      for(auto l : *trans_i_aut_labels){
        if(sync_trans.find(l) != sync_trans.end())
          lhs.insert(l);
      }
      DREAL_LOG_DEBUG << "lhs labels:";
      for(auto lab : lhs){
        DREAL_LOG_DEBUG << "lab = " << label_from_indices[lab]<< ":" << lab;
      }

      //set sync(trans) \cap train_i_aut_labels
      // set_intersection(trans_aut_labels->begin(), trans_aut_labels->end(),
      //                       sync_trans_i.begin(), sync_trans_i.end(),
      //                       rhs.begin());

      for(auto l : *trans_aut_labels){
        if(sync_trans_i.find(l) != sync_trans_i.end())
          rhs.insert(l);
      }
      DREAL_LOG_DEBUG << "rhs labels:";
      for(auto lab : rhs){
        DREAL_LOG_DEBUG << "lab = " << label_from_indices[lab]<< ":" << lab;
      }

      if(!trans_noop && !trans_i_noop){
	if(lhs != rhs)
	  return false;
      } else if (trans_i_noop) {
	return lhs.empty();
      }
      else if (trans_noop) {
	return rhs.empty();
      }

      //if sync_trans \cap trans_i_aut_labels != sync_trans_i \cap trans_aut_labels, then fail

    }
    return true;
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
    if (stack_index_for_path_index < static_cast<int>(m_decision_stack.size())){
      DREAL_LOG_INFO << "Stack(" << stack_index_for_path_index << ") = a"
                     << (m_decision_stack[stack_index_for_path_index]->first+1)
                     << " m"
                     << m_decision_stack[stack_index_for_path_index]->second->back()->second;
    }
    else
      DREAL_LOG_INFO << "Stack(" << stack_index_for_path_index << ") = *";

    if (stack_index_for_path_index <  static_cast<int>(m_decision_stack.size())){
      if (m_decision_stack[stack_index_for_path_index]->second->back()->second != path[j]){
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
      // if (i == num_backtrack_steps-1){
      //   //choose sibling of at this level if it exists
      //   int path_index_for_stack_pos = i;//((m_depth+1)*num_autom) - m_decision_stack.size()+1;
      //   // if SAT solver already chose a sibling, then choose it, otherwise take the last
      //   if (path[path_index_for_stack_pos] != -1){
      //     DREAL_LOG_DEBUG << "Moving to back " << path[path_index_for_stack_pos];
      //     m_decision_stack.back()->second->pop_back();
      //     for (vector<labeled_transition*>::iterator e = m_decision_stack.back()->second->begin();
      //          e != m_decision_stack.back()->second->end(); ){
      //       if ((*e)->second == path[path_index_for_stack_pos]){
      //         DREAL_LOG_DEBUG << "ReMoving " << *e;
      //         m_decision_stack.back()->second->erase(e);
      //         e = m_decision_stack.back()->second->begin();
      //       } else{
      //         e++;
      //       }
      //     }
      //     m_decision_stack.back()->second->push_back(new labeled_transition( new set<int>(), path[path_index_for_stack_pos]));
      //   } else{
      // 	  DREAL_LOG_DEBUG << "Choose sibling";
      //     m_decision_stack.back()->second->pop_back();
      //     if( m_decision_stack.back()->second->empty()){
      //       delete m_decision_stack.back()->second;
      //       delete m_decision_stack.back();
      //       m_decision_stack.pop_back();
      //     }
      //   }
      // } else {
          // the parent choice was unassigned too, so this decision no longer needed
          delete m_decision_stack.back()->second;
          delete m_decision_stack.back();
          m_decision_stack.pop_back();
	  //        }

      // there is only a decision to backtrack if m_decision_stack.size() > m_depth - i
      //if (static_cast<int>(m_decision_stack.size()) > 0){ // ((m_depth+1)*num_autom)-1 - i){
        // if (i == 0){
        //   // remove decision for time zero, which must be initial node
        //   // this is never to blame for the backtrack, but must be backtracked over
        //   delete m_decision_stack.back()->second;
        //   delete m_decision_stack.back();
        //   m_decision_stack.pop_back();
        // } else if (m_decision_stack.back() != NULL &&
        //         m_decision_stack.back()->second->size() > 1){
        //   // there is an unexplored sibling at this level
        //   // remove current choice at time and choose a sibling

        //   int path_index_for_stack_pos = ((m_depth+1)*num_autom) - m_decision_stack.size()+1;
        //   // if SAT solver already chose a sibling, then choose it, otherwise take the last
        //   if (path[path_index_for_stack_pos] != -1){
        //     DREAL_LOG_DEBUG << "Moving to back " << path[path_index_for_stack_pos];
        //     m_decision_stack.back()->second->pop_back();
        //     for (vector<int>::iterator e = m_decision_stack.back()->second->begin();
        //       e != m_decision_stack.back()->second->end(); ){
        //       if (*e == path[path_index_for_stack_pos]){
        //      DREAL_LOG_DEBUG << "ReMoving " << *e;
        //      m_decision_stack.back()->second->erase(e);
        //      e = m_decision_stack.back()->second->begin();
        //       } else{
        //      e++;
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
    if (stack_index_for_path_index < static_cast<int>(m_decision_stack.size())){
      DREAL_LOG_INFO << "Stack(" << stack_index_for_path_index << ") = "
                     << m_decision_stack[stack_index_for_path_index]->second->back();
    }
    else {
      DREAL_LOG_INFO << "No choices left!";
    }
  }

  return m_decision_stack.size() > 0;
}

  bool hybrid_heuristic::pbacktrack(){
    //      int num_backtrack_steps = 1; // actual_path_size;
    bool found_sibling = false;
      DREAL_LOG_INFO << "Starting backtrack from level "
                     << m_decision_stack.size()
		     << " lastDecisionStackEnd = " << lastDecisionStackEnd << endl;

    while (!found_sibling &&
	   m_decision_stack.size() > 0 &&
	   m_decision_stack.size() >= lastDecisionStackEnd
	   ){
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

    DREAL_LOG_DEBUG << "After BT stack: size = " << m_decision_stack.size();
    //    int i = 0;
    for (unsigned int i = 0; i < m_decision_stack.size(); i++){

// std::size_t time = (m_depth+1)*num_autom ;
//       time > (m_depth+1)-m_decision_stack.size(); time--) {
      stringstream labels;
      if(m_decision_stack[i]->second->back()->first){
	for(auto lab : *(m_decision_stack[i]->second->back()->first)) {
	  labels << lab;
	}
      }
      DREAL_LOG_DEBUG << "Stack[" << i << "] ="
		      << m_decision_stack[i]->second->back()->second
		      << " [" << labels.str() << "]";
    }
    return m_decision_stack.size() > lastDecisionStackEnd;
  }


  void hybrid_heuristic::pushTrailOnStack(){
    DREAL_LOG_INFO << "hybrid_heuristic::pushTrailOnStack() lastTrailEnd = "
                   << lastTrailEnd << " trail->size() = " << trail->size();
    //    DREAL_LOG_INFO << network_to_string();
    //    displayTrail();
    //    displayStack();

    if((unsigned int) trail_lim->size() >  m_stack_lim.size() &&
       m_stack.size() > 0) { //track start of levels after the first level
      m_stack_lim.push_back(m_stack.size());
    }
    for (int i = lastTrailEnd; i < trail->size(); i++){
      Enode *e = theory_handler->varToEnode(var((*trail)[i]));
      bool msign = !sign((*trail)[i]);
      //   DREAL_LOG_INFO << "hybrid_heuristic::pushTrailOnStack() " << e;
      if (mode_enodes.find(e) != mode_enodes.end()){
        DREAL_LOG_INFO << "hybrid_heuristic::pushTrailOnStack() " << e << " " << msign;
        m_stack.push_back(new std::pair<Enode *, bool>(e, msign));
        stack_literals.insert(e);
      } else  if (label_enodes.find(e) != label_enodes.end()){
        DREAL_LOG_INFO << "hybrid_heuristic::pushTrailOnStack() " << e << " " << msign;
        m_stack.push_back(new std::pair<Enode *, bool>(e, msign));
        stack_literals.insert(e);
      }
    }
    lastTrailEnd = trail->size();
    displayTrail();
    displayStack();
    DREAL_LOG_INFO << "Pushed trail";
  }

// unwind current current path to match stack
// complete path
// make suggestions for path
bool hybrid_heuristic::getSuggestions() {
  DREAL_LOG_INFO << "hybrid_heuristic::getSuggestions()";
  //  displayTrail();
  //  displayStack();
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
    DREAL_LOG_INFO << "have more suggestions";
    return true;
  } else if(!suggestion_consistent || backtracked) {
    //path_possible =
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

  // if couldn't expand path and not already at end of path
  if (m_decision_stack.size() == m_stack_lim.size() && m_decision_stack.size() < (m_depth+1)*num_autom){
    DREAL_LOG_INFO << "Ran out of suggestions, subtree is unsat!";
    //generate conflict clause
    return false;
  }
    
  if (m_stack.size() == (unsigned int)num_autom*(m_depth+1)){
    DREAL_LOG_INFO << "Made all the suggestions";
    return true;
  }

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
      int mode = m_decision_stack[((m_depth+1)*num_autom)-time]->second->back()->second;
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
    int mode = m_decision_stack[sl]->second->back()->second;
    set<int>* labels = m_decision_stack[sl]->second->back()->first;
    int autom =  m_decision_stack[sl]->first;

    stringstream label_string;
    if(labels){
    for(auto l : *labels){
      label_string << label_from_indices[l] << ", ";
    }
    }
    
    DREAL_LOG_INFO << "stack level = " << sl
                   << " time = " << time
                   << " a" << autom
                   << " m" << mode
		   << " labels = " << label_string.str();

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
              DREAL_LOG_INFO << "Suggested Neg: " << s << endl;
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
        DREAL_LOG_INFO << "Suggested Pos: " << s << endl;
      }
    }

    if(labels){
     for(auto l : *labels){
       Enode *le = (*time_label_enodes[time])[l];
       DREAL_LOG_INFO << "Suggesting Label: " << le;
       m_suggestions.push_back(new pair<Enode*, bool>(le, true));
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

  // for (auto e : m_suggestions) {
  //   DREAL_LOG_INFO << "hybrid_heuristic::getSuggestions(): Suggesting "
  //                  << (e->first->getPolarity() == l_True ? "     " : "(not ")
  //                  << e->first
  //                  << (e->first->getPolarity() == l_True ? "" : ")")
  //                  << " = "
  //                  << e->second;
  // }

  //m_suggestions.assign(suggestions.begin(), suggestions.end());

    int i = 0;
    for (auto d : m_decision_stack){
        DREAL_LOG_INFO << "Decision Stack(" << i++ << ") = " << endl;
        for (auto d1 : (*d->second))
            DREAL_LOG_INFO << d1->second << endl;
    }
    stringstream ss;
    for (int i =  m_decision_stack.size()-1; i > -1; i--){
      
      stringstream label;
      if(m_decision_stack[i]->second->back()->first){
	for( auto lab : *(m_decision_stack[i]->second->back()->first)){
	  label << label_from_indices[lab] << ",";
	}
      }
      ss << "(a" << (m_decision_stack[i]->first+1) << ",[" << label.str() << "],m"
         << m_decision_stack[i]->second->back()->second << ")";
      if (i != 0)
        ss << ",";
    }
    DREAL_LOG_INFO << "Suggesting the Path: [" << ss.str() << "]";
    //    cout << "Suggesting the Path: [" << ss.str() << "]" << endl;
    return true;
}


  Clause*  hybrid_heuristic::getConflict(){
  vec< Lit >  literals;

  stringstream cc;
  if(m_stack_lim.size() > 0){
    int start = m_stack_lim[0];
    for(int i = start; i < m_stack.size(); i++){
	auto lit = m_stack[i];
	Enode* e = lit->first;
	//bool sign = lit->second;
	Lit l = (!lit->second ? theory_handler->enodeToLit(e) : ~theory_handler->enodeToLit(e));
	
	literals.push(l);
	cc << (sign(l) ? "(not ": "") <<  e << (sign(l) ? ")": "") << " ";
      }
  }

  DREAL_LOG_DEBUG << "Conflict from heuristic: (" << cc.str() << ")";
  
  return Clause_new(literals);
}
  
}


