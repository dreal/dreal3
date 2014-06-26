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
#include <iomanip>
#include "dsolvers/heuristics/ode_sim_heuristic.h"
#include "opensmt/egraph/Egraph.h"
#include "util/logging.h"
#include "util/interval.h"

using std::string;
using std::ifstream;
using std::unordered_set;
using std::ios;
using std::sort;

namespace dreal{
  void ode_sim_heuristic::initialize(rp_propagator &propag, rp_problem &p) {
    m_propag = &propag;
    m_rp_problem = &p;
  }

  void ode_sim_heuristic::add_mode(SMTConfig & config, Egraph & egraph, Enode* l_int, // vector<Enode*> invs,
                                   std::unordered_map<Enode*, int> & enode_to_rp_id, std::unordered_map<int, Enode*> & rp_id_to_enode){
    DREAL_LOG_DEBUG << "ode_sim_heuristic::add_mode " << l_int;

    Enode* m_time = l_int->getCdr()->getCdr()->getCdr()->getCar();
    string time_str = m_time->getCar()->getName();                       // i.e. "time_1"
    int m_step = stoi(time_str.substr(time_str.find_last_of("_") + 1));      // i.e. 1
    m_mode_sims[m_step] = new ode_mode_sim(config, egraph, l_int, // invs,
                                           enode_to_rp_id);
    m_rp_id_to_enode = &rp_id_to_enode;
    m_enode_to_rp_id = &enode_to_rp_id;
  }

  void ode_sim_heuristic::display_interval(ostream & out, rp_interval i, int digits, bool exact) const {
    static interval tmp;
    tmp.lb = rp_binf(i);
    tmp.ub = rp_bsup(i);
    tmp.print(out, digits, exact);
  }


  void ode_sim_heuristic::pprint_vars(ostream & out, rp_box b, bool exact) const {
    for (int i = 0; i <rp_problem_nvar(*m_rp_problem); i++) {
      out << std::setw(15);
      out << rp_variable_name(rp_problem_var(*m_rp_problem, i));
      out << " : ";
      display_interval(out, rp_box_elem(b, i), 16, exact);
      if (i != rp_problem_nvar(*m_rp_problem) - 1)
        out << ";";
      out << endl;
    }
}

  rp_box ode_sim_heuristic::sim(rp_box &box, int varToGet){
    DREAL_LOG_DEBUG << "ode_sim_heuristic::sim() with modes " << m_mode_sims.size();


    rp_box & sim_box(box);

    Enode* eVarToGet = (*m_rp_id_to_enode)[varToGet];

    string name = eVarToGet->getCar()->getName();
    int startTimeIndex = name.find("_")+1;
    int endTimeIndex = name.find("_", startTimeIndex);
     int time = atoi(name.substr(startTimeIndex, endTimeIndex).c_str());

     for (int i = 0; i <= time; // static_cast<int>(m_mode_sims.size());
            i++){
      DREAL_LOG_DEBUG << "ode_sim_heuristic::sim step " << i;
      vector<pair<capd::interval, DVector>> bucket;
      ode_mode_sim & current_mode = *m_mode_sims[i];

      current_mode.update(sim_box);
      current_mode.compute_forward(bucket);

      Enode* modeTime = current_mode.getTime();
      int rp_id = (*m_enode_to_rp_id)[modeTime];
      double modeTimeLB = rp_binf(rp_box_elem(sim_box, rp_id));
      double modeTimeUB = rp_bsup(rp_box_elem(sim_box, rp_id));

      // rp_box first_box;
      // rp_box last_box;
      // boolean got_first = false;

      for (int j = 0; j < static_cast<int>(bucket.size()); j++){
        pair<capd::interval, DVector> p = bucket[j];
        if (p.first.rightBound() >= modeTimeLB && p.first.leftBound() <= modeTimeUB){
          pair<capd::interval, DVector> prev = (j > 0 ? bucket[j-1] : bucket[j]);
        // pair<capd::interval, DVector> next = (j < ((int)bucket.size() - 1) ? bucket[j+1] : bucket[j]);
        rp_box temp_box;
        rp_box_clone(&temp_box, sim_box);


        current_mode.update_box(temp_box, p.second, prev.second, p.first);
        if (!m_propag->apply_all(temp_box)){
          stringstream ss;
          pprint_vars(ss, temp_box, false);
          DREAL_LOG_DEBUG << ss.str();
          DREAL_LOG_DEBUG << "ode_sim_heuristic::sim UNSAT BOX ";
          rp_box_destroy(&temp_box);
        } else {
          stringstream ss;
          pprint_vars(ss, temp_box, false);
          DREAL_LOG_DEBUG << ss.str();
          DREAL_LOG_DEBUG << "ode_sim_heuristic::sim SAT BOX ";
          // guard is satisfied
          rp_box_destroy(&sim_box);

          sim_box = temp_box;
          break;
        }
      }
      }
    }
    return sim_box;
  }

ode_sim_heuristic&
ode_sim_heuristic::operator=(const ode_sim_heuristic& /*ds*/) {
  return( *this );
}
}
