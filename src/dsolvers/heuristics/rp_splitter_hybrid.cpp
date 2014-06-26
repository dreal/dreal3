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

#include "dsolvers/heuristics/rp_splitter_hybrid.h"
#include <algorithm>

// -------------------------------------------
// Class for domain splitting
// Enumeration of integer, bisection of reals
// Uses Hybrid System value selection heuristic
// -------------------------------------------
rp_splitter_mixed_hybrid::rp_splitter_mixed_hybrid(rp_problem * p):
  rp_splitter(p)
{}


void rp_splitter_mixed_hybrid::initialize(ode_sim_heuristic &ode_sim_heuristic){
  m_ode_sim_heuristic = &ode_sim_heuristic;
}

rp_splitter_mixed_hybrid::~rp_splitter_mixed_hybrid()
{}

void rp_splitter_mixed_hybrid::apply(rp_box_set& bs, int var) {
  rp_interval i1, i2;
  rp_box b1 = bs.remove_insert();
  this->observe(b1, var);
  rp_box b2 = bs.insert(b1);

  rp_box b1_copy;
  rp_box_clone(&b1_copy, b1);
  rp_box suggestion = m_ode_sim_heuristic->sim(b1_copy, var);


  DREAL_LOG_DEBUG << "rp_splitter_mixed_hybrid::apply() "
                  << "suggestion = " << var << " [" << rp_binf(rp_box_elem(suggestion, var)) << ", "
                  << rp_bsup(rp_box_elem(suggestion, var))
                  << "]";
  if (rp_variable_integer(rp_problem_var(*_problem, var)))  {
    if (this->integer_hole(rp_box_elem(b1, var),
                           rp_variable_domain(rp_problem_var(*_problem, var)),
                           i1, i2)){
      if (rp_interval_included(i1, rp_box_elem(suggestion, var))){
        rp_interval_copy(rp_box_elem(b1, var), i1);
        rp_interval_copy(rp_box_elem(b2, var), i2);
      } else{
        rp_interval_copy(rp_box_elem(b1, var), i2);
        rp_interval_copy(rp_box_elem(b2, var), i1);
      }
    } else  { // no hole found
      ++rp_binf(rp_box_elem(b1, var));
      if (rp_interval_included(rp_box_elem(b1, var), rp_box_elem(suggestion, var))){
        // Integer variable: [a,b] --> [a+1,b] and [a,a]
        rp_bsup(rp_box_elem(b2, var)) = rp_binf(rp_box_elem(b2, var));
      } else {
        --rp_binf(rp_box_elem(b1, var));
        ++rp_binf(rp_box_elem(b2, var));
        rp_bsup(rp_box_elem(b1, var)) = rp_binf(rp_box_elem(b1, var));
      }
    }
  }  else  {
    if (this->real_hole(rp_box_elem(b1, var),
                        rp_variable_domain(rp_problem_var(*_problem, var)),
                        i1, i2)) {
      if (rp_interval_included(i1, rp_box_elem(suggestion,  var))){
        rp_interval_copy(rp_box_elem(b1, var), i1);
        rp_interval_copy(rp_box_elem(b2, var), i2);
      }  else {
        rp_interval_copy(rp_box_elem(b1, var), i2);
        rp_interval_copy(rp_box_elem(b2, var), i1);
      }
    }  else {
      // Real variable: [a,b] --> [center,b] and [a,center]
      double mid = rp_interval_midpoint(rp_box_elem(b1, var));

      rp_binf(rp_box_elem(b1, var)) =
        rp_bsup(rp_box_elem(b2, var)) =
          mid;

      double b1Intersection =
        std::min(rp_bsup(rp_box_elem(b1, var)), rp_bsup(rp_box_elem(suggestion, var))) -
        std::max(rp_binf(rp_box_elem(b1, var)), rp_binf(rp_box_elem(suggestion, var)));
      double b2Intersection =
        std::min(rp_bsup(rp_box_elem(b2, var)), rp_bsup(rp_box_elem(suggestion, var))) -
        std::max(rp_binf(rp_box_elem(b2, var)), rp_binf(rp_box_elem(suggestion, var)));

      if (b2Intersection > b1Intersection
          // rp_interval_included(rp_box_elem(suggestion, var), rp_box_elem(b2, var))
          ){
        // okay
        DREAL_LOG_DEBUG << "rp_splitter_mixed_hybrid::apply() "
                        << "*[" << rp_binf(rp_box_elem(b2, var)) << ", " << rp_bsup(rp_box_elem(b2, var))
                        << "]* [" << rp_binf(rp_box_elem(b1, var)) << ", " << rp_bsup(rp_box_elem(b1, var))
                        << "]";
        // cout  << "*[" << rp_binf(rp_box_elem(b2, var)) << ", " << rp_bsup(rp_box_elem(b2, var))
        //                 << "]* [" << rp_binf(rp_box_elem(b1, var)) << ", " << rp_bsup(rp_box_elem(b1, var))
        //                 << "] \t";
      } else if (b2Intersection < b1Intersection){
          // rp_interval_included(rp_box_elem(suggestion, var), rp_box_elem(b1, var))){
        // reverse

        double b2_sup = rp_bsup(rp_box_elem(b1, var));
        rp_binf(rp_box_elem(b1, var)) = rp_binf(rp_box_elem(b2, var));
        rp_bsup(rp_box_elem(b1, var)) = mid;
        rp_binf(rp_box_elem(b2, var)) = mid;
        rp_bsup(rp_box_elem(b2, var)) = b2_sup;
        DREAL_LOG_DEBUG << "rp_splitter_mixed_hybrid::apply() "
                        << "[" << rp_binf(rp_box_elem(b1, var)) << ", " << rp_bsup(rp_box_elem(b1, var))
                        << "] *[" << rp_binf(rp_box_elem(b2, var)) << ", " << rp_bsup(rp_box_elem(b2, var))
                        << "]*";
        // cout << "[" << rp_binf(rp_box_elem(b1, var)) << ", " << rp_bsup(rp_box_elem(b1, var))
        //                 << "] *[" << rp_binf(rp_box_elem(b2, var)) << ", " << rp_bsup(rp_box_elem(b2, var))
        //                 << "]* \t";
      } else {
        DREAL_LOG_DEBUG << "rp_splitter_mixed_hybrid::apply() suggestion not found";
        DREAL_LOG_DEBUG << "rp_splitter_mixed_hybrid::apply() "
                        << "-[" << rp_binf(rp_box_elem(b2, var)) << ", " << rp_bsup(rp_box_elem(b2, var))
                        << "]- [" << rp_binf(rp_box_elem(b1, var)) << ", " << rp_bsup(rp_box_elem(b1, var))
                        << "]";
        // cout << "-[" << rp_binf(rp_box_elem(b2, var)) << ", " << rp_bsup(rp_box_elem(b2, var))
        //      << "]- [" << rp_binf(rp_box_elem(b1, var)) << ", " << rp_bsup(rp_box_elem(b1, var))
        //      << "] \t";
      }
    }
  }
  rp_box_destroy(&b1_copy);
}

rp_splitter_mixed_hybrid::rp_splitter_mixed_hybrid(const rp_splitter_mixed_hybrid& ds): rp_splitter(ds)
{}

rp_splitter_mixed_hybrid&
rp_splitter_mixed_hybrid::operator=(const rp_splitter_mixed_hybrid& /*ds*/){
  return( *this );
}
