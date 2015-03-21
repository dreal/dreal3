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
#include "heuristic.h"
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
  heuristic::~heuristic(){
  }

  void heuristic::initialize(SMTConfig &, Egraph &, THandler* thandler,
			     vec<Lit> *trail, vec<int> *trail_lim)  {
  }

  void heuristic::inform(Enode * e){
  }

  void heuristic::backtrack(){   
  }

  Lit heuristic::getSuggestion(){
  DREAL_LOG_INFO << "heuristic::getSuggestion()";
    if (!m_is_initialized || m_suggestions.empty()){
      getSuggestions();
    }
    if (!m_suggestions.empty()){
      std::pair<Enode *, bool> *s = m_suggestions.back();
      m_suggestions.pop_back();
      Enode *e = s->first;


    if ( e == NULL )
      return lit_Undef;



    DREAL_LOG_INFO << "heuristic::getSuggestion() " << e;
    if (theory_handler == NULL)
      DREAL_LOG_INFO << "heuristic::getSuggestion() NULL";
    Var v = theory_handler->enodeToVar(e);
    delete s;
    return Lit( v, !s->second );
    } else {
      return lit_Undef;
    }
  }

  void heuristic::getSuggestions(){
  }
}
