/*********************************************************************
Author: Daniel Bryce <dbryce@sift.net>
        Soonho Kong <soonhok@cs.cmu.edu>
        Sicun Gao <sicung@cs.cmu.edu>

dReal -- Copyright (C) 2013 - 2016, the dReal Team

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

#include "opensmt/heuristics/heuristic.h"

#include <stddef.h>
#include <algorithm>
#include <chrono>
#include <map>
#include <ratio>
#include <sstream>
#include <unordered_set>
#include <utility>
#include <string>

#include "egraph/Enode.h"
#include "minisat/mtl/Vec.h"
#include "smtsolvers/SMTConfig.h"
#include "tsolvers/THandler.h"
#include "util/logging.h"
#include "util/stat.h"

class Egraph;

using std::string;
using std::ifstream;
using std::unordered_set;
using std::ios;
using std::sort;

namespace dreal {
heuristic::~heuristic() {}

void heuristic::initialize(SMTConfig & config, Egraph &, THandler *, vec<Lit> *, vec<int> *) {
    m_config = &config;
}

void heuristic::inform(Enode *) {}

void heuristic::backtrack() {}

Clause * heuristic::getConflict() { return NULL; }

Lit heuristic::getSuggestion() {
    DREAL_LOG_INFO << "heuristic::getSuggestion()";
    std::chrono::high_resolution_clock::time_point start_time =
        std::chrono::high_resolution_clock::now();

    Lit rvalue;

    bool unsat = false;
    if (!m_is_initialized) {
        rvalue = lit_Undef;
    } else {
        if (trail->size() > lastTrailEnd) {
            pushTrailOnStack();
            //}

            // if (!m_is_initialized ||  backtracked){
            unsat = !getSuggestions();
            backtracked = false;
        }

        if (  // false &&
            !m_config->nra_hybrid_notlearn_clause && unsat) {
            rvalue = lit_Error;
        } else {
            if (!m_suggestions.empty()) {
                std::pair<Enode *, bool> * s = m_suggestions.back();
                m_suggestions.pop_back();
                Enode * e = s->first;

                if (e == NULL) {
                    rvalue = lit_Undef;
                } else {
                    DREAL_LOG_INFO << "heuristic::getSuggestion() " << e << " = " << s->second;
                    if (theory_handler == NULL) DREAL_LOG_INFO << "heuristic::getSuggestion() NULL";
                    Var v = theory_handler->enodeToVar(e);
                    delete s;
                    rvalue = Lit(v, !s->second);
                }
            } else {
                rvalue = lit_Undef;
            }
        }
    }

    if (m_config->nra_use_stat) {
        std::chrono::high_resolution_clock::time_point end_time =
            std::chrono::high_resolution_clock::now();
        // DREAL_LOG_DEBUG << end_time << " " << start_time;

        std::chrono::duration<double> elapsed_seconds =
            std::chrono::duration_cast<std::chrono::duration<double>>(end_time - start_time);
        m_config->nra_stat.increase_heuristic_time(elapsed_seconds);
        DREAL_LOG_INFO << "heuristic::getSuggestion() used " << elapsed_seconds.count();
    }

    return rvalue;
}

bool heuristic::getSuggestions() { return true; }

void heuristic::displayTrail() {
    int indx_low = 0;
    int indx_high = 0;
    // DREAL_LOG_INFO << "Trail size = " << trail->size() << " " << trail_lim->size();
    DREAL_LOG_INFO << " -- Start Trail --";
    for (int level = 0; level <= trail_lim->size(); level++) {
        if (level > 0) {
            indx_low = (*trail_lim)[level - 1];
        }
        indx_high = (trail_lim->size() == level ? trail->size() : (*trail_lim)[level]);

        DREAL_LOG_INFO << " -- LEVEL " << level << " (" << indx_low << ", " << indx_high << ") -- ";
        for (int i = indx_low; i < indx_high; i++) {
            // DREAL_LOG_INFO << i << " " << var((*trail)[i]);
            if (var((*trail)[i]) > 1)  // 0 and 1 are false and true
                DREAL_LOG_INFO << i << ":\t" << theory_handler->varToEnode(var((*trail)[i]))
                               << " = " << !sign((*trail)[i]);
        }
    }
    DREAL_LOG_INFO << " -- End Trail --";
}

void heuristic::displayStack(int bt_point) {
    int indx_low = 0;
    int indx_high = 0;
    // DREAL_LOG_INFO << "Trail size = " << trail->size() << " " << trail_lim->size();
    DREAL_LOG_INFO << " -- Start Stack --";
    for (unsigned int level = 0; level <= m_stack_lim.size(); level++) {
        if (level > 0) {
            indx_low = m_stack_lim[level - 1];
        }
        indx_high = (m_stack_lim.size() == level ? m_stack.size() : m_stack_lim[level]);

        DREAL_LOG_INFO << " -- LEVEL " << level << " (" << indx_low << ", " << indx_high << ") -- ";
        for (int i = indx_low; i < indx_high; i++) {
            DREAL_LOG_INFO << (bt_point <= i ? "*" : "") << i << ":\t" << m_stack[i]->first << " = "
                           << m_stack[i]->second;
        }
    }
    DREAL_LOG_INFO << " -- End Stack --";
}

void heuristic::pushTrailOnStack() {}

bool heuristic::isStackConsistentWithSuggestion() {
    // return true if no suggestion is inconsistent with the stack
    for (auto sug : m_suggestions) {
        for (auto sta : m_stack) {
            if (sug->first == sta->first && sug->second != sta->second) {
                DREAL_LOG_DEBUG << "Stack and Suggestion Inconsistent: " << sug->first << " = "
                                << sug->second << " " << sta->first << " = " << sta->second;
                return false;
            }
        }
    }
    return true;
}
}
