/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>
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

/*********************************************************************
 Backtrackable scoped_env. -- Soonho Kong

 This code is inspired by Leonardo de Moura's scoped_map code:

   https://github.com/leodemoura/lean/blob/master/src/util/scoped_map.h
*********************************************************************/

#include <cassert>
#include <iomanip>
#include <iostream>
#include "util/scoped_env.h"

using std::endl;
using std::setfill;
using std::setprecision;
using std::setw;

namespace dreal {

scoped_env::scoped_env() {
}

scoped_env::~scoped_env() {
}

void scoped_env::insert(key_type const & k) {
    insert(k, interval(k->getLowerBound(), k->getUpperBound()));
}

void scoped_env::insert(key_type const & k, mapped_type const & v) {
    auto p = make_pair(k, v);
    auto ite = m_map.find(k);
    if (ite != m_map.end()) {
        m_actions.push_back(make_pair(Action::UPDATE, *ite));
        m_map[k] = v;
    } else {
        m_actions.push_back(make_pair(Action::INSERT, p));
        m_map.insert(make_pair(k, v));
    }
}

void scoped_env::update(key_type const & k, mapped_type const & v) {
    auto ite = m_map.find(k);
    assert(ite != m_map.end());
    m_actions.push_back(make_pair(Action::UPDATE, *ite));
    m_map[k] = v;
}

scoped_env::mapped_type scoped_env::lookup(key_type const & k) {
    auto ite = m_map.find(k);
    return ite->second;
}

void scoped_env::erase(key_type const & k) {
    auto ite = m_map.find(k);
    assert(ite != m_map.end());
    m_actions.push_back(make_pair(Action::ERASE, *ite));
    m_map.erase(k);
}


void scoped_env::push() {
    m_scopes.push_back(m_actions.size());
}

void scoped_env::pop() {
    unsigned prev_size = m_scopes.back();
    unsigned c = m_actions.size();
    while (c-- > prev_size) {
        auto action = m_actions.back();
        switch (action.first) {
        case Action::UPDATE: {
            auto & k = action.second.first;
            auto & v = action.second.second;
            m_map[k] = v;
        }
            break;
        case Action::INSERT:
            m_map.erase(action.second.first);
            break;
        case Action::ERASE:
            m_map.insert(action.second);
            break;
        }
        m_actions.pop_back();
    }
    m_scopes.pop_back();
}

unsigned scoped_env::size() const {
    return m_map.size();
}

std::ostream & operator<<(std::ostream & out, scoped_env const & e) {
    for (auto const & p : e) {
        out << setfill(' ') << setw(15) << p.first
            << " : " << p.second << ";" << endl;
    }
    return out;
}
}
