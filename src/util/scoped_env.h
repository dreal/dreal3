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

#pragma once
#include <iostream>
#include <unordered_map>
#include <vector>
#include <utility>
#include "opensmt/egraph/Enode.h"
#include "util/interval.h"

namespace dreal {
class scoped_env {
private:
    typedef Enode * key_type;
    typedef interval mapped_type;
    typedef std::unordered_map<key_type, mapped_type> map;
    typedef map::value_type value_type;
    typedef map::iterator iterator;
    typedef map::const_iterator const_iterator;

    enum class Action {INSERT, UPDATE, ERASE};
    typedef std::pair<Action, value_type> record;
    map                   m_map;
    std::vector<record>   m_actions;
    std::vector<unsigned> m_scopes;

public:
    scoped_env();
    ~scoped_env();
    iterator begin()              { return m_map.begin(); }
    iterator end()                { return m_map.end(); }
    const_iterator begin()  const { return m_map.cbegin(); }
    const_iterator end()    const { return m_map.cend(); }
    const_iterator cbegin() const { return m_map.cbegin(); }
    const_iterator cend()   const { return m_map.cend(); }
    void insert(key_type const & k);
    void insert(key_type const & k, mapped_type const & v);
    void update(key_type const & k, mapped_type const & v);
    iterator find(key_type const & k)             { return m_map.find(k); }
    const_iterator find(key_type const & k) const { return m_map.find(k); }
    mapped_type lookup(key_type const & k);
    void erase(key_type const & k);
    void push();
    void pop();
    unsigned size() const;
    friend std::ostream & operator<<(std::ostream & out, scoped_env const & e);
};

std::ostream & operator<<(std::ostream & out, scoped_env const & e);
}
