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

#pragma once
#include <iostream>
#include <unordered_map>
#include <vector>
#include <utility>
#include "opensmt/egraph/Enode.h"

// Backtrackable scoped_vec. -- Soonho Kong

namespace dreal {
template<typename T>
class scoped_vec {
private:
    typedef std::vector<T> vec;
    typedef typename vec::value_type      value_type;
    typedef typename vec::iterator        iterator;
    typedef typename vec::const_iterator  const_iterator;
    typedef typename vec::size_type       size_type;
    typedef typename vec::reference       reference;
    typedef typename vec::const_reference const_reference;

    vec                   m_vec;
    std::vector<unsigned> m_scopes;

public:
    scoped_vec() { }
    ~scoped_vec() { }
    iterator       begin()        { return m_vec.begin(); }
    iterator       end()          { return m_vec.end(); }
    const_iterator begin()  const { return m_vec.cbegin(); }
    const_iterator end()    const { return m_vec.cend(); }
    const_iterator cbegin() const { return m_vec.cbegin(); }
    const_iterator cend()   const { return m_vec.cend(); }
    void push_back(value_type const & v) { m_vec.push_back(v); }
    void push() { m_scopes.push_back(m_vec.size()); };
    unsigned int pop() {
        unsigned int count = 0;
        unsigned const prev_size = m_scopes.back();
        m_scopes.pop_back();
        unsigned cur_size = m_vec.size();
        while (cur_size-- > prev_size) { m_vec.pop_back(); count++; }
        return count;
    }
    unsigned size() const    { return m_vec.size(); }
    vec const & get_vec() { return m_vec; }
    friend std::ostream & operator<<(std::ostream & out, scoped_vec<T> const & v) {
        for (auto const & e : v) {
            out << e << std::endl;
        }
        return out;
    }
    reference first() {
        assert(m_vec.size() > 0);
        return m_vec[0];
    }
    const_reference first() const {
        assert(m_vec.size() > 0);
        return m_vec[0]; }
    reference last() {
        assert(m_vec.size() > 0);
        return m_vec[size() - 1];
    }
    const_reference last() const {
        assert(m_vec.size() > 0);
        return m_vec[size() - 1];
    }
    reference operator[] (size_type n) { return m_vec[n]; }
    const_reference operator[] (size_type n) const { return m_vec[n]; }
};
}
