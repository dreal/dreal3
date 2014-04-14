/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>
        Sicun Gao <sicung@cs.cmu.edu>
        Edmund Clarke <emc@cs.cmu.edu>

dReal -- Copyright (C) 2013, Soonho Kong, Sicun Gao, and Edmund Clarke

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

class scoped_vec {
private:
    typedef std::vector<Enode *> vec;
    typedef vec::value_type      value_type;
    typedef vec::iterator        iterator;
    typedef vec::const_iterator  const_iterator;
    typedef vec::size_type       size_type;
    typedef vec::reference       reference;
    typedef vec::const_reference const_reference;

    vector<Enode *>  m_vec;
    vector<unsigned> m_scopes;

public:
    scoped_vec();
    ~scoped_vec();
    iterator       begin()        { return m_vec.begin(); }
    iterator       end()          { return m_vec.end(); }
    const_iterator begin()  const { return m_vec.cbegin(); }
    const_iterator end()    const { return m_vec.cend(); }
    const_iterator cbegin() const { return m_vec.cbegin(); }
    const_iterator cend()   const { return m_vec.cend(); }
    void push_back(value_type const & v);
    void push();
    void pop();
    unsigned size() const { return m_vec.size(); }
    friend std::ostream & operator<<(std::ostream & out, scoped_vec const & e);
    reference operator[] (size_type n);
    const_reference operator[] (size_type n) const;
};

std::ostream & operator<<(std::ostream & out, scoped_vec const & e);
