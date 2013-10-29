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
