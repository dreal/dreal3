#pragma once
#include <iostream>
#include <unordered_map>
#include <vector>
#include <utility>
#include "opensmt/egraph/Enode.h"

// Backtrackable scoped_env. -- Soonho Kong
//
// This code is inspired by Leonardo de Moura's scoped_map code.
//   https://github.com/leodemoura/lean/blob/master/src/util/scoped_map.h

class scoped_env {
private:
    typedef std::unordered_map<Enode *, std::pair<double, double>> map;
    typedef map::key_type key_type;
    typedef map::value_type value_type;
    typedef map::mapped_type mapped_type;
    typedef map::const_iterator const_iterator;

    enum class Action {INSERT, UPDATE, ERASE};
    typedef std::pair<Action, value_type> record;
    map                   m_map;
    std::vector<record>   m_actions;
    std::vector<unsigned> m_scopes;

public:
    scoped_env();
    ~scoped_env();
    const_iterator begin() const { return m_map.cbegin(); }
    const_iterator end() const { return m_map.cend(); }
    void insert(key_type const & k, mapped_type const & v);
    void erase(key_type const & k);
    void push();
    void pop();
    unsigned size() const;
    friend std::ostream & operator<<(std::ostream & out, scoped_env const & e);
};

std::ostream & operator<<(std::ostream & out, scoped_env const & e);
