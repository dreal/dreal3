#include <assert.h>
#include "dsolvers/util/scoped_env.h"

scoped_env::scoped_env() {
}

scoped_env::~scoped_env() {
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
    std::cerr << "Insert(" << k << ", [" << v.first << ", " << v.second << "])" << std::endl;
}

void scoped_env::erase(key_type const & k) {
    auto ite = m_map.find(k);
    assert(ite != m_map.end());
    m_actions.push_back(make_pair(Action::ERASE, *ite));
    m_map.erase(k);
}


void scoped_env::push() {
    std::cerr << "Push() " << m_actions.size() << std::endl;
    m_scopes.push_back(m_actions.size());
}

void scoped_env::pop() {
    unsigned prev_size = m_scopes.back();
    unsigned c = m_actions.size();
    std::cerr << "pop() Prev_size = " << prev_size << "\t"
              << "c = " << c << std::endl;

    while (c-- > prev_size) {
        auto action = m_actions.back();
        switch(action.first) {
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
    out << "{";
    for (auto p : e) {
        out << p.first << " |-> [" << p.second.first << ", " << p.second.second << "]; ";
    };

    out << "}";
    return out;
}
