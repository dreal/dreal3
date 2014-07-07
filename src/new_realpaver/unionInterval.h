#pragma once
#include <algorithm>
#include <list>
#include <initializer_list>
#include <iostream>
#include "new_realpaver/interval.h"

using std::any_of;
using std::cout;
using std::endl;

namespace realpaver {
class unionInterval {
public:
    typedef std::list<interval> list;
    typedef list::size_type size_type;
    typedef list::iterator iterator;
    typedef list::const_iterator const_iterator;
    typedef list::reverse_iterator reverseiterator;
    typedef list::const_reverse_iterator const_reverse_iterator;
private:
    list m_list;
public:
    unionInterval() { }
    unionInterval(list const & l) : m_list(l) { }
    unionInterval(interval const & i) : m_list() { insert(i); }
    unionInterval(unionInterval const & u) : m_list(u.m_list) { }
    unionInterval(std::initializer_list<interval> il) : m_list() {
        for (interval const & i : il) { insert(i); }
    }
    iterator       begin()        { return m_list.begin(); }
    iterator       end()          { return m_list.end(); }
    const_iterator begin()  const { return m_list.cbegin(); }
    const_iterator end()    const { return m_list.cend(); }
    const_iterator cbegin() const { return m_list.cbegin(); }
    const_iterator cend()   const { return m_list.cend(); }
    size_type size() const { return m_list.size(); }
    bool isEmpty() const { return m_list.empty(); }
    bool equals(unionInterval const & u) const { return m_list == u.m_list; }
    bool includes(double const x) const {
        return any_of(m_list.begin(), m_list.end(), [x](interval const &i) { return i.includes(x); });
    }
    bool includes(interval const & i) const {
        return any_of(m_list.begin(), m_list.end(), [&i](interval const &j) { return j.includes(i); });
    }
    bool includes(unionInterval const & u) const {
        return all_of(u.begin(), u.end(), [this](interval const &i) { return includes(i); });
    }
    bool lt(double const x) const {
        // empty() => [+oo, -oo]
        if (isEmpty()) { return true; }
        return m_list.back().sup < x;
    }
    bool lt(interval const & i) const {
        // empty() => [+oo, -oo]
        if (isEmpty()) { return true; }
        return m_list.back().sup < i.inf;
    }
    bool lte(double const x) const {
        // empty() => [+oo, -oo]
        if (isEmpty()) { return true; }
        return m_list.back().sup <= x;
    }
    bool lte(interval const & i) const {
        // empty() => [+oo, -oo]
        if (isEmpty()) { return true; }
        return m_list.back().sup <= i.inf;
    }
    bool gt(double const x) const {
        // empty() => [+oo, -oo]
        if (isEmpty()) { return true; }
        return x < m_list.front().inf;
    }
    bool gt(interval const & i) const {
        // empty() => [+oo, -oo]
        if (isEmpty()) { return true; }
        return i.sup < m_list.front().inf;
    }
    bool gte(double const x) const {
        // empty() => [+oo, -oo]
        if (isEmpty()) { return true; }
        return x <= m_list.front().inf;
    }
    bool gte(interval const & i) const {
        // empty() => [+oo, -oo]
        if (isEmpty()) { return true; }
        return i.sup <= m_list.front().inf;
    }
    friend bool operator<(unionInterval const & u, double const x)  { return u.lt(x); }
    friend bool operator<(double const x, unionInterval const & u)  { return u.gt(x); }
    friend bool operator<=(unionInterval const & u, double const x) { return u.lte(x); }
    friend bool operator<=(double const x, unionInterval const & u) { return u.gte(x); }
    friend bool operator>(unionInterval const & u, double const x)  { return u.gt(x); }
    friend bool operator>(double const x, unionInterval const & u)  { return u.gt(x); }
    friend bool operator>=(unionInterval const & u, double const x) { return u.gte(x); }
    friend bool operator>=(double const x, unionInterval const & u) { return u.gte(x); }
    friend bool operator<(unionInterval const & u, interval const & i)  { return u.lt(i); }
    friend bool operator<(interval const & i, unionInterval const & u)  { return u.gt(i); }
    friend bool operator<=(unionInterval const & u, interval const & i) { return u.lte(i); }
    friend bool operator<=(interval const & i, unionInterval const & u) { return u.gte(i); }
    friend bool operator>(unionInterval const & u, interval const & i)  { return u.gt(i); }
    friend bool operator>(interval const & i, unionInterval const & u)  { return u.gt(i); }
    friend bool operator>=(unionInterval const & u, interval const & i) { return u.gte(i); }
    friend bool operator>=(interval const & i, unionInterval const & u) { return u.gte(i); }
    double nextDouble(double const x) const {
        for (const_iterator it = m_list.cbegin(); it != m_list.cend(); it++) {
            //  x:          |
            // it:                [         ]
            if (x <= it->inf) { return it->inf; }
            //  x:          |
            // it:      [         ]
            if (it->inf <= x && x <= it->sup) { return x; }
        }
        return +interval::DBL_INFINITY;
    }
    double prevDouble(double const x) const {
        for (const_reverse_iterator it = m_list.crbegin(); it != m_list.crend(); it++) {
            //  x:          |
            // it: [     ]
            if (it->sup <= x) { return it->sup; }
            //  x:          |
            // it:      [         ]
            if (it->inf <= x && x <= it->sup) { return x; }
        }
        return -interval::DBL_INFINITY;
    }
    void setEmpty() {
        m_list.clear();
    }
    interval hull() const;
    void insert(interval const & i);
    void insert(unionInterval const & u);
    bool inter(interval const & i) {
        for (iterator it = m_list.begin(); it != m_list.end();) {
            //  i:           [       ]
            // it: [       ]
            if (it->sup < i.inf) { it++; continue; }

            //  i: [       ]
            // it:           [       ]
            if (i.sup < it->inf) { break; }

            //  i :  [         ]
            // it :    [         ]
            // it':    [       ]
            it->inter(i); it++;
        }
        return isEmpty();
    }
    bool inter(unionInterval const & u) {
        // TODO(soonhok): currently, it's O(n^2). Can implmenet O(n) algorithm.
        for (interval const & i : u) {
            bool result = inter(i);
            if (!result) return false;
        }
        return true;
    }

    unionInterval & operator=(unionInterval const & u) {
        m_list = u.m_list;
        return *this;
    }


    bool operator==(unionInterval const & u) {
        return equals(u);
    }

    bool operator!=(unionInterval const & u) {
        return !equals(u);
    }
    friend std::ostream& operator<<(std::ostream& out, unionInterval const & u);
};

unionInterval intervalExtendedDiv(interval const & i1, interval const & i2);
std::ostream& operator<<(std::ostream& out, unionInterval const & u);
}
