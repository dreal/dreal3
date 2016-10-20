#pragma once
#include <unordered_map>
#include "opensmt/egraph/Enode.h"

namespace dreal {
namespace hybrid {

/* Represents a system of ODEs. */
class odes {
public:
    typedef Enode * var;
    typedef Enode * equation;
    typedef var key_type;
    typedef equation mapped_type;
    typedef typename std::unordered_map<key_type, mapped_type> map;
    /** std::pair<key_type, mapped_type> */
    typedef typename map::value_type value_type;
    typedef typename map::iterator iterator;
    typedef typename map::const_iterator const_iterator;

    /** Default constructor. */
    odes() = default;
    /** Move-construct a set from an rvalue. */
    odes(odes && odes) = default;
    /** Copy-construct a set from an lvalue. */
    odes(const odes & odes) = default;
    /** Move-assign a set from an rvalue. */
    odes & operator=(odes && odes) = default;
    /** Copy-assign a set from an lvalue. */
    odes & operator=(const odes & odes) = default;
    /** List constructor. Constructs a system of ODEs from a list of
     * (var * equation). */
    odes(std::initializer_list<value_type> init);

    /** Returns an iterator to the beginning. */
    iterator begin() { return m_system.begin(); }
    /** Returns an iterator to the end. */
    iterator end() { return m_system.end(); }
    /** Returns a const iterator to the beginning. */
    const_iterator begin() const { return m_system.cbegin(); }
    /** Returns a const iterator to the end. */
    const_iterator end() const { return m_system.cend(); }
    /** Returns a const iterator to the beginning. */
    const_iterator cbegin() const { return m_system.cbegin(); }
    /** Returns a const iterator to the end. */
    const_iterator cend() const { return m_system.cend(); }

    /** Inserts a pair (\p key, \p elem). */
    void insert(const key_type & key, const mapped_type & elem);
    /** Checks whether the container is empty.  */
    bool empty() const { return m_system.empty(); }
    /** Returns the number of elements. */
    size_t size() const { return m_system.size(); }

    /** Finds element with specific key. */
    iterator find(const key_type & key) { return m_system.find(key); }
    /** Finds element with specific key. */
    const_iterator find(const key_type & key) const { return m_system.find(key); }

    /** Returns string representation. */
    std::string to_string() const;

    /** Returns a reference to the value that is mapped to a key equivalent to
     * \p key, performing an insertion if such key does not already exist. */
    mapped_type & operator[](const key_type & key);

    friend std::ostream & operator<<(std::ostream & os, const odes & odes);

private:
    /* m_system stores a system of ODEs as a map from var to
     * equation. Given a system of ODEs
     *
     *    d[x1]/dt = f1(x1, ..., xn)
     *            ...
     *    d[xn]/dt = fn(x1, ..., xn)
     *
     * we have m_system[x1] = f1, ..., m_system[xn] = fn.
     */
    map m_system;
};
}  // namespace hybrid
}  // namespace dreal
