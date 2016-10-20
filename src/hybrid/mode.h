#pragma once

#include <unordered_map>

#include "hybrid/odes.h"
#include "opensmt/egraph/Enode.h"

namespace dreal {
namespace hybrid {

/* Represents a mode in a hybrid system. */
class mode {
public:
    typedef Enode * formula;
    /** Default constructor. */
    mode() = default;
    /** Move-construct a set from an rvalue. */
    mode(mode && e) = default;
    /** Copy-construct a set from an lvalue. */
    mode(mode const & e) = default;
    /** Move-assign a set from an rvalue. */
    mode & operator=(mode && e) = default;
    /** Copy-assign a set from an lvalue. */
    mode & operator=(mode const & e) = default;
    /** Constructs a mode with `p odes and \p invariant */
    mode(int id, odes const & odes) : m_id(id), m_odes{odes}, m_invariant{} {}
    /** Constructs a mode with `p odes and \p invariant */
    mode(int id, odes const & odes, formula invariant)
        : m_id{id}, m_odes{odes}, m_invariant{invariant} {}

    /** Returns string representation. */
    std::string to_string() const;

    int get_id() const { return m_id; }
    odes const & get_odes() const { return m_odes; }
    formula const & get_invariant() const { return m_invariant; }

    odes get_odes() { return m_odes; }
    formula get_invariant() { return m_invariant; }

private:
    // Represents the ID of a mode.
    int const m_id;
    // Represents dynamics of a mode as a system of ODEs.
    odes m_odes;
    // Represents invariant of a mode.
    formula m_invariant;
};

std::ostream & operator<<(std::ostream & os, mode const & mode);
}  // namespace hybrid
}  // namespace dreal
