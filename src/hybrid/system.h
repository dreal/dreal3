#pragma once

#include <ostream>
#include <string>
#include <tuple>
#include <unordered_map>

#include "hybrid/mode.h"
#include "opensmt/egraph/Enode.h"

namespace dreal {
namespace hybrid {

/* Represents a hybrid system. */
class system {
public:
    typedef int mode_num;
    typedef Enode * guard;
    typedef Enode * reset;

    /** Default constructor. */
    system() = default;
    /** Move-construct a set from an rvalue. */
    system(system && s) = default;
    /** Copy-construct a set from an lvalue. */
    system(system const & s) = default;
    /** Move-assign a set from an rvalue. */
    system & operator=(system && s) = default;
    /** Copy-assign a set from an lvalue. */
    system & operator=(system const & s) = default;

    /** Returns string representation. */
    std::string to_string() const;
    friend std::ostream & operator<<(std::ostream & os, const system & system);

private:
    /* Store modes in a hybrid system as a map from "mode number" to "mode". */
    std::unordered_map<mode_num, mode> m_mode_map;

    /* Store jumps in a hybrid system as a map.
     *
     * To represent a jump from mode i to mode j with guard G and
     * reset R, we have m_jump_map[i] = (j, G, R).
     */
    std::unordered_map<mode_num, std::tuple<mode_num, guard, reset>> m_jump_map;
};
}  // namespace hybrid
}  // namespace dreal
