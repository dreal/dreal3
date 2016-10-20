#include "hybrid/system.h"

#include <iostream>
#include <ostream>
#include <sstream>
#include <string>
#include <tuple>
#include <unordered_map>

namespace dreal {
namespace hybrid {

using std::endl;
using std::ostream;
using std::ostringstream;
using std::string;
using std::get;

string system::to_string() const {
    ostringstream oss;
    oss << *this;
    return oss.str();
}

ostream & operator<<(ostream & os, system const & system) {
    os << "Modes:" << endl;
    for (auto const & p : system.m_mode_map) {
        os << p.second << endl;
    }
    os << "Jumps:" << endl;
    for (auto const & p : system.m_jump_map) {
        system::mode_num const from = p.first;
        system::mode_num const to = get<0>(p.second);
        system::guard const guard = get<1>(p.second);
        system::reset const reset = get<2>(p.second);
        // clang-format off
        os << "Jump " << from << " -> " << to
           << " Guard: " << guard
           << " Reset: " << reset;
        // clang-format on
    }
    return os;
}

}  // namespace hybrid
}  // namespace dreal
