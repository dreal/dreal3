#include "hybrid/odes.h"

#include <initializer_list>
#include <iostream>
#include <sstream>
#include <string>

namespace dreal {
namespace hybrid {
using std::endl;
using std::ostream;
using std::ostringstream;
using std::string;
using std::initializer_list;

odes::odes(initializer_list<value_type> const init) : m_system{init} {}

void odes::insert(key_type const & key, mapped_type const & elem) { m_system.emplace(key, elem); }

string odes::to_string() const {
    ostringstream oss;
    oss << *this;
    return oss.str();
}

odes::mapped_type & odes::operator[](key_type const & key) { return m_system[key]; }

ostream & operator<<(ostream & os, odes const & odes) {
    for (auto const & p : odes) {
        os << "d[" << p.first << "]/dt = " << p.second << endl;
    }
    return os;
}
}  // namespace hybrid
}  // namespace dreal
