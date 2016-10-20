#include "hybrid/mode.h"

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

/** Returns string representation. */
string mode::to_string() const {
    ostringstream oss;
    oss << *this;
    return oss.str();
}

ostream & operator<<(ostream & os, mode const & mode) {
    os << "mode id: " << mode.get_id() << endl;
    os << "odes:" << endl << mode.get_odes() << endl;
    mode::formula const invariant = mode.get_invariant();
    if (invariant) {
        os << "invariant: " << invariant;
    }
    return os;
}
}  // namespace hybrid
}  // namespace dreal
