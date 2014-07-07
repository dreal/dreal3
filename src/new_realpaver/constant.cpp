#include <iostream>
#include "new_realpaver/constant.h"

using std::ostream;
using std::endl;

namespace realpaver {

ostream & operator<<(ostream & out, constant const & c) {
    out << c.m_name << " := " << c.m_val << endl;
    return out;
}

}
