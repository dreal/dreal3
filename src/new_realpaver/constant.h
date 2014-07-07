#pragma once

#include <string>
#include "new_realpaver/interval.h"

namespace realpaver {

class constant {
private:
    std::string m_name;
    interval m_val;

public:
    constant(interval i) :
        m_name(""), m_val(i) { }
    constant(const char * s, interval i) :
        m_name(s), m_val(i) { }
    constant(std::string const & s, interval i) :
        m_name(s), m_val(i) { }
    std::string getName() const { return m_name; }

    friend std::ostream & operator<<(std::ostream & out, constant const & c);
};

std::ostream & operator<<(std::ostream & out, constant const & c);
}
