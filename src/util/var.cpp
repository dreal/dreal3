#include "util/var.h"
#include <stdexcept>
#include <string>

using std::logic_error;
using std::string;

namespace dreal {

std::ostream & operator<<(std::ostream & out, var_type const & ty) {
    switch (ty) {
    case var_type::INT:
        out << "int";
        break;
    case var_type::REAL:
        out << "real";
        break;
    }
    return out;
}

var_type findType(Enode * const e) {
    if (e->hasSortReal()) {
        return var_type::REAL;
    } else if (e->hasSortInt()) {
        return var_type::INT;
    }
    string varname = e->getCar()->getName();
    throw logic_error("Variable " + varname + " does not have either INT or REAL sort.");
}

var::var(Enode * const e) :
    m_enode(e),
    m_domain(e->getLowerBound(), e->getUpperBound()),
    m_value(m_domain),
    m_name(e->getCar()->getName()),
    m_type(findType(e)) {
}

void var::intersect(var const v) {
    m_value.intersect(v.m_value);
}

std::ostream & operator<<(std::ostream & out, var const & v) {
    out << v.m_name << " : " << v.m_type << " = " << v.m_value << " in " << v.m_domain;
    return out;
}

}
