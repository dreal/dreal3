#include "dsolvers/util/scoped_vec.h"

scoped_vec::scoped_vec()  { }
scoped_vec::~scoped_vec() { }
void scoped_vec::push_back(value_type const & v) {
    m_vec.push_back(v);
}
void scoped_vec::push() {
    m_scopes.push_back(m_vec.size());
}
void scoped_vec::pop() {
    unsigned const prev_size = m_scopes.back();
    m_scopes.pop_back();
    unsigned cur_size = m_vec.size();
    while (cur_size-- > prev_size) { m_vec.pop_back(); }
}
std::ostream & operator<<(std::ostream & out, scoped_vec const & s) {
    for (auto ite = s.begin(); ite != s.end(); ite++) {
        out << "asserted literal : " << *ite << "\t" << (*ite)->hasPolarity() << endl;
    }
    return out;
}
