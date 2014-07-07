#include <algorithm>
#include <cassert>
#include <iostream>
#include <numeric>

#include "new_realpaver/box.h"
#include "new_realpaver/interval.h"

using std::accumulate;
using std::max;
using std::max_element;
using std::any_of;
using std::endl;

namespace realpaver {

box::box(size_type n) :
    m_safe(false),
    m_inner(false),
    m_isafe(false),
    m_nvdec(0),
    m_nvaux(0) {
    enlarge(n);
}

box::~box() {}

box::box(box const & b) :
    m_safe(b.m_safe),
    m_inner(b.m_inner),
    m_isafe(b.m_isafe),
    m_nvdec(b.m_nvdec),
    m_nvaux(b.m_nvaux),
    m_elems(b.m_elems)
{ }

bool box::isEmpty() {
    if (m_elems.empty()) {
        return true;
    }
    if (any_of(m_elems.begin(), m_elems.end(), [](interval const & i) { return i.isEmpty(); })) {
        setEmpty();
        return true;
    }
    return false;
}

void box::setEmpty() {
    m_elems.clear();
}

void box::enlarge(size_type n) {
    m_elems.reserve(n);
}

double box::width() const {
    const_iterator iter = max_element(m_elems.begin(),
                                      m_elems.end(),
                                      [](interval const & i1, interval const & i2) {
                                          return i1.width() < i2.width();
                                      });
    if (iter != m_elems.end()) {
        return iter->width();
    } else {
        return 0.0;
    }
}

double box::distance(box const & b) const {
    assert(size() == b.size());
    double dist = 0;
    for (size_type i = 0; i < size(); i++) {
        double const i_th_distance = m_elems[i].distance(b[i]);
        if (i_th_distance > dist) {
            dist = i_th_distance;
        }
    }
    return dist;
}
double box::volume() const {
    return accumulate(m_elems.begin(), m_elems.end(), 1.0,
                      [](double const v, interval const & i) {
                          return v * i.width();
                      });
}
double box::volumeLog() const {
    return accumulate(m_elems.begin(), m_elems.end(), 0.0,
                      [](double const v, interval const & i) {
                          return v * std::log(i.width());
                      });
}
bool box::isCanonical() const {
    return any_of(m_elems.begin(), m_elems.end(), [](interval const & i) { return i.isCanonical(); });
}
box & box::merge(box const & b) {
    assert(size() == b.size());
    for (size_type i = 0; i < size(); i++) {
        m_elems[i].hull(b.m_elems[i]);
    }
    return *this;
}
box::reference box::operator[] (size_type n) {
    return m_elems[n];
}
box::const_reference box::operator[] (size_type n) const {
    return m_elems[n];
}
std::ostream & operator<<(std::ostream & out, box const & b) {
    for (box::value_type const & elem : b) {
        out << elem << endl;
    }
    return out;
}

}
