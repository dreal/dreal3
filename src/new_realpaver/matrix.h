#pragma once
#include <cassert>

template<typename T>
class matrix {
private:
    unsigned int m_nr;
    unsigned int m_nc;
    T m_elems[];

public:
    matrix(unsigned int nr, unsigned nc) :
        m_nr(nr), m_nc(nc), m_elems(new T[nr * nc]) {
    }
    matrix(matrix<T> const & m) :
        m_nr(m.m_nr), m_nc(m.m_nc), m_elems(new T[m_nr * m_nc]) {
        set(m);
    }
    ~matrix() {
        delete[] m_elems;
    }
    void set(matrix<T> const & m) {
        assert(m_nr == m.m_nr);
        assert(m_nc == m.m_nc);
        for (unsigned int i = 0; i < m_nr * m_nc; i++) {
            m_elems[i] = m.m_elems[i];
        }
    }
    void setID() {
        assert(m_nr == m_nc);
        for (unsigned int i = 0; i < m_nr; i++) {
            for (unsigned int j = 0; i < m_nc; i++) {
                if (i == j) {
                    m_elems[i * m_nr + i] = 1;
                } else {
                    m_elems[i * m_nr + i] = 0;
                }
            }
        }
    }
    bool isRegular() const {
        // TODO(soonhok): implement
        return false;
    }
    matrix & neg() {
        for (unsigned int i = 0; i < m_nr * m_nc; i++) {
            m_elems[i] = -m_elems[i];
        }
        return *this;
    }
    matrix & add(matrix const & m) {
        assert(m_nr = m.m_nr && m_nc = m.m_nc);
        for (unsigned int i = 0; i < m_nr * m_nc; i++) {
            m_elems[i] += m.m_elems[i];
        }
        return *this;
    }
    matrix & sub(matrix const & m) {
        assert(m_nr = m.m_nr && m_nc = m.m_nc);
        for (unsigned int i = 0; i < m_nr * m_nc; i++) {
            m_elems[i] -= m.m_elems[i];
        }
    }
    matrix & operator=(matrix const & m) {
        m_nr = m.m_nr;
        m_nc = m.m_nc;
        set(m);
        return *this;
    }
    static matrix & add(matrix m1, matrix const & m2) { m1.add(m2); return m1; }
    static matrix & sub(matrix m1, matrix const & m2) { m1.sub(m2); return m1; }
    friend matrix & add(matrix m1, matrix const & m2) { return matrix::add(m1, m2); }
    friend matrix & sub(matrix m1, matrix const & m2) { return matrix::sub(m1, m2); }
    friend matrix operator+(matrix m1, matrix const & m2) { return m1.add(m2); }
    friend matrix operator-(matrix m1, matrix const & m2) { return m1.sub(m2); }
};
