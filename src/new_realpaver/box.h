/****************************************************************************
 * RealPaver v. 1.0                                                         *
 *--------------------------------------------------------------------------*
 * Author: Laurent Granvilliers                                             *
 * Copyright (c) 1999-2003 Institut de Recherche en Informatique de Nantes  *
 * Copyright (c) 2004-2006 Laboratoire d'Informatique de Nantes Atlantique  *
 *--------------------------------------------------------------------------*
 * RealPaver is distributed WITHOUT ANY WARRANTY. Read the associated       *
 * COPYRIGHT file for more details.                                         *
 *--------------------------------------------------------------------------*
 * rp_box.h                                                                 *
 ****************************************************************************/

#pragma once
#include <vector>
#include "new_realpaver/interval.h"

namespace realpaver {

class box {
private:
    typedef std::vector<interval> vec;
    typedef vec::value_type      value_type;
    typedef vec::iterator        iterator;
    typedef vec::const_iterator  const_iterator;
    typedef vec::size_type       size_type;
    typedef vec::reference       reference;
    typedef vec::const_reference const_reference;

    bool m_safe;
    bool m_inner;
    bool m_isafe;

//    int m_split;
    int m_nvdec;
    int m_nvaux;
    vec m_elems;

public:
    box(size_type n);
    ~box();
    box(box const & b);

    iterator       begin()        { return m_elems.begin(); }
    iterator       end()          { return m_elems.end(); }
    const_iterator begin()  const { return m_elems.cbegin(); }
    const_iterator end()    const { return m_elems.cend(); }
    const_iterator cbegin() const { return m_elems.cbegin(); }
    const_iterator cend()   const { return m_elems.cend(); }

    void enlarge(size_type n);
    size_type size() const { return m_elems.size(); }
    bool isEmpty();
    void setEmpty();
    bool isSafe()  const { return m_safe; }
    bool isInner() const { return m_inner; }
    bool isIsafe() const { return m_isafe; }
    void setSafe(bool b)  { m_safe = b; }
    void setInner(bool b) { m_inner = b; }
    void setIsafe(bool b) { m_isafe = b; }

    double width() const;
    double distance(box const & b) const;
    double volume() const;
    double volumeLog() const;
    bool isCanonical() const;
    box & merge(box const & b);
    std::ostream & display(std::ostream & out, box const & /* b */) {
        // TODO(soonhok): implement this
        return out;
    }

    friend std::ostream & operator<<(std::ostream & out, box const & b);
    reference operator[] (size_type n);
    const_reference operator[] (size_type n) const;
};

std::ostream & operator<<(std::ostream & out, box const & b);
}
