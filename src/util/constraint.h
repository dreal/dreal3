/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>
        Sicun Gao <sicung@cs.cmu.edu>
        Edmund Clarke <emc@cs.cmu.edu>

dReal -- Copyright (C) 2013 - 2015, Soonho Kong, Sicun Gao, and Edmund Clarke

dReal is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

dReal is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with dReal. If not, see <http://www.gnu.org/licenses/>.
*********************************************************************/

#pragma once
#include <algorithm>
#include <unordered_map>
#include <vector>
#include <initializer_list>
#include <stdexcept>
#include <memory>
#include "opensmt/egraph/Enode.h"

namespace dreal {

enum class constraint_type { Algebraic, ODE, Integral, ForallT };

class constraint {
protected:
    constraint_type m_type;
    std::vector<Enode *> m_enodes;
    std::unordered_set<Enode *> m_vars;

public:
    constraint(constraint_type ty);
    constraint(constraint_type ty, Enode * e);
    constraint(constraint_type ty, std::vector<Enode *> const & enodes);
    constraint(constraint_type ty, std::vector<Enode *> const & enodes_1, std::vector<Enode *> const & enodes_2);
    inline constraint_type const & get_type() const { return m_type; }
    inline std::vector<Enode *> const & get_enodes() const { return m_enodes; }
    inline std::unordered_set<Enode *> const & get_vars() const { return m_vars; }
    virtual std::ostream & display(std::ostream & out) const = 0;
    virtual ~constraint() { }
    friend std::ostream & operator<<(std::ostream & out, constraint const & c);
};

std::ostream & operator<<(ostream & out, constraint const & c);

class algebraic_constraint : public constraint {
public:
    algebraic_constraint(Enode * e);
    virtual ~algebraic_constraint();
    virtual std::ostream & display(std::ostream & out) const;
};

class integral_constraint : public constraint {
private:
    unsigned m_flow;
    Enode * m_time_0;
    Enode * m_time_t;
    std::vector<Enode *> m_vars_0;
    std::vector<Enode *> m_vars_t;

public:
    inline unsigned get_flow()                      const { return m_flow; }
    inline Enode * get_time_0()                      const { return m_time_0; }
    inline Enode * get_time_t()                      const { return m_time_t; }
    inline std::vector<Enode *> const & get_vars_0() const { return m_vars_0; }
    inline std::vector<Enode *> const & get_vars_t() const { return m_vars_t; }
    integral_constraint(Enode * e);
    virtual ~integral_constraint();
    virtual std::ostream & display(std::ostream & out) const;
};

class forallt_constraint : public constraint {
private:
    unsigned m_flow;
    Enode * m_time_0;
    Enode * m_time_t;
    Enode * m_inv;

public:
    inline unsigned get_flow() const { return m_flow; }
    inline Enode * get_time_0() const { return m_time_0; }
    inline Enode * get_time_t() const { return m_time_t; }
    inline Enode * get_inv()   const { return m_inv; }
    forallt_constraint(Enode * e);
    virtual ~forallt_constraint();
    virtual std::ostream & display(std::ostream & out) const;
};

class ode_constraint : public constraint {
private:
    integral_constraint m_int;
    std::vector<forallt_constraint> m_invs;

public:
    ode_constraint(integral_constraint const & integral, std::vector<forallt_constraint> const & invs);
    virtual ~ode_constraint();
    virtual std::ostream & display(std::ostream & out) const;
};
}
