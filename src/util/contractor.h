/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>
        Sicun Gao <sicung@cs.cmu.edu>
        Edmund Clarke <emc@cs.cmu.edu>

dReal -- Copyright (C) 2013 - 2014, Soonho Kong, Sicun Gao, and Edmund Clarke

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
#include <unordered_map>
#include <vector>
#include <initializer_list>
#include <stdexcept>
#include <memory>
#include "opensmt/egraph/Enode.h"
#include "util/interval.h"
#include "util/var.h"
#include "util/box.h"

namespace dreal {

enum class contractor_kind { Seq, Or, If_Then_Else, While, Parallel_First, Parallel_All, Timeout, Realpaver, CAPD_Forward, CAPD_Backward };

class contractor;

class contractor_exception : public std::exception {
    virtual const char* what() const throw();
};

class contractor_cell {
protected:
    contractor_kind m_kind;
public:
    virtual box prune(box b) const = 0;
};

class contractor {
private:
    std::shared_ptr<contractor_cell> m_ptr;

public:
    box prune(box b) const;
};

class contractor_seq : public contractor_cell {
private:
    std::vector<contractor> m_vec;
public:
    contractor_seq(std::initializer_list<contractor> l);
    box prune(box b) const;
};

class contractor_or : public contractor_cell {
private:
    contractor m_c1;
    contractor m_c2;
public:
    contractor_or(contractor const & c1, contractor const & c2);
    box prune(box b) const;
};

class contractor_ite : public contractor_cell {
private:
    std::function<bool(box)> m_guard;
    contractor m_c_then;
    contractor m_c_else;
public:
    contractor_ite(std::function<bool(box const &)> guard, contractor const & c_then, contractor const & c_else);
    box prune(box b) const;
};

class contractor_while : public contractor_cell {
private:
    std::function<bool(box const &, box const &)> m_guard;
    contractor m_c;
public:
    contractor_while(std::function<bool(box const &, box const &)> guard, contractor const & c);
    box prune(box b) const;
};

}
