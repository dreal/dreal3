/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>

dReal -- Copyright (C) 2013 - 2016, the dReal Team

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
#include <iosfwd>
#include <string>
#include <unordered_map>
#include <vector>

#include "opensmt/api/OpenSMTContext.h"
#include "opensmt/egraph/Enode.h"

class Enode;
class OpenSMTContext;

namespace dop {

class var_map {
private:
    OpenSMTContext & m_ctx;
    std::string m_str;
    std::vector<double> m_double_vec;
    std::vector<std::string> m_vec_str;
    std::unordered_map<std::string, Enode *> m_map;

public:
    explicit var_map(OpenSMTContext & ctx) : m_ctx(ctx) {}
    double pop_num();
    void push_num(double const n);
    void push_id(std::string const & name);
    void set_lb();
    void set_ub();
    void push_var_decl();
    Enode * find(std::string const & name) const;
    std::unordered_map<std::string, Enode *> get_var_map() const { return m_map; }
};

}  // namespace dop
