/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>

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
#include <functional>
#include <vector>
#include <string>
#include "opensmt/egraph/Enode.h"
#include "opensmt/api/OpenSMTContext.h"

namespace dop {

class stacks {
private:
    std::vector<std::vector<Enode*>>      m_exp_stacks;
    std::vector<std::vector<std::string>> m_op_stacks;
    OpenSMTContext &                      m_ctx;

public:
    explicit stacks(OpenSMTContext & ctx) : m_ctx(ctx) { open(); }
    void open();
    void close();
    void push_back_op(std::string const & s);
    void push_back(Enode * const e);
    Enode * get_result() const;
    void reduce(std::function<Enode*(OpenSMTContext & ctx, std::vector<Enode*> &, std::vector<std::string> &)> const & f);
};


}  // namespace dop
