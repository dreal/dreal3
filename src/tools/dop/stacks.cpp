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

#include <vector>
#include <string>
#include <functional>
#include "tools/dop/pstate.h"

namespace dop {

using std::vector;
using std::string;
using std::function;

void stacks::open() {
    assert(m_exp_stacks.size() == m_op_stacks.size());
    m_exp_stacks.push_back(vector<Enode*>());
    m_op_stacks.push_back(vector<string>());
    assert(m_exp_stacks.size() == m_op_stacks.size());
}

void stacks::close() {
    assert(m_exp_stacks.size() > 0);
    assert(m_op_stacks.size() > 0);
    assert(m_exp_stacks.size() == m_op_stacks.size());
    vector<Enode*> const & top_stack = m_exp_stacks.back();
    assert(top_stack.size() <= 1);
    if (top_stack.size() == 1) {
        // | x |
        //
        // |   |  =>  | x |
        // | y |      | y |
        Enode * const top_stack_content = top_stack.back();
        m_exp_stacks.pop_back();
        m_exp_stacks.back().push_back(top_stack_content);
        m_op_stacks.pop_back();
    } else {
        // |   |
        //
        // |   |  =>  |   |
        // | y |      | y |
        m_exp_stacks.pop_back();
        m_op_stacks.pop_back();
    }
    assert(m_exp_stacks.size() == m_op_stacks.size());
}

void stacks::push_back_op(string const & s) {
    vector<string> & top_op_stack = m_op_stacks.back();
    top_op_stack.push_back(s);
}

void stacks::push_back(Enode * const e) {
    vector<Enode*> & top_stack = m_exp_stacks.back();
    top_stack.push_back(e);
}

Enode * stacks::get_result() const {
    assert(m_exp_stacks.size() == 1);        // everything has to be reduced.
    assert(m_op_stacks.size() == 1);         // everything has to be reduced.
    assert(m_op_stacks.back().size() == 0);  // everything has to be reduced.
    vector<Enode*> const & top_stack = m_exp_stacks.back();
    assert(top_stack.size() == 1);  // everything has to be reduced.
    return top_stack.back();
}

void stacks::reduce(function<Enode*(OpenSMTContext & ctx, vector<Enode*> &, vector<string> &)> const & f) {
    vector<Enode*> & top_exp_stack = m_exp_stacks.back();
    vector<string> & top_op_stack = m_op_stacks.back();
    Enode * const result = f(m_ctx, top_exp_stack, top_op_stack);
    top_exp_stack.push_back(result);
}

}  // namespace dop
