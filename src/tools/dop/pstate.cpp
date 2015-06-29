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

using std::function;
using std::vector;
using std::string;

pstate::pstate() : m_stacks(m_ctx), m_var_map(m_ctx) {
    SMTConfig & cfg = m_ctx.getConfig();
    cfg.incremental = 1;
    cfg.sat_theory_propagation = 1;
    cfg.nra_worklist_fp = 1;
    cfg.nra_ncbt = 1;
    m_ctx.SetLogic(QF_NRA);
}

// ============================
// m_stacks (expression stacks)
// ============================
void pstate::push_back(double const v) {
    Enode * const e = m_ctx.mkNum(v);
    m_stacks.push_back(e);
}
void pstate::push_back(string const & s) {
    Enode * const e = m_var_map.find(s);
    m_stacks.push_back(e);
}
void pstate::push_back_op(string const & s) {
    m_stacks.push_back_op(s);
}
void pstate::open() {
    m_stacks.open();
}
void pstate::close() {
    m_stacks.close();
}
void pstate::reduce(function<Enode*(OpenSMTContext & ctx, vector<Enode*> &, vector<string> &)> const & f) {
    m_stacks.reduce(f);
}
Enode * pstate::get_result() const {
    return m_stacks.get_result();
}

}  // namespace dop
