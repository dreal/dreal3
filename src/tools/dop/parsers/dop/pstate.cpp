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
#include <iostream>
#include <utility>
#include "tools/dop/parsers/dop/pstate.h"

namespace dop {
namespace dop_parser {

using std::function;
using std::vector;
using std::string;
using std::ostream;
using std::pair;

pair<Enode *, Enode *> pstate::parse_formula_helper() {
    vector<Enode*> & top_stack = m_stacks.get_top_stack();
    assert(top_stack.size() >= 2);
    Enode * rhs = top_stack.back();
    top_stack.pop_back();
    Enode * lhs = top_stack.back();
    top_stack.pop_back();
    clear_stacks();
    return make_pair(lhs, rhs);
}

pstate::pstate() : m_stacks(m_ctx), m_var_map(m_ctx) {
    SMTConfig & cfg = m_ctx.getConfig();
    cfg.incremental = 1;
    cfg.sat_theory_propagation = 1;
    // cfg.nra_worklist_fp = 1;
    // cfg.nra_ncbt = 1;
    // m_ctx.setDebug(true);
    m_ctx.SetLogic(QF_NRA);
}

ostream & pstate::debug_stacks(ostream & out) const {
    return m_stacks.debug(out);
}

void pstate::parse_formula_lt() {
    std::pair<Enode *, Enode *> nodes = parse_formula_helper();
    Enode * lhs = nodes.first;
    Enode * rhs = nodes.second;
    m_ctrs.push_back(m_ctx.mkLt(m_ctx.mkCons(lhs, m_ctx.mkCons(rhs))));
}
void pstate::parse_formula_gt() {
    std::pair<Enode *, Enode *> nodes = parse_formula_helper();
    Enode * lhs = nodes.first;
    Enode * rhs = nodes.second;
    m_ctrs.push_back(m_ctx.mkGt(m_ctx.mkCons(lhs, m_ctx.mkCons(rhs))));
}
void pstate::parse_formula_le() {
    std::pair<Enode *, Enode *> nodes = parse_formula_helper();
    Enode * lhs = nodes.first;
    Enode * rhs = nodes.second;
    m_ctrs.push_back(m_ctx.mkLeq(m_ctx.mkCons(lhs, m_ctx.mkCons(rhs))));
}
void pstate::parse_formula_ge() {
    std::pair<Enode *, Enode *> nodes = parse_formula_helper();
    Enode * lhs = nodes.first;
    Enode * rhs = nodes.second;
    m_ctrs.push_back(m_ctx.mkGeq(m_ctx.mkCons(lhs, m_ctx.mkCons(rhs))));
}
void pstate::parse_formula_eq() {
    std::pair<Enode *, Enode *> nodes = parse_formula_helper();
    Enode * lhs = nodes.first;
    Enode * rhs = nodes.second;
    m_ctrs.push_back(m_ctx.mkEq(m_ctx.mkCons(lhs, m_ctx.mkCons(rhs))));
}
void pstate::parse_formula_neq() {
    std::pair<Enode *, Enode *> nodes = parse_formula_helper();
    Enode * lhs = nodes.first;
    Enode * rhs = nodes.second;
    m_ctrs.push_back(m_ctx.mkNot(m_ctx.mkEq(m_ctx.mkCons(lhs, m_ctx.mkCons(rhs)))));
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
}  // namespace dop_parser
}  // namespace dop
