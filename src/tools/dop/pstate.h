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
#include <pegtl.hh>
#include <cassert>
#include <exception>
#include <iostream>
#include <list>
#include <map>
#include <string>
#include <unordered_map>
#include <vector>
#include "opensmt/egraph/Enode.h"
#include "opensmt/api/OpenSMTContext.h"
#include "tools/dop/stacks.h"
#include "tools/dop/var_map.h"

namespace dop {

class pstate {
private:
    OpenSMTContext m_ctx;
    stacks         m_stacks;
    var_map        m_var_map;
    bool           m_var_decl_done = false;
    double         m_prec = 0.001;

public:
    pstate();
    bool is_var_decl_done() const { return m_var_decl_done; }
    void mark_var_decl_done() { m_var_decl_done = true; }
    OpenSMTContext & get_ctx() { return m_ctx; }

    // ============================
    // m_stacks (expression stacks)
    // ============================
    void push_back(double const v);
    void push_back(string const & s);
    void push_back_op(string const & s);
    void open();
    void close();
    void reduce(std::function<Enode*(OpenSMTContext & ctx, std::vector<Enode*> &, std::vector<std::string> &)> const & f);
    Enode * get_result() const;

    // =========
    // Precision
    // =========
    void set_prec(double const v) { m_prec = v; }
    double get_prec() const { return m_prec; }

    // ==============
    // var_map
    // ==============
    void push_num(double const n) { m_var_map.push_num(n); }
    double pop_num() { return m_var_map.pop_num(); }
    void push_id(std::string const & name) { m_var_map.push_id(name); }
    void push_var_decl() { m_var_map.push_var_decl(); }
    std::unordered_map<std::string, Enode *> get_var_map() const {
        return m_var_map.get_var_map();
    }
};
}  // namespace dop
