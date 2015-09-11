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
#include <pegtl/internal/demangle.hh>
#include <cassert>
#include <iostream>
#include <vector>
#include <functional>
#include <list>
#include <string>
#include <unordered_map>
#include "tools/dop/parsers/dop/pstate.h"
#include "tools/dop/parsers/dop/parser.h"

namespace dop {
namespace dop_parser {
template<typename Rule>
struct action : pegtl::nothing<Rule> {};

template<> struct action<numeral> {
    static void apply(const pegtl::input & in, pstate & p) {
        double const v = std::stod(in.string());
        if (p.is_var_decl_done()) {
            p.push_back(v);
        } else {
            p.push_num(v);
        }
    }
};

template<> struct action<pegtl::identifier> {
    static void apply(const pegtl::input & in, pstate & p) {
        string const & s = in.string();
        if (p.is_var_decl_done()) {
            p.push_back(s);
        } else {
            p.push_id(s);
        }
    }
};

template<> struct action<var_decl> {
    static void apply(const pegtl::input &, pstate & p) {
        p.push_var_decl();
    }
};

template<> struct action<prec_sec> {
    static void apply(const pegtl::input &, pstate & p) {
        p.set_precision(p.pop_num());
    }
};

template<> struct action<lp> {
    static void apply(const pegtl::input &, pstate & p) {
        p.open();
    }
};

template<> struct action<rp> {
    static void apply(const pegtl::input &, pstate & p) {
        p.close();
    }
};

template<> struct action<var_decl_sec> {
    static void apply(const pegtl::input &, pstate & p) {
        p.mark_var_decl_done();
    }
};

template<> struct action<tk_plus> {
    static void apply(const pegtl::input &, pstate &p ) {
        p.push_back_op("+");
    }
};
template<> struct action<tk_minus> {
    static void apply(const pegtl::input &, pstate &p ) {
        p.push_back_op("-");
    }
};
template<> struct action<tk_times> {
    static void apply(const pegtl::input &, pstate &p ) {
        p.push_back_op("*");
    }
};
template<> struct action<tk_div> {
    static void apply(const pegtl::input &, pstate &p ) {
        p.push_back_op("/");
    }
};
template<> struct action<tk_pow> {
    static void apply(const pegtl::input &, pstate &p ) {
        p.push_back_op("^");
    }
};
template<> struct action<tk_abs> {
    static void apply(const pegtl::input &, pstate &p ) {
        p.push_back_op("abs");
    }
};
template<> struct action<tk_sin> {
    static void apply(const pegtl::input &, pstate &p ) {
        p.push_back_op("sin");
    }
};
template<> struct action<tk_cos> {
    static void apply(const pegtl::input &, pstate &p ) {
        p.push_back_op("cos");
    }
};
template<> struct action<tk_tan> {
    static void apply(const pegtl::input &, pstate &p ) {
        p.push_back_op("tan");
    }
};
template<> struct action<tk_asin> {
    static void apply(const pegtl::input &, pstate &p ) {
        p.push_back_op("asin");
    }
};
template<> struct action<tk_acos> {
    static void apply(const pegtl::input &, pstate &p ) {
        p.push_back_op("acos");
    }
};
template<> struct action<tk_atan> {
    static void apply(const pegtl::input &, pstate &p ) {
        p.push_back_op("atan");
    }
};
template<> struct action<tk_atan2> {
    static void apply(const pegtl::input &, pstate &p ) {
        p.push_back_op("atan2");
    }
};
template<> struct action<tk_log> {
    static void apply(const pegtl::input &, pstate &p ) {
        p.push_back_op("log");
    }
};
template<> struct action<tk_exp> {
    static void apply(const pegtl::input &, pstate &p ) {
        p.push_back_op("exp");
    }
};
template<> struct action<tk_sqrt> {
    static void apply(const pegtl::input &, pstate &p ) {
        p.push_back_op("sqrt");
    }
};

template<> struct action<exp_plus_minus> {
    static void apply(const pegtl::input &, pstate &p ) {
        p.reduce([](OpenSMTContext & ctx, std::vector<Enode *> & vec, std::vector<std::string> & ops) {
                assert(vec.size() > 0 && (vec.size() == ops.size() + 1));
                Enode * res = vec[0];
                for (unsigned i = 1; i < vec.size(); i++) {
                    string const & op = ops[i - 1];
                    Enode * const r = vec[i];
                    assert(op == "+" || op == "-");
                    if (op == "+") {
                        res = ctx.mkPlus(ctx.mkCons(res, ctx.mkCons(r)));
                    } else if (op == "-") {
                        res = ctx.mkMinus(ctx.mkCons(res, ctx.mkCons(r)));
                    }
                }
                vec.clear();
                ops.clear();
                return res;
            });
    }
};

template<> struct action<exp_times_div> {
    static void apply(const pegtl::input &, pstate & p) {
        p.reduce([](OpenSMTContext & ctx, std::vector<Enode *> & vec, std::vector<std::string> & ops) {
                assert(vec.size() > 0 && (vec.size() == ops.size() + 1));
                Enode * res = vec[0];
                for (unsigned i = 1; i < vec.size(); i++) {
                    string const & op = ops[i - 1];
                    Enode * const r = vec[i];
                    assert(op == "*" || op == "/");
                    if (op == "*") {
                        res = ctx.mkTimes(ctx.mkCons(res, ctx.mkCons(r)));
                    } else if (op == "/") {
                        res = ctx.mkDiv(ctx.mkCons(res, ctx.mkCons(r)));
                    }
                }
                vec.clear();
                ops.clear();
                return res;
            });
    }
};

template<> struct action<exp_pow> {
    static void apply(const pegtl::input &, pstate & p) {
        p.reduce([](OpenSMTContext & ctx, std::vector<Enode *> & vec, std::vector<std::string> & ops) {
                assert(vec.size() > 0 && (vec.size() == ops.size() + 1));
                Enode * res = vec.back();
                vec.pop_back();
                while (vec.size() >= 1) {
                    assert(ops.back() == "^");
                    ops.pop_back();
                    Enode * const l = vec.back();
                    vec.pop_back();
                    res = ctx.mkPow(ctx.mkCons(l, ctx.mkCons(res)));
                }
                return res;
            });
    }
};

template<> struct action<exp_sin> {
    static void apply(const pegtl::input &, pstate & p) {
        p.reduce([](OpenSMTContext & ctx, std::vector<Enode *> & vec, std::vector<std::string> & ops) {
                assert(vec.size() == 1 && ops.size() == 1);
                assert(ops.back() == "sin");
                Enode * const args_list = ctx.mkCons(vec.back());
                Enode * const res = ctx.mkSin(args_list);
                vec.pop_back();
                ops.pop_back();
                return res;
            });
    }
};

template<> struct action<exp_abs> {
    static void apply(const pegtl::input &, pstate & p) {
        p.reduce([](OpenSMTContext & ctx, std::vector<Enode *> & vec, std::vector<std::string> & ops) {
                assert(vec.size() == 1 && ops.size() == 1);
                assert(ops.back() == "abs");
                Enode * const args_list = ctx.mkCons(vec.back());
                Enode * const res = ctx.mkAbs(args_list);
                vec.pop_back();
                ops.pop_back();
                return res;
            });
    }
};

template<> struct action<exp_cos> {
    static void apply(const pegtl::input &, pstate & p) {
        p.reduce([](OpenSMTContext & ctx, std::vector<Enode *> & vec, std::vector<std::string> & ops) {
                assert(vec.size() == 1 && ops.size() == 1);
                assert(ops.back() == "cos");
                Enode * const args_list = ctx.mkCons(vec.back());
                Enode * const res = ctx.mkCos(args_list);
                vec.pop_back();
                ops.pop_back();
                return res;
            });
    }
};

template<> struct action<exp_tan> {
    static void apply(const pegtl::input &, pstate & p) {
        p.reduce([](OpenSMTContext & ctx, std::vector<Enode *> & vec, std::vector<std::string> & ops) {
                assert(vec.size() == 1 && ops.size() == 1);
                assert(ops.back() == "tan");
                Enode * const args_list = ctx.mkCons(vec.back());
                Enode * const res = ctx.mkTan(args_list);
                vec.pop_back();
                ops.pop_back();
                return res;
            });
    }
};

template<> struct action<exp_asin> {
    static void apply(const pegtl::input &, pstate & p) {
        p.reduce([](OpenSMTContext & ctx, std::vector<Enode *> & vec, std::vector<std::string> & ops) {
                assert(vec.size() == 1 && ops.size() == 1);
                assert(ops.back() == "asin");
                Enode * const args_list = ctx.mkCons(vec.back());
                Enode * const res = ctx.mkAsin(args_list);
                vec.pop_back();
                ops.pop_back();
                return res;
            });
    }
};

template<> struct action<exp_acos> {
    static void apply(const pegtl::input &, pstate & p) {
        p.reduce([](OpenSMTContext & ctx, std::vector<Enode *> & vec, std::vector<std::string> & ops) {
                assert(vec.size() == 1 && ops.size() == 1);
                assert(ops.back() == "acos");
                Enode * const args_list = ctx.mkCons(vec.back());
                Enode * const res = ctx.mkAcos(args_list);
                vec.pop_back();
                ops.pop_back();
                return res;
            });
    }
};

template<> struct action<exp_atan> {
    static void apply(const pegtl::input &, pstate & p) {
        p.reduce([](OpenSMTContext & ctx, std::vector<Enode *> & vec, std::vector<std::string> & ops) {
                assert(vec.size() == 1 && ops.size() == 1);
                assert(ops.back() == "atan");
                Enode * const args_list = ctx.mkCons(vec.back());
                Enode * const res = ctx.mkAtan(args_list);
                vec.pop_back();
                ops.pop_back();
                return res;
            });
    }
};

template<> struct action<exp_atan2> {
    static void apply(const pegtl::input &, pstate & p) {
        p.reduce([](OpenSMTContext & ctx, std::vector<Enode *> & vec, std::vector<std::string> & ops) {
                assert(vec.size() == 1 && ops.size() == 2);
                assert(ops.back() == "atan2");
                Enode * const r = vec.back();
                vec.pop_back();
                Enode * const l = vec.back();
                vec.pop_back();
                Enode * const args_list = ctx.mkCons(l, ctx.mkCons(r));
                Enode * const res = ctx.mkAtan2(args_list);
                ops.pop_back();
                return res;
            });
    }
};

template<> struct action<exp_exp> {
    static void apply(const pegtl::input &, pstate & p) {
        p.reduce([](OpenSMTContext & ctx, std::vector<Enode *> & vec, std::vector<std::string> & ops) {
                assert(vec.size() == 1 && ops.size() == 1);
                assert(ops.back() == "exp");
                Enode * const args_list = ctx.mkCons(vec.back());
                Enode * const res = ctx.mkExp(args_list);
                vec.pop_back();
                ops.pop_back();
                return res;
            });
    }
};

template<> struct action<exp_log> {
    static void apply(const pegtl::input &, pstate & p) {
        p.reduce([](OpenSMTContext & ctx, std::vector<Enode *> & vec, std::vector<std::string> & ops) {
                assert(vec.size() == 1 && ops.size() == 1);
                assert(ops.back() == "log");
                Enode * const args_list = ctx.mkCons(vec.back());
                Enode * const res = ctx.mkLog(args_list);
                vec.pop_back();
                ops.pop_back();
                return res;
            });
    }
};

template<> struct action<exp_sqrt> {
    static void apply(const pegtl::input &, pstate & p) {
        p.reduce([](OpenSMTContext & ctx, std::vector<Enode *> & vec, std::vector<std::string> & ops) {
                assert(vec.size() == 1 && ops.size() == 1);
                assert(ops.back() == "sqrt");
                Enode * const args_list = ctx.mkCons(vec.back());
                Enode * const res = ctx.mkSqrt(args_list);
                vec.pop_back();
                ops.pop_back();
                return res;
            });
    }
};

template<> struct action<cost_decl> {
    static void apply(const pegtl::input &, pstate &p ) {
        p.parse_cost();
        p.clear_stacks();
    }
};

template<> struct action<formula_lt> {
    static void apply(const pegtl::input &, pstate &p ) {
        p.parse_formula_lt();
    }
};

template<> struct action<formula_gt> {
    static void apply(const pegtl::input &, pstate &p ) {
        p.parse_formula_gt();
    }
};

template<> struct action<formula_le> {
    static void apply(const pegtl::input &, pstate &p ) {
        p.parse_formula_le();
    }
};

template<> struct action<formula_ge> {
    static void apply(const pegtl::input &, pstate &p ) {
        p.parse_formula_ge();
    }
};

template<> struct action<formula_eq> {
    static void apply(const pegtl::input &, pstate &p ) {
        p.parse_formula_eq();
    }
};

template<> struct action<formula_neq> {
    static void apply(const pegtl::input &, pstate &p ) {
        p.parse_formula_neq();
    }
};
}  // namespace dop_parser
}  // namespace dop
