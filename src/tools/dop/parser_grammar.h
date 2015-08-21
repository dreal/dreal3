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
#include <pegtl/analyze.hh>
#include <cassert>
#include <iostream>
#include <vector>
#include <functional>
#include <list>
#include <string>
#include <unordered_map>
#include "tools/dop/pstate.h"

namespace dop {

// Comments are introduced by a '#' and proceed to the end-of-line/file.
struct comment : pegtl::if_must<pegtl::one<'#'>, pegtl::until<pegtl::eolf>> {};
struct sep : pegtl::sor<pegtl::space, comment> {};
struct seps : pegtl::star<sep> {};
struct str_prec : pegtl::string<'p', 'r', 'e', 'c'> {};
struct str_var : pegtl::string<'v', 'a', 'r'> {};
struct str_cost : pegtl::string<'c', 'o', 's', 't'> {};
struct str_ctr : pegtl::string<'c', 't', 'r'> {};
struct eq : pegtl::string<'='> {};
struct neq : pegtl::string<'!', '='> {};
struct le : pegtl::string<'<', '='> {};
struct ge : pegtl::string<'>', '='> {};
struct colon : pegtl::one<':'> {};
struct comma : pegtl::one<','> {};
struct lt : pegtl::one<'<'> {};
struct gt : pegtl::one<'>'> {};
struct lb : pegtl::one<'['> {};
struct rb : pegtl::one<']'> {};
struct lp : pegtl::one<'('> {};
struct rp : pegtl::one<')'> {};

struct tk_plus  : pegtl::one<'+'> {};
struct tk_minus : pegtl::one<'-'> {};
struct tk_times : pegtl::one<'*'> {};
struct tk_div   : pegtl::one<'/'> {};
struct tk_pow   : pegtl::one<'^'> {};

struct tk_abs   : pegtl::string<'a', 'b', 's'> {};
struct tk_sin   : pegtl::string<'s', 'i', 'n'> {};
struct tk_cos   : pegtl::string<'c', 'o', 's'> {};
struct tk_tan   : pegtl::string<'t', 'a', 'n'> {};
struct tk_asin  : pegtl::string<'a', 's', 'i', 'n'> {};
struct tk_acos  : pegtl::string<'a', 'c', 'o', 's'> {};
struct tk_atan  : pegtl::string<'a', 't', 'a', 'n'> {};
struct tk_atan2 : pegtl::string<'a', 't', 'a', 'n', '2'> {};
struct tk_log   : pegtl::string<'l', 'o', 'g'> {};
struct tk_exp   : pegtl::string<'e', 'x', 'p'> {};
struct tk_sqrt  : pegtl::string<'s', 'q', 'r', 't'> {};

// A grammar for doubles suitable for std::stod without locale support.
// See also: http://en.cppreference.com/w/cpp/string/basic_string/stof

struct plus_minus : pegtl::opt<pegtl::one<'+', '-'>> {};
struct dot : pegtl::one<'.'> {};
struct inf : pegtl::seq<pegtl::istring<'i', 'n', 'f'>,
                        pegtl::opt<pegtl::istring<'i', 'n', 'i', 't', 'y'>>> {};
struct nan : pegtl::seq<pegtl::istring<'n', 'a', 'n'>,
                        pegtl::opt<pegtl::one<'('>,
                                   pegtl::plus<pegtl::alnum>,
                                   pegtl::one<')'>>> {};
template<typename D>
struct number : pegtl::if_then_else<dot,
                                    pegtl::plus<D>,
                                    pegtl::seq<pegtl::plus<D>, dot, pegtl::star<D>>> {};
struct e : pegtl::one<'e', 'E'> {};
struct p : pegtl::one<'p', 'P'> {};
struct exponent : pegtl::seq<plus_minus, pegtl::plus<pegtl::digit>> {};
struct decimal : pegtl::seq<number<pegtl::digit>, pegtl::opt<e, exponent>> {};
struct binary : pegtl::seq<pegtl::one<'0'>, pegtl::one<'x', 'X'>, number<pegtl::xdigit>, pegtl::opt<p, exponent>> {};
struct double_ : pegtl::seq<plus_minus, pegtl::sor<decimal, binary, inf, nan>> {};
struct int_ : pegtl::seq<pegtl::opt<pegtl::one<'+', '-'>>, pegtl::plus<pegtl::digit>> {};
struct numeral : pegtl::sor<double_, int_> {};

struct exp_sum;
struct exp_prod;
struct exp_term;
struct exp_value;
struct exp_plus_minus : pegtl::list<exp_prod,  pegtl::sor<tk_plus,  tk_minus>, sep> { };
struct exp_times_div  : pegtl::list<exp_term,  pegtl::sor<tk_times, tk_div>,   sep> { };
struct exp_pow   : pegtl::list<exp_value, tk_pow,   sep> { };

struct exp_abs   : pegtl::seq<tk_abs,   seps, lp, seps, exp_sum, seps, rp> { };
struct exp_sin   : pegtl::seq<tk_sin,   seps, lp, seps, exp_sum, seps, rp> { };
struct exp_cos   : pegtl::seq<tk_cos,   seps, lp, seps, exp_sum, seps, rp> { };
struct exp_tan   : pegtl::seq<tk_tan,   seps, lp, seps, exp_sum, seps, rp> { };
struct exp_asin  : pegtl::seq<tk_asin,  seps, lp, seps, exp_sum, seps, rp> { };
struct exp_acos  : pegtl::seq<tk_acos,  seps, lp, seps, exp_sum, seps, rp> { };
struct exp_atan  : pegtl::seq<tk_atan,  seps, lp, seps, exp_sum, seps, rp> { };
struct exp_atan2 : pegtl::seq<tk_atan2, seps, lp, seps, exp_sum, seps, rp> { };
struct exp_log   : pegtl::seq<tk_log,   seps, lp, seps, exp_sum, seps, rp> { };
struct exp_exp   : pegtl::seq<tk_exp,   seps, lp, seps, exp_sum, seps, rp> { };
struct exp_sqrt  : pegtl::seq<tk_sqrt,  seps, lp, seps, exp_sum, seps, rp> { };

struct exp_sum   : pegtl::seq<exp_plus_minus> { };
struct exp_prod  : pegtl::seq<exp_times_div>  { };
struct exp_term  : pegtl::sor<exp_pow>        { };

struct formula_gt  : pegtl::seq<exp_sum, seps, gt,  seps, exp_sum> { };
struct formula_lt  : pegtl::seq<exp_sum, seps, lt,  seps, exp_sum> { };
struct formula_ge  : pegtl::seq<exp_sum, seps, ge,  seps, exp_sum> { };
struct formula_le  : pegtl::seq<exp_sum, seps, le,  seps, exp_sum> { };
struct formula_eq  : pegtl::seq<exp_sum, seps, eq,  seps, exp_sum> { };
struct formula_neq : pegtl::seq<exp_sum, seps, neq, seps, exp_sum> { };
struct formula : pegtl::sor<formula_gt,
                            formula_lt,
                            formula_ge,
                            formula_le,
                            formula_eq,
                            formula_neq> { };

struct exp_call  : pegtl::sor<exp_abs, exp_sin, exp_cos, exp_tan, exp_asin, exp_acos, exp_atan, exp_atan2, exp_log, exp_exp, exp_sqrt> { };
struct exp_value : pegtl::sor<numeral,
                              pegtl::seq<lp, seps, exp_sum, seps, rp>,
                              exp_call,
                              pegtl::identifier> { };

struct interval : pegtl::seq<lb, seps, numeral, seps, comma, seps, numeral, rb> {};

// prec_sec
struct prec_sec : pegtl::seq<str_prec, colon, seps, numeral> {};

// var_decls
struct var_decl : pegtl::seq<pegtl::identifier, seps, colon, seps, interval> {};
struct var_decl_list : pegtl::list<var_decl, seps> {};
struct var_decl_sec : pegtl::seq<str_var, colon, seps, var_decl_list> {};

// cost_decl
struct cost_decl : pegtl::must<exp_sum> {};
struct cost_decl_sec : pegtl::seq<str_cost, colon, seps, cost_decl> {};

// ctr_decl
struct ctr_decl_list : pegtl::list<formula, seps> {};
struct ctr_decl_sec  : pegtl::seq<str_ctr, colon, seps, ctr_decl_list> {};

// grammar
struct grammar : pegtl::must<pegtl::opt<prec_sec>, seps,
                             pegtl::must<var_decl_sec>, seps,
                             pegtl::must<cost_decl_sec>, seps,
                             pegtl::opt<pegtl::seq<ctr_decl_sec, seps>>,
                             pegtl::eof> {};

void check_grammar() {
    std::cerr << "exp_plus_minus\n"; pegtl::analyze<dop::exp_plus_minus>();
    std::cerr << "exp_times_div\n";  pegtl::analyze<dop::exp_times_div>();
    std::cerr << "exp_sum\n";        pegtl::analyze<dop::exp_sum>();
    std::cerr << "exp_prod\n";       pegtl::analyze<dop::exp_prod>();
    std::cerr << "exp_term\n";       pegtl::analyze<dop::exp_term>();
    std::cerr << "grammar\n";        pegtl::analyze<dop::grammar>();
    std::cerr << "vardecl\n";        pegtl::analyze<dop::var_decl_sec>();
    std::cerr << "costdecl\n";       pegtl::analyze<dop::cost_decl_sec>();
    std::cerr << "ctrdecl\n";        pegtl::analyze<dop::ctr_decl_sec>();
}

}  // namespace dop
