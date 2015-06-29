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
#include "tools/dop/pstate.h"
#include "tools/dop/parser.h"

namespace dop {
template<typename Rule>
struct control : pegtl::normal<Rule> {
    // template< typename Input, typename ... States >
    // static void start( const Input & in, States && ... ) {
    //     std::cerr << pegtl::position_info( in ) << "  start  " << pegtl::internal::demangle< Rule >() << std::endl;
    // }

    // template< typename Input, typename ... States >
    // static void success( const Input & in, States && ... ) {
    //     std::cerr << pegtl::position_info( in ) << " success " << pegtl::internal::demangle< Rule >() << std::endl;
    // }

    // template< typename Input, typename ... States >
    // static void failure( const Input & in, States && ... ) {
    //     std::cerr << pegtl::position_info( in ) << " failure " << pegtl::internal::demangle< Rule >() << std::endl;
    // }
};

template<> struct control<exp_prod> {
    static void start(const pegtl::input &, pstate & p) {
        p.open();
    }
    static void success(const pegtl::input &, pstate & p) {
        p.close();
    }
    static void failure(const pegtl::input &, pstate & p) {
        p.close();
    }
    template<typename Input, typename ... States>
    static void raise(const Input & in, States && ...) {
        throw pegtl::parse_error("parse error matching " + pegtl::internal::demangle<exp_prod>(), in);
    }
    template<pegtl::apply_mode A, template<typename ...> class Action, template<typename ...> class Control, typename Input, typename ... States>
    static bool match(Input & in, States && ... st) {
        return pegtl::internal::rule_match_one<exp_prod, A, Action, Control>::match(in, st ...);
    }
};

template<> struct control<exp_term> {
    static void start(const pegtl::input &, pstate & p) {
        p.open();
    }
    static void success(const pegtl::input &, pstate & p) {
        p.close();
    }
    static void failure(const pegtl::input &, pstate & p) {
        p.close();
    }
    template<typename Input, typename ... States>
    static void raise(const Input & in, States && ...) {
        throw pegtl::parse_error("parse error matching " + pegtl::internal::demangle<exp_term>(), in);
    }
    template<pegtl::apply_mode A, template<typename ...> class Action, template<typename ...> class Control, typename Input, typename ... States>
    static bool match(Input & in, States && ... st) {
        return pegtl::internal::rule_match_one<exp_term, A, Action, Control>::match(in, st ...);
    }
};

template<> struct control<exp_sum> {
    static void start(const pegtl::input &, pstate & p) {
        p.open();
    }
    static void success(const pegtl::input &, pstate & p) {
        p.close();
    }
    static void failure(const pegtl::input &, pstate & p) {
        p.close();
    }
    template<typename Input, typename ... States>
    static void raise(const Input & in, States && ...) {
        throw pegtl::parse_error("parse error matching " + pegtl::internal::demangle<exp_sum>(), in);
    }
    template<pegtl::apply_mode A, template<typename ...> class Action, template<typename ...> class Control, typename Input, typename ... States>
    static bool match(Input & in, States && ... st) {
        return pegtl::internal::rule_match_one<exp_sum, A, Action, Control>::match(in, st ...);
    }
};

}  // namespace dop
