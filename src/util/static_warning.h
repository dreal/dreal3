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

// The following code is from http://stackoverflow.com/questions/8936063/does-there-exist-a-static-warning
// which is written by Michael Ekstrand (http://stackoverflow.com/users/1385039/michael-ekstrand)
// The code is cc-by-sa licensed (http://creativecommons.org/licenses/by-sa/3.0/).

#if defined(__GNUC__)
#define DEPRECATE(foo, msg) foo __attribute__((deprecated(msg)))
#elif defined(_MSC_VER)
#define DEPRECATE(foo, msg) __declspec(deprecated(msg)) foo
#else
#error This compiler is not supported
#endif

#define PP_CAT(x, y) PP_CAT1(x, y)
#define PP_CAT1(x, y) x##y

namespace detail {
struct true_type {};
struct false_type {};
template <int test> struct converter : public true_type {};
template <> struct converter<0> : public false_type {};
}  // namespace detail

#define STATIC_WARNING(cond, msg)                                       \
    struct PP_CAT(static_warning, __LINE__) {                           \
        DEPRECATE(void _(::detail::false_type const&), msg) {};         \
        void _(::detail::true_type const& ) {};                         \
        PP_CAT(static_warning, __LINE__)() {_(::detail::converter<(cond)>());} \
    }

// Note: using STATIC_WARNING_TEMPLATE changes the meaning of a program in a small way.
// It introduces a member/variable declaration.  This means at least one byte of space
// in each structure/class instantiation.  STATIC_WARNING should be preferred in any
// non-template situation.
//  'token' must be a program-wide unique identifier.
#define STATIC_WARNING_TEMPLATE(token, cond, msg)                       \
    STATIC_WARNING(cond, msg) PP_CAT(PP_CAT(_localvar_, token), __LINE__)
