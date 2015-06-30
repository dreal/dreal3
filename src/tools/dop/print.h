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
#include <iostream>
#include <string>
#include <functional>
#include "opensmt/egraph/Enode.h"

namespace dop {

std::ostream & print_infix_op(std::ostream & out, Enode * const e, std::string const & op, std::function<std::ostream & (std::ostream &, Enode * const)> const & f);
std::ostream & print_call_bar(std::ostream & out, Enode * const e, std::string const & fname, std::function<std::ostream & (std::ostream &, Enode * const)> const & f);
std::ostream & print_call_brace(std::ostream & out, Enode * const e, std::string const & fname, std::function<std::ostream & (std::ostream &, Enode * const)> const & f);
std::ostream & print_call_paren(std::ostream & out, Enode * const e, std::string const & fname, std::function<std::ostream & (std::ostream &, Enode * const)> const & f);

}  // namespace dop
