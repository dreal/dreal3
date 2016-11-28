/*********************************************************************
Author: Sicun Gao <sicung@cs.cmu.edu>
        Soonho Kong <soonhok@cs.cmu.edu>

dReal -- Copyright (C) 2013 - 2016, the dReal Team

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

#include <cassert>
#include <iostream>
#include <vector>

#include "api/dreal.h"

namespace dreal {
void checkBarrier(std::vector<expr> & x, std::vector<expr> & f, expr & B, double const eps);
void checkLyapunov(std::vector<expr> & x, std::vector<expr> & f, expr & V, double const eps);
expr plugSolutionsIn(expr & formula, std::vector<expr *> & x, std::vector<expr *> & sol,
                     std::vector<expr *> & p);
void synthesizeLyapunov(std::vector<expr *> & x, std::vector<expr *> & p, std::vector<expr *> & f,
                        expr & V, double const eps);
void synthesizeControlAndLyapunov(std::vector<expr *> & x, std::vector<expr *> & p_f,
                                  std::vector<expr *> & p_v, std::vector<expr *> & f, expr & V,
                                  double const eps);
}
