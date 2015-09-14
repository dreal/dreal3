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

#include "tools/dop/process.h"

int main(int argc, const char * argv[]) {
#ifdef LOGGING
    START_EASYLOGGINGPP(argc, argv);
#endif
    dop::config config(argc, argv);
    switch (config.get_type()) {
    case dop::type::DOP:
        return dop::process_dop(config);
    case dop::type::BARON:
        return dop::process_baron(config);
    case dop::type::BCH:
        return dop::process_bch(config);
    }
}
