/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>
        Sicun Gao <sicung@cs.cmu.edu>
        Edmund Clarke <emc@cs.cmu.edu>

dReal -- Copyright (C) 2013, Soonho Kong, Sicun Gao, and Edmund Clarke

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

#define LOGGER std::cerr
#define DREAL_LOG_TRACE(...) if (g_log_level <= LogLevel::TRACE) LOGGER << __VA_ARGS__ << std::endl
#define DREAL_LOG_DEBUG(...) if (g_log_level <= LogLevel::DEBUG) LOGGER << __VA_ARGS__ << std::endl
#define DREAL_LOG_INFO(...)  if (g_log_level <= LogLevel::INFO) LOGGER << __VA_ARGS__ << std::endl
#define DREAL_LOG_WARN(...)  if (g_log_level <= LogLevel::WARN) LOGGER << __VA_ARGS__ << std::endl
#define DREAL_LOG_ERROR(...) if (g_log_level <= LogLevel::ERROR) LOGGER << __VA_ARGS__ << std::endl
#define DREAL_LOG_FATAL(...) if (g_log_level <= LogLevel::FATAL) LOGGER << __VA_ARGS__ << std::endl

enum class LogLevel {TRACE, DEBUG, INFO, WARN, ERROR, FATAL };
extern LogLevel g_log_level;

void set_log_level(LogLevel l);
void init_log(LogLevel l = LogLevel::INFO);
