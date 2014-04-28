/****************************************************************************
 * RealPaver v. 1.0                                                         *
 *--------------------------------------------------------------------------*
 * Author: Laurent Granvilliers                                             *
 * Copyright (c) 1999-2003 Institut de Recherche en Informatique de Nantes  *
 * Copyright (c) 2004-2006 Laboratoire d'Informatique de Nantes Atlantique  *
 *--------------------------------------------------------------------------*
 * RealPaver is distributed WITHOUT ANY WARRANTY. Read the associated       *
 * COPYRIGHT file for more details.                                         *
 *--------------------------------------------------------------------------*
 * realpaver.h                                                              *
 ****************************************************************************/

#pragma once

#include "rp_config.h"
#include "rp_clock.h"
#include "rp_memory.h"
#include "rp_container.h"
#include "rp_float.h"
#include "rp_interval.h"
#include "rp_union_interval.h"
#include "rp_projection.h"
#include "rp_box.h"
#include "rp_constant.h"
#include "rp_variable.h"
#include "rp_constraint.h"
#include "rp_expression_symbol.h"
#include "rp_expression.h"
#include "rp_function.h"
#include "rp_problem.h"
#include "rp_stream.h"
#include "rp_lexer.h"
#include "rp_parser.h"
#include "rp_operator_sat.h"
#include "rp_operator_num.h"
#include "rp_matrix.h"

/* Use of the library between these two operations */

#define rp_basic_init_library()   \
  { rp_memory_init();     } \
  { rp_interval_init();   } \
  { rp_clock_init();      }

#define rp_basic_reset_library() \
  { rp_clock_reset();  }   \
  { rp_interval_reset(); } \
  { rp_memory_reset(); }
