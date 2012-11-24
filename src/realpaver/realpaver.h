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

#ifndef REALPAVER_H
#define REALPAVER_H 1

//#ifdef __cplusplus
//extern "C" {
//#endif

#include "realpaverbasic.h"
#include "rp_operator.h"
#include "rp_operator_factory.h"
#include "rp_propagator.h"
#include "rp_box_set.h"
#include "rp_split_selector.h"
#include "rp_split.h"
#include "rp_verification.h"
#include "rp_output.h"
#include "rp_solver.h"

/* Use of the library between these two operations */

//@the following two functions are used for initializing the memory
#define rp_init_library()   \
  { rp_basic_init_library(); }

#define rp_reset_library() \
  { rp_basic_reset_library(); }


//#ifdef __cplusplus
//}
//#endif

#endif  /* REALPAVER_H */
