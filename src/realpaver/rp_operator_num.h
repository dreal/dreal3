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
 * rp_operator_num.h                                                        *
 ****************************************************************************/

#ifndef RP_OPERATOR_NUM
#define RP_OPERATOR_NUM

#ifdef __cplusplus
extern "C" {
#endif

#include <stdio.h>
#include <stdlib.h>
#include "rp_config.h"
#include "rp_memory.h"
#include "rp_constraint.h"
#include "rp_matrix.h"

/* Newton iteration                                        */
/* let f be an expression and df_dx its derivative wrt. x  */
/* let b = (bx, b2, b3, ..., bn) be the box to be reduced  */
/* let c := midpoint(bx)                                   */
/* let bc := (bc, b2, b3, ..., bn)                         */
/*                                                         */
/* Newton internal step:                                   */
/*   bx := hull( bx inter [c - f(bc)/df_dx(b)] )           */
/*                                                         */
/* Iteration until bx is empty or bx cannot be reduced     */
/* with improvement factor improve                         */
int rp_num_newton (rp_expression f, rp_expression df_dx,
		   rp_box b, int x, double improve);

/* Gauss-Seidel iteration over system ax = b */
int rp_num_gs (rp_interval_matrix a,
	       rp_interval_vector x,
	       rp_interval_vector b,
	       double improve);

#ifdef __cplusplus
}
#endif

#endif /* RP_OPERATOR_NUM */
