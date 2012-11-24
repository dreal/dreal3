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
 * rp_clock.h                                                               *
 ****************************************************************************/

#ifndef RP_CLOCK_H
#define RP_CLOCK_H 1

#ifdef __cplusplus
extern "C" {
#endif

#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <sys/resource.h>
#include "rp_config.h"
#include "rp_memory.h"

/* ------------------------------------- */
/* Support of the user CPU time function */
/* ------------------------------------- */

#if RP_SYSTEM_SPARC
/* SPARC stations and Solaris */
static struct rusage rp_aux_rusage;
# define rp_user_time(t)                                                       \
    getrusage(RUSAGE_SELF,&rp_aux_rusage);                                    \
    t = rp_aux_rusage.ru_utime.tv_sec*1000 + rp_aux_rusage.ru_utime.tv_usec/1000

#elif RP_SYSTEM_LINUX_IX86
/* PC i386 and Linux */
# define rp_user_time(t) \
    t = (unsigned long)(((clock()/(double)CLOCKS_PER_SEC))*1000.0)

#elif RP_SYSTEM_POWERPC
/* POWER PC and MAC OS X */
# define rp_user_time(t) \
    t = (unsigned long)(((clock()/(double)CLOCKS_PER_SEC))*1000.0)

#elif RP_SYSTEM_SGI
/* MIPS SGI */
# define rp_user_time(t) \
    t = (unsigned long)(((clock()/(double)CLOCKS_PER_SEC))*1000.0)
#endif

/* ---------------------------------------------------------- */
/* Management of clocks to be used during the solving process */
/* ---------------------------------------------------------- */

typedef struct
{
  unsigned long btime;   /* starting time of operation to be measured */
  unsigned long accu;    /* total accumulated time */
} rp_clock;

typedef struct
{
  unsigned int size;
  rp_clock * clock;
} rp_clock_array;

/* Initialization of the clock management unit */
void rp_clock_init ();

/* Destruction of the clock management unit */
void rp_clock_reset ();

/* Creation of a new clock that returns the clock ID */
int rp_clock_create ();

/* Start the i-th clock */
void rp_clock_start (int i);

/* Stop the i-th clock and accumulate the elapsed time since the last start */
void rp_clock_stop (int i);

/* Get the value of the i-th clock in milliseconds */
unsigned long rp_clock_get (int i);

/* Set the value of the i-th clock */
void rp_clock_set (int i, unsigned long t);

/* Get the value of the i-th clock since the last start */
unsigned long rp_clock_elapsed_time (int i);

#ifdef __cplusplus
}
#endif

#endif /* RP_CLOCK_H */
