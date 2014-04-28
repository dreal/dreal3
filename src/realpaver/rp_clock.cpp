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
 * rp_clock.c                                                               *
 ****************************************************************************/

#include "rp_clock.h"

/* The array of clocks that are used during the solving process */
rp_clock_array __rp_clock_array;

/* Initialization of the clock management unit */
void rp_clock_init()
{
  __rp_clock_array.size  = 0;
  __rp_clock_array.clock = NULL;
}

/* Destruction of the clock management unit */
void rp_clock_reset()
{
  if (__rp_clock_array.clock!=NULL)
  {
    rp_free(__rp_clock_array.clock);
  }
}

/* Creation of a new clock */
int rp_clock_create()
{
  int i = __rp_clock_array.size ++;
  if (__rp_clock_array.clock==NULL)
  {
    rp_malloc(__rp_clock_array.clock,rp_clock*,sizeof(rp_clock));
  }
  else
  {
    rp_realloc(__rp_clock_array.clock,rp_clock*,
	       __rp_clock_array.size*sizeof(rp_clock));
  }
  rp_clock_set(i,0);  /* initialization */
  return( i );
}

/* Start the i-th clock */
void rp_clock_start(int i)
{
  unsigned long t;
  rp_user_time(t);
  __rp_clock_array.clock[i].btime = t;
}

/* Stop the i-th clock and accumulate the elapsed time since the last start */
void rp_clock_stop(int i)
{
  unsigned long t;
  rp_user_time(t);
  __rp_clock_array.clock[i].accu += (t - __rp_clock_array.clock[i].btime);
}

/* Get the value of the i-th clock in milliseconds */
unsigned long rp_clock_get(int i)
{
  return( __rp_clock_array.clock[i].accu );
}

/* Set the value of the i-th clock */
void rp_clock_set(int i, unsigned long t)
{
  __rp_clock_array.clock[i].accu = t;
}

/* Get the value of the i-th clock since the last start */
unsigned long rp_clock_elapsed_time(int i)
{
  unsigned long t;
  rp_user_time(t);
  return( t - __rp_clock_array.clock[i].btime );
}
