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
 * rp_memory.c                                                              *
 ****************************************************************************/

#include "rp_memory.h"

#if RP_DEBUGGING_MODE

struct rp_memory_cell* __rp_memory_block;
size_t __rp_memory_current_size;
size_t __rp_memory_max_size;

void rp_memory_init()
{
  __rp_memory_block = NULL;
  __rp_memory_current_size = __rp_memory_max_size = 0;
}

void rp_memory_insert(void* ptr, size_t size)
{
  struct rp_memory_cell* newcell;
  if ((newcell = (struct rp_memory_cell*)malloc(sizeof(struct rp_memory_cell)))
      == NULL)
  {
    fprintf(stderr,"rp_memory_insert: not enough memory\n");
    exit(1);
  }
  newcell->ptr = ptr;
  newcell->size = size;
  newcell->next = __rp_memory_block;
  __rp_memory_block = newcell;
  __rp_memory_current_size += (size+sizeof(struct rp_memory_cell));
  if (__rp_memory_current_size>__rp_memory_max_size)
  {
    __rp_memory_max_size = __rp_memory_current_size;
  }
}

size_t rp_memory_remove(void* ptr)
{
  struct rp_memory_cell * prev, * cell;
  int found = 0, size;

  if (__rp_memory_block==NULL)
  {
    fprintf(stderr,"rp_memory_remove: pointer %p to be removed: unknown\n",ptr);
    exit(1);
  }
  if (__rp_memory_block->ptr==ptr)
  {
    cell = __rp_memory_block;
    size = __rp_memory_block->size;
    __rp_memory_block = __rp_memory_block->next;
    free(cell);
  }
  else
  {
    prev = __rp_memory_block;
    cell = prev->next;
    while( (!found) && (cell!=NULL) )
    {
      if (cell->ptr==ptr)
      {
	found = 1;
      }
      else
      {
        prev = cell;
	cell = cell->next;
      }
    }
    if (!found)
    {
      fprintf(stderr,"rp_memory_remove: pointer %p to be removed: unknown\n",ptr);
      exit(1);
    }
    else
    {
      size = cell->size;
      prev->next = cell->next;
      free(cell);
    }
  }
  __rp_memory_current_size -= (size+sizeof(struct rp_memory_cell));
  return( size );
}

size_t rp_memory_destroy()
{
  struct rp_memory_cell * cell;
  int n = 0;
  while (__rp_memory_block!=NULL)
  {
    cell = __rp_memory_block;
    __rp_memory_block = __rp_memory_block->next;
    n += cell->size;
    __rp_memory_current_size -= (cell->size+sizeof(struct rp_memory_cell));
  }
  return( n );
}

void rp_memory_reset()
{
  size_t n = rp_memory_destroy();
  if (n!=0)
  {
    fprintf(stderr,"rp_memory_reset: %u bytes lost in the heap\n",n);
  }
}

#else

void rp_memory_init()
{ }

void rp_memory_reset()
{ }

#endif /* RP_DEBUGGING_MODE */
