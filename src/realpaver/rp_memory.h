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
 * rp_memory.h                                                              *
 ****************************************************************************/

#ifndef RP_MEMORY_H
#define RP_MEMORY_H 1

#ifdef __cplusplus
extern "C" {
#endif

#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <sys/resource.h>
#include "rp_config.h"

#define rp_throw
#ifdef __cplusplus
#undef rp_throw
#define rp_throw throw()
#define rp_inline inline 
#endif


/* Initialization and reset of the memory manager */
void rp_memory_init  ();
void rp_memory_reset ();

#if RP_DEBUGGING_MODE

/* ---------------------------------------------- */
/* DEBUGGING MODE: check for available memory and */
/* Watch memory allocations and desallocations    */
/* ---------------------------------------------- */

/* list of memory blocks in the heap */
struct rp_memory_cell
{
  void* ptr;                    /* address of block */
  size_t size;                  /* size of block    */
  struct rp_memory_cell* next;  /* next block       */
};

void   rp_memory_insert (void* ptr, size_t size);
size_t rp_memory_remove (void* ptr);

# define rp_malloc(ptr,ptrtype,size)                        \
  if ((ptr = (ptrtype)malloc(size)) == NULL)                \
  {                                                         \
    fprintf(stderr,"rp_malloc: not enough memory\n");       \
    exit(1);                                                \
  }                                                         \
  else                                                      \
  {                                                         \
    rp_memory_insert((void*)ptr,size);                      \
  }

# define rp_realloc(ptr,ptrtype,size)			    \
  if (ptr==NULL)                                            \
  {                                                         \
    fprintf(stderr,"rp_realloc: realloc a null pointer\n"); \
  }                                                         \
  else                                                      \
  {                                                         \
    rp_memory_remove((void*)ptr);		            \
    if ((ptr = (ptrtype)realloc(ptr,size)) == NULL)	    \
    {                                                       \
      fprintf(stderr,"rp_realloc: not enough memory\n");    \
      exit(1);                                              \
    }                                                       \
    else                                                    \
    {                                                       \
      rp_memory_insert((void*)ptr,size);                    \
    }                                                       \
  }

# define rp_free(ptr)                                       \
  if (ptr==NULL)                                            \
  {                                                         \
    fprintf(stderr,"rp_free: free on a null pointer\n");    \
  }                                                         \
  else                                                      \
  {                                                         \
    rp_memory_remove((void*)ptr);   	                    \
    free(ptr);                                              \
    ptr = NULL;                                             \
  }

# define rp_new(ptr,type,args)	                            \
  if ((ptr = new type args) == NULL)		            \
  {                                                         \
    fprintf(stderr,"rp_new: not enough memory\n");          \
    exit(1);                                                \
  }                                                         \
  else                                                      \
  {                                                         \
    rp_memory_insert((void*)ptr,sizeof(type));		    \
  }

# define rp_delete(ptr)                                     \
  if (ptr==NULL)                                            \
  {                                                         \
    fprintf(stderr,"rp_delete: delete a null pointer\n");   \
  }                                                         \
  else                                                      \
  {                                                         \
    rp_memory_remove((void*)ptr);   	                    \
    delete ptr;     				            \
    ptr = NULL;                                             \
  }

#else

/* --------------------------------------- */
/* NORMAL MODE: check for available memory */
/* --------------------------------------- */

# define rp_malloc(ptr,ptrtype,size)                        \
  if ((ptr = (ptrtype)malloc(size)) == NULL)                \
  {                                                         \
    fprintf(stderr,"rp_malloc: not enough memory\n");       \
    exit(1);                                                \
  }

# define rp_realloc(ptr,ptrtype,size)			    \
  if ((ptr = (ptrtype)realloc(ptr,size)) == NULL)	    \
  {                                                         \
    fprintf(stderr,"rp_realloc: not enough memory\n");      \
    exit(1);                                                \
  }

# define rp_free(ptr)                                       \
  if (ptr==NULL)                                            \
  {                                                         \
    fprintf(stderr,"rp_free: free on a null pointer\n");    \
  }                                                         \
  else                                                      \
  {                                                         \
    free(ptr);                                              \
    ptr = NULL;                                             \
  }

# define rp_new(ptr,type,args)	                            \
  if ((ptr = new type args) == NULL)		            \
  {                                                         \
    fprintf(stderr,"rp_new: not enough memory\n");          \
    exit(1);                                                \
  }

# define rp_delete(ptr)                                     \
  if (ptr==NULL)                                            \
  {                                                         \
    fprintf(stderr,"rp_delete: delete a null pointer\n");   \
  }                                                         \
  else                                                      \
  {                                                         \
    delete ptr;     				            \
    ptr = NULL;                                             \
  }


#endif /* RP_DEBUGGING_MODE */

#if RP_DEBUGGING_MODE
#define RP_DEBUG(s) fprintf(stderr,s)
#endif /* RP_DEBUGGING_MODE */


#ifdef __cplusplus
}
#endif

#endif /* RP_MEMORY_H */
