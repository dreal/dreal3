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
 * rp_box_set.h                                                             *
 ****************************************************************************/

#ifndef RP_BOX_SET_H
#define RP_BOX_SET_H 1

#include "rp_box.h"

// ----------------------------
// Base class for sets of boxes
// ----------------------------
class rp_box_set
{
public:
  // Constructor
  rp_box_set();

  // Destructor
  virtual ~rp_box_set();

  // To empty the set
  void reset();

  // Access to the current box
  virtual rp_box get() = 0;

  // Removal of the current box
  virtual void remove() = 0;

  // Returns true if the set is empty
  virtual int empty() = 0;

  // Insertion of a copy of b in the set
  virtual rp_box insert(rp_box b) = 0;

  // Removal and then insertion of the current box
  virtual rp_box remove_insert() = 0;

  // Number of physically allocated boxes in the set
  virtual int length() = 0;

  // Number of boxes in the set
  virtual int size() = 0;

  // Access to the i-th box
  virtual rp_box get(int i) = 0;

protected:
  // Copy protection
  rp_box_set(const rp_box_set& bs);

private:
  // Copy protection
  rp_box_set& operator=(const rp_box_set& bs);
};

// -------------------------------------
// Stack of boxes for Depth-First Search
// -------------------------------------
class rp_box_stack : public rp_box_set
{
public:
  // Constructor
  rp_box_stack(int bsize, int size = 10);

  // Destructor
  ~rp_box_stack();

  // Access to the current box
  rp_box get();

  // Removal of the current box
  void remove();

  // Returns true if the set is empty
  int empty();

  // Insertion of a box at the top of the stack
  rp_box insert(rp_box b);

  // Removal and then insertion of the current box
  rp_box remove_insert();

  // Number of physically allocated boxes in the set
  int length();

  // Number of boxes in the set
  int size();

  // Access to the i-th box
  rp_box get(int i);

private:
  // Copy protection
  rp_box_stack(const rp_box_stack& q);
  rp_box_stack& operator=(const rp_box_stack& q);

  // Structure: list of arrays of fixed size
  struct rp_blist_def
  {
    rp_box * ptr;
    struct rp_blist_def * prev;
    struct rp_blist_def * next;
  };
  typedef struct rp_blist_def * rp_blist;

  rp_blist _cell;   /* current cell in the stack                    */
  rp_blist _first;  /* first cell in the stack                      */
  int _cur;         /* index of the current box in the current cell */
  int _size;        /* array size                                   */
  int _bsize;       /* number of elements in a box                  */
  int _nb;          /* number of boxes in the set                   */

  // Allocation in memory of a stack element
  rp_blist alloc();
};

// ---------------------------------------
// Queue of boxes for Breadth-First Search
// ---------------------------------------
class rp_box_queue : public rp_box_set
{
public:
  // Constructor
  rp_box_queue(int bsize, int size = 10);

  // Destructor
  ~rp_box_queue();

  // Access to the current box
  rp_box get();

  // Removal of the current box
  void remove();

  // Returns true if the set is empty
  int empty();

  // Insertion of a box at the end of the queue
  rp_box insert(rp_box b);

  // Removal and then insertion of the current box
  rp_box remove_insert();

  // Number of physically allocated boxes in the set
  int length();

  // Number of boxes in the set
  int size();

  // Access to the i-th box
  rp_box get(int i);

private:
  // Copy protection
  rp_box_queue(const rp_box_queue& q);
  rp_box_queue& operator=(const rp_box_queue& q);

  // Structure: list of arrays of fixed size
  struct rp_blist_def
  {
    rp_box * ptr;
    struct rp_blist_def * prev;
    struct rp_blist_def * next;
  };
  typedef struct rp_blist_def * rp_blist;

  rp_blist _first;  /* top of the queue                                */
  rp_blist _last;   /* bottom of the queue                             */
  int _curfirst;    /* index of the top element (next to be extracted) */
  int _curlast;     /* index of the bottom element (last inserted)     */
  int _size;        /* array size                                      */
  int _bsize;       /* number of elements in a box                     */
  int _nb;          /* number of boxes in the set                      */

  // Allocation in memory of a queue element
  rp_blist alloc();
};

#endif /* RP_BOX_SET_H */
