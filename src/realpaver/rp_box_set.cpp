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
 * rp_box_set.cpp                                                           *
 ****************************************************************************/

#include "rp_box_set.h"

// ----------------------------
// Base class for sets of boxes
// ----------------------------
rp_box_set::rp_box_set()
{}

rp_box_set::~rp_box_set()
{}

void rp_box_set::reset()
{
  while (!this->empty())
  {
    this->remove();
  }
}

rp_box_set::rp_box_set(const rp_box_set& bs)
{}

rp_box_set& rp_box_set::operator=(const rp_box_set& bs)
{
  return( *this );
}

// -------------------------------------
// Stack of boxes for Depth-First Search
// -------------------------------------
rp_box_stack::rp_box_stack(int bsize, int size):
  rp_box_set(),
  _cell(NULL),
  _cur(-1),
  _size(size),
  _bsize(bsize),
  _nb(0)
{}

rp_box_stack::~rp_box_stack()
{
  if (_cell!=NULL)
  {
    // Seek _cell to the beginning
    while (_cell->prev!=NULL)
    {
      _cell = _cell->prev;
    }

    // Destruction of each cell from the stack
    while (_cell!=NULL)
    {
      rp_blist aux = _cell;
      _cell = _cell->next;

      for (int i=0; i<_size; ++i)
      {
	if (aux->ptr[i]!=NULL)
	{
	  rp_box_destroy(&aux->ptr[i]);
	}
      }
      rp_free(aux->ptr);
      rp_free(aux);
    }
  }
}

int rp_box_stack::length()
{
  int n = 0;
  rp_blist aux = _cell;
  while (aux->prev!=NULL)
  {
    aux = aux->prev;
  }
  while (aux->next!=NULL)
  {
    n += _size;
    aux = aux->next;
  }
  for (int i=0; i<_size; ++i)
  {
    if (aux->ptr[i]!=NULL)
    {
      ++ n;
    }
  }
  return( n );
}

rp_box rp_box_stack::get()
{
  return( _cell->ptr[_cur] );
}

rp_box rp_box_stack::get(int i)
{
  rp_blist l = _first;
  for (int k=0; k<(i/_size); ++k)
  {
    l = l->next;
  }
  return( l->ptr[i%_size] );
}

int rp_box_stack::size()
{
  return _nb;
}

void rp_box_stack::remove()
{
  if ((_cur>0) || (_cell->prev==NULL))
  {
    --_cur;
  }
  else
  {
    _cell = _cell->prev;
    _cur = _size-1;
  }
  --_nb;
}

int rp_box_stack::empty()
{
  return( _cur<0 );
}

rp_box_stack::rp_blist rp_box_stack::alloc()
{
  rp_blist l;
  rp_malloc(l,struct rp_blist_def*,sizeof(struct rp_blist_def));
  rp_malloc(l->ptr,rp_box*,_size*sizeof(rp_box));
  for (int i=0; i<_size; ++i)
  {
    l->ptr[i] = NULL;
  }
  l->prev = NULL;
  l->next = NULL;
  return( l );
}

rp_box rp_box_stack::insert(rp_box b)
{
  // Stack empty
  if (_cur==-1)
  {
    if (_cell==NULL)
    {
      _cell = this->alloc();
      _first = _cell;
    }
    _cur = 0;
  }

  // Current array not full
  else if (_cur<(_size-1))
  {
    ++_cur;
  }
  else
  {
    // Creation of a new cell
    if (_cell->next==NULL)
    {
      _cell->next = this->alloc();
      _cell->next->prev = _cell;
      _cell = _cell->next;
    }

    // Use of the next cell
    else
    {
      _cell = _cell->next;
    }
    _cur = 0;
  }

  // Allocation if the box not already created
  if (_cell->ptr[_cur]==NULL)
  {
    rp_box_create(&(_cell->ptr[_cur]),_bsize);
  }

  // Copy of Box b
  rp_box_copy(_cell->ptr[_cur],b);

  // One more box
  ++_nb;

  return( _cell->ptr[_cur] );
}

// Removal and then insertion of the current box
rp_box rp_box_stack::remove_insert()
{
  return( this->get() );
}

// NO REAL IMPLEMENTATION FOR THE FOLLOWING FUNCTIONS
rp_box_stack::rp_box_stack(const rp_box_stack& q): rp_box_set(q)
{}

rp_box_stack& rp_box_stack::operator=(const rp_box_stack& q)
{
  return( *this );
}

// ---------------------------------------
// Queue of boxes for Breadth-First Search
// ---------------------------------------
rp_box_queue::rp_box_queue(int bsize, int size):
  rp_box_set(),
  _first(NULL),
  _last(NULL),
  _curfirst(-1),
  _curlast(-1),
  _size(size),
  _bsize(bsize),
  _nb(0)
{}

rp_box_queue::~rp_box_queue()
{
  // Destruction of each cell from the queue
  while (_first!=NULL)
  {
    rp_blist aux = _first;
    _first = _first->next;

    for (int i=0; i<_size; ++i)
    {
      if (aux->ptr[i]!=NULL)
      {
	rp_box_destroy(&aux->ptr[i]);
      }
    }
    rp_free(aux->ptr);
    rp_free(aux);
  }
}

int rp_box_queue::length()
{
  int n = 0;
  rp_blist aux = _first;
  while (aux->next!=NULL)
  {
    n += _size;
    aux = aux->next;
  }
  for (int i=0; i<_size; ++i)
  {
    if (aux->ptr[i]!=NULL)
    {
      ++ n;
    }
  }
  return( n );
}

rp_box rp_box_queue::get()
{
  return( _first->ptr[_curfirst] );
}

rp_box rp_box_queue::get(int i)
{
  int shift = _size-_curfirst;
  if (i<shift)
  {
    return( _first->ptr[i+_curfirst] );
  }
  else
  {
    rp_blist l = _first->next;
    while (i>=shift+_size)
    {
      shift += _size;
      l = l->next;
    }
    return l->ptr[i-shift];
  }
}

int rp_box_queue::size()
{
  return _nb;
}

void rp_box_queue::remove()
{
  --_nb;
  if (_curfirst<_size-1)
  {
    ++ _curfirst;
  }
  else
  /* no element in current cell */
  {
    if (_nb==0)
    {
      _last = _first;
      _curfirst = _curlast = -1;
    }
    else
    {
      rp_blist aux = _first;
      _first = _first->next;
      _first->prev = NULL;
      _curfirst = 0;

      // reuse of aux at the bottom of the queue
      aux->prev = _last;
      aux->next = _last->next;
      _last->next = aux;
      if (aux->next!=NULL)
      {
	aux->next->prev = aux;
      }
    }
  }
}

int rp_box_queue::empty()
{
  return( _nb==0 );
}

rp_box_queue::rp_blist rp_box_queue::alloc()
{
  rp_blist l;
  rp_malloc(l,struct rp_blist_def*,sizeof(struct rp_blist_def));
  rp_malloc(l->ptr,rp_box*,_size*sizeof(rp_box));
  for (int i=0; i<_size; ++i)
  {
    l->ptr[i] = NULL;
  }
  l->prev = NULL;
  l->next = NULL;
  return( l );
}

rp_box rp_box_queue::insert(rp_box b)
{
  // Queue empty
  if (_nb==0)
  {
    if (_first==NULL)
    {
      _first = this->alloc();
    }
    _last = _first;
    _curfirst = _curlast = 0;
  }

  // Current array not full
  else if (_curlast<(_size-1))
  {
    ++_curlast;
  }
  else
  {
    // Creation of a new cell
    if (_last->next==NULL)
    {
      _last->next = this->alloc();
      _last->next->prev = _last;
      _last = _last->next;
    }

    // Use of the next cell
    else
    {
      _last = _last->next;
    }
    _curlast = 0;
  }

  // Allocation if the box not already created
  if (_last->ptr[_curlast]==NULL)
  {
    rp_box_create(&(_last->ptr[_curlast]),_bsize);
  }

  // Copy of Box b
  rp_box_copy(_last->ptr[_curlast],b);

  // One more box
  ++_nb;

  return( _last->ptr[_curlast] );
}

// Removal and then insertion of the current box
rp_box rp_box_queue::remove_insert()
{
  this->insert(this->get());
  this->remove();
  return( this->get() );
}

// NO REAL IMPLEMENTATION FOR THE FOLLOWING FUNCTIONS
rp_box_queue::rp_box_queue(const rp_box_queue& q): rp_box_set(q)
{}

rp_box_queue& rp_box_queue::operator=(const rp_box_queue& q)
{
  return( *this );
}
