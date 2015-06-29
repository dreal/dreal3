/*********************************************************************
Author: Roberto Bruttomesso   <roberto.bruttomesso@gmail.com>
Author: Simone Fulvio Rollini <simone.rollini@gmail.com>

OpenSMT -- Copyright (C) 2010, Roberto Bruttomesso
PeRIPLO -- Copyright (C) 2013, Simone Fulvio Rollini

Periplo is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

Periplo is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with Periplo. If not, see <http://www.gnu.org/licenses/>.
*********************************************************************/

/*********************************************************************
The code here is adapted from simple top-down splay from the publicy
available code of D. Sleator, avaialable via anonymous ftp from
spade.pc.cs.cmu.edu in directory /usr/sleator/public.

I've made it a template class parametrizable with the data T to be
stored and the comparison function C
*********************************************************************/

#ifndef SPLAY_TREE_H
#define SPLAY_TREE_H

#include <iostream>
#include "opensmt/minisat/mtl/Vec.h"

template <class T, class C >
class SplayTree
{
public:

  SplayTree( )
    : last_node  ( NULL )
    , initialized( false )
    , size       ( 0 )
  { }

  ~SplayTree( )
  {
    deleteTree();
    delete bnil_node;
    if ( last_node )
      delete last_node;
  }

  void setNil( T & e )
  {
    assert( !initialized );
    //
    // Initialize splay tree with just the
    // node containing an atom that we use
    // to express a failure in the search
    //
    bnil_node = new Bnode;
    bnil_node->left  = bnil_node;
    bnil_node->right = bnil_node;
    bnil_node->element = e;
    root = bnil_node;
    initialized = true;
  }

  T &         find    ( T & x );
  inline bool isEmpty ( ) const { assert( initialized ); return root == bnil_node; }

  T &  insert         ( T & );
  void remove         ( T & );
  //
  // Copy is not supported
  //
  const SplayTree & operator=( const SplayTree & ) = delete;

  void printStatistics( std::ostream & );

  void printTree            ();

  void debug                (const T elems[], int size);

private:
  //
  // Nodes of the tree
  //
  struct Bnode
  {

    Bnode( )
      : left( NULL )
      , right( NULL )
    { }

    Bnode( T & t, Bnode * lt, Bnode * rt )
      : element( t )
      , left   ( lt )
      , right  ( rt )
    { }

    T       element;
    Bnode * left;
    Bnode * right;
  };

  void deleteTree           ();
  void rotateWithLeftChild  ( Bnode * & k2 );
  void rotateWithRightChild ( Bnode * & k1 );
  void splay                ( T & x, Bnode * & t );

  Bnode *  root;             // rott of the tree
  Bnode *  last_node;        // rott of the tree
  Bnode *  bnil_node;        // nil node
  C        cmp;              // Comparison structure
  bool     initialized;      // Check if the nil node has been initialized
  unsigned size;             // Keep track of the size of the tree (number of nodes)
  struct SplayTreePair {
    Bnode* node;
    int    depth;
  };

public:
  void perf                 ( std::ostream & os );
  void printTree            ( Bnode* t );
};

//
// Inserts an element
//
template <class T, class C>
T & SplayTree< T, C >::insert( T & x )
{
  assert( initialized );

  if( last_node == NULL )
  {
    last_node = new Bnode;
  }

  last_node->element = x;

  if( root == bnil_node )
  {
    last_node->left = last_node->right = bnil_node;
    root = last_node;
  }
  else
  {
    splay( x, root );
    //
    // Element is less than
    //
    if( cmp( x, root->element ) )
    {
      last_node->left = root->left;
      last_node->right = root;
      root->left = bnil_node;
      root = last_node;
    }
    //
    // Element is greater than
    //
    else if( cmp( root->element, x ) )
    {
      last_node->right = root->right;
      last_node->left = root;
      root->right = bnil_node;
      root = last_node;
    }
    //
    // Element is equal; do not insert
    //
    else
    {
      return root->element;
    }
  }

  last_node = NULL;  // Element inserted
   size ++;
  return x;          // Insertion took place
}

//
// Remove element
//
template <class T, class C>
void SplayTree< T, C >::remove( T & x )
{
  assert( initialized );

  if (root == bnil_node) return;

  Bnode * new_tree;

  // If x is found, it will be at the root
  splay( x, root );
  if( root->element != x )
    return;   // Item not found; do nothing

  if( root->left == bnil_node )
    new_tree = root->right;
  else
  {
    // Find the maximum in the left subtree
    // Splay it to the root; and then attach right child
    new_tree = root->left;
    splay( x, new_tree );
    new_tree->right = root->right;
  }
  delete root;
  root = new_tree;

  size --;
}

//
// Find an element
//
template <class T, class C>
T & SplayTree< T, C >::find( T & x )
{
  assert( initialized );

  if( isEmpty( ) )
    return bnil_node->element;
  splay( x, root );
  if( root->element != x )
    return bnil_node->element;

  return root->element;
}

//
// Splay the tree with respect to t
//
template <class T, class C>
void SplayTree< T, C >::splay( T & t, Bnode * & n )
{
  assert( initialized );

  Bnode N, *l, *r, *y;

  if (n == bnil_node) return;

  N.left = N.right = bnil_node;

  l = r = &N;

//  Bnode *leftTreeMat, *rightTreeMin;
//  static Bnode header;

//  header.left = header.right = bnil_node;
//  leftTreeMat = rightTreeMin = &header;

  // t is always assigned to bnil_node->element
  // If the tree is empty, t will now be inserted to the tree!
//  bnil_node->element = t;

  for(;;)
  {
    if( cmp( t, n->element ) )
    {
      if( n->left == bnil_node )
        break;
      if( cmp( t, n->left->element ) ) {
        y = n->left;
        n->left = y->right;
        y->right = n;
        n = y;
        if (n->left == bnil_node) break;
      }
      // Link Right
      r->left = n;
      r = n;
      n = n->left;
    }
    else if ( cmp( n->element, t ) )
    {
      if ( n->right == bnil_node ) break;
      if ( cmp( n->right->element, t ) ) {
        y = n->right;
        n->right = y->left;
        y->left = n;
        n = y;
        if( n->right == bnil_node ) break;
      }
      // Link Left
      l->right = n;
      l = n;
      n = n->right;
    }
    else
      break;
  }

  l->right = r->left = bnil_node;

  l->right = n->left;
  r->left = n->right;
  n->left = N.right;
  n->right = N.left;

}

//
// Recursively delete the tree
//
template <class T, class C>
void SplayTree< T, C >::deleteTree()
{
  assert( initialized );

  Bnode** stack = new Bnode*[this->size];
  int idx = 0;
  stack[idx] = root;

  while (idx >= 0) {
    Bnode* t = stack[idx--];

    // Weird test, but essentially leaves out the bnil_node
    if( t != t->left )
    {
      stack[++idx] = t->left;
      if (this->size >= 2) {
          stack[++idx] = t->right;
      }
      delete t;
    }
  }

  delete[] stack;
}

template <class T, class C>
void SplayTree<T,C>::printTree(Bnode* t)
{
  if ( t == bnil_node) return;

  std::cout << "el: " << t->element;
  if (t->left != bnil_node)
    std::cout << " left: " << t->left->element;
  if (t->right != bnil_node)
    std::cout << " right : " << t->right->element;
  std::cout << std::endl;

  if (t->left != bnil_node)
    printTree(t->left);
  if (t->right != bnil_node)
    printTree(t->right);
}

template <class T, class C>
void SplayTree< T, C>::printTree()
{
  std::cout << "======" << std::endl << "Tree of size " << size << std::endl;
  printTree(root);
  std::cout << "======" << std::endl;
}

template <class T, class C>
void SplayTree< T, C >::printStatistics( std::ostream & os )
{
  os << "#" << std::endl;
  os << "# Total bnodes..........: " << size << std::endl;
  os << "# Bnode size in memory..: " << size * sizeof( Bnode ) / ( 1024.0 * 1024.0 ) << " MB" << std::endl;
  os << "# Avg size per bnode....: " << sizeof( Bnode ) << " B" << std::endl;
}

template <class T, class C>
void SplayTree<T,C>::debug(const T elems[], int size)
{
  assert( isEmpty() );
  if (size == 0) return;
  Bnode* prev = bnil_node;
  for (int i = size-1; i >= 0; i--) {
    Bnode* c = new Bnode;
    c->left = bnil_node;
    c->right = prev;
    c->element = elems[i];
    prev = c;
  }
  root = prev;
  this->size = size;
}


template <class T, class C>
void SplayTree<T,C>::perf( std::ostream & os ) {
  os << "#" << std::endl;
  os << "# Total bnodes..........: " << size << std::endl;
  os << "# Max depth.............: ";
  vec<SplayTreePair> queue;
  SplayTreePair p;
  p.node = root;
  p.depth = 0;
  queue.push(p);
  int max_depth = 0;
  while (queue.size() > 0) {
    SplayTreePair& pr = queue.last();
    queue.pop();
    if (pr.node->left != bnil_node) {
      SplayTreePair l;
      l.node = pr.node->left;
      l.depth = pr.depth+1;
      queue.push(l);
    }
    if (pr.node->right != bnil_node) {
      SplayTreePair r;
      r.node = pr.node->right;
      r.depth = pr.depth+1;
      queue.push(r);
    }
    max_depth = max_depth < pr.depth ? pr.depth : max_depth;
  }

  os << max_depth << std::endl;
}

#endif
