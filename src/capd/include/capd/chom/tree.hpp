// Copyright (C) 2004 by William D Kalies. All rights reserved.
//
//-----------------------------------------------------------------------------
// tree.hpp:
//-----------------------------------------------------------------------------

#ifndef _CAPD_CHOM_TREE_HPP_ 
#define _CAPD_CHOM_TREE_HPP_ 

#include "capd/chom/bitcodes.hpp"

class node{
 public:
   node *Left,*Right,*Parent;
   static int counter;
   static int max;
   node():Left(NULL),Right(NULL),Parent(NULL){++counter; ++max;}
   node(node *L, node *R):Left(L),Right(R),Parent(NULL){++counter; ++max;}
   node(node *P):Left(NULL),Right(NULL),Parent(P){++counter; ++max;}
   ~node() {--counter;}
   friend class tree;
};

class tree{
 public:
   node* Root;
   tree(): Root(NULL){}
   tree(node* n): Root(n) {}
   node* Find(const bitcode&);
   node* Insert(const bitcode&, node*);
   void Delete(const bitcode&);
   void Print(node*);
   void Print()
    {Print(Root);}
};

#endif // _CAPD_CHOM_TREE_HPP_ 
