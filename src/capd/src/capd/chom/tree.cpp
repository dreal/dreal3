// Copyright (C) 2004 by William D Kalies. All rights reserved.
//
//-----------------------------------------------------------------------------
// tree.cpp:
//-----------------------------------------------------------------------------

#include "capd/chom/tree.hpp"
#include "capd/chom/chom.hpp"

int node::counter=0;
int node::max=0;

void tree::Print(node* n)
{
  ofstream treeout("tree.dat");

  if (n==NULL)
    treeout << "0";
  else
    {
      treeout << "1";
      Print(n->Left);
      Print(n->Right);
    }
  return;
}

//Insert a node/block at certain bitcode in tree
//Assumes that node n is the (non-NULL) root node and code corresponds to a leaf
//modified by BK on 11/15/00
node* tree::Insert(const bitcode& code, node* n)
{
   if (n==NULL)
     return NULL;

   node* previous_node=Root;
   node* current_node=Root;
   for (int i=0; i<code.Bits(); ++i)
     {
 if (code[code.Bits()-1-i]==0)
   {
             current_node=current_node->Left;
      if (current_node==NULL)
        {
           if (i==code.Bits()-1)
             current_node=n;
           else
             current_node=new node();
           current_node->Parent=previous_node;
                  previous_node->Left=current_node;
        }
   }
 else
   {
      current_node=current_node->Right;
      if (current_node==NULL)
        {
           if (i==code.Bits()-1)
             current_node=n;
           else
             current_node=new node();
           current_node->Parent=previous_node;
                  previous_node->Right=current_node;
        }
   }
 previous_node=current_node;
     }
   return current_node;
}

node* tree::Find(const bitcode& code)
{
   node* current_node=Root;
   int i;
   for (i=0; i<code.Bits(); ++i)
     {
 if (code[code.Bits()-1-i]==0)
   {
             current_node=current_node->Left;
   }
 else
   {
      current_node=current_node->Right;
   }
 if (current_node==NULL)
   break;
     }
   if (i<code.Bits())
     return NULL;

   return current_node;
}

void tree::Delete(const bitcode& bc)
{
   node* n=Find(bc);
   node* parent=NULL;
   if (n==NULL)
     return;
   int i;
   for(i=0; i<bc.Bits(); ++i)
     {
 parent=n->Parent;
 if (n!=Root)
   {
      delete n;
   }
 if (bc[i]==0)
   {
      parent->Left=NULL;
      if ((parent->Right)!=NULL)
        break;
   }
 else
   {
      parent->Right=NULL;
      if ((parent->Left)!=NULL)
        break;
   }
 n=parent;
     }
}
