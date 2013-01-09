// Copyright (C) 2004 by William D Kalies. All rights reserved.
//
//-----------------------------------------------------------------------------
// block.hpp:
//-----------------------------------------------------------------------------

#ifndef _CAPD_CHOM_BLOCK_HPP_ 
#define _CAPD_CHOM_BLOCK_HPP_ 

#include "capd/chom/bitcodes.hpp"
#include "capd/chom/cell.hpp"
#include "capd/chom/list.hpp"
#include "capd/chom/tree.hpp"

class complex;

//-----------------------------------------------------------------------------
// Block declarations
//-----------------------------------------------------------------------------

/*! \class block
    \brief class for block data at nodes in binary tree.

    Blocks have lists of cells of any dimension.
    Last modified by BK on 10/1/00.

    Modified by MM to make it work simultaneously in several dimensions up to MAX_CHOM_DIM
*/

class block : public node{
 private:
   block(const block&);              // disable copy construction
   block operator=(const block&);    // disable copy assignment
 public:
   bitcode* bc;
//   cell_list cells[DIM+1];           // lists of interior cells at this node
   cell_list* cells;                   // modification by MM
   cell_list bdry_verts;
   static int counter;
   static int max;
   block() : node() {
     bc=new bitcode(0);
     cells=new cell_list[chomDIM+1];
   }   // used for root node of cube tree only
   block(char bits, complex* c) : node(){
     ++counter; ++max;
     bc=new bitcode(bits);
     cells=new cell_list[chomDIM+1];
   }
   block(const bitcode& cube_code, complex* c) : node(){
     ++counter; ++max; bc=new bitcode(cube_code.Bits());
     cells=new cell_list[chomDIM+1];
   }
   ~block(){
     --counter;
     delete bc;
     delete[] cells;
   }
   void CreateCells(complex*);
};

bitcode& BC(block* b);

/*! \fn Create(cell*, bitcode&, bitcode&, int, complex*, cell_list&);
    \brief Recursively creates a new cube and all its faces in any dimension.

    Last modified by BK on 5/10/00.
*/
int Create(cell**, bitcode&, bitcode&, int, complex*, cell_list&);

#endif // _CAPD_CHOM_BLOCK_HPP_ 
