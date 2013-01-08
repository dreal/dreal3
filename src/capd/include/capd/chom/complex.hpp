// Copyright (C) 2004 by William D Kalies. All rights reserved.
//
// Modified by Marcio Gameiro - 04/28/2005
//-----------------------------------------------------------------------------
// complex.hpp:
//-----------------------------------------------------------------------------

#ifndef _CAPD_CHOM_COMPLEX_HPP_ 
#define _CAPD_CHOM_COMPLEX_HPP_ 

#include "capd/chom/chom.hpp"
#include "capd/chom/cell.hpp"
#include "capd/chom/list.hpp"
#include "capd/chom/tree.hpp"
#include "capd/chom/block.hpp"
#include "capd/chom/vertex.hpp"

/*
    Modified by MM to make it work simultaneously in several dimensions up to MAX_CHOM_DIM
*/
class complex{
 private:
   bitcode* previous_cube;  // deleted in InsertCube/FinalCube
   int* min;
   tree cubes;                      // main tree for cubical complex
   tree vertices;
   block* Merge(node*);
   void Simplify(block*);
 public:
//   complex() {}
//   complex(block* nb) : cubes(nb), previous_cube(NULL) // Initialization order changed by MM to get rid of compilation warnings
   complex(block* nb) : previous_cube(NULL), cubes(nb){
     vertices.Root=new node();
     min=new int[chomDIM];
   }
   ~complex(){
     Cleanup();
     delete[] min;
   }
   void Cleanup();
   int NewVertex(bitcode&,cell**);
   cell* FindVertex(bitcode&);
   void DeleteVertex(vertex* v)
     {vertices.Delete(*(v->bc));}
   bool InsertCube(block*);
   void FinalCube();
   void FinalSimplify(block*);
   void Homology(ofstream* gout, int Betti[]);
   void Recurse(node*,list<block*>*,int);
   void Delete(node*,int,int);
   void PrintCubes()
     {cubes.Print();}
   void PrintVertices()
     {vertices.Print();}
};

#endif // _CAPD_CHOM_COMPLEX_HPP_ 
