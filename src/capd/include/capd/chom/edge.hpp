// Copyright (C) 2004 by William D Kalies. All rights reserved.
//
//-----------------------------------------------------------------------------
// edge.hpp:
//-----------------------------------------------------------------------------

#ifndef _CAPD_CHOM_EDGE_HPP_ 
#define _CAPD_CHOM_EDGE_HPP_ 

#include "capd/chom/chom.hpp"
#include "capd/chom/vertex.hpp"
#include "capd/chom/list.hpp"

/*! \class edge
    \brief Edges of a cubical complex.

    Edges have an orientation always from \f$v(0)\to v(1)\f$.
    Last modified by BK on 6/25/00.
*/

class edge : public cell{
 private:
   cobdry_list* cobdry;          // edges have a private coboundary list
   edge(const edge&);            // disable no copy constructor
   edge& operator=(const edge&); // disable assignment operator
 public:
   bitcode* diagonal[2];
   vertex* bdry[2];              // edges are an oriented array of two vertices.
   stack<bdry_elem>* S;

   static int counter;
   static int max;

   edge(vertex* v1, vertex* v2)
     :cell(1)
     {
 bdry[0]=v1; bdry[1]=v2; cobdry=new cobdry_list;
 diagonal[0]=NULL; diagonal[1]=NULL;
 if (gen_flag[1])
   {
      S=new stack<bdry_elem>;
      S->push(bdry_elem(this,1));
   }
 else
   S=NULL;
 ++counter; ++max;
     }                           //!< Constructor when no coboundary list is known.

   ~edge()
     {
 delete cobdry; --counter;
        if (S!=NULL)
   delete S;
 if (diagonal[0]!=NULL)
   delete diagonal[0];
 if (diagonal[1]!=NULL)
   delete diagonal[1];
     }                           //!< Destructor destroys coboundary list.

   vertex* VertexOpp(const vertex* v) const
     {return(bdry[0]==v ? bdry[1] : bdry[0]);}
                                 //!< Returns pointer to the vertex opposite of v along this edge.
   void Push(cell* c,int i)
     {S->push(bdry_elem(c,i));}
   void Generator(bdry_list*,int);
   int CobdryIncidenceOf(cell*) const;
   int BdryIncidenceOf(cell*) const;
   void CobdryRemove(cell* c)
     {cobdry->Remove(c);}
   void BdryRemove(cell*);
   void CobdryInsert(cell*, int);
   void BdryInsert(cell*, int);
   void Reduce(cell*);
   cell* FindInvertibleCobdryElement();
   void RemoveFromBdry();
   void RemoveFromCobdry();
   cobdry_list* Cobdry()
     {return(cobdry);}
   bool operator==(const edge &);
   bool operator<(const edge &);
};

#endif // _CAPD_CHOM_EDGE_HPP_ 
