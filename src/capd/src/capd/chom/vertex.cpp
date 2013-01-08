// Copyright (C) 2004 by William D Kalies. All rights reserved.
//
//-----------------------------------------------------------------------------
// vertex.cpp:
//-----------------------------------------------------------------------------

#include "capd/chom/vertex.hpp"
#include "capd/chom/edge.hpp"
#include "capd/chom/list.hpp"

//-----------------------------------------------------------------------------
// Non-inlined member functions for vertex class
//-----------------------------------------------------------------------------

int vertex::counter=0;
int vertex::max=0;

int vertex::CobdryIncidenceOf(cell* c) const
{
   cobdry_iter cbit=cobdry->Find(c);
   if (cbit!=cobdry->End())
     return((*cbit).Incidence());
   return(0);
}

void vertex::CobdryInsert(cell* c, int i)
{
   if (i==0)
     cobdry->Remove(c);                    // if new incidence # is 0 then remove it
   else
     {
 cobdry_iter cbit=cobdry->Find(c);
 if (cbit==cobdry->End())
          cobdry->InsertUniqueSort(c,i);   // not in list already
 else
   (*cbit).Incidence(i);            // in list already so just change incidence number
     }
}

/*! \fn vertex::Reduce(cell* e)
    \brief Reduces complex by removing this vertex and the edge e.
    This routine also removes v from its coboundary, removes e from coboundary of vopp,
    and removes e from its coboundary.

    Last modified by BK on 7/13/00.
*/
void vertex::Reduce(cell* e)
{
   edge* cc;
   int no,nu;
   int n=((edge*)e)->BdryIncidenceOf(this);
   vertex* vopp=((edge *)e)->VertexOpp(this);       // vertex opposite to this along e
   vopp->CobdryRemove(e);
   cobdry_iter cbit=cobdry->Begin();
   while (cbit!=cobdry->End())                      // loop over coboundary
     {
       cc=(edge*)Ptr(cbit);
       if (cc!=e)                                   // don't bother with e
  {
     no=cc->BdryIncidenceOf(vopp);
     nu=cc->BdryIncidenceOf(this);
     cc->BdryInsert(vopp,nu);
//     if (cc->bdry[0]!=NULL)
//              assert(cc->bdry[0]!=cc->bdry[1]);
            vopp->CobdryInsert(cc,no+nu);
     if (gen_flag[1])
       {
          cc->Push(e,(-1)*n*nu);
          cc->Save();
          e->Save();
       }
  }
       ++cbit;
     }
   ((edge*)e)->RemoveFromCobdry();
}

/*! \fn cell* vertex::FindInvertibleCobdryElement()
    \brief Searches for an interior edge at this vertex which is not a loop.

    Last modified by BK on 7/13/00.
*/
cell* vertex::FindInvertibleCobdryElement()
{
   cobdry_iter cbit=cobdry->Begin();
   while (cbit!=cobdry->End())        // loop through coboundary
     {
       if (((edge*)Ptr(cbit))->Interior())     // if edge is a loop, then wouldn't be in cobdry
   {
//      assert(((edge *)Ptr(cbit))->bdry[0]!=NULL);
//      assert(((edge *)Ptr(cbit))->bdry[0]!=((edge *)Ptr(cbit))->bdry[1]);
         return(Ptr(cbit));           // found an interior edge which is not a loop
   }
       ++cbit;
     }
   return(NULL);                      // no reducible edges
}
