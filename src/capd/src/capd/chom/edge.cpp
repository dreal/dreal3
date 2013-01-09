// Copyright (C) 2004 by William D Kalies. All rights reserved.
//
//-----------------------------------------------------------------------------
// edge.cpp:
//-----------------------------------------------------------------------------

#include "capd/chom/edge.hpp"
#include "capd/chom/ncell.hpp"
#include "capd/chom/list.hpp"

//-----------------------------------------------------------------------------
// Non-inlined member functions for edge class
//-----------------------------------------------------------------------------

int edge::counter=0;
int edge::max=0;

void edge::Generator(bdry_list* bl, int lambda)
{
   edge* top_edge;
   stack<bdry_elem> T;
   while(S->top().Cell()!=this)
     {
 top_edge=(edge*)(S->top().Cell());
 top_edge->Generator(bl,lambda*(S->top().Incidence()));
 T.push(S->top());
 S->pop();
     }
   BdryListInsert(bl,this,lambda*(S->top().Incidence()));
   while(!(T.empty()))
     {
        S->push(T.top());
 T.pop();
     }
}

int edge::CobdryIncidenceOf(cell* c) const
{
   cobdry_iter cbit=cobdry->Find(c);
   if (cbit!=cobdry->End())
     return((*cbit).Incidence());
   return(0);
}

int edge::BdryIncidenceOf(cell* c) const
{
   if (bdry[0]==c)
     return(-1);
   if (bdry[1]==c)
     return(1);
   return(0);                              // a loop will have NULL boundaries
}

void edge::CobdryInsert(cell* c, int i)
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

void edge::BdryInsert(cell* c, int i)
{
   if (i==-1)                 // if -1 then put in 0th place
     bdry[0]=(vertex *)c;
   if (i==1)                  // if +1 then put in 1st place
     bdry[1]=(vertex *)c;
   if (bdry[0]==bdry[1])      // now if they are equal then delete to give 0 incidence number
     {                        // this should be the only way to make a loop
 bdry[0]=NULL;         // a loop should have NULL boundaries
 bdry[1]=NULL;
     }
}

/*! \fn void edge::Reduce(cell* c)
    \brief Reduces complex by removing this edge and the ncell c.

    Last modified by BK on 7/13/00.
*/
void edge::Reduce(cell* cc)
{
   ncell* c=(ncell*)cc;
   ncell* cbp;
   edge* bp;
   int incidence;
   bdry_iter bit;
   int n=c->BdryIncidenceOf(this);
//   assert(n==CobdryIncidenceOf(c));

   int nu;
   cobdry_iter cbit=cobdry->Begin();
   while (cbit!=cobdry->End())         // loop over coboundry of this edge
     {
 cbp=(ncell*)Ptr(cbit);
 if (cbp!=c)                    // don't bother with c
   {
      cbp->BdryRemove(this);    // remove this edge from boundary of coboundary elements of this edge
      if (gen_flag[2])
        {
           nu=CobdryIncidenceOf(cbp);
           cbp->Push(c,(-1)*n*nu);
           cbp->Save();
           c->Save();
        }
   }
 bit=c->Bdry()->Begin();
 while (bit!=c->Bdry()->End())
   {
      bp=(edge*)Ptr(bit);
      if (bp!=this)             // don't bother with this
        {
    if (cbp!=c)          // don't bother with c
      {
//         assert(bp->CobdryIncidenceOf(cbp)==cbp->BdryIncidenceOf(bp));
// !!** USE this->CobdryIncidenceOf and c->BdryIncidenceOf NOT ->BdryIncidenceOf(this) or ->CobdryIncidenceOf(c) **!!
         incidence=bp->CobdryIncidenceOf(cbp)-(CobdryIncidenceOf(cbp))*(CobdryIncidenceOf(c))*(c->BdryIncidenceOf(bp));
         bp->CobdryInsert(cbp,incidence);
         cbp->BdryInsert(bp,incidence);
//         assert(bp->CobdryIncidenceOf(cbp)==cbp->BdryIncidenceOf(bp));
      }
    bp->CobdryRemove(c); // remove c from the coboundary of the boundary elements of c
//    assert(!(bp->Cobdry()->Contains(c)));
  }
             ++bit;
          }
 ++cbit;
     }
   RemoveFromBdry();
   if (chomDIM>2)
     c->RemoveFromCobdry();
}

/*! \fn cell* edge::FindInvertibleCobdryElement()
    \brief Searches for an interior 2-cell at this edge with invertible incidence number.

    Last modified by BK on 7/13/00.
*/
cell* edge::FindInvertibleCobdryElement()
{
   cobdry_iter cbit=cobdry->Begin();
   while (cbit!=cobdry->End())
     {
 if ((((ncell*)Ptr(cbit))->Interior())&&((*cbit).Invertible()))
   return(Ptr(cbit));
 ++cbit;
     }
   return(NULL);
}

/*! \fn edge::RemoveFromCobdry()
    \brief Removes this edge from boundary of ncells in its coboundary.

    Last modified by BK on 7/13/00.
*/
void edge::RemoveFromCobdry()
{
   ncell* cbp;
   cobdry_iter cbit=cobdry->Begin();
   while (cbit!=cobdry->End())
     {
 cbp=(ncell*)Ptr(cbit);
//        assert(cbp->Bdry()->Contains(this));
        cbp->BdryRemove(this);
// assert(!(cbp->Bdry()->Contains(this)));
        ++cbit;
     }
}

/*! \fn edge::RemoveFromBdry()
    \brief Removes this edge from coboundary of vertices in its boundary.

    Last modified by BK on 7/13/00.
*/
void edge::RemoveFromBdry()
{
   if (bdry[0]!=NULL)
     {
// assert(bdry[1]!=NULL);
// assert(this->Interior());
        bdry[0]->CobdryRemove(this);
        bdry[1]->CobdryRemove(this);
     }
}

bool edge::operator==(const edge& e)
{
   return((bdry[0]==e.bdry[0])&&(bdry[1]==e.bdry[1]));
}

bool edge::operator<(const edge& e)
{
   if (bdry[0]!=e.bdry[0])
     return(bdry[0]<e.bdry[0]);
   else
     return(bdry[1]<e.bdry[1]);
}
