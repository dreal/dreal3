// Copyright (C) 2004 by William D Kalies. All rights reserved.
//
//-----------------------------------------------------------------------------
// ncell.cpp:
//-----------------------------------------------------------------------------

#include "capd/chom/edge.hpp"
#include "capd/chom/ncell.hpp"
#include "capd/chom/list.hpp"

int ncell::counter=0;
int ncell::max=0;

void ncell::Generator(bdry_list* bl, int lambda)
{
   ncell* top_ncell;
   stack<bdry_elem> T;
   while(S->top().Cell()!=this)
     {
 top_ncell=(ncell*)(S->top().Cell());
 top_ncell->Generator(bl,lambda*(S->top().Incidence()));
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

int ncell::CobdryIncidenceOf(cell* c) const
{
   cobdry_iter cbit=cobdry->Find(c);
   if (cbit!=cobdry->End())
     return((*cbit).Incidence());
   return(0);
}

int ncell::BdryIncidenceOf(cell* c) const
{
   bdry_iter bit=bdry->Find(c);
   if (bit!=bdry->End())
     return((*bit).Incidence());
   return(0);
}

void ncell::CobdryInsert(cell* c, int i)
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

void ncell::BdryInsert(cell* c, int i)
{
   if (i==0)
     bdry->Remove(c);                      // if new incidence # is 0 then remove it
   else
     {
 bdry_iter bit=bdry->Find(c);
 if (bit==bdry->End())
          bdry->InsertUniqueSort(c,i);     // not in list already
 else
   (*bit).Incidence(i);             // in list already so just change incidence number
     }
}

void ncell::Reduce(cell* cc)
{
   ncell* c=(ncell*)cc;
   ncell* cbp;
   ncell* bp;
   int incidence;
   bdry_iter bit;
   int n=c->BdryIncidenceOf(this);
//   assert(n==CobdryIncidenceOf(c));

   int nu;
   cobdry_iter cbit=cobdry->Begin();
   while (cbit!=cobdry->End())               // loop over coboundry of this cell
     {
 cbp=(ncell*)Ptr(cbit);
 if (cbp!=c)                    // don't bother with c
   {
      cbp->BdryRemove(this);    // remove this cell from boundary of coboundary elements of this cell
      if (gen_flag[int(c->Dim())])   // conversion to int added by MM to get rid of compiler  warnings
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
      bp=(ncell*)Ptr(bit);
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
  if (dim<chomDIM-1)
    c->RemoveFromCobdry();
}

cell* ncell::FindInvertibleCobdryElement()
{
   cobdry_iter cbit=cobdry->Begin();
   while (cbit!=cobdry->End())
     {
 if ((Ptr(cbit)->Interior())&&((*cbit).Invertible()))
   return(Ptr(cbit));
 ++cbit;
     }
   return(NULL);
}

void ncell::RemoveFromCobdry()
{
   cobdry_iter cbit=cobdry->Begin();
   while (cbit!=cobdry->End())
     {
       ((ncell*)Ptr(cbit))->BdryRemove(this);
       ++cbit;
     }
}

void ncell::RemoveFromBdry()
{
   bdry_iter bit=bdry->Begin();
   while (bit!=bdry->End())
     {
 if (Dim()==2)
          ((edge*)Ptr(bit))->CobdryRemove(this);
 else
   ((ncell*)Ptr(bit))->CobdryRemove(this);
        ++bit;
     }
}
