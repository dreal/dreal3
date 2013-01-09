// Copyright (C) 2004 by William D Kalies. All rights reserved.
//
//-----------------------------------------------------------------------------
// list.cpp:
//-----------------------------------------------------------------------------

#include "capd/chom/list.hpp"
#include "capd/chom/cell.hpp"

//int bdry_elem::counter=0;
//int bdry_elem::max=0;

bool BdryListEqual(bdry_list* bl1, bdry_list* bl2)
{
   if (bl1->Size()!=bl2->Size())
     return(0);
   bdry_iter bit1=bl1->Begin();
   bdry_iter bit2=bl2->Begin();
   while(bit1!=bl1->End())
     {
 if (Ptr(bit1)!=Ptr(bit2))
   return(0);
 ++bit1;
 ++bit2;
     }
   return(1);
}

void BdryListInsert(bdry_list* bl, cell* c, int lambda)
{
   bdry_iter bit=bl->Find(c);
   if (bit==bl->End())
     bl->InsertUniqueSort(c,lambda);
   else
     {
 int i=(*bit).Incidence()+lambda;
 if (i==0)
   bl->Remove(c);
 else
   (*bit).Incidence(i);
     }
}

//-----------------------------------------------------------------------------
// Non-inlined member functions for bdry_list class
//-----------------------------------------------------------------------------

bool bdry_elem::operator<(const bdry_elem& be)  const     // ordering based on cell* only
{
   return(c<be.c);
//   return(c->Interior()<be.c->Interior() ? c<be.c : 0);
} // Order operator for sorting puts non-interior cells first.

bool bdry_list::Remove(cell* c)
{
   bdry_iter it=Find(c);
   if (it!=l.end())
     {
 l.erase(it);  // Use list remove instead?
// assert(!(Contains(c)));
 return true;
     }
   else
     return false;
}

void bdry_list::Print()
{
   bdry_iter it=l.begin();
   int count=1;

   if (it==l.end())
     {
 cout << "\nBdry_list is empty.\n";
 return;
     }
   else
     cout << "\nPrinting bdry_list...\n";

   while (it!=l.end())
     {
 cout<<count++<<": cell*: "<<(*it).Cell()<<", Incidence: ";
 cout<<(*it).Incidence()<<"\n";
 ++it;
     }
   cout <<"\n";
   return;
}

cell* Ptr(bdry_iter& it)
{
   return((*it).Cell());
}

//-----------------------------------------------------------------------------
// Non-inlined member functions for cell_list class
//-----------------------------------------------------------------------------

bool cell_list::Remove(cell* c)
{
   cell_iter it=Find(c);
   if (it!=l.end())
     {
 l.erase(it);  // Use list remove instead?
 return true;
     }
   else
     return false;
}

void cell_list::Print()
{
   cell_iter it=l.begin();
   int count=1;

   if (it==l.end())
     {
 cout << "\nCell_list is empty.\n";
 return;
     }
   else
     cout << "\nPrinting cell_list...\n";

   while (it!=l.end())
     {
 cout<<count++<<": cell*: "<<*it<<"\n";
 ++it;
     }
   cout << "\n";
   return;
}

cell* Ptr(cell_iter& it)
{
   return(*it);
}
