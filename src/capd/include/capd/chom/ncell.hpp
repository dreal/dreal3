// Copyright (C) 2004 by William D Kalies. All rights reserved.
//
//-----------------------------------------------------------------------------
// ncell.hpp:
//-----------------------------------------------------------------------------

#ifndef _CAPD_CHOM_NCELL_HPP_ 
#define _CAPD_CHOM_NCELL_HPP_ 

#include "capd/chom/chom.hpp"
#include "capd/chom/cell.hpp"
#include "capd/chom/list.hpp"

/*! \class ncell
    \brief Higher-dimensional cells in a cubical complex.

    This class is for cells of dimension \f$>1\f$.
    Last modified by BK on 6/25/00.
*/

class ncell : public cell{
 private:
   bdry_list* bdry;
   cobdry_list* cobdry;
   ncell(const ncell&);            // disable copy constructor
   ncell& operator=(const ncell&); // disable assignment operator
 public:
   stack<bdry_elem>* S;
   bitcode* diagonal[2];
   cell* dv[2];

   static int counter;
   static int max;

   ncell(char d)
     :cell(d)
     {
 bdry=new bdry_list; cobdry=new cobdry_list; ++counter; ++max;
 diagonal[0]=NULL; diagonal[1]=NULL;
// if (gen_flag[d]) // conversion to int added to get rid of compiler warinings (MM)
 if (gen_flag[int(d)])
   {
      S=new stack<bdry_elem>;
      S->push(bdry_elem(this,1));
   }
 else
   S=NULL;
     }                      //!< Constructor with unknown boundary/coboundary lists.

   ncell(char d, bdry_list* b, cobdry_list* cb)
     :cell(d)
     {
 bdry=b; cobdry=cb; ++counter; ++max;
 diagonal[0]=NULL; diagonal[1]=NULL;
// if (gen_flag[d]) // conversion to int added to get rid of compiler warinings (MM)
 if (gen_flag[int(d)])
   {
      S=new stack<bdry_elem>;
      S->push(bdry_elem(this,1));
   }
 else
   S=NULL;
     }                      //!< Constructor with known boundary/coboundary lists.

   ~ncell()
     {
 delete bdry; delete cobdry; --counter;
        if (S!=NULL)
   delete S;
 if (diagonal[0]!=NULL)
   delete diagonal[0];
 if (diagonal[1]!=NULL)
   delete diagonal[1];
     }                      //<! Destructor destroys boundary and coboundary lists.

   void Generator(bdry_list*,int);
   void Push(cell* c,int i)
     {S->push(bdry_elem(c,i));}
   int CobdryIncidenceOf(cell*) const;
   int BdryIncidenceOf(cell*) const;
   void CobdryRemove(cell* c)
     {cobdry->Remove(c);}
   void BdryRemove(cell* c)
     {bdry->Remove(c);}
//      assert(!(bdry->Contains(c)));}
   void CobdryInsert(cell*, int);
   void BdryInsert(cell*, int);
   void Reduce(cell*);
   cell* FindInvertibleCobdryElement();
   void RemoveFromBdry();
   void RemoveFromCobdry();
   bdry_list* Bdry()
     {return(bdry);}
   cobdry_list* Cobdry()
     {return(cobdry);}
};

#endif // _CAPD_CHOM_NCELL_HPP_ 

