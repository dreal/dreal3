/// @addtogroup krak
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file item.cpp
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#include "capd/krak/item.h"

/*****************************************************************************/
capd::krak::record *capd::krak::record::framecopy(void)
/*  copy the fields with their names but assign NULL to values
*/
{
   capd::krak::record *r = new capd::krak::record;
   capd::krak::link *l = this;
   while((l=l->next())!=NULL)
   {
      r->addfield(*((capd::krak::field *)l),*((capd::krak::atom *)NULL));
   }
   return r;
}

/*****************************************************************************/
/*  copy the fields with their names,
    preserve the type of values but reassign them to trivial copies
    descent recursively other records
*/

capd::krak::record *capd::krak::record::novalcopy(void)
{
   capd::krak::record *r = new capd::krak::record;
   capd::krak::link *l=this;
   while((l=l->next())!=NULL)
   {
      capd::krak::atom *a;
      capd::krak::field &f=*(capd::krak::field *)l;
      int type=(~f)->who();
      switch(type)
      {
         case STRING: a = new capd::krak::frstring; break;
         case LIST: a = new capd::krak::list; break;
         case RECORD: a=((capd::krak::record *)(~f))->novalcopy();break;
         default: a=NULL; break;
      }
      r->addfield(f,*a);
   }
   return r;
 }

/*****************************************************************************/
capd::krak::var &capd::krak::record::operator[](capd::krak::frstring &s)
{
   capd::krak::link *l=this;
   capd::krak::var *retval;

   for(;;){
      if(NULL==(l=l->next()))
         capd::krak::errorExit("Variable %s not found",s.string());
      if( *(retval=(capd::krak::field *)l) == s) break;
   }
   return *retval;
  }

/*****************************************************************************/

  /* The next function searches for the first field in the record which has non trivial value,
     treats it as a master copy and adjusts all other fields to have the same structure.
  */
void capd::krak::record::update(void)
{
   capd::krak::link *l=this;
   capd::krak::record *muster=NULL;
   int found=0;

   while((l=(l->next()))!=NULL)
   {
      int type=l->who();
      capd::krak::field &f = *(capd::krak::field *)l;
      switch(type)
      {
         case ITEM: break;
         case FIELD:
              if(~f==NULL) break;
              if((~f)->who()!=RECORD)break;
              muster=(((capd::krak::record *)(~f))->novalcopy());
              found=1;
              break;
         default:;
      }
      if(found) break;
   }

   if(!found) capd::krak::errorExit("No master found");

   l=this;
   while((l=(l->next()))!=NULL)
   {
      capd::krak::frstring name;
      int type=l->who();
      capd::krak::field *f=(capd::krak::field *)l;
      switch(type)
      {
         case ITEM: name=*(capd::krak::item *)l;
            l=l->prev();
            (l->next())->destroy();
            f=new capd::krak::field(name);
            f->capd::krak::link::insert(*l);
            l=l->next();
         case FIELD:
             if(~(*f)==NULL) (*f)|=*muster;
             break;
         default:;
      }
   }
}

  /*****************************************************************************/

/// @}
