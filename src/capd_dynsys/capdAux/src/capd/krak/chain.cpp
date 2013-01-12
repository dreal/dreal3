/// @addtogroup krak
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file chain.cpp
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#include "capd/krak/chain.h"


/*****************************************************************************/

void capd::krak::hlink::empty(void)
{
   capd::krak::link *l=this;
   while(l->nxt!=NULL)l=l->nxt;
   for(;;){
      if(l==this) break;
      l=l->prv;
//      if(l->nxt != NULL) (l->nxt)->~link();     // not necessary, an apprioprate desctructor
                                                  // is called together with delete 20.04.99
      delete l->nxt;
      l->nxt=NULL;
   }
}

/*****************************************************************************/

capd::krak::link *capd::krak::hlink::getfirst(void)
{
   capd::krak::link *first,*second;

   first=eject();
   if(first!=NULL)
      if((second=first->eject())!=NULL) second->join(*this);
   return first;
}

/*****************************************************************************/

capd::krak::link *capd::krak::hlink::getlast(void)
{
   capd::krak::link *last,*l,*beflast=this;

   if((l=next())==NULL)
   {
      last=NULL;
   } else {
      while((l=l->next())!=NULL) beflast=beflast->next();
      last=beflast->eject();
   }
   return last;
}

/*****************************************************************************/

capd::krak::link *capd::krak::hlink::first(void)
{
   return next();
}

/*****************************************************************************/

capd::krak::link *capd::krak::hlink::last(void)
{
   capd::krak::link *lst,*l,*beflast=this;

   if((l=next())==NULL)
   {
      lst=NULL;
   } else {
      while((l=l->next())!=NULL) beflast=beflast->next();
      lst=beflast->next();
   }
   return lst;
}

/*****************************************************************************/

void capd::krak::hlink::putfirst(capd::krak::link &a_link)
{
   a_link.insert(*this);
}

/*****************************************************************************/

void capd::krak::hlink::putrand(capd::krak::link &a_link)
{
   int n=len();
   int i=int(n*std::rand()/(1.+RAND_MAX));
   a_link.insert(*((*this) >> i));
}

/*****************************************************************************/

void capd::krak::hlink::putlast(capd::krak::link &a_link)
{
   capd::krak::link *l=this;
   while(l->next()!=NULL) l=l->next();
   a_link.insert(*l);
}

/*****************************************************************************/

void capd::krak::hlink::show(capd::krak::Frame &frm)
{
   frm <<" This queue contains " << len() << " items: \n";
   capd::krak::link *l=this;
   while((l=l->next())!=NULL){
      frm << l->descriptor();
   }
}

/*****************************************************************************/

int capd::krak::hlink::len(void)
{
   int i=0;
   capd::krak::link *c=this;
   while(c->next()!=NULL){c=c->next();i++;};
   return i;
}

/*****************************************************************************/

void capd::krak::hlink::cut(int pos, capd::krak::hlink &head2)
{
   int i;
   capd::krak::link *curr;

   curr = this;
   for(i=0;i<pos;i++) curr=curr->next();
   (curr->eject())->join(head2);
}


/*****************************************************************************/

void capd::krak::hlink::merge(capd::krak::hlink *head2)
{
   capd::krak::link *c,*c2;
   int inserted;

   c=this;
   while((c2=head2->getfirst())!=NULL)
   {
      inserted=0;
      while(c->next()!=NULL)
      {
         if(c2->operator<=(*(c->next())))
         {
            c2->insert(*c);inserted=1;c=c2;break;
         }
         c=c->next();
      }
      if(!inserted) {
         c2->insert(*c);
         c=c2;
      }
   }
}

/*****************************************************************************/

void capd::krak::hlink::sort(int l)
{
   capd::krak::hlink head2;
   int l1,l2;

   l1=l/2;
   l2=l-l1;
//rootFrame << "l1=" << (long)l1 << " l2=" << (long)l2 << "  \n";

   cut(l1,head2);
   if(l1>1) sort(l1);
   if(l2>1) head2.sort(l2);
   merge(&head2);
}

 /*****************************************************************************/

/// @}
