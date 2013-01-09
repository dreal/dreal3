/// @addtogroup krak
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file chain.h
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifndef _CAPD_KRAK_CHAIN_H_ 
#define _CAPD_KRAK_CHAIN_H_ 
#include <iostream>
#include <fstream>
#include "capd/krak/frame.h"

namespace capd{
namespace krak{
   class hlink;
   class item;
   class field;
   class pointing_field;
   class list;
   class record;
   class dblstr_item;
   class tst_b;
}}

/************************************ link **********************************/

namespace capd{
namespace krak{

class link : public capd::krak::atom
{
   friend class hlink;
   friend class item;
   friend class field;
   friend class pointing_field;
   friend class list;
   friend class record;
   friend class dblstr_item;
   friend class tst_b;

private:
   capd::krak::link *nxt,*prv;

public:
   capd::krak::frstring virtual descriptor(void);
   capd::krak::frstring virtual description(void);

protected:
   link(void);                              // default constructor
   virtual ~link(void);                     // destructor
   virtual capd::krak::atom *copy(void);
   void bind(void);                         // reconstruct missing reverse links
                                           // from forward links
   void operator=(link &a_link);
   void join(link &pred);
   link *eject(void);
   void insert(link &pred);

public:
   link &withdraw(void);
   void destroy(void);
   link *operator>>(int i);
   link *operator<<(int i);
   link *next(void);
   link *prev(void);
   int virtual who(void);
};

/************************************ hlink **********************************/

class hlink : public capd::krak::link
{
/* class hlink serves as a head of a chain of links

*/
public:


   hlink(void);
   void empty(void);                     //constructor
   virtual ~hlink(void);                 //destructor
   virtual capd::krak::atom *copy(void);             //virtual constructor
   hlink &operator=(hlink &v);           //destroy current structure,
                                        //make complety copy of v
   hlink &operator+( link &l);           //insert link at the end
   hlink &operator-( link &l);           //insert link at the beginning
   void promote(link &l);                //remove the link from wherever it is
                                        //and put it at the top of this list
   link *getfirst(void);                 //extract the first link from the list
                                        //and return a pointer to it
   link *getlast(void);                  //extract the last link from the list
                                        //and return a pointer to it
   link *first(void);                    //return the pointer to the first link
   link *last(void);                     //return the pointer to the last link
   void putfirst(link &a_link);          //insert the link at the top of the list
   void putlast(link &a_link);           //insert the link at the bottom of the list
   void putrand(link &a_link);           //insert the link at random
   void show(capd::krak::Frame &frm);                //print the contents of the list
   int len(void);                        //return the length of the list
   void merge(hlink *head2);             //merge the other list
   void cut(int pos, hlink &head2);      //cut to to lists at the given position
   void sort(int l);
   void sort(void);                      //sort the list
   int virtual who(void);
   capd::krak::frstring virtual descriptor(void);
   capd::krak::frstring virtual description(void);
};
}} // the end of the namespace capd::krak

/************************************ sn **********************************/

/*
class sn:public link
begin
  public:

  int val;

  frstring virtual descriptor(void);
  sn(void);
  int operator<=(link &sn2);
  int operator>=(link &sn2);
  int operator==(link &sn2);
end;
*/
//############################# inline definitions #############################

/************************************ link **********************************/

inline capd::krak::link::link(void)                              // default constructor
{
   nxt=prv=NULL;
}

inline capd::krak::link::~link(void)                     // destructor
{
   delete nxt;
   nxt=NULL;
}

inline capd::krak::atom*  capd::krak::link::copy(void)
{
   capd::krak::link* l = new capd::krak::link;
   if(nxt!=NULL)
   {
      (l->nxt)=(capd::krak::link *)(nxt->copy());
      (l->nxt)->prv=l;    // unverified change on 20.04.99 it seems to be necessary!
                          // although in hlink this is performed by bind!
                          // to get rid of bind one should ensure that
                          // this line is performed in every descendant of link
   }
   return l;
}

inline void capd::krak::link::bind(void)
{
   capd::krak::link *l=this;
   while(l->nxt!=NULL)
   {
      (l->nxt)->prv=l;
      l=l->nxt;
   }
}

inline void capd::krak::link::operator=(capd::krak::link &a_link)
{
   capd::krak::errorExit("Do not assign a link to a link");
}

inline void capd::krak::link::join(capd::krak::link &pred)
{
   if(pred.nxt==NULL && prv==NULL)
   {
      pred.nxt=this;prv=&pred;
   }
   else
      capd::krak::errorExit("Cannot join an occupied link");
}

inline capd::krak::link* capd::krak::link::eject(void)
{
   capd::krak::link* l=nxt;
   nxt=NULL;
   if (l!=NULL) l->prv=NULL;
   return l;
}

inline void capd::krak::link::insert(capd::krak::link &pred)
{
   if(nxt==NULL && prv==NULL)
   {
      prv=&pred;
      nxt=pred.nxt;
      pred.nxt=this;
      if(nxt!=NULL) nxt->prv=this;
   } else {
      capd::krak::errorExit("Cannot insert a non-free link");
   }
}

inline capd::krak::link &capd::krak::link::withdraw(void)
{
   if(prv!=NULL) prv->nxt=nxt;
   if(nxt!=NULL) nxt->prv=prv;
   nxt=NULL;
   prv=NULL;
   return *this;
}

inline void capd::krak::link::destroy(void)
{
   withdraw();
   delete this;
}

inline capd::krak::link* capd::krak::link::operator>>(int i)
{
   capd::krak::link *l=this;
   int j=0;

   while(++j<=i && (l=l->nxt)!=NULL);
   return l;
}

inline capd::krak::link* capd::krak::link::operator<<(int i)
{
   capd::krak::link *l=this;
   int j=0;

   while(++j<=i && (l=l->prv)!=NULL);
   return l;
}

inline capd::krak::link *capd::krak::link::next(void)
{
   return nxt;
}

inline capd::krak::link* capd::krak::link::prev(void)
{
   return prv;
}

inline int capd::krak::link::who(void)
{
   return LINK;
}

inline capd::krak::frstring capd::krak::link::descriptor(void)
{
   capd::krak::frstring s("Just a link \n");
   if (nxt!=NULL) s=s^nxt->descriptor();
   return s;
}

inline capd::krak::frstring capd::krak::link::description(void)
{
   capd::krak::frstring s=descriptor();
   if (nxt!=NULL) s=s^nxt->description();
   return s;
}

/********************************* hlink ************************************/

inline capd::krak::hlink::hlink(void)
   : capd::krak::link()
{}

inline capd::krak::frstring capd::krak::hlink::descriptor(void)
{
   capd::krak::frstring s="A queue which contains: {\n";
   if (nxt!=NULL) s=s^nxt->descriptor();
   s=s^" }\n";
   return s;
}

inline capd::krak::frstring capd::krak::hlink::description(void)
{
   capd::krak::frstring s=descriptor();
   if (nxt!=NULL) s=s^nxt->description();
   s=s^" }\n";
   return s;
}

inline capd::krak::hlink::~hlink(void)
{
   this->empty();
}

inline capd::krak::atom* capd::krak::hlink::copy(void)
{
   capd::krak::link *l = new capd::krak::hlink;
   if(nxt!=NULL) (l->nxt)=(capd::krak::link *)(nxt->copy());
   l->bind();
   return l;
}

inline capd::krak::hlink & capd::krak::hlink::operator=(capd::krak::hlink &v)
{
   this->~hlink();
   if(v.next()!=NULL) nxt=(capd::krak::link *)(v.next()->copy());
   this->bind();
   return *this;
}

inline capd::krak::hlink &capd::krak::hlink::operator+(capd::krak::link &l)
{
   putlast(l);
   return *this;
}

inline capd::krak::hlink &capd::krak::hlink::operator-(capd::krak::link &l)
{
   putfirst(l);
   return *this;
}

inline void capd::krak::hlink::promote(capd::krak::link &l)
{
   putfirst(l.withdraw());
}

inline void capd::krak::hlink::sort(void)
{
   sort(len());
}

inline int capd::krak::hlink::who(void)
{
   return HLINK;
}

/***************************************** sn ********************************/
/*
  inline frstring sn::descriptor(void)
  begin
    frstring t=double2string(val);
    return "Number "^t^frstring("\n");
  end;

  inline sn::sn(void) : link()
  begin
    val=0;
  end;


  inline int sn::operator<=(link &sn2)
  begin
    return (val<=((sn *)&sn2)->val);
  end

  inline int sn::operator>=(link &sn2)
  begin
    return (val>=((sn *)&sn2)->val);
  end

  inline int sn::operator==(link &sn2)
  begin
    return (val==((sn *)&sn2)->val);
  end
*/

#endif // _CAPD_KRAK_CHAIN_H_ 

/// @}
