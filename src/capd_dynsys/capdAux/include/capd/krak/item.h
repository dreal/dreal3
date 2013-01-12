/////////////////////////////////////////////////////////////////////////////
/// @file item.h
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifndef _CAPD_KRAK_ITEM_H_ 
#define _CAPD_KRAK_ITEM_H_ 
#include "capd/krak/chain.h"

/************************************ item **********************************/
namespace capd{
namespace krak{
class item : public capd::krak::link, public virtual capd::krak::frstring
/*  Linkable free strings
*/
{
   friend class list;
protected:

  // constructors
   item(void) : capd::krak::frstring(), capd::krak::link(){}
   item(item &another_item) : capd::krak::frstring(another_item), capd::krak::link() {}
   item(const capd::krak::frstring &from) : capd::krak::frstring(from), capd::krak::link() {}
   item(char *init_string) : capd::krak::frstring(init_string), capd::krak::link() {}

   virtual capd::krak::atom *copy(void);    //virtual constructor
   virtual ~item(void);         //destructor

public:

   int virtual who(void);                //test what atom (see krak/atom.h)
   int virtual operator<=(capd::krak::atom &a2);
   int virtual operator>=(capd::krak::atom &a2);
   int virtual operator==(capd::krak::atom &a2);
   capd::krak::frstring virtual descriptor(void);
   void put(std::ostream &out);
};

/************************************ var **********************************/

class var : public virtual capd::krak::frstring
/* variables, have name inherited form string and values,
   which may be arbitraty atoms.
*/
{
public:
   capd::krak::atom *value;            // pointer to value, may be NULL

//constructors
   var(void);
   var(var &a_var);
   var(char *text);
   var(capd::krak::frstring &text);
   var(capd::krak::frstring &s, capd::krak::atom &a);
   var(capd::krak::frstring &s, capd::krak::frstring &v);

protected:
   virtual capd::krak::atom *copy();            //virtual constructor
   virtual ~var(void);              //destructor

public:
   var &operator=(var &a_var);          //takes over the name and value
   frstring virtual descriptor(void);
   var &operator|=(capd::krak::atom &a);            //assign copy of *atom to value
   var &operator|=(capd::krak::frstring &s);        //assign copy of *s to value
   capd::krak::frstring &operator!(void);           //return value if frstring (???)
                                       //will fail if value is not an item
   capd::krak::atom *operator~(void);               //return pointer to value
   int virtual who(void);               //test what atom (see krak/atom.h)
   void virtual put(std::ostream &out);
};

/************************************ field **********************************/

class field : public item, public var
/*  field is a linkable var;
*/
{
   friend class record;
protected:

  //constructors
   field(void);
   field(capd::krak::frstring &t);                  //a field with no value
   field(capd::krak::frstring &t,capd::krak::atom &a);
   field(capd::krak::frstring &t,capd::krak::frstring &s);

   virtual ~field(void);               //destructor
   virtual capd::krak::atom *copy();               //virtual constructor
   field &operator=(field &a_field);   //copies everything, including followers
                                      //probably not save in usage !!!!!
public:

   int virtual who(void);              //test what atom (see krak/atom.h)
   capd::krak::frstring virtual descriptor(void);
   void virtual put(std::ostream &out);
};

/******************************* pointing_field ****************************/

class pointing_field : public field
/* introduced to enable alternatively sorted records
   however its usage not clear. Even not clear if used at all !!!
*/
{
public:

   pointing_field(void);
   virtual ~pointing_field(void);
};

/************************************ list **********************************/

class list : public hlink
/*  stores a linked list of atoms;
*/
{
public:

   list(void);                           //constructor
   int virtual who(void);                //test what atom (see krak/atom.h)
   virtual capd::krak::atom *copy(void);             //virtual constructor
   capd::krak::frstring virtual descriptor(void);
   list &operator+(capd::krak::frstring s);         //insert the given string at the end
   void additem(capd::krak::frstring &s);            //the same, different syntax
   capd::krak::atom *operator[](int i);              //pointer to the element at the given
                                        //position
   virtual void put(std::ostream &out);
};

/************************************ record **********************************/

class record : public list
{
public:

   record(void);                         //constructor
   int virtual who(void);                //test what atom (see krak/atom.h)
   virtual capd::krak::atom *copy(void);             //virtual constructor
   capd::krak::frstring virtual descriptor(void);
   record &operator+(capd::krak::frstring s);       //insert a field of a give name,
                                        // but no value
// various version of adding a field with value
   void addfield(capd::krak::frstring &name, capd::krak::atom &val);
   void addfield(capd::krak::frstring &name, capd::krak::frstring &val);
   void addfield(capd::krak::frstring &name, capd::krak::const_string &val);
   void addpointing_field(capd::krak::frstring &name, capd::krak::atom &val);

// copy the fields with their names but assign NULL to values
   record *framecopy(void);
// copy the fields with their names,
//  preserve the type of values but reassign them to trivial copies
//  descent recursively other records
   record *novalcopy(void);

//return pointer to the field of the given name
   capd::krak::var &operator[](capd::krak::frstring &s);
// search for the first field in the record which has non trivial value,
// treat it as a master copy and adjust all other fields to have
// the same structure.

   void update(void);

   virtual void put(std::ostream &out);
};

}} // the end of the namespace capd::krak

//########################### inline definitions ##############################/

/************************************ item **********************************/

inline capd::krak::atom *capd::krak::item::copy(void)
{
   capd::krak::item *i = new capd::krak::item;
   capd::krak::atom *a=(capd::krak::atom *)(void *)i;
   capd::krak::frstring *s=i;
   *s=*this;
   i->nxt=( next()==NULL ? NULL : (capd::krak::link *)(next()->copy()) );
   return a;
}

/*
inline capd::krak::atom *capd::krak::item::copy(void)
{
   capd::krak::item *i = new capd::krak::item;
   capd::krak::frstring *s=i;
   *s=*this;
   i->nxt=( next()==NULL ? NULL : (capd::krak::link *)(next()->copy()) );
   return (capd::krak::link *)i;
}
*/

inline capd::krak::item::~item(void)
{
   delete nxt;
   nxt=NULL;
   delete str;
   str=NULL;
}

inline int capd::krak::item::who(void)
{
   return ITEM;
}

inline int capd::krak::item::operator<=(capd::krak::atom &a2)
{
   capd::krak::item *item2=(capd::krak::item *)(void *)&a2;
   capd::krak::frstring *s1=this,*s2=item2;
   return *s1<=*s2;
}

inline int capd::krak::item::operator>=(capd::krak::atom &a2)
{
   capd::krak::item *item2=(capd::krak::item *)(void *)&a2;
   capd::krak::frstring *s1=this,*s2=item2;
   return *s1>=*s2;
}

inline int capd::krak::item::operator==(capd::krak::atom &a2)
{
   capd::krak::item *item2 = (capd::krak::item *)(void *)&a2;
   capd::krak::frstring *s1=this,*s2=item2;
   return *s1==*s2;
}

inline capd::krak::frstring capd::krak::item::descriptor(void)
{
   capd::krak::frstring s="Item: "^*this^capd::krak::frstring("\n");
   if (nxt!=NULL) s=s^nxt->descriptor();
   return s;
}

inline void capd::krak::item::put(std::ostream &out)
{
   capd::krak::frstring::put(out);
   out.put('\n');
   if (next()!=NULL) next()->put(out);
}

/************************************** var ***********************************/

inline capd::krak::var::var(void)
{
   value=NULL;
}

inline capd::krak::var::var(capd::krak::var &a_var) : capd::krak::frstring(a_var)
{
   value=(a_var.value==NULL ? NULL : a_var.copy());
}

inline capd::krak::var::var(char *text): capd::krak::frstring(text)
{
   value=NULL;
}

inline capd::krak::var::var(capd::krak::frstring &text): capd::krak::frstring(text)
{
   value=NULL;
}

inline capd::krak::var::var(capd::krak::frstring &s, capd::krak::atom &a) : capd::krak::frstring(s)
{
   value=a.copy();
}

inline capd::krak::var::var(capd::krak::frstring &s, capd::krak::frstring &v) : capd::krak::frstring(s)
{
   value=v.copy();
}

inline capd::krak::atom *capd::krak::var::copy()
{
   capd::krak::var *v = new capd::krak::var;
   capd::krak::frstring *s=v;
   *s=*this;
   v->value=(value==NULL ? NULL : value->copy());
   return v;
}

inline capd::krak::var::~var(void)
{
   delete str;
   str=NULL;
   delete value;
   value=NULL;
}

inline capd::krak::var &capd::krak::var::operator=(capd::krak::var &a_var)
{
   this->~var();
   (*this).frstring::operator=(a_var);
   value=(a_var.value==NULL ? NULL : a_var.value->copy());
   return *this;
}

inline capd::krak::frstring capd::krak::var::descriptor(void)
{
   capd::krak::frstring t;
   t="Variable: "^*this^capd::krak::frstring("\n")^capd::krak::frstring("With value=[");

   if(value==NULL) t=t^"NULL\n";
   else t=t^value->descriptor();
   t=t^"]\n";
   return t;
}


inline capd::krak::var &capd::krak::var::operator|=(capd::krak::atom &a)
{
   value=a.copy();
   return *this;
}

inline capd::krak::var &capd::krak::var::operator|=(capd::krak::frstring &s)
{
   value=s.copy();
   return *this;
}

inline capd::krak::frstring &capd::krak::var::operator!(void)
{
   return *((capd::krak::frstring *)value);
}

inline capd::krak::atom *capd::krak::var::operator~(void)
{
   return value;
}

inline int capd::krak::var::who(void)
{
   return VAR;
}

inline void capd::krak::var::put(std::ostream &out)
{
   capd::krak::frstring::put(out);
   out.put(':');
   if(value!=NULL) value->put(out);
   out.put('\n');
}

/********************************** field ************************************/

inline capd::krak::field::field(void)
   : capd::krak::frstring(), capd::krak::item(), capd::krak::var() {}

inline capd::krak::field::field(capd::krak::frstring &t)
   : capd::krak::frstring(t), capd::krak::item(), capd::krak::var() {}

inline capd::krak::field::field(capd::krak::frstring &t, capd::krak::atom &a)
   : capd::krak::frstring(t), capd::krak::var(t,a){}

inline capd::krak::field::field(capd::krak::frstring &t,capd::krak::frstring &s)
   : capd::krak::frstring(t), capd::krak::var(t,s){}

inline capd::krak::field::~field(void)
{
   delete str;
   delete value;
   delete nxt;
   str=NULL;value=NULL;nxt=NULL;
}


inline capd::krak::atom *capd::krak::field::copy()
{
   capd::krak::field *f = new capd::krak::field;
   capd::krak::atom *a = (capd::krak::atom *)(void *)f;
   capd::krak::frstring *s=f;
   *s=*this;
   f->nxt=(nxt==NULL ? NULL : (capd::krak::link *)(nxt->copy()));
   f->value=(value==NULL ? NULL : value->copy());
   return a;
}

/*
inline capd::krak::atom *capd::krak::field::copy()
{
   capd::krak::field *f=new capd::krak::field;
   capd::krak::frstring *s=f;
   *s=*this;
   f->nxt=(nxt==NULL ? NULL : (capd::krak::link *)(nxt->copy()));
   f->value=(value==NULL ? NULL : value->copy());
   return (capd::krak::link *)f;
}
*/

inline capd::krak::field &capd::krak::field::operator=(capd::krak::field &a_field)
{
   this->~field();
   (*this).frstring::operator=(a_field);
   value=(a_field.value==NULL ? NULL : a_field.value->copy());
   nxt=(a_field.nxt==NULL ? NULL : (capd::krak::link *)(a_field.nxt->copy()));
   return *this;
}

inline int capd::krak::field::who(void)
{
   return FIELD;
}

inline capd::krak::frstring capd::krak::field::descriptor(void)
{
   capd::krak::frstring t;
   t="Field : "^*this^capd::krak::frstring("\n")^capd::krak::frstring("With value=[");
   if(value==NULL) t=t^"NULL\n";
   else t=t^value->descriptor();
   t=t^"]\n";
   if (nxt!=NULL) t=t^nxt->descriptor();
   return t;
}

inline void capd::krak::field::put(std::ostream &out)
{
   capd::krak::frstring::put(out);
   out.put(':');
   if(value!=NULL) value->put(out);
   out.put('\n');
   if(next()!=NULL) next()->put(out);
}

/******************************* pointing_field ****************************/

inline capd::krak::pointing_field::pointing_field(void): capd::krak::field(){}

inline capd::krak::pointing_field::~pointing_field(void)
{
   delete str;
   delete nxt;
   str=NULL;
   value=NULL;
   nxt=NULL;
}

/************************************ list **********************************/

inline capd::krak::list::list(void): capd::krak::hlink(){}

inline int capd::krak::list::who(void)
{
   return LIST;
}

inline capd::krak::atom *capd::krak::list::copy(void)
{
   capd::krak::list *l = new capd::krak::list;
   if(next()!=NULL) l->nxt=(capd::krak::link *)(next()->copy());
   l->bind();
   return l;
}

inline capd::krak::frstring capd::krak::list::descriptor(void)
{
   capd::krak::frstring s="A list which contains: {\n";
   if (next()!=NULL) s=s^next()->descriptor();
   s=s^"}\n";
   return s;
}

inline capd::krak::list &capd::krak::list::operator+(capd::krak::frstring s)
{
   capd::krak::hlink &h=*this;

   capd::krak::item & an_item = * new capd::krak::item(s);

   h+an_item;
//  hlink::operator+(an_item);
   return *this;
}

inline void capd::krak::list::additem(capd::krak::frstring &s)
{
   capd::krak::hlink &h=*this;

   capd::krak::item &an_item = *new capd::krak::item(s);

   h.putlast(an_item);
//  putlast(an_item);
}

inline capd::krak::atom *capd::krak::list::operator[](int i)
{
   capd::krak::link *l=(*this)>>i;
   return (capd::krak::atom *)l;
}

inline void capd::krak::list::put(std::ostream &out)
{
   out.put('{');
   out.put('\n');
   if(next()!=NULL) next()->put(out);
   out.put('}');
   out.put('\n');
}


/************************************ record **********************************/

inline capd::krak::record::record(void): capd::krak::list(){}

inline int capd::krak::record::who(void)
{
   return RECORD;
}

inline capd::krak::atom *capd::krak::record::copy(void)
{
   capd::krak::record *l = new capd::krak::record;
   if(next()!=NULL) l->nxt=(capd::krak::link *)(next()->copy());
   l->bind();
   return l;
}

inline capd::krak::frstring capd::krak::record::descriptor(void)
{
   capd::krak::frstring s="A record which contains: {\n";
   if (next()!=NULL) s=s^next()->descriptor();
   s=s^"}\n";
   return s;
}

inline capd::krak::record &capd::krak::record::operator+(capd::krak::frstring s)
{
   capd::krak::hlink &h = *this;
   h+*new capd::krak::field(s);
   return *this;
}

inline void capd::krak::record::addfield(capd::krak::frstring &name, capd::krak::atom &val)
{
   capd::krak::field &nf = *new capd::krak::field;
   if (&nf==NULL) capd::krak::errorExit("No memory for a new field");
   nf.frstring::operator=(name);
   nf.value=&val;
   putlast(nf);
}

inline void capd::krak::record::addpointing_field(capd::krak::frstring &name, capd::krak::atom &val)
{
   capd::krak::field &nf = *new capd::krak::pointing_field;
   if (&nf==NULL) capd::krak::errorExit("No memory for a new field");
   nf.frstring::operator=(name);
   nf.value=&val;
   putlast(nf);
}

inline void capd::krak::record::addfield(capd::krak::frstring &name, capd::krak::frstring &val)
{
   capd::krak::field &nf = *new capd::krak::field;
   if (&nf==NULL) capd::krak::errorExit("No memory for a new field");
   nf.frstring::operator=(name);
   nf.value = new capd::krak::frstring(val);
   if(nf.value==NULL) capd::krak::errorExit("No memory for a new frstring value");
   putlast(nf);
}

inline void capd::krak::record::addfield(capd::krak::frstring &name, capd::krak::const_string &val)
{
   capd::krak::field &nf = *new capd::krak::field;
   if (&nf==NULL) capd::krak::errorExit("No memory for a new field");
   nf.frstring::operator=(name);
   nf.value = new capd::krak::const_string(val);
   if(nf.value==NULL) capd::krak::errorExit("No memory for a new frstring value");
   putlast(nf);
}

inline void capd::krak::record::put(std::ostream &out)
{
   out.put('[');
   out.put('\n');
   if(next()!=NULL) next()->put(out);
   out.put(']');
   out.put('\n');
}

  /******************************************************************************/

#endif // _CAPD_KRAK_ITEM_H_ 
