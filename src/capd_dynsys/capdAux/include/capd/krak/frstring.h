/////////////////////////////////////////////////////////////////////////////
/// @file frstring.h
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifndef _CAPD_KRAK_FRSTRING_H_ 
#define _CAPD_KRAK_FRSTRING_H_ 
#include "capd/krak/hardware.h"

//#include "capd/capd/myC.h"
#include "capd/krak/atom.h"

#define CEOF '\26'
#define TEOF "\26"
#define TERR "\26\26"
#undef strlen

#define INTERN_STR_LEN 20

namespace capd{
namespace krak{
   class Tab;
   class view_job;
}}

//----------------- frstring ---------------

namespace capd{
namespace krak{
class frstring : public capd::krak::atom {
   char *str;
public:
   int virtual who(void);

   frstring(void);                              //constructor
   frstring(const frstring &from);              //constructor
   frstring(const char *init_string);                 //constructor

   virtual ~frstring(void);                     //destructor
   char *string(void) const;
   char character(int n){ return str[n]; }
   virtual atom *copy();

   // frstring operator^(const frstring &second_string); //concatenation
   int operator+(frstring &second_string);      //addition
   int operator+(int an_int);                   //addition
   frstring &operator=(const frstring &second_string);//substitution
// frstring &operator=(char *c);                //substitution
   frstring &operator=(double a_double);        //substitution
   frstring operator++(void);                   //return the first item
   frstring operator++(int);                    //extract the first item
   frstring operator--(void);                   //return the last item
   int operator<=(frstring &second_string);     //lexicographical inequality
   int operator>=(frstring &second_string);     //lexicographical inequality
   int operator<(frstring &second_string);     //lexicographical inequality
   int operator>(frstring &second_string);     //lexicographical inequality
   int operator==(const frstring &second_string);     //identity
   int operator!=(const frstring &second_string);     //not identity
   int operator<=(capd::krak::atom &an_atom);               //lexicographical inequality
   int operator>=(capd::krak::atom &an_atom);               //lexicographical inequality
   int operator==(capd::krak::atom &an_atom);               //identity

   virtual void resize(int len);                //resize to "len" plus place for
                                                //teminating \0'and initialize
                                                //with empty frstring
   frstring operator[](int last);               //substring up to the "last" char
   frstring operator()(int first) const;              //substring from the "first" char
   frstring operator()(int first,int last) const;     //substring from "first" to "last"
   frstring rmqm(void);                         //remove question marks
   void insert(int pos,char c);                 //insert "c" at "pos"
   void remove(int pos);                        //delete the char at "pos"
   void split(int ncol);            //remove \r and \n and insert \n after each ncol characters
   frstring virtual descriptor(void);
   virtual void put(std::ostream &out);
   frstring extractFirstItem(void);            // the same as oparator++(int);
   frstring getFirstItem(void);                // the same as oparator++();
   int get(void);                              // frstring acting as stream

   friend frstring &operator>>(frstring &in, char &c);
   friend frstring &operator>>(frstring &in, int &n);
   friend frstring &operator>>(frstring &in, double &d);

   friend frstring &operator<<(frstring &out, char c);
   friend frstring &operator<<(frstring &out, int n);
   friend frstring &operator<<(frstring &out, double d);
   friend frstring &operator<<(frstring &out, frstring f);

   friend frstring operator^(const frstring &first_str,const frstring &second_string); //concatenation
   friend frstring operator^(const char *t,const frstring &s);                 //concatenation
   friend frstring operator^(const frstring &s,const char *t );                 //concatenation
   friend int operator+(int an_int, frstring &s);              //addition

   friend void getstring(std::istream &in, frstring &a_string, int len);
   friend void gettoken (std::istream &stream, frstring &a_string);
   friend void get_to_eol (std::istream &in, frstring &a_string);   // read line with eol
   friend void get_line (std::istream &in, frstring &a_string);     // read line up to eol
   friend std::ostream &operator<<(std::ostream &stream, frstring a_string);
   friend int frstrlen(const frstring &a_string);
   friend void getitem(std::istream &in, frstring &s);
   friend void getitem(frstring &in, frstring &s);
//   friend void open_and_warn(fstream &strm, frstring &name, int mode);
   friend frstring normalize (frstring &s);
   friend int string2int(frstring &s);
   friend double string2double(const frstring &s);         // convert string to double
   friend double string2double(const frstring &s, int &k); // as above but starting from position k.
                                               // k is updated.
   friend frstring double2string(double number);
   friend frstring byte2hex(unsigned char c);
   friend frstring halfbyte2hex(unsigned char c);
   friend frstring double2hex(double number);
   friend void skipto(std::istream &in, frstring &s);

   friend frstring deitem(frstring &s);
   friend frstring deitem_intitem(frstring &s);
   friend frstring &operator<<(frstring &out, capd::krak::Tab &t);
   friend view_job &operator<<(capd::krak::view_job &out, capd::krak::Tab &t);

   friend class item;
   friend class var;
   friend class field;
   friend class pointing_field;
   friend class flexstring;
   friend class colstring;
   friend class view_job;
};//end class frstring

 class flexstring : public frstring {
 public:
   char *extern_str;
   char intern_str[INTERN_STR_LEN];

   int virtual who(void);
   flexstring(void);                              //constructor
   flexstring(const frstring &from);              //constructor
   flexstring(const char *init_string);                 //constructor
// flexstring(double number);                     //constructor - removed
                                                  //use operator= instead
   flexstring &operator=(frstring &second_string);//substitution
   flexstring &operator=(double d);               //substitution
   virtual ~flexstring(void);                     //destructor
   virtual void resize(int len);                  //resize to "len" and initialize with empty frstring
 };//end class flexstring

 class colstring : public frstring{
   public:
   int fgcolor,bgcolor;
   colstring(void);
   colstring(int bgc,int fgc,const frstring &from);
   colstring(int bgc,int fgc,const char *init_string);
   colstring operator=(colstring second_string);
 };// end class colstring

 class const_string : public frstring{   //  designed specially for ed_rec_job
   public:
   const_string(const frstring &original): frstring(original){}
   int virtual who(void);
   virtual capd::krak::atom *copy();
 };//end class const_string

}} // the end of the namespace capd::krak

//###################### INLINE DEFINITIONS ####################################

inline char *capd::krak::frstring::string (void) const
{
   return str;
}

inline int capd::krak::frstring::who(void)
{
   return STRING;
}

inline capd::krak::frstring::~frstring(void)
{
   free(str);
}

inline capd::krak::atom *capd::krak::frstring::copy()
{
   return (capd::krak::atom *)new capd::krak::frstring(*this);
}

inline int capd::krak::frstring::operator!=(const capd::krak::frstring &second_string)
{
   return !(*this==second_string);
}

inline int capd::krak::frstring::operator<=(capd::krak::atom &an_atom)
{
   return *this<=*((capd::krak::frstring *)&an_atom);
}

inline int capd::krak::frstring::operator>=(capd::krak::atom &an_atom)
{
   return *this>=*((capd::krak::frstring *)&an_atom);
}

inline int capd::krak::frstring::operator==(capd::krak::atom &an_atom)
{
   return *this==*((capd::krak::frstring *)&an_atom);
}

inline capd::krak::frstring capd::krak::frstring::descriptor(void)
{
   return (capd::krak::frstring("String: ")^*this^capd::krak::frstring("\n"));
}

inline int capd::krak::flexstring::who(void)
{
   return STRING;
}

inline int capd::krak::const_string::who(void)
{
   return CONST_STRING;
}

inline capd::krak::atom *capd::krak::const_string::copy()
{
   return (capd::krak::atom *)new capd::krak::const_string(*this);
}

namespace capd{
namespace krak{
inline int frstrlen(const capd::krak::frstring &a_string)
{
   return strlen(a_string.str);
}

inline capd::krak::frstring deitem(capd::krak::frstring &s)
{
   if(s.str[0]=='{')
   {
      int l=strlen(s.str)-2;
      return s[l](1);
   }else{
      return s;
   }
}

inline capd::krak::frstring deitem_intitem(capd::krak::frstring &s)
{
   capd::krak::frstring t("0");
   s = capd::krak::deitem(s);
   if (s.str[0]<'0' || s.str[0]>'9') return t;
   else return s;
}

   capd::krak::frstring double2string(double number);
   capd::krak::frstring byte2hex(unsigned char c);
   capd::krak::frstring halfbyte2hex(unsigned char c);
   capd::krak::frstring double2hex(double number);
   void skipto(std::istream &in, capd::krak::frstring &s);

}} // the end of the namespace capd::krak


inline int capd::krak::frstring::get(void){
  if(*this =="") return EOF;
  int c=this->character(0);
  int len=strlen(str)-1;
  *this=this->operator()(1,len-1);
  return c;
}

#endif // _CAPD_KRAK_FRSTRING_H_ 
