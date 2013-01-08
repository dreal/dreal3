/// @addtogroup krak
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file frstring.cpp
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#include <cstring>
#include <memory>
#include "capd/krak/krakSetting.h"
#include "capd/krak/frame.h"
#include "capd/krak/frstring.h"
#include "capd/krak/color.h"
#include "capd/capd/minmax.h"

/*___________________________________________________________________________*/

capd::krak::frstring::frstring(const char *init_text)
{
   int le=1+strlen(init_text);
   str = (char *)malloc(le);
   if(str==NULL)
   {
      std::cout << "Not enough memory for frstring!\n";
      std::exit(0);
   }
   strcpy(str, init_text);
}

/*___________________________________________________________________________*/

capd::krak::frstring::frstring(void)
{
   str = (char *)malloc((long)1);
   if(str==NULL)
   {
      std::cout << "Not enough memory for frstring!\n";
      std::exit(0);
   }
   str[0]='\0';
}
/*___________________________________________________________________________*/


capd::krak::frstring::frstring(const capd::krak::frstring &original)
{
   str = (char *)malloc(1+strlen(original.str));
   if(str==NULL)
   {
      std::cout << "Not enough memory for frstring!\n";
      std::exit(0);
   }
   strcpy(str, original.str);
}

/*___________________________________________________________________________*/

capd::krak::frstring &capd::krak::frstring::operator=(double number)
{
   std::ostringstream bufor;
   bufor << number << '\0';
   *this = bufor.str().c_str();
   return *this;
}

/*___________________________________________________________________________*/

int capd::krak::frstring::operator+(capd::krak::frstring &second_string)
{
   return string2int(*this)+string2int(second_string);
}
/*___________________________________________________________________________*/

int capd::krak::frstring::operator+(int an_int)
{
   return string2int(*this)+an_int;
}

/*___________________________________________________________________________*/


capd::krak::frstring &capd::krak::frstring::operator=(const capd::krak::frstring &second_string)
{
   resize(frstrlen(second_string));
   strcpy(str, second_string.str);
   return *this;
}

/*___________________________________________________________________________*/
/*

capd::krak::frstring &capd::krak::frstring::operator=(char *c)
{
   resize(strlen(c));
   strcpy(str, c);
   return *this;
}
*/
/*___________________________________________________________________________*/
/*
capd::krak::frstring &capd::krak::frstring::operator=(int an_int)
{
   capd::krak::frstring s = capd::krak::frstring(an_int);
   resize(frstrlen(s));
   strcpy(str, s.str);
   return *this;
}
*/
/*___________________________________________________________________________*/

int capd::krak::frstring::operator==(const capd::krak::frstring &second_string)
{
   int i=0,res=1;
   do{
      if (str[i]!=second_string.str[i])
      {
         res=0;
         break;
      }
   }while(str[i++]!='\0');
   return res;
}

/*___________________________________________________________________________*/

int capd::krak::frstring::operator<=(capd::krak::frstring &second_string)
{
   int i=0,res=1;

   do{
      if (str[i]<second_string.str[i])
         break;
      if (str[i]>second_string.str[i])
      {
         res=0;
         break;
      }
   }while(str[i++]!='\0');
   return res;
}

/*___________________________________________________________________________*/

int capd::krak::frstring::operator>=(capd::krak::frstring &second_string)
{
   int i=0,res=1;

   do{
      if (str[i]>second_string.str[i])
         break;
      if (str[i]<second_string.str[i])
      {
         res=0;
         break;
      }
   }while(str[i++]!='\0');
   return res;
}

/*___________________________________________________________________________*/

int capd::krak::frstring::operator<(capd::krak::frstring &second_string)
{
   int i=0,res=0;

   do{
   if (str[i]<second_string.str[i])
   {
      res=1;
      break;
   }
   if (str[i]>second_string.str[i])
      break;
   }while(str[i++]!='\0');
   return res;
}

/*___________________________________________________________________________*/

int capd::krak::frstring::operator>(capd::krak::frstring &second_string)
{
   int i=0,res=0;

   do{
      if (str[i]>second_string.str[i])
      {
         res=1;
         break;
      }
      if (str[i]<second_string.str[i])
         break;
   }while(str[i++]!='\0');
   return res;
}

/*___________________________________________________________________________*/
capd::krak::frstring capd::krak::frstring::operator[](int last)
{
   int len=strlen(str);
   if (last>=len)
      last=len-1;
   capd::krak::frstring local;
   local.resize(last+1);
   int i;

   for(i=0;i<last+1;i++)
      local.str[i]=str[i];
   local.str[last+1]='\0';
   return local;
}

/*___________________________________________________________________________*/

capd::krak::frstring capd::krak::frstring::operator()(int first) const
{
   int len=strlen(str);
   capd::krak::frstring local;
   local.resize(len-first);
   int i;

   for(i=first;i<len;i++)
      local.str[i-first]=str[i];
   local.str[len-first]='\0';
   return local;
}

/*___________________________________________________________________________*/

capd::krak::frstring capd::krak::frstring::operator()(int first,int last) const
{
   int afterlast=last+1,n;
   if (afterlast>(n=strlen(str)) || last<0)
      afterlast=n;
   if (first>=n)
      first=n;
   capd::krak::frstring local;
   local.resize(afterlast-first);
   int i;

   for(i=first;i<afterlast;i++)
      local.str[i-first]=str[i];
   local.str[afterlast-first]='\0';
   return local;
}

/*___________________________________________________________________________*/

void capd::krak::frstring::insert(int pos,char c)                    //insert "c" at "pos"
{
   capd::krak::frstring newstr;
   int newlen=strlen(str)+1;
   newstr.resize(newlen);
   int i;
   for(i=0;i<pos;i++)
      newstr.str[i]=str[i];
   newstr.str[i++]=c;
   for(;i<newlen;i++)
      newstr.str[i]=str[i-1];
   newstr.str[i]='\0';
   //rootFrame << At(3,0) << "After insertion: " << newstr << " " << c << " " << pos;
   *this=newstr;
}


/*___________________________________________________________________________*/

void capd::krak::frstring::remove(int pos)                            //delete the char at "pos"
{
   capd::krak::frstring newstr;
   int newlen=strlen(str)-1;
   newstr.resize(newlen);
   int i;
   for(i=0;i<pos;i++)
      newstr.str[i]=str[i];
   for(;i<newlen;i++)
      newstr.str[i]=str[i+1];
   newstr.str[i]='\0';
   *this=newstr;
}


/*___________________________________________________________________________*/

void capd::krak::frstring::split(int ncol)
{
   char c;
   int i=0;
   while ((c=str[i++])!='\0')
      if(c=='\r' || c=='\n')
         str[i-1]=' ';
   i=0;
   while(str[i++]!='\0')
      if(i%ncol==0)
         insert(i++,'\n');
}

/*___________________________________________________________________________*/
namespace capd{
namespace krak{
   std::ostream &operator<<(std::ostream &stream, capd::krak::frstring a_string)
   {
      stream << a_string.str;
      return stream;
   }
}}

/*___________________________________________________________________________*/

void capd::krak::frstring::resize(int len)     // resizes the frstring to len characters plus \0
{
   delete str;
   str = new char[1+len];
   if(str==NULL)
   {
      std::cout << "Not enough memory for frstring!\n";
      std::exit(0);
   }
   str[0]=str[len]='\0';
}

/*___________________________________________________________________________*/

void capd::krak::frstring::put(std::ostream &out)
{
   int i,length=frstrlen(*this);
   char ch;
   out.put('"');
   for(i=0;i<length;i++)
   {
      if((ch=(this->str[i]))=='"')
         out.put('\\');
      out.put(ch);
   }
   out.put('"');
}

/*___________________________________________________________________________*/


namespace capd{
namespace krak{
capd::krak::frstring operator^(
      const capd::krak::frstring &first_string,
      const capd::krak::frstring &second_string
   )
{
   capd::krak::frstring internal_string;
   internal_string.resize(frstrlen(first_string)+frstrlen(second_string));

   strcpy(internal_string.str, first_string.str);
   strcat(internal_string.str, second_string.str);
   return internal_string;
}

/*___________________________________________________________________________*/

capd::krak::frstring operator^(const char *t,const capd::krak::frstring &s)
{
   capd::krak::frstring s1(t);
   s1=s1^s;
   return s1;
}

/*___________________________________________________________________________*/

capd::krak::frstring operator^(const capd::krak::frstring &s ,const char *t)
{
   capd::krak::frstring s1(t);
   s1=s^s1;
   return s1;
}

/*___________________________________________________________________________*/

int operator+(int an_int, capd::krak::frstring &s)
{
   return an_int+string2int(s);
}

/*___________________________________________________________________________*/


void getstring(std::istream &in, capd::krak::frstring &a_string, int len)
{
   int i;

   a_string.resize(1+len);
   for (i=0;i<len;i++)
   {
      int ch;
      ch=in.get();
      if(ch==EOF) break;
      a_string.str[i]=(char)ch;
   }
   a_string.str[i]='\0';
}

/*___________________________________________________________________________*/

void gettoken (std::istream &in, capd::krak::frstring &a_string)
    /* token is defined as a single non-alphanumeric character
       or a sequence of alphanumeric characters bounded by non-
       alphanumeric characters. The '_' sign is considered as
       an alphanumeric characterc. */
{
   std::streampos pos;
   int ch,len=1;

   while(' '==(ch=in.peek()) || ch=='\r' || ch=='\n' )
      ch=in.get();
   pos=in.tellg();
   ch=in.get();
   if( ch == EOF || ch == '\0' || ch == '\26')
   {
      a_string=TEOF;
   } else {
      if(isalnum(ch) || ch=='_')
         while(isalnum(ch=in.peek()) || ch=='_')
         {
            in.get();
            len++;
         }
   in.seekg(pos);
   getstring(in,a_string,len);
   }
}

/*___________________________________________________________________________*/


void get_to_eol (std::istream &in, capd::krak::frstring &a_string)
{
   std::streampos pos;
   int ch,len=0;

   if(in.peek() == EOF)
   {
      a_string=TEOF;
      return;
   }

   pos=in.tellg();
   do{
      ch=in.get();
      if (ch!=EOF)
         len++;
   }while(! (ch=='\n' || ch==EOF));
   in.seekg(pos);in.clear();
   getstring(in,a_string,len);
}

/*___________________________________________________________________________*/


void get_line(std::istream &in, capd::krak::frstring &a_string)
{
   std::streampos pos;
   int ch,len=0;

   if(in.peek() == EOF)
   {
      a_string=TEOF;
      return;
   }

   pos=in.tellg();
   do{
      ch=in.get();
      if (ch!=EOF && ch!='\n' && ch != '\r')
         len++;
   }while (!(ch=='\n' || ch==EOF || ch=='\r'));
   in.seekg(pos);in.clear();
   getstring(in,a_string,len);
}

/*___________________________________________________________________________*/


capd::krak::frstring normalize(capd::krak::frstring &in)
{
   std::istringstream ins(in.str);
   capd::krak::frstring token,out;
   out.resize(frstrlen(in));
   std::ostringstream outs(out.str);
   std::streampos pos;

   for(;;){
      gettoken(ins,token);
      if(token==TEOF || token=="")
         break;
      outs << token << " ";
   }
   outs.seekp(-1,std::ios::cur);
   pos=outs.tellp();
   //      outs << ends;
   return out(0,pos);
}


}} // the end of the namespace capd::krak

/*___________________________________________________________________________*/

capd::krak::frstring capd::krak::frstring::getFirstItem()
  /* This is the same as the prefix operator +
   It returns the first token of the frstring
   and leaves the original frstring unchanged */
{
   std::istringstream in(str);
   capd::krak::flexstring token;
   capd::krak::flexstring s("");
   int level=1,len=1,ch;
   std::streampos pos;

   while(' '==(ch=in.peek()) || ch=='\r' || ch=='\n' )
      ch=in.get();
   pos=in.tellg();
   gettoken(in,token);
   if(!(token=="{"))
   {
      s=token;
      } else {
      do{
         int ch;
         ch=in.get();
         if(ch!=EOF) len++;
         if(ch=='{') level++;
         if(ch=='}') level--;
      }while(level!=0 && !in.eof());

      if(level!=0)
      {
         s=capd::krak::frstring(TERR);
      } else {
         in.seekg(pos);
         in.clear();
         getstring(in,s,len);
      }
   }
   return s;
}

/*___________________________________________________________________________*/


capd::krak::frstring capd::krak::frstring::extractFirstItem(void)
  /* returns the first item of the frstring
   and removes it from the original frstring
       (the same as operator++(int) )*/
{
   std::istringstream in(str);
   capd::krak::frstring token;
   int ch,level=0,len;
   capd::krak::frstring s(""),t("");
   std::streampos pos;

   while(' '==(ch=in.peek()) || ch=='\r' || ch=='\n' )
      ch=in.get();
   pos=in.tellg();
   do{
      gettoken(in,token);
      if(token=="{") level++;
      if(token=="}") level--;
   }while(level!=0 && !in.eof());

   if(token == TEOF) return TEOF;

   len=in.tellg()-pos;
   in.seekg(pos);in.clear();
   getstring(in,s,len);

   if(level!=0)
   {
      s=TERR;
      } else {
      pos=in.tellg();
      do{
         ch=in.get();
         if(ch!=EOF)
            len++;
      }while(!in.eof());
      in.seekg(pos);in.clear();
      pos=in.tellg();
      getstring(in,t,len);
   }
   if (level==0)
   {
      resize(frstrlen(t));
      strcpy(str,t.str);
   }
   return s;
}

/*___________________________________________________________________________*/


capd::krak::frstring capd::krak::frstring::operator++(void)
  /* This is the prefix operator +
   It returns the first token of the frstring
   and leaves the original frstring unchanged */
{
   std::istringstream in(str);
   capd::krak::flexstring token;
   capd::krak::flexstring s("");
   int level=1,len=1,ch;
   std::streampos pos;

   while(' '==(ch=in.peek()) || ch=='\r' || ch=='\n' )
      ch=in.get();
   pos=in.tellg();
   gettoken(in,token);
   if(!(token=="{"))
   {
      s=token;
      } else {
      do{
         int ch;
         ch=in.get();
         if(ch!=EOF) len++;
         if(ch=='{') level++;
         if(ch=='}') level--;
      }while(level!=0 && !in.eof());

      if(level!=0)
      {
         s=frstring(TERR);
      } else {
         in.seekg(pos);
         in.clear();
         getstring(in,s,len);
      }
   }
   return s;
}

/*___________________________________________________________________________*/

capd::krak::frstring capd::krak::frstring::operator++(int)
  /* This is the suffix operator ++
   It returns the first token of the frstring
   and removes it from the original frstring */
{
   std::istringstream in(str);
   capd::krak::frstring token;
   int ch,level=0,len;
   capd::krak::frstring s(""),t("");
   std::streampos pos;

   while(' '==(ch=in.peek()) || ch=='\r' || ch=='\n' )
      ch=in.get();
   pos=in.tellg();
   do{
      gettoken(in,token);
      if(token=="{") level++;
      if(token=="}") level--;
   }while(level!=0 && !in.eof());

   if(token == TEOF) return TEOF;

   len=in.tellg()-pos;
   in.seekg(pos);in.clear();
   getstring(in,s,len);

   if(level!=0)
   {
      s=TERR;
      } else {
      pos=in.tellg();
      do{
         ch=in.get();
         if(ch!=EOF)
            len++;
      }while(!in.eof());
      in.seekg(pos);in.clear();
      pos=in.tellg();
      getstring(in,t,len);
   }
   if (level==0)
   {
      resize(frstrlen(t));
      strcpy(str,t.str);
   }
   return s;
}

/*___________________________________________________________________________*/

capd::krak::frstring capd::krak::frstring::operator--(void)
  /* This is the prefix operator --
   It returns the frstring with the first token removed
   and leaves the original frstring unchanged */
{
   std::istringstream in(str);
   capd::krak::frstring token;
   int ch,level=0,len=0;
   capd::krak::frstring s("");
   std::streampos pos;

   do{
      gettoken(in,token);
      if(token=="{") level++;
      if(token=="}") level--;
   }while(level!=0 && !in.eof());

   if(level!=0)
   {
      s=TERR;
   } else {
      while(' '==(ch=in.peek()) || ch=='\r' || ch=='\n' )
         ch=in.get();
      pos=in.tellg();
      do{
         ch=in.get();
         if(ch!=EOF)
            len++;
      }while(!in.eof());
      in.seekg(pos);in.clear();
      pos=in.tellg();
      getstring(in,s,len);
   }
   return s;
}

/*___________________________________________________________________________*/


capd::krak::frstring capd::krak::frstring::rmqm(void)
{
   std::istringstream in(str);
   int ch;
   char sch[]=" ";
   capd::krak::frstring s;

   s="";
   for(;;){
      ch=in.get();
      if(ch==EOF) break;
      sch[0]=(char)ch;
      if(ch!='?') s=s^sch;
   }
   return s;
}

/*___________________________________________________________________________*/
namespace capd{
namespace krak{
void getitem(capd::krak::frstring &in, frstring &s)
{
   std::istringstream instr(in.str);
   getitem(instr,s);
}

/*___________________________________________________________________________*/

void getitem(std::istream &in, frstring &s)
    /* An item is defined as a token except '{' and '}' or
       as a sequence of tokens embedded in "{' and '}'
       parentheses */
{
   capd::krak::frstring token;
   int level=1,len=1;
   std::streampos pos;

   gettoken(in,token);
   if(token!="{")
   {
      s=token;
   } else {
      pos=in.tellg();
      do{
         int ch;
         ch=in.get();
         if(ch!=EOF) len++;
         if(ch=='{') level++;
         if(ch=='}') level--;
      }while(level!=0 && !in.eof());

      if(level!=0)
      {
         s=TERR;
      } else {
         in.seekg(pos,std::ios::beg);
         in.seekg(-1,std::ios::cur);
         in.clear();
         getstring(in,s,len);
      }
   }
}

/*___________________________________________________________________________*/

double string2double(const capd::krak::frstring &s)
{
   int i=0,j=0,sign=1,k=0;
   double bas=1.0;
   char ch;

   for(;;){
      ch=s.str[k];
      if(ch=='\0') return 0.0;
      if(ch == '-' || ch == '.' || (ch >= '0' && ch <= '9')) break;
      k++;
   }

   if(ch == '-')
   {
      k++;
      sign=-1;
   }
   for(;;){
      ch=s.str[k++];
      if(ch < '0' || ch > '9')break;
      i=i*10+(ch-'0');
   }

   if(ch == '.')
   for(;;){
      ch=s.str[k++];
      if(ch < '0' || ch > '9')break;
      bas*=10;
      j=j*10+(ch-'0');
   }
   return sign*(i+(double)j/bas);
}

/*___________________________________________________________________________*/

double string2double(const capd::krak::frstring &s, int &k)
{
   int i=0,j=0,sign=1;
   double bas=1.0;
   char ch;

   k = capd::min(k,frstrlen(s));
   for(;;){
      ch=s.str[k];
      if(ch=='\0') return 0.0;
      if(ch == '-' || ch == '.' || (ch >= '0' && ch <= '9')) break;
      k++;
   }

   if(ch == '-')
   {
      k++;
      sign=-1;
   }
   for(;;){
      ch=s.str[k++];
      if(ch < '0' || ch > '9') break;
      i=i*10+(ch-'0');
   }

   if(ch == '.')
   for(;;){
      ch=s.str[k++];
      if(ch < '0' || ch > '9') break;
      bas*=10;
      j=j*10+(ch-'0');
   }
   return sign*(i+(double)j/bas);
}

/*___________________________________________________________________________*/


int string2int(capd::krak::frstring &s)
{
   std::istringstream in(s.str);
   int i,sign=1,ch;

   if((ch=in.peek())=='-' || ch=='+')
   {
      in.get();
      if(ch=='-') sign=-1;
   }
   if((ch=in.peek())<'0'|| ch>'9')
      i=0;
   else
      in >> i;
   return (sign>0 ? i : -i );
}

/*___________________________________________________________________________*/

/*
frstring double2string(double number)
{
   frstring s;
   ostrstream bufor;
   char *wsk;
   bufor << number << ends;
   wsk=bufor.str();
   s.str = new char[1+strlen(wsk)];
   if(s.str==NULL)
   {
      std::cout << "Not enough memory for frstring!\n";
      exit(0);
   }
   strcpy(s.str,wsk);
   delete(wsk);
   return s;
}
*/
/*___________________________________________________________________________*/

capd::krak::frstring double2string(double number)
{
   std::ostringstream bufor;
   bufor << number << std::ends;
   capd::krak::frstring s = bufor.str().c_str();
   return s;
}

/*___________________________________________________________________________*/

capd::krak::frstring halfbyte2hex(unsigned char c)
{
   capd::krak::frstring s;
   s.resize(1);
   if(c > 9)
      c+=(char)('A'-':');
   c += '0';
   s.str[0]=c;
   return s;
}

/*___________________________________________________________________________*/
capd::krak::frstring byte2hex(unsigned char c)
{
   return halfbyte2hex((unsigned char)(c >> 4)) ^ halfbyte2hex((unsigned char)(c & 0xf));
}

/*___________________________________________________________________________*/

capd::krak::frstring double2hex(double number)
{
   int i;
   long exponent;
   unsigned long b_exponent;
   capd::krak::frstring s,sign,exp_sign;
   unsigned char bytes[8],b0,b1;
   unsigned char *ptr=(unsigned char *)&number;

   for(i=0;i<8;i++)
   #ifdef INTEL
      bytes[i]=*(ptr+i);
   #else
      bytes[i]=*(ptr+7-i);
   #endif

   sign=((bytes[7] & 0x80) == 0 ? " " : "-");
   b_exponent = ((bytes[7] & 0x7f)*16)+ ((bytes[6] >> 4) & 0x0f);
   exponent=b_exponent-0x3ff;
   exp_sign="+";
   if(exponent<0)
   {
      exponent=-exponent;
      exp_sign="-";
   }
   bytes[6] &= 0x0f;
//       non_zero=bytes[6] & bytes[5] & bytes[4] &
//            bytes[3] & bytes[2] & bytes[1] & bytes[0];

   s = s ^ sign;

   if(b_exponent == 0 )
   {
      s=s ^ "0.";
   }else{
      s=s ^ "1.";
   }
   s = s ^ halfbyte2hex(bytes[6]) ^ byte2hex(bytes[5]) ^
   byte2hex(bytes[4]) ^ byte2hex(bytes[3]) ^ byte2hex(bytes[2]) ^
   byte2hex(bytes[1]) ^ byte2hex(bytes[0]);
   if(b_exponent == 0x7ff || b_exponent == 0)
   {
      if(b_exponent == 0)
      {
         s = s ^ "e ";
      }else{
         s = s ^ "nn";
      }
      b1 = (unsigned char)(b_exponent >> 8);
      b0 = (unsigned char)(b_exponent & 0xff);
   }else{
      s = s ^ "e" ^ exp_sign;
      b1 = (unsigned char)(exponent >> 8);
      b0 = (unsigned char)(exponent & 0xff);
   }
   s = s ^ halfbyte2hex(b1) ^ byte2hex(b0);
   return s;
}

/*___________________________________________________________________________*/

void skipto(std::istream &in, capd::krak::frstring &s)
{
   capd::krak::frstring it;

   do{
      getitem(in,it);
   }while (it!=s);
}
}} // the end of the namespace capd::krak

/*___________________________________________________________________________*/

capd::krak::flexstring::flexstring(const char *init_text)
{
   int len0=1+strlen(init_text);
   if(len0>INTERN_STR_LEN)
   {
      str=extern_str= new char[len0];
      if(extern_str==NULL)
      {
         std::cout << "Not enough memory for frstring!\n";
         std::exit(0);
      }
   } else {
      extern_str=NULL;str=intern_str;
   }
   strcpy(str, init_text);
}

/*___________________________________________________________________________*/

capd::krak::flexstring::flexstring(void)
{
   str = intern_str;
   extern_str=NULL;
   str[0]='\0';
}

/*___________________________________________________________________________*/

capd::krak::flexstring::flexstring(const capd::krak::frstring &original)
{
   int len0=1+frstrlen(original);
   if(len0>INTERN_STR_LEN)
   {
      str=extern_str= new char[len0];
      if(extern_str==NULL)
      {
         std::cout << "Not enough memory for frstring!\n";
         std::exit(0);
      }
   } else {
      extern_str=NULL;str=intern_str;
   }
   strcpy(str, original.str);
}

/*___________________________________________________________________________*/
/*
flexstring::flexstring(double number)
{
   ostrstream bufor;
   char *wsk;
   bufor << number << '\0';
   wsk=bufor.str();
   int len0=1+strlen(wsk);
   if(len0>INTERN_STR_LEN)
   {
      str=extern_str= new char[len0];
      if(extern_str==NULL)
      {
         std::cout << "Not enough memory for frstring!\n";
         exit(0);
      }
   } else {
      extern_str=NULL;str=intern_str;
   }
      strcpy(str, wsk);
   delete(wsk);
}
*/
/*___________________________________________________________________________*/

capd::krak::flexstring::~flexstring(void)                              //destructor
{
   if(extern_str!=NULL)
      delete extern_str;
   str=extern_str=NULL;
}

/*___________________________________________________________________________*/

void capd::krak::flexstring::resize(int len)     // resizes the frstring to len characters plus \0
{
   int len0=1+len;
   if(extern_str!=NULL)
      delete extern_str;
   if(len0>INTERN_STR_LEN)
   {
      str=extern_str= new char[len0];
      if(extern_str==NULL)
      {
         std::cout << "Not enough memory for frstring!\n";
         std::exit(0);
      }
   } else {
      extern_str=NULL;str=intern_str;
   }
   str[0]=str[len]='\0';
}

/*___________________________________________________________________________*/
capd::krak::flexstring &capd::krak::flexstring::operator=(double d)
{
   std::ostringstream bufor;
   const char *wsk;
   bufor << d << '\0';
   wsk=bufor.str().c_str();
   if(extern_str!=NULL)
      delete extern_str;
   int len0=1+strlen(wsk);
   if(len0>INTERN_STR_LEN)
   {
      str=extern_str= new char[len0];
      if(extern_str==NULL)
      {
         std::cout << "Not enough memory for frstring!\n";
         std::exit(0);
      }
   } else {
      extern_str=NULL;str=intern_str;
   }
   strcpy(str, wsk);
   return *this;
}

/*___________________________________________________________________________*/

capd::krak::flexstring &capd::krak::flexstring::operator=(capd::krak::frstring &second_string)
{
   resize(frstrlen(second_string));
   strcpy(str, second_string.str);
   return *this;
}

/*___________________________________________________________________________*/

capd::krak::colstring::colstring(void) : frstring()
{
   fgcolor=BLACK;
   bgcolor=WHITE;
}

/*___________________________________________________________________________*/

capd::krak::colstring::colstring(int bgc,int fgc,const char *init_string) : frstring(init_string)
{
   fgcolor=fgc;
   bgcolor=bgc;
}

/*___________________________________________________________________________*/
capd::krak::colstring::colstring(int bgc,int fgc,const capd::krak::frstring &original)
   : capd::krak::frstring(original)
{
   fgcolor=fgc;
   bgcolor=bgc;
}

/*
colstring::colstring(void)
{
   str = new char[1];
   if(str==NULL)
   {
      std::cout << "Not enough memory for frstring!\n";
      exit(0);
   }
   str[0]='\0';
   fgcolor=BLACK;
   bgcolor=WHITE;
}

colstring::colstring(int bgc,int fgc,char *init_string)
{
   str = new char[1+strlen(init_string)];
   if(str==NULL)
   {
      std::cout << "Not enough memory for frstring!\n";
      exit(0);
   }
   strcpy(str, init_string);
   fgcolor=fgc;
   bgcolor=bgc;
}

colstring::colstring(int bgc,int fgc,const frstring &original)
{
   str=new char[1+strlen(original.str)];
   if(str==NULL)
   {
      std::cout << "Not enough memory for frstring!\n";
      exit(0);
   }
   strcpy(str, original.str);
   fgcolor=fgc;
   bgcolor=bgc;
}
*/
/*___________________________________________________________________________*/

/*
colstring::colstring(const frstring &original)
{
   str=new char[1+strlen(original.str)];
   if(str==NULL)
   {
      std::cout << "Not enough memory for frstring!\n";
      exit(0);
   }
   strcpy(str, original.str);
   fgcolor=BLACK;
   bgcolor=WHITE;
}
*/
/*___________________________________________________________________________*/

capd::krak::colstring capd::krak::colstring::operator=(capd::krak::colstring second_colstring)
{
   resize(frstrlen(second_colstring));
   strcpy(str, second_colstring.str);
   bgcolor=second_colstring.bgcolor;
   fgcolor=second_colstring.fgcolor;
   return *this;
}

/*___________________________________________________________________________*/

namespace capd{
namespace krak{
capd::krak::frstring &operator>>(capd::krak::frstring &in, char &c)
{
   c=in.str[0];
   if(c != '\0')
      in=in(1);
   return in;
}

/*___________________________________________________________________________*/

capd::krak::frstring &operator>>(capd::krak::frstring &in, int &n)
{
   std::istringstream inp(in.string());
   inp >> n;
   in=in(inp.tellg());
   return in;
}

/*

frstring &operator>>(frstring &in, int &n)
{
   int i=0,j=0,sign=1,k=0;
   double bas=1.0;
   char ch;

   while((ch=in.str[k++]) == ' ' || ch == '\n' || ch == '\r');
   if(ch == '-' || ch == '+' || (ch >= '0' && ch <= '9'))
   {
      if(ch == '-')
      {
         ch=in.str[k++];
         sign=-1;
      }
      if(ch == '+')
      {
         ch=in.str[k++];
      }
      for(;;){
         if(ch < '0' || ch > '9')break;
         i=i*10+(ch-'0');
         ch=in.str[k++];
      }
   }
   n=(sign>0 ? i : -i);
   in=in(k-1);
   return in;
}
*/

/*___________________________________________________________________________*/

capd::krak::frstring &operator>>(capd::krak::frstring &in, double &d)
{
   std::istringstream inp(in.string());
   inp >> d;
   in=in(inp.tellg());
   return in;
}

/*
frstring &operator>>(frstring &in, double &d)
{
   int i=0,j=0,sign=1,k=0;
   double bas=1.0;
   char ch;

   while((ch=in.str[k++]) == ' ' || ch == '\n' || ch == '\r');
   if(ch == '-' || ch == '.' || (ch >= '0' && ch <= '9'))
   {
      if(ch == '-'){ch=in.str[k++];sign=-1;};
      for(;;){
         if(ch < '0' || ch > '9')break;
         i=i*10+(ch-'0');
         ch=in.str[k++];
      }
      if(ch == '.')
      {
         ch=in.str[k++];
         for(;;){
            if(ch < '0' || ch > '9')break;
            bas*=10;
            j=j*10+(ch-'0');
            ch=in.str[k++];
         }
      }
   }
   d=sign*(i+(double)j/bas);
   in=in(k-1);
   return in;
}
*/
/*___________________________________________________________________________*/

capd::krak::frstring &operator<<(capd::krak::frstring &out, char c)
{
   char cc[2];
   cc[0]=c;
   cc[1]=0;
   out=out^cc;
   return out;
}

/*___________________________________________________________________________*/

capd::krak::frstring &operator<<(capd::krak::frstring &out, int n)
{
   capd::krak::frstring f;
   f=n;
   out=out^f;
   return out;
}

/*___________________________________________________________________________*/

capd::krak::frstring &operator<<(capd::krak::frstring &out, double d)
{
   capd::krak::frstring f;
   f=d;
   out=out^f;
   return out;
}

/*___________________________________________________________________________*/

capd::krak::frstring &operator<<(capd::krak::frstring &out, capd::krak::frstring f)
{
   out=out^f;
   return out;
}

}} // the end of the namespace capd::krak

/*___________________________________________________________________________*/

/// @}
