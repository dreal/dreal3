/// @addtogroup krak
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file atom.cpp
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#include "capd/krak/atom.h"
//#include "capd/capd/myC.h"

#ifdef IS_THIS_FILE_REALLY_NECESSARY // It does not even compile! - PwP

namespace capd{
namespace krak{
capd::krak::atom &get(std::istream &in)
{
   atom *result;
   char *wsk;
   int ch=in.get();

   switch(ch)
   {
      case ' ':break;
      case '\n':break;
      case '\r':break;
      case -1: result=NULL; break;
      case '"':
         ostrstream s;
         while((ch=in.get())!='"')
         {
            if(ch==')') ch=in.get();
            s << ch;
         }
         s << ends;
         wsk=s.str();
         result = new string(wsk);
         delete wsk;
         break;
      case '[':
         capd::krak::record *rec = new capd::krak::record;
         while(in.peek()!=']')
         {
            capd::krak::field *f = new capd::krak::field;
            capd::krak::atom *a = get(in);
            if(a.who!=STRING)
               capd::krak::errorExit("Found type %d instead of string",a.who());
            string *s=f;
            *s=*(string *)a;
            if(in.get()!=':')
               capd::krak::errorExit("Colon missing");
            f->value=get(in);
            rec.putfirst(*f);
         }
         in.get();
         result=rec;
         break;
      case '{':

      default:
   }
   return *result;
}

#endif

/// @}
