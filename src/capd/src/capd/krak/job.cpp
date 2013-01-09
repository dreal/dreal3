/// @addtogroup krak
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file job.cpp
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#include "capd/krak/job.h"
#include "capd/krak/frstring.h"
namespace capd{
namespace krak{
   capd::krak::job *job::runningJob=NULL;
   capd::krak::job *job::previousJob=NULL;
   capd::krak::job *job::requestedJob=NULL;
   capd::krak::job *job::rootJob=new job;
   int capd::krak::job::desktopColor=WHITE;
   capd::krak::frstring job::message="";
}}

int no_launched_jobs=0;

//############################### class job ###################################

/******************************************************************************/

capd::krak::job::job(void) :
   jobfrm(0,0,0,0,WHITE,BLACK,0,0), status(sleeping), visible(1), parent(NULL),
   immortal(0),request_repaint(1)
{}

capd::krak::job *capd::krak::job::userSelectedJob(capd::krak::UserMove &um)
{
   capd::krak::job *userJob=capd::krak::job::runningJob;
   switch(um.key)
   {
      case TabKey: if((rootJob->children).len()>1)
         userJob=(job *)((capd::krak::job::rootJob->children).last());
         (capd::krak::job::rootJob->children).promote(*userJob);
         um.key=NO_KEY;
         break;
      case ButtonKey:
         userJob=capd::krak::job::rootJob->selectJob(um);
         break;
      default:;
   }
   if(userJob==NULL) userJob=capd::krak::job::runningJob;
   return userJob;
}

/******************************************************************************/

/* The following routine recursively reviews all jobs and their children
   and promotes the first job enclosing the user selected point, as well as
   all its parents */

capd::krak::job *capd::krak::job::selectJob(capd::krak::UserMove &um)
{
   capd::krak::job *j = (capd::krak::job *)(children.next()),*fj=NULL;
   while(j!=NULL)
   {
      if((fj=j->selectJob(um))!=NULL) break;
      j=(capd::krak::job *)(j->next());
   }
   if(fj!=NULL)
   {
      children.promote(*j);
   } else {
      if(jobfrm.isInside(um.pxl)) fj=this;
   }
   return fj;
}

/******************************************************************************/

int capd::krak::job::exists(capd::krak::job *jobPt)
{
   if(jobPt==NULL) return 0;
   if (this==jobPt) return 1;
   capd::krak::job *j=(capd::krak::job *)(children.next());
   if(j!=NULL && j->exists(jobPt)) return 1;
   if(next()==NULL) return 0;
   else return ((capd::krak::job*)next())->exists(jobPt);
}

/******************************************************************************/

int capd::krak::job::exists(int a_type)
{
   if (a_type==type() ) return 1;
   capd::krak::job *j=(capd::krak::job *)(children.next());
   if(j!=NULL && j->exists(a_type)) return 1;
   if(next()==NULL) return 0;
   else return ((capd::krak::job*)next())->exists(a_type);
}

/******************************************************************************/

void capd::krak::job::mainLoop(void)
{
   capd::krak::UserMove um;
   um.key=NO_KEY;

   capd::krak::rootFrame.Clear();
   capd::krak::job::rootJob->repaint();
   if(capd::krak::job::runningJob == NULL) capd::krak::job::runningJob = capd::krak::job::requestedJob;

   while (capd::krak::job::runningJob!=NULL)
   {
      capd::krak::job *new_runningJob=NULL;
      Status s;
      s=Status(capd::krak::job::runningJob->process(um));
      previousJob = capd::krak::job::runningJob;
      if (message=="finish") break;
      switch(s)
      {
         case sleeping:
            capd::krak::errorExit("Encountered a sleeping job in the main loop");
            break;
         case finished:
            new_runningJob = capd::krak::job::runningJob->parent;
            capd::krak::job::runningJob->terminate();
            if(new_runningJob == capd::krak::job::rootJob || new_runningJob==NULL)
            {
               new_runningJob=
                  (capd::krak::job *)(capd::krak::job::rootJob->children.first());
               while(new_runningJob!=NULL && new_runningJob->status==sleeping)
                  new_runningJob=(capd::krak::job *)(new_runningJob->next());
            }
            um.key=NO_KEY;
            break;
         case running:
         default:
            if(capd::krak::job::requestedJob!=NULL &&
               capd::krak::job::rootJob->exists(capd::krak::job::requestedJob))
            {
               new_runningJob = capd::krak::job::requestedJob;
               capd::krak::job::requestedJob=NULL;
               um.key=NO_KEY;
            } else {
               capd::krak::Frame fifofrm = capd::krak::Frame(
                  capd::krak::job::runningJob->jobfrm,
                  capd::krak::At(capd::krak::job::runningJob->jobfrm.lRow-1,
                  capd::krak::job::runningJob->jobfrm.lCol-1),
                  capd::krak::At(capd::krak::job::runningJob->jobfrm.lRow-1,
                  capd::krak::job::runningJob->jobfrm.lCol-1),WHITE,BLACK);
               capd::krak::Rct r;
               capd::krak::SetRct(&r,fifofrm.lti,fifofrm.ltj,fifofrm.rbi,fifofrm.rbj);
               capd::krak::WaitUserMove(um,r,BLACK,WHITE,0.3);
               new_runningJob = capd::krak::job::userSelectedJob(um);
            }
      } // end of switch
//rootFrame << At(0,0) << new_runningJob->order_no << " order_no"; waitBt;
      if(capd::krak::job::runningJob!=new_runningJob)
      {
         capd::krak::job::runningJob = new_runningJob;
//      rootFrame.Clear();  // clear move to repaint to speed up things!
         capd::krak::job::rootJob->repaint();
      }
   } // end of while
}

/******************************************************************************/

void capd::krak::job::launch(capd::krak::job *prnt)
// unless there is some future for sleeping jobs which already have run
// the launch and terminate functions could be incorporated in con(de)structors.
{
   if(status==sleeping)
   {
      order_no=no_launched_jobs++;
      (prnt->children).putfirst(*this);
      capd::krak::job::requestedJob = this;
      parent=prnt;
      status=running;
   } else {
      capd::krak::rootFrame << At(0,0);
      capd::krak::rootFrame << "Attempt to launch a non-sleeping job. Status= " << status;
   }
}

/******************************************************************************/

void capd::krak::job::terminate(void)
{
   jobfrm.Clear(desktopColor);
   jobfrm.Bound(desktopColor);
   if(immortal) status=sleeping;
      capd::krak::job *l=(capd::krak::job *)(children.last()),*lprev;
   if(l!=NULL)
   while (l!=(capd::krak::link *)&children)
   {
      lprev=(capd::krak::job *)(l->prev());
      l->terminate();
      l=lprev;
   }
   if(this != capd::krak::job::rootJob)
   {
      if(status!=sleeping)
         destroy();
      else
         withdraw();
   }
}

/******************************************************************************/

void capd::krak::job::repaint(void)
{
   if(visible){
//      jobfrm.Clear();
      own_repaint();
   }
   capd::krak::job *l=(capd::krak::job *)(children.last());
   if(l!=NULL)
      while (l!=(capd::krak::link *)&children)
      {
         if(l->status!=sleeping) l->repaint();
         l=(capd::krak::job *)(l->prev());
      }
}

/******************************************************************************/

int capd::krak::confirm(capd::krak::Frame &jobfrm, const char *prompt, const char *yes, const char *no)
{
   int answer=-1,mid=jobfrm.lCol/2;
   capd::krak::Frame yesFrm,noFrm;

   jobfrm.bgColor=ORANGERED;
   jobfrm.fgColor=BLACK;
   jobfrm.Clear();
   yesFrm = capd::krak::Frame(jobfrm,capd::krak::At(6,mid-6),capd::krak::At(7,mid-1),DARKBLUE,WHITE);
   noFrm = capd::krak::Frame(jobfrm,capd::krak::At(6,mid+1),capd::krak::At(7,mid+6),DARKBLUE,WHITE);
   yesFrm.Clear();
   noFrm.Clear();
   jobfrm << capd::krak::At(2,mid-6) << prompt;
   yesFrm << capd::krak::At(0,0) << yes;
   noFrm << capd::krak::At(0,0) << no;

   for(;;){
      capd::krak::UserMove um;
      capd::krak::WaitUserMove(um);
      switch(um.key)
      {
         case 't':  answer=1;break;
         case 'n':  answer=0;break;
         case ButtonKey:
            if(yesFrm.isInside(um.pxl)) answer=1;
            if(noFrm.isInside(um.pxl)) answer=0;break;
         default:;
      }
      if(answer>=0) break;
   }

   jobfrm.bgColor=WHITE;
   jobfrm.Clear();
   return answer;
}

//############################### class basic_job ##############################

/******************************************************************************/
int capd::krak::basic_job::process(capd::krak::UserMove &um)
{
   if (um.key==EscKey || (um.key==ButtonKey && stopfrm.isInside(um.pxl)))
   {
      status=finished;
      return status;
   }
   if(help!=NULL)
   if(um.key==F1Key || (um.key==ButtonKey && helpfrm.isInside(um.pxl)))
   {
      help->launch();help->own_repaint();
      requestedJob=help;
      um.key=NO_KEY;
      return running;
   }

   if(um.key==DragKey && titlefrm.isInside(um.pxl))
   {
      int i=um.pxl.i,j=um.pxl.j, rlti=jobfrm.lti,rltj=jobfrm.ltj,rrbi=jobfrm.rbi,rrbj=jobfrm.rbj;
      capd::krak::Pxl p;
      for(;;){
         if(!capd::krak::Button()) break;
         capd::krak::GetMouse(&p);
         rlti=jobfrm.lti+(p.i-i);
         rltj=jobfrm.ltj+(p.j-j);
         rrbi=jobfrm.rbi+(p.i-i);
         rrbj=jobfrm.rbj+(p.j-j);
         capd::krak::rootFrame.Clear();
         capd::krak::job::rootJob->repaint();
         capd::krak::SetFgCol(BLACK);
         capd::krak::Rctngl(rlti,rltj,rrbi,rrbj);
      }
      jobfrm.lti=rlti;jobfrm.ltj=rltj;jobfrm.rbi=rrbi;jobfrm.rbj=rrbj;
      furnish();
      capd::krak::rootFrame.Clear();
      capd::krak::job::rootJob->repaint();
   }
   return status;
}

/******************************************************************************/

void capd::krak::basic_job::own_repaint(void)
{
   int boundColor=(this==capd::krak::job::runningJob ? CYAN : BLACK);
   jobfrm.Clear();
   titlefrm.Clear();
   stopfrm.Clear();
   titlefrm.Bound();
   stopfrm.Bound();
   if(help!=NULL) helpfrm.Bound();
//    jobfrm.Bound(boundColor);
   jobfrm.Bound();
   capd::krak::SetFgCol(boundColor);
   capd::krak::Rctngl(jobfrm.lti+1,jobfrm.ltj+1,jobfrm.rbi-1,jobfrm.rbj-1);
   capd::krak::Rctngl(jobfrm.lti+2,jobfrm.ltj+2,jobfrm.rbi-2,jobfrm.rbj-2);

   titlefrm << capd::krak::At(0,0);
   titlefrm << title;
   titlefrm << " (";
   titlefrm << order_no;
   titlefrm << ")";

   stopfrm << capd::krak::At(0,0) << "x";
   if(help!=NULL) helpfrm << capd::krak::At(0,0) << "?";
}

//############################### class sel_job ##############################

/******************************************************************************/

void capd::krak::sel_job::launch(capd::krak::job *prnt)
{
   length=a_list.len();
   lastshown = capd::min(length,maxshown)-1;
   capd::krak::job::launch(prnt);
//rootFrame << At(0,0) << "Launched sel_job no " << order_no;waitBt();
}

/******************************************************************************/

void capd::krak::sel_job::own_repaint(void)
{
   capd::krak::link *l = (a_list)>>firstshown;
   int i=0;

//    if(search_permitted || previousJob!=runningJob)
   basic_job::own_repaint();
   window.Clear();
//  upFrm.Bound();
//  downFrm.Bound();
   upFrm << capd::krak::At(upFrm.lRow,1) << "A";
   downFrm << capd::krak::At(0,1) << "V";
   if(search_permitted)
      titlefrm << capd::krak::At(0,titlefrm.lCol-7) << capd::krak::colstring(WHITE,BLACK,search_token);
   titlefrm << capd::krak::At(0,titlefrm.lCol-7) << capd::krak::colstring(WHITE,BLACK,search_token);
   while((l=l->next())!=NULL && i<=lastshown)
   {
      int selected=(firstshown+i==selector);
      window << capd::krak::At(i,0) <<
         capd::krak::colstring((selected ? window.fgColor : window.bgColor),
         (selected ? window.bgColor : window.fgColor), *(capd::krak::item *)l);
      i++;
   }
}

#  define TOP rootFrame << At(0,0)

/******************************************************************************/

int capd::krak::sel_job::MakeSelection(capd::krak::UserMove &um)
{
   int selection=selector,noselection=-1000;
   int k=(um.key>=97 ? um.key-32 : um.key);
   if(search_permitted && ((k>='A' && k <= 'Z') || k==BSKey) )
   {
      int i=0,found=0,length=strlen(search_token.string());
      capd::krak::link *l = &a_list;
      if(k==BSKey)
      {
         if(length>0) search_token.remove(length-1);
      } else {
         if(search_token_length<8) search_token.insert(length,k);
      }
      while(NULL!=(l=l->next()))
      {
         capd::krak::flexstring s;
         int check=0;
         switch(l->who())
         {
            case STRING: s=*(capd::krak::frstring *)l;
               check=1;
               break;
            case ITEM:
               s=*(capd::krak::item *)l;
               check=1;
               break;
            case FIELD:
               s=*(capd::krak::field *)l;
               check=1;
               break;
            default:;
         }

         if(check && s>=search_token) {found=1;break;};
         i++;
      }
      selection=(found ? i : noselection);
   } else {
      search_token="";
      switch(um.key)
      {
         case UpKey: --selection;break;
         case DownKey: ++selection;break;
         case PgUpKey:selection-=(maxshown-1);break;
         case PgDnKey:selection+=(maxshown-1);break;
         case CRKey: break;
         case ButtonKey: selection=window.getRow(um.pxl)+firstshown;break;
         default: selection=noselection;
      }
   }
   if(selection==noselection)
   {
      selection=-1;
   } else {
      if(selection>=length) selection=length-1;
      if(selection<0) selection=0;
   }
   int result=((selection==selector) && (um.key==ButtonKey || um.key==CRKey));
   if(selection>=0)
   {
      selector=selection;
      if(selection<firstshown)
      {
         firstshown=selection;
         lastshown=firstshown+maxshown-1;
      }
      if(selection>lastshown)
      {
         lastshown=selection;
         firstshown=lastshown-maxshown+1;
      }
   }
   return result;
}

/******************************************************************************/

void capd::krak::sel_job::testUpDown(capd::krak::UserMove &um)
{
   if(um.key==ButtonKey)
   {
      if(!window.isInside(um.pxl))
      {
         if(upFrm.isInside(um.pxl)) um.key=UpKey;
         if(downFrm.isInside(um.pxl)) um.key=DownKey;
      }
   }
}

/******************************************************************************/

int capd::krak::sel_job::process(capd::krak::UserMove &um)
{
   Status s;

   if((s=Status(basic_job::process(um)))==finished)
   {
      return s;
   } else {
      testUpDown(um);
      if(um.key==ButtonKey && !window.isInside(um.pxl)) return status;
      if(MakeSelection(um))
      {
         status=finished;
         return status;
      }
      repaint();
      return status;
   }
}

//############################### class view_job ##############################

/******************************************************************************/

int capd::krak::view_job::process(capd::krak::UserMove &um)
{
   Status s;

   if(!noStopFrm && ((s=Status(basic_job::process(um)))==finished))
   {
      return s;
   } else {
      testUpDown(um);
      if(um.key==ButtonKey && !window.isInside(um.pxl)) return status;
      MakeSelection(um);
      repaint();
      return status;
   }
}

/******************************************************************************/

void capd::krak::view_job::own_repaint(void)
{
   capd::krak::link *l=(a_list)>>firstshown;
   int i=0;

   capd::krak::basic_job::own_repaint();
   window.Clear();
   upFrm << capd::krak::At(upFrm.lRow,1) << "A";
   downFrm << capd::krak::At(0,1) << "V";
   while((l=l->next())!=NULL && i<=lastshown)
   {
//      int selected=(firstshown+i==selector);
      window << At(i,0) << *(item *)l;
      i++;
   }
   request_repaint=0;
}

/******************************************************************************/

int pos=0;

/******************************************************************************/
// This routine adds the requested string to the buffer.
// Then it searches through the buffer for \n characters and adds
// each line found as a seperate entry to the list a_list.
//  view_job  &operator<<(view_job &v,char *s)
namespace capd{
namespace krak{
capd::krak::view_job  &operator<<(capd::krak::view_job &v, capd::krak::frstring f)
{
   char *s=f.string();
   v.makeVisible();
   if(!v.opened)
      capd::krak::errorExit("Access to %s is not open",(v.title).string());
   int found;
   char ch;
//    int j,nblanks=field_width-strlen(s);

   v.window << s;
   v.bufor=v.bufor^s;
   v.pos=frstrlen(v.bufor);

//    for(j=0;j<nblanks;j++) bufor=bufor^" ";
   v.field_width=0;
   do{
      found=0;
      int position=0;
      while((ch=v.bufor.character(position++))!='\0') if(ch=='\n'){found=1; break;}
      if(found)
      {
         v.a_list+v.bufor[position-1];
         if(v.with_file) v.job_file << v.bufor[position-1];
         v.lastshown=v.selector=v.length++;
         if(v.lastshown>v.maxshown) v.request_repaint=1;
         v.firstshown=max(0,v.lastshown-v.maxshown+1);
         v.bufor=v.bufor(position);
         v.pos=frstrlen(v.bufor);
      }
   }while(!(found==0));

   if(v.active && v.request_repaint)
   {
      v.own_repaint();
      v.requestedJob=&v;
   }
   return v;
}

/******************************************************************************/

capd::krak::view_job  &operator<<(capd::krak::view_job &v, capd::krak::Tab &t)
{
   int nblanks=t.col-v.pos;
   if(nblanks>0)
   {
//      char *blanks=new char(nblanks+1);
      capd::krak::frstring blanks;
      blanks.resize(nblanks);
      for(int i=0;i<nblanks;i++) blanks.str[i]=' ';
      blanks.str[nblanks]='\0';
      v.window << blanks;
      v.bufor=v.bufor^blanks;
      v.pos+=nblanks;
   }
   return v;
}

}} // the end of the namespace capd::krak

/******************************************************************************/

void capd::krak::view_job::open(int read)
{
   a_list.empty();
   search_token_length=selector=firstshown=length=0;
   lastshown = capd::min(length,maxshown)-1;
   window << capd::krak::At(0,0);
   if(with_file)
   {
      if(read)
      {
         capd::krak::frstring one_line;
         job_file.open(filename.string(),std::ios::in);
         for(;;){
            get_to_eol(job_file,one_line);
            if(one_line=="")break;
            a_list+one_line;
         }
      } else {
         job_file.open(filename.string(),std::ios::out);
      }
   }
   opened=1;
   if(status!=running) launch();
}

//############################### class menu_job ##############################

int capd::krak::menu_job::process(capd::krak::UserMove &um)
{
   Status s;

   if((!noStopFrm && (s=Status(basic_job::process(um)))==finished))
   {
      return s;
   } else {
      if(um.key==F1Key || (um.key==ButtonKey && helpfrm.isInside(um.pxl)))
      {
         help->launch();
         help->own_repaint();
         capd::krak::job::requestedJob=help;
         um.key=NO_KEY;
         return running;
      }
      testUpDown(um);
      if(um.key==ButtonKey && !window.isInside(um.pxl)) return status;
      if(MakeSelection(um) || (um.key>='a' && um.key<='z' && selector<length && selector>=0))
      {
         capd::krak::flexstring control=*((capd::krak::item *)(void *)(a_list[selector+1]));
         (*executor)(control);
      }
      repaint();
      search_token="";
      return status;
   }
}

//############################### class del_ins_job ##############################

/******************************************************************************/

void capd::krak::del_ins_job::own_repaint(void)
{
   capd::krak::sel_job::own_repaint();
   insfrm << capd::krak::At(0,0) << "Ins";
   delfrm << capd::krak::At(0,0) << "Del";
   insfrm.Bound();
   delfrm.Bound();
   titlefrm << capd::krak::At(0,titlefrm.lCol-7) << capd::krak::colstring(WHITE,BLACK,search_token);
}

/******************************************************************************/

int capd::krak::del_ins_job::process(capd::krak::UserMove &um)
{
   Status s;
   int mid=window.lRow/2;

   if((s=Status(basic_job::process(um)))==finished)
   {
      return s;
   } else {
//    int l=a_list.len()-1;
      enum frame_type{none,sel,ins,del};
      frame_type ft=none;

      if(um.key==ButtonKey && !jobfrm.isInside(um.pxl)) return status;
      testUpDown(um);
      switch(um.key)
      {
         case ButtonKey:
            if(window.isInside(um.pxl)) ft=sel;
            if(delfrm.isInside(um.pxl)) ft=del;
            if(insfrm.isInside(um.pxl)) ft=ins;
            break;
         case PgUpKey:
         case PgDnKey:
         case UpKey:
         case DownKey: ft=sel;break;
         case InsKey: ft=ins; break;
         case DelKey: ft=del; break;
         default: ft=sel;
      }

      capd::krak::frstring newitem_name;
      capd::krak::Frame lfrm(window,capd::krak::At(mid-5,1), capd::krak::At(mid+5,window.lCol-1));
      switch(ft)
      {
         case sel:
            MakeSelection(um);
//   int selection=GetSelection(window,um,selector,a_list.len()-1);
//   if(selection>=0) selector=selection;
            break;
         case del:
            if(confirm(lfrm,"Delete?","Yes","No"))
            {
               length--;
               (*(a_list>>(selector+1))).destroy();
               selector=0;
               lastshown = capd::min(length,maxshown)-1;
            }
            own_repaint();
            break;
         case ins:
            length++;
//    jobfrm >> At(jobfrm.lRow-3,6) >> BgColor(WHITE) >> FgColor(BLACK) >> newitem_name;
            jobfrm.Edit(At(jobfrm.lRow-2,10),20,newitem_name);
//rootFrame << At(5,0) << "strlen=" << (int)strlen(newitem_name.str);
            if(!(newitem_name==""))
            {
               (a_list)+newitem_name;
               a_list.sort();
               selector=0;
//             if(selector<firstshown){firstshown=selector;lastshown=firstshown+maxshown-1;};
//           if(selector>lastshown){lastshown=selector;firstshown=lastshown-maxshown+1;};
               firstshown=0;
               lastshown = capd::min(length,maxshown)-1;
            }
         break;
         default: break;
      }
   }
   repaint();
   return status;
}

//############################### class ed_rec_job #############################

/******************************************************************************/

void capd::krak::ed_rec_job::own_repaint(void)
{
   capd::krak::field *l = (capd::krak::field *)((a_list)>>firstshown);
   int i=0;

   capd::krak::basic_job::own_repaint();
   window.Clear();
   editfrm.Clear();
   titlefrm << capd::krak::At(0,titlefrm.lCol-7) << capd::krak::colstring(WHITE,BLACK,search_token);
   upFrm << capd::krak::At(upFrm.lRow,1) << "A";
   downFrm << capd::krak::At(0,1) << "V";

   while((l=(capd::krak::field *)(l->next()))!=NULL && i<=lastshown)
   {
      capd::krak::colstring cs;
      int selected=(firstshown+i==selector);
      capd::krak::field &f=*l;
      int dimmed=PINE;
      int type=(~f==NULL ? NONE : (~f)->who());
      int fgc=(type==CONST_STRING ? dimmed : window.fgColor);
      int bgc=window.bgColor;
      window << capd::krak::At(i,0) <<
         capd::krak::colstring((selected ? fgc : bgc),(selected ? bgc : fgc),f);
      capd::krak::frstring stype;
      stype = capd::krak::double2string(type);

      switch(type)
      {
         case CONST_STRING: cs = capd::krak::colstring(window.bgColor,dimmed,!f);break;
         case STRING: cs = capd::krak::colstring(window.bgColor,window.fgColor,!f);break;
//   case STRING: cs=colstring(window.bgColor,PINE,!f);break;
         case LIST: cs = capd::krak::colstring(window.bgColor,BLUE,"LIST");break;
         case RECORD: cs = capd::krak::colstring(window.bgColor,BLUE,"RECORD");break;
         case NONE: cs = capd::krak::colstring(window.bgColor,RED,"NULL");break;
         default: cs = capd::krak::colstring(window.bgColor,RED,"UNKNOWN: "^stype);break;;
      }
      editfrm << capd::krak::At(i,0) << cs;
      i++;
   }
}

int capd::krak::ed_rec_job::process(capd::krak::UserMove &um)
{
   Status s;

   if((s=Status(capd::krak::basic_job::process(um)))==finished)
   {
      return s;
   } else {
      testUpDown(um);
      if(um.key==ButtonKey && !window.isInside(um.pxl)) return status;
      if(MakeSelection(um))
      {
         capd::krak::field &f=(*(capd::krak::field *)(void *)((a_list)[1+selector]));
         if(~f!=NULL)
         {
            int type=(~f)->who();
            capd::krak::del_ins_job *list_job;
            capd::krak::ed_rec_job *rec_job;
            switch(type)
            {
               case STRING:
                  editfrm.Edit(At(selector-firstshown,0),edit_field_length,!f);
                  break;
               case LIST:
                  {
                  capd::krak::Frame lfrm(jobfrm,
                     capd::krak::At(1,1),
                     capd::krak::At(jobfrm.lRow,jobfrm.lCol),
                     jobfrm.bgColor,jobfrm.fgColor);
                  list_job = new capd::krak::del_ins_job(f,*(list *)~f,lfrm);
                  list_job->launch(this);
                  }
                  break;
               case RECORD:
                  {
                  capd::krak::Frame lfrm(jobfrm,
                     capd::krak::At(2,2),
                     capd::krak::At(jobfrm.lRow+2,jobfrm.lCol+2),
                     jobfrm.bgColor,jobfrm.fgColor);
                  rec_job=new capd::krak::ed_rec_job(f,*(capd::krak::record *)~f,lfrm);

                  rec_job->launch(this);
                  }
                  break;
               case CONST_STRING:
                  default:;
            }
         }
      }
      repaint();
      return status;
   }
}

/******************************************************************************/

/// @}
