/// @addtogroup krak
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file job.h
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifndef _CAPD_KRAK_JOB_H_ 
#define _CAPD_KRAK_JOB_H_ 

#include "capd/krak/frame.h"
#include "capd/krak/item.h"
#include "capd/capd/minmax.h"

#  define A_JOB       0
#  define BASIC_JOB   1
#  define SEL_JOB     2
#  define MENU_JOB    3
#  define VIEW_JOB    4
#  define DEL_INS_JOB 5
#  define ED_REC_JOB  6

namespace capd{
namespace krak{
   enum Status{sleeping,running,finished};
   typedef int Stat;
   extern void (*restore_window)(void);
   class view_job;
   int confirm(capd::krak::Frame &jobfrm, const char *prompt, const char *yes, const char *no);
}}


//############################  class job #################################
namespace capd{
namespace krak{
class job : public capd::krak::link
{
public:

   static job* runningJob;
   static job *rootJob,*requestedJob,*previousJob;
   static int desktopColor;

   static job* userSelectedJob(capd::krak::UserMove &um);
   static capd::krak::frstring message;
   static void mainLoop(void);

   capd::krak::Frame jobfrm;
   capd::krak::Stat status;
   int visible;
   job *parent;
   capd::krak::hlink children;
   int order_no;
   int immortal;
   int request_repaint;     //introduced experimentally, so far use only in view_job;

   void makeInvisible(void);
   void makeVisible(void);
   virtual void furnish(void);
   job(void);
   job(const capd::krak::Frame &prntfrm, const capd::krak::At &lt, const capd::krak::At &rb);
   job(int mylti, int myltj, int myrbi, int myrbj);
   job(const capd::krak::Frame &frame);

   virtual int type();
   job* selectJob(capd::krak::UserMove &um);
   virtual void launch(job *prnt=rootJob);
   virtual capd::krak::Stat process(capd::krak::UserMove &um);
   virtual void terminate(void);
   virtual void own_repaint(void);
   virtual void repaint(void);
   int exists(job *jobPt);
   int exists(int type);
};

//############################  class basic_job ################################

class basic_job : public job
{
   public:


   capd::krak::frstring title;
   capd::krak::Frame titlefrm,stopfrm,userfrm,helpfrm;
   capd::krak::view_job *help;

   virtual void furnish(void);
   basic_job(void);

   basic_job(const capd::krak::Frame &prntfrm,
      const capd::krak::At &lt, const capd::krak::At &rb, const capd::krak::frstring &text);
   basic_job(int mylti, int myltj, int myrbi, int myrbj, const capd::krak::frstring &text);
   basic_job(const capd::krak::Frame &frame, const capd::krak::frstring &text);
   virtual int type();
   virtual Stat process(capd::krak::UserMove &um);
   virtual void own_repaint(void);
};


//############################  class sel_job #################################

class sel_job : public basic_job
{
public:
   capd::krak::list &a_list;
   capd::krak::Frame window,upFrm,downFrm;
   int selector,firstshown,lastshown,maxshown,length,search_token_length,search_permitted;
   capd::krak::frstring search_token;
   int noStopFrm;

   virtual void launch(job *prnt=rootJob);
   virtual void furnish(void);

   sel_job(const capd::krak::frstring &t,capd::krak::list &l, const capd::krak::Frame &f, int nostopfrm=0);
   virtual int type();
   virtual capd::krak::Stat process(capd::krak::UserMove &um);
   virtual void own_repaint(void);
   virtual int MakeSelection(capd::krak::UserMove &um);
   void testUpDown(capd::krak::UserMove &um);
};

//############################  class menu_job #################################

class menu_job  : public sel_job
{
public:
   void (*executor)(capd::krak::frstring &);

   menu_job(const capd::krak::frstring &t,list &l,const capd::krak::Frame &f,
      void (*e)(capd::krak::frstring &), int nostopfrm=0);
   virtual int type();
   virtual capd::krak::Stat process(capd::krak::UserMove &um);
};

//############################  class view_job #################################

class view_job  : public sel_job
{
public:
   capd::krak::frstring bufor;
   int pos;               // current position in line;
   int field_width;       // seems to be unused
   int active,opened,size,with_file;
   capd::krak::frstring filename;
   std::fstream job_file;

   view_job(const capd::krak::frstring &t,capd::krak::list &l,
      const capd::krak::Frame &f,int act=1, int nostopfrm=0);
   view_job(const capd::krak::frstring &fname,const capd::krak::frstring &t,
      capd::krak::list &l,const capd::krak::Frame &f,int act=1);
   virtual int type();
   virtual capd::krak::Stat process(capd::krak::UserMove &um);
   virtual void own_repaint(void);
   void open(int read=0);
   void reset(void);                    //clear window
   void close(void);
   void width(int n);
//  friend view_job &operator<<(view_job &v, char *s);     //send string to window
   friend view_job &operator<<(view_job &v,capd::krak::frstring f);   //send frstring to window
   friend view_job &operator<<(view_job &v, capd::krak::Tab &t);        //send Tab to window
};

//############################  class del_ins_job ##############################

class del_ins_job : public sel_job
{
public:
   capd::krak::Frame insfrm,delfrm;

   virtual void furnish(void);
   del_ins_job(const capd::krak::frstring &t,capd::krak::list &l,const capd::krak::Frame &f);
   virtual int type();
   virtual capd::krak::Stat process(capd::krak::UserMove &um);
   virtual void own_repaint(void);
};

//############################  class ed_rec_job ###############################

class ed_rec_job : public sel_job
{
public:
   capd::krak::Frame editfrm;
   int edit_field_start,edit_field_length;

   virtual void furnish(void);
   ed_rec_job(const capd::krak::frstring &t,capd::krak::record &r,const capd::krak::Frame &f);
   virtual int type();
   virtual capd::krak::Stat process(capd::krak::UserMove &um);
   virtual void own_repaint(void);
   void set_edit_field_start(int percent); //set the proportion between the name
                                          //and value subframes
};

}} // the end of the namespace capd::krak

//#############################################################################
//############################### inline definitions ##########################
//#############################################################################
namespace capd{
namespace krak{
   inline void job_restore_window(void)
   {
      capd::krak::job::rootJob->repaint();
   }
}}

//############################  class job #################################

inline void capd::krak::job::makeInvisible(void)
{
   visible=0;
}

inline void capd::krak::job::makeVisible(void)
{
   visible=1;
}

inline void capd::krak::job::furnish(void){}

inline capd::krak::job::job(const capd::krak::Frame &prntfrm, const capd::krak::At &lt, const capd::krak::At &rb)
   : jobfrm(prntfrm,lt,rb,PINE,WHITE,0,0), status(sleeping), visible(1), parent(NULL),
   immortal(0), request_repaint(1)
{}

inline capd::krak::job::job(int mylti, int myltj, int myrbi, int myrbj)
   : jobfrm(mylti,myltj,myrbi,myrbj,WHITE,BLACK,0,0), status(sleeping), visible(1), parent(NULL),
   immortal(0), request_repaint(1)
{}

inline capd::krak::job::job(const capd::krak::Frame &frame)
   : status(sleeping), visible(1), parent(NULL), immortal(0), request_repaint(1)
{
   jobfrm=frame;
   jobfrm.imarg=jobfrm.jmarg=0;
}

inline int capd::krak::job::type()
{
   return A_JOB;
}

inline capd::krak::Stat capd::krak::job::process(capd::krak::UserMove &um)
{
   return running;
}

inline void capd::krak::job::own_repaint(void) {}

//############################### basic_job #################################

inline void capd::krak::basic_job::furnish(void)
{
   jobfrm.adjust();
   titlefrm = capd::krak::Frame(jobfrm,At(1,1),At(2,jobfrm.lCol-3),jobfrm.bgColor,jobfrm.fgColor);
   stopfrm = capd::krak::Frame(jobfrm, capd::krak::At(1,jobfrm.lCol-2),
      capd::krak::At(2,jobfrm.lCol-1), jobfrm.bgColor, jobfrm.fgColor);
   helpfrm = capd::krak::Frame(jobfrm, capd::krak::At(1,jobfrm.lCol-4),
      capd::krak::At(2,jobfrm.lCol-3), jobfrm.bgColor, jobfrm.fgColor);
   help=NULL;
}

inline capd::krak::basic_job::basic_job(void)
{
   furnish();
}


inline capd::krak::basic_job::basic_job(const capd::krak::Frame &prntfrm,
   const capd::krak::At &lt, const capd::krak::At &rb, const capd::krak::frstring &text)
   : capd::krak::job(prntfrm,lt,rb)
{
   furnish();
   title=text;
}

inline capd::krak::basic_job::basic_job(int mylti, int myltj, int myrbi, int myrbj,
   const capd::krak::frstring &text) : capd::krak::job(mylti,myltj,myrbi,myrbj)
{
   furnish();
   title=text;
}

inline capd::krak::basic_job::basic_job(const capd::krak::Frame &frame, const capd::krak::frstring &text)
   : capd::krak::job(frame)
{
   title=text;
   furnish();
}

inline int capd::krak::basic_job::type()
{
   return BASIC_JOB;
}

//############################  class sel_job #################################

inline void capd::krak::sel_job::furnish(void)
{
//    window=Frame(jobfrm,At(2,1),At(jobfrm.lRow-1,jobfrm.lCol-1),WHITE,BLACK);
   window = capd::krak::Frame(jobfrm,At(3,1),At(jobfrm.lRow-1,jobfrm.lCol-2),WHITE,BLACK);
   upFrm = capd::krak::Frame(jobfrm, capd::krak::At(3,jobfrm.lCol-2),
      capd::krak::At(jobfrm.lRow/2,jobfrm.lCol), jobfrm.bgColor, jobfrm.fgColor);
   downFrm = capd::krak::Frame(jobfrm, capd::krak::At(jobfrm.lRow/2+1,jobfrm.lCol-2),
      capd::krak::At(jobfrm.lRow-1,jobfrm.lCol), jobfrm.bgColor, jobfrm.fgColor);
   maxshown=window.NoRow();
}

inline capd::krak::sel_job::sel_job(const capd::krak::frstring &t,
   capd::krak::list &l, const capd::krak::Frame &f, int nostopfrm)
   : capd::krak::basic_job(f,t), a_list(l)
{
   furnish();
   search_token="";
   search_token_length=selector=firstshown=0;
   length=l.len();
   lastshown = capd::min(length,maxshown)-1;
   search_permitted=0;
   noStopFrm=nostopfrm;
}

inline int capd::krak::sel_job::type()
{
   return SEL_JOB;
}

//############################  class menu_job #################################

inline capd::krak::menu_job::menu_job(const capd::krak::frstring &t,
   capd::krak::list &l,const capd::krak::Frame &f, void (*e)(capd::krak::frstring &), int nostopfrm)
   : capd::krak::sel_job(t,l,f,nostopfrm)
{
   noStopFrm=nostopfrm;
   executor=e;
   search_permitted=1;
}

inline int capd::krak::menu_job::type()
{
   return MENU_JOB;
}

//############################  class view_job #################################

inline capd::krak::view_job::view_job(const capd::krak::frstring &t,
   capd::krak::list &l, const capd::krak::Frame &f,int act,int nostopfrm)
   : capd::krak::sel_job(t,l,f,nostopfrm), pos(0),
   field_width(0), active(act), opened(0), size(0), with_file(0)
{
     if(active) opened=1;
}

inline capd::krak::view_job::view_job(const capd::krak::frstring &fname,
   const capd::krak::frstring &t, capd::krak::list &l, const capd::krak::Frame &f,int act)
   : capd::krak::sel_job(t,l,f), pos(0),
   field_width(0), active(act), opened(0), size(0), with_file(1), filename(fname)
{
   if(active)opened=1;
}

inline int capd::krak::view_job::type()
{
   return VIEW_JOB;
}

/*
  inline view_job &view_job::operator<<(frstring &s)
  begin
    return operator<<(t.string());
  end;
*/

inline void capd::krak::view_job::reset(void)
{
   if(!with_file)
   {
      a_list.empty();
      search_token_length=selector=firstshown=length=0;
      lastshown = capd::min(length,maxshown)-1;
      window.Clear();
      window << At(0,0);
   }
}

inline void capd::krak::view_job::close(void)
{
   *this << "\n";
   if(!active)
   {
      firstshown=selector=0;
      length=a_list.len();
      lastshown = capd::min(length,maxshown)-1;
      own_repaint();
   }
   if(with_file) job_file.close();
   opened=0;
}

inline void capd::krak::view_job::width(int n)
{
   field_width=n;
}

//############################  class del_ins_job ##############################

inline void capd::krak::del_ins_job::furnish(void)
{
   window = capd::krak::Frame(jobfrm, capd::krak::At(3,1),
      capd::krak::At(jobfrm.lRow-5,jobfrm.lCol-2),WHITE,BLACK);
   maxshown=window.NoRow();
   insfrm = capd::krak::Frame(jobfrm, capd::krak::At(jobfrm.lRow-2,5),
      capd::krak::At(jobfrm.lRow-1,8),jobfrm.bgColor,WHITE);
   delfrm = capd::krak::Frame(jobfrm, capd::krak::At(jobfrm.lRow-2,1),
      capd::krak::At(jobfrm.lRow-1  ,4), jobfrm.bgColor,WHITE);
   upFrm = capd::krak::Frame(jobfrm, capd::krak::At(3,jobfrm.lCol-2),
      capd::krak::At(jobfrm.lRow/2, jobfrm.lCol), jobfrm.bgColor, jobfrm.fgColor);
   downFrm = capd::krak::Frame(jobfrm, capd::krak::At(jobfrm.lRow/2+1,jobfrm.lCol-2),
      capd::krak::At(jobfrm.lRow-5,jobfrm.lCol), jobfrm.bgColor, jobfrm.fgColor);
}

inline capd::krak::del_ins_job::del_ins_job(const capd::krak::frstring &t,
   capd::krak::list &l,const capd::krak::Frame &f): capd::krak::sel_job(t,l,f)
{
   furnish();
   lastshown = capd::min(length,maxshown)-1;
   search_permitted=1;
}

inline int capd::krak::del_ins_job::type()
{
   return DEL_INS_JOB;
}

//############################  class ed_rec_job ###############################

inline void capd::krak::ed_rec_job::furnish(void)
{
   window = capd::krak::Frame(jobfrm, capd::krak::At(3,1),
      capd::krak::At(jobfrm.lRow-1,edit_field_start-2),WHITE,BLACK);
   maxshown=window.NoRow();
   editfrm = capd::krak::Frame(jobfrm, capd::krak::At(3,edit_field_start),
      capd::krak::At(jobfrm.lRow-1,jobfrm.lCol-3),WHITE,BLACK);
   upFrm = capd::krak::Frame(jobfrm, capd::krak::At(3,jobfrm.lCol-2),
      capd::krak::At(jobfrm.lRow/2,jobfrm.lCol), jobfrm.bgColor, jobfrm.fgColor);
   downFrm = capd::krak::Frame(jobfrm, capd::krak::At(jobfrm.lRow/2+1,jobfrm.lCol-2),
      capd::krak::At(jobfrm.lRow-1,jobfrm.lCol), jobfrm.bgColor, jobfrm.fgColor);
   edit_field_length=jobfrm.lCol-1-edit_field_start;
}

inline capd::krak::ed_rec_job::ed_rec_job(const capd::krak::frstring &t,
   capd::krak::record &r,const capd::krak::Frame &f) : capd::krak::sel_job(t,r,f)
{
   set_edit_field_start(40);
   furnish();
   lastshown = capd::min(length,maxshown)-1;
   search_permitted=1;
}

inline void capd::krak::ed_rec_job::set_edit_field_start(int percent)
{
   edit_field_start=percent*jobfrm.lCol/100;
}

inline int capd::krak::ed_rec_job::type()
{
   return ED_REC_JOB;
}

//#############################################################################

#if defined(KRAK_ERRORS)
namespace capd{
namespace krak{
   extern capd::krak::view_job *view_cerr;
}}
   #define cerr (* view_cerr)
   #define exit  waitBt();exit
#endif

// Obecnosc tego wzorca powoduje, ze gcc wywala sie pod LINUXem,
// jezeli jest wlaczona opcja kompilacji "-fexternal-templates".
namespace capd{
namespace krak{
template<class OBJECT>
   capd::krak::view_job &operator<<(capd::krak::view_job &s, OBJECT &o){
      capd::krak::frstring f;
      f << o;
      s << f;
      return s;
   }
}}

#endif // _CAPD_KRAK_JOB_H_ 

/// @}
