/// @addtogroup setarth
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file setarth.cpp
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#include <fstream>
#include <sstream>
#include "capd/krak/krak.h"
#include "capd/krak/item.h"
#include "capd/krak/job.h"
#include "capd/capdlib.h"

#include "lorenz.h"
#include "rossler.h"
#include "kursiva.h"

#include "henon3.h"
#include "setarth.h"
using namespace capd;


std::ofstream raport("raport",std::ios::app);

/******************************************************************************/


IEuclNorm euclN;
IMaxNorm maxN;
ISumNorm sumN;
IEuclLNorm euclLN;
IMaxLNorm maxLN;
ISumLNorm sumLN;

Frame dynFrame;
Frame expansionFrame;
Frame localExpansionFrame;
Frame trajectoryFrame;
frstring status;

Lorenz *lor; // global , needed for sections lorenz system
Interval (* section_form)(IVector &);


/******************************************************************************/

record problems;
record current_problem;
menu_job *do_menu=NULL;
menu_job *select_problem_job=NULL;
ed_rec_job *edit_problem_job=NULL;
std::ifstream inp;
problemData pd;

/******************************************************************************/

const double blowUpLimit=10000;
extern char status_description[];

int setin(IVector &s1,IVector &s2,int interior=0)
{
  int res=1;
  int i=0;
  while((i<DIM) && res)
  {
    res = (interior)? subsetInterior(s1[i],s2[i]) :  subset(s1[i],s2[i]);
    i++;
  }
  return(res);
}

/******************************************************************************/
// this function was previously a method of the class C0Set
template <typename C0Set>
int reach(C0Set& s, IDynSys &dynsys, v_form alpha)
{
  IVector oldvek,vek;
  vek = IVector(s);

  Interval old_side,side=alpha(vek);
  int count=0;
  int still_on_section=side.contains(0.0);
  #if defined(TESTING)
  double ini_size=size();
  #endif

  while(true)
  {
    count++;
    old_side = side;
    oldvek = vek;
    s.move(dynsys);
    vek = IVector(s);
    side = alpha(vek);

    if(setin(oldvek,vek))
      break;

    #if defined(TESTING)
    if(size()/ini_size>blowUpLimit)
      errorExit("Blow up!");
    #endif

    if(still_on_section){
      still_on_section=side.contains(0.0);
    }else{
      if( side>0 && !(old_side>0) ) break;
    }
    if( status != ""){
      break;
    }
  }
  return count;
}

/******************************************************************************/

// this function was previously a method of the class C0Set
template <typename C0Set>
Interval blowUp(C0Set &S, IDynSys &dynsys,double blowuptime)
{
  Interval ini_size = S.size();
  int counter=0;
  status="";


  Interval tstep=0.0;
  if(dynsys.type()=="flow")
  {
    IOdeNum *podenum;
    podenum=(IOdeNum *)&dynsys;
    tstep=podenum->step;
  }else
    tstep=1.0;

  #define BLOWUPTESTY
  #define EXPTEST
  #define OSCYLATOR

  #ifdef BLOWUPTESTY
  Frame frmcom(rootFrame,1,70,99,99);
  frmcom.Clear();
  frmcom << dynsys.type() << "\n";
  frmcom <<  "x=" << S.center() << " size=" << S.size() << " \n";
  frmcom << "tstep=" << tstep << "\n";
  waitBt();
  #endif

  Interval time=0.0;

  #ifdef BLOWUPTESTY
  double progstep=0.3;
  double prog=progstep;
  #endif

  while(time < blowuptime)
  {
    S.move(dynsys);
    time+=tstep;
    counter++;

    #ifdef BLOWUPTESTY
    if(time > prog)
    {
      prog+=progstep;
      frmcom.Clear();
      frmcom << "time=" << time << "\n";
      frmcom << " size=" << S.size() << " \n";
      frmcom << "x=" << S.center() << "\n";

      #ifdef OSCYLATOR
      double c=cos(time.leftBound());
      double s=sin(time.leftBound());
      frmcom << "(cos(t),sin(t))=(" << c << ","<< s << ")"  << "\n";
      frmcom << "diff=" <<  "(" << c - S.center()[0] << ","<< s - S.center()[1] << ")"  << "\n";
      #endif // OSCYLATOR

      #ifdef EXPTEST
      double expt= exp(time.leftBound());
      frmcom << "exp(t)="<< expt << "\n";
      frmcom << "diff="<< expt - S.center()[0] << "\n";
      #endif

     // waitBt();
    }

    #endif // BLOWUPTESTY

    if(S.size()/ini_size>blowUpLimit) break;
    if( status != ""){
       std::cerr << status << std::endl;
       break;
    }
  }
  return time;
}

/******************************************************************************/

Interval lorenz_form(IVector &x)
{
  return lor->getR()-x[2];
}

/******************************************************************************/

Interval rossler_form(IVector &x)
{
  return x[0];
}

/******************************************************************************/

Interval kursiva_form(IVector &x)
{
  return -(2 + x[0]);
}

/******************************************************************************/

Interval lin_form(IVector &x)
{
  return x[0];
}

/******************************************************************************/

Interval lorenz_form2(IVector &x)
{
  return -lor->getR()+x[2];
}

/******************************************************************************/

Interval lorenz_form3(IVector &x)
{
  return -9+x[0];
}

/******************************************************************************/

Interval lorenz_form4(IVector &x)
{
  return 3*lor->getR()/4-x[2];
}

/******************************************************************************/

void test_factorial(void)
{
  dynFrame << factorial(5) << "\n";
  dynFrame << factorial(3) << "\n";
  dynFrame << factorial(11) << "\n";
  dynFrame << factorial(0) << "\n";

  dynFrame << newton(3,0) << "\n";
  dynFrame << newton(5,5) << "\n";
  dynFrame << newton(0,0) << "\n";
  dynFrame << newton(11,10) << "\n";
}


/******************************************************************************/

template <typename SetType>
double subdivisionTest(IDynSys &d, SetType &muster, int no_it,
                       frstring descr,
                       IVector ini_vect, IVector ini_box,
                       double expansion, double reltime)
{
  double retval;
  dynFrame << descr << "  ";
  int attempts=0;
  int time=0;
  IntervalSet ini_set(ini_vect,ini_box);

  Interval final_size=expansion*size(ini_box);
  while(true)
  {
    double prev_size=0;
    status = "";
    attempts++;
    if(attempts > 20)
    {
      status = "more than 20 attempts";
      break;
    }
    rootFrame << At(30,30) << "trying: " << ini_box;
    SetType *s= dynamic_cast<SetType *>(muster.cover(ini_set));
    tick_meter();
    for(int i=0;i<no_it;i++)
    {
      rootFrame << At(28,30) << "size=" << s->size() << "     ";
      prev_size=(s->size()).rightBound();
      s->move(d);
      if(s->size()>final_size)
      {
        status = "blowUp in iterate";
        break;
      }
    }
    time=tick_meter();
    if(time == 0) time=1;
    Interval set_size=s->size();
    dynFrame << Tab(12) << "(" << attempts << ") (" << set_size.rightBound() << ") (" << prev_size << ") ";
    delete s;
//waitBt();
    if(set_size < final_size) break;
    ini_set=IntervalSet(ini_vect,ini_box/=2);
    //      Interval org_size=ini_set.size();
  }
  if(status == "")
  {
    double col3=1.0;
    retval=power((double)2,(DIM*attempts))*time;
    if(reltime > 0)
    {
      col3=retval/reltime;
    }
    dynFrame << Tab(40) <<  retval << Tab(50) << col3 << "\n";
  }else{
    dynFrame << Tab(30) << "  Failure, status=" << status << "  \n";
    retval=-1;
  }
  return(retval);
}

/******************************************************************************/

int set_no=0;
int set_color[16]={ORANGE,DARKBLUE,RED,OLIVE,
                   VIOLET,ORANGERED,BLUE,MAGENTA,
                   CYAN,PINE,GREEN,BROWN,BLUEGREEN};

/******************************************************************************/

template <typename C0Set>
double iterateTest(IDynSys &d, C0Set &s, int no_it, frstring descr, double reltime)
{
  Interval org_size=s.size();
  double retval,L=1.0,prevL=1.0,L_rel_change;
  status = "";

  dynFrame.SetFgColor(set_color[set_no]);
  dynFrame << descr << "  ";
  dynFrame.SetFgColor(BLACK);
  expansionFrame.jump(0.0,0.0);
  tick_meter();
  for(int i=0;i<no_it;i++)
  {
    s.move(d);
    prevL=L;
    L=(s.size()/org_size).rightBound();
    L_rel_change=L/prevL;
    if(L<=pd.max_expansion) 
      expansionFrame.draw((double)i,L,set_color[set_no]);
    if(i>1 && L_rel_change>=pd.min_loc_expansion &&
         L_rel_change<=pd.max_loc_expansion)
            localExpansionFrame.draw((double)i,L_rel_change,set_color[set_no]);
    else 
      localExpansionFrame.jump((double)i,L_rel_change);

    double z=(s.center()[2]).rightBound();
    if(i>1 && z>=pd.min_z && z<=pd.max_z)
      trajectoryFrame.draw((double)i,z,set_color[set_no]);
    else 
      trajectoryFrame.jump((double)i,z);
    if(L>pd.blowuplimit)
    {
      status = "blowUp in iterate";
      break;
    }
  }
  int time=tick_meter();
  if(time == 0) time=1;
  if(status == "")
  {
    double col3=1.0;
    L=(s.size()/org_size).rightBound();
    if(reltime > 0)
    {
      col3=time*L/reltime;
    }
    dynFrame << Tab(12) <<  L << Tab(24) << time << Tab(36) << time*L << Tab(48) << col3 << "\n";
    retval=time*L;
  }else{
    dynFrame << Tab(12) << "  Failure, status=" << status << "  \n";
    retval=-1;
  }
  set_no++;
  return(retval);
}

/******************************************************************************/

template <typename C0Set>
double sectionTest(IDynSys &d, C0Set &s, v_form alpha, frstring descr,
                            double reltime,int itno=0)
  // itno - important only when d.type()<>"flow" - number of iterates
{
  Interval org_size=s.size();

  double retval;
  status = "";
  dynFrame << descr << "  ";
  raport << descr << "  " ;

  tick_meter();
  if(d.type()=="flow")
    reach(s,d,alpha);
  else{
    for(int i=0;i < itno; i++)
      s.move(d);
  }

  int time=tick_meter();

  if(status == "")
  {
    double col3=1.0;
    double L=(s.size()/org_size).rightBound();
    if(reltime > 0)
    {
      col3=time*L/reltime;
    }
    dynFrame << Tab(30) <<  L << Tab(50) << col3 << "\n";
    raport.setf(std::ios::scientific);  // notacja naukowa liczb
    raport << "     " <<  L << "         "  << col3 << "\n";
    retval=time*L;
  }else{
    dynFrame << Tab(30) << "  Failure, status=" << status << "  \n";
    raport << "      " << "  Failure, status=" << status << "  \n";
    retval=-1;
  }
  return(retval);
}

/******************************************************************************/

template <typename C0Set>
double blowUpTest(IDynSys &d, C0Set &s, frstring descr,double reltime)
{
  // if reltime < 0 - then we write in the last column 1
  //      otherwise we write there t/tdynsys <- this average computer time
  //                                   divided by reltime

  dynFrame << descr << "   ";
  raport << descr << "   ";
  tick_meter();
  double tdynsys = mid(blowUp(s,d,pd.blowuptime)).rightBound();  // dynsys - time
  double time=tick_meter()/tdynsys;

  double col3=1;
  if(reltime > 0)
    col3=time/reltime;

  if (tdynsys < pd.blowuptime)
  {
    dynFrame << Tab(30) << tdynsys << Tab(50) << col3 << " \n";
    raport <<  "      " <<  tdynsys << "          " << col3 << "\n";
  }
  else{
    dynFrame << Tab(30) << "No blowUp" << Tab(50) << col3 << " \n";
    raport << "      " << "No blowUp" << "    " << col3 << " \n";
  }
  return(time);
}

/******************************************************************************/

template <typename C0Set1, typename C0Set2 >
void parallelTest(IDynSys &d, C0Set1 &s1, C0Set2 &s2, int no_it)
{
  dynFrame << "It. no" << Tab(10) << "C0Set 1" << Tab(25) << "C0Set 2\n";
  for(int i=0;i<no_it;i++)
  {
    if(status == "")
    {
      dynFrame << i << Tab(10) << (s1.size()).rightBound() << Tab(25) << (s2.size()).rightBound() << " \n";
    }else{
      dynFrame << i << Tab(10) << "Failure: " << status;
      break;
    }
    if(i % 20 == 0)
    {
      dynFrame << At(5,0); waitBt();
    }
    s1.move(d);
    s2.move(d);
  }
}

/******************************************************************************/

void subdivisionTest(IDynSys &d)
{
  IntervalSet intv(pd.initialVector,pd.initialBox);
  C0RectSet rect(pd.initialVector,pd.initialBox);
  C0Rect2Set rect2(pd.initialVector,pd.initialBox);
  C0PpedSet pped(pd.initialVector,pd.initialBox);
  C0Pped2Set pped2(pd.initialVector,pd.initialBox);
  EllipsoidSet ellipsoid(pd.initialVector,pd.initialSize);
  BallSet euclBall(pd.initialVector,pd.initialSize,euclN);
  BallSet maxBall(pd.initialVector,pd.initialSize,maxN);
  BallSet sumBall(pd.initialVector,pd.initialSize,sumN);
  BallSet eucllBall(pd.initialVector,pd.initialSize,euclN);
  BallSet maxlBall(pd.initialVector,pd.initialSize,maxN);
  BallSet sumlBall(pd.initialVector,pd.initialSize,sumN);
  FlowballSet feuclBall(pd.initialVector,pd.initialSize,euclN);
  FlowballSet fmaxBall(pd.initialVector,pd.initialSize,maxN);
  FlowballSet fsumBall(pd.initialVector,pd.initialSize,sumN);
  FlowballSet feuclLBall(pd.initialVector,pd.initialSize,euclLN);
  FlowballSet fmaxLBall(pd.initialVector,pd.initialSize,maxLN);
  FlowballSet fsumLBall(pd.initialVector,pd.initialSize,sumLN);

  int no_it=( d.type()=="flow" ?  int(pd.iteratetime/pd.step) : int(pd.iteratetime));

  dynFrame << "requested size=" << pd.expansion*size(pd.initialBox) << "\n";
  dynFrame << Tab(20) << "attempts" << Tab(45) << "Cost" << Tab(60) << "Cost" << "\n\n";

  double reltime=-1;
  reltime=subdivisionTest(d,intv,no_it,"intv",pd.initialVector,pd.initialBox,pd.expansion,reltime);
  subdivisionTest(d,pped,no_it,"pped",pd.initialVector,pd.initialBox,pd.expansion,reltime);
  subdivisionTest(d,pped2,no_it,"pped2",pd.initialVector,pd.initialBox,pd.expansion,reltime);
  subdivisionTest(d,rect,no_it,"rect",pd.initialVector,pd.initialBox,pd.expansion,reltime);
  subdivisionTest(d,rect2,no_it,"rect2",pd.initialVector,pd.initialBox,pd.expansion,reltime);
  subdivisionTest(d,ellipsoid,no_it,"ellipsoid",pd.initialVector,pd.initialBox,pd.expansion,reltime);
  if(d.type()=="flow")
  {
    subdivisionTest(d,feuclLBall,no_it,"feuclLBall",pd.initialVector,pd.initialBox,pd.expansion,reltime);
    subdivisionTest(d,fmaxLBall,no_it,"fmaxLBall",pd.initialVector,pd.initialBox,pd.expansion,reltime);
    subdivisionTest(d,fsumLBall,no_it,"fsumLBall",pd.initialVector,pd.initialBox,pd.expansion,reltime);
    subdivisionTest(d,euclBall,no_it,"feuclBall",pd.initialVector,pd.initialBox,pd.expansion,reltime);
    subdivisionTest(d,maxBall,no_it,"fmaxBall",pd.initialVector,pd.initialBox,pd.expansion,reltime);
    subdivisionTest(d,sumBall,no_it,"fsumBall",pd.initialVector,pd.initialBox,pd.expansion,reltime);
  }else{
    subdivisionTest(d,euclBall,no_it,"euclBall",pd.initialVector,pd.initialBox,pd.expansion,reltime);
    subdivisionTest(d,maxBall,no_it,"maxBall",pd.initialVector,pd.initialBox,pd.expansion,reltime);
    subdivisionTest(d,sumBall,no_it,"sumBall",pd.initialVector,pd.initialBox,pd.expansion,reltime);
  }

  dynFrame << "----------------------------------\n";
}

/******************************************************************************/

void iterateTest(IDynSys &d)
{
  IntervalSet intv(pd.initialVector,pd.initialBox);
  Intv2Set intv2(pd.initialVector,pd.initialBox);
  C0RectSet rect(pd.initialVector,pd.initialBox);
  C0Rect2Set rect2(pd.initialVector,pd.initialBox);
  C0PpedSet pped(pd.initialVector,pd.initialBox);
  C0Pped2Set pped2(pd.initialVector,pd.initialBox);
  EllipsoidSet ellipsoid(pd.initialVector,pd.initialSize);
  BallSet euclBall(pd.initialVector,pd.initialSize,euclN);
  BallSet maxBall(pd.initialVector,pd.initialSize,maxN);
  BallSet sumBall(pd.initialVector,pd.initialSize,sumN);
  BallSet eucllBall(pd.initialVector,pd.initialSize,euclN);
  BallSet maxlBall(pd.initialVector,pd.initialSize,maxN);
  BallSet sumlBall(pd.initialVector,pd.initialSize,sumN);
  FlowballSet feuclBall(pd.initialVector,pd.initialSize,euclN);
  FlowballSet fmaxBall(pd.initialVector,pd.initialSize,maxN);
  FlowballSet fsumBall(pd.initialVector,pd.initialSize,sumN);
  FlowballSet feuclLBall(pd.initialVector,pd.initialSize,euclLN);
  FlowballSet fmaxLBall(pd.initialVector,pd.initialSize,maxLN);
  FlowballSet fsumLBall(pd.initialVector,pd.initialSize,sumLN);

  int no_it=( d.type()=="flow" ?  int(pd.iteratetime/pd.step) : int(pd.iteratetime));

  set_no=0;
  expansionFrame.Bound();
  localExpansionFrame.Bound();
  trajectoryFrame.Bound();

  expansionFrame.setWorldCoord(0.0,0.0,(double)no_it,pd.max_expansion);
  localExpansionFrame.setWorldCoord(0.0,pd.min_loc_expansion,
                            (double)no_it,pd.max_loc_expansion);
  trajectoryFrame.setWorldCoord(0.0,pd.min_z,(double)no_it,pd.max_z);

  dynFrame << "iteration time=" << pd.iteratetime << "   no_it=" << no_it  << "\n\n";

  dynFrame << Tab(12) <<  "Expansion" << Tab(24) << "Proc.time" << Tab(36) << "Cost" << Tab(48) << "Rel.Cost" << "\n";
  //  dynFrame << Tab(30) << "L - Expansion" << Tab(45) << "Cost=L*time" << Tab(60) << "Cost" << "\n\n";

  double reltime=-1;
  reltime=iterateTest(d,intv,no_it,"intv",reltime);
  iterateTest(d,intv2,no_it,"intv2",reltime);
  iterateTest(d,pped,no_it,"pped",reltime);
  iterateTest(d,pped2,no_it,"pped2",reltime);
  iterateTest(d,rect,no_it,"rect",reltime);
  iterateTest(d,rect2,no_it,"rect2",reltime);
  iterateTest(d,ellipsoid,no_it,"ellipsoid",reltime);
  if(d.type()=="flow")
  {
    iterateTest(d,feuclLBall,no_it,"feuclLBall",reltime);
    iterateTest(d,fmaxLBall,no_it,"fmaxLBall",reltime);
    iterateTest(d,fsumLBall,no_it,"fsumLBall",reltime);
    iterateTest(d,euclBall,no_it,"feuclBall",reltime);
    iterateTest(d,maxBall,no_it,"fmaxBall",reltime);
    iterateTest(d,sumBall,no_it,"fsumBall",reltime);
  }else{
    iterateTest(d,euclBall,no_it,"euclBall",reltime);
    iterateTest(d,maxBall,no_it,"maxBall",reltime);
    iterateTest(d,sumBall,no_it,"sumBall",reltime);
  }

  dynFrame << "----------------------------------\n";
}

/******************************************************************************/

void sectionTest(IDynSys &d, v_form alpha,int itno)
{
  IntervalSet intv(pd.initialVector,pd.initialBox);
  Intv2Set intv2(pd.initialVector,pd.initialBox);
  C0RectSet rect(pd.initialVector,pd.initialBox);
  C0Rect2Set rect2(pd.initialVector,pd.initialBox);
  C0PpedSet pped(pd.initialVector,pd.initialBox);
  C0Pped2Set pped2(pd.initialVector,pd.initialBox);
  EllipsoidSet ellipsoid(pd.initialVector,pd.initialSize);
  BallSet euclBall(pd.initialVector,pd.initialSize,euclN);
  BallSet maxBall(pd.initialVector,pd.initialSize,maxN);
  BallSet sumBall(pd.initialVector,pd.initialSize,sumN);
  BallSet eucllBall(pd.initialVector,pd.initialSize,euclN);
  BallSet maxlBall(pd.initialVector,pd.initialSize,maxN);
  BallSet sumlBall(pd.initialVector,pd.initialSize,sumN);
  FlowballSet feuclBall(pd.initialVector,pd.initialSize,euclN);
  FlowballSet fmaxBall(pd.initialVector,pd.initialSize,maxN);
  FlowballSet fsumBall(pd.initialVector,pd.initialSize,sumN);
  FlowballSet feuclLBall(pd.initialVector,pd.initialSize,euclLN);
  FlowballSet fmaxLBall(pd.initialVector,pd.initialSize,maxLN);
  FlowballSet fsumLBall(pd.initialVector,pd.initialSize,sumLN);

  dynFrame << Tab(30) << "L - Expansion" << Tab(50) << "Cost=L*time" << "\n\n";
  raport <<  "     " << "L - Expansion" << "          " << "Cost=L*time" << "\n\n";

  double reltime=-1;
  if(d.type()=="flow")
  {
  //   reltime=sectionTest(d,zfeuclLBall,alpha,"zfeuclLBall",reltime);
    reltime=sectionTest(d,feuclLBall,alpha,"feuclLBall",reltime);
    sectionTest(d,fmaxLBall,alpha,"fmaxLBall",reltime);
    sectionTest(d,fsumLBall,alpha,"fsumLBall",reltime);
    sectionTest(d,euclBall,alpha,"feuclBall",reltime);
    sectionTest(d,maxBall,alpha,"fmaxBall",reltime);
    sectionTest(d,sumBall,alpha,"fsumBall",reltime);
  }else{
  //   nie ustawiam reltime - bo bylo za szybko - pokazywal zera
    sectionTest(d,euclBall,alpha,"euclBall",reltime,itno);
    sectionTest(d,maxBall,alpha,"maxBall",reltime,itno);
    sectionTest(d,sumBall,alpha,"sumBall",reltime,itno);
  }
  sectionTest(d,ellipsoid,alpha,"ellipsoid",reltime,itno);
  sectionTest(d,intv,alpha,"intv",reltime,itno);
  sectionTest(d,intv2,alpha,"intv2",reltime,itno);
  sectionTest(d,pped,alpha,"pped",reltime,itno);
  sectionTest(d,pped2,alpha,"pped2",reltime,itno);
  sectionTest(d,rect,alpha,"rect",reltime,itno);
  sectionTest(d,rect2,alpha,"rect2",reltime,itno);

  dynFrame << "----------------------------------\n";
  raport <<  "----------------------------------\n";
}

/******************************************************************************/

void blowUpTest(IDynSys &d)
{
   IntervalSet intv(pd.initialVector,pd.initialBox); // Lohner - Interval method
   Intv2Set intv2(pd.initialVector,pd.initialBox);
   C0RectSet rect(pd.initialVector,pd.initialBox);  // Lohner: QR - decomposition
   C0Rect2Set rect2(pd.initialVector,pd.initialBox); // Lohner last method; Lipschitz part + QR decomposition
   C0PpedSet pped(pd.initialVector,pd.initialBox); // Lohner second method   - paralleograms
   C0Pped2Set pped2(pd.initialVector,pd.initialBox); // Lohner last method +  paralleograms
   EllipsoidSet ellipsoid(pd.initialVector,pd.initialSize);

   BallSet euclBall(pd.initialVector,pd.initialSize,euclN);
   BallSet maxBall(pd.initialVector,pd.initialSize,maxN);
   BallSet sumBall(pd.initialVector,pd.initialSize,sumN);
   FlowballSet feuclLBall(pd.initialVector,pd.initialSize,euclLN);
   FlowballSet fmaxLBall(pd.initialVector,pd.initialSize,maxLN);
   FlowballSet fsumLBall(pd.initialVector,pd.initialSize,sumLN);

   dynFrame << "BlowUpLimit="<<  blowUpLimit
      << "    Max blowUp time =" << pd.blowuptime << "\n";
   raport << "BlowUpLimit="<<  blowUpLimit
      << "    Max blowUp time =" << pd.blowuptime << "\n";
   dynFrame << "Set type" << Tab(30) << "BlowUp time" <<
                Tab(50) << "rel. cost " << " \n";
   raport << "Set type" << "      " << "BlowUp time" <<
                "          " << "rel. cost " << " \n";

   double reltime;
   reltime=blowUpTest(d,intv,"intv",-1.0);
   blowUpTest(d,intv2,"intv2",reltime);
   blowUpTest(d,pped,"pped",reltime);
   blowUpTest(d,pped2,"pped2",reltime);
   blowUpTest(d,rect,"rect",reltime);
   blowUpTest(d,rect2,"rect2",reltime);

   blowUpTest(d,euclBall,"euclBall",reltime);
   blowUpTest(d,maxBall,"maxBall",reltime);
   blowUpTest(d,sumBall,"sumBall",reltime);
   blowUpTest(d,ellipsoid,"ellipsoid",reltime);

   if(d.type()=="flow")
   {
      blowUpTest(d,feuclLBall,"feuclLBall",reltime);
      blowUpTest(d,fmaxLBall,"fmaxLBall",reltime);
      blowUpTest(d,fsumLBall,"fsumLBall",reltime);
   }

   dynFrame << "----------------------------------\n";
   raport <<  "----------------------------------\n";
}

/******************************************************************************/

void parallelTest(IDynSys &d)
{
   IntervalSet intv(pd.initialVector,pd.initialBox);
   IntervalSet intv_half(pd.initialVector,pd.initialBox/8);
   C0RectSet rect(pd.initialVector,pd.initialBox);
   C0Rect2Set rect2(pd.initialVector,pd.initialBox);
   C0PpedSet pped(pd.initialVector,pd.initialBox);
   C0Pped2Set pped2(pd.initialVector,pd.initialBox);
   BallSet euclBall(pd.initialVector,pd.initialSize,euclN);
   BallSet maxBall(pd.initialVector,pd.initialSize,maxN);
   BallSet sumBall(pd.initialVector,pd.initialSize,sumN);
   BallSet euclLBall(pd.initialVector,pd.initialSize,euclLN);
   BallSet maxLBall(pd.initialVector,pd.initialSize,maxLN);
   BallSet sumLBall(pd.initialVector,pd.initialSize,sumLN);
   FlowballSet feuclLBall(pd.initialVector,pd.initialSize,euclLN);
   FlowballSet fmaxLBall(pd.initialVector,pd.initialSize,maxLN);
   FlowballSet fsumLBall(pd.initialVector,pd.initialSize,sumLN);

//  parallelTest(d,zfeuclLBall,feuclLBall,3000);
   parallelTest(d,intv,intv_half,400);

   dynFrame << "----------------------------------\n";
}

/******************************************************************************/
// the new style input data routine

int processInputData(record &problems)
{
   int how_many=0;
   frstring line,key,op,value;

   get_to_eol(inp,line);
   key=line.getFirstItem();
   while(true)
   {
      frstring name;
      int name_found=0;

      while(key == TEOF)
      {
         if(line == TEOF) return how_many;
         get_to_eol(inp,line);
         key=line.getFirstItem();
      }

      record *rec=new record;
      while(true)
      {
         key=line.extractFirstItem();
         if(key == TEOF) break;
         if(key == "#") continue;
         op=line.extractFirstItem();
         if(op != "=") continue;
         rec->addfield(key,line);
         if(key == "name")
         {
            if(name_found) errorExit("two names in the same problem");
            name_found=1;
            how_many++;
            name=line.getFirstItem();
         }
         get_to_eol(inp,line);
      }
      if(name_found) problems.addfield(name,*rec);
      if(line == TEOF) break;
   }
   return 1;
}

/******************************************************************************/

void saveData(const char *file, record &problems)
{
   std::ofstream out(file);
//  if(!out) return 0;

   field *fieldPt=(field *)(problems.next());
   while(fieldPt!=NULL)
   {
      field *field2Pt=(field *)(((record *)(fieldPt->value))->next());
      while(field2Pt!=NULL)
      {
         frstring value=*(frstring *)(field2Pt->value);
         out << *(frstring *)field2Pt << "=" << value;
         field2Pt=(field *)(field2Pt->next());
      }
      out << "\n\n";
      fieldPt=(field *)(fieldPt->next());
   }
}


/******************************************************************************/

void initializePd(problemData &pd, record &rec)
{
   DVector vv;

   pd.dynSysName="noName";
   pd.testType="noTestType";
   pd.initialSize=0.005;
   pd.step=0.01;
   pd.blowuplimit=100;
   pd.blowuptime=10.0;
   pd.iteratetime=10;

   capd::krak::link *l=rec.next();
   while(l != NULL)
   {
      field &v=*(field *)l;
      frstring val=*(frstring *)(v.value);
      frstring key=v;
//rootFrame << At(30,0) << "Got: " << v << "====" << val << "#####";
//waitBt();
      if(key == "dynSysName") pd.dynSysName=val.getFirstItem();
      if(key == "testType") pd.testType=val.getFirstItem();
      if(key == "size") val >> pd.initialSize;
      if(key == "starting_point")
      {
         std::istringstream str(val.string());
         str >> vv;
         pd.initialVector = IVector(vv);
      }
      if(key == "step") val >> pd.step;
      if(key == "blowup_limit") val >> pd.blowuplimit;
      if(key == "iterate_time") val >> pd.iteratetime;
      if(key == "blowup_time") val >> pd.blowuptime;
      if(key == "required_expansion") val >> pd.expansion;
      if(key == "max_expansion") val >> pd.max_expansion;
      if(key == "min_loc_expansion") val >> pd.min_loc_expansion;
      if(key == "max_loc_expansion") val >> pd.max_loc_expansion;
      if(key == "min_z") val >> pd.min_z;
      if(key == "max_z") val >> pd.max_z;
      l=l->next();
   }
   for(int i=0;i<DIM;i++)
      pd.initialBox[i]=Interval(-pd.initialSize,pd.initialSize);
}

/******************************************************************************/

void add_problem(record &where)
{
   frstring name,nnn;
   nnn="name";
   name=(!current_problem[nnn]).getFirstItem();
   record *r=(record *)(current_problem.copy());
   where.addfield(name,*r);
}

/******************************************************************************/

void initialize_problem(record &rec)
{
   field *f=(field *)problems.first();
   rec=*(record *)((f->value)->copy());
}

/******************************************************************************/

void select_problem(frstring &control)
{
   current_problem=*(record *)(problems[control].value->copy());

   if(!job::rootJob->exists(edit_problem_job))
   {
      edit_problem_job=new ed_rec_job("Edit problem",current_problem,
                  Frame(rootFrame,55,25,99,50,BLUE,WHITE));
      edit_problem_job->launch();
   }else{
      job::requestedJob=edit_problem_job;
   }
}

/******************************************************************************/

void process_menu(frstring &control)
{
   if(control == SELECT)
   {
      if(!job::rootJob->exists(select_problem_job))
      {
         select_problem_job=new menu_job("Select problem",*(list *)&problems,
                    Frame(rootFrame,55,0,80,25,BLUE,WHITE),select_problem,0);
         select_problem_job->launch();
      }else{
         job::requestedJob=select_problem_job;
      }
   }
   if(control == MAKETEST)
   {
      initializePd(pd,current_problem);
      makeTest();
   }
   if(control == CHANGEPAR)
   {
      if(!job::rootJob->exists(edit_problem_job))
      {
         edit_problem_job=new ed_rec_job("Edit problem",current_problem,
                    Frame(rootFrame,55,25,99,50,BLUE,WHITE));
         edit_problem_job->launch();
      }else{
         job::requestedJob=edit_problem_job;
      }
   }
   if(control == ADD)
   {
      Frame frm(rootFrame, 30,30,60,60);
      if(confirm(frm,"Add problem?","YES","NO"))
      {
         add_problem(problems);
         if(job::rootJob->exists(select_problem_job))
                                          select_problem_job->terminate();
         select_problem_job=new menu_job("Select problem",*(list *)&problems,
                  Frame(rootFrame,55,0,80,25,BLUE,WHITE),select_problem,0);
         select_problem_job->launch();
      }
   }
   if(control == SORT)
   {
      Frame frm(rootFrame, 30,30,60,60);
      if(confirm(frm,"Sort problems?","YES","NO")) problems.sort();
      if(job::rootJob->exists(select_problem_job))
         select_problem_job->terminate();
      select_problem_job=new menu_job("Select problem",*(list *)&problems,
                  Frame(rootFrame,55,0,80,25,BLUE,WHITE),select_problem,0);
      select_problem_job->launch();
   }
   if(control == SAVE)
   {
      Frame frm(rootFrame, 30,30,60,60);
      if(confirm(frm,"Save problems?","YES","NO"))
         saveData("problems.txt",problems);
   }
   if(control == QUIT)
   {
      job::message="finish";
   }
   if(control == ERROR)
   {
//    cerr << "Error!\n";
   }
}

/******************************************************************************/

void job_main_loop(void)
{
   list menu_list;
   menu_list+CHANGEPAR+ADD+SELECT+MAKETEST+SORT+SAVE+QUIT+ERROR;

   if(!processInputData(problems))
      errorExit("No problems found!");
   initialize_problem(current_problem);
//current_problem.~record();

//  rootFrame << At(10,0) << problems.description();
//  rootFrame << At(10,0) << current_problem.description();
//  waitBt();

   do_menu = new menu_job("Menu",menu_list,Frame(rootFrame,80,0,99,25,BLUE,WHITE),process_menu,1);

   job::requestedJob=do_menu;
   do_menu->launch();
   job::mainLoop();

  //exit(0);
}

/******************************************************************************/
// the old style input data routine

void inputData(int example)
{
   int i;
   DVector vv;
   frstring waste;

   for(i=0;i<example;i++)
   {
      gettoken(inp,waste);
      gettoken(inp,waste);
      gettoken(inp,waste);

      gettoken(inp,waste);
      gettoken(inp,waste);
      gettoken(inp,pd.dynSysName);

      gettoken(inp,waste);
      gettoken(inp,waste);
      gettoken(inp,pd.testType);

      gettoken(inp,waste);
      gettoken(inp,waste);
      inp >> pd.initialSize;

      gettoken(inp,waste);
      gettoken(inp,waste);
      inp >> vv;

      gettoken(inp,waste);
      gettoken(inp,waste);
      inp >> pd.step;

      gettoken(inp,waste);
      gettoken(inp,waste);
      inp >> pd.blowuplimit;

      gettoken(inp,waste);
      gettoken(inp,waste);
      inp >> pd.blowuptime;

      gettoken(inp,waste);
      gettoken(inp,waste);
      inp >> pd.iteratetime;

      gettoken(inp,waste);
      gettoken(inp,waste);
      inp >> pd.max_expansion;

      gettoken(inp,waste);
      gettoken(inp,waste);
      inp >> pd.min_loc_expansion;

      gettoken(inp,waste);
      gettoken(inp,waste);
      inp >> pd.max_loc_expansion;

      gettoken(inp,waste);
      gettoken(inp,waste);
      inp >> pd.min_z;

      gettoken(inp,waste);
      gettoken(inp,waste);
      inp >> pd.max_z;
   }

   pd.initialVector=IVector(vv);
   for(i=0;i<DIM;i++)
      pd.initialBox[i]=Interval(-pd.initialSize,pd.initialSize);
}

/******************************************************************************/

void makeTest(void)
{
#if DIM==3
   IDynSys *ds=NULL;

   int itno=0; // iterates for sectionTest only for Henon

   Lorenz lorenz(10,28,2.6666666);
   Rossler rossler(5.7,0.2);
   KurSiva kursiva(1.0,1.0);
   lor=&lorenz;

   IOdeNumTaylor lorenzNumTaylor(lorenz,5,pd.step);
   IOdeNumTaylor rosslerNumTaylor(rossler,5,pd.step);
   IOdeNumTaylor kursivaNumTaylor(kursiva,5,pd.step);
   Henon3 henon(1.4,0.3);
//   VLin3D lin(1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0); // exp na pierwszej
//   wspolrzednej - 04/01/99 - dobrze sie liczyl, blowUp
//   VLin3D lin(0.0,-1.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0);  // oscylator harmoniczny
//   blowUp dobrze sie policzyl


   VLin3D lin(0.0,-1.0,0.0,1.0,0.2,0.0,0.0,0.0,0.0); // powoli rozkrecajaca
    // sie spirala jak dla Rosslera - blowup dobrze sie policzyl

//   Linear3d lin(1.0,1.0,-1.0,0.0,1.0,1.0,0.0,0.0,1.0);


   IOdeNumTaylor lin3dNumTaylor(lin,5,pd.step);


   if(pd.dynSysName=="lorenz")ds=&lorenzNumTaylor;
   if(pd.dynSysName=="rossler")ds=&rosslerNumTaylor;
   if(pd.dynSysName=="kursiva")ds=&kursivaNumTaylor;
   if(pd.dynSysName=="henon")ds=&henon;
   if(pd.dynSysName=="lin")ds=&lin3dNumTaylor;

   if(pd.dynSysName == "lorenz") pd.initialVector[2]=lorenz.getR()-1.;

   if(pd.dynSysName == "lorenz") section_form=lorenz_form;
   if(pd.dynSysName == "rossler") section_form=rossler_form;
   if(pd.dynSysName == "kursiva") section_form=kursiva_form;
   if(pd.dynSysName == "lin") section_form=lin_form;
   if(pd.dynSysName == "henon") itno=7;



//   C0Set::blowUpLimit=pd.blowuplimit;
   lorenzNumTaylor.setRoughEnclosureOrder(1);
   rosslerNumTaylor.setRoughEnclosureOrder(1);
   kursivaNumTaylor.setRoughEnclosureOrder(1);

   if(pd.testType=="iterate")
   {
      int drawingFramesRC=50;
      dynFrame.Locate(rootFrame,drawingFramesRC,50,99,99);
      trajectoryFrame.Locate(rootFrame,0,0,drawingFramesRC,20);
      expansionFrame.Locate(rootFrame,0,20,drawingFramesRC,40);
      localExpansionFrame.Locate(rootFrame,0,40,drawingFramesRC,100);
      trajectoryFrame.Clear();
      trajectoryFrame << "z - coordinate versus time";
      expansionFrame.Clear();
      expansionFrame << "expansion versus time";
      localExpansionFrame.Clear();
      localExpansionFrame << "local expansion versus time";
   }

   dynFrame.Clear();
   dynFrame << At(0,0) << "Test: " << pd.testType <<
               "  IDynSys: " << pd.dynSysName << "\nInitial point: " << pd.initialVector <<
               "  Box size: " << 2*pd.initialSize  << "       \n\n";

   dynFrame.Bound();

   raport << "------------------------------------" << std::endl;
   raport << "Test: " << pd.testType <<
               "  IDynSys: " << pd.dynSysName << "\nInitial point: "
          << pd.initialVector <<
       "  Box size: " << 2*pd.initialSize << "   Step:" << pd.step <<  "\n\n";



   if(pd.testType=="blowUp") blowUpTest(*ds);
   if(pd.testType=="iterate") iterateTest(*ds);
   if(pd.testType=="subdivision") subdivisionTest(*ds);
   if(pd.testType=="section") sectionTest(*ds,section_form,itno);
   if(pd.testType=="parallel") parallelTest(*ds);
#endif
   capd::rounding::DoubleRounding::roundNearest();
}

/******************************************************************************/

int main(int argc, char* argcv[])
{

   int example = 0;
   char c;

   int width=800,height=600;
#if defined(LINUX) || defined(SUN_OS)
   width=1000, height=800;
#endif

   openGW( width,height,WHITE,BLACK);
   
   dynFrame.Locate(rootFrame,0,0,70,40);
   inp.open("dane.txt",std::ios::binary);
   if(!inp) rootFrame << "Failed to open inp\n";

   while(inp.peek() == ' ') inp.get();
   if( (c=inp.peek()) >= '0' && c <= '9') inp >> example;

   if(example)
   {
      inputData(example);
      makeTest();
      waitBt();
   }else{
      job_main_loop();
   }
   closeGW();

   return 0;
}

/// @}
