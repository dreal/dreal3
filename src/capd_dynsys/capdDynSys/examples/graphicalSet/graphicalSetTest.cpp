
#include <cmath>
#include <stdexcept>
#include <fstream>

#include "capd/krak/krak.h"
#include "capd/intervals/lib.h"
#include "capd/vectalg/Vector.hpp"
#include "capd/vectalg/Matrix.hpp"
#include "capd/vectalg/Norm.hpp"

#include "capd/map/Function.hpp"
#include "capd/map/CnMap.hpp"
#include "capd/map/Map.hpp"

#include "capd/dynsys/BasicTaylor.hpp"
#include "capd/dynsys/Taylor.hpp"

#include "capd/dynset/C1Rect2Set.hpp"
#include "capd/dynset/C0Rect2Set.hpp"
#include "capd/dynset/C0RectSet.hpp"
#include "capd/dynset/IntervalSet.hpp"
#include "capd/dynset/Intv2Set.hpp"
#include "capd/dynset/C2Rect2.hpp"

const int DIMENSION=0;

typedef capd::DInterval interval;

typedef capd::vectalg::Vector<double,DIMENSION> FloatVector;
typedef capd::vectalg::Matrix<double,DIMENSION,DIMENSION> FloatMatrix;

typedef capd::vectalg::Vector<interval,DIMENSION> IntervalVector;
typedef capd::vectalg::Matrix<interval,DIMENSION,DIMENSION> IntervalMatrix;
typedef capd::vectalg::EuclLNorm<IntervalVector,IntervalMatrix> ELNorm;

typedef capd::map::Function<IntervalVector> Function;
typedef capd::map::CnMap<IntervalMatrix> Map;


typedef capd::dynsys::DynSys<IntervalMatrix> DynSys;
typedef capd::dynsys::Taylor<Map> Taylor;
typedef capd::dynsys::BasicTaylor<capd::map::Map<FloatMatrix> > BasicTaylor;

typedef capd::dynset::C0Set<IntervalMatrix> C0Set;
typedef capd::dynset::C1Set<IntervalMatrix> C1Set;

typedef capd::dynset::IntervalSet<IntervalMatrix> IntvSet;
typedef capd::dynset::C0RectSet<IntervalMatrix> C0RectSet;
typedef capd::dynset::C0Rect2Set<IntervalMatrix> C0Rect2Set;
typedef capd::dynset::C1Rect2Set<IntervalMatrix> C1Rect2Set;
typedef capd::dynset::Intv2Set<IntervalMatrix> Intv2Set;
typedef capd::dynset::C2Rect2<IntervalMatrix> C2rect2;


#include "capd/dynset/C1GraphicalSet.h"
#include "capd/dynset/C0GraphicalSet.h"

template <typename SetType>
class GraphicalOutput{
public:
  GraphicalOutput(Frame &fr, int color = GREEN, int freqency=1)
	  : m_fr(fr), m_color(color), m_freqency(freqency), m_count(0){
  }
  void show(const SetType & set){
	  if((m_count++ % m_freqency) ==0){
		  IntervalVector w = IntervalVector(set);
		  m_fr.boxFill(w[0].leftBound(),w[1].leftBound(),w[0].rightBound(),w[1].rightBound(),m_color);
		  m_fr.box(w[0].leftBound(),w[1].leftBound(),w[0].rightBound(),w[1].rightBound());
	  }
  }
private:
  Frame &m_fr;
  int m_color;
  int m_freqency;
  int m_count;
};
typedef capd::dynset::C1GraphicalSet<IntervalMatrix, GraphicalOutput<C1Set> > C1GraphicalSet;
typedef capd::dynset::C0GraphicalSet<IntervalMatrix, GraphicalOutput<C0Set> > C0GraphicalSet;


double minx=-2.6;
double maxx=2.6;
double miny=-2.6;
double maxy=2.6;

Frame fr[4], txt;

void axes(Frame &fr, double minx, double miny, double maxx, double maxy)
{
   fr.setWorldCoord(minx,miny,maxx,maxy);
   fr.Clear();
   fr.line(0.0,miny,0.0,maxy,BLACK);
   fr.line(minx,0.0,maxx,0.0,BLACK);
}

// uncomment the following line if you wish to wait for a key after each step
#define _WAIT_FOR_KEY_

int readKey() {
  int s=NO_KEY;  UserMove um;
#ifdef _WAIT_FOR_KEY_
  while(NO_KEY==s)
#endif
  {   GetUserMove(um);
      s=um.key;
  }
  return s;
}

// -------------------------------------------------------------------------

void initGraph()
{
   openGW(860,610,WHITE,BLACK);
   fr[0] = Frame(5,5,400,300,WHITE,BLACK);
   fr[1] = Frame(400,5,800,300,WHITE,BLACK);
   fr[2] = Frame(5,300,400,600,WHITE,BLACK);
   fr[3] = Frame(400,300,800,600,WHITE,BLACK);
   txt = Frame(5,400,800,860,WHITE,BLACK);
   rootFrame.Clear();
  for(int i =0; i<4; i++)
    axes(fr[i],minx,miny,maxx,maxy);
}


// -------------------------------------------------------------------------
void drawRectangle(std::vector<IntervalVector> & cor, Frame & fr, int color){
  for(int i = 0; i<4; i++){
    for(int j=0; j<4; j++){
      fr.line( cor[i][0].mid().leftBound(), cor[i][1].mid().leftBound(),cor[j][0].mid().leftBound(),cor[j][1].mid().leftBound(), color);
    }
    fr.boxFill(cor[i][0].leftBound(), cor[i][1].leftBound(),cor[i][0].rightBound(), cor[i][1].rightBound(),color,SOLID_P);
  }
}

template<typename T>
void corners(T& head, const T & tail, int i, int dim, std::vector<T> & cor)
{
  if(i < dim)
  {
    head[i] = left(tail[i]);
    corners(head, tail, i+1, dim, cor);
    head[i] = right(tail[i]);
    corners(head, tail, i+1, dim, cor);
    head[i] = tail[i];
  }
  else
  {
    cor.push_back(head);
  }
}


std::vector<IntervalVector> getCorners(const IntervalVector &center,
        const IntervalMatrix &B,
        const IntervalVector &r
) {
  typedef IntervalVector VectorType;
  std::vector<VectorType> cor;
  VectorType v = r;
  corners(v, r, 0, v.dimension(), cor);
  for(std::vector<VectorType>::iterator it = cor.begin(); it != cor.end(); ++it){
    *it = center + B * *it;
  }
  return cor;
}



// -------------------------------------------------------------------------

void makeTests(Taylor &T, const IntervalVector & x0)
{

  fr[0] << "C0GraphicalSet(Intv2Set)";
  C0GraphicalSet set0(new Intv2Set(x0), new GraphicalOutput<C0Set>(fr[0], RED));

  fr[1] << "C0GraphicalSet(C0RectSet)";
  C0GraphicalSet set1(new C0RectSet(x0), new GraphicalOutput<C0Set>(fr[1], BLUE));

  fr[2] << "C0GraphicalSet(C0Rect2Set)";
  C0GraphicalSet set2(new C0Rect2Set(x0), new GraphicalOutput<C0Set>(fr[2],GREEN));

  fr[3] << "C1GraphicalSet(C1Rect2Set)";
  C1GraphicalSet set3(new C1Rect2Set(x0, ELNorm()), new GraphicalOutput<C1Set>(fr[3],BLACK));


  //int colors[] = {RED, BLUE, GREEN, BLACK};
  int s;
  do{
    set0.move(T);
    set1.move(T);
    set2.move(T);
    set3.move(T);
    s=readKey();
  }while(s!=EscKey);
  rootFrame.Clear();
  rootFrame << "C0GraphicalSet(Intv2Set)     size = " << size(IntervalVector(set0)) << "\n\n"
            << "C0GraphicalSet(C0RectSet)    size = " << size(IntervalVector(set1)) << "\n\n"
            << "C0GraphicalSet(C0Rect2Set)   size = " << size(IntervalVector(set2)) << "\n\n"
            << "C1GraphicalSet(C1Rect2Set)   size = " << size(IntervalVector(set3)) << "\n\n";
}

void harmonicOscilator(){
  int order = 5;
  double step = 6.28 / 30.;
  double sizeOfSet = 0.15;
  FloatVector x(2);  x[0] = 1.0;  x[1] = 0.0;


  IntervalVector v(2);
  v[0] = interval(x[0]-sizeOfSet,x[0]+sizeOfSet);
  v[1] = interval(x[1]-sizeOfSet,x[1]+sizeOfSet);

  Map vfield("var:x,y;fun:-y,x;");
  Taylor T(vfield,order,step);

  makeTests(T, v);
}
// -------------------------------------------------------------------------

//int main(int , char*[])
int main(int, char**)
{
  initGraph();

  try
  {
    harmonicOscilator();
    waitBt();

  }catch(std::exception& e)
  {
    std::ofstream plik;
    plik.open("report");
    plik << e.what();
    plik.close();

   rootFrame << "\n\nException caught! See 'report' file for details.";
   waitBt();
  }
  closeGW();
  return 0;
}


/// @}
