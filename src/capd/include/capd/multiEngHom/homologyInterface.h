/// @addtogroup multiEngHom
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file homologyInterface.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Marian Mrozek 2005-2006
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#include "capd/auxil/CRef.h"
#include "capd/homologicalAlgebra/HomologySignature.h"
#include "capd/homology/homology.h"
#include "capd/auxil/stringOstream.h"



/***
     Conversion from EuclBitSetT used in this
     package to SetOfCubes used in homology package
***/
template <typename P_CubSet>
void makeSet(P_CubSet const& set, capd::homology::SetOfCubes& Xcubes){
  using namespace capd::homology;
  for(typename P_CubSet::PointCoordIterator it=set.begin();it<set.end();++it){
    int dim=set.embDim();
    std::vector<coordinate> c(dim);
    for(int d=0;d<dim;++d){
      c[d]=it[d];
    }
    Cube cb(&c[0],dim);   // For some reason this call to Pilarczyk's homology library sometimes fails without any warning
    Xcubes.add(cb);
  }
}

/***
     Generate a multivalued representation of the inclusion map
***/

template <typename P_CubSet>
void makeMVInclusionMap(P_CubSet const& set, capd::homology::CombinatorialMultivaluedMap& Fcubmap){
  using namespace capd::homology;
  for(typename P_CubSet::PointCoordIterator it=set.begin();it<set.end();++it)
  if(it.getBit()){
    int dim=set.embDim();
    std::vector<coordinate> c(dim);
    for(int d=0;d<dim;++d) c[d]=it[d];
    Fcubmap[Cube(&c[0],dim)].add(Cube(&c[0],dim));
  }
}

/***
     Homology Computations based on the Homology package
     Uses the above functions to convert sets
     Returns generators
***/
template <typename P_CubSet>
int getHomology(
    const P_CubSet& X,     // set X
    capd::homology::Chain *&hom,            // pseudo chain with computted Betti numbers (?)
    capd::homology::Chain **&gen,           // reference to table of table of generators
    capd::homology::CubicalComplex *&gcompl // reference to table of geometric form of generators
){
  using namespace capd::homology;
  SetOfCubes Xcubes;
  makeSet(X,Xcubes);

  // compute the homology of the set
// Previous version:
//  int maxlevel = Homology (Xcubes, "X", hom, &gen, &gcompl);

// New version (modified by Pawel Pilarczyk on March 28, 2006):
// Without computing homology generators.
  int maxlevel = Homology (Xcubes, "X", hom);

  return maxlevel;
}

/***
     Relative Homology Computations based on the Homology package
     Uses the above functions to convert sets
     Returns generators
***/
template<typename P_CubSet>
int getRelativeHomology(
    const P_CubSet& X,     // set X
    const P_CubSet& A,     // subset A
    capd::homology::Chain *&hom,            // pseudo chain with computted Betti numbers (?)
    capd::homology::Chain **&gen,           // reference to table of table of generators
    capd::homology::CubicalComplex *&gcompl // reference to table of geometric form of generators
){
  using namespace capd::homology;
  SetOfCubes Xcubes, Acubes;
//fcout << "getRelativeHomology Here 0" << std::endl;;
  makeSet(X,Xcubes);
  makeSet(A,Acubes);

  // compute the homology of the pair
//fcout << "getRelativeHomology Here 1" << std::endl;;
  int maxlevel = Homology (Xcubes, "X", Acubes, "A", hom, &gen, &gcompl);
//fcout << "getRelativeHomology Here 2" << std::endl;;
  return maxlevel;
}


/***
     Homology Index Map computation based on the Homology package
     Uses the above functionss to convert sets and maps
     Returns the matrix of the homology map
***/

template <typename P_CubSet>
CRef<std::vector<capd::vectalg::Matrix<int,0,0> > >
getHomologyInclusionMap(
   P_CubSet const& X,                                    // domain X
   P_CubSet const& A,                                    // domain X0
   P_CubSet const& Y,                                    // codomain Y
   P_CubSet const& B,                                    // codomain Y0
   int& maxlevel_cx, int& maxlevel_cy,
   capd::homology::Chain *&hom_cx, capd::homology::Chain *&hom_cy,
   capd::homology::Chain **&gen_cx, capd::homology::Chain **&gen_cy,
   capd::homology::CubicalComplex *&gcompl_cx,capd::homology::CubicalComplex *&gcompl_cy
){
  using namespace capd::homology;
  CombinatorialMultivaluedMap Fcubmap;
  SetOfCubes Xcubes, Acubes, Ycubes, Bcubes;
  ChainMap *hom_f = NULL;

//  bool inclusion=true;
  bool inclusion=false;
//  bool checkacyclic=true;
  bool checkacyclic=false;
//  bool generators=false;
  bool generators=true;

  makeSet(X,Xcubes);
  makeSet(A,Acubes);
  makeSet(Y,Ycubes);
  makeSet(B,Bcubes);

  makeMVInclusionMap(X,Fcubmap);


  Homology(
    Fcubmap, Xcubes, Acubes, Ycubes, Bcubes,
    hom_cx, maxlevel_cx, hom_cy, maxlevel_cy, hom_f,
    inclusion, checkacyclic ? 0x03 : 0x01,
    (generators && !inclusion) ? &gen_cx : NULL,
    (generators && !inclusion) ? &gcompl_cx : NULL,
    generators ? &gen_cy : NULL, generators ? &gcompl_cy : NULL
  );
  CRef<std::vector<capd::vectalg::Matrix<int,0,0> > > mCR( new std::vector<capd::vectalg::Matrix<int,0,0> >() );
  for(int q=0;q<=maxlevel_cx;++q){
    int nRows=(*hom_f)[q].getnrows();
    int nCols=(*hom_f)[q].getncols();
    mCR().push_back(capd::vectalg::Matrix<int,0,0>(nRows,nCols));
    for(int i=0;i<nRows;i++){
      for(int j=0;j<nCols;j++){
      integer ii=(*hom_f)[q].get(i,j);
      int iii=*(signed short *)(&ii);
        mCR()[q](i+1,j+1)=iii;
      }
    }
  }

  // release the memory and finish
  if (hom_f) delete hom_f;
  fcout  << "Leaving" << endl;

  return mCR;
}

template <class euclidom>
inline int extractBetti(const capd::homology::chain<euclidom> &c){
  using namespace capd::homology;
  int countfree = 0;
  // count invertible coefficients
  for (int i=0; i<c.size();i++) if(c.coef(i).delta() == 1) ++countfree;
  return countfree;
}

template <class euclidom>
string groupToString(const capd::homology::chain<euclidom> &c){
  using namespace capd::homology;
  ostringstream result;
  int countfree = 0;
  bool writeplus = false;

  // write the homology module exactly in the order it appears in 'c'
  for(int i=0;i<c.size();++i){
    // if the coefficient is invertible, it will be shown later
    if (c.coef(i).delta()==1){
      countfree ++;
    // otherwise show the corresponding torsion part now
    }else{
      result << (writeplus ? " + " : "") << euclidom::ringsymbol() << "_" << c.coef(i);
      writeplus = true;
    }

    // if there were some free ingredients show them if necessary
    if( countfree && ((i==c.size()-1) || (c.coef(i+1).delta()!=1)) ){
      result << (writeplus ? " + " : "") << euclidom::ringsymbol ();
      if (countfree > 1) result << "^" << countfree;
      countfree = 0;
      writeplus = true;
    }
  }
  // if there was nothing to show, then just show zero
  if(!c.size()) result << "0";
  return result.str();
}

template <class euclidom>
string homologyToString(const capd::homology::chain<euclidom> *hom, int maxlevel){
  using namespace capd::homology;
  if (!hom) return "";
  ostringstream result;
  for(int q=0;q<=maxlevel;++q){
    result << "H_" << q << " = " << groupToString(hom [q]) << endl;
  }
  return result.str();
}

template <typename P_CubSet>
std::string homologyViaHomologyPackage(const P_CubSet& A_cubSet){
  capd::homology::Chain *hom;            // pseudo chain with computted Betti numbers
  capd::homology::Chain **gen=0;         // reference to table of table of generators
  capd::homology::CubicalComplex *gcompl=0;
  int maxlevel=getHomology<P_CubSet>(A_cubSet,hom,gen,gcompl);
  return homologyToString(hom,maxlevel);
}


template <typename P_CubSet>
CRef<HomologySignature<int> > homologyViaHomologyPackage(CRef<P_CubSet> A_setCR){
  std::vector<int> betti(A_setCR().embDim() + 1,0);
  capd::homology::Chain *hom;            // pseudo chain with computted Betti numbers
  capd::homology::Chain **gen=0;         // reference to table of table of generators
  capd::homology::CubicalComplex *gcompl=0;
  int maxlevel=getHomology<P_CubSet>(A_setCR(),hom,gen,gcompl);
  for(int i=0;i<=maxlevel;++i) betti[i]=extractBetti(hom[i]);
  return CRef<HomologySignature<int> >(new HomologySignature<int> (betti));
}

template <typename P_CubSet>
std::string inclHomologyViaHomologyPackage(CRef<P_CubSet> A_subSetCR,CRef<P_CubSet> A_supSetCR){
  P_CubSet empty(A_subSetCR());
  empty.clear();
  int maxlevel_cx;
  int maxlevel_cy;
  capd::homology::Chain *hom_cx;
  capd::homology::Chain *hom_cy;
  capd::homology::Chain **gen_cx=0;
  capd::homology::Chain **gen_cy=0;
  capd::homology::CubicalComplex *gcompl_cx=0;
  capd::homology::CubicalComplex *gcompl_cy=0;
  CRef<std::vector<capd::vectalg::Matrix<int,0,0> > > mCR=getHomologyInclusionMap(
    A_subSetCR(),
    empty,
    A_supSetCR(),
    empty,
    maxlevel_cx,maxlevel_cy,
    hom_cx,hom_cy,
    gen_cx,gen_cy,
    gcompl_cx,gcompl_cy
  );
  std::string s;
  for(unsigned int q=0;q<mCR().size();++q){
    s << "Inclusion homology matrix in dimension " << q << " is\n";
    s << mCR()[q] << "\n";
  }
  return s;
}


/// @}

