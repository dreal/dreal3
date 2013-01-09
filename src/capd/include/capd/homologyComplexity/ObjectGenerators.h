/// @addtogroup 2
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file ObjectGenerators.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Marian Mrozek 2005-2006
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#if !defined(_OBJECTGENERATORS_H)
#define _OBJECTGENERATORS_H

#include <vector>
#include "capd/bitSet/selector.h"
#include "capd/homologyComplexity/SetPairT.h"

template<typename OutObject>
class ObjectGenerator{
  public:
    typedef OutObject ObjectType;
    virtual CRef<OutObject> getObjectCR(int s) const=0;
    virtual ~ObjectGenerator(){}
};

template<typename InObject, typename OutObject>
class RescaledObjectGenerator : public ObjectGenerator<OutObject>{
  public:
    typedef OutObject ObjectType;
    RescaledObjectGenerator(CRef<InObject> A_inObjectCR):m_baseInObjectCR(A_inObjectCR){}
    CRef<ObjectType> getObjectCR(int s) const{
      InObject baseInObjectCopy( m_baseInObjectCR() );
      baseInObjectCopy.rescale(s);
      return CRef<OutObject>(new OutObject(baseInObjectCopy) )  ;
    }
  private:
    CRef<InObject> m_baseInObjectCR;
};

template<typename InObject, typename OutObject>
class RescaledD2ObjectGenerator : public ObjectGenerator<OutObject>{
  public:
    typedef OutObject ObjectType;
    RescaledD2ObjectGenerator(CRef<InObject> A_inObjectCR):m_baseInObjectCR(A_inObjectCR){}
    CRef<ObjectType> getObjectCR(int s) const{
      int dim=m_baseInObjectCR().embDim();
      std::vector<int> sc(dim);
      sc[0]=sc[1]=s;
      for(int i=2;i<dim;++i) sc[i]=1;
      InObject baseInObjectCopy( m_baseInObjectCR() );
      baseInObjectCopy.rescale(&sc[0]);
      return CRef<OutObject>(new OutObject(baseInObjectCopy) )  ;
    }
  private:
    CRef<InObject> m_baseInObjectCR;
};

template<typename InObject, typename OutObject>
class RescaledPairObjectGenerator: public ObjectGenerator<SetPairT<OutObject> >{
  public:
    typedef SetPairT<OutObject> ObjectType;
    RescaledPairObjectGenerator(
      CRef<InObject> A_inSubObjectCR,
      CRef<InObject> A_inSupObjectCR
    ):
      m_baseInSubObjectCR(A_inSubObjectCR),
      m_baseInSupObjectCR(A_inSupObjectCR)
    {}
    CRef<ObjectType> getObjectCR(int s) const{
      InObject baseInSubObjectCopy( m_baseInSubObjectCR() );
      InObject baseInSupObjectCopy( m_baseInSupObjectCR() );
      baseInSubObjectCopy.rescale(s);
      baseInSupObjectCopy.rescale(s);
      return CRef<ObjectType>(new ObjectType(CRef<OutObject>(new OutObject(baseInSubObjectCopy) ),CRef<OutObject>(new OutObject(baseInSupObjectCopy) ) ) );
    }
  private:
    CRef<InObject> m_baseInSubObjectCR,m_baseInSupObjectCR;
};

template<typename InObject, typename OutObject>
class SubObjectGenerator : public ObjectGenerator<OutObject>{
  public:
    typedef OutObject ObjectType;
    SubObjectGenerator(CRef<InObject> A_inObjectCR):m_baseInObjectCR(A_inObjectCR),stripDepth(A_inObjectCR().embDim()){}
    SubObjectGenerator(CRef<InObject> A_inObjectCR,int A_stripDepth):m_baseInObjectCR(A_inObjectCR),stripDepth(A_stripDepth){}
    CRef<ObjectType> getObjectCR(int s) const{
      int dim=m_baseInObjectCR().embDim();
      std::vector<int> lc(dim),uc(dim);
      for(int i=0;i<dim;++i){
        int width=m_baseInObjectCR().getUnpaddedWidth(i);
        // In this convention s must be negative or zero,
        // because we gradually strip the big set of margin of size -s
        if(s>0 || 2*s <= 1-width){
          std::string s;
          s << "SubObjectGenerator: scale is " << s << " and must be between " << (1-width)/2. << " and 0\n";
          throw std::runtime_error(s.c_str());
        }
        if(i>=stripDepth) s=0;
        lc[i]=-s;
        uc[i]=width+s-1;
      }
      return CRef<OutObject>(new OutObject(m_baseInObjectCR(),lc,uc) )  ;
    }
  private:
    CRef<InObject> m_baseInObjectCR;
    int stripDepth;
};

template<typename InObject, typename OutObject>
class LinearSubObjectGenerator : public ObjectGenerator<OutObject>{
  public:
    typedef OutObject ObjectType;
    LinearSubObjectGenerator(CRef<InObject> A_inObjectCR):m_baseInObjectCR(A_inObjectCR){}
    CRef<ObjectType> getObjectCR(int s) const{
      // In this convention s must be negative or zero,
      // because we gradually strip the big set of margin of size -s
      int dim=m_baseInObjectCR().embDim();
      int width=m_baseInObjectCR().getUnpaddedWidth(dim-1);
      if(2*s > width-1){
        std::string s;
        s << "LinearSubObjectGenerator: scale is " << s << " and must be between 0 and " << (width-1)/2 << "\n";
        throw std::runtime_error(s.c_str());
      }
      std::vector<int> lc(dim),uc(dim);
      for(int i=0;i<dim;++i){
        lc[i]=0;
        uc[i]= (i==dim-1 ? 2*s : m_baseInObjectCR().getUnpaddedWidth(i)-1);
      }
      return CRef<OutObject>(new OutObject(m_baseInObjectCR(),lc,uc) )  ;
    }
  private:
    CRef<InObject> m_baseInObjectCR;
};

// This object generator was designed specifically for bitmaps of 128 pixels in each direction
// s>=8 means no masks will be inserted.
template<typename InObject, typename OutObject>
class MaskedObjectGenerator : public ObjectGenerator<OutObject>{
  public:
    typedef OutObject ObjectType;
    MaskedObjectGenerator(CRef<InObject> A_inObjectCR):m_baseInObjectCR(A_inObjectCR){}
    CRef<ObjectType> getObjectCR(int s) const{
      CRef<ObjectType> resultCR=CRef<ObjectType>(new ObjectType(m_baseInObjectCR()) );
      int freq = 1 << s;
      int value=(s<=7 ? 0 : 100000);
      HiperSurfSelector selector(0,freq,value);
      resultCR().add(selector);
      return resultCR;
    }
  private:
    CRef<InObject> m_baseInObjectCR;
};

template<typename InObject, typename OutObject>
class ShiftedObjectGenerator : public ObjectGenerator<OutObject>{
  public:
    typedef OutObject ObjectType;
    ShiftedObjectGenerator(CRef<InObject> A_inObjectCR):m_baseInObjectCR(A_inObjectCR){}
    CRef<ObjectType> getObjectCR(int s) const{
      int dim=m_baseInObjectCR().embDim();
      std::vector<int> w(dim),jump(dim);
      for(int i=0;i<dim;++i){
        jump[i]=m_baseInObjectCR().getUnpaddedWidth(i)-1;
        w[i]=jump[i]*s+1;
      }
      CRef<OutObject> shiftedObjectCR(new OutObject(&w[0]));
      for(typename InObject::PointCoordIterator it=m_baseInObjectCR().begin(); it<m_baseInObjectCR().end();++it){
        // shifts will store all zero-one vectors, beginning from the zero vector
        std::vector<int> shift(dim);
        for(int i=0;i<dim;++i) shift[i]=0;
        // loop through all shifts
        while(true){
          std::vector<int> coord(dim);
          for(int i=0;i<dim;++i) coord[i]=it[i]+shift[i];
          typename InObject::Pixel p(&coord[0]);
          shiftedObjectCR().addPixel(p);
          // prepare next shift
          for(int i=0;i<dim;++i){
            shift[i]+=jump[i];
            if(shift[i]>=w[i]-1){
              shift[i]=0;
            }else{
              goto next;
            }
          }
          // when the for loop manages to complete, all shifts are done, so break the while loop
          break;
          next:;
        }
      }
      return shiftedObjectCR;
    }
  private:
    CRef<InObject> m_baseInObjectCR;
};
#endif //_OBJECTGENERATORS_H


/// @}

