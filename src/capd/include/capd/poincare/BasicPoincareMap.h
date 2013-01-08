/// @addtogroup poincare
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file BasicPoincareMap.h
///
/// @author Daniel Wilczak
/// @author Tomasz Kapela
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2008 by the CAPD Group.
//
// Distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#ifndef _CAPD_POINCARE_BASIC_POINCARE_MAP_H_
#define _CAPD_POINCARE_BASIC_POINCARE_MAP_H_

#include <string>
#include "capd/capd/factrial.h"
#include "capd/capd/TypeTraits.h"

namespace capd{
namespace poincare{

/**
 * Defines constants to specify section crossing direction
 *
 * Section is given zeros of some scalar function.
 * PlusMinus means that we want to cross section comming from positive values
 * and going to negative ones (MinusPlus means opposite direction).
 * Constant None means that we do not specify direction, both are allowed.
 */
enum CrossingDirection { PlusMinus = 1, None = 0, MinusPlus = -1};

/**
 *  BasicPoicareMap class is mainly used for non-rigorous computations of Poincare Map.
 *  For given Dynamical System and section it computes first return map
 *  and its derivatives but non-rigorously (i.e. without handling any computational errors).
 *
 *  Let \f$ \varphi(t, x): R \times R^n -> R^n \f$ be a dynamical system
 *  Let \f$ s: R^n \to R \f$ be a section function,
 *  Let \f$ S = \{x \in R^n : s(x) = 0\} \f$
 *  Let \f$ P: S \to S \f$ be a Poincare Map
 *  For given point \f$ x \in S \f$ let T(x) be first return time (in given crossing direction)
 *  i.e.  \f$ P(x) = \varphi(T(x), x) \in S \f$
 *
 *  In the following we denote by
 *    - dP the derivative of Poincare Map P  : \f$ dP(x) = \frac{\partial P(x)}{\partial x} \f$
 *    - dT the derivative of T(x) : \f$ dT(x)  = \frac{\partial T(x)}{\partial x} \f$
 *    - dF the derivative of the flow : \f$ dF(x) = \frac{\partial \varphi(T(x), x)}{\partial x} \f$
 *  Then
 *    \f$ dP = dF + \frac{\partial \varphi}{\partial t} dT \f$
 *
 *  Parameters:
 *   - DS    dynamical system
 *       - DS::MapType  vector field type
 *   - FunT  - section function type
 *       - FunT should have method gradient()
 *
 */

template <typename DS, typename FunT = typename DS::FunctionType >
class BasicPoincareMap
{
public:
  typedef DS DynamicalSystemType;                     ///< dynamical system type
  typedef typename DS::MapType VectorFieldType;       ///< vector field type
  typedef typename DS::MatrixType MatrixType;         ///< matrix type
  typedef typename DS::VectorType VectorType;         ///< vector type
  typedef typename DS::ScalarType ScalarType;         ///< scalar entries type
  typedef typename TypeTraits<ScalarType>::Real RealType;    ///< floating point type: for floating points is equal to ScalarType, for intervals is a type of their bounds.

  typedef  FunT FunctionType;                         ///< Section function type

  typedef capd::poincare::CrossingDirection CrossingDirection;

  /// Constructor
  BasicPoincareMap(
             DynamicalSystemType  &ds,
             FunctionType & section,
             CrossingDirection direction = None,
             const RealType & errorTolerance = TypeTraits<RealType>::epsilon()*10
        );

  /// Computes value of Poincare Map
  VectorType operator()(VectorType v);  // we copy v to be changed in computations

  /// Computes value of Poincare Map and derivatives of the flow
  VectorType operator()(VectorType v, MatrixType & dF);

  /// Computes Poincare Map and derivatives of the flow to given order
  template <typename CnCoeffType>
  CnCoeffType& operator()(CnCoeffType& result);

  // computations of derivatives of Poincare map from the derivatives of flow

  /// Computes dT from derivative of the flow
  VectorType computeDT(const VectorType& Px, const MatrixType& derivativeOfFlow);

  /// Computes derivative of Poincare Map dP
  MatrixType computeDP(const VectorType& Px, const MatrixType& derivativeOfFlow, const VectorType& dT);

  /// Computes derivative of Poincare Map dP
  MatrixType computeDP(const VectorType& Px, const MatrixType& derivativeOfFlow);

  /// Compute d2T/dx2 only for linear section
  MatrixType computeD2T(
           const VectorType& Px,
           const MatrixType& derivativeOfFlow,
           const VectorType& DT,
           const MatrixType& DP,
           MatrixType hessianOfFlow[]
         );
  /// Compute second derivative of Poincare Map d2P/dx2 only for linear section
  void computeD2P(
           const VectorType& Px,
           const MatrixType& derivativeOfFlow,
           const VectorType& DT,
           const MatrixType& DP,
           MatrixType hessianOfFlow[],
           const MatrixType& D2T,
           MatrixType result[]
      );

  /// Computes a partial derivatives of a Poincare map to an arbitrarily order only for linear section.
  template<typename CnCoeffType>
  CnCoeffType computePartialDerivatives(const CnCoeffType& DPhi);

  DynamicalSystemType & getDynamicalSystem();              ///< Returns dynamical system used
  const DynamicalSystemType & getDynamicalSystem() const;  ///< Returns dynamical system used

  VectorFieldType & getField();               ///< Returns vector field
  const VectorFieldType & getField() const;   ///< Returns vector field

  FunctionType & getSection();                ///< Returns section function
  const FunctionType& getSection() const;     ///< Returns section function

  int getOrder() const;                       ///< Returns order of numerical method used
  ScalarType getStep() const;         ///< Returns time step

  void setOrder(int newOrder);                ///< Sets order of Taylor method
  void setSection(const FunctionType& newSection);  ///< Sets new section function
  void setStep(const ScalarType& newStep);    ///< Sets time step for integration of DS
  void setFactor(double newFactor);           ///

  void setSectionOrder(unsigned a_order){ m_sectionOrder=a_order; }

  void turnOnStepControl()
  {
    m_stepControl = true;
  }

  void turnOffStepControl()
  {
    m_stepControl = false;
  }

protected:
  DS & m_dynamicalSystem;     ///< dynamical system (e.g. Taylor, C2Taylor or CnTaylor)
  FunctionType & m_section;   ///< section function
  CrossingDirection m_crossingDirection;  ///< wanted direction of section crossing

/// sectionFactor is used in the procedures reachSection and crossSection.
/// IN NONRIGOROUS : we want to be closer than m_sectionFactor after section crossing
/// IN RIGOROUS VERSION: Before and after section crossing  we want the set to be closer to section
/// than sectionFactor * sizeOfSet
  RealType m_sectionFactor;

  int m_sectionOrder;
  int m_dim;                 ///< dimension of the space.
  bool m_stepControl;

}; // end of template PoincareMap

// ------------------------------------------------------------------------------------------

template <typename DS, typename FunT>
inline BasicPoincareMap<DS, FunT>::BasicPoincareMap(
   DynamicalSystemType  & ds,
   FunctionType & section,
   CrossingDirection direction,
   const RealType & errorTolerance
 ) : m_dynamicalSystem(ds),
     m_section(section),
     m_crossingDirection(direction),
     m_sectionFactor(errorTolerance),
     m_sectionOrder(0),
     m_stepControl(true)
{
  m_dim = m_dynamicalSystem.getField().dimension();
}

// -----------------------------------------------------------------------------------------

/**
 * Nonrigorous Poincare map
 *
 * A point just after the section on the nonrigorous trajectory is returned
 * The result contains also approximate values of the partial derivatives
 * of the flow
 */

template <typename DS, typename FunT>
template <typename CnCoeffType>
CnCoeffType& BasicPoincareMap<DS, FunT>::operator()(CnCoeffType& v)
{
  ScalarType sign;
  ScalarType step = m_dynamicalSystem.getStep();

  do{
     m_dynamicalSystem(v);
     sign = m_section(v());
  } while( (sign==0.0) ||                  // We are on the section
         !((m_crossingDirection == None) ||         // section sign is not correct
           ((m_crossingDirection == MinusPlus) && (sign < 0.0)) ||
           ((m_crossingDirection == PlusMinus) && (sign > 0.0))
         ));

//first approach to section
  CnCoeffType beforeSection(m_dim,v.rank());
  while(m_section(v())*sign>0)
  {
      beforeSection = v;
      m_dynamicalSystem(v);
  }

// we approach section with small time steps as close as possible

  int order = m_dynamicalSystem.getOrder(), i;
  for(i=0;i<order;++i)
  {
    VectorType Grad = m_section.gradient(beforeSection());
    VectorType fieldDirection = m_dynamicalSystem.getField()(beforeSection());
    ScalarType approxDistance = abs(section(beforeSection()));
    ScalarType fieldSectionDirection = abs(fieldDirection * Grad);
    ScalarType approxTime = 0.9*approxDistance/fieldSectionDirection;
    if(step<0)
      approxTime = -approxTime;
    m_dynamicalSystem.setStep(approxTime);
    m_dynamicalSystem(beforeSection);
    if (m_section(beforeSection())*sign<=0.)
      break;
  }

  while(m_section(beforeSection())*sign>0)
    m_dynamicalSystem(beforeSection);
  m_dynamicalSystem.setStep(step);
  v = beforeSection;
  return v;
}

// ------------------------------------------------------------------------------------------
/**
 *  Computes a partial derivatives of a Poincare map to an arbitrarily order.
 *
 *  @param PhiSeries  partial derivatives of the flow to a given order
 *
 *  @remark Computations are valid only for linear sections.
 */
template <typename DS, typename FunT>
template<typename CnCoeffType>
CnCoeffType BasicPoincareMap<DS, FunT>::computePartialDerivatives(const CnCoeffType& PhiSeries)
{
  typedef typename CnCoeffType::Multipointer Multipointer;

  const int rank = PhiSeries.rank();
  if(m_dim != PhiSeries.dimension())
      throw std::runtime_error("Incompatible dimensions in BasicPoincareMap::computePartialDerivatives");
  if(rank > this->m_dynamicalSystem.getRank())
      throw std::runtime_error("Incompatible orders in BasicPoincareMap::computePartialDerivatives");

  CnCoeffType PSeries(m_dim,rank); // result
  PSeries() = PhiSeries();
  if(rank<=0)
    return PSeries;

// fieldOnPx contains a series of vectorField computed at Px
  const typename DS::SeriesContainerType& DtPhiSeries = m_dynamicalSystem.computeDaPhi(PhiSeries,rank+1);

  VectorType gradientOnPx = m_section.gradient(PhiSeries());
  VectorType fieldOnPx =  getField()(PhiSeries());
  ScalarType scalarProduct = - gradientOnPx * fieldOnPx;

// first we compute separately dt/dx
  CnCoeffType TSeries(m_dim,rank);
  int i,j,k,s,p;
  for(j=0;j<m_dim;++j)
      for(i=0;i<m_dim;++i)
        TSeries(0,j) += gradientOnPx[i] * PhiSeries(i,j);
  for(j=0;j<m_dim;++j)
      TSeries(0,j) /= scalarProduct;

// and we compute dP/dx
  for(i=0;i<m_dim;++i)
      for(j=0;j<m_dim;++j)
        PSeries(i,j) = fieldOnPx[i]*TSeries(0,j) + PhiSeries(i,j);

// recursive computation of higher order partial derivatives
  for(p=2;p<=rank;++p)
  {
      Multipointer a = PSeries.first(p);
      do
      {
        VectorType temp = PhiSeries(a);
        VectorType temp2(m_dim);

        for(k=2;k<=p;++k)
        {
            const typename Multipointer::IndicesSet& is = Multipointer::generateList(p,k);
            typename Multipointer::IndicesSet::const_iterator b=is.begin(), e=is.end();
            while(b!=e)
            {
              ScalarType product=TSeries( 0,a.subMultipointer((*b)[0]) );
              for(j=1;j<k;++j)
                  product *= TSeries( 0,a.subMultipointer((*b)[j]) );

              DtPhiSeries.takeVector(Multipointer(0),k,temp2);
              temp += (product*factorial(k)) * temp2;

              for(s=0;s<k;++s)
              {
                  ScalarType product2(1.);
                  for(j=0;j<k;++j)
                    if(j!=s)
                        product2 *= TSeries( 0,a.subMultipointer((*b)[j]) );

                  DtPhiSeries.takeVector(a.subMultipointer((*b)[s]),k-1,temp2);
                  temp += product2*factorial(k-1)*temp2;
              }
              ++b;
        } // end while loop
      } // end k-loop

        TSeries(0,a) = (gradientOnPx*temp)/scalarProduct;
        PSeries(a) = temp + TSeries(0,a)*fieldOnPx;
      }while(PSeries.next(a));
  }

  return PSeries;
}

// -----------------------------------------------------------------------------------------


template <typename DS, typename FunT>
inline const typename BasicPoincareMap<DS, FunT>::DynamicalSystemType&
BasicPoincareMap<DS, FunT>::getDynamicalSystem() const
{
  return m_dynamicalSystem;
}
// -----------------------------------------------------------------------------------------

template <typename DS, typename FunT>
inline typename BasicPoincareMap<DS, FunT>::DynamicalSystemType&
BasicPoincareMap<DS, FunT>::getDynamicalSystem()
{
  return m_dynamicalSystem;
}
// -----------------------------------------------------------------------------------------

template <typename DS, typename FunT>
inline typename BasicPoincareMap<DS, FunT>::VectorFieldType const&
BasicPoincareMap<DS, FunT>::getField() const
{
  return m_dynamicalSystem.getField();
}

// -----------------------------------------------------------------------------------------

template <typename DS, typename FunT>
inline typename BasicPoincareMap<DS, FunT>::VectorFieldType&
BasicPoincareMap<DS, FunT>::getField()
{
  return m_dynamicalSystem.getField();
}

// -----------------------------------------------------------------------------------------

template <typename DS, typename FunT>
inline typename BasicPoincareMap<DS, FunT>::FunctionType const&
BasicPoincareMap<DS, FunT>::getSection() const
{
  return m_section;
}

// -----------------------------------------------------------------------------------------

template <typename DS, typename FunT>
inline typename BasicPoincareMap<DS, FunT>::FunctionType& \
BasicPoincareMap<DS, FunT>::getSection()
{
  return m_section;
}

// -----------------------------------------------------------------------------------------

template <typename DS, typename FunT>
inline int BasicPoincareMap<DS, FunT>::getOrder() const
{
  return m_dynamicalSystem.getOrder();
}

// -----------------------------------------------------------------------------------------

template <typename DS, typename FunT>
inline typename BasicPoincareMap<DS, FunT>::ScalarType
BasicPoincareMap<DS, FunT>::getStep() const
{
  return m_dynamicalSystem.getStep();
}

// -----------------------------------------------------------------------------------------

template <typename DS, typename FunT>
inline void BasicPoincareMap<DS, FunT>::setOrder(int newOrder)
{
  m_dynamicalSystem.setOrder(newOrder);
}

// -----------------------------------------------------------------------------------------

template <typename DS, typename FunT>
inline void BasicPoincareMap<DS, FunT>::setStep(const ScalarType& newStep)
{
  m_dynamicalSystem.setStep(newStep);
}

// -----------------------------------------------------------------------------------------

template <typename DS, typename FunT>
inline void BasicPoincareMap<DS, FunT>::setFactor(double newFactor)
{
  m_sectionFactor = newFactor;
}

// -----------------------------------------------------------------------------------------

template <typename DS, typename FunT>
inline void BasicPoincareMap<DS, FunT>::setSection(const FunctionType& newSection)
{
  m_section = newSection;
}

/*  Expected interfaces of DS and FunT
 *
template <typename FunT>
class DynamicalSystemInterface{
  // Following internal types should be defined
  typedef FunT MapType;
  typedef typename MapType::MatrixType MatrixType;
  typedef typename MapType::VectorType VectorType;
  typedef typename MapType::ScalaType ScalarType;

  virtual MapType getField() = 0;
  void setField(MapType &) = 0;
  int  getOrder() = 0;
  void setOrder(int) = 0;
  ScalarType getStep() =0;
  void setStep(ScalarType) = 0;
  // NOT FINISHED
};


class SectionInterface{
  class FunctionType{
    virtual SectionInterface gradient() = 0;

  };
  // NOT FINISHED
};*/

}} // namespace capd::poincare


#endif  /* _BasicPoincareMap_H */

/// @}
