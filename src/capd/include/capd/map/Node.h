/// @addtogroup map
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file Node.h
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

/* Author: Daniel Wilczak 2004-2005 */

#ifndef _CAPD_MAP_NODE_H_ 
#define _CAPD_MAP_NODE_H_ 

#include <ostream>

#include "capd/interval/Interval.h"

namespace capd{
namespace map{

template<typename ScalarType>
class Node
{
private:
  Node(const Node & ){}
  void operator=(const Node & ){}
protected:
  int m_maxComputedDerivative;
  int m_order;
  Node(int a_order, Node* a_left, Node* a_right)
   : m_maxComputedDerivative(-1), m_order(a_order), m_links(0), left(a_left), right(a_right)
  {}
  void allocateAndClear();

public:
  void reset();
  typedef ScalarType* iterator;
  typedef const ScalarType* const_iterator;
  int m_links;
  Node *left,*right;              /* left and right leaf of the tree*/
  ScalarType *value;              /* value of leaf */
  virtual ScalarType& operator()(int) = 0;  /* operator or function (+,-,*,/,^,sin,cos,exp,log) */
  virtual void setOrder(int, ScalarType*) = 0;
  virtual bool isConst() const {return false;} 
  int getOrder() const { return m_order; }
  void computeDerivatives(int a_upTo);
    
  ScalarType& operator[](int i){
    return *(value+i);
  }
  
  const ScalarType& operator[](int i) const{
   return *(value+i);
  }

  iterator begin(){
   return value;
  }
  iterator end(){
   return value+m_order;
  }
  
  const_iterator begin() const{
   return value;
  }
  const_iterator end() const{
   return value+m_order;
  }
  virtual ~Node();
};

// -----------------------------------------------------------------------------

template<typename ScalarType>
class UnaryNode : public Node<ScalarType>
{
  public:
  typedef ScalarType* iterator;
  typedef const ScalarType* const_iterator;

  UnaryNode(int a_order, Node<ScalarType>* a_left):
    Node<ScalarType>(a_order,a_left,0)
  {
    this->allocateAndClear();
    if(this->left) ++(this->left->m_links);
  }

  void setOrder(int a_order, ScalarType *a_val)
  {
    if(this->m_order==a_order) return;
    delete [] this->value;
    this->m_order = a_order;
    this->allocateAndClear();
    if(this->left) this->left->setOrder(this->m_order,a_val);
  }

  ~UnaryNode()
  {  
    if( !( --(this->left->m_links)) ) 
      delete this->left;
    delete [] this->value;  
  }
};

// -----------------------------------------------------------------------------

template<typename ScalarType>
class BinaryNode : public Node<ScalarType>
{
  public:
  typedef ScalarType* iterator;
  typedef const ScalarType* const_iterator;

  BinaryNode(int a_order, Node<ScalarType>* a_left, Node<ScalarType>* a_right):
    Node<ScalarType>(a_order,a_left,a_right)
  {
    this->allocateAndClear();
    if(this->left) ++(this->left->m_links);
    if(this->right) ++(this->right->m_links);
  }

  void setOrder(int a_order, ScalarType *a_val)
  {
    if(this->m_order==a_order) return;
    delete [] this->value;
    this->m_order = a_order;
    this->allocateAndClear();
    if(this->left) this->left->setOrder(this->m_order,a_val);
    if(this->right) this->right->setOrder(this->m_order,a_val);
  }

  ~BinaryNode()
  {  
    if( !( --(this->left->m_links)) ) 
      delete this->left;
    if( !( --(this->right->m_links)) ) 
      delete this->right;
    delete [] this->value;  
  }
};

// -----------------------------------------------------------------------------

template<typename ScalarType>
class ConsNode : public Node<ScalarType>
{
public:
  typedef ScalarType* iterator;
  typedef const ScalarType* const_iterator;

  ScalarType& operator()(int i)
  {
    this->m_maxComputedDerivative=i;
    return *(this->value+i);
  }
  void setOrder(int, ScalarType*);
  bool isConst() const {return true;}

  ConsNode(int a_order, ScalarType d);

  ~ConsNode()
  {
   delete [] this->value;
  }
};

// -----------------------------------------------------------------------------

template<typename ScalarType>
class VarNode : public Node<ScalarType>
{
private:
  int m_numberOfVariables;
public:
  typedef ScalarType* iterator;
  typedef const ScalarType* const_iterator;

  ScalarType& operator()(int i)
  {
    this->m_maxComputedDerivative=i;
    return *(this->value+i);
  }
  void setOrder(int, ScalarType*);

  VarNode(int a_order, ScalarType *d, int variable);
  ~VarNode(){}
};

// -----------------------------------------------------------------------------

template<typename ScalarType>
class SinNode : public BinaryNode<ScalarType> // this is binary because sin node requires dual cos node
{
public:
  typedef ScalarType* iterator;
  typedef const ScalarType* const_iterator;

  ScalarType& operator()(int);

  SinNode(int a_order, Node<ScalarType> *L, Node<ScalarType> *R)
    : BinaryNode<ScalarType>(a_order,L,R)
  {}

  ~SinNode(){}
};

// -----------------------------------------------------------------------------

template<typename ScalarType>
class CosNode : public BinaryNode<ScalarType>
{
public:
  typedef ScalarType* iterator;
  typedef const ScalarType* const_iterator;

  ScalarType& operator()(int);

  CosNode(int a_order, Node<ScalarType> *L, Node<ScalarType> *R)
    : BinaryNode<ScalarType>(a_order,L,R)
  {}

  ~CosNode(){}
};

// -----------------------------------------------------------------------------

template<typename ScalarType>
class ExpNode : public UnaryNode<ScalarType>
{
public:
  typedef ScalarType* iterator;
  typedef const ScalarType* const_iterator;

  ScalarType& operator()(int);

  ExpNode(int a_order, Node<ScalarType> *L)
    : UnaryNode<ScalarType>(a_order,L)
  {}

  ~ExpNode(){}
};

// -----------------------------------------------------------------------------

template<typename ScalarType>
class LogNode : public UnaryNode<ScalarType>
{
public:
  typedef ScalarType* iterator;
  typedef const ScalarType* const_iterator;

  ScalarType& operator()(int);

  LogNode(int a_order, Node<ScalarType> *L)
    : UnaryNode<ScalarType>(a_order,L)
  {}
  ~LogNode(){}
};

// -----------------------------------------------------------------------------
// Definitions in Node_invtrig.hpp
// -----------------------------------------------------------------------------

template<typename ScalarType>
class AtanNode : public BinaryNode<ScalarType> // this is binary because atan(u) requires computation of u nad 1+u^2
{
public:
  ScalarType & operator()(int);

  AtanNode(int a_order, Node<ScalarType> *L, Node<ScalarType> *R)
    : BinaryNode<ScalarType>(a_order,L,R){
  }
};

/// asin(x) = sin^{-1}(x)
///
/// It is a binary node because it stores an auxiliary function sqrt1mx2
/// left = x ,    right = sqrt1mx2(x)
template<typename ScalarType>
class AsinNode : public BinaryNode<ScalarType> {
public:
  ScalarType& operator()(int);

  AsinNode(int a_order, Node<ScalarType> *L, Node<ScalarType> *R)
    : BinaryNode<ScalarType>(a_order,L,R){
  }
};

/// acos(x) = cos^{-1}(x)
///
/// It is binary node because it stores auxiliary function
/// left = x ,    right = sqrt1mx2(x)
template<typename ScalarType>
class AcosNode : public BinaryNode<ScalarType> // this is binary because atan(u) requires computation of u nad 1+u^2
{
public:
  typedef ScalarType* iterator;
  typedef const ScalarType* const_iterator;

  ScalarType& operator()(int);

  AcosNode(int a_order, Node<ScalarType> *L, Node<ScalarType> *R)
    : BinaryNode<ScalarType>(a_order,L,R){
  }
};

// -----------------------------------------------------------------------------
template<typename ScalarType, bool isInterval = TypeTraits<ScalarType>::isInterval >
class PowNodeBase{
};

template<typename ScalarType>
class PowNodeBase<ScalarType, false> : public BinaryNode<ScalarType> {
public:
  ScalarType& operator()(int);

  PowNodeBase(int a_order, Node<ScalarType> *L, Node<ScalarType> *R)
    : BinaryNode<ScalarType>(a_order,L,R)
  {}
};

template<typename ScalarType>
class PowNodeBase<ScalarType, true> : public BinaryNode<ScalarType> {
public:
  ScalarType& operator()(int);

  PowNodeBase(int a_order, Node<ScalarType> *L, Node<ScalarType> *R)
    : BinaryNode<ScalarType>(a_order,L,R)
  {}
};

template<typename ScalarType>
class PowNode: public PowNodeBase<ScalarType,  TypeTraits<ScalarType>::isInterval> {
public:
  PowNode(int a_order, Node<ScalarType> *L, Node<ScalarType> *R)
    : PowNodeBase<ScalarType, TypeTraits<ScalarType>::isInterval>(a_order,L,R)
  {}
};

// -----------------------------------------------------------------------------

template<typename ScalarType>
class SqrNode : public UnaryNode<ScalarType>
{
public:
  typedef ScalarType* iterator;
  typedef const ScalarType* const_iterator;

  ScalarType& operator()(int);

  SqrNode(int a_order, Node<ScalarType> *L)
    : UnaryNode<ScalarType>(a_order,L)
  {}

  ~SqrNode(){}
};

// -----------------------------------------------------------------------------

/// Node of u^2+1.
/// Used in recursive formula of atan and acot.
template<typename ScalarType>
class Sqrp1Node : public UnaryNode<ScalarType> {
protected:
  ScalarType zeroCoeff;
public:
  typedef ScalarType* iterator;
  typedef const ScalarType* const_iterator;

  ScalarType& operator()(int);

  Sqrp1Node(int a_order, Node<ScalarType> *L)
    : UnaryNode<ScalarType>(a_order,L)
  {}

  ~Sqrp1Node(){}
};

// -----------------------------------------------------------------------------
// Definitions in Node_powsqrt.hpp
// -----------------------------------------------------------------------------

template<typename ScalarType>
class SqrtNode : public UnaryNode<ScalarType>
{
public:
  typedef ScalarType* iterator;
  typedef const ScalarType* const_iterator;

  ScalarType& operator()(int);

  SqrtNode(int a_order, Node<ScalarType> *L)
    : UnaryNode<ScalarType>(a_order,L)
  {}

  ~SqrtNode(){}
};

/// sqrt1px2 = sqrt(1+x^2)
template<typename ScalarType>
class Sqrt1px2Node : public UnaryNode<ScalarType>{
public:
  ScalarType& operator()(int);
  Sqrt1px2Node(int a_order, Node<ScalarType> *L)
    : UnaryNode<ScalarType>(a_order,L){
  }
  ~Sqrt1px2Node(){}
};

/// sqrt1mx2(u) = sqrt(1-u^2)
/// left=u  right=u^2
template<typename ScalarType>
class Sqrt1mx2Node : public BinaryNode<ScalarType>{
public:
  ScalarType& operator()(int);
  Sqrt1mx2Node(int a_order, Node<ScalarType> *L, Node<ScalarType> *R )
    : BinaryNode<ScalarType>(a_order, L, R){
  }
};

/// sqrtx2m1 = sqrt(x^2-1)
template<typename ScalarType>
class Sqrtx2m1Node : public UnaryNode<ScalarType>{
public:
  ScalarType& operator()(int);
  Sqrtx2m1Node(int a_order, Node<ScalarType> *L)
    : UnaryNode<ScalarType>(a_order,L){
  }
  ~Sqrtx2m1Node(){}
};

// -----------------------------------------------------------------------------

template<typename ScalarType>
class SumNode : public BinaryNode<ScalarType>
{
public:
  typedef ScalarType* iterator;
  typedef const ScalarType* const_iterator;

  ScalarType& operator()(int);

  SumNode(int a_order, Node<ScalarType> *L, Node<ScalarType> *R)
    : BinaryNode<ScalarType>(a_order,L,R)
  {}

  ~SumNode(){}
};

// -----------------------------------------------------------------------------

template<typename ScalarType>
class DifNode : public BinaryNode<ScalarType>
{
public:
  typedef ScalarType* iterator;
  typedef const ScalarType* const_iterator;

  ScalarType& operator()(int);

  DifNode(int a_order, Node<ScalarType> *L, Node<ScalarType> *R)
    : BinaryNode<ScalarType>(a_order,L,R)
  {}

  ~DifNode(){}
};

// -----------------------------------------------------------------------------

template<typename ScalarType>
class MulNode : public BinaryNode<ScalarType>
{
public:
  typedef ScalarType* iterator;
  typedef const ScalarType* const_iterator;

  ScalarType& operator()(int);

  MulNode(int a_order, Node<ScalarType> *L, Node<ScalarType> *R)
    : BinaryNode<ScalarType>(a_order,L,R)
  {}

  ~MulNode(){}
};

// -----------------------------------------------------------------------------

template<typename ScalarType>
class MulConsNode : public UnaryNode<ScalarType>
{
  ScalarType m_constant;
public:
  typedef ScalarType* iterator;
  typedef const ScalarType* const_iterator;

  ScalarType& operator()(int i);

  MulConsNode(int a_order, Node<ScalarType> *L, const ScalarType& a_constant)
    : UnaryNode<ScalarType>(a_order,L), m_constant(a_constant)
  {}

  ~MulConsNode(){}
};

// -----------------------------------------------------------------------------

template<typename ScalarType>
class MulParamNode : public BinaryNode<ScalarType>
{
public:
  typedef ScalarType* iterator;
  typedef const ScalarType* const_iterator;

  ScalarType& operator()(int i);

  MulParamNode(int a_order, Node<ScalarType> *L, Node<ScalarType> *paramNode)
    : BinaryNode<ScalarType>(a_order,L,paramNode)
  {}

  ~MulParamNode(){}
};

// -----------------------------------------------------------------------------

template<typename ScalarType>
class MulParamParamNode : public BinaryNode<ScalarType>
{
public:
  typedef ScalarType* iterator;
  typedef const ScalarType* const_iterator;

  ScalarType& operator()(int i);

  MulParamParamNode(int a_order, Node<ScalarType> *L, Node<ScalarType> *paramNode)
    : BinaryNode<ScalarType>(a_order,L,paramNode)
  {}

  ~MulParamParamNode(){}
};

// -----------------------------------------------------------------------------

template<typename ScalarType>
class MulConsParamNode : public UnaryNode<ScalarType>
{
  ScalarType m_constant;
public:
  typedef ScalarType* iterator;
  typedef const ScalarType* const_iterator;

  ScalarType& operator()(int i);

  MulConsParamNode(int a_order, Node<ScalarType> *L, const ScalarType& a_constant)
    : UnaryNode<ScalarType>(a_order,L), m_constant(a_constant)
  {}

  ~MulConsParamNode(){}
};
// -----------------------------------------------------------------------------

template<typename ScalarType>
class DivNode : public BinaryNode<ScalarType>
{
public:
  typedef ScalarType* iterator;
  typedef const ScalarType* const_iterator;

  ScalarType& operator()(int);

  DivNode(int a_order, Node<ScalarType> *L, Node<ScalarType> *R)
    : BinaryNode<ScalarType>(a_order,L,R)
  {}

  ~DivNode(){}
};


// -----------------------------------------------------------------------------

template<typename ScalarType>
class DivByParamNode : public BinaryNode<ScalarType>
{
public:
  typedef ScalarType* iterator;
  typedef const ScalarType* const_iterator;

  ScalarType& operator()(int i);

  DivByParamNode(int a_order, Node<ScalarType> *L, Node<ScalarType> *R)
    : BinaryNode<ScalarType>(a_order,L,R)
  {}

  ~DivByParamNode(){}
};

// -----------------------------------------------------------------------------

template<typename ScalarType>
class DivConsByParamNode : public UnaryNode<ScalarType>
{
  ScalarType m_constant; 
public:
  typedef ScalarType* iterator;
  typedef const ScalarType* const_iterator;

  ScalarType& operator()(int i);

  DivConsByParamNode(int a_order, Node<ScalarType> *L, const ScalarType& a_constant)
    : UnaryNode<ScalarType>(a_order,L), m_constant(a_constant)
  {}

  ~DivConsByParamNode(){}
};

// -----------------------------------------------------------------------------

template<typename ScalarType>
capd::map::Node<ScalarType>& operator+(capd::map::Node<ScalarType>& x, capd::map::Node<ScalarType>& y);

template<typename ScalarType>
capd::map::Node<ScalarType>& operator-(capd::map::Node<ScalarType>& x, capd::map::Node<ScalarType>& y);

template<typename ScalarType>
capd::map::Node<ScalarType>& operator*(capd::map::Node<ScalarType>& x, capd::map::Node<ScalarType>& y);

template<typename ScalarType>
capd::map::Node<ScalarType>& operator/(capd::map::Node<ScalarType>& x, capd::map::Node<ScalarType>& y);

template<typename ScalarType>
std::ostream& operator<<(std::ostream&, const capd::map::Node<ScalarType>&);

}} // the end of the namespace capd::map


#endif // _CAPD_MAP_NODE_H_ 

/// @}
