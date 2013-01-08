/// @addtogroup map
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file BasicFunction.hpp
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

/* Author: Daniel Wilczak 2006-2009 */

#ifndef _CAPD_MAP_BASICFUNCTION_HPP_
#define _CAPD_MAP_BASICFUNCTION_HPP_

#include <sstream>
#include <stdexcept>
#include <cstdlib>

#include "capd/map/BasicFunction.h"
#include "capd/map/Parser.h"
#include "capd/map/Node.hpp"
#include <algorithm>

namespace capd{
namespace map{

template<typename Scalar>
const Scalar& BasicFunction<Scalar>::getCurrentTime(int timeIndex) const
{
  static ScalarType noTime(0.);
  if(timeIndex>=m_dim)
    return noTime;

  return m_val[m_order*timeIndex];
}

// -----------------------------------------------------------------------------

template<typename Scalar>
void BasicFunction<Scalar>::setCurrentTime(const ScalarType& a_time, int timeIndex) const
{
  if(timeIndex>=m_dim)
    return;
  m_val[m_order*timeIndex] = a_time;
}

// -----------------------------------------------------------------------------

template<typename Scalar>
void BasicFunction<Scalar>::differentiateTime(int timeIndex) const
{
  if(timeIndex>=m_dim)
    return;
  m_val[m_order*timeIndex+1] = ScalarType(1.);
}

// -----------------------------------------------------------------------------

template<typename Scalar>
void BasicFunction<Scalar>::operator=(const BasicFunction& f)
{
  if(this!=&f)
  {
    deleteTables();
    createFromObject(f);
  }
}

// -----------------------------------------------------------------------------

template<typename Scalar>
void BasicFunction<Scalar>::operator=(const std::string& s)
{
  deleteTables();
  createFromText(s,0);
}

// -----------------------------------------------------------------------------

template<typename Scalar>
void BasicFunction<Scalar>::operator=(const char* s)
{
  deleteTables();
  createFromText(s,0);
}

// -----------------------------------------------------------------------------

template<typename Scalar>
BasicFunction<Scalar>::BasicFunction()
{
  createDefault();
}

// -----------------------------------------------------------------------------

template<typename Scalar>
BasicFunction<Scalar>::BasicFunction(const BasicFunction& f)
{
  createFromObject(f);
}

// -----------------------------------------------------------------------------

template<typename Scalar>
BasicFunction<Scalar>::BasicFunction(const std::string&s, int a_order)
{
  createFromText(s,a_order);
}

// -----------------------------------------------------------------------------

template<typename Scalar>
BasicFunction<Scalar>::BasicFunction(const char* s, int a_order)
{
  createFromText(s,a_order);
}

// -----------------------------------------------------------------------------

template<typename Scalar>
BasicFunction<Scalar>::~BasicFunction()
{
  deleteTables();
}

//--------------------- createDefault ----------------------------------

template<typename Scalar>
void BasicFunction<Scalar>::createDefault()
{
  m_dim = 1;
  m_order = 1;
  m_size = 1;
  m_indexOfFirstParam = 1;

  m_var.clear();
  m_var.push_back("");

  m_val = new ScalarType[1];
  m_val[0] = ScalarType(0.);
}

// --------------------- deleteTables ---------------------------------

template<typename Scalar>
void BasicFunction<Scalar>::deleteTables()
{
  m_var.clear();
  delete []m_val;
  m_val = 0; // NULL
  m_nodes.clear();
}

// -----------------------------------------------------------------------------

template<typename Scalar>
void BasicFunction<Scalar>::createFromText(std::string s, int a_order)
{
  Parser::removeWhiteSpaces(s);
  m_order = a_order+1;
  Parser::splitVariables("var:",s,m_var);  /* we read variables and dimension */
  m_indexOfFirstParam = m_var.size();

  size_t parPos = s.find("par");
  if(parPos!=std::string::npos)
    Parser::splitVariables("par:",s,m_var);  /* we read variables and dimension */

  m_dim = m_var.size();
  m_size = m_dim*m_order;
  m_val = new ScalarType[m_size];
  std::fill(m_val,m_val+m_size,ScalarType(0.));
}

// -----------------------------------------------------------------------------

template<typename Scalar>
void BasicFunction<Scalar>::createFromObject(const BasicFunction &f)
{
  m_dim = f.m_dim;
  m_size = f.m_size;
  m_order = f.m_order;
  m_indexOfFirstParam = f.m_indexOfFirstParam;

  m_var.resize(m_dim);
  m_val = new ScalarType[m_size];

  int i;
  for(i=0;i<m_size;++i)
    m_val[i] = f.m_val[i];

  for(i=0;i<m_dim;++i)
    m_var[i] = f.m_var[i];
}

// -----------------------------------------------------------------------------

template<typename Scalar>
void BasicFunction<Scalar>::setOrder(int the_new)
{
  if(m_order==the_new+1) return;
  if (the_new<0)
  {
    std::ostringstream message;
    message <<  "BasicFunction error: invalid argument " << the_new << " in method setOrder";
    throw std::out_of_range(message.str());
  }
  m_size = m_dim*(the_new+1);
  ScalarType *temp = new ScalarType[m_size];
  std::fill(temp,temp+m_size,ScalarType(0.));

  for(int i=0;i<m_dim;++i)
    temp[i*(the_new+1)] = m_val[i*m_order];

  delete []m_val;
  m_val = temp;
  m_order = the_new+1;
}

/* _________________________________________________________________ */

template<typename Scalar>
void BasicFunction<Scalar>::setParameter(const std::string &name, const ScalarType& value)
{
  int cnt=0;
  while( (cnt<m_dim) && (m_var[cnt]!=name) ) ++cnt;

  if(cnt<m_dim)
  {
    m_val[m_order*cnt] = value;
  }
}

/* _________________________________________________________________ */

template<typename Scalar>
std::string BasicFunction<Scalar>::variables() const
{
  std::string result = "var:";
  result += m_var[0];
  for(int i=1;i<m_indexOfFirstParam;++i)
    result = result + ","  + m_var[i];
  result += ";";
  if(m_indexOfFirstParam!=m_dim)
  {
    result += "par:";
    result += m_var[m_indexOfFirstParam];
    for(int i=m_indexOfFirstParam+1;i<m_dim;++i)
      result = result + ","  + m_var[i];
    result += ";";
  }
  return result;
}

template<typename ScalarType>
template <template <typename T> class NodeT >
inline NodeT<ScalarType> * BasicFunction<ScalarType>::addUnaryNode(
    std::string & left
  ){
  NodeT<ScalarType> * node = new NodeT<ScalarType>( m_order, NULL);
  eqnanal(left, &(node->left));
  node->left->m_links++;
  return node;
}

template<typename ScalarType>
template <template <typename T> class NodeT >
inline NodeT<ScalarType> * BasicFunction<ScalarType>::addBinaryNode(
    std::string & left, std::string & right
  ){
  NodeT<ScalarType> * node = new NodeT<ScalarType>( m_order, NULL, NULL);
  eqnanal(left, &(node->left));
  eqnanal(right, &(node->right));
  node->left->m_links++;
  node->right->m_links++;
  return node;
}

/* _____________________________ EQNANAL ______________________________ */


template<typename Scalar>
void BasicFunction<Scalar>::eqnanal(std::string &eq, NodeType **N)
/*
  a recurrent function, which analyze <eq> - a text containing a formula
  and produces a tree representing it.
*/
{
  int hp;
  if (eq.at(0)=='+') eq.erase(0,1); // remove '+' from at the begin of <eq>

  Parser::removeBrackets(eq);

  typename std::map<std::string,NodeType*>::iterator it = m_nodes.find(eq);
  if(it!=m_nodes.end())
  {
    *N = it->second;
    return;
  }

  // if <eq> starts with '-', then we insert '0' in front to turn
  // this into an occurence of a subtraction
  if (eq.at(0)=='-') eq.insert(0,"0");

  hp = Parser::searchForOperator(eq,'+');
  if(hp)
  {
    std::string left = std::string(eq,0,hp);
    std::string right = std::string(eq,hp+1,std::string::npos);
    *N = new SumNode<ScalarType>(m_order,NULL,NULL);
    eqnanal(left,&((*N)->left));
    eqnanal(right,&((*N)->right));
    (*N)->left->m_links++;
    (*N)->right->m_links++;
    m_nodes[eq]=*N;
    return;
  }

  hp = Parser::searchForOperator(eq,'-');
  if(hp)
  {
    std::string left = std::string(eq,0,hp);
    std::string right = std::string(eq,hp+1,std::string::npos);
    *N = new DifNode<ScalarType>(m_order,NULL,NULL);
    eqnanal(left,&((*N)->left));
    eqnanal(right,&((*N)->right));
    (*N)->left->m_links++;
    (*N)->right->m_links++;
    m_nodes[eq]=*N;
    return;
  }

  hp = Parser::searchForOperator(eq,'*');
  if(hp)
  {
    std::string left = std::string(eq,0,hp);
    std::string right = std::string(eq,hp+1,std::string::npos);
    double leftValue, rightValue;
    bool isLeftConstant = Parser::isConstant(left,leftValue);
    bool isRightConstant = Parser::isConstant(right,rightValue);
    int isLeftParam = isParam(left);
    int isRightParam = isParam(right);

    if(isLeftConstant)
    {
      if(isRightConstant)
      {
        *N = new ConsNode<ScalarType>(m_order,ScalarType(leftValue)*ScalarType(rightValue));
        return;
      }
      if(isRightParam<m_dim)
        *N = new MulConsParamNode<ScalarType>(m_order,NULL,ScalarType(leftValue));
      else
        *N = new MulConsNode<ScalarType>(m_order,NULL,ScalarType(leftValue));

      eqnanal(right,&((*N)->left));
      (*N)->left->m_links++;
      m_nodes[eq]=*N;
      return;
    }

    if(isRightConstant)
    {
      if(isLeftParam<m_dim)
        *N = new MulConsParamNode<ScalarType>(m_order,NULL,ScalarType(rightValue));
      else
        *N = new MulConsNode<ScalarType>(m_order,NULL,ScalarType(rightValue));

      eqnanal(left,&((*N)->left));
      (*N)->left->m_links++;
      m_nodes[eq]=*N;
      return;
    }

    if(isLeftParam<m_dim && isRightParam < m_dim)
    {
      *N = new MulParamParamNode<ScalarType>(m_order,NULL,NULL);
      eqnanal(left,&((*N)->left));
      eqnanal(right,&((*N)->right));
    }
    else if(isLeftParam < m_dim)
    {
      *N = new MulParamNode<ScalarType>(m_order,NULL,NULL);
      eqnanal(left,&((*N)->right)); // param is always in right node
      eqnanal(right,&((*N)->left));
    }
    else if(isRightParam <m_dim)
    {
      *N = new MulParamNode<ScalarType>(m_order,NULL,NULL);
      eqnanal(left,&((*N)->left));
      eqnanal(right,&((*N)->right));
    }
    else
    {
      *N = new MulNode<ScalarType>(m_order,NULL,NULL);
      eqnanal(left,&((*N)->left));
      eqnanal(right,&((*N)->right));
    }
    (*N)->left->m_links++;
    (*N)->right->m_links++;
    m_nodes[eq]=*N;
    return;
  } // end of operator *

  hp = Parser::searchForOperator(eq,'/');
  if(hp)
  {
    std::string left = std::string(eq,0,hp);
    std::string right = std::string(eq,hp+1,std::string::npos);
    double leftValue,rightValue;
    bool isLeftConstant = Parser::isConstant(left,leftValue);
    bool isRightConstant = Parser::isConstant(right,rightValue);
    int isLeftParam = isParam(left);
    int isRightParam = isParam(right);

    if(isRightConstant)
    {
      if(isLeftConstant)
      {
        ScalarType value = ScalarType(leftValue)/ScalarType(rightValue);
        *N = new ConsNode<ScalarType>(m_order,value);
        return;
      }
      if(isLeftParam<m_dim)
        *N = new MulConsParamNode<ScalarType>(m_order,NULL,ScalarType(1.)/ScalarType(rightValue));
      else
        *N = new MulConsNode<ScalarType>(m_order,NULL,ScalarType(1.)/ScalarType(rightValue));

      eqnanal(left,&((*N)->left));
      (*N)->left->m_links++;
      m_nodes[eq]=*N;
      return;
    }

    if(isLeftConstant && isRightParam<m_dim)
    {
      *N = new DivConsByParamNode<ScalarType>(m_order,NULL,ScalarType(leftValue));
      eqnanal(right,&((*N)->left));
      (*N)->left->m_links++;
      m_nodes[eq]=*N;
      return;
    }

    *N = new DivNode<ScalarType>(m_order,NULL,NULL);
    eqnanal(left,&((*N)->left));
    eqnanal(right,&((*N)->right));
    (*N)->left->m_links++;
    (*N)->right->m_links++;
    m_nodes[eq]=*N;
    return;
  } // the end of operator /

  hp = Parser::searchForOperator(eq,'^');
  if(hp)
  {
    std::string left = std::string(eq,0,hp);
    std::string right = std::string(eq,hp+1,std::string::npos);
    if(right!="2"){
      m_nodes[eq]=*N = addBinaryNode<PowNode>(left,right);
    }else {
      *N = new SqrNode<ScalarType>(m_order,NULL);
      eqnanal(left,&((*N)->left));
      (*N)->left->m_links++;
      m_nodes[eq]=*N;
    }
    return;
  }

  std::string params;
  // there was'nt any operator found, hence we look for functions
  hp = Parser::searchForFunction("sqrt",eq);

  // @deprecated  sqr stands for square root in function parser (use sqrt instead)!
  //if(!hp)
  //  hp = Parser::searchForFunction("sqr",eq);

  if(hp)
  {
    std::string left = std::string(eq,hp,std::string::npos);
    *N = new SqrtNode<ScalarType>(m_order,NULL);
    eqnanal(left,&((*N)->left));
    (*N)->left->m_links++;
    m_nodes[eq]=*N;
    return;
  }

  // sqrt1mx2(u) = sqrt(1-u^2)
  if(Parser::searchForFunction("sqrt1mx2", eq, params)){
    std::string auxiliaryFunction =  params+"^2";

    m_nodes[eq] = *N = addBinaryNode<Sqrt1mx2Node>(params, auxiliaryFunction);
    return;
  }
  //   sqrp1(u)=u^2+1
  hp = Parser::searchForFunction("sqrp1",eq);

  if(hp)
  {
    std::string left = std::string(eq,hp,std::string::npos);
    *N = new Sqrp1Node<ScalarType>(m_order,NULL);
    eqnanal(left,&((*N)->left));
    (*N)->left->m_links++;
    m_nodes[eq]=*N;
    return;
  }

  if(Parser::searchForFunction("sin",eq, params)){
    std::string right = "1";
    m_nodes[eq]=*N = addBinaryNode<SinNode>(params, right);
    return;
  }

  hp = Parser::searchForFunction("cos",eq);
  if(hp)
  {
    std::string left = std::string(eq,hp,std::string::npos);
    std::string right = "1";
    *N = new CosNode<ScalarType>(m_order,NULL,NULL);
    eqnanal(left,&((*N)->left));
    eqnanal(right,&((*N)->right));
    (*N)->left->m_links++;
    (*N)->right->m_links++;
    m_nodes[eq]=*N;
    return;
  }

  hp = Parser::searchForFunction("exp",eq);
  if(hp)
  {
    std::string left = std::string(eq,hp,std::string::npos);
    *N = new ExpNode<ScalarType>(m_order,NULL);
    eqnanal(left,&((*N)->left));
    (*N)->left->m_links++;
    m_nodes[eq]=*N;
    return;
  }

  hp = Parser::searchForFunction("log",eq);
  if(hp)
  {
    std::string left = std::string(eq,hp,std::string::npos);
    *N = new LogNode<ScalarType>(m_order,NULL);
    eqnanal(left,&((*N)->left));
    (*N)->left->m_links++;
    m_nodes[eq]=*N;
    return;
  }
  // arc tan
  if(Parser::searchForFunction("atan", eq, params)){
    std::string help = "sqrp1("+params+")";
    m_nodes[eq]= *N = addBinaryNode<AtanNode>(params, help);
    return;
  }
  // arc sin
  if(Parser::searchForFunction("asin", eq, params)){
    std::string help = "sqrt1mx2("+params+")";
    m_nodes[eq]= *N = addBinaryNode<AsinNode>(params, help);
    return;
  }
  // arc cos
  if(Parser::searchForFunction("acos", eq, params)){
    std::string help = "sqrt1mx2"+params;
    m_nodes[eq]= *N = addBinaryNode<AcosNode>(params, help);
    return;
  }
  // this was'nt functions - now we check for variables
  hp=0;
  while((hp<m_dim)&&(m_var[hp]!=eq)) hp++;

  if(hp<m_dim)
  {
    *N = new VarNode<ScalarType>(m_order,&m_val[hp*m_order], hp);
    return;
  }

  // now we check for  constants
  double value;
  if(Parser::stringToDouble(eq, value)){
    *N = new ConsNode<ScalarType>( m_order, ScalarType(value));
    //m_nodes[eq]=*N;
    return;
  }
/* //Replaced by TK with above (it accept 1.2dafds and do not accept 0.0)
  if ( (std::strtod(eq.c_str(),NULL)) || (eq=="0") )
  {
    *N = new ConsNode<ScalarType>( m_order, ScalarType(std::strtod(eq.c_str(),NULL)));
    //m_nodes[eq]=*N;
    return;
  }
*/
  *N = NULL;

  deleteTables();
  std::string re = "undefined symbol '" + eq + "' in the formula: ";
  re += currentFormula();

  throw std::runtime_error(re);
}

/* ______________________ DEPENDS _____________________________*/

template<typename Scalar>
bool BasicFunction<Scalar>::depends(std::string str, int i) const
/**
  This function checks if 'str' depends on i-th coordinate
*/
{
  int hp;

  Parser::removeBrackets(str);
  if((str.at(0)=='-') || str.at(0)=='+')
      str.erase(0,1);
  Parser::removeBrackets(str);

  // an analysis of arguments of our function

  hp = Parser::searchForOperator(str,'+');
  if(hp) return depends(std::string(str,hp+1,std::string::npos),i) ? true : depends(std::string(str,0,hp),i);

  hp = Parser::searchForOperator(str,'-');
  if(hp) return depends(std::string(str,hp+1,std::string::npos),i) ? true : depends(std::string(str,0,hp),i);

  hp = Parser::searchForOperator(str,'*');
  if(hp) return depends(std::string(str,hp+1,std::string::npos),i) ? true : depends(std::string(str,0,hp),i);

  hp = Parser::searchForOperator(str,'/');
  if(hp) return depends(std::string(str,hp+1,std::string::npos),i) ? true : depends(std::string(str,0,hp),i);

  hp = Parser::searchForOperator(str,'^');
  if(hp) return depends(std::string(str,0,hp),i);

  /// TODO: this should be changed to static member of the class or even global variable.
  const std::string functionList[] = {"sqrt", "sin", "cos", "exp", "log", "atan", "acos", "asin", "sqrt1mx2"};
  const int numberOfFunctions = 9;
  for(int fun = 0; fun < numberOfFunctions; fun++ ){
    hp = Parser::searchForFunction(functionList[fun], str);
    if(hp)
      return depends(std::string(str,hp,std::string::npos),i);
  }
/*
  hp = Parser::searchForFunction("sqr",str);
  if(hp) return depends(std::string(str,hp,std::string::npos),i);


  hp = Parser::searchForFunction("sin",str);
  if(hp) return depends(std::string(str,hp,std::string::npos),i);

  hp = Parser::searchForFunction("cos",str);
  if(hp) return depends(std::string(str,hp,std::string::npos),i);

  hp = Parser::searchForFunction("exp",str);
  if(hp) return depends(std::string(str,hp,std::string::npos),i);

  hp = Parser::searchForFunction("log",str);
  if(hp) return depends(std::string(str,hp,std::string::npos),i);

  hp = Parser::searchForFunction("atan",str);
  if(hp) return depends(std::string(str,hp,std::string::npos),i);
*/
  hp=0;

  while((hp<m_dim)&&(str!=m_var[hp]))
    hp++;

  if (hp!=i)
      return false;
  else
     return true;
}

// --------------------- isVariable ------------------------------------

template<typename Scalar>
bool BasicFunction<Scalar>::isVariable(std::string &f, int i) const
/**
  this function checks if <f> consist of i-th variable only
*/

{
  Parser::removeBrackets(f); // removes external brackets

  int hp=0;
  while((hp<m_dim)&&(f!=m_var[hp])) // looking for a variable
    hp++;

  if (hp!=i)
    return false;
  else
    return true;
}

template<typename Scalar>
int BasicFunction<Scalar>::isParam(std::string &f) const
/**
  this function checks if <f> consist of i-th variable only
*/

{
  Parser::removeBrackets(f); // removes external brackets

  int hp=m_indexOfFirstParam;
  while((hp<m_dim)&&(f!=m_var[hp])) // looking for a variable
    hp++;

  return hp;
}

//--------------------- DIFFANAL ----------------------------------

template<typename Scalar>
std::string BasicFunction<Scalar>::diffanal(std::string &str,int i) const
/**
  a recurrent function creating a partial derivative with respect
  to i-th coordinate
*/
{
  int hp,d1,d2;
  Parser::removeBrackets(str); // removes external brackets
  std::string b="";

  if(str.at(0)=='+')
    str.erase(0,1);

  Parser::removeBrackets(str); //removes external brackets

  if(str.at(0)=='-')
  {   // (-f)'=0-f'
    str.insert(0,"0");
    return diffanal(str,i);
  }

  Parser::removeBrackets(str);

  hp = Parser::searchForOperator(str,'+');  // (f+g)'=f'+g'
  if(hp)
  {
    b="";
    std::string left = std::string(str,0,hp);
    std::string right = std::string(str,hp+1,std::string::npos);
    d1 = depends(left,i);  // checks if f depends on i-th variable
    d2 = depends(right,i);  // checks if g depends on i-th variable

    if(d1)
      b = diffanal(Parser::removeBrackets(left),i);
    if(d1&&d2)
      b += "+";                  // both arguments depend on i-th variable
    if(d2)
      b += diffanal(Parser::removeBrackets(right),i);
    return b;
  }


  hp = Parser::searchForOperator(str,'-');   // (f-g)'=f'-g'
  if(hp)
  {              // we proceed as in case of '+'
    b="";
    std::string left = std::string(str,0,hp);
    std::string right = std::string(str,hp+1,std::string::npos);
    d1 = depends(left,i);  // checks if f depends on i-th variable
    d2 = depends(right,i);  // checks if g depends on i-th variable

    if(d1)
      b += diffanal(Parser::removeBrackets(left),i);
    if(d1&&d2)
      b += "-(" + diffanal(Parser::removeBrackets(right),i) + ")";
    if((!d1)&&d2)
      b += "0-(" + diffanal(Parser::removeBrackets(right),i) + ")"; // then (f-g)'=-(g')
    return b;
  }


  hp = Parser::searchForOperator(str,'*');  //(f*g)'=f'*g+f*g'
  if(hp)
  {
    b="";
    std::string left = std::string(str,0,hp);
    std::string right = std::string(str,hp+1,std::string::npos);
    d1 = depends(left,i);  // checks if f depends on i-th variable
    d2 = depends(right,i);  // checks if g depends on i-th variable

    if(d1)
    {          // we need to include  (f')*g
      if (!isVariable(left,i))
        b += "(" + diffanal(Parser::removeBrackets(left),i) + ")*";
      b += right;
    }

    if(d2&&d1) b += "+";

    if(d2)
    {          // we need to include f*(g')
      b += "(" + left + ")";
      if(!isVariable(right,i))
        b += "*(" + diffanal(Parser::removeBrackets(right),i) + ")";
    }
    return b;
  }


  hp = Parser::searchForOperator(str,'/'); // (f/g)'=(f'*g-f*g')/g^2
  if(hp)
  {
    b="";
    std::string left = std::string(str,0,hp);
    std::string right = std::string(str,hp+1,std::string::npos);
    d1 = depends(left,i);  // checks if f depends on i-th variable
    d2 = depends(right,i);  // checks if g depends on i-th variable

    if(d1&&(!d2))    // in this situation (f/g)'=(f')/g
      b += "(" + diffanal(Parser::removeBrackets(left),i) + ")/" + right;

    if((!d1)&&d2)
    {    //  (f/g)'= (-(g')*f)/g^2
      b += "(0-";
      if(!isVariable(right,i))
        b += "(" + diffanal(Parser::removeBrackets(right),i) + ")*";
      b += left + ")/(" + right + ")^2";
    }

    if(d1&&d2)
    {      // full formula for derivative of f/g
      b += "(" + right;
      if(!isVariable(left,i))
        b += "*(" + diffanal(Parser::removeBrackets(left),i) + ")";
      b += "-";
      if(!isVariable(right,i))
        b += "(" + diffanal(Parser::removeBrackets(right),i) + ")*(";
      b += left + "))/(" + right + ")^2";
    }
    return b;
  }


  hp = Parser::searchForOperator(str,'^');
  if(hp)
  {
    b="";
    std::string left = std::string(str,0,hp);
    std::string right = std::string(str,hp+1,std::string::npos);
    d1 = depends(left,i);  // checks if f depends on i-th variable

    if (!d1)
      return "";
    double j = std::strtod((b=Parser::removeBrackets(right)).c_str(),NULL); // check the exponent
    if(j==0) return "0";                    // (f^0)'=0
    if(j==1) return diffanal(Parser::removeBrackets(left),i);  // (f^1)'=f'
    if(j==2)
    {                          // (f^2)'=f*2*(f')
      b="";
      b += left + "*2";
      if(!isVariable(left,i))
        b += "*(" + diffanal(Parser::removeBrackets(left),i) + ")";
      return b;
    }

// in remaining cases, also for negative exponents
// (f^n)'=(f')*(n)*f^(n-1)

    b="";
    if(!isVariable(left,i))
      b += "(" + diffanal(Parser::removeBrackets(left),i) + ")*";
    b += "(" + right + ")*(" + left + ")^(";
    std::ostringstream bufor;
    bufor << (j-1);
    b += bufor.str() + ")";
    return b;
  }

  hp = Parser::searchForFunction("sqrt", str);

   /// @deprecated  sqr stands for square root in function parser (use sqrt instead)!
  //if(!hp)
    // hp = Parser::searchForFunction("sqr", str);

  // sqrt(f(x))'=0.5*(f'(x))/sqrt(f(x))
  if(hp)
  {
    b="";
    std::string right = std::string(str,hp,std::string::npos);
    d1 = depends(right,i);  // checks if f depends on i-th variable

    if(!d1)
      return "";
    b = "";
    b += "0.5*(" + diffanal(Parser::removeBrackets(right),i) + ")/" + str; // here str=sqr(...), hence parethesses are not required
    return b;
  }


  hp = Parser::searchForFunction("sin",str);
     // sin(x)'=cos(x)  or  sin(f(x))'=cos(f(x))*(f'(x))
  if(hp)
  {
    std::string right = std::string(str,hp,std::string::npos);
    d1 = depends(right,i);  // checks if f depends on i-th variable
    if(!d1)
       return "";
    b = "";
    b += "cos" + right;
    if(!isVariable(right,i))
      b += "*(" + diffanal(Parser::removeBrackets(right),i) + ")" ;
    return b;
  }


  hp = Parser::searchForFunction("cos",str);
     // cos(x)'=(-sin(x))  or  cos(f(x))'=(-sin(f(x)))*(f'(x))
  if(hp)
  {
    std::string right = std::string(str,hp,std::string::npos);
    d1 = depends(right,i);  // checks if f depends on i-th variable
    if(!d1)
      return "";
    b = ""; b += "(-sin" + right + ")";
    if(!isVariable(right,i))
      b += "*(" + diffanal(Parser::removeBrackets(right),i) + ")";
    return b;
  }


  hp = Parser::searchForFunction("exp",str);
  // exp(x)'=exp(x)  or  exp(f(x))'=exp(f(x))*(f'(x))
  if(hp)
  {
    std::string right = std::string(str,hp,std::string::npos);
    d1 = depends(right,i);  // checks if f depends on i-th variable
    if(!d1) return "";
    b = "";
    b += str;
    if (!isVariable(right,i))
      b += "*(" + diffanal(Parser::removeBrackets(right),i) + ")";
    return b;
  }


  hp = Parser::searchForFunction("log",str); // log(f(x))'=(f'(x))/f(x)
  if(hp)
  {
    std::string right = std::string(str,hp,std::string::npos);
    d1 = depends(right,i);  // checks if f depends on i-th variable
    if(!d1) return "";
    b = ""; b += "(" + diffanal(Parser::removeBrackets(right),i) + ")/(" + right + ")";
    return b;
  }

  hp = Parser::searchForFunction("atan",str);
  // atan'(u) = 1/(1+u^2) * u'
  if(hp)
  {

    std::string right = std::string(str,hp,std::string::npos);
    d1 = depends(right,i);  // checks if f depends on i-th variable
    if(!d1)
      return "";
    if(!isVariable(right,i))
      b = "((" + diffanal(Parser::removeBrackets(right),i) + ")";
    else
      b = "(1";
    b += "/(1+(" + Parser::removeBrackets(right) +")^2))";
    return b;
  }
  hp = Parser::searchForFunction("asin",str) + Parser::searchForFunction("acos",str) + Parser::searchForFunction("sqrt1px2",str);
  if(hp){
    throw std::runtime_error("derivative not yet implemented for asin, acos");
  }
  hp=0;
  while((hp<m_dim)&&(m_var[hp]!=str)) hp++;

  if(hp!=i) return "0";
  else return "1";
}

}} // namespace capd::map

#endif // _CAPD_MAP_BASICFUNCTION_HPP_

/// @}
