/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@gmail.com>

OpenSMT -- Copyright (C) 2009, Roberto Bruttomesso

OpenSMT is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

OpenSMT is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with OpenSMT. If not, see <http://www.gnu.org/licenses/>.
*********************************************************************/

#include "Enode.h"
#include "util/string.h"

using std::unordered_set;

//
// Constructor for ENIL
//
Enode::Enode( )
  : id        ( ENODE_ID_ENIL )
  , properties( 0 )
  , car       ( NULL )
  , cdr       ( NULL )
  , cong_data ( NULL )
  , atom_data ( NULL )
  , value     ( NULL )
  , lb        ( NULL )
  , ub        ( NULL )
  , precision ( NULL )
{
  setEtype( ETYPE_LIST );
  // dynamic = this;
}
//
// Constructor for new Symbols
//
Enode::Enode( const enodeid_t      id_
            , const char *         name_
            , const etype_t        etype_
            , Snode *              sort_
            )
  : id         ( id_ )
  , properties ( 0 )
  , car        ( NULL )
  , cdr        ( NULL )
  , atom_data  ( NULL )
  , value      ( NULL )
  , lb        ( NULL )
  , ub        ( NULL )
  , precision ( NULL )
{
  setEtype( etype_ );
  setArity( sort_->getArity( ) - 1 ); // Sort arity includes return value ...
  symb_data = new SymbData( name_, etype_, sort_ );
  // dynamic = this;
}
//
// Constructor for new Terms/Lists
//
Enode::Enode( const enodeid_t id_
            , Enode *         car_
            , Enode *         cdr_ )
  : id         ( id_ )
  , properties ( 0 )
  , car        ( car_ )
  , cdr        ( cdr_ )
  , cong_data  ( NULL )
  , atom_data  ( NULL )
  , value      ( NULL )
  , lb        ( NULL )
  , ub        ( NULL )
  , precision ( NULL )
  // , dynamic   ( NULL )
{
  assert( car );
  assert( cdr );
  assert( car->isTerm( ) || car->isSymb( ) || car->isNumb( ) );
  assert( cdr->isList( ) );
  //
  // If car is term, then this node is a list
  //
  if ( car->isTerm( ) )
  {
    setEtype( ETYPE_LIST );
    if ( cdr->getArity( ) == MAX_ARITY - 1 )
      setArity( cdr->getArity( ) );
    else
      setArity( cdr->getArity( ) + 1 );
  }
  //
  // Otherwise this node is a term
  //
  else
  {
    //
    // Set Etype
    //
    setEtype( ETYPE_TERM );
    //
    // Set Arity
    //
    setArity( cdr->getArity( ) );
  }

  if ( isTAtom( ) )
    atom_data = new AtomData( );

  if ( car->isNumb( ) ) {
    value = new double;
    setValue( *(car->symb_data->value) );
  }
  if(car->hasPrecision()){
    setPrecision(car->getPrecision());
  }

  assert( isTerm( ) || isList( ) );
}
//
// Constructor for new Definition
//
Enode::Enode( const enodeid_t	id_
            , Enode *		def_ )
  : id         ( id_ )
  , properties ( ETYPE_DEF )
  , car        ( def_ )
  , cong_data  ( NULL )
  , atom_data  ( NULL )
  , value      ( NULL )
  , lb        ( NULL )
  , ub        ( NULL )
  , precision ( NULL )
  // , dynamic   ( NULL )
{ }

Enode::~Enode ( )
{
  if ( isSymb( ) || isNumb( ) )
    delete symb_data;
  else if ( cong_data )
    delete cong_data;
  if ( atom_data )
    delete atom_data;
  if ( value )
    delete value;
  if ( ub )
      delete ub;
  if ( lb )
      delete lb;
  if ( precision )
      delete precision;
}

Snode * Enode::getLastSort ( )
{
  assert( isTerm( ) );
  if ( isIte( ) )
    return get2nd( )->getLastSort( );
  Snode * l = getSort( )->getLast( );
  return l;
}

void Enode::addParent ( Enode * p )
{
  if ( isEnil( ) )
    return;

  assert( p );
  assert( cong_data );
  assert( isTerm( ) || isList( ) );

  setParentSize( getParentSize( ) + 1 );
  // If it has no parents, adds p
  if ( getParent( ) == NULL )
  {
    setParent( p );

    if ( isList( ) )
      p->setSameCdr( p );
    else
      p->setSameCar( p );

    return;
  }
  // Otherwise adds p in the samecar/cdr of the parent of this node
  if ( isList( ) )
  {
    // Build or update samecdr circular list
    assert( getParent( )->getSameCdr( ) != NULL );
    p->setSameCdr( getParent( )->getSameCdr( ) );
    getParent( )->setSameCdr( p );
  }
  else
  {
    // Build or update samecar circular list
    assert( getParent( )->getSameCar( ) != NULL );
    p->setSameCar( getParent( )->getSameCar( ) );
    getParent( )->setSameCar( p );
  }
}

void Enode::addParentTail ( Enode * p )
{
  if ( isEnil( ) )
    return;

  cerr << "Adding Parent: " << p << " to " << this << endl;

  assert( p );
  assert( cong_data );
  assert( isTerm( ) || isList( ) );

  setParentSize( getParentSize( ) + 1 );

  // If it has no parents, adds p
  if ( getParent( ) == NULL )
  {
    setParent( p );

    if ( isList( ) )
      p->setSameCdr( p );
    else
      p->setSameCar( p );
  }
  // Otherwise adds p in the samecar/cdr of the
  // parent of this node at the end of the circular list
  else if ( isList( ) )
  {
    // Build or update samecdr circular list
    assert( getParent( )->getSameCdr( ) != NULL );
    Enode * q = getParent( );
    Enode * qstart = q;
    for ( ;; )
    {
      assert( q->isTerm( ) || q->isList( ) );
      if ( q->getSameCdr( ) == qstart )
      {
        q->setSameCdr( p );
        p->setSameCdr( qstart );
        break;
      }
      // Next element
      q = q->getSameCdr( );
    }
  }
  else
  {
    // Build or update samecar circular list
    assert( getParent( )->getSameCar( ) != NULL );
    Enode * q = getParent( );
    Enode * qstart = q;
    for ( ;; )
    {
      assert( q->isTerm( ) || q->isList( ) );
      if ( q->getSameCar( ) == qstart )
      {
        q->setSameCar( p );
        p->setSameCar( qstart );
        break;
      }
      // Next element
      q = q->getSameCar( );
    }
  }
}

void Enode::removeParent ( Enode * p )
{
  if ( isEnil( ) ) return;

  assert( isList( ) || isTerm( ) );
  assert( getParent( ) != NULL );
  assert( getParentSize( ) > 0 );
  setParentSize( getParentSize( ) - 1 );
  // If only one parent, remove it and restore NULL
  if ( getParentSize( ) == 0 )
  {
    assert( getParent( ) == p );
    setParent( NULL );
    return;
  }
  // Otherwise adds remove p from the samecar/cdr list
  if ( isList( ) )
  {
    // Build or update samecdr circular list
    assert( getParent( )->getSameCdr( ) == p );
    getParent( )->setSameCdr( p->getSameCdr( ) );
  }
  else
  {
    // Build or update samecar circular list
    assert( getParent( )->getSameCar( ) == p );
    getParent( )->setSameCar( p->getSameCar( ) );
  }
}

void Enode::print_infix(ostream & os, lbool polarity, string const & variable_postfix) const {
    Enode *p = NULL;
    if(isSymb()) {
        if (polarity == l_False && (getId() == ENODE_ID_LEQ || getId() == ENODE_ID_LT)) {
            os << ">=";
        } else if (polarity == l_False && (getId() == ENODE_ID_GEQ || getId() == ENODE_ID_GT)) {
            os << "<=";
        } else {
            os << getName();
            if (getId() > ENODE_ID_LAST) {
                os << variable_postfix;
            }
        }
    } else if (isNumb()) {
        string temp = getName();
        os << getName();
        if(dreal::ends_with(temp, ".")) {
            os << "0";
        }
    } else if (isTerm()) {
        // output "("
        if (!getCdr()->isEnil() && (isPlus() || isMinus() || isTimes() || isPow())) {
            os << "(";
        }
        // !(X = Y) ==> (0 = 0)
        if (isEq() && polarity  == l_False) {
            os << "0 = 0";
        }
        else if (isPlus() || isMinus() || isTimes() || isDiv() || isEq() || isLeq() ||
                 isGeq() || isLt() || isGt()) {
            // assert(getArity() == 2);
            Enode* op = getCar();
            p = getCdr();
            // Print 1st argument
            p->getCar()->print_infix(os, polarity, variable_postfix);
            p = p->getCdr();
            while (!p->isEnil()) {
                // output operator
                op->print_infix(os, polarity, variable_postfix);
                // output argument
                p->getCar()->print_infix(os, polarity, variable_postfix);
                // move p
                p = p->getCdr();
            }
        } else if (isPow()) {
            Enode* op = getCar();
            p = getCdr();
            // Print 1st argument
            p->getCar()->print_infix(os, polarity, variable_postfix);
            p = p->getCdr();
            while (!p->isEnil()) {
                // output operator
                op->print_infix(os, polarity, variable_postfix);
                // output argument
                os << "(";
                p->getCar()->print_infix(os, polarity, variable_postfix);
                os << ")";
                // move p
                p = p->getCdr();
            }
        } else if (isAtan2()) {
            assert(getArity() == 2);
            // output operator
            getCar()->print_infix(os, polarity, variable_postfix);
            os << "(";
            // output 1st argument
            getCdr()->getCar()->print_infix(os, polarity, variable_postfix);
            os << ", ";
            // output 1st argument
            getCdr()->getCdr()->getCar()->print_infix(os, polarity, variable_postfix);
            os << ")";
        } else if (isAcos() || isAsin() || isAtan() || isMatan() || isSafeSqrt() ||
                   isSin() || isCos() || isTan() || isLog() || isExp() || isSinh() || isCosh() || isTanh()) {
            assert(getArity() == 1);
            // output operator
            getCar()->print_infix(os, polarity, variable_postfix);
            os << "(";
            // output 1st argument
            getCdr()->getCar()->print_infix(os, polarity, variable_postfix);
            os << ")";
        } else {
            getCar()->print_infix(os, polarity, variable_postfix);
            p = getCdr();
            while (!p->isEnil()) {
                os << " ";
                // print Car
                p->getCar()->print_infix(os, polarity, variable_postfix);
                p = p->getCdr();
            }
        }
        // output ")"
        if (!getCdr()->isEnil() && (isPlus() || isMinus() || isTimes() || isPow())) {
            os << ")";
        }
    } else if (isList()) {
        if (isEnil()) {
            os << "-";
        } else {
            os << "[";
            getCar()->print_infix(os, polarity, variable_postfix);
            p = getCdr();
            while (!p->isEnil()) {
                    os << ", ";
                    p->getCar()->print_infix(os, polarity, variable_postfix);
                    p = p->getCdr();
            }
            os << "]";
        }
    } else if (isDef()) {
        os << ":= " << getCar();
    } else if (isEnil()) {
        os << "-";
    } else opensmt_error("unknown case value");
}

void Enode::print(ostream & os) {
    Enode * p = NULL;
    if(isSymb()) {
        os << getName();
    } else if (isNumb()) {
        double r = *(symb_data->value);
        os << r;
    } else if (isTerm()) {
        if (!cdr->isEnil())
            os << "(";
        car->print(os);
        p = cdr;
        while (!p->isEnil()) {
            os << " ";
            p->car->print(os);
            p = p->cdr;
        }
        if(precision){
          os << " [" << getPrecision() << "]";
        }
        if (!cdr->isEnil())
            os << ")";
    } else if (isList()) {
        if (isEnil()) {
            os << "-";
        } else {
            os << "[";
            car->print(os);
            p = cdr;
            while (!p->isEnil()) {
                os << ", ";
                p->car->print(os);
                p = p->cdr;
            }
            os << "]";
        }
    } else if (isDef()) {
        os << ":= " << car;
    } else if (isEnil()) {
        os << "-";
    } else opensmt_error("unknown case value");
}

void Enode::printSig( ostream & os )
{
#ifdef BUILD_64
  enodeid_pair_t sig = getSig( );
  os << "(" << (sig>>sizeof(enodeid_t)*8) << ", " << (sig|0x00000000FFFFFFFF) << ")";
#else
  Pair( enodeid_t ) sig = getSig( );
  os << "(" << sig.first << ", " << sig.second << ")";
#endif
}

string Enode::stripName( string s ) const
{
  return s.substr( 0, s.find( ' ', 0 ) );
}

unordered_set<Enode *> Enode::get_vars() {
    // TODO(soonhok): need to support integral and forallt?
    unordered_set<Enode *> result;
    Enode const * p = nullptr;
    if ( isSymb()) { /* do nothing */ }
    else if (isNumb()) { /* do nothing */ }
    else if (isTerm()) {
        if ( isVar() ) { result.insert(this); }
        p = this;
        while (!p->isEnil()) {
            unordered_set<Enode *> const & tmp_set = p->getCar()->get_vars();
            result.insert(tmp_set.begin(), tmp_set.end());
            p = p->getCdr();
        }
    } else if (isList()) {
        p = this;
        while (!p->isEnil()) {
            unordered_set<Enode *> const  & tmp_set = p->getCar()->get_vars();
            result.insert(tmp_set.begin(), tmp_set.end());
            p = p->getCdr();
        }
    } else if (isDef()) { /* do nothing */ }
    else if (isEnil()) { /* do nothing */ }
    else opensmt_error("unknown case value");
    return result;
}
