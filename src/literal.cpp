
#include "literal.h"

literal::literal(Enode * e , rp_table_symbol * ts)
{
  	_e = e;
	_ts = ts;
	_c = new rp_constraint;
}

literal::~literal()
{}

void literal::mk_constraint( const char * src )
{
    rp_parse_constraint_string ( _c , src, (*_ts) );
}

void infix( const Enode *e, ostream & os )
{
  Enode *p = NULL;
  if( e->isSymb( ) ) {
    os << e->getName( );
  }
  else if ( e->isNumb( ) )
  {
    os << e->getName( );
  }
  else if ( e->isTerm( ) )
  {
    // output "("
    if ( !e->getCdr()->isEnil( ) && ( e->isPlus() || e->isMinus() || e->isTimes() || e->isPow() ) ) {
      os << "(";
    }

    if ( e->isPlus() ||
         e->isMinus() ||
         e->isTimes() ||
         e->isDiv() ||
         e->isEq() ||
         e->isLeq() ||
         e->isGeq() ||
         e->isLt() ||
         e->isGt() ||
         e->isPow()
         )
      {
        assert(e->getArity() == 2);

        // output 1st argument
        infix(e->getCdr()->getCar(), os);
        os << " ";
        // output operator
        infix(e->getCar(), os);
        os << " ";
        // output 2nd argument
        infix(e->getCdr()->getCdr()->getCar(), os);
      }
    else if (e->isArcCos() ||
             e->isArcSin() ||
             e->isArcTan() ||
             e->isSin() ||
             e->isCos() ||
             e->isTan() ||
             e->isLog() ||
             e->isExp()
             ) {
        assert(e->getArity() == 1);
        // output operator
        infix(e->getCar(), os);
        os << "(";
        // output 1st argument
        infix(e->getCdr()->getCar(), os);
        os << ")";
    }
    else {
      infix(e->getCar(), os);
      p = e->getCdr();
      while ( !p->isEnil( ) )
        {
          os << " ";
          // print Car
          infix(p->getCar(), os);
          p = p->getCdr();
        }
    }

    // output ")"
    if ( !e->getCdr()->isEnil( ) && ( e->isPlus() || e->isMinus() || e->isTimes() || e->isPow() )) {
      os << ")";
    }
  }
  else if ( e->isList( ) )
    {
      if ( e->isEnil( ) )
        os << "-";
      else
        {
          os << "[";
          infix(e->getCar(), os);

          p = e->getCdr();
          while ( !p->isEnil( ) )
            {
              os << ", ";
              infix(p->getCar(), os);
              p = p->getCdr();
            }

          os << "]";
        }
    }
  else if ( e->isDef( ) )
    {
      os << ":= " << e->getCar();
    }
  else if ( e->isEnil( ) )
    {
      os << "-";
    }
  else
    opensmt_error( "unknown case value" );
}

const string infix(const Enode *e)
{
  stringstream buf;
  infix(e, buf);
  return buf.str();
}
