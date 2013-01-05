
#include "literal.h"

literal::literal(Enode * e , rp_table_symbol * ts)
{
  	_e = e;
	_ts = ts;
	_c = new rp_constraint;
}

literal::~literal()
{}

void literal::mk_constraint( const char * s )
{
    char * src = const_cast<char*> ( s );
    rp_parse_constraint_string ( _c , src, (*_ts) );
}

void infix( Enode *e, ostream & os )
{
  Enode *p = NULL;
  if( e->isSymb( ) )
    os << e->getName( );
  else if ( e->isNumb( ) )
  {
    os << e->getName( );
  }
  else if ( e->isTerm( ) )
  {
    if ( !e->getCdr()->isEnil( ) )
      os << "(";

    infix(e->getCar(), os);

    p = e->getCdr();
    while ( !p->isEnil( ) )
    {
      os << " ";
      infix(p->getCar(), os);
      p = p->getCdr();
    }

    if ( !e->getCdr()->isEnil( ) )
      os << ")";
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

const char * infix(Enode *e)
{
  stringstream buf;
  infix(e, buf);
  return buf.str().c_str();
}
