
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
