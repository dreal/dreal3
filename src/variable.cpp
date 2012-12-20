#include "variable.h"

variable::variable( Enode * e, rp_box * b, rp_table_symbol * ts )
{
	_e = e;
	_b = b;
	_ts = ts;
}


void variable::mk_rp_variable( const char * name )
{
    _v = new rp_variable;
    
    rp_variable_create( _v, name);
    rp_id = rp_vector_insert(rp_table_symbol_vars(*_ts), (*_v));
    
    rp_interval_set( rp_box_elem ( (*_b), rp_id), 0, 1 );
  
}
