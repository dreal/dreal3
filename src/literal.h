#include "variable.h"

class literal
{
public:
	literal ( Enode *, rp_table_symbol * );
	~literal();

	inline Enode * 	get_enode()	{ return _e; }
	void		mk_constraint( const char * );
		
private:
  
	vector< variable * >	v_list;
	lbool polarity;	//whether it's negated
	
	Enode *			_e;	//original enode position
	rp_constraint *		_c;
	rp_table_symbol * 	_ts; //pointer to an outside symbol table
	
};

void infix ( Enode *, string & s);