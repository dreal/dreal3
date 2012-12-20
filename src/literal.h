#include "variable.h"

class literal
{
public:
	literal ( Enode * );
	~literal();

	rp_ctr_num 	c;	//realpaver constraint, defined in rp_constraint.h

	lbool polarity;	//whether it's negated

	vector< variable * >	v_list;

	inline Enode * get_enode()	{ return _e; }

private:

	Enode *		_e;	//original enode position


};

