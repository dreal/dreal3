#include "variable.h"

class literal
{
public:
	literal ( Enode * );
	~literal();

	Enode *		e;	//original enode position
	rp_ctr_num 	c;	//realpaver constraint, defined in rp_constraint.h

	lbool polarity;	//whether it's negated

	vector< variable * >	v_list;
};

