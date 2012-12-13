#include "realpaver.h"
#include "Enode.h"

class variable
{
public:
	variable( Enode * );
	~variable();

	Enode * e;	//original enode of the variable

	rp_interval bounds;	//bounds as stored in rp_format
	double u_bound;
	double l_bound;

	int id;		//id in the interval box

private:

};

