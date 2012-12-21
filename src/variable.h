#include "realpaver.h"
#include "Enode.h"

void rp_interval_cout(rp_interval , int , int );
void rp_box_cout(rp_box , int , int );
void rp_box_stack_cout(rp_box_stack, int, int);

class variable
{
public:
	variable( Enode *, rp_box *, rp_table_symbol * );
	~variable();

	inline Enode * get_enode() { return _e; }
	
	inline rp_variable * get_rp_variable() { return _v; }
	void mk_rp_variable( const char * );
	
	inline double get_ub() { return u_bound; }
	inline double get_lb()	{ return l_bound; }
	inline void set_ub( double b ) { u_bound = b ; }
	inline void set_lb( double b ) { l_bound = b ; }
	
private:

	rp_interval bounds;	//bounds as stored in rp_format
	double u_bound;
	double l_bound;
  
	Enode * _e;	//original enode of the variable
	rp_variable * _v;
	int rp_id;		//id in the interval box
	
	rp_box * _b;	//pointer to an outside rp_box
	rp_table_symbol * _ts; //pointer to an outside symbol table
	
};

