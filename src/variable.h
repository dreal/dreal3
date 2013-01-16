#ifndef VARIABLE_H
#define VARIABLE_H

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

	inline Enode * get_enode() const { return _e; }

        inline void            setODEtimevar          (variable* tv)
        {
            timevar = tv;
        }
        inline variable*       getODEtimevar          ( ) const
        {
            return timevar;
        }


	inline rp_variable * get_rp_variable() { return _v; }
	void mk_rp_variable( const char *, const double, const double );

        inline string getName() const { return _e->getCar()->getName(); }


	inline void set_ub( double b )
        {
            rp_bsup(rp_box_elem(*_b, rp_id)) = b;
        }

	inline void set_lb( double b ) {
            rp_binf(rp_box_elem(*_b, rp_id)) = b ;
        }

	inline double get_ub()
        {
            return rp_bsup(rp_box_elem(*_b, rp_id));
        }
	inline double get_lb()
        {
            return rp_binf(rp_box_elem(*_b, rp_id));
        }

	inline void set_top_ub( double b )
        {
            rp_bsup(rp_box_elem(*_b_top, rp_id)) = b;
        }

	inline void set_top_lb( double b ) {
            rp_binf(rp_box_elem(*_b_top, rp_id)) = b ;
        }

	inline double get_top_ub()
        {
            return rp_bsup(rp_box_elem(*_b_top, rp_id));
        }
	inline double get_top_lb()
        {
            return rp_binf(rp_box_elem(*_b_top, rp_id));
        }


        inline void set_top_box(rp_box * _new_b) {
            _b_top = _new_b;
        }

        inline void set_empty_interval() {
            rp_interval_set_empty(rp_box_elem(*_b, rp_id));
        }

        inline int get_rpid () {
            return rp_id;
        }

        bool operator<(const variable &rhs) const
        {
            return getName() < rhs.getName();
        }

        string name;

private:
	// rp_interval* bounds;	//bounds as stored in rp_format
	Enode * _e;	//original enode of the variable
	rp_variable * _v;
	int rp_id;		//id in the interval box

	rp_box * _b;	//pointer to an outside rp_box
        rp_box * _b_top;

	rp_table_symbol * _ts; //pointer to an outside symbol table
        variable* timevar; // poitner to time variable
};

#endif
