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
    
    //TODO make these consistent with the new pointers to symbolc table inside rp_problem
    
    rp_id = rp_vector_insert(rp_table_symbol_vars(*_ts), (*_v));
    
    rp_box_enlarge_size( _b, 1);
    rp_interval_set( rp_box_elem ( (*_b), rp_id), 0, 1 );
    
    rp_box_cout( (*_b) , 2 , 0);
      
}

void rp_interval_cout(rp_interval i, int digits, int mode)
{
  char tmp[255];
  rp_interval_print(tmp,i,digits,mode);
  cout<< tmp;
}

void rp_box_cout(rp_box b, int digits, int mode)
{
  if (rp_box_empty(b))
  {
    cout<<"empty";
  }
  else
  {
    int i;
//    cout<<"The intervals are:"<<endl;
    for (i=0; i<rp_box_size(b); ++i)
    {
      cout <<"x"<<i<<" is in: ";
      rp_interval_cout(rp_box_elem(b,i),digits,mode);
      if (i<(rp_box_size(b)-1))
      {
        cout<<";"<<endl;
      }
    }
    cout<<endl;
  }
}

void rp_box_stack_cout(rp_box_stack boxes, int digits, int mode)
{
        int i;
        for (i = 0; i< boxes.size(); i++)
        {
                rp_box_cout(boxes.get(i), digits, mode);
        }
}

