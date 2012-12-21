
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


//TODO: fix the following translation
/*
void infix( Enode * e, string & s )
{
  Enode * p = NULL;
  string  tmp1, tmp2, tmp3;

//  ostringstream tmpnum;

  if( e -> isSymb( ) )
  {
 //     s+= " ";
      s+= e -> getName( );
 //     s+= " ";
  }
  else if ( e -> isNumb( ) )
  {
        s+= e -> getName();

  }
  else if ( e -> isTerm( ) )
  {

    bool tran = false;

    if ( !e -> getCdr() ->isEnil( ) && ( e -> isPlus() || e -> isMinus() || e -> isTimes() || e -> isPow() ))
    {
      s+= "(";
    }

   if ( e -> isSin() || e -> isCos() || e ->isTan() || e -> isArcSin() || e -> isArcCos() || e -> isArcTan() || e -> isExp() ||  e -> isLog() )
    {
        tran = true;
    }

    e -> getCar() ->print_str( tmp1 );
    p = e -> getCdr() ;

      if (!p->isEnil())
      {
        p->getCar()-> print_str( tmp2 );

        if (!p-> getCdr()->isEnil())
        {
                p = p-> cdr;
                p-> car->print_str( tmp3 );
        }
      }

      if (tran)
      {
          s+=tmp1;
          s+="(";
          s+= tmp2;
          s+= ")";
      }
      else
      {
              s+= tmp2 ;
              s+= tmp1 ;
              s+= tmp3 ;

            if ( !cdr->isEnil( ) && ( this -> isPlus() || this -> isMinus() || this ->isTimes() || this -> isPow() ))
            {
                s += ")";
            }
        }
  }
  else if ( isList( ) )
  {
    if ( isEnil( ) )
    {
      s += "-";
    }
    else
    {
//      s += "[";
      car->print_str( s );
 //     s+= "#";

      p = cdr;
      while ( !p->isEnil( ) )
      {
//      s += ", ";
        p->car->print_str( s );
        p = p->cdr;
      }

      s += "]";
    }
  }
  else if ( isDef( ) )
  {
//    s+= ":= ";
    car->print_str(s);
  }
  else if ( isEnil( ) )
  {
    s += "-";
  }
  else
    opensmt_error( "unknown case value" );
}
*/
