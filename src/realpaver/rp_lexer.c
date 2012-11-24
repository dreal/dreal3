/****************************************************************************
 * RealPaver v. 1.0                                                         *
 *--------------------------------------------------------------------------*
 * Author: Laurent Granvilliers                                             *
 * Copyright (c) 1999-2003 Institut de Recherche en Informatique de Nantes  *
 * Copyright (c) 2004-2006 Laboratoire d'Informatique de Nantes Atlantique  *
 *--------------------------------------------------------------------------*
 * RealPaver is distributed WITHOUT ANY WARRANTY. Read the associated       *
 * COPYRIGHT file for more details.                                         *
 *--------------------------------------------------------------------------*
 * rp_lexer.c                                                               *
 ****************************************************************************/

#include <string.h>
#include <ctype.h>
#include "rp_lexer.h"

/* Creation of a lexical analyzer from a string */
int rp_lexer_create_string (rp_lexer * l, char * src)
{
  if (rp_stream_create_string(&rp_lexer_input(*l),src))
  {
    rp_lexer_token(*l) = RP_TOKEN_INIT;
    strcpy(rp_lexer_text(*l),"");
    rp_lexer_prev_token(*l) = RP_TOKEN_INIT;
    strcpy(rp_lexer_prev_text(*l),"");
    strcpy(rp_lexer_error_msg(*l),"");
    return( 1 );
  }
  else
  {
    return( 0 );
  }
}

/* Creation of a lexical analyzer from a file */
int rp_lexer_create_file (rp_lexer * l, char * filename)
{
  if (rp_stream_create_file(&rp_lexer_input(*l),filename))
  {
    rp_lexer_token(*l) = RP_TOKEN_INIT;
    strcpy(rp_lexer_text(*l),"");
    rp_lexer_prev_token(*l) = RP_TOKEN_INIT;
    strcpy(rp_lexer_prev_text(*l),"");
    strcpy(rp_lexer_error_msg(*l),"");
    return( 1 );
  }
  else
  {
    return( 0 );
  }
}

/* Destruction of a lexical analyzer */
void rp_lexer_destroy (rp_lexer * l)
{
  rp_stream_destroy(&rp_lexer_input(*l));
}

/* Compare two strings ignoring case */
int rp_string_equal_case(char * s1, char * s2)
{
  int len;
  if ((len = (int)strlen(s1))!=(int)strlen(s2))
  {
    return( 0 );
  }
  else
  {
    int i = 0;
    while ( (i<len) && (toupper(s1[i])==toupper(s2[i])))
    {
      ++i;
    }
    return( i==len );
  }
}

/* s := lower case(s) */
void rp_lexer_text_to_lower(char * s)
{
  int i;
  for (i=0; i<(int)strlen(s); ++i)
  {
    s[i] = tolower(s[i]);
  }
}

/* Eat comment in the stream */
void rp_lexer_eat_comment(rp_lexer l)
{
  char c;
  do
  {
    c = rp_stream_get_char(rp_lexer_input(l));
  }
  while ((c!='*') && (!rp_stream_end(rp_lexer_input(l))));
  if (!rp_stream_end(rp_lexer_input(l)))
  {
    c = rp_stream_get_char(rp_lexer_input(l));
    if (c!='/')
    {
      rp_stream_unget_char(rp_lexer_input(l),c);
      rp_lexer_eat_comment(l);
    }
  }
}

/* Stop the lexer with an error */
int rp_lexer_stop(rp_lexer l, char * msg)
{
  char tmp[RP_LEXER_ERRLEN];
  strcpy(rp_lexer_error_msg(l),"LEX ERROR: ");

  /* Position in file or string */
  rp_stream_get_position(rp_lexer_input(l),tmp);
  strcat(rp_lexer_error_msg(l),tmp);

  /* Error message */
  strcat(rp_lexer_error_msg(l),": ");
  strcat(rp_lexer_error_msg(l),msg);

  return( rp_lexer_token(l)=RP_TOKEN_ERROR );
}

/* Get a new token from l */
int rp_lexer_get_token(rp_lexer l)
{
  /* eat spaces */
  rp_stream_eat_space(rp_lexer_input(l));

  /* save the current token in the previous one */
  rp_lexer_prev_token(l) = rp_lexer_token(l);
  strcpy(rp_lexer_prev_text(l),rp_lexer_text(l));

  if (rp_stream_end(rp_lexer_input(l)))
  {
    return( rp_lexer_token(l)=RP_TOKEN_NO );
  }
  else
  {
    char c = rp_stream_get_char(rp_lexer_input(l));

    /* 'a'..'z' 'A'..'Z' */
    if (isalpha(c))
    {
      rp_stream_unget_char(rp_lexer_input(l),c);
      return( rp_lexer_get_ident(l) );
    }

    /* '0'..'9' '.' */
    else if (isdigit(c) || (c=='.'))
    {
      rp_stream_unget_char(rp_lexer_input(l),c);
      return( rp_lexer_get_number(l) );
    }

    /* plus */
    else if (c=='+')
    {
      strcpy(rp_lexer_text(l),"+");
      return( rp_lexer_token(l)=RP_TOKEN_PLUS );
    }

    /* minus */
    else if (c=='-')
    {
      char d = rp_stream_get_char(rp_lexer_input(l));
      if (d=='>')
      {
	strcpy(rp_lexer_text(l),"->");
	return( rp_lexer_token(l)=RP_TOKEN_IMPLY );
      }
      else
      {
	rp_stream_unget_char(rp_lexer_input(l),d);
	strcpy(rp_lexer_text(l),"-");
	return( rp_lexer_token(l)=RP_TOKEN_MINUS );
      }
    }

    /* multiplication */
    else if (c=='*')
    {
      strcpy(rp_lexer_text(l),"*");
      return( rp_lexer_token(l)=RP_TOKEN_MUL );
    }

    /* division */
    else if (c=='/')
    {
      char d = rp_stream_get_char(rp_lexer_input(l));
      if (d=='*')
      {
	rp_lexer_eat_comment(l);
	return( rp_lexer_get_token(l) );
      }
      else
      {
	rp_stream_unget_char(rp_lexer_input(l),d);
	strcpy(rp_lexer_text(l),"/");
	return( rp_lexer_token(l)=RP_TOKEN_DIV );
      }
    }

    /* exponent */
    else if (c=='^')
    {
      strcpy(rp_lexer_text(l),"^");
      return( rp_lexer_token(l)=RP_TOKEN_POW );
    }

    /* left round bracket */
    else if (c=='(')
    {
      strcpy(rp_lexer_text(l),"(");
      return( rp_lexer_token(l)=RP_TOKEN_LBR );
    }

    /* right round bracket */
    else if (c==')')
    {
      strcpy(rp_lexer_text(l),")");
      return( rp_lexer_token(l)=RP_TOKEN_RBR );
    }

    /* left square bracket */
    else if (c=='[')
    {
      strcpy(rp_lexer_text(l),"[");
      return( rp_lexer_token(l)=RP_TOKEN_SQLBR );
    }

    /* right square bracket */
    else if (c==']')
    {
      strcpy(rp_lexer_text(l),"]");
      return( rp_lexer_token(l)=RP_TOKEN_SQRBR );
    }

    /* comma */
    else if (c==',')
    {
      strcpy(rp_lexer_text(l),",");
      return( rp_lexer_token(l)=RP_TOKEN_COMMA );
    }

    /* left brace */
    else if (c=='{')
    {
      strcpy(rp_lexer_text(l),"{");
      return( rp_lexer_token(l)=RP_TOKEN_SETLBR );
    }

    /* right brace */
    else if (c=='}')
    {
      strcpy(rp_lexer_text(l),"}");
      return( rp_lexer_token(l)=RP_TOKEN_SETRBR );
    }

    /* tilde */
    else if (c=='~')
    {
      strcpy(rp_lexer_text(l),"~");
      return( rp_lexer_token(l)=RP_TOKEN_TILDE );
    }

    /* semicolon */
    else if (c==';')
    {
      strcpy(rp_lexer_text(l),";");
      return( rp_lexer_token(l)=RP_TOKEN_SEMICOLON );
    }

    /* sharp */
    else if (c=='#')
    {
      strcpy(rp_lexer_text(l),"#");
      return( rp_lexer_token(l)=RP_TOKEN_SHARP );
    }

    /* percent */
    else if (c=='%')
    {
      strcpy(rp_lexer_text(l),"%");
      return( rp_lexer_token(l)=RP_TOKEN_PERCENT );
    }

    /* : or := */
    else if (c==':')
    {
      char d = rp_stream_get_char(rp_lexer_input(l));
      if (d=='=')
      {
	strcpy(rp_lexer_text(l),":=");
	return( rp_lexer_token(l)=RP_TOKEN_SETVALUE );
      }
      else
      {
	rp_stream_unget_char(rp_lexer_input(l),d);
	strcpy(rp_lexer_text(l),":");
	return( rp_lexer_token(l)=RP_TOKEN_COLON );
      }
    }

    /* >= */
    else if (c=='>')
    {
      char d = rp_stream_get_char(rp_lexer_input(l));
      if (d=='=')
      {
	strcpy(rp_lexer_text(l),">=");
	return( rp_lexer_token(l)=RP_TOKEN_SUPEQUAL );
      }
      else
      {
	return( rp_lexer_stop(l,"'>' not supported") );
      }
    }

    /* <= */
    else if (c=='<')
    {
      char d = rp_stream_get_char(rp_lexer_input(l));
      if (d=='=')
      {
	strcpy(rp_lexer_text(l),"<=");
	return( rp_lexer_token(l)=RP_TOKEN_INFEQUAL );
      }
      else
      {
	return( rp_lexer_stop(l,"'<' not supported") );
      }
    }

    /* = */
    else if (c=='=')
    {
      strcpy(rp_lexer_text(l),"=");
      return( rp_lexer_token(l)=RP_TOKEN_EQUAL );
    }

    else
    {
      char tmp[RP_LEXER_ERRLEN];
      if (iscntrl(rp_stream_char(rp_lexer_input(l))))
      {
	sprintf(tmp,"control character '%u' unknown",
		rp_stream_char(rp_lexer_input(l)));
      }
      else
      {
	sprintf(tmp,"character '%c' unknown",
		rp_stream_char(rp_lexer_input(l)));
      }
      return( rp_lexer_stop(l,tmp) );
    }
  }
}

/* Get a sequence of characters c from l in dest such that f(c)    */
/* The function f has the following type as functions from ctype.h */
typedef int (*rp_accept_char)(int);
/* The sequence length belongs to 0..n-1                           */
/* If the length is equal to n-1 and the next character nc is      */
/* such that f(nc) then returns false (that means a too long token */
int rp_lexer_get_sequence(rp_lexer l, char * dest, int n, rp_accept_char f)
{
  int i = 0;
  dest[0] = rp_stream_get_char(rp_lexer_input(l));
  while (f(dest[i]) && (!rp_lexer_end(l)) && (i<n))
  {
    dest[++i] = rp_stream_get_char(rp_lexer_input(l));
  }
  if (i==n)
  {
    return( 0 );
  }
  else
  {
    rp_stream_unget_char(rp_lexer_input(l),dest[i]);
    dest[i] = '\0';
    return( 1 );
  }
}

/* Function verifying the allowed characters for identifiers */
int rp_isident(int c)
{
  return( isalnum(c) || c=='_' );
}

/* Get an identifier from l */
int rp_lexer_get_ident(rp_lexer l)
{
  /* first character necessarily ok */
  if (!rp_lexer_get_sequence(l,rp_lexer_text(l),
			     RP_LEXER_TOKLEN,rp_isident))
  {
    return( rp_lexer_stop(l,"identifier too long") );
  }
  else
  {
    /* INT */
    if (rp_string_equal_case(rp_lexer_text(l),"INT"))
    {
      return( rp_lexer_token(l)=RP_TOKEN_TYPE_INT );
    }

    /* REAL */
    if (rp_string_equal_case(rp_lexer_text(l),"REAL"))
    {
      return( rp_lexer_token(l)=RP_TOKEN_TYPE_REAL );
    }

    /* INFINITY */
    if (rp_string_equal_case(rp_lexer_text(l),"oo"))
    {
      return( rp_lexer_token(l)=RP_TOKEN_INFINITY );
    }

    /* SQRT */
    if (rp_string_equal_case(rp_lexer_text(l),"SQRT"))
    {
      return( rp_lexer_token(l)=RP_TOKEN_SQRT );
    }

    /* EXP */
    else if (rp_string_equal_case(rp_lexer_text(l),"EXP"))
    {
      return( rp_lexer_token(l)=RP_TOKEN_EXP );
    }

    /* LOG */
    else if (rp_string_equal_case(rp_lexer_text(l),"LOG"))
    {
      return( rp_lexer_token(l)=RP_TOKEN_LOG );
    }

    /* SIN */
    else if (rp_string_equal_case(rp_lexer_text(l),"SIN"))
    {
      return( rp_lexer_token(l)=RP_TOKEN_SIN );
    }

    /* COS */
    else if (rp_string_equal_case(rp_lexer_text(l),"COS"))
    {
      return( rp_lexer_token(l)=RP_TOKEN_COS );
    }

    /* TAN */
    else if (rp_string_equal_case(rp_lexer_text(l),"TAN"))
    {
      return( rp_lexer_token(l)=RP_TOKEN_TAN );
    }

    /* COSH */
    else if (rp_string_equal_case(rp_lexer_text(l),"COSH"))
    {
      return( rp_lexer_token(l)=RP_TOKEN_COSH );
    }

    /* SINH */
    else if (rp_string_equal_case(rp_lexer_text(l),"SINH"))
    {
      return( rp_lexer_token(l)=RP_TOKEN_SINH );
    }

    /* TANH */
    else if (rp_string_equal_case(rp_lexer_text(l),"TANH"))
    {
      return( rp_lexer_token(l)=RP_TOKEN_TANH );
    }

    /* ASIN */
    else if (rp_string_equal_case(rp_lexer_text(l),"ASIN"))
    {
      return( rp_lexer_token(l)=RP_TOKEN_ASIN );
    }

    /* ACOS */
    else if (rp_string_equal_case(rp_lexer_text(l),"ACOS"))
    {
      return( rp_lexer_token(l)=RP_TOKEN_ACOS );
    }

    /* ATAN */
    else if (rp_string_equal_case(rp_lexer_text(l),"ATAN"))
    {
      return( rp_lexer_token(l)=RP_TOKEN_ATAN );
    }

    /* ASINH */
    else if (rp_string_equal_case(rp_lexer_text(l),"ASINH"))
    {
      return( rp_lexer_token(l)=RP_TOKEN_ASINH );
    }

    /* ACOSH */
    else if (rp_string_equal_case(rp_lexer_text(l),"ACOSH"))
    {
      return( rp_lexer_token(l)=RP_TOKEN_ACOSH );
    }

    /* ATANH */
    else if (rp_string_equal_case(rp_lexer_text(l),"ATANH"))
    {
      return( rp_lexer_token(l)=RP_TOKEN_ATANH );
    }

    /* ABS */
    else if (rp_string_equal_case(rp_lexer_text(l),"ABS"))
    {
      return( rp_lexer_token(l)=RP_TOKEN_ABS );
    }

    /* MIN */
    else if (rp_string_equal_case(rp_lexer_text(l),"MIN"))
    {
      return( rp_lexer_token(l)=RP_TOKEN_MIN );
    }

    /* MAX */
    else if (rp_string_equal_case(rp_lexer_text(l),"MAX"))
    {
      return( rp_lexer_token(l)=RP_TOKEN_MAX );
    }

    /* PI */
    else if (rp_string_equal_case(rp_lexer_text(l),"PI"))
    {
      rp_lexer_text_to_lower(rp_lexer_text(l));
      return( rp_lexer_token(l)=RP_TOKEN_IDENT );
    }

    /* PIECEWISE */
    else if (rp_string_equal_case(rp_lexer_text(l),"PIECEWISE"))
    {
      rp_lexer_text_to_lower(rp_lexer_text(l));
      return( rp_lexer_token(l)=RP_TOKEN_PIECEWISE );
    }

    /* VAR */
    else if (rp_string_equal_case(rp_lexer_text(l),"VAR"))
    {
      rp_lexer_text_to_lower(rp_lexer_text(l));
      return( rp_lexer_token(l)=RP_TOKEN_BLOCK_VAR );
    }

    /* NUM */
    else if (rp_string_equal_case(rp_lexer_text(l),"NUM"))
    {
      rp_lexer_text_to_lower(rp_lexer_text(l));
      return( rp_lexer_token(l)=RP_TOKEN_BLOCK_NUM );
    }

    /* FUNC */
    else if (rp_string_equal_case(rp_lexer_text(l),"FUNC"))
    {
      rp_lexer_text_to_lower(rp_lexer_text(l));
      return( rp_lexer_token(l)=RP_TOKEN_BLOCK_FUNC );
    }

    /* CTR */
    else if (rp_string_equal_case(rp_lexer_text(l),"CTR"))
    {
      rp_lexer_text_to_lower(rp_lexer_text(l));
      return( rp_lexer_token(l)=RP_TOKEN_BLOCK_CTR );
    }

    /* END */
    else if (rp_string_equal_case(rp_lexer_text(l),"END"))
    {
      rp_lexer_text_to_lower(rp_lexer_text(l));
      return( rp_lexer_token(l)=RP_TOKEN_END );
    }

    /* PROBLEM */
    else if (rp_string_equal_case(rp_lexer_text(l),"PROBLEM"))
    {
      rp_lexer_text_to_lower(rp_lexer_text(l));
      return( rp_lexer_token(l)=RP_TOKEN_PROBLEM );
    }

    /* SOLVE */
    else if (rp_string_equal_case(rp_lexer_text(l),"SOLVE"))
    {
      rp_lexer_text_to_lower(rp_lexer_text(l));
      return( rp_lexer_token(l)=RP_TOKEN_SOLVE );
    }

    /* SPLIT */
    else if (rp_string_equal_case(rp_lexer_text(l),"SPLIT"))
    {
      rp_lexer_text_to_lower(rp_lexer_text(l));
      return( rp_lexer_token(l)=RP_TOKEN_SPLIT );
    }

    /* IDENTIFIER (not a reserved keyword) */
    else
    {
      return( rp_lexer_token(l)=RP_TOKEN_IDENT );
    }
  }
}

/* Get a number from l */
int rp_lexer_get_number(rp_lexer l)
{
  int i;
  /* first character necessarily ok */
  if (!rp_lexer_get_sequence(l,rp_lexer_text(l),
			     RP_LEXER_TOKLEN,isdigit))
  {
    return( rp_lexer_stop(l,"integral part of number too long") );
  }

  /* integer */
  if (rp_lexer_end(l))
  {
    return( rp_lexer_token(l)=RP_TOKEN_INTEGER );
  }

  /* decimal part? */
  i = strlen(rp_lexer_text(l));
  rp_lexer_text(l)[i] = rp_stream_get_char(rp_lexer_input(l));
  if (rp_lexer_text(l)[i]!='.')
  {
    /* integer */
    rp_stream_unget_char(rp_lexer_input(l),rp_lexer_text(l)[i]);
    rp_lexer_text(l)[i] = '\0';
    return( rp_lexer_token(l)=RP_TOKEN_INTEGER );
  }

  /* float, at least one digit in the decimal part */
  if (rp_lexer_end(l))
  {
    return( rp_lexer_stop(l,"decimal part of float unterminated") );
  }
  rp_lexer_text(l)[++i] = rp_stream_get_char(rp_lexer_input(l));
  if (!isdigit(rp_lexer_text(l)[i]))
  {
    return( rp_lexer_stop(l,"decimal part of float null") );
  }

  /* Get the rest of the decimal part */
  if (!rp_lexer_get_sequence(l,&(rp_lexer_text(l)[++i]),
			     RP_LEXER_TOKLEN-i-1,isdigit))
  {
    return( rp_lexer_stop(l,"float too long") );
  }

  /* exponent part? */
  i = strlen(rp_lexer_text(l));
  rp_lexer_text(l)[i] = rp_stream_get_char(rp_lexer_input(l));
  if (toupper(rp_lexer_text(l)[i])!='E')
  {
    /* float with no exponent */
    rp_stream_unget_char(rp_lexer_input(l),rp_lexer_text(l)[i]);
    rp_lexer_text(l)[i] = '\0';
    return( rp_lexer_token(l)=RP_TOKEN_FLOAT );
  }

  /* at least one digit in the exponent part and possibly a sign */
  if (rp_lexer_end(l))
  {
    return( rp_lexer_stop(l,"exponent part of float unterminated") );
  }
  rp_lexer_text(l)[++i] = rp_stream_get_char(rp_lexer_input(l));

  /* sign?*/
  if ((rp_lexer_text(l)[i]=='+') || (rp_lexer_text(l)[i]=='-'))
  {
    if (rp_lexer_end(l))
    {
      return( rp_lexer_stop(l,"exponent part of float null") );
    }
    rp_lexer_text(l)[++i] = rp_stream_get_char(rp_lexer_input(l));
  }

  /* unsigned exponent */
  if (!isdigit(rp_lexer_text(l)[i]))
  {
    return( rp_lexer_stop(l,"exponent part of float null") );
  }

  /* Get the rest of the decimal part */
  if (!rp_lexer_get_sequence(l,&(rp_lexer_text(l)[++i]),
			     RP_LEXER_TOKLEN-i-1,isdigit))
  {
    return( rp_lexer_stop(l,"float too long") );
  }

  return( rp_lexer_token(l)=RP_TOKEN_FLOAT );
}
