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
 * rp_stream.c                                                              *
 ****************************************************************************/

#include <string.h>
#include <ctype.h>
#include "rp_stream.h"

/* Open a stream from the string src */
/* Returns false if failure          */
int rp_stream_create_string(rp_stream * s, char * src)
{
  if ((src==NULL) || (strlen(src)==0))
  {
    return( 0 );
  }
  else
  {
    rp_stream_file(*s) = NULL;
    strcpy(rp_stream_str(*s),src);
    strcpy(rp_stream_filename(*s),"");
    rp_stream_col(*s) = -1;
    rp_stream_line(*s) = 0;
    rp_stream_index_buf(*s) = -1;
    return( 1 );
  }
}

/* Open a stream from the file filename */
/* Returns false if failure             */
int rp_stream_create_file(rp_stream * s, char * filename)
{
  FILE * f;
  if ((f = fopen(filename,"r"))==NULL)
  {
    return( 0 );
  }
  else
  {
    rp_stream_file(*s) = f;
    strcpy(rp_stream_str(*s),"");
    strcpy(rp_stream_filename(*s),filename);
    rp_stream_col(*s) = -1;
    rp_stream_line(*s) = 0;
    rp_stream_index_buf(*s) = -1;
    return( 1 );
  }
}

/* Destruction of a stream */
void rp_stream_destroy(rp_stream * s)
{
  if (rp_stream_file(*s)!=NULL)
  {
    fclose(rp_stream_file(*s));
  }
}

/* Returns true is the stream pointer is at the end of the stream */
int rp_stream_end(rp_stream s)
{
  if (rp_stream_index_buf(s)>=0)
  {
    return( 0 );
  }
  else
  {
    if (rp_stream_file(s)!=NULL)
    {
      return( feof(rp_stream_file(s))!=0 );
    }
    else
    {
      return( (rp_stream_col(s)>=0) && (rp_stream_char(s)=='\0') );
    }
  }
}

/* Get the next character from the stream */
char rp_stream_get_char(rp_stream s)
{
  if (rp_stream_index_buf(s)>=0)
  {
    return rp_stream_buf(s)[rp_stream_index_buf(s)--];
  }
  else
  {
    ++ rp_stream_col(s);
    if ((rp_stream_char(s)=='\0') && (rp_stream_file(s)!=NULL))
    {
      if (!feof(rp_stream_file(s)))
      {
	fgets(rp_stream_str(s),RP_STREAM_STR_SIZE,rp_stream_file(s));
	++ rp_stream_line(s);
	rp_stream_col(s) = 0;
      }
    }
    return( rp_stream_char(s) );
  }
}

/* To give back a character to a stream, returns true if success */
int rp_stream_unget_char(rp_stream s, char c)
{
  if (rp_stream_index_buf(s)<(RP_STREAM_BUF_SIZE-1))
  {
    rp_stream_buf(s)[++rp_stream_index_buf(s)] = c;
    return( 1 );
  }
  else
  {
    return( 0 );
  }
}

/* Eat up the next spaces in a stream */
void rp_stream_eat_space(rp_stream s)
{
  if (rp_stream_end(s))
  {
    return;
  }
  else
  {
    char c = rp_stream_get_char(s);
    while ((isspace(c) || iscntrl(c)) && (!rp_stream_end(s)))
    {
      c = rp_stream_get_char(s);
    }
    if (!rp_stream_end(s))
    {
      rp_stream_unget_char(s,c);
    }
  }
}

/* Print the stream position in dest */
void rp_stream_get_position(rp_stream s, char * dest)
{
  int col = rp_stream_col(s)-rp_stream_index_buf(s)-1;

  if (rp_stream_file(s)!=NULL)
  {
    sprintf(dest,"file %s, line %d, column %d",
	    rp_stream_filename(s),
	    rp_stream_line(s),
	    col);
  }
  else
  {
    sprintf(dest,"position %d",col);
  }
}

/* Display a stream on out */
void rp_stream_display(FILE * out, rp_stream s)
{
  rp_stream_get_char(s);
  while (!rp_stream_end(s))
  {
    if ((rp_stream_file(s)!=NULL) && (rp_stream_col(s)==0))
    {
      printf("%d:",rp_stream_line(s));
    }
    printf("%c",rp_stream_char(s));
    rp_stream_get_char(s);
  }
}
