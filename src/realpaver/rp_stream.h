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
 * rp_stream.h                                                              *
 ****************************************************************************/

#ifndef RP_STREAM
#define RP_STREAM 1

#ifdef __cplusplus
extern "C" {
#endif

#include <stdio.h>
#include <stdlib.h>
#include "rp_config.h"
#include "rp_memory.h"

/* Maximum string length of an input string */
#define RP_STREAM_STR_SIZE 255
#define RP_STREAM_BUF_SIZE 10
#define RP_STREAM_FILENAME 100

typedef struct
{
  FILE * f;                            /* input stream to be read             */
  char   filename[RP_STREAM_FILENAME]; /* name of f                           */
  char   str[RP_STREAM_STR_SIZE];      /* current string to be read           */
  int    col;                          /* current char in s [-1..strlen(s)]   */
  int    line;                         /* current line in f [1..last_line(f)] */
  char   buf[RP_STREAM_BUF_SIZE];      /* characters that have been returned  */
  int    ibuf;                         /* index of last returned character    */
}
rp_stream_def;

typedef rp_stream_def rp_stream[1];

#define rp_stream_file(s)      (s)[0].f
#define rp_stream_filename(s)  (s)[0].filename
#define rp_stream_str(s)       (s)[0].str
#define rp_stream_col(s)       (s)[0].col
#define rp_stream_line(s)      (s)[0].line
#define rp_stream_buf(s)       (s)[0].buf
#define rp_stream_index_buf(s) (s)[0].ibuf
#define rp_stream_char(s)      (s)[0].str[(s)[0].col]

/* Creation of a stream from a string : returns false if failure */
int rp_stream_create_string (rp_stream * s, char * src);

/* Creation of a stream from a file : returns false if failure */
int rp_stream_create_file (rp_stream * s, char * filename);

/* Destruction of a stream */
void rp_stream_destroy (rp_stream * s);

/* Returns true is the stream pointer is at the end of the stream */
int rp_stream_end (rp_stream s);

/* Get the next character from the stream */
char rp_stream_get_char (rp_stream s);

/* To give back a character to a stream, returns true if success */
int rp_stream_unget_char (rp_stream s, char c);

/* Eat up the next spaces in a stream */
void rp_stream_eat_space (rp_stream s);

/* Print the stream position in dest */
void rp_stream_get_position (rp_stream s, char * dest);

/* Display a stream on out */
void rp_stream_display (FILE * out, rp_stream s);

#ifdef __cplusplus
}
#endif

#endif /* RP_STREAM */
