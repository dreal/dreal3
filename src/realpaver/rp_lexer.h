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
 * rp_lexer.h                                                               *
 ****************************************************************************/

#ifndef RP_LEXER
#define RP_LEXER 1

#ifdef __cplusplus
extern "C" {
#endif

#include <stdio.h>
#include <stdlib.h>
#include "rp_config.h"
#include "rp_memory.h"
#include "rp_stream.h"

/* ---------------------- */
/* Tokens (lexical units) */
/* ---------------------- */

/* Specific tokens */
#define RP_TOKEN_ERROR          10
#define RP_TOKEN_NO             11
#define RP_TOKEN_INIT           12

/* Operations and elementary functions */
#define RP_TOKEN_PLUS          100
#define RP_TOKEN_MINUS         101
#define RP_TOKEN_MUL           102
#define RP_TOKEN_DIV           103
#define RP_TOKEN_POW           104
#define RP_TOKEN_SQRT          105
#define RP_TOKEN_EXP           106
#define RP_TOKEN_LOG           107
#define RP_TOKEN_SIN           108
#define RP_TOKEN_COS           109
#define RP_TOKEN_TAN           110
#define RP_TOKEN_COSH          111
#define RP_TOKEN_SINH          112
#define RP_TOKEN_TANH          113
#define RP_TOKEN_ASIN          114
#define RP_TOKEN_ACOS          115
#define RP_TOKEN_ATAN          116
#define RP_TOKEN_ASINH         117
#define RP_TOKEN_ACOSH         118
#define RP_TOKEN_ATANH         119
#define RP_TOKEN_ABS           120
#define RP_TOKEN_MIN           121
#define RP_TOKEN_MAX           122

/* Operands */
#define RP_TOKEN_IDENT         200
#define RP_TOKEN_INTEGER       201
#define RP_TOKEN_FLOAT         202
#define RP_TOKEN_INFINITY      203

/* Brackets () [] {} and punctuation */
#define RP_TOKEN_LBR           300
#define RP_TOKEN_RBR           301
#define RP_TOKEN_SQLBR         302
#define RP_TOKEN_SQRBR         303
#define RP_TOKEN_SETLBR        304
#define RP_TOKEN_SETRBR        305
#define RP_TOKEN_COMMA         306
#define RP_TOKEN_COLON         307
#define RP_TOKEN_TILDE         308
#define RP_TOKEN_SEMICOLON     309
#define RP_TOKEN_SHARP         310
#define RP_TOKEN_PERCENT       311

/* Relations and value setting */
#define RP_TOKEN_SETVALUE      400
#define RP_TOKEN_EQUAL         401
#define RP_TOKEN_SUPEQUAL      402
#define RP_TOKEN_INFEQUAL      403
#define RP_TOKEN_PIECEWISE     404

/* Types */
#define RP_TOKEN_TYPE_INT      500
#define RP_TOKEN_TYPE_REAL     501

/* Keywords */
#define RP_TOKEN_BLOCK_VAR     600
#define RP_TOKEN_BLOCK_NUM     601
#define RP_TOKEN_BLOCK_CTR     602
#define RP_TOKEN_END           603
#define RP_TOKEN_PROBLEM       604
#define RP_TOKEN_SOLVE         605
#define RP_TOKEN_SPLIT         606
#define RP_TOKEN_BLOCK_FUNC    607

/* Connectives */
#define RP_TOKEN_IMPLY         700

/* -------------- */
/* The lexer type */
/* -------------- */

#define RP_LEXER_TOKLEN 50
#define RP_LEXER_ERRLEN 255

typedef struct
{
  rp_stream input;                       /* input stream           */
  int       token;                       /* current token          */
  char      text[RP_LEXER_TOKLEN];       /* text of current token  */
  int       prev_token;                  /* previous token         */
  char      prev_text[RP_LEXER_TOKLEN];  /* text of previous token */
  char      msge[RP_LEXER_ERRLEN];       /* error message          */
}
rp_lexer_def;

typedef rp_lexer_def rp_lexer[1];

#define rp_lexer_input(l)       (l)[0].input
#define rp_lexer_token(l)       (l)[0].token
#define rp_lexer_text(l)        (l)[0].text
#define rp_lexer_prev_token(l)  (l)[0].prev_token
#define rp_lexer_prev_text(l)   (l)[0].prev_text
#define rp_lexer_error_msg(l)   (l)[0].msge
#define rp_lexer_end(l) \
   ((rp_lexer_token(l)==RP_TOKEN_ERROR) || \
    (rp_lexer_token(l)==RP_TOKEN_NO))
#define rp_lexer_error(l) \
   (rp_lexer_token(l)==RP_TOKEN_ERROR)

/* Creation of a lexical analyzer from a string */
int rp_lexer_create_string (rp_lexer * l, char * src);

/* Creation of a lexical analyzer from a file */
int rp_lexer_create_file (rp_lexer * l, char * filename);

/* Destruction of a lexical analyzer */
void rp_lexer_destroy (rp_lexer * l);

/* Get a new token from l */
int rp_lexer_get_token  (rp_lexer l);
int rp_lexer_get_ident  (rp_lexer l);
int rp_lexer_get_number (rp_lexer l);

#ifdef __cplusplus
}
#endif

#endif /* RP_LEXER */
