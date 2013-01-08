/// @addtogroup krak
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file dos16.c
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

  void myfread(ptr,size,n,f)
  CHAR_P ptr;
  int size,n;
  FILE *f;
  begin
    DWORD i,ile=size*n;
    CHAR_P ptri=ptr;
    for (i=0;i<ile;i++) *(ptri++)=getc(f);
  end;

  void myfwrite(ptr,size,n,f)
  CHAR_P ptr;
  int size,n;
  FILE *f;
  begin
    DWORD i,ile=size*n;
    CHAR_P ptri=ptr;

    for (i=0;i<ile;i++) putc(*(ptri++),f);
  end;

/// @}
