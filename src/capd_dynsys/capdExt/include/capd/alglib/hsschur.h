/*************************************************************************
Copyright (c) 1992-2007 The University of Tennessee.  All rights reserved.

Contributors:
    * Sergey Bochkanov (ALGLIB project). Translation from FORTRAN to
      pseudocode.

See subroutines comments for additional copyrights.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are
met:

- Redistributions of source code must retain the above copyright
  notice, this list of conditions and the following disclaimer.

- Redistributions in binary form must reproduce the above copyright
  notice, this list of conditions and the following disclaimer listed
  in this license in the documentation and/or other materials
  provided with the distribution.

- Neither the name of the copyright holders nor the names of its
  contributors may be used to endorse or promote products derived from
  this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
"AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*************************************************************************/

#ifndef _hsschur_h
#define _hsschur_h

#include "capd/alglib/ap.h"

#include "capd/alglib/blas.h"
#include "capd/alglib/reflections.h"
#include "capd/alglib/rotations.h"


/*************************************************************************
Subroutine performing  the  Schur  decomposition  of  a  matrix  in  upper
Hessenberg form using the QR algorithm with multiple shifts.

The  source matrix  H  is  represented as  S'*H*S = T, where H - matrix in
upper Hessenberg form,  S - orthogonal matrix (Schur vectors),   T - upper
quasi-triangular matrix (with blocks of sizes  1x1  and  2x2  on  the main
diagonal).

Input parameters:
    H   -   matrix to be decomposed.
            Array whose indexes range within [1..N, 1..N].
    N   -   size of H, N>=0.


Output parameters:
    H   –   contains the matrix T.
            Array whose indexes range within [1..N, 1..N].
            All elements below the blocks on the main diagonal are equal
            to 0.
    S   -   contains Schur vectors.
            Array whose indexes range within [1..N, 1..N].

Note 1:
    The block structure of matrix T could be easily recognized: since  all
    the elements  below  the blocks are zeros, the elements a[i+1,i] which
    are equal to 0 show the block border.

Note 2:
    the algorithm  performance  depends  on  the  value  of  the  internal
    parameter NS of InternalSchurDecomposition  subroutine  which  defines
    the number of shifts in the QR algorithm (analog of  the  block  width
    in block matrix algorithms in linear algebra). If you require  maximum
    performance  on  your  machine,  it  is  recommended  to  adjust  this
    parameter manually.

Result:
    True, if the algorithm has converged and the parameters H and S contain
        the result.
    False, if the algorithm has not converged.

Algorithm implemented on the basis of subroutine DHSEQR (LAPACK 3.0 library).
*************************************************************************/
bool upperhessenbergschurdecomposition(ap::real_2d_array& h,
     int n,
     ap::real_2d_array& s);


void internalschurdecomposition(ap::real_2d_array& h,
     int n,
     int tneeded,
     int zneeded,
     ap::real_1d_array& wr,
     ap::real_1d_array& wi,
     ap::real_2d_array& z,
     int& info);


#endif
