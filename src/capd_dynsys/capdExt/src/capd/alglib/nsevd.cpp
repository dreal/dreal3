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



#include "capd/alglib/nsevd.h"


static void internaltrevc(const ap::real_2d_array& t,

     int n,

     int side,

     int howmny,

     ap::boolean_1d_array vselect,

     ap::real_2d_array& vl,

     ap::real_2d_array& vr,

     int& m,

     int& info);

static void internalhsevdlaln2(const bool& ltrans,

     const int& na,

     const int& nw,

     const double& smin,

     const double& ca,

     const ap::real_2d_array& a,

     const double& d1,

     const double& d2,

     const ap::real_2d_array& b,

     const double& wr,

     const double& wi,

     ap::boolean_1d_array& rswap4,

     ap::boolean_1d_array& zswap4,

     ap::integer_2d_array& ipivot44,

     ap::real_1d_array& civ4,

     ap::real_1d_array& crv4,

     ap::real_2d_array& x,

     double& scl,

     double& xnorm,

     int& info);

static void internalhsevdladiv(const double& a,

     const double& b,

     const double& c,

     const double& d,

     double& p,

     double& q);



/*************************************************************************

Finding eigenvalues and eigenvectors of a general matrix



The algorithm finds eigenvalues and eigenvectors of a general matrix by

using the QR algorithm with multiple shifts. The algorithm can find

eigenvalues and both left and right eigenvectors.



The right eigenvector is a vector x such that A*x = w*x, and the left

eigenvector is a vector y such that y'*A = w*y' (here y' implies a complex

conjugate transposition of vector y).



Input parameters:

    A       -   matrix. Array whose indexes range within [0..N-1, 0..N-1].

    N       -   size of matrix A.

    VNeeded -   flag controlling whether eigenvectors are needed or not.

                If VNeeded is equal to:

                 * 0, eigenvectors are not returned;

                 * 1, right eigenvectors are returned;

                 * 2, left eigenvectors are returned;

                 * 3, both left and right eigenvectors are returned.



Output parameters:

    WR      -   real parts of eigenvalues.

                Array whose index ranges within [0..N-1].

    WR      -   imaginary parts of eigenvalues.

                Array whose index ranges within [0..N-1].

    VL, VR  -   arrays of left and right eigenvectors (if they are needed).

                If WI[i]=0, the respective eigenvalue is a real number,

                and it corresponds to the column number I of matrices VL/VR.

                If WI[i]>0, we have a pair of complex conjugate numbers with

                positive and negative imaginary parts:

                    the first eigenvalue WR[i] + sqrt(-1)*WI[i];

                    the second eigenvalue WR[i+1] + sqrt(-1)*WI[i+1];

                    WI[i]>0

                    WI[i+1] = -WI[i] < 0

                In that case, the eigenvector  corresponding to the first

                eigenvalue is located in i and i+1 columns of matrices

                VL/VR (the column number i contains the real part, and the

                column number i+1 contains the imaginary part), and the vector

                corresponding to the second eigenvalue is a complex conjugate to

                the first vector.

                Arrays whose indexes range within [0..N-1, 0..N-1].



Result:

    True, if the algorithm has converged.

    False, if the algorithm has not converged.



Note 1:

    Some users may ask the following question: what if WI[N-1]>0?

    WI[N] must contain an eigenvalue which is complex conjugate to the

    N-th eigenvalue, but the array has only size N?

    The answer is as follows: such a situation cannot occur because the

    algorithm finds a pairs of eigenvalues, therefore, if WI[i]>0, I is

    strictly less than N-1.



Note 2:

    The algorithm performance depends on the value of the internal parameter

    NS of the InternalSchurDecomposition subroutine which defines the number

    of shifts in the QR algorithm (similarly to the block width in block-matrix

    algorithms of linear algebra). If you require maximum performance

    on your machine, it is recommended to adjust this parameter manually.





See also the InternalTREVC subroutine.



The algorithm is based on the LAPACK 3.0 library.

*************************************************************************/

bool rmatrixevd(ap::real_2d_array a,

     int n,

     int vneeded,

     ap::real_1d_array& wr,

     ap::real_1d_array& wi,

     ap::real_2d_array& vl,

     ap::real_2d_array& vr)

{

    bool result;

    ap::real_2d_array a1;

    ap::real_2d_array vl1;

    ap::real_2d_array vr1;

    ap::real_1d_array wr1;

    ap::real_1d_array wi1;

    int i;

  //  double mx;



    ap::ap_error::make_assertion(vneeded>=0&&vneeded<=3, "RMatrixEVD: incorrect VNeeded!");

    a1.setbounds(1, n, 1, n);

    for(i = 1; i <= n; i++)

    {

        ap::vmove(&a1(i, 1), &a(i-1, 0), ap::vlen(1,n));

    }

    result = nonsymmetricevd(a1, n, vneeded, wr1, wi1, vl1, vr1);

    if( result )

    {

        wr.setbounds(0, n-1);

        wi.setbounds(0, n-1);

        ap::vmove(&wr(0), &wr1(1), ap::vlen(0,n-1));

        ap::vmove(&wi(0), &wi1(1), ap::vlen(0,n-1));

        if( vneeded==2||vneeded==3 )

        {

            vl.setbounds(0, n-1, 0, n-1);

            for(i = 0; i <= n-1; i++)

            {

                ap::vmove(&vl(i, 0), &vl1(i+1, 1), ap::vlen(0,n-1));

            }

        }

        if( vneeded==1||vneeded==3 )

        {

            vr.setbounds(0, n-1, 0, n-1);

            for(i = 0; i <= n-1; i++)

            {

                ap::vmove(&vr(i, 0), &vr1(i+1, 1), ap::vlen(0,n-1));

            }

        }

    }

    return result;

}





/*************************************************************************

Obsolete 1-based subroutine

*************************************************************************/

bool nonsymmetricevd(ap::real_2d_array a,

     int n,

     int vneeded,

     ap::real_1d_array& wr,

     ap::real_1d_array& wi,

     ap::real_2d_array& vl,

     ap::real_2d_array& vr)

{

    bool result;

    ap::real_2d_array s;

    ap::real_1d_array tau;

    ap::boolean_1d_array sel;

    int i;

    int info;

    int m;



    ap::ap_error::make_assertion(vneeded>=0&&vneeded<=3, "NonSymmetricEVD: incorrect VNeeded!");

    if( vneeded==0 )

    {

        

        //

        // Eigen values only

        //

        toupperhessenberg(a, n, tau);

        internalschurdecomposition(a, n, 0, 0, wr, wi, s, info);

        result = info==0;

        return result;

    }

    

    //

    // Eigen values and vectors

    //

    toupperhessenberg(a, n, tau);

    unpackqfromupperhessenberg(a, n, tau, s);

    internalschurdecomposition(a, n, 1, 1, wr, wi, s, info);

    result = info==0;

    if( !result )

    {

        return result;

    }

    if( vneeded==1||vneeded==3 )

    {

        vr.setbounds(1, n, 1, n);

        for(i = 1; i <= n; i++)

        {

            ap::vmove(&vr(i, 1), &s(i, 1), ap::vlen(1,n));

        }

    }

    if( vneeded==2||vneeded==3 )

    {

        vl.setbounds(1, n, 1, n);

        for(i = 1; i <= n; i++)

        {

            ap::vmove(&vl(i, 1), &s(i, 1), ap::vlen(1,n));

        }

    }

    internaltrevc(a, n, vneeded, 1, sel, vl, vr, m, info);

    result = info==0;

    return result;

}





static void internaltrevc(const ap::real_2d_array& t,

     int n,

     int side,

     int howmny,

     ap::boolean_1d_array vselect,

     ap::real_2d_array& vl,

     ap::real_2d_array& vr,

     int& m,

     int& info)

{

    bool allv;

    bool bothv;

    bool leftv;

    bool over;

    bool pair;

    bool rightv;

    bool somev;

    int i;

    int ierr;

    int ii;

    int ip;

    int iis;

    int j;

    int j1;

    int j2;

    int jnxt;

    int k;

    int ki;

    int n2;

    double beta;

    double bignum;

    double emax;

   // double ovfl;

    double rec;

    double remax;

    double scl;

    double smin;

    double smlnum;

    double ulp;

    double unfl;

    double vcrit;

    double vmax;

    double wi;

    double wr;

    double xnorm;

    ap::real_2d_array x;

    ap::real_1d_array work;

    ap::real_1d_array temp;

    ap::real_2d_array temp11;

    ap::real_2d_array temp22;

    ap::real_2d_array temp11b;

    ap::real_2d_array temp21b;

    ap::real_2d_array temp12b;

    ap::real_2d_array temp22b;

    bool skipflag;

    int k1;

    int k2;

    int k3;

    int k4;

    double vt;

    ap::boolean_1d_array rswap4;

    ap::boolean_1d_array zswap4;

    ap::integer_2d_array ipivot44;

    ap::real_1d_array civ4;

    ap::real_1d_array crv4;



    x.setbounds(1, 2, 1, 2);

    temp11.setbounds(1, 1, 1, 1);

    temp11b.setbounds(1, 1, 1, 1);

    temp21b.setbounds(1, 2, 1, 1);

    temp12b.setbounds(1, 1, 1, 2);

    temp22b.setbounds(1, 2, 1, 2);

    temp22.setbounds(1, 2, 1, 2);

    work.setbounds(1, 3*n);

    temp.setbounds(1, n);

    rswap4.setbounds(1, 4);

    zswap4.setbounds(1, 4);

    ipivot44.setbounds(1, 4, 1, 4);

    civ4.setbounds(1, 4);

    crv4.setbounds(1, 4);

    if( howmny!=1 )

    {

        if( side==1||side==3 )

        {

            vr.setbounds(1, n, 1, n);

        }

        if( side==2||side==3 )

        {

            vl.setbounds(1, n, 1, n);

        }

    }

    

    //

    // Decode and test the input parameters

    //

    bothv = side==3;

    rightv = side==1||bothv;

    leftv = side==2||bothv;

    allv = howmny==2;

    over = howmny==1;

    somev = howmny==3;

    info = 0;

    if( n<0 )

    {

        info = -2;

        return;

    }

    if( !rightv&&!leftv )

    {

        info = -3;

        return;

    }

    if( !allv&&!over&&!somev )

    {

        info = -4;

        return;

    }

    

    //

    // Set M to the number of columns required to store the selected

    // eigenvectors, standardize the array SELECT if necessary, and

    // test MM.

    //

    if( somev )

    {

        m = 0;

        pair = false;

        for(j = 1; j <= n; j++)

        {

            if( pair )

            {

                pair = false;

                vselect(j) = false;

            }

            else

            {

                if( j<n )

                {

                    if( t(j+1,j)==0 )

                    {

                        if( vselect(j) )

                        {

                            m = m+1;

                        }

                    }

                    else

                    {

                        pair = true;

                        if( vselect(j)||vselect(j+1) )

                        {

                            vselect(j) = true;

                            m = m+2;

                        }

                    }

                }

                else

                {

                    if( vselect(n) )

                    {

                        m = m+1;

                    }

                }

            }

        }

    }

    else

    {

        m = n;

    }

    

    //

    // Quick return if possible.

    //

    if( n==0 )

    {

        return;

    }

    

    //

    // Set the constants to control overflow.

    //

    unfl = ap::minrealnumber;

   // ovfl = 1/unfl;

    ulp = ap::machineepsilon;

    smlnum = unfl*(n/ulp);

    bignum = (1-ulp)/smlnum;

    

    //

    // Compute 1-norm of each column of strictly upper triangular

    // part of T to control overflow in triangular solver.

    //

    work(1) = 0;

    for(j = 2; j <= n; j++)

    {

        work(j) = 0;

        for(i = 1; i <= j-1; i++)

        {

            work(j) = work(j)+fabs(t(i,j));

        }

    }

    

    //

    // Index IP is used to specify the real or complex eigenvalue:

    // IP = 0, real eigenvalue,

    //      1, first of conjugate complex pair: (wr,wi)

    //     -1, second of conjugate complex pair: (wr,wi)

    //

    n2 = 2*n;

    if( rightv )

    {

        

        //

        // Compute right eigenvectors.

        //

        ip = 0;

        iis = m;

        for(ki = n; ki >= 1; ki--)

        {

            skipflag = false;

            if( ip==1 )

            {

                skipflag = true;

            }

            else

            {

                if( ki!=1 )

                {

                    if( t(ki,ki-1)!=0 )

                    {

                        ip = -1;

                    }

                }

                if( somev )

                {

                    if( ip==0 )

                    {

                        if( !vselect(ki) )

                        {

                            skipflag = true;

                        }

                    }

                    else

                    {

                        if( !vselect(ki-1) )

                        {

                            skipflag = true;

                        }

                    }

                }

            }

            if( !skipflag )

            {

                

                //

                // Compute the KI-th eigenvalue (WR,WI).

                //

                wr = t(ki,ki);

                wi = 0;

                if( ip!=0 )

                {

                    wi = sqrt(fabs(t(ki,ki-1)))*sqrt(fabs(t(ki-1,ki)));

                }

                smin = ap::maxreal(ulp*(fabs(wr)+fabs(wi)), smlnum);

                if( ip==0 )

                {

                    

                    //

                    // Real right eigenvector

                    //

                    work(ki+n) = 1;

                    

                    //

                    // Form right-hand side

                    //

                    for(k = 1; k <= ki-1; k++)

                    {

                        work(k+n) = -t(k,ki);

                    }

                    

                    //

                    // Solve the upper quasi-triangular system:

                    //   (T(1:KI-1,1:KI-1) - WR)*X = SCALE*WORK.

                    //

                    jnxt = ki-1;

                    for(j = ki-1; j >= 1; j--)

                    {

                        if( j>jnxt )

                        {

                            continue;

                        }

                        j1 = j;

                        j2 = j;

                        jnxt = j-1;

                        if( j>1 )

                        {

                            if( t(j,j-1)!=0 )

                            {

                                j1 = j-1;

                                jnxt = j-2;

                            }

                        }

                        if( j1==j2 )

                        {

                            

                            //

                            // 1-by-1 diagonal block

                            //

                            temp11(1,1) = t(j,j);

                            temp11b(1,1) = work(j+n);

                            internalhsevdlaln2(false, 1, 1, smin, double(1), temp11, 1.0, 1.0, temp11b, wr, 0.0, rswap4, zswap4, ipivot44, civ4, crv4, x, scl, xnorm, ierr);

                            

                            //

                            // Scale X(1,1) to avoid overflow when updating

                            // the right-hand side.

                            //

                            if( xnorm>1 )

                            {

                                if( work(j)>bignum/xnorm )

                                {

                                    x(1,1) = x(1,1)/xnorm;

                                    scl = scl/xnorm;

                                }

                            }

                            

                            //

                            // Scale if necessary

                            //

                            if( scl!=1 )

                            {

                                k1 = n+1;

                                k2 = n+ki;

                                ap::vmul(&work(k1), ap::vlen(k1,k2), scl);

                            }

                            work(j+n) = x(1,1);

                            

                            //

                            // Update right-hand side

                            //

                            k1 = 1+n;

                            k2 = j-1+n;

                            k3 = j-1;

                            vt = -x(1,1);

                            ap::vadd(work.getvector(k1, k2), t.getcolumn(j, 1, k3), vt);

                        }

                        else

                        {

                            

                            //

                            // 2-by-2 diagonal block

                            //

                            temp22(1,1) = t(j-1,j-1);

                            temp22(1,2) = t(j-1,j);

                            temp22(2,1) = t(j,j-1);

                            temp22(2,2) = t(j,j);

                            temp21b(1,1) = work(j-1+n);

                            temp21b(2,1) = work(j+n);

                            internalhsevdlaln2(false, 2, 1, smin, 1.0, temp22, 1.0, 1.0, temp21b, wr, double(0), rswap4, zswap4, ipivot44, civ4, crv4, x, scl, xnorm, ierr);

                            

                            //

                            // Scale X(1,1) and X(2,1) to avoid overflow when

                            // updating the right-hand side.

                            //

                            if( xnorm>1 )

                            {

                                beta = ap::maxreal(work(j-1), work(j));

                                if( beta>bignum/xnorm )

                                {

                                    x(1,1) = x(1,1)/xnorm;

                                    x(2,1) = x(2,1)/xnorm;

                                    scl = scl/xnorm;

                                }

                            }

                            

                            //

                            // Scale if necessary

                            //

                            if( scl!=1 )

                            {

                                k1 = 1+n;

                                k2 = ki+n;

                                ap::vmul(&work(k1), ap::vlen(k1,k2), scl);

                            }

                            work(j-1+n) = x(1,1);

                            work(j+n) = x(2,1);

                            

                            //

                            // Update right-hand side

                            //

                            k1 = 1+n;

                            k2 = j-2+n;

                            k3 = j-2;

                            k4 = j-1;

                            vt = -x(1,1);

                            ap::vadd(work.getvector(k1, k2), t.getcolumn(k4, 1, k3), vt);

                            vt = -x(2,1);

                            ap::vadd(work.getvector(k1, k2), t.getcolumn(j, 1, k3), vt);

                        }

                    }

                    

                    //

                    // Copy the vector x or Q*x to VR and normalize.

                    //

                    if( !over )

                    {

                        k1 = 1+n;

                        k2 = ki+n;

                        ap::vmove(vr.getcolumn(iis, 1, ki), work.getvector(k1, k2));

                        ii = columnidxabsmax(vr, 1, ki, iis);

                        remax = 1/fabs(vr(ii,iis));

                        ap::vmul(vr.getcolumn(iis, 1, ki), remax);

                        for(k = ki+1; k <= n; k++)

                        {

                            vr(k,iis) = 0;

                        }

                    }

                    else

                    {

                        if( ki>1 )

                        {

                            ap::vmove(temp.getvector(1, n), vr.getcolumn(ki, 1, n));

                            matrixvectormultiply(vr, 1, n, 1, ki-1, false, work, 1+n, ki-1+n, 1.0, temp, 1, n, work(ki+n));

                            ap::vmove(vr.getcolumn(ki, 1, n), temp.getvector(1, n));

                        }

                        ii = columnidxabsmax(vr, 1, n, ki);

                        remax = 1/fabs(vr(ii,ki));

                        ap::vmul(vr.getcolumn(ki, 1, n), remax);

                    }

                }

                else

                {

                    

                    //

                    // Complex right eigenvector.

                    //

                    // Initial solve

                    //     [ (T(KI-1,KI-1) T(KI-1,KI) ) - (WR + I* WI)]*X = 0.

                    //     [ (T(KI,KI-1)   T(KI,KI)   )               ]

                    //

                    if( fabs(t(ki-1,ki))>=fabs(t(ki,ki-1)) )

                    {

                        work(ki-1+n) = 1;

                        work(ki+n2) = wi/t(ki-1,ki);

                    }

                    else

                    {

                        work(ki-1+n) = -wi/t(ki,ki-1);

                        work(ki+n2) = 1;

                    }

                    work(ki+n) = 0;

                    work(ki-1+n2) = 0;

                    

                    //

                    // Form right-hand side

                    //

                    for(k = 1; k <= ki-2; k++)

                    {

                        work(k+n) = -work(ki-1+n)*t(k,ki-1);

                        work(k+n2) = -work(ki+n2)*t(k,ki);

                    }

                    

                    //

                    // Solve upper quasi-triangular system:

                    // (T(1:KI-2,1:KI-2) - (WR+i*WI))*X = SCALE*(WORK+i*WORK2)

                    //

                    jnxt = ki-2;

                    for(j = ki-2; j >= 1; j--)

                    {

                        if( j>jnxt )

                        {

                            continue;

                        }

                        j1 = j;

                        j2 = j;

                        jnxt = j-1;

                        if( j>1 )

                        {

                            if( t(j,j-1)!=0 )

                            {

                                j1 = j-1;

                                jnxt = j-2;

                            }

                        }

                        if( j1==j2 )

                        {

                            

                            //

                            // 1-by-1 diagonal block

                            //

                            temp11(1,1) = t(j,j);

                            temp12b(1,1) = work(j+n);

                            temp12b(1,2) = work(j+n+n);

                            internalhsevdlaln2(false, 1, 2, smin, 1.0, temp11, 1.0, 1.0, temp12b, wr, wi, rswap4, zswap4, ipivot44, civ4, crv4, x, scl, xnorm, ierr);

                            

                            //

                            // Scale X(1,1) and X(1,2) to avoid overflow when

                            // updating the right-hand side.

                            //

                            if( xnorm>1 )

                            {

                                if( work(j)>bignum/xnorm )

                                {

                                    x(1,1) = x(1,1)/xnorm;

                                    x(1,2) = x(1,2)/xnorm;

                                    scl = scl/xnorm;

                                }

                            }

                            

                            //

                            // Scale if necessary

                            //

                            if( scl!=1 )

                            {

                                k1 = 1+n;

                                k2 = ki+n;

                                ap::vmul(&work(k1), ap::vlen(k1,k2), scl);

                                k1 = 1+n2;

                                k2 = ki+n2;

                                ap::vmul(&work(k1), ap::vlen(k1,k2), scl);

                            }

                            work(j+n) = x(1,1);

                            work(j+n2) = x(1,2);

                            

                            //

                            // Update the right-hand side

                            //

                            k1 = 1+n;

                            k2 = j-1+n;

                            k3 = 1;

                            k4 = j-1;

                            vt = -x(1,1);

                            ap::vadd(work.getvector(k1, k2), t.getcolumn(j, k3, k4), vt);

                            k1 = 1+n2;

                            k2 = j-1+n2;

                            k3 = 1;

                            k4 = j-1;

                            vt = -x(1,2);

                            ap::vadd(work.getvector(k1, k2), t.getcolumn(j, k3, k4), vt);

                        }

                        else

                        {

                            

                            //

                            // 2-by-2 diagonal block

                            //

                            temp22(1,1) = t(j-1,j-1);

                            temp22(1,2) = t(j-1,j);

                            temp22(2,1) = t(j,j-1);

                            temp22(2,2) = t(j,j);

                            temp22b(1,1) = work(j-1+n);

                            temp22b(1,2) = work(j-1+n+n);

                            temp22b(2,1) = work(j+n);

                            temp22b(2,2) = work(j+n+n);

                            internalhsevdlaln2(false, 2, 2, smin, 1.0, temp22, 1.0, 1.0, temp22b, wr, wi, rswap4, zswap4, ipivot44, civ4, crv4, x, scl, xnorm, ierr);

                            

                            //

                            // Scale X to avoid overflow when updating

                            // the right-hand side.

                            //

                            if( xnorm>1 )

                            {

                                beta = ap::maxreal(work(j-1), work(j));

                                if( beta>bignum/xnorm )

                                {

                                    rec = 1/xnorm;

                                    x(1,1) = x(1,1)*rec;

                                    x(1,2) = x(1,2)*rec;

                                    x(2,1) = x(2,1)*rec;

                                    x(2,2) = x(2,2)*rec;

                                    scl = scl*rec;

                                }

                            }

                            

                            //

                            // Scale if necessary

                            //

                            if( scl!=1 )

                            {

                                ap::vmul(&work(1+n), ap::vlen(1+n,ki+n), scl);

                                ap::vmul(&work(1+n2), ap::vlen(1+n2,ki+n2), scl);

                            }

                            work(j-1+n) = x(1,1);

                            work(j+n) = x(2,1);

                            work(j-1+n2) = x(1,2);

                            work(j+n2) = x(2,2);

                            

                            //

                            // Update the right-hand side

                            //

                            vt = -x(1,1);

                            ap::vadd(work.getvector(n+1, n+j-2), t.getcolumn(j-1, 1, j-2), vt);

                            vt = -x(2,1);

                            ap::vadd(work.getvector(n+1, n+j-2), t.getcolumn(j, 1, j-2), vt);

                            vt = -x(1,2);

                            ap::vadd(work.getvector(n2+1, n2+j-2), t.getcolumn(j-1, 1, j-2), vt);

                            vt = -x(2,2);

                            ap::vadd(work.getvector(n2+1, n2+j-2), t.getcolumn(j, 1, j-2), vt);

                        }

                    }

                    

                    //

                    // Copy the vector x or Q*x to VR and normalize.

                    //

                    if( !over )

                    {

                        ap::vmove(vr.getcolumn(iis-1, 1, ki), work.getvector(n+1, n+ki));

                        ap::vmove(vr.getcolumn(iis, 1, ki), work.getvector(n2+1, n2+ki));

                        emax = 0;

                        for(k = 1; k <= ki; k++)

                        {

                            emax = ap::maxreal(emax, fabs(vr(k,iis-1))+fabs(vr(k,iis)));

                        }

                        remax = 1/emax;

                        ap::vmul(vr.getcolumn(iis-1, 1, ki), remax);

                        ap::vmul(vr.getcolumn(iis, 1, ki), remax);

                        for(k = ki+1; k <= n; k++)

                        {

                            vr(k,iis-1) = 0;

                            vr(k,iis) = 0;

                        }

                    }

                    else

                    {

                        if( ki>2 )

                        {

                            ap::vmove(temp.getvector(1, n), vr.getcolumn(ki-1, 1, n));

                            matrixvectormultiply(vr, 1, n, 1, ki-2, false, work, 1+n, ki-2+n, 1.0, temp, 1, n, work(ki-1+n));

                            ap::vmove(vr.getcolumn(ki-1, 1, n), temp.getvector(1, n));

                            ap::vmove(temp.getvector(1, n), vr.getcolumn(ki, 1, n));

                            matrixvectormultiply(vr, 1, n, 1, ki-2, false, work, 1+n2, ki-2+n2, 1.0, temp, 1, n, work(ki+n2));

                            ap::vmove(vr.getcolumn(ki, 1, n), temp.getvector(1, n));

                        }

                        else

                        {

                            vt = work(ki-1+n);

                            ap::vmul(vr.getcolumn(ki-1, 1, n), vt);

                            vt = work(ki+n2);

                            ap::vmul(vr.getcolumn(ki, 1, n), vt);

                        }

                        emax = 0;

                        for(k = 1; k <= n; k++)

                        {

                            emax = ap::maxreal(emax, fabs(vr(k,ki-1))+fabs(vr(k,ki)));

                        }

                        remax = 1/emax;

                        ap::vmul(vr.getcolumn(ki-1, 1, n), remax);

                        ap::vmul(vr.getcolumn(ki, 1, n), remax);

                    }

                }

                iis = iis-1;

                if( ip!=0 )

                {

                    iis = iis-1;

                }

            }

            if( ip==1 )

            {

                ip = 0;

            }

            if( ip==-1 )

            {

                ip = 1;

            }

        }

    }

    if( leftv )

    {

        

        //

        // Compute left eigenvectors.

        //

        ip = 0;

        iis = 1;

        for(ki = 1; ki <= n; ki++)

        {

            skipflag = false;

            if( ip==-1 )

            {

                skipflag = true;

            }

            else

            {

                if( ki!=n )

                {

                    if( t(ki+1,ki)!=0 )

                    {

                        ip = 1;

                    }

                }

                if( somev )

                {

                    if( !vselect(ki) )

                    {

                        skipflag = true;

                    }

                }

            }

            if( !skipflag )

            {

                

                //

                // Compute the KI-th eigenvalue (WR,WI).

                //

                wr = t(ki,ki);

                wi = 0;

                if( ip!=0 )

                {

                    wi = sqrt(fabs(t(ki,ki+1)))*sqrt(fabs(t(ki+1,ki)));

                }

                smin = ap::maxreal(ulp*(fabs(wr)+fabs(wi)), smlnum);

                if( ip==0 )

                {

                    

                    //

                    // Real left eigenvector.

                    //

                    work(ki+n) = 1;

                    

                    //

                    // Form right-hand side

                    //

                    for(k = ki+1; k <= n; k++)

                    {

                        work(k+n) = -t(ki,k);

                    }

                    

                    //

                    // Solve the quasi-triangular system:

                    // (T(KI+1:N,KI+1:N) - WR)'*X = SCALE*WORK

                    //

                    vmax = 1;

                    vcrit = bignum;

                    jnxt = ki+1;

                    for(j = ki+1; j <= n; j++)

                    {

                        if( j<jnxt )

                        {

                            continue;

                        }

                        j1 = j;

                        j2 = j;

                        jnxt = j+1;

                        if( j<n )

                        {

                            if( t(j+1,j)!=0 )

                            {

                                j2 = j+1;

                                jnxt = j+2;

                            }

                        }

                        if( j1==j2 )

                        {

                            

                            //

                            // 1-by-1 diagonal block

                            //

                            // Scale if necessary to avoid overflow when forming

                            // the right-hand side.

                            //

                            if( work(j)>vcrit )

                            {

                                rec = 1/vmax;

                                ap::vmul(&work(ki+n), ap::vlen(ki+n,n+n), rec);

                                vmax = 1;

                                vcrit = bignum;

                            }

                            vt = ap::vdotproduct(t.getcolumn(j, ki+1, j-1), work.getvector(ki+1+n, j-1+n));

                            work(j+n) = work(j+n)-vt;

                            

                            //

                            // Solve (T(J,J)-WR)'*X = WORK

                            //

                            temp11(1,1) = t(j,j);

                            temp11b(1,1) = work(j+n);

                            internalhsevdlaln2(false, 1, 1, smin, 1.0, temp11, 1.0, 1.0, temp11b, wr, double(0), rswap4, zswap4, ipivot44, civ4, crv4, x, scl, xnorm, ierr);

                            

                            //

                            // Scale if necessary

                            //

                            if( scl!=1 )

                            {

                                ap::vmul(&work(ki+n), ap::vlen(ki+n,n+n), scl);

                            }

                            work(j+n) = x(1,1);

                            vmax = ap::maxreal(fabs(work(j+n)), vmax);

                            vcrit = bignum/vmax;

                        }

                        else

                        {

                            

                            //

                            // 2-by-2 diagonal block

                            //

                            // Scale if necessary to avoid overflow when forming

                            // the right-hand side.

                            //

                            beta = ap::maxreal(work(j), work(j+1));

                            if( beta>vcrit )

                            {

                                rec = 1/vmax;

                                ap::vmul(&work(ki+n), ap::vlen(ki+n,n+n), rec);

                                vmax = 1;

                                vcrit = bignum;

                            }

                            vt = ap::vdotproduct(t.getcolumn(j, ki+1, j-1), work.getvector(ki+1+n, j-1+n));

                            work(j+n) = work(j+n)-vt;

                            vt = ap::vdotproduct(t.getcolumn(j+1, ki+1, j-1), work.getvector(ki+1+n, j-1+n));

                            work(j+1+n) = work(j+1+n)-vt;

                            

                            //

                            // Solve

                            //    [T(J,J)-WR   T(J,J+1)     ]'* X = SCALE*( WORK1 )

                            //    [T(J+1,J)    T(J+1,J+1)-WR]             ( WORK2 )

                            //

                            temp22(1,1) = t(j,j);

                            temp22(1,2) = t(j,j+1);

                            temp22(2,1) = t(j+1,j);

                            temp22(2,2) = t(j+1,j+1);

                            temp21b(1,1) = work(j+n);

                            temp21b(2,1) = work(j+1+n);

                            internalhsevdlaln2(true, 2, 1, smin, 1.0, temp22, 1.0, 1.0, temp21b, wr, double(0), rswap4, zswap4, ipivot44, civ4, crv4, x, scl, xnorm, ierr);

                            

                            //

                            // Scale if necessary

                            //

                            if( scl!=1 )

                            {

                                ap::vmul(&work(ki+n), ap::vlen(ki+n,n+n), scl);

                            }

                            work(j+n) = x(1,1);

                            work(j+1+n) = x(2,1);

                            vmax = ap::maxreal(fabs(work(j+n)), ap::maxreal(fabs(work(j+1+n)), vmax));

                            vcrit = bignum/vmax;

                        }

                    }

                    

                    //

                    // Copy the vector x or Q*x to VL and normalize.

                    //

                    if( !over )

                    {

                        ap::vmove(vl.getcolumn(iis, ki, n), work.getvector(ki+n, n+n));

                        ii = columnidxabsmax(vl, ki, n, iis);

                        remax = 1/fabs(vl(ii,iis));

                        ap::vmul(vl.getcolumn(iis, ki, n), remax);

                        for(k = 1; k <= ki-1; k++)

                        {

                            vl(k,iis) = 0;

                        }

                    }

                    else

                    {

                        if( ki<n )

                        {

                            ap::vmove(temp.getvector(1, n), vl.getcolumn(ki, 1, n));

                            matrixvectormultiply(vl, 1, n, ki+1, n, false, work, ki+1+n, n+n, 1.0, temp, 1, n, work(ki+n));

                            ap::vmove(vl.getcolumn(ki, 1, n), temp.getvector(1, n));

                        }

                        ii = columnidxabsmax(vl, 1, n, ki);

                        remax = 1/fabs(vl(ii,ki));

                        ap::vmul(vl.getcolumn(ki, 1, n), remax);

                    }

                }

                else

                {

                    

                    //

                    // Complex left eigenvector.

                    //

                    // Initial solve:

                    //   ((T(KI,KI)    T(KI,KI+1) )' - (WR - I* WI))*X = 0.

                    //   ((T(KI+1,KI) T(KI+1,KI+1))                )

                    //

                    if( fabs(t(ki,ki+1))>=fabs(t(ki+1,ki)) )

                    {

                        work(ki+n) = wi/t(ki,ki+1);

                        work(ki+1+n2) = 1;

                    }

                    else

                    {

                        work(ki+n) = 1;

                        work(ki+1+n2) = -wi/t(ki+1,ki);

                    }

                    work(ki+1+n) = 0;

                    work(ki+n2) = 0;

                    

                    //

                    // Form right-hand side

                    //

                    for(k = ki+2; k <= n; k++)

                    {

                        work(k+n) = -work(ki+n)*t(ki,k);

                        work(k+n2) = -work(ki+1+n2)*t(ki+1,k);

                    }

                    

                    //

                    // Solve complex quasi-triangular system:

                    // ( T(KI+2,N:KI+2,N) - (WR-i*WI) )*X = WORK1+i*WORK2

                    //

                    vmax = 1;

                    vcrit = bignum;

                    jnxt = ki+2;

                    for(j = ki+2; j <= n; j++)

                    {

                        if( j<jnxt )

                        {

                            continue;

                        }

                        j1 = j;

                        j2 = j;

                        jnxt = j+1;

                        if( j<n )

                        {

                            if( t(j+1,j)!=0 )

                            {

                                j2 = j+1;

                                jnxt = j+2;

                            }

                        }

                        if( j1==j2 )

                        {

                            

                            //

                            // 1-by-1 diagonal block

                            //

                            // Scale if necessary to avoid overflow when

                            // forming the right-hand side elements.

                            //

                            if( work(j)>vcrit )

                            {

                                rec = 1/vmax;

                                ap::vmul(&work(ki+n), ap::vlen(ki+n,n+n), rec);

                                ap::vmul(&work(ki+n2), ap::vlen(ki+n2,n+n2), rec);

                                vmax = 1;

                                vcrit = bignum;

                            }

                            vt = ap::vdotproduct(t.getcolumn(j, ki+2, j-1), work.getvector(ki+2+n, j-1+n));

                            work(j+n) = work(j+n)-vt;

                            vt = ap::vdotproduct(t.getcolumn(j, ki+2, j-1), work.getvector(ki+2+n2, j-1+n2));

                            work(j+n2) = work(j+n2)-vt;

                            

                            //

                            // Solve (T(J,J)-(WR-i*WI))*(X11+i*X12)= WK+I*WK2

                            //

                            temp11(1,1) = t(j,j);

                            temp12b(1,1) = work(j+n);

                            temp12b(1,2) = work(j+n+n);

                            internalhsevdlaln2(false, 1, 2, smin, 1.0, temp11, 1.0, 1.0, temp12b, wr, -wi, rswap4, zswap4, ipivot44, civ4, crv4, x, scl, xnorm, ierr);

                            

                            //

                            // Scale if necessary

                            //

                            if( scl!=1 )

                            {

                                ap::vmul(&work(ki+n), ap::vlen(ki+n,n+n), scl);

                                ap::vmul(&work(ki+n2), ap::vlen(ki+n2,n+n2), scl);

                            }

                            work(j+n) = x(1,1);

                            work(j+n2) = x(1,2);

                            vmax = ap::maxreal(fabs(work(j+n)), ap::maxreal(fabs(work(j+n2)), vmax));

                            vcrit = bignum/vmax;

                        }

                        else

                        {

                            

                            //

                            // 2-by-2 diagonal block

                            //

                            // Scale if necessary to avoid overflow when forming

                            // the right-hand side elements.

                            //

                            beta = ap::maxreal(work(j), work(j+1));

                            if( beta>vcrit )

                            {

                                rec = 1/vmax;

                                ap::vmul(&work(ki+n), ap::vlen(ki+n,n+n), rec);

                                ap::vmul(&work(ki+n2), ap::vlen(ki+n2,n+n2), rec);

                                vmax = 1;

                                vcrit = bignum;

                            }

                            vt = ap::vdotproduct(t.getcolumn(j, ki+2, j-1), work.getvector(ki+2+n, j-1+n));

                            work(j+n) = work(j+n)-vt;

                            vt = ap::vdotproduct(t.getcolumn(j, ki+2, j-1), work.getvector(ki+2+n2, j-1+n2));

                            work(j+n2) = work(j+n2)-vt;

                            vt = ap::vdotproduct(t.getcolumn(j+1, ki+2, j-1), work.getvector(ki+2+n, j-1+n));

                            work(j+1+n) = work(j+1+n)-vt;

                            vt = ap::vdotproduct(t.getcolumn(j+1, ki+2, j-1), work.getvector(ki+2+n2, j-1+n2));

                            work(j+1+n2) = work(j+1+n2)-vt;

                            

                            //

                            // Solve 2-by-2 complex linear equation

                            //   ([T(j,j)   T(j,j+1)  ]'-(wr-i*wi)*I)*X = SCALE*B

                            //   ([T(j+1,j) T(j+1,j+1)]             )

                            //

                            temp22(1,1) = t(j,j);

                            temp22(1,2) = t(j,j+1);

                            temp22(2,1) = t(j+1,j);

                            temp22(2,2) = t(j+1,j+1);

                            temp22b(1,1) = work(j+n);

                            temp22b(1,2) = work(j+n+n);

                            temp22b(2,1) = work(j+1+n);

                            temp22b(2,2) = work(j+1+n+n);

                            internalhsevdlaln2(true, 2, 2, smin, 1.0, temp22, 1.0, 1.0, temp22b, wr, -wi, rswap4, zswap4, ipivot44, civ4, crv4, x, scl, xnorm, ierr);

                            

                            //

                            // Scale if necessary

                            //

                            if( scl!=1 )

                            {

                                ap::vmul(&work(ki+n), ap::vlen(ki+n,n+n), scl);

                                ap::vmul(&work(ki+n2), ap::vlen(ki+n2,n+n2), scl);

                            }

                            work(j+n) = x(1,1);

                            work(j+n2) = x(1,2);

                            work(j+1+n) = x(2,1);

                            work(j+1+n2) = x(2,2);

                            vmax = ap::maxreal(fabs(x(1,1)), vmax);

                            vmax = ap::maxreal(fabs(x(1,2)), vmax);

                            vmax = ap::maxreal(fabs(x(2,1)), vmax);

                            vmax = ap::maxreal(fabs(x(2,2)), vmax);

                            vcrit = bignum/vmax;

                        }

                    }

                    

                    //

                    // Copy the vector x or Q*x to VL and normalize.

                    //

                    if( !over )

                    {

                        ap::vmove(vl.getcolumn(iis, ki, n), work.getvector(ki+n, n+n));

                        ap::vmove(vl.getcolumn(iis+1, ki, n), work.getvector(ki+n2, n+n2));

                        emax = 0;

                        for(k = ki; k <= n; k++)

                        {

                            emax = ap::maxreal(emax, fabs(vl(k,iis))+fabs(vl(k,iis+1)));

                        }

                        remax = 1/emax;

                        ap::vmul(vl.getcolumn(iis, ki, n), remax);

                        ap::vmul(vl.getcolumn(iis+1, ki, n), remax);

                        for(k = 1; k <= ki-1; k++)

                        {

                            vl(k,iis) = 0;

                            vl(k,iis+1) = 0;

                        }

                    }

                    else

                    {

                        if( ki<n-1 )

                        {

                            ap::vmove(temp.getvector(1, n), vl.getcolumn(ki, 1, n));

                            matrixvectormultiply(vl, 1, n, ki+2, n, false, work, ki+2+n, n+n, 1.0, temp, 1, n, work(ki+n));

                            ap::vmove(vl.getcolumn(ki, 1, n), temp.getvector(1, n));

                            ap::vmove(temp.getvector(1, n), vl.getcolumn(ki+1, 1, n));

                            matrixvectormultiply(vl, 1, n, ki+2, n, false, work, ki+2+n2, n+n2, 1.0, temp, 1, n, work(ki+1+n2));

                            ap::vmove(vl.getcolumn(ki+1, 1, n), temp.getvector(1, n));

                        }

                        else

                        {

                            vt = work(ki+n);

                            ap::vmul(vl.getcolumn(ki, 1, n), vt);

                            vt = work(ki+1+n2);

                            ap::vmul(vl.getcolumn(ki+1, 1, n), vt);

                        }

                        emax = 0;

                        for(k = 1; k <= n; k++)

                        {

                            emax = ap::maxreal(emax, fabs(vl(k,ki))+fabs(vl(k,ki+1)));

                        }

                        remax = 1/emax;

                        ap::vmul(vl.getcolumn(ki, 1, n), remax);

                        ap::vmul(vl.getcolumn(ki+1, 1, n), remax);

                    }

                }

                iis = iis+1;

                if( ip!=0 )

                {

                    iis = iis+1;

                }

            }

            if( ip==-1 )

            {

                ip = 0;

            }

            if( ip==1 )

            {

                ip = -1;

            }

        }

    }

}





static void internalhsevdlaln2(const bool& ltrans,

     const int& na,

     const int& nw,

     const double& smin,

     const double& ca,

     const ap::real_2d_array& a,

     const double& d1,

     const double& d2,

     const ap::real_2d_array& b,

     const double& wr,

     const double& wi,

     ap::boolean_1d_array& rswap4,

     ap::boolean_1d_array& zswap4,

     ap::integer_2d_array& ipivot44,

     ap::real_1d_array& civ4,

     ap::real_1d_array& crv4,

     ap::real_2d_array& x,

     double& scl,

     double& xnorm,

     int& info)

{

    int icmax;

    int j;

    double bbnd;

    double bi1;

    double bi2;

    double bignum;

    double bnorm;

    double br1;

    double br2;

    double ci21;

    double ci22;

    double cmax;

    double cnorm;

    double cr21;

    double cr22;

    double csi;

    double csr;

    double li21;

    double lr21;

    double smini;

    double smlnum;

    double temp;

    double u22abs;

    double ui11;

    double ui11r;

    double ui12;

    double ui12s;

    double ui22;

    double ur11;

    double ur11r;

    double ur12;

    double ur12s;

    double ur22;

    double xi1;

    double xi2;

    double xr1;

    double xr2;

    double tmp1;

    double tmp2;



    zswap4(1) = false;

    zswap4(2) = false;

    zswap4(3) = true;

    zswap4(4) = true;

    rswap4(1) = false;

    rswap4(2) = true;

    rswap4(3) = false;

    rswap4(4) = true;

    ipivot44(1,1) = 1;

    ipivot44(2,1) = 2;

    ipivot44(3,1) = 3;

    ipivot44(4,1) = 4;

    ipivot44(1,2) = 2;

    ipivot44(2,2) = 1;

    ipivot44(3,2) = 4;

    ipivot44(4,2) = 3;

    ipivot44(1,3) = 3;

    ipivot44(2,3) = 4;

    ipivot44(3,3) = 1;

    ipivot44(4,3) = 2;

    ipivot44(1,4) = 4;

    ipivot44(2,4) = 3;

    ipivot44(3,4) = 2;

    ipivot44(4,4) = 1;

    smlnum = 2*ap::minrealnumber;

    bignum = 1/smlnum;

    smini = ap::maxreal(smin, smlnum);

    

    //

    // Don't check for input errors

    //

    info = 0;

    

    //

    // Standard Initializations

    //

    scl = 1;

    if( na==1 )

    {

        

        //

        // 1 x 1  (i.e., scalar) system   C X = B

        //

        if( nw==1 )

        {

            

            //

            // Real 1x1 system.

            //

            // C = ca A - w D

            //

            csr = ca*a(1,1)-wr*d1;

            cnorm = fabs(csr);

            

            //

            // If | C | < SMINI, use C = SMINI

            //

            if( cnorm<smini )

            {

                csr = smini;

                cnorm = smini;

                info = 1;

            }

            

            //

            // Check scaling for  X = B / C

            //

            bnorm = fabs(b(1,1));

            if( cnorm<1&&bnorm>1 )

            {

                if( bnorm>bignum*cnorm )

                {

                    scl = 1/bnorm;

                }

            }

            

            //

            // Compute X

            //

            x(1,1) = b(1,1)*scl/csr;

            xnorm = fabs(x(1,1));

        }

        else

        {

            

            //

            // Complex 1x1 system (w is complex)

            //

            // C = ca A - w D

            //

            csr = ca*a(1,1)-wr*d1;

            csi = -wi*d1;

            cnorm = fabs(csr)+fabs(csi);

            

            //

            // If | C | < SMINI, use C = SMINI

            //

            if( cnorm<smini )

            {

                csr = smini;

                csi = 0;

                cnorm = smini;

                info = 1;

            }

            

            //

            // Check scaling for  X = B / C

            //

            bnorm = fabs(b(1,1))+fabs(b(1,2));

            if( cnorm<1&&bnorm>1 )

            {

                if( bnorm>bignum*cnorm )

                {

                    scl = 1/bnorm;

                }

            }

            

            //

            // Compute X

            //

            internalhsevdladiv(scl*b(1,1), scl*b(1,2), csr, csi, tmp1, tmp2);

            x(1,1) = tmp1;

            x(1,2) = tmp2;

            xnorm = fabs(x(1,1))+fabs(x(1,2));

        }

    }

    else

    {

        

        //

        // 2x2 System

        //

        // Compute the real part of  C = ca A - w D  (or  ca A' - w D )

        //

        crv4(1+0) = ca*a(1,1)-wr*d1;

        crv4(2+2) = ca*a(2,2)-wr*d2;

        if( ltrans )

        {

            crv4(1+2) = ca*a(2,1);

            crv4(2+0) = ca*a(1,2);

        }

        else

        {

            crv4(2+0) = ca*a(2,1);

            crv4(1+2) = ca*a(1,2);

        }

        if( nw==1 )

        {

            

            //

            // Real 2x2 system  (w is real)

            //

            // Find the largest element in C

            //

            cmax = 0;

            icmax = 0;

            for(j = 1; j <= 4; j++)

            {

                if( fabs(crv4(j))>cmax )

                {

                    cmax = fabs(crv4(j));

                    icmax = j;

                }

            }

            

            //

            // If norm(C) < SMINI, use SMINI*identity.

            //

            if( cmax<smini )

            {

                bnorm = ap::maxreal(fabs(b(1,1)), fabs(b(2,1)));

                if( smini<1&&bnorm>1 )

                {

                    if( bnorm>bignum*smini )

                    {

                        scl = 1/bnorm;

                    }

                }

                temp = scl/smini;

                x(1,1) = temp*b(1,1);

                x(2,1) = temp*b(2,1);

                xnorm = temp*bnorm;

                info = 1;

                return;

            }

            

            //

            // Gaussian elimination with complete pivoting.

            //

            ur11 = crv4(icmax);

            cr21 = crv4(ipivot44(2,icmax));

            ur12 = crv4(ipivot44(3,icmax));

            cr22 = crv4(ipivot44(4,icmax));

            ur11r = 1/ur11;

            lr21 = ur11r*cr21;

            ur22 = cr22-ur12*lr21;

            

            //

            // If smaller pivot < SMINI, use SMINI

            //

            if( fabs(ur22)<smini )

            {

                ur22 = smini;

                info = 1;

            }

            if( rswap4(icmax) )

            {

                br1 = b(2,1);

                br2 = b(1,1);

            }

            else

            {

                br1 = b(1,1);

                br2 = b(2,1);

            }

            br2 = br2-lr21*br1;

            bbnd = ap::maxreal(fabs(br1*(ur22*ur11r)), fabs(br2));

            if( bbnd>1&&fabs(ur22)<1 )

            {

                if( bbnd>=bignum*fabs(ur22) )

                {

                    scl = 1/bbnd;

                }

            }

            xr2 = br2*scl/ur22;

            xr1 = scl*br1*ur11r-xr2*(ur11r*ur12);

            if( zswap4(icmax) )

            {

                x(1,1) = xr2;

                x(2,1) = xr1;

            }

            else

            {

                x(1,1) = xr1;

                x(2,1) = xr2;

            }

            xnorm = ap::maxreal(fabs(xr1), fabs(xr2));

            

            //

            // Further scaling if  norm(A) norm(X) > overflow

            //

            if( xnorm>1&&cmax>1 )

            {

                if( xnorm>bignum/cmax )

                {

                    temp = cmax/bignum;

                    x(1,1) = temp*x(1,1);

                    x(2,1) = temp*x(2,1);

                    xnorm = temp*xnorm;

                    scl = temp*scl;

                }

            }

        }

        else

        {

            

            //

            // Complex 2x2 system  (w is complex)

            //

            // Find the largest element in C

            //

            civ4(1+0) = -wi*d1;

            civ4(2+0) = 0;

            civ4(1+2) = 0;

            civ4(2+2) = -wi*d2;

            cmax = 0;

            icmax = 0;

            for(j = 1; j <= 4; j++)

            {

                if( fabs(crv4(j))+fabs(civ4(j))>cmax )

                {

                    cmax = fabs(crv4(j))+fabs(civ4(j));

                    icmax = j;

                }

            }

            

            //

            // If norm(C) < SMINI, use SMINI*identity.

            //

            if( cmax<smini )

            {

                bnorm = ap::maxreal(fabs(b(1,1))+fabs(b(1,2)), fabs(b(2,1))+fabs(b(2,2)));

                if( smini<1&&bnorm>1 )

                {

                    if( bnorm>bignum*smini )

                    {

                        scl = 1/bnorm;

                    }

                }

                temp = scl/smini;

                x(1,1) = temp*b(1,1);

                x(2,1) = temp*b(2,1);

                x(1,2) = temp*b(1,2);

                x(2,2) = temp*b(2,2);

                xnorm = temp*bnorm;

                info = 1;

                return;

            }

            

            //

            // Gaussian elimination with complete pivoting.

            //

            ur11 = crv4(icmax);

            ui11 = civ4(icmax);

            cr21 = crv4(ipivot44(2,icmax));

            ci21 = civ4(ipivot44(2,icmax));

            ur12 = crv4(ipivot44(3,icmax));

            ui12 = civ4(ipivot44(3,icmax));

            cr22 = crv4(ipivot44(4,icmax));

            ci22 = civ4(ipivot44(4,icmax));

            if( icmax==1||icmax==4 )

            {

                

                //

                // Code when off-diagonals of pivoted C are real

                //

                if( fabs(ur11)>fabs(ui11) )

                {

                    temp = ui11/ur11;

                    ur11r = 1/(ur11*(1+ap::sqr(temp)));

                    ui11r = -temp*ur11r;

                }

                else

                {

                    temp = ur11/ui11;

                    ui11r = -1/(ui11*(1+ap::sqr(temp)));

                    ur11r = -temp*ui11r;

                }

                lr21 = cr21*ur11r;

                li21 = cr21*ui11r;

                ur12s = ur12*ur11r;

                ui12s = ur12*ui11r;

                ur22 = cr22-ur12*lr21;

                ui22 = ci22-ur12*li21;

            }

            else

            {

                

                //

                // Code when diagonals of pivoted C are real

                //

                ur11r = 1/ur11;

                ui11r = 0;

                lr21 = cr21*ur11r;

                li21 = ci21*ur11r;

                ur12s = ur12*ur11r;

                ui12s = ui12*ur11r;

                ur22 = cr22-ur12*lr21+ui12*li21;

                ui22 = -ur12*li21-ui12*lr21;

            }

            u22abs = fabs(ur22)+fabs(ui22);

            

            //

            // If smaller pivot < SMINI, use SMINI

            //

            if( u22abs<smini )

            {

                ur22 = smini;

                ui22 = 0;

                info = 1;

            }

            if( rswap4(icmax) )

            {

                br2 = b(1,1);

                br1 = b(2,1);

                bi2 = b(1,2);

                bi1 = b(2,2);

            }

            else

            {

                br1 = b(1,1);

                br2 = b(2,1);

                bi1 = b(1,2);

                bi2 = b(2,2);

            }

            br2 = br2-lr21*br1+li21*bi1;

            bi2 = bi2-li21*br1-lr21*bi1;

            bbnd = ap::maxreal((fabs(br1)+fabs(bi1))*(u22abs*(fabs(ur11r)+fabs(ui11r))), fabs(br2)+fabs(bi2));

            if( bbnd>1&&u22abs<1 )

            {

                if( bbnd>=bignum*u22abs )

                {

                    scl = 1/bbnd;

                    br1 = scl*br1;

                    bi1 = scl*bi1;

                    br2 = scl*br2;

                    bi2 = scl*bi2;

                }

            }

            internalhsevdladiv(br2, bi2, ur22, ui22, xr2, xi2);

            xr1 = ur11r*br1-ui11r*bi1-ur12s*xr2+ui12s*xi2;

            xi1 = ui11r*br1+ur11r*bi1-ui12s*xr2-ur12s*xi2;

            if( zswap4(icmax) )

            {

                x(1,1) = xr2;

                x(2,1) = xr1;

                x(1,2) = xi2;

                x(2,2) = xi1;

            }

            else

            {

                x(1,1) = xr1;

                x(2,1) = xr2;

                x(1,2) = xi1;

                x(2,2) = xi2;

            }

            xnorm = ap::maxreal(fabs(xr1)+fabs(xi1), fabs(xr2)+fabs(xi2));

            

            //

            // Further scaling if  norm(A) norm(X) > overflow

            //

            if( xnorm>1&&cmax>1 )

            {

                if( xnorm>bignum/cmax )

                {

                    temp = cmax/bignum;

                    x(1,1) = temp*x(1,1);

                    x(2,1) = temp*x(2,1);

                    x(1,2) = temp*x(1,2);

                    x(2,2) = temp*x(2,2);

                    xnorm = temp*xnorm;

                    scl = temp*scl;

                }

            }

        }

    }

}





static void internalhsevdladiv(const double& a,

     const double& b,

     const double& c,

     const double& d,

     double& p,

     double& q)

{

    double e;

    double f;



    if( fabs(d)<fabs(c) )

    {

        e = d/c;

        f = c+d*e;

        p = (a+b*e)/f;

        q = (b-a*e)/f;

    }

    else

    {

        e = c/d;

        f = d+c*e;

        p = (b+a*e)/f;

        q = (-a+b*e)/f;

    }

}







