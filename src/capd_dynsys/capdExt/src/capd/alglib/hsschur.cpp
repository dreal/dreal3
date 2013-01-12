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



#include "capd/alglib/stdafx.h"
#include "capd/alglib/hsschur.h"


static void internalauxschur(bool wantt,

     bool wantz,

     int n,

     int ilo,

     int ihi,

     ap::real_2d_array& h,

     ap::real_1d_array& wr,

     ap::real_1d_array& wi,

     int iloz,

     int ihiz,

     ap::real_2d_array& z,

     ap::real_1d_array& work,

     ap::real_1d_array& workv3,

     ap::real_1d_array& workc1,

     ap::real_1d_array& works1,

     int& info);

static void aux2x2schur(double& a,

     double& b,

     double& c,

     double& d,

     double& rt1r,

     double& rt1i,

     double& rt2r,

     double& rt2i,

     double& cs,

     double& sn);

static double extschursign(double a, double b);

static int extschursigntoone(double b);



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

    H   �   contains the matrix T.

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

     ap::real_2d_array& s)

{

    bool result;

    ap::real_1d_array wi;

    ap::real_1d_array wr;

    int info;



    internalschurdecomposition(h, n, 1, 2, wr, wi, s, info);

    result = info==0;

    return result;

}





void internalschurdecomposition(ap::real_2d_array& h,

     int n,

     int tneeded,

     int zneeded,

     ap::real_1d_array& wr,

     ap::real_1d_array& wi,

     ap::real_2d_array& z,

     int& info)

{

    ap::real_1d_array work;

    int i;

    int i1;

    int i2 =0;

    int ierr;

    int ii;

    int itemp;

    int itn;

    int its;

    int j;

    int k;

    int l;

    int maxb;

    int nr;

    int ns;

    int nv;

    double absw;

//    double ovfl;

    double smlnum;

    double tau;

    double temp;

    double tst1;

    double ulp;

    double unfl;

    ap::real_2d_array s;

    ap::real_1d_array v;

    ap::real_1d_array vv;

    ap::real_1d_array workc1;

    ap::real_1d_array works1;

    ap::real_1d_array workv3;

    ap::real_1d_array tmpwr;

    ap::real_1d_array tmpwi;

    bool initz;

    bool wantt;

    bool wantz;

    double cnst;

    bool failflag;

    int p1;

    int p2;

      double vt;



    

    //

    // Set the order of the multi-shift QR algorithm to be used.

    // If you want to tune algorithm, change this values

    //

    ns = 12;

    maxb = 50;

    

    //

    // Now 2 < NS <= MAXB < NH.

    //

    maxb = ap::maxint(3, maxb);

    ns = ap::minint(maxb, ns);

    

    //

    // Initialize

    //

    cnst = 1.5;

    work.setbounds(1, ap::maxint(n, 1));

    s.setbounds(1, ns, 1, ns);

    v.setbounds(1, ns+1);

    vv.setbounds(1, ns+1);

    wr.setbounds(1, ap::maxint(n, 1));

    wi.setbounds(1, ap::maxint(n, 1));

    workc1.setbounds(1, 1);

    works1.setbounds(1, 1);

    workv3.setbounds(1, 3);

    tmpwr.setbounds(1, ap::maxint(n, 1));

    tmpwi.setbounds(1, ap::maxint(n, 1));

    ap::ap_error::make_assertion(n>=0, "InternalSchurDecomposition: incorrect N!");

    ap::ap_error::make_assertion(tneeded==0||tneeded==1, "InternalSchurDecomposition: incorrect TNeeded!");

    ap::ap_error::make_assertion(zneeded==0||zneeded==1||zneeded==2, "InternalSchurDecomposition: incorrect ZNeeded!");

    wantt = tneeded==1;

    initz = zneeded==2;

    wantz = zneeded!=0;

    info = 0;

    

    //

    // Initialize Z, if necessary

    //

    if( initz )

    {

        z.setbounds(1, n, 1, n);

        for(i = 1; i <= n; i++)

        {

            for(j = 1; j <= n; j++)

            {

                if( i==j )

                {

                    z(i,j) = 1;

                }

                else

                {

                    z(i,j) = 0;

                }

            }

        }

    }

    

    //

    // Quick return if possible

    //

    if( n==0 )

    {

        return;

    }

    if( n==1 )

    {

        wr(1) = h(1,1);

        wi(1) = 0;

        return;

    }

    

    //

    // Set rows and columns 1 to N to zero below the first

    // subdiagonal.

    //

    for(j = 1; j <= n-2; j++)

    {

        for(i = j+2; i <= n; i++)

        {

            h(i,j) = 0;

        }

    }

    

    //

    // Test if N is sufficiently small

    //

    if( ns<=2||ns>n||maxb>=n )

    {

        

        //

        // Use the standard double-shift algorithm

        //

        internalauxschur(wantt, wantz, n, 1, n, h, wr, wi, 1, n, z, work, workv3, workc1, works1, info);

        

        //

        // fill entries under diagonal blocks of T with zeros

        //

        if( wantt )

        {

            j = 1;

            while(j<=n)

            {

                if( wi(j)==0 )

                {

                    for(i = j+1; i <= n; i++)

                    {

                        h(i,j) = 0;

                    }

                    j = j+1;

                }

                else

                {

                    for(i = j+2; i <= n; i++)

                    {

                        h(i,j) = 0;

                        h(i,j+1) = 0;

                    }

                    j = j+2;

                }

            }

        }

        return;

    }

    unfl = ap::minrealnumber;

   //ovfl = 1/unfl;

    ulp = 2*ap::machineepsilon;

    smlnum = unfl*(n/ulp);

    

    //

    // I1 and I2 are the indices of the first row and last column of H

    // to which transformations must be applied. If eigenvalues only are

    // being computed, I1 and I2 are set inside the main loop.

    //

    if( wantt )

    {

        i1 = 1;

        i2 = n;

    }

    

    //

    // ITN is the total number of multiple-shift QR iterations allowed.

    //

    itn = 30*n;

    

    //

    // The main loop begins here. I is the loop index and decreases from

    // IHI to ILO in steps of at most MAXB. Each iteration of the loop

    // works with the active submatrix in rows and columns L to I.

    // Eigenvalues I+1 to IHI have already converged. Either L = ILO or

    // H(L,L-1) is negligible so that the matrix splits.

    //

    i = n;

    while(true)

    {

        l = 1;

        if( i<1 )

        {

            

            //

            // fill entries under diagonal blocks of T with zeros

            //

            if( wantt )

            {

                j = 1;

                while(j<=n)

                {

                    if( wi(j)==0 )

                    {

                        for(i = j+1; i <= n; i++)

                        {

                            h(i,j) = 0;

                        }

                        j = j+1;

                    }

                    else

                    {

                        for(i = j+2; i <= n; i++)

                        {

                            h(i,j) = 0;

                            h(i,j+1) = 0;

                        }

                        j = j+2;

                    }

                }

            }

            

            //

            // Exit

            //

            return;

        }

        

        //

        // Perform multiple-shift QR iterations on rows and columns ILO to I

        // until a submatrix of order at most MAXB splits off at the bottom

        // because a subdiagonal element has become negligible.

        //

        failflag = true;

        for(its = 0; its <= itn; its++)

        {

            

            //

            // Look for a single small subdiagonal element.

            //

            for(k = i; k >= l+1; k--)

            {

                tst1 = fabs(h(k-1,k-1))+fabs(h(k,k));

                if( tst1==0 )

                {

                    tst1 = upperhessenberg1norm(h, l, i, l, i, work);

                }

                if( fabs(h(k,k-1))<=ap::maxreal(ulp*tst1, smlnum) )

                {

                    break;

                }

            }

            l = k;

            if( l>1 )

            {

                

                //

                // H(L,L-1) is negligible.

                //

                h(l,l-1) = 0;

            }

            

            //

            // Exit from loop if a submatrix of order <= MAXB has split off.

            //

            if( l>=i-maxb+1 )

            {

                failflag = false;

                break;

            }

            

            //

            // Now the active submatrix is in rows and columns L to I. If

            // eigenvalues only are being computed, only the active submatrix

            // need be transformed.

            //

            if( !wantt )

            {

                i1 = l;

                i2 = i;

            }

            if( its==20||its==30 )

            {

                

                //

                // Exceptional shifts.

                //

                for(ii = i-ns+1; ii <= i; ii++)

                {

                    wr(ii) = cnst*(fabs(h(ii,ii-1))+fabs(h(ii,ii)));

                    wi(ii) = 0;

                }

            }

            else

            {

                

                //

                // Use eigenvalues of trailing submatrix of order NS as shifts.

                //

                copymatrix(h, i-ns+1, i, i-ns+1, i, s, 1, ns, 1, ns);

                internalauxschur(false, false, ns, 1, ns, s, tmpwr, tmpwi, 1, ns, z, work, workv3, workc1, works1, ierr);

                for(p1 = 1; p1 <= ns; p1++)

                {

                    wr(i-ns+p1) = tmpwr(p1);

                    wi(i-ns+p1) = tmpwi(p1);

                }

                if( ierr>0 )

                {

                    

                    //

                    // If DLAHQR failed to compute all NS eigenvalues, use the

                    // unconverged diagonal elements as the remaining shifts.

                    //

                    for(ii = 1; ii <= ierr; ii++)

                    {

                        wr(i-ns+ii) = s(ii,ii);

                        wi(i-ns+ii) = 0;

                    }

                }

            }

            

            //

            // Form the first column of (G-w(1)) (G-w(2)) . . . (G-w(ns))

            // where G is the Hessenberg submatrix H(L:I,L:I) and w is

            // the vector of shifts (stored in WR and WI). The result is

            // stored in the local array V.

            //

            v(1) = 1;

            for(ii = 2; ii <= ns+1; ii++)

            {

                v(ii) = 0;

            }

            nv = 1;

            for(j = i-ns+1; j <= i; j++)

            {

                if( wi(j)>=0 )

                {

                    if( wi(j)==0 )

                    {

                        

                        //

                        // real shift

                        //

                        p1 = nv+1;

                        ap::vmove(&vv(1), &v(1), ap::vlen(1,p1));

                        matrixvectormultiply(h, l, l+nv, l, l+nv-1, false, vv, 1, nv, 1.0, v, 1, nv+1, -wr(j));

                        nv = nv+1;

                    }

                    else

                    {

                        if( wi(j)>0 )

                        {

                            

                            //

                            // complex conjugate pair of shifts

                            //

                            p1 = nv+1;

                            ap::vmove(&vv(1), &v(1), ap::vlen(1,p1));

                            matrixvectormultiply(h, l, l+nv, l, l+nv-1, false, v, 1, nv, 1.0, vv, 1, nv+1, -2*wr(j));

                            itemp = vectoridxabsmax(vv, 1, nv+1);

                            temp = 1/ap::maxreal(fabs(vv(itemp)), smlnum);

                            p1 = nv+1;

                            ap::vmul(&vv(1), ap::vlen(1,p1), temp);

                            absw = pythag2(wr(j), wi(j));

                            temp = temp*absw*absw;

                            matrixvectormultiply(h, l, l+nv+1, l, l+nv, false, vv, 1, nv+1, 1.0, v, 1, nv+2, temp);

                            nv = nv+2;

                        }

                    }

                    

                    //

                    // Scale V(1:NV) so that max(abs(V(i))) = 1. If V is zero,

                    // reset it to the unit vector.

                    //

                    itemp = vectoridxabsmax(v, 1, nv);

                    temp = fabs(v(itemp));

                    if( temp==0 )

                    {

                        v(1) = 1;

                        for(ii = 2; ii <= nv; ii++)

                        {

                            v(ii) = 0;

                        }

                    }

                    else

                    {

                        temp = ap::maxreal(temp, smlnum);

                        vt = 1/temp;

                        ap::vmul(&v(1), ap::vlen(1,nv), vt);

                    }

                }

            }

            

            //

            // Multiple-shift QR step

            //

            for(k = l; k <= i-1; k++)

            {

                

                //

                // The first iteration of this loop determines a reflection G

                // from the vector V and applies it from left and right to H,

                // thus creating a nonzero bulge below the subdiagonal.

                //

                // Each subsequent iteration determines a reflection G to

                // restore the Hessenberg form in the (K-1)th column, and thus

                // chases the bulge one step toward the bottom of the active

                // submatrix. NR is the order of G.

                //

                nr = ap::minint(ns+1, i-k+1);

                if( k>l )

                {

                    p1 = k-1;

                    p2 = k+nr-1;

                    ap::vmove(v.getvector(1, nr), h.getcolumn(p1, k, p2));

                }

                generatereflection(v, nr, tau);

                if( k>l )

                {

                    h(k,k-1) = v(1);

                    for(ii = k+1; ii <= i; ii++)

                    {

                        h(ii,k-1) = 0;

                    }

                }

                v(1) = 1;

                

                //

                // Apply G from the left to transform the rows of the matrix in

                // columns K to I2.

                //

                applyreflectionfromtheleft(h, tau, v, k, k+nr-1, k, i2, work);

                

                //

                // Apply G from the right to transform the columns of the

                // matrix in rows I1 to min(K+NR,I).

                //

                applyreflectionfromtheright(h, tau, v, i1, ap::minint(k+nr, i), k, k+nr-1, work);

                if( wantz )

                {

                    

                    //

                    // Accumulate transformations in the matrix Z

                    //

                    applyreflectionfromtheright(z, tau, v, 1, n, k, k+nr-1, work);

                }

            }

        }

        

        //

        // Failure to converge in remaining number of iterations

        //

        if( failflag )

        {

            info = i;

            return;

        }

        

        //

        // A submatrix of order <= MAXB in rows and columns L to I has split

        // off. Use the double-shift QR algorithm to handle it.

        //

        internalauxschur(wantt, wantz, n, l, i, h, wr, wi, 1, n, z, work, workv3, workc1, works1, info);

        if( info>0 )

        {

            return;

        }

        

        //

        // Decrement number of remaining iterations, and return to start of

        // the main loop with a new value of I.

        //

        itn = itn-its;

        i = l-1;

    }

}





static void internalauxschur(bool wantt,

     bool wantz,

     int n,

     int ilo,

     int ihi,

     ap::real_2d_array& h,

     ap::real_1d_array& wr,

     ap::real_1d_array& wi,

     int iloz,

     int ihiz,

     ap::real_2d_array& z,

     ap::real_1d_array& work,

     ap::real_1d_array& workv3,

     ap::real_1d_array& workc1,

     ap::real_1d_array& works1,

     int& info)

{

    int i;

    int i1;

    int i2=0;

    int itn;

    int its;

    int j;

    int k;

    int l;

    int m;

    int nh;

    int nr;

    int nz;

    double ave;

    double cs;

    double disc;

    double h00;

    double h10;

    double h11;

    double h12;

    double h21;

    double h22;

    double h33;

    double h33s;

    double h43h34;

    double h44;

    double h44s;

    //double ovfl;

    double s;

    double smlnum;

    double sn;

    double sum;

    double t1;

    double t2;

    double t3;

    double tst1;

    double unfl;

    double v1;

    double v2;

    double v3;

    bool failflag;

    double dat1;

    double dat2;

    int p1;

    double him1im1;

    double him1i;

    double hiim1;

    double hii;

    double wrim1;

    double wri;

    double wiim1;

    double wii;

    double ulp;



    info = 0;

    dat1 = 0.75;

    dat2 = -0.4375;

    ulp = ap::machineepsilon;

    

    //

    // Quick return if possible

    //

    if( n==0 )

    {

        return;

    }

    if( ilo==ihi )

    {

        wr(ilo) = h(ilo,ilo);

        wi(ilo) = 0;

        return;

    }

    nh = ihi-ilo+1;

    nz = ihiz-iloz+1;

    

    //

    // Set machine-dependent constants for the stopping criterion.

    // If norm(H) <= sqrt(OVFL), overflow should not occur.

    //

    unfl = ap::minrealnumber;

   // ovfl = 1/unfl;

    smlnum = unfl*(nh/ulp);

    

    //

    // I1 and I2 are the indices of the first row and last column of H

    // to which transformations must be applied. If eigenvalues only are

    // being computed, I1 and I2 are set inside the main loop.

    //

    if( wantt )

    {

        i1 = 1;

        i2 = n;

    }

    

    //

    // ITN is the total number of QR iterations allowed.

    //

    itn = 30*nh;

    

    //

    // The main loop begins here. I is the loop index and decreases from

    // IHI to ILO in steps of 1 or 2. Each iteration of the loop works

    // with the active submatrix in rows and columns L to I.

    // Eigenvalues I+1 to IHI have already converged. Either L = ILO or

    // H(L,L-1) is negligible so that the matrix splits.

    //

    i = ihi;

    while(true)

    {

        l = ilo;

        if( i<ilo )

        {

            return;

        }

        

        //

        // Perform QR iterations on rows and columns ILO to I until a

        // submatrix of order 1 or 2 splits off at the bottom because a

        // subdiagonal element has become negligible.

        //

        failflag = true;

        for(its = 0; its <= itn; its++)

        {

            

            //

            // Look for a single small subdiagonal element.

            //

            for(k = i; k >= l+1; k--)

            {

                tst1 = fabs(h(k-1,k-1))+fabs(h(k,k));

                if( tst1==0 )

                {

                    tst1 = upperhessenberg1norm(h, l, i, l, i, work);

                }

                if( fabs(h(k,k-1))<=ap::maxreal(ulp*tst1, smlnum) )

                {

                    break;

                }

            }

            l = k;

            if( l>ilo )

            {

                

                //

                // H(L,L-1) is negligible

                //

                h(l,l-1) = 0;

            }

            

            //

            // Exit from loop if a submatrix of order 1 or 2 has split off.

            //

            if( l>=i-1 )

            {

                failflag = false;

                break;

            }

            

            //

            // Now the active submatrix is in rows and columns L to I. If

            // eigenvalues only are being computed, only the active submatrix

            // need be transformed.

            //

            if( !wantt )

            {

                i1 = l;

                i2 = i;

            }

            if( its==10||its==20 )

            {

                

                //

                // Exceptional shift.

                //

                s = fabs(h(i,i-1))+fabs(h(i-1,i-2));

                h44 = dat1*s+h(i,i);

                h33 = h44;

                h43h34 = dat2*s*s;

            }

            else

            {

                

                //

                // Prepare to use Francis' double shift

                // (i.e. 2nd degree generalized Rayleigh quotient)

                //

                h44 = h(i,i);

                h33 = h(i-1,i-1);

                h43h34 = h(i,i-1)*h(i-1,i);

                s = h(i-1,i-2)*h(i-1,i-2);

                disc = (h33-h44)*0.5;

                disc = disc*disc+h43h34;

                if( disc>0 )

                {

                    

                    //

                    // Real roots: use Wilkinson's shift twice

                    //

                    disc = sqrt(disc);

                    ave = 0.5*(h33+h44);

                    if( fabs(h33)-fabs(h44)>0 )

                    {

                        h33 = h33*h44-h43h34;

                        h44 = h33/(extschursign(disc, ave)+ave);

                    }

                    else

                    {

                        h44 = extschursign(disc, ave)+ave;

                    }

                    h33 = h44;

                    h43h34 = 0;

                }

            }

            

            //

            // Look for two consecutive small subdiagonal elements.

            //

            for(m = i-2; m >= l; m--)

            {

                

                //

                // Determine the effect of starting the double-shift QR

                // iteration at row M, and see if this would make H(M,M-1)

                // negligible.

                //

                h11 = h(m,m);

                h22 = h(m+1,m+1);

                h21 = h(m+1,m);

                h12 = h(m,m+1);

                h44s = h44-h11;

                h33s = h33-h11;

                v1 = (h33s*h44s-h43h34)/h21+h12;

                v2 = h22-h11-h33s-h44s;

                v3 = h(m+2,m+1);

                s = fabs(v1)+fabs(v2)+fabs(v3);

                v1 = v1/s;

                v2 = v2/s;

                v3 = v3/s;

                workv3(1) = v1;

                workv3(2) = v2;

                workv3(3) = v3;

                if( m==l )

                {

                    break;

                }

                h00 = h(m-1,m-1);

                h10 = h(m,m-1);

                tst1 = fabs(v1)*(fabs(h00)+fabs(h11)+fabs(h22));

                if( fabs(h10)*(fabs(v2)+fabs(v3))<=ulp*tst1 )

                {

                    break;

                }

            }

            

            //

            // Double-shift QR step

            //

            for(k = m; k <= i-1; k++)

            {

                

                //

                // The first iteration of this loop determines a reflection G

                // from the vector V and applies it from left and right to H,

                // thus creating a nonzero bulge below the subdiagonal.

                //

                // Each subsequent iteration determines a reflection G to

                // restore the Hessenberg form in the (K-1)th column, and thus

                // chases the bulge one step toward the bottom of the active

                // submatrix. NR is the order of G.

                //

                nr = ap::minint(3, i-k+1);

                if( k>m )

                {

                    for(p1 = 1; p1 <= nr; p1++)

                    {

                        workv3(p1) = h(k+p1-1,k-1);

                    }

                }

                generatereflection(workv3, nr, t1);

                if( k>m )

                {

                    h(k,k-1) = workv3(1);

                    h(k+1,k-1) = 0;

                    if( k<i-1 )

                    {

                        h(k+2,k-1) = 0;

                    }

                }

                else

                {

                    if( m>l )

                    {

                        h(k,k-1) = -h(k,k-1);

                    }

                }

                v2 = workv3(2);

                t2 = t1*v2;

                if( nr==3 )

                {

                    v3 = workv3(3);

                    t3 = t1*v3;

                    

                    //

                    // Apply G from the left to transform the rows of the matrix

                    // in columns K to I2.

                    //

                    for(j = k; j <= i2; j++)

                    {

                        sum = h(k,j)+v2*h(k+1,j)+v3*h(k+2,j);

                        h(k,j) = h(k,j)-sum*t1;

                        h(k+1,j) = h(k+1,j)-sum*t2;

                        h(k+2,j) = h(k+2,j)-sum*t3;

                    }

                    

                    //

                    // Apply G from the right to transform the columns of the

                    // matrix in rows I1 to min(K+3,I).

                    //

                    for(j = i1; j <= ap::minint(k+3, i); j++)

                    {

                        sum = h(j,k)+v2*h(j,k+1)+v3*h(j,k+2);

                        h(j,k) = h(j,k)-sum*t1;

                        h(j,k+1) = h(j,k+1)-sum*t2;

                        h(j,k+2) = h(j,k+2)-sum*t3;

                    }

                    if( wantz )

                    {

                        

                        //

                        // Accumulate transformations in the matrix Z

                        //

                        for(j = iloz; j <= ihiz; j++)

                        {

                            sum = z(j,k)+v2*z(j,k+1)+v3*z(j,k+2);

                            z(j,k) = z(j,k)-sum*t1;

                            z(j,k+1) = z(j,k+1)-sum*t2;

                            z(j,k+2) = z(j,k+2)-sum*t3;

                        }

                    }

                }

                else

                {

                    if( nr==2 )

                    {

                        

                        //

                        // Apply G from the left to transform the rows of the matrix

                        // in columns K to I2.

                        //

                        for(j = k; j <= i2; j++)

                        {

                            sum = h(k,j)+v2*h(k+1,j);

                            h(k,j) = h(k,j)-sum*t1;

                            h(k+1,j) = h(k+1,j)-sum*t2;

                        }

                        

                        //

                        // Apply G from the right to transform the columns of the

                        // matrix in rows I1 to min(K+3,I).

                        //

                        for(j = i1; j <= i; j++)

                        {

                            sum = h(j,k)+v2*h(j,k+1);

                            h(j,k) = h(j,k)-sum*t1;

                            h(j,k+1) = h(j,k+1)-sum*t2;

                        }

                        if( wantz )

                        {

                            

                            //

                            // Accumulate transformations in the matrix Z

                            //

                            for(j = iloz; j <= ihiz; j++)

                            {

                                sum = z(j,k)+v2*z(j,k+1);

                                z(j,k) = z(j,k)-sum*t1;

                                z(j,k+1) = z(j,k+1)-sum*t2;

                            }

                        }

                    }

                }

            }

        }

        if( failflag )

        {

            

            //

            // Failure to converge in remaining number of iterations

            //

            info = i;

            return;

        }

        if( l==i )

        {

            

            //

            // H(I,I-1) is negligible: one eigenvalue has converged.

            //

            wr(i) = h(i,i);

            wi(i) = 0;

        }

        else

        {

            if( l==i-1 )

            {

                

                //

                // H(I-1,I-2) is negligible: a pair of eigenvalues have converged.

                //

                //        Transform the 2-by-2 submatrix to standard Schur form,

                //        and compute and store the eigenvalues.

                //

                him1im1 = h(i-1,i-1);

                him1i = h(i-1,i);

                hiim1 = h(i,i-1);

                hii = h(i,i);

                aux2x2schur(him1im1, him1i, hiim1, hii, wrim1, wiim1, wri, wii, cs, sn);

                wr(i-1) = wrim1;

                wi(i-1) = wiim1;

                wr(i) = wri;

                wi(i) = wii;

                h(i-1,i-1) = him1im1;

                h(i-1,i) = him1i;

                h(i,i-1) = hiim1;

                h(i,i) = hii;

                if( wantt )

                {

                    

                    //

                    // Apply the transformation to the rest of H.

                    //

                    if( i2>i )

                    {

                        workc1(1) = cs;

                        works1(1) = sn;

                        applyrotationsfromtheleft(true, i-1, i, i+1, i2, workc1, works1, h, work);

                    }

                    workc1(1) = cs;

                    works1(1) = sn;

                    applyrotationsfromtheright(true, i1, i-2, i-1, i, workc1, works1, h, work);

                }

                if( wantz )

                {

                    

                    //

                    // Apply the transformation to Z.

                    //

                    workc1(1) = cs;

                    works1(1) = sn;

                    applyrotationsfromtheright(true, iloz, iloz+nz-1, i-1, i, workc1, works1, z, work);

                }

            }

        }

        

        //

        // Decrement number of remaining iterations, and return to start of

        // the main loop with new value of I.

        //

        itn = itn-its;

        i = l-1;

    }

}





static void aux2x2schur(double& a,

     double& b,

     double& c,

     double& d,

     double& rt1r,

     double& rt1i,

     double& rt2r,

     double& rt2i,

     double& cs,

     double& sn)

{

    double multpl;

    double aa;

    double bb;

    double bcmax;

    double bcmis;

    double cc;

    double cs1;

    double dd;

    double eps;

    double p;

    double sab;

    double sac;

    double scl;

    double sigma;

    double sn1;

    double tau;

    double temp;

    double z;



    multpl = 4.0;

    eps = ap::machineepsilon;

    if( c==0 )

    {

        cs = 1;

        sn = 0;

    }

    else

    {

        if( b==0 )

        {

            

            //

            // Swap rows and columns

            //

            cs = 0;

            sn = 1;

            temp = d;

            d = a;

            a = temp;

            b = -c;

            c = 0;

        }

        else

        {

            if( a-d==0&&extschursigntoone(b)!=extschursigntoone(c) )

            {

                cs = 1;

                sn = 0;

            }

            else

            {

                temp = a-d;

                p = 0.5*temp;

                bcmax = ap::maxreal(fabs(b), fabs(c));

                bcmis = ap::minreal(fabs(b), fabs(c))*extschursigntoone(b)*extschursigntoone(c);

                scl = ap::maxreal(fabs(p), bcmax);

                z = p/scl*p+bcmax/scl*bcmis;

                

                //

                // If Z is of the order of the machine accuracy, postpone the

                // decision on the nature of eigenvalues

                //

                if( z>=multpl*eps )

                {

                    

                    //

                    // Real eigenvalues. Compute A and D.

                    //

                    z = p+extschursign(sqrt(scl)*sqrt(z), p);

                    a = d+z;

                    d = d-bcmax/z*bcmis;

                    

                    //

                    // Compute B and the rotation matrix

                    //

                    tau = pythag2(c, z);

                    cs = z/tau;

                    sn = c/tau;

                    b = b-c;

                    c = 0;

                }

                else

                {

                    

                    //

                    // Complex eigenvalues, or real (almost) equal eigenvalues.

                    // Make diagonal elements equal.

                    //

                    sigma = b+c;

                    tau = pythag2(sigma, temp);

                    cs = sqrt(0.5*(1+fabs(sigma)/tau));

                    sn = -p/(tau*cs)*extschursign(double(1), sigma);

                    

                    //

                    // Compute [ AA  BB ] = [ A  B ] [ CS -SN ]

                    //         [ CC  DD ]   [ C  D ] [ SN  CS ]

                    //

                    aa = a*cs+b*sn;

                    bb = -a*sn+b*cs;

                    cc = c*cs+d*sn;

                    dd = -c*sn+d*cs;

                    

                    //

                    // Compute [ A  B ] = [ CS  SN ] [ AA  BB ]

                    //         [ C  D ]   [-SN  CS ] [ CC  DD ]

                    //

                    a = aa*cs+cc*sn;

                    b = bb*cs+dd*sn;

                    c = -aa*sn+cc*cs;

                    d = -bb*sn+dd*cs;

                    temp = 0.5*(a+d);

                    a = temp;

                    d = temp;

                    if( c!=0 )

                    {

                        if( b!=0 )

                        {

                            if( extschursigntoone(b)==extschursigntoone(c) )

                            {

                                

                                //

                                // Real eigenvalues: reduce to upper triangular form

                                //

                                sab = sqrt(fabs(b));

                                sac = sqrt(fabs(c));

                                p = extschursign(sab*sac, c);

                                tau = 1/sqrt(fabs(b+c));

                                a = temp+p;

                                d = temp-p;

                                b = b-c;

                                c = 0;

                                cs1 = sab*tau;

                                sn1 = sac*tau;

                                temp = cs*cs1-sn*sn1;

                                sn = cs*sn1+sn*cs1;

                                cs = temp;

                            }

                        }

                        else

                        {

                            b = -c;

                            c = 0;

                            temp = cs;

                            cs = -sn;

                            sn = temp;

                        }

                    }

                }

            }

        }

    }

    

    //

    // Store eigenvalues in (RT1R,RT1I) and (RT2R,RT2I).

    //

    rt1r = a;

    rt2r = d;

    if( c==0 )

    {

        rt1i = 0;

        rt2i = 0;

    }

    else

    {

        rt1i = sqrt(fabs(b))*sqrt(fabs(c));

        rt2i = -rt1i;

    }

}





static double extschursign(double a, double b)

{

    double result;



    if( b>=0 )

    {

        result = fabs(a);

    }

    else

    {

        result = -fabs(a);

    }

    return result;

}





static int extschursigntoone(double b)

{

    int result;



    if( b>=0 )

    {

        result = 1;

    }

    else

    {

        result = -1;

    }

    return result;

}







