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



#include <stdio.h>

#include "capd/alglib/reflections.h"


//static void testreflections();



/*************************************************************************

Generation of an elementary reflection transformation



The subroutine generates elementary reflection H of order N, so that, for

a given X, the following equality holds true:



    ( X(1) )   ( Beta )

H * (  ..  ) = (  0   )

    ( X(n) )   (  0   )



where

              ( V(1) )

H = 1 - Tau * (  ..  ) * ( V(1), ..., V(n) )

              ( V(n) )



where the first component of vector V equals 1.



Input parameters:

    X   -   vector. Array whose index ranges within [1..N].

    N   -   reflection order.



Output parameters:

    X   -   components from 2 to N are replaced with vector V.

            The first component is replaced with parameter Beta.

    Tau -   scalar value Tau. If X is a null vector, Tau equals 0,

            otherwise 1 <= Tau <= 2.



This subroutine is the modification of the DLARFG subroutines from

the LAPACK library. It has a similar functionality except for the

fact that it doesn�t handle errors when the intermediate results

cause an overflow.





MODIFICATIONS:

    24.12.2005 sign(Alpha) was replaced with an analogous to the Fortran SIGN code.



  -- LAPACK auxiliary routine (version 3.0) --

     Univ. of Tennessee, Univ. of California Berkeley, NAG Ltd.,

     Courant Institute, Argonne National Lab, and Rice University

     September 30, 1994

*************************************************************************/

void generatereflection(ap::real_1d_array& x, int n, double& tau)

{

    int j;

    double alpha;

    double xnorm;

    double v;

    double beta;

    double mx;



    

    //

    // Executable Statements ..

    //

    if( n<=1 )

    {

        tau = 0;

        return;

    }

    

    //

    // XNORM = DNRM2( N-1, X, INCX )

    //

    alpha = x(1);

    mx = 0;

    for(j = 2; j <= n; j++)

    {

        mx = ap::maxreal(fabs(x(j)), mx);

    }

    xnorm = 0;

    if( mx!=0 )

    {

        for(j = 2; j <= n; j++)

        {

            xnorm = xnorm+ap::sqr(x(j)/mx);

        }

        xnorm = sqrt(xnorm)*mx;

    }

    if( xnorm==0 )

    {

        

        //

        // H  =  I

        //

        tau = 0;

        return;

    }

    

    //

    // general case

    //

    mx = ap::maxreal(fabs(alpha), fabs(xnorm));

    beta = -mx*sqrt(ap::sqr(alpha/mx)+ap::sqr(xnorm/mx));

    if( alpha<0 )

    {

        beta = -beta;

    }

    tau = (beta-alpha)/beta;

    v = 1/(alpha-beta);

    ap::vmul(&x(2), ap::vlen(2,n), v);

    x(1) = beta;

}





/*************************************************************************

Application of an elementary reflection to a rectangular matrix of size MxN



The algorithm pre-multiplies the matrix by an elementary reflection transformation

which is given by column V and scalar Tau (see the description of the

GenerateReflection procedure). Not the whole matrix but only a part of it

is transformed (rows from M1 to M2, columns from N1 to N2). Only the elements

of this submatrix are changed.



Input parameters:

    C       -   matrix to be transformed.

    Tau     -   scalar defining the transformation.

    V       -   column defining the transformation.

                Array whose index ranges within [1..M2-M1+1].

    M1, M2  -   range of rows to be transformed.

    N1, N2  -   range of columns to be transformed.

    WORK    -   working array whose indexes goes from N1 to N2.



Output parameters:

    C       -   the result of multiplying the input matrix C by the

                transformation matrix which is given by Tau and V.

                If N1>N2 or M1>M2, C is not modified.



  -- LAPACK auxiliary routine (version 3.0) --

     Univ. of Tennessee, Univ. of California Berkeley, NAG Ltd.,

     Courant Institute, Argonne National Lab, and Rice University

     September 30, 1994

*************************************************************************/

void applyreflectionfromtheleft(ap::real_2d_array& c,

     double tau,

     const ap::real_1d_array& v,

     int m1,

     int m2,

     int n1,

     int n2,

     ap::real_1d_array& work)

{

    double t;

    int i;

 //   int vm;



    if( tau==0||n1>n2||m1>m2 )

    {

        return;

    }

    

    //

    // w := C' * v

    //

   // vm = m2-m1+1;

    for(i = n1; i <= n2; i++)

    {

        work(i) = 0;

    }

    for(i = m1; i <= m2; i++)

    {

        t = v(i+1-m1);

        ap::vadd(&work(n1), &c(i, n1), ap::vlen(n1,n2), t);

    }

    

    //

    // C := C - tau * v * w'

    //

    for(i = m1; i <= m2; i++)

    {

        t = v(i-m1+1)*tau;

        ap::vsub(&c(i, n1), &work(n1), ap::vlen(n1,n2), t);

    }

}





/*************************************************************************

Application of an elementary reflection to a rectangular matrix of size MxN



The algorithm post-multiplies the matrix by an elementary reflection transformation

which is given by column V and scalar Tau (see the description of the

GenerateReflection procedure). Not the whole matrix but only a part of it

is transformed (rows from M1 to M2, columns from N1 to N2). Only the

elements of this submatrix are changed.



Input parameters:

    C       -   matrix to be transformed.

    Tau     -   scalar defining the transformation.

    V       -   column defining the transformation.

                Array whose index ranges within [1..N2-N1+1].

    M1, M2  -   range of rows to be transformed.

    N1, N2  -   range of columns to be transformed.

    WORK    -   working array whose indexes goes from M1 to M2.



Output parameters:

    C       -   the result of multiplying the input matrix C by the

                transformation matrix which is given by Tau and V.

                If N1>N2 or M1>M2, C is not modified.



  -- LAPACK auxiliary routine (version 3.0) --

     Univ. of Tennessee, Univ. of California Berkeley, NAG Ltd.,

     Courant Institute, Argonne National Lab, and Rice University

     September 30, 1994

*************************************************************************/

void applyreflectionfromtheright(ap::real_2d_array& c,

     double tau,

     const ap::real_1d_array& v,

     int m1,

     int m2,

     int n1,

     int n2,

     ap::real_1d_array& work)

{

    double t;

    int i;

   // int vm;



    if( tau==0||n1>n2||m1>m2 )

    {

        return;

    }

    

    //

    // w := C * v

    //

    //vm = n2-n1+1;

    for(i = m1; i <= m2; i++)

    {

        t = ap::vdotproduct(&c(i, n1), &v(1), ap::vlen(n1,n2));

        work(i) = t;

    }

    

    //

    // C := C - w * v'

    //

    for(i = m1; i <= m2; i++)

    {

        t = work(i)*tau;

        ap::vsub(&c(i, n1), &v(1), ap::vlen(n1,n2), t);

    }

}





/*static void testreflections()

{

    int i;

    int j;

    int n;

    int m;

    int maxmn;

    ap::real_1d_array x;

    ap::real_1d_array v;

    ap::real_1d_array work;

    ap::real_2d_array h;

    ap::real_2d_array a;

    ap::real_2d_array b;

    ap::real_2d_array c;

    double tmp;

    double beta;

    double tau;

    double err;

    double mer;

    double mel;

    double meg;

    int pass;

    int passcount;



    passcount = 1000;

    mer = 0;

    mel = 0;

    meg = 0;

    for(pass = 1; pass <= passcount; pass++)

    {

        

        //

        // Task

        //

        n = 1+ap::randominteger(10);

        m = 1+ap::randominteger(10);

        maxmn = ap::maxint(m, n);

        

        //

        // Initialize

        //

        x.setbounds(1, maxmn);

        v.setbounds(1, maxmn);

        work.setbounds(1, maxmn);

        h.setbounds(1, maxmn, 1, maxmn);

        a.setbounds(1, maxmn, 1, maxmn);

        b.setbounds(1, maxmn, 1, maxmn);

        c.setbounds(1, maxmn, 1, maxmn);

        

        //

        // GenerateReflection

        //

        for(i = 1; i <= n; i++)

        {

            x(i) = 2*ap::randomreal()-1;

            v(i) = x(i);

        }

        generatereflection(v, n, tau);

        beta = v(1);

        v(1) = 1;

        for(i = 1; i <= n; i++)

        {

            for(j = 1; j <= n; j++)

            {

                if( i==j )

                {

                    h(i,j) = 1-tau*v(i)*v(j);

                }

                else

                {

                    h(i,j) = -tau*v(i)*v(j);

                }

            }

        }

        err = 0;

        for(i = 1; i <= n; i++)

        {

            tmp = ap::vdotproduct(&h(i, 1), &x(1), ap::vlen(1,n));

            if( i==1 )

            {

                err = ap::maxreal(err, fabs(tmp-beta));

            }

            else

            {

                err = ap::maxreal(err, fabs(tmp));

            }

        }

        meg = ap::maxreal(meg, err);

        

        //

        // ApplyReflectionFromTheLeft

        //

        for(i = 1; i <= m; i++)

        {

            x(i) = 2*ap::randomreal()-1;

            v(i) = x(i);

        }

        for(i = 1; i <= m; i++)

        {

            for(j = 1; j <= n; j++)

            {

                a(i,j) = 2*ap::randomreal()-1;

                b(i,j) = a(i,j);

            }

        }

        generatereflection(v, m, tau);

        beta = v(1);

        v(1) = 1;

        applyreflectionfromtheleft(b, tau, v, 1, m, 1, n, work);

        for(i = 1; i <= m; i++)

        {

            for(j = 1; j <= m; j++)

            {

                if( i==j )

                {

                    h(i,j) = 1-tau*v(i)*v(j);

                }

                else

                {

                    h(i,j) = -tau*v(i)*v(j);

                }

            }

        }

        for(i = 1; i <= m; i++)

        {

            for(j = 1; j <= n; j++)

            {

                tmp = ap::vdotproduct(h.getrow(i, 1, m), a.getcolumn(j, 1, m));

                c(i,j) = tmp;

            }

        }

        err = 0;

        for(i = 1; i <= m; i++)

        {

            for(j = 1; j <= n; j++)

            {

                err = ap::maxreal(err, fabs(b(i,j)-c(i,j)));

            }

        }

        mel = ap::maxreal(mel, err);

        

        //

        // ApplyReflectionFromTheRight

        //

        for(i = 1; i <= n; i++)

        {

            x(i) = 2*ap::randomreal()-1;

            v(i) = x(i);

        }

        for(i = 1; i <= m; i++)

        {

            for(j = 1; j <= n; j++)

            {

                a(i,j) = 2*ap::randomreal()-1;

                b(i,j) = a(i,j);

            }

        }

        generatereflection(v, n, tau);

        beta = v(1);

        v(1) = 1;

        applyreflectionfromtheright(b, tau, v, 1, m, 1, n, work);

        for(i = 1; i <= n; i++)

        {

            for(j = 1; j <= n; j++)

            {

                if( i==j )

                {

                    h(i,j) = 1-tau*v(i)*v(j);

                }

                else

                {

                    h(i,j) = -tau*v(i)*v(j);

                }

            }

        }

        for(i = 1; i <= m; i++)

        {

            for(j = 1; j <= n; j++)

            {

                tmp = ap::vdotproduct(a.getrow(i, 1, n), h.getcolumn(j, 1, n));

                c(i,j) = tmp;

            }

        }

        err = 0;

        for(i = 1; i <= m; i++)

        {

            for(j = 1; j <= n; j++)

            {

                err = ap::maxreal(err, fabs(b(i,j)-c(i,j)));

            }

        }

        mer = ap::maxreal(mer, err);

    }

    

    //

    // Overflow crash test

    //

    x.setbounds(1, 10);

    v.setbounds(1, 10);

    for(i = 1; i <= 10; i++)

    {

        v(i) = ap::maxrealnumber*0.01*(2*ap::randomreal()-1);

    }

    generatereflection(v, 10, tau);

    printf("TESTING REFLECTIONS\n");

    printf("Pass count is %0ld\n",

        long(passcount));

    printf("Generate     absolute error is       %5.3e\n",

        double(meg));

    printf("Apply(Left)  absolute error is       %5.3e\n",

        double(mel));

    printf("Apply(Right) absolute error is       %5.3e\n",

        double(mer));

    printf("Overflow crash test passed\n");

}

*/





