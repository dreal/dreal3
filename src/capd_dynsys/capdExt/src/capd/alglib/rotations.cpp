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
#include "capd/alglib/rotations.h"

//static void testrotations();

/*************************************************************************
Application of a sequence of  elementary rotations to a matrix

The algorithm pre-multiplies the matrix by a sequence of rotation
transformations which is given by arrays C and S. Depending on the value
of the IsForward parameter either 1 and 2, 3 and 4 and so on (if IsForward=true)
rows are rotated, or the rows N and N-1, N-2 and N-3 and so on, are rotated.

Not the whole matrix but only a part of it is transformed (rows from M1 to
M2, columns from N1 to N2). Only the elements of this submatrix are changed.

Input parameters:
    IsForward   -   the sequence of the rotation application.
    M1,M2       -   the range of rows to be transformed.
    N1, N2      -   the range of columns to be transformed.
    C,S         -   transformation coefficients.
                    Array whose index ranges within [1..M2-M1].
    A           -   processed matrix.
    WORK        -   working array whose index ranges within [N1..N2].

Output parameters:
    A           -   transformed matrix.

Utility subroutine.
*************************************************************************/
void applyrotationsfromtheleft(bool isforward,
     int m1,
     int m2,
     int n1,
     int n2,
     const ap::real_1d_array& c,
     const ap::real_1d_array& s,
     ap::real_2d_array& a,
     ap::real_1d_array& work)
{
    int j;
    int jp1;
    double ctemp;
    double stemp;
    double temp;

    if( m1>m2||n1>n2 )
    {
        return;
    }
    
    //
    // Form  P * A
    //
    if( isforward )
    {
        if( n1!=n2 )
        {
            
            //
            // Common case: N1<>N2
            //
            for(j = m1; j <= m2-1; j++)
            {
                ctemp = c(j-m1+1);
                stemp = s(j-m1+1);
                if( ctemp!=1||stemp!=0 )
                {
                    jp1 = j+1;
                    ap::vmove(&work(n1), &a(jp1, n1), ap::vlen(n1,n2), ctemp);
                    ap::vsub(&work(n1), &a(j, n1), ap::vlen(n1,n2), stemp);
                    ap::vmul(&a(j, n1), ap::vlen(n1,n2), ctemp);
                    ap::vadd(&a(j, n1), &a(jp1, n1), ap::vlen(n1,n2), stemp);
                    ap::vmove(&a(jp1, n1), &work(n1), ap::vlen(n1,n2));
                }
            }
        }
        else
        {
            
            //
            // Special case: N1=N2
            //
            for(j = m1; j <= m2-1; j++)
            {
                ctemp = c(j-m1+1);
                stemp = s(j-m1+1);
                if( ctemp!=1||stemp!=0 )
                {
                    temp = a(j+1,n1);
                    a(j+1,n1) = ctemp*temp-stemp*a(j,n1);
                    a(j,n1) = stemp*temp+ctemp*a(j,n1);
                }
            }
        }
    }
    else
    {
        if( n1!=n2 )
        {
            
            //
            // Common case: N1<>N2
            //
            for(j = m2-1; j >= m1; j--)
            {
                ctemp = c(j-m1+1);
                stemp = s(j-m1+1);
                if( ctemp!=1||stemp!=0 )
                {
                    jp1 = j+1;
                    ap::vmove(&work(n1), &a(jp1, n1), ap::vlen(n1,n2), ctemp);
                    ap::vsub(&work(n1), &a(j, n1), ap::vlen(n1,n2), stemp);
                    ap::vmul(&a(j, n1), ap::vlen(n1,n2), ctemp);
                    ap::vadd(&a(j, n1), &a(jp1, n1), ap::vlen(n1,n2), stemp);
                    ap::vmove(&a(jp1, n1), &work(n1), ap::vlen(n1,n2));
                }
            }
        }
        else
        {
            
            //
            // Special case: N1=N2
            //
            for(j = m2-1; j >= m1; j--)
            {
                ctemp = c(j-m1+1);
                stemp = s(j-m1+1);
                if( ctemp!=1||stemp!=0 )
                {
                    temp = a(j+1,n1);
                    a(j+1,n1) = ctemp*temp-stemp*a(j,n1);
                    a(j,n1) = stemp*temp+ctemp*a(j,n1);
                }
            }
        }
    }
}


/*************************************************************************
Application of a sequence of  elementary rotations to a matrix

The algorithm post-multiplies the matrix by a sequence of rotation
transformations which is given by arrays C and S. Depending on the value
of the IsForward parameter either 1 and 2, 3 and 4 and so on (if IsForward=true)
rows are rotated, or the rows N and N-1, N-2 and N-3 and so on are rotated.

Not the whole matrix but only a part of it is transformed (rows from M1
to M2, columns from N1 to N2). Only the elements of this submatrix are changed.

Input parameters:
    IsForward   -   the sequence of the rotation application.
    M1,M2       -   the range of rows to be transformed.
    N1, N2      -   the range of columns to be transformed.
    C,S         -   transformation coefficients.
                    Array whose index ranges within [1..N2-N1].
    A           -   processed matrix.
    WORK        -   working array whose index ranges within [M1..M2].

Output parameters:
    A           -   transformed matrix.

Utility subroutine.
*************************************************************************/
void applyrotationsfromtheright(bool isforward,
     int m1,
     int m2,
     int n1,
     int n2,
     const ap::real_1d_array& c,
     const ap::real_1d_array& s,
     ap::real_2d_array& a,
     ap::real_1d_array& work)
{
    int j;
    int jp1;
    double ctemp;
    double stemp;
    double temp;

    
    //
    // Form A * P'
    //
    if( isforward )
    {
        if( m1!=m2 )
        {
            
            //
            // Common case: M1<>M2
            //
            for(j = n1; j <= n2-1; j++)
            {
                ctemp = c(j-n1+1);
                stemp = s(j-n1+1);
                if( ctemp!=1||stemp!=0 )
                {
                    jp1 = j+1;
                    ap::vmove(work.getvector(m1, m2), a.getcolumn(jp1, m1, m2), ctemp);
                    ap::vsub(work.getvector(m1, m2), a.getcolumn(j, m1, m2), stemp);
                    ap::vmul(a.getcolumn(j, m1, m2), ctemp);
                    ap::vadd(a.getcolumn(j, m1, m2), a.getcolumn(jp1, m1, m2), stemp);
                    ap::vmove(a.getcolumn(jp1, m1, m2), work.getvector(m1, m2));
                }
            }
        }
        else
        {
            
            //
            // Special case: M1=M2
            //
            for(j = n1; j <= n2-1; j++)
            {
                ctemp = c(j-n1+1);
                stemp = s(j-n1+1);
                if( ctemp!=1||stemp!=0 )
                {
                    temp = a(m1,j+1);
                    a(m1,j+1) = ctemp*temp-stemp*a(m1,j);
                    a(m1,j) = stemp*temp+ctemp*a(m1,j);
                }
            }
        }
    }
    else
    {
        if( m1!=m2 )
        {
            
            //
            // Common case: M1<>M2
            //
            for(j = n2-1; j >= n1; j--)
            {
                ctemp = c(j-n1+1);
                stemp = s(j-n1+1);
                if( ctemp!=1||stemp!=0 )
                {
                    jp1 = j+1;
                    ap::vmove(work.getvector(m1, m2), a.getcolumn(jp1, m1, m2), ctemp);
                    ap::vsub(work.getvector(m1, m2), a.getcolumn(j, m1, m2), stemp);
                    ap::vmul(a.getcolumn(j, m1, m2), ctemp);
                    ap::vadd(a.getcolumn(j, m1, m2), a.getcolumn(jp1, m1, m2), stemp);
                    ap::vmove(a.getcolumn(jp1, m1, m2), work.getvector(m1, m2));
                }
            }
        }
        else
        {
            
            //
            // Special case: M1=M2
            //
            for(j = n2-1; j >= n1; j--)
            {
                ctemp = c(j-n1+1);
                stemp = s(j-n1+1);
                if( ctemp!=1||stemp!=0 )
                {
                    temp = a(m1,j+1);
                    a(m1,j+1) = ctemp*temp-stemp*a(m1,j);
                    a(m1,j) = stemp*temp+ctemp*a(m1,j);
                }
            }
        }
    }
}


/*************************************************************************
The subroutine generates the elementary rotation, so that:

[  CS  SN  ]  .  [ F ]  =  [ R ]
[ -SN  CS  ]     [ G ]     [ 0 ]

CS**2 + SN**2 = 1
*************************************************************************/
void generaterotation(double f, double g, double& cs, double& sn, double& r)
{
    double f1;
    double g1;

    if( g==0 )
    {
        cs = 1;
        sn = 0;
        r = f;
    }
    else
    {
        if( f==0 )
        {
            cs = 0;
            sn = 1;
            r = g;
        }
        else
        {
            f1 = f;
            g1 = g;
            r = sqrt(ap::sqr(f1)+ap::sqr(g1));
            cs = f1/r;
            sn = g1/r;
            if( fabs(f)>fabs(g)&&cs<0 )
            {
                cs = -cs;
                sn = -sn;
                r = -r;
            }
        }
    }
}

/*
static void testrotations()
{
    ap::real_2d_array al1;
    ap::real_2d_array al2;
    ap::real_2d_array ar1;
    ap::real_2d_array ar2;
    ap::real_1d_array cl;
    ap::real_1d_array sl;
    ap::real_1d_array cr;
    ap::real_1d_array sr;
    ap::real_1d_array w;
    int m;
    int n;
    int maxmn;
    double t;
    int pass;
    int passcount;
    int i;
    int j;
    double err;
    double maxerr;
    bool isforward;

    passcount = 1000;
    maxerr = 0;
    for(pass = 1; pass <= passcount; pass++)
    {
        
        //
        // settings
        //
        m = 2+ap::randominteger(50);
        n = 2+ap::randominteger(50);
        isforward = ap::randomreal()>0.5;
        maxmn = ap::maxint(m, n);
        al1.setbounds(1, m, 1, n);
        al2.setbounds(1, m, 1, n);
        ar1.setbounds(1, m, 1, n);
        ar2.setbounds(1, m, 1, n);
        cl.setbounds(1, m-1);
        sl.setbounds(1, m-1);
        cr.setbounds(1, n-1);
        sr.setbounds(1, n-1);
        w.setbounds(1, maxmn);
        
        //
        // matrices and rotaions
        //
        for(i = 1; i <= m; i++)
        {
            for(j = 1; j <= n; j++)
            {
                al1(i,j) = 2*ap::randomreal()-1;
                al2(i,j) = al1(i,j);
                ar1(i,j) = al1(i,j);
                ar2(i,j) = al1(i,j);
            }
        }
        for(i = 1; i <= m-1; i++)
        {
            t = 2*ap::pi()*ap::randomreal();
            cl(i) = cos(t);
            sl(i) = sin(t);
        }
        for(j = 1; j <= n-1; j++)
        {
            t = 2*ap::pi()*ap::randomreal();
            cr(j) = cos(t);
            sr(j) = sin(t);
        }
        
        //
        // Test left
        //
        applyrotationsfromtheleft(isforward, 1, m, 1, n, cl, sl, al1, w);
        for(j = 1; j <= n; j++)
        {
            applyrotationsfromtheleft(isforward, 1, m, j, j, cl, sl, al2, w);
        }
        err = 0;
        for(i = 1; i <= m; i++)
        {
            for(j = 1; j <= n; j++)
            {
                err = ap::maxreal(err, fabs(al1(i,j)-al2(i,j)));
            }
        }
        maxerr = ap::maxreal(err, maxerr);
        
        //
        // Test right
        //
        applyrotationsfromtheright(isforward, 1, m, 1, n, cr, sr, ar1, w);
        for(i = 1; i <= m; i++)
        {
            applyrotationsfromtheright(isforward, i, i, 1, n, cr, sr, ar2, w);
        }
        err = 0;
        for(i = 1; i <= m; i++)
        {
            for(j = 1; j <= n; j++)
            {
                err = ap::maxreal(err, fabs(ar1(i,j)-ar2(i,j)));
            }
        }
        maxerr = ap::maxreal(err, maxerr);
    }
    printf("TESTING ROTATIONS\n");
    printf("Pass count %0ld\n",
        long(passcount));
    printf("Error is %5.3le\n",
        double(maxerr));
}



*/
