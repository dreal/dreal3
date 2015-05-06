/*
Copyright (c) 2015 Carnegie Mellon University. All Rights Reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are
met:

1. Redistributions of source code must retain the above copyright
notice, this list of conditions and the following acknowledgments and
disclaimers.

2. Redistributions in binary form must reproduce the above copyright
notice, this list of conditions and the following disclaimer in the
documentation and/or other materials provided with the distribution.

3. The names "Carnegie Mellon University," "SEI" and/or "Software
Engineering Institute" shall not be used to endorse or promote
products derived from this software without prior written
permission. For written permission, please contact
permission@sei.cmu.edu.

4. Products derived from this software may not be called "SEI" nor may
"SEI" appear in their names without prior written permission of
permission@sei.cmu.edu.

5. Redistributions of any form whatsoever must retain the following
acknowledgment:

This material is based upon work funded and supported by the
Department of Defense under Contract No. FA8721-05-C-0003 with
Carnegie Mellon University for the operation of the Software
Engineering Institute, a federally funded research and development
center.

Any opinions, findings and conclusions or recommendations expressed in
this material are those of the author(s) and do not necessarily
reflect the views of the United States Department of Defense.

NO WARRANTY. THIS CARNEGIE MELLON UNIVERSITY AND SOFTWARE ENGINEERING
INSTITUTE MATERIAL IS FURNISHED ON AN AS-IS BASIS. CARNEGIE
MELLON UNIVERSITY MAKES NO WARRANTIES OF ANY KIND, EITHER EXPRESSED OR
IMPLIED, AS TO ANY MATTER INCLUDING, BUT NOT LIMITED TO, WARRANTY OF
FITNESS FOR PURPOSE OR MERCHANTABILITY, EXCLUSIVITY, OR RESULTS
OBTAINED FROM USE OF THE MATERIAL. CARNEGIE MELLON UNIVERSITY DOES NOT
MAKE ANY WARRANTY OF ANY KIND WITH RESPECT TO FREEDOM FROM PATENT,
TRADEMARK, OR COPYRIGHT INFRINGEMENT.

This material has been approved for public release and unlimited distribution.

DM-0002403
*/
#include <math.h>
#include "osmosis_client.h"

const double x1 = 0;
const double x2 = 50;

const double PI = 3.1415926;

const double COLLISION_RADIUS = 1;

//@dist Y1 = uni(min=0,max=50)
//@dist Y2 = uni(min=0,max=50)
//@dist H1 = uni(min=-90,max=90)
//@dist H2 = uni(min=90,max=270)
void collisionAvoid()
{
  double y1 = INPUT_D("Y1");
  double y2 = INPUT_D("Y2");
  double h1 = INPUT_D("H1");
  double h2 = INPUT_D("H2");

  double sin1 = sin(h1*PI/180);
  double cos1 = cos(h1*PI/180);
  double sin2 = sin(h2*PI/180);
  double cos2 = cos(h2*PI/180);

  double v1 = 1;
  double v2 = 1;


  double a0 = v1*cos1 - v2*cos2;
  double a1 = v1*sin1 - v2*sin2;
  double a = a0*a0 + a1*a1;
  double b = 2*(x1-x2)*(v1*cos1-v2*cos2) + 2*(y1-y2)*(v1*sin1-v2*sin2);
  double c0 = x1 - x2;
  double c1 = y1 - y2;
  double c = c0*c0 + c1*c1;

  double q = b*b-4*a*(c-COLLISION_RADIUS);


  ASSERT(q < 0);
}
