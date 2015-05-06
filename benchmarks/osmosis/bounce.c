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

//
// Our favoriate constant Pi.
//
const double PI = 3.1415926;

//
// Gravitation force
//
const double G = 9.8;

//
// Initial position of ball
//
const double x0 = 0;

//
// Position and width of hole
//
const double HOLE_X = 10;
const double HOLE_RADIUS = 0.05;

//@dist v0 = normal(min=1,max=10,mean=5,std=1.5)
//@dist theta = uni(min=1,max=89)
void bounce()
{
  double v0 = INPUT_D("v0");
  double theta = INPUT_D("theta")*PI/180.0;

  double vx = v0*cos(theta);
  double vy = v0*sin(theta);

  double x = x0;
  double t = 0;
  int bounces = 0;

  //@maxLoop=5
  while ( (x < HOLE_X+HOLE_RADIUS) && (fabs(x-HOLE_X) > HOLE_RADIUS) && bounces < 5) {
    //
    // Time and position of next bounce
    //
    t = sqrt(2)*vy/G;
    x += vx*t;

    //
    // Energy loss in bounce
    //
    vx *= 0.9;
    vy *= 0.9;

    //
    // Increment the bounce count
    //
    bounces += 1;
  }

  ASSERT(fabs(x-HOLE_X) > HOLE_RADIUS);
}
