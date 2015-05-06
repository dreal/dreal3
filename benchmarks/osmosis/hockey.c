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
// Target position
//
const double TX = 0.25;
const double TY = 0.5;

//
// Puck radius
//
const double R = 0.02;

//
// Table bounce coordinates
//
const double minX = 0.0;
const double minY = 0.0;
const double maxX = 1.5;
const double maxY = 1.0;

//
// Maximum distance
//
const double Dmax = 10.0;

//@range 0 <= angle <= 6.2831852
//@range 0 <= distance <= 10
void hockeyTable()
{
  double angle = INPUT_D("angle");
  double distance = INPUT_D("distance");

    //
    // Puck position
    //
    double px = 1.25;
    double py = 0.5;

    //
    // Sin and cos of angle
    //
    double sinA = sin(angle);
    double cosA = cos(angle);


    double xHitDist = 0;
    double yHitDist = 0;
	
    double xSign = 1;
    double ySign = 1;

    if (sinA < 0) {
      sinA = -sinA;
      ySign = -1;
      yHitDist = (py-minY); //sinA;
    } else
      yHitDist = (maxY-py); //sinA;

    if (cosA < 0) {
      cosA = -cosA;
      xSign = -1;
      xHitDist = (px-minX); //cosA;
    } else
      xHitDist = (maxX-px); //cosA;
    
    //
    // Bounce off walls until we come to a rest
    //
    //@maxLoop=2
    while (sinA*distance > yHitDist || cosA*distance > xHitDist) {
      if (cosA*yHitDist <= sinA*xHitDist) {
	px += xSign*yHitDist*cosA/sinA;
	py += ySign*yHitDist;
	ySign = -ySign;
	distance -= yHitDist/sinA;
      } else {
	px += xSign*xHitDist;
	py += ySign*xHitDist*sinA/cosA;
	xSign = -xSign;
	distance -= xHitDist/cosA;
      }

      if (xSign > 0) {
	xHitDist = (maxX-px); //cosA;
      } else {
	xHitDist = (px-minX); //cosA;
      }
      if (ySign > 0) {
	yHitDist = (maxY-py); //sinA;
      } else {
	yHitDist = (py-minY); //sinA;
      }
    }


    //
    // Final coast to stop
    //
    px += distance*cosA*xSign;
    py += distance*sinA*ySign;

    //
    // Test to see if we are on the target.
    //
    double dx = TX - px;
    double dy = TY - py;
    double deltaSq = dx*dx + dy*dy;
    ASSERT(deltaSq > R*R);
}
