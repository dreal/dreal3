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

const double WAIT = 0.025;
const double COLLISION_THRESH = 0.01;

const double MAX_DELAY = 4;

//@dist T11 = uni(min=0,max=1)
//@dist T21 = uni(min=0,max=1)
//@dist T12 = uni(min=0,max=1)
//@dist T22 = uni(min=0,max=1)
//@dist T13 = uni(min=0,max=1)
//@dist T23 = uni(min=0,max=1)
void backoff()
{
  double t1 = INPUT_D("T11");
  double t2 = INPUT_D("T21");

  if (fabs(t1-t2) < COLLISION_THRESH) {
    t1 += WAIT+INPUT_D("T12")*2;
    t2 += WAIT+INPUT_D("T22")*2;
  }
  if (fabs(t1-t2) < COLLISION_THRESH) {
      t1 += WAIT+INPUT_D("T13")*4;
      t2 += WAIT+INPUT_D("T23")*4;
  }

  ASSERT(fabs(t1-t2) > COLLISION_THRESH && t1 < MAX_DELAY && t2 < MAX_DELAY);
}
