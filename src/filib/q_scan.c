/*********************************************************************/
/*       fi_lib  --- A fast interval library (Version 1.2)           */
/*        (For copyright and info`s see file "fi_lib.h")             */
/*********************************************************************/

#include <stdio.h>
#include "fi_lib.h"

double scandown()
{
  double x;
  if (scanf("%lf",&x) != 0) {
      fprintf(stderr, "filib - q_scan.c::scanf failed\n");
  }
  if (fabs(x)>(1e17-1)*1e27) return q_pred(q_pred(x));
  else return q_pred(x);
}

double scanup()
{
  double x;
  if (scanf("%lf",&x) != 0) {
      fprintf(stderr, "filib - q_scan.c::scanf failed\n");
  }
  if (fabs(x)>(1e17-1)*1e27) return q_succ(q_succ(x));
  else return q_succ(x);
}

interval scanInterval()
{
  interval dummy;
  dummy.INF = scandown();
  dummy.SUP = scanup();
  return dummy;
}
