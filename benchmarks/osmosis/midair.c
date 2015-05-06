#include <math.h>
#include "osmosis_client.h"

const double R = 0.1;

const double D = 10.0;

const double G = 9.8;

//@dist theta1 = uni(min=0.01,max=1.56)
//@dist theta2 = uni(min=0.01,max=1.56)
//@dist v1 = normal(min=0.01,max=10,mean=3,std=1)
//@dist v2 = normal(min=0.01,max=10,mean=3,std=1)
void midair()
{
  double theta1 = INPUT_D("theta1");
  double theta2 = INPUT_D("theta2");
  double v1 = INPUT_D("v1");
  double v2 = INPUT_D("v2");

  double sin1 = sin(theta1);
  double sin2 = sin(theta2);
  double cos1 = cos(theta1);
  double cos2 = cos(theta2);


  double t = D*(v1*cos1+v2*cos2)/(cos1*cos1*v1*v1+2*cos1*cos2*v1*v2+cos2*cos2*v2*v2+sin1*sin1*v1*v1-2*sin1*sin2*v1*v2+sin2*sin2*v2*v2);

  double x1 = v1*cos1*t;
  double x2 = D-v2*cos2*t;
  double y1 = v1*sin1*t - 0.5*G*t*t;
  double y2 = v2*sin2*t - 0.5*G*t*t;

  double minD2 = (x1-y2)*(x1-y2) + (y1-y2)*(y1-y2);

  ASSERT(minD2 > 4*R*R);
}
