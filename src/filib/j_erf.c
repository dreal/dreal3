/*********************************************************************/
/*       fi_lib  --- A fast interval library (Version 1.2)           */
/*        (For copyright and info`s see file "fi_lib.h")             */
/*********************************************************************/

/***********************************************************************/  
/* Stand: 18.04.2000                                                   */
/* Autor: cand.math.oec Stefan Traub, IAM, Universitaet Karlsruhe (TH) */    
/***********************************************************************/

#include "fi_lib.h" 

/* ------------------------------------------------------------------- */
/* ----                    the function j_erf                   ------ */
/* ------------------------------------------------------------------- */

#ifdef LINT_ARGS
local interval j_erf(interval x)
#else
local interval j_erf(x)

interval x;
#endif
{
  interval res;
  double y;

  if (x.INF==x.SUP)             /* point interval */
    { 
      if (x.INF==q_erft[0])
        { res.INF=0.0; res.SUP=0.0; }
      else 
        { 
          if ((x.INF>-q_erft[1])&&(x.INF<q_erft[0]))
            {
              res.INF=-q_minr;
              res.SUP=0.0;
            }
          else 
	    {
	      if ((x.INF>q_erft[0])&&(x.INF<q_erft[1]))
		{         
		  res.INF=0.0;
		  res.SUP=q_minr;
		}
	      else 
		{
		  if (x.INF<=-q_erft[5])
		    {
		      res.INF=-1.0;
		      res.SUP=-1.0+1e-15;
		    }
		  else
		    {
		      if (x.INF>=q_erft[5])
			{
			  res.INF=1.0-1e-15;
			  res.SUP=1.0;
			}
		      else 
			{
			  if (x.INF<=-q_erft[1])
			    {
			      y=q_erf(x.INF);
			      res.INF=y*q_erfp;
			      res.SUP=y*q_erfm;
			    }
			  else
			    {
			      y=q_erf(x.INF);
			      res.INF=y*q_erfm;
			      res.SUP=y*q_erfp;
			    }  
			}
		    }
		}
	    }
	}
    }
  else
    {
      if (x.INF<=-q_erft[5])
	res.INF=-1.0;
      else
	{
	  if (x.INF<=-q_erft[1])
	    res.INF=q_erf(x.INF)*q_erfp;
	  else
	    {
	      if (x.INF<q_erft[0]) 
		res.INF=-q_minr;
	      else
		{
		  if (x.INF<q_erft[1])
		    res.INF=0.0;
		  else
		    {
		      if (x.INF<q_erft[5])
			res.INF=q_erf(x.INF)*q_erfm;
		      else
			res.INF=1.0-1e-15;
		    }
		}
	    }
	}
      if (x.SUP<=-q_erft[5])
	res.SUP=-1.0+1e-15;
      else
	{
	  if (x.SUP<=-q_erft[1])
	    res.SUP=q_erf(x.SUP)*q_erfm;
	  else
	    {
	      if (x.SUP<q_erft[0]) 
		res.SUP=0.0;
	      else
		{
		  if (x.SUP<q_erft[1])
		    res.SUP=q_minr;
		  else 
		    {
		      if (x.SUP<q_erft[5])
			res.SUP=q_erf(x.SUP)*q_erfp;
		      else
			res.SUP=1.0;
		    }
		}
	    }
	}
    }     

  if (res.INF<-1.0) res.INF=-1.0;
  if (res.SUP<=-1.0) res.SUP=-1.0+1e-15;
  if (res.SUP>1.0) res.SUP=1.0;
  if (res.INF>=1.0) res.INF=1.0-1e-15;

  return(res);
}


/* ------------------------------------------------------------------- */
/* ----                    the function j_erfc                  ------ */
/* ------------------------------------------------------------------- */

#ifdef LINT_ARGS
local interval j_erfc(interval x)
#else
local interval j_erfc(x)

interval x;
#endif
{
  interval res;
  double y;

  if (x.INF==x.SUP)             /* point interval */
    { 
      if (x.INF==q_erft[0])
        { res.INF=1.0; res.SUP=1.0; }
      else 
        { 
          if ((x.INF>-q_erft[1])&&(x.INF<q_erft[0]))
            {
              res.INF=1.0;
              res.SUP=1.0+1e-15;   
            }
          else 
	    {
	      if ((x.INF>q_erft[0])&&(x.INF<q_erft[1]))
		{         
		  res.INF=1.0-1e-15;
		  res.SUP=1.0;
		}
	      else 
		{
		  if (x.INF>=q_erft[6])
		    {
		      res.INF=0.0;
		      res.SUP=q_minr;
		    }
		  else 
		    {
		      if (x.INF<=-q_erft[6])
			{
			  res.INF=2.0-1e-15;
			  res.SUP=2.0;
			}
		      else
			{
			  y=q_erfc(x.INF);
			  res.INF=y*q_efcm;
			  res.SUP=y*q_efcp;
			}
		    }
		}  
	    }
	}
    }
  else
    {
      if (x.INF<=-q_erft[6])
	res.SUP=2.0;
      else
	{
	  if (x.INF<=-q_erft[1])
	    res.SUP=q_erfc(x.INF)*q_efcp;
	  else
	    {
	      if (x.INF<q_erft[0]) 
		res.SUP=1.0+1e-15;
	      else
		{
		  if (x.INF<q_erft[1])
		    res.SUP=1.0;
		  else
		    {
		      if (x.INF<q_erft[6])
			res.SUP=q_erfc(x.INF)*q_efcp;
		      else
			res.SUP=q_minr;
		    }
		}
	    }
	}
      if (x.SUP<=-q_erft[6])
	res.INF=2.0-1e-15;
      else
	{
	  if (x.SUP<=-q_erft[1])
	    res.INF=q_erfc(x.SUP)*q_efcm;
	  else
	    {
	      if (x.SUP<q_erft[0]) 
		res.INF=1.0;
	      else
		{
		  if (x.SUP<q_erft[1])
		    res.INF=1.0-1e-15;
		  else
		    {
		      if (x.SUP<q_erft[6])
			res.INF=q_erfc(x.SUP)*q_efcm;
		      else
			res.INF=0.0;
		    }
		}
	    }
	}
    }     

  if (res.INF<0.0) res.INF=0.0;
  if (res.SUP<=0.0) res.SUP=q_minr;
  if (res.SUP>2.0) res.SUP=2.0;  
  if (res.INF>=2.0) res.INF=2.0-1e-15;

  return(res);
}




