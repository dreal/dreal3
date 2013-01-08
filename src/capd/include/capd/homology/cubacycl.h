/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file cubacycl.h
///
/// This file contains functions generated using Binary Decision Diagrams
/// for checking the acyclicity of full cubical neighborhoods of a cube
/// in dimensions 1, 2, and 3.
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started on November 12, 2005. Last revision: April 23, 2008.


#ifndef _CAPD_HOMOLOGY_CUBACYCL_H_ 
#define _CAPD_HOMOLOGY_CUBACYCL_H_ 

#include "capd/homology/bitfield.h"

namespace capd {
namespace homology {

// --------------------------------------------------
// ------------------- acyclic1d --------------------
// --------------------------------------------------

/// Verifies whether the neighborhood of a 1-dimensional "cube" is acyclic.
template <class NeighborCheck>
bool acyclic1d (NeighborCheck &n)
{
	if (n. check (0)) goto K4; else goto K5;
K4:	if (n. check (1)) return false; else return true;
K5:	if (n. check (1)) return true; else return false;
} /* acyclic1d */


// --------------------------------------------------
// ------------------- acyclic2d --------------------
// --------------------------------------------------

/// Verifies whether the neighborhood of a 2-dimensional "cube" is acyclic.
template <class NeighborCheck>
bool acyclic2d (NeighborCheck &n)
{
	if (n. check (0)) goto L659; else goto L20;
L12:	return !n. check (5);
L13:	return n. check (5);
L14:	return !n. check (6);
L16:	return !n. check (7);
L17:	return n. check (7);
L18:	if (n. check (2)) goto L514; else goto L523;
L20:	if (n. check (1)) goto L40; else goto L18;
L21:	if (n. check (5)) return true; else goto L651;
L23:	if (n. check (4)) goto L514; else goto L21;
L24:	if (n. check (4)) return false; else goto L514;
L40:	if (n. check (2)) goto L513; else goto L637;
L505:	if (n. check (6)) return false; else goto L16;
L507:	if (n. check (5)) return true; else goto L16;
L508:	if (n. check (2)) goto L507; else goto L646;
L513:	if (n. check (5)) return true; else goto L14;
L514:	if (n. check (5)) return false; else goto L505;
L523:	if (n. check (3)) goto L24; else goto L23;
L637:	if (n. check (3)) return false; else goto L513;
L646:	if (n. check (4)) return false; else goto L507;
L651:	if (n. check (6)) goto L16; else goto L17;
L658:	if (n. check (2)) goto L12; else goto L13;
L659:	if (n. check (1)) goto L658; else goto L508;
} /* acyclic2d */


// --------------------------------------------------
// ------------------- acyclic3d --------------------
// --------------------------------------------------

/// Verifies whether the neighborhood of a 3-dimensional cube is acyclic.
/// This procedure has been received from G. Malandain, see
/// L. Robert and G. Malandain, Computer Vision and Image Understanding,
/// Fast Binary Image Processing Using Binary Decision Diagrams,
/// October 1998, No. 1, Vol. 72, pp. 1--9.
template <class NeighborCheck>
bool acyclic3d_Malandain (NeighborCheck &n)
{
	int statInv = 0;

/*L147001:*/ if (n. check (5)) {goto L143033;} else {goto L120232;}
L143033: if (n. check (0)) {goto L123529;} else {goto L118136;}
L123529: if (n. check (17)) {goto L146041;} else {goto L144920;}
L146041: if (n. check (2)) {goto L124809;} else {goto L145112;}
L124809: if (n. check (1)) {goto L106441;} else {goto L124904;}
L106441: if (n. check (8)) {goto L105737;} else {goto L105736;}
L124904: if (n. check (8)) {goto L105736;} else {goto L106537;}
L106537: if (n. check (10)) {goto L105737;} else {goto L105736;}
L145112: if (n. check (1)) {goto L124648;} else {goto L108505;}
L124648: if (n. check (8)) {goto L105736;} else {goto L106473;}
L106473: if (n. check (11)) {goto L105737;} else {goto L105736;}
L108505: if (n. check (8)) {goto L106281;} else {goto L114329;}
L106281: if (n. check (4)) {goto L105737;} else {goto L105736;}
L114329: if (n. check (4)) {goto L128185;} else {goto L115769;}
L128185: if (n. check (11)) {goto L105737;} else {goto L106537;}
L115769: if (n. check (11)) {goto L106537;} else {goto L144408;}
L144408: if (n. check (10)) {goto L105736;} else {goto L106569;}
L106569: if (n. check (13)) {goto L105737;} else {goto L105736;}
L144920: if (n. check (2)) {goto L109080;} else {goto L116761;}
L109080: if (n. check (1)) {statInv=!statInv;goto L106441;} else {goto L118697;}
L118697: if (n. check (19)) {goto L105737;} else {goto L124904;}
L116761: if (n. check (20)) {goto L117817;} else {goto L127624;}
L117817: if (n. check (1)) {goto L105737;} else {goto L117017;}
L117017: if (n. check (19)) {goto L105737;} else {goto L108505;}
L127624: if (n. check (1)) {goto L124648;} else {goto L114553;}
L114553: if (n. check (19)) {goto L108505;} else {goto L118680;}
L118680: if (n. check (8)) {goto L130584;} else {goto L130041;}
L130584: if (n. check (22)) {statInv=!statInv;goto L106281;} else {goto L105736;}
L130041: if (n. check (22)) {goto L126505;} else {goto L137305;}
L126505: if (n. check (4)) {goto L127657;} else {goto L105737;}
L127657: if (n. check (11)) {goto L106537;} else {statInv=!statInv;goto L106537;}
L137305: if (n. check (4)) {goto L127657;} else {goto L115769;}
L118136: if (n. check (17)) {goto L131608;} else {goto L137497;}
L131608: if (n. check (2)) {goto L115784;} else {goto L108185;}
L115784: if (n. check (1)) {goto L117608;} else {goto L121673;}
L117608: if (n. check (9)) {statInv=!statInv;goto L106441;} else {goto L105736;}
L121673: if (n. check (9)) {goto L105737;} else {goto L134921;}
L134921: if (n. check (8)) {goto L105737;} else {goto L106537;}
L108185: if (n. check (1)) {goto L145497;} else {goto L120857;}
L145497: if (n. check (3)) {goto L146729;} else {goto L118584;}
L146729: if (n. check (9)) {goto L105737;} else {goto L130201;}
L130201: if (n. check (8)) {goto L105737;} else {goto L106473;}
L118584: if (n. check (9)) {goto L124648;} else {goto L120680;}
L120680: if (n. check (8)) {goto L105736;} else {goto L119432;}
L119432: if (n. check (12)) {statInv=!statInv;goto L106473;} else {goto L105736;}
L120857: if (n. check (3)) {goto L129049;} else {goto L115481;}
L129049: if (n. check (9)) {goto L105737;} else {goto L120265;}
L120265: if (n. check (8)) {goto L105737;} else {goto L114329;}
L115481: if (n. check (9)) {goto L108505;} else {goto L126889;}
L126889: if (n. check (8)) {goto L106281;} else {goto L146681;}
L146681: if (n. check (4)) {goto L129465;} else {goto L121080;}
L129465: if (n. check (12)) {goto L109273;} else {goto L106537;}
L109273: if (n. check (11)) {goto L106537;} else {goto L105737;}
L121080: if (n. check (12)) {goto L121864;} else {goto L107128;}
L121864: if (n. check (11)) {statInv=!statInv;goto L106537;} else {goto L105737;}
L107128: if (n. check (11)) {statInv=!statInv;goto L106537;} else {goto L144408;}
L137497: if (n. check (18)) {goto L109625;} else {goto L144984;}
L109625: if (n. check (2)) {goto L116633;} else {goto L116569;}
L116633: if (n. check (1)) {goto L105737;} else {goto L107753;}
L107753: if (n. check (19)) {goto L105737;} else {goto L121673;}
L116569: if (n. check (20)) {goto L137753;} else {goto L126057;}
L137753: if (n. check (1)) {goto L105737;} else {goto L122249;}
L122249: if (n. check (19)) {goto L105737;} else {goto L120857;}
L126057: if (n. check (1)) {goto L145497;} else {goto L119273;}
L119273: if (n. check (19)) {goto L120857;} else {goto L107833;}
L107833: if (n. check (3)) {goto L135929;} else {goto L122824;}
L135929: if (n. check (9)) {goto L105737;} else {goto L107961;}
L107961: if (n. check (8)) {goto L105737;} else {goto L130041;}
L122824: if (n. check (9)) {goto L118680;} else {goto L121448;}
L121448: if (n. check (8)) {goto L130584;} else {goto L124136;}
L124136: if (n. check (22)) {goto L143960;} else {goto L125928;}
L143960: if (n. check (4)) {goto L146936;} else {goto L105737;}
L146936: if (n. check (12)) {goto L121864;} else {statInv=!statInv;goto L106537;}
L125928: if (n. check (4)) {goto L146936;} else {goto L121080;}
L144984: if (n. check (2)) {goto L120456;} else {goto L128441;}
L120456: if (n. check (1)) {goto L117608;} else {goto L117657;}
L117657: if (n. check (19)) {goto L121673;} else {goto L127016;}
L127016: if (n. check (9)) {goto L124904;} else {statInv=!statInv;goto L134921;}
L128441: if (n. check (20)) {goto L121577;} else {goto L114488;}
L121577: if (n. check (1)) {goto L145497;} else {goto L124089;}
L124089: if (n. check (19)) {goto L120857;} else {goto L129337;}
L129337: if (n. check (3)) {goto L130169;} else {goto L135480;}
L130169: if (n. check (9)) {goto L108505;} else {goto L107225;}
L107225: if (n. check (8)) {goto L106281;} else {goto L126025;}
L126025: if (n. check (4)) {goto L123049;} else {goto L121864;}
L123049: if (n. check (11)) {goto L105737;} else {statInv=!statInv;goto L106537;}
L135480: if (n. check (9)) {goto L130904;} else {goto L146968;}
L130904: if (n. check (8)) {statInv=!statInv;goto L106281;} else {goto L126505;}
L146968: if (n. check (8)) {statInv=!statInv;goto L106281;} else {goto L143960;}
L114488: if (n. check (1)) {goto L146616;} else {goto L129881;}
L146616: if (n. check (3)) {goto L134312;} else {goto L136217;}
L134312: if (n. check (9)) {goto L124648;} else {statInv=!statInv;goto L130201;}
L136217: if (n. check (21)) {goto L105737;} else {goto L118584;}
L129881: if (n. check (19)) {goto L133913;} else {goto L125960;}
L133913: if (n. check (3)) {goto L108953;} else {goto L122217;}
L108953: if (n. check (9)) {goto L108505;} else {goto L136281;}
L136281: if (n. check (8)) {goto L106281;} else {goto L143177;}
L143177: if (n. check (4)) {goto L109273;} else {goto L121864;}
L122217: if (n. check (21)) {goto L105737;} else {goto L115481;}
L125960: if (n. check (3)) {goto L134536;} else {goto L134697;}
L134536: if (n. check (9)) {goto L118680;} else {goto L135096;}
L135096: if (n. check (8)) {goto L130584;} else {goto L137704;}
L137704: if (n. check (22)) {goto L143128;} else {goto L121864;}
L143128: if (n. check (4)) {goto L121864;} else {goto L105737;}
L134697: if (n. check (21)) {goto L105737;} else {goto L122824;}
L120232: if (n. check (0)) {goto L126936;} else {goto L126121;}
L126936: if (n. check (17)) {goto L123272;} else {goto L132825;}
L123272: if (n. check (2)) {goto L123848;} else {goto L131161;}
L123848: if (n. check (1)) {goto L114968;} else {goto L119785;}
L114968: if (n. check (14)) {statInv=!statInv;goto L106441;} else {goto L105736;}
L119785: if (n. check (7)) {goto L135721;} else {goto L128600;}
L135721: if (n. check (14)) {goto L105737;} else {goto L134921;}
L128600: if (n. check (14)) {goto L124904;} else {goto L135352;}
L135352: if (n. check (8)) {goto L105736;} else {goto L136472;}
L136472: if (n. check (16)) {statInv=!statInv;goto L106537;} else {goto L105736;}
L131161: if (n. check (1)) {goto L113913;} else {goto L145833;}
L113913: if (n. check (14)) {goto L105737;} else {goto L130201;}
L145833: if (n. check (7)) {goto L132249;} else {goto L142617;}
L132249: if (n. check (14)) {goto L105737;} else {goto L120265;}
L142617: if (n. check (14)) {goto L108505;} else {goto L137769;}
L137769: if (n. check (8)) {goto L106281;} else {goto L125321;}
L125321: if (n. check (4)) {goto L142841;} else {goto L129368;}
L142841: if (n. check (11)) {goto L105737;} else {goto L136472;}
L129368: if (n. check (11)) {goto L136472;} else {goto L106809;}
L106809: if (n. check (16)) {goto L105737;} else {goto L130457;}
L130457: if (n. check (10)) {goto L105737;} else {goto L106569;}
L132825: if (n. check (23)) {goto L136121;} else {goto L123080;}
L136121: if (n. check (2)) {goto L123785;} else {goto L132537;}
L123785: if (n. check (1)) {goto L105737;} else {goto L108697;}
L108697: if (n. check (19)) {goto L105737;} else {goto L119785;}
L132537: if (n. check (20)) {goto L138169;} else {goto L142761;}
L138169: if (n. check (1)) {goto L105737;} else {goto L116793;}
L116793: if (n. check (19)) {goto L105737;} else {goto L145833;}
L142761: if (n. check (1)) {goto L113913;} else {goto L135737;}
L135737: if (n. check (19)) {goto L145833;} else {goto L131481;}
L131481: if (n. check (7)) {goto L123753;} else {goto L107608;}
L123753: if (n. check (14)) {goto L105737;} else {goto L107961;}
L107608: if (n. check (14)) {goto L118680;} else {goto L109400;}
L109400: if (n. check (8)) {goto L130584;} else {goto L128504;}
L128504: if (n. check (22)) {goto L135224;} else {goto L124712;}
L135224: if (n. check (4)) {goto L144696;} else {goto L105737;}
L144696: if (n. check (11)) {goto L136472;} else {goto L105737;}
L124712: if (n. check (4)) {goto L144696;} else {goto L129368;}
L123080: if (n. check (2)) {goto L107192;} else {goto L114137;}
L107192: if (n. check (1)) {goto L114968;} else {goto L130521;}
L130521: if (n. check (19)) {goto L119785;} else {goto L133768;}
L133768: if (n. check (7)) {goto L136760;} else {goto L127209;}
L136760: if (n. check (14)) {goto L124904;} else {statInv=!statInv;goto L134921;}
L127209: if (n. check (25)) {goto L105737;} else {goto L128600;}
L114137: if (n. check (20)) {goto L107801;} else {goto L132280;}
L107801: if (n. check (1)) {goto L113913;} else {goto L143225;}
L143225: if (n. check (19)) {goto L145833;} else {goto L136249;}
L136249: if (n. check (7)) {goto L132345;} else {goto L130361;}
L132345: if (n. check (14)) {goto L108505;} else {goto L107225;}
L130361: if (n. check (25)) {goto L105737;} else {goto L142617;}
L132280: if (n. check (1)) {goto L114008;} else {goto L106649;}
L114008: if (n. check (14)) {goto L124648;} else {statInv=!statInv;goto L130201;}
L106649: if (n. check (19)) {goto L137465;} else {goto L121512;}
L137465: if (n. check (7)) {goto L130329;} else {goto L144904;}
L130329: if (n. check (14)) {goto L108505;} else {goto L136281;}
L144904: if (n. check (14)) {goto L130904;} else {goto L132040;}
L132040: if (n. check (8)) {statInv=!statInv;goto L106281;} else {goto L135224;}
L121512: if (n. check (7)) {goto L134152;} else {goto L117401;}
L134152: if (n. check (14)) {goto L118680;} else {goto L135096;}
L117401: if (n. check (25)) {goto L105737;} else {goto L107608;}
L126121: if (n. check (17)) {goto L123817;} else {goto L145849;}
L123817: if (n. check (6)) {goto L123465;} else {goto L119336;}
L123465: if (n. check (2)) {goto L122809;} else {goto L117305;}
L122809: if (n. check (1)) {goto L118169;} else {goto L107769;}
L118169: if (n. check (9)) {goto L105737;} else {goto L123337;}
L123337: if (n. check (14)) {goto L105737;} else {goto L106441;}
L107769: if (n. check (9)) {goto L105737;} else {goto L125993;}
L125993: if (n. check (7)) {goto L135721;} else {goto L145145;}
L145145: if (n. check (14)) {goto L134921;} else {goto L114105;}
L114105: if (n. check (8)) {goto L105737;} else {goto L136472;}
L117305: if (n. check (1)) {goto L143769;} else {goto L146873;}
L143769: if (n. check (3)) {goto L125865;} else {goto L132665;}
L125865: if (n. check (9)) {goto L105737;} else {goto L113913;}
L132665: if (n. check (9)) {goto L113913;} else {goto L128825;}
L128825: if (n. check (14)) {goto L105737;} else {goto L135865;}
L135865: if (n. check (8)) {goto L105737;} else {goto L119432;}
L146873: if (n. check (3)) {goto L146297;} else {goto L146233;}
L146297: if (n. check (9)) {goto L105737;} else {goto L117241;}
L117241: if (n. check (7)) {goto L132249;} else {goto L106585;}
L106585: if (n. check (14)) {goto L120265;} else {goto L126537;}
L126537: if (n. check (8)) {goto L105737;} else {goto L125321;}
L146233: if (n. check (9)) {goto L145833;} else {goto L125417;}
L125417: if (n. check (7)) {goto L134009;} else {goto L125369;}
L134009: if (n. check (14)) {goto L105737;} else {goto L145977;}
L145977: if (n. check (8)) {goto L105737;} else {goto L146681;}
L125369: if (n. check (14)) {goto L126889;} else {goto L136233;}
L136233: if (n. check (8)) {goto L106281;} else {goto L136440;}
L136440: if (n. check (4)) {goto L136056;} else {goto L108601;}
L136056: if (n. check (12)) {goto L144696;} else {goto L136472;}
L108601: if (n. check (12)) {goto L105737;} else {goto L118617;}
L118617: if (n. check (11)) {goto L105737;} else {goto L106809;}
L119336: if (n. check (2)) {goto L134824;} else {goto L124105;}
L134824: if (n. check (1)) {goto L115992;} else {goto L128377;}
L115992: if (n. check (9)) {goto L114968;} else {goto L146072;}
L146072: if (n. check (15)) {statInv=!statInv;goto L123337;} else {goto L105736;}
L128377: if (n. check (9)) {goto L119785;} else {goto L130729;}
L130729: if (n. check (7)) {goto L122041;} else {goto L108056;}
L122041: if (n. check (15)) {goto L107273;} else {goto L134921;}
L107273: if (n. check (14)) {goto L134921;} else {goto L105737;}
L108056: if (n. check (15)) {goto L134568;} else {goto L134440;}
L134568: if (n. check (14)) {statInv=!statInv;goto L134921;} else {statInv=!statInv;goto L106441;}
L134440: if (n. check (14)) {statInv=!statInv;goto L134921;} else {goto L135352;}
L124105: if (n. check (1)) {goto L136841;} else {goto L108153;}
L136841: if (n. check (3)) {goto L143209;} else {goto L120488;}
L143209: if (n. check (9)) {goto L113913;} else {goto L143161;}
L143161: if (n. check (15)) {goto L123017;} else {goto L130201;}
L123017: if (n. check (14)) {goto L130201;} else {goto L105737;}
L120488: if (n. check (9)) {goto L114008;} else {goto L143832;}
L143832: if (n. check (15)) {goto L123496;} else {goto L120680;}
L123496: if (n. check (14)) {goto L120680;} else {statInv=!statInv;goto L106441;}
L108153: if (n. check (3)) {goto L136825;} else {goto L120873;}
L136825: if (n. check (9)) {goto L145833;} else {goto L121833;}
L121833: if (n. check (7)) {goto L108441;} else {goto L131321;}
L108441: if (n. check (15)) {goto L126729;} else {goto L120265;}
L126729: if (n. check (14)) {goto L120265;} else {goto L105737;}
L131321: if (n. check (15)) {goto L145177;} else {goto L129945;}
L145177: if (n. check (14)) {goto L107225;} else {goto L107065;}
L107065: if (n. check (8)) {goto L106281;} else {goto L105737;}
L129945: if (n. check (14)) {goto L107225;} else {goto L137769;}
L120873: if (n. check (9)) {goto L137465;} else {goto L109305;}
L109305: if (n. check (7)) {goto L121257;} else {goto L135992;}
L121257: if (n. check (15)) {goto L114393;} else {goto L126889;}
L114393: if (n. check (14)) {goto L126889;} else {goto L107065;}
L135992: if (n. check (15)) {goto L108376;} else {goto L146136;}
L108376: if (n. check (14)) {goto L146968;} else {goto L143384;}
L143384: if (n. check (8)) {statInv=!statInv;goto L106281;} else {goto L105737;}
L146136: if (n. check (14)) {goto L146968;} else {goto L106968;}
L106968: if (n. check (8)) {statInv=!statInv;goto L106281;} else {goto L136440;}
L145849: if (n. check (23)) {goto L136025;} else {goto L131385;}
L136025: if (n. check (18)) {goto L128953;} else {goto L144505;}
L128953: if (n. check (6)) {goto L136921;} else {goto L115561;}
L136921: if (n. check (2)) {goto L115705;} else {goto L124425;}
L115705: if (n. check (1)) {goto L105737;} else {goto L116729;}
L116729: if (n. check (19)) {goto L105737;} else {goto L107769;}
L124425: if (n. check (20)) {goto L114617;} else {goto L133241;}
L114617: if (n. check (1)) {goto L105737;} else {goto L116825;}
L116825: if (n. check (19)) {goto L105737;} else {goto L146873;}
L133241: if (n. check (1)) {goto L143769;} else {goto L123241;}
L123241: if (n. check (19)) {goto L146873;} else {goto L125481;}
L125481: if (n. check (3)) {goto L137737;} else {goto L123433;}
L137737: if (n. check (9)) {goto L105737;} else {goto L108409;}
L108409: if (n. check (7)) {goto L123753;} else {goto L135769;}
L135769: if (n. check (14)) {goto L107961;} else {goto L134025;}
L134025: if (n. check (8)) {goto L105737;} else {goto L128504;}
L123433: if (n. check (9)) {goto L131481;} else {goto L114905;}
L114905: if (n. check (7)) {goto L131865;} else {goto L108632;}
L131865: if (n. check (14)) {goto L105737;} else {goto L129849;}
L129849: if (n. check (8)) {goto L105737;} else {goto L124136;}
L108632: if (n. check (14)) {goto L121448;} else {goto L109112;}
L109112: if (n. check (8)) {goto L130584;} else {goto L116281;}
L116281: if (n. check (22)) {goto L105737;} else {goto L135193;}
L135193: if (n. check (4)) {goto L105737;} else {goto L108601;}
L115561: if (n. check (2)) {goto L127913;} else {goto L134873;}
L127913: if (n. check (1)) {goto L105737;} else {goto L145689;}
L145689: if (n. check (19)) {goto L105737;} else {goto L128377;}
L134873: if (n. check (20)) {goto L115353;} else {goto L116217;}
L115353: if (n. check (1)) {goto L105737;} else {goto L131193;}
L131193: if (n. check (19)) {goto L105737;} else {goto L108153;}
L116217: if (n. check (1)) {goto L136841;} else {goto L137209;}
L137209: if (n. check (19)) {goto L108153;} else {goto L107865;}
L107865: if (n. check (3)) {goto L142969;} else {goto L124232;}
L142969: if (n. check (9)) {goto L131481;} else {goto L129193;}
L129193: if (n. check (7)) {goto L146201;} else {goto L106616;}
L146201: if (n. check (15)) {goto L132297;} else {goto L107961;}
L132297: if (n. check (14)) {goto L107961;} else {goto L105737;}
L106616: if (n. check (15)) {goto L134280;} else {goto L121336;}
L134280: if (n. check (14)) {goto L135096;} else {goto L124616;}
L124616: if (n. check (8)) {goto L130584;} else {goto L105737;}
L121336: if (n. check (14)) {goto L135096;} else {goto L109400;}
L124232: if (n. check (9)) {goto L143576;} else {goto L145816;}
L143576: if (n. check (7)) {goto L134152;} else {goto L105737;}
L145816: if (n. check (7)) {goto L145656;} else {goto L145577;}
L145656: if (n. check (15)) {goto L134408;} else {goto L121448;}
L134408: if (n. check (14)) {goto L121448;} else {goto L124616;}
L145577: if (n. check (15)) {goto L105737;} else {goto L122153;}
L122153: if (n. check (14)) {goto L105737;} else {goto L119721;}
L119721: if (n. check (8)) {goto L105737;} else {goto L116281;}
L144505: if (n. check (6)) {goto L127689;} else {goto L117912;}
L127689: if (n. check (2)) {goto L129081;} else {goto L142873;}
L129081: if (n. check (1)) {goto L118169;} else {goto L120937;}
L120937: if (n. check (19)) {goto L107769;} else {goto L122745;}
L122745: if (n. check (9)) {goto L119785;} else {goto L108665;}
L108665: if (n. check (7)) {goto L131129;} else {goto L134568;}
L131129: if (n. check (14)) {goto L105737;} else {statInv=!statInv;goto L124904;}
L142873: if (n. check (20)) {goto L125065;} else {goto L137977;}
L125065: if (n. check (1)) {goto L143769;} else {goto L106873;}
L106873: if (n. check (19)) {goto L146873;} else {goto L122889;}
L122889: if (n. check (3)) {goto L120137;} else {goto L116921;}
L120137: if (n. check (9)) {goto L145833;} else {goto L120121;}
L120121: if (n. check (7)) {goto L128009;} else {goto L145177;}
L128009: if (n. check (14)) {goto L105737;} else {goto L114057;}
L114057: if (n. check (8)) {goto L105737;} else {goto L126025;}
L116921: if (n. check (9)) {goto L136537;} else {goto L109465;}
L136537: if (n. check (7)) {goto L121129;} else {goto L144904;}
L121129: if (n. check (14)) {goto L105737;} else {goto L127305;}
L127305: if (n. check (8)) {goto L105737;} else {goto L126505;}
L109465: if (n. check (7)) {goto L126089;} else {goto L108376;}
L126089: if (n. check (14)) {goto L105737;} else {goto L128137;}
L128137: if (n. check (8)) {goto L105737;} else {goto L143960;}
L137977: if (n. check (1)) {goto L137369;} else {goto L131033;}
L137369: if (n. check (3)) {goto L121961;} else {goto L120809;}
L121961: if (n. check (9)) {goto L113913;} else {goto L108281;}
L108281: if (n. check (14)) {goto L105737;} else {statInv=!statInv;goto L124648;}
L120809: if (n. check (21)) {goto L105737;} else {goto L132665;}
L131033: if (n. check (19)) {goto L115257;} else {goto L131833;}
L115257: if (n. check (3)) {goto L143801;} else {goto L117273;}
L143801: if (n. check (9)) {goto L145833;} else {goto L118777;}
L118777: if (n. check (7)) {goto L144089;} else {goto L144841;}
L144089: if (n. check (14)) {goto L105737;} else {goto L121353;}
L121353: if (n. check (8)) {goto L105737;} else {goto L143177;}
L144841: if (n. check (14)) {goto L136281;} else {goto L135801;}
L135801: if (n. check (8)) {goto L106281;} else {goto L135224;}
L117273: if (n. check (21)) {goto L105737;} else {goto L146233;}
L131833: if (n. check (3)) {goto L122505;} else {goto L119593;}
L122505: if (n. check (9)) {goto L131481;} else {goto L123721;}
L123721: if (n. check (7)) {goto L133721;} else {goto L134280;}
L133721: if (n. check (14)) {goto L105737;} else {goto L133561;}
L133561: if (n. check (8)) {goto L105737;} else {goto L137704;}
L119593: if (n. check (21)) {goto L105737;} else {goto L123433;}
L117912: if (n. check (2)) {goto L137048;} else {goto L136601;}
L137048: if (n. check (1)) {goto L115992;} else {goto L119881;}
L119881: if (n. check (19)) {goto L128377;} else {goto L137912;}
L137912: if (n. check (9)) {goto L119944;} else {goto L127336;}
L119944: if (n. check (7)) {goto L136760;} else {goto L105737;}
L127336: if (n. check (7)) {goto L115576;} else {goto L105737;}
L115576: if (n. check (15)) {goto L134568;} else {statInv=!statInv;goto L134921;}
L136601: if (n. check (20)) {goto L128025;} else {goto L129304;}
L128025: if (n. check (1)) {goto L136841;} else {goto L120985;}
L120985: if (n. check (19)) {goto L108153;} else {goto L120041;}
L120041: if (n. check (3)) {goto L118553;} else {goto L120712;}
L118553: if (n. check (9)) {goto L118905;} else {goto L119177;}
L118905: if (n. check (7)) {goto L132345;} else {goto L105737;}
L119177: if (n. check (7)) {goto L126249;} else {goto L105737;}
L126249: if (n. check (15)) {goto L145177;} else {goto L107225;}
L120712: if (n. check (9)) {goto L124200;} else {goto L127848;}
L124200: if (n. check (7)) {goto L107672;} else {goto L105737;}
L107672: if (n. check (14)) {goto L130904;} else {goto L144024;}
L144024: if (n. check (8)) {statInv=!statInv;goto L106281;} else {goto L143128;}
L127848: if (n. check (7)) {goto L146920;} else {goto L105737;}
L146920: if (n. check (15)) {goto L108376;} else {goto L146968;}
L129304: if (n. check (1)) {goto L125560;} else {goto L132601;}
L125560: if (n. check (3)) {goto L125576;} else {goto L121769;}
L125576: if (n. check (9)) {goto L114008;} else {goto L124008;}
L124008: if (n. check (15)) {goto L115496;} else {statInv=!statInv;goto L130201;}
L115496: if (n. check (14)) {statInv=!statInv;goto L130201;} else {statInv=!statInv;goto L106441;}
L121769: if (n. check (21)) {goto L105737;} else {goto L120488;}
L132601: if (n. check (19)) {goto L106681;} else {goto L133080;}
L106681: if (n. check (3)) {goto L144729;} else {goto L109209;}
L144729: if (n. check (9)) {goto L137465;} else {goto L108985;}
L108985: if (n. check (7)) {goto L123113;} else {goto L144568;}
L123113: if (n. check (15)) {goto L133785;} else {goto L136281;}
L133785: if (n. check (14)) {goto L136281;} else {goto L107065;}
L144568: if (n. check (15)) {goto L137272;} else {goto L138440;}
L137272: if (n. check (14)) {goto L144024;} else {goto L143384;}
L138440: if (n. check (14)) {goto L144024;} else {goto L132040;}
L109209: if (n. check (21)) {goto L105737;} else {goto L120873;}
L133080: if (n. check (3)) {goto L114632;} else {goto L126409;}
L114632: if (n. check (9)) {goto L143576;} else {goto L143896;}
L143896: if (n. check (7)) {goto L131112;} else {goto L105737;}
L131112: if (n. check (15)) {goto L134280;} else {goto L135096;}
L126409: if (n. check (21)) {goto L105737;} else {goto L124232;}
L131385: if (n. check (18)) {goto L128985;} else {goto L132920;}
L128985: if (n. check (6)) {goto L115833;} else {goto L143816;}
L115833: if (n. check (2)) {goto L120841;} else {goto L138329;}
L120841: if (n. check (1)) {goto L118169;} else {goto L143481;}
L143481: if (n. check (19)) {goto L107769;} else {goto L121801;}
L121801: if (n. check (9)) {goto L105737;} else {goto L118809;}
L118809: if (n. check (7)) {goto L121609;} else {goto L116665;}
L121609: if (n. check (14)) {goto L134921;} else {statInv=!statInv;goto L124904;}
L116665: if (n. check (25)) {goto L105737;} else {goto L145145;}
L138329: if (n. check (20)) {goto L125225;} else {goto L124553;}
L125225: if (n. check (1)) {goto L143769;} else {goto L117721;}
L117721: if (n. check (19)) {goto L146873;} else {goto L127081;}
L127081: if (n. check (3)) {goto L120905;} else {goto L130009;}
L120905: if (n. check (9)) {goto L105737;} else {goto L126265;}
L126265: if (n. check (7)) {goto L136137;} else {goto L107321;}
L136137: if (n. check (14)) {goto L120265;} else {goto L114057;}
L107321: if (n. check (25)) {goto L105737;} else {goto L106585;}
L130009: if (n. check (9)) {goto L136249;} else {goto L124745;}
L124745: if (n. check (7)) {goto L115609;} else {goto L115385;}
L115609: if (n. check (14)) {goto L126889;} else {goto L109561;}
L109561: if (n. check (8)) {goto L106281;} else {goto L143960;}
L115385: if (n. check (25)) {goto L105737;} else {goto L125369;}
L124553: if (n. check (1)) {goto L143417;} else {goto L129209;}
L143417: if (n. check (3)) {goto L138297;} else {goto L130712;}
L138297: if (n. check (9)) {goto L105737;} else {goto L126857;}
L126857: if (n. check (14)) {goto L130201;} else {statInv=!statInv;goto L124648;}
L130712: if (n. check (9)) {goto L114008;} else {goto L123496;}
L129209: if (n. check (19)) {goto L144537;} else {goto L132217;}
L144537: if (n. check (3)) {goto L117785;} else {goto L137625;}
L117785: if (n. check (9)) {goto L105737;} else {goto L108521;}
L108521: if (n. check (7)) {goto L125513;} else {goto L119001;}
L125513: if (n. check (14)) {goto L120265;} else {goto L121353;}
L119001: if (n. check (14)) {goto L127305;} else {goto L119737;}
L119737: if (n. check (8)) {goto L105737;} else {goto L135224;}
L137625: if (n. check (9)) {goto L137465;} else {goto L143353;}
L143353: if (n. check (7)) {goto L114393;} else {goto L108376;}
L132217: if (n. check (3)) {goto L137113;} else {goto L145208;}
L137113: if (n. check (9)) {goto L105737;} else {goto L119849;}
L119849: if (n. check (7)) {goto L132761;} else {goto L138025;}
L132761: if (n. check (14)) {goto L107961;} else {goto L133561;}
L138025: if (n. check (25)) {goto L105737;} else {goto L135769;}
L145208: if (n. check (9)) {goto L121512;} else {goto L138040;}
L138040: if (n. check (7)) {goto L134408;} else {goto L133017;}
L133017: if (n. check (25)) {goto L105737;} else {goto L108632;}
L143816: if (n. check (2)) {goto L137176;} else {goto L127721;}
L137176: if (n. check (1)) {goto L115992;} else {goto L146009;}
L146009: if (n. check (19)) {goto L128377;} else {goto L130120;}
L130120: if (n. check (9)) {goto L133768;} else {goto L120296;}
L120296: if (n. check (7)) {goto L115576;} else {goto L126153;}
L126153: if (n. check (25)) {goto L105737;} else {goto L108056;}
L127721: if (n. check (20)) {goto L125161;} else {goto L118664;}
L125161: if (n. check (1)) {goto L136841;} else {goto L144249;}
L144249: if (n. check (19)) {goto L108153;} else {goto L126713;}
L126713: if (n. check (3)) {goto L123305;} else {goto L143192;}
L123305: if (n. check (9)) {goto L136249;} else {goto L137657;}
L137657: if (n. check (7)) {goto L126249;} else {goto L146377;}
L146377: if (n. check (25)) {goto L105737;} else {goto L131321;}
L143192: if (n. check (9)) {goto L116184;} else {goto L125128;}
L116184: if (n. check (7)) {goto L107672;} else {goto L137433;}
L137433: if (n. check (25)) {goto L105737;} else {goto L144904;}
L125128: if (n. check (7)) {goto L146920;} else {goto L134137;}
L134137: if (n. check (25)) {goto L105737;} else {goto L135992;}
L118664: if (n. check (1)) {goto L109432;} else {goto L109033;}
L109432: if (n. check (3)) {goto L125576;} else {goto L105737;}
L109033: if (n. check (19)) {goto L134217;} else {goto L122120;}
L134217: if (n. check (3)) {goto L144729;} else {goto L105737;}
L122120: if (n. check (3)) {goto L115672;} else {goto L145433;}
L115672: if (n. check (9)) {goto L121512;} else {goto L136664;}
L136664: if (n. check (7)) {goto L131112;} else {goto L143321;}
L143321: if (n. check (25)) {goto L105737;} else {goto L106616;}
L145433: if (n. check (9)) {goto L105737;} else {goto L114873;}
L114873: if (n. check (7)) {goto L105737;} else {goto L126377;}
L126377: if (n. check (25)) {goto L105737;} else {goto L145577;}
L132920: if (n. check (6)) {goto L118488;} else {goto L115001;}
L118488: if (n. check (2)) {goto L133976;} else {goto L118537;}
L133976: if (n. check (1)) {goto L107704;} else {goto L115161;}
L107704: if (n. check (9)) {goto L114968;} else {statInv=!statInv;goto L123337;}
L115161: if (n. check (19)) {goto L108489;} else {goto L131416;}
L108489: if (n. check (9)) {goto L119785;} else {goto L123209;}
L123209: if (n. check (7)) {goto L107273;} else {goto L134568;}
L131416: if (n. check (9)) {goto L133768;} else {goto L130024;}
L130024: if (n. check (7)) {goto L134568;} else {goto L125721;}
L125721: if (n. check (25)) {goto L105737;} else {goto L134568;}
L118537: if (n. check (20)) {goto L125833;} else {goto L117368;}
L125833: if (n. check (1)) {goto L118521;} else {goto L106745;}
L118521: if (n. check (3)) {goto L143305;} else {goto L130712;}
L143305: if (n. check (9)) {goto L113913;} else {goto L123017;}
L106745: if (n. check (19)) {goto L109593;} else {goto L135257;}
L109593: if (n. check (3)) {goto L132089;} else {goto L137625;}
L132089: if (n. check (9)) {goto L145833;} else {goto L129113;}
L129113: if (n. check (7)) {goto L126729;} else {goto L145177;}
L135257: if (n. check (3)) {goto L145561;} else {goto L127976;}
L145561: if (n. check (9)) {goto L136249;} else {goto L114361;}
L114361: if (n. check (7)) {goto L145177;} else {goto L119113;}
L119113: if (n. check (25)) {goto L105737;} else {goto L145177;}
L127976: if (n. check (9)) {goto L116184;} else {goto L127112;}
L127112: if (n. check (7)) {goto L108376;} else {goto L108313;}
L108313: if (n. check (25)) {goto L105737;} else {goto L108376;}
L117368: if (n. check (1)) {goto L119528;} else {goto L107289;}
L119528: if (n. check (3)) {goto L118232;} else {goto L106841;}
L118232: if (n. check (9)) {goto L114008;} else {goto L115496;}
L106841: if (n. check (21)) {goto L105737;} else {goto L130712;}
L107289: if (n. check (19)) {goto L133817;} else {goto L118200;}
L133817: if (n. check (3)) {goto L136089;} else {goto L130617;}
L136089: if (n. check (9)) {goto L137465;} else {goto L134121;}
L134121: if (n. check (7)) {goto L133785;} else {goto L137272;}
L130617: if (n. check (21)) {goto L105737;} else {goto L137625;}
L118200: if (n. check (3)) {goto L145880;} else {goto L114201;}
L145880: if (n. check (9)) {goto L121512;} else {goto L108856;}
L108856: if (n. check (7)) {goto L134280;} else {goto L127593;}
L127593: if (n. check (25)) {goto L105737;} else {goto L134280;}
L114201: if (n. check (21)) {goto L105737;} else {goto L145208;}
L115001: if (n. check (24)) {goto L121929;} else {goto L107640;}
L121929: if (n. check (2)) {goto L105737;} else {goto L123593;}
L123593: if (n. check (20)) {goto L105737;} else {goto L144281;}
L144281: if (n. check (1)) {goto L105737;} else {goto L122473;}
L122473: if (n. check (19)) {goto L105737;} else {goto L143545;}
L143545: if (n. check (3)) {goto L105737;} else {goto L126793;}
L126793: if (n. check (21)) {goto L105737;} else {goto L145433;}
L107640: if (n. check (2)) {goto L137176;} else {goto L132857;}
L132857: if (n. check (20)) {goto L125161;} else {goto L143912;}
L143912: if (n. check (1)) {goto L125560;} else {goto L134601;}
L134601: if (n. check (19)) {goto L106681;} else {goto L125608;}
L125608: if (n. check (3)) {goto L115672;} else {goto L135609;}
L135609: if (n. check (21)) {goto L145433;} else {goto L109016;}
L109016: if (n. check (9)) {goto L121512;} else {goto L143000;}
L143000: if (n. check (7)) {goto L145656;} else {goto L132889;}
L132889: if (n. check (25)) {goto L145577;} else {goto L143928;}
L143928: if (n. check (15)) {goto L108632;} else {goto L135672;}
L135672: if (n. check (14)) {goto L121448;} else {goto L118008;}
L118008: if (n. check (8)) {goto L130584;} else {goto L128344;}
L128344: if (n. check (22)) {goto L136440;} else {goto L115448;}
L115448: if (n. check (4)) {goto L136056;} else {goto L122056;}
L122056: if (n. check (12)) {goto L129368;} else {goto L129688;}
L129688: if (n. check (11)) {goto L136472;} else {goto L136376;}
L136376: if (n. check (16)) {goto L144408;} else {statInv=!statInv;goto L130457;}
L105736: return !statInv;
L105737: return statInv;
} /* acyclic3d_Malandain */

/// Verifies whether the neighborhood of a 3-dimensional cube is acyclic.
template <class NeighborCheck>
bool acyclic3d (NeighborCheck &n)
{
	if (n. check (0)) goto K1043; else goto K978;
K14:	return !n. check (6);
K15:	return n. check (6);
K36:	return !n. check (17);
K37:	return n. check (17);
K38:	return !n. check (18);
K39:	return n. check (18);
K48:	return !n. check (23);
K49:	return n. check (23);
K50:	return !n. check (24);
K52:	return !n. check (25);
K53:	return n. check (25);
K54:	if (n. check (17)) goto K2585; else goto K154;
K56:	if (n. check (20)) return false; else goto K2302;
K57:	if (n. check (7)) goto K1863; else goto K939;
K59:	if (n. check (20)) goto K2302; else goto K2088;
K63:	if (n. check (17)) goto K15; else goto K2377;
K64:	if (n. check (4)) goto K1575; else goto K1541;
K65:	if (n. check (1)) goto K504; else goto K1046;
K67:	if (n. check (4)) goto K1402; else goto K793;
K68:	if (n. check (16)) return false; else goto K174;
K69:	if (n. check (18)) goto K49; else goto K1636;
K76:	if (n. check (19)) return false; else goto K1900;
K78:	if (n. check (19)) goto K690; else goto K1873;
K79:	if (n. check (20)) goto K57; else goto K1797;
K80:	if (n. check (20)) goto K2317; else goto K237;
K82:	if (n. check (19)) goto K1559; else goto K1414;
K85:	if (n. check (20)) goto K2317; else goto K464;
K90:	if (n. check (4)) goto K862; else goto K1928;
K92:	if (n. check (4)) goto K59; else goto K2119;
K93:	if (n. check (7)) goto K1863; else return false;
K97:	if (n. check (5)) goto K361; else goto K244;
K98:	if (n. check (1)) return false; else goto K1299;
K101:	if (n. check (13)) return false; else goto K184;
K102:	if (n. check (1)) goto K2536; else goto K2453;
K105:	if (n. check (20)) goto K248; else goto K712;
K106:	if (n. check (1)) goto K1410; else goto K139;
K112:	if (n. check (5)) goto K359; else goto K121;
K115:	if (n. check (4)) goto K307; else goto K101;
K117:	if (n. check (14)) goto K2247; else goto K580;
K118:	if (n. check (4)) goto K826; else goto K2473;
K119:	if (n. check (13)) return false; else goto K2174;
K121:	if (n. check (8)) goto K106; else goto K226;
K123:	if (n. check (4)) goto K1814; else goto K1442;
K124:	if (n. check (10)) goto K1086; else goto K1683;
K125:	if (n. check (14)) goto K355; else goto K1816;
K127:	if (n. check (1)) return false; else goto K1000;
K131:	if (n. check (17)) return false; else goto K200;
K134:	if (n. check (19)) return false; else goto K1862;
K137:	if (n. check (11)) goto K177; else goto K167;
K139:	if (n. check (4)) goto K891; else goto K1234;
K143:	if (n. check (13)) return false; else goto K2460;
K154:	if (n. check (15)) return false; else goto K342;
K155:	if (n. check (14)) goto K1410; else goto K1549;
K156:	if (n. check (1)) return false; else goto K2181;
K158:	if (n. check (4)) goto K1610; else goto K1250;
K163:	if (n. check (16)) return false; else goto K2112;
K164:	if (n. check (17)) goto K2585; else return false;
K165:	if (n. check (10)) return false; else goto K1607;
K166:	if (n. check (20)) goto K2422; else goto K2417;
K167:	if (n. check (1)) goto K504; else goto K977;
K172:	if (n. check (7)) goto K988; else goto K559;
K174:	if (n. check (19)) goto K1950; else goto K465;
K175:	if (n. check (19)) goto K1948; else goto K164;
K177:	if (n. check (1)) return false; else goto K2279;
K181:	if (n. check (14)) goto K533; else goto K118;
K182:	if (n. check (19)) return false; else goto K2368;
K184:	if (n. check (20)) goto K1607; else goto K2423;
K185:	if (n. check (20)) return false; else goto K1614;
K192:	if (n. check (20)) goto K2410; else goto K2063;
K195:	if (n. check (7)) goto K1153; else goto K268;
K198:	if (n. check (23)) return true; else goto K52;
K199:	if (n. check (1)) goto K117; else goto K1399;
K200:	if (n. check (15)) goto K2377; else goto K1992;
K202:	if (n. check (7)) goto K273; else goto K1332;
K203:	if (n. check (19)) return true; else goto K37;
K204:	if (n. check (16)) return false; else goto K1794;
K205:	if (n. check (13)) return false; else goto K1442;
K215:	if (n. check (19)) goto K545; else goto K37;
K219:	if (n. check (7)) goto K182; else goto K2264;
K222:	if (n. check (1)) goto K728; else goto K1954;
K224:	if (n. check (7)) goto K1226; else goto K261;
K225:	if (n. check (7)) goto K1922; else goto K2403;
K226:	if (n. check (9)) goto K452; else goto K1825;
K229:	if (n. check (15)) goto K1571; else goto K453;
K230:	if (n. check (19)) goto K1949; else goto K1263;
K232:	if (n. check (7)) goto K1153; else return false;
K235:	if (n. check (19)) goto K2063; else goto K1760;
K236:	if (n. check (6)) goto K1940; else goto K1506;
K237:	if (n. check (7)) goto K2112; else goto K163;
K238:	if (n. check (20)) return false; else goto K2058;
K241:	if (n. check (1)) goto K624; else goto K2371;
K242:	if (n. check (1)) goto K1832; else goto K687;
K244:	if (n. check (8)) goto K258; else goto K2277;
K246:	if (n. check (23)) return true; else goto K803;
K248:	if (n. check (7)) goto K987; else goto K1804;
K249:	if (n. check (14)) return false; else goto K1135;
K251:	if (n. check (4)) goto K872; else goto K2576;
K254:	if (n. check (7)) goto K1924; else return false;
K255:	if (n. check (17)) goto K14; else goto K2377;
K257:	if (n. check (14)) return false; else goto K832;
K258:	if (n. check (1)) goto K832; else goto K863;
K260:	if (n. check (19)) goto K839; else goto K722;
K261:	if (n. check (19)) goto K2058; else goto K873;
K267:	if (n. check (16)) return false; else goto K2313;
K268:	if (n. check (16)) return false; else goto K1253;
K273:	if (n. check (19)) return false; else goto K1769;
K278:	if (n. check (19)) goto K686; else goto K37;
K281:	if (n. check (22)) goto K2381; else goto K1559;
K285:	if (n. check (11)) goto K1257; else goto K199;
K293:	if (n. check (7)) goto K1565; else goto K2296;
K307:	if (n. check (20)) goto K1607; else goto K203;
K342:	if (n. check (6)) return false; else goto K2000;
K350:	if (n. check (6)) goto K1805; else goto K2602;
K354:	if (n. check (6)) goto K867; else goto K2002;
K355:	if (n. check (4)) goto K1762; else goto K1519;
K356:	if (n. check (7)) goto K1297; else goto K1794;
K359:	if (n. check (8)) goto K1256; else goto K2365;
K360:	if (n. check (19)) return false; else goto K1761;
K361:	if (n. check (8)) goto K1773; else goto K2344;
K368:	if (n. check (19)) return false; else goto K36;
K399:	if (n. check (17)) goto K15; else goto K1571;
K401:	if (n. check (14)) goto K427; else goto K875;
K411:	if (n. check (13)) return false; else goto K762;
K427:	if (n. check (4)) goto K928; else goto K2134;
K428:	if (n. check (1)) goto K2247; else goto K1135;
K433:	if (n. check (17)) return false; else goto K1571;
K448:	if (n. check (1)) goto K921; else goto K856;
K451:	if (n. check (7)) goto K578; else goto K1939;
K452:	if (n. check (11)) goto K222; else goto K2113;
K453:	if (n. check (6)) goto K2544; else goto K2002;
K454:	if (n. check (14)) goto K1135; else goto K67;
K464:	if (n. check (7)) goto K1799; else goto K2349;
K465:	if (n. check (17)) goto K14; else return false;
K486:	if (n. check (21)) goto K1242; else goto K198;
K492:	if (n. check (17)) goto K15; else goto K2421;
K494:	if (n. check (8)) goto K428; else goto K1147;
K497:	if (n. check (7)) goto K1924; else goto K2306;
K504:	if (n. check (20)) return false; else goto K1559;
K507:	if (n. check (7)) goto K1470; else goto K2487;
K521:	if (n. check (14)) goto K1648; else goto K1171;
K522:	if (n. check (14)) return false; else goto K1608;
K523:	if (n. check (14)) goto K248; else goto K2317;
K524:	if (n. check (12)) goto K98; else goto K2215;
K533:	if (n. check (4)) goto K1542; else return false;
K543:	if (n. check (14)) goto K2044; else goto K1405;
K545:	if (n. check (17)) return true; else goto K39;
K559:	if (n. check (22)) goto K174; else goto K1864;
K578:	if (n. check (19)) goto K2410; else goto K2063;
K580:	if (n. check (20)) goto K832; else goto K1950;
K590:	if (n. check (6)) goto K2497; else goto K2602;
K591:	if (n. check (14)) goto K863; else goto K225;
K592:	if (n. check (15)) goto K2467; else goto K2602;
K624:	if (n. check (20)) goto K37; else return true;
K649:	if (n. check (5)) goto K1520; else goto K2586;
K685:	if (n. check (10)) goto K454; else goto K2267;
K686:	if (n. check (17)) return true; else goto K2363;
K687:	if (n. check (10)) goto K2028; else goto K181;
K690:	if (n. check (17)) return false; else goto K229;
K691:	if (n. check (6)) goto K1242; else return false;
K698:	if (n. check (1)) goto K1457; else goto K685;
K703:	if (n. check (20)) goto K2302; else goto K281;
K712:	if (n. check (7)) goto K1110; else goto K2199;
K718:	if (n. check (19)) goto K2058; else return false;
K722:	if (n. check (17)) goto K2585; else goto K1593;
K724:	if (n. check (17)) goto K14; else goto K236;
K725:	if (n. check (18)) return false; else goto K1233;
K728:	if (n. check (14)) return false; else goto K1410;
K731:	if (n. check (13)) return false; else goto K2119;
K741:	if (n. check (14)) goto K1608; else goto K451;
K751:	if (n. check (7)) goto K1264; else goto K1179;
K752:	if (n. check (20)) goto K921; else goto K686;
K761:	if (n. check (7)) goto K1813; else goto K1253;
K762:	if (n. check (20)) goto K2120; else goto K2350;
K773:	if (n. check (19)) return false; else goto K433;
K785:	if (n. check (22)) goto K2533; else goto K690;
K792:	if (n. check (8)) goto K1534; else goto K2314;
K793:	if (n. check (20)) goto K225; else goto K942;
K803:	if (n. check (24)) goto K52; else goto K53;
K826:	if (n. check (20)) goto K2317; else goto K908;
K831:	if (n. check (16)) goto K2092; else goto K1623;
K832:	if (n. check (17)) goto K14; else goto K354;
K839:	if (n. check (17)) goto K2585; else goto K592;
K843:	if (n. check (22)) goto K2112; else goto K260;
K856:	if (n. check (10)) goto K2302; else goto K2120;
K862:	if (n. check (20)) goto K225; else goto K2386;
K863:	if (n. check (7)) goto K134; else goto K1527;
K867:	if (n. check (18)) return false; else goto K48;
K871:	if (n. check (10)) goto K2028; else goto K2310;
K872:	if (n. check (20)) goto K2302; else goto K2381;
K873:	if (n. check (17)) return false; else goto K198;
K875:	if (n. check (4)) goto K1957; else goto K119;
K891:	if (n. check (20)) goto K863; else goto K2367;
K894:	if (n. check (17)) goto K15; else goto K691;
K907:	if (n. check (14)) return false; else goto K2247;
K908:	if (n. check (7)) goto K175; else goto K1048;
K909:	if (n. check (16)) return false; else goto K920;
K920:	if (n. check (19)) goto K690; else goto K2175;
K921:	if (n. check (17)) return true; else goto K38;
K924:	if (n. check (10)) goto K1245; else goto K1441;
K928:	if (n. check (20)) goto K863; else goto K1972;
K937:	if (n. check (4)) goto K1204; else goto K2119;
K939:	if (n. check (16)) return false; else goto K1804;
K942:	if (n. check (7)) goto K785; else goto K843;
K966:	if (n. check (20)) goto K921; else goto K545;
K977:	if (n. check (10)) goto K2001; else goto K251;
K978:	if (n. check (2)) goto K97; else goto K1563;
K983:	if (n. check (4)) goto K1903; else goto K184;
K987:	if (n. check (19)) goto K832; else goto K1042;
K988:	if (n. check (22)) goto K2416; else goto K1862;
K1000:	if (n. check (10)) return false; else goto K983;
K1001:	if (n. check (6)) goto K1735; else goto K1090;
K1002:	if (n. check (14)) goto K1846; else goto K123;
K1042:	if (n. check (17)) goto K14; else goto K350;
K1043:	if (n. check (2)) goto K649; else goto K1904;
K1044:	if (n. check (20)) goto K2317; else goto K2057;
K1046:	if (n. check (10)) goto K2001; else goto K937;
K1048:	if (n. check (16)) return false; else goto K1179;
K1067:	if (n. check (17)) return false; else goto K1001;
K1075:	if (n. check (1)) goto K2437; else goto K2123;
K1086:	if (n. check (14)) goto K1923; else goto K90;
K1087:	if (n. check (20)) goto K1608; else goto K202;
K1090:	if (n. check (21)) goto K2602; else goto K69;
K1095:	if (n. check (19)) goto K2058; else goto K1769;
K1108:	if (n. check (1)) goto K2198; else goto K2570;
K1110:	if (n. check (19)) goto K1042; else goto K465;
K1112:	if (n. check (20)) goto K1608; else goto K761;
K1134:	if (n. check (22)) goto K175; else goto K1948;
K1135:	if (n. check (4)) goto K185; else goto K1977;
K1136:	if (n. check (22)) goto K215; else goto K545;
K1147:	if (n. check (9)) goto K285; else goto K2256;
K1149:	if (n. check (19)) goto K2144; else goto K839;
K1153:	if (n. check (22)) goto K1332; else goto K2063;
K1171:	if (n. check (4)) goto K79; else goto K1289;
K1179:	if (n. check (19)) goto K1948; else goto K54;
K1180:	if (n. check (20)) goto K2144; else goto K1948;
K1181:	if (n. check (6)) goto K1242; else goto K1506;
K1196:	if (n. check (7)) return false; else goto K2495;
K1200:	if (n. check (7)) goto K1149; else return false;
K1204:	if (n. check (20)) return false; else goto K82;
K1210:	if (n. check (19)) goto K1862; else goto K2368;
K1211:	if (n. check (7)) goto K78; else goto K909;
K1217:	if (n. check (14)) goto K1135; else goto K1633;
K1221:	if (n. check (10)) goto K591; else goto K523;
K1226:	if (n. check (19)) return false; else goto K2058;
K1233:	if (n. check (23)) return false; else goto K2352;
K1234:	if (n. check (20)) goto K248; else goto K507;
K1238:	if (n. check (7)) goto K360; else goto K1794;
K1242:	if (n. check (18)) goto K198; else return false;
K1245:	if (n. check (4)) goto K1460; else goto K762;
K1250:	if (n. check (20)) goto K1200; else goto K1300;
K1253:	if (n. check (22)) goto K1332; else goto K235;
K1256:	if (n. check (1)) goto K752; else goto K1245;
K1257:	if (n. check (1)) goto K907; else goto K1471;
K1263:	if (n. check (17)) goto K14; else goto K2421;
K1264:	if (n. check (19)) return false; else goto K131;
K1270:	if (n. check (14)) return false; else goto K863;
K1285:	if (n. check (20)) return false; else goto K690;
K1288:	if (n. check (7)) goto K2250; else goto K174;
K1289:	if (n. check (13)) return false; else goto K2490;
K1297:	if (n. check (19)) goto K1949; else goto K465;
K1299:	if (n. check (10)) return false; else goto K1302;
K1300:	if (n. check (7)) goto K1134; else goto K2092;
K1302:	if (n. check (14)) return false; else goto K2341;
K1307:	if (n. check (4)) goto K105; else goto K143;
K1327:	if (n. check (11)) goto K1910; else goto K1915;
K1328:	if (n. check (20)) goto K2120; else goto K215;
K1332:	if (n. check (19)) goto K2063; else goto K37;
K1393:	if (n. check (1)) goto K543; else goto K124;
K1395:	if (n. check (1)) goto K752; else goto K2486;
K1399:	if (n. check (10)) goto K1867; else goto K401;
K1402:	if (n. check (20)) return false; else goto K1598;
K1405:	if (n. check (20)) goto K2144; else goto K839;
K1409:	if (n. check (17)) return false; else goto K590;
K1410:	if (n. check (20)) goto K832; else goto K1949;
K1413:	if (n. check (1)) goto K966; else goto K1763;
K1414:	if (n. check (17)) return false; else goto K39;
K1423:	if (n. check (14)) goto K139; else goto K2429;
K1438:	if (n. check (17)) goto K15; else return false;
K1441:	if (n. check (4)) goto K1498; else return false;
K1442:	if (n. check (20)) goto K451; else goto K195;
K1449:	if (n. check (20)) return false; else goto K1211;
K1457:	if (n. check (14)) goto K2247; else goto K1285;
K1460:	if (n. check (20)) goto K2302; else goto K76;
K1461:	if (n. check (17)) return false; else goto K236;
K1470:	if (n. check (22)) goto K1297; else goto K1949;
K1471:	if (n. check (10)) goto K249; else goto K1217;
K1475:	if (n. check (19)) goto K2410; else goto K1760;
K1498:	if (n. check (20)) goto K2120; else goto K278;
K1506:	if (n. check (18)) goto K198; else goto K1233;
K1507:	if (n. check (4)) goto K80; else goto K1947;
K1519:	if (n. check (13)) return false; else goto K1112;
K1520:	if (n. check (8)) goto K1803; else goto K1693;
K1521:	if (n. check (4)) goto K1449; else goto K85;
K1527:	if (n. check (19)) goto K832; else goto K724;
K1534:	if (n. check (1)) goto K504; else goto K2001;
K1538:	if (n. check (20)) goto K451; else goto K2062;
K1541:	if (n. check (20)) goto K1970; else goto K1801;
K1542:	if (n. check (20)) goto K248; else goto K356;
K1543:	if (n. check (21)) goto K1506; else goto K2581;
K1549:	if (n. check (20)) goto K399; else goto K63;
K1558:	if (n. check (1)) goto K257; else goto K2173;
K1559:	if (n. check (17)) return false; else goto K38;
K1562:	if (n. check (13)) return false; else goto K1234;
K1563:	if (n. check (3)) goto K2598; else goto K112;
K1565:	if (n. check (22)) goto K174; else goto K1950;
K1571:	if (n. check (6)) goto K2544; else return false;
K1575:	if (n. check (20)) goto K863; else goto K1288;
K1587:	if (n. check (4)) goto K1328; else goto K731;
K1593:	if (n. check (15)) goto K691; else goto K1181;
K1598:	if (n. check (7)) goto K1922; else goto K920;
K1599:	if (n. check (1)) goto K624; else goto K983;
K1607:	if (n. check (19)) goto K37; else return true;
K1608:	if (n. check (7)) goto K1226; else goto K1475;
K1610:	if (n. check (20)) goto K225; else goto K751;
K1611:	if (n. check (20)) return false; else goto K224;
K1614:	if (n. check (7)) goto K134; else goto K2313;
K1623:	if (n. check (22)) goto K1179; else goto K1700;
K1633:	if (n. check (4)) goto K2209; else goto K2174;
K1636:	if (n. check (23)) return true; else goto K50;
K1648:	if (n. check (4)) goto K1542; else goto K1562;
K1664:	if (n. check (20)) goto K93; else goto K254;
K1683:	if (n. check (14)) goto K1307; else goto K1507;
K1687:	if (n. check (17)) goto K15; else goto K2467;
K1692:	if (n. check (7)) goto K1860; else goto K2411;
K1693:	if (n. check (1)) goto K37; else goto K165;
K1700:	if (n. check (19)) goto K1948; else goto K2451;
K1705:	if (n. check (8)) goto K2045; else goto K1835;
K1728:	if (n. check (10)) return false; else goto K2302;
K1735:	if (n. check (21)) goto K1805; else goto K48;
K1760:	if (n. check (17)) return true; else goto K198;
K1761:	if (n. check (17)) return false; else goto K2377;
K1762:	if (n. check (20)) goto K1608; else goto K1925;
K1763:	if (n. check (10)) goto K92; else goto K1587;
K1764:	if (n. check (4)) goto K166; else goto K2490;
K1769:	if (n. check (17)) return false; else goto K49;
K1772:	if (n. check (7)) goto K578; else return false;
K1773:	if (n. check (1)) goto K921; else goto K2302;
K1789:	if (n. check (1)) goto K2410; else goto K1608;
K1794:	if (n. check (19)) goto K63; else goto K1438;
K1797:	if (n. check (7)) goto K1794; else goto K204;
K1798:	if (n. check (19)) goto K63; else goto K492;
K1799:	if (n. check (22)) goto K2112; else goto K839;
K1801:	if (n. check (7)) goto K1565; else return false;
K1803:	if (n. check (1)) goto K36; else goto K1607;
K1804:	if (n. check (19)) goto K399; else goto K894;
K1805:	if (n. check (18)) goto K48; else return false;
K1813:	if (n. check (22)) goto K718; else goto K2058;
K1814:	if (n. check (20)) return false; else goto K1843;
K1816:	if (n. check (4)) goto K1538; else goto K205;
K1822:	if (n. check (7)) goto K1799; else return false;
K1824:	if (n. check (19)) return false; else goto K1873;
K1825:	if (n. check (11)) goto K242; else goto K524;
K1828:	if (n. check (14)) goto K863; else goto K2422;
K1832:	if (n. check (14)) goto K1410; else goto K1180;
K1835:	if (n. check (11)) goto K1075; else goto K1108;
K1843:	if (n. check (7)) goto K1095; else goto K2091;
K1846:	if (n. check (4)) goto K1611; else goto K1112;
K1855:	if (n. check (14)) goto K139; else goto K1764;
K1859:	if (n. check (7)) goto K2190; else goto K267;
K1860:	if (n. check (22)) goto K1110; else goto K1042;
K1861:	if (n. check (20)) goto K1772; else goto K232;
K1862:	if (n. check (17)) return false; else goto K354;
K1863:	if (n. check (19)) goto K399; else goto K1687;
K1864:	if (n. check (19)) goto K1950; else goto K724;
K1867:	if (n. check (14)) goto K1135; else goto K64;
K1873:	if (n. check (17)) return false; else goto K592;
K1900:	if (n. check (17)) return false; else goto K2363;
K1903:	if (n. check (20)) return false; else goto K368;
K1904:	if (n. check (5)) goto K2108; else goto K1705;
K1905:	if (n. check (13)) goto K2473; else goto K1044;
K1910:	if (n. check (1)) goto K752; else goto K924;
K1915:	if (n. check (12)) return false; else goto K1395;
K1922:	if (n. check (19)) return false; else goto K690;
K1923:	if (n. check (4)) goto K2200; else goto K2460;
K1924:	if (n. check (22)) goto K1794; else goto K63;
K1925:	if (n. check (7)) goto K718; else goto K1332;
K1926:	if (n. check (20)) goto K1998; else goto K1238;
K1928:	if (n. check (20)) goto K1200; else goto K1822;
K1934:	if (n. check (7)) goto K174; else goto K68;
K1939:	if (n. check (16)) return false; else goto K1475;
K1940:	if (n. check (18)) return false; else goto K198;
K1947:	if (n. check (13)) return false; else goto K85;
K1948:	if (n. check (17)) goto K2585; else goto K200;
K1949:	if (n. check (17)) goto K14; else goto K1001;
K1950:	if (n. check (17)) goto K14; else goto K590;
K1954:	if (n. check (10)) goto K2343; else goto K1855;
K1957:	if (n. check (20)) goto K2422; else goto K1934;
K1970:	if (n. check (7)) goto K2292; else return false;
K1972:	if (n. check (7)) goto K2416; else goto K174;
K1977:	if (n. check (20)) goto K863; else goto K172;
K1985:	if (n. check (19)) goto K433; else goto K2003;
K1992:	if (n. check (6)) goto K2321; else goto K1090;
K1996:	if (n. check (16)) return false; else goto K1332;
K1998:	if (n. check (7)) goto K773; else goto K1804;
K2000:	if (n. check (21)) return false; else goto K725;
K2001:	if (n. check (4)) goto K56; else goto K703;
K2002:	if (n. check (18)) goto K48; else goto K1636;
K2003:	if (n. check (17)) return false; else goto K691;
K2019:	if (n. check (1)) return false; else goto K1728;
K2028:	if (n. check (14)) goto K139; else goto K158;
K2041:	if (n. check (11)) goto K156; else goto K1395;
K2044:	if (n. check (20)) goto K832; else goto K1042;
K2045:	if (n. check (1)) goto K238; else goto K1846;
K2057:	if (n. check (7)) goto K1134; else goto K831;
K2058:	if (n. check (17)) return false; else goto K48;
K2062:	if (n. check (7)) goto K1332; else goto K1996;
K2063:	if (n. check (17)) return true; else goto K49;
K2067:	if (n. check (16)) return false; else goto K230;
K2082:	if (n. check (20)) return false; else goto K2177;
K2084:	if (n. check (13)) return false; else goto K2473;
K2087:	if (n. check (14)) goto K832; else goto K2144;
K2088:	if (n. check (19)) return false; else goto K1414;
K2091:	if (n. check (16)) return false; else goto K261;
K2092:	if (n. check (22)) return false; else goto K2099;
K2099:	if (n. check (19)) return false; else goto K2376;
K2108:	if (n. check (8)) goto K1599; else goto K2434;
K2112:	if (n. check (19)) goto K839; else goto K164;
K2113:	if (n. check (1)) goto K155; else goto K2415;
K2117:	if (n. check (14)) return false; else goto K1846;
K2119:	if (n. check (20)) goto K2120; else goto K1136;
K2120:	if (n. check (19)) goto K921; else goto K545;
K2122:	if (n. check (4)) goto K1498; else goto K411;
K2123:	if (n. check (10)) goto K2117; else goto K1002;
K2134:	if (n. check (13)) return false; else goto K1977;
K2144:	if (n. check (17)) goto K2585; else goto K229;
K2147:	if (n. check (1)) goto K2087; else goto K1221;
K2152:	if (n. check (19)) goto K1687; else goto K894;
K2173:	if (n. check (10)) goto K1270; else goto K1828;
K2174:	if (n. check (20)) goto K2422; else goto K293;
K2175:	if (n. check (17)) return false; else goto K1593;
K2177:	if (n. check (7)) goto K1210; else goto K1985;
K2181:	if (n. check (10)) return false; else goto K1245;
K2190:	if (n. check (19)) goto K1862; else goto K1409;
K2198:	if (n. check (14)) goto K238; else goto K192;
K2199:	if (n. check (19)) goto K1687; else goto K1438;
K2200:	if (n. check (20)) goto K863; else goto K219;
K2209:	if (n. check (20)) return false; else goto K1859;
K2214:	if (n. check (4)) goto K2082; else goto K2460;
K2215:	if (n. check (1)) goto K1832; else goto K871;
K2232:	if (n. check (4)) goto K826; else goto K1905;
K2245:	if (n. check (15)) goto K2421; else goto K2303;
K2247:	if (n. check (20)) return false; else goto K1862;
K2250:	if (n. check (19)) return false; else goto K1409;
K2256:	if (n. check (11)) goto K698; else goto K1393;
K2264:	if (n. check (19)) goto K1042; else goto K2360;
K2267:	if (n. check (14)) goto K2214; else goto K1521;
K2277:	if (n. check (9)) goto K1558; else goto K2147;
K2279:	if (n. check (10)) return false; else goto K2001;
K2292:	if (n. check (19)) goto K832; else goto K1950;
K2293:	if (n. check (4)) goto K1087; else goto K1861;
K2296:	if (n. check (16)) return false; else goto K559;
K2302:	if (n. check (19)) return false; else goto K1559;
K2303:	if (n. check (6)) goto K486; else goto K1543;
K2306:	if (n. check (16)) return false; else goto K2487;
K2310:	if (n. check (14)) goto K1648; else goto K2232;
K2312:	if (n. check (11)) goto K65; else goto K1413;
K2313:	if (n. check (19)) goto K1862; else goto K1461;
K2314:	if (n. check (9)) goto K137; else goto K2312;
K2317:	if (n. check (7)) goto K1149; else goto K2557;
K2321:	if (n. check (21)) goto K2602; else goto K49;
K2341:	if (n. check (4)) return false; else goto K2084;
K2343:	if (n. check (14)) return false; else goto K139;
K2344:	if (n. check (9)) goto K2019; else goto K448;
K2349:	if (n. check (16)) return false; else goto K843;
K2350:	if (n. check (22)) goto K278; else goto K686;
K2352:	if (n. check (24)) return false; else goto K52;
K2360:	if (n. check (17)) goto K14; else goto K691;
K2363:	if (n. check (21)) goto K39; else return true;
K2365:	if (n. check (9)) goto K2041; else goto K1327;
K2367:	if (n. check (7)) goto K2515; else goto K230;
K2368:	if (n. check (17)) return false; else goto K350;
K2371:	if (n. check (10)) goto K983; else goto K115;
K2376:	if (n. check (17)) return false; else goto K154;
K2377:	if (n. check (6)) goto K2321; else return false;
K2381:	if (n. check (19)) goto K1559; else return false;
K2386:	if (n. check (7)) goto K1824; else goto K2112;
K2387:	if (n. check (19)) goto K1949; else goto K255;
K2403:	if (n. check (19)) goto K2144; else goto K722;
K2410:	if (n. check (17)) return true; else goto K48;
K2411:	if (n. check (22)) goto K2199; else goto K2152;
K2412:	if (n. check (14)) goto K1846; else goto K2293;
K2415:	if (n. check (10)) goto K1423; else goto K521;
K2416:	if (n. check (19)) goto K1862; else return false;
K2417:	if (n. check (7)) goto K2387; else goto K2067;
K2421:	if (n. check (6)) goto K486; else goto K2000;
K2422:	if (n. check (7)) goto K2292; else goto K2555;
K2423:	if (n. check (22)) goto K203; else return true;
K2429:	if (n. check (4)) goto K1926; else goto K1664;
K2434:	if (n. check (11)) goto K127; else goto K241;
K2437:	if (n. check (14)) return false; else goto K238;
K2451:	if (n. check (17)) goto K2585; else goto K2245;
K2453:	if (n. check (10)) goto K522; else goto K741;
K2460:	if (n. check (20)) goto K248; else goto K1692;
K2467:	if (n. check (6)) goto K2602; else return false;
K2473:	if (n. check (20)) return false; else goto K1196;
K2486:	if (n. check (10)) goto K1245; else goto K2122;
K2487:	if (n. check (22)) goto K1794; else goto K1798;
K2490:	if (n. check (20)) goto K57; else goto K497;
K2495:	if (n. check (16)) return false; else goto K2092;
K2497:	if (n. check (18)) return false; else goto K49;
K2515:	if (n. check (19)) return false; else goto K1067;
K2533:	if (n. check (19)) goto K690; else return false;
K2536:	if (n. check (14)) return false; else goto K2410;
K2544:	if (n. check (18)) goto K48; else goto K49;
K2555:	if (n. check (16)) return false; else goto K1527;
K2557:	if (n. check (16)) return false; else goto K2403;
K2570:	if (n. check (10)) goto K2412; else goto K125;
K2576:	if (n. check (13)) return false; else goto K703;
K2581:	if (n. check (18)) goto K198; else goto K246;
K2585:	if (n. check (15)) goto K15; else return true;
K2586:	if (n. check (8)) goto K1789; else goto K102;
K2598:	if (n. check (5)) goto K792; else goto K494;
K2602:	if (n. check (18)) goto K49; else return false;
} /* acyclic3d */


// --------------------------------------------------
// ------------- neighborhoods for BDDs -------------
// --------------------------------------------------

/// The neighborhood of a cube in a set of cubes.
template <class cubetype, class settype>
class Neighbors
{
public:
	/// The default constructor.
	Neighbors (const cubetype &middle, const settype &cset,
		BitField &bfield): q (middle), s (cset), b (bfield) {};

	/// The procedure for checking whether the given neighbor exists.
	/// The number of the neighbor is consistent with the "bit2neighbor"
	/// and "neighbor2bit" procedures.
	bool check (int n) const
	{
		cubetype neighbor = bit2neighbor (q, n);
		if (neighbor == q)
			return false;
		bool result = s. check (neighbor);
		if (result)
			b. set (n);
		return result;
	}

private:
	/// The cube whose neighbors are verified.
	const cubetype &q;

	/// The set of cubes in which the neighbors of the cube are sought.
	const settype &s;

	/// The bitfield to record each neighbor in.
	BitField &b;

}; /* class Neighbors */


// --------------------------------------------------
// ------- acyclicity verification with BDDs --------
// --------------------------------------------------

/// The maximal dimension for which binary decision diagrams are programmed.
const int MaxBddDimPossible = 3;

/// The maximal dimension for which binary decision diagrams are used.
/// This can be decreased by a program if no binary decision diagrams
/// should be used. However, the value of MaxBddDim cannot exceed
/// the value of MaxBddDimPossible.
extern int MaxBddDim;

/// The variable which controls which binary decision diagrams
/// should be used in dimension 3, either programmed by P. Pilarczyk
/// (if set to false) or received from G. Malandain (if set to true).
extern bool UseMalandainCode;

// --------------------------------------------------

/// Uses binary decision diagrams to verify whether the neighborhood
/// of the given cube in the given set is acyclic. Uses the bitfield
/// provided to record each tested neighbor in.
/// Verifies whether the neighborhood of the given cube is acyclic or not
/// using the code generated from binary decision diagrams.
template <class tCube, class tCubeSet>
bool bddacyclic (const tCube &q, int dim, const tCubeSet &s,
	BitField &b)
{
	switch (dim)
	{
	case 1:
	{
		Neighbors<tCube,tCubeSet> n (q, s, b);
		return acyclic1d (n);
	//	break;
	}
	case 2:
	{
		Neighbors<tCube,tCubeSet> n (q, s, b);
		return acyclic2d (n);
	//	break;
	}
	case 3:
	{
		Neighbors<tCube,tCubeSet> n (q, s, b);
		if (UseMalandainCode)
			return acyclic3d_Malandain (n);
		else
			return acyclic3d (n);
	//	break;
	}
	}
	throw "Trying to use a BDD for dimension other than 1-3.";
} /* bddacyclic */


} // namespace homology
} // namespace capd

#endif // _CAPD_HOMOLOGY_CUBACYCL_H_ 

/// @}

