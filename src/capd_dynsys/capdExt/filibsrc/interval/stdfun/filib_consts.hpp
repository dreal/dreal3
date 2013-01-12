/*                                                                           
**  fi_lib++  --- A fast interval library (Version 2.0)                     
**                                                                  
**  Copyright (C) 2001:                                                        
**                                                     
**  Werner Hofschuster, Walter Kraemer                               
**  Wissenschaftliches Rechnen/Softwaretechnologie (WRSWT)  
**  Universitaet Wuppertal, Germany                                           
**  Michael Lerch, German Tischler, Juergen Wolff von Gudenberg       
**  Institut fuer Informatik                                         
**  Universitaet Wuerzburg, Germany                                           
** 
**  This library is free software; you can redistribute it and/or
**  modify it under the terms of the GNU Library General Public
**  License as published by the Free Software Foundation; either
**  version 2 of the License, or (at your option) any later version.
**
**  This library is distributed in the hope that it will be useful,
**  but WITHOUT ANY WARRANTY; without even the implied warranty of
**  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
**  Library General Public License for more details.
**
**  You should have received a copy of the GNU Library General Public
**  License along with this library; if not, write to the Free
**  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307 USA
*/
#if ! defined(FILIB_CONSTS_HPP)
#define FILIB_CONSTS_HPP

namespace filib
{
	template < typename N >
	struct
#if defined(_MSC_VER) && defined(FILIB_BUILD_DLL) && defined(FILIB_DLL)
	__declspec(dllexport)
#elif defined(_MSC_VER) && defined(FILIB_BUILD_DLL) && ! defined(FILIB_DLL)
	__declspec(dllimport)
#endif
	filib_consts
	{
		/* for |x|<=q_atnt approx. x=arctan(x)     */
		/* used in q_atan, q_atn1, j_atan, q_asin, */
		/* j_asin, ...                             */ 
		static N const q_atnt;
		static N const q_atna[7];
		static N const q_atnb[8];
		static N const q_atnc[7];
		static N const q_atnd[6];

		/* worst case relative error bound for q_acos */   
		/* eps(q_acos) = 2.148489042525242E-015;                  */
		/*     q_ccsm  = 1 - eps(q_acos) = 9.999999999999974E-001 */
		static N const q_ccsm;
		/*     q_ccsp  = 1 + eps(q_acos) = 1.000000000000003E+000 */
		static N const q_ccsp;

		/*        q_pi     = pi   ( rounding towards -infinity )                 */
		static N const q_pi;
		/*        q_piha   = pi/2                                                */ 
		static N const q_piha;

		/* worst case relative error bound for q_exp */

		/* eps(q_exp)  = 2.357962555295842e-16;                   */ 
		/*     q_exem  = 1 - eps(q_exp) = 9.999999999999993E-001  */
		static N const q_exem;
		/*     q_exep  = 1 + eps(q_exp) = 1.000000000000001E+000  */
		static N const q_exep;
	
		/* worst case relative error bound for q_expm */
	
		/* eps(q_expm) = 2.592561649228397E-016;                  */
		/*     q_exmm  = 1 - eps(q_expm) = 9.999999999999993E-001 */
		static N const q_exmm;
		/*     q_exmp  = 1 + eps(q_expm) = 1.000000000000001E+000 */
		static N const q_exmp;
	
		/* worst case relative error bound for q_log */ 
   	
		/* eps(q_log)  = 2.9398E-016;                             */
		/*     q_logm  = 1 - eps(q_log)                           */
		static N const q_logm;
		/*     q_logp  = 1 + eps(q_log)                           */
		static N const q_logp;
	
		/* worst case relative error bound for q_lg1p */
   	
		/* eps(q_lg1p) = 2.5082E-016;                             */
		/*     q_lgpm  = 1 - eps(q_lg1p)                          */
		static N const q_lgpm;
		/*     q_lgpp  = 1 + eps(q_lg1p)                          */
		static N const q_lgpp;
	
		/* worst case relative error bound for sqrt */    
   	
		/* eps(sqrt)   = 2.220447e-16;                            */
		/*     q_sqtm  = 1 - eps(sqrt)                            */
		static N const q_sqtm;
		/*     q_sqtp  = 1 + eps(sqrt)                            */
		static N const q_sqtp;
	
		/* worst case relative error bound for q_sinh */
   	
		/* eps(q_sinh) = 7.093289735801012E-016;                  */
		/*     q_snhm  = 1 - eps(q_sinh) = 9.999999999999989E-001 */
		static N const q_snhm;
		/*     q_snhp  = 1 + eps(q_sinh) = 1.000000000000002E+000 */
		static N const q_snhp;
	
		/* worst case relative error bound for q_cosh */
   	
		/* eps(q_cosh) = 4.581660384746620E-016;                  */
		/*     q_cshm  = 1 - eps(q_cosh) = 9.999999999999991E-001 */
		static N const q_cshm;
		/*     q_cshp  = 1 + eps(q_cosh) = 1.000000000000001E+000 */
		static N const q_cshp;
 	
		/* worst case relative error bound for q_coth */
   	
		/* eps(q_coth) = 8.325226430245611E-016;                  */
		/*     q_cthm  = 1 - eps(q_coth) = 9.999999999999988E-001 */
		static N const q_cthm;
		/*     q_cthp  = 1 + eps(q_coth) = 1.000000000000002E+000 */
		static N const q_cthp;
 	
		/* worst case relative error bound for q_tanh */
   	
		/* eps(q_tanh) = 1.054585718561371E-015;                  */
		/*     q_tnhm  = 1 - eps(q_tanh) = 9.999999999999986E-001 */
		static N const q_tnhm;
		/*     q_tnhp  = 1 + eps(q_tnhp) = 1.000000000000002E+000 */
		static N const q_tnhp;
	
		/* worst case relative error bound for q_asnh */         
   	
		/* eps(q_asnh) = 7.2075e-16;                              */
		static N const q_asnm;
		static N const q_asnp;
	
		/* worst case relative error bound for q_acnh */          
   	
		/* eps(q_acnh) = 1.6180e-15;                              */
		static N const q_acsm;
		static N const q_acsp;
	
		/* worst case relative error bound for q_acth */
   	
		/* eps(q_acth) = 1.147880588000001E-015;                  */
		static N const q_actm;
		static N const q_actp;
	
		/* worst case relative error bound for q_atnh */
   	
		/* eps(q_atnh) = 1.264618646263405E-015;                  */
		static N const q_atnm;
		static N const q_atnp;
	
		/* worst case relative error bound for q_asin */
   	
		/* eps(q_asin) = 2.148875977690793E-015;                  */
		/*     q_csnm  = 1 - eps(q_asin) = 9.999999999999974E-001 */
		static N const q_csnm;
		/*     q_csnp  = 1 + eps(q_asin) = 1.000000000000003E+000 */
		static N const q_csnp;
	
		/* worst case relative error bound for q_acot */
   	
		/* eps(q_acot) = 1.802884893838539E-015;                  */
		/*     q_cctm  = 1 - eps(q_acot) = 9.999999999999978E-001 */
		static N const q_cctm;
		/*     q_cctp  = 1 + eps(q_acot) = 1.000000000000003E+000 */
		static N const q_cctp;
	
		/* worst case relative error bound for q_atan */  
   	
		/* eps(q_atan) = 1.358774060669230E-015;                  */
		/*     q_ctnm  = 1 - eps(q_atan) = 9.999999999999982E-001 */
		static N const q_ctnm;
		/*     q_ctnp  = 1 + eps(q_atan) = 1.000000000000002E+000 */
		static N const q_ctnp;
	
		/* worst case relative error bound for q_sin */          
   	
		/* eps(q_sin)  = 1.071713978232866e-15;                   */
		static N const q_sinm;
		static N const q_sinp;
	
		/* worst case relative error bound for q_cos */         
   	
		/* eps(q_cos)  = 1.071713978232866e-15;                   */
		static N const q_cosm;
		static N const q_cosp;
	
		/* worst case relative error bound for q_cot */         
   	
		/* eps(q_cot)  = 2.97768e-15;                             */
		static N const q_cotm;
		static N const q_cotp;
	
		/* worst case relative error bound for q_tan */         
   	
		/* eps(q_tan) = 2.97768e-15;                              */
		static N const q_tanm;
		static N const q_tanp;
  	
		/* worst case relative error bound for q_lg2 */
   	
		/* eps(q_lg2)  = 2.7754e-15;                              */
		static N const q_lg2m;
		static N const q_lg2p;
	
		/* worst case relative error bound for q_lg10 */
   	
		/* eps(q_lg10) = 2.7754e-15;                              */
		static N const q_l10m;
		static N const q_l10p;
	
		/* worst case relative error bound for q_exp2 */ 
   	
		/* eps(q_exp2) = 2.350296792932261e-16                    */
		static N const q_e2em;
		static N const q_e2ep;
	
		/* worst case relative error bound for q_ex10 */ 
   	
		/* eps(q_ex10) = 2.418059815583812e-16;                   */
		static N const q_e10m;
		static N const q_e10p;

		/*        q_minr   = smallest positive normalised number                 */
		static N const q_minr;
		/*        q_mine   = ln( q_minr ) = -708.3964185322641062617539          */
		static N const q_mine;
		/*        q_sqra   = 1.3407807929942596e154;                             */
		static N const q_sqra;
		/*        q_ctht   = 5.562684646268013e-309;                             */
		static N const q_ctht;

		/*        q_ln2h   = ln( 2.0 ) / 2 = 0.346573590279972654708616          */
		static N const q_ln2h;
		/*        q_l10i   =  1 / ln( 10 ) = 4.342944819032518E-001              */ 
		static N const q_l10i;
		/*        q_l2i    =  1 / ln( 2 )  = 1.442695040888963E+000              */ 
		static N const q_l2i;
		/*        q_l10    = ln( 10 ) = 2.302585092994046E+000                   */ 
		static N const q_l10;
		/*        q_l2     = ln( 2 ) = 6.931471805599453E-001                    */ 
		static N const q_l2;

		/*        q_p2h    = 2^(100)                                             */
		static N const q_p2h;
		/*        q_p2mh   = 2^(-100)                                            */
		static N const q_p2mh;

		/*        q_pih[7] = pi/2 with 7*22 bits                                 */
		static N const q_pih[7];

		/*        q_pi2p[3]=                                                     */
		static N const q_pi2p[3];

		/*        q_pi2i   = 2/pi    = 6.366197723675814E-001 = 3FE45F306DC9C883 */
		static N const q_pi2i;

		/* q_pi2d = pred(down(2/pi)) = 6.366197723675812E-001 = 3FE45F306DC9C881 */
		static N const q_pi2d;

		/* q_pi2u = pred(up(2/pi))   = 6.366197723675815E-001 = 3FE45F306DC9C884 */
		static N const q_pi2u;

		/* --------------------------------------------------------------------- */
		/* ---- global constants and table values for  q_expm1 and q_exp ------- */
		/* --------------------------------------------------------------------- */

		/*        q_ext1 = 5.551115123125783E-017                                */
		static N const q_ext1;
		/*        q_ext2 = 1.809114141261457E+003                                */
		static N const q_ext2;
		/*        q_ex2a = 7.097827128933840E+002                                */
		static N const q_ex2a;
		/*        q_ex2b =-744.44008                                            */
		static N const q_ex2b;
		/*        q_ex2c = 7.090895657128240E+002                                */
		static N const q_ex2c;
		/*        q_ext3 =-3.742994775023704E+001                                */
		static N const q_ext3;
		/*        q_ext4 =-2.876820724517810E-001                                */
		static N const q_ext4;
		/*        q_ext5 = 2.231435513142098E-001                                */
		static N const q_ext5;
		/*        q_extm = 307.9536855642527627036                               */
		static N const q_extm;
		/*        q_extn =-307.65265556858878150844                               */
		static N const q_extn;

		/*        q_exil = 4.616624130844683E+001                                */
		static N const q_exil;
		/*        q_exl1 = 2.166084939017310E-002                                */
		static N const q_exl1;
		/*        q_exl2 = 2.325192846878874E-012                                */
		static N const q_exl2;
		/*        q_e10i = 32/lg10(2) = 1.063016990363956E+002                   */
		static N const q_e10i;
		/*        q_e1l1 = lg10(2)/32 ( lead )  = 9.407187363649427E-003         */
		static N const q_e1l1;
		/*        q_e1l2 = lg10(2)/32 ( trail ) = 8.499849253130399E-013         */
		static N const q_e1l2;

		static N const q_exa[5];
		/* q_exa[0] = 5.000000000000000E-001                                     */
		/* q_exa[1] = 1.666666666658136E-001                                     */
		/* q_exa[2] = 4.166666666638950E-002                                     */
		/* q_exa[3] = 8.333362425159880E-003                                     */
		/* q_exa[4] = 1.388893979532449E-003                                     */
		
		static N const q_exb[9];
		/* q_exb[0] = 1.666666666666666E-001                                     */
		/* q_exb[1] = 4.166666666666610E-002                                     */
		/* q_exb[2] = 8.333333333354122E-003                                     */
		/* q_exb[3] = 1.388888889017890E-003                                     */
		/* q_exb[4] = 1.984126964158297E-004                                     */
		/* q_exb[5] = 2.480157863209126E-005                                     */
		/* q_exb[6] = 2.755792722352050E-006                                     */
		/* q_exb[7] = 2.758025508816736E-007                                     */
		/* q_exb[8] = 2.448136759253856E-008                                     */

		/* approximation for function q_exp2                                     */
		static N const q_exc[7];
		/* q_exc[0] = 6.931471805599453E-001                                     */
		/* q_exc[1] = 2.402265069591007E-001                                     */
		/* q_exc[2] = 5.550410866482158E-002                                     */
		/* q_exc[3] = 9.618129107559553E-003                                     */
		/* q_exc[4] = 1.333355814632986E-003                                     */
		/* q_exc[5] = 1.540358685612716E-004                                     */
		/* q_exc[6] = 1.525278971414304E-005                                     */
				
		/* approximation for function q_ex10                                     */
		static N const q_exd[7];
		/* q_exd[0] = 1.302585092994046E+000                                     */
		/* q_exd[1] = 2.650949055239199E+000                                     */
		/* q_exd[2] = 2.034678592293476E+000                                     */
		/* q_exd[3] = 1.171255148903874E+000                                     */
		/* q_exd[4] = 5.393829291915935E-001                                     */
		/* q_exd[5] = 2.069966074549993E-001                                     */
		/* q_exd[6] = 6.808961466129955E-002                                     */
		
		static N const q_exld[32];
		/* qExpLead [ 0]:= 1.000000000000000E+000 */
		/* qExpLead [ 1]:= 1.021897148654105E+000 */
		/* qExpLead [ 2]:= 1.044273782427410E+000 */
		/* qExpLead [ 3]:= 1.067140400676820E+000 */
		/* qExpLead [ 4]:= 1.090507732665245E+000 */
		/* qExpLead [ 5]:= 1.114386742595883E+000 */
		/* qExpLead [ 6]:= 1.138788634756679E+000 */
		/* qExpLead [ 7]:= 1.163724858777570E+000 */
		/* qExpLead [ 8]:= 1.189207115002716E+000 */
		/* qExpLead [ 9]:= 1.215247359980467E+000 */
		/* qExpLead [10]:= 1.241857812073476E+000 */
		/* qExpLead [11]:= 1.269050957191723E+000 */
		/* qExpLead [12]:= 1.296839554651001E+000 */
		/* qExpLead [13]:= 1.325236643159741E+000 */
		/* qExpLead [14]:= 1.354255546936884E+000 */
		/* qExpLead [15]:= 1.383909881963831E+000 */
		/* qExpLead [16]:= 1.414213562373092E+000 */
		/* qExpLead [17]:= 1.445180806977035E+000 */
		/* qExpLead [18]:= 1.476826145939498E+000 */
		/* qExpLead [19]:= 1.509164427593419E+000 */
		/* qExpLead [20]:= 1.542210825407935E+000 */
		/* qExpLead [21]:= 1.575980845107878E+000 */
		/* qExpLead [22]:= 1.610490331949251E+000 */
		/* qExpLead [23]:= 1.645755478153959E+000 */
		/* qExpLead [24]:= 1.681792830507419E+000 */
		/* qExpLead [25]:= 1.718619298122476E+000 */
		/* qExpLead [26]:= 1.756252160373293E+000 */
		/* qExpLead [27]:= 1.794709075003098E+000 */
		/* qExpLead [28]:= 1.834008086409341E+000 */
		/* qExpLead [29]:= 1.874167634110293E+000 */
		/* qExpLead [30]:= 1.915206561397142E+000 */
		/* qExpLead [31]:= 1.957144124175400E+000 */

		static N const q_extl[32];
		/* qExpTrail[ 0]:= 0.000000000000000E+000 */
		/* qExpTrail[ 1]:= 1.159741170639136E-014 */
		/* qExpTrail[ 2]:= 3.416187970930849E-015 */
		/* qExpTrail[ 3]:= 3.695759744057116E-015 */
		/* qExpTrail[ 4]:= 1.307016386977872E-014 */
		/* qExpTrail[ 5]:= 9.429976191419770E-015 */
		/* qExpTrail[ 6]:= 1.252362600256201E-014 */
		/* qExpTrail[ 7]:= 7.365764010895274E-015 */
		/* qExpTrail[ 8]:= 4.702756855740314E-015 */
		/* qExpTrail[ 9]:= 2.365364347248530E-015 */
		/* qExpTrail[10]:= 7.596096843369434E-015 */
		/* qExpTrail[11]:= 9.994675153757751E-015 */
		/* qExpTrail[12]:= 8.685122094871109E-015 */
		/* qExpTrail[13]:= 4.155018977496740E-016 */
		/* qExpTrail[14]:= 9.180838285724313E-015 */
		/* qExpTrail[15]:= 1.042517908037209E-015 */
		/* qExpTrail[16]:= 2.789906930890878E-015 */
		/* qExpTrail[17]:= 1.151608187475169E-014 */
		/* qExpTrail[18]:= 1.519472288906291E-015 */
		/* qExpTrail[19]:= 4.117201960800166E-015 */
		/* qExpTrail[20]:= 6.074702681072822E-015 */
		/* qExpTrail[21]:= 8.205513465754880E-015 */
		/* qExpTrail[22]:= 3.577420871370299E-015 */
		/* qExpTrail[23]:= 6.338036743689160E-015 */
		/* qExpTrail[24]:= 1.007399732183222E-014 */
		/* qExpTrail[25]:= 1.535798430292588E-015 */
		/* qExpTrail[26]:= 6.246850344855366E-015 */
		/* qExpTrail[27]:= 9.122056260354196E-015 */
		/* qExpTrail[28]:= 1.587143306717675E-015 */
		/* qExpTrail[29]:= 6.822155118545929E-015 */
		/* qExpTrail[30]:= 5.666960267488855E-015 */
		/* qExpTrail[31]:= 8.960767791036668E-017 */
		
		/* --------------------------------------------------------------------- */
		/* ---- global constants and table values for  q_lg1p and q_log -------- */
		/* --------------------------------------------------------------------- */

		/* qLogT1= 9.394130628134757E-001 */
		static N const q_lgt1;
		/* qLogT2= 1.064494458917860E+000 */
		static N const q_lgt2;
		/* qLogT3=-6.058693718652422E-002 */
		static N const q_lgt3;
		/* qLogT4= 6.449445891785943E-002 */
		static N const q_lgt4;
		/* qLogT5= 2^-53 = 1.110223024625157E-016 */
		static N const q_lgt5;
		/* qLogT6= 2^55 = 3.60287970189639680E+016 */
		static N const q_lgt6;

		static N const q_lgb[2];
		/* qLogB[1]= 8.333333333326792E-002 */
		/* qLogB[2]= 1.250003418826767E-002 */

		static N const q_lgc[4];
		/* qLogC[1]= 8.333333333333318E-002 */
		/* qLogC[2]= 1.250000000132536E-002 */
		/* qLogC[3]= 2.232141161100800E-003 */
		/* qLogC[4]= 4.347221829254529E-004 */

		static N const q_lgld[129];
		/* qLogLead [  1]= 7.782140442941454E-003 = 3F7FE02A6B200000 */
		/* qLogLead [  2]= 1.550418653641827E-002 = 3F8FC0A8B1000000 */
		/* qLogLead [  3]= 2.316705928205920E-002 = 3F97B91B07D80000 */
		/* qLogLead [  4]= 3.077165866670839E-002 = 3F9F829B0E780000 */
		/* qLogLead [  5]= 3.831886430270970E-002 = 3FA39E87BA000000 */
		/* qLogLead [  6]= 4.580953603181115E-002 = 3FA77458F6340000 */
		/* qLogLead [  7]= 5.324451451815548E-002 = 3FAB42DD71180000 */
		/* qLogLead [  8]= 6.062462181580486E-002 = 3FAF0A30C0100000 */
		/* qLogLead [  9]= 6.795066190898069E-002 = 3FB16536EEA40000 */
		/* qLogLead [ 10]= 7.522342123775161E-002 = 3FB341D7961C0000 */
		/* qLogLead [ 11]= 8.244366921098845E-002 = 3FB51B073F060000 */
		/* qLogLead [ 12]= 8.961215869021544E-002 = 3FB6F0D28AE60000 */
		/* qLogLead [ 13]= 9.672962645890948E-002 = 3FB8C345D6320000 */
		/* qLogLead [ 14]= 1.037967936808855E-001 = 3FBA926D3A4A0000 */
		/* qLogLead [ 15]= 1.108143663404917E-001 = 3FBC5E548F5C0000 */
		/* qLogLead [ 16]= 1.177830356555205E-001 = 3FBE27076E2A0000 */
		/* qLogLead [ 17]= 1.247034785010328E-001 = 3FBFEC9131DC0000 */
		/* qLogLead [ 18]= 1.315763577895268E-001 = 3FC0D77E7CD10000 */
		/* qLogLead [ 19]= 1.384023228583828E-001 = 3FC1B72AD52F0000 */
		/* qLogLead [ 20]= 1.451820098445751E-001 = 3FC29552F8200000 */
		/* qLogLead [ 21]= 1.519160420266417E-001 = 3FC371FC201F0000 */
		/* qLogLead [ 22]= 1.586050301757496E-001 = 3FC44D2B6CCB0000 */
		/* qLogLead [ 23]= 1.652495728958456E-001 = 3FC526E5E3A20000 */
		/* qLogLead [ 24]= 1.718502569274278E-001 = 3FC5FF3070A80000 */
		/* qLogLead [ 25]= 1.784076574731444E-001 = 3FC6D60FE71A0000 */
		/* qLogLead [ 26]= 1.849223384942889E-001 = 3FC7AB8902110000 */
		/* qLogLead [ 27]= 1.913948530000198E-001 = 3FC87FA065210000 */
		/* qLogLead [ 28]= 1.978257433293038E-001 = 3FC9525A9CF40000 */
		/* qLogLead [ 29]= 2.042155414292210E-001 = 3FCA23BC1FE30000 */
		/* qLogLead [ 30]= 2.105647691078048E-001 = 3FCAF3C94E810000 */
		/* qLogLead [ 31]= 2.168739383014326E-001 = 3FCBC286742E0000 */
		/* qLogLead [ 32]= 2.231435513149336E-001 = 3FCC8FF7C79B0000 */
		/* qLogLead [ 33]= 2.293741010653321E-001 = 3FCD5C216B500000 */
		/* qLogLead [ 34]= 2.355660713128600E-001 = 3FCE27076E2B0000 */
		/* qLogLead [ 35]= 2.417199368865113E-001 = 3FCEF0ADCBDC0000 */
		/* qLogLead [ 36]= 2.478361639041395E-001 = 3FCFB9186D5E0000 */
		/* qLogLead [ 37]= 2.539152099816420E-001 = 3FD0402594B50000 */
		/* qLogLead [ 38]= 2.599575244366861E-001 = 3FD0A324E2738000 */
		/* qLogLead [ 39]= 2.659635484978935E-001 = 3FD1058BF9AE8000 */
		/* qLogLead [ 40]= 2.719337154831010E-001 = 3FD1675CABAB8000 */
		/* qLogLead [ 41]= 2.778684510030871E-001 = 3FD1C898C1698000 */
		/* qLogLead [ 42]= 2.837681731307384E-001 = 3FD22941FBCF8000 */
		/* qLogLead [ 43]= 2.896332925829483E-001 = 3FD2895A13DE8000 */
		/* qLogLead [ 44]= 2.954642128934211E-001 = 3FD2E8E2BAE10000 */
		/* qLogLead [ 45]= 3.012613305781997E-001 = 3FD347DD9A988000 */
		/* qLogLead [ 46]= 3.070250352957373E-001 = 3FD3A64C55698000 */
		/* qLogLead [ 47]= 3.127557100033300E-001 = 3FD4043086868000 */
		/* qLogLead [ 48]= 3.184537311190070E-001 = 3FD4618BC21C8000 */
		/* qLogLead [ 49]= 3.241194686543167E-001 = 3FD4BE5F95778000 */
		/* qLogLead [ 50]= 3.297532863725792E-001 = 3FD51AAD872E0000 */
		/* qLogLead [ 51]= 3.353555419216718E-001 = 3FD5767717458000 */
		/* qLogLead [ 52]= 3.409265869704541E-001 = 3FD5D1BDBF580000 */
		/* qLogLead [ 53]= 3.464667673470103E-001 = 3FD62C82F2BA0000 */
		/* qLogLead [ 54]= 3.519764231568843E-001 = 3FD686C81E9B0000 */
		/* qLogLead [ 55]= 3.574558889213222E-001 = 3FD6E08EAA2B8000 */
		/* qLogLead [ 56]= 3.629054936900502E-001 = 3FD739D7F6BC0000 */
		/* qLogLead [ 57]= 3.683255611595087E-001 = 3FD792A55FDD8000 */
		/* qLogLead [ 58]= 3.737164097929053E-001 = 3FD7EAF83B828000 */
		/* qLogLead [ 59]= 3.790783529348118E-001 = 3FD842D1DA1E8000 */
		/* qLogLead [ 60]= 3.844116989112081E-001 = 3FD89A3386C18000 */
		/* qLogLead [ 61]= 3.897167511404405E-001 = 3FD8F11E87368000 */
		/* qLogLead [ 62]= 3.949938082405424E-001 = 3FD947941C210000 */
		/* qLogLead [ 63]= 4.002431641274597E-001 = 3FD99D9581180000 */
		/* qLogLead [ 64]= 4.054651081078191E-001 = 3FD9F323ECBF8000 */
		/* qLogLead [ 65]= 4.106599249844294E-001 = 3FDA484090E58000 */
		/* qLogLead [ 66]= 4.158278951435932E-001 = 3FDA9CEC9A9A0000 */
		/* qLogLead [ 67]= 4.209692946442374E-001 = 3FDAF12932478000 */
		/* qLogLead [ 68]= 4.260843953106814E-001 = 3FDB44F77BCC8000 */
		/* qLogLead [ 69]= 4.311734648181300E-001 = 3FDB985896930000 */
		/* qLogLead [ 70]= 4.362367667745275E-001 = 3FDBEB4D9DA70000 */
		/* qLogLead [ 71]= 4.412745608042314E-001 = 3FDC3DD7A7CD8000 */
		/* qLogLead [ 72]= 4.462871026280482E-001 = 3FDC8FF7C79A8000 */
		/* qLogLead [ 73]= 4.512746441396303E-001 = 3FDCE1AF0B860000 */
		/* qLogLead [ 74]= 4.562374334818742E-001 = 3FDD32FE7E010000 */
		/* qLogLead [ 75]= 4.611757151214988E-001 = 3FDD83E7258A0000 */
		/* qLogLead [ 76]= 4.660897299254430E-001 = 3FDDD46A04C20000 */
		/* qLogLead [ 77]= 4.709797152190731E-001 = 3FDE24881A7C8000 */
		/* qLogLead [ 78]= 4.758459048698569E-001 = 3FDE744261D68000 */
		/* qLogLead [ 79]= 4.806885293455707E-001 = 3FDEC399D2468000 */
		/* qLogLead [ 80]= 4.855078157816024E-001 = 3FDF128F5FAF0000 */
		/* qLogLead [ 81]= 4.903039880446158E-001 = 3FDF6123FA700000 */
		/* qLogLead [ 82]= 4.950772667980345E-001 = 3FDFAF588F790000 */
		/* qLogLead [ 83]= 4.998278695566114E-001 = 3FDFFD2E08580000 */
		/* qLogLead [ 84]= 5.045560107519123E-001 = 3FE02552A5A5C000 */
		/* qLogLead [ 85]= 5.092619017905236E-001 = 3FE04BDF9DA94000 */
		/* qLogLead [ 86]= 5.139457511013461E-001 = 3FE0723E5C1CC000 */
		/* qLogLead [ 87]= 5.186077642083546E-001 = 3FE0986F4F574000 */
		/* qLogLead [ 88]= 5.232481437651586E-001 = 3FE0BE72E4254000 */
		/* qLogLead [ 89]= 5.278670896204858E-001 = 3FE0E44985D1C000 */
		/* qLogLead [ 90]= 5.324647988691140E-001 = 3FE109F39E2D4000 */
		/* qLogLead [ 91]= 5.370414658973459E-001 = 3FE12F7195940000 */
		/* qLogLead [ 92]= 5.415972824321216E-001 = 3FE154C3D2F4C000 */
		/* qLogLead [ 93]= 5.461324375974073E-001 = 3FE179EABBD88000 */
		/* qLogLead [ 94]= 5.506471179523942E-001 = 3FE19EE6B467C000 */
		/* qLogLead [ 95]= 5.551415075406112E-001 = 3FE1C3B81F714000 */
		/* qLogLead [ 96]= 5.596157879353996E-001 = 3FE1E85F5E704000 */
		/* qLogLead [ 97]= 5.640701382853877E-001 = 3FE20CDCD192C000 */
		/* qLogLead [ 98]= 5.685047353526897E-001 = 3FE23130D7BEC000 */
		/* qLogLead [ 99]= 5.729197535620187E-001 = 3FE2555BCE990000 */
		/* qLogLead [100]= 5.773153650352469E-001 = 3FE2795E1289C000 */
		/* qLogLead [101]= 5.816917396350618E-001 = 3FE29D37FEC2C000 */
		/* qLogLead [102]= 5.860490450031648E-001 = 3FE2C0E9ED448000 */
		/* qLogLead [103]= 5.903874466021080E-001 = 3FE2E47436E40000 */
		/* qLogLead [104]= 5.947071077462169E-001 = 3FE307D7334F0000 */
		/* qLogLead [105]= 5.990081896452466E-001 = 3FE32B1339120000 */
		/* qLogLead [106]= 6.032908514389419E-001 = 3FE34E289D9D0000 */
		/* qLogLead [107]= 6.075552502243227E-001 = 3FE37117B5474000 */
		/* qLogLead [108]= 6.118015411066153E-001 = 3FE393E0D3564000 */
		/* qLogLead [109]= 6.160298772156239E-001 = 3FE3B6844A000000 */
		/* qLogLead [110]= 6.202404097512044E-001 = 3FE3D9026A714000 */
		/* qLogLead [111]= 6.244332880123693E-001 = 3FE3FB5B84D18000 */
		/* qLogLead [112]= 6.286086594227527E-001 = 3FE41D8FE8468000 */
		/* qLogLead [113]= 6.327666695706284E-001 = 3FE43F9FE2F9C000 */
		/* qLogLead [114]= 6.369074622361950E-001 = 3FE4618BC21C4000 */
		/* qLogLead [115]= 6.410311794206791E-001 = 3FE48353D1EA8000 */
		/* qLogLead [116]= 6.451379613736208E-001 = 3FE4A4F85DB04000 */
		/* qLogLead [117]= 6.492279466256150E-001 = 3FE4C679AFCD0000 */
		/* qLogLead [118]= 6.533012720119586E-001 = 3FE4E7D811B74000 */
		/* qLogLead [119]= 6.573580727090302E-001 = 3FE50913CC018000 */
		/* qLogLead [120]= 6.613984822452039E-001 = 3FE52A2D265BC000 */
		/* qLogLead [121]= 6.654226325445052E-001 = 3FE54B2467998000 */
		/* qLogLead [122]= 6.694306539429817E-001 = 3FE56BF9D5B40000 */
		/* qLogLead [123]= 6.734226752123504E-001 = 3FE58CADB5CD8000 */
		/* qLogLead [124]= 6.773988235909201E-001 = 3FE5AD404C358000 */
		/* qLogLead [125]= 6.813592248072382E-001 = 3FE5CDB1DC6C0000 */
		/* qLogLead [126]= 6.853040030982811E-001 = 3FE5EE02A9240000 */
		/* qLogLead [127]= 6.892332812385575E-001 = 3FE60E32F4478000 */
		/* qLogLead [128]= 6.931471805601177E-001 = 3FE62E42FEFA4000 */

		static N const q_lgtl[129];
		/* qLogTrail [  1]=-8.865052917267247E-013 = BD6F30EE07912DF9 */
		/* qLogTrail [  2]=-4.530198941364935E-013 = BD5FE0E183092C59 */
		/* qLogTrail [  3]=-5.248209479295644E-013 = BD62772AB6C0559C */
		/* qLogTrail [  4]= 4.529814257790929E-014 = 3D2980267C7E09E4 */
		/* qLogTrail [  5]=-5.730994833076631E-013 = BD642A056FEA4DFD */
		/* qLogTrail [  6]=-5.169456928812220E-013 = BD62303B9CB0D5E1 */
		/* qLogTrail [  7]= 6.567993368985218E-013 = 3D671BEC28D14C7E */
		/* qLogTrail [  8]= 6.299848199383311E-013 = 3D662A6617CC9717 */
		/* qLogTrail [  9]=-4.729424109166329E-013 = BD60A3E2F3B47D18 */
		/* qLogTrail [ 10]=-1.640830158559866E-013 = BD4717B6B33E44F8 */
		/* qLogTrail [ 11]= 8.614512936087814E-014 = 3D383F69278E686A */
		/* qLogTrail [ 12]=-5.283050530808144E-013 = BD62968C836CC8C2 */
		/* qLogTrail [ 13]=-3.583666743009414E-013 = BD5937C294D2F567 */
		/* qLogTrail [ 14]= 7.581073923016376E-013 = 3D6AAC6CA17A4554 */
		/* qLogTrail [ 15]=-2.015736841601622E-013 = BD4C5E7514F4083F */
		/* qLogTrail [ 16]= 8.629474042969438E-013 = 3D6E5CBD3D50FFFC */
		/* qLogTrail [ 17]=-7.556920687451337E-014 = BD354555D1AE6607 */
		/* qLogTrail [ 18]=-8.075373495358435E-013 = BD6C69A65A23A170 */
		/* qLogTrail [ 19]= 7.363043577087051E-013 = 3D69E80A41811A39 */
		/* qLogTrail [ 20]=-7.718001336828099E-014 = BD35B967F4471DFC */
		/* qLogTrail [ 21]=-7.996871607743758E-013 = BD6C22F10C9A4EA8 */
		/* qLogTrail [ 22]= 8.890223439724663E-013 = 3D6F4799F4F6543E */
		/* qLogTrail [ 23]=-5.384682618788232E-013 = BD62F21746FF8A47 */
		/* qLogTrail [ 24]=-7.686134224018169E-013 = BD6B0B0DE3077D7E */
		/* qLogTrail [ 25]=-3.260571793105816E-013 = BD56F1B955C4D1DA */
		/* qLogTrail [ 26]=-2.768588431044831E-013 = BD537B720E4A694B */
		/* qLogTrail [ 27]=-3.903387893794952E-013 = BD5B77B7EFFB7F41 */
		/* qLogTrail [ 28]= 6.160755775588723E-013 = 3D65AD1D904C1D4E */
		/* qLogTrail [ 29]=-5.301565160060260E-013 = BD62A739B23B93E1 */
		/* qLogTrail [ 30]=-4.551124227747820E-013 = BD600349CC67F9B2 */
		/* qLogTrail [ 31]=-8.182853292737783E-013 = BD6CCA75818C5DBC */
		/* qLogTrail [ 32]=-7.238189921749681E-013 = BD697794F689F843 */
		/* qLogTrail [ 33]=-4.862400015383790E-013 = BD611BA91BBCA682 */
		/* qLogTrail [ 34]=-9.309459495196889E-014 = BD3A342C2AF0003C */
		/* qLogTrail [ 35]= 6.338907368997553E-013 = 3D664D948637950E */
		/* qLogTrail [ 36]= 4.417175537131555E-013 = 3D5F1546AAA3361C */
		/* qLogTrail [ 37]=-6.785208495970588E-013 = BD67DF928EC217A5 */
		/* qLogTrail [ 38]= 2.399954048421174E-013 = 3D50E35F73F7A018 */
		/* qLogTrail [ 39]=-7.555569400283742E-013 = BD6A9573B02FAA5A */
		/* qLogTrail [ 40]= 5.407904186145515E-013 = 3D630701CE63EAB9 */
		/* qLogTrail [ 41]= 3.692037508208009E-013 = 3D59FAFBC68E7540 */
		/* qLogTrail [ 42]=-9.383417223663700E-014 = BD3A6976F5EB0963 */
		/* qLogTrail [ 43]= 9.433398189512690E-014 = 3D3A8D7AD24C13F0 */
		/* qLogTrail [ 44]= 4.148131870425857E-013 = 3D5D309C2CC91A85 */
		/* qLogTrail [ 45]=-3.792316480209315E-014 = BD25594DD4C58092 */
		/* qLogTrail [ 46]=-8.254631387250040E-013 = BD6D0B1C68651946 */
		/* qLogTrail [ 47]= 5.668653582900739E-013 = 3D63F1DE86093EFA */
		/* qLogTrail [ 48]=-4.723727821986367E-013 = BD609EC17A426426 */
		/* qLogTrail [ 49]=-1.047575005877654E-013 = BD3D7C92CD9AD824 */
		/* qLogTrail [ 50]=-1.111867138955932E-013 = BD3F4BD8DB0A7CC1 */
		/* qLogTrail [ 51]=-5.339989292003297E-013 = BD62C9D5B2A49AF9 */
		/* qLogTrail [ 52]= 1.391284121219757E-013 = 3D4394A11B1C1EE4 */
		/* qLogTrail [ 53]=-8.017372713972018E-013 = BD6C356848506EAD */
		/* qLogTrail [ 54]= 2.939185918764800E-013 = 3D54AEC442BE1015 */
		/* qLogTrail [ 55]= 4.815896111723205E-013 = 3D60F1C609C98C6C */
		/* qLogTrail [ 56]=-6.817539406325327E-013 = BD67FCB18ED9D603 */
		/* qLogTrail [ 57]=-8.009990055432491E-013 = BD6C2EC1F512DC03 */
		/* qLogTrail [ 58]= 6.787566823158706E-013 = 3D67E1B259D2F3DA */
		/* qLogTrail [ 59]= 1.576120377396944E-013 = 3D462E927628CBC2 */
		/* qLogTrail [ 60]=-8.760375990774874E-013 = BD6ED2A52C73BF78 */
		/* qLogTrail [ 61]=-4.152515806343612E-013 = BD5D3881E8962A96 */
		/* qLogTrail [ 62]= 3.265569889690715E-013 = 3D56FABA4CDD147D */
		/* qLogTrail [ 63]=-4.470426501045244E-013 = BD5F753456D113B8 */
		/* qLogTrail [ 64]= 3.452764795203977E-013 = 3D584BF2B68D766F */
		/* qLogTrail [ 65]= 8.390050778518307E-013 = 3D6D8515FE535B87 */
		/* qLogTrail [ 66]= 1.177697875136921E-013 = 3D40931A909FEA5E */
		/* qLogTrail [ 67]=-1.077434146160958E-013 = BD3E53BB31EED7A9 */
		/* qLogTrail [ 68]= 2.186334329321591E-013 = 3D4EC5197DDB55D3 */
		/* qLogTrail [ 69]= 2.413263949133313E-013 = 3D50FB598FB14F89 */
		/* qLogTrail [ 70]= 3.905746220983070E-013 = 3D5B7BF7861D37AC */
		/* qLogTrail [ 71]= 6.437879097373207E-013 = 3D66A6B9D9E0A5BD */
		/* qLogTrail [ 72]= 3.713514191959202E-013 = 3D5A21AC25D81EF3 */
		/* qLogTrail [ 73]=-1.716692133608243E-013 = BD48290905A86AA6 */
		/* qLogTrail [ 74]=-2.865828515791435E-013 = BD542A9E21373414 */
		/* qLogTrail [ 75]= 6.713692791384601E-013 = 3D679F2828ADD176 */
		/* qLogTrail [ 76]=-8.437281040871276E-013 = BD6DAFA08CECADB1 */
		/* qLogTrail [ 77]=-2.821014384618127E-013 = BD53D9E34270BA6B */
		/* qLogTrail [ 78]= 1.070193176211425E-013 = 3D3E1F8DF68DBCF3 */
		/* qLogTrail [ 79]= 1.811934636644111E-013 = 3D49802EB9DCA7E7 */
		/* qLogTrail [ 80]= 9.840465278232627E-014 = 3D3BB2CD720EC44C */
		/* qLogTrail [ 81]= 5.780031989454028E-013 = 3D645630A2B61E5B */
		/* qLogTrail [ 82]=-1.830285735604167E-013 = BD49C24CA098362B */
		/* qLogTrail [ 83]=-1.620740015674495E-013 = BD46CF54D05F9367 */
		/* qLogTrail [ 84]= 4.830331494955320E-013 = 3D60FEC69C695D7F */
		/* qLogTrail [ 85]=-7.156055317238212E-013 = BD692D9A033EFF75 */
		/* qLogTrail [ 86]= 8.882123951857185E-013 = 3D6F404E57963891 */
		/* qLogTrail [ 87]=-3.090058051323824E-013 = BD55BE8DC04AD601 */
		/* qLogTrail [ 88]=-6.107655197285150E-013 = BD657D49676844CC */
		/* qLogTrail [ 89]= 3.565996966334783E-013 = 3D5917EDD5CBBD2D */
		/* qLogTrail [ 90]= 3.578239659127638E-013 = 3D592DFBC7D93617 */
		/* qLogTrail [ 91]=-4.622608700154458E-013 = BD6043ACFEDCE638 */
		/* qLogTrail [ 92]= 6.227976291722515E-013 = 3D65E9A98F33A396 */
		/* qLogTrail [ 93]= 7.283894727206574E-013 = 3D69A0BFC60E6FA0 */
		/* qLogTrail [ 94]= 2.680964661521167E-013 = 3D52DD98B97BAEF0 */
		/* qLogTrail [ 95]=-1.096082504605928E-013 = BD3EDA1B58389902 */
		/* qLogTrail [ 96]= 2.311949383800538E-014 = 3D1A07BD8B34BE7C */
		/* qLogTrail [ 97]=-5.846905800529924E-013 = BD64926CAFC2F08A */
		/* qLogTrail [ 98]=-2.103748251144494E-014 = BD17AFA4392F1BA7 */
		/* qLogTrail [ 99]=-2.332318294558741E-013 = BD506987F78A4A5E */
		/* qLogTrail [100]=-4.233369428814192E-013 = BD5DCA290F81848D */
		/* qLogTrail [101]=-4.393393796973784E-013 = BD5EEA6F465268B4 */
		/* qLogTrail [102]= 4.134164707383556E-013 = 3D5D1772F5386374 */
		/* qLogTrail [103]= 6.841763641591467E-014 = 3D334202A10C3491 */
		/* qLogTrail [104]= 4.758553400443064E-013 = 3D60BE1FB590A1F5 */
		/* qLogTrail [105]= 8.367967867475769E-013 = 3D6D71320556B67B */
		/* qLogTrail [106]=-8.576373464665864E-013 = BD6E2CE9146D277A */
		/* qLogTrail [107]= 2.191328122934009E-013 = 3D4ED71774092113 */
		/* qLogTrail [108]=-6.224284253643115E-013 = BD65E6563BBD9FC9 */
		/* qLogTrail [109]=-1.098359432543843E-013 = BD3EEA838909F3D3 */
		/* qLogTrail [110]= 6.531043137763365E-013 = 3D66FAA404263D0B */
		/* qLogTrail [111]=-4.758019902171077E-013 = BD60BDA4B162AFA3 */
		/* qLogTrail [112]=-3.785425126545704E-013 = BD5AA33736867A17 */
		/* qLogTrail [113]= 4.093923321867867E-013 = 3D5CCEF4E4F736C2 */
		/* qLogTrail [114]= 8.742438391485829E-013 = 3D6EC27D0B7B37B3 */
		/* qLogTrail [115]= 2.521818845684288E-013 = 3D51BEE7ABD17660 */
		/* qLogTrail [116]=-3.608131360422557E-014 = BD244FDD840B8591 */
		/* qLogTrail [117]=-5.051855592428090E-013 = BD61C64E971322CE */
		/* qLogTrail [118]= 7.869940332335532E-013 = 3D6BB09CB0985646 */
		/* qLogTrail [119]=-6.702087696194906E-013 = BD6794B434C5A4F5 */
		/* qLogTrail [120]= 1.610857575393246E-013 = 3D46ABB9DF22BC57 */
		/* qLogTrail [121]= 5.852718843625151E-013 = 3D6497A915428B44 */
		/* qLogTrail [122]=-3.524675729790479E-013 = BD58CD7DC73BD194 */
		/* qLogTrail [123]=-1.837208449562906E-013 = BD49DB3DB43689B4 */
		/* qLogTrail [124]= 8.860668981349492E-013 = 3D6F2CFB29AAA5F0 */
		/* qLogTrail [125]= 6.648626807146870E-013 = 3D67648CF6E3C5D7 */
		/* qLogTrail [126]= 6.383161517064652E-013 = 3D667570D6095FD2 */
		/* qLogTrail [127]= 2.514423072837607E-013 = 3D51B194F912B417 */
		/* qLogTrail [128]=-1.723944452561483E-013 = BD48432A1B0E2634 */
 
		/* --------------------------------------------------------------------- */
		/* ---- global constants for q_sin and q_cos --------------------------- */
		/* --------------------------------------------------------------------- */
		static N const q_sinc[6];
		static N const q_sins[6];
		static N const q_sint[5];
		/* 2.580900000000000E-008 */ 
		/* 1.825000000000000E-008 */ 
		/* q_sint[2]= 3.373259425345106E+009 */ 

		/* --------------------------------------------------------------------- */
		/* ---- global constants for q_atnh ------------------------------------ */
		/* --------------------------------------------------------------------- */
 
		/*     q_at3i = 3.333333333333333E-001                               */
		static N const q_at3i;
	};

}

#endif
