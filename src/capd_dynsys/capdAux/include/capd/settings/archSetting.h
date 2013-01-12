/// @addtogroup capd
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file archSetting.h
///
/// @author Mikalaj Zalewski
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// This files determines the processor architecture. If checks the compiler-dependent
// symbols and sets the CAPD_CPU_ARCH variable to one of x86, x86_64 or sparc
// The CAPD_ASM_NOTATION is set to one of 'gnu' or 'intel' depending on the compiler


#ifndef _CAPD_CAPD_ARCHSETTING_H_ 
#define _CAPD_CAPD_ARCHSETTING_H_ 

// This files determines the CPU architecture. After including this file, the
// CAPD_CPU_ARCH will be set to one of the CAPD_CPU_ARCH_* constants

// Possible architectures
#define CAPD_CPU_ARCH_X86 1
#define CAPD_CPU_ARCH_AMD64 2
#define CAPD_CPU_ARCH_SPARC 3
#define CAPD_CPU_ARCH_POWERPC 4

// ################ Manual CPU architecture selection #######################
// Uncomment exactly one of the following defines if the automatic system
// selection doesn't work for you.
//
//#define CAPD_CPU_ARCH  CAPD_CPU_ARCH_X86   // x86 processor (a.k.a. IA-32, i386) 
//                               // - found in PCs with a 32-bit operating system
//#define CAPD_CPU_ARCH  CAPD_CPU_ARCH_AMD64 // amd64 processor (a.k.a. x86-64, x86_64,
//                               // EM64T, x64) - newer PCs with a 64-bit CPU and OS
//                               // Note: if you have a 64-bit CPU but a 32-bit OS choose x86
//#define CAPD_CPU_ARCH  CAPD_CPU_ARCH_SPARC   // SPARC processor - found in Sun workstations/servers
//#define CAPD_CPU_ARCH  CAPD_CPU_ARCH_POWERPC // PowerPC processor - used in most Apple MacIntoshes


// ################## Automatic operating system selection ##################
// Determine the target platform. Note that the code in the entire package
// relies on the compiler settings like WIN95, LINUX, etc.

// auto-detect if not set before
#ifndef CAPD_CPU_ARCH

#if defined(__i386__) ||        /* GNU C */ \
    defined(_M_IX86) ||         /* Visual C++ / Intel C/C++ */ \
    defined(__i386) ||          /* Sun Pro C*/ \
    defined(_X86_) ||           /* MinGW */ \
    defined(BORLAND)            /* Borland C++ (available for DOS/Windows) */
#define CAPD_CPU_ARCH CAPD_CPU_ARCH_X86

#elif defined(__x86_64__) ||        /* GNU C */ \
    defined(_M_X64)               /* Visual C++ / Intel C/C++ */
#define CAPD_CPU_ARCH CAPD_CPU_ARCH_AMD64

#elif defined(__sparc__) ||        /* GNU C */ \
    defined(__sparc)             /* Sun Pro C*/
#define CAPD_CPU_ARCH CAPD_CPU_ARCH_SPARC

#elif defined(__APPLE__) ||        /* GNU C */ \
    defined(__powerpc__) ||          /* GNU C */ \
    defined(__powerpc) ||          /* GNU C */ \
    defined(__POWERPC__) ||        /* GNU C */ \
    defined(_M_PPC)                /* Visual C++ */
#define CAPD_CPU_ARCH CAPD_CPU_ARCH_POWERPC
#endif

#endif /* !defined(CAPD_CPU_ARCH) */

#ifndef CAPD_CPU_ARCH
#error Couldnt determine the processor architecture. Set it manually in archSetting.h
#endif

#endif // _CAPD_CAPD_ARCHSETTING_H_ 
/// @}
