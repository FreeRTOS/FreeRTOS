//////////////////////////////////////////////////////////////////////
//
// Copyright (c) 2002-2011 Xilinx, Inc.  All rights reserved.
// Xilinx, Inc.
//
// XILINX IS PROVIDING THIS DESIGN, CODE, OR INFORMATION "AS IS" AS A
// COURTESY TO YOU.  BY PROVIDING THIS DESIGN, CODE, OR INFORMATION AS
// ONE POSSIBLE   IMPLEMENTATION OF THIS FEATURE, APPLICATION OR
// STANDARD, XILINX IS MAKING NO REPRESENTATION THAT THIS IMPLEMENTATION
// IS FREE FROM ANY CLAIMS OF INFRINGEMENT, AND YOU ARE RESPONSIBLE
// FOR OBTAINING ANY RIGHTS YOU MAY REQUIRE FOR YOUR IMPLEMENTATION.
// XILINX EXPRESSLY DISCLAIMS ANY WARRANTY WHATSOEVER WITH RESPECT TO
// THE ADEQUACY OF THE IMPLEMENTATION, INCLUDING BUT NOT LIMITED TO
// ANY WARRANTIES OR REPRESENTATIONS THAT THIS IMPLEMENTATION IS FREE
// FROM CLAIMS OF INFRINGEMENT, IMPLIED WARRANTIES OF MERCHANTABILITY
// AND FITNESS FOR A PARTICULAR PURPOSE.
//
// $Id: _profile_init.c,v 1.1.2.1 2011/05/17 04:37:56 sadanan Exp $
//
// _program_init.c:
//	Initialize the Profiling Structures.
//
//////////////////////////////////////////////////////////////////////

#include "profile.h"

// XMD Initializes the following Global Variables Value during Program
// Download with appropriate values.

#ifdef PROC_MICROBLAZE

extern int microblaze_init(void);

#elif defined PROC_PPC

extern int powerpc405_init(void);

#else

extern int cortexa9_init(void);

#endif



int profile_version = 1;	// Version of S/W Intrusive Profiling library

int binsize = BINSIZE;    			// Histogram Bin Size
unsigned int cpu_clk_freq = CPU_FREQ_HZ ;	// CPU Clock Frequency
unsigned int sample_freq_hz = SAMPLE_FREQ_HZ ;	// Histogram Sampling Frequency
unsigned int timer_clk_ticks = TIMER_CLK_TICKS ;// Timer Clock Ticks for the Timer

// Structure for Storing the Profiling Data
struct gmonparam *_gmonparam = (struct gmonparam *)0xffffffff;
int n_gmon_sections = 1;

// This is the initialization code, which is called from the crtinit.
//
void _profile_init( void )
{
/* 	print("Gmon Init called....\r\n") ; */
/* 	putnum(n_gmon_sections) ; print("\r\n") ; */
/* 	if( _gmonparam == 0xffffffff ) */
/* 		printf("Gmonparam is NULL !!\r\n"); */
/* 	for( i = 0; i < n_gmon_sections; i++ ){ */
/* 		putnum(_gmonparam[i].lowpc) ; print("\t") ; */
/* 		putnum(_gmonparam[i].highpc) ; print("\r\n") ; */
/* 		putnum( _gmonparam[i].textsize ); print("\r\n") ; */
/* 		putnum( _gmonparam[i].kcountsize * sizeof(unsigned short));print("\r\n"); */
/* 	} */

#ifdef PROC_MICROBLAZE
	microblaze_init();
#elif defined PROC_PPC
	powerpc405_init();
#else
	cortexa9_init ();
#endif
}

