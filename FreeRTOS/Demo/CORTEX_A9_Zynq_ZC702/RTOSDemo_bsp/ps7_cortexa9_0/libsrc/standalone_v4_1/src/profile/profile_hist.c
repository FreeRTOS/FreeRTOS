//
// Copyright (c) 2002-2010 Xilinx, Inc.  All rights reserved.
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
// $Id: profile_hist.c,v 1.1.2.1 2011/05/17 04:37:57 sadanan Exp $
//
#include "profile.h"
#include "_profile_timer_hw.h"

#ifdef PROC_MICROBLAZE
#include "mblaze_nt_types.h"
#endif

#ifdef PROC_PPC
#include "xpseudo_asm.h"
#define SPR_SRR0 0x01A
#endif

#include "xil_types.h" 

extern int binsize ;
u32 prof_pc ;

void profile_intr_handler( void )
{

	int j;

#ifdef PROC_MICROBLAZE
	asm( "swi r14, r0, prof_pc" ) ;
#elif defined PROC_PPC
	prof_pc = mfspr(SPR_SRR0);
#else
	// for cortexa9, lr is saved in asm interrupt handler
#endif
	//print("PC: "); putnum(prof_pc); print("\r\n");
	for(j = 0; j < n_gmon_sections; j++ ){
		if((prof_pc >= _gmonparam[j].lowpc) && (prof_pc < _gmonparam[j].highpc)) {
			_gmonparam[j].kcount[(prof_pc-_gmonparam[j].lowpc)/(4 * binsize)]++;
			break;
		}
	}
	// Ack the Timer Interrupt
	timer_ack();
}

