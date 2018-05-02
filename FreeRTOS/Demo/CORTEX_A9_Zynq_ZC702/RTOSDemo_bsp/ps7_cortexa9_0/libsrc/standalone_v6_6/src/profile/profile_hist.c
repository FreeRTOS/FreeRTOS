/******************************************************************************
*
* Copyright (C) 2002 - 2014 Xilinx, Inc. All rights reserved.
*
* Permission is hereby granted, free of charge, to any person obtaining a copy
* of this software and associated documentation files (the "Software"), to deal
* in the Software without restriction, including without limitation the rights
* to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
* copies of the Software, and to permit persons to whom the Software is
* furnished to do so, subject to the following conditions:
*
* The above copyright notice and this permission notice shall be included in
* all copies or substantial portions of the Software.
*
* Use of the Software is limited solely to applications:
* (a) running on a Xilinx device, or
* (b) that interact with a Xilinx device through a bus or interconnect.
*
* THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
* IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
* FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
* XILINX  BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
* WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF
* OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
* SOFTWARE.
*
* Except as contained in this notice, the name of the Xilinx shall not be used
* in advertising or otherwise to promote the sale, use or other dealings in
* this Software without prior written authorization from Xilinx.
*
******************************************************************************/

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

extern u32 binsize ;
u32 prof_pc ;

void profile_intr_handler( void )
{

	s32 j;

#ifdef PROC_MICROBLAZE
	asm( "swi r14, r0, prof_pc" ) ;
#elif defined PROC_PPC
	prof_pc = mfspr(SPR_SRR0);
#else
	/* for cortexa9, lr is saved in asm interrupt handler */
#endif
	/* print("PC: "), putnum(prof_pc), print("\r\n"), */
	for(j = 0; j < n_gmon_sections; j++ ){
		if((prof_pc >= ((u32)_gmonparam[j].lowpc)) && (prof_pc < ((u32)_gmonparam[j].highpc))) {
			_gmonparam[j].kcount[(prof_pc-_gmonparam[j].lowpc)/((u32)4 * binsize)]++;
			break;
		}
	}
	/* Ack the Timer Interrupt */
	timer_ack();
}
