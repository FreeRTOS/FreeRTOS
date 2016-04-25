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
******************************************************************************
*
* _program_init.c:
*	Initialize the Profiling Structures.
*
******************************************************************************/

#include "profile.h"

/* XMD Initializes the following Global Variables Value during Program
 *  Download with appropriate values. */

#ifdef PROC_MICROBLAZE

extern s32 microblaze_init(void);

#elif defined PROC_PPC

extern s32 powerpc405_init(void);

#else

extern s32 cortexa9_init(void);

#endif

s32 profile_version = 1;	/* Version of S/W Intrusive Profiling library */

u32 binsize = (u32)BINSIZE;    			/* Histogram Bin Size */
u32 cpu_clk_freq = (u32)CPU_FREQ_HZ ;	/* CPU Clock Frequency */
u32 sample_freq_hz = (u32)SAMPLE_FREQ_HZ ;	/* Histogram Sampling Frequency */
u32 timer_clk_ticks = (u32)TIMER_CLK_TICKS ;/* Timer Clock Ticks for the Timer */

/* Structure for Storing the Profiling Data */
struct gmonparam *_gmonparam = (struct gmonparam *)(0xffffffffU);
s32 n_gmon_sections = 1;

/* This is the initialization code, which is called from the crtinit. */

void _profile_init( void )
{
/* 	print("Gmon Init called....\r\n")  */
/* 	putnum(n_gmon_sections) , print("\r\n")   */
/* 	if( _gmonparam == 0xffffffff ) */
/* 		printf("Gmonparam is NULL !!\r\n")  */
/* 	for( i = 0, i < n_gmon_sections, i++ )[ */
/* 		putnum( _gmonparam[i].lowpc) , print("\t")   */
/* 		putnum( _gmonparam[i].highpc) , print("\r\n")  */
/* 		putnum( _gmonparam[i].textsize ), print("\r\n")  */
/* 		putnum( _gmonparam[i].kcountsize * sizeof(unsigned short)), print("\r\n")  */
/* 	] */

#ifdef PROC_MICROBLAZE
	(void)microblaze_init();
#elif defined PROC_PPC
	powerpc405_init();
#else
	(void)cortexa9_init();
#endif
}
