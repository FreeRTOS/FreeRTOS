// $Id: profile.h,v 1.1.2.2 2011/05/30 06:46:18 svemula Exp $
/******************************************************************************
*
* Copyright (C) 2002 - 2014 Xilinx, Inc.  All rights reserved.
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

#ifndef	_PROFILE_H
#define	_PROFILE_H	1

#include <stdio.h>
#include "profile_config.h"

#ifdef PROC_MICROBLAZE
#include "mblaze_nt_types.h"
#endif

#ifdef __cplusplus
extern "C" {
#endif

void _system_init( void ) ;
void _system_clean( void ) ;
void mcount(unsigned long frompc, unsigned long selfpc);
void profile_intr_handler( void ) ;



/****************************************************************************
 * Profiling on hardware - Hash table maintained on hardware and data sent
 * to xmd for gmon.out generation.
 ****************************************************************************/
/*
 * histogram counters are unsigned shorts (according to the kernel).
 */
#define	HISTCOUNTER	unsigned short

struct tostruct {
	unsigned long  selfpc;
	long	       count;
	short 	       link;
	unsigned short pad;
};

struct fromstruct {
	unsigned long frompc ;
	short link ;
	unsigned short pad ;
} ;

/*
 * general rounding functions.
 */
#define ROUNDDOWN(x,y)	(((x)/(y))*(y))
#define ROUNDUP(x,y)	((((x)+(y)-1)/(y))*(y))

/*
 * The profiling data structures are housed in this structure.
 */
struct gmonparam {
	long int		state;

	// Histogram Information
	unsigned short		*kcount;	/* No. of bins in histogram */
	unsigned long		kcountsize;	/* Histogram samples */

	// Call-graph Information
	struct fromstruct	*froms;
	unsigned long		fromssize;
	struct tostruct		*tos;
	unsigned long		tossize;

	// Initialization I/Ps
	unsigned long    	lowpc;
	unsigned long		highpc;
	unsigned long		textsize;
	//unsigned long 		cg_froms;
	//unsigned long 		cg_tos;
};
extern struct gmonparam *_gmonparam;
extern int n_gmon_sections;

/*
 * Possible states of profiling.
 */
#define	GMON_PROF_ON	0
#define	GMON_PROF_BUSY	1
#define	GMON_PROF_ERROR	2
#define	GMON_PROF_OFF	3

/*
 * Sysctl definitions for extracting profiling information from the kernel.
 */
#define	GPROF_STATE	0	/* int: profiling enabling variable */
#define	GPROF_COUNT	1	/* struct: profile tick count buffer */
#define	GPROF_FROMS	2	/* struct: from location hash bucket */
#define	GPROF_TOS	3	/* struct: destination/count structure */
#define	GPROF_GMONPARAM	4	/* struct: profiling parameters (see above) */

#ifdef __cplusplus
}
#endif

#endif 		/* _PROFILE_H */












