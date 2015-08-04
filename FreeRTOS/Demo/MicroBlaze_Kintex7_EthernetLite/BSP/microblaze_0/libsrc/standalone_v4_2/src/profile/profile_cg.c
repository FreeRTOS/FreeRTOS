// $Id: profile_cg.c,v 1.1.2.1 2011/05/17 04:37:57 sadanan Exp $
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

#include "profile.h"
#include "_profile_timer_hw.h"
#ifdef PROC_MICROBLAZE
#include "mblaze_nt_types.h"
#endif

/*
 * The mcount fucntion is excluded from the library, if the user defines
 * PROFILE_NO_GRAPH.
 */
#ifndef PROFILE_NO_GRAPH

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

extern struct gmonparam *_gmonparam;

#ifdef PROFILE_NO_FUNCPTR
int searchpc( struct fromto_struct *cgtable, int cgtable_size, unsigned long frompc )
{
	int index = 0 ;

	while( (index < cgtable_size) && (cgtable[index].frompc != frompc) ){
		index++ ;
	}
	if( index == cgtable_size )
		return -1 ;
	else
		return index ;
}
#else
int searchpc( struct fromstruct *froms, int fromssize, unsigned long frompc )
{
	int index = 0 ;

	while( (index < fromssize) && (froms[index].frompc != frompc) ){
		index++ ;
	}
	if( index == fromssize )
		return -1 ;
	else
		return index ;
}
#endif		/* PROFILE_NO_FUNCPTR */


void mcount( unsigned long frompc, unsigned long selfpc )
{
	register struct gmonparam *p = NULL;
	register long toindex, fromindex;
	int j;

	disable_timer();

	//print("CG: "); putnum(frompc); print("->"); putnum(selfpc); print("\r\n");
	// check that frompcindex is a reasonable pc value.
	// for example:	signal catchers get called from the stack,
	//		not from text space.  too bad.
	//
	for(j = 0; j < n_gmon_sections; j++ ){
		if((frompc >= _gmonparam[j].lowpc) && (frompc < _gmonparam[j].highpc)) {
			p = &_gmonparam[j];
			break;
		}
	}
	if( j == n_gmon_sections )
		goto done;

#ifdef PROFILE_NO_FUNCPTR
	fromindex = searchpc( p->cgtable, p->cgtable_size, frompc ) ;
	if( fromindex == -1 ) {
		fromindex = p->cgtable_size ;
		p->cgtable_size++ ;
		p->cgtable[fromindex].frompc = frompc ;
		p->cgtable[fromindex].selfpc = selfpc ;
		p->cgtable[fromindex].count = 1 ;
		goto done ;
	}
	p->cgtable[fromindex].count++ ;
#else
	fromindex = searchpc( p->froms, p->fromssize, frompc ) ;
	if( fromindex == -1 ) {
		fromindex = p->fromssize ;
		p->fromssize++ ;
		//if( fromindex >= N_FROMS ) {
		//print("Error : From PC table overflow\r\n") ;
		//goto overflow ;
		//}
		p->froms[fromindex].frompc = frompc ;
		p->froms[fromindex].link = -1 ;
	}else {
		toindex = p->froms[fromindex].link ;
		while(toindex != -1) {
			toindex = (p->tossize - toindex)-1 ;
			if( p->tos[toindex].selfpc == selfpc ) {
				p->tos[toindex].count++ ;
				goto done ;
			}
			toindex = p->tos[toindex].link ;
		}
	}

	//if( toindex == -1 ) {
	p->tos-- ;
	p->tossize++ ;
	//if( toindex >= N_TOS ) {
	//print("Error : To PC table overflow\r\n") ;
	//goto overflow ;
	//}
	p->tos[0].selfpc = selfpc ;
	p->tos[0].count = 1 ;
	p->tos[0].link = p->froms[fromindex].link ;
	p->froms[fromindex].link = p->tossize-1 ;
#endif

 done:
	p->state = GMON_PROF_ON;
	goto enable_timer ;
 //overflow:
	p->state = GMON_PROF_ERROR;
 enable_timer:
	enable_timer();
	return ;
}


#endif		/* PROFILE_NO_GRAPH */

