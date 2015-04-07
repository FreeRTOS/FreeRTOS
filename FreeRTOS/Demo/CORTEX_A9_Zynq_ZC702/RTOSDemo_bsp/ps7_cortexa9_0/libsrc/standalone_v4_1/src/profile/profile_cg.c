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
// $Id: profile_cg.c,v 1.1.2.1 2011/05/17 04:37:57 sadanan Exp $
//

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

