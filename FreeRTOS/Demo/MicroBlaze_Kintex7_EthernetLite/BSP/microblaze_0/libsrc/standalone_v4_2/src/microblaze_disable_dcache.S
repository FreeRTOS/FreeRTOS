/******************************************************************************
* Copyright (c) 2008-2013 Xilinx, Inc.  All rights reserved. 
* 
* Xilinx, Inc. 
* XILINX IS PROVIDING THIS DESIGN, CODE, OR INFORMATION "AS IS" AS A 
* COURTESY TO YOU.  BY PROVIDING THIS DESIGN, CODE, OR INFORMATION AS 
* ONE POSSIBLE   IMPLEMENTATION OF THIS FEATURE, APPLICATION OR 
* STANDARD, XILINX IS MAKING NO REPRESENTATION THAT THIS IMPLEMENTATION 
* IS FREE FROM ANY CLAIMS OF INFRINGEMENT, AND YOU ARE RESPONSIBLE 
* FOR OBTAINING ANY RIGHTS YOU MAY REQUIRE FOR YOUR IMPLEMENTATION. 
* XILINX EXPRESSLY DISCLAIMS ANY WARRANTY WHATSOEVER WITH RESPECT TO 
* THE ADEQUACY OF THE IMPLEMENTATION, INCLUDING BUT NOT LIMITED TO 
* ANY WARRANTIES OR REPRESENTATIONS THAT THIS IMPLEMENTATION IS FREE 
* FROM CLAIMS OF INFRINGEMENT, IMPLIED WARRANTIES OF MERCHANTABILITY 
* AND FITNESS FOR A PARTICULAR PURPOSE. 
* 
* File   : microblaze_disable_dcache.s
* Date   : 2002, March 20.
* Company: Xilinx
* Group  : Emerging Software Technologies
*
* Summary:
* Disable the L1 dcache on the microblaze.
*
*******************************************************************************/

#include "xparameters.h"
	
	.text
	.globl	microblaze_disable_dcache
	.ent	microblaze_disable_dcache
	.align	2
microblaze_disable_dcache:
#if XPAR_MICROBLAZE_USE_MSR_INSTR == 1

#if XPAR_MICROBLAZE_DCACHE_USE_WRITEBACK != 0
    addik   r1, r1, -4
    swi     r15, r1, 0
    brlid   r15, microblaze_flush_dcache /* microblaze_flush_dcache does not use r1*/
    nop
    lwi     r15, r1, 0
    addi    r1, r1, 4
#endif /* XPAR_MICROBLAZE_DCACHE_USE_WRITEBACK != 0 */
	rtsd	r15, 8
	msrclr r0, 0x80

#else /* XPAR_MICROBLAZE_USE_MSR_INSTR == 1 */

    addik   r1, r1, -4

#if XPAR_MICROBLAZE_DCACHE_USE_WRITEBACK != 0
    swi     r15, r1, 0
    brlid   r15, microblaze_flush_dcache
    nop
#endif /* XPAR_MICROBLAZE_DCACHE_USE_WRITEBACK != 0 */
    mfs	r11, rmsr
	andi	r11, r11, ~(0x80)
	mts	rmsr, r11

#if XPAR_MICROBLAZE_DCACHE_USE_WRITEBACK != 0   
    lwi     r15, r1, 0
#endif /* XPAR_MICROBLAZE_DCACHE_USE_WRITEBACK != 0 */

	rtsd	r15, 8
	addi	r1, r1, 4

#endif /*XPAR_MICROBLAZE_USE_MSR_INSTR == 1*/
        .end	microblaze_disable_dcache
