/******************************************************************************
*
* Copyright (C) 2014 - 2015 Xilinx, Inc. All rights reserved.
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
/*****************************************************************************/
/**
* @file xil_mmu.c
*
* This file provides APIs for enabling/disabling MMU and setting the memory
* attributes for sections, in the MMU translation table.
* MMU APIs are yet to be implemented. They are left blank to avoid any
* compilation error
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- ---------------------------------------------------
* 5.00 	pkp  05/29/14 First release
* </pre>
*
* @note
*
* None.
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xil_cache.h"
#include "xpseudo_asm.h"
#include "xil_types.h"
#include "xil_mmu.h"
#include "bspconfig.h"
/***************** Macros (Inline Functions) Definitions *********************/

/**************************** Type Definitions *******************************/

/************************** Constant Definitions *****************************/

#define BLOCK_SIZE_2MB 0x200000U
#define BLOCK_SIZE_1GB 0x40000000U
#define ADDRESS_LIMIT_4GB 0x100000000UL

/************************** Variable Definitions *****************************/

extern INTPTR MMUTableL1;
extern INTPTR MMUTableL2;

/************************** Function Prototypes ******************************/
/*****************************************************************************
*
* Set the memory attributes for a section, in the translation table.
*
* @param	addr is the address for which attributes are to be set.
* @param	attrib specifies the attributes for that memory region.
*
* @return	None.
*
* @note		The MMU and D-cache need not be disabled before changing an
*			translation table attribute.
*
******************************************************************************/

void Xil_SetTlbAttributes(INTPTR Addr, u64 attrib)
{
	INTPTR *ptr;
	INTPTR section;
	u64 block_size;
	/* if region is less than 4GB MMUTable level 2 need to be modified */
	if(Addr < ADDRESS_LIMIT_4GB){
		/* block size is 2MB for addressed < 4GB*/
		block_size = BLOCK_SIZE_2MB;
		section = Addr / block_size;
		ptr = &MMUTableL2 + section;
	}
	/* if region is greater than 4GB MMUTable level 1 need to be modified */
	else{
		/* block size is 1GB for addressed > 4GB */
		block_size = BLOCK_SIZE_1GB;
		section = Addr / block_size;
		ptr = &MMUTableL1 + section;
	}
	*ptr = (Addr & (~(block_size-1))) | attrib;

	Xil_DCacheFlush();

	mtcptlbi(ALLE3);

	dsb(); /* ensure completion of the BP and TLB invalidation */
    isb(); /* synchronize context on this processor */

}
