/******************************************************************************
*
* Copyright (C) 2012 - 2015 Xilinx, Inc.  All rights reserved.
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
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- ---------------------------------------------------
* 1.00a sdm  01/12/12 Initial version
* 3.05a asa  03/10/12 Modified the Xil_EnableMMU to invalidate the caches
*		      before enabling back.
* 3.05a asa  04/15/12 Modified the Xil_SetTlbAttributes routine so that
*		      translation table and branch predictor arrays are
*		      invalidated, D-cache flushed before the attribute
*		      change is applied. This is done so that the user
*		      need not call Xil_DisableMMU before calling
*		      Xil_SetTlbAttributes.
* 3.10a  srt 04/18/13 Implemented ARM Erratas. Please refer to file
*		      'xil_errata.h' for errata description
* 3.11a  asa 09/23/13 Modified Xil_SetTlbAttributes to flush the complete
*			 D cache after the translation table update. Removed the
*			 redundant TLB invalidation in the same API at the beginning.
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
#include "xil_errata.h"

/***************** Macros (Inline Functions) Definitions *********************/

/**************************** Type Definitions *******************************/

/************************** Constant Definitions *****************************/

/************************** Variable Definitions *****************************/

extern u32 MMUTable;

/************************** Function Prototypes ******************************/

/*****************************************************************************
*
* Set the memory attributes for a section, in the translation table. Each
* section covers 1MB of memory.
*
* @param	Addr is the address for which attributes are to be set.
* @param	attrib specifies the attributes for that memory region.
*
* @return	None.
*
* @note		The MMU and D-cache need not be disabled before changing an
*		translation table attribute.
*
******************************************************************************/
void Xil_SetTlbAttributes(INTPTR Addr, u32 attrib)
{
	u32 *ptr;
	u32 section;

	section = Addr / 0x100000U;
	ptr = &MMUTable;
	ptr += section;
	if(ptr != NULL) {
		*ptr = (Addr & 0xFFF00000U) | attrib;
	}

	Xil_DCacheFlush();

	mtcp(XREG_CP15_INVAL_UTLB_UNLOCKED, 0U);
	/* Invalidate all branch predictors */
	mtcp(XREG_CP15_INVAL_BRANCH_ARRAY, 0U);

	dsb(); /* ensure completion of the BP and TLB invalidation */
    isb(); /* synchronize context on this processor */
}

/*****************************************************************************
*
* Invalidate the caches, enable MMU and D Caches for Cortex A9 processor.
*
* @param	None.
* @return	None.
*
******************************************************************************/
void Xil_EnableMMU(void)
{
	u32 Reg;
	Xil_DCacheInvalidate();
	Xil_ICacheInvalidate();

#ifdef __GNUC__
	Reg = mfcp(XREG_CP15_SYS_CONTROL);
#elif defined (__ICCARM__)
	mfcp(XREG_CP15_SYS_CONTROL, Reg);
#else
	{ volatile register u32 Cp15Reg __asm(XREG_CP15_SYS_CONTROL);
	  Reg = Cp15Reg; }
#endif
	Reg |= (u32)0x05U;
	mtcp(XREG_CP15_SYS_CONTROL, Reg);

	dsb();
	isb();
}

/*****************************************************************************
*
* Disable MMU for Cortex A9 processors. This function invalidates the TLBs,
* Branch Predictor Array and flushed the D Caches before disabling
* the MMU and D cache.
*
* @param	None.
*
* @return	None.
*
******************************************************************************/
void Xil_DisableMMU(void)
{
	u32 Reg;

	mtcp(XREG_CP15_INVAL_UTLB_UNLOCKED, 0U);
	mtcp(XREG_CP15_INVAL_BRANCH_ARRAY, 0U);
	Xil_DCacheFlush();

#ifdef __GNUC__
	Reg = mfcp(XREG_CP15_SYS_CONTROL);
#elif defined (__ICCARM__)
	mfcp(XREG_CP15_SYS_CONTROL, Reg);
#else
	{ volatile register u32 Cp15Reg __asm(XREG_CP15_SYS_CONTROL);
	  Reg = Cp15Reg; }
#endif
	Reg &= (u32)(~0x05U);
#ifdef CONFIG_ARM_ERRATA_794073
	/* Disable Branch Prediction */
	Reg &= (u32)(~0x800U);
#endif
	mtcp(XREG_CP15_SYS_CONTROL, Reg);
}
