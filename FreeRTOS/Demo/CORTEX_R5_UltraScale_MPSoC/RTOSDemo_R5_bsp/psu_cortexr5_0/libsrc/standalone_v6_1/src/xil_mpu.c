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
* @file xil_mpu.c
*
* This file provides APIs for enabling/disabling MPU and setting the memory
* attributes for sections, in the MPU translation table.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- ---------------------------------------------------
* 5.00  pkp  02/10/14 Initial version
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
#include "xil_mpu.h"
#include "xdebug.h"
/***************** Macros (Inline Functions) Definitions *********************/

/**************************** Type Definitions *******************************/

/************************** Constant Definitions *****************************/

/************************** Variable Definitions *****************************/

static const struct {
	u64 size;
	unsigned int encoding;
}region_size[] = {
	{ 0x20, REGION_32B },
	{ 0x40, REGION_64B },
	{ 0x80, REGION_128B },
	{ 0x100, REGION_256B },
	{ 0x200, REGION_512B },
	{ 0x400, REGION_1K },
	{ 0x800, REGION_2K },
	{ 0x1000, REGION_4K },
	{ 0x2000, REGION_8K },
	{ 0x4000, REGION_16K },
	{ 0x8000, REGION_32K },
	{ 0x10000, REGION_64K },
	{ 0x20000, REGION_128K },
	{ 0x40000, REGION_256K },
	{ 0x80000, REGION_512K },
	{ 0x100000, REGION_1M },
	{ 0x200000, REGION_2M },
	{ 0x400000, REGION_4M },
	{ 0x800000, REGION_8M },
	{ 0x1000000, REGION_16M },
	{ 0x2000000, REGION_32M },
	{ 0x4000000, REGION_64M },
	{ 0x8000000, REGION_128M },
	{ 0x10000000, REGION_256M },
	{ 0x20000000, REGION_512M },
	{ 0x40000000, REGION_1G },
	{ 0x80000000, REGION_2G },
	{ 0x100000000, REGION_4G },
};

/************************** Function Prototypes ******************************/

/*****************************************************************************
*
* Set the memory attributes for a section of memory with starting address addr
* of the region size 1MB having attributes attrib
*
* @param	addr is the address for which attributes are to be set.
* @param	attrib specifies the attributes for that memory region.
* @return	None.
*
*
******************************************************************************/
void Xil_SetTlbAttributes(INTPTR addr, u32 attrib)
{
	INTPTR Localaddr = addr;
	Localaddr &= (~(0xFFFFFU));
	/* Setting the MPU region with given attribute with 1MB size */
	Xil_SetMPURegion(Localaddr, 0x100000, attrib);
}

/*****************************************************************************
*
* Set the memory attributes for a section of memory with starting address addr
* of the region size size and having attributes attrib
*
* @param	addr is the address for which attributes are to be set.
* @param	size is the size of the region.
* @param	attrib specifies the attributes for that memory region.
* @return	None.
*
*
******************************************************************************/
void Xil_SetMPURegion(INTPTR addr, u64 size, u32 attrib)
{
	u32 Regionsize = 0;
	INTPTR Localaddr = addr;
	u32 NextAvailableMemRegion;
	unsigned int i;

	Xil_DCacheFlush();
	Xil_ICacheInvalidate();
	NextAvailableMemRegion = mfcp(XREG_CP15_MPU_MEMORY_REG_NUMBER);
	NextAvailableMemRegion++;
	if (NextAvailableMemRegion > 16) {
		xdbg_printf(DEBUG, "No regions available\r\n");
		return;
	}
	mtcp(XREG_CP15_MPU_MEMORY_REG_NUMBER,NextAvailableMemRegion);
	isb();

	/* Lookup the size.  */
	for (i = 0; i < sizeof region_size / sizeof region_size[0]; i++) {
		if (size <= region_size[i].size) {
			Regionsize = region_size[i].encoding;
			break;
		}
	}

	Localaddr &= ~(region_size[i].size - 1);

	Regionsize <<= 1;
	Regionsize |= REGION_EN;
	dsb();
	mtcp(XREG_CP15_MPU_REG_BASEADDR, Localaddr);	/* Set base address of a region */
	mtcp(XREG_CP15_MPU_REG_ACCESS_CTRL, attrib);	/* Set the control attribute */
	mtcp(XREG_CP15_MPU_REG_SIZE_EN, Regionsize);	/* set the region size and enable it*/
	dsb();
	isb();
}
/*****************************************************************************
*
* Enable MPU for Cortex R5 processor. This function invalidates I cache and
* flush the D Caches before enabling the MPU.
*
*
* @param	None.
* @return	None.
*
******************************************************************************/
void Xil_EnableMPU(void)
{
	u32 CtrlReg, Reg;
	s32 DCacheStatus=0, ICacheStatus=0;
	/* enable caches only if they are disabled */
	CtrlReg = mfcp(XREG_CP15_SYS_CONTROL);
	if ((CtrlReg & XREG_CP15_CONTROL_C_BIT) != 0x00000000U) {
		DCacheStatus=1;
	}
	if ((CtrlReg & XREG_CP15_CONTROL_I_BIT) != 0x00000000U) {
		ICacheStatus=1;
	}

	if(DCacheStatus != 0) {
		Xil_DCacheDisable();
	}
	if(ICacheStatus != 0){
		Xil_ICacheDisable();
	}
	Reg = mfcp(XREG_CP15_SYS_CONTROL);
	Reg |= 0x00000001U;
	dsb();
	mtcp(XREG_CP15_SYS_CONTROL, Reg);
	isb();
	/* enable caches only if they are disabled in routine*/
	if(DCacheStatus != 0) {
		Xil_DCacheEnable();
	}
	if(ICacheStatus != 0) {
		Xil_ICacheEnable();
	}
}

/*****************************************************************************
*
* Disable MPU for Cortex R5 processors. This function invalidates I cache and
* flush the D Caches before disabling the MPU.
*
* @param	None.
*
* @return	None.
*
******************************************************************************/
void Xil_DisableMPU(void)
{
	u32 CtrlReg, Reg;
	s32 DCacheStatus=0, ICacheStatus=0;
	/* enable caches only if they are disabled */
	CtrlReg = mfcp(XREG_CP15_SYS_CONTROL);
	if ((CtrlReg & XREG_CP15_CONTROL_C_BIT) != 0x00000000U) {
		DCacheStatus=1;
	}
	if ((CtrlReg & XREG_CP15_CONTROL_I_BIT) != 0x00000000U) {
		ICacheStatus=1;
	}

	if(DCacheStatus != 0) {
		Xil_DCacheDisable();
	}
	if(ICacheStatus != 0){
		Xil_ICacheDisable();
	}

	mtcp(XREG_CP15_INVAL_BRANCH_ARRAY, 0);
	Reg = mfcp(XREG_CP15_SYS_CONTROL);
	Reg &= ~(0x00000001U);
	dsb();
	mtcp(XREG_CP15_SYS_CONTROL, Reg);
	isb();
	/* enable caches only if they are disabled in routine*/
	if(DCacheStatus != 0) {
		Xil_DCacheEnable();
	}
	if(ICacheStatus != 0) {
		Xil_ICacheEnable();
	}
}