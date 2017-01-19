/******************************************************************************
*
* Copyright (C) 2009 - 2015 Xilinx, Inc. All rights reserved.
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
*
* @file xil_testcache.c
*
* Contains utility functions to test cache.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date	 Changes
* ----- ---- -------- -------------------------------------------------------
* 1.00a hbm  07/28/09 Initial release
* 4.1   asa  05/09/14 Ensured that the address uses for cache test is aligned
*				      cache line.
* </pre>
*
* @note
*
* This file contain functions that all operate on HAL.
*
******************************************************************************/
#ifdef __ARM__
#include "xil_cache.h"
#include "xil_testcache.h"
#include "xil_types.h"
#include "xpseudo_asm.h"
#ifdef __aarch64__
#include "xreg_cortexa53.h"
#else
#include "xreg_cortexr5.h"
#endif

#include "xil_types.h"

extern void xil_printf(const char8 *ctrl1, ...);

#define DATA_LENGTH 128

#ifdef __aarch64__
static INTPTR Data[DATA_LENGTH] __attribute__ ((aligned(64)));
#else
static INTPTR Data[DATA_LENGTH] __attribute__ ((aligned(32)));
#endif

/**
* Perform DCache range related API test such as Xil_DCacheFlushRange and
* Xil_DCacheInvalidateRange. This test function writes a constant value
* to the Data array, flushes the range, writes a new value, then invalidates
* the corresponding range.
*
* @return
*
*     - 0 is returned for a pass
*     - -1 is returned for a failure
*/
s32 Xil_TestDCacheRange(void)
{
	s32 Index;
	s32 Status = 0;
	u32 CtrlReg;
	INTPTR Value;

	xil_printf("-- Cache Range Test --\n\r");

	for (Index = 0; Index < DATA_LENGTH; Index++)
		Data[Index] = 0xA0A00505;

	xil_printf("    initialize Data done:\r\n");

	Xil_DCacheFlushRange((INTPTR)Data, DATA_LENGTH * sizeof(INTPTR));

	xil_printf("    flush range done\r\n");

	dsb();
	#ifdef __aarch64__
			CtrlReg = mfcp(SCTLR_EL3);
			CtrlReg &= ~(XREG_CONTROL_DCACHE_BIT);
			mtcp(SCTLR_EL3,CtrlReg);
	#else
			CtrlReg = mfcp(XREG_CP15_SYS_CONTROL);
			CtrlReg &= ~(XREG_CP15_CONTROL_C_BIT);
			mtcp(XREG_CP15_SYS_CONTROL, CtrlReg);
	#endif
	dsb();

	Status = 0;

	for (Index = 0; Index < DATA_LENGTH; Index++) {
		Value = Data[Index];
		if (Value != 0xA0A00505) {
			Status = -1;
			xil_printf("Data[%d] = %x\r\n", Index, Value);
			break;
		}
	}

	if (!Status) {
		xil_printf("	Flush worked\r\n");
	}
	else {
		xil_printf("Error: flush dcache range not working\r\n");
	}
	dsb();
	#ifdef __aarch64__
			CtrlReg = mfcp(SCTLR_EL3);
			CtrlReg |= (XREG_CONTROL_DCACHE_BIT);
			mtcp(SCTLR_EL3,CtrlReg);
		#else
			CtrlReg = mfcp(XREG_CP15_SYS_CONTROL);
			CtrlReg |= (XREG_CP15_CONTROL_C_BIT);
			mtcp(XREG_CP15_SYS_CONTROL, CtrlReg);
		#endif
	dsb();
	for (Index = 0; Index < DATA_LENGTH; Index++)
		Data[Index] = 0xA0A0C505;



	Xil_DCacheFlushRange((INTPTR)Data, DATA_LENGTH * sizeof(INTPTR));

	for (Index = 0; Index < DATA_LENGTH; Index++)
		Data[Index] = Index + 3;

	Xil_DCacheInvalidateRange((INTPTR)Data, DATA_LENGTH * sizeof(INTPTR));

	xil_printf("    invalidate dcache range done\r\n");
	dsb();
	#ifdef __aarch64__
			CtrlReg = mfcp(SCTLR_EL3);
			CtrlReg &= ~(XREG_CONTROL_DCACHE_BIT);
			mtcp(SCTLR_EL3,CtrlReg);
	#else
			CtrlReg = mfcp(XREG_CP15_SYS_CONTROL);
			CtrlReg &= ~(XREG_CP15_CONTROL_C_BIT);
			mtcp(XREG_CP15_SYS_CONTROL, CtrlReg);
	#endif
	dsb();
	for (Index = 0; Index < DATA_LENGTH; Index++)
		Data[Index] = 0xA0A0A05;
	dsb();
	#ifdef __aarch64__
			CtrlReg = mfcp(SCTLR_EL3);
			CtrlReg |= (XREG_CONTROL_DCACHE_BIT);
			mtcp(SCTLR_EL3,CtrlReg);
	#else
			CtrlReg = mfcp(XREG_CP15_SYS_CONTROL);
			CtrlReg |= (XREG_CP15_CONTROL_C_BIT);
			mtcp(XREG_CP15_SYS_CONTROL, CtrlReg);
	#endif
	dsb();

	Status = 0;

	for (Index = 0; Index < DATA_LENGTH; Index++) {
		Value = Data[Index];
		if (Value != 0xA0A0A05) {
			Status = -1;
			xil_printf("Data[%d] = %x\r\n", Index, Value);
			break;
		}
	}


	if (!Status) {
		xil_printf("    Invalidate worked\r\n");
	}
	else {
		xil_printf("Error: Invalidate dcache range not working\r\n");
	}
	xil_printf("-- Cache Range Test Complete --\r\n");
	return Status;

}

/**
* Perform DCache all related API test such as Xil_DCacheFlush and
* Xil_DCacheInvalidate. This test function writes a constant value
* to the Data array, flushes the DCache, writes a new value, then invalidates
* the DCache.
*
* @return
*     - 0 is returned for a pass
*     - -1 is returned for a failure
*/
s32 Xil_TestDCacheAll(void)
{
	s32 Index;
	s32 Status;
	INTPTR Value;
	u32 CtrlReg;

	xil_printf("-- Cache All Test --\n\r");

	for (Index = 0; Index < DATA_LENGTH; Index++)
		Data[Index] = 0x50500A0A;
	xil_printf("    initialize Data done:\r\n");

	Xil_DCacheFlush();
	xil_printf("    flush all done\r\n");
	dsb();
	#ifdef __aarch64__
		CtrlReg = mfcp(SCTLR_EL3);
		CtrlReg &= ~(XREG_CONTROL_DCACHE_BIT);
		mtcp(SCTLR_EL3,CtrlReg);
	#else
		CtrlReg = mfcp(XREG_CP15_SYS_CONTROL);
		CtrlReg &= ~(XREG_CP15_CONTROL_C_BIT);
		mtcp(XREG_CP15_SYS_CONTROL, CtrlReg);
	#endif
	dsb();
	Status = 0;

	for (Index = 0; Index < DATA_LENGTH; Index++) {
		Value = Data[Index];

		if (Value != 0x50500A0A) {
			Status = -1;
			xil_printf("Data[%d] = %x\r\n", Index, Value);
			break;
		}
	}

	if (!Status) {
		xil_printf("    Flush all worked\r\n");
	}
	else {
		xil_printf("Error: Flush dcache all not working\r\n");
	}
	dsb();
	#ifdef __aarch64__
		CtrlReg = mfcp(SCTLR_EL3);
		CtrlReg |= (XREG_CONTROL_DCACHE_BIT);
		mtcp(SCTLR_EL3,CtrlReg);
	#else
		CtrlReg = mfcp(XREG_CP15_SYS_CONTROL);
			CtrlReg |= (XREG_CP15_CONTROL_C_BIT);
			mtcp(XREG_CP15_SYS_CONTROL, CtrlReg);
	#endif
	dsb();
	for (Index = 0; Index < DATA_LENGTH; Index++)
		Data[Index] = 0x505FFA0A;

	Xil_DCacheFlush();


	for (Index = 0; Index < DATA_LENGTH; Index++)
		Data[Index] = Index + 3;

	Xil_DCacheInvalidate();

	xil_printf("    invalidate all done\r\n");
	dsb();
	#ifdef __aarch64__
		CtrlReg = mfcp(SCTLR_EL3);
		CtrlReg &= ~(XREG_CONTROL_DCACHE_BIT);
		mtcp(SCTLR_EL3,CtrlReg);
	#else
		CtrlReg = mfcp(XREG_CP15_SYS_CONTROL);
		CtrlReg &= ~(XREG_CP15_CONTROL_C_BIT);
		mtcp(XREG_CP15_SYS_CONTROL, CtrlReg);
	#endif
	dsb();
	for (Index = 0; Index < DATA_LENGTH; Index++)
		Data[Index] = 0x50CFA0A;
	dsb();
	#ifdef __aarch64__
		CtrlReg = mfcp(SCTLR_EL3);
		CtrlReg |= (XREG_CONTROL_DCACHE_BIT);
		mtcp(SCTLR_EL3,CtrlReg);
	#else
		CtrlReg = mfcp(XREG_CP15_SYS_CONTROL);
		CtrlReg |= (XREG_CP15_CONTROL_C_BIT);
		mtcp(XREG_CP15_SYS_CONTROL, CtrlReg);
	#endif
	dsb();
	Status = 0;

	for (Index = 0; Index < DATA_LENGTH; Index++) {
		Value = Data[Index];
		if (Value != 0x50CFA0A) {
			Status = -1;
			xil_printf("Data[%d] = %x\r\n", Index, Value);
			break;
		}
	}

	if (!Status) {
		xil_printf("    Invalidate all worked\r\n");
	}
	else {
			xil_printf("Error: Invalidate dcache all not working\r\n");
	}

	xil_printf("-- DCache all Test Complete --\n\r");

	return Status;
}


/**
* Perform Xil_ICacheInvalidateRange() on a few function pointers.
*
* @return
*
*     - 0 is returned for a pass
*     The function will hang if it fails.
*/
s32 Xil_TestICacheRange(void)
{

	Xil_ICacheInvalidateRange((INTPTR)Xil_TestICacheRange, 1024);
	Xil_ICacheInvalidateRange((INTPTR)Xil_TestDCacheRange, 1024);
	Xil_ICacheInvalidateRange((INTPTR)Xil_TestDCacheAll, 1024);

	xil_printf("-- Invalidate icache range done --\r\n");

	return 0;
}

/**
* Perform Xil_ICacheInvalidate().
*
* @return
*
*     - 0 is returned for a pass
*     The function will hang if it fails.
*/
s32 Xil_TestICacheAll(void)
{
	Xil_ICacheInvalidate();
	xil_printf("-- Invalidate icache all done --\r\n");
	return 0;
}
#endif
