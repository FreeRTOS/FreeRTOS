/******************************************************************************
*
* Copyright (C) 2009 - 2014 Xilinx, Inc.  All rights reserved.
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
#include "xil_cache.h"
#include "xil_testcache.h"

extern void xil_printf(const char *ctrl1, ...);

#define DATA_LENGTH 128

#ifdef __GNUC__
static u32 Data[DATA_LENGTH] __attribute__ ((aligned(32)));
#elif defined (__ICCARM__)
static u32 Data[DATA_LENGTH];
#else
static u32 Data[DATA_LENGTH] __attribute__ ((aligned(32)));
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
int Xil_TestDCacheRange(void)
{
	int Index;
	int Status;

	u32 Value;

	xil_printf("-- Cache Range Test --\n\r");


	for (Index = 0; Index < DATA_LENGTH; Index++)
		Data[Index] = 0xA0A00505;

	xil_printf("    initialize Data done:\r\n");

	Xil_DCacheFlushRange((u32)Data, DATA_LENGTH * sizeof(u32));

	xil_printf("    flush range done\r\n");
	for (Index = 0; Index < DATA_LENGTH; Index++)
		Data[Index] = Index + 3;

	Xil_DCacheInvalidateRange((u32)Data, DATA_LENGTH * sizeof(u32));

	xil_printf("    invalidate dcache range done\r\n");

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
int Xil_TestDCacheAll(void)
{
	int Index;
	int Status;
	u32 Value;

	xil_printf("-- Cache All Test --\n\r");


	for (Index = 0; Index < DATA_LENGTH; Index++)
		Data[Index] = 0x50500A0A;

	xil_printf("    initialize Data done:\r\n");

	Xil_DCacheFlush();

	xil_printf("    flush all done\r\n");

	for (Index = 0; Index < DATA_LENGTH; Index++)
		Data[Index] = Index + 3;

	Xil_DCacheInvalidate();

	xil_printf("    invalidate all done\r\n");

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
int Xil_TestICacheRange(void)
{

	Xil_ICacheInvalidateRange((u32)Xil_TestICacheRange, 1024);
	Xil_ICacheInvalidateRange((u32)Xil_TestDCacheRange, 1024);
	Xil_ICacheInvalidateRange((u32)Xil_TestDCacheAll, 1024);

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
int Xil_TestICacheAll(void)
{
	Xil_ICacheInvalidate();
	xil_printf("-- Invalidate icache all done --\r\n");
	return 0;
}
