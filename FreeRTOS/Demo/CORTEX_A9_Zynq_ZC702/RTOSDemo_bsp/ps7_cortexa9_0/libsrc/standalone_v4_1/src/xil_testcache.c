/******************************************************************************
*
* (c) Copyright 2009 Xilinx, Inc. All rights reserved.
*
* This file contains confidential and proprietary information of Xilinx, Inc.
* and is protected under U.S. and international copyright and other
* intellectual property laws.
*
* DISCLAIMER
* This disclaimer is not a license and does not grant any rights to the
* materials distributed herewith. Except as otherwise provided in a valid
* license issued to you by Xilinx, and to the maximum extent permitted by
* applicable law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND WITH ALL
* FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES AND CONDITIONS, EXPRESS,
* IMPLIED, OR STATUTORY, INCLUDING BUT NOT LIMITED TO WARRANTIES OF
* MERCHANTABILITY, NON-INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE;
* and (2) Xilinx shall not be liable (whether in contract or tort, including
* negligence, or under any other theory of liability) for any loss or damage
* of any kind or nature related to, arising under or in connection with these
* materials, including for any direct, or any indirect, special, incidental,
* or consequential loss or damage (including loss of data, profits, goodwill,
* or any type of loss or damage suffered as a result of any action brought by
* a third party) even if such damage or loss was reasonably foreseeable or
* Xilinx had been advised of the possibility of the same.
*
* CRITICAL APPLICATIONS
* Xilinx products are not designed or intended to be fail-safe, or for use in
* any application requiring fail-safe performance, such as life-support or
* safety devices or systems, Class III medical devices, nuclear facilities,
* applications related to the deployment of airbags, or any other applications
* that could lead to death, personal injury, or severe property or
* environmental damage (individually and collectively, "Critical
* Applications"). Customer assumes the sole risk and liability of any use of
* Xilinx products in Critical Applications, subject only to applicable laws
* and regulations governing limitations on product liability.
*
* THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS PART OF THIS FILE
* AT ALL TIMES.
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

static u32 Data[DATA_LENGTH] __attribute__ ((aligned(32)));

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
