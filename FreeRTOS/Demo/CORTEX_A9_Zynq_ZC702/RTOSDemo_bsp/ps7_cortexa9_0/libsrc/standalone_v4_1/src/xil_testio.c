/******************************************************************************
*
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
*
******************************************************************************/
/*****************************************************************************/
/**
*
* @file xil_testmemend.c
*
* Contains the memory test utility functions.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver    Who    Date    Changes
* ----- ---- -------- -----------------------------------------------
* 1.00a hbm  08/25/09 First release
* </pre>
*
*****************************************************************************/

/***************************** Include Files ********************************/
#include "xil_testio.h"
#include "xil_assert.h"
#include "xil_io.h"

/************************** Constant Definitions ****************************/
/************************** Function Prototypes *****************************/



/**
 *
 * Endian swap a 16-bit word.
 * @param	Data is the 16-bit word to be swapped.
 * @return	The endian swapped valud.
 *
 */
static u16 Swap16(u16 Data)
{
	return ((Data >> 8) & 0x00FF) | ((Data << 8) & 0xFF00);
}

/**
 *
 * Endian swap a 32-bit word.
 * @param	Data is the 32-bit word to be swapped.
 * @return	The endian swapped valud.
 *
 */
static u32 Swap32(u32 Data)
{
	u16 Lo16;
	u16 Hi16;

	u16 Swap16Lo;
	u16 Swap16Hi;

	Hi16 = (u16)((Data >> 16) & 0x0000FFFF);
	Lo16 = (u16)(Data & 0x0000FFFF);

	Swap16Lo = Swap16(Lo16);
	Swap16Hi = Swap16(Hi16);

	return (((u32)(Swap16Lo)) << 16) | ((u32)Swap16Hi);
}

/*****************************************************************************/
/**
*
* Perform a destructive 8-bit wide register IO test where the register is
* accessed using Xil_Out8 and Xil_In8, and comparing the reading and writing
* values.
*
* @param	Addr is a pointer to the region of memory to be tested.
* @param	Len is the length of the block.
* @param	Value is the constant used for writting the memory.
*
* @return
*
* - -1 is returned for a failure
* - 0 is returned for a pass
*
*****************************************************************************/

int Xil_TestIO8(u8 *Addr, int Len, u8 Value)
{
	u8 ValueIn;
	int Index;

	for (Index = 0; Index < Len; Index++) {
		Xil_Out8((u32)Addr, Value);

		ValueIn = Xil_In8((u32)Addr);

		if (Value != ValueIn) {
			return -1;
		}
	}

	return 0;

}

/*****************************************************************************/
/**
*
* Perform a destructive 16-bit wide register IO test. Each location is tested
* by sequentially writing a 16-bit wide register, reading the register, and
* comparing value. This function tests three kinds of register IO functions,
* normal register IO, little-endian register IO, and big-endian register IO.
* When testing little/big-endian IO, the function performs the following
* sequence, Xil_Out16LE/Xil_Out16BE, Xil_In16, Compare In-Out values,
* Xil_Out16, Xil_In16LE/Xil_In16BE, Compare In-Out values. Whether to swap the
* read-in value before comparing is controlled by the 5th argument.
*
* @param	Addr is a pointer to the region of memory to be tested.
* @param	Len is the length of the block.
* @param	Value is the constant used for writting the memory.
* @param	Kind is the test kind. Acceptable values are:
*		XIL_TESTIO_DEFAULT, XIL_TESTIO_LE, XIL_TESTIO_BE.
* @param	Swap indicates whether to byte swap the read-in value.
*
* @return
*
* - -1 is returned for a failure
* - 0 is returned for a pass
*
*****************************************************************************/

int Xil_TestIO16(u16 *Addr, int Len, u16 Value, int Kind, int Swap)
{
	u16 ValueIn;
	int Index;

	for (Index = 0; Index < Len; Index++) {
		switch (Kind) {
		case XIL_TESTIO_LE:
			Xil_Out16LE((u32)Addr, Value);
			break;
		case XIL_TESTIO_BE:
			Xil_Out16BE((u32)Addr, Value);
			break;
		default:
			Xil_Out16((u32)Addr, Value);
			break;
		}

		ValueIn = Xil_In16((u32)Addr);

		if (Kind && Swap)
			ValueIn = Swap16(ValueIn);

		if (Value != ValueIn) {
			return -1;
		}

		/* second round */
		Xil_Out16((u32)Addr, Value);

		switch (Kind) {
		case XIL_TESTIO_LE:
			ValueIn = Xil_In16LE((u32)Addr);
			break;
		case XIL_TESTIO_BE:
			ValueIn = Xil_In16BE((u32)Addr);
			break;
		default:
			ValueIn = Xil_In16((u32)Addr);
			break;
		}


		if (Kind && Swap)
			ValueIn = Swap16(ValueIn);

		if (Value != ValueIn) {
			return -1;
		}
		Addr++;
	}

	return 0;

}


/*****************************************************************************/
/**
*
* Perform a destructive 32-bit wide register IO test. Each location is tested
* by sequentially writing a 32-bit wide regsiter, reading the register, and
* comparing value. This function tests three kinds of register IO functions,
* normal register IO, little-endian register IO, and big-endian register IO.
* When testing little/big-endian IO, the function perform the following
* sequence, Xil_Out32LE/Xil_Out32BE, Xil_In32, Compare,
* Xil_Out32, Xil_In32LE/Xil_In32BE, Compare. Whether to swap the read-in value
* before comparing is controlled by the 5th argument.
*
* @param	Addr is a pointer to the region of memory to be tested.
* @param	Len is the length of the block.
* @param	Value is the constant used for writting the memory.
* @param	Kind is the test kind. Acceptable values are:
*		XIL_TESTIO_DEFAULT, XIL_TESTIO_LE, XIL_TESTIO_BE.
* @param	Swap indicates whether to byte swap the read-in value.
*
* @return
*
* - -1 is returned for a failure
* - 0 is returned for a pass
*
*****************************************************************************/
int Xil_TestIO32(u32 *Addr, int Len, u32 Value, int Kind, int Swap)
{
	u32 ValueIn;
	int Index;

	for (Index = 0; Index < Len; Index++) {
		switch (Kind) {
		case XIL_TESTIO_LE:
			Xil_Out32LE((u32)Addr, Value);
			break;
		case XIL_TESTIO_BE:
			Xil_Out32BE((u32)Addr, Value);
			break;
		default:
			Xil_Out32((u32)Addr, Value);
			break;
		}

		ValueIn = Xil_In32((u32)Addr);

		if (Kind && Swap)
			ValueIn = Swap32(ValueIn);

		if (Value != ValueIn) {
			return -1;
		}

		/* second round */
		Xil_Out32((u32)Addr, Value);


		switch (Kind) {
		case XIL_TESTIO_LE:
			ValueIn = Xil_In32LE((u32)Addr);
			break;
		case XIL_TESTIO_BE:
			ValueIn = Xil_In32BE((u32)Addr);
			break;
		default:
			ValueIn = Xil_In32((u32)Addr);
			break;
		}

		if (Kind && Swap)
			ValueIn = Swap32(ValueIn);

		if (Value != ValueIn) {
			return -1;
		}
		Addr++;
	}
	return 0;
}

