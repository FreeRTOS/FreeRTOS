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
 * @return	The endian swapped value.
 *
 */
static u16 Swap16(u16 Data)
{
	return ((Data >> 8U) & 0x00FFU) | ((Data << 8U) & 0xFF00U);
}

/**
 *
 * Endian swap a 32-bit word.
 * @param	Data is the 32-bit word to be swapped.
 * @return	The endian swapped value.
 *
 */
static u32 Swap32(u32 Data)
{
	u16 Lo16;
	u16 Hi16;

	u16 Swap16Lo;
	u16 Swap16Hi;

	Hi16 = (u16)((Data >> 16U) & 0x0000FFFFU);
	Lo16 = (u16)(Data & 0x0000FFFFU);

	Swap16Lo = Swap16(Lo16);
	Swap16Hi = Swap16(Hi16);

	return (((u32)(Swap16Lo)) << 16U) | ((u32)Swap16Hi);
}

/*****************************************************************************/
/**
*
* Perform a destructive 8-bit wide register IO test where the register is
* accessed using Xil_Out8 and Xil_In8, and comparing the reading and writing
* values.
*
* @param	Addr is a pointer to the region of memory to be tested.
* @param	Length is the Length of the block.
* @param	Value is the constant used for writting the memory.
*
* @return
*
* - -1 is returned for a failure
* - 0 is returned for a pass
*
*****************************************************************************/

s32 Xil_TestIO8(u8 *Addr, s32 Length, u8 Value)
{
	u8 ValueIn;
	s32 Index;
	s32 Status = 0;

	for (Index = 0; Index < Length; Index++) {
		Xil_Out8((INTPTR)Addr, Value);

		ValueIn = Xil_In8((INTPTR)Addr);

		if ((Value != ValueIn) && (Status == 0)) {
			Status = -1;
			break;
		}
	}
	return Status;

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
* @param	Length is the Length of the block.
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

s32 Xil_TestIO16(u16 *Addr, s32 Length, u16 Value, s32 Kind, s32 Swap)
{
	u16 *TempAddr16;
	u16 ValueIn = 0U;
	s32 Index;
	TempAddr16 = Addr;
	Xil_AssertNonvoid(TempAddr16 != NULL);

	for (Index = 0; Index < Length; Index++) {
		switch (Kind) {
		case XIL_TESTIO_LE:
			Xil_Out16LE((INTPTR)TempAddr16, Value);
			break;
		case XIL_TESTIO_BE:
			Xil_Out16BE((INTPTR)TempAddr16, Value);
			break;
		default:
			Xil_Out16((INTPTR)TempAddr16, Value);
			break;
		}

		ValueIn = Xil_In16((INTPTR)TempAddr16);

		if ((Kind != 0) && (Swap != 0)) {
			ValueIn = Swap16(ValueIn);
		}

		if (Value != ValueIn) {
			return -1;
		}

		/* second round */
		Xil_Out16((INTPTR)TempAddr16, Value);

		switch (Kind) {
		case XIL_TESTIO_LE:
			ValueIn = Xil_In16LE((INTPTR)TempAddr16);
			break;
		case XIL_TESTIO_BE:
			ValueIn = Xil_In16BE((INTPTR)TempAddr16);
			break;
		default:
			ValueIn = Xil_In16((INTPTR)TempAddr16);
			break;
		}


		if ((Kind != 0) && (Swap != 0)) {
			ValueIn = Swap16(ValueIn);
		}

		if (Value != ValueIn) {
			return -1;
		}
		TempAddr16 += sizeof(u16);
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
* @param	Length is the Length of the block.
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
s32 Xil_TestIO32(u32 *Addr, s32 Length, u32 Value, s32 Kind, s32 Swap)
{
	u32 *TempAddr;
	u32 ValueIn = 0U;
	s32 Index;
	TempAddr = Addr;
	Xil_AssertNonvoid(TempAddr != NULL);

	for (Index = 0; Index < Length; Index++) {
		switch (Kind) {
		case XIL_TESTIO_LE:
			Xil_Out32LE((INTPTR)TempAddr, Value);
			break;
		case XIL_TESTIO_BE:
			Xil_Out32BE((INTPTR)TempAddr, Value);
			break;
		default:
			Xil_Out32((INTPTR)TempAddr, Value);
			break;
		}

		ValueIn = Xil_In32((INTPTR)TempAddr);

		if ((Kind != 0) && (Swap != 0)) {
			ValueIn = Swap32(ValueIn);
		}

		if (Value != ValueIn) {
			return -1;
		}

		/* second round */
		Xil_Out32((INTPTR)TempAddr, Value);


		switch (Kind) {
		case XIL_TESTIO_LE:
			ValueIn = Xil_In32LE((INTPTR)TempAddr);
			break;
		case XIL_TESTIO_BE:
			ValueIn = Xil_In32BE((INTPTR)TempAddr);
			break;
		default:
			ValueIn = Xil_In32((INTPTR)TempAddr);
			break;
		}

		if ((Kind != 0) && (Swap != 0)) {
			ValueIn = Swap32(ValueIn);
		}

		if (Value != ValueIn) {
			return -1;
		}
		TempAddr += sizeof(u32);
	}
	return 0;
}
