/******************************************************************************
*
* Copyright (C) 2009 - 2015 Xilinx, Inc.  All rights reserved.
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
* @file xil_io.c
*
* Contains I/O functions for memory-mapped or non-memory-mapped I/O
* architectures.  These functions encapsulate Cortex A9 architecture-specific
* I/O requirements.
*
* @note
*
* This file contains architecture-dependent code.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who      Date     Changes
* ----- -------- -------- -----------------------------------------------
* 1.00a ecm/sdm  10/24/09 First release
* 3.06a sgd      05/15/12 Pointer volatile used for the all read functions
* 3.07a sgd      08/17/12 Removed barriers (SYNCHRONIZE_IO) calls.
* 3.09a sgd      02/05/13 Comments cleanup
* </pre>
******************************************************************************/


/***************************** Include Files *********************************/
#include "xil_io.h"
#include "xil_types.h"
#include "xil_assert.h"
#include "xpseudo_asm.h"
#include "xreg_cortexa9.h"

/************************** Constant Definitions *****************************/

/**************************** Type Definitions *******************************/

/***************** Macros (Inline Functions) Definitions *********************/

/************************** Function Prototypes ******************************/

/*****************************************************************************/
/**
*
* Performs an input operation for an 8-bit memory location by reading from the
* specified address and returning the Value read from that address.
*
* @param	Addr contains the address to perform the input operation
*		at.
*
* @return	The Value read from the specified input address.
*
* @note		None.
*
******************************************************************************/
u8 Xil_In8(INTPTR Addr)
{
	return *(volatile u8 *) Addr;
}

/*****************************************************************************/
/**
*
* Performs an input operation for a 16-bit memory location by reading from the
* specified address and returning the Value read from that address.
*
* @param	Addr contains the address to perform the input operation
*		at.
*
* @return	The Value read from the specified input address.
*
* @note		None.
*
******************************************************************************/
u16 Xil_In16(INTPTR Addr)
{
	return *(volatile u16 *) Addr;
}

/*****************************************************************************/
/**
*
* Performs an input operation for a 32-bit memory location by reading from the
* specified address and returning the Value read from that address.
*
* @param	Addr contains the address to perform the input operation
*		at.
*
* @return	The Value read from the specified input address.
*
* @note		None.
*
******************************************************************************/
u32 Xil_In32(UINTPTR Addr)
{
	return *(volatile u32 *) Addr;
}

/*****************************************************************************/
/**
*
* Performs an output operation for an 8-bit memory location by writing the
* specified Value to the the specified address.
*
* @param	Addr contains the address to perform the output operation
*		at.
* @param	Value contains the Value to be output at the specified address.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
void Xil_Out8(INTPTR Addr, u8 Value)
{
	volatile u8 *LocalAddr = (u8 *)Addr;
	*LocalAddr = Value;
}

/*****************************************************************************/
/**
*
* Performs an output operation for a 16-bit memory location by writing the
* specified Value to the the specified address.
*
* @param	Addr contains the address to perform the output operation
*		at.
* @param	Value contains the Value to be output at the specified address.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
void Xil_Out16(INTPTR Addr, u16 Value)
{
	volatile u16 *LocalAddr = (u16 *)Addr;
	*LocalAddr = Value;
}

/*****************************************************************************/
/**
*
* Performs an output operation for a 32-bit memory location by writing the
* specified Value to the the specified address.
*
* @param	Addr contains the address to perform the output operation
*		at.
* @param	Value contains the Value to be output at the specified address.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
void Xil_Out32(UINTPTR Addr, u32 Value)
{
	volatile u32 *LocalAddr = (u32 *)Addr;
	*LocalAddr = Value;
}

/*****************************************************************************/
/**
*
* Performs an input operation for a 16-bit memory location by reading from the
* specified address and returning the byte-swapped Value read from that
* address.
*
* @param	Addr contains the address to perform the input operation
*		at.
*
* @return	The byte-swapped Value read from the specified input address.
*
* @note		None.
*
******************************************************************************/
u16 Xil_In16BE(INTPTR Addr)
{
	u16 temp;
	u16 result;

	temp = Xil_In16(Addr);

	result = Xil_EndianSwap16(temp);

	return result;
}

/*****************************************************************************/
/**
*
* Performs an input operation for a 32-bit memory location by reading from the
* specified address and returning the byte-swapped Value read from that
* address.
*
* @param	Addr contains the address to perform the input operation
*		at.
*
* @return	The byte-swapped Value read from the specified input address.
*
* @note		None.
*
******************************************************************************/
u32 Xil_In32BE(INTPTR Addr)
{
	u32 temp;
	u32 result;

	temp = Xil_In32(Addr);

	result = Xil_EndianSwap32(temp);

	return result;
}

/*****************************************************************************/
/**
*
* Performs an output operation for a 16-bit memory location by writing the
* specified Value to the the specified address. The Value is byte-swapped
* before being written.
*
* @param	Addr contains the address to perform the output operation
*		at.
* @param	Value contains the Value to be output at the specified address.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
void Xil_Out16BE(INTPTR Addr, u16 Value)
{
	u16 temp;

	temp = Xil_EndianSwap16(Value);

    Xil_Out16(Addr, temp);
}

/*****************************************************************************/
/**
*
* Performs an output operation for a 32-bit memory location by writing the
* specified Value to the the specified address. The Value is byte-swapped
* before being written.
*
* @param	Addr contains the address to perform the output operation
*		at.
* @param	Value contains the Value to be output at the specified address.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
void Xil_Out32BE(INTPTR Addr, u32 Value)
{
	u32 temp;

	temp = Xil_EndianSwap32(Value);

    Xil_Out32(Addr, temp);
}

/*****************************************************************************/
/**
*
* Perform a 16-bit endian converion.
*
* @param	Data contains the value to be converted.
*
* @return	converted value.
*
* @note		None.
*
******************************************************************************/
u16 Xil_EndianSwap16(u16 Data)
{
	return (u16) (((Data & 0xFF00U) >> 8U) | ((Data & 0x00FFU) << 8U));
}

/*****************************************************************************/
/**
*
* Perform a 32-bit endian converion.
*
* @param	Data contains the value to be converted.
*
* @return	converted value.
*
* @note		None.
*
******************************************************************************/
u32 Xil_EndianSwap32(u32 Data)
{
	u16 LoWord;
	u16 HiWord;

	/* get each of the half words from the 32 bit word */

	LoWord = (u16) (Data & 0x0000FFFFU);
	HiWord = (u16) ((Data & 0xFFFF0000U) >> 16U);

	/* byte swap each of the 16 bit half words */

	LoWord = (((LoWord & 0xFF00U) >> 8U) | ((LoWord & 0x00FFU) << 8U));
	HiWord = (((HiWord & 0xFF00U) >> 8U) | ((HiWord & 0x00FFU) << 8U));

	/* swap the half words before returning the value */

	return ((((u32)LoWord) << (u32)16U) | (u32)HiWord);
}
