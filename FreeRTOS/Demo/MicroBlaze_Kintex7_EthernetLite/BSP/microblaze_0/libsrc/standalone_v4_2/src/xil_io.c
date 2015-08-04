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
* @file xil_io.c
*
* Contains I/O functions for memory-mapped architectures.  These functions
* encapsulate generic CPU I/O requirements.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date	 Changes
* ----- ---- -------- -------------------------------------------------------
* 3.00a hbm  07/28/09 Initial release
* 3.00a hbm  07/21/10 Added Xil_EndianSwap32/16, Xil_Htonl/s, Xil_Ntohl/s
*
* </pre>
*
* @note
*
* This file may contain architecture-dependent code.
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xil_io.h"
#include "xil_types.h"

/************************** Constant Definitions *****************************/


/**************************** Type Definitions *******************************/


/***************** Macros (Inline Functions) Definitions *********************/


/************************** Function Prototypes ******************************/



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
	return (u16) (((Data & 0xFF00) >> 8) | ((Data & 0x00FF) << 8));
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

	LoWord = (u16) (Data & 0x0000FFFF);
	HiWord = (u16) ((Data & 0xFFFF0000) >> 16);

	/* byte swap each of the 16 bit half words */

	LoWord = (((LoWord & 0xFF00) >> 8) | ((LoWord & 0x00FF) << 8));
	HiWord = (((HiWord & 0xFF00) >> 8) | ((HiWord & 0x00FF) << 8));

	/* swap the half words before returning the value */

	return (u32) ((LoWord << 16) | HiWord);
}

/*****************************************************************************/
/**
*
* Perform a little-endian input operation for a 16-bit memory location
* by reading from the specified address and returning the byte-swapped value
* read from that address.
*
* @param	Addr contains the address to perform the input operation at.
*
* @return	The value read from the specified input address with the
*		proper endianness. The return value has the same endianness
*		as that of the processor, i.e. if the processor is big-engian,
*		the return value is the byte-swapped value read from the
*		address.
*
*
* @note		None.
*
******************************************************************************/
#ifndef __LITTLE_ENDIAN__
u16 Xil_In16LE(u32 Addr)
#else
u16 Xil_In16BE(u32 Addr)
#endif
{
	u16 Value;

	/* get the data then swap it */
	Value = Xil_In16(Addr);

	return Xil_EndianSwap16(Value);
}

/*****************************************************************************/
/**
*
* Perform a little-endian input operation for a 32-bit memory location
* by reading from the specified address and returning the byte-swapped value
* read from that address.
*
* @param	Addr contains the address to perform the input operation at.
*
* @return	The value read from the specified input address with the
*		proper endianness. The return value has the same endianness
*		as that of the processor, i.e. if the processor is big-engian,
*		the return value is the byte-swapped value read from the
*		address.
*
* @note		None.
*
******************************************************************************/
#ifndef __LITTLE_ENDIAN__
u32 Xil_In32LE(u32 Addr)
#else
u32 Xil_In32BE(u32 Addr)
#endif
{
	u32 InValue;

	/* get the data then swap it */
	InValue = Xil_In32(Addr);
	return Xil_EndianSwap32(InValue);
}

/*****************************************************************************/
/**
*
* Perform a little-endian output operation for a 16-bit memory location by
* writing the specified value to the the specified address. The value is
* byte-swapped before being written.
*
* @param	Addr contains the address to perform the output operation at.
* @param	Value contains the value to be output at the specified address.
*		The value has the same endianness as that of the processor.
*		If the processor is big-endian, the byte-swapped value is
*		written to the address.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
#ifndef __LITTLE_ENDIAN__
void Xil_Out16LE(u32 Addr, u16 Value)
#else
void Xil_Out16BE(u32 Addr, u16 Value)
#endif
{
	u16 OutValue;

	/* swap the data then output it */
	OutValue = Xil_EndianSwap16(Value);

	Xil_Out16(Addr, OutValue);
}

/*****************************************************************************/
/**
*
* Perform a little-endian output operation for a 32-bit memory location
* by writing the specified value to the the specified address. The value is
* byte-swapped before being written.
*
* @param	Addr contains the address at which the output operation at.
* @param	Value contains the value to be output at the specified address.
*		The value has the same endianness as that of the processor.
*		If the processor is big-endian, the byte-swapped value is
*		written to the address.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
#ifndef __LITTLE_ENDIAN__
void Xil_Out32LE(u32 Addr, u32 Value)
#else
void Xil_Out32BE(u32 Addr, u32 Value)
#endif
{
	u32 OutValue;

	/* swap the data then output it */
	OutValue = Xil_EndianSwap32(Value);
	Xil_Out32(Addr, OutValue);
}
