/******************************************************************************
*
* Copyright (C) 2007 - 2014 Xilinx, Inc.  All rights reserved.
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
* @file xio.c
*
* Contains I/O functions for memory-mapped or non-memory-mapped I/O
* architectures.  These functions encapsulate generic CPU I/O requirements.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date	 Changes
* ----- ---- -------- -------------------------------------------------------
* 1.00a rpm  11/07/03 Added InSwap/OutSwap routines for endian conversion
* 1.01a ecm  02/24/06 CR225908 corrected the extra curly braces in macros
*                     and bumped version to 1.01.a.
* 2.11a mta  03/21/07 Updated to new coding style.
*
* </pre>
*
* @note
*
* This file may contain architecture-dependent code.
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xio.h"
#include "xil_types.h"
#include "xil_assert.h"

/************************** Constant Definitions *****************************/


/**************************** Type Definitions *******************************/


/***************** Macros (Inline Functions) Definitions *********************/


/************************** Function Prototypes ******************************/


/*****************************************************************************/
/**
*
* Performs a 16-bit endian converion.
*
* @param	Source contains the value to be converted.
* @param	DestPtr contains a pointer to the location to put the
*		converted value.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
void XIo_EndianSwap16(u16 Source, u16 *DestPtr)
{
	*DestPtr = (u16) (((Source & 0xFF00) >> 8) | ((Source & 0x00FF) << 8));
}

/*****************************************************************************/
/**
*
* Performs a 32-bit endian converion.
*
* @param	Source contains the value to be converted.
* @param	DestPtr contains a pointer to the location to put the
*		converted value.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
void XIo_EndianSwap32(u32 Source, u32 *DestPtr)
{
	/* get each of the half words from the 32 bit word */

	u16 LoWord = (u16) (Source & 0x0000FFFF);
	u16 HiWord = (u16) ((Source & 0xFFFF0000) >> 16);

	/* byte swap each of the 16 bit half words */

	LoWord = (((LoWord & 0xFF00) >> 8) | ((LoWord & 0x00FF) << 8));
	HiWord = (((HiWord & 0xFF00) >> 8) | ((HiWord & 0x00FF) << 8));

	/* swap the half words before returning the value */

	*DestPtr = (u32) ((LoWord << 16) | HiWord);
}

/*****************************************************************************/
/**
*
* Performs an input operation for a 16-bit memory location by reading from the
* specified address and returning the byte-swapped value read from that
* address.
*
* @param	InAddress contains the address to perform the input
*		operation at.
*
* @return	The byte-swapped value read from the specified input address.
*
* @note		None.
*
******************************************************************************/
u16 XIo_InSwap16(XIo_Address InAddress)
{
	u16 InData;

	/* get the data then swap it */
	InData = XIo_In16(InAddress);

	return (u16) (((InData & 0xFF00) >> 8) | ((InData & 0x00FF) << 8));
}

/*****************************************************************************/
/**
*
* Performs an input operation for a 32-bit memory location by reading from the
* specified address and returning the byte-swapped value read from that
* address.
*
* @param	InAddress contains the address to perform the input
*		operation at.
*
* @return	The byte-swapped value read from the specified input address.
*
* @note		None.
*
******************************************************************************/
u32 XIo_InSwap32(XIo_Address InAddress)
{
	u32 InData;
	u32 SwapData;

	/* get the data then swap it */
	InData = XIo_In32(InAddress);
	XIo_EndianSwap32(InData, &SwapData);

	return SwapData;
}

/*****************************************************************************/
/**
*
* Performs an output operation for a 16-bit memory location by writing the
* specified value to the the specified address. The value is byte-swapped
* before being written.
*
* @param	OutAddress contains the address to perform the output
*		operation at.
* @param	Value contains the value to be output at the specified address.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
void XIo_OutSwap16(XIo_Address OutAddress, u16 Value)
{
	u16 OutData;

	/* swap the data then output it */
	OutData = (u16) (((Value & 0xFF00) >> 8) | ((Value & 0x00FF) << 8));

	XIo_Out16(OutAddress, OutData);
}

/*****************************************************************************/
/**
*
* Performs an output operation for a 32-bit memory location by writing the
* specified value to the the specified address. The value is byte-swapped
* before being written.
*
* @param	OutAddress contains the address at which the
*		output operation has to be done.
* @param	Value contains the value to be output at the specified address.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
void XIo_OutSwap32(XIo_Address OutAddress, u32 Value)
{
	u32 OutData;

	/* swap the data then output it */
	XIo_EndianSwap32(Value, &OutData);
	XIo_Out32(OutAddress, OutData);
}
