/******************************************************************************
*
* (c) Copyright 2009-13  Xilinx, Inc. All rights reserved.
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
*******************************************************************************/
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
u8 Xil_In8(u32 Addr)
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
u16 Xil_In16(u32 Addr)
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
u32 Xil_In32(u32 Addr)
{
	return *(volatile u32 *) Addr;
}

/*****************************************************************************/
/**
*
* Performs an output operation for an 8-bit memory location by writing the
* specified Value to the the specified address.
*
* @param	OutAddress contains the address to perform the output operation
*		at.
* @param	Value contains the Value to be output at the specified address.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
void Xil_Out8(u32 OutAddress, u8 Value)
{
	*(volatile u8 *) OutAddress = Value;
}

/*****************************************************************************/
/**
*
* Performs an output operation for a 16-bit memory location by writing the
* specified Value to the the specified address.
*
* @param	OutAddress contains the address to perform the output operation
*		at.
* @param	Value contains the Value to be output at the specified address.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
void Xil_Out16(u32 OutAddress, u16 Value)
{
	*(volatile u16 *) OutAddress = Value;
}

/*****************************************************************************/
/**
*
* Performs an output operation for a 32-bit memory location by writing the
* specified Value to the the specified address.
*
* @param	OutAddress contains the address to perform the output operation
*		at.
* @param	Value contains the Value to be output at the specified address.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
void Xil_Out32(u32 OutAddress, u32 Value)
{
	*(volatile u32 *) OutAddress = Value;
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
u16 Xil_In16BE(u32 Addr)
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
u32 Xil_In32BE(u32 Addr)
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
* @param	OutAddress contains the address to perform the output operation
*		at.
* @param	Value contains the Value to be output at the specified address.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
void Xil_Out16BE(u32 OutAddress, u16 Value)
{
	u16 temp;

	temp = Xil_EndianSwap16(Value);

    Xil_Out16(OutAddress, temp);
}

/*****************************************************************************/
/**
*
* Performs an output operation for a 32-bit memory location by writing the
* specified Value to the the specified address. The Value is byte-swapped
* before being written.
*
* @param	OutAddress contains the address to perform the output operation
*		at.
* @param	Value contains the Value to be output at the specified address.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
void Xil_Out32BE(u32 OutAddress, u32 Value)
{
	u32 temp;

	temp = Xil_EndianSwap32(Value);

    Xil_Out32(OutAddress, temp);
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
