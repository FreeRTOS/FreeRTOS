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
*
* @file xil_io.h
*
* This file contains the interface for the general IO component, which
* encapsulates the Input/Output functions for processors that do not
* require any special I/O handling.
*
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who      Date     Changes
* ----- -------- -------- -----------------------------------------------
* 5.00 	pkp  	 02/20/14 First release
* </pre>
******************************************************************************/

#ifndef XIL_IO_H           /* prevent circular inclusions */
#define XIL_IO_H           /* by using protection macros */

#ifdef __cplusplus
extern "C" {
#endif

/***************************** Include Files *********************************/

#include "xil_types.h"
#include "xpseudo_asm.h"
#include "xil_printf.h"

/************************** Constant Definitions *****************************/

/**************************** Type Definitions *******************************/

/***************** Macros (Inline Functions) Definitions *********************/

#if defined __GNUC__
#  define SYNCHRONIZE_IO	dmb()
#  define INST_SYNC		isb()
#  define DATA_SYNC		dsb()
#else
#  define SYNCHRONIZE_IO
#  define INST_SYNC
#  define DATA_SYNC
#endif /* __GNUC__ */

/*****************************************************************************/
/**
*
* Perform an big-endian input operation for a 16-bit memory location
* by reading from the specified address and returning the Value read from
* that address.
*
* @param	Addr contains the address to perform the input operation at.
*
* @return	The Value read from the specified input address with the
*		proper endianness. The return Value has the same endianness
*		as that of the processor, i.e. if the processor is
*		little-engian, the return Value is the byte-swapped Value read
*		from the address.
*
* @note		None.
*
******************************************************************************/
#define Xil_In16LE(Addr) Xil_In16((Addr))

/*****************************************************************************/
/**
*
* Perform a big-endian input operation for a 32-bit memory location
* by reading from the specified address and returning the Value read from
* that address.
*
* @param	Addr contains the address to perform the input operation at.
*
* @return	The Value read from the specified input address with the
*		proper endianness. The return Value has the same endianness
*		as that of the processor, i.e. if the processor is
*		little-engian, the return Value is the byte-swapped Value read
*		from the address.
*
*
* @note		None.
*
******************************************************************************/
#define Xil_In32LE(Addr) Xil_In32((Addr))

/*****************************************************************************/
/**
*
* Perform a big-endian output operation for a 16-bit memory location
* by writing the specified Value to the specified address.
*
* @param	Addr contains the address to perform the output operation at.
* @param	Value contains the Value to be output at the specified address.
*		The Value has the same endianness as that of the processor.
*		If the processor is little-endian, the byte-swapped Value is
*		written to the address.
*
*
* @return	None
*
* @note		None.
*
******************************************************************************/
#define Xil_Out16LE(Addr, Value) Xil_Out16((Addr), (Value))

/*****************************************************************************/
/**
*
* Perform a big-endian output operation for a 32-bit memory location
* by writing the specified Value to the specified address.
*
* @param	Addr contains the address to perform the output operation at.
* @param	Value contains the Value to be output at the specified address.
*		The Value has the same endianness as that of the processor.
*		If the processor is little-endian, the byte-swapped Value is
*		written to the address.
*
* @return	None
*
* @note		None.
*
******************************************************************************/
#define Xil_Out32LE(Addr, Value) Xil_Out32((Addr), (Value))

/*****************************************************************************/
/**
*
* Convert a 32-bit number from host byte order to network byte order.
*
* @param	Data the 32-bit number to be converted.
*
* @return	The converted 32-bit number in network byte order.
*
* @note		None.
*
******************************************************************************/
#define Xil_Htonl(Data) Xil_EndianSwap32((Data))

/*****************************************************************************/
/**
*
* Convert a 16-bit number from host byte order to network byte order.
*
* @param	Data the 16-bit number to be converted.
*
* @return	The converted 16-bit number in network byte order.
*
* @note		None.
*
******************************************************************************/
#define Xil_Htons(Data) Xil_EndianSwap16((Data))

/*****************************************************************************/
/**
*
* Convert a 32-bit number from network byte order to host byte order.
*
* @param	Data the 32-bit number to be converted.
*
* @return	The converted 32-bit number in host byte order.
*
* @note		None.
*
******************************************************************************/
#define Xil_Ntohl(Data) Xil_EndianSwap32((Data))

/*****************************************************************************/
/**
*
* Convert a 16-bit number from network byte order to host byte order.
*
* @param	Data the 16-bit number to be converted.
*
* @return	The converted 16-bit number in host byte order.
*
* @note		None.
*
******************************************************************************/
#define Xil_Ntohs(Data) Xil_EndianSwap16((Data))

/************************** Function Prototypes ******************************/

/* The following functions allow the software to be transportable across
 * processors which may use memory mapped I/O or I/O which is mapped into a
 * seperate address space.
 */
u8 Xil_In8(INTPTR Addr);
u16 Xil_In16(INTPTR Addr);
u32 Xil_In32(INTPTR Addr);
u64 Xil_In64(INTPTR Addr);

void Xil_Out8(INTPTR Addr, u8 Value);
void Xil_Out16(INTPTR Addr, u16 Value);
void Xil_Out32(INTPTR Addr, u32 Value);
void Xil_Out64(INTPTR Addr, u64 Value);

u16 Xil_In16BE(INTPTR Addr);
u32 Xil_In32BE(INTPTR Addr);
void Xil_Out16BE(INTPTR Addr, u16 Value);
void Xil_Out32BE(INTPTR Addr, u32 Value);

u16 Xil_EndianSwap16(u16 Data);
u32 Xil_EndianSwap32(u32 Data);

#ifdef __cplusplus
}
#endif

#endif /* end of protection macro */
