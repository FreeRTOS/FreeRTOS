/******************************************************************************
*
* Copyright (C) 2009 - 2014 Xilinx, Inc. All rights reserved.
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
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- -------------------------------------------------------
* 3.00a hbm  07/28/09 Initial release
* 3.00a hbm  07/21/10 Added Xil_EndianSwap32/16, Xil_Htonl/s, Xil_Ntohl/s
* 3.03a sdm  08/18/11 Added INST_SYNC and DATA_SYNC macros.
* 3.07a asa  08/31/12 Added xil_printf.h include
* 5.4   sk   01/14/16 Changed xil_io() and xil_out() functions to static inline
*                     functions.
*
* </pre>
*
* @note
*
* This file may contain architecture-dependent items.
*
******************************************************************************/

#ifndef XIL_IO_H			/* prevent circular inclusions */
#define XIL_IO_H			/* by using protection macros */

#ifdef __cplusplus
extern "C" {
#endif

/***************************** Include Files *********************************/

#include "xil_types.h"
#include "mb_interface.h"
#include "xil_printf.h"

/************************** Constant Definitions *****************************/

/**************************** Function Prototypes ****************************/

static inline u8 Xil_In8(UINTPTR Addr);
static inline u16 Xil_In16(UINTPTR Addr);
static inline u32 Xil_In32(UINTPTR Addr);

static inline void Xil_Out8(UINTPTR Addr, u8 Value);
static inline void Xil_Out16(UINTPTR Addr, u16 Value);
static inline void Xil_Out32(UINTPTR Addr, u32 Value);

/***************** Macros (Inline Functions) Definitions *********************/

/*****************************************************************************/
/**
*
* Perform an input operation for an 8-bit memory location by reading from the
* specified address and returning the value read from that address.
*
* @param	Addr contains the address to perform the input operation at.
*
* @return	The value read from the specified input address.
*
* @note		None.
*
******************************************************************************/
static inline u8 Xil_In8(UINTPTR Addr) {
	return *(volatile u8 *)Addr;
}

/*****************************************************************************/
/**
*
* Perform an input operation for a 16-bit memory location by reading from the
* specified address and returning the value read from that address.
*
* @param	Addr contains the address to perform the input operation at.
*
* @return	The value read from the specified input address.
*
* @note		None.
*
******************************************************************************/
static inline u16 Xil_In16(UINTPTR Addr) {
	return *(volatile u16 *)Addr;
}

/*****************************************************************************/
/**
*
* Performs an input operation for a 32-bit memory location by reading from the
* specified address and returning the Value read from that address.
*
* @param	Addr contains the address to perform the input operation at.
*
* @return	The value read from the specified input address.
*
* @note		None.
*
******************************************************************************/
static inline u32 Xil_In32(UINTPTR Addr) {
	return *(volatile u32 *)Addr;
}


/*****************************************************************************/
/**
*
* Perform an output operation for an 8-bit memory location by writing the
* specified value to the specified address.
*
* @param	Addr contains the address to perform the output operation at.
* @param	value contains the value to be output at the specified address.
*
* @return	None
*
* @note		None.
*
******************************************************************************/
static inline void Xil_Out8(UINTPTR Addr, u8 Value) {
	volatile u8 *LocalAddr = (u8 *)Addr;
	*LocalAddr = Value;
}

/*****************************************************************************/
/**
*
* Perform an output operation for a 16-bit memory location by writing the
* specified value to the specified address.
*
* @param	Addr contains the address to perform the output operation at.
* @param	value contains the value to be output at the specified address.
*
* @return	None
*
* @note		None.
*
******************************************************************************/
static inline void Xil_Out16(UINTPTR Addr, u16 Value) {
	volatile u16 *LocalAddr = (u16 *)Addr;
	*LocalAddr = Value;
}

/*****************************************************************************/
/**
*
* Perform an output operation for a 32-bit memory location by writing the
* specified value to the specified address.
*
* @param	addr contains the address to perform the output operation at.
* @param	value contains the value to be output at the specified address.
*
* @return	None
*
* @note		None.
*
******************************************************************************/
static inline void Xil_Out32(UINTPTR Addr, u32 Value) {
	volatile u32 *LocalAddr = (u32 *)Addr;
	*LocalAddr = Value;
}

#if defined __GNUC__
#  define INST_SYNC		mbar(0)
#  define DATA_SYNC		mbar(1)
#else
#  define INST_SYNC
#  define DATA_SYNC
#endif /* __GNUC__ */

/*
 * The following macros allow optimized I/O operations for memory mapped I/O.
 * It should be noted that macros cannot be used if synchronization of the I/O
 * operation is needed as it will likely break some code.
 */



extern u16 Xil_EndianSwap16(u16 Data);
extern u32 Xil_EndianSwap32(u32 Data);

#ifndef __LITTLE_ENDIAN__
extern u16 Xil_In16LE(UINTPTR Addr);
extern u32 Xil_In32LE(UINTPTR Addr);
extern void Xil_Out16LE(UINTPTR Addr, u16 Value);
extern void Xil_Out32LE(UINTPTR Addr, u32 Value);

/**
*
* Perform an big-endian input operation for a 16-bit memory location
* by reading from the specified address and returning the value read from
* that address.
*
* @param	addr contains the address to perform the input operation at.
*
* @return	The value read from the specified input address with the
*		proper endianness. The return value has the same endianness
*		as that of the processor, i.e. if the processor is
*		little-engian, the return value is the byte-swapped value read
*		from the address.
*
* @note		None.
*
******************************************************************************/
#define Xil_In16BE(Addr) Xil_In16((Addr))

/**
*
* Perform a big-endian input operation for a 32-bit memory location
* by reading from the specified address and returning the value read from
* that address.
*
* @param	Addr contains the address to perform the input operation at.
*
* @return	The value read from the specified input address with the
*		proper endianness. The return value has the same endianness
*		as that of the processor, i.e. if the processor is
*		little-engian, the return value is the byte-swapped value read
*		from the address.
*
*
* @note		None.
*
******************************************************************************/
#define Xil_In32BE(Addr) Xil_In32((Addr))

/*****************************************************************************/
/**
*
* Perform a big-endian output operation for a 16-bit memory location
* by writing the specified value to the specified address.
*
* @param	Addr contains the address to perform the output operation at.
* @param	Value contains the value to be output at the specified address.
*		The value has the same endianness as that of the processor.
*		If the processor is little-endian, the byte-swapped value is
*		written to the address.
*
*
* @return	None
*
* @note		None.
*
******************************************************************************/
#define Xil_Out16BE(Addr, Value) Xil_Out16((Addr), (Value))

/*****************************************************************************/
/**
*
* Perform a big-endian output operation for a 32-bit memory location
* by writing the specified value to the specified address.
*
* @param	Addr contains the address to perform the output operation at.
* @param	Value contains the value to be output at the specified address.
*		The value has the same endianness as that of the processor.
*		If the processor is little-endian, the byte-swapped value is
*		written to the address.
*
* @return	None
*
* @note		None.
*
******************************************************************************/
#define Xil_Out32BE(Addr, Value) Xil_Out32((Addr), (Value))

#define Xil_Htonl(Data) (Data)
#define Xil_Htons(Data) (Data)
#define Xil_Ntohl(Data) (Data)
#define Xil_Ntohs(Data) (Data)

#else

extern u16 Xil_In16BE(UINTPTR Addr);
extern u32 Xil_In32BE(UINTPTR Addr);
extern void Xil_Out16BE(UINTPTR Addr, u16 Value);
extern void Xil_Out32BE(UINTPTR Addr, u32 Value);

#define Xil_In16LE(Addr) Xil_In16((Addr))
#define Xil_In32LE(Addr) Xil_In32((Addr))
#define Xil_Out16LE(Addr, Value) Xil_Out16((Addr), (Value))
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
* @param	Value the 32-bit number to be converted.
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
* @param	Value the 16-bit number to be converted.
*
* @return	The converted 16-bit number in host byte order.
*
* @note		None.
*
******************************************************************************/
#define Xil_Ntohs(Data) Xil_EndianSwap16((Data))

#endif

#ifdef __cplusplus
}
#endif

#endif /* end of protection macro */
