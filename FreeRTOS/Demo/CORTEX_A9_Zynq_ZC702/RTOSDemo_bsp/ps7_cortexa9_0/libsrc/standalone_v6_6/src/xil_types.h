/******************************************************************************
*
* Copyright (C) 2010 - 2015 Xilinx, Inc. All rights reserved.
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
* @file xil_types.h
*
* @addtogroup common_types Basic Data types for Xilinx&reg; Software IP
*
* The xil_types.h file contains basic types for Xilinx software IP. These data types
* are applicable for all processors supported by Xilinx.
* @{
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who    Date   Changes
* ----- ---- -------- -------------------------------------------------------
* 1.00a hbm  07/14/09 First release
* 3.03a sdm  05/30/11 Added Xuint64 typedef and XUINT64_MSW/XUINT64_LSW macros
* 5.00 	pkp  05/29/14 Made changes for 64 bit architecture
*	srt  07/14/14 Use standard definitions from stdint.h and stddef.h
*		      Define LONG and ULONG datatypes and mask values
* </pre>
*
******************************************************************************/

#ifndef XIL_TYPES_H	/* prevent circular inclusions */
#define XIL_TYPES_H	/* by using protection macros */

#include <stdint.h>
#include <stddef.h>

/************************** Constant Definitions *****************************/

#ifndef TRUE
#  define TRUE		1U
#endif

#ifndef FALSE
#  define FALSE		0U
#endif

#ifndef NULL
#define NULL		0U
#endif

#define XIL_COMPONENT_IS_READY     0x11111111U  /**< In device drivers, This macro will be
                                                 assigend to "IsReady" member of driver
												 instance to indicate that driver
												 instance is initialized and ready to use. */
#define XIL_COMPONENT_IS_STARTED   0x22222222U  /**< In device drivers, This macro will be assigend to
                                                 "IsStarted" member of driver instance
												 to indicate that driver instance is
												 started and it can be enabled. */

/* @name New types
 * New simple types.
 * @{
 */
#ifndef __KERNEL__
#ifndef XBASIC_TYPES_H
/*
 * guarded against xbasic_types.h.
 */
typedef uint8_t u8;
typedef uint16_t u16;
typedef uint32_t u32;
/** @}*/
#define __XUINT64__
typedef struct
{
	u32 Upper;
	u32 Lower;
} Xuint64;


/*****************************************************************************/
/**
* @brief    Return the most significant half of the 64 bit data type.
*
* @param    x is the 64 bit word.
*
* @return   The upper 32 bits of the 64 bit word.
*
******************************************************************************/
#define XUINT64_MSW(x) ((x).Upper)

/*****************************************************************************/
/**
* @brief    Return the least significant half of the 64 bit data type.
*
* @param    x is the 64 bit word.
*
* @return   The lower 32 bits of the 64 bit word.
*
******************************************************************************/
#define XUINT64_LSW(x) ((x).Lower)

#endif /* XBASIC_TYPES_H */

/*
 * xbasic_types.h does not typedef s* or u64
 */
/** @{ */
typedef char char8;
typedef int8_t s8;
typedef int16_t s16;
typedef int32_t s32;
typedef int64_t s64;
typedef uint64_t u64;
typedef int sint32;

typedef intptr_t INTPTR;
typedef uintptr_t UINTPTR;
typedef ptrdiff_t PTRDIFF;
/** @}*/
#if !defined(LONG) || !defined(ULONG)
typedef long LONG;
typedef unsigned long ULONG;
#endif

#define ULONG64_HI_MASK	0xFFFFFFFF00000000U
#define ULONG64_LO_MASK	~ULONG64_HI_MASK

#else
#include <linux/types.h>
#endif

/** @{ */
/**
 * This data type defines an interrupt handler for a device.
 * The argument points to the instance of the component
 */
typedef void (*XInterruptHandler) (void *InstancePtr);

/**
 * This data type defines an exception handler for a processor.
 * The argument points to the instance of the component
 */
typedef void (*XExceptionHandler) (void *InstancePtr);

/**
 * @brief  Returns 32-63 bits of a number.
 * @param  n : Number being accessed.
 * @return Bits 32-63 of number.
 *
 * @note    A basic shift-right of a 64- or 32-bit quantity.
 *          Use this to suppress the "right shift count >= width of type"
 *          warning when that quantity is 32-bits.
 */
#define UPPER_32_BITS(n) ((u32)(((n) >> 16) >> 16))

/**
 * @brief  Returns 0-31 bits of a number
 * @param  n : Number being accessed.
 * @return Bits 0-31 of number
 */
#define LOWER_32_BITS(n) ((u32)(n))




/************************** Constant Definitions *****************************/

#ifndef TRUE
#define TRUE		1U
#endif

#ifndef FALSE
#define FALSE		0U
#endif

#ifndef NULL
#define NULL		0U
#endif

#endif	/* end of protection macro */
/**
* @} End of "addtogroup common_types".
*/
