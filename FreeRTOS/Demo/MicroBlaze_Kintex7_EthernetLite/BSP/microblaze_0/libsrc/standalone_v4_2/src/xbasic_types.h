/******************************************************************************
*
* Copyright (C) 2010 - 2014 Xilinx, Inc.  All rights reserved.
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
* @file xbasic_types.h
*
*
* @note  Dummy File for backwards compatibility
*

*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who    Date   Changes
* ----- ---- -------- -------------------------------------------------------
* 1.00a adk   1/31/14  Added in bsp common folder for backward compatibility
* </pre>
*
******************************************************************************/

#ifndef XBASIC_TYPES_H	/* prevent circular inclusions */
#define XBASIC_TYPES_H	/* by using protection macros */

/** @name Legacy types
 * Deprecated legacy types.
 * @{
 */
typedef unsigned char	Xuint8;		/**< unsigned 8-bit */
typedef char		Xint8;		/**< signed 8-bit */
typedef unsigned short	Xuint16;	/**< unsigned 16-bit */
typedef short		Xint16;		/**< signed 16-bit */
typedef unsigned long	Xuint32;	/**< unsigned 32-bit */
typedef long		Xint32;		/**< signed 32-bit */
typedef float		Xfloat32;	/**< 32-bit floating point */
typedef double		Xfloat64;	/**< 64-bit double precision FP */
typedef unsigned long	Xboolean;	/**< boolean (XTRUE or XFALSE) */

#if !defined __XUINT64__
typedef struct
{
	Xuint32 Upper;
	Xuint32 Lower;
} Xuint64;
#endif

/** @name New types
 * New simple types.
 * @{
 */
#ifndef __KERNEL__
#ifndef XIL_TYPES_H
typedef Xuint32         u32;
typedef Xuint16         u16;
typedef Xuint8          u8;
#endif
#else
#include <linux/types.h>
#endif

#ifndef TRUE
#  define TRUE		1
#endif

#ifndef FALSE
#  define FALSE		0
#endif

#ifndef NULL
#define NULL		0
#endif

/*
 * Xilinx NULL, TRUE and FALSE legacy support. Deprecated.
 * Please use NULL, TRUE and FALSE
 */
#define XNULL		NULL
#define XTRUE		TRUE
#define XFALSE		FALSE

/*
 * This file is deprecated and users
 * should use xil_types.h and xil_assert.h\n\r
 */
#warning  The xbasics_type.h file is deprecated and users should use xil_types.h and xil_assert.
#warning  Please refer the Standalone BSP UG647 for further details


#endif	/* end of protection macro */
