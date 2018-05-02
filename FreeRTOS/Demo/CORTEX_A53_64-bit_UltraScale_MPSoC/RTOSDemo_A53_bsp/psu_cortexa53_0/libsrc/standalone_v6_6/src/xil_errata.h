/******************************************************************************
*
* Copyright (C) 2017 Xilinx, Inc.  All rights reserved.
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
* @file xil_errata.h
*
* @addtogroup a53_errata Cortex A53 64 bit Processor Errata Support
* @{
* Various ARM errata are handled in the standalone BSP. The implementation for
* errata handling follows ARM guidelines and is based on the open source Linux
* support for these errata.
*
* @note
* The errata handling is enabled by default. To disable handling of all the
* errata globally, un-define the macro ENABLE_ARM_ERRATA in xil_errata.h. To
* disable errata on a per-erratum basis, un-define relevant macros in
* xil_errata.h.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- -----------------------------------------------
* 6.4   mus  08/11/17 First release
* </pre>
*
******************************************************************************/
#ifndef XIL_ERRATA_H
#define XIL_ERRATA_H

/**
 * @name errata_definitions
 *
 * The errata conditions handled in the standalone BSP are listed below
 * @{
 */

#define ENABLE_ARM_ERRATA 1

#ifdef ENABLE_ARM_ERRATA

/**
 *  Errata No: 855873
 *  Description: An eviction might overtake a cache clean operation
 */
#define CONFIG_ARM_ERRATA_855873 1


/*@}*/
#endif  /* ENABLE_ARM_ERRATA */

#endif  /* XIL_ERRATA_H */
/**
* @} End of "addtogroup a53_errata".
*/