/******************************************************************************
*
* Copyright (C) 2013 - 2015 Xilinx, Inc.  All rights reserved.
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
 * @addtogroup a9_errata Cortex A9 Processor and pl310 Errata Support
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
 * 1.00a srt  04/18/13 First release
 * 6.6   mus  12/07/17 Removed errata 753970, It fixes CR#989132.
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

#define ENABLE_ARM_ERRATA    1

#ifdef ENABLE_ARM_ERRATA

/**
 *  Errata No:   742230
 *  Description: DMB operation may be faulty
 */
    #define CONFIG_ARM_ERRATA_742230    1

/**
 *  Errata No:   743622
 *  Description: Faulty hazard checking in the Store Buffer may lead
 *	             to data corruption.
 */
    #define CONFIG_ARM_ERRATA_743622    1

/**
 *  Errata No:   775420
 *  Description: A data cache maintenance operation which aborts,
 *		         might lead to deadlock
 */
    #define CONFIG_ARM_ERRATA_775420    1

/**
 *  Errata No:   794073
 *  Description: Speculative instruction fetches with MMU disabled
 *               might not comply with architectural requirements
 */
    #define CONFIG_ARM_ERRATA_794073    1


/** PL310 L2 Cache Errata */

/**
 *  Errata No:   588369
 *  Description: Clean & Invalidate maintenance operations do not
 *	             invalidate clean lines
 */
    #define CONFIG_PL310_ERRATA_588369    1

/**
 *  Errata No:   727915
 *  Description: Background Clean and Invalidate by Way operation
 *		 can cause data corruption
 */
    #define CONFIG_PL310_ERRATA_727915    1

/*@}*/
#endif /* ENABLE_ARM_ERRATA */

#endif /* XIL_ERRATA_H */

/**
 * @} End of "addtogroup a9_errata".
 */
