/******************************************************************************
*
* Copyright (C) 2009 - 2015 Xilinx, Inc. All rights reserved.
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
 * @file xil_testcache.h
 *
 * @addtogroup common_test_utils
 * <h2>Cache test </h2>
 * The xil_testcache.h file contains utility functions to test cache.
 *
 * @{
 * <pre>
 * Ver    Who    Date    Changes
 * ----- ---- -------- -----------------------------------------------
 * 1.00a hbm  07/29/09 First release
 * </pre>
 *
 ******************************************************************************/

#ifndef XIL_TESTCACHE_H     /* prevent circular inclusions */
    #define XIL_TESTCACHE_H /* by using protection macros */

    #include "xil_types.h"

    #ifdef __cplusplus
    extern "C" {
    #endif

    extern s32 Xil_TestDCacheRange( void );
    extern s32 Xil_TestDCacheAll( void );
    extern s32 Xil_TestICacheRange( void );
    extern s32 Xil_TestICacheAll( void );

    #ifdef __cplusplus
}
    #endif

#endif /* end of protection macro */

/**
 * @} End of "addtogroup common_test_utils".
 */
