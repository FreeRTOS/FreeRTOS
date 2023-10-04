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
 * @file xil_cache.h
 *
 * @addtogroup a53_64_cache_apis Cortex A53 64bit Processor Cache Functions
 *
 * Cache functions provide access to cache related operations such as flush
 * and invalidate for instruction and data caches. It gives option to perform
 * the cache operations on a single cacheline, a range of memory and an entire
 * cache.
 *
 * @{
 *
 * <pre>
 * MODIFICATION HISTORY:
 *
 * Ver   Who  Date     Changes
 * ----- ---- -------- -----------------------------------------------
 * 5.00     pkp  05/29/14 First release
 * </pre>
 *
 ******************************************************************************/
#ifndef XIL_CACHE_H
    #define XIL_CACHE_H

    #include "xil_types.h"

    #ifdef __cplusplus
    extern "C" {
    #endif

/************************** Constant Definitions *****************************/
    #define L1_DATA_PREFETCH_CONTROL_MASK     0xE000
    #define L1_DATA_PREFETCH_CONTROL_SHIFT    13

/************************** Function Prototypes ******************************/
    void Xil_DCacheEnable( void );
    void Xil_DCacheDisable( void );
    void Xil_DCacheInvalidate( void );
    void Xil_DCacheInvalidateRange( INTPTR adr,
                                    INTPTR len );
    void Xil_DCacheInvalidateLine( INTPTR adr );
    void Xil_DCacheFlush( void );
    void Xil_DCacheFlushRange( INTPTR adr,
                               INTPTR len );
    void Xil_DCacheFlushLine( INTPTR adr );

    void Xil_ICacheEnable( void );
    void Xil_ICacheDisable( void );
    void Xil_ICacheInvalidate( void );
    void Xil_ICacheInvalidateRange( INTPTR adr,
                                    INTPTR len );
    void Xil_ICacheInvalidateLine( INTPTR adr );
    void Xil_ConfigureL1Prefetch( u8 num );
    #ifdef __cplusplus
}
    #endif

#endif /* ifndef XIL_CACHE_H */

/**
 * @} End of "addtogroup a53_64_cache_apis".
 */
