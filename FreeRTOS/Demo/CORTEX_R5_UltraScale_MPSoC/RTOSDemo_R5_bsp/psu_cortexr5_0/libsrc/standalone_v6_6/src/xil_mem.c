/******************************************************************************/

/**
 * Copyright (C) 2015 - 2016 Xilinx, Inc.  All rights reserved.
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
/****************************************************************************/

/**
 * @file xil_mem.c
 *
 * This file contains xil mem copy function to use in case of word aligned
 * data copies.
 *
 * <pre>
 * MODIFICATION HISTORY:
 *
 * Ver   Who      Date     Changes
 * ----- -------- -------- -----------------------------------------------
 * 6.1   nsk      11/07/16 First release.
 *
 * </pre>
 *
 *****************************************************************************/

/***************************** Include Files ********************************/

#include "xil_types.h"

/***************** Inline Functions Definitions ********************/
/*****************************************************************************/

/**
 * @brief       This  function copies memory from once location to other.
 *
 * @param       dst: pointer pointing to destination memory
 *
 * @param       src: pointer pointing to source memory
 *
 * @param       cnt: 32 bit length of bytes to be copied
 *
 *****************************************************************************/
void Xil_MemCpy( void * dst,
                 const void * src,
                 u32 cnt )
{
    char * d = ( char * ) ( void * ) dst;
    const char * s = src;

    while( cnt >= sizeof( int ) )
    {
        *( int * ) d = *( int * ) s;
        d += sizeof( int );
        s += sizeof( int );
        cnt -= sizeof( int );
    }

    while( ( cnt ) > 0U )
    {
        *d = *s;
        d += 1U;
        s += 1U;
        cnt -= 1U;
    }
}
