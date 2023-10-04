/******************************************************************************
*
* Copyright (C) 2009 - 2018 Xilinx, Inc.  All rights reserved.
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

/* write.c -- write bytes to an output device.
 */
#ifndef UNDEFINE_FILE_OPS
#include "xil_printf.h"
#include "xparameters.h"

#ifdef __cplusplus
extern "C" {
__attribute__( ( weak ) ) sint32 _write( sint32 fd,
                                         char8 * buf,
                                         sint32 nbytes );
}
#endif

/*
 * write -- write bytes to the serial port. Ignore fd, since
 *          stdout and stderr are the same. Since we have no filesystem,
 *          open will only return an error.
 */
__attribute__( ( weak ) ) sint32 write( sint32 fd,
                                        char8 * buf,
                                        sint32 nbytes )

{
    #ifdef STDOUT_BASEADDRESS
        s32 i;
        char8 * LocalBuf = buf;

        ( void ) fd;

        for( i = 0; i < nbytes; i++ )
        {
            if( LocalBuf != NULL )
            {
                LocalBuf += i;
            }

            if( LocalBuf != NULL )
            {
                if( *LocalBuf == '\n' )
                {
                    outbyte( '\r' );
                }

                outbyte( *LocalBuf );
            }

            if( LocalBuf != NULL )
            {
                LocalBuf -= i;
            }
        }

        return( nbytes );
    #else  /* ifdef STDOUT_BASEADDRESS */
        ( void ) fd;
        ( void ) buf;
        ( void ) nbytes;
        return 0;
    #endif /* ifdef STDOUT_BASEADDRESS */
}

__attribute__( ( weak ) ) sint32 _write( sint32 fd,
                                         char8 * buf,
                                         sint32 nbytes )
{
    #if HYP_GUEST && EL1_NONSECURE && XEN_USE_PV_CONSOLE
        sint32 length;

        ( void ) fd;
        ( void ) nbytes;
        length = XPVXenConsole_Write( buf );
        return length;
    #else
        #ifdef STDOUT_BASEADDRESS
            s32 i;
            char8 * LocalBuf = buf;

            ( void ) fd;

            for( i = 0; i < nbytes; i++ )
            {
                if( LocalBuf != NULL )
                {
                    LocalBuf += i;
                }

                if( LocalBuf != NULL )
                {
                    if( *LocalBuf == '\n' )
                    {
                        outbyte( '\r' );
                    }

                    outbyte( *LocalBuf );
                }

                if( LocalBuf != NULL )
                {
                    LocalBuf -= i;
                }
            }

            return( nbytes );
        #else  /* ifdef STDOUT_BASEADDRESS */
            ( void ) fd;
            ( void ) buf;
            ( void ) nbytes;
            return 0;
        #endif /* ifdef STDOUT_BASEADDRESS */
    #endif /* if HYP_GUEST && EL1_NONSECURE && XEN_USE_PV_CONSOLE */
}
#endif /* ifndef UNDEFINE_FILE_OPS */
