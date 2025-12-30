/* run-xenbus-read-test
 *
 * Copyright (C) 2025 Advanced Micro Devices, Inc. or its affiliates. All Rights Reserved.
 *
 * SPDX-License-Identifier: MIT
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 *
 */

#include "FreeRTOS.h"
#include "FreeRTOS_CLI.h"
#include "stdint.h"
#include "string.h"
#include "stdlib.h"
#include "stdio.h"
#include "cli.h"
#include "task.h"
#include <xen/event_channel.h>
#include <hypervisor.h>
#include <events.h>
#include <xenbus.h>

char xenbus_readpath[256];

void cliXenBusReadTask( char* path  )
{
    char *res, *msg;
    msg = xenbus_read(0, path, &res);
    if ( msg )
    {
	    printk("Error in xenbus read: %s\n", msg);
            free(msg);
    } else {
	    printk("\n\n");
	    printk("Read %s : \"%s\"\n", path, res);
	    free(res);
    }
}

static BaseType_t prvXenBusRead( char * pcWriteBuffer,
                                           size_t xWriteBufferLen,
                                           const char * pcCommandString )
{
    memset( pcWriteBuffer, 0x00, xWriteBufferLen );
    const char * pcParameter;
    BaseType_t xParameterStringLength, xReturn;
    static UBaseType_t uxParameterNumber = 0;
    if( uxParameterNumber == 0 )
    {
        uxParameterNumber = 1U;
        xReturn = 1;
    }
    else
    {
        pcParameter = FreeRTOS_CLIGetParameter(pcCommandString, uxParameterNumber, &xParameterStringLength);

        if( pcParameter != NULL )
        {
            printk("Sending Read Request\n");
            strncpy(xenbus_readpath,pcParameter,256);
            cliXenBusReadTask(xenbus_readpath);
            uxParameterNumber = 0;
            return 0;
        }
        else
        {
            snprintf(pcWriteBuffer,xWriteBufferLen,"\nPath must be specified\n");
            xReturn = 0;
            uxParameterNumber = 0;
        }
    }
    return xReturn;
}


static const CLI_Command_Definition_t xXenBusRead =
{
    "xenbus-read",
    "\r\nxenbus-read <path>:\r\n Read xenstore path\r\n\r\n",
    prvXenBusRead, /* The function to run. */
    1
};

void register_xenbus_read_test(void) {
    FreeRTOS_CLIRegisterCommand( &xXenBusRead );
}


