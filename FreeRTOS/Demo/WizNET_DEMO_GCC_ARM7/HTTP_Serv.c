/*
 * FreeRTOS Kernel V10.1.0
 * Copyright (C) 2017 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * http://www.FreeRTOS.org
 * http://aws.amazon.com/freertos
 *
 * 1 tab == 4 spaces!
 */


/* Standard includes. */
#include <stdlib.h>

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"

/* Application includes. */
#include "tcp.h"

/* Misc constants. */
#define tcpPOLL_DELAY					( ( TickType_t ) 12 / portTICK_PERIOD_MS )
#define tcpCONNECTION_DELAY				( ( TickType_t ) 8 / portTICK_PERIOD_MS )
/*-----------------------------------------------------------*/

/*
 * This task initialises the hardware then processes one TCP connection at a
 * time.  When an HTTP client connects we just simply send a single page then
 * disconnect - reset the socket data and wait for the next connection.
 */
void vHTTPServerTask( void *pvParameters )
{
	/* Reset the network hardware. */
	vTCPHardReset();

	/* Loop, processing connections are they arrive. */
	for( ;; )
	{
		/* Initialise the TCP interface.

		The current minimal implementation does not check for buffer overflows
		in the WIZnet hardware, so simply resets all the buffers for each
		connection - and only processes one connection at a time. */
		if( lTCPSoftReset() )
		{	  
			/* Create the socket that is going to accept incoming connections. */
			if( lTCPCreateSocket() )
			{
				/* Wait for a connection. */
				vTCPListen();

				/* Process connections as they arrive.  This function will only
				return once the connection has been closed. */
				lProcessConnection();
			}
		}

		/* If we get here then the connection completed or failed.  Wait a 
		while then try or start again. */
		vTaskDelay( tcpCONNECTION_DELAY );		
	}
}

