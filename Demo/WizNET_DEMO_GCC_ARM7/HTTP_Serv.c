/*
	FreeRTOS.org V5.0.0 - Copyright (C) 2003-2008 Richard Barry.

	This file is part of the FreeRTOS.org distribution.

	FreeRTOS.org is free software; you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation; either version 2 of the License, or
	(at your option) any later version.

	FreeRTOS.org is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with FreeRTOS.org; if not, write to the Free Software
	Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

	A special exception to the GPL can be applied should you wish to distribute
	a combined work that includes FreeRTOS.org, without being obliged to provide
	the source code for any proprietary components.  See the licensing section 
	of http://www.FreeRTOS.org for full details of how and when the exception
	can be applied.

    ***************************************************************************
    ***************************************************************************
    *                                                                         *
    * SAVE TIME AND MONEY!  We can port FreeRTOS.org to your own hardware,    *
    * and even write all or part of your application on your behalf.          *
    * See http://www.OpenRTOS.com for details of the services we provide to   *
    * expedite your project.                                                  *
    *                                                                         *
    ***************************************************************************
    ***************************************************************************

	Please ensure to read the configuration and relevant port sections of the
	online documentation.

	http://www.FreeRTOS.org - Documentation, latest information, license and 
	contact details.

	http://www.SafeRTOS.com - A version that is certified for use in safety 
	critical systems.

	http://www.OpenRTOS.com - Commercial support, development, porting, 
	licensing and training services.
*/


/* Standard includes. */
#include <stdlib.h>

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"

/* Application includes. */
#include "tcp.h"

/* Misc constants. */
#define tcpPOLL_DELAY					( ( portTickType ) 12 / portTICK_RATE_MS )
#define tcpCONNECTION_DELAY				( ( portTickType ) 8 / portTICK_RATE_MS )
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

