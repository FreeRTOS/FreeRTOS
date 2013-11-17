/*
    FreeRTOS V7.6.0 - Copyright (C) 2013 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that has become a de facto standard.             *
     *                                                                       *
     *    Help yourself get started quickly and support the FreeRTOS         *
     *    project by purchasing a FreeRTOS tutorial book, reference          *
     *    manual, or both from: http://www.FreeRTOS.org/Documentation        *
     *                                                                       *
     *    Thank you!                                                         *
     *                                                                       *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>!AND MODIFIED BY!<< the FreeRTOS exception.

    >>! NOTE: The modification to the GPL is included to allow you to distribute
    >>! a combined work that includes FreeRTOS without being obliged to provide
    >>! the source code for proprietary components outside of the FreeRTOS
    >>! kernel.

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available from the following
    link: http://www.freertos.org/a00114.html

    1 tab == 4 spaces!

    ***************************************************************************
     *                                                                       *
     *    Having a problem?  Start by reading the FAQ "My application does   *
     *    not run, what could be wrong?"                                     *
     *                                                                       *
     *    http://www.FreeRTOS.org/FAQHelp.html                               *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org - Documentation, books, training, latest versions,
    license and Real Time Engineers Ltd. contact details.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.OpenRTOS.com - Real Time Engineers ltd license FreeRTOS to High
    Integrity Systems to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
*/

 /******************************************************************************
 *
 * See the following URL for information on the commands defined in this file:
 * http://www.FreeRTOS.org/FreeRTOS-Plus/FreeRTOS_Plus_UDP/Embedded_Ethernet_Examples/Ethernet_Related_CLI_Commands.shtml
 *
 ******************************************************************************/


/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Standard includes. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

/* FreeRTOS+CLI includes. */
#include "FreeRTOS_CLI.h"

/* FreeRTOS+UDP includes, just to make the stats available to the CLI
commands. */
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_Sockets.h"

/*
 * Defines a command that prints out IP address information.
 */
static portBASE_TYPE prvDisplayIPConfig( int8_t *pcWriteBuffer, size_t xWriteBufferLen, const int8_t *pcCommandString );

/*
 * Defines a command that prints out the gathered demo debug stats.
 */
static portBASE_TYPE prvDisplayIPDebugStats( int8_t *pcWriteBuffer, size_t xWriteBufferLen, const int8_t *pcCommandString );

/*
 * Defines a command that sends an ICMP ping request to an IP address.
 */
static portBASE_TYPE prvPingCommand( int8_t *pcWriteBuffer, size_t xWriteBufferLen, const int8_t *pcCommandString );

/* Structure that defines the "ip-config" command line command. */
static const CLI_Command_Definition_t xIPConfig =
{
	( const int8_t * const ) "ip-config",
	( const int8_t * const ) "ip-config:\r\n Displays IP address configuration\r\n\r\n",
	prvDisplayIPConfig,
	0
};

#if configINCLUDE_DEMO_DEBUG_STATS != 0
	/* Structure that defines the "ip-debug-stats" command line command. */
	static const CLI_Command_Definition_t xIPDebugStats =
	{
		( const int8_t * const ) "ip-debug-stats", /* The command string to type. */
		( const int8_t * const ) "ip-debug-stats:\r\n Shows some IP stack stats useful for debug - an example only.\r\n\r\n",
		prvDisplayIPDebugStats, /* The function to run. */
		0 /* No parameters are expected. */
	};
#endif /* configINCLUDE_DEMO_DEBUG_STATS */

#if ipconfigSUPPORT_OUTGOING_PINGS == 1

	/* Structure that defines the "ping" command line command.  This takes an IP
	address or host name and (optionally) the number of bytes to ping as
	parameters. */
	static const CLI_Command_Definition_t xPing =
	{
		( const int8_t * const ) "ping",
		( const int8_t * const ) "ping <ipaddress> <optional:bytes to send>:\r\n for example, ping 192.168.0.3 8, or ping www.example.com\r\n\r\n",
		prvPingCommand, /* The function to run. */
		-1 /* Ping can take either one or two parameter, so the number of parameters has to be determined by the ping command implementation. */
	};

#endif /* ipconfigSUPPORT_OUTGOING_PINGS */


/*-----------------------------------------------------------*/

void vRegisterUDPCLICommands( void )
{
	/* Register all the command line commands defined immediately above. */
	FreeRTOS_CLIRegisterCommand( &xIPConfig );

	#if configINCLUDE_DEMO_DEBUG_STATS == 1
	{
		FreeRTOS_CLIRegisterCommand( &xIPDebugStats );
	}
	#endif /* configINCLUDE_DEMO_DEBUG_STATS */

	#if ipconfigSUPPORT_OUTGOING_PINGS == 1
	{
		FreeRTOS_CLIRegisterCommand( &xPing );
	}
	#endif /* ipconfigSUPPORT_OUTGOING_PINGS */
}
/*-----------------------------------------------------------*/

#if ipconfigSUPPORT_OUTGOING_PINGS == 1

	static portBASE_TYPE prvPingCommand( int8_t *pcWriteBuffer, size_t xWriteBufferLen, const int8_t *pcCommandString )
	{
	int8_t * pcParameter;
	portBASE_TYPE lParameterStringLength, xReturn;
	uint32_t ulIPAddress, ulBytesToPing;
	const uint32_t ulDefaultBytesToPing = 8UL;
	int8_t cBuffer[ 16 ];

		/* Remove compile time warnings about unused parameters, and check the
		write buffer is not NULL.  NOTE - for simplicity, this example assumes the
		write buffer length is adequate, so does not check for buffer overflows. */
		( void ) pcCommandString;
		( void ) xWriteBufferLen;
		configASSERT( pcWriteBuffer );

		/* Start with an empty string. */
		pcWriteBuffer[ 0 ] = 0x00;

		/* Obtain the number of bytes to ping. */
		pcParameter = ( int8_t * ) FreeRTOS_CLIGetParameter
									(
										pcCommandString,		/* The command string itself. */
										2,						/* Return the second parameter. */
										&lParameterStringLength	/* Store the parameter string length. */
									);

		if( pcParameter == NULL )
		{
			/* The number of bytes was not specified, so default it. */
			ulBytesToPing = ulDefaultBytesToPing;
		}
		else
		{
			ulBytesToPing = atol( ( const char * ) pcParameter );
		}

		/* Obtain the IP address string. */
		pcParameter = ( int8_t * ) FreeRTOS_CLIGetParameter
									(
										pcCommandString,		/* The command string itself. */
										1,						/* Return the first parameter. */
										&lParameterStringLength	/* Store the parameter string length. */
									);

		/* Sanity check something was returned. */
		configASSERT( pcParameter );

		/* Attempt to obtain the IP address.   If the first character is not a
		digit, assume the host name has been passed in. */
		if( ( *pcParameter >= '0' ) && ( *pcParameter <= '9' ) )
		{
			ulIPAddress = FreeRTOS_inet_addr( ( const uint8_t * ) pcParameter );
		}
		else
		{
			/* Terminate the host name. */
			pcParameter[ lParameterStringLength ] = 0x00;

			/* Attempt to resolve host. */
			ulIPAddress = FreeRTOS_gethostbyname( ( uint8_t * ) pcParameter );
		}

		/* Convert IP address, which may have come from a DNS lookup, to string. */
		FreeRTOS_inet_ntoa( ulIPAddress, ( char * ) cBuffer );

		if( ulIPAddress != 0 )
		{
			xReturn = FreeRTOS_SendPingRequest( ulIPAddress, ( uint16_t ) ulBytesToPing, portMAX_DELAY );
		}
		else
		{
			xReturn = pdFALSE;
		}

		if( xReturn == pdFALSE )
		{
			sprintf( ( char * ) pcWriteBuffer, "%s", "Could not send ping request\r\n" );
		}
		else
		{
			sprintf( ( char * ) pcWriteBuffer, "Ping sent to %s with identifier %d\r\n", cBuffer, ( int ) xReturn );
		}

		return pdFALSE;
	}
	/*-----------------------------------------------------------*/

#endif /* ipconfigSUPPORT_OUTGOING_PINGS */

#if configINCLUDE_DEMO_DEBUG_STATS != 0

	static portBASE_TYPE prvDisplayIPDebugStats( int8_t *pcWriteBuffer, size_t xWriteBufferLen, const int8_t *pcCommandString )
	{
	static portBASE_TYPE xIndex = -1;
	extern xExampleDebugStatEntry_t xIPTraceValues[];
	portBASE_TYPE xReturn;

		/* Remove compile time warnings about unused parameters, and check the
		write buffer is not NULL.  NOTE - for simplicity, this example assumes the
		write buffer length is adequate, so does not check for buffer overflows. */
		( void ) pcCommandString;
		( void ) xWriteBufferLen;
		configASSERT( pcWriteBuffer );

		xIndex++;

		if( xIndex < xExampleDebugStatEntries() )
		{
			sprintf( ( char * ) pcWriteBuffer, "%s %d\r\n", ( char * ) xIPTraceValues[ xIndex ].pucDescription, ( int ) xIPTraceValues[ xIndex ].ulData );
			xReturn = pdPASS;
		}
		else
		{
			/* Reset the index for the next time it is called. */
			xIndex = -1;

			/* Ensure nothing remains in the write buffer. */
			pcWriteBuffer[ 0 ] = 0x00;
			xReturn = pdFALSE;
		}

		return xReturn;
	}
	/*-----------------------------------------------------------*/

#endif /* configINCLUDE_DEMO_DEBUG_STATS */

static portBASE_TYPE prvDisplayIPConfig( int8_t *pcWriteBuffer, size_t xWriteBufferLen, const int8_t *pcCommandString )
{
static portBASE_TYPE xIndex = 0;
portBASE_TYPE xReturn;
uint32_t ulAddress;

	/* Remove compile time warnings about unused parameters, and check the
	write buffer is not NULL.  NOTE - for simplicity, this example assumes the
	write buffer length is adequate, so does not check for buffer overflows. */
	( void ) pcCommandString;
	( void ) xWriteBufferLen;
	configASSERT( pcWriteBuffer );

	switch( xIndex )
	{
		case 0 :
			FreeRTOS_GetAddressConfiguration( &ulAddress, NULL, NULL, NULL );
			sprintf( ( char * ) pcWriteBuffer, "\r\nIP address " );
			xReturn = pdTRUE;
			xIndex++;
			break;

		case 1 :
			FreeRTOS_GetAddressConfiguration( NULL, &ulAddress, NULL, NULL );
			sprintf( ( char * ) pcWriteBuffer, "\r\nNet mask " );
			xReturn = pdTRUE;
			xIndex++;
			break;

		case 2 :
			FreeRTOS_GetAddressConfiguration( NULL, NULL, &ulAddress, NULL );
			sprintf( ( char * ) pcWriteBuffer, "\r\nGateway address " );
			xReturn = pdTRUE;
			xIndex++;
			break;

		case 3 :
			FreeRTOS_GetAddressConfiguration( NULL, NULL, NULL, &ulAddress );
			sprintf( ( char * ) pcWriteBuffer, "\r\nDNS server address " );
			xReturn = pdTRUE;
			xIndex++;
			break;

		default :
			ulAddress = 0;
			sprintf( ( char * ) pcWriteBuffer, "\r\n\r\n" );
			xReturn = pdFALSE;
			xIndex = 0;
			break;
	}

	if( ulAddress != 0 )
	{
		FreeRTOS_inet_ntoa( ulAddress, ( ( char * ) &( pcWriteBuffer[ strlen( ( char * ) pcWriteBuffer ) ] ) ) );
	}

	return xReturn;
}
/*-----------------------------------------------------------*/

