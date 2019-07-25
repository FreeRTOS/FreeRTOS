/*
 * FreeRTOS Kernel V10.2.1
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
static BaseType_t prvDisplayIPConfig( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString );

/*
 * Defines a command that prints out the gathered demo debug stats.
 */
static BaseType_t prvDisplayIPDebugStats( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString );

/*
 * Defines a command that sends an ICMP ping request to an IP address.
 */
static BaseType_t prvPingCommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString );

/* Structure that defines the "ip-config" command line command. */
static const CLI_Command_Definition_t xIPConfig =
{
	"ip-config",
	"ip-config:\r\n Displays IP address configuration\r\n\r\n",
	prvDisplayIPConfig,
	0
};

#if configINCLUDE_DEMO_DEBUG_STATS != 0
	/* Structure that defines the "ip-debug-stats" command line command. */
	static const CLI_Command_Definition_t xIPDebugStats =
	{
		"ip-debug-stats", /* The command string to type. */
		"ip-debug-stats:\r\n Shows some IP stack stats useful for debug - an example only.\r\n\r\n",
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
		"ping",
		"ping <ipaddress> <optional:bytes to send>:\r\n for example, ping 192.168.0.3 8, or ping www.example.com\r\n\r\n",
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

	static BaseType_t prvPingCommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString )
	{
	char * pcParameter;
	BaseType_t lParameterStringLength, xReturn;
	uint32_t ulIPAddress, ulBytesToPing;
	const uint32_t ulDefaultBytesToPing = 8UL;
	char cBuffer[ 16 ];

		/* Remove compile time warnings about unused parameters, and check the
		write buffer is not NULL.  NOTE - for simplicity, this example assumes the
		write buffer length is adequate, so does not check for buffer overflows. */
		( void ) pcCommandString;
		( void ) xWriteBufferLen;
		configASSERT( pcWriteBuffer );

		/* Start with an empty string. */
		pcWriteBuffer[ 0 ] = 0x00;

		/* Obtain the number of bytes to ping. */
		pcParameter = ( char * ) FreeRTOS_CLIGetParameter
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
			ulBytesToPing = atol( pcParameter );
		}

		/* Obtain the IP address string. */
		pcParameter = ( char * ) FreeRTOS_CLIGetParameter
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
			ulIPAddress = FreeRTOS_inet_addr( pcParameter );
		}
		else
		{
			/* Terminate the host name. */
			pcParameter[ lParameterStringLength ] = 0x00;

			/* Attempt to resolve host. */
			ulIPAddress = FreeRTOS_gethostbyname( pcParameter );
		}

		/* Convert IP address, which may have come from a DNS lookup, to string. */
		FreeRTOS_inet_ntoa( ulIPAddress, cBuffer );

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
			sprintf( pcWriteBuffer, "%s", "Could not send ping request\r\n" );
		}
		else
		{
			sprintf( pcWriteBuffer, "Ping sent to %s with identifier %d\r\n", cBuffer, ( int ) xReturn );
		}

		return pdFALSE;
	}
	/*-----------------------------------------------------------*/

#endif /* ipconfigSUPPORT_OUTGOING_PINGS */

#if configINCLUDE_DEMO_DEBUG_STATS != 0

	static BaseType_t prvDisplayIPDebugStats( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString )
	{
	static BaseType_t xIndex = -1;
	extern xExampleDebugStatEntry_t xIPTraceValues[];
	BaseType_t xReturn;

		/* Remove compile time warnings about unused parameters, and check the
		write buffer is not NULL.  NOTE - for simplicity, this example assumes the
		write buffer length is adequate, so does not check for buffer overflows. */
		( void ) pcCommandString;
		( void ) xWriteBufferLen;
		configASSERT( pcWriteBuffer );

		xIndex++;

		if( xIndex < xExampleDebugStatEntries() )
		{
			sprintf( pcWriteBuffer, "%s %d\r\n", ( char * ) xIPTraceValues[ xIndex ].pucDescription, ( int ) xIPTraceValues[ xIndex ].ulData );
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

static BaseType_t prvDisplayIPConfig( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString )
{
static BaseType_t xIndex = 0;
BaseType_t xReturn;
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
			sprintf( pcWriteBuffer, "\r\nIP address " );
			xReturn = pdTRUE;
			xIndex++;
			break;

		case 1 :
			FreeRTOS_GetAddressConfiguration( NULL, &ulAddress, NULL, NULL );
			sprintf( pcWriteBuffer, "\r\nNet mask " );
			xReturn = pdTRUE;
			xIndex++;
			break;

		case 2 :
			FreeRTOS_GetAddressConfiguration( NULL, NULL, &ulAddress, NULL );
			sprintf( pcWriteBuffer, "\r\nGateway address " );
			xReturn = pdTRUE;
			xIndex++;
			break;

		case 3 :
			FreeRTOS_GetAddressConfiguration( NULL, NULL, NULL, &ulAddress );
			sprintf( pcWriteBuffer, "\r\nDNS server address " );
			xReturn = pdTRUE;
			xIndex++;
			break;

		default :
			ulAddress = 0;
			sprintf( pcWriteBuffer, "\r\n\r\n" );
			xReturn = pdFALSE;
			xIndex = 0;
			break;
	}

	if( ulAddress != 0 )
	{
		FreeRTOS_inet_ntoa( ulAddress, ( &( pcWriteBuffer[ strlen( pcWriteBuffer ) ] ) ) );
	}

	return xReturn;
}
/*-----------------------------------------------------------*/

