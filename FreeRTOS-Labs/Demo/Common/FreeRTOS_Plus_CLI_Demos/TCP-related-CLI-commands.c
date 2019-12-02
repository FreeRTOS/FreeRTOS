/*
    FreeRTOS V9.0.0 - Copyright (C) 2016 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>!AND MODIFIED BY!<< the FreeRTOS exception.

    ***************************************************************************
    >>!   NOTE: The modification to the GPL is included to allow you to     !<<
    >>!   distribute a combined work that includes FreeRTOS without being   !<<
    >>!   obliged to provide the source code for proprietary components     !<<
    >>!   outside of the FreeRTOS kernel.                                   !<<
    ***************************************************************************

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available on the following
    link: http://www.freertos.org/a00114.html

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that is more than just the market leader, it     *
     *    is the industry's de facto standard.                               *
     *                                                                       *
     *    Help yourself get started quickly while simultaneously helping     *
     *    to support the FreeRTOS project by purchasing a FreeRTOS           *
     *    tutorial book, reference manual, or both:                          *
     *    http://www.FreeRTOS.org/Documentation                              *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org/FAQHelp.html - Having a problem?  Start by reading
    the FAQ page "My application does not run, what could be wrong?".  Have you
    defined configASSERT()?

    http://www.FreeRTOS.org/support - In return for receiving this top quality
    embedded software for free we request you assist our global community by
    participating in the support forum.

    http://www.FreeRTOS.org/training - Investing in training allows your team to
    be as productive as possible as early as possible.  Now you can receive
    FreeRTOS training directly from Richard Barry, CEO of Real Time Engineers
    Ltd, and the world's leading authority on the world's leading RTOS.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.FreeRTOS.org/labs - Where new FreeRTOS products go to incubate.
    Come and try FreeRTOS+TCP, our new open source TCP/IP stack for FreeRTOS.

    http://www.OpenRTOS.com - Real Time Engineers ltd. license FreeRTOS to High
    Integrity Systems ltd. to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and commercial middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
*/

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Standard includes. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

/* FreeRTOS+CLI includes. */
#include "FreeRTOS_CLI.h"

/* FreeRTOS+TCP includes, just to make the stats available to the CLI
commands. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"

/*
 * Defines a command that prints out IP address information.
 */
static BaseType_t prvDisplayIPConfig( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString );

/*
 * Defines a command that prints out the gathered demo debug stats.
 */
#if( configINCLUDE_DEMO_DEBUG_STATS != 0 )
	static BaseType_t prvDisplayIPDebugStats( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString );
#endif

/*
 * Defines a command that sends an ICMP ping request to an IP address.
 */
#if( ipconfigSUPPORT_OUTGOING_PINGS == 1 )
	static BaseType_t prvPingCommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString );
#endif

/*
 * Defines a command that calls FreeRTOS_netstat().
 */
static BaseType_t prvNetStatCommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString );

/* Structure that defines the "ip-config" command line command. */
static const CLI_Command_Definition_t xIPConfig =
{
	"ip-config",
	"\r\nip-config:\r\n Displays IP address configuration\r\n",
	prvDisplayIPConfig,
	0
};

#if( configINCLUDE_DEMO_DEBUG_STATS != 0 )
	/* Structure that defines the "ip-debug-stats" command line command. */
	static const CLI_Command_Definition_t xIPDebugStats =
	{
		"ip-debug-stats", /* The command string to type. */
		"\r\nip-debug-stats:\r\n Shows some IP stack stats useful for debug - an example only.\r\n",
		prvDisplayIPDebugStats, /* The function to run. */
		0 /* No parameters are expected. */
	};
#endif /* configINCLUDE_DEMO_DEBUG_STATS */

#if( ipconfigSUPPORT_OUTGOING_PINGS == 1 )

	/* Structure that defines the "ping" command line command.  This takes an IP
	address or host name and (optionally) the number of bytes to ping as
	parameters. */
	static const CLI_Command_Definition_t xPing =
	{
		"ping",
		"\r\nping <ipaddress> <optional:bytes to send>:\r\n for example, ping 192.168.0.3 8, or ping www.example.com\r\n",
		prvPingCommand, /* The function to run. */
		-1 /* Ping can take either one or two parameter, so the number of parameters has to be determined by the ping command implementation. */
	};

#endif /* ipconfigSUPPORT_OUTGOING_PINGS */

/* Structure that defines the "task-stats" command line command.  This generates
a table that gives information on each task in the system. */
static const CLI_Command_Definition_t xNetStats =
{
	"net-stats", /* The command string to type. */
	"\r\nnet-stats:\r\n Calls FreeRTOS_netstat()\r\n",
	prvNetStatCommand, /* The function to run. */
	0 /* No parameters are expected. */
};

/*-----------------------------------------------------------*/

void vRegisterTCPCLICommands( void )
{
	/* Register all the command line commands defined immediately above. */
	FreeRTOS_CLIRegisterCommand( &xIPConfig );

	#if( configINCLUDE_DEMO_DEBUG_STATS == 1 )
	{
		FreeRTOS_CLIRegisterCommand( &xIPDebugStats );
	}
	#endif /* configINCLUDE_DEMO_DEBUG_STATS */

	#if( ipconfigSUPPORT_OUTGOING_PINGS == 1 )
	{
		FreeRTOS_CLIRegisterCommand( &xPing );
	}
	#endif /* ipconfigSUPPORT_OUTGOING_PINGS */

	FreeRTOS_CLIRegisterCommand( &xNetStats );
}
/*-----------------------------------------------------------*/

#if( ipconfigSUPPORT_OUTGOING_PINGS == 1 )

	static BaseType_t prvPingCommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString )
	{
	char * pcParameter;
	BaseType_t lParameterStringLength, xReturn = pdFALSE;
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

		if( pcParameter != NULL )
		{
			/* Terminate the host name or IP address string. */
			pcParameter[ lParameterStringLength ] = 0x00;

			/* Attempt to obtain the IP address.   If the first character is not a
			digit, assume the host name has been passed in. */
			if( ( *pcParameter >= '0' ) && ( *pcParameter <= '9' ) )
			{
				ulIPAddress = FreeRTOS_inet_addr( pcParameter );
			}
			else
			{
				/* Attempt to resolve host. */
				ulIPAddress = FreeRTOS_gethostbyname( pcParameter );
			}

			/* Convert IP address, which may have come from a DNS lookup, to string. */
			FreeRTOS_inet_ntoa( ulIPAddress, cBuffer );

			if( ulIPAddress != 0 )
			{
				xReturn = FreeRTOS_SendPingRequest( ulIPAddress, ( uint16_t ) ulBytesToPing, portMAX_DELAY );
			}
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

#if( configINCLUDE_DEMO_DEBUG_STATS != 0 )

	static BaseType_t prvDisplayIPDebugStats( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString )
	{
	static BaseType_t xIndex = -1;
	extern ExampleDebugStatEntry_t xIPTraceValues[];
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

static BaseType_t prvNetStatCommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString )
{
	( void ) pcWriteBuffer;
	( void ) xWriteBufferLen;
	( void ) pcCommandString;

	FreeRTOS_netstat();
	snprintf( pcWriteBuffer, xWriteBufferLen, "FreeRTOS_netstat() called - output uses FreeRTOS_printf\r\n" );
	return pdFALSE;
}

