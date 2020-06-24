/*
 * FreeRTOS Kernel V10.3.1
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

#ifndef  configINCLUDE_TRACE_RELATED_CLI_COMMANDS
	#define configINCLUDE_TRACE_RELATED_CLI_COMMANDS 0
#endif


/*
 * Implements the run-time-stats command.
 */
static BaseType_t prvTaskStatsCommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString );

/*
 * Implements the task-stats command.
 */
static BaseType_t prvRunTimeStatsCommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString );

/*
 * Implements the echo-three-parameters command.
 */
static BaseType_t prvThreeParameterEchoCommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString );

/*
 * Implements the echo-parameters command.
 */
static BaseType_t prvParameterEchoCommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString );

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

/*
 * Implements the "trace start" and "trace stop" commands;
 */
#if configINCLUDE_TRACE_RELATED_CLI_COMMANDS == 1
	static BaseType_t prvStartStopTraceCommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString );
#endif

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

/* Structure that defines the "run-time-stats" command line command.   This
generates a table that shows how much run time each task has */
static const CLI_Command_Definition_t xRunTimeStats =
{
	"run-time-stats", /* The command string to type. */
	"run-time-stats:\r\n Displays a table showing how much processing time each FreeRTOS task has used\r\n\r\n",
	prvRunTimeStatsCommand, /* The function to run. */
	0 /* No parameters are expected. */
};

/* Structure that defines the "task-stats" command line command.  This generates
a table that gives information on each task in the system. */
static const CLI_Command_Definition_t xTaskStats =
{
	"task-stats", /* The command string to type. */
	"task-stats:\r\n Displays a table showing the state of each FreeRTOS task\r\n\r\n",
	prvTaskStatsCommand, /* The function to run. */
	0 /* No parameters are expected. */
};

/* Structure that defines the "echo_3_parameters" command line command.  This
takes exactly three parameters that the command simply echos back one at a
time. */
static const CLI_Command_Definition_t xThreeParameterEcho =
{
	"echo-3-parameters",
	"echo-3-parameters <param1> <param2> <param3>:\r\n Expects three parameters, echos each in turn\r\n\r\n",
	prvThreeParameterEchoCommand, /* The function to run. */
	3 /* Three parameters are expected, which can take any value. */
};

/* Structure that defines the "echo_parameters" command line command.  This
takes a variable number of parameters that the command simply echos back one at
a time. */
static const CLI_Command_Definition_t xParameterEcho =
{
	"echo-parameters",
	"echo-parameters <...>:\r\n Take variable number of parameters, echos each in turn\r\n\r\n",
	prvParameterEchoCommand, /* The function to run. */
	-1 /* The user can enter any number of commands. */
};

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

#if configINCLUDE_TRACE_RELATED_CLI_COMMANDS == 1
	/* Structure that defines the "trace" command line command.  This takes a single
	parameter, which can be either "start" or "stop". */
	static const CLI_Command_Definition_t xStartStopTrace =
	{
		"trace",
		"trace [start | stop]:\r\n Starts or stops a trace recording for viewing in FreeRTOS+Trace\r\n\r\n",
		prvStartStopTraceCommand, /* The function to run. */
		1 /* One parameter is expected.  Valid values are "start" and "stop". */
	};
#endif /* configINCLUDE_TRACE_RELATED_CLI_COMMANDS */

/*-----------------------------------------------------------*/

void vRegisterCLICommands( void )
{
	/* Register all the command line commands defined immediately above. */
	FreeRTOS_CLIRegisterCommand( &xTaskStats );
	FreeRTOS_CLIRegisterCommand( &xRunTimeStats );
	FreeRTOS_CLIRegisterCommand( &xThreeParameterEcho );
	FreeRTOS_CLIRegisterCommand( &xParameterEcho );
	FreeRTOS_CLIRegisterCommand( &xIPDebugStats );
	FreeRTOS_CLIRegisterCommand( &xIPConfig );

	#if ipconfigSUPPORT_OUTGOING_PINGS == 1
	{
		FreeRTOS_CLIRegisterCommand( &xPing );
	}
	#endif /* ipconfigSUPPORT_OUTGOING_PINGS */

	#if configINCLUDE_TRACE_RELATED_CLI_COMMANDS == 1
		FreeRTOS_CLIRegisterCommand( & xStartStopTrace );
	#endif
}
/*-----------------------------------------------------------*/

static BaseType_t prvTaskStatsCommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString )
{
const char *const pcHeader = "  State\tPriority\tStack\t#\r\n************************************************\r\n";
BaseType_t xSpacePadding;

	/* Remove compile time warnings about unused parameters, and check the
	write buffer is not NULL.  NOTE - for simplicity, this example assumes the
	write buffer length is adequate, so does not check for buffer overflows. */
	( void ) pcCommandString;
	( void ) xWriteBufferLen;
	configASSERT( pcWriteBuffer );

	/* Generate a table of task stats. */
	strcpy( pcWriteBuffer, "Task" );
	pcWriteBuffer += strlen( pcWriteBuffer );

	/* Pad the string "task" with however many bytes necessary to make it the
	length of a task name.  Minus three for the null terminator and half the 
	number of characters in	"Task" so the column lines up with the centre of 
	the heading. */
	for( xSpacePadding = strlen( "Task" ); xSpacePadding < ( configMAX_TASK_NAME_LEN - 3 ); xSpacePadding++ )
	{
		/* Add a space to align columns after the task's name. */
		*pcWriteBuffer = ' ';
		pcWriteBuffer++;

		/* Ensure always terminated. */
		*pcWriteBuffer = 0x00;
	}
	strcpy( pcWriteBuffer, pcHeader );
	vTaskList( pcWriteBuffer + strlen( pcHeader ) );

	/* There is no more data to return after this single string, so return
	pdFALSE. */
	return pdFALSE;
}
/*-----------------------------------------------------------*/

static BaseType_t prvRunTimeStatsCommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString )
{
const char * const pcHeader = "  Abs Time      % Time\r\n****************************************\r\n";
BaseType_t xSpacePadding;

	/* Remove compile time warnings about unused parameters, and check the
	write buffer is not NULL.  NOTE - for simplicity, this example assumes the
	write buffer length is adequate, so does not check for buffer overflows. */
	( void ) pcCommandString;
	( void ) xWriteBufferLen;
	configASSERT( pcWriteBuffer );

	/* Generate a table of task stats. */
	strcpy( pcWriteBuffer, "Task" );
	pcWriteBuffer += strlen( pcWriteBuffer );

	/* Pad the string "task" with however many bytes necessary to make it the
	length of a task name.  Minus three for the null terminator and half the 
	number of characters in	"Task" so the column lines up with the centre of 
	the heading. */
	for( xSpacePadding = strlen( "Task" ); xSpacePadding < ( configMAX_TASK_NAME_LEN - 3 ); xSpacePadding++ )
	{
		/* Add a space to align columns after the task's name. */
		*pcWriteBuffer = ' ';
		pcWriteBuffer++;

		/* Ensure always terminated. */
		*pcWriteBuffer = 0x00;
	}

	strcpy( pcWriteBuffer, pcHeader );
	vTaskGetRunTimeStats( pcWriteBuffer + strlen( pcHeader ) );

	/* There is no more data to return after this single string, so return
	pdFALSE. */
	return pdFALSE;
}
/*-----------------------------------------------------------*/

static BaseType_t prvThreeParameterEchoCommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString )
{
const char *pcParameter;
BaseType_t xParameterStringLength, xReturn;
static BaseType_t lParameterNumber = 0;

	/* Remove compile time warnings about unused parameters, and check the
	write buffer is not NULL.  NOTE - for simplicity, this example assumes the
	write buffer length is adequate, so does not check for buffer overflows. */
	( void ) pcCommandString;
	( void ) xWriteBufferLen;
	configASSERT( pcWriteBuffer );

	if( lParameterNumber == 0 )
	{
		/* The first time the function is called after the command has been
		entered just a header string is returned. */
		sprintf( pcWriteBuffer, "The three parameters were:\r\n" );

		/* Next time the function is called the first parameter will be echoed
		back. */
		lParameterNumber = 1L;

		/* There is more data to be returned as no parameters have been echoed
		back yet. */
		xReturn = pdPASS;
	}
	else
	{
		/* Obtain the parameter string. */
		pcParameter = FreeRTOS_CLIGetParameter
						(
							pcCommandString,		/* The command string itself. */
							lParameterNumber,		/* Return the next parameter. */
							&xParameterStringLength	/* Store the parameter string length. */
						);

		/* Sanity check something was returned. */
		configASSERT( pcParameter );

		/* Return the parameter string. */
		memset( pcWriteBuffer, 0x00, xWriteBufferLen );
		sprintf( pcWriteBuffer, "%d: ", ( int ) lParameterNumber );
		strncat( pcWriteBuffer, pcParameter, xParameterStringLength );
		strncat( pcWriteBuffer, "\r\n", strlen( "\r\n" ) );

		/* If this is the last of the three parameters then there are no more
		strings to return after this one. */
		if( lParameterNumber == 3L )
		{
			/* If this is the last of the three parameters then there are no more
			strings to return after this one. */
			xReturn = pdFALSE;
			lParameterNumber = 0L;
		}
		else
		{
			/* There are more parameters to return after this one. */
			xReturn = pdTRUE;
			lParameterNumber++;
		}
	}

	return xReturn;
}
/*-----------------------------------------------------------*/

static BaseType_t prvParameterEchoCommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString )
{
const char *pcParameter;
BaseType_t xParameterStringLength, xReturn;
static BaseType_t lParameterNumber = 0;

	/* Remove compile time warnings about unused parameters, and check the
	write buffer is not NULL.  NOTE - for simplicity, this example assumes the
	write buffer length is adequate, so does not check for buffer overflows. */
	( void ) pcCommandString;
	( void ) xWriteBufferLen;
	configASSERT( pcWriteBuffer );

	if( lParameterNumber == 0 )
	{
		/* The first time the function is called after the command has been
		entered just a header string is returned. */
		sprintf( pcWriteBuffer, "The parameters were:\r\n" );

		/* Next time the function is called the first parameter will be echoed
		back. */
		lParameterNumber = 1L;

		/* There is more data to be returned as no parameters have been echoed
		back yet. */
		xReturn = pdPASS;
	}
	else
	{
		/* Obtain the parameter string. */
		pcParameter = FreeRTOS_CLIGetParameter
						(
							pcCommandString,		/* The command string itself. */
							lParameterNumber,		/* Return the next parameter. */
							&xParameterStringLength	/* Store the parameter string length. */
						);

		if( pcParameter != NULL )
		{
			/* Return the parameter string. */
			memset( pcWriteBuffer, 0x00, xWriteBufferLen );
			sprintf( pcWriteBuffer, "%d: ", ( int ) lParameterNumber );
			strncat( pcWriteBuffer, pcParameter, xParameterStringLength );
			strncat( pcWriteBuffer, "\r\n", strlen( "\r\n" ) );

			/* There might be more parameters to return after this one. */
			xReturn = pdTRUE;
			lParameterNumber++;
		}
		else
		{
			/* No more parameters were found.  Make sure the write buffer does
			not contain a valid string. */
			pcWriteBuffer[ 0 ] = 0x00;

			/* No more data to return. */
			xReturn = pdFALSE;

			/* Start over the next time this command is executed. */
			lParameterNumber = 0;
		}
	}

	return xReturn;
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
			sprintf( pcWriteBuffer, "Ping sent to %s with identifier %d\r\n", cBuffer, xReturn );
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
			sprintf( pcWriteBuffer, "%s %d\r\n", xIPTraceValues[ xIndex ].pucDescription, ( int ) xIPTraceValues[ xIndex ].ulData );
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
		FreeRTOS_inet_ntoa( ulAddress,  &( pcWriteBuffer[ strlen( pcWriteBuffer ) ] ) );
	}

	return xReturn;
}
/*-----------------------------------------------------------*/

#if configINCLUDE_TRACE_RELATED_CLI_COMMANDS == 1

	static BaseType_t prvStartStopTraceCommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString )
	{
	const char *pcParameter;
	BaseType_t lParameterStringLength;

		/* Remove compile time warnings about unused parameters, and check the
		write buffer is not NULL.  NOTE - for simplicity, this example assumes the
		write buffer length is adequate, so does not check for buffer overflows. */
		( void ) pcCommandString;
		( void ) xWriteBufferLen;
		configASSERT( pcWriteBuffer );

		/* Obtain the parameter string. */
		pcParameter = FreeRTOS_CLIGetParameter
						(
							pcCommandString,		/* The command string itself. */
							1,						/* Return the first parameter. */
							&lParameterStringLength	/* Store the parameter string length. */
						);

		/* Sanity check something was returned. */
		configASSERT( pcParameter );

		/* There are only two valid parameter values. */
		if( strncmp( pcParameter, "start", strlen( "start" ) ) == 0 )
		{
			/* Start or restart the trace. */
			vTraceStop();
			vTraceClear();
			vTraceStart();

			sprintf( pcWriteBuffer, "Trace recording (re)started.\r\n" );
		}
		else if( strncmp( pcParameter, "stop", strlen( "stop" ) ) == 0 )
		{
			/* End the trace, if one is running. */
			vTraceStop();
			sprintf( pcWriteBuffer, "Stopping trace recording.\r\n" );
		}
		else
		{
			sprintf( pcWriteBuffer, "Valid parameters are 'start' and 'stop'.\r\n" );
		}

		/* There is no more data to return after this single string, so return
		pdFALSE. */
		return pdFALSE;
	}

#endif /* configINCLUDE_TRACE_RELATED_CLI_COMMANDS */
