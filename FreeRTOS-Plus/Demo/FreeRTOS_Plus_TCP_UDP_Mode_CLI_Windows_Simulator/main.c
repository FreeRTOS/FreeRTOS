/*
 * FreeRTOS V202107.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * https://www.FreeRTOS.org
 * https://github.com/FreeRTOS
 *
 */

/* Standard includes. */
#include <stdio.h>
#include <stdint.h>

/* FreeRTOS includes. */
#include <FreeRTOS.h>
#include "task.h"
#include "queue.h"
#include "semphr.h"

/* Demo application includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "SimpleClientAndServer.h"
#include "TwoEchoClients.h"
#include "UDPCommandInterpreter.h"
#include "logging.h"

/* UDP command server task parameters. */
#define mainUDP_CLI_TASK_PRIORITY					( tskIDLE_PRIORITY )
#define mainUDP_CLI_PORT_NUMBER						( 5001UL )
#define mainUDP_CLI_TASK_STACK_SIZE					( configMINIMAL_STACK_SIZE )

/* Simple UDP client and server task parameters. */
#define mainSIMPLE_CLIENT_SERVER_TASK_PRIORITY		( tskIDLE_PRIORITY )
#define mainSIMPLE_CLIENT_SERVER_PORT				( 5005UL )
#define mainSIMPLE_CLIENT_SERVER_TASK_STACK_SIZE	( configMINIMAL_STACK_SIZE )

/* Echo client task parameters. */
#define mainECHO_CLIENT_TASK_STACK_SIZE 			( configMINIMAL_STACK_SIZE * 2 )
#define mainECHO_CLIENT_TASK_PRIORITY				( tskIDLE_PRIORITY + 1 )

/* Set the following constants to 1 or 0 to define which tasks to include and 
exclude. */
#define mainCREATE_UDP_CLI_TASKS					1
#define mainCREATE_SIMPLE_UDP_CLIENT_SERVER_TASKS	0
#define mainCREATE_UDP_ECHO_TASKS					1

/*-----------------------------------------------------------*/

/*
 * Register commands that can be used with FreeRTOS+CLI through the UDP socket.
 * The commands are defined in CLI-commands.c.
 */
extern void vRegisterCLICommands( void );

/* The default IP and MAC address used by the demo.  The address configuration
defined here will be used if ipconfigUSE_DHCP is 0, or if ipconfigUSE_DHCP is
1 but a DHCP server could not be contacted.  See the online documentation for
more information. */
static const uint8_t ucIPAddress[ 4 ] = { configIP_ADDR0, configIP_ADDR1, configIP_ADDR2, configIP_ADDR3 };
static const uint8_t ucNetMask[ 4 ] = { configNET_MASK0, configNET_MASK1, configNET_MASK2, configNET_MASK3 };
static const uint8_t ucGatewayAddress[ 4 ] = { configGATEWAY_ADDR0, configGATEWAY_ADDR1, configGATEWAY_ADDR2, configGATEWAY_ADDR3 };
static const uint8_t ucDNSServerAddress[ 4 ] = { configDNS_SERVER_ADDR0, configDNS_SERVER_ADDR1, configDNS_SERVER_ADDR2, configDNS_SERVER_ADDR3 };

/* Default MAC address configuration.  The demo creates a virtual network
connection that uses this MAC address by accessing the raw Ethernet data
to and from a real network connection on the host PC.  See the
configNETWORK_INTERFACE_TO_USE definition for information on how to configure
the real network connection to use. */
const uint8_t ucMACAddress[ 6 ] = { configMAC_ADDR0, configMAC_ADDR1, configMAC_ADDR2, configMAC_ADDR3, configMAC_ADDR4, configMAC_ADDR5 };

/* Used to guard prints to the console. */
static xSemaphoreHandle xConsoleMutex = NULL;

/* Set the following constant to pdTRUE to log using the method indicated by the
 * name of the constant, or pdFALSE to not log using the method indicated by the
 * name of the constant.  Options include to standard out (xLogToStdout), to a disk
 * file (xLogToFile), and to a UDP port (xLogToUDP).  If xLogToUDP is set to pdTRUE
 * then UDP messages are sent to the IP address configured as the echo server
 * address (see the configECHO_SERVER_ADDR0 definitions in FreeRTOSConfig.h) and
 * the port number set by configPRINT_PORT in FreeRTOSConfig.h. */
const BaseType_t xLogToStdout = pdTRUE, xLogToFile = pdFALSE, xLogToUDP = pdFALSE;

/*-----------------------------------------------------------*/

/* Define a name that will be used for LLMNR and NBNS searches. */
#define mainHOST_NAME                                 "RTOSDemo"
#define mainDEVICE_NICK_NAME                          "windows_demo"

/* Used by the pseudo random number generator. */
static UBaseType_t ulNextRand;

/******************************************************************************
 *
 * See the following web page for information on using this demo.
 * http://www.FreeRTOS.org/FreeRTOS-Plus/FreeRTOS_Plus_UDP/Embedded_Ethernet_Examples/RTOS_UDP_CLI_Windows_Simulator.shtml
 *
 ******************************************************************************/


int main( void )
{
const uint32_t ulLongTime_ms = 250UL;

	/* Create a mutex that is used to guard against the console being accessed 
	by more than one task simultaniously. */
	xConsoleMutex = xSemaphoreCreateMutex();

	/* Initialise the network interface.  Tasks that use the network are
	created in the network event hook when the network is connected and ready
	for use.  The address values passed in here are used if ipconfigUSE_DHCP is
	set to 0, or if ipconfigUSE_DHCP is set to 1 but a DHCP server cannot be
	contacted. */
	FreeRTOS_IPInit( ucIPAddress, ucNetMask, ucGatewayAddress, ucDNSServerAddress, ucMACAddress );

	/* Initialise the logging. */
	uint32_t ulLoggingIPAddress;

    ulLoggingIPAddress = FreeRTOS_inet_addr_quick( configECHO_SERVER_ADDR0,
		                                           configECHO_SERVER_ADDR1,
		                                           configECHO_SERVER_ADDR2,
		                                           configECHO_SERVER_ADDR3 );
    vLoggingInit( xLogToStdout, xLogToFile, xLogToUDP, ulLoggingIPAddress, configPRINT_PORT );


	/* Register commands with the FreeRTOS+CLI command interpreter. */
	vRegisterCLICommands();

	/* Start the RTOS scheduler. */
	vTaskStartScheduler();

	/* If all is well, the scheduler will now be running, and the following
	line will never be reached.  If the following line does execute, then
	there was insufficient FreeRTOS heap memory available for the idle and/or
	timer tasks	to be created.  See the memory management section on the
	FreeRTOS web site for more details (this is standard text that is not not
	really applicable to the Win32 simulator port). */
	for( ;; )
	{
		Sleep( ulLongTime_ms );
	}
}
/*-----------------------------------------------------------*/

void vApplicationIdleHook( void )
{
const unsigned long ulMSToSleep = 5;

	/* This function is called on each cycle of the idle task if
	configUSE_IDLE_HOOK is set to 1 in FreeRTOSConfig.h.  Sleep to reduce CPU
	load. */
	Sleep( ulMSToSleep );
}
/*-----------------------------------------------------------*/

void vAssertCalled( void )
{
const unsigned long ulLongSleep = 1000UL;
volatile uint32_t ulBlockVariable = 0UL;

	/* Setting ulBlockVariable to a non-zero value in the debugger will allow
	this function to be exited. */
	taskDISABLE_INTERRUPTS();
	{
		while( ulBlockVariable == 0UL )
		{
			Sleep( ulLongSleep );
		}
	}
	taskENABLE_INTERRUPTS();
}
/*-----------------------------------------------------------*/

/* Called by FreeRTOS+TCP when the network connects. */
void vApplicationIPNetworkEventHook( eIPCallbackEvent_t eNetworkEvent )
{
uint32_t ulIPAddress, ulNetMask, ulGatewayAddress, ulDNSServerAddress;
int8_t cBuffer[ 16 ];
static BaseType_t xTasksAlreadyCreated = pdFALSE;

	if( eNetworkEvent == eNetworkUp )
	{
		/* Create the tasks that use the IP stack if they have not already been
		created. */
		if( xTasksAlreadyCreated == pdFALSE )
		{
			#if( mainCREATE_SIMPLE_UDP_CLIENT_SERVER_TASKS == 1 )
			{
				/* Create tasks that demonstrate sending and receiving in both
				standard and zero copy mode. */
				vStartSimpleUDPClientServerTasks( mainSIMPLE_CLIENT_SERVER_TASK_STACK_SIZE, mainSIMPLE_CLIENT_SERVER_PORT, mainSIMPLE_CLIENT_SERVER_TASK_PRIORITY );
			}
			#endif /* mainCREATE_SIMPLE_UDP_CLIENT_SERVER_TASKS */

			#if( mainCREATE_UDP_ECHO_TASKS == 1 )
			{
				/* Create the tasks that transmit to and receive from a standard
				echo server (see the web documentation for this port) in both
				standard and zero copy mode. */
				vStartEchoClientTasks( mainECHO_CLIENT_TASK_STACK_SIZE, mainECHO_CLIENT_TASK_PRIORITY );
			}
			#endif /* mainCREATE_UDP_ECHO_TASKS */

			#if( mainCREATE_UDP_CLI_TASKS == 1 )
			{
				/* Create the task that handles the CLI on a UDP port.  The port number
				is set using the configUDP_CLI_PORT_NUMBER setting in FreeRTOSConfig.h. */
				vStartUDPCommandInterpreterTask( mainUDP_CLI_TASK_STACK_SIZE, mainUDP_CLI_PORT_NUMBER, mainUDP_CLI_TASK_PRIORITY );
			}
			#endif /* mainCREATE_UDP_CLI_TASKS */

			xTasksAlreadyCreated = pdTRUE;
		}

		/* Print out the network configuration, which may have come from a DHCP
		server. */
		FreeRTOS_GetAddressConfiguration( &ulIPAddress, &ulNetMask, &ulGatewayAddress, &ulDNSServerAddress );
		FreeRTOS_debug_printf( ( "IP Address: " ) );
		FreeRTOS_inet_ntoa( ulIPAddress, cBuffer );
		FreeRTOS_debug_printf( ( ( char * ) cBuffer ) );
		FreeRTOS_debug_printf( ( "\r\nSubnet Mask: " ) );
		FreeRTOS_inet_ntoa( ulNetMask, cBuffer );
		FreeRTOS_debug_printf( ( ( char * ) cBuffer ) );
		FreeRTOS_debug_printf( ( "\r\nGateway Address: " ) );
		FreeRTOS_inet_ntoa( ulGatewayAddress, cBuffer );
		FreeRTOS_debug_printf( ( ( char * ) cBuffer ) );
		FreeRTOS_debug_printf( ( "\r\nDNS Server Address: " ) );
		FreeRTOS_inet_ntoa( ulDNSServerAddress, cBuffer );
		FreeRTOS_debug_printf( ( ( char * ) cBuffer ) );
		FreeRTOS_debug_printf( ( "\r\n\r\n" ) );
	}
}
/*-----------------------------------------------------------*/

/* Called automatically when a reply to an outgoing ping is received. */
void vApplicationPingReplyHook( ePingReplyStatus_t eStatus, uint16_t usIdentifier )
{
static const uint8_t *pcSuccess = ( uint8_t * ) "Ping reply received - ";
static const uint8_t *pcInvalidChecksum = ( uint8_t * ) "Ping reply received with invalid checksum - ";
static const uint8_t *pcInvalidData = ( uint8_t * ) "Ping reply received with invalid data - ";
static uint8_t cMessage[ 50 ];


	switch( eStatus )
	{
		case eSuccess	:
			FreeRTOS_debug_printf( ( ( char * ) pcSuccess ) );
			break;

		case eInvalidChecksum :
			FreeRTOS_debug_printf( ( ( char * ) pcInvalidChecksum ) );
			break;

		case eInvalidData :
			FreeRTOS_debug_printf( ( ( char * ) pcInvalidData ) );
			break;

		default :
			/* It is not possible to get here as all enums have their own
			case. */
			break;
	}

	sprintf( ( char * ) cMessage, "identifier %d\r\n", ( int ) usIdentifier );
	FreeRTOS_debug_printf( ( ( char * ) cMessage ) );
}
/*-----------------------------------------------------------*/

void vApplicationMallocFailedHook( void )
{
	/* vApplicationMallocFailedHook() will only be called if
	configUSE_MALLOC_FAILED_HOOK is set to 1 in FreeRTOSConfig.h.  It is a hook
	function that will get called if a call to pvPortMalloc() fails.
	pvPortMalloc() is called internally by the kernel whenever a task, queue,
	timer or semaphore is created.  It is also called by various parts of the
	demo application.  If heap_1.c, heap_2.c or heap_4.c are used, then the 
	size of the heap available to pvPortMalloc() is defined by 
	configTOTAL_HEAP_SIZE in FreeRTOSConfig.h, and the xPortGetFreeHeapSize() 
	API function can be used to query the size of free heap space that remains 
	(although it does not provide information on how the remaining heap might 
	be fragmented). */
	taskDISABLE_INTERRUPTS();
	for( ;; );
}
/*-----------------------------------------------------------*/

#if ( ipconfigUSE_LLMNR != 0 ) || ( ipconfigUSE_NBNS != 0 ) || ( ipconfigDHCP_REGISTER_HOSTNAME == 1 )

    const char * pcApplicationHostnameHook( void )
    {
        /* Assign the name "FreeRTOS" to this network node.  This function will
         * be called during the DHCP: the machine will be registered with an IP
         * address plus this name. */
        return mainHOST_NAME;
    }

#endif
/*-----------------------------------------------------------*/

#if ( ipconfigUSE_LLMNR != 0 ) || ( ipconfigUSE_NBNS != 0 )

    BaseType_t xApplicationDNSQueryHook( const char * pcName )
    {
        BaseType_t xReturn;

        /* Determine if a name lookup is for this node.  Two names are given
         * to this node: that returned by pcApplicationHostnameHook() and that set
         * by mainDEVICE_NICK_NAME. */
        if( _stricmp( pcName, pcApplicationHostnameHook() ) == 0 )
        {
            xReturn = pdPASS;
        }
        else if( _stricmp( pcName, mainDEVICE_NICK_NAME ) == 0 )
        {
            xReturn = pdPASS;
        }
        else
        {
            xReturn = pdFAIL;
        }

        return xReturn;
    }

#endif /* if ( ipconfigUSE_LLMNR != 0 ) || ( ipconfigUSE_NBNS != 0 ) */
/*-----------------------------------------------------------*/

UBaseType_t uxRand( void )
{
    const uint32_t ulMultiplier = 0x015a4e35UL, ulIncrement = 1UL;

    /* Utility function to generate a pseudo random number. */

    ulNextRand = ( ulMultiplier * ulNextRand ) + ulIncrement;
    return( ( int ) ( ulNextRand >> 16UL ) & 0x7fffUL );
}


/*
 * Supply a random number to FreeRTOS+TCP stack.
 * THIS IS ONLY A DUMMY IMPLEMENTATION THAT RETURNS A PSEUDO RANDOM NUMBER
 * SO IS NOT INTENDED FOR USE IN PRODUCTION SYSTEMS.
 */
BaseType_t xApplicationGetRandomNumber( uint32_t * pulNumber )
{
    *( pulNumber ) = uxRand();
    return pdTRUE;
}
