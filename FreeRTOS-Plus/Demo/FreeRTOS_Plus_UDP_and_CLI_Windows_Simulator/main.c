/*
    FreeRTOS V7.4.2 - Copyright (C) 2013 Real Time Engineers Ltd.

    FEATURES AND PORTS ARE ADDED TO FREERTOS ALL THE TIME.  PLEASE VISIT
    http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS tutorial books are available in pdf and paperback.        *
     *    Complete, revised, and edited pdf reference manuals are also       *
     *    available.                                                         *
     *                                                                       *
     *    Purchasing FreeRTOS documentation will not only help you, by       *
     *    ensuring you get running as quickly as possible and with an        *
     *    in-depth knowledge of how to use FreeRTOS, it will also help       *
     *    the FreeRTOS project to continue with its mission of providing     *
     *    professional grade, cross platform, de facto standard solutions    *
     *    for microcontrollers - completely free of charge!                  *
     *                                                                       *
     *    >>> See http://www.FreeRTOS.org/Documentation for details. <<<     *
     *                                                                       *
     *    Thank you for using FreeRTOS, and thank you for your support!      *
     *                                                                       *
    ***************************************************************************


    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.

    >>>>>>NOTE<<<<<< The modification to the GPL is included to allow you to
    distribute a combined work that includes FreeRTOS without being obliged to
    provide the source code for proprietary components outside of the FreeRTOS
    kernel.

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
    details. You should have received a copy of the GNU General Public License
    and the FreeRTOS license exception along with FreeRTOS; if not it can be
    viewed here: http://www.freertos.org/a00114.html and also obtained by
    writing to Real Time Engineers Ltd., contact details for whom are available
    on the FreeRTOS WEB site.

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
    including FreeRTOS+Trace - an indispensable productivity tool, and our new
    fully thread aware and reentrant UDP/IP stack.

    http://www.OpenRTOS.com - Real Time Engineers ltd license FreeRTOS to High 
    Integrity Systems, who sell the code with commercial support, 
    indemnification and middleware, under the OpenRTOS brand.
    
    http://www.SafeRTOS.com - High Integrity Systems also provide a safety 
    engineered and independently SIL3 certified version for use in safety and 
    mission critical applications that require provable dependability.
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
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_Sockets.h"
#include "SimpleClientAndServer.h"
#include "TwoEchoClients.h"
#include "UDPCommandInterpreter.h"
#include "SelectServer.h"

/* UDP command server task parameters. */
#define mainUDP_CLI_TASK_PRIORITY					( tskIDLE_PRIORITY )
#define mainUDP_CLI_PORT_NUMBER						( 5001UL )
#define mainUDP_CLI_TASK_STACK_SIZE					( configMINIMAL_STACK_SIZE )

/* Simple UDP client and server task parameters. */
#define mainSIMPLE_CLIENT_SERVER_TASK_PRIORITY		( tskIDLE_PRIORITY )
#define mainSIMPLE_CLIENT_SERVER_PORT				( 5005UL )
#define mainSIMPLE_CLIENT_SERVER_TASK_STACK_SIZE	( configMINIMAL_STACK_SIZE )

/* Select UDP server task parameters. */
#define mainSELECT_SERVER_TASK_PRIORITY				( tskIDLE_PRIORITY )
#define mainSELECT_SERVER_PORT						( 10001UL )
#define mainSELECT_SERVER_TASK_STACK_SIZE			( configMINIMAL_STACK_SIZE )

/* Echo client task parameters. */
#define mainECHO_CLIENT_TASK_STACK_SIZE 			( configMINIMAL_STACK_SIZE * 2 )
#define mainECHO_CLIENT_TASK_PRIORITY				( tskIDLE_PRIORITY + 1 )

/* Set the following constants to 1 or 0 to define which tasks to include and 
exclude. */
#define mainCREATE_UDP_CLI_TASKS					1
#define mainCREATE_SIMPLE_UDP_CLIENT_SERVER_TASKS	0
#define mainCREATE_SELECT_UDP_SERVER_TASKS			1
#define mainCREATE_UDP_ECHO_TASKS					0

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

/*-----------------------------------------------------------*/



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

void vOutputString( char *pcMessage )
{
	/* Wrap the standard windows console output (as opposed to the FreeRTOS+CLI
	console) with a mutex to ensure it can only be accessed by one task at a
	time. */
	xSemaphoreTake( xConsoleMutex, portMAX_DELAY );
		printf( pcMessage );
	xSemaphoreGive( xConsoleMutex );
}
/*-----------------------------------------------------------*/

/* Called by FreeRTOS+UDP when the network connects. */
void vApplicationIPNetworkEventHook( eIPCallbackEvent_t eNetworkEvent )
{
uint32_t ulIPAddress, ulNetMask, ulGatewayAddress, ulDNSServerAddress;
int8_t cBuffer[ 16 ];
static portBASE_TYPE xTasksAlreadyCreated = pdFALSE;

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

			#if( mainCREATE_SELECT_UDP_SERVER_TASKS == 1 )
			{
				/* Create tasks that demonstrate sending and receiving in both
				standard and zero copy mode. */
				vStartSelectUDPServerTasks( mainSELECT_SERVER_TASK_STACK_SIZE, mainSELECT_SERVER_PORT, mainSELECT_SERVER_TASK_PRIORITY );
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
		vOutputString( "IP Address: " );
		FreeRTOS_inet_ntoa( ulIPAddress, cBuffer );
		vOutputString( ( char * ) cBuffer );
		vOutputString( "\r\nSubnet Mask: " );
		FreeRTOS_inet_ntoa( ulNetMask, cBuffer );
		vOutputString( ( char * ) cBuffer );
		vOutputString( "\r\nGateway Address: " );
		FreeRTOS_inet_ntoa( ulGatewayAddress, cBuffer );
		vOutputString( ( char * ) cBuffer );
		vOutputString( "\r\nDNS Server Address: " );
		FreeRTOS_inet_ntoa( ulDNSServerAddress, cBuffer );
		vOutputString( ( char * ) cBuffer );
		vOutputString( "\r\n\r\n" );
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
			vOutputString( ( char * ) pcSuccess );
			break;

		case eInvalidChecksum :
			vOutputString( ( char * ) pcInvalidChecksum );
			break;

		case eInvalidData :
			vOutputString( ( char * ) pcInvalidData );
			break;

		default :
			/* It is not possible to get here as all enums have their own
			case. */
			break;
	}

	sprintf( ( char * ) cMessage, "identifier %d\r\n", ( int ) usIdentifier );
	vOutputString( ( char * ) cMessage );
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



