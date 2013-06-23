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
#include <string.h>
#include <stdio.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "timers.h"
#include "queue.h"

/* FreeRTOS+UDP includes. */
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_Sockets.h"

/* Example includes. */
#include "TwoEchoClients.h"
#include "CDCCommandConsole.h"

/* Library includes. */
#include "LPC18xx.h"

/* The size of the stack and the priority used by the two echo client tasks. */
#define mainECHO_CLIENT_TASK_STACK_SIZE 	( configMINIMAL_STACK_SIZE * 2 )
#define mainECHO_CLIENT_TASK_PRIORITY		( tskIDLE_PRIORITY + 1 )

/* The size of the stack and the priority used by the USB CDC command console
task. */
#define mainCDC_COMMAND_CONSOLE_STACK_SIZE		( configMINIMAL_STACK_SIZE * 2 )
#define mainCDC_COMMAND_CONSOLE_TASK_PRIORITY	( 4U )

/*
* Register commands that can be used with FreeRTOS+CLI.  The commands are
* defined in CLI-commands.c.
*/
extern void vRegisterCLICommands( void );

/*
 * Initialise the LED ports, and create a timer that periodically toggles an LED
 * just to provide a visual indication that the program is running.
 */
extern void vLEDsInitialise( void );

/*-----------------------------------------------------------*/

/* The default IP and MAC address used by the demo.  The address configuration
defined here will be used if ipconfigUSE_DHCP is 0, or if ipconfigUSE_DHCP is
1 but a DHCP server could not be contacted.  See the online documentation for
more information. */
static const uint8_t ucIPAddress[ 4 ] = { configIP_ADDR0, configIP_ADDR1, configIP_ADDR2, configIP_ADDR3 };
static const uint8_t ucNetMask[ 4 ] = { configNET_MASK0, configNET_MASK1, configNET_MASK2, configNET_MASK3 };
static const uint8_t ucGatewayAddress[ 4 ] = { configGATEWAY_ADDR0, configGATEWAY_ADDR1, configGATEWAY_ADDR2, configGATEWAY_ADDR3 };
static const uint8_t ucDNSServerAddress[ 4 ] = { configDNS_SERVER_ADDR0, configDNS_SERVER_ADDR1, configDNS_SERVER_ADDR2, configDNS_SERVER_ADDR3 };

/* The MAC address used by the demo.  In production units the MAC address would
probably be read from flash memory or an EEPROM.  Here it is just hard coded. */
const uint8_t ucMACAddress[ 6 ] = { configMAC_ADDR0, configMAC_ADDR1, configMAC_ADDR2, configMAC_ADDR3, configMAC_ADDR4, configMAC_ADDR5 };

/*-----------------------------------------------------------*/


/******************************************************************************
 *
 * See the following web page for information on using this demo.
 * http://www.FreeRTOS.org/FreeRTOS-Plus/FreeRTOS_Plus_UDP/Embedded_Ethernet_Examples/RTOS_UDP_and_CLI_LPC1830_NGX.shtml
 *
 ******************************************************************************/


int main( void )
{
	/* Prepare the trace recorder library. */
	#if configINCLUDE_TRACE_RELATED_CLI_COMMANDS == 1
		vTraceInitTraceData();
	#endif

	/* The examples assume that all priority bits are assigned as preemption
	priority bits. */
	NVIC_SetPriorityGrouping( 0UL );

	/* Start the timer that just toggles an LED to show the demo is running. */
	vLEDsInitialise();

	/* Start the tasks that implements the command console on the UART, as
	described above. */
	vCDCCommandConsoleStart( mainCDC_COMMAND_CONSOLE_STACK_SIZE, mainCDC_COMMAND_CONSOLE_TASK_PRIORITY );

	/* Register CLI commands. */
	vRegisterCLICommands();

	/* Initialise the network interface.  Tasks that use the network are
	created in the network event hook when the network is connected and ready
	for use.  The address values passed in here are used if ipconfigUSE_DHCP is
	set to 0, or if ipconfigUSE_DHCP is set to 1 but a DHCP server cannot be
	contacted. */
	FreeRTOS_IPInit( ucIPAddress, ucNetMask, ucGatewayAddress, ucDNSServerAddress, ucMACAddress );

	/* If the trace recorder code is included... */
	#if configINCLUDE_TRACE_RELATED_CLI_COMMANDS == 1
	{
		extern xQueueHandle xNetworkEventQueue;

		/* Name the queue for viewing in FreeRTOS+Trace. */
		vTraceSetQueueName( xNetworkEventQueue, "IPStackEvent" );
	}
	#endif /*  configINCLUDE_TRACE_RELATED_CLI_COMMANDS == 1 */

	/* Start the FreeRTOS scheduler. */
	vTaskStartScheduler();

	/* The following line should never execute.  If it does, it means there was
	insufficient FreeRTOS heap memory available to create the Idle and/or timer
	tasks.  See the memory management section on the http://www.FreeRTOS.org web
	site for more information. */
	for( ;; );
}
/*-----------------------------------------------------------*/

void vApplicationStackOverflowHook( xTaskHandle pxTask, signed char *pcTaskName )
{
	( void ) pcTaskName;
	( void ) pxTask;

	/* Run time stack overflow checking is performed if
	configCHECK_FOR_STACK_OVERFLOW is defined to 1 or 2.  This hook
	function is called if a stack overflow is detected. */
	taskDISABLE_INTERRUPTS();
	for( ;; );
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

/* Called by FreeRTOS+UDP when the network connects. */
void vApplicationIPNetworkEventHook( eIPCallbackEvent_t eNetworkEvent )
{
static portBASE_TYPE xTaskAlreadyCreated = pdFALSE;

	if( eNetworkEvent == eNetworkUp )
	{
		/* Create the tasks that transmit to and receive from a standard
		echo server (see the web documentation for this port) in both
		standard and zero copy mode. */
		if( xTaskAlreadyCreated == pdFALSE )
		{
			vStartEchoClientTasks( mainECHO_CLIENT_TASK_STACK_SIZE, mainECHO_CLIENT_TASK_PRIORITY );
			xTaskAlreadyCreated = pdTRUE;
		}
	}
}
/*-----------------------------------------------------------*/

/* Called by FreeRTOS+UDP when a reply is received to an outgoing ping request. */
void vApplicationPingReplyHook( ePingReplyStatus_t eStatus, uint16_t usIdentifier )
{
static const uint8_t *pucSuccess = ( uint8_t * ) "\r\n\r\nPing reply received - ";
static const uint8_t *pucInvalidChecksum = ( uint8_t * ) "\r\n\r\nPing reply received with invalid checksum - ";
static const uint8_t *pucInvalidData = ( uint8_t * ) "\r\n\r\nPing reply received with invalid data - ";
static uint8_t ucMessage[ 50 ];
void vOutputString( const uint8_t * const pucMessage );

	switch( eStatus )
	{
		case eSuccess	:
			vOutputString( pucSuccess );
			break;

		case eInvalidChecksum :
			vOutputString( pucInvalidChecksum );
			break;

		case eInvalidData :
			vOutputString( pucInvalidData );
			break;

		default :
			/* It is not possible to get here as all enums have their own
			case. */
			break;
	}

	sprintf( ( char * ) ucMessage, "identifier %d\r\n\r\n", ( int ) usIdentifier );
	vOutputString( ucMessage );
}

