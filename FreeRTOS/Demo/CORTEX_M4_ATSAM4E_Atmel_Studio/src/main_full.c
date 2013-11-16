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

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "timers.h"

/* FreeRTOS+UDP includes. */
#include "FreeRTOS_UDP_IP.h"

/* Demo application includes. */
#include "UDPCommandInterpreter.h"

/* Note:  If the application is started without the network cable plugged in 
then ipconfigUDP_TASK_PRIORITY should be set to 0 in FreeRTOSIPConfig.h to
ensure the IP task is created at the idle priority.  This is because the Atmel 
ASF GMAC driver polls the GMAC looking for a connection, and doing so will 
prevent any lower priority tasks from executing.  In this demo the IP task is 
started at the idle priority, then set to configMAX_PRIORITIES - 2 in the 
network event hook only after a connection has been established (when the event
passed into the network event hook is eNetworkUp). */
#define mainCONNECTED_IP_TASK_PRIORITY		( configMAX_PRIORITIES - 2 )
#define mainDISCONNECTED_IP_TASK_PRIORITY	( tskIDLE_PRIORITY )

/* UDP command server task parameters. */
#define mainUDP_CLI_TASK_PRIORITY					( tskIDLE_PRIORITY )
#define mainUDP_CLI_PORT_NUMBER						( 5001UL )
#define mainUDP_CLI_TASK_STACK_SIZE					( configMINIMAL_STACK_SIZE * 2U )

/* Simple toggles an LED to show the program is running. */
static void prvFlashTimerCallback( xTimerHandle xTimer );

/* Creates a set of sample files on a RAM disk. */
extern void vCreateAndVerifySampleFiles( void );

/*
 * Register the generic commands that can be used with FreeRTOS+CLI.
 */
extern void vRegisterSampleCLICommands( void );

/*
 * Register the file system commands that can be used with FreeRTOS+CLI.
 */
extern void vRegisterFileSystemCLICommands( void );

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
probably be read from flash memory or an EEPROM.  Here it is just hard coded.
Note each node on a network must have a unique MAC address. */
const uint8_t ucMACAddress[ 6 ] = { configMAC_ADDR0, configMAC_ADDR1, configMAC_ADDR2, configMAC_ADDR3, configMAC_ADDR4, configMAC_ADDR5 };

/*-----------------------------------------------------------*/
int main_full( void )
{
xTimerHandle xFlashTimer;

	/* If the file system is only going to be accessed from one task then
	F_FS_THREAD_AWARE can be set to 0 and the set of example files are created
	before the RTOS scheduler is started.  If the file system is going to be
	access from more than one task then F_FS_THREAD_AWARE must be set to 1 and
	the	set of sample files are created from the idle task hook function
	vApplicationIdleHook() - which is defined in this file. */
	#if( F_FS_THREAD_AWARE == 0 )
	{
		/* Initialise the drive and file system, then create a few example
		files.  The output from this function just goes to the stdout window,
		allowing the output to be viewed when the UDP command console is not
		connected. */
		vCreateAndVerifySampleFiles();
	}
	#endif

	/* Register generic commands with the FreeRTOS+CLI command interpreter. */
	vRegisterSampleCLICommands();

	/* Register file system related commands with the FreeRTOS+CLI command
	interpreter. */
	vRegisterFileSystemCLICommands();

	/* Create the timer that just toggles an LED to indicate that the 
	application is running. */
	xFlashTimer = xTimerCreate( ( const signed char * const ) "Flash", 200 / portTICK_RATE_MS, pdTRUE, NULL, prvFlashTimerCallback );
	configASSERT( xFlashTimer );
	
	/* Start the timer.  As the scheduler is not running a block time cannot be
	used and is set to 0. */
	xTimerStart( xFlashTimer, 0 );

	/* Initialise the network interface.  Tasks that use the network are
	created in the network event hook when the network is connected and ready
	for use.  The address values passed in here are used if ipconfigUSE_DHCP is
	set to 0, or if ipconfigUSE_DHCP is set to 1 but a DHCP server cannot be
	contacted.  The Nabto service task is created automatically if
	ipconfigFREERTOS_PLUS_NABTO is set to 1 in FreeRTOSIPConfig.h. */
	FreeRTOS_IPInit( ucIPAddress, ucNetMask, ucGatewayAddress, ucDNSServerAddress, ucMACAddress );

	/* Start the scheduler itself. */
	vTaskStartScheduler();

	/* If all is well, the scheduler will now be running, and the following line
	will never be reached.  If the following line does execute, then there was
	insufficient FreeRTOS heap memory available for the idle and/or timer tasks
	to be created.  See the memory management section on the FreeRTOS web site
	for more details. */
	for( ;; );
}
/*-----------------------------------------------------------*/

static void prvFlashTimerCallback( xTimerHandle xTimer )
{
	/* The parameter is not used. */
	( void ) xTimer;
	
	/* Timer callback function that does nothing other than toggle an LED to
	indicate that the application is still running. */
	ioport_toggle_pin_level( LED0_GPIO );
}
/*-----------------------------------------------------------*/

/* Called by FreeRTOS+UDP when the network connects. */
void vApplicationIPNetworkEventHook( eIPCallbackEvent_t eNetworkEvent )
{
static long lTasksAlreadyCreated = pdFALSE;

	/* Note:  If the application is started without the network cable plugged in
	then ipconfigUDP_TASK_PRIORITY should be set to 0 in FreeRTOSIPConfig.h to
	ensure the IP task is created at the idle priority.  This is because the Atmel
	ASF GMAC driver polls the GMAC looking for a connection, and doing so will
	prevent any lower priority tasks from executing.  In this demo the IP task is
	started at the idle priority, then set to configMAX_PRIORITIES - 2 in the
	network event hook only after a connection has been established (when the event
	passed into the network event hook is eNetworkUp). */
	if( eNetworkEvent == eNetworkUp )
	{
		vTaskPrioritySet( NULL, mainCONNECTED_IP_TASK_PRIORITY );

		if( lTasksAlreadyCreated == pdFALSE )
		{		
			/* Create the task that handles the CLI on a UDP port.  The port number
			is set using the configUDP_CLI_PORT_NUMBER setting in FreeRTOSConfig.h. */
			vStartUDPCommandInterpreterTask( mainUDP_CLI_TASK_STACK_SIZE, mainUDP_CLI_PORT_NUMBER, mainUDP_CLI_TASK_PRIORITY );
		}
	}

	if( eNetworkEvent == eNetworkDown )
	{
		vTaskPrioritySet( NULL, tskIDLE_PRIORITY );
	}
}
/*-----------------------------------------------------------*/

void vFullDemoIdleHook( void )
{	
	/* If the file system is only going to be accessed from one task then
	F_FS_THREAD_AWARE can be set to 0 and the set of example files is created
	before the RTOS scheduler is started.  If the file system is going to be
	access from more than one task then F_FS_THREAD_AWARE must be set to 1 and
	the	set of sample files are created from the idle task hook function. */
	#if( F_FS_THREAD_AWARE == 1 )
	{
		static portBASE_TYPE xCreatedSampleFiles = pdFALSE;

		/* Initialise the drive and file system, then create a few example
		files.  The output from this function just goes to the stdout window,
		allowing the output to be viewed when the UDP command console is not
		connected. */
		if( xCreatedSampleFiles == pdFALSE )
		{
			vCreateAndVerifySampleFiles();
			xCreatedSampleFiles = pdTRUE;
		}
	}
	#endif
}




