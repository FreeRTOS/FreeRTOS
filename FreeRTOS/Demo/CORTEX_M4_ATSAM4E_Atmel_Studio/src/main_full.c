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
#include "partest.h"
#include "blocktim.h"
#include "flash_timer.h"
#include "semtest.h"
#include "GenQTest.h"
#include "QPeek.h"
#include "IntQueue.h"
#include "countsem.h"
#include "dynamic.h"
#include "QueueOverwrite.h"
#include "QueueSet.h"
#include "recmutex.h"

/* The period after which the check timer will expire, in ms, provided no errors
have been reported by any of the standard demo tasks.  ms are converted to the
equivalent in ticks using the portTICK_RATE_MS constant. */
#define mainCHECK_TIMER_PERIOD_MS			( 3000UL / portTICK_RATE_MS )

/* The period at which the check timer will expire, in ms, if an error has been
reported in one of the standard demo tasks.  ms are converted to the equivalent
in ticks using the portTICK_RATE_MS constant. */
#define mainERROR_CHECK_TIMER_PERIOD_MS 	( 200UL / portTICK_RATE_MS )

/* The priorities of the various demo application tasks. */
#define mainSEM_TEST_PRIORITY				( tskIDLE_PRIORITY + 1 )
#define mainBLOCK_Q_PRIORITY				( tskIDLE_PRIORITY + 2 )
#define mainCOM_TEST_PRIORITY				( tskIDLE_PRIORITY + 2 )
#define mainINTEGER_TASK_PRIORITY           ( tskIDLE_PRIORITY )
#define mainGEN_QUEUE_TASK_PRIORITY			( tskIDLE_PRIORITY )
#define mainQUEUE_OVERWRITE_TASK_PRIORITY	( tskIDLE_PRIORITY )

/* The LED controlled by the 'check' software timer. */
#define mainCHECK_LED						( 2 )

/* The number of LEDs that should be controlled by the flash software timer
standard demo.  In this case it is only 1 as the starter kit has three LEDs, one
of which is controlled by the check timer and one of which is controlled by the
ISR triggered task. */
#define mainNUM_FLASH_TIMER_LEDS			( 1 )

/* Misc. */
#define mainDONT_BLOCK						( 0 )

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

/*-----------------------------------------------------------*/

/*
 * The check timer callback function, as described at the top of this file.
 */
static void prvCheckTimerCallback( xTimerHandle xTimer );

/* 
 * Creates a set of sample files on a RAM disk. 
 */
extern void vCreateAndVerifySampleFiles( void );

/*
 * Register the generic commands that can be used with FreeRTOS+CLI.
 */
extern void vRegisterSampleCLICommands( void );

/*
 * Register the file system commands that can be used with FreeRTOS+CLI.
 */
extern void vRegisterFileSystemCLICommands( void );

/*
 * Register the UDP related commands that can be used with FreeRTOS+CLI.
 */
extern void vRegisterUDPCLICommands( void );

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
xTimerHandle xTimer = NULL;

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

	/* Register example generic, file system related and UDP related CLI 
	commands respectively. */
	vRegisterSampleCLICommands();
	vRegisterFileSystemCLICommands();
	vRegisterUDPCLICommands();

	/* Initialise the network interface.  Tasks that use the network are
	created in the network event hook when the network is connected and ready
	for use.  The address values passed in here are used if ipconfigUSE_DHCP is
	set to 0, or if ipconfigUSE_DHCP is set to 1 but a DHCP server cannot be
	contacted.  The Nabto service task is created automatically if
	ipconfigFREERTOS_PLUS_NABTO is set to 1 in FreeRTOSIPConfig.h. */
	FreeRTOS_IPInit( ucIPAddress, ucNetMask, ucGatewayAddress, ucDNSServerAddress, ucMACAddress );

	/* Create all the other standard demo tasks. */
	vStartLEDFlashTimers( mainNUM_FLASH_TIMER_LEDS );
	vCreateBlockTimeTasks();
	vStartSemaphoreTasks( mainSEM_TEST_PRIORITY );
	vStartGenericQueueTasks( mainGEN_QUEUE_TASK_PRIORITY );
	vStartQueuePeekTasks();
	vStartCountingSemaphoreTasks();
	vStartDynamicPriorityTasks();
	vStartQueueOverwriteTask( mainQUEUE_OVERWRITE_TASK_PRIORITY );
	vStartQueueSetTasks();
	vStartRecursiveMutexTasks();

	/* Create the software timer that performs the 'check' functionality, as
	described at the top of this file. */
	xTimer = xTimerCreate( 	( const signed char * ) "CheckTimer",/* A text name, purely to help debugging. */
							( mainCHECK_TIMER_PERIOD_MS ),		/* The timer period, in this case 3000ms (3s). */
							pdTRUE,								/* This is an auto-reload timer, so xAutoReload is set to pdTRUE. */
							( void * ) 0,						/* The ID is not used, so can be set to anything. */
							prvCheckTimerCallback );			/* The callback function that inspects the status of all the other tasks. */

	if( xTimer != NULL )
	{
		xTimerStart( xTimer, mainDONT_BLOCK );
	}

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

static void prvCheckTimerCallback( xTimerHandle xTimer )
{
static long lChangedTimerPeriodAlready = pdFALSE;
unsigned long ulErrorOccurred = pdFALSE;

	/* Avoid compiler warnings. */
	( void ) xTimer;

	/* Have any of the standard demo tasks detected an error in their
	operation? */
	if( xAreGenericQueueTasksStillRunning() != pdTRUE )
	{
		ulErrorOccurred |= ( 0x01UL << 3UL );
	}
	else if( xAreQueuePeekTasksStillRunning() != pdTRUE )
	{
		ulErrorOccurred |= ( 0x01UL << 4UL );
	}
	else if( xAreBlockTimeTestTasksStillRunning() != pdTRUE )
	{
		ulErrorOccurred |= ( 0x01UL << 5UL );
	}
	else if( xAreSemaphoreTasksStillRunning() != pdTRUE )
	{
		ulErrorOccurred |= ( 0x01UL << 6UL );
	}
	else if( xAreCountingSemaphoreTasksStillRunning() != pdTRUE )
	{
		ulErrorOccurred |= ( 0x01UL << 8UL );
	}
	else if( xAreDynamicPriorityTasksStillRunning() != pdTRUE )
	{
		ulErrorOccurred |= ( 0x01UL << 9UL );
	}
	else if( xIsQueueOverwriteTaskStillRunning() != pdTRUE )
	{
		ulErrorOccurred |= ( 0x01UL << 10UL );
	}
	else if( xAreQueueSetTasksStillRunning() != pdTRUE )
	{
		ulErrorOccurred |= ( 0x01UL << 11UL );
	}
	else if( xAreRecursiveMutexTasksStillRunning() != pdTRUE )
	{
		ulErrorOccurred |= ( 0x01UL << 12UL );
	}

	if( ulErrorOccurred != pdFALSE )
	{
		/* An error occurred.  Increase the frequency at which the check timer
		toggles its LED to give visual feedback of the potential error
		condition. */
		if( lChangedTimerPeriodAlready == pdFALSE )
		{
			lChangedTimerPeriodAlready = pdTRUE;

			/* This call to xTimerChangePeriod() uses a zero block time.
			Functions called from inside of a timer callback function must
			*never* attempt	to block as to do so could impact other software
			timers. */
			xTimerChangePeriod( xTimer, ( mainERROR_CHECK_TIMER_PERIOD_MS ), mainDONT_BLOCK );
		}
	}

	vParTestToggleLED( mainCHECK_LED );
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
/*-----------------------------------------------------------*/

void vFullDemoTickHook( void )
{
	/* Call the periodic queue overwrite from ISR demo. */
	vQueueOverwritePeriodicISRDemo();

	/* Call the queue set ISR test function. */
	vQueueSetAccessQueueSetFromISR();
}
/*-----------------------------------------------------------*/

/* Called automatically when a reply to an outgoing ping is received. */
void vApplicationPingReplyHook( ePingReplyStatus_t eStatus, uint16_t usIdentifier )
{
	/* This demo has nowhere to output any information so does nothing. */
	( void ) usIdentifier;
	
	switch( eStatus )
	{
		case eSuccess	:
			break;

		case eInvalidChecksum :
			break;

		case eInvalidData :
			break;

		default :
			/* It is not possible to get here as all enums have their own
			case. */
			break;
	}
}




