/*
    FreeRTOS V9.0.1 - Copyright (C) 2017 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>>> AND MODIFIED BY <<<< the FreeRTOS exception.

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

/******************************************************************************
 * NOTE 1:  This project provides two demo applications.  A simple blinky style
 * project, and a more comprehensive test and demo application that makes use of
 * the FreeRTOS+CLI, FreeRTOS+UDP and FreeRTOS+FAT SL components.  The
 * mainCREATE_SIMPLE_BLINKY_DEMO_ONLY setting in main.c is used to select
 * between the two.  See the notes on using mainCREATE_SIMPLE_BLINKY_DEMO_ONLY
 * in main.c.  This file implements the comprehensive test and demo version,
 * which is fully documented on the following URL:
 * http://www.FreeRTOS.org/Atmel_SAM4E_RTOS_Demo.html
 *
 * NOTE 2:  This file only contains the source code that is specific to the
 * full demo.  Generic functions, such FreeRTOS hook functions, and functions
 * required to configure the hardware, are defined in main.c.
 ******************************************************************************
 *
 * Full user instructions are provided on the following URL:
 * http://www.FreeRTOS.org/Atmel_SAM4E_RTOS_Demo.html
 *
 * main_full():
 * 	+ Uses FreeRTOS+FAT SL to create a set of example files on a RAM disk.
 *  + Displays some bitmaps on the LCD.
 *  + Registers sample generic, file system related and UDP related commands
 *	  with FreeRTOS+CLI.
 *	+ Creates all the standard demo application tasks and software timers.
 *	+ Starts the scheduler.
 *
 * A UDP command server and optionally two UDP echo client tasks are created
 * from the network event hook after an IP address has been obtained.  The IP
 * address is displayed on the LCD.
 *
 * A "check software timer" is created to provide visual feedback of the system
 * status.  The timer's period is initially set to three seconds.  The callback
 * function associated with the timer checks all the standard demo tasks are not
 * only still executed, but are executing without reporting any errors.  If the
 * timer discovers a task has either stalled, or reported an error, then it
 * changes its own period from the initial three seconds, to just 200ms.  The
 * check software timer also toggles the LED marked D4 - so if the LED toggles
 * every three seconds then no potential errors have been found, and if the LED
 * toggles every 200ms then a potential error has been found in at least one
 * task.
 *
 * Information on accessing the CLI and file system, and using the UDP echo
 * tasks is provided on http://www.FreeRTOS.org/Atmel_SAM4E_RTOS_Demo.html
 *
 */

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "timers.h"

/* FreeRTOS+UDP includes. */
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_Sockets.h"

/* UDP demo includes. */
#include "UDPCommandInterpreter.h"
#include "TwoEchoClients.h"

/* Standard demo includes. */
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
#include "EventGroupsDemo.h"
#include "TaskNotify.h"
#include "IntSemTest.h"
#include "TimerDemo.h"
#include "IntQueue.h"

/* The period after which the check timer will expire, in ms, provided no errors
have been reported by any of the standard demo tasks.  ms are converted to the
equivalent in ticks using the portTICK_PERIOD_MS constant. */
#define mainCHECK_TIMER_PERIOD_MS			( 3000UL / portTICK_PERIOD_MS )

/* The period at which the check timer will expire, in ms, if an error has been
reported in one of the standard demo tasks.  ms are converted to the equivalent
in ticks using the portTICK_PERIOD_MS constant. */
#define mainERROR_CHECK_TIMER_PERIOD_MS 	( 200UL / portTICK_PERIOD_MS )

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
passed into the network event hook is eNetworkUp).
http://www.FreeRTOS.org/udp */
#define mainCONNECTED_IP_TASK_PRIORITY		( configMAX_PRIORITIES - 1 )
#define mainDISCONNECTED_IP_TASK_PRIORITY	( tskIDLE_PRIORITY )

/* UDP command server and echo task parameters. */
#define mainUDP_CLI_TASK_PRIORITY			( tskIDLE_PRIORITY )
#define mainUDP_CLI_PORT_NUMBER				( 5001UL )
#define mainUDP_CLI_TASK_STACK_SIZE			( configMINIMAL_STACK_SIZE + 90 )
#define mainECHO_CLIENT_STACK_SIZE			( configMINIMAL_STACK_SIZE + 30 )

/* Set to 1 to include the UDP echo client tasks in the build.  The echo clients
require the IP address of the echo server to be defined using the
configECHO_SERVER_ADDR0 to configECHO_SERVER_ADDR3 constants in
FreeRTOSConfig.h. */
#define mainINCLUDE_ECHO_CLIENT_TASKS		1

/* Used by the standard demo timer tasks. */
#define mainTIMER_TEST_PERIOD				( 50 )

/*-----------------------------------------------------------*/

/*
 * The check timer callback function, as described at the top of this file.
 */
static void prvCheckTimerCallback( TimerHandle_t xTimer );

/*
 * Creates a set of sample files on a RAM disk.  http://www.FreeRTOS.org/fat_sl
 */
extern void vCreateAndVerifySampleFiles( void );

/*
 * Register sample generic commands that can be used with FreeRTOS+CLI.  Type
 * 'help' in the command line to see a list of registered commands.
 * http://www.FreeRTOS.org/cli
 */
extern void vRegisterSampleCLICommands( void );

/*
 * Register sample file system commands that can be used with FreeRTOS+CLI.
 */
extern void vRegisterFileSystemCLICommands( void );

/*
 * Register sample UDP related commands that can be used with FreeRTOS+CLI.
 */
extern void vRegisterUDPCLICommands( void );

/*
 * Initialise the LCD and output a bitmap.
 */
extern void vInitialiseLCD( void );

/*
 * Register check tasks, and the tasks used to write over and check the contents
 * of the FPU registers, as described at the top of this file.  The nature of
 * these files necessitates that they are written in an assembly file.
 */
static void prvRegTest1Task( void *pvParameters ) __attribute__((naked));
static void prvRegTest2Task( void *pvParameters ) __attribute__((naked));

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

/* The following two variables are used to communicate the status of the
register check tasks to the check software timer.  If the variables keep
incrementing, then the register check tasks have not discovered any errors.  If
a variable stops incrementing, then an error has been found. */
volatile unsigned long ulRegTest1LoopCounter = 0UL, ulRegTest2LoopCounter = 0UL;

/*-----------------------------------------------------------*/

int main_full( void )
{
	/* Usage instructions on http://www.FreeRTOS.org/Atmel_SAM4E_RTOS_Demo.html */

	/* Initialise the LCD and output a bitmap.  The IP address will also be
	displayed on the LCD when it has been obtained. */
	vInitialiseLCD();

	/* If the file system is only going to be accessed from one task then
	F_FS_THREAD_AWARE can be set to 0 and the set of example files are created
	before the RTOS scheduler is started.  If the file system is going to be
	access from more than one task then F_FS_THREAD_AWARE must be set to 1 and
	the	set of sample files are created from the idle task hook function
	vApplicationIdleHook(). */
	#if( F_FS_THREAD_AWARE == 0 )
	{
		/* Initialise the drive and file system, then create a few example
		files.  The files can be viewed and accessed via the CLI.  View the
		documentation page for this demo (link at the top of this file) for more
		information. */
		vCreateAndVerifySampleFiles();
	}
	#endif

	/* Register example generic, file system related and UDP related CLI
	commands respectively.  Type 'help' into the command console to view a list
	of registered commands. */
	vRegisterSampleCLICommands();
	vRegisterFileSystemCLICommands();
	vRegisterUDPCLICommands();

	/* Initialise the network interface.  Tasks that use the network are
	created in the network event hook when the network is connected and ready
	for use.  The address values passed in here are used if ipconfigUSE_DHCP is
	set to 0, or if ipconfigUSE_DHCP is set to 1 but a DHCP server cannot be
	contacted.  The IP address actually used is displayed on the LCD (after DHCP
	has completed if DHCP is used). */
	FreeRTOS_IPInit( ucIPAddress, ucNetMask, ucGatewayAddress, ucDNSServerAddress, ucMACAddress );

	/* Create all the other standard demo tasks. */	
	vCreateBlockTimeTasks();
	vStartSemaphoreTasks( mainSEM_TEST_PRIORITY );
	vStartGenericQueueTasks( mainGEN_QUEUE_TASK_PRIORITY );
	vStartQueuePeekTasks();
	vStartCountingSemaphoreTasks();
	vStartDynamicPriorityTasks();
	vStartQueueOverwriteTask( mainQUEUE_OVERWRITE_TASK_PRIORITY );
	vStartQueueSetTasks();
	vStartRecursiveMutexTasks();
	vStartEventGroupTasks();
	vStartTaskNotifyTask();
	vStartInterruptSemaphoreTasks();
	vStartTimerDemoTask( mainTIMER_TEST_PERIOD );
	vStartInterruptQueueTasks();

	/* Create the register check tasks, as described at the top of this
	file */
	xTaskCreate( prvRegTest1Task, "Reg1", configMINIMAL_STACK_SIZE, ( void * ) NULL, tskIDLE_PRIORITY, NULL );
	xTaskCreate( prvRegTest2Task, "Reg2", configMINIMAL_STACK_SIZE, ( void * ) NULL, tskIDLE_PRIORITY, NULL );

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

static void prvCheckTimerCallback( TimerHandle_t xTimer )
{
static long lChangedTimerPeriodAlready = pdFALSE;
static unsigned long ulLastRegTest1Value = 0, ulLastRegTest2Value = 0;
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
	else if( xAreEventGroupTasksStillRunning() != pdTRUE )
	{
		ulErrorOccurred |= ( 0x01UL << 13UL );
	}
	else if( xAreTaskNotificationTasksStillRunning() != pdTRUE )
	{
		ulErrorOccurred |= ( 0x01UL << 14UL );
	}
	else if( xAreInterruptSemaphoreTasksStillRunning() != pdTRUE )
	{
		ulErrorOccurred |= ( 0x01UL << 15UL );
	}
	else if( xAreTimerDemoTasksStillRunning( mainCHECK_TIMER_PERIOD_MS ) != pdTRUE )
	{
		ulErrorOccurred |= 1UL << 16UL;
	}	
	else if( xAreIntQueueTasksStillRunning() != pdTRUE )
	{
		ulErrorOccurred |= 1UL << 17UL;
	}

	
	/* Check that the register test 1 task is still running. */
	if( ulLastRegTest1Value == ulRegTest1LoopCounter )
	{
		ulErrorOccurred |= 1UL << 18UL;
	}
	ulLastRegTest1Value = ulRegTest1LoopCounter;

	/* Check that the register test 2 task is still running. */
	if( ulLastRegTest2Value == ulRegTest2LoopCounter )
	{
		ulErrorOccurred |= 1UL << 19UL;
	}
	ulLastRegTest2Value = ulRegTest2LoopCounter;

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

	/* Toggle the LED to give visual feedback of the system status.  The rate at
	which the LED toggles will increase to mainERROR_CHECK_TIMER_PERIOD_MS if a
	suspected error has been found in any of the standard demo tasks. */
	vParTestToggleLED( mainCHECK_LED );
}
/*-----------------------------------------------------------*/

/* Called by FreeRTOS+UDP when the network connects. */
void vApplicationIPNetworkEventHook( eIPCallbackEvent_t eNetworkEvent )
{
static long lTasksAlreadyCreated = pdFALSE;
const unsigned long ulXCoord = 3, ulYCoord = 3, ulIPAddressOffset = 45;
unsigned long ulIPAddress;
char cIPAddress[ 20 ];

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
		/* Ensure tasks are only created once. */
		if( lTasksAlreadyCreated == pdFALSE )
		{
			/* Create the task that handles the CLI on a UDP port.  The port
			number is set using the configUDP_CLI_PORT_NUMBER setting in
			FreeRTOSConfig.h. */
			vStartUDPCommandInterpreterTask( mainUDP_CLI_TASK_STACK_SIZE, mainUDP_CLI_PORT_NUMBER, mainUDP_CLI_TASK_PRIORITY );

			#if( mainINCLUDE_ECHO_CLIENT_TASKS == 1 )
			{
				/* Create the UDP echo tasks.  The UDP echo tasks require the IP
				address of the echo server to be defined using the
				configECHO_SERVER_ADDR0 to configECHO_SERVER_ADDR3 constants in
				FreeRTOSConfig.h. */
				vStartEchoClientTasks( mainECHO_CLIENT_STACK_SIZE, tskIDLE_PRIORITY );
			}
			#endif
		}

		/* Obtain the IP address, convert it to a string, then display it on the
		LCD. */
		FreeRTOS_GetAddressConfiguration( &ulIPAddress, NULL, NULL, NULL );
		FreeRTOS_inet_ntoa( ulIPAddress, cIPAddress );
		ili93xx_draw_string( ulXCoord, ulYCoord, ( uint8_t * ) "IP: " );
		ili93xx_draw_string( ulXCoord + ulIPAddressOffset, ulYCoord, ( uint8_t * ) cIPAddress );

		/* Set the priority of the IP task up to the desired priority now it has
		connected. */
		vTaskPrioritySet( NULL, mainCONNECTED_IP_TASK_PRIORITY );
	}

	/* NOTE:  At the time of writing the Ethernet driver does not report the
	cable being unplugged - so the following if() condition will never be met.
	It is included for possible future updates to the driver. */
	if( eNetworkEvent == eNetworkDown )
	{
		/* Ensure the Atmel GMAC drivers don't hog all the CPU time as they look
		for a new connection by lowering the priority of the IP task to that of
		the Idle task. */
		vTaskPrioritySet( NULL, tskIDLE_PRIORITY );

		/* Disconnected - so no IP address. */
		ili93xx_draw_string( ulXCoord, ulYCoord, ( uint8_t * ) "IP:                  " );
	}
}
/*-----------------------------------------------------------*/

void vFullDemoIdleHook( void )
{
static TimerHandle_t xCheckTimer = NULL;
		
	if( xCheckTimer == NULL )
	{
		/* Create the software timer that performs the 'check' 
		functionality, in the full demo.  This is not done before the
		scheduler is started as to do so would prevent the standard demo
		timer tasks from passing their tests (they expect the timer
		command queue to be empty. */
		xCheckTimer = xTimerCreate( "CheckTimer",					/* A text name, purely to help debugging. */
									( mainCHECK_TIMER_PERIOD_MS ),	/* The timer period, in this case 3000ms (3s). */
									pdTRUE,							/* This is an auto-reload timer, so xAutoReload is set to pdTRUE. */
									( void * ) 0,					/* The ID is not used, so can be set to anything. */
									prvCheckTimerCallback );		/* The callback function that inspects the status of all the other tasks. */

		if( xCheckTimer != NULL )
		{
			xTimerStart( xCheckTimer, mainDONT_BLOCK );
		}
		
		/* Also start some timers that just flash LEDs. */
		vStartLEDFlashTimers( mainNUM_FLASH_TIMER_LEDS );
	}
	
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
	/* Call the periodic queue overwrite from ISR test function. */
	vQueueOverwritePeriodicISRDemo();

	/* Call the periodic queue set ISR test function. */
	vQueueSetAccessQueueSetFromISR();
	
	/* Call the event group ISR tests. */
	vPeriodicEventGroupsProcessing();
	
	/* Exercise task notifications from interrupts. */
	xNotifyTaskFromISR();
	
	/* Use mutexes from interrupts. */
	vInterruptSemaphorePeriodicTest();
	
	/* Use timers from an interrupt. */
	vTimerPeriodicISRTests();
}
/*-----------------------------------------------------------*/

/* Called automatically when a reply to an outgoing ping is received. */
void vApplicationPingReplyHook( ePingReplyStatus_t eStatus, uint16_t usIdentifier )
{
	/* This demo has nowhere to output any information so does nothing, but the
	IP address resolved for the pined URL is displayed in the CLI. */
	( void ) usIdentifier;
	( void ) eStatus;
}
/*-----------------------------------------------------------*/

/* This is a naked function. */
static void prvRegTest1Task( void *pvParameters )
{
	__asm volatile
	(
		"	/* Fill the core registers with known values. */		\n"
		"	mov r0, #100											\n"
		"	mov r1, #101											\n"
		"	mov r2, #102											\n"
		"	mov r3, #103											\n"
		"	mov	r4, #104											\n"
		"	mov	r5, #105											\n"
		"	mov	r6, #106											\n"
		"	mov r7, #107											\n"
		"	mov	r8, #108											\n"
		"	mov	r9, #109											\n"
		"	mov	r10, #110											\n"
		"	mov	r11, #111											\n"
		"	mov r12, #112											\n"
		"															\n"
		"	/* Fill the VFP registers with known values. */			\n"
		"	vmov d0, r0, r1											\n"
		"	vmov d1, r2, r3											\n"
		"	vmov d2, r4, r5											\n"
		"	vmov d3, r6, r7											\n"
		"	vmov d4, r8, r9											\n"
		"	vmov d5, r10, r11										\n"
		"	vmov d6, r0, r1											\n"
		"	vmov d7, r2, r3											\n"
		"	vmov d8, r4, r5											\n"
		"	vmov d9, r6, r7											\n"
		"	vmov d10, r8, r9										\n"
		"	vmov d11, r10, r11										\n"
		"	vmov d12, r0, r1										\n"
		"	vmov d13, r2, r3										\n"
		"	vmov d14, r4, r5										\n"
		"	vmov d15, r6, r7										\n"
		"															\n"
		"reg1_loop:													\n"
		"	/* Check all the VFP registers still contain the values set above.\n"
		"	First save registers that are clobbered by the test. */	\n"
		"	push { r0-r1 }											\n"
		"															\n"
		"	vmov r0, r1, d0											\n"
		"	cmp r0, #100											\n"
		"	bne reg1_error_loopf									\n"
		"	cmp r1, #101											\n"
		"	bne reg1_error_loopf									\n"
		"	vmov r0, r1, d1											\n"
		"	cmp r0, #102											\n"
		"	bne reg1_error_loopf									\n"
		"	cmp r1, #103											\n"
		"	bne reg1_error_loopf									\n"
		"	vmov r0, r1, d2											\n"
		"	cmp r0, #104											\n"
		"	bne reg1_error_loopf									\n"
		"	cmp r1, #105											\n"
		"	bne reg1_error_loopf									\n"
		"	vmov r0, r1, d3											\n"
		"	cmp r0, #106											\n"
		"	bne reg1_error_loopf									\n"
		"	cmp r1, #107											\n"
		"	bne reg1_error_loopf									\n"
		"	vmov r0, r1, d4											\n"
		"	cmp r0, #108											\n"
		"	bne reg1_error_loopf									\n"
		"	cmp r1, #109											\n"
		"	bne reg1_error_loopf									\n"
		"	vmov r0, r1, d5											\n"
		"	cmp r0, #110											\n"
		"	bne reg1_error_loopf									\n"
		"	cmp r1, #111											\n"
		"	bne reg1_error_loopf									\n"
		"	vmov r0, r1, d6											\n"
		"	cmp r0, #100											\n"
		"	bne reg1_error_loopf									\n"
		"	cmp r1, #101											\n"
		"	bne reg1_error_loopf									\n"
		"	vmov r0, r1, d7											\n"
		"	cmp r0, #102											\n"
		"	bne reg1_error_loopf									\n"
		"	cmp r1, #103											\n"
		"	bne reg1_error_loopf									\n"
		"	vmov r0, r1, d8											\n"
		"	cmp r0, #104											\n"
		"	bne reg1_error_loopf									\n"
		"	cmp r1, #105											\n"
		"	bne reg1_error_loopf									\n"
		"	vmov r0, r1, d9											\n"
		"	cmp r0, #106											\n"
		"	bne reg1_error_loopf									\n"
		"	cmp r1, #107											\n"
		"	bne reg1_error_loopf									\n"
		"	vmov r0, r1, d10										\n"
		"	cmp r0, #108											\n"
		"	bne reg1_error_loopf									\n"
		"	cmp r1, #109											\n"
		"	bne reg1_error_loopf									\n"
		"	vmov r0, r1, d11										\n"
		"	cmp r0, #110											\n"
		"	bne reg1_error_loopf									\n"
		"	cmp r1, #111											\n"
		"	bne reg1_error_loopf									\n"
		"	vmov r0, r1, d12										\n"
		"	cmp r0, #100											\n"
		"	bne reg1_error_loopf									\n"
		"	cmp r1, #101											\n"
		"	bne reg1_error_loopf									\n"
		"	vmov r0, r1, d13										\n"
		"	cmp r0, #102											\n"
		"	bne reg1_error_loopf									\n"
		"	cmp r1, #103											\n"
		"	bne reg1_error_loopf									\n"
		"	vmov r0, r1, d14										\n"
		"	cmp r0, #104											\n"
		"	bne reg1_error_loopf									\n"
		"	cmp r1, #105											\n"
		"	bne reg1_error_loopf									\n"
		"	vmov r0, r1, d15										\n"
		"	cmp r0, #106											\n"
		"	bne reg1_error_loopf									\n"
		"	cmp r1, #107											\n"
		"	bne reg1_error_loopf									\n"
		"															\n"
		"	/* Restore the registers that were clobbered by the test. */\n"
		"	pop {r0-r1}												\n"
		"															\n"
		"	/* VFP register test passed.  Jump to the core register test. */\n"
		"	b reg1_loopf_pass										\n"
		"															\n"
		"reg1_error_loopf:											\n"
		"	/* If this line is hit then a VFP register value was found to be\n"
		"	incorrect. */											\n"
		"	b reg1_error_loopf										\n"
		"															\n"
		"reg1_loopf_pass:											\n"
		"															\n"
		"	cmp	r0, #100											\n"
		"	bne	reg1_error_loop										\n"
		"	cmp	r1, #101											\n"
		"	bne	reg1_error_loop										\n"
		"	cmp	r2, #102											\n"
		"	bne	reg1_error_loop										\n"
		"	cmp r3, #103											\n"
		"	bne	reg1_error_loop										\n"
		"	cmp	r4, #104											\n"
		"	bne	reg1_error_loop										\n"
		"	cmp	r5, #105											\n"
		"	bne	reg1_error_loop										\n"
		"	cmp	r6, #106											\n"
		"	bne	reg1_error_loop										\n"
		"	cmp	r7, #107											\n"
		"	bne	reg1_error_loop										\n"
		"	cmp	r8, #108											\n"
		"	bne	reg1_error_loop										\n"
		"	cmp	r9, #109											\n"
		"	bne	reg1_error_loop										\n"
		"	cmp	r10, #110											\n"
		"	bne	reg1_error_loop										\n"
		"	cmp	r11, #111											\n"
		"	bne	reg1_error_loop										\n"
		"	cmp	r12, #112											\n"
		"	bne	reg1_error_loop										\n"
		"															\n"
		"	/* Everything passed, increment the loop counter. */	\n"
		"	push { r0-r1 }											\n"
		"	ldr	r0, =ulRegTest1LoopCounter							\n"
		"	ldr r1, [r0]											\n"
		"	adds r1, r1, #1											\n"
		"	str r1, [r0]											\n"
		"	pop { r0-r1 }											\n"
		"															\n"
		"	/* Start again. */										\n"
		"	b reg1_loop												\n"
		"															\n"
		"reg1_error_loop:											\n"
		"	/* If this line is hit then there was an error in a core register value.\n"
		"	The loop ensures the loop counter stops incrementing. */\n"
		"	b reg1_error_loop										\n"
		"	nop														"
	);
	
	/* Remove compiler warnings about unused parameters. */
	( void ) pvParameters;
}
/*-----------------------------------------------------------*/

/* This is a naked function. */
static void prvRegTest2Task( void *pvParameters )
{
	__asm volatile
	(
		"	/* Set all the core registers to known values. */		\n"
		"	mov r0, #-1												\n"
		"	mov r1, #1												\n"
		"	mov r2, #2												\n"
		"	mov r3, #3												\n"
		"	mov	r4, #4												\n"
		"	mov	r5, #5												\n"
		"	mov	r6, #6												\n"
		"	mov r7, #7												\n"
		"	mov	r8, #8												\n"
		"	mov	r9, #9												\n"
		"	mov	r10, #10											\n"
		"	mov	r11, #11											\n"
		"	mov r12, #12											\n"
		"															\n"
		"	/* Set all the VFP to known values. */					\n"
		"	vmov d0, r0, r1											\n"
		"	vmov d1, r2, r3											\n"
		"	vmov d2, r4, r5											\n"
		"	vmov d3, r6, r7											\n"
		"	vmov d4, r8, r9											\n"
		"	vmov d5, r10, r11										\n"
		"	vmov d6, r0, r1											\n"
		"	vmov d7, r2, r3											\n"
		"	vmov d8, r4, r5											\n"
		"	vmov d9, r6, r7											\n"
		"	vmov d10, r8, r9										\n"
		"	vmov d11, r10, r11										\n"
		"	vmov d12, r0, r1										\n"
		"	vmov d13, r2, r3										\n"
		"	vmov d14, r4, r5										\n"
		"	vmov d15, r6, r7										\n"
		"															\n"
		"reg2_loop:													\n"
		"															\n"
		"	/* Check all the VFP registers still contain the values set above.\n"
		"	First save registers that are clobbered by the test. */	\n"
		"	push { r0-r1 }											\n"
		"															\n"
		"	vmov r0, r1, d0											\n"
		"	cmp r0, #-1												\n"
		"	bne reg2_error_loopf									\n"
		"	cmp r1, #1												\n"
		"	bne reg2_error_loopf									\n"
		"	vmov r0, r1, d1											\n"
		"	cmp r0, #2												\n"
		"	bne reg2_error_loopf									\n"
		"	cmp r1, #3												\n"
		"	bne reg2_error_loopf									\n"
		"	vmov r0, r1, d2											\n"
		"	cmp r0, #4												\n"
		"	bne reg2_error_loopf									\n"
		"	cmp r1, #5												\n"
		"	bne reg2_error_loopf									\n"
		"	vmov r0, r1, d3											\n"
		"	cmp r0, #6												\n"
		"	bne reg2_error_loopf									\n"
		"	cmp r1, #7												\n"
		"	bne reg2_error_loopf									\n"
		"	vmov r0, r1, d4											\n"
		"	cmp r0, #8												\n"
		"	bne reg2_error_loopf									\n"
		"	cmp r1, #9												\n"
		"	bne reg2_error_loopf									\n"
		"	vmov r0, r1, d5											\n"
		"	cmp r0, #10												\n"
		"	bne reg2_error_loopf									\n"
		"	cmp r1, #11												\n"
		"	bne reg2_error_loopf									\n"
		"	vmov r0, r1, d6											\n"
		"	cmp r0, #-1												\n"
		"	bne reg2_error_loopf									\n"
		"	cmp r1, #1												\n"
		"	bne reg2_error_loopf									\n"
		"	vmov r0, r1, d7											\n"
		"	cmp r0, #2												\n"
		"	bne reg2_error_loopf									\n"
		"	cmp r1, #3												\n"
		"	bne reg2_error_loopf									\n"
		"	vmov r0, r1, d8											\n"
		"	cmp r0, #4												\n"
		"	bne reg2_error_loopf									\n"
		"	cmp r1, #5												\n"
		"	bne reg2_error_loopf									\n"
		"	vmov r0, r1, d9											\n"
		"	cmp r0, #6												\n"
		"	bne reg2_error_loopf									\n"
		"	cmp r1, #7												\n"
		"	bne reg2_error_loopf									\n"
		"	vmov r0, r1, d10										\n"
		"	cmp r0, #8												\n"
		"	bne reg2_error_loopf									\n"
		"	cmp r1, #9												\n"
		"	bne reg2_error_loopf									\n"
		"	vmov r0, r1, d11										\n"
		"	cmp r0, #10												\n"
		"	bne reg2_error_loopf									\n"
		"	cmp r1, #11												\n"
		"	bne reg2_error_loopf									\n"
		"	vmov r0, r1, d12										\n"
		"	cmp r0, #-1												\n"
		"	bne reg2_error_loopf									\n"
		"	cmp r1, #1												\n"
		"	bne reg2_error_loopf									\n"
		"	vmov r0, r1, d13										\n"
		"	cmp r0, #2												\n"
		"	bne reg2_error_loopf									\n"
		"	cmp r1, #3												\n"
		"	bne reg2_error_loopf									\n"
		"	vmov r0, r1, d14										\n"
		"	cmp r0, #4												\n"
		"	bne reg2_error_loopf									\n"
		"	cmp r1, #5												\n"
		"	bne reg2_error_loopf									\n"
		"	vmov r0, r1, d15										\n"
		"	cmp r0, #6												\n"
		"	bne reg2_error_loopf									\n"
		"	cmp r1, #7												\n"
		"	bne reg2_error_loopf									\n"
		"															\n"
		"	/* Restore the registers that were clobbered by the test. */\n"
		"	pop {r0-r1}												\n"
		"															\n"
		"	/* VFP register test passed.  Jump to the core register test. */\n"
		"	b reg2_loopf_pass										\n"
		"															\n"
		"reg2_error_loopf:											\n"
		"	/* If this line is hit then a VFP register value was found to be\n"
		"	incorrect. */											\n"
		"	b reg2_error_loopf										\n"
		"															\n"
		"reg2_loopf_pass:											\n"
		"															\n"
		"	cmp	r0, #-1												\n"
		"	bne	reg2_error_loop										\n"
		"	cmp	r1, #1												\n"
		"	bne	reg2_error_loop										\n"
		"	cmp	r2, #2												\n"
		"	bne	reg2_error_loop										\n"
		"	cmp r3, #3												\n"
		"	bne	reg2_error_loop										\n"
		"	cmp	r4, #4												\n"
		"	bne	reg2_error_loop										\n"
		"	cmp	r5, #5												\n"
		"	bne	reg2_error_loop										\n"
		"	cmp	r6, #6												\n"
		"	bne	reg2_error_loop										\n"
		"	cmp	r7, #7												\n"
		"	bne	reg2_error_loop										\n"
		"	cmp	r8, #8												\n"
		"	bne	reg2_error_loop										\n"
		"	cmp	r9, #9												\n"
		"	bne	reg2_error_loop										\n"
		"	cmp	r10, #10											\n"
		"	bne	reg2_error_loop										\n"
		"	cmp	r11, #11											\n"
		"	bne	reg2_error_loop										\n"
		"	cmp	r12, #12											\n"
		"	bne	reg2_error_loop										\n"
		"															\n"
		"	/* Increment the loop counter to indicate this test is still functioning\n"
		"	correctly. */											\n"
		"	push { r0-r1 }											\n"
		"	ldr	r0, =ulRegTest2LoopCounter							\n"
		"	ldr r1, [r0]											\n"
		"	adds r1, r1, #1											\n"
		"	str r1, [r0]											\n"
		"															\n"
		"	/* Yield to increase test coverage. */ 					\n"
		"	movs r0, #0x01											\n"
		"	ldr r1, =0xe000ed04 									\n" /* NVIC_INT_CTRL */
		"	lsl r0, #28 											\n" /* Shift to PendSV bit */
		"	str r0, [r1]											\n"
		"	dsb														\n"
		"	pop { r0-r1 }											\n"
		"															\n"
		"	/* Start again. */										\n"
		"	b reg2_loop												\n"
		"															\n"
		"reg2_error_loop:											\n"
		"	/* If this line is hit then there was an error in a core register value.\n"
		"	This loop ensures the loop counter variable stops incrementing. */\n"
		"	b reg2_error_loop										\n"
		"	nop														\n"
	);

	/* Remove compiler warnings about unused parameters. */
	( void ) pvParameters;
}
