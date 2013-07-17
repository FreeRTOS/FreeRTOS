/*
    FreeRTOS V7.5.0 - Copyright (C) 2013 Real Time Engineers Ltd.

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

#error "The batch file Demo\CORTEX_LPC1768_GCC_RedSuite\CreateProjectDirectoryStructure.bat must be executed before the first build.  After executing the batch file hit F5 to refrech the Eclipse project, then delete this line."


/*
 * This file demonstrates the use of FreeRTOS-MPU.  It creates tasks in both
 * User mode and Privileged mode, and using both the original xTaskCreate() and
 * the new xTaskCreateRestricted() API functions.  The purpose of each created
 * task is documented in the comments above the task function prototype (in
 * this file), with the task behaviour demonstrated and documented within the 
 * task function itself.  In addition a queue is used to demonstrate passing
 * data between protected/restricted tasks as well as passing data between an
 * interrupt and a protected/restricted task.
 */



/* Library includes. */
#include <string.h>

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"

/* Red Suite includes. */
#include "lcd_driver.h"
#include "lcd.h"


/*-----------------------------------------------------------*/

/* Misc constants. */
#define mainDONT_BLOCK					( 0 )

/* Definitions for the messages that can be sent to the check task. */
#define mainREG_TEST_1_STILL_EXECUTING	( 0 )
#define mainREG_TEST_2_STILL_EXECUTING	( 1 )
#define mainPRINT_SYSTEM_STATUS			( 2 )

/* GCC specifics. */
#define mainALIGN_TO( x )				__attribute__((aligned(x)))

/* Hardware specifics.  The start and end address are chosen to ensure the
required GPIO are covered while also ensuring the necessary alignment is
achieved. */
#define mainGPIO_START_ADDRESS			( ( unsigned long * ) 0x2009c000 )
#define mainGPIO_END_ADDRESS			( mainGPIO_START_ADDRESS + ( 64 * 1024 ) )


/*-----------------------------------------------------------*/
/* Prototypes for functions that implement tasks. -----------*/
/*-----------------------------------------------------------*/

/* 
 * Prototype for the reg test tasks.  Amongst other things, these fill the CPU
 * registers with known values before checking that the registers still contain
 * the expected values.  Each of the two tasks use different values so an error
 * in the context switch mechanism can be caught.  Both reg test tasks execute
 * at the idle priority so will get preempted regularly.  Each task repeatedly
 * sends a message on a queue so long as it remains functioning correctly.  If
 * an error is detected within the task the task is simply deleted.
 */
static void prvRegTest1Task( void *pvParameters );
static void prvRegTest2Task( void *pvParameters );

/*
 * Prototype for the check task.  The check task demonstrates various features
 * of the MPU before entering a loop where it waits for messages to arrive on a
 * queue.
 *
 * Two types of messages can be processes:
 *
 * 1) "I'm Alive" messages sent from the reg test tasks, indicating that the
 *    task is still operational.
 *
 * 2) "Print Status commands" sent periodically by the tick hook function (and
 *    therefore from within an interrupt) which command the check task to write
 *    either pass or fail to the terminal, depending on the status of the reg
 *    test tasks.
 */
static void prvCheckTask( void *pvParameters );

/*
 * Prototype for a task created in User mode using the original vTaskCreate() 
 * API function.  The task demonstrates the characteristics of such a task,
 * before simply deleting itself.
 */
static void prvOldStyleUserModeTask( void *pvParameters );

/*
 * Prototype for a task created in Privileged mode using the original 
 * vTaskCreate() API function.  The task demonstrates the characteristics of 
 * such a task, before simply deleting itself.
 */
static void prvOldStylePrivilegedModeTask( void *pvParameters );


/*-----------------------------------------------------------*/
/* Prototypes for other misc functions.  --------------------*/
/*-----------------------------------------------------------*/

/*
 * Just configures any clocks and IO necessary.
 */
static void prvSetupHardware( void );

/*
 * Simply deletes the calling task.  The function is provided only because it
 * is simpler to call from asm code than the normal vTaskDelete() API function.
 * It has the noinline attribute because it is called from asm code.
 */
static void prvDeleteMe( void ) __attribute__((noinline));

/*
 * Used by both reg test tasks to send messages to the check task.  The message
 * just lets the check task know that the task is still functioning correctly.
 * If a reg test task detects an error it will delete itself, and in so doing
 * prevent itself from sending any more 'I'm Alive' messages to the check task.
 */
static void prvSendImAlive( xQueueHandle xHandle, unsigned long ulTaskNumber );

/*
 * The check task is created with access to three memory regions (plus its
 * stack).  Each memory region is configured with different parameters and
 * prvTestMemoryRegions() demonstrates what can and cannot be accessed for each
 * region.  prvTestMemoryRegions() also demonstrates a task that was created
 * as a privileged task settings its own privilege level down to that of a user
 * task.
 */
static void prvTestMemoryRegions( void );

/*-----------------------------------------------------------*/

/* The handle of the queue used to communicate between tasks and between tasks
and interrupts.  Note that this is a file scope variable that falls outside of
any MPU region.  As such other techniques have to be used to allow the tasks
to gain access to the queue.  See the comments in the tasks themselves for 
further information. */
static xQueueHandle xFileScopeCheckQueue = NULL;



/*-----------------------------------------------------------*/
/* Data used by the 'check' task. ---------------------------*/
/*-----------------------------------------------------------*/

/* Define the constants used to allocate the check task stack.  Note that the
stack size is defined in words, not bytes. */
#define mainCHECK_TASK_STACK_SIZE_WORDS	128
#define mainCHECK_TASK_STACK_ALIGNMENT ( mainCHECK_TASK_STACK_SIZE_WORDS * sizeof( portSTACK_TYPE ) )

/* Declare the stack that will be used by the check task.  The kernel will
 automatically create an MPU region for the stack.  The stack alignment must 
 match its size, so if 128 words are reserved for the stack then it must be 
 aligned to ( 128 * 4 ) bytes. */
static portSTACK_TYPE xCheckTaskStack[ mainCHECK_TASK_STACK_SIZE_WORDS ] mainALIGN_TO( mainCHECK_TASK_STACK_ALIGNMENT );

/* Declare three arrays - an MPU region will be created for each array
using the xTaskParameters structure below.  THIS IS JUST TO DEMONSTRATE THE
MPU FUNCTIONALITY, the data is not used by the check tasks primary function
of monitoring the reg test tasks and printing out status information.

Note that the arrays allocate slightly more RAM than is actually assigned to 
the MPU region.  This is to permit writes off the end of the array to be 
detected even when the arrays are placed in adjacent memory locations (with no 
gaps between them).  The align size must be a power of two. */
#define mainREAD_WRITE_ARRAY_SIZE 130
#define mainREAD_WRITE_ALIGN_SIZE 128
char cReadWriteArray[ mainREAD_WRITE_ARRAY_SIZE ] mainALIGN_TO( mainREAD_WRITE_ALIGN_SIZE );

#define mainREAD_ONLY_ARRAY_SIZE 260
#define mainREAD_ONLY_ALIGN_SIZE 256
char cReadOnlyArray[ mainREAD_ONLY_ARRAY_SIZE ] mainALIGN_TO( mainREAD_ONLY_ALIGN_SIZE );

#define mainPRIVILEGED_ONLY_ACCESS_ARRAY_SIZE 130
#define mainPRIVILEGED_ONLY_ACCESS_ALIGN_SIZE 128
char cPrivilegedOnlyAccessArray[ mainPRIVILEGED_ONLY_ACCESS_ALIGN_SIZE ] mainALIGN_TO( mainPRIVILEGED_ONLY_ACCESS_ALIGN_SIZE );

/* Fill in a xTaskParameters structure to define the check task - this is the
structure passed to the xTaskCreateRestricted() function. */
static const xTaskParameters xCheckTaskParameters =
{
	prvCheckTask,								/* pvTaskCode - the function that implements the task. */
	( signed char * ) "Check",					/* pcName			*/
	mainCHECK_TASK_STACK_SIZE_WORDS,			/* usStackDepth	- defined in words, not bytes. */
	( void * ) 0x12121212,						/* pvParameters - this value is just to test that the parameter is being passed into the task correctly. */
	( tskIDLE_PRIORITY + 1 ) | portPRIVILEGE_BIT,/* uxPriority - this is the highest priority task in the system.  The task is created in privileged mode to demonstrate accessing the privileged only data. */
	xCheckTaskStack,							/* puxStackBuffer - the array to use as the task stack, as declared above. */

	/* xRegions - In this case the xRegions array is used to create MPU regions
	for all three of the arrays declared directly above.  Each MPU region is
	created with different parameters.  Again, THIS IS JUST TO DEMONSTRATE THE
	MPU FUNCTIONALITY, the data is not used by the check tasks primary function
	of monitoring the reg test tasks and printing out status information.*/
	{											
		/* Base address					Length									Parameters */
        { cReadWriteArray,				mainREAD_WRITE_ALIGN_SIZE,				portMPU_REGION_READ_WRITE },
        { cReadOnlyArray,				mainREAD_ONLY_ALIGN_SIZE,				portMPU_REGION_READ_ONLY },
        { cPrivilegedOnlyAccessArray,	mainPRIVILEGED_ONLY_ACCESS_ALIGN_SIZE,	portMPU_REGION_PRIVILEGED_READ_WRITE }
	}
};

/* Three MPU regions are defined for use by the 'check' task when the task is 
created.  These are only used to demonstrate the MPU features and are not
actually necessary for the check task to fulfill its primary purpose.  Instead
the MPU regions are replaced with those defined by xAltRegions prior to the 
check task receiving any data on the queue or printing any messages to the
debug console.  The MPU region defined below covers the GPIO peripherals used
to write to the LCD. */
static const xMemoryRegion xAltRegions[ portNUM_CONFIGURABLE_REGIONS ] =
{											
	/* Base address				Length			Parameters */
	{ mainGPIO_START_ADDRESS,	( 64 * 1024 ),	portMPU_REGION_READ_WRITE },
	{ 0,						0,				0 },
	{ 0,						0,				0 }
};



/*-----------------------------------------------------------*/
/* Data used by the 'reg test' tasks. -----------------------*/
/*-----------------------------------------------------------*/

/* Define the constants used to allocate the reg test task stacks.  Note that
that stack size is defined in words, not bytes. */
#define mainREG_TEST_STACK_SIZE_WORDS	128
#define mainREG_TEST_STACK_ALIGNMENT	( mainREG_TEST_STACK_SIZE_WORDS * sizeof( portSTACK_TYPE ) )

/* Declare the stacks that will be used by the reg test tasks.  The kernel will
automatically create an MPU region for the stack.  The stack alignment must 
match its size, so if 128 words are reserved for the stack then it must be 
aligned to ( 128 * 4 ) bytes. */
static portSTACK_TYPE xRegTest1Stack[ mainREG_TEST_STACK_SIZE_WORDS ] mainALIGN_TO( mainREG_TEST_STACK_ALIGNMENT );
static portSTACK_TYPE xRegTest2Stack[ mainREG_TEST_STACK_SIZE_WORDS ] mainALIGN_TO( mainREG_TEST_STACK_ALIGNMENT );

/* Fill in a xTaskParameters structure per reg test task to define the tasks. */
static const xTaskParameters xRegTest1Parameters =
{
	prvRegTest1Task,						/* pvTaskCode - the function that implements the task. */
	( signed char * ) "RegTest1",			/* pcName			*/
	mainREG_TEST_STACK_SIZE_WORDS,			/* usStackDepth		*/
	( void * ) 0x12345678,					/* pvParameters - this value is just to test that the parameter is being passed into the task correctly. */
	tskIDLE_PRIORITY | portPRIVILEGE_BIT,	/* uxPriority - note that this task is created with privileges to demonstrate one method of passing a queue handle into the task. */
	xRegTest1Stack,							/* puxStackBuffer - the array to use as the task stack, as declared above. */
	{										/* xRegions - this task does not use any non-stack data hence all members are zero. */
		/* Base address		Length		Parameters */
        { 0x00,				0x00,			0x00 },
        { 0x00,				0x00,			0x00 },
        { 0x00,				0x00,			0x00 }
	}
};
/*-----------------------------------------------------------*/

static xTaskParameters xRegTest2Parameters =
{
	prvRegTest2Task,				/* pvTaskCode - the function that implements the task. */
	( signed char * ) "RegTest2",	/* pcName			*/
	mainREG_TEST_STACK_SIZE_WORDS,	/* usStackDepth		*/
	( void * ) NULL,				/* pvParameters	- this task uses the parameter to pass in a queue handle, but the queue is not created yet. */
	tskIDLE_PRIORITY,				/* uxPriority		*/
	xRegTest2Stack,					/* puxStackBuffer - the array to use as the task stack, as declared above. */
	{								/* xRegions - this task does not use any non-stack data hence all members are zero. */
		/* Base address		Length		Parameters */
        { 0x00,				0x00,			0x00 },
        { 0x00,				0x00,			0x00 },
        { 0x00,				0x00,			0x00 }
	}
};

/*-----------------------------------------------------------*/

int main( void )
{
	prvSetupHardware();

	/* Create the queue used to pass "I'm alive" messages to the check task. */
	xFileScopeCheckQueue = xQueueCreate( 1, sizeof( unsigned long ) );

	/* One check task uses the task parameter to receive the queue handle.
	This allows the file scope variable to be accessed from within the task.
	The pvParameters member of xRegTest2Parameters can only be set after the
	queue has been created so is set here. */
	xRegTest2Parameters.pvParameters = xFileScopeCheckQueue;

	/* Create the three test tasks.  Handles to the created tasks are not
	required, hence the second parameter is NULL. */
	xTaskCreateRestricted( &xRegTest1Parameters, NULL );
    xTaskCreateRestricted( &xRegTest2Parameters, NULL );
	xTaskCreateRestricted( &xCheckTaskParameters, NULL );

	/* Create the tasks that are created using the original xTaskCreate() API
	function. */
	xTaskCreate(	prvOldStyleUserModeTask,	/* The function that implements the task. */
					( signed char * ) "Task1",	/* Text name for the task. */
					100,						/* Stack depth in words. */
					NULL,						/* Task parameters. */
					3,							/* Priority and mode (user in this case). */
					NULL						/* Handle. */
				);

	xTaskCreate(	prvOldStylePrivilegedModeTask,	/* The function that implements the task. */
					( signed char * ) "Task2",		/* Text name for the task. */
					100,							/* Stack depth in words. */
					NULL,							/* Task parameters. */
					( 3 | portPRIVILEGE_BIT ),		/* Priority and mode. */
					NULL							/* Handle. */
				);

	/* Start the scheduler. */
	vTaskStartScheduler();

	/* Will only get here if there was insufficient memory to create the idle
	task. */
	for( ;; );
	return 0;
}
/*-----------------------------------------------------------*/

static void prvCheckTask( void *pvParameters )
{
/* This task is created in privileged mode so can access the file scope
queue variable.  Take a stack copy of this before the task is set into user
mode.  Once that task is in user mode the file scope queue variable will no
longer be accessible but the stack copy will. */
xQueueHandle xQueue = xFileScopeCheckQueue;
long lMessage;
unsigned long ulStillAliveCounts[ 2 ] = { 0 };
char *pcStatusMessage = "PASS\r\n";
unsigned char x = 5, y = 10;

	/* Just to remove compiler warning. */
	( void ) pvParameters;

	/* Demonstrate how the various memory regions can and can't be accessed. 
	The task privilege is set down to user mode within this function. */
	prvTestMemoryRegions();

	/* Change the memory regions allocated to this task to those initially
	set up for demonstration purposes to those actually required by the task. */
	vTaskAllocateMPURegions( NULL, xAltRegions );

	/* This loop performs the main function of the task, which is blocking
	on a message queue then processing each message as it arrives. */
	for( ;; )
	{
		/* Wait for the next message to arrive. */
		xQueueReceive( xQueue, &lMessage, portMAX_DELAY );
		
		switch( lMessage )
		{
			case mainREG_TEST_1_STILL_EXECUTING	:	
					/* Message from task 1, so task 1 must still be executing. */
					( ulStillAliveCounts[ 0 ] )++;
					break;

			case mainREG_TEST_2_STILL_EXECUTING	:						
					/* Message from task 2, so task 2 must still be executing. */
					( ulStillAliveCounts[ 1 ] )++;
					break;

			case mainPRINT_SYSTEM_STATUS		:	
					/* Message from tick hook, time to print out the system
					status.  If messages has stopped arriving from either reg
					test task then the status must be set to fail. */
					if( ( ulStillAliveCounts[ 0 ] == 0 ) || ( ulStillAliveCounts[ 1 ] == 0 )  )
					{
						/* One or both of the test tasks are no longer sending 
						'still alive' messages. */
						pcStatusMessage = "FAIL\r\n";
					}

					/* Print a pass/fail message to the LCD - moving the
					message each time to provide feedback that the output
					is still being produced.  LCD_PrintString() accesses const
					data stored in flash, which all tasks are at liberty to do, 
					and GPIO for which an MPU region has been set up for it. */
					LCD_ClearScreen();
					LCD_PrintString( x>>1, y>>1, pcStatusMessage, 6, COLOR_RED );
					x += 7;
					y += 9;

					/* Reset the count of 'still alive' messages. */
					memset( ulStillAliveCounts, 0x00, sizeof( ulStillAliveCounts ) );
					break;

		default :
					/* Something unexpected happened.  Delete this task so the 
					error is apparent (no output will be displayed). */
					prvDeleteMe();
					break;
		}
	}
}
/*-----------------------------------------------------------*/

static void prvTestMemoryRegions( void )
{
long l;
char cTemp;

	/* The check task (from which this function is called) is created in the 
	Privileged mode.  The privileged array can be both read from and written 
	to while this task is privileged. */
	cPrivilegedOnlyAccessArray[ 0 ] = 'a';
	if( cPrivilegedOnlyAccessArray[ 0 ] != 'a' )
	{
		/* Something unexpected happened.  Delete this task so the error is
		apparent (no output will be displayed). */
		prvDeleteMe();
	}

	/* Writing off the end of the RAM allocated to this task will *NOT* cause a
	protection fault because the task is still executing in a privileged mode.  
	Uncomment the following to test. */
	/* cPrivilegedOnlyAccessArray[ mainPRIVILEGED_ONLY_ACCESS_ALIGN_SIZE ] = 'a'; */

	/* Now set the task into user mode. */
	portSWITCH_TO_USER_MODE();
	 
	/* Accessing the privileged only array will now cause a fault.  Uncomment 
	the following line to test. */    
	/* cPrivilegedOnlyAccessArray[ 0 ] = 'a'; */

	/* The read/write array can still be successfully read and written. */
	for( l = 0; l < mainREAD_WRITE_ALIGN_SIZE; l++ )
	{
		cReadWriteArray[ l ] = 'a';
		if( cReadWriteArray[ l ] != 'a' )
		{
			/* Something unexpected happened.  Delete this task so the error is
			apparent (no output will be displayed). */
			prvDeleteMe();
		}
	}

	/* But attempting to read or write off the end of the RAM allocated to this
	task will cause a fault.  Uncomment either of the following two lines to 
	test. */
	/* cReadWriteArray[ 0 ] = cReadWriteArray[ -1 ]; */
	/* cReadWriteArray[ mainREAD_WRITE_ALIGN_SIZE ] = 0x00; */

	/* The read only array can be successfully read... */
	for( l = 0; l < mainREAD_ONLY_ALIGN_SIZE; l++ )
	{
		cTemp = cReadOnlyArray[ l ];
	}

	/* ...but cannot be written.  Uncomment the following line to test. */
	/* cReadOnlyArray[ 0 ] = 'a'; */

	/* Writing to the first and last locations in the stack array should not 
	cause a protection fault.  Note that doing this will cause the kernel to
	detect a stack overflow if configCHECK_FOR_STACK_OVERFLOW is greater than 
	1. */
    xCheckTaskStack[ 0 ] = 0;
    xCheckTaskStack[ mainCHECK_TASK_STACK_SIZE_WORDS - 1 ] = 0;

	/* Writing off either end of the stack array should cause a protection 
	fault, uncomment either of the following two lines to test. */
	/* xCheckTaskStack[ -1 ] = 0; */
    /* xCheckTaskStack[ mainCHECK_TASK_STACK_SIZE_WORDS ] = 0; */
}
/*-----------------------------------------------------------*/

static void prvRegTest1Task( void *pvParameters )
{
/* This task is created in privileged mode so can access the file scope
queue variable.  Take a stack copy of this before the task is set into user
mode.  Once this task is in user mode the file scope queue variable will no
longer be accessible but the stack copy will. */
xQueueHandle xQueue = xFileScopeCheckQueue;

	/* Now the queue handle has been obtained the task can switch to user 
	mode.  This is just one method of passing a handle into a protected
	task, the other	reg test task uses the task parameter instead. */
    portSWITCH_TO_USER_MODE();

	/* First check that the parameter value is as expected. */
	if( pvParameters != ( void * ) 0x12345678 )
	{
		/* Error detected.  Delete the task so it stops communicating with
		the check task. */
		prvDeleteMe();
	}


	for( ;; )
	{		
		/* This task tests the kernel context switch mechanism by reading and
		writing directly to registers - which requires the test to be written
		in assembly code. */
		__asm volatile 
		(	
			"		MOV	R4, #104			\n" /* Set registers to a known value.  R0 to R1 are done in the loop below. */
			"		MOV	R5, #105			\n"
			"		MOV	R6, #106			\n"
			"		MOV	R8, #108			\n"
			"		MOV	R9, #109			\n"
			"		MOV	R10, #110			\n"
			"		MOV	R11, #111			\n"
			"reg1loop:						\n"
			"		MOV	R0, #100			\n" /* Set the scratch registers to known values - done inside the loop as they get clobbered. */
			"		MOV	R1, #101			\n"
			"		MOV	R2, #102			\n"
			"		MOV R3, #103			\n"
			"		MOV	R12, #112			\n"
			"		SVC #1					\n" /* Yield just to increase test coverage. */
			"		CMP	R0, #100			\n" /* Check all the registers still contain their expected values. */
			"		BNE	prvDeleteMe			\n" /* Value was not as expected, delete the task so it stops communicating with the check task. */
			"		CMP	R1, #101			\n"
			"		BNE	prvDeleteMe			\n"
			"		CMP	R2, #102			\n"
			"		BNE	prvDeleteMe			\n"
			"		CMP R3, #103			\n"
			"		BNE	prvDeleteMe			\n"
			"		CMP	R4, #104			\n" 
			"		BNE	prvDeleteMe			\n" 
			"		CMP	R5, #105			\n"
			"		BNE	prvDeleteMe			\n"
			"		CMP	R6, #106			\n"
			"		BNE	prvDeleteMe			\n"
			"		CMP	R8, #108			\n"
			"		BNE	prvDeleteMe			\n"
			"		CMP	R9, #109			\n"
			"		BNE	prvDeleteMe			\n"
			"		CMP	R10, #110			\n"
			"		BNE	prvDeleteMe			\n"
			"		CMP	R11, #111			\n"
			"		BNE	prvDeleteMe			\n"
			"		CMP	R12, #112			\n"
			"		BNE	prvDeleteMe			\n"
			:::"r0", "r1", "r2", "r3", "r4", "r5", "r6", "r8", "r9", "r10", "r11", "r12"
		);

		/* Send mainREG_TEST_1_STILL_EXECUTING to the check task to indicate that this 
		task is still functioning. */
		prvSendImAlive( xQueue, mainREG_TEST_1_STILL_EXECUTING );

		/* Go back to check all the register values again. */
		__asm volatile( "		B reg1loop	" );
	}
}
/*-----------------------------------------------------------*/

static void prvRegTest2Task( void *pvParameters )
{
/* The queue handle is passed in as the task parameter.  This is one method of
passing data into a protected task, the other reg test task uses a different 
method. */
xQueueHandle xQueue = ( xQueueHandle ) pvParameters;

	for( ;; )
	{
		/* This task tests the kernel context switch mechanism by reading and
		writing directly to registers - which requires the test to be written
		in assembly code. */
		__asm volatile 
		(	
			"		MOV	R4, #4				\n" /* Set registers to a known value.  R0 to R1 are done in the loop below. */
			"		MOV	R5, #5				\n"
			"		MOV	R6, #6				\n"
			"		MOV	R8, #8				\n" /* Frame pointer is omitted as it must not be changed. */
			"		MOV	R9, #9				\n"
			"		MOV	R10, 10				\n"
			"		MOV	R11, #11			\n"						
			"reg2loop:						\n"
			"		MOV	R0, #13				\n" /* Set the scratch registers to known values - done inside the loop as they get clobbered. */
			"		MOV	R1, #1				\n"
			"		MOV	R2, #2				\n"
			"		MOV R3, #3				\n"
			"		MOV	R12, #12			\n"
			"		CMP	R0, #13				\n" /* Check all the registers still contain their expected values. */
			"		BNE	prvDeleteMe			\n" /* Value was not as expected, delete the task so it stops communicating with the check task */
			"		CMP	R1, #1				\n"
			"		BNE	prvDeleteMe			\n"
			"		CMP	R2, #2				\n"
			"		BNE	prvDeleteMe			\n"
			"		CMP R3, #3				\n"
			"		BNE	prvDeleteMe			\n"
			"		CMP	R4, #4				\n"
			"		BNE	prvDeleteMe			\n"
			"		CMP	R5, #5				\n"
			"		BNE	prvDeleteMe			\n"
			"		CMP	R6, #6				\n"
			"		BNE	prvDeleteMe			\n"
			"		CMP	R8, #8				\n"
			"		BNE	prvDeleteMe			\n"
			"		CMP	R9, #9				\n"
			"		BNE	prvDeleteMe			\n"
			"		CMP	R10, #10			\n"
			"		BNE	prvDeleteMe			\n"
			"		CMP	R11, #11			\n"
			"		BNE	prvDeleteMe			\n"
			"		CMP	R12, #12			\n"
			"		BNE	prvDeleteMe			\n"
            :::"r0", "r1", "r2", "r3", "r4", "r5", "r6", "r8", "r9", "r10", "r11", "r12"
		);

		/* Send mainREG_TEST_2_STILL_EXECUTING to the check task to indicate that this 
		task is still functioning. */
		prvSendImAlive( xQueue, mainREG_TEST_2_STILL_EXECUTING );

		/* Go back to check all the register values again. */
		__asm volatile( "		B reg2loop	" );
	}
}
/*-----------------------------------------------------------*/

void vApplicationIdleHook( void )
{
extern unsigned long __SRAM_segment_end__[];
extern unsigned long __privileged_data_start__[];
extern unsigned long __privileged_data_end__[];
extern unsigned long __FLASH_segment_start__[];
extern unsigned long __FLASH_segment_end__[];
volatile unsigned long *pul;
volatile unsigned long ulReadData;

	/* The idle task, and therefore this function, run in Supervisor mode and
	can therefore access all memory.  Try reading from corners of flash and
	RAM to ensure a memory fault does not occur. 
	
	Start with the edges of the privileged data area. */
	pul = __privileged_data_start__;
	ulReadData = *pul;
	pul = __privileged_data_end__ - 1;
	ulReadData = *pul;

	/* Next the standard SRAM area. */
	pul = __SRAM_segment_end__ - 1;
	ulReadData = *pul;

	/* And the standard Flash area - the start of which is marked for
	privileged access only. */
	pul = __FLASH_segment_start__;
	ulReadData = *pul;
	pul = __FLASH_segment_end__ - 1;
	ulReadData = *pul;

	/* Reading off the end of Flash or SRAM space should cause a fault.  
	Uncomment one of the following two pairs of lines to test. */
	
	/* pul = __FLASH_segment_end__ + 4;
	ulReadData = *pul; */

	/* pul = __SRAM_segment_end__ + 1;
	ulReadData = *pul; */
}
/*-----------------------------------------------------------*/

static void prvOldStyleUserModeTask( void *pvParameters )
{
extern unsigned long __privileged_data_start__[];
extern unsigned long __privileged_data_end__[];
extern unsigned long __SRAM_segment_end__[];
extern unsigned long __privileged_functions_end__[];
extern unsigned long __FLASH_segment_start__[];
extern unsigned long __FLASH_segment_end__[];
const volatile unsigned long *pulStandardPeripheralRegister = ( volatile unsigned long * ) 0x400FC0C4; /* PCONP */
volatile unsigned long *pul;
volatile unsigned long ulReadData;

/* The following lines are commented out to prevent the unused variable 
compiler warnings when the tests that use the variable are also commented out.
extern unsigned long __privileged_functions_start__[];
const volatile unsigned long *pulSystemPeripheralRegister = ( volatile unsigned long * ) 0xe000e014; */

	( void ) pvParameters;

	/* This task is created in User mode using the original xTaskCreate() API
	function.  It should have access to all Flash and RAM except that marked
	as Privileged access only.  Reading from the start and end of the non-
	privileged RAM should not cause a problem (the privileged RAM is the first
	block at the bottom of the RAM memory). */
	pul = __privileged_data_end__ + 1;
	ulReadData = *pul;
	pul = __SRAM_segment_end__ - 1;
	ulReadData = *pul;

	/* Likewise reading from the start and end of the non-privileged Flash
	should not be a problem (the privileged Flash is the first block at the
	bottom of the Flash memory). */
	pul = __privileged_functions_end__ + 1;
	ulReadData = *pul;
	pul = __FLASH_segment_end__ - 1;
	ulReadData = *pul;

	/* Standard peripherals are accessible. */
	ulReadData = *pulStandardPeripheralRegister;

	/* System peripherals are not accessible.  Uncomment the following line
	to test.  Also uncomment the declaration of pulSystemPeripheralRegister
	at the top of this function. */
    /* ulReadData = *pulSystemPeripheralRegister; */

	/* Reading from anywhere inside the privileged Flash or RAM should cause a
	fault.  This can be tested by uncommenting any of the following pairs of
	lines.  Also uncomment the declaration of __privileged_functions_start__
	at the top of this function. */

	/* pul = __privileged_functions_start__;
	ulReadData = *pul; */
	
	/* pul = __privileged_functions_end__ - 1;
	ulReadData = *pul; */

	/* pul = __privileged_data_start__;
	ulReadData = *pul; */ 
	
	/* pul = __privileged_data_end__ - 1;
	ulReadData = *pul; */

	/* Must not just run off the end of a task function, so delete this task. 
	Note that because this task was created using xTaskCreate() the stack was
	allocated dynamically and I have not included any code to free it again. */
	vTaskDelete( NULL );
}
/*-----------------------------------------------------------*/

static void prvOldStylePrivilegedModeTask( void *pvParameters )
{
extern unsigned long __privileged_data_start__[];
extern unsigned long __privileged_data_end__[];
extern unsigned long __SRAM_segment_end__[];
extern unsigned long __privileged_functions_start__[];
extern unsigned long __privileged_functions_end__[];
extern unsigned long __FLASH_segment_start__[];
extern unsigned long __FLASH_segment_end__[];
volatile unsigned long *pul;
volatile unsigned long ulReadData;
const volatile unsigned long *pulSystemPeripheralRegister = ( volatile unsigned long * ) 0xe000e014; /* Systick */
const volatile unsigned long *pulStandardPeripheralRegister = ( volatile unsigned long * ) 0x400FC0C4; /* PCONP */

	( void ) pvParameters;

	/* This task is created in Privileged mode using the original xTaskCreate() 
	API	function.  It should have access to all Flash and RAM including that 
	marked as Privileged access only.  So reading from the start and end of the 
	non-privileged RAM should not cause a problem (the privileged RAM is the 
	first block at the bottom of the RAM memory). */
	pul = __privileged_data_end__ + 1;
	ulReadData = *pul;
	pul = __SRAM_segment_end__ - 1;
	ulReadData = *pul;

	/* Likewise reading from the start and end of the non-privileged Flash
	should not be a problem (the privileged Flash is the first block at the
	bottom of the Flash memory). */
	pul = __privileged_functions_end__ + 1;
	ulReadData = *pul;
	pul = __FLASH_segment_end__ - 1;
	ulReadData = *pul;

	/* Reading from anywhere inside the privileged Flash or RAM should also
	not be a problem. */
	pul = __privileged_functions_start__;
	ulReadData = *pul;
	pul = __privileged_functions_end__ - 1;
	ulReadData = *pul;
	pul = __privileged_data_start__;
	ulReadData = *pul;	
	pul = __privileged_data_end__ - 1;
	ulReadData = *pul;

	/* Finally, accessing both System and normal peripherals should both be
	possible. */
    ulReadData = *pulSystemPeripheralRegister;
	ulReadData = *pulStandardPeripheralRegister;

	/* Must not just run off the end of a task function, so delete this task. 
	Note that because this task was created using xTaskCreate() the stack was
	allocated dynamically and I have not included any code to free it again. */
	vTaskDelete( NULL );
}
/*-----------------------------------------------------------*/

static void prvDeleteMe( void )
{
	vTaskDelete( NULL );
}
/*-----------------------------------------------------------*/

static void prvSendImAlive( xQueueHandle xHandle, unsigned long ulTaskNumber )
{
	if( xHandle != NULL )
	{
		xQueueSend( xHandle, &ulTaskNumber, mainDONT_BLOCK );
	}
}
/*-----------------------------------------------------------*/

void prvSetupHardware( void )
{
	/* Disable peripherals power. */
	SC->PCONP = 0;

	/* Enable GPIO power. */
	SC->PCONP = PCONP_PCGPIO;

	/* Disable TPIU. */
	PINCON->PINSEL10 = 0;

	if ( SC->PLL0STAT & ( 1 << 25 ) )
	{
		/* Enable PLL, disconnected. */
		SC->PLL0CON = 1;			
		SC->PLL0FEED = PLLFEED_FEED1;
		SC->PLL0FEED = PLLFEED_FEED2;
	}
	
	/* Disable PLL, disconnected. */
	SC->PLL0CON = 0;				
	SC->PLL0FEED = PLLFEED_FEED1;
	SC->PLL0FEED = PLLFEED_FEED2;
	    
	/* Enable main OSC. */
	SC->SCS |= 0x20;			
	while( !( SC->SCS & 0x40 ) );
	
	/* select main OSC, 12MHz, as the PLL clock source. */
	SC->CLKSRCSEL = 0x1;		
	
	SC->PLL0CFG = 0x20031;
	SC->PLL0FEED = PLLFEED_FEED1;
	SC->PLL0FEED = PLLFEED_FEED2;
	      
	/* Enable PLL, disconnected. */
	SC->PLL0CON = 1;				
	SC->PLL0FEED = PLLFEED_FEED1;
	SC->PLL0FEED = PLLFEED_FEED2;
	
	/* Set clock divider. */
	SC->CCLKCFG = 0x03;
	
	/* Configure flash accelerator. */
	SC->FLASHCFG = 0x403a;
	
	/* Check lock bit status. */
	while( ( ( SC->PLL0STAT & ( 1 << 26 ) ) == 0 ) );	
	    
	/* Enable and connect. */
	SC->PLL0CON = 3;				
	SC->PLL0FEED = PLLFEED_FEED1;
	SC->PLL0FEED = PLLFEED_FEED2;
	while( ( ( SC->PLL0STAT & ( 1 << 25 ) ) == 0 ) );	

	
	
	
	/* Configure the clock for the USB. */
	  
	if( SC->PLL1STAT & ( 1 << 9 ) )
	{
		/* Enable PLL, disconnected. */
		SC->PLL1CON = 1;			
		SC->PLL1FEED = PLLFEED_FEED1;
		SC->PLL1FEED = PLLFEED_FEED2;
	}
	
	/* Disable PLL, disconnected. */
	SC->PLL1CON = 0;				
	SC->PLL1FEED = PLLFEED_FEED1;
	SC->PLL1FEED = PLLFEED_FEED2;
	
	SC->PLL1CFG = 0x23;
	SC->PLL1FEED = PLLFEED_FEED1;
	SC->PLL1FEED = PLLFEED_FEED2;
	      
	/* Enable PLL, disconnected. */
	SC->PLL1CON = 1;				
	SC->PLL1FEED = PLLFEED_FEED1;
	SC->PLL1FEED = PLLFEED_FEED2;
	while( ( ( SC->PLL1STAT & ( 1 << 10 ) ) == 0 ) );
	
	/* Enable and connect. */
	SC->PLL1CON = 3;				
	SC->PLL1FEED = PLLFEED_FEED1;
	SC->PLL1FEED = PLLFEED_FEED2;
	while( ( ( SC->PLL1STAT & ( 1 << 9 ) ) == 0 ) );

	/*  Setup the peripheral bus to be the same as the PLL output (64 MHz). */
	SC->PCLKSEL0 = 0x05555555;
	
	/* Prepare the LCD. */
	LCDdriver_initialisation();
	LCD_PrintString( 5, 10, "FreeRTOS.org", 14, COLOR_GREEN);
}
/*-----------------------------------------------------------*/

void vApplicationTickHook( void )
{
static unsigned long ulCallCount;
const unsigned long ulCallsBetweenSends = 5000 / portTICK_RATE_MS;
const unsigned long ulMessage = mainPRINT_SYSTEM_STATUS;
portBASE_TYPE xDummy;

	/* If configUSE_TICK_HOOK is set to 1 then this function will get called
	from each RTOS tick.  It is called from the tick interrupt and therefore
	will be executing in the privileged state. */

	ulCallCount++;

	/* Is it time to print out the pass/fail message again? */
	if( ulCallCount >= ulCallsBetweenSends )
	{
		ulCallCount = 0;

		/* Send a message to the check task to command it to check that all
		the tasks are still running then print out the status. 
		
		This is running in an ISR so has to use the "FromISR" version of
		xQueueSend().  Because it is in an ISR it is running with privileges
		so can access xFileScopeCheckQueue directly. */
		xQueueSendFromISR( xFileScopeCheckQueue, &ulMessage, &xDummy );
	}
}
/*-----------------------------------------------------------*/

void vApplicationStackOverflowHook( xTaskHandle pxTask, signed char *pcTaskName )
{
	/* If configCHECK_FOR_STACK_OVERFLOW is set to either 1 or 2 then this 
	function will automatically get called if a task overflows its stack. */
	( void ) pxTask;
	( void ) pcTaskName;
	for( ;; );
}
/*-----------------------------------------------------------*/

void vApplicationMallocFailedHook( void )
{
	/* If configUSE_MALLOC_FAILED_HOOK is set to 1 then this function will
	be called automatically if a call to pvPortMalloc() fails.  pvPortMalloc()
	is called automatically when a task, queue or semaphore is created. */
	for( ;; );
}
/*-----------------------------------------------------------*/


