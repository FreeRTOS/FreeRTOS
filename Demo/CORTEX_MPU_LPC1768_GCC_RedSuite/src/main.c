/*
    FreeRTOS V6.0.0 - Copyright (C) 2009 Real Time Engineers Ltd.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it    under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation and modified by the FreeRTOS exception.
    **NOTE** The exception to the GPL is included to allow you to distribute a
    combined work that includes FreeRTOS without being obliged to provide the
    source code for proprietary components outside of the FreeRTOS kernel.
    Alternative commercial license and support terms are also available upon
    request.  See the licensing section of http://www.FreeRTOS.org for full
    license details.

    FreeRTOS is distributed in the hope that it will be useful,    but WITHOUT
    ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
    FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
    more details.

    You should have received a copy of the GNU General Public License along
    with FreeRTOS; if not, write to the Free Software Foundation, Inc., 59
    Temple Place, Suite 330, Boston, MA  02111-1307  USA.


    ***************************************************************************
    *                                                                         *
    * The FreeRTOS eBook and reference manual are available to purchase for a *
    * small fee. Help yourself get started quickly while also helping the     *
    * FreeRTOS project! See http://www.FreeRTOS.org/Documentation for details *
    *                                                                         *
    ***************************************************************************

    1 tab == 4 spaces!

    Please ensure to read the configuration and relevant port sections of the
    online documentation.

    http://www.FreeRTOS.org - Documentation, latest information, license and
    contact details.

    http://www.SafeRTOS.com - A version that is certified for use in safety
    critical systems.

    http://www.OpenRTOS.com - Commercial support, development, porting,
    licensing and training services.
*/


//#error The batch file Demo\CORTEX_LPC1768_GCC_RedSuite\CreateProjectDirectoryStructure.bat must be executed before the first build.  After executing the batch file hit F5 to refrech the Eclipse project, then delete this line.

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

/*
 * This file demonstrates the use of MPU using just three tasks - two 'reg test'
 * tasks and one 'check' task.  Read the comments above the
 * function prototypes for more information.
 */

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
#define mainGPIO_START_ADDRESS			( 0x2009c000UL )
#define mainGPIO_END_ADDRESS			( mainGPIO_START_ADDRESS + ( 64 * 1024 ) )
/*-----------------------------------------------------------*/
/* Prototypes for functions that implement tasks. -----------*/
/*-----------------------------------------------------------*/

/* 
 * Prototype for the reg test tasks.  Amongst other things, these fill the CPU
 * registers with known values before checking that the registers still contain
 * the expected values.  Each of the two tasks use different values so an error
 * in the context switch mechanism can be caught.  Both reg test tasks execute
 * at the idle priority so will get preempted regularly.
 */
static void prvRegTest1Task( void *pvParameters );
static void prvRegTest2Task( void *pvParameters );

/*
 * Prototype for the check task.  The check task demonstrates various features
 * of the MPU before entering a loop where it waits for commands to arrive on a
 * queue.
 *
 * The check task will periodically be commanded to print out a status message.
 * If both the reg tests tasks are executing as expected the check task will
 * print "PASS" to the debug port, otherwise it will print 'FAIL'.  Debug port
 * messages can be viewed within the CrossWorks IDE.
 */
static void prvCheckTask( void *pvParameters );



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
 * just lets the check task know that the sending is still functioning correctly.
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
 using the xTaskParameters structure below.  Note that the arrays allocate 
slightly more RAM than is actually assigned to the MPU region.  This is to 
permit writes off the end of the array to be detected even when the arrays are 
placed in adjacent memory locations (with no gaps between them).  The align 
size must be a power of two. */
#define mainREAD_WRITE_ARRAY_SIZE 130
#define mainREAD_WRITE_ALIGN_SIZE 128
char cReadWriteArray[ mainREAD_WRITE_ARRAY_SIZE ] mainALIGN_TO( mainREAD_WRITE_ALIGN_SIZE );

#define mainREAD_ONLY_ARRAY_SIZE 260
#define mainREAD_ONLY_ALIGN_SIZE 256
char cReadOnlyArray[ mainREAD_ONLY_ARRAY_SIZE ] mainALIGN_TO( mainREAD_ONLY_ALIGN_SIZE );

#define mainPRIVILEGED_ONLY_ACCESS_ARRAY_SIZE 130
#define mainPRIVILEGED_ONLY_ACCESS_ALIGN_SIZE 128
char cPrivilegedOnlyAccessArray[ mainPRIVILEGED_ONLY_ACCESS_ALIGN_SIZE ] mainALIGN_TO( mainPRIVILEGED_ONLY_ACCESS_ALIGN_SIZE );

/* Fill in a xTaskParameters structure to define the check task. */
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
	created with different parameters. */
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
	{										/* xRegions - this task does not use any non-stack data. */
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
	{								/* xRegions - this task does not use any non-stack data. */
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
	queue has been created. */
	xRegTest2Parameters.pvParameters = xFileScopeCheckQueue;

	/* Create the three test tasks.  Handles to the created tasks are not
	required, hence the second parameter is NULL. */
	xTaskCreateRestricted( &xRegTest1Parameters, NULL );
    xTaskCreateRestricted( &xRegTest2Parameters, NULL );
	xTaskCreateRestricted( &xCheckTaskParameters, NULL );

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

	/* The check task is created in the privileged mode.  The privileged array 
	can be both read from and written to while this	task is privileged. */
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
	/*cPrivilegedOnlyAccessArray[ mainPRIVILEGED_ONLY_ACCESS_ALIGN_SIZE ] = 'a';*/

	/* Now set the task into user mode. */
	portSWITCH_TO_USER_MODE();
	 
	/* Accessing the privileged only array will now cause a fault.  Uncomment 
	the following line to test. */    
	/*cPrivilegedOnlyAccessArray[ 0 ] = 'a';*/

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
mode.  Once that task is in user mode the file scope queue variable will no
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
passing data into a protected task, the other check task uses a different 
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
		);

		/* Send mainREG_TEST_2_STILL_EXECUTING to the check task to indicate that this 
		task is still functioning. */
		prvSendImAlive( xQueue, mainREG_TEST_2_STILL_EXECUTING );

		/* Go back to check all the register values again. */
		__asm volatile( "		B reg2loop	" );
	}
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

void vApplicationStackOverflowHook( xTaskHandle *pxTask, signed char *pcTaskName )
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


