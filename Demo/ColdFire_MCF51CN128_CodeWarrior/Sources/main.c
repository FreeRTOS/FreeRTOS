/*
	FreeRTOS.org V5.3.1 - Copyright (C) 2003-2009 Richard Barry.

	This file is part of the FreeRTOS.org distribution.

	FreeRTOS.org is free software; you can redistribute it and/or modify it
	under the terms of the GNU General Public License (version 2) as published
	by the Free Software Foundation and modified by the FreeRTOS exception.
	**NOTE** The exception to the GPL is included to allow you to distribute a
	combined work that includes FreeRTOS.org without being obliged to provide
	the source code for any proprietary components.  Alternative commercial
	license and support terms are also available upon request.  See the 
	licensing section of http://www.FreeRTOS.org for full details.

	FreeRTOS.org is distributed in the hope that it will be useful,	but WITHOUT
	ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
	FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
	more details.

	You should have received a copy of the GNU General Public License along
	with FreeRTOS.org; if not, write to the Free Software Foundation, Inc., 59
	Temple Place, Suite 330, Boston, MA  02111-1307  USA.


	***************************************************************************
	*                                                                         *
	* Get the FreeRTOS eBook!  See http://www.FreeRTOS.org/Documentation      *
	*                                                                         *
	* This is a concise, step by step, 'hands on' guide that describes both   *
	* general multitasking concepts and FreeRTOS specifics. It presents and   *
	* explains numerous examples that are written using the FreeRTOS API.     *
	* Full source code for all the examples is provided in an accompanying    *
	* .zip file.                                                              *
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


/*
 * Creates all the demo application tasks, then starts the scheduler.  The WEB
 * documentation provides more details of the standard demo application tasks.
 * In addition to the standard demo tasks, the following tasks and tests are
 * defined and/or created within this file:
 *
 * "Web server" - Very basic demonstration of the uIP stack.  The WEB server
 * simply generates a page that shows the current state of all the tasks within
 * the system, including the high water mark of each task stack. The high water
 * mark is displayed as the amount of stack that has never been used, so the
 * closer the value is to zero the closer the task has come to overflowing its
 * stack.  The IP address and net mask are set within FreeRTOSConfig.h.  Sub
 * pages display some TCP/IP status information and permit LED3 to be turned on
 * and off using a check box.
 *
 * Tick hook function that implements a "Check" function -  This is executed 
 * every 5 seconds from the tick hook function.  It checks to ensure that all 
 * the standard demo tasks are still operational and running without error.  
 * The system status (pass/fail) is then displayed underneith the task table on 
 * the served WEB pages.  
 *
 * "Reg test" tasks - These fill the registers with known values, then check
 * that each register still contains its expected value.  Each task uses
 * different values.  The tasks run with very low priority so get preempted very
 * frequently.  A register containing an unexpected value is indicative of an
 * error in the context switching mechanism.
 *
 */

/* Standard includes. */
#include <stdio.h>

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"

/* Demo app includes. */
#include "BlockQ.h"
#include "death.h"
#include "flash.h"
#include "partest.h"
#include "GenQTest.h"
#include "QPeek.h"
#include "recmutex.h"

/*-----------------------------------------------------------*/

/* ComTest constants - there is no free LED for the comtest tasks. */
#define mainCOM_TEST_BAUD_RATE				( ( unsigned portLONG ) 19200 )
#define mainCOM_TEST_LED					( 5 )

/* Task priorities. */
#define mainQUEUE_POLL_PRIORITY				( tskIDLE_PRIORITY + 2 )
#define mainCHECK_TASK_PRIORITY				( tskIDLE_PRIORITY + 3 )
#define mainSEM_TEST_PRIORITY				( tskIDLE_PRIORITY + 1 )
#define mainBLOCK_Q_PRIORITY				( tskIDLE_PRIORITY + 2 )
#define mainCREATOR_TASK_PRIORITY           ( tskIDLE_PRIORITY + 2 )
#define mainINTEGER_TASK_PRIORITY           ( tskIDLE_PRIORITY )
#define mainGEN_QUEUE_TASK_PRIORITY			( tskIDLE_PRIORITY )
#define mainWEB_TASK_PRIORITY       		( tskIDLE_PRIORITY + 2 )

/* WEB server requires enough stack for the string handling functions. */
#define mainBASIC_WEB_STACK_SIZE            ( configMINIMAL_STACK_SIZE * 2 )

/*
 * Configure the hardware for the demo.
 */
static void prvSetupHardware( void );

/*
 * Implements the 'check' function as described at the top of this file.
 */
static void prvCheckFunction( void );

/*
 * Implement the 'Reg test' functionality as described at the top of this file.
 */
static void vRegTest1Task( void *pvParameters );
static void vRegTest2Task( void *pvParameters );

/*
 * The task that handles the uIP stack.  All TCP/IP processing is performed in
 * this task.
 */
extern void vuIP_Task( void *pvParameters );

/*-----------------------------------------------------------*/

/* Counters used to detect errors within the reg test tasks. */
static volatile unsigned portLONG ulRegTest1Counter = 0x11111111, ulRegTest2Counter = 0x22222222;

/* Flag that latches any errors detected in the system. */
unsigned long ulCheckErrors = 0;

/*-----------------------------------------------------------*/

int main( void )
{
extern void vBasicWEBServer( void *pv );

	/* Setup the hardware ready for this demo. */
	prvSetupHardware();
	
	xTaskCreate( vuIP_Task, ( signed portCHAR * ) "uIP", mainBASIC_WEB_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY - 1, NULL );

	/* Start the standard demo tasks. */
	vStartLEDFlashTasks( tskIDLE_PRIORITY );
	vStartGenericQueueTasks( mainGEN_QUEUE_TASK_PRIORITY );
	vStartQueuePeekTasks();
	vStartRecursiveMutexTasks();
	vStartBlockingQueueTasks( mainBLOCK_Q_PRIORITY );

	/* Start the reg test tasks - defined in this file. */
	xTaskCreate( vRegTest1Task, ( signed portCHAR * ) "Reg1", configMINIMAL_STACK_SIZE, ( void * ) &ulRegTest1Counter, tskIDLE_PRIORITY, NULL );
	xTaskCreate( vRegTest2Task, ( signed portCHAR * ) "Reg2", configMINIMAL_STACK_SIZE, ( void * ) &ulRegTest2Counter, tskIDLE_PRIORITY, NULL );

	/* Start the scheduler. */
	vTaskStartScheduler();

    /* Will only get here if there was insufficient memory to create the idle
    task. */
	for( ;; )
	{
	}
}
/*-----------------------------------------------------------*/

void vApplicationTickHook( void )
{
static unsigned long ulExecutionCount = 0, ulLastRegTest1Count = 0, ulLastRegTest2Count = 0;
const unsigned long ulExecutionRate = 5000 / portTICK_RATE_MS;
	
    /* Increment the count of how many times the tick hook has been called. */
    ulExecutionCount++;
    
    /* Is it time to perform the check again? */
	if( ulExecutionCount >= ulExecutionRate )
	{
		/* Reset the execution count so this function is called again in 5
		seconds time. */
		ulExecutionCount = 0;
	
		/* Has an error been found in any task? */
		if( xAreGenericQueueTasksStillRunning() != pdTRUE )
		{
			ulCheckErrors |= 0x01UL;
		}

		if( xAreQueuePeekTasksStillRunning() != pdTRUE )
		{
			ulCheckErrors |= 0x02UL;
		}

		if( xAreBlockingQueuesStillRunning() != pdTRUE )
		{
			ulCheckErrors |= 0x04UL;
		}

		if( xAreRecursiveMutexTasksStillRunning() != pdTRUE )
	    {
	    	ulCheckErrors |= 0x200UL;
	    }

		if( ulLastRegTest1Count == ulRegTest1Counter )
		{
			ulCheckErrors |= 0x1000UL;
		}

		if( ulLastRegTest2Count == ulRegTest2Counter )
		{
			ulCheckErrors |= 0x1000UL;
		}

		ulLastRegTest1Count = ulRegTest1Counter;
		ulLastRegTest2Count = ulRegTest2Counter;
	}
}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void ) 
{
	/* Disable the watchdog, STOP and WAIT modes. */
	SOPT1 = 0;

	/* --- Setup clock to use external 25MHz source. --- */
	
	/* Extal and xtal pin ON. */
	PTDPF1_D4 = 0x03;
	PTDPF1_D5 = 0x03;

	/* Switch from FEI to FBE (FLL bypassed external)
	enable external clock source */
	MCGC2 = MCGC2_ERCLKEN_MASK  /* Activate external reference clock */
	      | MCGC2_EREFS_MASK    /* Because crystal is being used */
	      | MCGC2_RANGE_MASK;   /* High range */
	        
	/* Select clock mode and clear IREFs. */
	MCGC1 = (0x02 << 6 )        /* CLKS = 10 -> external reference clock. */
	      | (0x04 << 3 )        /* RDIV = 2^4 -> 25MHz/16 = 1.5625 MHz */
	      | MCGC1_IRCLKEN_MASK; /* IRCLK to RTC enabled */
	  
	/* Wait for Reference and Clock status bits to update. */
	while( MCGSC_IREFST | ( MCGSC_CLKST != 0x02 ) )
	{
		/* Nothing to do here. */
	}

	/* Switch from FBE to PBE (PLL bypassed internal) mode. */
	MCGC3 =  0x08               /* Set PLL multi 50MHz. */
	      |  MCGC3_PLLS_MASK;   /* Select PLL. */

	/* Wait for PLL status and lock bits to update. */
	while( !MCGSC_PLLST | !MCGSC_LOCK )
	{
		/* Nothing to do here. */
	}


	/* Now in PBE Mode, finally switch from PBE to PEE (PLL enabled external 
	mode). */
	MCGC1_CLKS  = 0b00; /* PLL clock to system (MCGOUT) */

	/* Wait for the clock status bits to update. */
	while( MCGSC_CLKST != 0x03 )
	{
		/* Nothing to do here. */
	}

	/* Setup the IO for the LED outputs. */
	vParTestInitialise();
}
/*-----------------------------------------------------------*/

void vApplicationStackOverflowHook( xTaskHandle *pxTask, signed portCHAR *pcTaskName )
{
	/* This will get called if a stack overflow is detected during the context
	switch.  Set configCHECK_FOR_STACK_OVERFLOWS to 2 to also check for stack
	problems within nested interrupts, but only do this for debug purposes as
	it will increase the context switch time. */

	( void ) pxTask;
	( void ) pcTaskName;

	for( ;; )
	{
	}
}
/*-----------------------------------------------------------*/

static void vRegTest1Task( void *pvParameters )
{
  /* Just to remove compiler warnings. */
  ( void ) pvParameters;
  
	/* Set all the registers to known values, then check that each retains its
	expected value - as described at the top of this file.  If an error is
	found then the loop counter will no longer be incremented allowing the check
	task to recognise the error. */
	asm volatile 	(	"reg_test_1_start:						\n\t"
						"	moveq		#1, d0					\n\t"
						"	moveq		#2, d1					\n\t"
						"	moveq		#3, d2					\n\t"
						"	moveq		#4, d3					\n\t"
						"	moveq		#5, d4					\n\t"
						"	moveq		#6, d5					\n\t"						
						"	moveq		#7, d6					\n\t"
						"	moveq		#8, d7					\n\t"
						"	move		#9, a0					\n\t"
						"	move		#10, a1					\n\t"
						"	move		#11, a2					\n\t"
						"	move		#12, a3					\n\t"
						"	move		#13, a4					\n\t"
						"	move		#15, a6					\n\t"
						"										\n\t"
						"	cmpi.l		#1, d0					\n\t"
						"	bne			reg_test_1_error		\n\t"
						"	cmpi.l		#2, d1					\n\t"
						"	bne			reg_test_1_error		\n\t"
						"	cmpi.l		#3, d2					\n\t"
						"	bne			reg_test_1_error		\n\t"
						"	cmpi.l		#4, d3					\n\t"
						"	bne			reg_test_1_error		\n\t"
						"	cmpi.l		#5, d4					\n\t"
						"	bne			reg_test_1_error		\n\t"
						"	cmpi.l		#6, d5					\n\t"
						"	bne			reg_test_1_error		\n\t"
						"	cmpi.l		#7, d6					\n\t"
						"	bne			reg_test_1_error		\n\t"
						"	cmpi.l		#8, d7					\n\t"
						"	bne			reg_test_1_error		\n\t"
						"	move		a0, d0					\n\t"
						"	cmpi.l		#9, d0					\n\t"
						"	bne			reg_test_1_error		\n\t"
						"	move		a1, d0					\n\t"
						"	cmpi.l		#10, d0					\n\t"
						"	bne			reg_test_1_error		\n\t"
						"	move		a2, d0					\n\t"
						"	cmpi.l		#11, d0					\n\t"
						"	bne			reg_test_1_error		\n\t"
						"	move		a3, d0					\n\t"
						"	cmpi.l		#12, d0					\n\t"
						"	bne			reg_test_1_error		\n\t"
						"	move		a4, d0					\n\t"
						"	cmpi.l		#13, d0					\n\t"
						"	bne			reg_test_1_error		\n\t"
						"	move		a6, d0					\n\t"
						"	cmpi.l		#15, d0					\n\t"
						"	bne			reg_test_1_error		\n\t"
						"	move		ulRegTest1Counter, d0	\n\t"
						"	addq		#1, d0					\n\t"
						"	move		d0, ulRegTest1Counter	\n\t"
						"	bra			reg_test_1_start		\n\t"
						"reg_test_1_error:						\n\t"
						"	bra			reg_test_1_error		\n\t"
					);
}
/*-----------------------------------------------------------*/

static void vRegTest2Task( void *pvParameters )
{
  /* Just to remove compiler warnings. */
  ( void ) pvParameters;

	/* Set all the registers to known values, then check that each retains its
	expected value - as described at the top of this file.  If an error is
	found then the loop counter will no longer be incremented allowing the check
	task to recognise the error. */
	asm volatile 	(	"reg_test_2_start:						\n\t"
						"	moveq		#10, d0					\n\t"
						"	moveq		#20, d1					\n\t"
						"	moveq		#30, d2					\n\t"
						"	moveq		#40, d3					\n\t"
						"	moveq		#50, d4					\n\t"
						"	moveq		#60, d5					\n\t"
						"	moveq		#70, d6					\n\t"
						"	moveq		#80, d7					\n\t"
						"	move		#90, a0					\n\t"
						"	move		#100, a1				\n\t"
						"	move		#110, a2				\n\t"
						"	move		#120, a3				\n\t"
						"	move		#130, a4				\n\t"
						"	move		#150, a6				\n\t"
						"										\n\t"
						"	cmpi.l		#10, d0					\n\t"
						"	bne			reg_test_2_error		\n\t"
						"	cmpi.l		#20, d1					\n\t"
						"	bne			reg_test_2_error		\n\t"
						"	cmpi.l		#30, d2					\n\t"
						"	bne			reg_test_2_error		\n\t"
						"	cmpi.l		#40, d3					\n\t"
						"	bne			reg_test_2_error		\n\t"
						"	cmpi.l		#50, d4					\n\t"
						"	bne			reg_test_2_error		\n\t"
						"	cmpi.l		#60, d5					\n\t"
						"	bne			reg_test_2_error		\n\t"
						"	cmpi.l		#70, d6					\n\t"
						"	bne			reg_test_2_error		\n\t"
						"	cmpi.l		#80, d7					\n\t"
						"	bne			reg_test_2_error		\n\t"
						"	move		a0, d0					\n\t"
						"	cmpi.l		#90, d0					\n\t"
						"	bne			reg_test_2_error		\n\t"
						"	move		a1, d0					\n\t"
						"	cmpi.l		#100, d0				\n\t"
						"	bne			reg_test_2_error		\n\t"
						"	move		a2, d0					\n\t"
						"	cmpi.l		#110, d0				\n\t"
						"	bne			reg_test_2_error		\n\t"
						"	move		a3, d0					\n\t"
						"	cmpi.l		#120, d0				\n\t"
						"	bne			reg_test_2_error		\n\t"
						"	move		a4, d0					\n\t"
						"	cmpi.l		#130, d0				\n\t"
						"	bne			reg_test_2_error		\n\t"
						"	move		a6, d0					\n\t"
						"	cmpi.l		#150, d0				\n\t"
						"	bne			reg_test_2_error		\n\t"
						"	move		ulRegTest1Counter, d0	\n\t"
						"	addq		#1, d0					\n\t"
						"	move		d0, ulRegTest2Counter	\n\t"
						"	bra			reg_test_2_start		\n\t"
						"reg_test_2_error:						\n\t"
						"	bra			reg_test_2_error		\n\t"
					);
}
/*-----------------------------------------------------------*/

