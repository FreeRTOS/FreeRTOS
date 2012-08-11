#error This project has been reworked for use with a later version of the Xilinx tools and IP.  Please find more up to date projects in other FreeRTOS/Demo/MicroBlaze_nnn directories.

/*
    FreeRTOS V7.1.1 - Copyright (C) 2012 Real Time Engineers Ltd.
	

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
    >>>NOTE<<< The modification to the GPL is included to allow you to
    distribute a combined work that includes FreeRTOS without being obliged to
    provide the source code for proprietary components outside of the FreeRTOS
    kernel.  FreeRTOS is distributed in the hope that it will be useful, but
    WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
    or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
    more details. You should have received a copy of the GNU General Public
    License and the FreeRTOS license exception along with FreeRTOS; if not it
    can be viewed here: http://www.freertos.org/a00114.html and also obtained
    by writing to Richard Barry, contact details for whom are available on the
    FreeRTOS WEB site.

    1 tab == 4 spaces!
    
    ***************************************************************************
     *                                                                       *
     *    Having a problem?  Start by reading the FAQ "My application does   *
     *    not run, what could be wrong?                                      *
     *                                                                       *
     *    http://www.FreeRTOS.org/FAQHelp.html                               *
     *                                                                       *
    ***************************************************************************

    
    http://www.FreeRTOS.org - Documentation, training, latest information, 
    license and contact details.
    
    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool.

    Real Time Engineers ltd license FreeRTOS to High Integrity Systems, who sell 
    the code with commercial support, indemnification, and middleware, under 
    the OpenRTOS brand: http://www.OpenRTOS.com.  High Integrity Systems also
    provide a safety engineered and independently SIL3 certified version under 
    the SafeRTOS brand: http://www.SafeRTOS.com.
*/

/*
 * Creates all the demo application tasks, then starts the scheduler.  The WEB
 * documentation provides more details of the standard demo application tasks.
 *
 * In addition to the standard tasks, main() creates two "Register Check" 
 * tasks.  These tasks write known values into every general purpose register,
 * then check each register to ensure it still contains the expected (written)
 * value.  The register check tasks operate at the idle priority so will get
 * repeatedly preempted.  A register being found to contain an incorrect value
 * following such a preemption would be indicative of an error in the context
 * switch mechanism.
 * 
 * Main.c also creates a task called "Check".  This only executes every three 
 * seconds but has the highest priority so is guaranteed to get processor time.  
 * Its main function is to check that all the other tasks are still operational.
 * Each task (other than the "flash" tasks) maintains a unique count that is 
 * incremented each time the task successfully completes its function.  Should 
 * any error occur within such a task the count is permanently halted.  The 
 * check task inspects the count of each task to ensure it has changed since
 * the last time the check task executed.  If all the count variables have 
 * changed all the tasks are still executing error free, and the check task
 * toggles the onboard LED.  Should any task contain an error at any time 
 * the LED toggle rate will change from 3 seconds to 500ms.
 *
 */

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo application includes. */
#include "partest.h"
#include "flash.h"
#include "comtest2.h"
#include "integer.h"
#include "semtest.h"
#include "BlockQ.h"
#include "dynamic.h"
#include "PollQ.h"

/* Hardware library includes. */
#include <xintc.h>

/* The rate at which the 'check' LED will flash when no errors have been
detected. */
#define mainNO_ERROR_CHECK_PERIOD	3000

/* The rate at which the 'check' LED will flash when an error has been
detected in one of the demo tasks. */
#define mainERROR_CHECK_PERIOD		500

/* Demo application task priorities. */
#define mainLED_TASK_PRIORITY		( tskIDLE_PRIORITY + 2 )
#define mainCHECK_TASK_PRIORITY		( tskIDLE_PRIORITY + 3 )
#define mainSEM_TEST_PRIORITY		( tskIDLE_PRIORITY + 1 )
#define mainCOM_TEST_PRIORITY		( tskIDLE_PRIORITY + 2 )
#define mainBLOCK_Q_PRIORITY		( tskIDLE_PRIORITY + 2 )
#define mainQUEUE_POLL_PRIORITY		( tskIDLE_PRIORITY + 2 )

/* Software cannot influence the BAUD rate used by the simple UART 
implementation. */
#define mainBAUD_RATE				0

/* The LED flashed by the 'check' task to indicate the system status. */
#define mainCHECK_TASK_LED			3

/* The first LED flashed by the COM port test tasks.  LED mainCOM_TEST_LED + 1
will also be used. */
#define mainCOM_TEST_LED			4

/* The register test task does not make any function calls so does not require
much stack at all. */
#define mainTINY_STACK				70

/*
 * The task that executes at the highest priority and calls 
 * prvCheckOtherTasksAreStillRunning().  See the description at the top
 * of the file.
 */
static void vErrorChecks( void *pvParameters );

/*
 * Checks that all the demo application tasks are still executing without error
 * - as described at the top of the file.
 */
static portBASE_TYPE prvCheckOtherTasksAreStillRunning( void );

/*
 * The register test task as described at the top of this file.
 */
static void vRegisterTest( void *pvParameters );

/*
 * Perform any necessary hardware configuration.
 */
static void prvSetupHardware( void );

/* Set to pdFAIL should an error be discovered in the register test tasks. */
static unsigned long ulRegisterTestStatus = pdPASS;
const unsigned long *pulStatusAddr = &ulRegisterTestStatus;

/*-----------------------------------------------------------*/

/*
 * Create all the demo tasks - then start the scheduler.
 */
int main (void) 
{
	/* When re-starting a debug session (rather than cold booting) we want
	to ensure the installed interrupt handlers do not execute until after the
	scheduler has been started. */
	portDISABLE_INTERRUPTS();

	prvSetupHardware();

	/* Start the standard demo application tasks. */
	vStartLEDFlashTasks( mainLED_TASK_PRIORITY );
	vAltStartComTestTasks( mainCOM_TEST_PRIORITY, mainBAUD_RATE, mainCOM_TEST_LED );
	vStartIntegerMathTasks( tskIDLE_PRIORITY );
	vStartSemaphoreTasks( mainSEM_TEST_PRIORITY );
	vStartBlockingQueueTasks( mainBLOCK_Q_PRIORITY );
	vStartDynamicPriorityTasks();
	vStartPolledQueueTasks( mainQUEUE_POLL_PRIORITY );
	
	/* Create two register check tasks - using a different parameter for each.
	The parameter is used to generate the known values written to the registers. */
	#if configUSE_PREEMPTION == 1
		xTaskCreate( vRegisterTest, "Reg1", mainTINY_STACK, ( void * ) 10, tskIDLE_PRIORITY, NULL );
		xTaskCreate( vRegisterTest, "Reg2", mainTINY_STACK, ( void * ) 20, tskIDLE_PRIORITY, NULL );
	#endif

	/* Create the 'check' task that is defined in this file. */
	xTaskCreate( vErrorChecks, "Check", configMINIMAL_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY, NULL );

	/* Finally start the scheduler. */
	vTaskStartScheduler();

	/* Should not get here as the processor is now under control of the 
	scheduler! */

   	return 0;
}
/*-----------------------------------------------------------*/

static void vErrorChecks( void *pvParameters )
{
portTickType xDelayPeriod = mainNO_ERROR_CHECK_PERIOD;

	/* The parameters are not used. */
	( void ) pvParameters;

	/* Cycle for ever, delaying then checking all the other tasks are still
	operating without error.  The delay period used will depend on whether
	or not an error has been discovered in one of the demo tasks. */
	for( ;; )
	{
		vTaskDelay( xDelayPeriod );
		if( !prvCheckOtherTasksAreStillRunning() )
		{
			/* An error has been found.  Shorten the delay period to make
			the LED flash faster. */
			xDelayPeriod = mainERROR_CHECK_PERIOD;
		}

		vParTestToggleLED( mainCHECK_TASK_LED );
	}
}
/*-----------------------------------------------------------*/

static portBASE_TYPE prvCheckOtherTasksAreStillRunning( void )
{
static portBASE_TYPE xAllTestsPass = pdTRUE;

	/* Return pdFALSE if any demo application task set has encountered
	an error. */

	if( xAreIntegerMathsTaskStillRunning() != pdTRUE )
	{
		xAllTestsPass = pdFALSE;
	}

	if( xAreComTestTasksStillRunning() != pdTRUE )
	{
		xAllTestsPass = pdFALSE;
	}

	if( xAreSemaphoreTasksStillRunning() != pdTRUE )
	{
		xAllTestsPass = pdFALSE;
	}

	if( xAreBlockingQueuesStillRunning() != pdTRUE )
	{
		xAllTestsPass = pdFAIL;
	}

	if( xAreDynamicPriorityTasksStillRunning() != pdTRUE )
	{
		xAllTestsPass = ( long ) pdFAIL;
	}

	if( xArePollingQueuesStillRunning() != pdTRUE )
	{
		xAllTestsPass = ( long ) pdFAIL;
	}

	/* Mutual exclusion on this variable is not necessary as we only read it. */
	if( ulRegisterTestStatus != pdPASS )
	{
		xAllTestsPass = pdFALSE;
	}

	return xAllTestsPass;
}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
	/* Ensure the interrupt controller is enabled in order that subsequent 
	code can successfully configure the peripherals. */
	XIntc_mMasterEnable( XPAR_OPB_INTC_0_BASEADDR );

	/* Initialise the GPIO used for the LED's. */
	vParTestInitialise();
}
/*-----------------------------------------------------------*/

static void vRegisterTest( void *pvParameters )
{
	for( ;; )
	{
		/* Fill the registers with their register number plus the offset 
		(added) value.  The added value is passed in as a parameter so
		is contained in r5. */
		asm volatile (	"addi r3, r5, 3		\n\t" \
						"addi r4, r5, 4		\n\t" \
						"addi r6, r5, 6		\n\t" \
						"addi r7, r5, 7		\n\t" \
						"addi r8, r5, 8		\n\t" \
						"addi r9, r5, 9		\n\t" \
						"addi r10, r5, 10	\n\t" \
						"addi r11, r5, 11	\n\t" \
						"addi r12, r5, 12	\n\t" \
						"addi r16, r5, 16	\n\t" \
						"addi r17, r5, 17	\n\t" \
						"addi r18, r5, 18	\n\t" \
						"addi r19, r5, 19	\n\t" \
						"addi r20, r5, 20	\n\t" \
						"addi r21, r5, 21	\n\t" \
						"addi r22, r5, 22	\n\t" \
						"addi r23, r5, 23	\n\t" \
						"addi r24, r5, 24	\n\t" \
						"addi r25, r5, 25	\n\t" \
						"addi r26, r5, 26	\n\t" \
						"addi r27, r5, 27	\n\t" \
						"addi r28, r5, 28	\n\t" \
						"addi r29, r5, 29	\n\t" \
						"addi r30, r5, 30	\n\t" \
						"addi r31, r5, 31	\n\t"
					);

		/* Now read back the register values to ensure they are as we expect. 
		This task will get preempted frequently so other tasks are likely to
		have executed since the register values were written. */

		/* r3 should contain r5 + 3.  Subtract 3 to leave r3 equal to r5. */
		asm volatile (	"addi r3, r3, -3 " );

		/* Compare r3 and r5.  If they are not equal then either r3 or r5
		contains the wrong value and *pulStatusAddr is to pdFAIL. */
		asm volatile (	"cmp r3, r3, r5				\n\t" \
						"beqi r3, 12				\n\t" \
						"lwi r3, r0, pulStatusAddr	\n\t" \
						"sw	r0, r0, r3				\n\t" 
					 );

		/* Repeat for all the other registers. */
		asm volatile ( 	"addi r4, r4, -4			\n\t" \
						"cmp r4, r4, r5				\n\t" \
						"beqi r4, 12				\n\t" \
						"lwi r3, r0, pulStatusAddr	\n\t" \
						"sw	r0, r0, r3				\n\t" \
						"addi r6, r6, -6			\n\t" \
						"cmp r6, r6, r5				\n\t" \
						"beqi r6, 12				\n\t" \
						"lwi r3, r0, pulStatusAddr	\n\t" \
						"sw	r0, r0, r3				\n\t" \
						"addi r7, r7, -7			\n\t" \
						"cmp r7, r7, r5				\n\t" \
						"beqi r7, 12				\n\t" \
						"lwi r3, r0, pulStatusAddr	\n\t" \
						"sw	r0, r0, r3				\n\t" \
						"addi r8, r8, -8			\n\t" \
						"cmp r8, r8, r5				\n\t" \
						"beqi r8, 12				\n\t" \
						"lwi r3, r0, pulStatusAddr	\n\t" \
						"sw	r0, r0, r3				\n\t" \
						"addi r9, r9, -9			\n\t" \
						"cmp r9, r9, r5				\n\t" \
						"beqi r9, 12				\n\t" \
						"lwi r3, r0, pulStatusAddr	\n\t" \
						"sw	r0, r0, r3				\n\t" \
						"addi r10, r10, -10			\n\t" \
						"cmp r10, r10, r5			\n\t" \
						"beqi r10, 12				\n\t" \
						"lwi r3, r0, pulStatusAddr	\n\t" \
						"sw	r0, r0, r3				\n\t" \
						"addi r11, r11, -11			\n\t" \
						"cmp r11, r11, r5			\n\t" \
						"beqi r11, 12				\n\t" \
						"lwi r3, r0, pulStatusAddr	\n\t" \
						"sw	r0, r0, r3				\n\t" \
						"addi r12, r12, -12			\n\t" \
						"cmp r12, r12, r5			\n\t" \
						"beqi r12, 12				\n\t" \
						"lwi r3, r0, pulStatusAddr	\n\t" \
						"sw	r0, r0, r3				\n\t" \
						"sw	r0, r0, r3				\n\t" \
						"addi r16, r16, -16			\n\t" \
						"cmp r16, r16, r5			\n\t" \
						"beqi r16, 12				\n\t" \
						"lwi r3, r0, pulStatusAddr	\n\t" \
						"sw	r0, r0, r3				\n\t" \
						"addi r17, r17, -17			\n\t" \
						"cmp r17, r17, r5			\n\t" \
						"beqi r17, 12				\n\t" \
						"lwi r3, r0, pulStatusAddr	\n\t" \
						"sw	r0, r0, r3				\n\t" \
						"addi r18, r18, -18			\n\t" \
						"cmp r18, r18, r5			\n\t" \
						"beqi r18, 12				\n\t" \
						"lwi r3, r0, pulStatusAddr	\n\t" \
						"sw	r0, r0, r3				\n\t" \
						"addi r19, r19, -19			\n\t" \
						"cmp r19, r19, r5			\n\t" \
						"beqi r19, 12				\n\t" \
						"lwi r3, r0, pulStatusAddr	\n\t" \
						"sw	r0, r0, r3				\n\t" \
						"addi r20, r20, -20			\n\t" \
						"cmp r20, r20, r5			\n\t" \
						"beqi r20, 12				\n\t" \
						"lwi r3, r0, pulStatusAddr	\n\t" \
						"sw	r0, r0, r3				\n\t" \
						"addi r21, r21, -21			\n\t" \
						"cmp r21, r21, r5			\n\t" \
						"beqi r21, 12				\n\t" \
						"lwi r3, r0, pulStatusAddr	\n\t" \
						"sw	r0, r0, r3				\n\t" \
						"addi r22, r22, -22			\n\t" \
						"cmp r22, r22, r5			\n\t" \
						"beqi r22, 12				\n\t" \
						"lwi r3, r0, pulStatusAddr	\n\t" \
						"sw	r0, r0, r3				\n\t" \
						"addi r23, r23, -23			\n\t" \
						"cmp r23, r23, r5			\n\t" \
						"beqi r23, 12				\n\t" \
						"lwi r3, r0, pulStatusAddr	\n\t" \
						"sw	r0, r0, r3				\n\t" \
						"addi r24, r24, -24			\n\t" \
						"cmp r24, r24, r5			\n\t" \
						"beqi r24, 12				\n\t" \
						"lwi r3, r0, pulStatusAddr	\n\t" \
						"sw	r0, r0, r3				\n\t" \
						"addi r25, r25, -25			\n\t" \
						"cmp r25, r25, r5			\n\t" \
						"beqi r25, 12				\n\t" \
						"lwi r3, r0, pulStatusAddr	\n\t" \
						"sw	r0, r0, r3				\n\t" \
						"addi r26, r26, -26			\n\t" \
						"cmp r26, r26, r5			\n\t" \
						"beqi r26, 12				\n\t" \
						"lwi r3, r0, pulStatusAddr	\n\t" \
						"sw	r0, r0, r3				\n\t" \
						"addi r27, r27, -27			\n\t" \
						"cmp r27, r27, r5			\n\t" \
						"beqi r27, 12				\n\t" \
						"lwi r3, r0, pulStatusAddr	\n\t" \
						"sw	r0, r0, r3				\n\t" \
						"addi r28, r28, -28			\n\t" \
						"cmp r28, r28, r5			\n\t" \
						"beqi r28, 12				\n\t" \
						"lwi r3, r0, pulStatusAddr	\n\t" \
						"sw	r0, r0, r3				\n\t" \
						"addi r29, r29, -29			\n\t" \
						"cmp r29, r29, r5			\n\t" \
						"beqi r29, 12				\n\t" \
						"lwi r3, r0, pulStatusAddr	\n\t" \
						"sw	r0, r0, r3				\n\t" \
						"addi r30, r30, -30			\n\t" \
						"cmp r30, r30, r5			\n\t" \
						"beqi r30, 12				\n\t" \
						"lwi r3, r0, pulStatusAddr	\n\t" \
						"sw	r0, r0, r3				\n\t" \
						"addi r31, r31, -31			\n\t" \
						"cmp r31, r31, r5			\n\t" \
						"beqi r31, 12				\n\t" \
						"lwi r3, r0, pulStatusAddr	\n\t" \
						"sw	r0, r0, r3				\n\t"
					);
	}
}



