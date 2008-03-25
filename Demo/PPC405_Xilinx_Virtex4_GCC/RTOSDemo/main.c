/*
	FreeRTOS.org V4.7.1 - Copyright (C) 2003-2008 Richard Barry.

	This file is part of the FreeRTOS.org distribution.

	FreeRTOS.org is free software; you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation; either version 2 of the License, or
	(at your option) any later version.

	FreeRTOS.org is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with FreeRTOS.org; if not, write to the Free Software
	Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

	A special exception to the GPL can be applied should you wish to distribute
	a combined work that includes FreeRTOS.org, without being obliged to provide
	the source code for any proprietary components.  See the licensing section
	of http://www.FreeRTOS.org for full details of how and when the exception
	can be applied.

	***************************************************************************
	***************************************************************************
	*																		  *
	* SAVE TIME AND MONEY!  Why not get us to quote to get FreeRTOS.org		  *
	* running on your hardware - or even write all or part of your application*
	* for you?  See http://www.OpenRTOS.com for details.					  *
	*																		  *
	***************************************************************************
	***************************************************************************

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
 * documentation provides more details of the demo application tasks.
 * 
 * In addition to the standard demo tasks, the follow demo specific tasks are
 * create:
 *
 * The "Check" task.  This only executes every three seconds but has the highest 
 * priority so is guaranteed to get processor time.  Its main function is to 
 * check that all the other tasks are still operational.  Most tasks maintain 
 * a unique count that is incremented each time the task successfully completes 
 * its function.  Should any error occur within such a task the count is 
 * permanently halted.  The check task inspects the count of each task to ensure 
 * it has changed since the last time the check task executed.  If all the count 
 * variables have changed all the tasks are still executing error free, and the 
 * check task toggles the onboard LED.  Should any task contain an error at any time 
 * the LED toggle rate will change from 3 seconds to 500ms.
 *
 * The "Register Check" tasks.  These tasks fill the CPU registers with known
 * values, then check that each register still contains the expected value, the
 * discovery of an unexpected value being indicative of an error in the RTOS
 * context switch mechanism.  The register check tasks operate at low priority
 * so are switched in and out frequently.
 *
 */

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Xilinx library includes. */
#include "xcache_l.h"
#include "xintc.h"

/* Demo application includes. */
#include "flash.h"
#include "integer.h"
#include "comtest2.h"
#include "semtest.h"
#include "BlockQ.h"
#include "dynamic.h"
#include "flop.h"
#include "GenQTest.h"
#include "QPeek.h"
#include "blocktim.h"
#include "death.h"
#include "partest.h"

/* Priorities assigned to the demo tasks. */
#define mainCHECK_TASK_PRIORITY			( tskIDLE_PRIORITY + 4 )
#define mainSEM_TEST_PRIORITY			( tskIDLE_PRIORITY + 3 )
#define mainCOM_TEST_PRIORITY			( tskIDLE_PRIORITY + 2 )
#define mainQUEUE_BLOCK_PRIORITY		( tskIDLE_PRIORITY + 2 )
#define mainDEATH_PRIORITY 				( tskIDLE_PRIORITY + 1 )
#define mainLED_TASK_PRIORITY			( tskIDLE_PRIORITY + 1 )
#define mainGENERIC_QUEUE_PRIORITY		( tskIDLE_PRIORITY )

/* The first LED used by the COM test and check tasks respectively. */
#define mainCOM_TEST_LED				( 4 )
#define mainCHECK_TEST_LED				( 3 )

/* The baud rate used by the comtest tasks is set by the hardware, so the
baud rate parameters passed into the comtest initialisation has no effect. */
#define mainBAUD_SET_IN_HARDWARE		( 0 )

/* Delay periods used by the check task.  If no errors have been found then
the check LED will toggle every mainNO_ERROR_CHECK_DELAY milliseconds.  If an
error has been found at any time then the toggle rate will increase to 
mainERROR_CHECK_DELAY milliseconds. */
#define mainNO_ERROR_CHECK_DELAY		( ( portTickType ) 3000 / portTICK_RATE_MS  )
#define mainERROR_CHECK_DELAY			( ( portTickType ) 500 / portTICK_RATE_MS  )


/* 
 * The tasks defined within this file - described within the comments at the
 * head of this page. 
 */
static void prvRegTestTask1( void *pvParameters );
static void prvRegTestTask2( void *pvParameters );
static void prvErrorChecks( void *pvParameters );

/*
 * Called by the 'check' task to inspect all the standard demo tasks within
 * the system, as described within the comments at the head of this page.
 */
static portSHORT prvCheckOtherTasksAreStillRunning( void );

/*
 * Perform any hardware initialisation required by the demo application.
 */
static void prvSetupHardware( void );

/*-----------------------------------------------------------*/

/* xRegTestStatus will get set to pdFAIL by the regtest tasks if they
discover an unexpected value. */
static unsigned portBASE_TYPE xRegTestStatus = pdPASS;

/* Counters used to ensure the regtest tasks are still running. */
static volatile unsigned portLONG ulRegTest1Counter = 0UL, ulRegTest2Counter = 0UL;

/*-----------------------------------------------------------*/

int main( void )
{
	/* Must be called prior to installing any interrupt handlers! */
	vPortSetupInterruptController();

	/* In this case prvSetupHardware() just enables the caches and and
	configures the IO ports for the LED outputs. */
	prvSetupHardware();

	/* Start the standard demo application tasks.  Note that the baud rate used
	by the comtest tasks is set by the hardware, so the baud rate parameter
	passed has no effect. */
	vStartLEDFlashTasks( mainLED_TASK_PRIORITY );	
	vStartIntegerMathTasks( tskIDLE_PRIORITY );
	vAltStartComTestTasks( mainCOM_TEST_PRIORITY, mainBAUD_SET_IN_HARDWARE, mainCOM_TEST_LED );
	vStartSemaphoreTasks( mainSEM_TEST_PRIORITY );
	vStartBlockingQueueTasks ( mainQUEUE_BLOCK_PRIORITY );	
	vStartDynamicPriorityTasks();	
	vStartMathTasks( tskIDLE_PRIORITY );	
	vStartGenericQueueTasks( mainGENERIC_QUEUE_PRIORITY );
	vStartQueuePeekTasks();
	vCreateBlockTimeTasks();

	/* Create the tasks defined within this file. */
	xTaskCreate( prvRegTestTask1, "Regtest1", configMINIMAL_STACK_SIZE, NULL, tskIDLE_PRIORITY, NULL );
	xTaskCreate( prvRegTestTask2, "Regtest2", configMINIMAL_STACK_SIZE, NULL, tskIDLE_PRIORITY, NULL );
	xTaskCreate( prvErrorChecks, "Check", configMINIMAL_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY, NULL );

	/* The suicide tasks must be started last as they record the number of other
	tasks that exist within the system.  The value is then used to ensure at run
	time the number of tasks that exists is within expected bounds. */
	vCreateSuicidalTasks( mainDEATH_PRIORITY );

	/* Now start the scheduler.  Following this call the created tasks should
	be executing. */	
	vTaskStartScheduler( );

	/* vTaskStartScheduler() will only return if an error occurs while the 
	idle task is being created. */
	for( ;; );

	return 0;
}
/*-----------------------------------------------------------*/

static portSHORT prvCheckOtherTasksAreStillRunning( void )
{
portBASE_TYPE lReturn = pdPASS;
static unsigned portLONG ulLastRegTest1Counter= 0UL, ulLastRegTest2Counter = 0UL;

	/* The demo tasks maintain a count that increments every cycle of the task
	provided that the task has never encountered an error.  This function 
	checks the counts maintained by the tasks to ensure they are still being
	incremented.  A count remaining at the same value between calls therefore
	indicates that an error has been detected. */

	if( xAreIntegerMathsTaskStillRunning() != pdTRUE )
	{
		lReturn = pdFAIL;
	}

	if( xAreComTestTasksStillRunning() != pdTRUE )
	{
		lReturn = pdFAIL;
	}
	
	if( xAreSemaphoreTasksStillRunning() != pdTRUE )
	{
		lReturn = pdFAIL;
	}
	
	if( xAreBlockingQueuesStillRunning() != pdTRUE )
	{
		lReturn = pdFAIL;
	}
	
	if( xAreDynamicPriorityTasksStillRunning() != pdTRUE )
	{
		lReturn = pdFAIL;
	}
	
	if( xAreMathsTaskStillRunning() != pdTRUE )
	{
		lReturn = pdFAIL;
	}
	
	if( xIsCreateTaskStillRunning() != pdTRUE )
	{
		lReturn = pdFAIL;
	}
	
	if( xAreBlockTimeTestTasksStillRunning() != pdTRUE )
	{
		lReturn = pdFAIL;
	}
	
	if ( xAreGenericQueueTasksStillRunning() != pdTRUE )
	{
		lReturn = pdFAIL;
	}
	
	if ( xAreQueuePeekTasksStillRunning() != pdTRUE )
	{
		lReturn = pdFAIL;
	}

	/* Have the register test tasks found any errors? */
	if( xRegTestStatus != pdPASS )
	{
		lReturn = pdFAIL;
	}

	/* Are the register test tasks still looping? */
	if( ulLastRegTest1Counter == ulRegTest1Counter )
	{
		lReturn = pdFAIL;
	}
	else
	{
		ulLastRegTest1Counter = ulRegTest1Counter;
	}

	if( ulLastRegTest2Counter == ulRegTest2Counter )
	{
		lReturn = pdFAIL;
	}
	else
	{
		ulLastRegTest2Counter = ulRegTest2Counter;
	}

	return lReturn;
}
/*-----------------------------------------------------------*/

static void prvErrorChecks( void *pvParameters )
{
portTickType xDelayPeriod = mainNO_ERROR_CHECK_DELAY, xLastExecutionTime;
volatile unsigned portBASE_TYPE uxFreeStack;

	/* This call is just to demonstrate the use of the function - nothing is
	done with the value.  You would expect the stack high water mark to be
	lower (the function to return a larger value) here at function entry than
	later following calls to other functions. */
	uxFreeStack = uxTaskGetStackHighWaterMark( NULL );

	/* Initialise xLastExecutionTime so the first call to vTaskDelayUntil()
	works correctly. */
	xLastExecutionTime = xTaskGetTickCount();

	/* Cycle for ever, delaying then checking all the other tasks are still
	operating without error. */
	for( ;; )
	{
		/* Again just for demo purposes - uxFreeStack should have a lower value
		here than following the call to uxTaskGetStackHighWaterMark() on the
		task entry. */
		uxFreeStack = uxTaskGetStackHighWaterMark( NULL );

		/* Wait until it is time to check again.  The time we wait here depends
		on whether an error has been detected or not.  When an error is 
		detected the time is shortened resulting in a faster LED flash rate. */
		vTaskDelayUntil( &xLastExecutionTime, xDelayPeriod );

		/* See if the other tasks are all ok. */
		if( prvCheckOtherTasksAreStillRunning() != pdPASS )
		{
			/* An error occurred in one of the tasks so shorten the delay 
			period - which has the effect of increasing the frequency of the
			LED toggle. */
			xDelayPeriod = mainERROR_CHECK_DELAY;
		}

		/* Flash! */
		vParTestToggleLED( mainCHECK_TEST_LED );
	}
}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
	XCache_EnableICache( 0x80000000 );
	XCache_EnableDCache( 0x80000000 );

	/* Setup the IO port for use with the LED outputs. */
	vParTestInitialise();
}
/*-----------------------------------------------------------*/

void prvRegTest1Pass( void )
{
	/* Called from the inline assembler - this cannot be static
	otherwise it can get optimised away. */
	ulRegTest1Counter++;
}
/*-----------------------------------------------------------*/

void prvRegTest2Pass( void )
{
	/* Called from the inline assembler - this cannot be static
	otherwise it can get optimised away. */
	ulRegTest2Counter++;
}
/*-----------------------------------------------------------*/

void prvRegTestFail( void )
{
	/* Called from the inline assembler - this cannot be static
	otherwise it can get optimised away. */
	xRegTestStatus = pdFAIL;
}
/*-----------------------------------------------------------*/

static void prvRegTestTask1( void *pvParameters )
{
	/* The first register test task as described at the top of this file.  The
	values used in the registers are different to those use in the second 
	register test task.  Also, unlike the second register test task, this task
	yields between setting the register values and subsequently checking the
	register values. */
	asm volatile
	(
		"RegTest1Start:					\n\t" \
		"								\n\t" \
		"	li		0, 301				\n\t" \
		"	mtspr	256, 0	#USPRG0		\n\t" \
		"	li		0, 501				\n\t" \
		"	mtspr	8, 0	#LR			\n\t" \
		"	li		0, 4				\n\t" \
		"	mtspr	1, 0	#XER		\n\t" \
		"								\n\t" \
		"	li		0, 1				\n\t" \
		"	li		2, 2				\n\t" \
		"	li		3, 3				\n\t" \
		"	li		4,	4				\n\t" \
		"	li		5,	5				\n\t" \
		"	li		6,	6				\n\t" \
		"	li		7,	7				\n\t" \
		"	li		8,	8				\n\t" \
		"	li		9,	9				\n\t" \
		"	li		10,	10				\n\t" \
		"	li		11,	11				\n\t" \
		"	li		12,	12				\n\t" \
		"	li		13,	13				\n\t" \
		"	li		14,	14				\n\t" \
		"	li		15,	15				\n\t" \
		"	li		16,	16				\n\t" \
		"	li		17,	17				\n\t" \
		"	li		18,	18				\n\t" \
		"	li		19,	19				\n\t" \
		"	li		20,	20				\n\t" \
		"	li		21,	21				\n\t" \
		"	li		22,	22				\n\t" \
		"	li		23,	23				\n\t" \
		"	li		24,	24				\n\t" \
		"	li		25,	25				\n\t" \
		"	li		26,	26				\n\t" \
		"	li		27,	27				\n\t" \
		"	li		28,	28				\n\t" \
		"	li		29,	29				\n\t" \
		"	li		30,	30				\n\t" \
		"	li		31,	31				\n\t" \
		"								\n\t" \
		"	sc							\n\t" \
		"	nop							\n\t" \
		"								\n\t" \
		"	cmpwi	0, 1				\n\t" \
		"	bne	RegTest1Fail			\n\t" \
		"	cmpwi	2, 2				\n\t" \
		"	bne	RegTest1Fail			\n\t" \
		"	cmpwi	3, 3				\n\t" \
		"	bne	RegTest1Fail			\n\t" \
		"	cmpwi	4, 4				\n\t" \
		"	bne	RegTest1Fail			\n\t" \
		"	cmpwi	5, 5				\n\t" \
		"	bne	RegTest1Fail			\n\t" \
		"	cmpwi	6, 6				\n\t" \
		"	bne	RegTest1Fail			\n\t" \
		"	cmpwi	7, 7				\n\t" \
		"	bne	RegTest1Fail			\n\t" \
		"	cmpwi	8, 8				\n\t" \
		"	bne	RegTest1Fail			\n\t" \
		"	cmpwi	9, 9				\n\t" \
		"	bne	RegTest1Fail			\n\t" \
		"	cmpwi	10, 10				\n\t" \
		"	bne	RegTest1Fail			\n\t" \
		"	cmpwi	11, 11				\n\t" \
		"	bne	RegTest1Fail			\n\t" \
		"	cmpwi	12, 12				\n\t" \
		"	bne	RegTest1Fail			\n\t" \
		"	cmpwi	13, 13				\n\t" \
		"	bne	RegTest1Fail			\n\t" \
		"	cmpwi	14, 14				\n\t" \
		"	bne	RegTest1Fail			\n\t" \
		"	cmpwi	15, 15				\n\t" \
		"	bne	RegTest1Fail			\n\t" \
		"	cmpwi	16, 16				\n\t" \
		"	bne	RegTest1Fail			\n\t" \
		"	cmpwi	17, 17				\n\t" \
		"	bne	RegTest1Fail			\n\t" \
		"	cmpwi	18, 18				\n\t" \
		"	bne	RegTest1Fail			\n\t" \
		"	cmpwi	19, 19				\n\t" \
		"	bne	RegTest1Fail			\n\t" \
		"	cmpwi	20, 20				\n\t" \
		"	bne	RegTest1Fail			\n\t" \
		"	cmpwi	21, 21				\n\t" \
		"	bne	RegTest1Fail			\n\t" \
		"	cmpwi	22, 22				\n\t" \
		"	bne	RegTest1Fail			\n\t" \
		"	cmpwi	23, 23				\n\t" \
		"	bne	RegTest1Fail			\n\t" \
		"	cmpwi	24, 24				\n\t" \
		"	bne	RegTest1Fail			\n\t" \
		"	cmpwi	25, 25				\n\t" \
		"	bne	RegTest1Fail			\n\t" \
		"	cmpwi	26, 26				\n\t" \
		"	bne	RegTest1Fail			\n\t" \
		"	cmpwi	27, 27				\n\t" \
		"	bne	RegTest1Fail			\n\t" \
		"	cmpwi	28, 28				\n\t" \
		"	bne	RegTest1Fail			\n\t" \
		"	cmpwi	29, 29				\n\t" \
		"	bne	RegTest1Fail			\n\t" \
		"	cmpwi	30, 30				\n\t" \
		"	bne	RegTest1Fail			\n\t" \
		"	cmpwi	31, 31				\n\t" \
		"	bne	RegTest1Fail			\n\t" \
		"								\n\t" \
		"	mfspr	0, 256	#USPRG0		\n\t" \
		"	cmpwi	0, 301				\n\t" \
		"	bne	RegTest1Fail			\n\t" \
		"	mfspr	0, 8	#LR			\n\t" \
		"	cmpwi	0, 501				\n\t" \
		"	bne	RegTest1Fail			\n\t" \
		"	mfspr	0, 1	#XER		\n\t" \
		"	cmpwi	0, 4				\n\t" \
		"	bne	RegTest1Fail			\n\t" \
		"								\n\t" \
		"	bl prvRegTest1Pass			\n\t" \
		"	b RegTest1Start				\n\t" \
		"								\n\t" \
		"RegTest1Fail:					\n\t" \
		"								\n\t" \
		"								\n\t" \
		"	bl prvRegTestFail			\n\t" \
		"	b RegTest1Start				\n\t" \
	);
}
/*-----------------------------------------------------------*/

static void prvRegTestTask2( void *pvParameters )
{
	/* The second register test task as described at the top of this file.  
	Note that this task fills the registers with different values to the
	first register test task. */
	asm volatile
	(
		"RegTest2Start:					\n\t" \
		"								\n\t" \
		"	li		0, 300				\n\t" \
		"	mtspr	256, 0	#USPRG0		\n\t" \
		"	li		0, 500				\n\t" \
		"	mtspr	8, 0	#LR			\n\t" \
		"	li		0, 4				\n\t" \
		"	mtspr	1, 0	#XER		\n\t" \
		"								\n\t" \
		"	li		0, 11				\n\t" \
		"	li		2, 12				\n\t" \
		"	li		3, 13				\n\t" \
		"	li		4,	14				\n\t" \
		"	li		5,	15				\n\t" \
		"	li		6,	16				\n\t" \
		"	li		7,	17				\n\t" \
		"	li		8,	18				\n\t" \
		"	li		9,	19				\n\t" \
		"	li		10,	110				\n\t" \
		"	li		11,	111				\n\t" \
		"	li		12,	112				\n\t" \
		"	li		13,	113				\n\t" \
		"	li		14,	114				\n\t" \
		"	li		15,	115				\n\t" \
		"	li		16,	116				\n\t" \
		"	li		17,	117				\n\t" \
		"	li		18,	118				\n\t" \
		"	li		19,	119				\n\t" \
		"	li		20,	120				\n\t" \
		"	li		21,	121				\n\t" \
		"	li		22,	122				\n\t" \
		"	li		23,	123				\n\t" \
		"	li		24,	124				\n\t" \
		"	li		25,	125				\n\t" \
		"	li		26,	126				\n\t" \
		"	li		27,	127				\n\t" \
		"	li		28,	128				\n\t" \
		"	li		29,	129				\n\t" \
		"	li		30,	130				\n\t" \
		"	li		31,	131				\n\t" \
		"								\n\t" \
		"	cmpwi	0, 11				\n\t" \
		"	bne	RegTest2Fail			\n\t" \
		"	cmpwi	2, 12				\n\t" \
		"	bne	RegTest2Fail			\n\t" \
		"	cmpwi	3, 13				\n\t" \
		"	bne	RegTest2Fail			\n\t" \
		"	cmpwi	4, 14				\n\t" \
		"	bne	RegTest2Fail			\n\t" \
		"	cmpwi	5, 15				\n\t" \
		"	bne	RegTest2Fail			\n\t" \
		"	cmpwi	6, 16				\n\t" \
		"	bne	RegTest2Fail			\n\t" \
		"	cmpwi	7, 17				\n\t" \
		"	bne	RegTest2Fail			\n\t" \
		"	cmpwi	8, 18				\n\t" \
		"	bne	RegTest2Fail			\n\t" \
		"	cmpwi	9, 19				\n\t" \
		"	bne	RegTest2Fail			\n\t" \
		"	cmpwi	10, 110				\n\t" \
		"	bne	RegTest2Fail			\n\t" \
		"	cmpwi	11, 111				\n\t" \
		"	bne	RegTest2Fail			\n\t" \
		"	cmpwi	12, 112				\n\t" \
		"	bne	RegTest2Fail			\n\t" \
		"	cmpwi	13, 113				\n\t" \
		"	bne	RegTest2Fail			\n\t" \
		"	cmpwi	14, 114				\n\t" \
		"	bne	RegTest2Fail			\n\t" \
		"	cmpwi	15, 115				\n\t" \
		"	bne	RegTest2Fail			\n\t" \
		"	cmpwi	16, 116				\n\t" \
		"	bne	RegTest2Fail			\n\t" \
		"	cmpwi	17, 117				\n\t" \
		"	bne	RegTest2Fail			\n\t" \
		"	cmpwi	18, 118				\n\t" \
		"	bne	RegTest2Fail			\n\t" \
		"	cmpwi	19, 119				\n\t" \
		"	bne	RegTest2Fail			\n\t" \
		"	cmpwi	20, 120				\n\t" \
		"	bne	RegTest2Fail			\n\t" \
		"	cmpwi	21, 121				\n\t" \
		"	bne	RegTest2Fail			\n\t" \
		"	cmpwi	22, 122				\n\t" \
		"	bne	RegTest2Fail			\n\t" \
		"	cmpwi	23, 123				\n\t" \
		"	bne	RegTest2Fail			\n\t" \
		"	cmpwi	24, 124				\n\t" \
		"	bne	RegTest2Fail			\n\t" \
		"	cmpwi	25, 125				\n\t" \
		"	bne	RegTest2Fail			\n\t" \
		"	cmpwi	26, 126				\n\t" \
		"	bne	RegTest2Fail			\n\t" \
		"	cmpwi	27, 127				\n\t" \
		"	bne	RegTest2Fail			\n\t" \
		"	cmpwi	28, 128				\n\t" \
		"	bne	RegTest2Fail			\n\t" \
		"	cmpwi	29, 129				\n\t" \
		"	bne	RegTest2Fail			\n\t" \
		"	cmpwi	30, 130				\n\t" \
		"	bne	RegTest2Fail			\n\t" \
		"	cmpwi	31, 131				\n\t" \
		"	bne	RegTest2Fail			\n\t" \
		"								\n\t" \
		"	mfspr	0, 256	#USPRG0		\n\t" \
		"	cmpwi	0, 300				\n\t" \
		"	bne	RegTest2Fail			\n\t" \
		"	mfspr	0, 8	#LR			\n\t" \
		"	cmpwi	0, 500				\n\t" \
		"	bne	RegTest2Fail			\n\t" \
		"	mfspr	0, 1	#XER		\n\t" \
		"	cmpwi	0, 4				\n\t" \
		"	bne	RegTest2Fail			\n\t" \
		"								\n\t" \
		"	bl prvRegTest2Pass			\n\t" \
		"	b RegTest2Start				\n\t" \
		"								\n\t" \
		"RegTest2Fail:					\n\t" \
		"								\n\t" \
		"								\n\t" \
		"	bl prvRegTestFail			\n\t" \
		"	b RegTest2Start				\n\t" \
	);
}
/*-----------------------------------------------------------*/

/* This hook function will get called if there is a suspected stack overflow.
An overflow can cause the task name to be corrupted, in which case the task
handle needs to be used to determine the offending task. */
void vApplicationStackOverflowHook( xTaskHandle xTask, signed portCHAR *pcTaskName );
void vApplicationStackOverflowHook( xTaskHandle xTask, signed portCHAR *pcTaskName )
{
	/* The following three calls are simply to stop compiler warnings about the
	functions not being used - they are called from the inline assembly. */
	prvRegTest1Pass();
	prvRegTest2Pass();
	prvRegTestFail();

	for( ;; );
}



