/*
    FreeRTOS V6.0.5 - Copyright (C) 2010 Real Time Engineers Ltd.

    ***************************************************************************
    *                                                                         *
    * If you are:                                                             *
    *                                                                         *
    *    + New to FreeRTOS,                                                   *
    *    + Wanting to learn FreeRTOS or multitasking in general quickly       *
    *    + Looking for basic training,                                        *
    *    + Wanting to improve your FreeRTOS skills and productivity           *
    *                                                                         *
    * then take a look at the FreeRTOS eBook                                  *
    *                                                                         *
    *        "Using the FreeRTOS Real Time Kernel - a Practical Guide"        *
    *                  http://www.FreeRTOS.org/Documentation                  *
    *                                                                         *
    * A pdf reference manual is also available.  Both are usually delivered   *
    * to your inbox within 20 minutes to two hours when purchased between 8am *
    * and 8pm GMT (although please allow up to 24 hours in case of            *
    * exceptional circumstances).  Thank you for your support!                *
    *                                                                         *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.
    ***NOTE*** The exception to the GPL is included to allow you to distribute
    a combined work that includes FreeRTOS without being obliged to provide the
    source code for proprietary components outside of the FreeRTOS kernel.
    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT
    ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
    FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
    more details. You should have received a copy of the GNU General Public 
    License and the FreeRTOS license exception along with FreeRTOS; if not it 
    can be viewed here: http://www.freertos.org/a00114.html and also obtained 
    by writing to Richard Barry, contact details for whom are available on the
    FreeRTOS WEB site.

    1 tab == 4 spaces!

    http://www.FreeRTOS.org - Documentation, latest information, license and
    contact details.

    http://www.SafeRTOS.com - A version that is certified for use in safety
    critical systems.

    http://www.OpenRTOS.com - Commercial support, development, porting,
    licensing and training services.
*/

/*
 * NOTE 1: The CPU must be in Supervisor mode when the scheduler is started.
 * The PowerON_Reset_PC() supplied in resetprg.c with this demo has 
 * Change_PSW_PM_to_UserMode() commented out to ensure this is the case.
*/

/* Hardware specific includes. */
#include "iodefine.h"
#include "rskrx62ndef.h"

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Standard demo includes. */
#include "partest.h"
#include "flash.h"
#include "IntQueue.h"

/* Values that are passed into the reg test tasks using the task parameter.  The 
tasks then check that the values are passed in correctly. */
#define mainREG_TEST_1_PARAMETER	( 0x12121212UL )
#define mainREG_TEST_2_PARAMETER	( 0x12345678UL )

/* Priorities at which the tasks are created. */
#define mainFLASH_TASK_PRIORITY		1
#define mainCHECK_TASK_PRIORITY		( configMAX_PRIORITIES - 1 )

/* The LED toggled by the check task. */
#define mainCHECK_LED						( 5 )

/* The rate at which mainCHECK_LED will toggle when all the tasks are running
without error. */
#define mainNO_ERROR_CYCLE_TIME				( 5000 / portTICK_RATE_MS )

/* The rate at which mainCHECK_LED will toggle when an error has been reported
by at least one task. */
#define mainERROR_CYCLE_TIME				( 200 / portTICK_RATE_MS )

/*
 * vApplicationMallocFailedHook() will only be called if
 * configUSE_MALLOC_FAILED_HOOK is set to 1 in FreeRTOSConfig.h.  It is a hook
 * function that will execute if a call to pvPortMalloc() fails.
 * pvPortMalloc() is called internally by the kernel whenever a task, queue or
 * semaphore is created.  It is also called by various parts of the demo
 * application.  
 */
void vApplicationMallocFailedHook( void );

/*
 * vApplicationIdleHook() will only be called if configUSE_IDLE_HOOK is set to 1
 * in FreeRTOSConfig.h.  It is a hook function that is called on each iteration
 * of the idle task.  It is essential that code added to this hook function
 * never attempts to block in any way (for example, call xQueueReceive() with
 * a block time specified).  If the application makes use of the vTaskDelete()
 * API function (as this demo application does) then it is also important that
 * vApplicationIdleHook() is permitted to return to its calling function because
 * it is the responsibility of the idle task to clean up memory allocated by the
 * kernel to any task that has since been deleted.
 */
void vApplicationIdleHook( void );

/*
 * vApplicationStackOverflowHook() will only be called if 
 * configCHECK_FOR_STACK_OVERFLOW is set to a non-zero value.  The handle and 
 * name of the offending task should be passed in the function parameters, but
 * it is possible that the stack overflow will have corrupted these - in which
 * case pxCurrentTCB can be inspected to find the same information.
 */
void vApplicationStackOverflowHook( xTaskHandle *pxTask, signed char *pcTaskName );

/*
 * The reg test tasks as described at the top of this file.
 */
void vRegTest1Task( void *pvParameters );
void vRegTest2Task( void *pvParameters );

/*
 * The actual implementatio of the reg test functionality, which, because of
 * the direct register access, have to be in assembly.
 */
static void prvRegTest1Implementation( void );
static void prvRegTest2Implementation( void );

/*
 * The check task as described at the top of this file.
 */
static void prvCheckTask( void *pvParameters );

/* Variables that are incremented on each iteration of the reg test tasks - 
provided the tasks have not reported any errors.  The check task inspects these
variables to ensure they are still incrementing as expected. */
unsigned long ulRegTest1CycleCount = 0UL, ulRegTest2CycleCount = 0UL;

/*-----------------------------------------------------------*/

void main(void)
{
extern void HardwareSetup( void );

	/* Renesas provided CPU configuration routine.  The clocks are configured in
	here. */
	HardwareSetup();
	
	/* Turn all LEDs off. */
	vParTestInitialise();
	
	/* Start the common demo tasks. */
	vStartLEDFlashTasks( mainFLASH_TASK_PRIORITY );
	vStartInterruptQueueTasks();
	
	/* Start the reg test tasks which test the context switching mechanism. */
	xTaskCreate( vRegTest1Task, "RegTst1", configMINIMAL_STACK_SIZE, ( void * ) mainREG_TEST_1_PARAMETER, tskIDLE_PRIORITY, NULL );
	xTaskCreate( vRegTest2Task, "RegTst2", configMINIMAL_STACK_SIZE, ( void * ) mainREG_TEST_2_PARAMETER, tskIDLE_PRIORITY, NULL );

	/* Start the check task as described at the top of this file. */
	xTaskCreate( prvCheckTask, "Check", configMINIMAL_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY, NULL );

	/* Start the tasks running. */
	vTaskStartScheduler();
	
	/* If all is well we will never reach here as the scheduler will now be
	running.  If we do reach here then it is likely that there was insufficient
	heap available for the idle task to be created. */
	for( ;; );
}
/*-----------------------------------------------------------*/

static void prvCheckTask( void *pvParameters )
{
static volatile unsigned long ulLastRegTest1CycleCount = 0UL, ulLastRegTest2CycleCount = 0UL;
portTickType xNextWakeTime, xCycleFrequency = mainNO_ERROR_CYCLE_TIME;

	/* Initialise xNextWakeTime - this only needs to be done once. */
	xNextWakeTime = xTaskGetTickCount();

	for( ;; )
	{
		/* Place this task in the blocked state until it is time to run again. */
		vTaskDelayUntil( &xNextWakeTime, xCycleFrequency );

		/* Check the standard demo tasks are running without error. */
		if( xAreIntQueueTasksStillRunning() != pdPASS )
		{
			xCycleFrequency = mainERROR_CYCLE_TIME;
		}

		/* Check the reg test tasks are still cycling.  They will stop incrementing
		their loop counters if they encounter an error. */
		if( ulRegTest1CycleCount == ulLastRegTest1CycleCount )
		{
			xCycleFrequency = mainERROR_CYCLE_TIME;
		}

		if( ulRegTest2CycleCount == ulLastRegTest2CycleCount )
		{
			xCycleFrequency = mainERROR_CYCLE_TIME;
		}
		
		ulLastRegTest1CycleCount = ulRegTest1CycleCount;
		ulLastRegTest2CycleCount = ulRegTest2CycleCount;
		
		/* Toggle the check LED to give an indication of the system status.  If the
		LED toggles every 5 seconds then everything is ok.  A faster toggle indicates
		an error. */
		vParTestToggleLED( mainCHECK_LED );
	}
}
/*-----------------------------------------------------------*/

void vApplicationSetupTimerInterrupt( void )
{
	/* Enable compare match timer 0. */
	MSTP( CMT0 ) = 0;
	
	/* Interrupt on compare match. */
	CMT0.CMCR.BIT.CMIE = 1;
	
	/* Set the compare match value. */
	CMT0.CMCOR = ( unsigned short ) ( ( ( configCPU_CLOCK_HZ / configTICK_RATE_HZ ) -1 ) / 8 );
	
	/* Divide the PCLK by 8. */
	CMT0.CMCR.BIT.CKS = 0;
	
	/* Enable the interrupt... */
	_IEN( _CMT0_CMI0 ) = 1;
	
	/* ...and set its priority to the application defined kernel priority. */
	_IPR( _CMT0_CMI0 ) = configKERNEL_INTERRUPT_PRIORITY;
	
	/* Start the timer. */
	CMT.CMSTR0.BIT.STR0 = 1;
}
/*-----------------------------------------------------------*/

/* This function is explained by the comments above its prototype at the top
of this file. */
void vApplicationMallocFailedHook( void )
{
	for( ;; );
}
/*-----------------------------------------------------------*/

/* This function is explained by the comments above its prototype at the top
of this file. */
void vApplicationStackOverflowHook( xTaskHandle *pxTask, signed char *pcTaskName )
{
	for( ;; );
}
/*-----------------------------------------------------------*/

/* This function is explained by the comments above its prototype at the top
of this file. */
void vApplicationIdleHook( void )
{
}
/*-----------------------------------------------------------*/

void vRegTest1Task( void *pvParameters )
{
	if( ( ( unsigned long ) pvParameters ) != mainREG_TEST_1_PARAMETER )
	{
		/* The parameter did not contain the expected value. */
		for( ;; )
		{
			/* Stop the tick interrupt so its obvious something has gone wrong. */
			taskDISABLE_INTERRUPTS();
		}
	}
	
	/* This is an inline asm function that never returns. */
	prvRegTest1Implementation();		
}
/*-----------------------------------------------------------*/

void vRegTest2Task( void *pvParameters )
{
	if( ( ( unsigned long ) pvParameters ) != mainREG_TEST_2_PARAMETER )
	{
		/* The parameter did not contain the expected value. */
		for( ;; )
		{
			/* Stop the tick interrupt so its obvious something has gone wrong. */
			taskDISABLE_INTERRUPTS();
		}
	}
	
	/* This is an inline asm function that never returns. */
	prvRegTest2Implementation();		
}
/*-----------------------------------------------------------*/

#pragma inline_asm prvRegTest1Implementation
static void prvRegTest1Implementation( void )
{
	; Put a known value in each register.
	MOV.L	#1, R1
	MOV.L	#2, R2
	MOV.L	#3, R3
	MOV.L	#4, R4
	MOV.L	#5, R5
	MOV.L	#6, R6
	MOV.L	#7, R7
	MOV.L	#8, R8
	MOV.L	#9, R9
	MOV.L	#10, R10
	MOV.L	#11, R11
	MOV.L	#12, R12
	MOV.L	#13, R13
	MOV.L	#14, R14
	MOV.L	#15, R15
	
	; Loop, checking each itteration that each register still contains the
	; expected value.
TestLoop1:	

	; Push the registers that are going to get clobbered.
	PUSHM	R14-R15
	
	; Increment the loop counter to show this task is still getting CPU time.
	MOV.L	#_ulRegTest1CycleCount, R14
	MOV.L	[ R14 ], R15
	ADD		#1, R15
	MOV.L	R15, [ R14 ]
	
	; Yield to extend the text coverage.  Set the bit in the ITU SWINTR register.
	MOV.L	#1, R14
	MOV.L 	#0872E0H, R15
	MOV.B	R14, [R15]
	NOP
	NOP
	
	; Restore the clobbered registers.
	POPM	R14-R15
	
	; Now compare each register to ensure it still contains the value that was
	; set before this loop was entered.
	CMP		#1, R1
	BNE		RegTest2Error
	CMP		#2, R2
	BNE		RegTest2Error
	CMP		#3, R3
	BNE		RegTest2Error
	CMP		#4, R4
	BNE		RegTest2Error
	CMP		#5, R5
	BNE		RegTest2Error
	CMP		#6, R6
	BNE		RegTest2Error
	CMP		#7, R7
	BNE		RegTest2Error
	CMP		#8, R8
	BNE		RegTest2Error
	CMP		#9, R9
	BNE		RegTest2Error
	CMP		#10, R10
	BNE		RegTest2Error
	CMP		#11, R11
	BNE		RegTest2Error
	CMP		#12, R12
	BNE		RegTest2Error
	CMP		#13, R13
	BNE		RegTest2Error
	CMP		#14, R14
	BNE		RegTest2Error
	CMP		#15, R15
	BNE		RegTest2Error

	; All comparisons passed, start a new itteratio of this loop.
	BRA		TestLoop1
	
RegTest1Error:
	; A compare failed, something has gone wrong.  Stop the tick and any other 
	; interrupts to make it obvious that things have halted.
	CLRPSW	I
	BRA RegTest1Error
}
/*-----------------------------------------------------------*/

#pragma inline_asm prvRegTest2Implementation
static void prvRegTest2Implementation( void )
{
	; Put a known value in each register.
	MOV.L	#10, R1
	MOV.L	#20, R2
	MOV.L	#30, R3
	MOV.L	#40, R4
	MOV.L	#50, R5
	MOV.L	#60, R6
	MOV.L	#70, R7
	MOV.L	#80, R8
	MOV.L	#90, R9
	MOV.L	#100, R10
	MOV.L	#110, R11
	MOV.L	#120, R12
	MOV.L	#130, R13
	MOV.L	#140, R14
	MOV.L	#150, R15
	
	; Loop, checking on each itteration that each register still contains the
	; expected value.
TestLoop2:	
	
	; Push the registers that are going to get clobbered.
	PUSHM	R14-R15
	
	; Increment the loop counter to show this task is still getting CPU time.
	MOV.L	#_ulRegTest2CycleCount, R14
	MOV.L	[ R14 ], R15
	ADD		#1, R15
	MOV.L	R15, [ R14 ]
	
	; Restore the clobbered registers.
	POPM	R14-R15	
	
	CMP		#10, R1
	BNE		RegTest2Error
	CMP		#20, R2
	BNE		RegTest2Error
	CMP		#30, R3
	BNE		RegTest2Error
	CMP		#40, R4
	BNE		RegTest2Error
	CMP		#50, R5
	BNE		RegTest2Error
	CMP		#60, R6
	BNE		RegTest2Error
	CMP		#70, R7
	BNE		RegTest2Error
	CMP		#80, R8
	BNE		RegTest2Error
	CMP		#90, R9
	BNE		RegTest2Error
	CMP		#100, R10
	BNE		RegTest2Error
	CMP		#110, R11
	BNE		RegTest2Error
	CMP		#120, R12
	BNE		RegTest2Error
	CMP		#130, R13
	BNE		RegTest2Error
	CMP		#140, R14
	BNE		RegTest2Error
	CMP		#150, R15
	BNE		RegTest2Error

	; All comparisons passed, start a new itteratio of this loop.
	BRA		TestLoop2
	
RegTest2Error:
	; A compare failed, something went wrong.  Stop the tick and any other 
	; interrupts to make it obvious that things have halted.
	CLRPSW	I
	BRA RegTest2Error
}





