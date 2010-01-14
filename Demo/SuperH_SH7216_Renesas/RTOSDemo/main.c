/*
    FreeRTOS V6.0.1 - Copyright (C) 2009 Real Time Engineers Ltd.

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

#include "FreeRTOS.h"
#include "task.h"

#include "partest.h"

#define mainFRQCR_VALUE 					( 0x0303 )	/* Input = 12.5MHz, I Clock = 200MHz, B Clock = 50MHz, P Clock = 50MHz */

void vApplicationMallocFailedHook( void );
void vApplicationIdleHook( void );
static void prvSetupHardware( void );

extern void vRegTest1Task( void *pvParameters );
extern void vRegTest2Task( void *pvParameters );

unsigned long ulRegTest1CycleCount = 0UL, ulRegTest2CycleCount = 0UL;

/*-----------------------------------------------------------*/

void main(void)
{
	prvSetupHardware();

	xTaskCreate( vRegTest1Task, "RegTest1", configMINIMAL_STACK_SIZE, ( void * ) 0x12345678UL, 1, NULL );
	xTaskCreate( vRegTest2Task, "RegTest2", configMINIMAL_STACK_SIZE, ( void * ) 0x11223344UL, 1, NULL );
	 
	vTaskStartScheduler();

	for( ;; );
}
/*-----------------------------------------------------------*/

void vApplicationMallocFailedHook( void )
{
	/* A call to vPortMalloc() failed, probably during the creation of a task,
	queue or semaphore.  Inspect pxCurrentTCB to find which task is currently
	executing. */
	for( ;; );
}
/*-----------------------------------------------------------*/

void vApplicationIdleHook( void )
{
	/* Code can be added to the idle task here.  This function must *NOT* attempt
	to block.  Also, if the application uses the vTaskDelete() API function then
	this function must return regularly to ensure the idle task gets a chance to
	clean up the memory used by deleted tasks. */
}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
volatile unsigned long ul;

	/* Set the CPU and peripheral clocks. */
	CPG.FRQCR.WORD = mainFRQCR_VALUE;
	
	/* Wait for the clock to settle. */
	for( ul = 0; ul < 99; ul++ )
	{
		nop();
	}
	
	/* Initialise the ports used to toggle LEDs. */
	vParTestInitialise();
}
/*-----------------------------------------------------------*/

void vApplicationSetupTimerInterrupt( void )
{
/* The peripheral clock is divided by 32 before feeding the compare match
periphersl (CMT). */
unsigned long ulCompareMatch = ( configPERIPHERAL_CLOCK_HZ / ( configTICK_RATE_HZ * 32 ) ) + 1;

	/* Configure a timer to create the RTOS tick interrupt.  This example uses
	the compare match timer, but the multi function timer or possible even the
	watchdog timer could also be used.  Ensure vPortTickInterrupt() is installed
	as the interrupt handler for whichever peripheral is used. */
	
	/* Turn the CMT on. */
	STB.CR4.BIT._CMT = 0;
	
	/* Set the compare match value for the required tick frequency. */
	CMT0.CMCOR = ( unsigned short ) ulCompareMatch;
	
	/* Divide the peripheral clock by 32. */
	CMT0.CMCSR.BIT.CKS = 0x01;
	
	/* Set the CMT interrupt priority - the interrupt priority must be
	configKERNEL_INTERRUPT_PRIORITY no matter which peripheral is used to generate
	the tick interrupt. */
	INTC.IPR08.BIT._CMT0 = configKERNEL_INTERRUPT_PRIORITY;
	
	/* Clear the interrupt flag. */
	CMT0.CMCSR.BIT.CMF = 0;
	
	/* Enable the compare match interrupt. */
	CMT0.CMCSR.BIT.CMIE = 0x01;
	
	/* Start the timer. */
	CMT.CMSTR.BIT.STR0 = 0x01;
}
/*-----------------------------------------------------------*/

void INT_CMT_CMI0( void )
{
static unsigned long ul = 0;

	ul++;
	if( ul >= 1000 )
	{
		if( PE.DR.WORD & ( 0x01 << 9 ) )
		{
			PE.DR.WORD &= ~( 0x01 << 9 );
		}
		else
		{
			PE.DR.WORD |= ( 0x01 << 9 );
		}
		
		ul = 0;
	}

	CMT0.CMCSR.BIT.CMF = 0;
}
/*-----------------------------------------------------------*/

