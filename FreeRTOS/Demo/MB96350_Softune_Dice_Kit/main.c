/*
 * FreeRTOS Kernel V10.1.0
 * Copyright (C) 2018 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * http://www.FreeRTOS.org
 * http://aws.amazon.com/freertos
 *
 * 1 tab == 4 spaces!
 */


/*****
 *
 * See http://www.freertos.org/Documentation/FreeRTOS-documentation-and-book.html
 * for an introductory guide to using real time kernels, and FreeRTOS in
 * particular.
 *
 *****
 *
 * The DICE-KIT-16FX has two 7 segment displays and two buttons that can
 * generate interrupts.  This example uses this IO as follows:
 *
 *
 * - Left 7 segment display -
 *
 * 7 'flash' tasks are created, each of which toggles a single segment of the
 * left display.  Each task executes at a fixed frequency, with a different
 * frequency being used by each task.
 *
 * When button SW2 is pressed an interrupt is generated that wakes up a 'dice'
 * task.  The dice task suspends the 7 tasks that are accessing the left display
 * before simulating a dice being thrown by generating a random number between
 * 1 and 6.  After the number has been generated the task sleeps for 5 seconds,
 * if SW2 is pressed again within the 5 seconds another random number is
 * generated, if SW2 is not pressed within the 5 seconds then the 7 tasks are
 * un-suspended and will once again toggle the segments of the left hand display.
 *
 *
 * - Right 7 segment display -
 *
 * Control of the right side 7 segment display is very similar to that of the
 * left, except co-routines are used to toggle the segments instead of tasks,
 * and button SW3 is used instead of SW2.
 *
 *
 * - Notes -
 *
 * Only one dice task is actually defined.  Two instances of this single
 * definition are created, the first to simulate a dice being thrown on the left
 * display, and the other to simulate a dice being thrown on the right display.
 * The task parameter is used to let the dice tasks know which display to
 * control.
 *
 * Both dice tasks and the flash tasks operate completely independently under
 * the control of FreeRTOS.  11 tasks and 7 co-routines are created in total,
 * including the idle task.
 *
 * The co-routines all execute within a single low priority task.
 *
 *
 *
 * When this demo is executing as expected:
 *
 * + Every segment of both displays will toggle at a fixed frequency - with each
 *   segment using a different frequency.
 * + When a button is pushed the segment toggling will temporarily stop and the
 *   dice 'throw' will start whereby the display will show a fast changing random
 *   number for a few seconds before the dice value is chosen and displayed.
 * + If the button is not pushed again within five seconds of the dice value being
 *   displayed the segment toggling will commence again.
 *
 *****/

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo includes. */
#include "DiceTask.h"
#include "ParTest.h"
#include "Flash.h"

/* The priority at which the dice task execute. */
#define mainDICE_PRIORITY			( tskIDLE_PRIORITY + 2 )

/*
 * Sets up the MCU IO for the 7 segment displays and the button inputs.
 */
static void prvSetupHardware( void );

/*
 * The function that creates the flash tasks and co-routines (the tasks and
 * co-routines that toggle the 7 segment display segments.
 */
extern vCreateFlashTasksAndCoRoutines( void );

/*-----------------------------------------------------------*/

void main( void )
{
	/* Setup the MCU IO. */
	prvSetupHardware();

	/* Create the tasks and co-routines that toggle the display segments. */
	vCreateFlashTasksAndCoRoutines();

	/* Create a 'dice' task to control the left hand display. */
	xTaskCreate( vDiceTask, "Dice1", configMINIMAL_STACK_SIZE, ( void * ) configLEFT_DISPLAY, mainDICE_PRIORITY, NULL );

	/* Create a 'dice' task to control the right hand display. */
	xTaskCreate( vDiceTask, "Dice2", configMINIMAL_STACK_SIZE, ( void * ) configRIGHT_DISPLAY, mainDICE_PRIORITY, NULL );

	/* Start the scheduler running. */
	vTaskStartScheduler();

	/* If this loop is executed then there was insufficient heap memory for the
	idle task to be created - causing vTaskStartScheduler() to return. */
	while( 1 );
}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
	/* Setup interrupt hardware - interrupts are kept disabled for now to
	prevent any interrupts attempting to cause a context switch before the
	scheduler has been started. */
	InitIrqLevels();
	portDISABLE_INTERRUPTS();
	__set_il( 7 );

	/* Set Port3 as output (7Segment Display). */
	DDR03  = 0xff;

	/* Use Port 5 as I/O-Port. */
	ADER1  = 0;
	PDR05  = 0x7f;

	/* Set Port5 as output (7Segment Display). */
	DDR05  = 0xff;

	/* Disable inputs on the following ports. */
	PIER02 = 0x00;
	PDR02  = 0x00;
	DDR02  = 0xff;
	PIER03 = 0x00;
	PDR03  = 0xff;
	PIER05 = 0x00;
	PDR05  = 0x00;
	PIER06 = 0x00;
	PDR06  = 0x00;
	DDR06  = 0xff;

	/* Enable P00_0/INT8 and P00_1/INT9 as input. */
	PIER00 = 0x03;

	/* Enable external interrupt 8. */
	PIER00_IE0 = 1;

	/* LB0, LA0 = 11 -> falling edge. */
	ELVRL1_LB8 = 1;
	ELVRL1_LA8 = 1;

	/* Reset and enable the interrupt request. */
	EIRR1_ER8 = 0;
	ENIR1_EN8 = 1;

	/* Enable external interrupt 9. */
	PIER00_IE1 = 1;

	/* LB1, LA1 = 11 -> falling edge. */
	ELVRL1_LB9 = 1;
	ELVRL1_LA9 = 1;

	/* Reset and enable the interrupt request. */
	EIRR1_ER9 = 0;
	ENIR1_EN9 = 1;
}

