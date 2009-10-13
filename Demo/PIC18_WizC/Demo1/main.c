/*
    FreeRTOS V6.0.0 - Copyright (C) 2009 Real Time Engineers Ltd.

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
Changes from V3.0.0

Changes from V3.0.1
*/

/*
 * Instead of the normal single demo application, the PIC18F demo is split 
 * into several smaller programs of which this is the first.  This enables the 
 * demo's to be executed on the RAM limited PIC-devices.
 *
 * The Demo1 project is configured for a PIC18F4620 device.  Main.c starts 9 
 * tasks (including the idle task).

 * This first demo is included to do a quick check on the FreeRTOS
 * installation. It is also included to demonstrate a minimal project-setup
 * to use FreeRTOS in a wizC environment.
 *
 * Eight independant tasks are created. All tasks share the same taskcode.
 * Each task blinks a different led on portB. The blinkrate for each task
 * is different, but chosen in such a way that portB will show a binary
 * counter pattern. All blinkrates are derived from a single master-rate.
 * By default, this  masterrate is set to 100 milliseconds. Although such
 * a low value will make it almost impossible to see some of the leds
 * actually blink, it is a good value when using the wizC-simulator.
 * When testing on a real chip, changing the value to eg. 500 milliseconds
 * would be appropiate.
 */
 
/* Scheduler include files. */
#include <FreeRTOS.h>
#include <task.h>

#define mainBLINK_LED_INTERVAL	( ( portTickType ) 100 / ( portTICK_RATE_MS ) )

/* The LED that is flashed by the B0 task. */
#define mainBLINK_LED0_PORT		LATD
#define mainBLINK_LED0_TRIS		TRISD
#define mainBLINK_LED0_PIN		0
#define mainBLINK_LED0_INTERVAL	((mainBLINK_LED_INTERVAL) << (mainBLINK_LED0_PIN))

/* The LED that is flashed by the B1 task. */
#define mainBLINK_LED1_PORT		LATD
#define mainBLINK_LED1_TRIS		TRISD
#define mainBLINK_LED1_PIN		1
#define mainBLINK_LED1_INTERVAL	((mainBLINK_LED_INTERVAL) << (mainBLINK_LED1_PIN))

/* The LED that is flashed by the B2 task. */
#define mainBLINK_LED2_PORT		LATD
#define mainBLINK_LED2_TRIS		TRISD
#define mainBLINK_LED2_PIN		2
#define mainBLINK_LED2_INTERVAL	((mainBLINK_LED_INTERVAL) << (mainBLINK_LED2_PIN))

/* The LED that is flashed by the B3 task. */
#define mainBLINK_LED3_PORT		LATD
#define mainBLINK_LED3_TRIS		TRISD
#define mainBLINK_LED3_PIN		3
#define mainBLINK_LED3_INTERVAL	((mainBLINK_LED_INTERVAL) << (mainBLINK_LED3_PIN))

/* The LED that is flashed by the B4 task. */
#define mainBLINK_LED4_PORT		LATD
#define mainBLINK_LED4_TRIS		TRISD
#define mainBLINK_LED4_PIN		4
#define mainBLINK_LED4_INTERVAL	((mainBLINK_LED_INTERVAL) << (mainBLINK_LED4_PIN))

/* The LED that is flashed by the B5 task. */
#define mainBLINK_LED5_PORT		LATD
#define mainBLINK_LED5_TRIS		TRISD
#define mainBLINK_LED5_PIN		5
#define mainBLINK_LED5_INTERVAL	((mainBLINK_LED_INTERVAL) << (mainBLINK_LED5_PIN))

/* The LED that is flashed by the B6 task. */
#define mainBLINK_LED6_PORT		LATD
#define mainBLINK_LED6_TRIS		TRISD
#define mainBLINK_LED6_PIN		6
#define mainBLINK_LED6_INTERVAL	((mainBLINK_LED_INTERVAL) << (mainBLINK_LED6_PIN))

/* The LED that is flashed by the B7 task. */
#define mainBLINK_LED7_PORT		LATD
#define mainBLINK_LED7_TRIS		TRISD
#define mainBLINK_LED7_PIN		7
#define mainBLINK_LED7_INTERVAL	((mainBLINK_LED_INTERVAL) << (mainBLINK_LED7_PIN))

typedef struct {
	unsigned char *port;
	unsigned char *tris;
	unsigned char pin;
	portTickType  interval;
} SBLINK;

const SBLINK sled0 = {&mainBLINK_LED0_PORT, &mainBLINK_LED0_TRIS, mainBLINK_LED0_PIN, mainBLINK_LED0_INTERVAL};
const SBLINK sled1 = {&mainBLINK_LED1_PORT, &mainBLINK_LED1_TRIS, mainBLINK_LED1_PIN, mainBLINK_LED1_INTERVAL};
const SBLINK sled2 = {&mainBLINK_LED2_PORT, &mainBLINK_LED2_TRIS, mainBLINK_LED2_PIN, mainBLINK_LED2_INTERVAL};
const SBLINK sled3 = {&mainBLINK_LED3_PORT, &mainBLINK_LED3_TRIS, mainBLINK_LED3_PIN, mainBLINK_LED3_INTERVAL};
const SBLINK sled4 = {&mainBLINK_LED4_PORT, &mainBLINK_LED4_TRIS, mainBLINK_LED4_PIN, mainBLINK_LED4_INTERVAL};
const SBLINK sled5 = {&mainBLINK_LED5_PORT, &mainBLINK_LED5_TRIS, mainBLINK_LED5_PIN, mainBLINK_LED5_INTERVAL};
const SBLINK sled6 = {&mainBLINK_LED6_PORT, &mainBLINK_LED6_TRIS, mainBLINK_LED6_PIN, mainBLINK_LED6_INTERVAL};
const SBLINK sled7 = {&mainBLINK_LED7_PORT, &mainBLINK_LED7_TRIS, mainBLINK_LED7_PIN, mainBLINK_LED7_INTERVAL};

/*
 * The task code for the "vBlink" task.
 */
static portTASK_FUNCTION_PROTO(vBlink, pvParameters);

/*-----------------------------------------------------------*/

/*
 * Creates the tasks, then starts the scheduler.
 */
void main( void )
{
	/*
	 * Start the blink tasks defined in this file.
	 */
	xTaskCreate( vBlink,  "B0", configMINIMAL_STACK_SIZE, &sled0, tskIDLE_PRIORITY, NULL );
	xTaskCreate( vBlink,  "B1", configMINIMAL_STACK_SIZE, &sled1, tskIDLE_PRIORITY, NULL );
	xTaskCreate( vBlink,  "B2", configMINIMAL_STACK_SIZE, &sled2, tskIDLE_PRIORITY, NULL );
	xTaskCreate( vBlink,  "B3", configMINIMAL_STACK_SIZE, &sled3, tskIDLE_PRIORITY, NULL );
	xTaskCreate( vBlink,  "B4", configMINIMAL_STACK_SIZE, &sled4, tskIDLE_PRIORITY, NULL );
	xTaskCreate( vBlink,  "B5", configMINIMAL_STACK_SIZE, &sled5, tskIDLE_PRIORITY, NULL );
	xTaskCreate( vBlink,  "B6", configMINIMAL_STACK_SIZE, &sled6, tskIDLE_PRIORITY, NULL );
	xTaskCreate( vBlink,  "B7", configMINIMAL_STACK_SIZE, &sled7, tskIDLE_PRIORITY, NULL );

	/*
	 * Start the scheduler.
	 */
	vTaskStartScheduler( );
	
	while(1)	/* This point should never be reached. */
	{
	}
}
/*-----------------------------------------------------------*/

static portTASK_FUNCTION(vBlink, pvParameters)
{
	unsigned char	*Port		= ((SBLINK *)pvParameters)->port;
	unsigned char	*Tris		= ((SBLINK *)pvParameters)->tris;
	unsigned char	Pin			= ((SBLINK *)pvParameters)->pin;
	portTickType	Interval	= ((SBLINK *)pvParameters)->interval;
	
	portTickType	xLastWakeTime;

	/*
	 * Initialize the hardware
	 */
	*Tris &= ~(1<<Pin);	// Set the pin that is used by this task to ouput
	*Port &= ~(1<<Pin);	// Drive the pin low
	
	/*
	 * Initialise the xLastWakeTime variable with the current time.
	 */
	xLastWakeTime = xTaskGetTickCount();

	/*
	 * Cycle for ever, delaying then toggle the LED.
	 */
	for( ;; )
	{
		/*
		 * Wait until it is time to toggle
		 */
		vTaskDelayUntil( &xLastWakeTime, Interval );

		/*
		 * Toggle the LED for visual feedback.
		 */
		*Port ^= 1<<Pin;
	}
}
