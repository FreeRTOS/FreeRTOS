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
 * This is a mini co-routine demo for the Rowley CrossFire LM3S102 development
 * board.  It makes use of the boards tri-colour LED and analogue input.
 *
 * Four co-routines are created - an 'I2C' co-routine and three 'flash'
 * co-routines.
 *
 * The I2C co-routine triggers an ADC conversion then blocks on a queue to 
 * wait for the conversion result - which it receives on the queue directly
 * from the I2C interrupt service routine.  The conversion result is then
 * scalled to a delay period.  The I2C interrupt then wakes each of the 
 * flash co-routines before itself delaying for the calculated period and
 * then repeating the whole process.
 *
 * When woken by the I2C co-routine the flash co-routines each block for 
 * a given period, illuminate an LED for a fixed period, then go back to
 * sleep to wait for the next cycle.  The uxIndex parameter of the flash
 * co-routines is used to ensure that each flashes a different LED, and that
 * the delay periods are such that the LED's get flashed in sequence.
 */


/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "croutine.h"

/* Demo application include files. */
#include "partest.h"

/* Library include files. */
#include "DriverLib.h"

/* States of the I2C master interface. */
#define mainI2C_IDLE       0
#define mainI2C_READ_1     1
#define mainI2C_READ_2     2
#define mainI2C_READ_DONE  3

#define mainZERO_LENGTH 0

/* Address of the A2D IC on the CrossFire board. */
#define mainI2CAddress	0x4D

/* The queue used to send data from the I2C ISR to the co-routine should never
contain more than one item as the same co-routine is used to trigger the I2C
activity. */
#define mainQUEUE_LENGTH 1

/* The CrossFire board contains a tri-colour LED. */
#define mainNUM_LEDs	3

/* The I2C co-routine has a higher priority than the flash co-routines.  This
is not really necessary as when the I2C co-routine is active the other 
co-routines are delaying. */
#define mainI2c_CO_ROUTINE_PRIORITY 1


/* The current state of the I2C master. */
static volatile unsigned portBASE_TYPE uxState = mainI2C_IDLE;

/* The delay period derived from the A2D value. */
static volatile portBASE_TYPE uxDelay = 250;

/* The queue used to communicate between the I2C interrupt and the I2C 
co-routine. */
static xQueueHandle xADCQueue;

/* The queue used to synchronise the flash co-routines. */
static xQueueHandle xDelayQueue;

/*
 * Sets up the PLL, I2C and GPIO used by the demo.
 */
static void prvSetupHardware( void );

/* The co-routines as described at the top of the file. */
static void vI2CCoRoutine( xCoRoutineHandle xHandle, unsigned portBASE_TYPE uxIndex );
static void vFlashCoRoutine( xCoRoutineHandle xHandle, unsigned portBASE_TYPE uxIndex );

/*-----------------------------------------------------------*/

int main( void )
{
unsigned portBASE_TYPE uxCoRoutine;

	/* Setup all the hardware used by this demo. */
	prvSetupHardware();

	/* Create the queue used to communicate between the ISR and I2C co-routine.
	This can only ever contain one value. */
	xADCQueue = xQueueCreate( mainQUEUE_LENGTH, sizeof( portTickType ) );

	/* Create the queue used to synchronise the flash co-routines.  The queue
	is used to trigger three tasks, but is for synchronisation only and does
	not pass any data.  It therefore has three position each of zero length. */
	xDelayQueue = xQueueCreate( mainNUM_LEDs, mainZERO_LENGTH );

	/* Create the co-routine that initiates the i2c. */
	xCoRoutineCreate( vI2CCoRoutine, mainI2c_CO_ROUTINE_PRIORITY, 0 );

	/* Create the flash co-routines. */
	for( uxCoRoutine = 0; uxCoRoutine < mainNUM_LEDs; uxCoRoutine++ )
	{
		xCoRoutineCreate( vFlashCoRoutine, tskIDLE_PRIORITY, uxCoRoutine );        
	}

	/* Start the scheduler.  From this point on the co-routines should 
	execute. */
	vTaskStartScheduler();

	/* Should not get here unless we did not have enough memory to start the
	scheduler. */
	for( ;; );
	return 0;
}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
	/* Setup the PLL. */
	SysCtlClockSet( SYSCTL_SYSDIV_10 | SYSCTL_USE_PLL | SYSCTL_OSC_MAIN | SYSCTL_XTAL_6MHZ );

	/* Enable the I2C used to read the pot. */
	SysCtlPeripheralEnable( SYSCTL_PERIPH_I2C );
	SysCtlPeripheralEnable( SYSCTL_PERIPH_GPIOB );
	GPIOPinTypeI2C( GPIO_PORTB_BASE, GPIO_PIN_2 | GPIO_PIN_3 );

	/* Initialize the I2C master. */
	I2CMasterInit( I2C_MASTER_BASE, pdFALSE );
	
	/* Enable the I2C master interrupt. */
	I2CMasterIntEnable( I2C_MASTER_BASE );
    IntEnable( INT_I2C );

	/* Initialise the hardware used to talk to the LED's. */
	vParTestInitialise();
}
/*-----------------------------------------------------------*/

static void vI2CCoRoutine( xCoRoutineHandle xHandle, unsigned portBASE_TYPE uxIndex )
{
portTickType xADCResult;
static portBASE_TYPE xResult = 0, xMilliSecs, xLED;

	crSTART( xHandle );

	for( ;; )
	{
		/* Start the I2C off to read the ADC. */
		uxState = mainI2C_READ_1;
		I2CMasterSlaveAddrSet( I2C_MASTER_BASE, mainI2CAddress, pdTRUE );		
		I2CMasterControl( I2C_MASTER_BASE, I2C_MASTER_CMD_BURST_RECEIVE_START );

		/* Wait to receive the conversion result. */
		crQUEUE_RECEIVE( xHandle, xADCQueue, &xADCResult, portMAX_DELAY, &xResult );

		/* Scale the result to give a useful range of values for a visual 
		demo. */
		xADCResult >>= 2;
		xMilliSecs = xADCResult / portTICK_RATE_MS;

		/* The delay is split between the four co-routines so they remain in
		synch. */
		uxDelay = xMilliSecs / ( mainNUM_LEDs + 1 );

		/* Trigger each of the flash co-routines. */
		for( xLED = 0; xLED < mainNUM_LEDs; xLED++ )
		{
			crQUEUE_SEND( xHandle, xDelayQueue, &xLED, 0, &xResult );
		}

		/* Wait for the full delay time then start again.  This delay is long 
		enough to ensure the flash co-routines have done their thing and gone
		back to sleep. */
		crDELAY( xHandle, xMilliSecs );
	}

	crEND();
}
/*-----------------------------------------------------------*/

static void vFlashCoRoutine( xCoRoutineHandle xHandle, unsigned portBASE_TYPE uxIndex )
{
portBASE_TYPE xResult, xNothing;

	crSTART( xHandle );

	for( ;; )
	{
		/* Wait for start of next round. */
		crQUEUE_RECEIVE( xHandle, xDelayQueue, &xNothing, portMAX_DELAY, &xResult );

		/* Wait until it is this co-routines turn to flash. */
		crDELAY( xHandle, uxDelay * uxIndex );

		/* Turn on the LED for a fixed period. */
		vParTestSetLED( uxIndex, pdTRUE );
		crDELAY( xHandle, uxDelay );
		vParTestSetLED( uxIndex, pdFALSE );

		/* Go back and wait for the next round. */
	}

	crEND();
}
/*-----------------------------------------------------------*/

void vI2C_ISR(void)
{
static portTickType xReading;

	/* Clear the interrupt. */
	I2CMasterIntClear( I2C_MASTER_BASE );

	/* Determine what to do based on the current uxState. */
	switch (uxState)
	{
		case mainI2C_IDLE:		break;
	
		case mainI2C_READ_1:	/* Read ADC result high byte. */
								xReading = I2CMasterDataGet( I2C_MASTER_BASE );
								xReading <<= 8;
		
								/* Continue the burst read. */
								I2CMasterControl( I2C_MASTER_BASE, I2C_MASTER_CMD_BURST_RECEIVE_CONT );
								uxState = mainI2C_READ_2;
								break;
	
		case mainI2C_READ_2:	/* Read ADC result low byte. */
								xReading |= I2CMasterDataGet( I2C_MASTER_BASE );								
			
								/* Finish the burst read. */
								I2CMasterControl( I2C_MASTER_BASE, I2C_MASTER_CMD_BURST_RECEIVE_FINISH );
								uxState = mainI2C_READ_DONE;
								break;
			
		case mainI2C_READ_DONE:	/* Complete. */
								I2CMasterDataGet( I2C_MASTER_BASE );
								uxState = mainI2C_IDLE;

								/* Send the result to the co-routine. */
                                crQUEUE_SEND_FROM_ISR( xADCQueue, &xReading, pdFALSE );
								break;
	}
}
/*-----------------------------------------------------------*/

void vApplicationIdleHook( void )
{
	for( ;; )
	{
		vCoRoutineSchedule();
	}
}

