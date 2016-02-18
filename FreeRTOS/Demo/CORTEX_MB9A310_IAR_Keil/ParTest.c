/*
    FreeRTOS V9.0.0rc1 - Copyright (C) 2016 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>>> AND MODIFIED BY <<<< the FreeRTOS exception.

    ***************************************************************************
    >>!   NOTE: The modification to the GPL is included to allow you to     !<<
    >>!   distribute a combined work that includes FreeRTOS without being   !<<
    >>!   obliged to provide the source code for proprietary components     !<<
    >>!   outside of the FreeRTOS kernel.                                   !<<
    ***************************************************************************

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available on the following
    link: http://www.freertos.org/a00114.html

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that is more than just the market leader, it     *
     *    is the industry's de facto standard.                               *
     *                                                                       *
     *    Help yourself get started quickly while simultaneously helping     *
     *    to support the FreeRTOS project by purchasing a FreeRTOS           *
     *    tutorial book, reference manual, or both:                          *
     *    http://www.FreeRTOS.org/Documentation                              *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org/FAQHelp.html - Having a problem?  Start by reading
    the FAQ page "My application does not run, what could be wrong?".  Have you
    defined configASSERT()?

    http://www.FreeRTOS.org/support - In return for receiving this top quality
    embedded software for free we request you assist our global community by
    participating in the support forum.

    http://www.FreeRTOS.org/training - Investing in training allows your team to
    be as productive as possible as early as possible.  Now you can receive
    FreeRTOS training directly from Richard Barry, CEO of Real Time Engineers
    Ltd, and the world's leading authority on the world's leading RTOS.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.FreeRTOS.org/labs - Where new FreeRTOS products go to incubate.
    Come and try FreeRTOS+TCP, our new open source TCP/IP stack for FreeRTOS.

    http://www.OpenRTOS.com - Real Time Engineers ltd. license FreeRTOS to High
    Integrity Systems ltd. to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and commercial middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
*/

/*-----------------------------------------------------------
 * Simple parallel port IO routines.
 *-----------------------------------------------------------*/

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Fujitsu drivers/libraries. */
#include "mcu.h"

/* Only the LEDs on one of the two seven segment displays are used. */
#define partstMAX_LEDS		8

/*-----------------------------------------------------------*/

void vParTestInitialise( void )
{
	/* Analog inputs are not used on the LED outputs. */
	FM3_GPIO->ADE  = 0x0000;

	/* Set to output. */
	FM3_GPIO->DDR1 |= 0xFFFF;
	FM3_GPIO->DDR3 |= 0xFFFF;
	
	/* Set as GPIO. */
	FM3_GPIO->PFR1 &= 0x0000;
	FM3_GPIO->PFR3 &= 0x0000;

	/* Start with all LEDs off. */
	FM3_GPIO->PDOR1 = 0xFFFF;
	FM3_GPIO->PDOR1 = 0xFFFF;
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned portBASE_TYPE uxLED, signed portBASE_TYPE xValue )
{
	if( uxLED < partstMAX_LEDS )
	{
		/* A critical section is used as the LEDs are also accessed from an
		interrupt. */
		taskENTER_CRITICAL();
		{
			if( xValue == pdTRUE )
			{
				FM3_GPIO->PDOR1 &= ~( 1UL << uxLED );
			}
			else
			{
				FM3_GPIO->PDOR1 |= ( 1UL << uxLED );
			}
		}
		taskEXIT_CRITICAL();
	}
}
/*-----------------------------------------------------------*/

void vParTestSetLEDFromISR( unsigned portBASE_TYPE uxLED, signed portBASE_TYPE xValue )
{
unsigned portBASE_TYPE uxInterruptFlags;

	uxInterruptFlags = portSET_INTERRUPT_MASK_FROM_ISR();
	{
		if( uxLED < partstMAX_LEDS )
		{
			if( xValue == pdTRUE )
			{
				FM3_GPIO->PDOR1 &= ~( 1UL << uxLED );
			}
			else
			{
				FM3_GPIO->PDOR1 |= ( 1UL << uxLED );
			}
		}
	}
	portCLEAR_INTERRUPT_MASK_FROM_ISR( uxInterruptFlags );
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned portBASE_TYPE uxLED )
{
	if( uxLED < partstMAX_LEDS )
	{
		/* A critical section is used as the LEDs are also accessed from an
		interrupt. */
		taskENTER_CRITICAL();
		{
			if( ( FM3_GPIO->PDOR1 & ( 1UL << uxLED ) ) != 0UL )
			{
				FM3_GPIO->PDOR1 &= ~( 1UL << uxLED );
			}
			else
			{
				FM3_GPIO->PDOR1 |= ( 1UL << uxLED );
			}
		}
		taskEXIT_CRITICAL();
	}
}
/*-----------------------------------------------------------*/

