/*
 * FreeRTOS Kernel V10.1.0
 * Copyright (C) 2017 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

