/*
    FreeRTOS V7.6.0 - Copyright (C) 2013 Real Time Engineers Ltd. 
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that has become a de facto standard.             *
     *                                                                       *
     *    Help yourself get started quickly and support the FreeRTOS         *
     *    project by purchasing a FreeRTOS tutorial book, reference          *
     *    manual, or both from: http://www.FreeRTOS.org/Documentation        *
     *                                                                       *
     *    Thank you!                                                         *
     *                                                                       *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>!AND MODIFIED BY!<< the FreeRTOS exception.

    >>! NOTE: The modification to the GPL is included to allow you to distribute
    >>! a combined work that includes FreeRTOS without being obliged to provide
    >>! the source code for proprietary components outside of the FreeRTOS
    >>! kernel.

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available from the following
    link: http://www.freertos.org/a00114.html

    1 tab == 4 spaces!

    ***************************************************************************
     *                                                                       *
     *    Having a problem?  Start by reading the FAQ "My application does   *
     *    not run, what could be wrong?"                                     *
     *                                                                       *
     *    http://www.FreeRTOS.org/FAQHelp.html                               *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org - Documentation, books, training, latest versions,
    license and Real Time Engineers Ltd. contact details.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.OpenRTOS.com - Real Time Engineers ltd license FreeRTOS to High
    Integrity Systems to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and middleware.

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

/* ST library functions. */
#include "stm32l152_eval.h"

#define partstMAX_OUTPUT_LED 4

/*-----------------------------------------------------------*/

void vParTestInitialise( void )
{
	/* Configure the output LEDs.   Note that JP18 and JP19 must be closed on
	the Eval board for LED3 and LED4 to work. */
	STM_EVAL_LEDInit( LED1 );
	STM_EVAL_LEDInit( LED2 );
	STM_EVAL_LEDInit( LED3 );
	STM_EVAL_LEDInit( LED4 );
	STM_EVAL_LEDOff( LED1 );
	STM_EVAL_LEDOff( LED2 );
	STM_EVAL_LEDOff( LED3 );
	STM_EVAL_LEDOff( LED4 );	
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned portBASE_TYPE uxLED, signed portBASE_TYPE xValue )
{
	vTaskSuspendAll();
	{
		if( xValue != pdFALSE )
		{
			switch( uxLED )
			{
				case 0: STM_EVAL_LEDOn( LED1 );
						break;
	
				case 1: STM_EVAL_LEDOn( LED2 );
						break;
	
				case 2: STM_EVAL_LEDOn( LED3 );
						break;
	
				case 3: STM_EVAL_LEDOn( LED4 );
						break;					
			}
		}
		else
		{
			switch( uxLED )
			{
				case 0: STM_EVAL_LEDOff( LED1 );
						break;
	
				case 1: STM_EVAL_LEDOff( LED2 );
						break;
	
				case 2: STM_EVAL_LEDOff( LED3 );
						break;
	
				case 3: STM_EVAL_LEDOff( LED4 );
						break;					
			}
		}
	}
	xTaskResumeAll();
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned portBASE_TYPE uxLED )
{
	vTaskSuspendAll();
	{
		switch( uxLED )
		{
			case 0: STM_EVAL_LEDToggle( LED1 );
					break;

			case 1: STM_EVAL_LEDToggle( LED2 );
					break;

			case 2: STM_EVAL_LEDToggle( LED3 );
					break;

			case 3: STM_EVAL_LEDToggle( LED4 );
					break;					
		}
	}
	xTaskResumeAll();
}
/*-----------------------------------------------------------*/

