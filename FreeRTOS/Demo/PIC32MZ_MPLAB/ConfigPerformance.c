/*
    FreeRTOS V8.1.0 - Copyright (C) 2014 Real Time Engineers Ltd.
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

    >>!   NOTE: The modification to the GPL is included to allow you to     !<<
    >>!   distribute a combined work that includes FreeRTOS without being   !<<
    >>!   obliged to provide the source code for proprietary components     !<<
    >>!   outside of the FreeRTOS kernel.                                   !<<

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

/*
 * This file implements functions to access and manipulate the PIC32 hardware
 * without reliance on third party library functions that may be liable to
 * change.
 */

/* FreeRTOS includes. */
#include "FreeRTOS.h"

/* Demo includes. */
#include "ConfigPerformance.h"

#define hwUNLOCK_KEY_0					( 0xAA996655UL )
#define hwUNLOCK_KEY_1					( 0x556699AAUL )

/*-----------------------------------------------------------*/

void vHardwareConfigurePerformance( void )
{
	/* set PBCLK2 to deliver 40Mhz clock for PMP/I2C/UART/SPI. */
	SYSKEY = hwUNLOCK_KEY_0;
	SYSKEY = hwUNLOCK_KEY_1;

	/* 200MHz / 5 = 40MHz */
	PB2DIVbits.PBDIV = 0b100;

	/* Timers use clock PBCLK3, set this to 40MHz. */
	PB3DIVbits.PBDIV = 0b100;

	/* Ports use PBCLK4. */
	PB4DIVbits.PBDIV = 0b000;

	SYSKEY = 0;

	/* Disable interrupts - note taskDISABLE_INTERRUPTS() cannot be used here as
	FreeRTOS does not globally disable interrupt. */
	__builtin_disable_interrupts();
}
/*-----------------------------------------------------------*/

void vHardwareUseMultiVectoredInterrupts( void )
{
	/* Enable multi-vector interrupts. */
	_CP0_BIS_CAUSE( 0x00800000U );
	INTCONSET = _INTCON_MVEC_MASK;
	__builtin_enable_interrupts();
}




