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

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "Task.h"

/* Renesas driver includes. */
#include "stdint.h"
#include "dev_drv.h"
#include "devdrv_ostm.h"
#include "devdrv_intc.h"
#include "iodefine.h"

#define runtimeCLOCK_SCALE_SHIFT	( 9UL )
#define runtimeOVERFLOW_BIT			( 1UL << ( 32UL - runtimeCLOCK_SCALE_SHIFT ) )

/* To make casting to the ISR prototype expected by the Renesas GIC drivers. */
typedef void (*ISR_FUNCTION)( uint32_t );

/*
 * The application must provide a function that configures a peripheral to
 * create the FreeRTOS tick interrupt, then define configSETUP_TICK_INTERRUPT()
 * in FreeRTOSConfig.h to call the function.  This file contains a function
 * that is suitable for use on the Renesas RZ MPU.
 */
void vConfigureTickInterrupt( void )
{
	/* Stop the counter. */
    OSTM0.OSTMnTT.BIT.OSTMnTT = 1;

    /* Work in interval mode. */
    OSTM0.OSTMnCTL.BIT.OSTMnMD1 = OSTM_MODE_INTERVAL;

    /* Use interrupts after counting starts. */
    OSTM0.OSTMnCTL.BIT.OSTMnMD0 = 1;

    /* Start value for down counter. */
    OSTM0.OSTMnCMP = configPERIPHERAL_CLOCK_HZ / configTICK_RATE_HZ;

    /* Configure the interrupt controller. */
    R_INTC_RegistIntFunc( INTC_ID_OSTMI0, ( ISR_FUNCTION ) FreeRTOS_Tick_Handler );

    /* Tick must be assigned the lowest interrupt priority. */
    R_INTC_SetPriority( INTC_ID_OSTMI0, portLOWEST_USABLE_INTERRUPT_PRIORITY );

    INTC.ICCBPR.BIT.Binarypoint = 0;
    R_INTC_Enable( INTC_ID_OSTMI0 );

    R_OSTM_Open( DEVDRV_CH_0 );
}
/*-----------------------------------------------------------*/

/*
 * Crude implementation of a run time counter used to measure how much time
 * each task spends in the Running state.
 */
unsigned long ulGetRunTimeCounterValue( void )
{
static unsigned long ulLastCounterValue = 0UL, ulOverflows = 0;
unsigned long ulValueNow;

	ulValueNow = OSTM1.OSTMnCNT;

	/* Has the value overflowed since it was last read. */
	if( ulValueNow < ulLastCounterValue )
	{
		ulOverflows++;
	}
	ulLastCounterValue = ulValueNow;

	/* There is no prescale on the counter, so simulate in software. */
	ulValueNow >>= runtimeCLOCK_SCALE_SHIFT;
	ulValueNow += ( runtimeOVERFLOW_BIT * ulOverflows );

	return ulValueNow;
}
/*-----------------------------------------------------------*/

void vInitialiseRunTimeStats( void )
{
	/* OSTM1 is used as the run time stats counter. */

	/* Stop the counter. */
    OSTM1.OSTMnTT.BIT.OSTMnTT = 1;

    /* Work in compare mode mode. */
    OSTM1.OSTMnCTL.BIT.OSTMnMD1 = OSTM_MODE_COMPARE;

    /* Don't use interrupts. */
    OSTM1.OSTMnCTL.BIT.OSTMnMD0 = 0;

    /* Compare is just set to 0. */
    OSTM1.OSTMnCMP = 0;

    R_OSTM_Open( DEVDRV_CH_1 );
}



