/*
    FreeRTOS V7.0.1 - Copyright (C) 2011 Real Time Engineers Ltd.
	

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS tutorial books are available in pdf and paperback.        *
     *    Complete, revised, and edited pdf reference manuals are also       *
     *    available.                                                         *
     *                                                                       *
     *    Purchasing FreeRTOS documentation will not only help you, by       *
     *    ensuring you get running as quickly as possible and with an        *
     *    in-depth knowledge of how to use FreeRTOS, it will also help       *
     *    the FreeRTOS project to continue with its mission of providing     *
     *    professional grade, cross platform, de facto standard solutions    *
     *    for microcontrollers - completely free of charge!                  *
     *                                                                       *
     *    >>> See http://www.FreeRTOS.org/Documentation for details. <<<     *
     *                                                                       *
     *    Thank you for using FreeRTOS, and thank you for your support!      *
     *                                                                       *
    ***************************************************************************


    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.
    >>>NOTE<<< The modification to the GPL is included to allow you to
    distribute a combined work that includes FreeRTOS without being obliged to
    provide the source code for proprietary components outside of the FreeRTOS
    kernel.  FreeRTOS is distributed in the hope that it will be useful, but
    WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
    or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
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

/* Standard includes. */
#include <stdlib.h>

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Critical nesting should be initialised to a non zero value so interrupts don't
accidentally get enabled before the scheduler is started. */
#define portINITIAL_CRITICAL_NESTING  (( portSTACK_TYPE ) 10)

/* The PSW value assigned to tasks when they start to run for the first time. */
#define portPSW		  (( portSTACK_TYPE ) 0x00000000)

/* We require the address of the pxCurrentTCB variable, but don't want to know
any details of its type. */
typedef void tskTCB;
extern volatile tskTCB * volatile pxCurrentTCB;

/* Keeps track of the nesting level of critical sections. */
volatile portSTACK_TYPE usCriticalNesting = portINITIAL_CRITICAL_NESTING;
/*-----------------------------------------------------------*/

/* Sets up the timer to generate the tick interrupt. */
static void prvSetupTimerInterrupt( void );

/*-----------------------------------------------------------*/
portSTACK_TYPE *pxPortInitialiseStack( portSTACK_TYPE *pxTopOfStack, pdTASK_CODE pxCode, void *pvParameters )
{
	*pxTopOfStack = ( portSTACK_TYPE ) pxCode;          /* Task function start address */
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) pxCode;          /* Task function start address */
	pxTopOfStack--;
	*pxTopOfStack = portPSW;                            /* Initial PSW value */
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0x20202020;      /* Initial Value of R20 */
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0x21212121;      /* Initial Value of R21 */
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0x22222222;      /* Initial Value of R22 */
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0x23232323;      /* Initial Value of R23 */
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0x24242424;      /* Initial Value of R24 */
	pxTopOfStack--;
#if (__DATA_MODEL__ == 0) || (__DATA_MODEL__ == 1)
	*pxTopOfStack = ( portSTACK_TYPE ) 0x25252525;      /* Initial Value of R25 */
	pxTopOfStack--;
#endif /* configDATA_MODE */
	*pxTopOfStack = ( portSTACK_TYPE ) 0x26262626;      /* Initial Value of R26 */
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0x27272727;      /* Initial Value of R27 */
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0x28282828;      /* Initial Value of R28 */
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0x29292929;      /* Initial Value of R29 */
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0x30303030;      /* Initial Value of R30 */
	pxTopOfStack--; 	
	*pxTopOfStack = ( portSTACK_TYPE ) 0x19191919;      /* Initial Value of R19 */
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0x18181818;      /* Initial Value of R18 */
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0x17171717;      /* Initial Value of R17 */
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0x16161616;      /* Initial Value of R16 */
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0x15151515;      /* Initial Value of R15 */
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0x14141414;      /* Initial Value of R14 */
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0x13131313;      /* Initial Value of R13 */
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0x12121212;      /* Initial Value of R12 */
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0x11111111;      /* Initial Value of R11 */
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0x10101010;      /* Initial Value of R10 */
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0x99999999;      /* Initial Value of R09 */
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0x88888888;      /* Initial Value of R08 */
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0x77777777;      /* Initial Value of R07 */
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0x66666666;      /* Initial Value of R06 */
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0x55555555;      /* Initial Value of R05 */
	pxTopOfStack--;
#if __DATA_MODEL__ == 0 || __DATA_MODEL__ == 1
	*pxTopOfStack = ( portSTACK_TYPE ) 0x44444444;      /* Initial Value of R04 */
	pxTopOfStack--;
#endif /* configDATA_MODE */
	*pxTopOfStack = ( portSTACK_TYPE ) 0x22222222;      /* Initial Value of R02 */
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) pvParameters;    /* R1 is expected to hold the function parameter*/
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) portNO_CRITICAL_SECTION_NESTING;	

	/*
	 * Return a pointer to the top of the stack we have generated so this can
	 * be stored in the task control block for the task.
	 */
	return pxTopOfStack;
}
/*-----------------------------------------------------------*/

portBASE_TYPE xPortStartScheduler( void )
{
	/* Setup the hardware to generate the tick.  Interrupts are disabled when
	this function is called. */
	prvSetupTimerInterrupt();

	/* Restore the context of the first task that is going to run. */
	vPortStart();

	/* Should not get here as the tasks are now running! */
	return pdTRUE;
}
/*-----------------------------------------------------------*/

void vPortEndScheduler( void )
{
	/* It is unlikely that the V850ES/Fx3 port will get stopped.  If required simply
	disable the tick interrupt here. */
}
/*-----------------------------------------------------------*/

/*
 * Hardware initialisation to generate the RTOS tick.  This uses
 */
static void prvSetupTimerInterrupt( void )
{
	TM0CE     = 0;	/* TMM0 operation disable */
	TM0EQMK0  = 1;	/* INTTM0EQ0 interrupt disable */
	TM0EQIF0  = 0;	/* clear INTTM0EQ0 interrupt flag */

	#ifdef __IAR_V850ES_Fx3__
	{
		TM0CMP0   = (((configCPU_CLOCK_HZ / configTICK_RATE_HZ) / 2)-1);    /* divided by 2 because peripherals only run at CPU_CLOCK/2 */
	}
	#else
	{
		TM0CMP0   = (configCPU_CLOCK_HZ / configTICK_RATE_HZ);	
	}
	#endif

	TM0EQIC0 &= 0xF8;
	TM0CTL0   = 0x00;
	TM0EQIF0 =  0;	/* clear INTTM0EQ0 interrupt flag */
	TM0EQMK0 =  0;	/* INTTM0EQ0 interrupt enable */
	TM0CE =     1;	/* TMM0 operation enable */
}
/*-----------------------------------------------------------*/


