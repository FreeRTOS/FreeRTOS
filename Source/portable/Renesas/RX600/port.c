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

/*-----------------------------------------------------------
 * Implementation of functions defined in portable.h for the SH2A port.
 *----------------------------------------------------------*/

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Library includes. */
#include "string.h"

/*-----------------------------------------------------------*/

/* Tasks should start with interrupts enabled, therefore PSW is set with U,I,PM 
flags set and IPL clear. */
/* 
 U = 1 User stack pointer.
 I = 1 Interrupts enabled.
 PM = 0 Supervisor mode.
 IPL = 0 All interrupt priorities enabled.
*/
#define portINITIAL_PSW      ( ( portSTACK_TYPE ) 0x00030000 )
#define portINITIAL_FPSW     ( ( portSTACK_TYPE ) 0x00000100 )


/*-----------------------------------------------------------*/

/*
 * 
 */
void vPortYield( void );

/*
 * Function to start the first task executing.
 */
void vPortStartFirstTask( void );

void vPortPendContextSwitch( void );

static void prvStartFirstTask( void );

/*-----------------------------------------------------------*/

extern void *pxCurrentTCB;

/*-----------------------------------------------------------*/

/* 
 * See header file for description. 
 */
portSTACK_TYPE *pxPortInitialiseStack( portSTACK_TYPE *pxTopOfStack, pdTASK_CODE pxCode, void *pvParameters )
{
	/* R0 is not included as it is the stack pointer. */
	
	*pxTopOfStack = 0xdeadbeef;
	pxTopOfStack--;
 	*pxTopOfStack = portINITIAL_PSW;
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) pxCode;
	pxTopOfStack--;
	*pxTopOfStack = 0xffffffff;	/* r15. */
	pxTopOfStack--;
	*pxTopOfStack = 0xeeeeeeee;
	pxTopOfStack--;
	*pxTopOfStack = 0xdddddddd;
	pxTopOfStack--;
	*pxTopOfStack = 0xcccccccc;
	pxTopOfStack--;
	*pxTopOfStack = 0xbbbbbbbb;
	pxTopOfStack--;
	*pxTopOfStack = 0xaaaaaaaa;
	pxTopOfStack--;
	*pxTopOfStack = 0x99999999;
	pxTopOfStack--;
	*pxTopOfStack = 0x88888888;
	pxTopOfStack--;
	*pxTopOfStack = 0x77777777;
	pxTopOfStack--;
	*pxTopOfStack = 0x66666666;
	pxTopOfStack--;
	*pxTopOfStack = 0x55555555;
	pxTopOfStack--;
	*pxTopOfStack = 0x44444444;
	pxTopOfStack--;
	*pxTopOfStack = 0x33333333;
	pxTopOfStack--;
	*pxTopOfStack = 0x22222222;
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) pvParameters; /* R1 */
	pxTopOfStack--;				
	*pxTopOfStack = portINITIAL_FPSW;
	pxTopOfStack--;
	*pxTopOfStack = 0x12345678; /* Accumulator. */
	pxTopOfStack--;
	*pxTopOfStack = 0x87654321; /* Accumulator. */

	return pxTopOfStack;
}
/*-----------------------------------------------------------*/

portBASE_TYPE xPortStartScheduler( void )
{
extern void vApplicationSetupTimerInterrupt( void );

	/* Use pxCurrentTCB just so it does not get optimised away. */
	if( pxCurrentTCB != NULL )
	{
		/* Call an application function to set up the timer that will generate the
		tick interrupt.  This way the application can decide which peripheral to 
		use.  A demo application is provided to show a suitable example. */
		vApplicationSetupTimerInterrupt();

		/* Start the first task. */
		prvStartFirstTask();
	}

	/* Should not get here. */
	return pdFAIL;
}
/*-----------------------------------------------------------*/

void vPortEndScheduler( void )
{
	/* Not implemented as there is nothing to return to. */
}
/*-----------------------------------------------------------*/

void vPortYield( void )
{
}
/*-----------------------------------------------------------*/

#pragma interrupt (vTickISR(vect=configTICK_VECTOR,enable))
void vTickISR( void )
{
	/* Restore previous IPL on exit. */
	//set_ipl( configMAX_SYSCALL_INTERRUPT_PRIORITY );
	
	/* Clear the interrupt. */
	vTaskIncrementTick();
	
	#if( configUSE_PREEMPTION == 1 )
		taskYIELD();
	#endif
}
/*-----------------------------------------------------------*/

#pragma inline_asm prvStartFirstTask
static void prvStartFirstTask( void )
{
	/* When starting the scheduler there is nothing that needs moving to the
	interrupt stack because the function is not called from an interrupt.
	Just ensure the current stack is the user stack. */
	SETPSW      U

	/* Obtain the location of the stack associated with which ever task 
	pxCurrentTCB is currently pointing to. */
	MOV.L       #_pxCurrentTCB,R15
	MOV.L       [R15],R15
	MOV.L       [R15],R0

	/* Restore the registers from the stack of the task pointed to by 
	pxCurrentTCB. */
    POP		R15
    MVTACLO	R15 		/* Accumulator low 32 bits. */
    POP		R15
    MVTACHI	R15 		/* Accumulator high 32 bits. */
    POP		R15
    MVTC	R15,FPSW 	/* Floating point status word. */
    POPM	R1-R15 		/* R1 to R15 - R0 is not included as it is the SP. */
    RTE					/* This pops the remaining registers. */
    NOP
    NOP
}
