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

/* Hardware specifics. */
#include "iodefine.h"

/*-----------------------------------------------------------*/

/* Tasks should start with interrupts enabled and in Supervisor mode, therefore 
PSW is set with U and I set, and PM and IPL clear. */
#define portINITIAL_PSW     ( ( portSTACK_TYPE ) 0x00030000 )
#define portINITIAL_FPSW    ( ( portSTACK_TYPE ) 0x00000100 )

/*-----------------------------------------------------------*/

/*
 * Function to start the first task executing - written in asm code as direct
 * access to registers is required. 
 */
static void prvStartFirstTask( void ) __attribute__((naked));

/*
 * Software interrupt handler.  Performs the actual context switch (saving and
 * restoring of registers).  Written in asm code as direct register access is
 * required.
 */
static void prvYieldHandler( void );

/*
 * The entry point for the software interrupt handler.  This is the function
 * that calls the inline asm function prvYieldHandler().  It is installed in 
 * the vector table, but the code that installs it is in prvYieldHandler rather
 * than using a #pragma.
 */
void vSoftwareInterruptISR( void );

/*-----------------------------------------------------------*/

/* This is accessed by the inline assembler functions so is file scope for
convenience. */
extern void *pxCurrentTCB;
extern void vTaskSwitchContext( void );

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
	
	/* When debugging it can be useful if every register is set to a known
	value.  Otherwise code space can be saved by just setting the registers
	that need to be set. */
	#ifdef USE_FULL_REGISTER_INITIALISATION
	{
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
	}
	#else
	{
		pxTopOfStack -= 15;
	}
	#endif
	
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

		/* Enable the software interrupt. */		
		_IEN( _ICU_SWINT ) = 1;
		
		/* Ensure the software interrupt is clear. */
		_IR( _ICU_SWINT ) = 0;
		
		/* Ensure the software interrupt is set to the kernel priority. */
		_IPR( _ICU_SWINT ) = configKERNEL_INTERRUPT_PRIORITY;
	
		/* Start the first task. */
		prvStartFirstTask();
	}

	/* Just to make sure the function is not optimised away. */
	( void ) vSoftwareInterruptISR();

	/* Should not get here. */
	return pdFAIL;
}
/*-----------------------------------------------------------*/

static void prvStartFirstTask( void )
{
	__asm
	(	
		/* When starting the scheduler there is nothing that needs moving to the
		interrupt stack because the function is not called from an interrupt.
		Just ensure the current stack is the user stack. */
		"SETPSW	U						\n" \

		/* Obtain the location of the stack associated with which ever task 
		pxCurrentTCB is currently pointing to. */
		"MOV.L	#_pxCurrentTCB, R15		\n" \
		"MOV.L	[R15], R15				\n" \
		"MOV.L	[R15], R0				\n" \

		/* Restore the registers from the stack of the task pointed to by 
		pxCurrentTCB. */
	    "POP		R15					\n" \
		
		/* Accumulator low 32 bits. */
	    "MVTACLO	R15 				\n" \
	    "POP		R15					\n" \
		
		/* Accumulator high 32 bits. */
	    "MVTACHI	R15 				\n" \
	    "POP		R15					\n" \
		
		/* Floating point status word. */
	    "MVTC		R15, FPSW 			\n" \
		
		/* R1 to R15 - R0 is not included as it is the SP. */
	    "POPM		R1-R15 				\n" \
		
		/* This pops the remaining registers. */
	    "RTE							\n" \
	    "NOP							\n" \
	    "NOP							\n"
	);
}
/*-----------------------------------------------------------*/

void vTickISR( void )
{
	/* Increment the tick, and perform any processing the new tick value
	necessitates. */
	vTaskIncrementTick();
	
	/* Only select a new task if the preemptive scheduler is being used. */
	#if( configUSE_PREEMPTION == 1 )
		taskYIELD();
	#endif
}
/*-----------------------------------------------------------*/

void vSoftwareInterruptISR( void )
{
//	prvYieldHandler();
}
/*-----------------------------------------------------------*/

#if 0
#pragma inline_asm prvYieldHandler
static void prvYieldHandler( void )
{
	/* Install as the software interrupt handler. */
	.RVECTOR    _VECT( _ICU_SWINT ), _vSoftwareInterruptISR

	/* Re-enable interrupts. */
	SETPSW	I

	/* Move the data that was automatically pushed onto the interrupt stack when
	the interrupt occurred from the interrupt stack to the user stack.  
	
	R15 is saved before it is clobbered. */
	PUSH.L	R15
	
	/* Read the user stack pointer. */
	MVFC	USP, R15
	
	/* Move the address down to the data being moved. */
	SUB		#12, R15
	MVTC	R15, USP
	
	/* Copy the data across. */
	MOV.L	[ R0 ], [ R15 ] ; R15
	MOV.L 	4[ R0 ], 4[ R15 ]  ; PC
	MOV.L	8[ R0 ], 8[ R15 ]  ; PSW

	/* Move the interrupt stack pointer to its new correct position. */
	ADD	#12, R0
	
	/* All the rest of the registers are saved directly to the user stack. */
	SETPSW	U

	/* Save the rest of the general registers (R15 has been saved already). */
	PUSHM	R1-R14
	
	/* Save the FPSW and accumulator. */
	MVFC	FPSW, R15
	PUSH.L	R15
	MVFACHI	R15
	PUSH.L	R15
	MVFACMI	R15	; Middle order word.
	SHLL	#16, R15 ; Shifted left as it is restored to the low order word.
	PUSH.L	R15

	/* Save the stack pointer to the TCB. */
	MOV.L	#_pxCurrentTCB, R15
	MOV.L	[ R15 ], R15
	MOV.L	R0, [ R15 ]
			
	/* Ensure the interrupt mask is set to the syscall priority while the kernel
	structures are being accessed. */
	MVTIPL	#configMAX_SYSCALL_INTERRUPT_PRIORITY

	/* Select the next task to run. */
	BSR.A	_vTaskSwitchContext

	/* Reset the interrupt mask as no more data structure access is required. */
	MVTIPL	#configKERNEL_INTERRUPT_PRIORITY

	/* Load the stack pointer of the task that is now selected as the Running
	state task from its TCB. */
	MOV.L	#_pxCurrentTCB,R15
	MOV.L	[ R15 ], R15
	MOV.L	[ R15 ], R0

	/* Restore the context of the new task.  The PSW (Program Status Word) and
	PC will be popped by the RTE instruction. */
	POP		R15
	MVTACLO	R15
	POP		R15
	MVTACHI	R15
	POP		R15
	MVTC	R15,FPSW
	POPM	R1-R15
	RTE
	NOP
	NOP
}
#endif
/*-----------------------------------------------------------*/

void vPortEndScheduler( void )
{
	/* Not implemented as there is nothing to return to. */
	
	/* The following line is just to prevent the symbol getting optimised away. */
	( void ) vTaskSwitchContext();
}
/*-----------------------------------------------------------*/

unsigned long ulPortGetIPL( void )
{
	__asm( 
			"MVFC	PSW, R1			\n"	\
			"SHLR	#28, R1			\n"	\
			"RTS					  "
		 );
}
/*-----------------------------------------------------------*/

void vPortSetIPL( unsigned long ulNewIPL )
{
	__asm( 
			"MVFC	PSW, R5			\n"	\
			"SHLL	#28, R1			\n" \
			"AND	#-0F000001H, R5 \n" \
			"OR		R1, R5			\n" \
			"MVTC	R5, PSW			\n" \
			"RTS					  "
		 );
}
/*-----------------------------------------------------------*/



