/*
    FreeRTOS V7.4.0 - Copyright (C) 2013 Real Time Engineers Ltd.

    FEATURES AND PORTS ARE ADDED TO FREERTOS ALL THE TIME.  PLEASE VISIT
    http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

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

    >>>>>>NOTE<<<<<< The modification to the GPL is included to allow you to
    distribute a combined work that includes FreeRTOS without being obliged to
    provide the source code for proprietary components outside of the FreeRTOS
    kernel.

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
    details. You should have received a copy of the GNU General Public License
    and the FreeRTOS license exception along with FreeRTOS; if not itcan be
    viewed here: http://www.freertos.org/a00114.html and also obtained by
    writing to Real Time Engineers Ltd., contact details for whom are available
    on the FreeRTOS WEB site.

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
    including FreeRTOS+Trace - an indispensable productivity tool, and our new
    fully thread aware and reentrant UDP/IP stack.

    http://www.OpenRTOS.com - Real Time Engineers ltd license FreeRTOS to High 
    Integrity Systems, who sell the code with commercial support, 
    indemnification and middleware, under the OpenRTOS brand.
    
    http://www.SafeRTOS.com - High Integrity Systems also provide a safety 
    engineered and independently SIL3 certified version for use in safety and 
    mission critical applications that require provable dependability.
*/

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"

/*-----------------------------------------------------------*/

/* Count of the critical section nesting depth. */
unsigned portLONG ulCriticalNesting = 9999;

/*-----------------------------------------------------------*/

/* Registers required to configure the RTI. */
#define portRTI_GCTRL_REG  		( * ( ( volatile unsigned long * ) 0xFFFFFC00 ) )
#define portRTI_TBCTRL_REG  	( * ( ( volatile unsigned long * ) 0xFFFFFC04 ) )
#define portRTI_COMPCTRL_REG  	( * ( ( volatile unsigned long * ) 0xFFFFFC0C ) )
#define portRTI_CNT0_FRC0_REG  	( * ( ( volatile unsigned long * ) 0xFFFFFC10 ) )
#define portRTI_CNT0_UC0_REG  	( * ( ( volatile unsigned long * ) 0xFFFFFC14 ) )
#define portRTI_CNT0_CPUC0_REG  ( * ( ( volatile unsigned long * ) 0xFFFFFC18 ) )
#define portRTI_CNT0_COMP0_REG  ( * ( ( volatile unsigned long * ) 0xFFFFFC50 ) )
#define portRTI_CNT0_UDCP0_REG  ( * ( ( volatile unsigned long * ) 0xFFFFFC54 ) )
#define portRTI_SETINTENA_REG  	( * ( ( volatile unsigned long * ) 0xFFFFFC80 ) )
#define portRTI_CLEARINTENA_REG ( * ( ( volatile unsigned long * ) 0xFFFFFC84 ) )
#define portRTI_INTFLAG_REG  	( * ( ( volatile unsigned long * ) 0xFFFFFC88 ) )


/* Constants required to set up the initial stack of each task. */
#define portINITIAL_SPSR	   	( ( portSTACK_TYPE ) 0x1F )
#define portINITIAL_FPSCR	  	( ( portSTACK_TYPE ) 0x00 )
#define portINSTRUCTION_SIZE   	( ( portSTACK_TYPE ) 0x04 )
#define portTHUMB_MODE_BIT		( ( portSTACK_TYPE ) 0x20 )

/* The number of words on the stack frame between the saved Top Of Stack and
R0 (in which the parameters are passed. */
#define portSPACE_BETWEEN_TOS_AND_PARAMETERS	( 12 )

/*-----------------------------------------------------------*/

/* vPortStartFirstSTask() is defined in portASM.asm */
extern void vPortStartFirstTask( void );

/*-----------------------------------------------------------*/

/* Saved as part of the task context.  Set to pdFALSE if the task does not
require an FPU context. */
unsigned long ulTaskHasFPUContext = 0;

/*-----------------------------------------------------------*/


/*
 * See header file for description.
 */
portSTACK_TYPE *pxPortInitialiseStack( portSTACK_TYPE *pxTopOfStack, pdTASK_CODE pxCode, void *pvParameters )
{
portSTACK_TYPE *pxOriginalTOS;

	pxOriginalTOS = pxTopOfStack;

	#if __TI_VFP_SUPPORT__
	{
		/* Ensure the stack is correctly aligned on exit. */
		pxTopOfStack--;
	}
	#endif

	/* Setup the initial stack of the task.  The stack is set exactly as
	expected by the portRESTORE_CONTEXT() macro. */

	/* First on the stack is the return address - which is the start of the as
	the task has not executed yet.  The offset is added to make the return
	address appear as it would within an IRQ ISR. */
	*pxTopOfStack = ( portSTACK_TYPE ) pxCode + portINSTRUCTION_SIZE;
	pxTopOfStack--;

	*pxTopOfStack = ( portSTACK_TYPE ) 0x00000000;	/* R14 */
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) pxOriginalTOS; /* Stack used when task starts goes in R13. */
	pxTopOfStack--;

	#ifdef portPRELOAD_TASK_REGISTERS
	{
		*pxTopOfStack = ( portSTACK_TYPE ) 0x12121212;	/* R12 */
		pxTopOfStack--;
		*pxTopOfStack = ( portSTACK_TYPE ) 0x11111111;	/* R11 */
		pxTopOfStack--;
		*pxTopOfStack = ( portSTACK_TYPE ) 0x10101010;	/* R10 */
		pxTopOfStack--;
		*pxTopOfStack = ( portSTACK_TYPE ) 0x09090909;	/* R9 */
		pxTopOfStack--;
		*pxTopOfStack = ( portSTACK_TYPE ) 0x08080808;	/* R8 */
		pxTopOfStack--;
		*pxTopOfStack = ( portSTACK_TYPE ) 0x07070707;	/* R7 */
		pxTopOfStack--;
		*pxTopOfStack = ( portSTACK_TYPE ) 0x06060606;	/* R6 */
		pxTopOfStack--;
		*pxTopOfStack = ( portSTACK_TYPE ) 0x05050505;	/* R5 */
		pxTopOfStack--;
		*pxTopOfStack = ( portSTACK_TYPE ) 0x04040404;	/* R4 */
		pxTopOfStack--;
		*pxTopOfStack = ( portSTACK_TYPE ) 0x03030303;	/* R3 */
		pxTopOfStack--;
		*pxTopOfStack = ( portSTACK_TYPE ) 0x02020202;	/* R2 */
		pxTopOfStack--;
		*pxTopOfStack = ( portSTACK_TYPE ) 0x01010101;	/* R1 */
		pxTopOfStack--;
	}
	#else
	{
		pxTopOfStack -= portSPACE_BETWEEN_TOS_AND_PARAMETERS;
	}
	#endif

	/* Function parameters are passed in R0. */
	*pxTopOfStack = ( portSTACK_TYPE ) pvParameters; /* R0 */
	pxTopOfStack--;

	/* Set the status register for system mode, with interrupts enabled. */
	*pxTopOfStack = ( portSTACK_TYPE ) ( ( _get_CPSR() & ~0xFF ) | portINITIAL_SPSR );

	if( ( ( unsigned long ) pxCode & 0x01UL ) != 0x00 )
	{
		/* The task will start in thumb mode. */
		*pxTopOfStack |= portTHUMB_MODE_BIT;
	}

	#ifdef __TI_VFP_SUPPORT__
	{
		pxTopOfStack--;

		/* The last thing on the stack is the tasks ulUsingFPU value, which by
		default is set to indicate that the stack frame does not include FPU
		registers. */
		*pxTopOfStack = pdFALSE;
	}
	#endif

	return pxTopOfStack;
}
/*-----------------------------------------------------------*/

static void prvSetupTimerInterrupt(void)
{
	/* Disable timer 0. */
	portRTI_GCTRL_REG &= 0xFFFFFFFEUL;

	/* Use the internal counter. */
	portRTI_TBCTRL_REG = 0x00000000U;

	/* COMPSEL0 will use the RTIFRC0 counter. */
	portRTI_COMPCTRL_REG = 0x00000000U;

	/* Initialise the counter and the prescale counter registers. */
	portRTI_CNT0_UC0_REG =  0x00000000U;
	portRTI_CNT0_FRC0_REG =  0x00000000U;

	/* Set Prescalar for RTI clock. */
	portRTI_CNT0_CPUC0_REG = 0x00000001U;
	portRTI_CNT0_COMP0_REG = ( configCPU_CLOCK_HZ / 2 ) / configTICK_RATE_HZ;
	portRTI_CNT0_UDCP0_REG = ( configCPU_CLOCK_HZ / 2 ) / configTICK_RATE_HZ;

	/* Clear interrupts. */
	portRTI_INTFLAG_REG =  0x0007000FU;
	portRTI_CLEARINTENA_REG	= 0x00070F0FU;

	/* Enable the compare 0 interrupt. */
	portRTI_SETINTENA_REG = 0x00000001U;
	portRTI_GCTRL_REG |= 0x00000001U;
}
/*-----------------------------------------------------------*/

/*
 * See header file for description.
 */
portBASE_TYPE xPortStartScheduler(void)
{
	/* Start the timer that generates the tick ISR. */
	prvSetupTimerInterrupt();

	/* Reset the critical section nesting count read to execute the first task. */
	ulCriticalNesting = 0;

	/* Start the first task.  This is done from portASM.asm as ARM mode must be
	used. */
	vPortStartFirstTask();

	/* Should not get here! */
	return pdFAIL;
}
/*-----------------------------------------------------------*/

/*
 * See header file for description.
 */
void vPortEndScheduler(void)
{
	/* It is unlikely that the port will require this function as there
	is nothing to return to. */
}
/*-----------------------------------------------------------*/

#if configUSE_PREEMPTION == 0

	/* The cooperative scheduler requires a normal IRQ service routine to
	 * simply increment the system tick. */
	__interrupt void vPortNonPreemptiveTick( void )
	{
		/* clear clock interrupt flag */
		RTI->INTFLAG = 0x00000001;

		/* Increment the tick count - this may make a delaying task ready
		to run - but a context switch is not performed. */
		vTaskIncrementTick();
	}

 #else

	/*
	 **************************************************************************
	 * The preemptive scheduler ISR is written in assembler and can be found
	 * in the portASM.asm file. This will only get used if portUSE_PREEMPTION
	 * is set to 1 in portmacro.h
	 **************************************************************************
	 */
	void vPortPreemptiveTick( void );

#endif
/*-----------------------------------------------------------*/


/*
 * Disable interrupts, and keep a count of the nesting depth.
 */
void vPortEnterCritical( void )
{
	/* Disable interrupts as per portDISABLE_INTERRUPTS(); */
	portDISABLE_INTERRUPTS();

	/* Now interrupts are disabled ulCriticalNesting can be accessed
	directly.  Increment ulCriticalNesting to keep a count of how many times
	portENTER_CRITICAL() has been called. */
	ulCriticalNesting++;
}
/*-----------------------------------------------------------*/

/*
 * Decrement the critical nesting count, and if it has reached zero, re-enable
 * interrupts.
 */
void vPortExitCritical( void )
{
	if( ulCriticalNesting > 0 )
	{
		/* Decrement the nesting count as we are leaving a critical section. */
		ulCriticalNesting--;

		/* If the nesting level has reached zero then interrupts should be
		re-enabled. */
		if( ulCriticalNesting == 0 )
		{
			/* Enable interrupts as per portENABLE_INTERRUPTS(). */
			portENABLE_INTERRUPTS();
		}
	}
}
/*-----------------------------------------------------------*/

#if __TI_VFP_SUPPORT__

	void vPortTaskUsesFPU( void )
	{
	extern void vPortInitialiseFPSCR( void );

		/* A task is registering the fact that it needs an FPU context.  Set the
		FPU flag (saved as part of the task context. */
		ulTaskHasFPUContext = pdTRUE;

		/* Initialise the floating point status register. */
		vPortInitialiseFPSCR();
	}

#endif /* __TI_VFP_SUPPORT__ */

/*-----------------------------------------------------------*/

