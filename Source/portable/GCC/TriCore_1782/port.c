/*
    FreeRTOS V7.0.2 - Copyright (C) 2011 Real Time Engineers Ltd.


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
#include <string.h>
#include <tc1782.h>
#include <machine/intrinsics.h>
#include <machine/cint.h>
#include <machine/wdtcon.h>

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "list.h"
/*-----------------------------------------------------------*/

/* System register Definitions. */
#define portSYSTEM_PROGRAM_STATUS_WORD					( (unsigned portBASE_TYPE) 0x000008FF ) /* Supervisor Mode, MPU Register Set 0 and Call Depth Counting disabled. */
#define portINITIAL_PRIVILEGED_PROGRAM_STATUS_WORD		( (unsigned portBASE_TYPE) 0x000014FF ) /* IO Level 1, MPU Register Set 1 and Call Depth Counting disabled. */
#define portINITIAL_UNPRIVILEGED_PROGRAM_STATUS_WORD	( (unsigned portBASE_TYPE) 0x000010FF ) /* IO Level 0, MPU Register Set 1 and Call Depth Counting disabled. */
#define portINITIAL_PCXI_UPPER_CONTEXT_WORD				( (unsigned portBASE_TYPE) 0x00C00000 )	/* The lower 20 bits identify the CSA address. */
#define portINITIAL_PCXI_LOWER_CONTEXT_WORD				( (unsigned portBASE_TYPE) 0x00000000 )	/* The lower 20 bits identify the CSA address. */
#define portUPPER_CONTEXT_BIT							( (unsigned portBASE_TYPE) 0x00400000 )	/* Bit that indicates whether the context is upper or lower. */

#define portINITIAL_SYSCON								( (unsigned portBASE_TYPE) 0x00000000 )	/* MPU Disable. */

/* This macro should be used when the MPU is being used. */
#define portSELECT_PROGRAM_STATUS_WORD( xRunPrivileged )		( ( xRunPrivileged ) ? portINITIAL_PRIVILEGED_PROGRAM_STATUS_WORD : portINITIAL_UNPRIVILEGED_PROGRAM_STATUS_WORD )

/* CSA manipulation macros. */
#define portCSA_FCX_MASK					( 0x000FFFFFUL )

/* OS Interrupt and Trap mechanisms. */
#define portRESTORE_PSW_MASK				( ~( 0x000000FFUL ) )
#define portSYSCALL_TRAP					6
#define portCCPN_MASK						( 0x000000FFUL )

#define portSYSTEM_DATA_PRIVILEGES			( 0xC0C0C0C0UL )
#define portSYSTEM_CODE_PRIVILEGES			( 0x00008080UL )

#define portSYSTEM_PRIVILEGE_PROGRAM_STATUS_WORD	( (unsigned portBASE_TYPE) 0x00000800 ) /* Supervisor Mode. */
/*-----------------------------------------------------------*/

#if configCHECK_FOR_STACK_OVERFLOW > 0
	#error "pxTopOfStack is used to store the last used CSA so it is not appropriate to enable stack checking."
	/* The stack pointer is accessible using portCSA_TO_ADDRESS( portCSA_TO_ADDRESS( pxCurrentTCB->pxTopOfStack )[ 0 ] )[ 2 ]; */
#endif /* configCHECK_FOR_STACK_OVERFLOW */
/*-----------------------------------------------------------*/

/*
 * This reference is required by the Save/Restore Context Macros.
 */
extern volatile unsigned portBASE_TYPE * pxCurrentTCB;
/*-----------------------------------------------------------*/

/*
 * Perform any hardware configuration necessary to generate the tick interrupt.
 */
void vPortSystemTickHandler( int ) __attribute__((longcall));
static void prvSetupTimerInterrupt( void );
/*-----------------------------------------------------------*/

/*
 * The Yield Handler and Syscalls when using the MPU build.
 */
void vPortYield( int iTrapIdentification );
/*-----------------------------------------------------------*/

portSTACK_TYPE *pxPortInitialiseStack( portSTACK_TYPE * pxTopOfStack, pdTASK_CODE pxCode, void *pvParameters )
{
unsigned portBASE_TYPE *pxUpperCSA = NULL;
unsigned portBASE_TYPE *pxLowerCSA = NULL;

	/* 16 Address Registers (4 Address registers are global) and 16 Data Registers. */
	/* 3 System Registers */

	/* There are 3 registers that track the CSAs. */
	/* FCX points to the head of globally free set of CSAs.
	 * PCX for the task needs to point to Lower->Upper->NULL arrangement.
	 * LCX points to the last free CSA so that corrective action can be taken.
	 */

	/* Need two CSAs to store the context of a task.
	 * The upper context contains D8-D15, A10-A15, PSW and PCXI->NULL.
	 * The lower context contains D0-D7, A2-A7, A11 and PCXI->UpperContext.
	 * The pxCurrentTCB->pxTopOfStack points to the Lower Context RSLCX matching the initial BISR.
	 * The Lower Context points to the Upper Context ready for the ready return from the interrupt handler.
	 * The Real stack pointer for the task is stored in the A10 which is restored with the upper context.
	 */

	/* Have to disable interrupts here because we are manipulating the CSAs. */
	portENTER_CRITICAL();
	{
		/* DSync to ensure that buffering is not a problem. */
		_dsync();

		/* Consume two Free CSAs. */
		pxLowerCSA = portCSA_TO_ADDRESS( _mfcr( $FCX ) );
		if ( NULL != pxLowerCSA )
		{
			/* The Lower Links to the Upper. */
			pxUpperCSA = portCSA_TO_ADDRESS( pxLowerCSA[ 0 ] );
		}

		/* Check that we have successfully reserved two CSAs. */
		if ( ( NULL != pxLowerCSA ) && ( NULL != pxUpperCSA ) )
		{
			/* Remove the two consumed CSAs from the Free List. */
			_mtcr( $FCX, pxUpperCSA[ 0 ] );
			/* ISync to commit the change to the FCX. */
			_isync();
		}
		else
		{
			/* For the time being, simply trigger a context list depletion trap. */
			_svlcx();
		}
	}
	portEXIT_CRITICAL();

	/* Clear the CSA. */
	memset( pxUpperCSA, 0, 16 * sizeof( unsigned portBASE_TYPE ) );

	/* Upper Context. */
	pxUpperCSA[ 2 ] = (unsigned portBASE_TYPE)pxTopOfStack;				/* A10;	Stack Return aka Stack Pointer */
	pxUpperCSA[ 1 ] = portSYSTEM_PROGRAM_STATUS_WORD;					/* PSW	*/

	/* Clear the CSA. */
	memset( pxLowerCSA, 0, 16 * sizeof( unsigned portBASE_TYPE ) );

	/* Lower Context. */
	pxLowerCSA[ 8 ] = (unsigned portBASE_TYPE)pvParameters;			/* A4;	Address Type Parameter Register	*/
	pxLowerCSA[ 1 ] = (unsigned portBASE_TYPE)pxCode;				/* A11;	Return Address aka RA */
	/* PCXI pointing to the Upper context. */
	pxLowerCSA[ 0 ] = ( portINITIAL_PCXI_UPPER_CONTEXT_WORD | (unsigned portBASE_TYPE)portADDRESS_TO_CSA( pxUpperCSA ) );

	/* Save the link to the CSA in the Top of Stack. */
	pxTopOfStack = (unsigned portBASE_TYPE *)portADDRESS_TO_CSA( pxLowerCSA );

	/* DSync to ensure that buffering is not a problem. */
	_dsync();

	return pxTopOfStack;
}
/*-----------------------------------------------------------*/

portBASE_TYPE xPortStartScheduler( void )
{
unsigned portBASE_TYPE uxMFCR = 0UL;
unsigned portBASE_TYPE *pxUpperCSA = NULL;
unsigned portBASE_TYPE *pxLowerCSA = NULL;
	/* Set-up the timer interrupt. */
	prvSetupTimerInterrupt();

	/* Install the Trap Handlers. */
extern void vTrapInstallHandlers( void );
	vTrapInstallHandlers();

	/* Install the Syscall Handler. */
	if ( 0 == _install_trap_handler( portSYSCALL_TRAP, vPortYield ) )
	{
		/* Failed to install the Yield handler. */
		_debug();
	}

	/* Load the initial SYSCON. */
	_dsync();
	_mtcr( $SYSCON, portINITIAL_SYSCON );

	/* ENDINIT has already been applied in the 'cstart.c' code. */

	/* Set-up the Task switching ISR. */
	CPU_SRC0.reg = 0x00001001UL;

	/* Clear the PSW.CDC to enable RFE */
	uxMFCR = _mfcr( $PSW );
	uxMFCR &= portRESTORE_PSW_MASK;
	_mtcr( $PSW, uxMFCR );

	/* Finally, perform the equivalent of a portRESTORE_CONTEXT() */
	pxLowerCSA = portCSA_TO_ADDRESS( *(unsigned portBASE_TYPE *)pxCurrentTCB );
	pxUpperCSA = portCSA_TO_ADDRESS( pxLowerCSA[0] );
	_mtcr( $PCXI, *pxCurrentTCB );

	_dsync();
	_nop();
	_rslcx();
	_nop();
	__asm volatile( "rfe" );

	/* Will not get here. */
	return 0;
}
/*-----------------------------------------------------------*/

static void prvSetupTimerInterrupt( void )
{
	/* Set-up the clock divider. */
	unlock_wdtcon();
		while ( 0 != ( WDT_CON0.reg & 0x1UL ) );
		/* RMC == 1 so STM Clock == FPI */
		STM_CLC.reg = ( 1UL << 8 );
	lock_wdtcon();

    /* Set-up the Compare value. */
	STM_CMCON.reg = ( 31UL - __CLZ( configPERIPHERAL_CLOCK_HZ / configTICK_RATE_HZ ) );
	/* Take into account the current time so a tick doesn't happen immediately. */
	STM_CMP0.reg = ( configPERIPHERAL_CLOCK_HZ / configTICK_RATE_HZ ) + STM_TIM0.reg;

	if ( 0 != _install_int_handler( portKERNEL_INTERRUPT_PRIORITY_LEVEL, vPortSystemTickHandler, 0 ) )
	{
		/* Set-up the interrupt. */
		STM_SRC0.reg = ( portKERNEL_INTERRUPT_PRIORITY_LEVEL | 0x00005000UL );

		/* Enable the Interrupt. */
		STM_ISRR.reg = 0x1UL;
		STM_ICR.reg = 0x1UL;
	}
	else
	{
		/* Failed to install the Tick Interrupt. */
		_debug();
	}
}
/*-----------------------------------------------------------*/

void vPortSystemTickHandler( int iArg )
{
	/* Clear the interrupt source. */
	STM_ISRR.reg = 1UL;
	/* Reload the Compare Match register for X ticks into the future. */
	STM_CMP0.reg += ( configPERIPHERAL_CLOCK_HZ / configTICK_RATE_HZ );

	/* Kernel API calls require Critical Sections. */
	portINTERRUPT_ENTER_CRITICAL();
	{
		/* Increment the Tick. */
		vTaskIncrementTick();
	}
	portINTERRUPT_EXIT_CRITICAL();

#if configUSE_PREEMPTION == 1
	portYIELD_FROM_ISR( pdTRUE );
#endif

	(void)iArg;
}
/*-----------------------------------------------------------*/

/*
 * When a task is deleted, it is yielded permanently until the IDLE task
 * has an opportunity to reclaim the memory that that task was using.
 * Typically, the memory used by a task is the TCB and Stack but in the
 * TriCore this includes the CSAs that were consumed as part of the Call
 * Stack. These CSAs can only be returned to the Globally Free Pool when
 * they are not part of the current Call Stack, hence, delaying the
 * reclamation until the IDLE task is freeing the task's other resources.
 * This function uses the head of the linked list of CSAs (from when the
 * task yielded for the last time) and finds the tail (the very bottom of
 * the call stack) and inserts this list at the head of the Free list,
 * attaching the existing Free List to the tail of the reclaimed call stack.
 *
 * NOTE: the IDLE task needs processing time to complete this function
 * and in heavily loaded systems, the Free CSAs may be consumed faster
 * than they can be freed assuming that tasks are being spawned and
 * deleted frequently.
 */
void vPortReclaimCSA( unsigned portBASE_TYPE *pxTCB )
{
unsigned portBASE_TYPE pxHeadCSA, pxTailCSA, pxFreeCSA;
unsigned portBASE_TYPE *pulNextCSA;

	/* A pointer to the first CSA in the list of CSAs consumed by the task is
	stored in the first element of the tasks TCB structure (where the stack
	pointer would be on a traditional stack based architecture). */
	pxHeadCSA = ( *pxTCB ) & portCSA_FCX_MASK;

	/* Mask off everything in the CSA link field other than the address.  If
	the	address is NULL, then the CSA is not linking anywhere and there is
	nothing	to do. */
	pxTailCSA = pxHeadCSA;

	/* Convert the link value to contain just a raw address and store this
	in a local variable. */
	pulNextCSA = portCSA_TO_ADDRESS( pxTailCSA );

	/* Iterate over the CSAs that were consumed as part of the task.  The
	first field in the CSA is the pointer to then next CSA.  Mask off
	everything in the pointer to the next CSA, other than the link address.
	If this is NULL, then the CSA currently being pointed to is the last in
	the chain. */
	while( 0UL != ( pulNextCSA[ 0 ] & portCSA_FCX_MASK ) )
	{
		/* Clear all bits of the pointer to the next in the chain, other
		than the address bits themselves. */
		pulNextCSA[ 0 ] = pulNextCSA[ 0 ] & portCSA_FCX_MASK;

		/* Move the pointer to point to the next CSA in the list. */
		pxTailCSA = pulNextCSA[ 0 ];

		/* Update the local pointer to the CSA. */
		pulNextCSA = portCSA_TO_ADDRESS( pxTailCSA );
	}

	taskENTER_CRITICAL();
	{
		/* Look up the current free CSA head. */
		_dsync();
		pxFreeCSA = _mfcr( $FCX );

		/* Join the current Free onto the Tail of what is being reclaimed. */
		portCSA_TO_ADDRESS( pxTailCSA )[ 0 ] = pxFreeCSA;

		/* Move the head of the reclaimed into the Free. */
		_dsync();
		_mtcr( $FCX, pxHeadCSA );

		/* ISync to commit the change to the FCX. */
		_isync();
	}
	taskEXIT_CRITICAL();
}
/*-----------------------------------------------------------*/

void vPortEndScheduler( void )
{
	/* Nothing to do. Unlikely to want to end. */
}
/*-----------------------------------------------------------*/

void vPortYield( int iTrapIdentification )
{
	switch ( iTrapIdentification )
	{
	case portSYSCALL_TASK_YIELD:
		/* Select another task to run. */
		portYIELD_FROM_ISR( pdTRUE );
		break;

	default:
		_debug();
		break;
	}
}
/*-----------------------------------------------------------*/
