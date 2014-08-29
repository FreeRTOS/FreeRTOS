/*
    FreeRTOS V8.1.1 - Copyright (C) 2014 Real Time Engineers Ltd. 
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
Changes from V3.2.1
	+ CallReturn Depth increased from 8 to 10 levels to accomodate wizC/fedC V12.
	
Changes from V3.2.0
	+ TBLPTRU is now initialised to zero during the initial stack creation of a new task. This solves
	an error on devices with more than 64kB ROM.

Changes from V3.0.0
	+ ucCriticalNesting is now initialised to 0x7F to prevent interrupts from being
          handled before the scheduler is started.

Changes from V3.0.1
*/

/* Scheduler include files. */
#include <FreeRTOS.h>
#include <task.h>

#include <malloc.h>

/*---------------------------------------------------------------------------
 * Implementation of functions defined in portable.h for the WizC PIC18 port.
 *---------------------------------------------------------------------------*/

/*
 * We require the address of the pxCurrentTCB variable, but don't want to
 * know any details of its type.
 */
typedef void TCB_t;
extern volatile TCB_t * volatile pxCurrentTCB;

/*
 * Define minimal-stack constants
 * -----
 * FSR's:
 *		STATUS, WREG, BSR, PRODH, PRODL, FSR0H, FSR0L,
 *		FSR1H, FSR1L,TABLAT, (TBLPTRU), TBLPTRH, TBLPTRL,
 *		(PCLATU), PCLATH
 *		sfr's within parenthesis only on devices > 64kB
 * -----
 * Call/Return stack:
 *		 2 bytes per entry on devices <= 64kB
 *		 3 bytes per entry on devices >  64kB
 * -----
 * Other bytes:
 *		 2 bytes: FunctionParameter for initial taskcode
 *		 1 byte : Number of entries on call/return stack
 *		 1 byte : ucCriticalNesting
 *		16 bytes: Free space on stack
 */
#if _ROMSIZE > 0x8000
	#define portSTACK_FSR_BYTES				( 15 )
	#define portSTACK_CALLRETURN_ENTRY_SIZE	(  3 )
#else
	#define portSTACK_FSR_BYTES				( 13 )
	#define portSTACK_CALLRETURN_ENTRY_SIZE	(  2 )
#endif

#define portSTACK_MINIMAL_CALLRETURN_DEPTH	( 10 )
#define portSTACK_OTHER_BYTES				( 20 )

uint16_t usCalcMinStackSize		= 0;

/*-----------------------------------------------------------*/

/*
 * We initialise ucCriticalNesting to the middle value an 
 * uint8_t can contain. This way portENTER_CRITICAL()
 * and portEXIT_CRITICAL() can be called without interrupts
 * being enabled before the scheduler starts.
 */
register uint8_t ucCriticalNesting = 0x7F;

/*-----------------------------------------------------------*/

/* 
 * Initialise the stack of a new task.
 * See portSAVE_CONTEXT macro for description. 
 */
StackType_t *pxPortInitialiseStack( StackType_t *pxTopOfStack, TaskFunction_t pxCode, void *pvParameters )
{
uint8_t ucScratch;
	/*
	 * Get the size of the RAMarea in page 0 used by the compiler
	 * We do this here already to avoid W-register conflicts.
	 */
	_Pragma("asm")
		movlw	OVERHEADPAGE0-LOCOPTSIZE+MAXLOCOPTSIZE
		movwf	PRODL,ACCESS		; PRODL is used as temp register
	_Pragma("asmend")
	ucScratch = PRODL;

	/*
	 * Place a few bytes of known values on the bottom of the stack. 
	 * This is just useful for debugging.
	 */
//	*pxTopOfStack--	= 0x11;
//	*pxTopOfStack-- = 0x22;
//	*pxTopOfStack-- = 0x33;

	/*
	 * Simulate how the stack would look after a call to vPortYield()
	 * generated by the compiler.
	 */

	/*
	 * First store the function parameters.  This is where the task expects
	 * to find them when it starts running.
	 */
	*pxTopOfStack-- = ( StackType_t ) ( (( uint16_t ) pvParameters >> 8) & 0x00ff );
	*pxTopOfStack-- = ( StackType_t ) (  ( uint16_t ) pvParameters       & 0x00ff );

	/*
	 * Next are all the registers that form part of the task context.
	 */
	*pxTopOfStack-- = ( StackType_t ) 0x11; /* STATUS. */
	*pxTopOfStack-- = ( StackType_t ) 0x22; /* WREG. */
	*pxTopOfStack-- = ( StackType_t ) 0x33; /* BSR. */
	*pxTopOfStack-- = ( StackType_t ) 0x44; /* PRODH. */
	*pxTopOfStack-- = ( StackType_t ) 0x55; /* PRODL. */
	*pxTopOfStack-- = ( StackType_t ) 0x66; /* FSR0H. */
	*pxTopOfStack-- = ( StackType_t ) 0x77; /* FSR0L. */
	*pxTopOfStack-- = ( StackType_t ) 0x88; /* FSR1H. */
	*pxTopOfStack-- = ( StackType_t ) 0x99; /* FSR1L. */
	*pxTopOfStack-- = ( StackType_t ) 0xAA; /* TABLAT. */
#if _ROMSIZE > 0x8000
	*pxTopOfStack-- = ( StackType_t ) 0x00; /* TBLPTRU. */
#endif
	*pxTopOfStack-- = ( StackType_t ) 0xCC; /* TBLPTRH. */
	*pxTopOfStack-- = ( StackType_t ) 0xDD; /* TBLPTRL. */
#if _ROMSIZE > 0x8000
	*pxTopOfStack-- = ( StackType_t ) 0xEE; /* PCLATU. */
#endif
	*pxTopOfStack-- = ( StackType_t ) 0xFF; /* PCLATH. */

	/*
	 * Next the compiler's scratchspace.
	 */
	while(ucScratch-- > 0)
	{
		*pxTopOfStack-- = ( StackType_t ) 0;
	}
	
	/*
	 * The only function return address so far is the address of the task entry.
	 * The order is TOSU/TOSH/TOSL. For devices > 64kB, TOSU is put on the 
	 * stack, too. TOSU is always written as zero here because wizC does not allow
	 * functionpointers to point above 64kB in ROM.
	 */
#if _ROMSIZE > 0x8000
	*pxTopOfStack-- = ( StackType_t ) 0;
#endif
	*pxTopOfStack-- = ( StackType_t ) ( ( ( uint16_t ) pxCode >> 8 ) & 0x00ff );
	*pxTopOfStack-- = ( StackType_t ) ( (   uint16_t ) pxCode        & 0x00ff );

	/*
	 * Store the number of return addresses on the hardware stack.
	 * So far only the address of the task entry point.
	 */
	*pxTopOfStack-- = ( StackType_t ) 1;

	/*
	 * The code generated by wizC does not maintain separate
	 * stack and frame pointers. Therefore the portENTER_CRITICAL macro cannot 
	 * use the stack as per other ports.  Instead a variable is used to keep
	 * track of the critical section nesting.  This variable has to be stored
	 * as part of the task context and is initially set to zero.
	 */
	*pxTopOfStack-- = ( StackType_t ) portNO_CRITICAL_SECTION_NESTING;	

	return pxTopOfStack;
}
/*-----------------------------------------------------------*/

uint16_t usPortCALCULATE_MINIMAL_STACK_SIZE( void )
{
	/*
	 * Fetch the size of compiler's scratchspace.
	 */
	_Pragma("asm")
		movlw	OVERHEADPAGE0-LOCOPTSIZE+MAXLOCOPTSIZE
		movlb	usCalcMinStackSize>>8
		movwf	usCalcMinStackSize,BANKED
	_Pragma("asmend")

	/*
	 * Add minimum needed stackspace
	 */
	usCalcMinStackSize	+=	( portSTACK_FSR_BYTES )
		+	( portSTACK_MINIMAL_CALLRETURN_DEPTH * portSTACK_CALLRETURN_ENTRY_SIZE )
		+	( portSTACK_OTHER_BYTES );

	return(usCalcMinStackSize);
}

/*-----------------------------------------------------------*/

BaseType_t xPortStartScheduler( void )
{
	extern void portSetupTick( void );

	/*
	 * Setup a timer for the tick ISR for the preemptive scheduler.
	 */
	portSetupTick(); 

	/*
	 * Restore the context of the first task to run.
	 */
	portRESTORE_CONTEXT();

	/*
	 * This point should never be reached during execution.
	 */
	return pdTRUE;
}

/*-----------------------------------------------------------*/

void vPortEndScheduler( void )
{
	/*
	 * It is unlikely that the scheduler for the PIC port will get stopped
	 * once running. When called a reset is done which is probably the
	 * most valid action.
	 */
	_Pragma(asmline reset);
}

/*-----------------------------------------------------------*/

/*
 * Manual context switch.  This is similar to the tick context switch,
 * but does not increment the tick count.  It must be identical to the
 * tick context switch in how it stores the stack of a task.
 */
void vPortYield( void )
{
	/*
	 * Save the context of the current task.
	 */
	portSAVE_CONTEXT( portINTERRUPTS_UNCHANGED );

	/*
	 * Switch to the highest priority task that is ready to run.
	 */
	vTaskSwitchContext();

	/*
	 * Start executing the task we have just switched to.
	 */
	portRESTORE_CONTEXT();
}

/*-----------------------------------------------------------*/

void *pvPortMalloc( uint16_t usWantedSize )
{
void *pvReturn;

	vTaskSuspendAll();
	{
		pvReturn = malloc( ( malloc_t ) usWantedSize );
	}
	xTaskResumeAll();

	return pvReturn;
}

void vPortFree( void *pv )
{
	if( pv )
	{
		vTaskSuspendAll();
		{
			free( pv );
		}
		xTaskResumeAll();
	}
}
