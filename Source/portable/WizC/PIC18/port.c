/*
    FreeRTOS V7.1.1 - Copyright (C) 2012 Real Time Engineers Ltd.
	

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
    
    ***************************************************************************
     *                                                                       *
     *    Having a problem?  Start by reading the FAQ "My application does   *
     *    not run, what could be wrong?                                      *
     *                                                                       *
     *    http://www.FreeRTOS.org/FAQHelp.html                               *
     *                                                                       *
    ***************************************************************************

    
    http://www.FreeRTOS.org - Documentation, training, latest information, 
    license and contact details.
    
    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool.

    Real Time Engineers ltd license FreeRTOS to High Integrity Systems, who sell 
    the code with commercial support, indemnification, and middleware, under 
    the OpenRTOS brand: http://www.OpenRTOS.com.  High Integrity Systems also
    provide a safety engineered and independently SIL3 certified version under 
    the SafeRTOS brand: http://www.SafeRTOS.com.
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
typedef void tskTCB;
extern volatile tskTCB * volatile pxCurrentTCB;

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

unsigned short usCalcMinStackSize		= 0;

/*-----------------------------------------------------------*/

/*
 * We initialise ucCriticalNesting to the middle value an 
 * unsigned char can contain. This way portENTER_CRITICAL()
 * and portEXIT_CRITICAL() can be called without interrupts
 * being enabled before the scheduler starts.
 */
register unsigned char ucCriticalNesting = 0x7F;

/*-----------------------------------------------------------*/

/* 
 * Initialise the stack of a new task.
 * See portSAVE_CONTEXT macro for description. 
 */
portSTACK_TYPE *pxPortInitialiseStack( portSTACK_TYPE *pxTopOfStack, pdTASK_CODE pxCode, void *pvParameters )
{
unsigned char ucScratch;
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
	*pxTopOfStack-- = ( portSTACK_TYPE ) ( (( unsigned short ) pvParameters >> 8) & 0x00ff );
	*pxTopOfStack-- = ( portSTACK_TYPE ) (  ( unsigned short ) pvParameters       & 0x00ff );

	/*
	 * Next are all the registers that form part of the task context.
	 */
	*pxTopOfStack-- = ( portSTACK_TYPE ) 0x11; /* STATUS. */
	*pxTopOfStack-- = ( portSTACK_TYPE ) 0x22; /* WREG. */
	*pxTopOfStack-- = ( portSTACK_TYPE ) 0x33; /* BSR. */
	*pxTopOfStack-- = ( portSTACK_TYPE ) 0x44; /* PRODH. */
	*pxTopOfStack-- = ( portSTACK_TYPE ) 0x55; /* PRODL. */
	*pxTopOfStack-- = ( portSTACK_TYPE ) 0x66; /* FSR0H. */
	*pxTopOfStack-- = ( portSTACK_TYPE ) 0x77; /* FSR0L. */
	*pxTopOfStack-- = ( portSTACK_TYPE ) 0x88; /* FSR1H. */
	*pxTopOfStack-- = ( portSTACK_TYPE ) 0x99; /* FSR1L. */
	*pxTopOfStack-- = ( portSTACK_TYPE ) 0xAA; /* TABLAT. */
#if _ROMSIZE > 0x8000
	*pxTopOfStack-- = ( portSTACK_TYPE ) 0x00; /* TBLPTRU. */
#endif
	*pxTopOfStack-- = ( portSTACK_TYPE ) 0xCC; /* TBLPTRH. */
	*pxTopOfStack-- = ( portSTACK_TYPE ) 0xDD; /* TBLPTRL. */
#if _ROMSIZE > 0x8000
	*pxTopOfStack-- = ( portSTACK_TYPE ) 0xEE; /* PCLATU. */
#endif
	*pxTopOfStack-- = ( portSTACK_TYPE ) 0xFF; /* PCLATH. */

	/*
	 * Next the compiler's scratchspace.
	 */
	while(ucScratch-- > 0)
	{
		*pxTopOfStack-- = ( portSTACK_TYPE ) 0;
	}
	
	/*
	 * The only function return address so far is the address of the task entry.
	 * The order is TOSU/TOSH/TOSL. For devices > 64kB, TOSU is put on the 
	 * stack, too. TOSU is always written as zero here because wizC does not allow
	 * functionpointers to point above 64kB in ROM.
	 */
#if _ROMSIZE > 0x8000
	*pxTopOfStack-- = ( portSTACK_TYPE ) 0;
#endif
	*pxTopOfStack-- = ( portSTACK_TYPE ) ( ( ( unsigned short ) pxCode >> 8 ) & 0x00ff );
	*pxTopOfStack-- = ( portSTACK_TYPE ) ( (   unsigned short ) pxCode        & 0x00ff );

	/*
	 * Store the number of return addresses on the hardware stack.
	 * So far only the address of the task entry point.
	 */
	*pxTopOfStack-- = ( portSTACK_TYPE ) 1;

	/*
	 * The code generated by wizC does not maintain separate
	 * stack and frame pointers. Therefore the portENTER_CRITICAL macro cannot 
	 * use the stack as per other ports.  Instead a variable is used to keep
	 * track of the critical section nesting.  This variable has to be stored
	 * as part of the task context and is initially set to zero.
	 */
	*pxTopOfStack-- = ( portSTACK_TYPE ) portNO_CRITICAL_SECTION_NESTING;	

	return pxTopOfStack;
}
/*-----------------------------------------------------------*/

unsigned short usPortCALCULATE_MINIMAL_STACK_SIZE( void )
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

portBASE_TYPE xPortStartScheduler( void )
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

void *pvPortMalloc( unsigned short usWantedSize )
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
