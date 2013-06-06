/*
    FreeRTOS V7.4.2 - Copyright (C) 2013 Real Time Engineers Ltd.

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
    and the FreeRTOS license exception along with FreeRTOS; if not it can be
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

/*-----------------------------------------------------------
 * Implementation of functions defined in portable.h for the MicroBlaze port.
 *----------------------------------------------------------*/


/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Standard includes. */
#include <string.h>

/* Hardware includes. */
#include <xintc_i.h>
#include <xil_exception.h>
#include <microblaze_exceptions_g.h>

/* Tasks are started with a critical section nesting of 0 - however, prior to 
the scheduler being commenced interrupts should not be enabled, so the critical 
nesting variable is initialised to a non-zero value. */
#define portINITIAL_NESTING_VALUE	( 0xff )

/* The bit within the MSR register that enabled/disables interrupts. */
#define portMSR_IE					( 0x02U )

/* If the floating point unit is included in the MicroBlaze build, then the
FSR register is saved as part of the task context.  portINITIAL_FSR is the value
given to the FSR register when the initial context is set up for a task being
created. */
#define portINITIAL_FSR				( 0U )
/*-----------------------------------------------------------*/

/*
 * Initialise the interrupt controller instance.
 */
static long prvInitialiseInterruptController( void );

/* Ensure the interrupt controller instance variable is initialised before it is 
 * used, and that the initialisation only happens once. 
 */
static long prvEnsureInterruptControllerIsInitialised( void );

/*-----------------------------------------------------------*/

/* Counts the nesting depth of calls to portENTER_CRITICAL().  Each task 
maintains its own count, so this variable is saved as part of the task
context. */
volatile unsigned portBASE_TYPE uxCriticalNesting = portINITIAL_NESTING_VALUE;

/* This port uses a separate stack for interrupts.  This prevents the stack of
every task needing to be large enough to hold an entire interrupt stack on top
of the task stack. */
unsigned long *pulISRStack;

/* If an interrupt requests a context switch, then ulTaskSwitchRequested will
get set to 1.  ulTaskSwitchRequested is inspected just before the main interrupt
handler exits.  If, at that time, ulTaskSwitchRequested is set to 1, the kernel
will call vTaskSwitchContext() to ensure the task that runs immediately after
the interrupt exists is the highest priority task that is able to run.  This is 
an unusual mechanism, but is used for this port because a single interrupt can 
cause the servicing of multiple peripherals - and it is inefficient to call
vTaskSwitchContext() multiple times as each peripheral is serviced. */
volatile unsigned long ulTaskSwitchRequested = 0UL;

/* The instance of the interrupt controller used by this port.  This is required
by the Xilinx library API functions. */
static XIntc xInterruptControllerInstance;

/*-----------------------------------------------------------*/

/* 
 * Initialise the stack of a task to look exactly as if a call to 
 * portSAVE_CONTEXT had been made.
 * 
 * See the portable.h header file.
 */
portSTACK_TYPE *pxPortInitialiseStack( portSTACK_TYPE *pxTopOfStack, pdTASK_CODE pxCode, void *pvParameters )
{
extern void *_SDA2_BASE_, *_SDA_BASE_;
const unsigned long ulR2 = ( unsigned long ) &_SDA2_BASE_;
const unsigned long ulR13 = ( unsigned long ) &_SDA_BASE_;

	/* Place a few bytes of known values on the bottom of the stack. 
	This is essential for the Microblaze port and these lines must
	not be omitted. */
	*pxTopOfStack = ( portSTACK_TYPE ) 0x00000000;
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0x00000000;
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0x00000000;
	pxTopOfStack--;

	#if XPAR_MICROBLAZE_0_USE_FPU == 1
		/* The FSR value placed in the initial task context is just 0. */
		*pxTopOfStack = portINITIAL_FSR;
		pxTopOfStack--;
	#endif

	/* The MSR value placed in the initial task context should have interrupts
	disabled.  Each task will enable interrupts automatically when it enters
	the running state for the first time. */
	*pxTopOfStack = mfmsr() & ~portMSR_IE;
	pxTopOfStack--;

	/* First stack an initial value for the critical section nesting.  This
	is initialised to zero. */
	*pxTopOfStack = ( portSTACK_TYPE ) 0x00;
	
	/* R0 is always zero. */
	/* R1 is the SP. */

	/* Place an initial value for all the general purpose registers. */
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) ulR2;	/* R2 - read only small data area. */
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0x03;	/* R3 - return values and temporaries. */
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0x04;	/* R4 - return values and temporaries. */
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) pvParameters;/* R5 contains the function call parameters. */

	#ifdef portPRE_LOAD_STACK_FOR_DEBUGGING
		pxTopOfStack--;
		*pxTopOfStack = ( portSTACK_TYPE ) 0x06;	/* R6 - other parameters and temporaries.  Used as the return address from vPortTaskEntryPoint. */
		pxTopOfStack--;
		*pxTopOfStack = ( portSTACK_TYPE ) 0x07;	/* R7 - other parameters and temporaries. */
		pxTopOfStack--;
		*pxTopOfStack = ( portSTACK_TYPE ) 0x08;	/* R8 - other parameters and temporaries. */
		pxTopOfStack--;
		*pxTopOfStack = ( portSTACK_TYPE ) 0x09;	/* R9 - other parameters and temporaries. */
		pxTopOfStack--;
		*pxTopOfStack = ( portSTACK_TYPE ) 0x0a;	/* R10 - other parameters and temporaries. */
		pxTopOfStack--;
		*pxTopOfStack = ( portSTACK_TYPE ) 0x0b;	/* R11 - temporaries. */
		pxTopOfStack--;
		*pxTopOfStack = ( portSTACK_TYPE ) 0x0c;	/* R12 - temporaries. */
		pxTopOfStack--;
	#else
		pxTopOfStack-= 8;
	#endif
	
	*pxTopOfStack = ( portSTACK_TYPE ) ulR13;	/* R13 - read/write small data area. */
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) pxCode;	/* R14 - return address for interrupt. */
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) NULL;	/* R15 - return address for subroutine. */
	
	#ifdef portPRE_LOAD_STACK_FOR_DEBUGGING
		pxTopOfStack--;
		*pxTopOfStack = ( portSTACK_TYPE ) 0x10;	/* R16 - return address for trap (debugger). */
		pxTopOfStack--;
		*pxTopOfStack = ( portSTACK_TYPE ) 0x11;	/* R17 - return address for exceptions, if configured. */
		pxTopOfStack--;
		*pxTopOfStack = ( portSTACK_TYPE ) 0x12;	/* R18 - reserved for assembler and compiler temporaries. */
		pxTopOfStack--;
	#else
		pxTopOfStack -= 4;
	#endif
	
	*pxTopOfStack = ( portSTACK_TYPE ) 0x00;	/* R19 - must be saved across function calls. Callee-save.  Seems to be interpreted as the frame pointer. */
	
	#ifdef portPRE_LOAD_STACK_FOR_DEBUGGING	
		pxTopOfStack--;
		*pxTopOfStack = ( portSTACK_TYPE ) 0x14;	/* R20 - reserved for storing a pointer to the Global Offset Table (GOT) in Position Independent Code (PIC). Non-volatile in non-PIC code. Must be saved across function calls. Callee-save.  Not used by FreeRTOS. */
		pxTopOfStack--;
		*pxTopOfStack = ( portSTACK_TYPE ) 0x15;	/* R21 - must be saved across function calls. Callee-save. */
		pxTopOfStack--;
		*pxTopOfStack = ( portSTACK_TYPE ) 0x16;	/* R22 - must be saved across function calls. Callee-save. */
		pxTopOfStack--;
		*pxTopOfStack = ( portSTACK_TYPE ) 0x17;	/* R23 - must be saved across function calls. Callee-save. */
		pxTopOfStack--;
		*pxTopOfStack = ( portSTACK_TYPE ) 0x18;	/* R24 - must be saved across function calls. Callee-save. */
		pxTopOfStack--;
		*pxTopOfStack = ( portSTACK_TYPE ) 0x19;	/* R25 - must be saved across function calls. Callee-save. */
		pxTopOfStack--;
		*pxTopOfStack = ( portSTACK_TYPE ) 0x1a;	/* R26 - must be saved across function calls. Callee-save. */
		pxTopOfStack--;
		*pxTopOfStack = ( portSTACK_TYPE ) 0x1b;	/* R27 - must be saved across function calls. Callee-save. */
		pxTopOfStack--;
		*pxTopOfStack = ( portSTACK_TYPE ) 0x1c;	/* R28 - must be saved across function calls. Callee-save. */
		pxTopOfStack--;
		*pxTopOfStack = ( portSTACK_TYPE ) 0x1d;	/* R29 - must be saved across function calls. Callee-save. */
		pxTopOfStack--;
		*pxTopOfStack = ( portSTACK_TYPE ) 0x1e;	/* R30 - must be saved across function calls. Callee-save. */
		pxTopOfStack--;
		*pxTopOfStack = ( portSTACK_TYPE ) 0x1f;	/* R31 - must be saved across function calls. Callee-save. */
		pxTopOfStack--;
	#else
		pxTopOfStack -= 13;
	#endif

	/* Return a pointer to the top of the stack that has been generated so this 
	can	be stored in the task control block for the task. */
	return pxTopOfStack;
}
/*-----------------------------------------------------------*/

portBASE_TYPE xPortStartScheduler( void )
{
extern void ( vPortStartFirstTask )( void );
extern unsigned long _stack[];

	/* Setup the hardware to generate the tick.  Interrupts are disabled when
	this function is called.  
	
	This port uses an application defined callback function to install the tick
	interrupt handler because the kernel will run on lots of different 
	MicroBlaze and FPGA configurations - not all of	which will have the same 
	timer peripherals defined or available.  An example definition of
	vApplicationSetupTimerInterrupt() is provided in the official demo
	application that accompanies this port. */
	vApplicationSetupTimerInterrupt();

	/* Reuse the stack from main() as the stack for the interrupts/exceptions. */
	pulISRStack = ( unsigned long * ) _stack;

	/* Ensure there is enough space for the functions called from the interrupt
	service routines to write back into the stack frame of the caller. */
	pulISRStack -= 2;

	/* Restore the context of the first task that is going to run.  From here
	on, the created tasks will be executing. */
	vPortStartFirstTask();

	/* Should not get here as the tasks are now running! */
	return pdFALSE;
}
/*-----------------------------------------------------------*/

void vPortEndScheduler( void )
{
	/* Not implemented. */
}
/*-----------------------------------------------------------*/

/*
 * Manual context switch called by portYIELD or taskYIELD.  
 */
void vPortYield( void )
{
extern void VPortYieldASM( void );

	/* Perform the context switch in a critical section to assure it is
	not interrupted by the tick ISR.  It is not a problem to do this as
	each task maintains its own interrupt status. */
	portENTER_CRITICAL();
	{
		/* Jump directly to the yield function to ensure there is no
		compiler generated prologue code. */
		asm volatile (	"bralid r14, VPortYieldASM		\n\t" \
						"or r0, r0, r0					\n\t" );
	}
	portEXIT_CRITICAL();
}
/*-----------------------------------------------------------*/

void vPortEnableInterrupt( unsigned char ucInterruptID )
{
long lReturn;

	/* An API function is provided to enable an interrupt in the interrupt
	controller because the interrupt controller instance variable is private
	to this file. */
	lReturn = prvEnsureInterruptControllerIsInitialised();
	if( lReturn == pdPASS )
	{
		XIntc_Enable( &xInterruptControllerInstance, ucInterruptID );
	}
	
	configASSERT( lReturn );
}
/*-----------------------------------------------------------*/

void vPortDisableInterrupt( unsigned char ucInterruptID )
{
long lReturn;

	/* An API function is provided to disable an interrupt in the interrupt
	controller because the interrupt controller instance variable is private
	to this file. */
	lReturn = prvEnsureInterruptControllerIsInitialised();
	
	if( lReturn == pdPASS )
	{
		XIntc_Disable( &xInterruptControllerInstance, ucInterruptID );
	}
	
	configASSERT( lReturn );
}
/*-----------------------------------------------------------*/

portBASE_TYPE xPortInstallInterruptHandler( unsigned char ucInterruptID, XInterruptHandler pxHandler, void *pvCallBackRef )
{
long lReturn;

	/* An API function is provided to install an interrupt handler because the 
	interrupt controller instance variable is private to this file. */

	lReturn = prvEnsureInterruptControllerIsInitialised();
	
	if( lReturn == pdPASS )
	{
		lReturn = XIntc_Connect( &xInterruptControllerInstance, ucInterruptID, pxHandler, pvCallBackRef );
	}

	if( lReturn == XST_SUCCESS )
	{
		lReturn = pdPASS;
	}
	
	configASSERT( lReturn == pdPASS );

	return lReturn;
}
/*-----------------------------------------------------------*/

static long prvEnsureInterruptControllerIsInitialised( void )
{
static long lInterruptControllerInitialised = pdFALSE;
long lReturn;

	/* Ensure the interrupt controller instance variable is initialised before
	it is used, and that the initialisation only happens once. */
	if( lInterruptControllerInitialised != pdTRUE )
	{
		lReturn = prvInitialiseInterruptController();
		
		if( lReturn == pdPASS )
		{
			lInterruptControllerInitialised = pdTRUE;
		}
	}
	else
	{
		lReturn = pdPASS;
	}

	return lReturn;
}
/*-----------------------------------------------------------*/

/* 
 * Handler for the timer interrupt.  This is the handler that the application
 * defined callback function vApplicationSetupTimerInterrupt() should install.
 */
void vPortTickISR( void *pvUnused )
{
extern void vApplicationClearTimerInterrupt( void );

	/* Ensure the unused parameter does not generate a compiler warning. */
	( void ) pvUnused;

	/* This port uses an application defined callback function to clear the tick
	interrupt because the kernel will run on lots of different MicroBlaze and 
	FPGA configurations - not all of which will have the same timer peripherals 
	defined or available.  An example definition of
	vApplicationClearTimerInterrupt() is provided in the official demo
	application that accompanies this port. */	
	vApplicationClearTimerInterrupt();

	/* Increment the RTOS tick - this might cause a task to unblock. */
	if( xTaskIncrementTick() != pdFALSE )
	{
		/* Force vTaskSwitchContext() to be called as the interrupt exits. */
		ulTaskSwitchRequested = 1;
	}
}
/*-----------------------------------------------------------*/

static long prvInitialiseInterruptController( void )
{
long lStatus;

	lStatus = XIntc_Initialize( &xInterruptControllerInstance, configINTERRUPT_CONTROLLER_TO_USE );

	if( lStatus == XST_SUCCESS )
	{
		/* Initialise the exception table. */
		Xil_ExceptionInit();

	    /* Service all pending interrupts each time the handler is entered. */
	    XIntc_SetIntrSvcOption( xInterruptControllerInstance.BaseAddress, XIN_SVC_ALL_ISRS_OPTION );

	    /* Install exception handlers if the MicroBlaze is configured to handle
	    exceptions, and the application defined constant
	    configINSTALL_EXCEPTION_HANDLERS is set to 1. */
		#if ( MICROBLAZE_EXCEPTIONS_ENABLED == 1 ) && ( configINSTALL_EXCEPTION_HANDLERS == 1 )
	    {
	    	vPortExceptionsInstallHandlers();
	    }
		#endif /* MICROBLAZE_EXCEPTIONS_ENABLED */

		/* Start the interrupt controller.  Interrupts are enabled when the
		scheduler starts. */
		lStatus = XIntc_Start( &xInterruptControllerInstance, XIN_REAL_MODE );

		if( lStatus == XST_SUCCESS )
		{
			lStatus = pdPASS;
		}
		else
		{
			lStatus = pdFAIL;
		}
	}

	configASSERT( lStatus == pdPASS );

	return lStatus;
}
/*-----------------------------------------------------------*/


