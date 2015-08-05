/*
    FreeRTOS V8.2.2 - Copyright (C) 2015 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>!AND MODIFIED BY!<< the FreeRTOS exception.

    ***************************************************************************
    >>!   NOTE: The modification to the GPL is included to allow you to     !<<
    >>!   distribute a combined work that includes FreeRTOS without being   !<<
    >>!   obliged to provide the source code for proprietary components     !<<
    >>!   outside of the FreeRTOS kernel.                                   !<<
    ***************************************************************************

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available on the following
    link: http://www.freertos.org/a00114.html

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that is more than just the market leader, it     *
     *    is the industry's de facto standard.                               *
     *                                                                       *
     *    Help yourself get started quickly while simultaneously helping     *
     *    to support the FreeRTOS project by purchasing a FreeRTOS           *
     *    tutorial book, reference manual, or both:                          *
     *    http://www.FreeRTOS.org/Documentation                              *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org/FAQHelp.html - Having a problem?  Start by reading
    the FAQ page "My application does not run, what could be wrong?".  Have you
    defined configASSERT()?

    http://www.FreeRTOS.org/support - In return for receiving this top quality
    embedded software for free we request you assist our global community by
    participating in the support forum.

    http://www.FreeRTOS.org/training - Investing in training allows your team to
    be as productive as possible as early as possible.  Now you can receive
    FreeRTOS training directly from Richard Barry, CEO of Real Time Engineers
    Ltd, and the world's leading authority on the world's leading RTOS.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.FreeRTOS.org/labs - Where new FreeRTOS products go to incubate.
    Come and try FreeRTOS+TCP, our new open source TCP/IP stack for FreeRTOS.

    http://www.OpenRTOS.com - Real Time Engineers ltd. license FreeRTOS to High
    Integrity Systems ltd. to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and commercial middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
*/

/*-----------------------------------------------------------
 * Implementation of functions defined in portable.h for the NIOS2 port.
 *----------------------------------------------------------*/

/* Standard Includes. */
#include <string.h>
#include <errno.h>

/* Altera includes. */
#include "sys/alt_irq.h"
#include "altera_avalon_timer_regs.h"
#include "priv/alt_irq_table.h"

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Interrupts are enabled. */
#define portINITIAL_ESTATUS     ( StackType_t ) 0x01 

/*-----------------------------------------------------------*/

/* 
 * Setup the timer to generate the tick interrupts.
 */
static void prvSetupTimerInterrupt( void );

/*
 * Call back for the alarm function.
 */
void vPortSysTickHandler( void * context, alt_u32 id );

/*-----------------------------------------------------------*/

static void prvReadGp( uint32_t *ulValue )
{
	asm( "stw gp, (%0)" :: "r"(ulValue) );
}
/*-----------------------------------------------------------*/

/* 
 * See header file for description. 
 */
StackType_t *pxPortInitialiseStack( StackType_t *pxTopOfStack, TaskFunction_t pxCode, void *pvParameters )
{    
StackType_t *pxFramePointer = pxTopOfStack - 1;
StackType_t xGlobalPointer;

    prvReadGp( &xGlobalPointer ); 

    /* End of stack marker. */
    *pxTopOfStack = 0xdeadbeef;
    pxTopOfStack--;
    
    *pxTopOfStack = ( StackType_t ) pxFramePointer; 
    pxTopOfStack--;
    
    *pxTopOfStack = xGlobalPointer; 
    
    /* Space for R23 to R16. */
    pxTopOfStack -= 9;

    *pxTopOfStack = ( StackType_t ) pxCode; 
    pxTopOfStack--;

    *pxTopOfStack = portINITIAL_ESTATUS; 

    /* Space for R15 to R5. */    
    pxTopOfStack -= 12;
    
    *pxTopOfStack = ( StackType_t ) pvParameters; 

    /* Space for R3 to R1, muldiv and RA. */
    pxTopOfStack -= 5;
    
    return pxTopOfStack;
}
/*-----------------------------------------------------------*/

/* 
 * See header file for description. 
 */
BaseType_t xPortStartScheduler( void )
{
	/* Start the timer that generates the tick ISR.  Interrupts are disabled
	here already. */
	prvSetupTimerInterrupt();
	
	/* Start the first task. */
    asm volatile (  " movia r2, restore_sp_from_pxCurrentTCB        \n"
                    " jmp r2                                          " );

	/* Should not get here! */
	return 0;
}
/*-----------------------------------------------------------*/

void vPortEndScheduler( void )
{
	/* It is unlikely that the NIOS2 port will require this function as there
	is nothing to return to.  */
}
/*-----------------------------------------------------------*/

/*
 * Setup the systick timer to generate the tick interrupts at the required
 * frequency.
 */
void prvSetupTimerInterrupt( void )
{
	/* Try to register the interrupt handler. */
	if ( -EINVAL == alt_irq_register( SYS_CLK_IRQ, 0x0, vPortSysTickHandler ) )
	{ 
		/* Failed to install the Interrupt Handler. */
		asm( "break" );
	}
	else
	{
		/* Configure SysTick to interrupt at the requested rate. */
		IOWR_ALTERA_AVALON_TIMER_CONTROL( SYS_CLK_BASE, ALTERA_AVALON_TIMER_CONTROL_STOP_MSK );
		IOWR_ALTERA_AVALON_TIMER_PERIODL( SYS_CLK_BASE, ( configCPU_CLOCK_HZ / configTICK_RATE_HZ ) & 0xFFFF );
		IOWR_ALTERA_AVALON_TIMER_PERIODH( SYS_CLK_BASE, ( configCPU_CLOCK_HZ / configTICK_RATE_HZ ) >> 16 );
		IOWR_ALTERA_AVALON_TIMER_CONTROL( SYS_CLK_BASE, ALTERA_AVALON_TIMER_CONTROL_CONT_MSK | ALTERA_AVALON_TIMER_CONTROL_START_MSK | ALTERA_AVALON_TIMER_CONTROL_ITO_MSK );	
	} 

	/* Clear any already pending interrupts generated by the Timer. */
	IOWR_ALTERA_AVALON_TIMER_STATUS( SYS_CLK_BASE, ~ALTERA_AVALON_TIMER_STATUS_TO_MSK );
}
/*-----------------------------------------------------------*/

void vPortSysTickHandler( void * context, alt_u32 id )
{
	/* Increment the kernel tick. */
	if( xTaskIncrementTick() != pdFALSE )
	{
        vTaskSwitchContext();
	}
		
	/* Clear the interrupt. */
	IOWR_ALTERA_AVALON_TIMER_STATUS( SYS_CLK_BASE, ~ALTERA_AVALON_TIMER_STATUS_TO_MSK );
}
/*-----------------------------------------------------------*/

/** This function is a re-implementation of the Altera provided function.
 * The function is re-implemented to prevent it from enabling an interrupt
 * when it is registered. Interrupts should only be enabled after the FreeRTOS.org
 * kernel has its scheduler started so that contexts are saved and switched 
 * correctly.
 */
int alt_irq_register( alt_u32 id, void* context, void (*handler)(void*, alt_u32) )
{
	int rc = -EINVAL;  
	alt_irq_context status;

	if (id < ALT_NIRQ)
	{
		/* 
		 * interrupts are disabled while the handler tables are updated to ensure
		 * that an interrupt doesn't occur while the tables are in an inconsistent
		 * state.
		 */
	
		status = alt_irq_disable_all ();
	
		alt_irq[id].handler = handler;
		alt_irq[id].context = context;
	
		rc = (handler) ? alt_irq_enable (id): alt_irq_disable (id);
	
		/* alt_irq_enable_all(status); This line is removed to prevent the interrupt from being immediately enabled. */
	}
    
	return rc; 
}
/*-----------------------------------------------------------*/

