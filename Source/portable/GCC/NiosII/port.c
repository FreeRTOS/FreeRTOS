/*
    FreeRTOS V6.1.1 - Copyright (C) 2011 Real Time Engineers Ltd.

    ***************************************************************************
    *                                                                         *
    * If you are:                                                             *
    *                                                                         *
    *    + New to FreeRTOS,                                                   *
    *    + Wanting to learn FreeRTOS or multitasking in general quickly       *
    *    + Looking for basic training,                                        *
    *    + Wanting to improve your FreeRTOS skills and productivity           *
    *                                                                         *
    * then take a look at the FreeRTOS books - available as PDF or paperback  *
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
#define portINITIAL_ESTATUS     ( portSTACK_TYPE ) 0x01 

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

void prvReadGp( unsigned long *ulValue )
{ 
	asm( "stw gp, (r4) " );
};
/*-----------------------------------------------------------*/

/* 
 * See header file for description. 
 */
portSTACK_TYPE *pxPortInitialiseStack( portSTACK_TYPE *pxTopOfStack, pdTASK_CODE pxCode, void *pvParameters )
{    
portSTACK_TYPE *pxFramePointer = pxTopOfStack - 1;
portSTACK_TYPE xGlobalPointer;

    prvReadGp( &xGlobalPointer ); 

    /* End of stack marker. */
    *pxTopOfStack = 0xdeadbeef;
    pxTopOfStack--;
    
    *pxTopOfStack = ( portSTACK_TYPE ) pxFramePointer; 
    pxTopOfStack--;
    
    *pxTopOfStack = xGlobalPointer; 
    
    /* Space for R23 to R16. */
    pxTopOfStack -= 9;

    *pxTopOfStack = ( portSTACK_TYPE ) pxCode; 
    pxTopOfStack--;

    *pxTopOfStack = portINITIAL_ESTATUS; 

    /* Space for R15 to R5. */    
    pxTopOfStack -= 12;
    
    *pxTopOfStack = ( portSTACK_TYPE ) pvParameters; 

    /* Space for R3 to R1, muldiv and RA. */
    pxTopOfStack -= 5;
    
    return pxTopOfStack;
}
/*-----------------------------------------------------------*/

/* 
 * See header file for description. 
 */
portBASE_TYPE xPortStartScheduler( void )
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
	/* Increment the Kernel Tick. */
	vTaskIncrementTick();

	/* If using preemption, also force a context switch. */
	#if configUSE_PREEMPTION == 1
        vTaskSwitchContext();
	#endif

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

