/*This file has been prepared for Doxygen automatic documentation generation.*/
/*! \file *********************************************************************
 *
 * \brief FreeRTOS port source for AVR32 UC3.
 *
 * - Compiler:           IAR EWAVR32
 * - Supported devices:  All AVR32 devices can be used.
 * - AppNote:
 *
 * \author               Atmel Corporation: http://www.atmel.com \n
 *                       Support and FAQ: http://support.atmel.no/
 *
 *****************************************************************************/

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


/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"

/* AVR32 UC3 includes. */
#include <avr32/io.h>
#include <intrinsics.h>
#include "gpio.h"

#if configDBG
	#include "usart.h"
#endif

#if( configTICK_USE_TC==1 )
	#include "tc.h"
#endif


/* Constants required to setup the task context. */
#define portINITIAL_SR            ( ( StackType_t ) 0x00400000 ) /* AVR32 : [M2:M0]=001 I1M=0 I0M=0, GM=0 */
#define portINSTRUCTION_SIZE      ( ( StackType_t ) 0 )

/* Each task maintains its own critical nesting variable. */
#define portNO_CRITICAL_NESTING   ( ( uint32_t ) 0 )
volatile uint32_t ulCriticalNesting = 9999UL;

#if( configTICK_USE_TC==0 )
	static void prvScheduleNextTick( void );
#else
	static void prvClearTcInt( void );
#endif

/* Setup the timer to generate the tick interrupts. */
static void prvSetupTimerInterrupt( void );

/*-----------------------------------------------------------*/

/*
 * Low-level initialization routine called during startup, before the main
 * function.
 */
int __low_level_init(void)
{
	#if configHEAP_INIT
		#pragma segment = "HEAP"
		BaseType_t *pxMem;
	#endif

	/* Enable exceptions. */
	ENABLE_ALL_EXCEPTIONS();

	/* Initialize interrupt handling. */
	INTC_init_interrupts();

	#if configHEAP_INIT
	{
		/* Initialize the heap used by malloc. */
		for( pxMem = __segment_begin( "HEAP" ); pxMem < ( BaseType_t * ) __segment_end( "HEAP" ); )
		{
			*pxMem++ = 0xA5A5A5A5;
		}
	}
	#endif

	/* Code section present if and only if the debug trace is activated. */
	#if configDBG
	{
		static const gpio_map_t DBG_USART_GPIO_MAP =
		{
			{ configDBG_USART_RX_PIN, configDBG_USART_RX_FUNCTION },
			{ configDBG_USART_TX_PIN, configDBG_USART_TX_FUNCTION }
		};

		static const usart_options_t DBG_USART_OPTIONS =
		{
			.baudrate = configDBG_USART_BAUDRATE,
			.charlength = 8,
			.paritytype = USART_NO_PARITY,
			.stopbits = USART_1_STOPBIT,
			.channelmode = USART_NORMAL_CHMODE
		};

		/* Initialize the USART used for the debug trace with the configured parameters. */
		extern volatile avr32_usart_t *volatile stdio_usart_base;
		stdio_usart_base = configDBG_USART;
		gpio_enable_module( DBG_USART_GPIO_MAP,
		                    sizeof( DBG_USART_GPIO_MAP ) / sizeof( DBG_USART_GPIO_MAP[0] ) );
		usart_init_rs232(configDBG_USART, &DBG_USART_OPTIONS, configCPU_CLOCK_HZ);
	}
	#endif

	/* Request initialization of data segments. */
	return 1;
}
/*-----------------------------------------------------------*/

/* Added as there is no such function in FreeRTOS. */
void *pvPortRealloc( void *pv, size_t xWantedSize )
{
void *pvReturn;

	vTaskSuspendAll();
	{
		pvReturn = realloc( pv, xWantedSize );
	}
	xTaskResumeAll();

	return pvReturn;
}
/*-----------------------------------------------------------*/

/* The cooperative scheduler requires a normal IRQ service routine to
simply increment the system tick. */
/* The preemptive scheduler is defined as "naked" as the full context is saved
on entry as part of the context switch. */
#pragma shadow_registers = full   // Naked.
static void vTick( void )
{
	/* Save the context of the interrupted task. */
	portSAVE_CONTEXT_OS_INT();

	#if( configTICK_USE_TC==1 )
		/* Clear the interrupt flag. */
		prvClearTcInt();
	#else
		/* Schedule the COUNT&COMPARE match interrupt in (configCPU_CLOCK_HZ/configTICK_RATE_HZ)
		clock cycles from now. */
		prvScheduleNextTick();
	#endif

	/* Because FreeRTOS is not supposed to run with nested interrupts, put all OS
	calls in a critical section . */
	portENTER_CRITICAL();
		xTaskIncrementTick();
	portEXIT_CRITICAL();

	/* Restore the context of the "elected task". */
	portRESTORE_CONTEXT_OS_INT();
}
/*-----------------------------------------------------------*/

#pragma shadow_registers = full   // Naked.
void SCALLYield( void )
{
	/* Save the context of the interrupted task. */
	portSAVE_CONTEXT_SCALL();
	vTaskSwitchContext();
	portRESTORE_CONTEXT_SCALL();
}
/*-----------------------------------------------------------*/

/* The code generated by the GCC compiler uses the stack in different ways at
different optimisation levels.  The interrupt flags can therefore not always
be saved to the stack.  Instead the critical section nesting level is stored
in a variable, which is then saved as part of the stack context. */
#pragma optimize = no_inline
void vPortEnterCritical( void )
{
	/* Disable interrupts */
	portDISABLE_INTERRUPTS();

	/* Now interrupts are disabled ulCriticalNesting can be accessed
	 directly.  Increment ulCriticalNesting to keep a count of how many times
	 portENTER_CRITICAL() has been called. */
	ulCriticalNesting++;
}
/*-----------------------------------------------------------*/

#pragma optimize = no_inline
void vPortExitCritical( void )
{
	if(ulCriticalNesting > portNO_CRITICAL_NESTING)
	{
		ulCriticalNesting--;
		if( ulCriticalNesting == portNO_CRITICAL_NESTING )
		{
			/* Enable all interrupt/exception. */
			portENABLE_INTERRUPTS();
		}
	}
}
/*-----------------------------------------------------------*/

/*
 * Initialise the stack of a task to look exactly as if a call to
 * portSAVE_CONTEXT had been called.
 *
 * See header file for description.
 */
StackType_t *pxPortInitialiseStack( StackType_t *pxTopOfStack, TaskFunction_t pxCode, void *pvParameters )
{
	/* Setup the initial stack of the task.  The stack is set exactly as
	expected by the portRESTORE_CONTEXT() macro. */

	/* When the task starts, it will expect to find the function parameter in R12. */
	pxTopOfStack--;
	*pxTopOfStack-- = ( StackType_t ) 0x08080808;					/* R8 */
	*pxTopOfStack-- = ( StackType_t ) 0x09090909;					/* R9 */
	*pxTopOfStack-- = ( StackType_t ) 0x0A0A0A0A;					/* R10 */
	*pxTopOfStack-- = ( StackType_t ) 0x0B0B0B0B;					/* R11 */
	*pxTopOfStack-- = ( StackType_t ) pvParameters;					/* R12 */
	*pxTopOfStack-- = ( StackType_t ) 0xDEADBEEF;					/* R14/LR */
	*pxTopOfStack-- = ( StackType_t ) pxCode + portINSTRUCTION_SIZE; /* R15/PC */
	*pxTopOfStack-- = ( StackType_t ) portINITIAL_SR;				/* SR */
	*pxTopOfStack-- = ( StackType_t ) 0xFF0000FF;					/* R0 */
	*pxTopOfStack-- = ( StackType_t ) 0x01010101;					/* R1 */
	*pxTopOfStack-- = ( StackType_t ) 0x02020202;					/* R2 */
	*pxTopOfStack-- = ( StackType_t ) 0x03030303;					/* R3 */
	*pxTopOfStack-- = ( StackType_t ) 0x04040404;					/* R4 */
	*pxTopOfStack-- = ( StackType_t ) 0x05050505;					/* R5 */
	*pxTopOfStack-- = ( StackType_t ) 0x06060606;					/* R6 */
	*pxTopOfStack-- = ( StackType_t ) 0x07070707;					/* R7 */
	*pxTopOfStack = ( StackType_t ) portNO_CRITICAL_NESTING;			/* ulCriticalNesting */

	return pxTopOfStack;
}
/*-----------------------------------------------------------*/

BaseType_t xPortStartScheduler( void )
{
	/* Start the timer that generates the tick ISR.  Interrupts are disabled
	here already. */
	prvSetupTimerInterrupt();

	/* Start the first task. */
	portRESTORE_CONTEXT();

	/* Should not get here! */
	return 0;
}
/*-----------------------------------------------------------*/

void vPortEndScheduler( void )
{
	/* It is unlikely that the AVR32 port will require this function as there
	is nothing to return to.  */
}
/*-----------------------------------------------------------*/

/* Schedule the COUNT&COMPARE match interrupt in (configCPU_CLOCK_HZ/configTICK_RATE_HZ)
clock cycles from now. */
#if( configTICK_USE_TC==0 )
	static void prvScheduleFirstTick(void)
	{
		uint32_t lCycles;

		lCycles = Get_system_register(AVR32_COUNT);
		lCycles += (configCPU_CLOCK_HZ/configTICK_RATE_HZ);
		// If lCycles ends up to be 0, make it 1 so that the COMPARE and exception
		// generation feature does not get disabled.
		if(0 == lCycles)
		{
			lCycles++;
		}
		Set_system_register(AVR32_COMPARE, lCycles);
	}
	
	#pragma optimize = no_inline
	static void prvScheduleNextTick(void)
	{
		uint32_t lCycles, lCount;

		lCycles = Get_system_register(AVR32_COMPARE);
		lCycles += (configCPU_CLOCK_HZ/configTICK_RATE_HZ);
		// If lCycles ends up to be 0, make it 1 so that the COMPARE and exception
		// generation feature does not get disabled.
		if(0 == lCycles)
		{
			lCycles++;
		}
		lCount = Get_system_register(AVR32_COUNT);
		if( lCycles < lCount )
		{		// We missed a tick, recover for the next.
			lCycles += (configCPU_CLOCK_HZ/configTICK_RATE_HZ);
		}
		Set_system_register(AVR32_COMPARE, lCycles);
	}
#else
	#pragma optimize = no_inline
	static void prvClearTcInt(void)
	{
		AVR32_TC.channel[configTICK_TC_CHANNEL].sr;
	}
#endif
/*-----------------------------------------------------------*/

/* Setup the timer to generate the tick interrupts. */
static void prvSetupTimerInterrupt(void)
{
	#if( configTICK_USE_TC==1 )

		volatile avr32_tc_t *tc = &AVR32_TC;

		// Options for waveform genration.
		tc_waveform_opt_t waveform_opt =
		{
		.channel  = configTICK_TC_CHANNEL,             /* Channel selection. */

		.bswtrg   = TC_EVT_EFFECT_NOOP,                /* Software trigger effect on TIOB. */
		.beevt    = TC_EVT_EFFECT_NOOP,                /* External event effect on TIOB. */
		.bcpc     = TC_EVT_EFFECT_NOOP,                /* RC compare effect on TIOB. */
		.bcpb     = TC_EVT_EFFECT_NOOP,                /* RB compare effect on TIOB. */

		.aswtrg   = TC_EVT_EFFECT_NOOP,                /* Software trigger effect on TIOA. */
		.aeevt    = TC_EVT_EFFECT_NOOP,                /* External event effect on TIOA. */
		.acpc     = TC_EVT_EFFECT_NOOP,                /* RC compare effect on TIOA: toggle. */
		.acpa     = TC_EVT_EFFECT_NOOP,                /* RA compare effect on TIOA: toggle (other possibilities are none, set and clear). */

		.wavsel   = TC_WAVEFORM_SEL_UP_MODE_RC_TRIGGER,/* Waveform selection: Up mode without automatic trigger on RC compare. */
		.enetrg   = FALSE,                             /* External event trigger enable. */
		.eevt     = 0,                                 /* External event selection. */
		.eevtedg  = TC_SEL_NO_EDGE,                    /* External event edge selection. */
		.cpcdis   = FALSE,                             /* Counter disable when RC compare. */
		.cpcstop  = FALSE,                             /* Counter clock stopped with RC compare. */

		.burst    = FALSE,                             /* Burst signal selection. */
		.clki     = FALSE,                             /* Clock inversion. */
		.tcclks   = TC_CLOCK_SOURCE_TC2                /* Internal source clock 2. */
		};

		tc_interrupt_t tc_interrupt =
		{
			.etrgs=0,
			.ldrbs=0,
			.ldras=0,
			.cpcs =1,
			.cpbs =0,
			.cpas =0,
			.lovrs=0,
			.covfs=0,
		};

	#endif

	/* Disable all interrupt/exception. */
	portDISABLE_INTERRUPTS();

	/* Register the compare interrupt handler to the interrupt controller and
	enable the compare interrupt. */

	#if( configTICK_USE_TC==1 )
	{
		INTC_register_interrupt((__int_handler)&vTick, configTICK_TC_IRQ, INT0);

		/* Initialize the timer/counter. */
		tc_init_waveform(tc, &waveform_opt);

		/* Set the compare triggers.
		Remember TC counter is 16-bits, so counting second is not possible!
		That's why we configure it to count ms. */
		tc_write_rc( tc, configTICK_TC_CHANNEL, ( configPBA_CLOCK_HZ / 4) / configTICK_RATE_HZ );

		tc_configure_interrupts( tc, configTICK_TC_CHANNEL, &tc_interrupt );

		/* Start the timer/counter. */
		tc_start(tc, configTICK_TC_CHANNEL);
	}
	#else
	{
		INTC_register_interrupt((__int_handler)&vTick, AVR32_CORE_COMPARE_IRQ, INT0);
		prvScheduleFirstTick();
	}
	#endif
}
