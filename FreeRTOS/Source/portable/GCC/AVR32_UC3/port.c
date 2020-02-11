/*This file has been prepared for Doxygen automatic documentation generation.*/
/*! \file *********************************************************************
 *
 * \brief FreeRTOS port source for AVR32 UC3.
 *
 * - Compiler:           GNU GCC for AVR32
 * - Supported devices:  All AVR32 devices can be used.
 * - AppNote:
 *
 * \author               Atmel Corporation: http://www.atmel.com \n
 *                       Support and FAQ: http://support.atmel.no/
 *
 *****************************************************************************/

/*
 * FreeRTOS Kernel
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * http://www.FreeRTOS.org
 * http://aws.amazon.com/freertos
 *
 * 1 tab == 4 spaces!
 */


/* Standard includes. */
#include <sys/cpu.h>
#include <sys/usart.h>
#include <malloc.h>

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"

/* AVR32 UC3 includes. */
#include <avr32/io.h>
#include "gpio.h"
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
 * This version comes in replacement to the default one provided by Newlib.
 * Newlib's _init_startup only calls init_exceptions, but Newlib's exception
 * vectors are not compatible with the SCALL management in the current FreeRTOS
 * port. More low-level initializations are besides added here.
 */
void _init_startup(void)
{
	/* Import the Exception Vector Base Address. */
	extern void _evba;

	#if configHEAP_INIT
		extern void __heap_start__;
		extern void __heap_end__;
		BaseType_t *pxMem;
	#endif

	/* Load the Exception Vector Base Address in the corresponding system register. */
	Set_system_register( AVR32_EVBA, ( int ) &_evba );

	/* Enable exceptions. */
	ENABLE_ALL_EXCEPTIONS();

	/* Initialize interrupt handling. */
	INTC_init_interrupts();

	#if configHEAP_INIT

		/* Initialize the heap used by malloc. */
		for( pxMem = &__heap_start__; pxMem < ( BaseType_t * )&__heap_end__; )
		{
			*pxMem++ = 0xA5A5A5A5;
		}

	#endif

	/* Give the used CPU clock frequency to Newlib, so it can work properly. */
	set_cpu_hz( configCPU_CLOCK_HZ );

	/* Code section present if and only if the debug trace is activated. */
	#if configDBG
	{
		static const gpio_map_t DBG_USART_GPIO_MAP =
		{
			{ configDBG_USART_RX_PIN, configDBG_USART_RX_FUNCTION },
			{ configDBG_USART_TX_PIN, configDBG_USART_TX_FUNCTION }
		};

		/* Initialize the USART used for the debug trace with the configured parameters. */
		set_usart_base( ( void * ) configDBG_USART );
		gpio_enable_module( DBG_USART_GPIO_MAP,
		                    sizeof( DBG_USART_GPIO_MAP ) / sizeof( DBG_USART_GPIO_MAP[0] ) );
		usart_init( configDBG_USART_BAUDRATE );
	}
	#endif
}
/*-----------------------------------------------------------*/

/*
 * malloc, realloc and free are meant to be called through respectively
 * pvPortMalloc, pvPortRealloc and vPortFree.
 * The latter functions call the former ones from within sections where tasks
 * are suspended, so the latter functions are task-safe. __malloc_lock and
 * __malloc_unlock use the same mechanism to also keep the former functions
 * task-safe as they may be called directly from Newlib's functions.
 * However, all these functions are interrupt-unsafe and SHALL THEREFORE NOT BE
 * CALLED FROM WITHIN AN INTERRUPT, because __malloc_lock and __malloc_unlock do
 * not call portENTER_CRITICAL and portEXIT_CRITICAL in order not to disable
 * interrupts during memory allocation management as this may be a very time-
 * consuming process.
 */

/*
 * Lock routine called by Newlib on malloc / realloc / free entry to guarantee a
 * safe section as memory allocation management uses global data.
 * See the aforementioned details.
 */
void __malloc_lock(struct _reent *ptr)
{
	vTaskSuspendAll();
}

/*
 * Unlock routine called by Newlib on malloc / realloc / free exit to guarantee
 * a safe section as memory allocation management uses global data.
 * See the aforementioned details.
 */
void __malloc_unlock(struct _reent *ptr)
{
	xTaskResumeAll();
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
__attribute__((__naked__)) static void vTick( void )
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

__attribute__((__naked__)) void SCALLYield( void )
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
__attribute__((__noinline__)) void vPortEnterCritical( void )
{
	/* Disable interrupts */
	portDISABLE_INTERRUPTS();

	/* Now interrupts are disabled ulCriticalNesting can be accessed
	 directly.  Increment ulCriticalNesting to keep a count of how many times
	 portENTER_CRITICAL() has been called. */
	ulCriticalNesting++;
}
/*-----------------------------------------------------------*/

__attribute__((__noinline__)) void vPortExitCritical( void )
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
	
	__attribute__((__noinline__)) static void prvScheduleNextTick(void)
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
	__attribute__((__noinline__)) static void prvClearTcInt(void)
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
		INTC_register_interrupt(&vTick, configTICK_TC_IRQ, INT0);

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
		INTC_register_interrupt(&vTick, AVR32_CORE_COMPARE_IRQ, INT0);
		prvScheduleFirstTick();
	}
	#endif
}
