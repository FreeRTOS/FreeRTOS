/*
    FreeRTOS V7.6.0 - Copyright (C) 2013 Real Time Engineers Ltd. 
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

    >>! NOTE: The modification to the GPL is included to allow you to distribute
    >>! a combined work that includes FreeRTOS without being obliged to provide
    >>! the source code for proprietary components outside of the FreeRTOS
    >>! kernel.

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

/*-----------------------------------------------------------
 * Implementation of functions defined in portable.h for the RX100 port.
 *----------------------------------------------------------*/

/* Standard C includes. */
#include "limits.h"

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

/* The peripheral clock is divided by this value before being supplying the
CMT. */
#if ( configUSE_TICKLESS_IDLE == 0 )
	/* If tickless idle is not used then the divisor can be fixed. */
	#define portCLOCK_DIVISOR	8UL
#elif ( configPERIPHERAL_CLOCK_HZ >= 12000000 )
	#define portCLOCK_DIVISOR	512UL
#elif ( configPERIPHERAL_CLOCK_HZ >= 6000000 )
	#define portCLOCK_DIVISOR	128UL
#elif ( configPERIPHERAL_CLOCK_HZ >= 1000000 )
	#define portCLOCK_DIVISOR	32UL
#else
	#define portCLOCK_DIVISOR	8UL
#endif


/* Keys required to lock and unlock access to certain system registers
respectively. */
#define portUNLOCK_KEY		0xA50B
#define portLOCK_KEY		0xA500

/*-----------------------------------------------------------*/

/* The following lines are to ensure vSoftwareInterruptEntry can be referenced,
 and therefore installed in the vector table, when the FreeRTOS code is built
as a library. */
extern portBASE_TYPE vSoftwareInterruptEntry;
const portBASE_TYPE * p_vSoftwareInterruptEntry = &vSoftwareInterruptEntry;

/*-----------------------------------------------------------*/

/*
 * Function to start the first task executing - written in asm code as direct
 * access to registers is required.
 */
static void prvStartFirstTask( void );

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

/*
 * Sets up the periodic ISR used for the RTOS tick using the CMT.
 * The application writer can define configSETUP_TICK_INTERRUPT() (in
 * FreeRTOSConfig.h) such that their own tick interrupt configuration is used
 * in place of prvSetupTimerInterrupt().
 */
static void prvSetupTimerInterrupt( void );
#ifndef configSETUP_TICK_INTERRUPT
	/* The user has not provided their own tick interrupt configuration so use
    the definition in this file (which uses the interval timer). */
	#define configSETUP_TICK_INTERRUPT() prvSetupTimerInterrupt()
#endif /* configSETUP_TICK_INTERRUPT */

/*
 * Called after the sleep mode registers have been configured, prvSleep()
 * executes the pre and post sleep macros, and actually calls the wait
 * instruction.
 */
#if configUSE_TICKLESS_IDLE == 1
	static void prvSleep( portTickType xExpectedIdleTime );
#endif /* configUSE_TICKLESS_IDLE */

/*-----------------------------------------------------------*/

/* These is accessed by the inline assembler functions. */
extern void *pxCurrentTCB;
extern void vTaskSwitchContext( void );

/*-----------------------------------------------------------*/

/* Calculate how many clock increments make up a single tick period. */
static const unsigned long ulMatchValueForOneTick = ( ( configPERIPHERAL_CLOCK_HZ / portCLOCK_DIVISOR ) / configTICK_RATE_HZ );

#if configUSE_TICKLESS_IDLE == 1

	/* Holds the maximum number of ticks that can be suppressed - which is
	basically how far into the future an interrupt can be generated. Set
	during initialisation.  This is the maximum possible value that the
	compare match register can hold divided by ulMatchValueForOneTick. */
	static const portTickType xMaximumPossibleSuppressedTicks = USHRT_MAX / ( ( configPERIPHERAL_CLOCK_HZ / portCLOCK_DIVISOR ) / configTICK_RATE_HZ );

	/* Flag set from the tick interrupt to allow the sleep processing to know if
	sleep mode was exited because of a tick interrupt, or an interrupt
	generated by something else. */
	static volatile uint32_t ulTickFlag = pdFALSE;

	/* The CMT counter is stopped temporarily each time it is re-programmed.
	The following constant offsets the CMT counter match value by the number of
	CMT	counts that would typically be missed while the counter was stopped to
	compensate for the lost time.  The large difference between the divided CMT
	clock and the CPU clock means it is likely ulStoppedTimerCompensation will
	equal zero - and be optimised away. */
	static const unsigned long ulStoppedTimerCompensation = 100UL / ( configCPU_CLOCK_HZ / ( configPERIPHERAL_CLOCK_HZ / portCLOCK_DIVISOR ) );

#endif

/*-----------------------------------------------------------*/

/*
 * See header file for description.
 */
portSTACK_TYPE *pxPortInitialiseStack( portSTACK_TYPE *pxTopOfStack, pdTASK_CODE pxCode, void *pvParameters )
{
	/* Offset to end up on 8 byte boundary. */
	pxTopOfStack--;

	/* R0 is not included as it is the stack pointer. */
	*pxTopOfStack = 0x00;
	pxTopOfStack--;
    *pxTopOfStack = 0x00;
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
		*pxTopOfStack = 0x12345678;	/* r15. */
		pxTopOfStack--;
		*pxTopOfStack = 0xaaaabbbb;
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
		/* Leave space for the registers that will get popped from the stack
		when the task first starts executing. */
		pxTopOfStack -= 15;
	}
	#endif

	*pxTopOfStack = ( portSTACK_TYPE ) pvParameters; /* R1 */
	pxTopOfStack--;
	*pxTopOfStack = 0x12345678; /* Accumulator. */
	pxTopOfStack--;
	*pxTopOfStack = 0x87654321; /* Accumulator. */

	return pxTopOfStack;
}
/*-----------------------------------------------------------*/

portBASE_TYPE xPortStartScheduler( void )
{
	/* Use pxCurrentTCB just so it does not get optimised away. */
	if( pxCurrentTCB != NULL )
	{
		/* Call an application function to set up the timer that will generate
		the tick interrupt.  This way the application can decide which
		peripheral to use.  If tickless mode is used then the default
		implementation defined in this file (which uses CMT0) should not be
		overridden. */
		configSETUP_TICK_INTERRUPT();

		/* Enable the software interrupt. */
		_IEN( _ICU_SWINT ) = 1;

		/* Ensure the software interrupt is clear. */
		_IR( _ICU_SWINT ) = 0;

		/* Ensure the software interrupt is set to the kernel priority. */
		_IPR( _ICU_SWINT ) = configKERNEL_INTERRUPT_PRIORITY;

		/* Start the first task. */
		prvStartFirstTask();
	}

	/* Execution should not reach here as the tasks are now running!
	prvSetupTimerInterrupt() is called here to prevent the compiler outputting
	a warning about a statically declared function not being referenced in the
	case that the application writer has provided their own tick interrupt
	configuration routine (and defined configSETUP_TICK_INTERRUPT() such that
	their own routine will be called in place of prvSetupTimerInterrupt()). */
	prvSetupTimerInterrupt();

	/* Just to make sure the function is not optimised away. */
	( void ) vSoftwareInterruptISR();

	/* Should not get here. */
	return pdFAIL;
}
/*-----------------------------------------------------------*/

#pragma inline_asm prvStartFirstTask
static void prvStartFirstTask( void )
{
	/* When starting the scheduler there is nothing that needs moving to the
	interrupt stack because the function is not called from an interrupt.
	Just ensure the current stack is the user stack. */
	SETPSW	U

	/* Obtain the location of the stack associated with which ever task
	pxCurrentTCB is currently pointing to. */
	MOV.L	#_pxCurrentTCB, R15
	MOV.L	[R15], R15
	MOV.L	[R15], R0

	/* Restore the registers from the stack of the task pointed to by
	pxCurrentTCB. */
    POP		R15
    MVTACLO	R15 		/* Accumulator low 32 bits. */
    POP		R15
    MVTACHI	R15 		/* Accumulator high 32 bits. */
    POPM	R1-R15 		/* R1 to R15 - R0 is not included as it is the SP. */
    RTE					/* This pops the remaining registers. */
    NOP
    NOP
}
/*-----------------------------------------------------------*/

#pragma interrupt ( prvTickISR( vect = configTICK_VECTOR, enable ) )
void prvTickISR( void )
{
	/* Increment the tick, and perform any processing the new tick value
	necessitates. */
	set_ipl( configMAX_SYSCALL_INTERRUPT_PRIORITY );
	{
		if( xTaskIncrementTick() != pdFALSE )
		{
			taskYIELD();
		}
	}
	set_ipl( configKERNEL_INTERRUPT_PRIORITY );

	#if configUSE_TICKLESS_IDLE == 1
	{
		/* The CPU woke because of a tick. */
		ulTickFlag = pdTRUE;

		/* If this is the first tick since exiting tickless mode then the CMT
		compare match value needs resetting. */
		CMT0.CMCOR = ( unsigned short ) ulMatchValueForOneTick;
	}
	#endif
}
/*-----------------------------------------------------------*/

void vSoftwareInterruptISR( void )
{
	prvYieldHandler();
}
/*-----------------------------------------------------------*/

#pragma inline_asm prvYieldHandler
static void prvYieldHandler( void )
{
	/* Re-enable interrupts. */
	SETPSW	I

	/* Move the data that was automatically pushed onto the interrupt stack
	when the interrupt occurred from the interrupt stack to the user stack.

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

	/* Save the accumulator. */
	MVFACHI	R15
	PUSH.L	R15
	MVFACMI	R15	; Middle order word.
	SHLL	#16, R15 ; Shifted left as it is restored to the low order word.
	PUSH.L	R15

	/* Save the stack pointer to the TCB. */
	MOV.L	#_pxCurrentTCB, R15
	MOV.L	[ R15 ], R15
	MOV.L	R0, [ R15 ]

	/* Ensure the interrupt mask is set to the syscall priority while the
	kernel structures are being accessed. */
	MVTIPL	#configMAX_SYSCALL_INTERRUPT_PRIORITY

	/* Select the next task to run. */
	BSR.A	_vTaskSwitchContext

	/* Reset the interrupt mask as no more data structure access is
	required. */
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
	POPM	R1-R15
	RTE
	NOP
	NOP
}
/*-----------------------------------------------------------*/

void vPortEndScheduler( void )
{
	/* Not implemented as there is nothing to return to. */

	/* The following line is just to prevent the symbol getting optimised away. */
	( void ) vTaskSwitchContext();
}
/*-----------------------------------------------------------*/

static void prvSetupTimerInterrupt( void )
{
	/* Unlock. */
	SYSTEM.PRCR.WORD = portUNLOCK_KEY;

	/* Enable CMT0. */
	MSTP( CMT0 ) = 0;

	/* Lock again. */
	SYSTEM.PRCR.WORD = portLOCK_KEY;

	/* Interrupt on compare match. */
	CMT0.CMCR.BIT.CMIE = 1;

	/* Set the compare match value. */
	CMT0.CMCOR = ( unsigned short ) ulMatchValueForOneTick;

	/* Divide the PCLK. */
	#if portCLOCK_DIVISOR == 512
	{
		CMT0.CMCR.BIT.CKS = 3;
	}
	#elif portCLOCK_DIVISOR == 128
	{
		CMT0.CMCR.BIT.CKS = 2;
	}
	#elif portCLOCK_DIVISOR == 32
	{
		CMT0.CMCR.BIT.CKS = 1;
	}
	#elif portCLOCK_DIVISOR == 8
	{
		CMT0.CMCR.BIT.CKS = 0;
	}
	#else
	{
		#error Invalid portCLOCK_DIVISOR setting
	}
	#endif


	/* Enable the interrupt... */
	_IEN( _CMT0_CMI0 ) = 1;

	/* ...and set its priority to the application defined kernel priority. */
	_IPR( _CMT0_CMI0 ) = configKERNEL_INTERRUPT_PRIORITY;

	/* Start the timer. */
	CMT.CMSTR0.BIT.STR0 = 1;
}
/*-----------------------------------------------------------*/

#if configUSE_TICKLESS_IDLE == 1

	static void prvSleep( portTickType xExpectedIdleTime )
	{
		/* Allow the application to define some pre-sleep processing. */
		configPRE_SLEEP_PROCESSING( xExpectedIdleTime );

		/* xExpectedIdleTime being set to 0 by configPRE_SLEEP_PROCESSING()
		means the application defined code has already executed the WAIT
		instruction. */
		if( xExpectedIdleTime > 0 )
		{
			wait();
		}

		/* Allow the application to define some post sleep processing. */
		configPOST_SLEEP_PROCESSING( xExpectedIdleTime );
	}

#endif /* configUSE_TICKLESS_IDLE */
/*-----------------------------------------------------------*/

#if configUSE_TICKLESS_IDLE == 1

	void vPortSuppressTicksAndSleep( portTickType xExpectedIdleTime )
	{
	unsigned long ulMatchValue, ulCompleteTickPeriods, ulCurrentCount;
	eSleepModeStatus eSleepAction;

		/* THIS FUNCTION IS CALLED WITH THE SCHEDULER SUSPENDED. */

		/* Make sure the CMT reload value does not overflow the counter. */
		if( xExpectedIdleTime > xMaximumPossibleSuppressedTicks )
		{
			xExpectedIdleTime = xMaximumPossibleSuppressedTicks;
		}

		/* Calculate the reload value required to wait xExpectedIdleTime tick
		periods. */
		ulMatchValue = ulMatchValueForOneTick * xExpectedIdleTime;
		if( ulMatchValue > ulStoppedTimerCompensation )
		{
			/* Compensate for the fact that the CMT is going to be stopped
			momentarily. */
			ulMatchValue -= ulStoppedTimerCompensation;
		}

		/* Stop the CMT momentarily.  The time the CMT is stopped for is
		accounted for as best it can be, but using the tickless mode will
		inevitably result in some tiny drift of the time maintained by the
		kernel with respect to calendar time. */
		CMT.CMSTR0.BIT.STR0 = 0;
		while( CMT.CMSTR0.BIT.STR0 == 1 )
		{
			/* Nothing to do here. */
		}

		/* Critical section using the global interrupt bit as the i bit is
		automatically reset by the WAIT instruction. */
		clrpsw_i();

		/* The tick flag is set to false before sleeping.  If it is true when
		sleep mode is exited then sleep mode was probably exited because the
		tick was suppressed for the entire xExpectedIdleTime period. */
		ulTickFlag = pdFALSE;

		/* If a context switch is pending then abandon the low power entry as
		the context switch might have been pended by an external interrupt that
		requires processing. */
		eSleepAction = eTaskConfirmSleepModeStatus();
		if( eSleepAction == eAbortSleep )
		{
			/* Restart tick. */
			CMT.CMSTR0.BIT.STR0 = 1;
			setpsw_i();
		}
		else if( eSleepAction == eNoTasksWaitingTimeout )
		{
		    /* Protection off. */
		    SYSTEM.PRCR.WORD = portUNLOCK_KEY;

		    /* Ready for software standby with all clocks stopped. */
			SYSTEM.SBYCR.BIT.SSBY = 1;

		    /* Protection on. */
		    SYSTEM.PRCR.WORD = portLOCK_KEY;

			/* Sleep until something happens.  Calling prvSleep() will
			automatically reset the i bit in the PSW. */
			prvSleep( xExpectedIdleTime );

			/* Restart the CMT. */
			CMT.CMSTR0.BIT.STR0 = 1;
		}
		else
		{
		    /* Protection off. */
		    SYSTEM.PRCR.WORD = portUNLOCK_KEY;

		    /* Ready for deep sleep mode. */
			SYSTEM.MSTPCRC.BIT.DSLPE = 1;
			SYSTEM.MSTPCRA.BIT.MSTPA28 = 1;
			SYSTEM.SBYCR.BIT.SSBY = 0;

		    /* Protection on. */
		    SYSTEM.PRCR.WORD = portLOCK_KEY;

		    /* Adjust the match value to take into account that the current
			time slice is already partially complete. */
			ulMatchValue -= ( unsigned long ) CMT0.CMCNT;
			CMT0.CMCOR = ( unsigned short ) ulMatchValue;

			/* Restart the CMT to count up to the new match value. */
			CMT0.CMCNT = 0;
			CMT.CMSTR0.BIT.STR0 = 1;

			/* Sleep until something happens.  Calling prvSleep() will
			automatically reset the i bit in the PSW. */
			prvSleep( xExpectedIdleTime );

			/* Stop CMT.  Again, the time the SysTick is stopped for is
			accounted for as best it can be, but using the tickless mode will
			inevitably result in some tiny drift of the time maintained by the
			kernel with	respect to calendar time. */
			CMT.CMSTR0.BIT.STR0 = 0;
			while( CMT.CMSTR0.BIT.STR0 == 1 )
			{
				/* Nothing to do here. */
			}

			ulCurrentCount = ( unsigned long ) CMT0.CMCNT;

			if( ulTickFlag != pdFALSE )
			{
				/* The tick interrupt has already executed, although because
				this function is called with the scheduler suspended the actual
				tick processing will not occur until after this function has
				exited.  Reset the match value with whatever remains of this
				tick period. */
				ulMatchValue = ulMatchValueForOneTick - ulCurrentCount;
				CMT0.CMCOR = ( unsigned short ) ulMatchValue;

				/* The tick interrupt handler will already have pended the tick
				processing in the kernel.  As the pending tick will be
				processed as soon as this function exits, the tick value
				maintained by the tick is stepped forward by one less than the
				time spent sleeping.  The actual stepping of the tick appears
				later in this function. */
				ulCompleteTickPeriods = xExpectedIdleTime - 1UL;
			}
			else
			{
				/* Something other than the tick interrupt ended the sleep.
				How	many complete tick periods passed while the processor was
				sleeping? */
				ulCompleteTickPeriods = ulCurrentCount / ulMatchValueForOneTick;

				/* The match value is set to whatever fraction of a single tick
				period remains. */
				ulMatchValue = ulCurrentCount - ( ulCompleteTickPeriods * ulMatchValueForOneTick );
				CMT0.CMCOR = ( unsigned short ) ulMatchValue;
			}

			/* Restart the CMT so it runs up to the match value.  The match value
			will get set to the value required to generate exactly one tick period
			the next time the CMT interrupt executes. */
			CMT0.CMCNT = 0;
			CMT.CMSTR0.BIT.STR0 = 1;

			/* Wind the tick forward by the number of tick periods that the CPU
			remained in a low power state. */
			vTaskStepTick( ulCompleteTickPeriods );
		}
	}

#endif /* configUSE_TICKLESS_IDLE */

