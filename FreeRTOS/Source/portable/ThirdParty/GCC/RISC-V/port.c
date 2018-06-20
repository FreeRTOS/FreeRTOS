/*
    FreeRTOS V8.2.3 - Copyright (C) 2015 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    This file is part of the FreeRTOS distribution and was contributed
    to the project by Technolution B.V. (www.technolution.nl,
    freertos-riscv@technolution.eu) under the terms of the FreeRTOS
    contributors license.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>>> AND MODIFIED BY <<<< the FreeRTOS exception.

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
 * Implementation of functions defined in portable.h for the RISC-V port.
 *----------------------------------------------------------*/

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "portmacro.h"

#include "riscv_hal.h"

#ifdef __riscv64
# define STORE    sd
# define LOAD     ld
# define REGBYTES 8
#else
# define STORE    sw
# define LOAD     lw
# define REGBYTES 4
#endif
/* A variable is used to keep track of the critical section nesting.  This
variable has to be stored as part of the task context and must be initialized to
a non zero value to ensure interrupts don't inadvertently become unmasked before
the scheduler starts.  As it is stored as part of the task context it will
automatically be set to 0 when the first task is started. */
static UBaseType_t uxCriticalNesting = 0xaaaaaaaa;

/* Contains context when starting scheduler, save all 31 registers */
#ifdef __gracefulExit
BaseType_t xStartContext[31] = {0};
#endif


typedef struct
{
	uint32_t val_low;
	uint32_t val_high;
}riscv_machine_timer_t;

static volatile riscv_machine_timer_t *mtime = (riscv_machine_timer_t *)0x4400BFF8;

static volatile riscv_machine_timer_t *mtimecmp = (riscv_machine_timer_t *)0x44004000;

/*
 * Setup the timer to generate the tick interrupts.
 */
void vPortSetupTimer( void );

/*
 * Set the next interval for the timer
 */
static void prvSetNextTimerInterrupt( void );

/*
 * Used to catch tasks that attempt to return from their implementing function.
 */
static void prvTaskExitError( void );

void vPortEnterCritical( void )
{
	portDISABLE_INTERRUPTS();
	uxCriticalNesting++;
}
/*-----------------------------------------------------------*/

void vPortExitCritical( void )
{
	uxCriticalNesting--;
	if( uxCriticalNesting == 0 )
	{
		portENABLE_INTERRUPTS();
	}
}
/*-----------------------------------------------------------*/

/* Sets the next timer interrupt
 * Reads previous timer compare register, and adds tickrate */
static void prvSetNextTimerInterrupt(void)
{
	uint64_t time;

	time = mtime->val_low;
	time |= ((uint64_t)mtime->val_high << 32);

	time += (configCPU_CLOCK_HZ / configTICK_RATE_HZ);

	mtimecmp->val_low = (uint32_t)(time & 0xFFFFFFFF);
	mtimecmp->val_high = (uint32_t)((time >> 32) & 0xFFFFFFFF);

	/* Enable timer interrupt */
	__asm volatile("csrs mie,%0"::"r"(0x80));
}
/*-----------------------------------------------------------*/

/* Sets and enable the timer interrupt */
void vPortSetupTimer(void)
{
	uint64_t time;

	time = mtime->val_low;
	time |= ((uint64_t)mtime->val_high << 32);

	time += (configCPU_CLOCK_HZ / configTICK_RATE_HZ);

	mtimecmp->val_low = (uint32_t)(time & 0xFFFFFFFF);
	mtimecmp->val_high = (uint32_t)((time >> 32) & 0xFFFFFFFF);


	/* Enable timer interrupt */
	__asm volatile("csrs mie,%0"::"r"(0x80));
}
/*-----------------------------------------------------------*/

void prvTaskExitError( void )
{
	/* A function that implements a task must not exit or attempt to return to
	its caller as there is nothing to return to.  If a task wants to exit it
	should instead call vTaskDelete( NULL ).

	Artificially force an assert() to be triggered if configASSERT() is
	defined, then stop here so application writers can catch the error. */
	configASSERT( uxCriticalNesting == ~0UL );
	portDISABLE_INTERRUPTS();
	for( ;; );
}
/*-----------------------------------------------------------*/

/* Clear current interrupt mask and set given mask */
void vPortClearInterruptMask(int mask)
{
	__asm volatile("csrw mie, %0"::"r"(mask));
}
/*-----------------------------------------------------------*/

/* Set interrupt mask and return current interrupt enable register */
int vPortSetInterruptMask(void)
{
	int ret;
	__asm volatile("csrr %0,mie":"=r"(ret));
	__asm volatile("csrc mie,%0"::"i"(7));
	return ret;
}

/*
 * See header file for description.
 */
StackType_t *pxPortInitialiseStack( StackType_t *pxTopOfStack, TaskFunction_t pxCode, void *pvParameters )
{
	/* Simulate the stack frame as it would be created by a context switch
	interrupt. */
	register int *tp asm("x3");
	pxTopOfStack--;
	*pxTopOfStack = (portSTACK_TYPE)pxCode;			/* Start address */
	pxTopOfStack -= 22;
	*pxTopOfStack = (portSTACK_TYPE)pvParameters;	/* Register a0 */
	pxTopOfStack -= 6;
	*pxTopOfStack = (portSTACK_TYPE)tp; /* Register thread pointer */
	pxTopOfStack -= 3;
	*pxTopOfStack = (portSTACK_TYPE)prvTaskExitError; /* Register ra */
	
	return pxTopOfStack;
}
/*-----------------------------------------------------------*/

void vPortSysTickHandler( void )
{
	/*Save Context*/
	{
		__asm volatile("lw	t0, pxCurrentTCB");
		__asm volatile("sw	a2, 0x0(t0)");
	}

	/* Increment the RTOS tick. */
	prvSetNextTimerInterrupt();

	/*Switch task */
	if( xTaskIncrementTick() != pdFALSE )
	{
		vTaskSwitchContext();
	}

	/*Restore Context*/
	{
		__asm volatile("lw	sp, pxCurrentTCB");
		__asm volatile("lw	sp, 0x0(sp)");

		__asm volatile("lw	t0, 31 * 4(sp)");
		__asm volatile("csrw	mepc, t0");

		__asm volatile("lw	x1, 0x0(sp)");
		__asm volatile("lw   x4, 3 * 4(sp)");
		__asm volatile("lw   x5, 4 * 4(sp)");
		__asm volatile("lw   x6, 5 * 4(sp)");
		__asm volatile("lw   x7, 6 * 4(sp)");
		__asm volatile("lw   x8, 7 * 4(sp)");
		__asm volatile("lw   x9, 8 * 4(sp)");
		__asm volatile("lw   x10, 9 * 4(sp)");
		__asm volatile("lw   x11, 10 * 4(sp)");
		__asm volatile("lw   x12, 11 * 4(sp)");
		__asm volatile("lw   x13, 12 * 4(sp)");
		__asm volatile("lw   x14, 13 * 4(sp)");
		__asm volatile("lw   x15, 14 * 4(sp)");
		__asm volatile("lw   x16, 15 * 4(sp)");
		__asm volatile("lw   x17, 16 * 4(sp)");
		__asm volatile("lw   x18, 17 * 4(sp)");
		__asm volatile("lw   x19, 18 * 4(sp)");
		__asm volatile("lw   x20, 19 * 4(sp)");
		__asm volatile("lw   x21, 20 * 4(sp)");
		__asm volatile("lw   x22, 21 * 4(sp)");
		__asm volatile("lw   x23, 22 * 4(sp)");
		__asm volatile("lw   x24, 23 * 4(sp)");
		__asm volatile("lw   x25, 24 * 4(sp)");
		__asm volatile("lw   x26, 25 * 4(sp)");
		__asm volatile("lw   x27, 26 * 4(sp)");
		__asm volatile("lw   x28, 27 * 4(sp)");
		__asm volatile("lw   x29, 28 * 4(sp)");
		__asm volatile("lw   x30, 29 * 4(sp)");
		__asm volatile("lw   x31, 30 * 4(sp)");

		__asm volatile("addi	sp, sp, 4 * 32");

		__asm volatile("mret");
	}
}
uint32_t g_startscheduler = 0;
BaseType_t xPortStartScheduler( void )
{
	vPortSetupTimer();
	uxCriticalNesting = 0;
	g_startscheduler = 1;
	__enable_irq();

	raise_soft_interrupt();

	/*Should not get here*/
	return pdFALSE;
}

void Software_IRQHandler(void)
{
	if(1 == g_startscheduler)
	{
		g_startscheduler = 2; //skip the save n switch context first time when scheduler is starting.
	}
	else
	{
		/*Save Context*/
		{
			__asm volatile("lw	t0, pxCurrentTCB");
			__asm volatile("sw	a2, 0x0(t0)");
		}

		vTaskSwitchContext();
	}

	/*Restore Context*/
	{
		__asm volatile("lw	sp, pxCurrentTCB");
		__asm volatile("lw	sp, 0x0(sp)");

		__asm volatile("lw	t0, 31 * 4(sp)");
		__asm volatile("csrw	mepc, t0");

		__asm volatile("lw	x1, 0x0(sp)");
		__asm volatile("lw   x4, 3 * 4(sp)");
		__asm volatile("lw   x5, 4 * 4(sp)");
		__asm volatile("lw   x6, 5 * 4(sp)");
		__asm volatile("lw   x7, 6 * 4(sp)");
		__asm volatile("lw   x8, 7 * 4(sp)");
		__asm volatile("lw   x9, 8 * 4(sp)");
		__asm volatile("lw   x10, 9 * 4(sp)");
		__asm volatile("lw   x11, 10 * 4(sp)");
		__asm volatile("lw   x12, 11 * 4(sp)");
		__asm volatile("lw   x13, 12 * 4(sp)");
		__asm volatile("lw   x14, 13 * 4(sp)");
		__asm volatile("lw   x15, 14 * 4(sp)");
		__asm volatile("lw   x16, 15 * 4(sp)");
		__asm volatile("lw   x17, 16 * 4(sp)");
		__asm volatile("lw   x18, 17 * 4(sp)");
		__asm volatile("lw   x19, 18 * 4(sp)");
		__asm volatile("lw   x20, 19 * 4(sp)");
		__asm volatile("lw   x21, 20 * 4(sp)");
		__asm volatile("lw   x22, 21 * 4(sp)");
		__asm volatile("lw   x23, 22 * 4(sp)");
		__asm volatile("lw   x24, 23 * 4(sp)");
		__asm volatile("lw   x25, 24 * 4(sp)");
		__asm volatile("lw   x26, 25 * 4(sp)");
		__asm volatile("lw   x27, 26 * 4(sp)");
		__asm volatile("lw   x28, 27 * 4(sp)");
		__asm volatile("lw   x29, 28 * 4(sp)");
		__asm volatile("lw   x30, 29 * 4(sp)");
		__asm volatile("lw   x31, 30 * 4(sp)");

		__asm volatile("addi	sp, sp, 4 * 32");

		//PRCI->MSIP[0] = 0x00;

		__asm volatile("addi sp, sp, -1*4");
		__asm volatile("sw t0, 0(sp)");
		__asm volatile("li t0, 0x44000000");	// address of PRCI->MSIP[0]
		__asm volatile("sw zero,0(t0)");
		__asm volatile("lw t0, 0(sp)");
		__asm volatile("addi sp, sp, 1*4");

		__asm volatile("mret");
	}
}

void vPortYield( void )
{
	raise_soft_interrupt();
}

