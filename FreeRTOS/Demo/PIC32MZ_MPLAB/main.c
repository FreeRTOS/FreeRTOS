/*
 * FreeRTOS Kernel V10.4.1
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

/******************************************************************************
 * This project provides two demo applications.  A simple blinky style project,
 * and a more comprehensive test and demo application.  The
 * mainCREATE_SIMPLE_BLINKY_DEMO_ONLY setting (defined in this file) is used to
 * select between the two.  The simply blinky demo is implemented and described
 * in main_blinky.c.  The more comprehensive test and demo application is
 * implemented and described in main_full.c.
 *
 * This file implements the code that is not demo specific, including the
 * hardware setup and FreeRTOS hook functions.
 */

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Standard demo includes. */
#include "partest.h"
#include "QueueOverwrite.h"
#include "QueueSet.h"
#include "EventGroupsDemo.h"

/* Hardware specific includes. */
#include "ConfigPerformance.h"

/* Core configuration fuse settings */
#if defined(__32MZ2048ECM144) || defined(__32MZ2048ECH144)
	#pragma config FMIIEN = OFF, FETHIO = OFF, PGL1WAY = OFF, PMDL1WAY = OFF, IOL1WAY = OFF, FUSBIDIO = OFF
	#pragma config FNOSC = SPLL, FSOSCEN = OFF, IESO = OFF, POSCMOD = EC
	#pragma config OSCIOFNC = OFF, FCKSM = CSECMD, FWDTEN = OFF, FDMTEN = OFF
	#pragma config DMTINTV = WIN_127_128, WDTSPGM = STOP, WINDIS= NORMAL
	#pragma config WDTPS = PS1048576, FWDTWINSZ = WINSZ_25, DMTCNT = DMT31
	#pragma config FPLLIDIV = DIV_3, FPLLRNG = RANGE_13_26_MHZ, FPLLICLK = PLL_POSC
	#pragma config FPLLMULT = MUL_50, FPLLODIV = DIV_2, UPLLFSEL = FREQ_12MHZ, UPLLEN = OFF
	#pragma config EJTAGBEN = NORMAL, DBGPER = PG_ALL, FSLEEP = OFF, FECCCON = OFF_UNLOCKED
	#pragma config BOOTISA = MIPS32, TRCEN = ON, ICESEL = ICS_PGx2, JTAGEN = OFF, DEBUG = ON
	#pragma config CP = OFF
#elif defined(__32MZ2048EFM144) || defined(__32MZ2048EFH144)
	#pragma config FMIIEN = OFF, FETHIO = OFF, PGL1WAY = OFF, PMDL1WAY = OFF, IOL1WAY = OFF, FUSBIDIO = OFF
	#pragma config FNOSC = SPLL, FSOSCEN = OFF, IESO = OFF, POSCMOD = EC
	#pragma config OSCIOFNC = OFF, FCKSM = CSECMD, FWDTEN = OFF, FDMTEN = OFF
	#pragma config DMTINTV = WIN_127_128, WDTSPGM = STOP, WINDIS= NORMAL
	#pragma config WDTPS = PS1048576, FWDTWINSZ = WINSZ_25, DMTCNT = DMT31
	#pragma config FPLLIDIV = DIV_3, FPLLRNG = RANGE_13_26_MHZ, FPLLICLK = PLL_POSC
	#pragma config FPLLMULT = MUL_50, FPLLODIV = DIV_2, UPLLFSEL = FREQ_12MHZ
	#pragma config EJTAGBEN = NORMAL, DBGPER = PG_ALL, FSLEEP = OFF, FECCCON = OFF_UNLOCKED
	#pragma config BOOTISA = MIPS32, TRCEN = ON, ICESEL = ICS_PGx2, JTAGEN = OFF, DEBUG = ON
	#pragma config CP = OFF
#endif

/*-----------------------------------------------------------*/

/* Set mainCREATE_SIMPLE_BLINKY_DEMO_ONLY to one to run the simple blinky demo,
or 0 to run the more comprehensive test and demo application. */
#define mainCREATE_SIMPLE_BLINKY_DEMO_ONLY	0

/*-----------------------------------------------------------*/

/*
 * Set up the hardware ready to run this demo.
 */
static void prvSetupHardware( void );

/*
 * main_blinky() is used when mainCREATE_SIMPLE_BLINKY_DEMO_ONLY is set to 1.
 * main_full() is used when mainCREATE_SIMPLE_BLINKY_DEMO_ONLY is set to 0.
 */
extern void main_blinky( void );
extern void main_full( void );

/*-----------------------------------------------------------*/

/*
 * Create the demo tasks then start the scheduler.
 */
int main( void )
{
	/* Prepare the hardware to run this demo. */
	prvSetupHardware();

	/* The mainCREATE_SIMPLE_BLINKY_DEMO_ONLY setting is described at the top
	of this file. */
	#if mainCREATE_SIMPLE_BLINKY_DEMO_ONLY == 1
	{
		main_blinky();
	}
	#else
	{
		main_full();
	}
	#endif

	return 0;
}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
	/* Configure the hardware for maximum performance. */
	vHardwareConfigurePerformance();

	/* Setup to use the external interrupt controller. */
	vHardwareUseMultiVectoredInterrupts();

	portDISABLE_INTERRUPTS();

	/* Setup the digital IO for the LED's. */
	vParTestInitialise();
}
/*-----------------------------------------------------------*/

void vApplicationMallocFailedHook( void )
{
	/* vApplicationMallocFailedHook() will only be called if
	configUSE_MALLOC_FAILED_HOOK is set to 1 in FreeRTOSConfig.h.  It is a hook
	function that will get called if a call to pvPortMalloc() fails.
	pvPortMalloc() is called internally by the kernel whenever a task, queue,
	timer or semaphore is created.  It is also called by various parts of the
	demo application.  If heap_1.c or heap_2.c are used, then the size of the
	heap available to pvPortMalloc() is defined by configTOTAL_HEAP_SIZE in
	FreeRTOSConfig.h, and the xPortGetFreeHeapSize() API function can be used
	to query the size of free heap space that remains (although it does not
	provide information on how the remaining heap might be fragmented). */
	taskDISABLE_INTERRUPTS();
	for( ;; );
}
/*-----------------------------------------------------------*/

void vApplicationIdleHook( void )
{
	/* vApplicationIdleHook() will only be called if configUSE_IDLE_HOOK is set
	to 1 in FreeRTOSConfig.h.  It will be called on each iteration of the idle
	task.  It is essential that code added to this hook function never attempts
	to block in any way (for example, call xQueueReceive() with a block time
	specified, or call vTaskDelay()).  If the application makes use of the
	vTaskDelete() API function (as this demo application does) then it is also
	important that vApplicationIdleHook() is permitted to return to its calling
	function, because it is the responsibility of the idle task to clean up
	memory allocated by the kernel to any task that has since been deleted. */
}
/*-----------------------------------------------------------*/

void vApplicationStackOverflowHook( TaskHandle_t pxTask, char *pcTaskName )
{
	( void ) pcTaskName;
	( void ) pxTask;

	/* Run time task stack overflow checking is performed if
	configCHECK_FOR_STACK_OVERFLOW is defined to 1 or 2.  This hook	function is
	called if a task stack overflow is detected.  Note the system/interrupt
	stack is not checked. */
	taskDISABLE_INTERRUPTS();
	for( ;; );
}
/*-----------------------------------------------------------*/

void vApplicationTickHook( void )
{
	/* This function will be called by each tick interrupt if
	configUSE_TICK_HOOK is set to 1 in FreeRTOSConfig.h.  User code can be
	added here, but the tick hook is called from an interrupt context, so
	code must not attempt to block, and only the interrupt safe FreeRTOS API
	functions can be used (those that end in FromISR()). */

	#if( mainCREATE_SIMPLE_BLINKY_DEMO_ONLY == 0 )
	{
		/* Call the periodic queue overwrite from ISR demo. */
		vQueueOverwritePeriodicISRDemo();

		/* Call the queue set ISR test function. */
		vQueueSetAccessQueueSetFromISR();

		/* Exercise event groups from interrupts. */
		vPeriodicEventGroupsProcessing();
	}
	#endif
}
/*-----------------------------------------------------------*/

extern void vAssertCalled( const char * pcFile, unsigned long ulLine )
{
volatile char *pcFileName;
volatile unsigned long ulLineNumber;

	/* Prevent things that are useful to view in the debugger from being
	optimised away. */
	pcFileName = ( char * ) pcFile;
	( void ) pcFileName;
	ulLineNumber = ulLine;

	/* Set ulLineNumber to 0 in the debugger to break out of this loop and
	return to the line that triggered the assert. */
	while( ulLineNumber != 0 )
	{
		__asm volatile( "NOP" );
		__asm volatile( "NOP" );
		__asm volatile( "NOP" );
		__asm volatile( "NOP" );
		__asm volatile( "NOP" );
	}
}
/*-----------------------------------------------------------*/

/* This function overrides the normal _weak_ generic handler. */
void _general_exception_handler(void)
{
static enum {
	EXCEP_IRQ = 0, 	/* interrupt */
	EXCEP_AdEL = 4, /* address error exception (load or ifetch) */
	EXCEP_AdES, 	/* address error exception (store) */
	EXCEP_IBE, 		/* bus error (ifetch) */
	EXCEP_DBE, 		/* bus error (load/store) */
	EXCEP_Sys, 		/* syscall */
	EXCEP_Bp, 		/* breakpoint */
	EXCEP_RI, 		/* reserved instruction */
	EXCEP_CpU, 		/* coprocessor unusable */
	EXCEP_Overflow,	/* arithmetic overflow */
	EXCEP_Trap, 	/* trap (possible divide by zero) */
	EXCEP_FPE = 15, /* floating point exception */
	EXCEP_IS1 = 16,	/* implementation specfic 1 */
	EXCEP_CEU, 		/* CorExtend Unuseable */
	EXCEP_C2E, 		/* coprocessor 2 */
	EXCEP_DSPDis = 26   /* DSP module disabled */
} _excep_code;

static unsigned long _epc_code;
static unsigned long _excep_addr;

	asm volatile( "mfc0 %0,$13" : "=r" (_epc_code) );
	asm volatile( "mfc0 %0,$14" : "=r" (_excep_addr) );

	_excep_code = ( _epc_code & 0x0000007C ) >> 2;

    for( ;; )
	{
		/* prevent compiler warning */
		(void) _excep_code;

		/* Examine _excep_code to identify the type of exception.  Examine
		_excep_addr to find the address that caused the exception */
		LATHSET = 0x0007;
		Nop();
		Nop();
		Nop();
	}
}
/*-----------------------------------------------------------*/

