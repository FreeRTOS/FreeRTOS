/*
 * FreeRTOS Kernel V10.3.0
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
 * https://www.FreeRTOS.org
 * https://aws.amazon.com/freertos
 *
 * 1 tab == 4 spaces!
 */

/******************************************************************************
 * This project is a modification of the standard blinky demo to demonstrate the
 * configuration of the PMP to prevent execution of data memory.
 * 
 * You want to read prvSetupHardware() and the linker script bsp/metal.pmp.lds 
 *
 */

/* FreeRTOS kernel includes. */
#include <FreeRTOS.h>
#include <task.h>

/* Freedom metal driver includes. */
#include <metal/cpu.h>
#include <metal/led.h>
#include <metal/pmp.h>

/* Set mainCREATE_SIMPLE_BLINKY_DEMO_ONLY to one to run the simple blinky demo,
or 0 to run the more comprehensive test and demo application. */
#define mainCREATE_SIMPLE_BLINKY_DEMO_ONLY	0

/* Index to first HART (there is only one). */
#define mainHART_0 		0

/* Registers used to initialise the PLIC. */
#define mainPLIC_PENDING_0 ( * ( ( volatile uint32_t * ) 0x0C001000UL ) )
#define mainPLIC_PENDING_1 ( * ( ( volatile uint32_t * ) 0x0C001004UL ) )
#define mainPLIC_ENABLE_0  ( * ( ( volatile uint32_t * ) 0x0C002000UL ) )
#define mainPLIC_ENABLE_1  ( * ( ( volatile uint32_t * ) 0x0C002004UL ) )

/*-----------------------------------------------------------*/

/*
 * main_blinky() is used when mainCREATE_SIMPLE_BLINKY_DEMO_ONLY is set to 1.
 * main_full() is used when mainCREATE_SIMPLE_BLINKY_DEMO_ONLY is set to 0.
 */
#if mainCREATE_SIMPLE_BLINKY_DEMO_ONLY == 1
	extern void main_blinky( void );
#else
	extern void main_full( void );
#endif /* #if mainCREATE_SIMPLE_BLINKY_DEMO_ONLY == 1 */

/*
 * Prototypes for the standard FreeRTOS callback/hook functions implemented
 * within this file.  See https://www.freertos.org/a00016.html
 */
void vApplicationMallocFailedHook( void );
void vApplicationIdleHook( void );
void vApplicationStackOverflowHook( TaskHandle_t pxTask, char *pcTaskName );
void vApplicationTickHook( void );

/*
 * Setup the hardware to run this demo.
 */
static void prvSetupHardware( void );

/*
 * Format base address for NAPOT address matching.
 *
 * NAPOT -- Naturally aligned power-of-two region, >= 8 bytes.
 * In additional to this function, the underlying linker script used
 * shall also have at least ALIGN(8) for the segment(s) to be protected.
 *
 * Examples for NAPOT address matching:
 * 8-byte:  pmpaddr yyyy....yyy0
 * 16-byte: pmpaddr yyyy....yy01
 * 32-byte: pmpaddr yyyy....y011
 * ...
 */
static size_t prvFormatPmpAddrMatchNapot( size_t ulBaseAddress, uint32_t ulNapotSize );

/*
 * Format base address for TOR address matching.
 */
static size_t prvFormatPmpAddrMatchTor( size_t ulBaseAddress );

/* Setup PMP config handle.
 * pmpxcfg[7] 	L: PMP entry locked.
 * pmpxcfg[4:3] A: PMP entry address matching mode.
 * pmpxcfg[2]	X: executable.
 * pmpxcfg[1]	W: writable.
 * pmpxcfg[0]	R: readable.
 */
static void prvPmpAccessConfig( struct metal_pmp_config * xPmpConfigHandle,
								enum metal_pmp_locked L,
								enum metal_pmp_address_mode A,
								int X,
								int W,
								int R );

/* A dummy function to increase a global variable.
 * The hex values of this function will be used to perform code injection.
 */
uint16_t uCounter = 0;
void prvIncGlobalCounter( void )
{
	uCounter += 1;
}

/* Copy over prvIncGlobalCounter() hex values into this block.
 * Per RISC-V spec:
 * Instructions are stored in memory as a sequence of 16-bit little-endian parcels,
 * regardless of memory system endianness.
 */
uint16_t pxInstructionArray[] = { 0x1141, 0xc622, 0x0800, 0x17b7, 0x8000, 0xd783, 0xacc7, 0x0785,
								  0x9713, 0x0107, 0x8341, 0x17b7, 0x8000, 0x9623, 0xace7, 0x0001,
								  0x4432, 0x0141, 0x8082 };

uint32_t ulDataAddr = (uint32_t) pxInstructionArray;

/*
 * Used by the Freedom Metal drivers.
 */
static struct metal_led *pxBlueLED = NULL;

/*-----------------------------------------------------------*/

int main( void )
{
	prvSetupHardware();

	/* The mainCREATE_SIMPLE_BLINKY_DEMO_ONLY setting is described at the top
	of this file. */
	#if( mainCREATE_SIMPLE_BLINKY_DEMO_ONLY == 1 )
	{
		main_blinky();
	}
	#else
	{
		main_full();
	}
	#endif
}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
struct metal_cpu *pxCPU;
struct metal_pmp *pxPMP;
struct metal_pmp_config xPmpConfig;
struct metal_interrupt *pxInterruptController;

size_t ulPmpBaseAddress;

int iStatus;

extern uint32_t _privileged_data_start;
extern uint32_t _privileged_function_start;
extern uint32_t _common_function_start;
extern uint32_t _common_data_end;

	/* This function initialises hardware in these steps:
	   - peripheral power on initialization.
	   - get the ID of the hart which is to be initialised.
	   - memory protection setup.
	   - enable interrupts.
	   FreeRTOS interrupt handler is initialised right before scheduler starts.
	   For now early_trap_vector is used to handle exceptions, see entry.S.
	*/

	/* Initialise the blue LED. */
	pxBlueLED = metal_led_get_rgb( "LD0", "blue" );
	configASSERT( pxBlueLED );
	metal_led_enable( pxBlueLED );
	metal_led_off( pxBlueLED );

	/* Get hart ID. */
	pxCPU = metal_cpu_get( mainHART_0 );
	configASSERT( pxCPU );

	/* Quick test, before setting up PMP.
	   Processor is still in M-mode, access to privileged_* sections cannot be
	   tested here. Though attempt to execute from .data/.bss will succeed, since
	   RAM has memory attribute X/W/R before setting up PMP. Attempt to write to
	   .text will fail, since flash has X/R attribute. PMP checking is in parallel
	   to PMA checking.

	   uCounter shall be incremented twice below.
	*/
	void (*pFuncIncGlobalCounter)(void) = &prvIncGlobalCounter;
	__asm volatile("funct_call_start: nop");
	(*pFuncIncGlobalCounter)();
	__asm volatile("funct_call_end: nop");

	pFuncIncGlobalCounter = (void (*)(void))pxInstructionArray;
	__asm volatile("code_inject_start: nop");
	(*pFuncIncGlobalCounter)();
	__asm volatile("code_inject_end: nop");


	/* Setup physical memory protection. */
	pxPMP = metal_pmp_get_device();
	configASSERT( pxPMP );

	metal_pmp_init( pxPMP );

	/* Kernel functions:
	   Full access to M-mode, no access to U-mode.
	   .privileged_functions section takes 0x4a2e bytes.
	   Thus with NAPOT alignment set block size to be 0x8000 bytes.
	   todo: switch to U-mode. */
	ulPmpBaseAddress = prvFormatPmpAddrMatchNapot( (size_t)&_privileged_function_start, 0x8000 );
	prvPmpAccessConfig( &xPmpConfig, METAL_PMP_UNLOCKED, METAL_PMP_NAPOT, 0, 0, 0 );
	iStatus = metal_pmp_set_region( pxPMP, 0, xPmpConfig, ulPmpBaseAddress );
	configASSERT( iStatus == 0 );

	/* .text section:
	   For both M-mode and U-mode, R/X access only.
	   .text is in flash and address range [0x2000_0000, 0x3FFFF_FFFF] has memory
	   attribute Read/eXecute/Cacheable (no Write attribute). Thus, no harm is
	   done even without PMP. The protection is more to catch anomaly instead of
	   assuring no change to code at runtime. The exception handler could simply
	   recover from this violation without any other action.

	   Also note that every time code is modified, needs to check whether the
	   section alignment is still correct. To be specific, all .text addresses
	   need to fit in one PMP entry. */
	ulPmpBaseAddress = prvFormatPmpAddrMatchNapot( (size_t)&_common_function_start, 0x10000 );
	prvPmpAccessConfig( &xPmpConfig, METAL_PMP_LOCKED, METAL_PMP_NAPOT, 1, 0, 1 );
	iStatus = metal_pmp_set_region( pxPMP, 1, xPmpConfig, ulPmpBaseAddress );
	configASSERT( iStatus == 0 );

	/* Kernel data:
	   Full access to M-mode, no access to U-mode.
	   .privilege_data section takes 0x1a8 bytes.
	   Thus with NAPOT alignment set block size to be 512 bytes.
	   todo: switch to U-mode. */
	ulPmpBaseAddress = prvFormatPmpAddrMatchNapot( (size_t)&_privileged_data_start, 0x200 );
	prvPmpAccessConfig( &xPmpConfig, METAL_PMP_UNLOCKED, METAL_PMP_NAPOT, 0, 0, 0 );
	iStatus = metal_pmp_set_region( pxPMP, 2, xPmpConfig, ulPmpBaseAddress );
	configASSERT( iStatus == 0 );

	/* .data and .bss sections:
	   For both M-mode and U-mode, R/W access only.
	   This PMP entry HAS TO be placed RIGHT AFTER "kernel data". AND
	   these sections HAVE TO be contiguous -- .privilege_data, .data, .bss
	   Since:
	   - RAM size is very limited. Using NAPOT/NA4 address matching results
	     significant waste. Thus, use TOR address matching.
	   - When TOR address matching is used, access to address within range
	     pmpaddr[i-1] <= y <= pmpaddr[i] is allowed. Also, since address matching
	     starts from the lowest numbered PMP entry, M-mode access to .privilege_data
	     matches previous entry's privilege configuration. M/U-mode access to .data
	     and .bss falls to this PMP entry. */
	ulPmpBaseAddress = prvFormatPmpAddrMatchTor( (size_t)&_common_data_end );
	prvPmpAccessConfig( &xPmpConfig, METAL_PMP_LOCKED, METAL_PMP_TOR, 0, 1, 1 );
	iStatus = metal_pmp_set_region( pxPMP, 3, xPmpConfig, ulPmpBaseAddress );
	configASSERT( iStatus == 0 );

	/* Initialise the interrupt controller. */
	pxInterruptController = metal_cpu_interrupt_controller( pxCPU );
	configASSERT( pxInterruptController );
	metal_interrupt_init( pxInterruptController );

	/* Set all interrupt enable bits to 0. */
	mainPLIC_ENABLE_0 = 0UL;
	mainPLIC_ENABLE_1 = 0UL;

	/* Quick test, after setting up PMP.
	   Attempt to execute from .data will get exception. uCounter shall not be
	   incremented.*/
	pFuncIncGlobalCounter = (void (*)(void))pxInstructionArray;
	__asm volatile("pmp_start: nop");
	(*pFuncIncGlobalCounter)();
	__asm volatile("pmp_end: nop");

}
/*-----------------------------------------------------------*/


static size_t prvFormatPmpAddrMatchNapot( size_t ulBaseAddress, uint32_t ulNapotSize )
{
size_t ulTempAddress;

	/* Drop the bottom two bits, since:
	   1- each PMP address register encodes bits [33: 2] of a 34-bit physical
	      address for RV32.
	   2- PMP addresses are 4-byte aligned. */
	ulTempAddress = ulBaseAddress >> 2;

	/* Clear the bit corresponding with alignment */
	ulTempAddress &= ~( ulNapotSize >> 3 );

	/* Set the bits up to the alignment bit */
	ulTempAddress |= ( ( ulNapotSize >> 3 ) - 1 );

	return ulTempAddress;
}
/*-----------------------------------------------------------*/


static size_t prvFormatPmpAddrMatchTor( size_t ulBaseAddress )
{
	/* Drop the bottom two bits, since:
	   1- each PMP address register encodes bits [33: 2] of a 34-bit physical
	      address for RV32.
	   2- PMP addresses are 4-byte aligned. */
	return ( ulBaseAddress >> 2 );
}

/*-----------------------------------------------------------*/

static void prvPmpAccessConfig( struct metal_pmp_config * xPmpConfigHandle,
								enum metal_pmp_locked L,
								enum metal_pmp_address_mode A,
								int X,
								int W,
								int R )
{
	/* Since this is not intended to be an API, do not check inputs here.
	 * L, A bits -- see enum definition.
	 * X, W, R bits -- 1 to grant access, 0 to clear access. */
	xPmpConfigHandle->L = L;
	xPmpConfigHandle->A = A;
	xPmpConfigHandle->X = X;
	xPmpConfigHandle->W = W;
	xPmpConfigHandle->R = R;

	return;
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

	/* Run time stack overflow checking is performed if
	configCHECK_FOR_STACK_OVERFLOW is defined to 1 or 2.  This hook
	function is called if a stack overflow is detected. */
	taskDISABLE_INTERRUPTS();
	for( ;; );
}
/*-----------------------------------------------------------*/

void vApplicationTickHook( void )
{
	/* The tests in the full demo expect some interaction with interrupts. */
	#if( mainCREATE_SIMPLE_BLINKY_DEMO_ONLY != 1 )
	{
		extern void vFullDemoTickHook( void );
		vFullDemoTickHook();
	}
	#endif
}
/*-----------------------------------------------------------*/

void vAssertCalled( void )
{
static struct metal_led *pxRedLED = NULL;
volatile uint32_t ul;
const uint32_t ulNullLoopDelay = 0x1ffffUL;

	taskDISABLE_INTERRUPTS();

	/* Initialise the red LED. */
	pxRedLED = metal_led_get_rgb( "LD0", "red" );
	configASSERT( pxRedLED );
	metal_led_enable( pxRedLED );
	metal_led_off( pxRedLED );

	/* Flash the red LED to indicate that assert was hit - interrupts are off
	here to prevent any further tick interrupts or context switches, so the
	delay is implemented as a crude loop instead of a peripheral timer. */
	for( ;; )
	{
		for( ul = 0; ul < ulNullLoopDelay; ul++ )
		{
			__asm volatile( "nop" );
		}
		metal_led_toggle( pxRedLED );
	}
}
/*-----------------------------------------------------------*/

void handle_trap( void )
{
volatile uint32_t ulMEPC = 0UL, ulMCAUSE = 0UL, ulPLICPending0Register = 0UL, ulPLICPending1Register = 0UL;

	/* Store a few register values that might be useful when determining why this
	function was called. */
	__asm volatile( "csrr %0, mepc" : "=r"( ulMEPC ) );
	__asm volatile( "csrr %0, mcause" : "=r"( ulMCAUSE ) );
	ulPLICPending0Register = mainPLIC_PENDING_0;
	ulPLICPending1Register = mainPLIC_PENDING_1;

	/* Prevent compiler warnings about unused variables. */
	( void ) ulPLICPending0Register;
	( void ) ulPLICPending1Register;

	/* Force an assert as this function has not been implemented as the demo
	does not use external interrupts. */
	configASSERT( metal_cpu_get( mainHART_0 ) == 0x00 );
}
/*-----------------------------------------------------------*/

void vToggleLED( void )
{
	metal_led_toggle( pxBlueLED );
}
/*-----------------------------------------------------------*/

void *malloc( size_t xSize )
{
	/* The linker script does not define a heap so artificially force an assert()
	if something unexpectedly uses the C library heap.  See
	https://www.freertos.org/a00111.html for more information. */
	configASSERT( metal_cpu_get( mainHART_0 ) == 0x00 );

	/* Remove warnings about unused parameter. */
	( void ) xSize;
	return NULL;
}
/*-----------------------------------------------------------*/


