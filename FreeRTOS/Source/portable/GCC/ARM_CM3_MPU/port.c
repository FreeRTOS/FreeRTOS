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
 * Implementation of functions defined in portable.h for the ARM CM3 port.
 *----------------------------------------------------------*/

/* Defining MPU_WRAPPERS_INCLUDED_FROM_API_FILE prevents task.h from redefining
all the API functions to use the MPU wrappers.  That should only be done when
task.h is included from an application file. */
#define MPU_WRAPPERS_INCLUDED_FROM_API_FILE

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"

#undef MPU_WRAPPERS_INCLUDED_FROM_API_FILE

/* Constants required to access and manipulate the NVIC. */
#define portNVIC_SYSTICK_CTRL					( ( volatile unsigned long * ) 0xe000e010 )
#define portNVIC_SYSTICK_LOAD					( ( volatile unsigned long * ) 0xe000e014 )
#define portNVIC_SYSPRI2						( ( volatile unsigned long * ) 0xe000ed20 )
#define portNVIC_SYSPRI1						( ( volatile unsigned long * ) 0xe000ed1c )
#define portNVIC_SYS_CTRL_STATE					( ( volatile unsigned long * ) 0xe000ed24 )
#define portNVIC_MEM_FAULT_ENABLE				( 1UL << 16UL )

/* Constants required to access and manipulate the MPU. */
#define portMPU_TYPE							( ( volatile unsigned long * ) 0xe000ed90 )
#define portMPU_REGION_BASE_ADDRESS				( ( volatile unsigned long * ) 0xe000ed9C )
#define portMPU_REGION_ATTRIBUTE				( ( volatile unsigned long * ) 0xe000edA0 )
#define portMPU_CTRL							( ( volatile unsigned long * ) 0xe000ed94 )
#define portEXPECTED_MPU_TYPE_VALUE				( 8UL << 8UL ) /* 8 regions, unified. */
#define portMPU_ENABLE							( 0x01UL )
#define portMPU_BACKGROUND_ENABLE				( 1UL << 2UL )
#define portPRIVILEGED_EXECUTION_START_ADDRESS	( 0UL )
#define portMPU_REGION_VALID					( 0x10UL )
#define portMPU_REGION_ENABLE					( 0x01UL )
#define portPERIPHERALS_START_ADDRESS			0x40000000UL
#define portPERIPHERALS_END_ADDRESS				0x5FFFFFFFUL

/* Constants required to access and manipulate the SysTick. */
#define portNVIC_SYSTICK_CLK					( 0x00000004UL )
#define portNVIC_SYSTICK_INT					( 0x00000002UL )
#define portNVIC_SYSTICK_ENABLE					( 0x00000001UL )
#define portNVIC_PENDSV_PRI						( ( ( unsigned long ) configKERNEL_INTERRUPT_PRIORITY ) << 16UL )
#define portNVIC_SYSTICK_PRI					( ( ( unsigned long ) configKERNEL_INTERRUPT_PRIORITY ) << 24UL )
#define portNVIC_SVC_PRI						( ( ( unsigned long ) configKERNEL_INTERRUPT_PRIORITY ) << 24UL )

/* Constants required to set up the initial stack. */
#define portINITIAL_XPSR						( 0x01000000 )
#define portINITIAL_CONTROL_IF_UNPRIVILEGED		( 0x03 )
#define portINITIAL_CONTROL_IF_PRIVILEGED		( 0x02 )

/* Offsets in the stack to the parameters when inside the SVC handler. */
#define portOFFSET_TO_PC						( 6 )

/* Set the privilege level to user mode if xRunningPrivileged is false. */
#define portRESET_PRIVILEGE( xRunningPrivileged ) if( xRunningPrivileged != pdTRUE ) __asm volatile ( " mrs r0, control \n orr r0, #1 \n msr control, r0" :::"r0" )

/* Each task maintains its own interrupt status in the critical nesting
variable.  Note this is not saved as part of the task context as context
switches can only occur when uxCriticalNesting is zero. */
static unsigned portBASE_TYPE uxCriticalNesting = 0xaaaaaaaa;

/*
 * Setup the timer to generate the tick interrupts.
 */
static void prvSetupTimerInterrupt( void ) PRIVILEGED_FUNCTION;

/*
 * Configure a number of standard MPU regions that are used by all tasks.
 */
static void prvSetupMPU( void ) PRIVILEGED_FUNCTION;

/*
 * Return the smallest MPU region size that a given number of bytes will fit
 * into.  The region size is returned as the value that should be programmed
 * into the region attribute register for that region.
 */
static unsigned long prvGetMPURegionSizeSetting( unsigned long ulActualSizeInBytes ) PRIVILEGED_FUNCTION;

/*
 * Checks to see if being called from the context of an unprivileged task, and
 * if so raises the privilege level and returns false - otherwise does nothing
 * other than return true.
 */
static portBASE_TYPE prvRaisePrivilege( void ) __attribute__(( naked ));

/*
 * Standard FreeRTOS exception handlers.
 */
void xPortPendSVHandler( void ) __attribute__ (( naked )) PRIVILEGED_FUNCTION;
void xPortSysTickHandler( void )  __attribute__ ((optimize("3"))) PRIVILEGED_FUNCTION;
void vPortSVCHandler( void ) __attribute__ (( naked )) PRIVILEGED_FUNCTION;

/*
 * Starts the scheduler by restoring the context of the first task to run.
 */
static void prvRestoreContextOfFirstTask( void ) __attribute__(( naked )) PRIVILEGED_FUNCTION;

/*
 * C portion of the SVC handler.  The SVC handler is split between an asm entry
 * and a C wrapper for simplicity of coding and maintenance.
 */
static void prvSVCHandler( unsigned long *pulRegisters ) __attribute__(( noinline )) PRIVILEGED_FUNCTION;

/*
 * Prototypes for all the MPU wrappers.
 */
signed portBASE_TYPE MPU_xTaskGenericCreate( pdTASK_CODE pvTaskCode, const signed char * const pcName, unsigned short usStackDepth, void *pvParameters, unsigned portBASE_TYPE uxPriority, xTaskHandle *pxCreatedTask, portSTACK_TYPE *puxStackBuffer, const xMemoryRegion * const xRegions );
void MPU_vTaskAllocateMPURegions( xTaskHandle xTask, const xMemoryRegion * const xRegions );
void MPU_vTaskDelete( xTaskHandle pxTaskToDelete );
void MPU_vTaskDelayUntil( portTickType * const pxPreviousWakeTime, portTickType xTimeIncrement );
void MPU_vTaskDelay( portTickType xTicksToDelay );
unsigned portBASE_TYPE MPU_uxTaskPriorityGet( xTaskHandle pxTask );
void MPU_vTaskPrioritySet( xTaskHandle pxTask, unsigned portBASE_TYPE uxNewPriority );
eTaskState MPU_eTaskGetState( xTaskHandle pxTask );
void MPU_vTaskSuspend( xTaskHandle pxTaskToSuspend );
signed portBASE_TYPE MPU_xTaskIsTaskSuspended( xTaskHandle xTask );
void MPU_vTaskResume( xTaskHandle pxTaskToResume );
void MPU_vTaskSuspendAll( void );
signed portBASE_TYPE MPU_xTaskResumeAll( void );
portTickType MPU_xTaskGetTickCount( void );
unsigned portBASE_TYPE MPU_uxTaskGetNumberOfTasks( void );
void MPU_vTaskList( signed char *pcWriteBuffer );
void MPU_vTaskGetRunTimeStats( signed char *pcWriteBuffer );
void MPU_vTaskSetApplicationTaskTag( xTaskHandle xTask, pdTASK_HOOK_CODE pxTagValue );
pdTASK_HOOK_CODE MPU_xTaskGetApplicationTaskTag( xTaskHandle xTask );
portBASE_TYPE MPU_xTaskCallApplicationTaskHook( xTaskHandle xTask, void *pvParameter );
unsigned portBASE_TYPE MPU_uxTaskGetStackHighWaterMark( xTaskHandle xTask );
xTaskHandle MPU_xTaskGetCurrentTaskHandle( void );
portBASE_TYPE MPU_xTaskGetSchedulerState( void );
xTaskHandle MPU_xTaskGetIdleTaskHandle( void );
xQueueHandle MPU_xQueueGenericCreate( unsigned portBASE_TYPE uxQueueLength, unsigned portBASE_TYPE uxItemSize, unsigned char ucQueueType );
signed portBASE_TYPE MPU_xQueueGenericSend( xQueueHandle xQueue, const void * const pvItemToQueue, portTickType xTicksToWait, portBASE_TYPE xCopyPosition );
portBASE_TYPE MPU_xQueueGenericReset( xQueueHandle pxQueue, portBASE_TYPE xNewQueue );
unsigned portBASE_TYPE MPU_uxQueueMessagesWaiting( const xQueueHandle pxQueue );
signed portBASE_TYPE MPU_xQueueGenericReceive( xQueueHandle pxQueue, void * const pvBuffer, portTickType xTicksToWait, portBASE_TYPE xJustPeeking );
xQueueHandle MPU_xQueueCreateMutex( void );
xQueueHandle MPU_xQueueCreateCountingSemaphore( unsigned portBASE_TYPE uxCountValue, unsigned portBASE_TYPE uxInitialCount );
portBASE_TYPE MPU_xQueueTakeMutexRecursive( xQueueHandle xMutex, portTickType xBlockTime );
portBASE_TYPE MPU_xQueueGiveMutexRecursive( xQueueHandle xMutex );
signed portBASE_TYPE MPU_xQueueAltGenericSend( xQueueHandle pxQueue, const void * const pvItemToQueue, portTickType xTicksToWait, portBASE_TYPE xCopyPosition );
signed portBASE_TYPE MPU_xQueueAltGenericReceive( xQueueHandle pxQueue, void * const pvBuffer, portTickType xTicksToWait, portBASE_TYPE xJustPeeking );
void MPU_vQueueAddToRegistry( xQueueHandle xQueue, signed char *pcName );
void MPU_vQueueDelete( xQueueHandle xQueue );
void *MPU_pvPortMalloc( size_t xSize );
void MPU_vPortFree( void *pv );
void MPU_vPortInitialiseBlocks( void );
size_t MPU_xPortGetFreeHeapSize( void );
xQueueSetHandle MPU_xQueueCreateSet( unsigned portBASE_TYPE uxEventQueueLength );
xQueueSetMemberHandle MPU_xQueueSelectFromSet( xQueueSetHandle xQueueSet, portTickType xBlockTimeTicks );
portBASE_TYPE MPU_xQueueAddToSet( xQueueSetMemberHandle xQueueOrSemaphore, xQueueSetHandle xQueueSet );
portBASE_TYPE MPU_xQueueRemoveFromSet( xQueueSetMemberHandle xQueueOrSemaphore, xQueueSetHandle xQueueSet );

/*-----------------------------------------------------------*/

/*
 * See header file for description.
 */
portSTACK_TYPE *pxPortInitialiseStack( portSTACK_TYPE *pxTopOfStack, pdTASK_CODE pxCode, void *pvParameters, portBASE_TYPE xRunPrivileged )
{
	/* Simulate the stack frame as it would be created by a context switch
	interrupt. */
	pxTopOfStack--; /* Offset added to account for the way the MCU uses the stack on entry/exit of interrupts. */
	*pxTopOfStack = portINITIAL_XPSR;	/* xPSR */
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) pxCode;	/* PC */
	pxTopOfStack--;
	*pxTopOfStack = 0;	/* LR */
	pxTopOfStack -= 5;	/* R12, R3, R2 and R1. */
	*pxTopOfStack = ( portSTACK_TYPE ) pvParameters;	/* R0 */
	pxTopOfStack -= 9;	/* R11, R10, R9, R8, R7, R6, R5 and R4. */

	if( xRunPrivileged == pdTRUE )
	{
		*pxTopOfStack = portINITIAL_CONTROL_IF_PRIVILEGED;
	}
	else
	{
		*pxTopOfStack = portINITIAL_CONTROL_IF_UNPRIVILEGED;
	}

	return pxTopOfStack;
}
/*-----------------------------------------------------------*/

void vPortSVCHandler( void )
{
	/* Assumes psp was in use. */
	__asm volatile
	(
		#ifndef USE_PROCESS_STACK	/* Code should not be required if a main() is using the process stack. */
			"	tst lr, #4						\n"
			"	ite eq							\n"
			"	mrseq r0, msp					\n"
			"	mrsne r0, psp					\n"
		#else
			"	mrs r0, psp						\n"
		#endif
			"	b %0							\n"
			::"i"(prvSVCHandler):"r0"
	);
}
/*-----------------------------------------------------------*/

static void prvSVCHandler(	unsigned long *pulParam )
{
unsigned char ucSVCNumber;

	/* The stack contains: r0, r1, r2, r3, r12, r14, the return address and
	xPSR.  The first argument (r0) is pulParam[ 0 ]. */
	ucSVCNumber = ( ( unsigned char * ) pulParam[ portOFFSET_TO_PC ] )[ -2 ];
	switch( ucSVCNumber )
	{
		case portSVC_START_SCHEDULER	:	*(portNVIC_SYSPRI1) |= portNVIC_SVC_PRI;
											prvRestoreContextOfFirstTask();
											break;

		case portSVC_YIELD				:	*(portNVIC_INT_CTRL) = portNVIC_PENDSVSET;
											/* Barriers are normally not required
											but do ensure the code is completely
											within the specified behaviour for the
											architecture. */
											__asm volatile( "dsb" );
											__asm volatile( "isb" );

											break;

		case portSVC_RAISE_PRIVILEGE	:	__asm volatile
											(
												"	mrs r1, control		\n" /* Obtain current control value. */
												"	bic r1, #1			\n" /* Set privilege bit. */
												"	msr control, r1		\n" /* Write back new control value. */
												:::"r1"
											);
											break;

		default							:	/* Unknown SVC call. */
											break;
	}
}
/*-----------------------------------------------------------*/

static void prvRestoreContextOfFirstTask( void )
{
	__asm volatile
	(
		"	ldr r0, =0xE000ED08				\n" /* Use the NVIC offset register to locate the stack. */
		"	ldr r0, [r0]					\n"
		"	ldr r0, [r0]					\n"
		"	msr msp, r0						\n" /* Set the msp back to the start of the stack. */
		"	ldr	r3, pxCurrentTCBConst2		\n" /* Restore the context. */
		"	ldr r1, [r3]					\n"
		"	ldr r0, [r1]					\n" /* The first item in the TCB is the task top of stack. */
		"	add r1, r1, #4					\n" /* Move onto the second item in the TCB... */
		"	ldr r2, =0xe000ed9c				\n" /* Region Base Address register. */
		"	ldmia r1!, {r4-r11}				\n" /* Read 4 sets of MPU registers. */
		"	stmia r2!, {r4-r11}				\n" /* Write 4 sets of MPU registers. */
		"	ldmia r0!, {r3, r4-r11}			\n" /* Pop the registers that are not automatically saved on exception entry. */
		"	msr control, r3					\n"
		"	msr psp, r0						\n" /* Restore the task stack pointer. */
		"	mov r0, #0						\n"
		"	msr	basepri, r0					\n"
		"	ldr r14, =0xfffffffd			\n" /* Load exec return code. */
		"	bx r14							\n"
		"									\n"
		"	.align 2						\n"
		"pxCurrentTCBConst2: .word pxCurrentTCB	\n"
	);
}
/*-----------------------------------------------------------*/

/*
 * See header file for description.
 */
portBASE_TYPE xPortStartScheduler( void )
{
	/* configMAX_SYSCALL_INTERRUPT_PRIORITY must not be set to 0.  See
	http://www.FreeRTOS.org/RTOS-Cortex-M3-M4.html */
	configASSERT( ( configMAX_SYSCALL_INTERRUPT_PRIORITY ) );

	/* Make PendSV and SysTick the same priority as the kernel. */
	*(portNVIC_SYSPRI2) |= portNVIC_PENDSV_PRI;
	*(portNVIC_SYSPRI2) |= portNVIC_SYSTICK_PRI;

	/* Configure the regions in the MPU that are common to all tasks. */
	prvSetupMPU();

	/* Start the timer that generates the tick ISR.  Interrupts are disabled
	here already. */
	prvSetupTimerInterrupt();

	/* Initialise the critical nesting count ready for the first task. */
	uxCriticalNesting = 0;

	/* Start the first task. */
	__asm volatile( "	svc %0			\n"
					:: "i" (portSVC_START_SCHEDULER) );

	/* Should not get here! */
	return 0;
}
/*-----------------------------------------------------------*/

void vPortEndScheduler( void )
{
	/* It is unlikely that the CM3 port will require this function as there
	is nothing to return to.  */
}
/*-----------------------------------------------------------*/

void vPortEnterCritical( void )
{
portBASE_TYPE xRunningPrivileged = prvRaisePrivilege();

	portDISABLE_INTERRUPTS();
	uxCriticalNesting++;

	portRESET_PRIVILEGE( xRunningPrivileged );
}
/*-----------------------------------------------------------*/

void vPortExitCritical( void )
{
portBASE_TYPE xRunningPrivileged = prvRaisePrivilege();

	uxCriticalNesting--;
	if( uxCriticalNesting == 0 )
	{
		portENABLE_INTERRUPTS();
	}
	portRESET_PRIVILEGE( xRunningPrivileged );
}
/*-----------------------------------------------------------*/

void xPortPendSVHandler( void )
{
	/* This is a naked function. */

	__asm volatile
	(
		"	mrs r0, psp							\n"
		"										\n"
		"	ldr	r3, pxCurrentTCBConst			\n" /* Get the location of the current TCB. */
		"	ldr	r2, [r3]						\n"
		"										\n"
		"	mrs r1, control						\n"
		"	stmdb r0!, {r1, r4-r11}				\n" /* Save the remaining registers. */
		"	str r0, [r2]						\n" /* Save the new top of stack into the first member of the TCB. */
		"										\n"
		"	stmdb sp!, {r3, r14}				\n"
		"	mov r0, %0							\n"
		"	msr basepri, r0						\n"
		"	bl vTaskSwitchContext				\n"
		"	mov r0, #0							\n"
		"	msr basepri, r0						\n"
		"	ldmia sp!, {r3, r14}				\n"
		"										\n"	/* Restore the context. */
		"	ldr r1, [r3]						\n"
		"	ldr r0, [r1]						\n" /* The first item in the TCB is the task top of stack. */
		"	add r1, r1, #4						\n" /* Move onto the second item in the TCB... */
		"	ldr r2, =0xe000ed9c					\n" /* Region Base Address register. */
		"	ldmia r1!, {r4-r11}					\n" /* Read 4 sets of MPU registers. */
		"	stmia r2!, {r4-r11}					\n" /* Write 4 sets of MPU registers. */
		"	ldmia r0!, {r3, r4-r11}				\n" /* Pop the registers that are not automatically saved on exception entry. */
		"	msr control, r3						\n"
		"										\n"
		"	msr psp, r0							\n"
		"	bx r14								\n"
		"										\n"
		"	.align 2							\n"
		"pxCurrentTCBConst: .word pxCurrentTCB	\n"
		::"i"(configMAX_SYSCALL_INTERRUPT_PRIORITY)
	);
}
/*-----------------------------------------------------------*/

void xPortSysTickHandler( void )
{
unsigned long ulDummy;

	ulDummy = portSET_INTERRUPT_MASK_FROM_ISR();
	{
		/* Increment the RTOS tick. */
		if( xTaskIncrementTick() != pdFALSE )
		{
			/* Pend a context switch. */
			*(portNVIC_INT_CTRL) = portNVIC_PENDSVSET;
		}
	}
	portCLEAR_INTERRUPT_MASK_FROM_ISR( ulDummy );
}
/*-----------------------------------------------------------*/

/*
 * Setup the systick timer to generate the tick interrupts at the required
 * frequency.
 */
static void prvSetupTimerInterrupt( void )
{
	/* Configure SysTick to interrupt at the requested rate. */
	*(portNVIC_SYSTICK_LOAD) = ( configCPU_CLOCK_HZ / configTICK_RATE_HZ ) - 1UL;
	*(portNVIC_SYSTICK_CTRL) = portNVIC_SYSTICK_CLK | portNVIC_SYSTICK_INT | portNVIC_SYSTICK_ENABLE;
}
/*-----------------------------------------------------------*/

static void prvSetupMPU( void )
{
extern unsigned long __privileged_functions_end__[];
extern unsigned long __FLASH_segment_start__[];
extern unsigned long __FLASH_segment_end__[];
extern unsigned long __privileged_data_start__[];
extern unsigned long __privileged_data_end__[];

	/* Check the expected MPU is present. */
	if( *portMPU_TYPE == portEXPECTED_MPU_TYPE_VALUE )
	{
		/* First setup the entire flash for unprivileged read only access. */
        *portMPU_REGION_BASE_ADDRESS =	( ( unsigned long ) __FLASH_segment_start__ ) | /* Base address. */
										( portMPU_REGION_VALID ) |
										( portUNPRIVILEGED_FLASH_REGION );

		*portMPU_REGION_ATTRIBUTE =		( portMPU_REGION_READ_ONLY ) |
										( portMPU_REGION_CACHEABLE_BUFFERABLE ) |
										( prvGetMPURegionSizeSetting( ( unsigned long ) __FLASH_segment_end__ - ( unsigned long ) __FLASH_segment_start__ ) ) |
										( portMPU_REGION_ENABLE );

		/* Setup the first 16K for privileged only access (even though less
		than 10K is actually being used).  This is where the kernel code is
		placed. */
        *portMPU_REGION_BASE_ADDRESS =	( ( unsigned long ) __FLASH_segment_start__ ) | /* Base address. */
										( portMPU_REGION_VALID ) |
										( portPRIVILEGED_FLASH_REGION );

		*portMPU_REGION_ATTRIBUTE =		( portMPU_REGION_PRIVILEGED_READ_ONLY ) |
										( portMPU_REGION_CACHEABLE_BUFFERABLE ) |
										( prvGetMPURegionSizeSetting( ( unsigned long ) __privileged_functions_end__ - ( unsigned long ) __FLASH_segment_start__ ) ) |
										( portMPU_REGION_ENABLE );

		/* Setup the privileged data RAM region.  This is where the kernel data
		is placed. */
		*portMPU_REGION_BASE_ADDRESS =	( ( unsigned long ) __privileged_data_start__ ) | /* Base address. */
										( portMPU_REGION_VALID ) |
										( portPRIVILEGED_RAM_REGION );

		*portMPU_REGION_ATTRIBUTE =		( portMPU_REGION_PRIVILEGED_READ_WRITE ) |
										( portMPU_REGION_CACHEABLE_BUFFERABLE ) |
										prvGetMPURegionSizeSetting( ( unsigned long ) __privileged_data_end__ - ( unsigned long ) __privileged_data_start__ ) |
										( portMPU_REGION_ENABLE );

		/* By default allow everything to access the general peripherals.  The
		system peripherals and registers are protected. */
		*portMPU_REGION_BASE_ADDRESS =	( portPERIPHERALS_START_ADDRESS ) |
										( portMPU_REGION_VALID ) |
										( portGENERAL_PERIPHERALS_REGION );

		*portMPU_REGION_ATTRIBUTE =		( portMPU_REGION_READ_WRITE | portMPU_REGION_EXECUTE_NEVER ) |
										( prvGetMPURegionSizeSetting( portPERIPHERALS_END_ADDRESS - portPERIPHERALS_START_ADDRESS ) ) |
										( portMPU_REGION_ENABLE );

		/* Enable the memory fault exception. */
		*portNVIC_SYS_CTRL_STATE |= portNVIC_MEM_FAULT_ENABLE;

		/* Enable the MPU with the background region configured. */
		*portMPU_CTRL |= ( portMPU_ENABLE | portMPU_BACKGROUND_ENABLE );
	}
}
/*-----------------------------------------------------------*/

static unsigned long prvGetMPURegionSizeSetting( unsigned long ulActualSizeInBytes )
{
unsigned long ulRegionSize, ulReturnValue = 4;

	/* 32 is the smallest region size, 31 is the largest valid value for
	ulReturnValue. */
	for( ulRegionSize = 32UL; ulReturnValue < 31UL; ( ulRegionSize <<= 1UL ) )
	{
		if( ulActualSizeInBytes <= ulRegionSize )
		{
			break;
		}
		else
		{
			ulReturnValue++;
		}
	}

	/* Shift the code by one before returning so it can be written directly
	into the the correct bit position of the attribute register. */
	return ( ulReturnValue << 1UL );
}
/*-----------------------------------------------------------*/

static portBASE_TYPE prvRaisePrivilege( void )
{
	__asm volatile
	(
		"	mrs r0, control						\n"
		"	tst r0, #1							\n" /* Is the task running privileged? */
		"	itte ne								\n"
		"	movne r0, #0						\n" /* CONTROL[0]!=0, return false. */
		"	svcne %0							\n" /* Switch to privileged. */
		"	moveq r0, #1						\n" /* CONTROL[0]==0, return true. */
		"	bx lr								\n"
		:: "i" (portSVC_RAISE_PRIVILEGE) : "r0"
	);

	return 0;
}
/*-----------------------------------------------------------*/

void vPortStoreTaskMPUSettings( xMPU_SETTINGS *xMPUSettings, const struct xMEMORY_REGION * const xRegions, portSTACK_TYPE *pxBottomOfStack, unsigned short usStackDepth )
{
extern unsigned long __SRAM_segment_start__[];
extern unsigned long __SRAM_segment_end__[];
extern unsigned long __privileged_data_start__[];
extern unsigned long __privileged_data_end__[];
long lIndex;
unsigned long ul;

	if( xRegions == NULL )
	{
		/* No MPU regions are specified so allow access to all RAM. */
        xMPUSettings->xRegion[ 0 ].ulRegionBaseAddress =
				( ( unsigned long ) __SRAM_segment_start__ ) | /* Base address. */
				( portMPU_REGION_VALID ) |
				( portSTACK_REGION );

		xMPUSettings->xRegion[ 0 ].ulRegionAttribute =
				( portMPU_REGION_READ_WRITE ) |
				( portMPU_REGION_CACHEABLE_BUFFERABLE ) |
				( prvGetMPURegionSizeSetting( ( unsigned long ) __SRAM_segment_end__ - ( unsigned long ) __SRAM_segment_start__ ) ) |
				( portMPU_REGION_ENABLE );

		/* Re-instate the privileged only RAM region as xRegion[ 0 ] will have
		just removed the privileged only parameters. */
		xMPUSettings->xRegion[ 1 ].ulRegionBaseAddress =
				( ( unsigned long ) __privileged_data_start__ ) | /* Base address. */
				( portMPU_REGION_VALID ) |
				( portSTACK_REGION + 1 );

		xMPUSettings->xRegion[ 1 ].ulRegionAttribute =
				( portMPU_REGION_PRIVILEGED_READ_WRITE ) |
				( portMPU_REGION_CACHEABLE_BUFFERABLE ) |
				prvGetMPURegionSizeSetting( ( unsigned long ) __privileged_data_end__ - ( unsigned long ) __privileged_data_start__ ) |
				( portMPU_REGION_ENABLE );

		/* Invalidate all other regions. */
		for( ul = 2; ul <= portNUM_CONFIGURABLE_REGIONS; ul++ )
		{
			xMPUSettings->xRegion[ ul ].ulRegionBaseAddress = ( portSTACK_REGION + ul ) | portMPU_REGION_VALID;
			xMPUSettings->xRegion[ ul ].ulRegionAttribute = 0UL;
		}
	}
	else
	{
		/* This function is called automatically when the task is created - in
		which case the stack region parameters will be valid.  At all other
		times the stack parameters will not be valid and it is assumed that the
		stack region has already been configured. */
		if( usStackDepth > 0 )
		{
			/* Define the region that allows access to the stack. */
			xMPUSettings->xRegion[ 0 ].ulRegionBaseAddress =
					( ( unsigned long ) pxBottomOfStack ) |
					( portMPU_REGION_VALID ) |
					( portSTACK_REGION ); /* Region number. */

			xMPUSettings->xRegion[ 0 ].ulRegionAttribute =
					( portMPU_REGION_READ_WRITE ) | /* Read and write. */
					( prvGetMPURegionSizeSetting( ( unsigned long ) usStackDepth * ( unsigned long ) sizeof( portSTACK_TYPE ) ) ) |
					( portMPU_REGION_CACHEABLE_BUFFERABLE ) |
					( portMPU_REGION_ENABLE );
		}

		lIndex = 0;

		for( ul = 1; ul <= portNUM_CONFIGURABLE_REGIONS; ul++ )
		{
			if( ( xRegions[ lIndex ] ).ulLengthInBytes > 0UL )
			{
				/* Translate the generic region definition contained in
				xRegions into the CM3 specific MPU settings that are then
				stored in xMPUSettings. */
				xMPUSettings->xRegion[ ul ].ulRegionBaseAddress =
						( ( unsigned long ) xRegions[ lIndex ].pvBaseAddress ) |
						( portMPU_REGION_VALID ) |
						( portSTACK_REGION + ul ); /* Region number. */

				xMPUSettings->xRegion[ ul ].ulRegionAttribute =
						( prvGetMPURegionSizeSetting( xRegions[ lIndex ].ulLengthInBytes ) ) |
						( xRegions[ lIndex ].ulParameters ) |
						( portMPU_REGION_ENABLE );
			}
			else
			{
				/* Invalidate the region. */
				xMPUSettings->xRegion[ ul ].ulRegionBaseAddress = ( portSTACK_REGION + ul ) | portMPU_REGION_VALID;
				xMPUSettings->xRegion[ ul ].ulRegionAttribute = 0UL;
			}

			lIndex++;
		}
	}
}
/*-----------------------------------------------------------*/

signed portBASE_TYPE MPU_xTaskGenericCreate( pdTASK_CODE pvTaskCode, const signed char * const pcName, unsigned short usStackDepth, void *pvParameters, unsigned portBASE_TYPE uxPriority, xTaskHandle *pxCreatedTask, portSTACK_TYPE *puxStackBuffer, const xMemoryRegion * const xRegions )
{
signed portBASE_TYPE xReturn;
portBASE_TYPE xRunningPrivileged = prvRaisePrivilege();

	xReturn = xTaskGenericCreate( pvTaskCode, pcName, usStackDepth, pvParameters, uxPriority, pxCreatedTask, puxStackBuffer, xRegions );
	portRESET_PRIVILEGE( xRunningPrivileged );
	return xReturn;
}
/*-----------------------------------------------------------*/

void MPU_vTaskAllocateMPURegions( xTaskHandle xTask, const xMemoryRegion * const xRegions )
{
portBASE_TYPE xRunningPrivileged = prvRaisePrivilege();

	vTaskAllocateMPURegions( xTask, xRegions );
	portRESET_PRIVILEGE( xRunningPrivileged );
}
/*-----------------------------------------------------------*/

#if ( INCLUDE_vTaskDelete == 1 )
	void MPU_vTaskDelete( xTaskHandle pxTaskToDelete )
	{
    portBASE_TYPE xRunningPrivileged = prvRaisePrivilege();

		vTaskDelete( pxTaskToDelete );
        portRESET_PRIVILEGE( xRunningPrivileged );
	}
#endif
/*-----------------------------------------------------------*/

#if ( INCLUDE_vTaskDelayUntil == 1 )
	void MPU_vTaskDelayUntil( portTickType * const pxPreviousWakeTime, portTickType xTimeIncrement )
	{
    portBASE_TYPE xRunningPrivileged = prvRaisePrivilege();

		vTaskDelayUntil( pxPreviousWakeTime, xTimeIncrement );
        portRESET_PRIVILEGE( xRunningPrivileged );
	}
#endif
/*-----------------------------------------------------------*/

#if ( INCLUDE_vTaskDelay == 1 )
	void MPU_vTaskDelay( portTickType xTicksToDelay )
	{
    portBASE_TYPE xRunningPrivileged = prvRaisePrivilege();

		vTaskDelay( xTicksToDelay );
        portRESET_PRIVILEGE( xRunningPrivileged );
	}
#endif
/*-----------------------------------------------------------*/

#if ( INCLUDE_uxTaskPriorityGet == 1 )
	unsigned portBASE_TYPE MPU_uxTaskPriorityGet( xTaskHandle pxTask )
	{
	unsigned portBASE_TYPE uxReturn;
    portBASE_TYPE xRunningPrivileged = prvRaisePrivilege();

		uxReturn = uxTaskPriorityGet( pxTask );
        portRESET_PRIVILEGE( xRunningPrivileged );
		return uxReturn;
	}
#endif
/*-----------------------------------------------------------*/

#if ( INCLUDE_vTaskPrioritySet == 1 )
	void MPU_vTaskPrioritySet( xTaskHandle pxTask, unsigned portBASE_TYPE uxNewPriority )
	{
    portBASE_TYPE xRunningPrivileged = prvRaisePrivilege();

		vTaskPrioritySet( pxTask, uxNewPriority );
        portRESET_PRIVILEGE( xRunningPrivileged );
	}
#endif
/*-----------------------------------------------------------*/

#if ( INCLUDE_eTaskGetState == 1 )
	eTaskState MPU_eTaskGetState( xTaskHandle pxTask )
	{
    portBASE_TYPE xRunningPrivileged = prvRaisePrivilege();
	eTaskState eReturn;

		eReturn = eTaskGetState( pxTask );
        portRESET_PRIVILEGE( xRunningPrivileged );
		return eReturn;
	}
#endif
/*-----------------------------------------------------------*/

#if ( INCLUDE_xTaskGetIdleTaskHandle == 1 )
	xTaskHandle MPU_xTaskGetIdleTaskHandle( void )
	{
	xTaskHandle xReturn;
    portBASE_TYPE xRunningPrivileged = prvRaisePrivilege();

		xReturn = xTaskGetIdleTaskHandle();
        portRESET_PRIVILEGE( xRunningPrivileged );
		return eReturn;
	}
#endif
/*-----------------------------------------------------------*/

#if ( INCLUDE_vTaskSuspend == 1 )
	void MPU_vTaskSuspend( xTaskHandle pxTaskToSuspend )
	{
    portBASE_TYPE xRunningPrivileged = prvRaisePrivilege();

		vTaskSuspend( pxTaskToSuspend );
        portRESET_PRIVILEGE( xRunningPrivileged );
	}
#endif
/*-----------------------------------------------------------*/

#if ( INCLUDE_vTaskSuspend == 1 )
	signed portBASE_TYPE MPU_xTaskIsTaskSuspended( xTaskHandle xTask )
	{
	signed portBASE_TYPE xReturn;
    portBASE_TYPE xRunningPrivileged = prvRaisePrivilege();

		xReturn = xTaskIsTaskSuspended( xTask );
        portRESET_PRIVILEGE( xRunningPrivileged );
		return xReturn;
	}
#endif
/*-----------------------------------------------------------*/

#if ( INCLUDE_vTaskSuspend == 1 )
	void MPU_vTaskResume( xTaskHandle pxTaskToResume )
	{
    portBASE_TYPE xRunningPrivileged = prvRaisePrivilege();

		vTaskResume( pxTaskToResume );
        portRESET_PRIVILEGE( xRunningPrivileged );
	}
#endif
/*-----------------------------------------------------------*/

void MPU_vTaskSuspendAll( void )
{
portBASE_TYPE xRunningPrivileged = prvRaisePrivilege();

	vTaskSuspendAll();
    portRESET_PRIVILEGE( xRunningPrivileged );
}
/*-----------------------------------------------------------*/

signed portBASE_TYPE MPU_xTaskResumeAll( void )
{
signed portBASE_TYPE xReturn;
portBASE_TYPE xRunningPrivileged = prvRaisePrivilege();

	xReturn = xTaskResumeAll();
    portRESET_PRIVILEGE( xRunningPrivileged );
    return xReturn;
}
/*-----------------------------------------------------------*/

portTickType MPU_xTaskGetTickCount( void )
{
portTickType xReturn;
portBASE_TYPE xRunningPrivileged = prvRaisePrivilege();

	xReturn = xTaskGetTickCount();
    portRESET_PRIVILEGE( xRunningPrivileged );
	return xReturn;
}
/*-----------------------------------------------------------*/

unsigned portBASE_TYPE MPU_uxTaskGetNumberOfTasks( void )
{
unsigned portBASE_TYPE uxReturn;
portBASE_TYPE xRunningPrivileged = prvRaisePrivilege();

	uxReturn = uxTaskGetNumberOfTasks();
    portRESET_PRIVILEGE( xRunningPrivileged );
	return uxReturn;
}
/*-----------------------------------------------------------*/

#if ( configUSE_TRACE_FACILITY == 1 )
	void MPU_vTaskList( signed char *pcWriteBuffer )
	{
	portBASE_TYPE xRunningPrivileged = prvRaisePrivilege();

		vTaskList( pcWriteBuffer );
		portRESET_PRIVILEGE( xRunningPrivileged );
	}
#endif
/*-----------------------------------------------------------*/

#if ( configGENERATE_RUN_TIME_STATS == 1 )
	void MPU_vTaskGetRunTimeStats( signed char *pcWriteBuffer )
	{
    portBASE_TYPE xRunningPrivileged = prvRaisePrivilege();

		vTaskGetRunTimeStats( pcWriteBuffer );
        portRESET_PRIVILEGE( xRunningPrivileged );
	}
#endif
/*-----------------------------------------------------------*/

#if ( configUSE_APPLICATION_TASK_TAG == 1 )
	void MPU_vTaskSetApplicationTaskTag( xTaskHandle xTask, pdTASK_HOOK_CODE pxTagValue )
	{
    portBASE_TYPE xRunningPrivileged = prvRaisePrivilege();

		vTaskSetApplicationTaskTag( xTask, pxTagValue );
        portRESET_PRIVILEGE( xRunningPrivileged );
	}
#endif
/*-----------------------------------------------------------*/

#if ( configUSE_APPLICATION_TASK_TAG == 1 )
	pdTASK_HOOK_CODE MPU_xTaskGetApplicationTaskTag( xTaskHandle xTask )
	{
	pdTASK_HOOK_CODE xReturn;
    portBASE_TYPE xRunningPrivileged = prvRaisePrivilege();

		xReturn = xTaskGetApplicationTaskTag( xTask );
        portRESET_PRIVILEGE( xRunningPrivileged );
		return xReturn;
	}
#endif
/*-----------------------------------------------------------*/

#if ( configUSE_APPLICATION_TASK_TAG == 1 )
	portBASE_TYPE MPU_xTaskCallApplicationTaskHook( xTaskHandle xTask, void *pvParameter )
	{
	portBASE_TYPE xReturn;
    portBASE_TYPE xRunningPrivileged = prvRaisePrivilege();

		xReturn = xTaskCallApplicationTaskHook( xTask, pvParameter );
        portRESET_PRIVILEGE( xRunningPrivileged );
		return xReturn;
	}
#endif
/*-----------------------------------------------------------*/

#if ( INCLUDE_uxTaskGetStackHighWaterMark == 1 )
	unsigned portBASE_TYPE MPU_uxTaskGetStackHighWaterMark( xTaskHandle xTask )
	{
	unsigned portBASE_TYPE uxReturn;
    portBASE_TYPE xRunningPrivileged = prvRaisePrivilege();

		uxReturn = uxTaskGetStackHighWaterMark( xTask );
        portRESET_PRIVILEGE( xRunningPrivileged );
		return uxReturn;
	}
#endif
/*-----------------------------------------------------------*/

#if ( INCLUDE_xTaskGetCurrentTaskHandle == 1 )
	xTaskHandle MPU_xTaskGetCurrentTaskHandle( void )
	{
	xTaskHandle xReturn;
    portBASE_TYPE xRunningPrivileged = prvRaisePrivilege();

		xReturn = xTaskGetCurrentTaskHandle();
        portRESET_PRIVILEGE( xRunningPrivileged );
		return xReturn;
	}
#endif
/*-----------------------------------------------------------*/

#if ( INCLUDE_xTaskGetSchedulerState == 1 )
	portBASE_TYPE MPU_xTaskGetSchedulerState( void )
	{
	portBASE_TYPE xReturn;
    portBASE_TYPE xRunningPrivileged = prvRaisePrivilege();

		xReturn = xTaskGetSchedulerState();
        portRESET_PRIVILEGE( xRunningPrivileged );
		return xReturn;
	}
#endif
/*-----------------------------------------------------------*/

xQueueHandle MPU_xQueueGenericCreate( unsigned portBASE_TYPE uxQueueLength, unsigned portBASE_TYPE uxItemSize, unsigned char ucQueueType )
{
xQueueHandle xReturn;
portBASE_TYPE xRunningPrivileged = prvRaisePrivilege();

	xReturn = xQueueGenericCreate( uxQueueLength, uxItemSize, ucQueueType );
	portRESET_PRIVILEGE( xRunningPrivileged );
	return xReturn;
}
/*-----------------------------------------------------------*/

portBASE_TYPE MPU_xQueueGenericReset( xQueueHandle pxQueue, portBASE_TYPE xNewQueue )
{
portBASE_TYPE xReturn;
portBASE_TYPE xRunningPrivileged = prvRaisePrivilege();

	xReturn = xQueueGenericReset( pxQueue, xNewQueue );
	portRESET_PRIVILEGE( xRunningPrivileged );
	return xReturn;
}
/*-----------------------------------------------------------*/

signed portBASE_TYPE MPU_xQueueGenericSend( xQueueHandle xQueue, const void * const pvItemToQueue, portTickType xTicksToWait, portBASE_TYPE xCopyPosition )
{
signed portBASE_TYPE xReturn;
portBASE_TYPE xRunningPrivileged = prvRaisePrivilege();

	xReturn = xQueueGenericSend( xQueue, pvItemToQueue, xTicksToWait, xCopyPosition );
	portRESET_PRIVILEGE( xRunningPrivileged );
	return xReturn;
}
/*-----------------------------------------------------------*/

unsigned portBASE_TYPE MPU_uxQueueMessagesWaiting( const xQueueHandle pxQueue )
{
portBASE_TYPE xRunningPrivileged = prvRaisePrivilege();
unsigned portBASE_TYPE uxReturn;

	uxReturn = uxQueueMessagesWaiting( pxQueue );
	portRESET_PRIVILEGE( xRunningPrivileged );
	return uxReturn;
}
/*-----------------------------------------------------------*/

signed portBASE_TYPE MPU_xQueueGenericReceive( xQueueHandle pxQueue, void * const pvBuffer, portTickType xTicksToWait, portBASE_TYPE xJustPeeking )
{
portBASE_TYPE xRunningPrivileged = prvRaisePrivilege();
signed portBASE_TYPE xReturn;

	xReturn = xQueueGenericReceive( pxQueue, pvBuffer, xTicksToWait, xJustPeeking );
	portRESET_PRIVILEGE( xRunningPrivileged );
	return xReturn;
}
/*-----------------------------------------------------------*/

#if ( configUSE_MUTEXES == 1 )
	xQueueHandle MPU_xQueueCreateMutex( void )
	{
    xQueueHandle xReturn;
	portBASE_TYPE xRunningPrivileged = prvRaisePrivilege();

		xReturn = xQueueCreateMutex( queueQUEUE_TYPE_MUTEX );
		portRESET_PRIVILEGE( xRunningPrivileged );
		return xReturn;
	}
#endif
/*-----------------------------------------------------------*/

#if configUSE_COUNTING_SEMAPHORES == 1
	xQueueHandle MPU_xQueueCreateCountingSemaphore( unsigned portBASE_TYPE uxCountValue, unsigned portBASE_TYPE uxInitialCount )
	{
    xQueueHandle xReturn;
	portBASE_TYPE xRunningPrivileged = prvRaisePrivilege();

		xReturn = xQueueCreateCountingSemaphore( uxCountValue, uxInitialCount );
		portRESET_PRIVILEGE( xRunningPrivileged );
		return xReturn;
	}
#endif
/*-----------------------------------------------------------*/

#if ( configUSE_MUTEXES == 1 )
	portBASE_TYPE MPU_xQueueTakeMutexRecursive( xQueueHandle xMutex, portTickType xBlockTime )
	{
	portBASE_TYPE xReturn;
	portBASE_TYPE xRunningPrivileged = prvRaisePrivilege();

		xReturn = xQueueTakeMutexRecursive( xMutex, xBlockTime );
		portRESET_PRIVILEGE( xRunningPrivileged );
		return xReturn;
	}
#endif
/*-----------------------------------------------------------*/

#if ( configUSE_MUTEXES == 1 )
	portBASE_TYPE MPU_xQueueGiveMutexRecursive( xQueueHandle xMutex )
	{
	portBASE_TYPE xReturn;
	portBASE_TYPE xRunningPrivileged = prvRaisePrivilege();

		xReturn = xQueueGiveMutexRecursive( xMutex );
		portRESET_PRIVILEGE( xRunningPrivileged );
		return xReturn;
	}
#endif
/*-----------------------------------------------------------*/

#if ( configUSE_QUEUE_SETS == 1 )
	xQueueSetHandle MPU_xQueueCreateSet( unsigned portBASE_TYPE uxEventQueueLength )
	{
	xQueueSetHandle xReturn;
	portBASE_TYPE xRunningPrivileged = prvRaisePrivilege();

		xReturn = xQueueCreateSet( uxEventQueueLength );
		portRESET_PRIVILEGE( xRunningPrivileged );
		return xReturn;
	}
#endif
/*-----------------------------------------------------------*/

#if ( configUSE_QUEUE_SETS == 1 )
	xQueueSetMemberHandle MPU_xQueueSelectFromSet( xQueueSetHandle xQueueSet, portTickType xBlockTimeTicks )
	{
	xQueueSetMemberHandle xReturn;
	portBASE_TYPE xRunningPrivileged = prvRaisePrivilege();

		xReturn = xQueueSelectFromSet( xQueueSet, xBlockTimeTicks );
		portRESET_PRIVILEGE( xRunningPrivileged );
		return xReturn;
	}
#endif
/*-----------------------------------------------------------*/

#if ( configUSE_QUEUE_SETS == 1 )
	portBASE_TYPE MPU_xQueueAddToSet( xQueueSetMemberHandle xQueueOrSemaphore, xQueueSetHandle xQueueSet )
	{
	portBASE_TYPE xReturn;
	portBASE_TYPE xRunningPrivileged = prvRaisePrivilege();

		xReturn = xQueueAddToSet( xQueueOrSemaphore, xQueueSet );
		portRESET_PRIVILEGE( xRunningPrivileged );
		return xReturn;
	}
#endif
/*-----------------------------------------------------------*/

#if ( configUSE_QUEUE_SETS == 1 )
	portBASE_TYPE MPU_xQueueRemoveFromSet( xQueueSetMemberHandle xQueueOrSemaphore, xQueueSetHandle xQueueSet )
	{
	portBASE_TYPE xReturn;
	portBASE_TYPE xRunningPrivileged = prvRaisePrivilege();

		xReturn = xQueueRemoveFromSet( xQueueOrSemaphore, xQueueSet );
		portRESET_PRIVILEGE( xRunningPrivileged );
		return xReturn;
	}
#endif
/*-----------------------------------------------------------*/

#if configUSE_ALTERNATIVE_API == 1
	signed portBASE_TYPE MPU_xQueueAltGenericSend( xQueueHandle pxQueue, const void * const pvItemToQueue, portTickType xTicksToWait, portBASE_TYPE xCopyPosition )
	{
   	signed portBASE_TYPE xReturn;
	portBASE_TYPE xRunningPrivileged = prvRaisePrivilege();

		xReturn = 	signed portBASE_TYPE xQueueAltGenericSend( pxQueue, pvItemToQueue, xTicksToWait, xCopyPosition );
		portRESET_PRIVILEGE( xRunningPrivileged );
		return xReturn;
	}
#endif
/*-----------------------------------------------------------*/

#if configUSE_ALTERNATIVE_API == 1
	signed portBASE_TYPE MPU_xQueueAltGenericReceive( xQueueHandle pxQueue, void * const pvBuffer, portTickType xTicksToWait, portBASE_TYPE xJustPeeking )
	{
    signed portBASE_TYPE xReturn;
	portBASE_TYPE xRunningPrivileged = prvRaisePrivilege();

		xReturn = xQueueAltGenericReceive( pxQueue, pvBuffer, xTicksToWait, xJustPeeking );
		portRESET_PRIVILEGE( xRunningPrivileged );
		return xReturn;
	}
#endif
/*-----------------------------------------------------------*/

#if configQUEUE_REGISTRY_SIZE > 0
	void MPU_vQueueAddToRegistry( xQueueHandle xQueue, signed char *pcName )
	{
	portBASE_TYPE xRunningPrivileged = prvRaisePrivilege();

		vQueueAddToRegistry( xQueue, pcName );

		portRESET_PRIVILEGE( xRunningPrivileged );
	}
#endif
/*-----------------------------------------------------------*/

void MPU_vQueueDelete( xQueueHandle xQueue )
{
portBASE_TYPE xRunningPrivileged = prvRaisePrivilege();

	vQueueDelete( xQueue );

	portRESET_PRIVILEGE( xRunningPrivileged );
}
/*-----------------------------------------------------------*/

void *MPU_pvPortMalloc( size_t xSize )
{
void *pvReturn;
portBASE_TYPE xRunningPrivileged = prvRaisePrivilege();

	pvReturn = pvPortMalloc( xSize );

	portRESET_PRIVILEGE( xRunningPrivileged );

	return pvReturn;
}
/*-----------------------------------------------------------*/

void MPU_vPortFree( void *pv )
{
portBASE_TYPE xRunningPrivileged = prvRaisePrivilege();

	vPortFree( pv );

	portRESET_PRIVILEGE( xRunningPrivileged );
}
/*-----------------------------------------------------------*/

void MPU_vPortInitialiseBlocks( void )
{
portBASE_TYPE xRunningPrivileged = prvRaisePrivilege();

	vPortInitialiseBlocks();

	portRESET_PRIVILEGE( xRunningPrivileged );
}
/*-----------------------------------------------------------*/

size_t MPU_xPortGetFreeHeapSize( void )
{
size_t xReturn;
portBASE_TYPE xRunningPrivileged = prvRaisePrivilege();

	xReturn = xPortGetFreeHeapSize();

	portRESET_PRIVILEGE( xRunningPrivileged );

	return xReturn;
}

