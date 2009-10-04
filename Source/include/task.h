/*
	FreeRTOS V5.4.2 - Copyright (C) 2009 Real Time Engineers Ltd.

	This file is part of the FreeRTOS distribution.

	FreeRTOS is free software; you can redistribute it and/or modify it	under
	the terms of the GNU General Public License (version 2) as published by the
	Free Software Foundation and modified by the FreeRTOS exception.
	**NOTE** The exception to the GPL is included to allow you to distribute a
	combined work that includes FreeRTOS without being obliged to provide the
	source code for proprietary components outside of the FreeRTOS kernel.
	Alternative commercial license and support terms are also available upon
	request.  See the licensing section of http://www.FreeRTOS.org for full
	license details.

	FreeRTOS is distributed in the hope that it will be useful,	but WITHOUT
	ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
	FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
	more details.

	You should have received a copy of the GNU General Public License along
	with FreeRTOS; if not, write to the Free Software Foundation, Inc., 59
	Temple Place, Suite 330, Boston, MA  02111-1307  USA.


	***************************************************************************
	*																		 *
	* Looking for a quick start?  Then check out the FreeRTOS eBook!		  *
	* See http://www.FreeRTOS.org/Documentation for details				   *
	*																		 *
	***************************************************************************

	1 tab == 4 spaces!

	Please ensure to read the configuration and relevant port sections of the
	online documentation.

	http://www.FreeRTOS.org - Documentation, latest information, license and
	contact details.

	http://www.SafeRTOS.com - A version that is certified for use in safety
	critical systems.

	http://www.OpenRTOS.com - Commercial support, development, porting,
	licensing and training services.
*/


#ifndef INC_FREERTOS_H
	#error "#include FreeRTOS.h" must appear in source files before "#include task.h"
#endif



#ifndef TASK_H
#define TASK_H

#include "portable.h"
#include "list.h"

#ifdef __cplusplus
extern "C" {
#endif

/*-----------------------------------------------------------
 * MACROS AND DEFINITIONS
 *----------------------------------------------------------*/

#define tskKERNEL_VERSION_NUMBER "V5.4.2"

/**
 * task. h
 *
 * Type by which tasks are referenced.  For example, a call to xTaskCreate
 * returns (via a pointer parameter) an xTaskHandle variable that can then
 * be used as a parameter to vTaskDelete to delete the task.
 *
 * \page xTaskHandle xTaskHandle
 * \ingroup Tasks
 */
typedef void * xTaskHandle;

/*
 * Used internally only.
 */
typedef struct xTIME_OUT
{
	portBASE_TYPE xOverflowCount;
	portTickType  xTimeOnEntering;
} xTimeOutType;

/*
 * Defines the memory ranges allocated to the task when an MPU is used.
 */
typedef struct xMEMORY_REGION
{
	void *pvBaseAddress;
	unsigned long ulLengthInBytes;
	unsigned long ulParameters;
} xMemoryRegion;

/*
 * Parameters required to create an MPU protected task.
 */
typedef struct xTASK_PARAMTERS
{
	pdTASK_CODE pvTaskCode;
	const signed char * const pcName;
	unsigned short usStackDepth;
	void *pvParameters;
	unsigned portBASE_TYPE uxPriority;
	portSTACK_TYPE *puxStackBuffer;
	xMemoryRegion xRegions[ portNUM_CONFIGURABLE_REGIONS ];
} xTaskParameters;

/*
 * Defines the priority used by the idle task.  This must not be modified.
 *
 * \ingroup TaskUtils
 */
#define tskIDLE_PRIORITY			( ( unsigned portBASE_TYPE ) 0 )

/**
 * task. h
 *
 * Macro for forcing a context switch.
 *
 * \page taskYIELD taskYIELD
 * \ingroup SchedulerControl
 */
#define taskYIELD()					portYIELD()

/**
 * task. h
 *
 * Macro to mark the start of a critical code region.  Preemptive context
 * switches cannot occur when in a critical region.
 *
 * NOTE: This may alter the stack (depending on the portable implementation)
 * so must be used with care!
 *
 * \page taskENTER_CRITICAL taskENTER_CRITICAL
 * \ingroup SchedulerControl
 */
#define taskENTER_CRITICAL()		portENTER_CRITICAL()

/**
 * task. h
 *
 * Macro to mark the end of a critical code region.  Preemptive context
 * switches cannot occur when in a critical region.
 *
 * NOTE: This may alter the stack (depending on the portable implementation)
 * so must be used with care!
 *
 * \page taskEXIT_CRITICAL taskEXIT_CRITICAL
 * \ingroup SchedulerControl
 */
#define taskEXIT_CRITICAL()			portEXIT_CRITICAL()

/**
 * task. h
 *
 * Macro to disable all maskable interrupts.
 *
 * \page taskDISABLE_INTERRUPTS taskDISABLE_INTERRUPTS
 * \ingroup SchedulerControl
 */
#define taskDISABLE_INTERRUPTS()	portDISABLE_INTERRUPTS()

/**
 * task. h
 *
 * Macro to enable microcontroller interrupts.
 *
 * \page taskENABLE_INTERRUPTS taskENABLE_INTERRUPTS
 * \ingroup SchedulerControl
 */
#define taskENABLE_INTERRUPTS()		portENABLE_INTERRUPTS()

/* Definitions returned by xTaskGetSchedulerState(). */
#define taskSCHEDULER_NOT_STARTED	0
#define taskSCHEDULER_RUNNING		1
#define taskSCHEDULER_SUSPENDED		2

/*-----------------------------------------------------------
 * TASK CREATION API
 *----------------------------------------------------------*/

/**
 * task. h
 *<pre>
 portBASE_TYPE xTaskCreate(
							  pdTASK_CODE pvTaskCode,
							  const char * const pcName,
							  unsigned short usStackDepth,
							  void *pvParameters,
							  unsigned portBASE_TYPE uxPriority,
							  xTaskHandle *pvCreatedTask
						  );</pre>
 *
 * Create a new task and add it to the list of tasks that are ready to run.
 * 
 * xTaskCreate() can only be used to create a task that has unrestricted
 * access to the entire microcontroller memory map.  Systems that include MPU
 * support can alternatively create an MPU constrained task using 
 * xTaskCreateRestricted().
 *
 * @param pvTaskCode Pointer to the task entry function.  Tasks
 * must be implemented to never return (i.e. continuous loop).
 *
 * @param pcName A descriptive name for the task.  This is mainly used to
 * facilitate debugging.  Max length defined by tskMAX_TASK_NAME_LEN - default
 * is 16.
 *
 * @param usStackDepth The size of the task stack specified as the number of
 * variables the stack can hold - not the number of bytes.  For example, if
 * the stack is 16 bits wide and usStackDepth is defined as 100, 200 bytes
 * will be allocated for stack storage.
 *
 * @param pvParameters Pointer that will be used as the parameter for the task
 * being created.
 *
 * @param uxPriority The priority at which the task should run.  Systems that
 * include MPU support can optionally create tasks in a privileged (system)
 * mode by setting bit portPRIVILEGE_BIT of the priority parameter.  For
 * example, to create a privileged task at priority 2 the uxPriority parameter
 * should be set to ( 2 | portPRIVILEGE_BIT ).
 *
 * @param pvCreatedTask Used to pass back a handle by which the created task
 * can be referenced.
 *
 * @return pdPASS if the task was successfully created and added to a ready
 * list, otherwise an error code defined in the file errors. h
 *
 * Example usage:
   <pre>
 // Task to be created.
 void vTaskCode( void * pvParameters )
 {
	 for( ;; )
	 {
		 // Task code goes here.
	 }
 }

 // Function that creates a task.
 void vOtherFunction( void )
 {
 static unsigned char ucParameterToPass;
 xTaskHandle xHandle;

	 // Create the task, storing the handle.  Note that the passed parameter ucParameterToPass
	 // must exist for the lifetime of the task, so in this case is declared static.  If it was just an
	 // an automatic stack variable it might no longer exist, or at least have been corrupted, by the time
	 // the new time attempts to access it.
	 xTaskCreate( vTaskCode, "NAME", STACK_SIZE, &ucParameterToPass, tskIDLE_PRIORITY, &xHandle );

	 // Use the handle to delete the task.
	 vTaskDelete( xHandle );
 }
   </pre>
 * \defgroup xTaskCreate xTaskCreate
 * \ingroup Tasks
 */
#define xTaskCreate( pvTaskCode, pcName, usStackDepth, pvParameters, uxPriority, pxCreatedTask ) xTaskGenericCreate( ( pvTaskCode ), ( pcName ), ( usStackDepth ), ( pvParameters ), ( uxPriority ), ( pxCreatedTask ), ( NULL ), ( NULL ) )

/**
 * task. h
 *<pre>
 portBASE_TYPE xTaskCreateRestricted( xTaskParameters *pxTaskDefinition, xTaskHandle pxCreatedTask );</pre>
 *
 * xTaskCreateRestricted() should only be used in systems that include an MPU
 * implementation.
 *
 * Create a new task and add it to the list of tasks that are ready to run.
 * The function parameters define the memory regions and associated access
 * permissions allocated to the task.
 *
 * @param pxTaskDefinition Pointer to a structure that contains a member
 * for each of the normal xTaskCreate() parameters (see the xTaskCreate() API
 * documentation) plus an optional stack buffer and the memory region 
 * definitions.
 *
 * @param pcName A descriptive name for the task.  This is mainly used to
 * facilitate debugging.  Max length defined by tskMAX_TASK_NAME_LEN - default
 * is 16.
 *
 * @param pxCreatedTask Used to pass back a handle by which the created task
 * can be referenced.
 *
 * @return pdPASS if the task was successfully created and added to a ready
 * list, otherwise an error code defined in the file errors. h
 *
 * Example usage:
   <pre>
// Create an xTaskParameters structure that defines the task to be created.
static const xTaskParameters xCheckTaskParameters =
{
	vATask,		// pvTaskCode - the function that implements the task.
	"ATask",	// pcName - just a text name for the task to assist debugging.
	100,		// usStackDepth	- the stack size DEFINED IN WORDS.
	NULL,		// pvParameters - passed into the task function as the function parameters.
	( 1UL | portPRIVILEGE_BIT ),// uxPriority - task priority, set the portPRIVILEGE_BIT if the task should run in a privileged state.
	cStackBuffer,// puxStackBuffer - the buffer to be used as the task stack.

	// xRegions - Allocate up to three separate memory regions for access by
	// the task, with appropriate access permissions.  Different processors have
	// different memory alignment requirements - refer to the FreeRTOS documentation
	// for full information.
	{											
		// Base address					Length	Parameters
        { cReadWriteArray,				32,		portMPU_REGION_READ_WRITE },
        { cReadOnlyArray,				32,		portMPU_REGION_READ_ONLY },
        { cPrivilegedOnlyAccessArray,	128,	portMPU_REGION_PRIVILEGED_READ_WRITE }
	}
};

int main( void )
{
xTaskHandle xHandle;

	// Create a task from the const structure defined above.  The task handle
	// is requested (the second parameter is not NULL) but in this case just for
	// demonstration purposes as its not actually used.
	xTaskCreateRestricted( &xRegTest1Parameters, &xHandle );

	// Start the scheduler.
	vTaskStartScheduler();

	// Will only get here if there was insufficient memory to create the idle
	// task.
	for( ;; );
}
   </pre>
 * \defgroup xTaskCreateRestricted xTaskCreateRestricted
 * \ingroup Tasks
 */
#define xTaskCreateRestricted( x, pxCreatedTask ) xTaskGenericCreate( ((x)->pvTaskCode), ((x)->pcName), ((x)->usStackDepth), ((x)->pvParameters), ((x)->uxPriority), (pxCreatedTask), ((x)->puxStackBuffer), ((x)->xRegions) )

/**
 * task. h
 *<pre>
 void vTaskAllocateMPURegions( xTaskHandle xTask, const xMemoryRegion * const pxRegions );</pre>
 *
 * Memory regions are assigned to a restricted task when the task is created by
 * a call to xTaskCreateRestricted().  These regions can be redefined using
 * vTaskAllocateMPURegions().
 * 
 * @param xTask The handle of the task being updated.
 *
 * @param xRegions A pointer to an xMemoryRegion structure that contains the
 * new memory region definitions.
 *
 * Example usage:
   <pre>
// Define an array of xMemoryRegion structures that configures an MPU region
// allowing read/write access for 1024 bytes starting at the beginning of the
// ucOneKByte array.  The other two of the maximum 3 definable regions are
// unused so set to zero.
static const xMemoryRegion xAltRegions[ portNUM_CONFIGURABLE_REGIONS ] =
{											
	// Base address		Length		Parameters
	{ ucOneKByte,		1024,		portMPU_REGION_READ_WRITE },
	{ 0,				0,			0 },
	{ 0,				0,			0 }
};

void vATask( void *pvParameters )
{
	// This task was created such that it has access to certain regions of
	// memory as defined by the MPU configuration.  At some point it is 
	// desired that these MPU regions are replaced with that defined in the
	// xAltRegions const struct above.  Use a call to vTaskAllocateMPURegions()
	// for this purpose.  NULL is used as the task handle to indicate that this
	// function should modify the MPU regions of the calling task.
	vTaskAllocateMPURegions( NULL, xAltRegions );
	
	// Now the task can continue its function, but from this point on can only
	// access its stack and the ucOneKByte array (unless any other statically
	// defined or shared regions have been declared elsewhere).
}
   </pre>
 * \defgroup xTaskCreateRestricted xTaskCreateRestricted
 * \ingroup Tasks
 */
void vTaskAllocateMPURegions( xTaskHandle xTask, const xMemoryRegion * const pxRegions ) PRIVILEGED_FUNCTION;

/**
 * task. h
 * <pre>void vTaskDelete( xTaskHandle pxTask );</pre>
 *
 * INCLUDE_vTaskDelete must be defined as 1 for this function to be available.
 * See the configuration section for more information.
 *
 * Remove a task from the RTOS real time kernels management.  The task being
 * deleted will be removed from all ready, blocked, suspended and event lists.
 *
 * NOTE:  The idle task is responsible for freeing the kernel allocated
 * memory from tasks that have been deleted.  It is therefore important that
 * the idle task is not starved of microcontroller processing time if your
 * application makes any calls to vTaskDelete ().  Memory allocated by the
 * task code is not automatically freed, and should be freed before the task
 * is deleted.
 *
 * See the demo application file death.c for sample code that utilises
 * vTaskDelete ().
 *
 * @param pxTask The handle of the task to be deleted.  Passing NULL will
 * cause the calling task to be deleted.
 *
 * Example usage:
   <pre>
 void vOtherFunction( void )
 {
 xTaskHandle xHandle;

	 // Create the task, storing the handle.
	 xTaskCreate( vTaskCode, "NAME", STACK_SIZE, NULL, tskIDLE_PRIORITY, &xHandle );

	 // Use the handle to delete the task.
	 vTaskDelete( xHandle );
 }
   </pre>
 * \defgroup vTaskDelete vTaskDelete
 * \ingroup Tasks
 */
void vTaskDelete( xTaskHandle pxTask ) PRIVILEGED_FUNCTION;


/*-----------------------------------------------------------
 * TASK CONTROL API
 *----------------------------------------------------------*/

/**
 * task. h
 * <pre>void vTaskDelay( portTickType xTicksToDelay );</pre>
 *
 * Delay a task for a given number of ticks.  The actual time that the
 * task remains blocked depends on the tick rate.  The constant
 * portTICK_RATE_MS can be used to calculate real time from the tick
 * rate - with the resolution of one tick period.
 *
 * INCLUDE_vTaskDelay must be defined as 1 for this function to be available.
 * See the configuration section for more information.
 *
 *
 * vTaskDelay() specifies a time at which the task wishes to unblock relative to
 * the time at which vTaskDelay() is called.  For example, specifying a block
 * period of 100 ticks will cause the task to unblock 100 ticks after
 * vTaskDelay() is called.  vTaskDelay() does not therefore provide a good method
 * of controlling the frequency of a cyclical task as the path taken through the
 * code, as well as other task and interrupt activity, will effect the frequency
 * at which vTaskDelay() gets called and therefore the time at which the task
 * next executes.  See vTaskDelayUntil() for an alternative API function designed
 * to facilitate fixed frequency execution.  It does this by specifying an
 * absolute time (rather than a relative time) at which the calling task should
 * unblock.
 *
 * @param xTicksToDelay The amount of time, in tick periods, that
 * the calling task should block.
 *
 * Example usage:

 void vTaskFunction( void * pvParameters )
 {
 void vTaskFunction( void * pvParameters )
 {
 // Block for 500ms.
 const portTickType xDelay = 500 / portTICK_RATE_MS;

	 for( ;; )
	 {
		 // Simply toggle the LED every 500ms, blocking between each toggle.
		 vToggleLED();
		 vTaskDelay( xDelay );
	 }
 }

 * \defgroup vTaskDelay vTaskDelay
 * \ingroup TaskCtrl
 */
void vTaskDelay( portTickType xTicksToDelay ) PRIVILEGED_FUNCTION;

/**
 * task. h
 * <pre>void vTaskDelayUntil( portTickType *pxPreviousWakeTime, portTickType xTimeIncrement );</pre>
 *
 * INCLUDE_vTaskDelayUntil must be defined as 1 for this function to be available.
 * See the configuration section for more information.
 *
 * Delay a task until a specified time.  This function can be used by cyclical
 * tasks to ensure a constant execution frequency.
 *
 * This function differs from vTaskDelay () in one important aspect:  vTaskDelay () will
 * cause a task to block for the specified number of ticks from the time vTaskDelay () is
 * called.  It is therefore difficult to use vTaskDelay () by itself to generate a fixed
 * execution frequency as the time between a task starting to execute and that task
 * calling vTaskDelay () may not be fixed [the task may take a different path though the
 * code between calls, or may get interrupted or preempted a different number of times
 * each time it executes].
 *
 * Whereas vTaskDelay () specifies a wake time relative to the time at which the function
 * is called, vTaskDelayUntil () specifies the absolute (exact) time at which it wishes to
 * unblock.
 *
 * The constant portTICK_RATE_MS can be used to calculate real time from the tick
 * rate - with the resolution of one tick period.
 *
 * @param pxPreviousWakeTime Pointer to a variable that holds the time at which the
 * task was last unblocked.  The variable must be initialised with the current time
 * prior to its first use (see the example below).  Following this the variable is
 * automatically updated within vTaskDelayUntil ().
 *
 * @param xTimeIncrement The cycle time period.  The task will be unblocked at
 * time *pxPreviousWakeTime + xTimeIncrement.  Calling vTaskDelayUntil with the
 * same xTimeIncrement parameter value will cause the task to execute with
 * a fixed interface period.
 *
 * Example usage:
   <pre>
 // Perform an action every 10 ticks.
 void vTaskFunction( void * pvParameters )
 {
 portTickType xLastWakeTime;
 const portTickType xFrequency = 10;

	 // Initialise the xLastWakeTime variable with the current time.
	 xLastWakeTime = xTaskGetTickCount ();
	 for( ;; )
	 {
		 // Wait for the next cycle.
		 vTaskDelayUntil( &xLastWakeTime, xFrequency );

		 // Perform action here.
	 }
 }
   </pre>
 * \defgroup vTaskDelayUntil vTaskDelayUntil
 * \ingroup TaskCtrl
 */
void vTaskDelayUntil( portTickType * const pxPreviousWakeTime, portTickType xTimeIncrement ) PRIVILEGED_FUNCTION;

/**
 * task. h
 * <pre>unsigned portBASE_TYPE uxTaskPriorityGet( xTaskHandle pxTask );</pre>
 *
 * INCLUDE_xTaskPriorityGet must be defined as 1 for this function to be available.
 * See the configuration section for more information.
 *
 * Obtain the priority of any task.
 *
 * @param pxTask Handle of the task to be queried.  Passing a NULL
 * handle results in the priority of the calling task being returned.
 *
 * @return The priority of pxTask.
 *
 * Example usage:
   <pre>
 void vAFunction( void )
 {
 xTaskHandle xHandle;

	 // Create a task, storing the handle.
	 xTaskCreate( vTaskCode, "NAME", STACK_SIZE, NULL, tskIDLE_PRIORITY, &xHandle );

	 // ...

	 // Use the handle to obtain the priority of the created task.
	 // It was created with tskIDLE_PRIORITY, but may have changed
	 // it itself.
	 if( uxTaskPriorityGet( xHandle ) != tskIDLE_PRIORITY )
	 {
		 // The task has changed it's priority.
	 }

	 // ...

	 // Is our priority higher than the created task?
	 if( uxTaskPriorityGet( xHandle ) < uxTaskPriorityGet( NULL ) )
	 {
		 // Our priority (obtained using NULL handle) is higher.
	 }
 }
   </pre>
 * \defgroup uxTaskPriorityGet uxTaskPriorityGet
 * \ingroup TaskCtrl
 */
unsigned portBASE_TYPE uxTaskPriorityGet( xTaskHandle pxTask ) PRIVILEGED_FUNCTION;

/**
 * task. h
 * <pre>void vTaskPrioritySet( xTaskHandle pxTask, unsigned portBASE_TYPE uxNewPriority );</pre>
 *
 * INCLUDE_vTaskPrioritySet must be defined as 1 for this function to be available.
 * See the configuration section for more information.
 *
 * Set the priority of any task.
 *
 * A context switch will occur before the function returns if the priority
 * being set is higher than the currently executing task.
 *
 * @param pxTask Handle to the task for which the priority is being set.
 * Passing a NULL handle results in the priority of the calling task being set.
 *
 * @param uxNewPriority The priority to which the task will be set.
 *
 * Example usage:
   <pre>
 void vAFunction( void )
 {
 xTaskHandle xHandle;

	 // Create a task, storing the handle.
	 xTaskCreate( vTaskCode, "NAME", STACK_SIZE, NULL, tskIDLE_PRIORITY, &xHandle );

	 // ...

	 // Use the handle to raise the priority of the created task.
	 vTaskPrioritySet( xHandle, tskIDLE_PRIORITY + 1 );

	 // ...

	 // Use a NULL handle to raise our priority to the same value.
	 vTaskPrioritySet( NULL, tskIDLE_PRIORITY + 1 );
 }
   </pre>
 * \defgroup vTaskPrioritySet vTaskPrioritySet
 * \ingroup TaskCtrl
 */
void vTaskPrioritySet( xTaskHandle pxTask, unsigned portBASE_TYPE uxNewPriority ) PRIVILEGED_FUNCTION;

/**
 * task. h
 * <pre>void vTaskSuspend( xTaskHandle pxTaskToSuspend );</pre>
 *
 * INCLUDE_vTaskSuspend must be defined as 1 for this function to be available.
 * See the configuration section for more information.
 *
 * Suspend any task.  When suspended a task will never get any microcontroller
 * processing time, no matter what its priority.
 *
 * Calls to vTaskSuspend are not accumulative -
 * i.e. calling vTaskSuspend () twice on the same task still only requires one
 * call to vTaskResume () to ready the suspended task.
 *
 * @param pxTaskToSuspend Handle to the task being suspended.  Passing a NULL
 * handle will cause the calling task to be suspended.
 *
 * Example usage:
   <pre>
 void vAFunction( void )
 {
 xTaskHandle xHandle;

	 // Create a task, storing the handle.
	 xTaskCreate( vTaskCode, "NAME", STACK_SIZE, NULL, tskIDLE_PRIORITY, &xHandle );

	 // ...

	 // Use the handle to suspend the created task.
	 vTaskSuspend( xHandle );

	 // ...

	 // The created task will not run during this period, unless
	 // another task calls vTaskResume( xHandle ).

	 //...


	 // Suspend ourselves.
	 vTaskSuspend( NULL );

	 // We cannot get here unless another task calls vTaskResume
	 // with our handle as the parameter.
 }
   </pre>
 * \defgroup vTaskSuspend vTaskSuspend
 * \ingroup TaskCtrl
 */
void vTaskSuspend( xTaskHandle pxTaskToSuspend ) PRIVILEGED_FUNCTION;

/**
 * task. h
 * <pre>void vTaskResume( xTaskHandle pxTaskToResume );</pre>
 *
 * INCLUDE_vTaskSuspend must be defined as 1 for this function to be available.
 * See the configuration section for more information.
 *
 * Resumes a suspended task.
 *
 * A task that has been suspended by one of more calls to vTaskSuspend ()
 * will be made available for running again by a single call to
 * vTaskResume ().
 *
 * @param pxTaskToResume Handle to the task being readied.
 *
 * Example usage:
   <pre>
 void vAFunction( void )
 {
 xTaskHandle xHandle;

	 // Create a task, storing the handle.
	 xTaskCreate( vTaskCode, "NAME", STACK_SIZE, NULL, tskIDLE_PRIORITY, &xHandle );

	 // ...

	 // Use the handle to suspend the created task.
	 vTaskSuspend( xHandle );

	 // ...

	 // The created task will not run during this period, unless
	 // another task calls vTaskResume( xHandle ).

	 //...


	 // Resume the suspended task ourselves.
	 vTaskResume( xHandle );

	 // The created task will once again get microcontroller processing
	 // time in accordance with it priority within the system.
 }
   </pre>
 * \defgroup vTaskResume vTaskResume
 * \ingroup TaskCtrl
 */
void vTaskResume( xTaskHandle pxTaskToResume ) PRIVILEGED_FUNCTION;

/**
 * task. h
 * <pre>void xTaskResumeFromISR( xTaskHandle pxTaskToResume );</pre>
 *
 * INCLUDE_xTaskResumeFromISR must be defined as 1 for this function to be
 * available.  See the configuration section for more information.
 *
 * An implementation of vTaskResume() that can be called from within an ISR.
 *
 * A task that has been suspended by one of more calls to vTaskSuspend ()
 * will be made available for running again by a single call to
 * xTaskResumeFromISR ().
 *
 * @param pxTaskToResume Handle to the task being readied.
 *
 * \defgroup vTaskResumeFromISR vTaskResumeFromISR
 * \ingroup TaskCtrl
 */
portBASE_TYPE xTaskResumeFromISR( xTaskHandle pxTaskToResume ) PRIVILEGED_FUNCTION;

/*-----------------------------------------------------------
 * SCHEDULER CONTROL
 *----------------------------------------------------------*/

/**
 * task. h
 * <pre>void vTaskStartScheduler( void );</pre>
 *
 * Starts the real time kernel tick processing.  After calling the kernel
 * has control over which tasks are executed and when.  This function
 * does not return until an executing task calls vTaskEndScheduler ().
 *
 * At least one task should be created via a call to xTaskCreate ()
 * before calling vTaskStartScheduler ().  The idle task is created
 * automatically when the first application task is created.
 *
 * See the demo application file main.c for an example of creating
 * tasks and starting the kernel.
 *
 * Example usage:
   <pre>
 void vAFunction( void )
 {
	 // Create at least one task before starting the kernel.
	 xTaskCreate( vTaskCode, "NAME", STACK_SIZE, NULL, tskIDLE_PRIORITY, NULL );

	 // Start the real time kernel with preemption.
	 vTaskStartScheduler ();

	 // Will not get here unless a task calls vTaskEndScheduler ()
 }
   </pre>
 *
 * \defgroup vTaskStartScheduler vTaskStartScheduler
 * \ingroup SchedulerControl
 */
void vTaskStartScheduler( void ) PRIVILEGED_FUNCTION;

/**
 * task. h
 * <pre>void vTaskEndScheduler( void );</pre>
 *
 * Stops the real time kernel tick.  All created tasks will be automatically
 * deleted and multitasking (either preemptive or cooperative) will
 * stop.  Execution then resumes from the point where vTaskStartScheduler ()
 * was called, as if vTaskStartScheduler () had just returned.
 *
 * See the demo application file main. c in the demo/PC directory for an
 * example that uses vTaskEndScheduler ().
 *
 * vTaskEndScheduler () requires an exit function to be defined within the
 * portable layer (see vPortEndScheduler () in port. c for the PC port).  This
 * performs hardware specific operations such as stopping the kernel tick.
 *
 * vTaskEndScheduler () will cause all of the resources allocated by the
 * kernel to be freed - but will not free resources allocated by application
 * tasks.
 *
 * Example usage:
   <pre>
 void vTaskCode( void * pvParameters )
 {
	 for( ;; )
	 {
		 // Task code goes here.

		 // At some point we want to end the real time kernel processing
		 // so call ...
		 vTaskEndScheduler ();
	 }
 }

 void vAFunction( void )
 {
	 // Create at least one task before starting the kernel.
	 xTaskCreate( vTaskCode, "NAME", STACK_SIZE, NULL, tskIDLE_PRIORITY, NULL );

	 // Start the real time kernel with preemption.
	 vTaskStartScheduler ();

	 // Will only get here when the vTaskCode () task has called
	 // vTaskEndScheduler ().  When we get here we are back to single task
	 // execution.
 }
   </pre>
 *
 * \defgroup vTaskEndScheduler vTaskEndScheduler
 * \ingroup SchedulerControl
 */
void vTaskEndScheduler( void ) PRIVILEGED_FUNCTION;

/**
 * task. h
 * <pre>void vTaskSuspendAll( void );</pre>
 *
 * Suspends all real time kernel activity while keeping interrupts (including the
 * kernel tick) enabled.
 *
 * After calling vTaskSuspendAll () the calling task will continue to execute
 * without risk of being swapped out until a call to xTaskResumeAll () has been
 * made.
 *
 * API functions that have the potential to cause a context switch (for example,
 * vTaskDelayUntil(), xQueueSend(), etc.) must not be called while the scheduler
 * is suspended.
 *
 * Example usage:
   <pre>
 void vTask1( void * pvParameters )
 {
	 for( ;; )
	 {
		 // Task code goes here.

		 // ...

		 // At some point the task wants to perform a long operation during
		 // which it does not want to get swapped out.  It cannot use
		 // taskENTER_CRITICAL ()/taskEXIT_CRITICAL () as the length of the
		 // operation may cause interrupts to be missed - including the
		 // ticks.

		 // Prevent the real time kernel swapping out the task.
		 vTaskSuspendAll ();

		 // Perform the operation here.  There is no need to use critical
		 // sections as we have all the microcontroller processing time.
		 // During this time interrupts will still operate and the kernel
		 // tick count will be maintained.

		 // ...

		 // The operation is complete.  Restart the kernel.
		 xTaskResumeAll ();
	 }
 }
   </pre>
 * \defgroup vTaskSuspendAll vTaskSuspendAll
 * \ingroup SchedulerControl
 */
void vTaskSuspendAll( void ) PRIVILEGED_FUNCTION;

/**
 * task. h
 * <pre>char xTaskResumeAll( void );</pre>
 *
 * Resumes real time kernel activity following a call to vTaskSuspendAll ().
 * After a call to vTaskSuspendAll () the kernel will take control of which
 * task is executing at any time.
 *
 * @return If resuming the scheduler caused a context switch then pdTRUE is
 *		  returned, otherwise pdFALSE is returned.
 *
 * Example usage:
   <pre>
 void vTask1( void * pvParameters )
 {
	 for( ;; )
	 {
		 // Task code goes here.

		 // ...

		 // At some point the task wants to perform a long operation during
		 // which it does not want to get swapped out.  It cannot use
		 // taskENTER_CRITICAL ()/taskEXIT_CRITICAL () as the length of the
		 // operation may cause interrupts to be missed - including the
		 // ticks.

		 // Prevent the real time kernel swapping out the task.
		 vTaskSuspendAll ();

		 // Perform the operation here.  There is no need to use critical
		 // sections as we have all the microcontroller processing time.
		 // During this time interrupts will still operate and the real
		 // time kernel tick count will be maintained.

		 // ...

		 // The operation is complete.  Restart the kernel.  We want to force
		 // a context switch - but there is no point if resuming the scheduler
		 // caused a context switch already.
		 if( !xTaskResumeAll () )
		 {
			  taskYIELD ();
		 }
	 }
 }
   </pre>
 * \defgroup xTaskResumeAll xTaskResumeAll
 * \ingroup SchedulerControl
 */
signed portBASE_TYPE xTaskResumeAll( void ) PRIVILEGED_FUNCTION;

/**
 * task. h
 * <pre>signed portBASE_TYPE xTaskIsTaskSuspended( xTaskHandle xTask );</pre>
 *
 * Utility task that simply returns pdTRUE if the task referenced by xTask is
 * currently in the Suspended state, or pdFALSE if the task referenced by xTask
 * is in any other state.
 *
 */
signed portBASE_TYPE xTaskIsTaskSuspended( xTaskHandle xTask ) PRIVILEGED_FUNCTION;

/*-----------------------------------------------------------
 * TASK UTILITIES
 *----------------------------------------------------------*/

/**
 * task. h
 * <PRE>volatile portTickType xTaskGetTickCount( void );</PRE>
 *
 * @return The count of ticks since vTaskStartScheduler was called.
 *
 * \page xTaskGetTickCount xTaskGetTickCount
 * \ingroup TaskUtils
 */
portTickType xTaskGetTickCount( void ) PRIVILEGED_FUNCTION;

/**
 * task. h
 * <PRE>unsigned short uxTaskGetNumberOfTasks( void );</PRE>
 *
 * @return The number of tasks that the real time kernel is currently managing.
 * This includes all ready, blocked and suspended tasks.  A task that
 * has been deleted but not yet freed by the idle task will also be
 * included in the count.
 *
 * \page uxTaskGetNumberOfTasks uxTaskGetNumberOfTasks
 * \ingroup TaskUtils
 */
unsigned portBASE_TYPE uxTaskGetNumberOfTasks( void ) PRIVILEGED_FUNCTION;

/**
 * task. h
 * <PRE>void vTaskList( char *pcWriteBuffer );</PRE>
 *
 * configUSE_TRACE_FACILITY must be defined as 1 for this function to be
 * available.  See the configuration section for more information.
 *
 * NOTE: This function will disable interrupts for its duration.  It is
 * not intended for normal application runtime use but as a debug aid.
 *
 * Lists all the current tasks, along with their current state and stack
 * usage high water mark.
 *
 * Tasks are reported as blocked ('B'), ready ('R'), deleted ('D') or
 * suspended ('S').
 *
 * @param pcWriteBuffer A buffer into which the above mentioned details
 * will be written, in ascii form.  This buffer is assumed to be large
 * enough to contain the generated report.  Approximately 40 bytes per
 * task should be sufficient.
 *
 * \page vTaskList vTaskList
 * \ingroup TaskUtils
 */
void vTaskList( signed char *pcWriteBuffer ) PRIVILEGED_FUNCTION;

/**
 * task. h
 * <PRE>void vTaskGetRunTimeStats( char *pcWriteBuffer );</PRE>
 *
 * configGENERATE_RUN_TIME_STATS must be defined as 1 for this function
 * to be available.  The application must also then provide definitions
 * for portCONFIGURE_TIMER_FOR_RUN_TIME_STATS() and
 * portGET_RUN_TIME_COUNTER_VALUE to configure a peripheral timer/counter
 * and return the timers current count value respectively.  The counter
 * should be at least 10 times the frequency of the tick count.
 *
 * NOTE: This function will disable interrupts for its duration.  It is
 * not intended for normal application runtime use but as a debug aid.
 *
 * Setting configGENERATE_RUN_TIME_STATS to 1 will result in a total
 * accumulated execution time being stored for each task.  The resolution
 * of the accumulated time value depends on the frequency of the timer
 * configured by the portCONFIGURE_TIMER_FOR_RUN_TIME_STATS() macro.
 * Calling vTaskGetRunTimeStats() writes the total execution time of each
 * task into a buffer, both as an absolute count value and as a percentage
 * of the total system execution time.
 *
 * @param pcWriteBuffer A buffer into which the execution times will be
 * written, in ascii form.  This buffer is assumed to be large enough to
 * contain the generated report.  Approximately 40 bytes per task should
 * be sufficient.
 *
 * \page vTaskGetRunTimeStats vTaskGetRunTimeStats
 * \ingroup TaskUtils
 */
void vTaskGetRunTimeStats( signed char *pcWriteBuffer ) PRIVILEGED_FUNCTION;

/**
 * task. h
 * <PRE>void vTaskStartTrace( char * pcBuffer, unsigned portBASE_TYPE uxBufferSize );</PRE>
 *
 * Starts a real time kernel activity trace.  The trace logs the identity of
 * which task is running when.
 *
 * The trace file is stored in binary format.  A separate DOS utility called
 * convtrce.exe is used to convert this into a tab delimited text file which
 * can be viewed and plotted in a spread sheet.
 *
 * @param pcBuffer The buffer into which the trace will be written.
 *
 * @param ulBufferSize The size of pcBuffer in bytes.  The trace will continue
 * until either the buffer in full, or ulTaskEndTrace () is called.
 *
 * \page vTaskStartTrace vTaskStartTrace
 * \ingroup TaskUtils
 */
void vTaskStartTrace( signed char * pcBuffer, unsigned long ulBufferSize ) PRIVILEGED_FUNCTION;

/**
 * task. h
 * <PRE>unsigned long ulTaskEndTrace( void );</PRE>
 *
 * Stops a kernel activity trace.  See vTaskStartTrace ().
 *
 * @return The number of bytes that have been written into the trace buffer.
 *
 * \page usTaskEndTrace usTaskEndTrace
 * \ingroup TaskUtils
 */
unsigned long ulTaskEndTrace( void ) PRIVILEGED_FUNCTION;

/**
 * task.h
 * <PRE>unsigned portBASE_TYPE uxTaskGetStackHighWaterMark( xTaskHandle xTask );</PRE>
 *
 * INCLUDE_uxTaskGetStackHighWaterMark must be set to 1 in FreeRTOSConfig.h for
 * this function to be available.
 *
 * Returns the high water mark of the stack associated with xTask.  That is,
 * the minimum free stack space there has been (in bytes) since the task
 * started.  The smaller the returned number the closer the task has come
 * to overflowing its stack.
 *
 * @param xTask Handle of the task associated with the stack to be checked.
 * Set xTask to NULL to check the stack of the calling task.
 *
 * @return The smallest amount of free stack space there has been (in bytes)
 * since the task referenced by xTask was created.
 */
unsigned portBASE_TYPE uxTaskGetStackHighWaterMark( xTaskHandle xTask ) PRIVILEGED_FUNCTION;

/**
 * task.h
 * <pre>void vTaskSetApplicationTaskTag( xTaskHandle xTask, pdTASK_HOOK_CODE pxHookFunction );</pre>
 *
 * Sets pxHookFunction to be the task hook function used by the task xTask.
 * Passing xTask as NULL has the effect of setting the calling tasks hook
 * function.
 */
void vTaskSetApplicationTaskTag( xTaskHandle xTask, pdTASK_HOOK_CODE pxHookFunction ) PRIVILEGED_FUNCTION;

/**
 * task.h
 * <pre>void xTaskGetApplicationTaskTag( xTaskHandle xTask );</pre>
 *
 * Returns the pxHookFunction value assigned to the task xTask.
 */
pdTASK_HOOK_CODE xTaskGetApplicationTaskTag( xTaskHandle xTask ) PRIVILEGED_FUNCTION;

/**
 * task.h
 * <pre>portBASE_TYPE xTaskCallApplicationTaskHook( xTaskHandle xTask, pdTASK_HOOK_CODE pxHookFunction );</pre>
 *
 * Calls the hook function associated with xTask.  Passing xTask as NULL has
 * the effect of calling the Running tasks (the calling task) hook function.
 *
 * pvParameter is passed to the hook function for the task to interpret as it
 * wants.
 */
portBASE_TYPE xTaskCallApplicationTaskHook( xTaskHandle xTask, void *pvParameter ) PRIVILEGED_FUNCTION;


/*-----------------------------------------------------------
 * SCHEDULER INTERNALS AVAILABLE FOR PORTING PURPOSES
 *----------------------------------------------------------*/

/*
 * THIS FUNCTION MUST NOT BE USED FROM APPLICATION CODE.  IT IS ONLY
 * INTENDED FOR USE WHEN IMPLEMENTING A PORT OF THE SCHEDULER AND IS
 * AN INTERFACE WHICH IS FOR THE EXCLUSIVE USE OF THE SCHEDULER.
 *
 * Called from the real time kernel tick (either preemptive or cooperative),
 * this increments the tick count and checks if any tasks that are blocked
 * for a finite period required removing from a blocked list and placing on
 * a ready list.
 */
void vTaskIncrementTick( void ) PRIVILEGED_FUNCTION;

/*
 * THIS FUNCTION MUST NOT BE USED FROM APPLICATION CODE.  IT IS AN
 * INTERFACE WHICH IS FOR THE EXCLUSIVE USE OF THE SCHEDULER.
 *
 * THIS FUNCTION MUST BE CALLED WITH INTERRUPTS DISABLED.
 *
 * Removes the calling task from the ready list and places it both
 * on the list of tasks waiting for a particular event, and the
 * list of delayed tasks.  The task will be removed from both lists
 * and replaced on the ready list should either the event occur (and
 * there be no higher priority tasks waiting on the same event) or
 * the delay period expires.
 *
 * @param pxEventList The list containing tasks that are blocked waiting
 * for the event to occur.
 *
 * @param xTicksToWait The maximum amount of time that the task should wait
 * for the event to occur.  This is specified in kernel ticks,the constant
 * portTICK_RATE_MS can be used to convert kernel ticks into a real time
 * period.
 */
void vTaskPlaceOnEventList( const xList * const pxEventList, portTickType xTicksToWait ) PRIVILEGED_FUNCTION;

/*
 * THIS FUNCTION MUST NOT BE USED FROM APPLICATION CODE.  IT IS AN
 * INTERFACE WHICH IS FOR THE EXCLUSIVE USE OF THE SCHEDULER.
 *
 * THIS FUNCTION MUST BE CALLED WITH INTERRUPTS DISABLED.
 *
 * Removes a task from both the specified event list and the list of blocked
 * tasks, and places it on a ready queue.
 *
 * xTaskRemoveFromEventList () will be called if either an event occurs to
 * unblock a task, or the block timeout period expires.
 *
 * @return pdTRUE if the task being removed has a higher priority than the task
 * making the call, otherwise pdFALSE.
 */
signed portBASE_TYPE xTaskRemoveFromEventList( const xList * const pxEventList ) PRIVILEGED_FUNCTION;

/*
 * THIS FUNCTION MUST NOT BE USED FROM APPLICATION CODE.  IT IS AN
 * INTERFACE WHICH IS FOR THE EXCLUSIVE USE OF THE SCHEDULER.
 *
 * INCLUDE_vTaskCleanUpResources and INCLUDE_vTaskSuspend must be defined as 1
 * for this function to be available.
 * See the configuration section for more information.
 *
 * Empties the ready and delayed queues of task control blocks, freeing the
 * memory allocated for the task control block and task stacks as it goes.
 */
void vTaskCleanUpResources( void ) PRIVILEGED_FUNCTION;

/*
 * THIS FUNCTION MUST NOT BE USED FROM APPLICATION CODE.  IT IS ONLY
 * INTENDED FOR USE WHEN IMPLEMENTING A PORT OF THE SCHEDULER AND IS
 * AN INTERFACE WHICH IS FOR THE EXCLUSIVE USE OF THE SCHEDULER.
 *
 * Sets the pointer to the current TCB to the TCB of the highest priority task
 * that is ready to run.
 */
void vTaskSwitchContext( void ) PRIVILEGED_FUNCTION;

/*
 * Return the handle of the calling task.
 */
xTaskHandle xTaskGetCurrentTaskHandle( void ) PRIVILEGED_FUNCTION;

/*
 * Capture the current time status for future reference.
 */
void vTaskSetTimeOutState( xTimeOutType * const pxTimeOut ) PRIVILEGED_FUNCTION;

/*
 * Compare the time status now with that previously captured to see if the
 * timeout has expired.
 */
portBASE_TYPE xTaskCheckForTimeOut( xTimeOutType * const pxTimeOut, portTickType * const pxTicksToWait ) PRIVILEGED_FUNCTION;

/*
 * Shortcut used by the queue implementation to prevent unnecessary call to
 * taskYIELD();
 */
void vTaskMissedYield( void ) PRIVILEGED_FUNCTION;

/*
 * Returns the scheduler state as taskSCHEDULER_RUNNING,
 * taskSCHEDULER_NOT_STARTED or taskSCHEDULER_SUSPENDED.
 */
portBASE_TYPE xTaskGetSchedulerState( void ) PRIVILEGED_FUNCTION;

/*
 * Raises the priority of the mutex holder to that of the calling task should
 * the mutex holder have a priority less than the calling task.
 */
void vTaskPriorityInherit( xTaskHandle * const pxMutexHolder ) PRIVILEGED_FUNCTION;

/*
 * Set the priority of a task back to its proper priority in the case that it
 * inherited a higher priority while it was holding a semaphore.
 */
void vTaskPriorityDisinherit( xTaskHandle * const pxMutexHolder ) PRIVILEGED_FUNCTION;

/*
 * Generic version of the task creation function which is in turn called by the
 * xTaskCreate() and xTaskCreateProtected() macros.
 */
signed portBASE_TYPE xTaskGenericCreate( pdTASK_CODE pvTaskCode, const signed char * const pcName, unsigned short usStackDepth, void *pvParameters, unsigned portBASE_TYPE uxPriority, xTaskHandle *pxCreatedTask, portSTACK_TYPE *puxStackBuffer, const xMemoryRegion * const xRegions ) PRIVILEGED_FUNCTION;

#ifdef __cplusplus
}
#endif
#endif /* TASK_H */



