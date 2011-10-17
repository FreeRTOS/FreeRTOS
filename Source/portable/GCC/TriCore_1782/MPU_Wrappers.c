/*
    FreeRTOS V7.0.2 - Copyright (C) 2011 Real Time Engineers Ltd.


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
    >>>NOTE<<< The modification to the GPL is included to allow you to
    distribute a combined work that includes FreeRTOS without being obliged to
    provide the source code for proprietary components outside of the FreeRTOS
    kernel.  FreeRTOS is distributed in the hope that it will be useful, but
    WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
    or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
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

/* Defining MPU_WRAPPERS_INCLUDED_FROM_API_FILE prevents task.h from redefining
all the API functions to use the MPU wrappers.  That should only be done when
task.h is included from an application file. */
#define MPU_WRAPPERS_INCLUDED_FROM_API_FILE

#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"

#undef MPU_WRAPPERS_INCLUDED_FROM_API_FILE

#if configUSE_MPU == 1

/* Function for raising the privilege of a task. */
extern portBASE_TYPE xPortRaisePrivilege( void );

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
void MPU_vTaskSuspend( xTaskHandle pxTaskToSuspend );
signed portBASE_TYPE MPU_xTaskIsTaskSuspended( xTaskHandle xTask );
void MPU_vTaskResume( xTaskHandle pxTaskToResume );
void MPU_vTaskSuspendAll( void );
signed portBASE_TYPE MPU_xTaskResumeAll( void );
portTickType MPU_xTaskGetTickCount( void );
unsigned portBASE_TYPE MPU_uxTaskGetNumberOfTasks( void );
void MPU_vTaskList( signed char *pcWriteBuffer );
void MPU_vTaskGetRunTimeStats( signed char *pcWriteBuffer );
void MPU_vTaskStartTrace( signed char * pcBuffer, unsigned long ulBufferSize );
unsigned long MPU_ulTaskEndTrace( void );
void MPU_vTaskSetApplicationTaskTag( xTaskHandle xTask, pdTASK_HOOK_CODE pxTagValue );
pdTASK_HOOK_CODE MPU_xTaskGetApplicationTaskTag( xTaskHandle xTask );
portBASE_TYPE MPU_xTaskCallApplicationTaskHook( xTaskHandle xTask, void *pvParameter );
unsigned portBASE_TYPE MPU_uxTaskGetStackHighWaterMark( xTaskHandle xTask );
xTaskHandle MPU_xTaskGetCurrentTaskHandle( void );
portBASE_TYPE MPU_xTaskGetSchedulerState( void );
xQueueHandle MPU_xQueueCreate( unsigned portBASE_TYPE uxQueueLength, unsigned portBASE_TYPE uxItemSize );
signed portBASE_TYPE MPU_xQueueGenericSend( xQueueHandle xQueue, const void * const pvItemToQueue, portTickType xTicksToWait, portBASE_TYPE xCopyPosition );
unsigned portBASE_TYPE MPU_uxQueueMessagesWaiting( const xQueueHandle pxQueue );
signed portBASE_TYPE MPU_xQueueGenericReceive( xQueueHandle pxQueue, void * const pvBuffer, portTickType xTicksToWait, portBASE_TYPE xJustPeeking );
xQueueHandle MPU_xQueueCreateMutex( void );
xQueueHandle MPU_xQueueCreateCountingSemaphore( unsigned portBASE_TYPE uxCountValue, unsigned portBASE_TYPE uxInitialCount );
portBASE_TYPE MPU_xQueueTakeMutexRecursive( xQueueHandle xMutex, portTickType xBlockTime );
portBASE_TYPE MPU_xQueueGiveMutexRecursive( xQueueHandle xMutex );
signed portBASE_TYPE MPU_xQueueAltGenericSend( xQueueHandle pxQueue, const void * const pvItemToQueue, portTickType xTicksToWait, portBASE_TYPE xCopyPosition );
signed portBASE_TYPE MPU_xQueueAltGenericReceive( xQueueHandle pxQueue, void * const pvBuffer, portTickType xTicksToWait, portBASE_TYPE xJustPeeking );
void MPU_vQueueAddToRegistry( xQueueHandle xQueue, signed char *pcName );
void *MPU_pvPortMalloc( size_t xSize );
void MPU_vPortFree( void *pv );
void MPU_vPortInitialiseBlocks( void );
size_t MPU_xPortGetFreeHeapSize( void );
/*---------------------------------------------------------------------------*/

signed portBASE_TYPE MPU_xTaskGenericCreate( pdTASK_CODE pvTaskCode, const signed char * const pcName, unsigned short usStackDepth, void *pvParameters, unsigned portBASE_TYPE uxPriority, xTaskHandle *pxCreatedTask, portSTACK_TYPE *puxStackBuffer, const xMemoryRegion * const xRegions )
{
signed portBASE_TYPE xReturn;
portBASE_TYPE xRunningPrivileged = xPortRaisePrivilege();

	xReturn = xTaskGenericCreate( pvTaskCode, pcName, usStackDepth, pvParameters, uxPriority, pxCreatedTask, puxStackBuffer, xRegions );
	portMPU_RESTORE_PRIORITY( xRunningPrivileged );
	return xReturn;
}
/*-----------------------------------------------------------*/

void MPU_vTaskAllocateMPURegions( xTaskHandle xTask, const xMemoryRegion * const xRegions )
{
portBASE_TYPE xRunningPrivileged = xPortRaisePrivilege();

	vTaskAllocateMPURegions( xTask, xRegions );
	portMPU_RESTORE_PRIORITY( xRunningPrivileged );
}
/*-----------------------------------------------------------*/

#if ( INCLUDE_vTaskDelete == 1 )
	void MPU_vTaskDelete( xTaskHandle pxTaskToDelete )
	{
    portBASE_TYPE xRunningPrivileged = xPortRaisePrivilege();

		vTaskDelete( pxTaskToDelete );
        portMPU_RESTORE_PRIORITY( xRunningPrivileged );
	}
#endif
/*-----------------------------------------------------------*/

#if ( INCLUDE_vTaskDelayUntil == 1 )
	void MPU_vTaskDelayUntil( portTickType * const pxPreviousWakeTime, portTickType xTimeIncrement )
	{
    portBASE_TYPE xRunningPrivileged = xPortRaisePrivilege();

		vTaskDelayUntil( pxPreviousWakeTime, xTimeIncrement );
        portMPU_RESTORE_PRIORITY( xRunningPrivileged );
	}
#endif
/*-----------------------------------------------------------*/

#if ( INCLUDE_vTaskDelay == 1 )
	void MPU_vTaskDelay( portTickType xTicksToDelay )
	{
    portBASE_TYPE xRunningPrivileged = xPortRaisePrivilege();

		vTaskDelay( xTicksToDelay );
        portMPU_RESTORE_PRIORITY( xRunningPrivileged );
	}
#endif
/*-----------------------------------------------------------*/

#if ( INCLUDE_uxTaskPriorityGet == 1 )
	unsigned portBASE_TYPE MPU_uxTaskPriorityGet( xTaskHandle pxTask )
	{
	unsigned portBASE_TYPE uxReturn;
    portBASE_TYPE xRunningPrivileged = xPortRaisePrivilege();

		uxReturn = uxTaskPriorityGet( pxTask );
        portMPU_RESTORE_PRIORITY( xRunningPrivileged );
		return uxReturn;
	}
#endif
/*-----------------------------------------------------------*/

#if ( INCLUDE_vTaskPrioritySet == 1 )
	void MPU_vTaskPrioritySet( xTaskHandle pxTask, unsigned portBASE_TYPE uxNewPriority )
	{
    portBASE_TYPE xRunningPrivileged = xPortRaisePrivilege();

		vTaskPrioritySet( pxTask, uxNewPriority );
        portMPU_RESTORE_PRIORITY( xRunningPrivileged );
	}
#endif
/*-----------------------------------------------------------*/

#if ( INCLUDE_vTaskSuspend == 1 )
	void MPU_vTaskSuspend( xTaskHandle pxTaskToSuspend )
	{
    portBASE_TYPE xRunningPrivileged = xPortRaisePrivilege();

		vTaskSuspend( pxTaskToSuspend );
        portMPU_RESTORE_PRIORITY( xRunningPrivileged );
	}
#endif
/*-----------------------------------------------------------*/

#if ( INCLUDE_vTaskSuspend == 1 )
	signed portBASE_TYPE MPU_xTaskIsTaskSuspended( xTaskHandle xTask )
	{
	signed portBASE_TYPE xReturn;
    portBASE_TYPE xRunningPrivileged = xPortRaisePrivilege();

		xReturn = xTaskIsTaskSuspended( xTask );
        portMPU_RESTORE_PRIORITY( xRunningPrivileged );
		return xReturn;
	}
#endif
/*-----------------------------------------------------------*/

#if ( INCLUDE_vTaskSuspend == 1 )
	void MPU_vTaskResume( xTaskHandle pxTaskToResume )
	{
    portBASE_TYPE xRunningPrivileged = xPortRaisePrivilege();

		vTaskResume( pxTaskToResume );
        portMPU_RESTORE_PRIORITY( xRunningPrivileged );
	}
#endif
/*-----------------------------------------------------------*/

void MPU_vTaskSuspendAll( void )
{
portBASE_TYPE xRunningPrivileged = xPortRaisePrivilege();

	vTaskSuspendAll();
    portMPU_RESTORE_PRIORITY( xRunningPrivileged );
}
/*-----------------------------------------------------------*/

signed portBASE_TYPE MPU_xTaskResumeAll( void )
{
signed portBASE_TYPE xReturn;
portBASE_TYPE xRunningPrivileged = xPortRaisePrivilege();

	xReturn = xTaskResumeAll();
    portMPU_RESTORE_PRIORITY( xRunningPrivileged );
    return xReturn;
}
/*-----------------------------------------------------------*/

portTickType MPU_xTaskGetTickCount( void )
{
portTickType xReturn;
portBASE_TYPE xRunningPrivileged = xPortRaisePrivilege();

	xReturn = xTaskGetTickCount();
    portMPU_RESTORE_PRIORITY( xRunningPrivileged );
	return xReturn;
}
/*-----------------------------------------------------------*/

unsigned portBASE_TYPE MPU_uxTaskGetNumberOfTasks( void )
{
unsigned portBASE_TYPE uxReturn;
portBASE_TYPE xRunningPrivileged = xPortRaisePrivilege();

	uxReturn = uxTaskGetNumberOfTasks();
    portMPU_RESTORE_PRIORITY( xRunningPrivileged );
	return uxReturn;
}
/*-----------------------------------------------------------*/

#if ( configUSE_TRACE_FACILITY == 1 )
	void MPU_vTaskList( signed char *pcWriteBuffer )
	{
	portBASE_TYPE xRunningPrivileged = xPortRaisePrivilege();

		vTaskList( pcWriteBuffer );
		portMPU_RESTORE_PRIORITY( xRunningPrivileged );
	}
#endif
/*-----------------------------------------------------------*/

#if ( configGENERATE_RUN_TIME_STATS == 1 )
	void MPU_vTaskGetRunTimeStats( signed char *pcWriteBuffer )
	{
    portBASE_TYPE xRunningPrivileged = xPortRaisePrivilege();

		vTaskGetRunTimeStats( pcWriteBuffer );
        portMPU_RESTORE_PRIORITY( xRunningPrivileged );
	}
#endif
/*-----------------------------------------------------------*/

#if ( configUSE_TRACE_FACILITY == 1 )
	void MPU_vTaskStartTrace( signed char * pcBuffer, unsigned long ulBufferSize )
	{
    portBASE_TYPE xRunningPrivileged = xPortRaisePrivilege();

		vTaskStartTrace( pcBuffer, ulBufferSize );
        portMPU_RESTORE_PRIORITY( xRunningPrivileged );
	}
#endif
/*-----------------------------------------------------------*/

#if ( configUSE_TRACE_FACILITY == 1 )
	unsigned long MPU_ulTaskEndTrace( void )
	{
	unsigned long ulReturn;
    portBASE_TYPE xRunningPrivileged = xPortRaisePrivilege();

		ulReturn = ulTaskEndTrace();
        portMPU_RESTORE_PRIORITY( xRunningPrivileged );
		return ulReturn;
	}
#endif
/*-----------------------------------------------------------*/

#if ( configUSE_APPLICATION_TASK_TAG == 1 )
	void MPU_vTaskSetApplicationTaskTag( xTaskHandle xTask, pdTASK_HOOK_CODE pxTagValue )
	{
    portBASE_TYPE xRunningPrivileged = xPortRaisePrivilege();

		vTaskSetApplicationTaskTag( xTask, pxTagValue );
        portMPU_RESTORE_PRIORITY( xRunningPrivileged );
	}
#endif
/*-----------------------------------------------------------*/

#if ( configUSE_APPLICATION_TASK_TAG == 1 )
	pdTASK_HOOK_CODE MPU_xTaskGetApplicationTaskTag( xTaskHandle xTask )
	{
	pdTASK_HOOK_CODE xReturn;
    portBASE_TYPE xRunningPrivileged = xPortRaisePrivilege();

		xReturn = xTaskGetApplicationTaskTag( xTask );
        portMPU_RESTORE_PRIORITY( xRunningPrivileged );
		return xReturn;
	}
#endif
/*-----------------------------------------------------------*/

#if ( configUSE_APPLICATION_TASK_TAG == 1 )
	portBASE_TYPE MPU_xTaskCallApplicationTaskHook( xTaskHandle xTask, void *pvParameter )
	{
	portBASE_TYPE xReturn;
    portBASE_TYPE xRunningPrivileged = xPortRaisePrivilege();

		xReturn = xTaskCallApplicationTaskHook( xTask, pvParameter );
        portMPU_RESTORE_PRIORITY( xRunningPrivileged );
		return xReturn;
	}
#endif
/*-----------------------------------------------------------*/

#if ( INCLUDE_uxTaskGetStackHighWaterMark == 1 )
	unsigned portBASE_TYPE MPU_uxTaskGetStackHighWaterMark( xTaskHandle xTask )
	{
	unsigned portBASE_TYPE uxReturn;
    portBASE_TYPE xRunningPrivileged = xPortRaisePrivilege();

		uxReturn = uxTaskGetStackHighWaterMark( xTask );
        portMPU_RESTORE_PRIORITY( xRunningPrivileged );
		return uxReturn;
	}
#endif
/*-----------------------------------------------------------*/

#if ( INCLUDE_xTaskGetCurrentTaskHandle == 1 )
	xTaskHandle MPU_xTaskGetCurrentTaskHandle( void )
	{
	xTaskHandle xReturn;
    portBASE_TYPE xRunningPrivileged = xPortRaisePrivilege();

		xReturn = xTaskGetCurrentTaskHandle();
        portMPU_RESTORE_PRIORITY( xRunningPrivileged );
		return xReturn;
	}
#endif
/*-----------------------------------------------------------*/

#if ( INCLUDE_xTaskGetSchedulerState == 1 )
	portBASE_TYPE MPU_xTaskGetSchedulerState( void )
	{
	portBASE_TYPE xReturn;
    portBASE_TYPE xRunningPrivileged = xPortRaisePrivilege();

		xReturn = xTaskGetSchedulerState();
        portMPU_RESTORE_PRIORITY( xRunningPrivileged );
		return xReturn;
	}
#endif
/*-----------------------------------------------------------*/

void MPU_vTaskEnterCritical( void )
{
extern void vTaskEnterCritical( void );
portBASE_TYPE xRunningPrivileged = xPortRaisePrivilege();

	vTaskEnterCritical();
	portMPU_RESTORE_PRIORITY( xRunningPrivileged );
}
/*-----------------------------------------------------------*/

void MPU_vTaskExitCritical( void )
{
extern void vTaskExitCritical( void );
portBASE_TYPE xRunningPrivileged = xPortRaisePrivilege();

	vTaskExitCritical();
	portMPU_RESTORE_PRIORITY( xRunningPrivileged );
}
/*-----------------------------------------------------------*/

xQueueHandle MPU_xQueueCreate( unsigned portBASE_TYPE uxQueueLength, unsigned portBASE_TYPE uxItemSize )
{
xQueueHandle xReturn;
portBASE_TYPE xRunningPrivileged = xPortRaisePrivilege();

	xReturn = xQueueCreate( uxQueueLength, uxItemSize );
	portMPU_RESTORE_PRIORITY( xRunningPrivileged );
	return xReturn;
}
/*-----------------------------------------------------------*/

signed portBASE_TYPE MPU_xQueueGenericSend( xQueueHandle xQueue, const void * const pvItemToQueue, portTickType xTicksToWait, portBASE_TYPE xCopyPosition )
{
signed portBASE_TYPE xReturn;
portBASE_TYPE xRunningPrivileged = xPortRaisePrivilege();

	xReturn = xQueueGenericSend( xQueue, pvItemToQueue, xTicksToWait, xCopyPosition );
	portMPU_RESTORE_PRIORITY( xRunningPrivileged );
	return xReturn;
}
/*-----------------------------------------------------------*/

unsigned portBASE_TYPE MPU_uxQueueMessagesWaiting( const xQueueHandle pxQueue )
{
portBASE_TYPE xRunningPrivileged = xPortRaisePrivilege();
unsigned portBASE_TYPE uxReturn;

	uxReturn = uxQueueMessagesWaiting( pxQueue );
	portMPU_RESTORE_PRIORITY( xRunningPrivileged );
	return uxReturn;
}
/*-----------------------------------------------------------*/

signed portBASE_TYPE MPU_xQueueGenericReceive( xQueueHandle pxQueue, void * const pvBuffer, portTickType xTicksToWait, portBASE_TYPE xJustPeeking )
{
portBASE_TYPE xRunningPrivileged = xPortRaisePrivilege();
signed portBASE_TYPE xReturn;

	xReturn = xQueueGenericReceive( pxQueue, pvBuffer, xTicksToWait, xJustPeeking );
	portMPU_RESTORE_PRIORITY( xRunningPrivileged );
	return xReturn;
}
/*-----------------------------------------------------------*/

#if ( configUSE_MUTEXES == 1 )
	xQueueHandle MPU_xQueueCreateMutex( void )
	{
    xQueueHandle xReturn;
	portBASE_TYPE xRunningPrivileged = xPortRaisePrivilege();

		xReturn = xQueueCreateMutex();
		portMPU_RESTORE_PRIORITY( xRunningPrivileged );
		return xReturn;
	}
#endif
/*-----------------------------------------------------------*/

#if configUSE_COUNTING_SEMAPHORES == 1
	xQueueHandle MPU_xQueueCreateCountingSemaphore( unsigned portBASE_TYPE uxCountValue, unsigned portBASE_TYPE uxInitialCount )
	{
    xQueueHandle xReturn;
	portBASE_TYPE xRunningPrivileged = xPortRaisePrivilege();

		xReturn = (xQueueHandle) xQueueCreateCountingSemaphore( uxCountValue, uxInitialCount );
		portMPU_RESTORE_PRIORITY( xRunningPrivileged );
		return xReturn;
	}
#endif
/*-----------------------------------------------------------*/

#if ( configUSE_MUTEXES == 1 )
	portBASE_TYPE MPU_xQueueTakeMutexRecursive( xQueueHandle xMutex, portTickType xBlockTime )
	{
	portBASE_TYPE xReturn;
	portBASE_TYPE xRunningPrivileged = xPortRaisePrivilege();

		xReturn = xQueueTakeMutexRecursive( xMutex, xBlockTime );
		portMPU_RESTORE_PRIORITY( xRunningPrivileged );
		return xReturn;
	}
#endif
/*-----------------------------------------------------------*/

#if ( configUSE_MUTEXES == 1 )
	portBASE_TYPE MPU_xQueueGiveMutexRecursive( xQueueHandle xMutex )
	{
	portBASE_TYPE xReturn;
	portBASE_TYPE xRunningPrivileged = xPortRaisePrivilege();

		xReturn = xQueueGiveMutexRecursive( xMutex );
		portMPU_RESTORE_PRIORITY( xRunningPrivileged );
		return xReturn;
	}
#endif
/*-----------------------------------------------------------*/

#if configUSE_ALTERNATIVE_API == 1
	signed portBASE_TYPE MPU_xQueueAltGenericSend( xQueueHandle pxQueue, const void * const pvItemToQueue, portTickType xTicksToWait, portBASE_TYPE xCopyPosition )
	{
   	signed portBASE_TYPE xReturn;
	portBASE_TYPE xRunningPrivileged = xPortRaisePrivilege();

		xReturn = 	signed portBASE_TYPE xQueueAltGenericSend( pxQueue, pvItemToQueue, xTicksToWait, xCopyPosition );
		portMPU_RESTORE_PRIORITY( xRunningPrivileged );
		return xReturn;
	}
#endif
/*-----------------------------------------------------------*/

#if configUSE_ALTERNATIVE_API == 1
	signed portBASE_TYPE MPU_xQueueAltGenericReceive( xQueueHandle pxQueue, void * const pvBuffer, portTickType xTicksToWait, portBASE_TYPE xJustPeeking )
	{
    signed portBASE_TYPE xReturn;
	portBASE_TYPE xRunningPrivileged = xPortRaisePrivilege();

		xReturn = xQueueAltGenericReceive( pxQueue, pvBuffer, xTicksToWait, xJustPeeking );
		portMPU_RESTORE_PRIORITY( xRunningPrivileged );
		return xReturn;
	}
#endif
/*-----------------------------------------------------------*/

#if configQUEUE_REGISTRY_SIZE > 0
	void MPU_vQueueAddToRegistry( xQueueHandle xQueue, signed char *pcName )
	{
	portBASE_TYPE xRunningPrivileged = xPortRaisePrivilege();

		vQueueAddToRegistry( xQueue, pcName );

		portMPU_RESTORE_PRIORITY( xRunningPrivileged );
	}
#endif
/*-----------------------------------------------------------*/

void *MPU_pvPortMalloc( size_t xSize )
{
void *pvReturn;
portBASE_TYPE xRunningPrivileged = xPortRaisePrivilege();

	pvReturn = pvPortMalloc( xSize );

	portMPU_RESTORE_PRIORITY( xRunningPrivileged );

	return pvReturn;
}
/*-----------------------------------------------------------*/

void MPU_vPortFree( void *pv )
{
portBASE_TYPE xRunningPrivileged = xPortRaisePrivilege();

	vPortFree( pv );

	portMPU_RESTORE_PRIORITY( xRunningPrivileged );
}
/*-----------------------------------------------------------*/

size_t xPortGetFreeHeapSize( void )
{
	/* This just exists to keep the linker quiet. */
extern unsigned long _lc_ub_heap[];		/* Heap */
extern unsigned long _lc_ue_heap[];		/* Heap end */
	return (size_t)( _lc_ue_heap - _lc_ub_heap );
}
/*-----------------------------------------------------------*/

void vPortInitialiseBlocks( void )
{
	/* This just exists to keep the linker quiet. */
}
/*-----------------------------------------------------------*/

void MPU_vPortInitialiseBlocks( void )
{
portBASE_TYPE xRunningPrivileged = xPortRaisePrivilege();

	vPortInitialiseBlocks();

	portMPU_RESTORE_PRIORITY( xRunningPrivileged );
}
/*-----------------------------------------------------------*/

size_t MPU_xPortGetFreeHeapSize( void )
{
size_t xReturn;
portBASE_TYPE xRunningPrivileged = xPortRaisePrivilege();

	xReturn = xPortGetFreeHeapSize();

	portMPU_RESTORE_PRIORITY( xRunningPrivileged );

	return xReturn;
}

#endif /* configUSE_MPU */
