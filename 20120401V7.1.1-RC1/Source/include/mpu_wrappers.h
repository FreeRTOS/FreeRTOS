/*
    FreeRTOS V7.1.0 - Copyright (C) 2011 Real Time Engineers Ltd.


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

#ifndef MPU_WRAPPERS_H
#define MPU_WRAPPERS_H

/* This file redefines API functions to be called through a wrapper macro, but
only for ports that are using the MPU. */
#ifdef portUSING_MPU_WRAPPERS

	/* MPU_WRAPPERS_INCLUDED_FROM_API_FILE will be defined when this file is
	included from queue.c or task.c to prevent it from having an effect within
	those files. */
	#ifndef MPU_WRAPPERS_INCLUDED_FROM_API_FILE

		#define xTaskGenericCreate				MPU_xTaskGenericCreate
		#define vTaskAllocateMPURegions			MPU_vTaskAllocateMPURegions
		#define vTaskDelete						MPU_vTaskDelete
		#define vTaskDelayUntil					MPU_vTaskDelayUntil
		#define vTaskDelay						MPU_vTaskDelay
		#define uxTaskPriorityGet				MPU_uxTaskPriorityGet
		#define vTaskPrioritySet				MPU_vTaskPrioritySet
		#define vTaskSuspend					MPU_vTaskSuspend
		#define xTaskIsTaskSuspended			MPU_xTaskIsTaskSuspended
		#define vTaskResume						MPU_vTaskResume
		#define vTaskSuspendAll					MPU_vTaskSuspendAll
		#define xTaskResumeAll					MPU_xTaskResumeAll
		#define xTaskGetTickCount				MPU_xTaskGetTickCount
		#define uxTaskGetNumberOfTasks			MPU_uxTaskGetNumberOfTasks
		#define vTaskList						MPU_vTaskList
		#define vTaskGetRunTimeStats			MPU_vTaskGetRunTimeStats
		#define vTaskStartTrace					MPU_vTaskStartTrace
		#define ulTaskEndTrace					MPU_ulTaskEndTrace
		#define vTaskSetApplicationTaskTag		MPU_vTaskSetApplicationTaskTag
		#define xTaskGetApplicationTaskTag		MPU_xTaskGetApplicationTaskTag
		#define xTaskCallApplicationTaskHook	MPU_xTaskCallApplicationTaskHook
		#define uxTaskGetStackHighWaterMark		MPU_uxTaskGetStackHighWaterMark
		#define xTaskGetCurrentTaskHandle		MPU_xTaskGetCurrentTaskHandle
		#define xTaskGetSchedulerState			MPU_xTaskGetSchedulerState

		#define xQueueGenericCreate				MPU_xQueueGenericCreate
		#define xQueueCreateMutex				MPU_xQueueCreateMutex
		#define xQueueGiveMutexRecursive		MPU_xQueueGiveMutexRecursive
		#define xQueueTakeMutexRecursive		MPU_xQueueTakeMutexRecursive
		#define xQueueCreateCountingSemaphore	MPU_xQueueCreateCountingSemaphore
		#define xQueueGenericSend				MPU_xQueueGenericSend
		#define xQueueAltGenericSend			MPU_xQueueAltGenericSend
		#define xQueueAltGenericReceive			MPU_xQueueAltGenericReceive
		#define xQueueGenericReceive			MPU_xQueueGenericReceive
		#define uxQueueMessagesWaiting			MPU_uxQueueMessagesWaiting
		#define vQueueDelete					MPU_vQueueDelete

		#define pvPortMalloc					MPU_pvPortMalloc
		#define vPortFree						MPU_vPortFree
		#define xPortGetFreeHeapSize			MPU_xPortGetFreeHeapSize
		#define vPortInitialiseBlocks			MPU_vPortInitialiseBlocks

		#if configQUEUE_REGISTRY_SIZE > 0
			#define vQueueAddToRegistry				MPU_vQueueAddToRegistry
			#define vQueueUnregisterQueue			MPU_vQueueUnregisterQueue
		#endif

		/* Remove the privileged function macro. */
		#define PRIVILEGED_FUNCTION

	#else /* MPU_WRAPPERS_INCLUDED_FROM_API_FILE */

		/* Ensure API functions go in the privileged execution section. */
		#define PRIVILEGED_FUNCTION __attribute__((section("privileged_functions")))
		#define PRIVILEGED_DATA __attribute__((section("privileged_data")))
        //#define PRIVILEGED_DATA

	#endif /* MPU_WRAPPERS_INCLUDED_FROM_API_FILE */

#else /* portUSING_MPU_WRAPPERS */

	#define PRIVILEGED_FUNCTION
	#define PRIVILEGED_DATA
	#define portUSING_MPU_WRAPPERS 0

#endif /* portUSING_MPU_WRAPPERS */


#endif /* MPU_WRAPPERS_H */

