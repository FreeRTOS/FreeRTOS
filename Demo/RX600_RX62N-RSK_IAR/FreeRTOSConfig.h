/*
    FreeRTOS V6.1.1 - Copyright (C) 2011 Real Time Engineers Ltd.

    ***************************************************************************
    *                                                                         *
    * If you are:                                                             *
    *                                                                         *
    *    + New to FreeRTOS,                                                   *
    *    + Wanting to learn FreeRTOS or multitasking in general quickly       *
    *    + Looking for basic training,                                        *
    *    + Wanting to improve your FreeRTOS skills and productivity           *
    *                                                                         *
    * then take a look at the FreeRTOS books - available as PDF or paperback  *
    *                                                                         *
    *        "Using the FreeRTOS Real Time Kernel - a Practical Guide"        *
    *                  http://www.FreeRTOS.org/Documentation                  *
    *                                                                         *
    * A pdf reference manual is also available.  Both are usually delivered   *
    * to your inbox within 20 minutes to two hours when purchased between 8am *
    * and 8pm GMT (although please allow up to 24 hours in case of            *
    * exceptional circumstances).  Thank you for your support!                *
    *                                                                         *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.
    ***NOTE*** The exception to the GPL is included to allow you to distribute
    a combined work that includes FreeRTOS without being obliged to provide the
    source code for proprietary components outside of the FreeRTOS kernel.
    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT
    ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
    FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
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

#ifndef FREERTOS_CONFIG_H
#define FREERTOS_CONFIG_H

/* Board specifics. */
#include "rskrx62ndef.h"

/*-----------------------------------------------------------
 * Application specific definitions.
 *
 * These definitions should be adjusted for your particular hardware and
 * application requirements.
 *
 * THESE PARAMETERS ARE DESCRIBED WITHIN THE 'CONFIGURATION' SECTION OF THE
 * FreeRTOS API DOCUMENTATION AVAILABLE ON THE FreeRTOS.org WEB SITE.
 *
 * See http://www.freertos.org/a00110.html.
 *----------------------------------------------------------*/

#define configUSE_PREEMPTION			1
#define configUSE_IDLE_HOOK				0
#define configUSE_TICK_HOOK				0
#define configCPU_CLOCK_HZ				( ICLK_FREQUENCY ) /* Set in rskrx62ndef.h. */
#define configPERIPHERAL_CLOCK_HZ		( PCLK_FREQUENCY ) /* Set in rskrx62ndef.h. */
#define configTICK_RATE_HZ				( ( portTickType ) 1000 )
#define configMINIMAL_STACK_SIZE		( ( unsigned short ) 140 )
#define configTOTAL_HEAP_SIZE			( ( size_t ) ( 45 * 1024 ) )
#define configMAX_TASK_NAME_LEN			( 12 )
#define configUSE_TRACE_FACILITY		1
#define configUSE_16_BIT_TICKS			0
#define configIDLE_SHOULD_YIELD			1
#define configUSE_CO_ROUTINES 			0
#define configUSE_MUTEXES				1
#define configGENERATE_RUN_TIME_STATS	1
#define configCHECK_FOR_STACK_OVERFLOW	2
#define configUSE_RECURSIVE_MUTEXES		1
#define configQUEUE_REGISTRY_SIZE		0
#define configUSE_MALLOC_FAILED_HOOK	1
#define configUSE_APPLICATION_TASK_TAG	0

#define configMAX_PRIORITIES			( ( unsigned portBASE_TYPE ) 7 )
#define configMAX_CO_ROUTINE_PRIORITIES ( 2 )


/* 
The interrupt priority used by the kernel itself for the tick interrupt and
the pended interrupt is set by configKERNEL_INTERRUPT_PRIORITY.  This would 
normally be the lowest priority (1 in this case).  The maximum interrupt 
priority from which FreeRTOS API calls can be made is set by
configMAX_SYSCALL_INTERRUPT_PRIORITY.  Interrupts that use a priority above this 
will not be effected by anything the kernel is doing.  Interrupts at or below
this priority can use FreeRTOS API functions - but *only* those that end in
"FromISR".  Both these constants are defined in 'PriorityDefinitions.h' so they
can also be included in assembly source files.
*/
#include "PriorityDefinitions.h"


/* The peripheral used to generate the tick interrupt is configured as part of
the application code.  This constant should be set to the vector number of the
peripheral chosen.  As supplied this is CMT0. */
#define configTICK_VECTOR				28 /*VECT_CMT0_CMI0*/

/* Set the following definitions to 1 to include the API function, or zero
to exclude the API function. */

#define INCLUDE_vTaskPrioritySet			1
#define INCLUDE_uxTaskPriorityGet			1
#define INCLUDE_vTaskDelete					1
#define INCLUDE_vTaskCleanUpResources		0
#define INCLUDE_vTaskSuspend				1
#define INCLUDE_vTaskDelayUntil				1
#define INCLUDE_vTaskDelay					1
#define INCLUDE_uxTaskGetStackHighWaterMark	1
#define INCLUDE_xTaskGetSchedulerState		1

extern volatile unsigned long ulHighFrequencyTickCount;
#define portCONFIGURE_TIMER_FOR_RUN_TIME_STATS() portNOP() /* Run time stats use the same timer as the high frequency timer test. */
#define portGET_RUN_TIME_COUNTER_VALUE() ulHighFrequencyTickCount


/* Override some of the priorities set in the common demo tasks.  This is
required to ensure flase positive timing errors are not reported. */
#define bktPRIMARY_PRIORITY		( configMAX_PRIORITIES - 3 )
#define bktSECONDARY_PRIORITY	( configMAX_PRIORITIES - 4 )
#define intqHIGHER_PRIORITY		( configMAX_PRIORITIES - 3 )


/*-----------------------------------------------------------
 * Ethernet configuration.
 *-----------------------------------------------------------*/

/* MAC address configuration. */
#define configMAC_ADDR0	0x00
#define configMAC_ADDR1	0x12
#define configMAC_ADDR2	0x13
#define configMAC_ADDR3	0x10
#define configMAC_ADDR4	0x15
#define configMAC_ADDR5	0x11

/* IP address configuration. */
#define configIP_ADDR0		192
#define configIP_ADDR1		168
#define configIP_ADDR2		0
#define configIP_ADDR3		200

/* Netmask configuration. */
#define configNET_MASK0		255
#define configNET_MASK1		255
#define configNET_MASK2		255
#define configNET_MASK3		0

#endif /* FREERTOS_CONFIG_H */
