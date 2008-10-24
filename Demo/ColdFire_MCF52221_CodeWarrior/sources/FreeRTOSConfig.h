/*
	FreeRTOS.org V5.1.0 - Copyright (C) 2003-2008 Richard Barry.

	This file is part of the FreeRTOS.org distribution.

	FreeRTOS.org is free software; you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation; either version 2 of the License, or
	(at your option) any later version.

	FreeRTOS.org is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with FreeRTOS.org; if not, write to the Free Software
	Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

	A special exception to the GPL can be applied should you wish to distribute
	a combined work that includes FreeRTOS.org, without being obliged to provide
	the source code for any proprietary components.  See the licensing section
	of http://www.FreeRTOS.org for full details of how and when the exception
	can be applied.

    ***************************************************************************
    ***************************************************************************
    *                                                                         *
    * SAVE TIME AND MONEY!  We can port FreeRTOS.org to your own hardware,    *
    * and even write all or part of your application on your behalf.          *
    * See http://www.OpenRTOS.com for details of the services we provide to   *
    * expedite your project.                                                  *
    *                                                                         *
    ***************************************************************************
    ***************************************************************************

	Please ensure to read the configuration and relevant port sections of the
	online documentation.

	http://www.FreeRTOS.org - Documentation, latest information, license and
	contact details.

	http://www.SafeRTOS.com - A version that is certified for use in safety
	critical systems.

	http://www.OpenRTOS.com - Commercial support, development, porting,
	licensing and training services.
*/

#ifndef FREERTOS_CONFIG_H
#define FREERTOS_CONFIG_H

#include "support_common.h"

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
#define configUSE_IDLE_HOOK				1
#define configUSE_TICK_HOOK				0
#define configCPU_CLOCK_HZ				( ( unsigned portLONG ) 80000000 )
#define configTICK_RATE_HZ				( ( portTickType ) 100 )
#define configMINIMAL_STACK_SIZE		( ( unsigned portSHORT ) 100 )
#define configTOTAL_HEAP_SIZE			( ( size_t ) ( 15000 ) )
#define configMAX_TASK_NAME_LEN			( 12 )
#define configUSE_TRACE_FACILITY		1
#define configUSE_16_BIT_TICKS			0
#define configIDLE_SHOULD_YIELD			0
#define configUSE_CO_ROUTINES 			1
#define configUSE_MUTEXES				1
#define configCHECK_FOR_STACK_OVERFLOW	2
#define configUSE_RECURSIVE_MUTEXES		1
#define configQUEUE_REGISTRY_SIZE		0
#define configUSE_COUNTING_SEMAPHORES	0

#define configMAX_PRIORITIES		( ( unsigned portBASE_TYPE ) 6 )
#define configMAX_CO_ROUTINE_PRIORITIES ( 2 )

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

#define configYIELD_INTERRUPT_VECTOR			16UL
#define configKERNEL_INTERRUPT_PRIORITY 		1
#define configMAX_SYSCALL_INTERRUPT_PRIORITY 	4

void vApplicationSetupInterrupts( void );

/* Ethernet configuration. */
#define configMAC_0	0x00
#define configMAC_1	0x04
#define configMAC_2	0x9F
#define configMAC_3	0x00
#define configMAC_4	0xAB
#define configMAC_5	0x2B

#define configIP_ADDR0	192
#define configIP_ADDR1	168
#define configIP_ADDR2	0
#define configIP_ADDR3	11

#define configGW_ADDR0	172
#define configGW_ADDR1	25
#define configGW_ADDR2	218
#define configGW_ADDR3	3

#define configNET_MASK0	255
#define configNET_MASK1	255
#define configNET_MASK2	255
#define configNET_MASK3	0

#define configNUM_FEC_TX_BUFFERS	2
#define configNUM_FEC_RX_BUFFERS	4
#define configFEC_BUFFER_SIZE		1520
#define configUSE_PROMISCUOUS_MODE	0
#define configETHERNET_INPUT_TASK_STACK_SIZE ( 320 )
#define configETHERNET_INPUT_TASK_PRIORITY ( configMAX_PRIORITIES - 1 )

#define configPHY_ADDRESS	1

#if ( configFEC_BUFFER_SIZE & 0x0F ) != 0
	#error configFEC_BUFFER_SIZE must be a multiple of 16.
#endif

#endif /* FREERTOS_CONFIG_H */
