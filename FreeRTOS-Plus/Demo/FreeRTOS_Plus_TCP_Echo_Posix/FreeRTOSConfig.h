/*
 * FreeRTOS V202107.00
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
 * https://github.com/FreeRTOS
 *
 */
#ifndef FREERTOS_CONFIG_H
#define FREERTOS_CONFIG_H

/*-----------------------------------------------------------
 * Application specific definitions.
 *
 * These definitions should be adjusted for your particular hardware and
 * application requirements.
 *
 * THESE PARAMETERS ARE DESCRIBED WITHIN THE 'CONFIGURATION' SECTION OF THE
 * FreeRTOS API DOCUMENTATION AVAILABLE ON THE FreeRTOS.org WEB SITE.  See
 * http://www.freertos.org/a00110.html
 *----------------------------------------------------------*/

#define configUSE_PREEMPTION					1
#define configUSE_PORT_OPTIMISED_TASK_SELECTION	0
#define configUSE_IDLE_HOOK						1
#define configUSE_TICK_HOOK						1
#define configUSE_DAEMON_TASK_STARTUP_HOOK		1
#define configTICK_RATE_HZ						( 1000 ) /* In this non-real time simulated environment the tick frequency has to be at least a multiple of the Win32 tick frequency, and therefore very slow. */
#define configMINIMAL_STACK_SIZE				( ( unsigned short ) 70 ) /* In this simulated case, the stack only has to hold one small structure as the real stack is part of the win32 thread. */
#define configTOTAL_HEAP_SIZE					( ( size_t ) ( 65 * 1024 ) )
#define configMAX_TASK_NAME_LEN					( 12 )
#define configUSE_TRACE_FACILITY				1
#define configUSE_16_BIT_TICKS					0
#define configIDLE_SHOULD_YIELD					1
#define configUSE_MUTEXES						1
#define configCHECK_FOR_STACK_OVERFLOW			0
#define configUSE_RECURSIVE_MUTEXES				1
#define configQUEUE_REGISTRY_SIZE				20
#define configUSE_APPLICATION_TASK_TAG			1
#define configUSE_COUNTING_SEMAPHORES			1
#define configUSE_ALTERNATIVE_API				0
#define configUSE_QUEUE_SETS					1
#define configUSE_TASK_NOTIFICATIONS			1
#define configSUPPORT_STATIC_ALLOCATION			1

/* Software timer related configuration options.  The maximum possible task
priority is configMAX_PRIORITIES - 1.  The priority of the timer task is
deliberately set higher to ensure it is correctly capped back to
configMAX_PRIORITIES - 1. */
#define configUSE_TIMERS						1
#define configTIMER_TASK_PRIORITY				( configMAX_PRIORITIES - 1 )
#define configTIMER_QUEUE_LENGTH				20
#define configTIMER_TASK_STACK_DEPTH			( configMINIMAL_STACK_SIZE * 2 )

#define configMAX_PRIORITIES					( 7 )

/* Run time stats gathering configuration options. */
unsigned long ulGetRunTimeCounterValue( void ); /* Prototype of function that returns run time counter. */
void vConfigureTimerForRunTimeStats( void );	/* Prototype of function that initialises the run time counter. */
#define configGENERATE_RUN_TIME_STATS			1

/* Co-routine related configuration options. */
#define configUSE_CO_ROUTINES 					0
#define configMAX_CO_ROUTINE_PRIORITIES			( 2 )

/* This demo can use of one or more example stats formatting functions.  These
format the raw data provided by the uxTaskGetSystemState() function in to human
readable ASCII form.  See the notes in the implementation of vTaskList() within
FreeRTOS/Source/tasks.c for limitations. */
#define configUSE_STATS_FORMATTING_FUNCTIONS	0

/* Enables the test whereby a stack larger than the total heap size is
requested. */
#define configSTACK_DEPTH_TYPE uint32_t

/* Set the following definitions to 1 to include the API function, or zero
to exclude the API function.  In most cases the linker will remove unused
functions anyway. */
#define INCLUDE_vTaskPrioritySet				1
#define INCLUDE_uxTaskPriorityGet				1
#define INCLUDE_vTaskDelete						1
#define INCLUDE_vTaskCleanUpResources			0
#define INCLUDE_vTaskSuspend					1
#define INCLUDE_vTaskDelayUntil					1
#define INCLUDE_vTaskDelay						1
#define INCLUDE_uxTaskGetStackHighWaterMark		1
#define INCLUDE_uxTaskGetStackHighWaterMark2	1
#define INCLUDE_xTaskGetSchedulerState			1
#define INCLUDE_xTimerGetTimerDaemonTaskHandle	1
#define INCLUDE_xTaskGetIdleTaskHandle			1
#define INCLUDE_xTaskGetHandle					1
#define INCLUDE_eTaskGetState					1
#define INCLUDE_xSemaphoreGetMutexHolder		1
#define INCLUDE_xTimerPendFunctionCall			1
#define INCLUDE_xTaskAbortDelay					1

#define configINCLUDE_MESSAGE_BUFFER_AMP_DEMO	0
#if ( configINCLUDE_MESSAGE_BUFFER_AMP_DEMO == 1 )
	extern void vGenerateCoreBInterrupt( void * xUpdatedMessageBuffer );
	#define sbSEND_COMPLETED( pxStreamBuffer ) vGenerateCoreBInterrupt( pxStreamBuffer )
#endif /* configINCLUDE_MESSAGE_BUFFER_AMP_DEMO */

extern void vAssertCalled( const char * const pcFileName,  unsigned long ulLine );

/* projCOVERAGE_TEST should be defined on the command line so this file can be
used with multiple project configurations.  If it is
 */
#ifndef projCOVERAGE_TEST
	#error projCOVERAGE_TEST should be defined to 1 or 0 on the command line.
#endif

#if( projCOVERAGE_TEST == 1 )
	/* Insert NOPs in empty decision paths to ensure both true and false paths
	are being tested. */
	#define mtCOVERAGE_TEST_MARKER() __asm volatile( "NOP" )

	/* Ensure the tick count overflows during the coverage test. */
	#define configINITIAL_TICK_COUNT 0xffffd800UL

	/* Allows tests of trying to allocate more than the heap has free. */
	#define configUSE_MALLOC_FAILED_HOOK			0

	/* To test builds that remove the static qualifier for debug builds. */
	#define portREMOVE_STATIC_QUALIFIER
#else
	/* It is a good idea to define configASSERT() while developing.  configASSERT()
	uses the same semantics as the standard C assert() macro.  Don't define
	configASSERT() when performing code coverage tests though, as it is not
	intended to asserts() to fail, some some code is intended not to run if no
	errors are present. */
	#define configASSERT( x ) if( ( x ) == 0 ) vAssertCalled(  __FILE__, __LINE__ )

	#define configUSE_MALLOC_FAILED_HOOK			1

	/* Include the FreeRTOS+Trace FreeRTOS trace macro definitions. */
	#include "trcRecorder.h"
#endif

/* networking definitions */
#define configMAC_ISR_SIMULATOR_PRIORITY	( configMAX_PRIORITIES - 1 )
#define ipconfigUSE_NETWORK_EVENT_HOOK 1
//#define ipconfigSOCK_DEFAULT_RECEIVE_BLOCK_TIME  pdMS_TO_TICKS(5000)
#define configNETWORK_INTERFACE_TO_USE 1L

/* The address of an echo server that will be used by the two demo echo client
tasks.
http://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_Echo_Clients.html
http://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/UDP_Echo_Clients.html */

#define configECHO_SERVER_ADDR0	172
#define configECHO_SERVER_ADDR1 19
#define configECHO_SERVER_ADDR2 195
#define configECHO_SERVER_ADDR3 36

/* Default MAC address configuration.  The demo creates a virtual network
connection that uses this MAC address by accessing the raw Ethernet/WiFi data
to and from a real network connection on the host PC.  See the
configNETWORK_INTERFACE_TO_USE definition above for information on how to
configure the real network connection to use. */
#define configMAC_ADDR0		0x00
#define configMAC_ADDR1		0x11
#define configMAC_ADDR2		0x22
#define configMAC_ADDR3		0x33
#define configMAC_ADDR4		0x44
#define configMAC_ADDR5		0x41

/* Default IP address configuration.  Used in ipconfigUSE_DNS is set to 0, or
ipconfigUSE_DNS is set to 1 but a DNS server cannot be contacted. */

#define configIP_ADDR0		172
#define configIP_ADDR1		19
#define configIP_ADDR2		195
#define configIP_ADDR3		37

/* Default gateway IP address configuration.  Used in ipconfigUSE_DNS is set to
0, or ipconfigUSE_DNS is set to 1 but a DNS server cannot be contacted. */

#define configGATEWAY_ADDR0	172
#define configGATEWAY_ADDR1	19
#define configGATEWAY_ADDR2	192
#define configGATEWAY_ADDR3	1

/* Default DNS server configuration.  OpenDNS addresses are 208.67.222.222 and
208.67.220.220.  Used in ipconfigUSE_DNS is set to 0, or ipconfigUSE_DNS is set
to 1 but a DNS server cannot be contacted.*/

#define configDNS_SERVER_ADDR0	10
#define configDNS_SERVER_ADDR1  4
#define configDNS_SERVER_ADDR2	4
#define configDNS_SERVER_ADDR3	10

/* Default netmask configuration.  Used in ipconfigUSE_DNS is set to 0, or
ipconfigUSE_DNS is set to 1 but a DNS server cannot be contacted. */
#define configNET_MASK0		255
#define configNET_MASK1	  255
#define configNET_MASK2	  240
#define configNET_MASK3		0

/* The UDP port to which print messages are sent. */
#define configPRINT_PORT	( 15000 )

#endif /* FREERTOS_CONFIG_H */
