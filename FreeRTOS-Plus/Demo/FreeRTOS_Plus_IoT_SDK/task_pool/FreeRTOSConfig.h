/*
 * FreeRTOS Kernel V10.2.1
 * Copyright (C) 2017 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

#ifndef FREERTOS_CONFIG_H
#define FREERTOS_CONFIG_H

/*-----------------------------------------------------------
 * Application specific definitions.
 *
 * These definitions should be adjusted for your particular hardware and
 * application requirements.
 *
 * THESE PARAMETERS ARE DESCRIBED WITHIN THE 'CONFIGURATION' SECTION OF THE
 * FreeRTOS API DOCUMENTATION AVAILABLE ON THE FreeRTOS.org WEB SITE.
 * http://www.freertos.org/a00110.html
 *
 * The bottom of this file contains some constants specific to running the UDP
 * stack in this demo.  Constants specific to FreeRTOS+TCP itself (rather than
 * the demo) are contained in FreeRTOSIPConfig.h.
 *----------------------------------------------------------*/
#define configUSE_PREEMPTION					1
#define configUSE_PORT_OPTIMISED_TASK_SELECTION	1
#define configMAX_PRIORITIES					( 7 )
#define configTICK_RATE_HZ						( 1000 ) /* In this non-real time simulated environment the tick frequency has to be at least a multiple of the Win32 tick frequency, and therefore very slow. */
#define configMINIMAL_STACK_SIZE				( ( unsigned short ) 60 ) /* In this simulated case, the stack only has to hold one small structure as the real stack is part of the Win32 thread. */
#define configTOTAL_HEAP_SIZE					( ( size_t ) ( 2048U * 1024U ) )
#define configMAX_TASK_NAME_LEN					( 15 )
#define configUSE_TRACE_FACILITY				1
#define configUSE_16_BIT_TICKS					0
#define configIDLE_SHOULD_YIELD					1
#define configUSE_CO_ROUTINES 					0
#define configUSE_MUTEXES						1
#define configUSE_RECURSIVE_MUTEXES				1
#define configQUEUE_REGISTRY_SIZE				0
#define configUSE_APPLICATION_TASK_TAG			0
#define configUSE_COUNTING_SEMAPHORES			1
#define configUSE_ALTERNATIVE_API				0
#define configNUM_THREAD_LOCAL_STORAGE_POINTERS	0
#define configENABLE_BACKWARD_COMPATIBILITY		1
#define configSUPPORT_STATIC_ALLOCATION			1

/* Hook function related definitions. */
#define configUSE_TICK_HOOK				0
#define configUSE_IDLE_HOOK				1
#define configUSE_MALLOC_FAILED_HOOK	1
#define configCHECK_FOR_STACK_OVERFLOW	0 /* Not applicable to the Win32 port. */

/* Software timer related definitions. */
#define configUSE_TIMERS				1
#define configTIMER_TASK_PRIORITY		( configMAX_PRIORITIES - 1 )
#define configTIMER_QUEUE_LENGTH		5
#define configTIMER_TASK_STACK_DEPTH	( configMINIMAL_STACK_SIZE * 2 )

/* Event group related definitions. */
#define configUSE_EVENT_GROUPS			1

/* Run time stats gathering definitions. */
#define configGENERATE_RUN_TIME_STATS	0

/* Co-routine definitions. */
#define configUSE_CO_ROUTINES 			0
#define configMAX_CO_ROUTINE_PRIORITIES ( 2 )

/* Set the following definitions to 1 to include the API function, or zero
to exclude the API function. */
#define INCLUDE_vTaskPrioritySet				1
#define INCLUDE_uxTaskPriorityGet				1
#define INCLUDE_vTaskDelete						1
#define INCLUDE_vTaskCleanUpResources			0
#define INCLUDE_vTaskSuspend					1
#define INCLUDE_vTaskDelayUntil					1
#define INCLUDE_vTaskDelay						1
#define INCLUDE_uxTaskGetStackHighWaterMark		1
#define INCLUDE_xTaskGetSchedulerState			1
#define INCLUDE_xTimerGetTimerTaskHandle		0
#define INCLUDE_xTaskGetIdleTaskHandle			0
#define INCLUDE_xQueueGetMutexHolder			1
#define INCLUDE_eTaskGetState					1
#define INCLUDE_xEventGroupSetBitsFromISR		1
#define INCLUDE_xTimerPendFunctionCall			1
#define INCLUDE_pcTaskGetTaskName				1

/* This demo makes use of one or more example stats formatting functions.  These
format the raw data provided by the uxTaskGetSystemState() function in to human
readable ASCII form.  See the notes in the implementation of vTaskList() within
FreeRTOS/Source/tasks.c for limitations.  configUSE_STATS_FORMATTING_FUNCTIONS
is set to 2 so the formatting functions are included without the stdio.h being
included in tasks.c.  That is because this project defines its own sprintf()
functions. */
#define configUSE_STATS_FORMATTING_FUNCTIONS	1

/* Assert call defined for debug builds. */
#ifdef _DEBUG
	extern void vAssertCalled( const char *pcFile, uint32_t ulLine );
	#define configASSERT( x ) if( ( x ) == 0 ) vAssertCalled( __FILE__, __LINE__ )
#endif /* _DEBUG */



/* Application specific definitions follow. **********************************/

/* Only used when running in the FreeRTOS Windows simulator.  Defines the
priority of the task used to simulate Ethernet interrupts. */
#define configMAC_ISR_SIMULATOR_PRIORITY	( configMAX_PRIORITIES - 1 )

/* This demo creates a virtual network connection by accessing the raw Ethernet
or WiFi data to and from a real network connection.  Many computers have more
than one real network port, and configNETWORK_INTERFACE_TO_USE is used to tell
the demo which real port should be used to create the virtual port.  The ports
available are displayed on the console when the application is executed.  For
example, on my development laptop setting configNETWORK_INTERFACE_TO_USE to 4
results in the wired network being used, while setting
configNETWORK_INTERFACE_TO_USE to 2 results in the wireless network being
used. */
#define configNETWORK_INTERFACE_TO_USE 4L

/* The address of an echo server that will be used by the two demo echo client
tasks.
http://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_Echo_Clients.html
http://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/UDP_Echo_Clients.html */
#define configECHO_SERVER_ADDR0	192
#define configECHO_SERVER_ADDR1 168
#define configECHO_SERVER_ADDR2 0
#define configECHO_SERVER_ADDR3 11

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
#define configIP_ADDR0		10
#define configIP_ADDR1		10
#define configIP_ADDR2		10
#define configIP_ADDR3		200

/* Default gateway IP address configuration.  Used in ipconfigUSE_DNS is set to
0, or ipconfigUSE_DNS is set to 1 but a DNS server cannot be contacted. */
#define configGATEWAY_ADDR0	10
#define configGATEWAY_ADDR1	10
#define configGATEWAY_ADDR2	10
#define configGATEWAY_ADDR3	1

/* Default DNS server configuration.  OpenDNS addresses are 208.67.222.222 and
208.67.220.220.  Used in ipconfigUSE_DNS is set to 0, or ipconfigUSE_DNS is set
to 1 but a DNS server cannot be contacted.*/
#define configDNS_SERVER_ADDR0 	208
#define configDNS_SERVER_ADDR1 	67
#define configDNS_SERVER_ADDR2 	222
#define configDNS_SERVER_ADDR3 	222

/* Default netmask configuration.  Used in ipconfigUSE_DNS is set to 0, or
ipconfigUSE_DNS is set to 1 but a DNS server cannot be contacted. */
#define configNET_MASK0		255
#define configNET_MASK1		0
#define configNET_MASK2		0
#define configNET_MASK3		0

/* The UDP port to which print messages are sent. */
#define configPRINT_PORT	( 15000 )

#if( defined( _MSC_VER ) && ( _MSC_VER <= 1600 ) && !defined( snprintf ) )
	/* Map to Windows names. */
	#define snprintf	_snprintf
	#define vsnprintf	_vsnprintf
#endif

/* Visual studio does not have an implementation of strcasecmp(). */
#define strcasecmp _stricmp
#define strncasecmp _strnicmp
#define strcmpi _strcmpi

#endif /* FREERTOS_CONFIG_H */

