/*
 * FreeRTOS Kernel V10.2.0
 * Copyright (C) 2019 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"

/**
 * @brief Size of the shared memory region.
 */
#define SHARED_MEMORY_SIZE 32

/**
 * @brief Memory region shared between two tasks.
 */
static uint8_t ucSharedMemory[ SHARED_MEMORY_SIZE ] __attribute__( ( aligned( 32 ) ) );

/**
 * @brief Memory region used to track Memory Fault intentionally caused by the
 * RO Access task.
 *
 * RO Access task sets ucROTaskFaultTracker[ 0 ] to 1 before accessing illegal
 * memory. Illegal memory access causes Memory Fault and the fault handler
 * checks ucROTaskFaultTracker[ 0 ] to see if this is an expected fault. We
 * recover gracefully from an expected fault by jumping to the next instruction.
 *
 * @note We are declaring a region of 32 bytes even though we need only one. The
 * reason is that the size of an MPU region must be a multiple of 32 bytes.
 */
static uint8_t ucROTaskFaultTracker[ SHARED_MEMORY_SIZE ] __attribute__( ( aligned( 32 ) ) ) = { 0 };
/*-----------------------------------------------------------*/

/**
 * @brief Implements the task which has Read Only access to the memory region
 * ucSharedMemory.
 *
 * @param pvParameters[in] Parameters as passed during task creation.
 */
static void prvROAccessTask( void * pvParameters );

/**
 * @brief Implements the task which has Read Write access to the memory region
 * ucSharedMemory.
 *
 * @param pvParameters[in] Parameters as passed during task creation.
 */
static void prvRWAccessTask( void * pvParameters );

/*-----------------------------------------------------------*/

static void prvROAccessTask( void * pvParameters )
{
uint8_t ucVal;

	/* Unused parameters. */
	( void ) pvParameters;

	for( ; ; )
	{
		/* This task has RO access to ucSharedMemory and therefore it can read
		 * it but cannot modify it. */
		ucVal = ucSharedMemory[ 0 ];

		/* Silent compiler warnings about unused variables. */
		( void ) ucVal;

		/* Since this task has Read Only access to the ucSharedMemory region,
		 * writing to it results in Memory Fault. Set ucROTaskFaultTracker[ 0 ]
		 * to 1 to tell the Memory Fault Handler that this is an expected fault.
		 * The handler will recover from this fault gracefully by jumping to the
		 * next instruction. */
		ucROTaskFaultTracker[ 0 ] = 1;

		/* Illegal access to generate Memory Fault. */
		ucSharedMemory[ 0 ] = 0;

		/* Wait for a second. */
		vTaskDelay( pdMS_TO_TICKS( 1000 ) );
	}
}
/*-----------------------------------------------------------*/

static void prvRWAccessTask( void * pvParameters )
{
	/* Unused parameters. */
	( void ) pvParameters;

	for( ; ; )
	{
		/* This task has RW access to ucSharedMemory and therefore can write to
		 * it. */
		ucSharedMemory[ 0 ] = 0;

		/* Wait for a second. */
		vTaskDelay( pdMS_TO_TICKS( 1000 ) );
	}
}
/*-----------------------------------------------------------*/

void vStartMPUDemo( void )
{
static StackType_t xROAccessTaskStack[ configMINIMAL_STACK_SIZE ] __attribute__( ( aligned( 32 ) ) );
static StackType_t xRWAccessTaskStack[ configMINIMAL_STACK_SIZE ] __attribute__( ( aligned( 32 ) ) );
TaskParameters_t xROAccessTaskParameters =
{
	.pvTaskCode		= prvROAccessTask,
	.pcName			= "ROAccess",
	.usStackDepth	= configMINIMAL_STACK_SIZE,
	.pvParameters	= NULL,
	.uxPriority		= tskIDLE_PRIORITY,
	.puxStackBuffer	= xROAccessTaskStack,
	.xRegions		=	{
							{ ucSharedMemory,		32,	tskMPU_REGION_READ_ONLY | tskMPU_REGION_EXECUTE_NEVER	},
							{ ucROTaskFaultTracker,	32,	tskMPU_REGION_READ_WRITE | tskMPU_REGION_EXECUTE_NEVER	},
							{ 0,					0,	0														},
						}
};
TaskParameters_t xRWAccessTaskParameters =
{
	.pvTaskCode		= prvRWAccessTask,
	.pcName			= "RWAccess",
	.usStackDepth	= configMINIMAL_STACK_SIZE,
	.pvParameters	= NULL,
	.uxPriority		= tskIDLE_PRIORITY,
	.puxStackBuffer	= xRWAccessTaskStack,
	.xRegions		=	{
							{ ucSharedMemory,	32,	tskMPU_REGION_READ_WRITE | tskMPU_REGION_EXECUTE_NEVER	},
							{ 0,				0,	0														},
							{ 0,				0,	0														},
						}
};

	/* Create an unprivileged task with RO access to ucSharedMemory. */
	xTaskCreateRestricted( &( xROAccessTaskParameters ), NULL );

	/* Create an unprivileged task with RW access to ucSharedMemory. */
	xTaskCreateRestricted( &( xRWAccessTaskParameters ), NULL );
}
/*-----------------------------------------------------------*/

void vHandleMemoryFault( uint32_t * pulFaultStackAddress )
{
uint32_t ulPC;

	/* Is this an expected fault? */
	if( ucROTaskFaultTracker[ 0 ] == 1 )
	{
		/* Read program counter. */
		ulPC = pulFaultStackAddress[ 6 ];

		/* Increment the program counter by 2 to move to the next instruction. */
		ulPC += 2;

		/* Save the new program counter on the stack. */
		pulFaultStackAddress[ 6 ] = ulPC;

		/* Mark the fault as handled. */
		ucROTaskFaultTracker[ 0 ] = 0;
	}
	else
	{
		/* This is an unexpected fault - loop forever. */
		for( ; ; )
		{
		}
	}
}
/*-----------------------------------------------------------*/
