/*
 * FreeRTOS V202111.00
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
 * http://www.FreeRTOS.org
 * http://aws.amazon.com/freertos
 *
 * 1 tab == 4 spaces!
 */

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"

/** ARMv7 MPU Details:
 *
 * - ARMv7 MPU requires that the size of a MPU region is a power of 2.
 * - Smallest supported region size is 32 bytes.
 * - Start address of a region must be aligned to an integer multiple of the
 *   region size. For example, if the region size is 4 KB(0x1000), the starting
 *   address must be N x 0x1000, where N is an integer.
 */

/**
 * @brief Size of the shared memory region.
 */
#define SHARED_MEMORY_SIZE 32

/**
 * @brief Memory regions shared between two tasks.
 */
static uint8_t ucSharedMemory1[ SHARED_MEMORY_SIZE ] __attribute__( ( aligned( SHARED_MEMORY_SIZE ) ) );
static uint8_t ucSharedMemory2[ SHARED_MEMORY_SIZE ] __attribute__( ( aligned( SHARED_MEMORY_SIZE ) ) );
static uint8_t ucSharedMemory3[ SHARED_MEMORY_SIZE ] __attribute__( ( aligned( SHARED_MEMORY_SIZE ) ) );
static uint8_t ucSharedMemory4[ SHARED_MEMORY_SIZE ] __attribute__( ( aligned( SHARED_MEMORY_SIZE ) ) );
static uint8_t ucSharedMemory5[ SHARED_MEMORY_SIZE ] __attribute__( ( aligned( SHARED_MEMORY_SIZE ) ) );
static uint8_t ucSharedMemory6[ SHARED_MEMORY_SIZE ] __attribute__( ( aligned( SHARED_MEMORY_SIZE ) ) );

/**
 * @brief Memory region used to track Memory Fault intentionally caused by the
 * RO Access task.
 *
 * RO Access task sets ucROTaskFaultTracker[ 0 ] to 1 before accessing illegal
 * memory. Illegal memory access causes Memory Fault and the fault handler
 * checks ucROTaskFaultTracker[ 0 ] to see if this is an expected fault. We
 * recover gracefully from an expected fault by jumping to the next instruction.
 *
 * @note We are declaring a region of 32 bytes even though we need only one.
 * The reason is that the smallest supported MPU region size is 32 bytes.
 */
static volatile uint8_t ucROTaskFaultTracker[ SHARED_MEMORY_SIZE ] __attribute__( ( aligned( SHARED_MEMORY_SIZE ) ) ) = { 0 };
/*-----------------------------------------------------------*/

/**
 * @brief Implements the task which has Read Only access to the shared memory
 * regions ucSharedMemoryN.
 *
 * @param pvParameters[in] Parameters as passed during task creation.
 */
static void prvROAccessTask( void * pvParameters );

/**
 * @brief Implements the task which has Read Write access to the shared memory
 * regions ucSharedMemoryN.
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
		/* This task performs the following sequence for all the shared memory
		 * regions:
		 *
		 * 1. Perfrom a read access to the shared memory. Since this task has
		 *    RO access to the shared memory, the read operation is successful.
		 *
		 * 2. Set ucROTaskFaultTracker[ 0 ] to 1 before performing a write to
		 *    the shared memory. Since this task has Read Only access to the
		 *    shared memory, the write operation would result in a Memory Fault.
		 *    Setting ucROTaskFaultTracker[ 0 ] to 1 tells the Memory Fault
		 *    Handler that this is an expected fault. The handler recovers from
		 *    the expected fault gracefully by jumping to the next instruction.
		 *
		 * 3. Perfrom a write to the shared memory resulting in a memory fault.
		 *
		 * 4. Ensure that the write access did generate MemFault and the fault
		 *    handler did clear the  ucROTaskFaultTracker[ 0 ].
		 */
		/* Perform the above mentioned sequence on ucSharedMemory1. */
		ucVal = ucSharedMemory1[ 0 ];
		/* Silent compiler warnings about unused variables. */
		( void ) ucVal;
		ucROTaskFaultTracker[ 0 ] = 1;
		ucSharedMemory1[ 0 ] = 0;
		configASSERT( ucROTaskFaultTracker[ 0 ] == 0 );

		/* Perform the above mentioned sequence on ucSharedMemory2. */
		ucVal = ucSharedMemory2[ 0 ];
		/* Silent compiler warnings about unused variables. */
		( void ) ucVal;
		ucROTaskFaultTracker[ 0 ] = 1;
		ucSharedMemory2[ 0 ] = 0;
		configASSERT( ucROTaskFaultTracker[ 0 ] == 0 );

		/* Perform the above mentioned sequence on ucSharedMemory3. */
		ucVal = ucSharedMemory3[ 0 ];
		/* Silent compiler warnings about unused variables. */
		( void ) ucVal;
		ucROTaskFaultTracker[ 0 ] = 1;
		ucSharedMemory3[ 0 ] = 0;
		configASSERT( ucROTaskFaultTracker[ 0 ] == 0 );

		/* Perform the above mentioned sequence on ucSharedMemory4. */
		ucVal = ucSharedMemory4[ 0 ];
		/* Silent compiler warnings about unused variables. */
		( void ) ucVal;
		ucROTaskFaultTracker[ 0 ] = 1;
		ucSharedMemory4[ 0 ] = 0;
		configASSERT( ucROTaskFaultTracker[ 0 ] == 0 );

		/* Perform the above mentioned sequence on ucSharedMemory5. */
		ucVal = ucSharedMemory5[ 0 ];
		/* Silent compiler warnings about unused variables. */
		( void ) ucVal;
		ucROTaskFaultTracker[ 0 ] = 1;
		ucSharedMemory5[ 0 ] = 0;
		configASSERT( ucROTaskFaultTracker[ 0 ] == 0 );

		/* Perform the above mentioned sequence on ucSharedMemory6. */
		ucVal = ucSharedMemory6[ 0 ];
		/* Silent compiler warnings about unused variables. */
		( void ) ucVal;
		ucROTaskFaultTracker[ 0 ] = 1;
		ucSharedMemory6[ 0 ] = 0;
		configASSERT( ucROTaskFaultTracker[ 0 ] == 0 );

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
		/* This task has RW access to shared memories and therefore can write to
		 * them. */
		ucSharedMemory1[ 0 ] = 0;
		ucSharedMemory2[ 0 ] = 0;
		ucSharedMemory3[ 0 ] = 0;
		ucSharedMemory4[ 0 ] = 0;
		ucSharedMemory5[ 0 ] = 0;
		ucSharedMemory6[ 0 ] = 0;

		/* Wait for a second. */
		vTaskDelay( pdMS_TO_TICKS( 1000 ) );
	}
}
/*-----------------------------------------------------------*/

void vStartMPUDemo( void )
{
/**
 * Since stack of a task is protected using MPU, it must satisfy MPU
 * requirements as mentioned at the top of this file.
 */
static StackType_t xROAccessTaskStack[ configMINIMAL_STACK_SIZE ] __attribute__( ( aligned( configMINIMAL_STACK_SIZE * sizeof( StackType_t ) ) ) );
static StackType_t xRWAccessTaskStack[ configMINIMAL_STACK_SIZE ] __attribute__( ( aligned( configMINIMAL_STACK_SIZE * sizeof( StackType_t ) ) ) );
TaskParameters_t xROAccessTaskParameters =
{
	.pvTaskCode		= prvROAccessTask,
	.pcName			= "ROAccess",
	.usStackDepth	= configMINIMAL_STACK_SIZE,
	.pvParameters	= NULL,
	.uxPriority		= tskIDLE_PRIORITY,
	.puxStackBuffer	= xROAccessTaskStack,
	.xRegions		=	{
							{ ucSharedMemory1,					SHARED_MEMORY_SIZE,	portMPU_REGION_PRIVILEGED_READ_WRITE_UNPRIV_READ_ONLY | portMPU_REGION_EXECUTE_NEVER	},
							{ ucSharedMemory2,					SHARED_MEMORY_SIZE,	portMPU_REGION_PRIVILEGED_READ_WRITE_UNPRIV_READ_ONLY | portMPU_REGION_EXECUTE_NEVER	},
							{ ucSharedMemory3,					SHARED_MEMORY_SIZE,	portMPU_REGION_PRIVILEGED_READ_WRITE_UNPRIV_READ_ONLY | portMPU_REGION_EXECUTE_NEVER	},
							{ ucSharedMemory4,					SHARED_MEMORY_SIZE,	portMPU_REGION_PRIVILEGED_READ_WRITE_UNPRIV_READ_ONLY | portMPU_REGION_EXECUTE_NEVER	},
							{ ucSharedMemory5,					SHARED_MEMORY_SIZE,	portMPU_REGION_PRIVILEGED_READ_WRITE_UNPRIV_READ_ONLY | portMPU_REGION_EXECUTE_NEVER	},
							{ ucSharedMemory6,					SHARED_MEMORY_SIZE,	portMPU_REGION_PRIVILEGED_READ_WRITE_UNPRIV_READ_ONLY | portMPU_REGION_EXECUTE_NEVER	},
							{ ( void * ) ucROTaskFaultTracker,	SHARED_MEMORY_SIZE,	portMPU_REGION_READ_WRITE | portMPU_REGION_EXECUTE_NEVER								},
							{ 0,								0,					0																						},
							{ 0,								0,					0																						},
							{ 0,								0,					0																						},
							{ 0,								0,					0																						}
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
							{ ucSharedMemory1,	SHARED_MEMORY_SIZE,	portMPU_REGION_READ_WRITE | portMPU_REGION_EXECUTE_NEVER},
							{ ucSharedMemory2,	SHARED_MEMORY_SIZE,	portMPU_REGION_READ_WRITE | portMPU_REGION_EXECUTE_NEVER},
							{ ucSharedMemory3,	SHARED_MEMORY_SIZE,	portMPU_REGION_READ_WRITE | portMPU_REGION_EXECUTE_NEVER},
							{ ucSharedMemory4,	SHARED_MEMORY_SIZE,	portMPU_REGION_READ_WRITE | portMPU_REGION_EXECUTE_NEVER},
							{ ucSharedMemory5,	SHARED_MEMORY_SIZE,	portMPU_REGION_READ_WRITE | portMPU_REGION_EXECUTE_NEVER},
							{ ucSharedMemory6,	SHARED_MEMORY_SIZE,	portMPU_REGION_READ_WRITE | portMPU_REGION_EXECUTE_NEVER},
							{ 0,				0,					0														},
							{ 0,				0,					0														},
							{ 0,				0,					0														},
							{ 0,				0,					0														},
							{ 0,				0,					0														}
						}
};

	/* Create an unprivileged task with RO access to ucSharedMemory. */
	xTaskCreateRestricted( &( xROAccessTaskParameters ), NULL );

	/* Create an unprivileged task with RW access to ucSharedMemory. */
	xTaskCreateRestricted( &( xRWAccessTaskParameters ), NULL );
}
/*-----------------------------------------------------------*/

portDONT_DISCARD void vHandleMemoryFault( uint32_t * pulFaultStackAddress )
{
uint32_t ulPC;
uint16_t usOffendingInstruction;

	/* Is this an expected fault? */
	if( ucROTaskFaultTracker[ 0 ] == 1 )
	{
		/* Read program counter. */
		ulPC = pulFaultStackAddress[ 6 ];

		/* Read the offending instruction. */
		usOffendingInstruction = *( uint16_t * )ulPC;

		/* From ARM docs:
		 * If the value of bits[15:11] of the halfword being decoded is one of
		 * the following, the halfword is the first halfword of a 32-bit
		 * instruction:
		 * - 0b11101.
		 * - 0b11110.
		 * - 0b11111.
		 * Otherwise, the halfword is a 16-bit instruction.
		 */

		/* Extract bits[15:11] of the offending instruction. */
		usOffendingInstruction = usOffendingInstruction & 0xF800;
		usOffendingInstruction = ( usOffendingInstruction >> 11 );

		/* Determine if the offending instruction is a 32-bit instruction or
		 * a 16-bit instruction. */
		if( usOffendingInstruction == 0x001F ||
			usOffendingInstruction == 0x001E ||
			usOffendingInstruction == 0x001D )
		{
			/* Since the offending instruction is a 32-bit instruction,
			 * increment the program counter by 4 to move to the next
			 * instruction. */
			ulPC += 4;
		}
		else
		{
			/* Since the offending instruction is a 16-bit instruction,
			 * increment the program counter by 2 to move to the next
			 * instruction. */
			ulPC += 2;
		}

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
