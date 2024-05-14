/*
 * FreeRTOS V202212.00
 * Copyright (C) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "mpu_wrappers.h"

/* Board Includes */
#include "sci.h"

/* Demo includes */
#include "demo_tasks.h"

/** @brief Size of the smallest valid MPU region, 32 bytes. */
#define SHARED_MEMORY_SIZE 0x20UL

#if( ( ( SHARED_MEMORY_SIZE % 2UL ) != 0UL ) || ( SHARED_MEMORY_SIZE < 32UL ) )
    #error SHARED_MEMORY_SIZE Must be a power of 2 that is larger than 32
#endif /* ( ( SHARED_MEMORY_SIZE % 2UL ) != 0UL ) || ( SHARED_MEMORY_SIZE < 32UL ) */
/**
 * @brief Memory region used to track Memory Fault intentionally caused by the
 * RO Access task.
 *
 * @note RO Access task sets ucROTaskFaultTracker[ 0 ] to 1 before accessing illegal
 * memory. Illegal memory access causes Memory Fault and the fault handler
 * checks ucROTaskFaultTracker[ 0 ] to see if this is an expected fault. We
 * recover gracefully from an expected fault by jumping to the next instruction.
 *
 */
static volatile uint8_t ucROTaskFaultTracker[ SHARED_MEMORY_SIZE ]
    __attribute__( ( aligned( SHARED_MEMORY_SIZE ) ) ) = { 0 };

#if( mainDEMO_TYPE & MPU_DEMO )

/* --------------------- Static Task Memory Allocation --------------------- */

/** @brief static variable that will be placed in privileged data */
static volatile uint32_t ulStaticUnprotectedData = 0xFEED;

/** @brief Memory regions shared between the two MPU Tasks. */
static volatile uint8_t ucSharedMemory[ SHARED_MEMORY_SIZE ]
    __attribute__( ( aligned( SHARED_MEMORY_SIZE ) ) );

static volatile uint8_t ucSharedMemory1[ SHARED_MEMORY_SIZE ]
    __attribute__( ( aligned( SHARED_MEMORY_SIZE ) ) );

static volatile uint8_t ucSharedMemory2[ SHARED_MEMORY_SIZE ]
    __attribute__( ( aligned( SHARED_MEMORY_SIZE ) ) );

static volatile uint8_t ucSharedMemory3[ SHARED_MEMORY_SIZE ]
    __attribute__( ( aligned( SHARED_MEMORY_SIZE ) ) );

static volatile uint8_t ucSharedMemory4[ SHARED_MEMORY_SIZE ]
    __attribute__( ( aligned( SHARED_MEMORY_SIZE ) ) );

    #if( configTOTAL_MPU_REGIONS == 16 )
static volatile uint8_t ucSharedMemory5[ SHARED_MEMORY_SIZE ]
    __attribute__( ( aligned( SHARED_MEMORY_SIZE ) ) );

static volatile uint8_t ucSharedMemory6[ SHARED_MEMORY_SIZE ]
    __attribute__( ( aligned( SHARED_MEMORY_SIZE ) ) );

static volatile uint8_t ucSharedMemory7[ SHARED_MEMORY_SIZE ]
    __attribute__( ( aligned( SHARED_MEMORY_SIZE ) ) );

static volatile uint8_t ucSharedMemory8[ SHARED_MEMORY_SIZE ]
    __attribute__( ( aligned( SHARED_MEMORY_SIZE ) ) );
    #endif /* configTOTAL_MPU_REGIONS == 16 */

/* These tasks will use over 288 bytes as of time of writing.
 * Minimal Cortex R MPU region sizes are 32, 64, 128, 256, and 512 bytes. Regions must
 * aligned to their size. Due to this limitation these regions declare 512, or 0x200,
 * bytes and align to that size. */

/** @brief Statically declared MPU aligned stack used by the Read Only task */
static StackType_t xROAccessTaskStack[ configMINIMAL_STACK_SIZE ]
    __attribute__( ( aligned( configMINIMAL_STACK_SIZE * 0x4U ) ) );

/** @brief Statically declared TCB Used by the Idle Task */
PRIVILEGED_DATA static StaticTask_t xROAccessTaskTCB;

/** @brief Statically declared MPU aligned stack used by the Read Write task */
static StackType_t xRWAccessTaskStack[ configMINIMAL_STACK_SIZE ]
    __attribute__( ( aligned( configMINIMAL_STACK_SIZE * 0x4U ) ) );

/** @brief Statically declared TCB Used by the Read Write Task */
PRIVILEGED_DATA static StaticTask_t xRWAccessTaskTCB;

/* ----------------------- Task Function Declaration ----------------------- */

/** @brief Task function used by the task with RO access to shared memory
 *
 * @param pvParameters[in] Parameters as passed during task creation.
 */
static void prvROAccessTask( void * pvParameters );

/** @brief Task function used by the task with RW access to shared memory
 *
 * @param pvParameters[in] Parameters as passed during task creation.
 */
static void prvRWAccessTask( void * pvParameters );

/* --------------------- MPU Demo Function Definitions --------------------- */

static void prvROAccessTask( void * pvParameters )
{
    volatile uint8_t ucVal = 0x0;

    /* Unused parameters. */
    ( void ) pvParameters;

    for( ;; )
    {
        /* This task performs the following sequence for all the shared memory
         * regions:
         *
         * 1. Perform a read access to the shared memory. Since this task has
         *    RO access to the shared memory, the read operation is successful.
         *
         * 2. Set ucROTaskFaultTracker[ 0 ] to 1 before performing a write to
         *    the shared memory. Since this task has Read Only access to the
         *    shared memory, the write operation would result in a Memory Fault.
         *    Setting ucROTaskFaultTracker[ 0 ] to 1 tells the Memory Fault
         *    Handler that this is an expected fault. The handler recovers from
         *    the expected fault gracefully by jumping to the next instruction.
         *
         * 3. Perform a write to the shared memory resulting in a memory fault.
         *
         * 4. Ensure that the write access did generate MemFault and the fault
         *    handler did clear the ucROTaskFaultTracker[ 0 ].
         */
        /* Perform the above mentioned sequence on ucSharedMemory. */
        ucVal = ucSharedMemory[ 0 ];
        ucVal = 1U;
        ucROTaskFaultTracker[ 0 ] = ucVal;
        ucSharedMemory[ 0 ] = 0U;
        ucVal = ucROTaskFaultTracker[ 0 ];
        configASSERT( ucVal == 0U );

        /* Perform the above mentioned sequence on ucSharedMemory1. */
        ucVal = ucSharedMemory1[ 0 ];
        ucROTaskFaultTracker[ 0 ] = 1U;
        ucSharedMemory1[ 0 ] = 0U;
        ucVal = ucROTaskFaultTracker[ 0 ];
        configASSERT( ucVal == 0U );

        /* Perform the above mentioned sequence on ucSharedMemory2. */
        ucVal = ucSharedMemory2[ 0 ];
        ucROTaskFaultTracker[ 0 ] = 1U;
        ucSharedMemory2[ 0 ] = 0U;
        ucVal = ucROTaskFaultTracker[ 0 ];
        configASSERT( ucVal == 0U );

        /* Perform the above mentioned sequence on ucSharedMemory3. */
        ucVal = ucSharedMemory3[ 0 ];
        ucROTaskFaultTracker[ 0 ] = 1U;
        ucSharedMemory3[ 0 ] = 0U;
        ucVal = ucROTaskFaultTracker[ 0 ];
        configASSERT( ucVal == 0U );

        /* Perform the above mentioned sequence on ucSharedMemory4. */
        ucVal = ucSharedMemory4[ 0 ];
        ucROTaskFaultTracker[ 0 ] = 1U;
        ucSharedMemory4[ 0 ] = 0U;
        ucVal = ucROTaskFaultTracker[ 0 ];
        configASSERT( ucVal == 0U );

    #if( configTOTAL_MPU_REGIONS == 16 )
        {
            /* Perform the above mentioned sequence on ucSharedMemory5. */
            ucVal = ucSharedMemory5[ 0 ];
            ucROTaskFaultTracker[ 0 ] = 1U;
            ucSharedMemory5[ 0 ] = 0U;
            ucVal = ucROTaskFaultTracker[ 0 ];
            configASSERT( ucVal == 0U );

            /* Perform the above mentioned sequence on ucSharedMemory6. */
            ucVal = ucSharedMemory6[ 0 ];
            ucROTaskFaultTracker[ 0 ] = 1U;
            ucSharedMemory6[ 0 ] = 0U;
            ucVal = ucROTaskFaultTracker[ 0 ];
            configASSERT( ucVal == 0U );

            /* Perform the above mentioned sequence on ucSharedMemory7. */
            ucVal = ucSharedMemory7[ 0 ];
            ucROTaskFaultTracker[ 0 ] = 1U;
            ucSharedMemory7[ 0 ] = 0U;
            ucVal = ucROTaskFaultTracker[ 0 ];
            configASSERT( ucVal == 0U );

            /* Perform the above mentioned sequence on ucSharedMemory8. */
            ucVal = ucSharedMemory8[ 0 ];
            ucROTaskFaultTracker[ 0 ] = 1U;
            ucSharedMemory8[ 0 ] = 0U;
            ucVal = ucROTaskFaultTracker[ 0 ];
            configASSERT( ucVal == 0U );
        }
    #endif /* configTOTAL_MPU_REGIONS == 16 */

        vToggleLED( 0x0 );
        sci_print( "Read Only MPU Task sleeping before next loop!\r\n\r\n" );

        /* Sleep for odd number of seconds to schedule at different real-times */
        vTaskDelay( pdMS_TO_TICKS( 4004UL ) );
    }
}
/*-----------------------------------------------------------*/

static void prvRWAccessTask( void * pvParameters )
{
    volatile uint32_t ulVal = ( uint32_t ) pvParameters;

    for( ;; )
    {
        /* This task has RW access to ucSharedMemory */
        ucSharedMemory[ 0 ] += 2U;
        ucSharedMemory1[ 0 ]++;
        ucSharedMemory2[ 0 ]++;
        ucSharedMemory3[ 0 ]++;
        ucSharedMemory4[ 0 ]++;
    #if( configTOTAL_MPU_REGIONS == 16 )
        {
            ucSharedMemory5[ 0 ]++;
            ucSharedMemory6[ 0 ]++;
            ucSharedMemory7[ 0 ]++;
            ucSharedMemory8[ 0 ]++;
        }
    #endif /* configTOTAL_MPU_REGIONS == 16 */

        /* Set ucVal to 0 */
        ulVal = ( uint32_t ) ucSharedMemory[ 0 ];

        /* Mark that we will trigger a data abort */
        ucROTaskFaultTracker[ 1 ] = 1U;
        /* Attempt to set ulVal to ulStaticUnprotectedData.
         * This will trigger a data abort as this task did not grant itself
         * access to this variable. The Data abort handler at the bottom of this
         * file will then see the raised value in the fault tracker, mark it low,
         * and cause this  task to resume from the following instruction.
         */
        ulVal = ulStaticUnprotectedData;

        /* The value of ucVal should not have changed */
        configASSERT( ulVal != ucSharedMemory[ 0 ] );

        vToggleLED( 0x1 );
        sci_print( "Read & Write MPU Task sleeping before next loop!\r\n\r\n" );

        /* Sleep for odd number of seconds to schedule at different real-times */
        vTaskDelay( pdMS_TO_TICKS( 4321UL ) );
    }
}
/*-----------------------------------------------------------*/

BaseType_t xCreateMPUTasks( void )
{
    /* Declaration when these variable are exported from linker scripts. */
    extern uint32_t __peripherals_start__[];
    extern uint32_t __peripherals_end__[];

    uint32_t ulPeriphRegionStart = ( uint32_t ) __peripherals_start__;
    uint32_t ulPeriphRegionSize = ( uint32_t ) __peripherals_end__ - ulPeriphRegionStart;
    uint32_t ulPeriphRegionAttr = portMPU_REGION_PRIV_RW_USER_RW_NOEXEC | portMPU_REGION_DEVICE_SHAREABLE;

    BaseType_t xReturn = pdPASS;

    uint32_t ulReadMemoryPermissions = portMPU_REGION_PRIV_RW_USER_RO_NOEXEC
                                     | portMPU_REGION_NORMAL_OIWTNOWA_SHARED;

    uint32_t ulWriteMemoryPermissions = portMPU_REGION_PRIV_RW_USER_RW_NOEXEC
                                      | portMPU_REGION_NORMAL_OIWTNOWA_SHARED;

    ulStaticUnprotectedData = 0xC3;

    TaskParameters_t
        xROAccessTaskParameters = { .pvTaskCode = prvROAccessTask,
                                    .pcName = "ROAccess",
                                    .usStackDepth = configMINIMAL_STACK_SIZE,
                                    .pvParameters = NULL,
                                    .uxPriority = demoMPU_READ_ONLY_TASK_PRIORITY,
                                    .puxStackBuffer = xROAccessTaskStack,
                                    .pxTaskBuffer = &xROAccessTaskTCB,
                                    .xRegions = {
                                        /* Region 0 */
                                        { ( void * ) ucSharedMemory,
                                          SHARED_MEMORY_SIZE,
                                          ulReadMemoryPermissions },
                                        /* Region 1 */
                                        { ( void * ) ucSharedMemory1,
                                          SHARED_MEMORY_SIZE,
                                          ulReadMemoryPermissions },
                                        /* Region 2 */
                                        { ( void * ) ucSharedMemory2,
                                          SHARED_MEMORY_SIZE,
                                          ulReadMemoryPermissions },
                                        /* Region 3 */
                                        { ( void * ) ucSharedMemory3,
                                          SHARED_MEMORY_SIZE,
                                          ulReadMemoryPermissions },
                                        /* Region 4 */
                                        { ( void * ) ucSharedMemory4,
                                          SHARED_MEMORY_SIZE,
                                          ulReadMemoryPermissions },
    #if( configTOTAL_MPU_REGIONS == 16 )
                                        /* Region 5 */
                                        { ( void * ) ucSharedMemory5,
                                          SHARED_MEMORY_SIZE,
                                          ulReadMemoryPermissions },
                                        /* Region 6 */
                                        { ( void * ) ucSharedMemory6,
                                          SHARED_MEMORY_SIZE,
                                          ulReadMemoryPermissions },
                                        /* Region 7 */
                                        { ( void * ) ucSharedMemory7,
                                          SHARED_MEMORY_SIZE,
                                          ulReadMemoryPermissions },
                                        /* Region 8 */
                                        { ( void * ) ucSharedMemory8,
                                          SHARED_MEMORY_SIZE,
                                          ulReadMemoryPermissions },
    #endif /* configTOTAL_MPU_REGIONS == 16 */
                                        /* Second to last Configurable Region */
                                        { ( void * ) ucROTaskFaultTracker,
                                          SHARED_MEMORY_SIZE,
                                          ulWriteMemoryPermissions },
                                        /* Last Configurable MPU Region */
                                        { ( void * ) ulPeriphRegionStart,
                                          ulPeriphRegionSize,
                                          ulPeriphRegionAttr },
                                    } };

    TaskParameters_t
        xRWAccessTaskParameters = { .pvTaskCode = prvRWAccessTask,
                                    .pcName = "RWAccess",
                                    .usStackDepth = configMINIMAL_STACK_SIZE,
                                    .pvParameters = ( void * ) ( 0xFF ),
                                    .uxPriority = demoMPU_READ_WRITE_TASK_PRIORITY,
                                    .puxStackBuffer = xRWAccessTaskStack,
                                    .pxTaskBuffer = &xRWAccessTaskTCB,
                                    .xRegions = {
                                        /* First Configurable Region 0 */
                                        { ( void * ) ucSharedMemory,
                                          SHARED_MEMORY_SIZE,
                                          ulWriteMemoryPermissions },
                                        /* MPU Region 1 */
                                        { ( void * ) ucSharedMemory1,
                                          SHARED_MEMORY_SIZE,
                                          ulWriteMemoryPermissions },
                                        /* MPU Region 2 */
                                        { ( void * ) ucSharedMemory2,
                                          SHARED_MEMORY_SIZE,
                                          ulWriteMemoryPermissions },
                                        /* MPU Region 3 */
                                        { ( void * ) ucSharedMemory3,
                                          SHARED_MEMORY_SIZE,
                                          ulWriteMemoryPermissions },
                                        /* MPU Region 4 */
                                        { ( void * ) ucSharedMemory4,
                                          SHARED_MEMORY_SIZE,
                                          ulWriteMemoryPermissions },
    #if( configTOTAL_MPU_REGIONS == 16 )
                                        /* MPU Region 5 */
                                        { ( void * ) ucSharedMemory5,
                                          SHARED_MEMORY_SIZE,
                                          ulWriteMemoryPermissions },
                                        /* MPU Region 6 */
                                        { ( void * ) ucSharedMemory6,
                                          SHARED_MEMORY_SIZE,
                                          ulWriteMemoryPermissions },
                                        /* MPU Region 7 */
                                        { ( void * ) ucSharedMemory7,
                                          SHARED_MEMORY_SIZE,
                                          ulWriteMemoryPermissions },
                                        /* MPU Region 8 */
                                        { ( void * ) ucSharedMemory8,
                                          SHARED_MEMORY_SIZE,
                                          ulWriteMemoryPermissions },
    #endif /* configTOTAL_MPU_REGIONS == 16 */
                                        /* Second to Last MPU Region */
                                        { ( void * ) ucROTaskFaultTracker,
                                          SHARED_MEMORY_SIZE,
                                          ulWriteMemoryPermissions },
                                        /* Last Configurable MPU Region */
                                        { ( void * ) ulPeriphRegionStart,
                                          ulPeriphRegionSize,
                                          ulPeriphRegionAttr },
                                    } };

    /* Create an unprivileged task with RO access to ucSharedMemory. */
    xReturn = xTaskCreateRestrictedStatic( &( xROAccessTaskParameters ), NULL );
    if( pdPASS == xReturn )
    {
        /* Create an unprivileged task with RW access to ucSharedMemory. */
        xReturn = xTaskCreateRestrictedStatic( &( xRWAccessTaskParameters ), NULL );
        if( pdPASS == xReturn )
        {
            sci_print( "Created the MPU Tasks\r\n" );
        }
        else
        {
            sci_print( "Failed to create the Read Write MPU Task\r\n" );
        }
    }
    else
    {
        sci_print( "Failed to create the Read Write MPU Task\r\n" );
    }

    return xReturn;
}
/*-----------------------------------------------------------*/
#endif /* ( mainDEMO_TYPE & MPU_DEMO ) */

PRIVILEGED_FUNCTION portDONT_DISCARD void vHandleMemoryFault(
    uint32_t * pulFaultStackAddress )
{
    volatile uint32_t ulPC;
    volatile uint32_t ulOffendingInstruction;

    /* Is this an expected fault? */
    if( ( ucROTaskFaultTracker[ 0 ] == 1U ) || ( ucROTaskFaultTracker[ 1 ] == 1U ) )
    {
        /* Read program counter. */
        ulPC = pulFaultStackAddress[ 6 ];

        /* Read the offending instruction. */
        ulOffendingInstruction = *( uint32_t * ) ulPC;

        /** From ARM docs:
         * Bits [31:28] are the conditional field
         * Bits [27:24] are the operation code
         * If bits [31:28] are 0b1111, the instruction can only be executed
         * unconditionally If bits [31:28] are not 0b1111, the op code determines what the
         * instruction is doing If bits [27:24] are 0b01x0 it is a load/store word If bits
         * [27:24] are 0b0111 it is a media instruction
         */

        /* Extract bits[31:25] of the offending instruction. */
        ulOffendingInstruction = ulOffendingInstruction & 0xFF000000;
        ulOffendingInstruction = ( ulOffendingInstruction >> 24 );

        /* Check if we were called by a load/store word instruction */
        if( ( ulOffendingInstruction == 0x00E4 ) || ( ulOffendingInstruction == 0x00E5 )
            || ( ulOffendingInstruction == 0x00E6 ) )
        {
            /* Increment the program counter to move to the next instruction */
            ulPC += 0x4;
        }
        else
        {
            sci_print( "Unexpected Instruction caused an MPU fault\r\n" );
            configASSERT( 0 );
        }

        /* Save the new program counter on the stack. */
        pulFaultStackAddress[ 6 ] = ulPC;

        /* Mark the fault as handled. */
        if( ucROTaskFaultTracker[ 0 ] == 1U )
        {
            ucROTaskFaultTracker[ 0 ] = 0U;
            sci_print( "Cleared an MPU Read Only Task Fault\r\n" );
        }
        else if( ucROTaskFaultTracker[ 1 ] == 1U )
        {
            sci_print( "Cleared an MPU Write Only Task Fault\r\n" );
            ucROTaskFaultTracker[ 1 ] = 0U;
        }
        else
        {
            sci_print( "TaskFaultTracker value changed, Are IRQs disabled? \r\n" );
            /* Sit in a loop forever */
            configASSERT( 0 );
        }
    }
    else
    {
        sci_print( "Unexpected MPU Fault\r\n" );
        /* This is an unexpected fault - loop forever. */
        configASSERT( 0 );
    }
}

/*-----------------------------------------------------------*/
