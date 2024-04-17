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

#ifndef DEMO_TASKS_H
#define DEMO_TASKS_H

/* ----------------------------------- Demo Option ----------------------------------- */

/** @brief Create Tasks that are written in assembly to test context swaps */
#define REGISTER_DEMO     0x1

/** @brief Demo that uses timers, timer callbacks, and Queues */
#define QUEUE_DEMO        0x2

/** @brief Demo that causes data aborts and clears them to show MPU usage */
#define MPU_DEMO          0x4

/** @brief Demo that causes and unwinds a Nested IRQ */
#define IRQ_DEMO          0x8

/** @brief Demo that uses the Task Notification APIs */
#define NOTIFICATION_DEMO 0x10

/** @brief Build Register, Queue, MPU, IRQ, and Notification demos */
#define FULL_DEMO         ( REGISTER_DEMO | QUEUE_DEMO | MPU_DEMO | IRQ_DEMO | NOTIFICATION_DEMO )

/** @brief Bitfield used to select the Demo Tasks to build and run
 *
 * @note This project contains multiple demo and test tasks. A bitfield is used
 * to select which demos and tests are built and run as part of the executable.
 * More information about what these demos and tests do can be found in their
 * corresponding files.
 *
 * Bit 1 Set: Include the Register Test Tasks
 *
 * Bit 2 Set: Include the Queue Send and Receive Test Tasks
 *
 * Bit 3 Set: Include the MPU Data Abort Test Tasks
 *
 * Bit 4 Set: Include the Nested IRQ Test Tasks
 *
 * Bit 5 Set: Include the Notification Test Tasks
 *
 */
#ifndef mainDEMO_TYPE
    #define mainDEMO_TYPE ( FULL_DEMO )
#endif /* mainDEMO_TYPE */

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "portmacro.h"
#include "mpu_wrappers.h"

/* These tasks have been given pseudo random priority values for testing.
 * Except for the queue send and receive task any of these tasks priorities
 * should be able to be set to any valid priority without issue. */

/** @brief Priority at which the Privileged Register Task is created. */
#define demoREG_PRIVILEGED_TASK_PRIORITY   ( configMAX_PRIORITIES - 2UL )

/** @brief Priority at which the Unprivileged Register Task is created. */
#define demoREG_UNPRIVILEGED_TASK_PRIORITY ( configMAX_PRIORITIES - 1UL )

/** @brief Priority at which the prvQueueSendTask is created. */
#define demoQUEUE_SEND_TASK_PRIORITY       ( tskIDLE_PRIORITY + 1UL )

/** @brief Priority at which the prvQueueReceiveTask is created. */
#define demoQUEUE_RECEIVE_TASK_PRIORITY    ( demoQUEUE_SEND_TASK_PRIORITY + 1UL )

/** @brief Priority at which the MPU Read & Write Task is created. */
#define demoMPU_READ_WRITE_TASK_PRIORITY   ( tskIDLE_PRIORITY + 3UL )

/** @brief Priority at which the MPU Read Only Task is created. */
#define demoMPU_READ_ONLY_TASK_PRIORITY    ( tskIDLE_PRIORITY + 4UL )

/** @brief Priority at which the Nested IRQ Test Task is created. */
#define demoIRQ_TASK_PRIORITY              ( configTIMER_TASK_PRIORITY + 2UL )

/** @brief Priority at which the Notification Demo Task is created. */
#define demoNOTIFICATION_TASK_PRIORITY     ( configTIMER_TASK_PRIORITY + 1UL )

/* ------------------------------- Register Test Tasks ------------------------------- */

/* @brief ASM function in reg_test_GCC.S that tests proper context swaps. */
void vRegTest1Implementation( void );

/** @brief ASM function in reg_test_GCC.S that tests proper context swaps. */
void vRegTest2Implementation( void );

/** @brief Creates the Register Test Tasks implemented in reg_test_GCC.S
 * @return pdPASS if all tasks are created, pdFAIL if they are not.
 */
BaseType_t xCreateRegisterTestTasks( void );

/* ----------------------------- Demo Tasks Declarations ----------------------------- */

/**
 * @brief Create two tasks, a queue, and a timer, which are used to blink an LED.
 *
 * @return
 * pdPASS if all objects are created.
 * pdFAIL if any object cannot be created.
 */
BaseType_t xCreateQueueTasks( void );

/**
 * @brief Create the MPU Tasks that trigger data aborts.
 *
 * @note The MPU demo creates 2 unprivileged tasks - One of which has Read Only
 * access to a shared memory region while the other has Read Write access. The
 * task with Read Only access then tries to write to the shared memory which
 * results in a Memory fault. The fault handler examines that it is the fault
 * generated by the task with Read Only access and if so, it recovers from the
 * fault gracefully by moving the Program Counter to the next instruction to the
 * one which generated the fault. If any other memory access violation occurs,
 * the fault handler will get stuck in an infinite loop.
 */
BaseType_t xCreateMPUTasks( void );

/** @brief Create a task that waits for a response from a nested IRQ
 *
 * @return pdPASS if tasks are created
 * pdFAIL if tasks are not created
 */
BaseType_t xCreateIRQTestTask( void );

/**
 * @brief Create tasks that send task notifications back and forth.
 *
 * @return pdPASS if tasks are created
 * pdFAIL if tasks are not created
 */
BaseType_t xCreateNotificationTestTask( void );

/** @brief Interrupt Handler used for Software Raised Interrupts */
PRIVILEGED_FUNCTION void vIRQDemoHandler( void );

/* Registers required to configure the Real Time Interrupt (RTI). */
#define portRTI_GCTRL_REG        ( *( ( volatile uint32_t * ) 0xFFFFFC00UL ) )
#define portRTI_TBCTRL_REG       ( *( ( volatile uint32_t * ) 0xFFFFFC04UL ) )
#define portRTI_COMPCTRL_REG     ( *( ( volatile uint32_t * ) 0xFFFFFC0CUL ) )
#define portRTI_CNT0_FRC0_REG    ( *( ( volatile uint32_t * ) 0xFFFFFC10UL ) )
#define portRTI_CNT0_UC0_REG     ( *( ( volatile uint32_t * ) 0xFFFFFC14UL ) )
#define portRTI_CNT0_CPUC0_REG   ( *( ( volatile uint32_t * ) 0xFFFFFC18UL ) )
#define portRTI_CNT0_COMP0_REG   ( *( ( volatile uint32_t * ) 0xFFFFFC50UL ) )
#define portRTI_CNT0_UDCP0_REG   ( *( ( volatile uint32_t * ) 0xFFFFFC54UL ) )
#define portRTI_SETINTENA_REG    ( *( ( volatile uint32_t * ) 0xFFFFFC80UL ) )
#define portRTI_CLEARINTENA_REG  ( *( ( volatile uint32_t * ) 0xFFFFFC84UL ) )
#define portRTI_INTFLAG_REG      ( *( ( volatile uint32_t * ) 0xFFFFFC88UL ) )
#define portEND_OF_INTERRUPT_REG ( ( ( volatile uint32_t * ) configEOI_ADDRESS ) )


/* Registers used by the Vectored Interrupt Manager */
typedef void ( *ISRFunction_t )( void );
#define portVIM_IRQ_INDEX     ( *( ( volatile uint32_t * ) 0xFFFFFE00 ) )
#define portVIM_IRQ_VEC_REG   ( *( ( volatile ISRFunction_t * ) 0xFFFFFE70 ) )

#define portSSI_INT_REG_BASE  ( ( ( volatile uint32_t * ) 0xFFFFFFB0 ) )

#define portSSI_INT_REG_ONE   ( ( ( volatile uint32_t * ) 0xFFFFFFB0 ) )
#define portSSI_ONE_KEY       0x7500UL

#define portSSI_INT_REG_TWO   ( ( ( volatile uint32_t * ) 0xFFFFFFB4 ) )
#define portSSI_TWO_KEY       0x8400UL

#define portSSI_INT_REG_THREE ( ( ( volatile uint32_t * ) 0xFFFFFFB8 ) )
#define portSSI_THREE_KEY     0x9300UL

#define portSSI_INT_REG_FOUR  ( ( ( volatile uint32_t * ) 0xFFFFFFBC ) )
#define portSSI_FOUR_KEY      0xA200UL

#define portSSI_VEC_REG       ( *( ( volatile uint32_t * ) 0xFFFFFFF4 ) )
#define portSSI_INTFLAG_REG   ( *( ( volatile uint32_t * ) 0xFFFFFFF8 ) )

/* --------------------------- Shared Function Deceleration --------------------------- */

/** @brief Function to toggle LEDs on the RM57-XL2 Launchpad
 * @param ulLED Which LED to flicker
 */
void vToggleLED( uint32_t ulLED );

/* ----------------------------------------------------------------------------------- */

#endif /* DEMO_TASKS_H */
