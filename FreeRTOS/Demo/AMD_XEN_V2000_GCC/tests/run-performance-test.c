/* run-performance-test
 *
 * Copyright (C) 2025 Advanced Micro Devices, Inc. or its affiliates. All Rights Reserved.
 *
 * SPDX-License-Identifier: MIT
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
 *
 */
#include "FreeRTOS.h"
#include "FreeRTOS_CLI.h"
#include "stdint.h"
#include "stdio.h"
#include "string.h"
#include "stdio.h"
#include "cli.h"
#include "task.h"
#include "register_tests.h"
#include "event_groups.h"
#include "queue.h"
#include "semphr.h"

#define BIT_0 (1 << 0)
#define EVENT_BIT_0 (1 << 0)

#define SEMAPHORE_TAKE_CYCLE_THRESHOLD 1000
#define SEMAPHORE_BLOCK_SWITCH_THRESHOLD 10000
#define SEMAPHORE_GIVE_CYCLE_THRESHOLD 500
#define QUEUE_LENGTH 1
#define QUEUE_ITEM_SIZE sizeof(int)

int debug_print_on=0;
EventBits_t uxBits;
static QueueHandle_t xQueue;
static EventGroupHandle_t waitTaskEventGroup;
static TimerHandle_t xTimer = NULL;
static TimerHandle_t xTestTimer = NULL;
static void perfTask( void * pvParameters );
static void waitingTask( void * pvParameters );

void test_xSemaphoreTake_mutexAvailable(void)
{
    uint64_t total_cycles;
    uint64_t start_cycles;
    uint64_t end_cycles;
    BaseType_t result;
    SemaphoreHandle_t testMutex;

    testMutex = xSemaphoreCreateMutex();
    if (testMutex == NULL) {
        return;
    }

    // Make sure it's available
    xSemaphoreGive(testMutex);

    // Measure xSemaphoreTake() in CPU cycles
    start_cycles = rdtsc();
    result = xSemaphoreTake(testMutex, portMAX_DELAY);
    end_cycles = rdtsc();
    total_cycles = end_cycles - start_cycles;
    printk("xSemaphoreTake(mutexAvailable):  %d \n", total_cycles);
    // Release it to clean up
    xSemaphoreGive(testMutex);
    vSemaphoreDelete(testMutex);
}

// Performance test: xSemaphoreGive() with no task pending and no context switching
void test_xSemaphoreGive_noTaskPending_noContextSwitching(void)
{
    uint64_t total_cycles;
    uint64_t start_cycles;
    uint64_t end_cycles;
    BaseType_t result;
    SemaphoreHandle_t testMutex;
    testMutex = xSemaphoreCreateMutex();
    if (testMutex == NULL) {
        return;
    }

    // Take the mutex so we can give it ourselves (ensuring no task is waiting)
    if (xSemaphoreTake(testMutex, portMAX_DELAY) != pdPASS) {
        vSemaphoreDelete(testMutex);
        return;
    }

    // Measure CPU cycles for xSemaphoreGive() with no other task waiting
    start_cycles = rdtsc();
    xSemaphoreGive(testMutex);
    end_cycles = rdtsc();

    total_cycles = end_cycles - start_cycles;
    printk("xSemaphoreTake(noTaskPending, noContextSwitch): %d \n", total_cycles);
    vSemaphoreDelete(testMutex);
}

// Performance test for xSemaphoreTake(binary semaphore available)

void test_xBinarySemaphoreTake_SemaphoreAvailable(void) {
    uint64_t total_cycles;
    uint64_t start_cycles;
    uint64_t end_cycles;
    BaseType_t result;
    SemaphoreHandle_t testSemaphore;

    // Create binary semaphore
    testSemaphore = xSemaphoreCreateBinary();
    if (testSemaphore == NULL) {
        return;
    }

    // Make the binary semaphore available (give once)
    xSemaphoreGive(testSemaphore);

    // Measure xSemaphoreTake() — should succeed immediately
    start_cycles = rdtsc();
    result = xSemaphoreTake(testSemaphore, portMAX_DELAY);
    end_cycles = rdtsc();

    total_cycles = end_cycles - start_cycles;

    if (result != pdPASS) {
        vSemaphoreDelete(testSemaphore);
        return;
    }

    printk("xSemaphoreTake(semaphore available): %d \n", total_cycles);

    vSemaphoreDelete(testSemaphore);
}

// Performance test for binary SemaphoreGive(no taskpending,no contextswitch)
void test_xBinarySemaphoreGive_noTaskPending_noContextSwitching(void) {
    uint64_t total_cycles;
    uint64_t start_cycles;
    uint64_t end_cycles;
    BaseType_t result;
    SemaphoreHandle_t testSemaphore;

    // Create binary semaphore
    testSemaphore = xSemaphoreCreateBinary();
    if (testSemaphore == NULL) {
        return;
    }

    // Binary semaphores are initially 'empty' — give it once so it's in the 'available' state
    xSemaphoreGive(testSemaphore);

    // Take it to make it unavailable
    if (xSemaphoreTake(testSemaphore, portMAX_DELAY) != pdPASS) {
        vSemaphoreDelete(testSemaphore);
        return;
    }

    // Now measure give (no tasks pending on it)
    start_cycles = rdtsc();
    result = xSemaphoreGive(testSemaphore);  // No task is waiting
    end_cycles = rdtsc();

    total_cycles = end_cycles - start_cycles;

    if (result != pdPASS) {
        vSemaphoreDelete(testSemaphore);
        return;
    }

    printk("xSemaphoreGive(noTaskPending, noContextSwitch): %d \n", total_cycles);
    vSemaphoreDelete(testSemaphore);
}

void test_xEventGroupWaitBits_FlagAvailable(void)
{
    uint64_t total_cycles;
    uint64_t start_cycles;
    uint64_t end_cycles;
    BaseType_t result;
    EventGroupHandle_t testEventGroup;
    testEventGroup = xEventGroupCreate();

    xEventGroupSetBits(testEventGroup, EVENT_BIT_0);

    start_cycles = rdtsc();
    uxBits = xEventGroupWaitBits(
        testEventGroup,
        EVENT_BIT_0,     // bits to wait for
        pdFALSE,         // don’t clear on exit
        pdTRUE,          // wait for all bits
        0                // no wait, return immediately
    );
    end_cycles = rdtsc();
    total_cycles = end_cycles - start_cycles;
    printk("xEventGroupWaitBits (flagAvailable): %d \n", total_cycles);
}

void test_xQueueReceive_MessageAvailable(void)
{
    int send_val = 42;
    int recv_val = 0;
    uint64_t total_cycles;
    uint64_t start_cycles;
    uint64_t end_cycles;
    BaseType_t result;
    QueueHandle_t testQueue;
    start_cycles = 0;
    end_cycles = 0;

    testQueue = xQueueCreate(QUEUE_LENGTH, QUEUE_ITEM_SIZE);
    if (testQueue == NULL) {
        printk("Failed to create queue.\n");
        return;
    }

    // Send an item so that it is available for immediate receive
    if (xQueueSend(testQueue, &send_val, 0) != pdPASS) {
        printk("Failed to send item to queue.\n");
        vQueueDelete(testQueue);
        return;
    }

    // Measure CPU cycles for immediate (non-blocking) receive
    start_cycles = rdtsc();
    xQueueReceive(testQueue, &recv_val, 0);  // No blocking
    end_cycles = rdtsc();
    total_cycles = end_cycles - start_cycles;

    printk("xQueueReceive (message available): %d \n", total_cycles);

    // Cleanup
    vQueueDelete(testQueue);
}

void test_xQueueSend_noTaskPending_noContextSwitch(void)
{
    int value = 123;
    uint64_t total_cycles;
    uint64_t start_cycles;
    uint64_t end_cycles;
    BaseType_t result;
    QueueHandle_t testQueue;
    start_cycles = 0;
    end_cycles = 0;

    // Create a queue with enough space
    testQueue = xQueueCreate(QUEUE_LENGTH, QUEUE_ITEM_SIZE);
    if (testQueue == NULL) {
        printk("Failed to create queue.\n");
        return;
    }

    // Make sure the queue is empty
    xQueueReset(testQueue);

    // Measure the cycle count for xQueueSend (no task is pending to receive)
    start_cycles = rdtsc();
    xQueueSend(testQueue, &value, 0);  // Immediate, no block
    end_cycles = rdtsc();
    total_cycles = end_cycles - start_cycles;

    printk("xQueueSend (no task pending, no context switch): %d \n", total_cycles);

    // Cleanup
    vQueueDelete(testQueue);
}

void test_xEventGroupSetBits_NoTaskPending_NoContextSwitch(void)
{
    uint64_t total_cycles;
    uint64_t start_cycles;
    uint64_t end_cycles;
    EventGroupHandle_t testEventGroup;
    BaseType_t result;
    start_cycles = 0;
    end_cycles = 0;

    // Create the event group
    testEventGroup = xEventGroupCreate();
    if (testEventGroup == NULL) {
        printk("Failed to create event group.\n");
        return;
    }
    // Ensure no tasks are waiting on it — this should be the default
    xEventGroupClearBits(testEventGroup, EVENT_BIT_0);

    // Measure cycle count for xEventGroupSetBits (no waiters)
    start_cycles = rdtsc();
    xEventGroupSetBits(testEventGroup, EVENT_BIT_0);
    end_cycles = rdtsc();
    total_cycles = end_cycles - start_cycles;
    printk("xEventGroupSetBits (no task pending, no context switch): %d\n", total_cycles);

    // Cleanup
    vEventGroupDelete(testEventGroup);
}

static uint64_t ctx_swch_start_cycles;
static uint64_t ctx_swch_end_cycles;
static int test_completed = 0;
static int test_to_run = 0;

#define NO_CTX_SWTCH_TESTS                 1
#define EVGRP_WAIT_CTX_SWTCH               2
#define QRECV_WAIT_CTX_SWTCH               3
#define MTXRECV_WAIT_CTX_SWTCH             4
#define SEMRECV_WAIT_CTX_SWTCH             5
#define EVGRP_WAIT_CTX_SWTCH_PENDING       6
#define QRECV_WAIT_CTX_SWTCH_PENDING       7
#define MTXRECV_WAIT_CTX_SWTCH_PENDING     8
#define SEMRECV_WAIT_CTX_SWTCH_PENDING     9
#define ISR_TEST                          10
#define EVGRP_WAIT_CTX_SWTCH_ISR          11
#define QRECV_WAIT_CTX_SWTCH_ISR          12
#define SEMRECV_WAIT_CTX_SWTCH_ISR        13

static EventGroupHandle_t ctxSwtchTestEventGroup;
static QueueHandle_t ctxSwtchTestQueue;
static SemaphoreHandle_t ctxSwtchTestMutex;
static SemaphoreHandle_t ctxSwtchTestSemaphore;

void irq_hander(void)
{
    BaseType_t xHigherPriorityTaskWoken;
    BaseType_t result;
    int dummy=0;
    if (test_to_run == ISR_TEST) {
        ctx_swch_end_cycles = rdtsc();
        return;
    }
    if (test_to_run == EVGRP_WAIT_CTX_SWTCH_ISR) {
        ctx_swch_start_cycles = rdtsc();
        result = xEventGroupSetBitsFromISR(ctxSwtchTestEventGroup, EVENT_BIT_0, &xHigherPriorityTaskWoken);
        if (result == pdPASS) {
            portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
        }
        return;
    }
    if (test_to_run == QRECV_WAIT_CTX_SWTCH_ISR) {
        ctx_swch_start_cycles = rdtsc();
        
        result = xQueueSendFromISR(ctxSwtchTestQueue, &dummy, &xHigherPriorityTaskWoken);
        if (result == pdPASS) {
            portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
        }
        return;
    }
    if (test_to_run == SEMRECV_WAIT_CTX_SWTCH_ISR) {
        ctx_swch_start_cycles = rdtsc();
        result = xSemaphoreGiveFromISR(ctxSwtchTestSemaphore, &xHigherPriorityTaskWoken);
        if (result == pdPASS) {
            portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
        }
        return;
    }
}

static void waitingTask(void * pvParameters )
{
    while (1)
    {
        xEventGroupWaitBits(waitTaskEventGroup, EVENT_BIT_0, pdTRUE, pdTRUE, portMAX_DELAY);
        ctx_swch_end_cycles = rdtsc();
        test_completed = 1;
    }
    
}
static void perfTask( void * pvParameters )
{
    uint32_t ulReceivedValue;
    uint64_t total_cycles;
    uint64_t isr_complete_time;

    /* Prevent the compiler warning about the unused parameter. */
    ( void ) pvParameters;


    for( ; ; )
    {
 
        /* Wait for what test to execute */
        xQueueReceive( xQueue, &ulReceivedValue, portMAX_DELAY );

        switch (ulReceivedValue) {
	case NO_CTX_SWTCH_TESTS:
            test_xQueueReceive_MessageAvailable();
            test_xQueueSend_noTaskPending_noContextSwitch();
            test_xEventGroupWaitBits_FlagAvailable();
            test_xEventGroupSetBits_NoTaskPending_NoContextSwitch();
            test_xSemaphoreTake_mutexAvailable();
            test_xSemaphoreGive_noTaskPending_noContextSwitching();
            test_xBinarySemaphoreTake_SemaphoreAvailable();
            test_xBinarySemaphoreGive_noTaskPending_noContextSwitching();
            test_completed = 1;
            break;
        case EVGRP_WAIT_CTX_SWTCH:
            xEventGroupSetBits(waitTaskEventGroup, EVENT_BIT_0);
            ctx_swch_start_cycles = rdtsc();
            xEventGroupWaitBits(ctxSwtchTestEventGroup, EVENT_BIT_0, pdTRUE, pdTRUE, portMAX_DELAY);
            total_cycles = ctx_swch_end_cycles - ctx_swch_start_cycles;
            printk("xEventGroupWaitBits (flag unavailable, context switch to new task): %d\n", total_cycles);
            break;
        case QRECV_WAIT_CTX_SWTCH:
            xEventGroupSetBits(waitTaskEventGroup, EVENT_BIT_0);
            ctx_swch_start_cycles = rdtsc();
            xQueueReceive(ctxSwtchTestQueue, &ulReceivedValue, portMAX_DELAY );
            total_cycles = ctx_swch_end_cycles - ctx_swch_start_cycles;
            printk("xQueueReceive(message unavailable, context switch to new task): %d\n", total_cycles);
            break;
        case MTXRECV_WAIT_CTX_SWTCH:
            xEventGroupSetBits(waitTaskEventGroup, EVENT_BIT_0);
            ctx_swch_start_cycles = rdtsc();
            xSemaphoreTake(ctxSwtchTestMutex, portMAX_DELAY);
            total_cycles = ctx_swch_end_cycles - ctx_swch_start_cycles;
            printk("xSemaphoreTake(mutex unavailable, context switch to new task): %d\n", total_cycles);
            xSemaphoreGive(ctxSwtchTestMutex);
            break;
        case SEMRECV_WAIT_CTX_SWTCH:
            xEventGroupSetBits(waitTaskEventGroup, EVENT_BIT_0);
            ctx_swch_start_cycles = rdtsc();
            xSemaphoreTake(ctxSwtchTestSemaphore, portMAX_DELAY);
            total_cycles = ctx_swch_end_cycles - ctx_swch_start_cycles;
            printk("xSemaphoreTake(semaphore unavailable, context switch to new task): %d\n", total_cycles);
            break;
        case EVGRP_WAIT_CTX_SWTCH_PENDING:
            xEventGroupWaitBits(ctxSwtchTestEventGroup, EVENT_BIT_0, pdTRUE, pdTRUE, portMAX_DELAY);
            ctx_swch_end_cycles = rdtsc();
            total_cycles = ctx_swch_end_cycles - ctx_swch_start_cycles;
            printk("xEventGroupSetBits (task waiting, context switch to pending task): %d\n", total_cycles);
            test_completed = 1;
            break;
        case QRECV_WAIT_CTX_SWTCH_PENDING:
            xQueueReceive(ctxSwtchTestQueue, &ulReceivedValue, portMAX_DELAY );
            ctx_swch_end_cycles = rdtsc();
            total_cycles = ctx_swch_end_cycles - ctx_swch_start_cycles;
            printk("xQueueSend(task waiting, context switch to pending task): %d\n", total_cycles);
            test_completed = 1;
            break;
        case MTXRECV_WAIT_CTX_SWTCH_PENDING:
            xSemaphoreTake(ctxSwtchTestMutex, portMAX_DELAY);
            ctx_swch_end_cycles = rdtsc();
            total_cycles = ctx_swch_end_cycles - ctx_swch_start_cycles;
            printk("xSemaphoreGive(task waiting on mutex, context switch to pending task): %d\n", total_cycles);
            xSemaphoreGive(ctxSwtchTestMutex);
            test_completed = 1;
            break;
        case SEMRECV_WAIT_CTX_SWTCH_PENDING:
            xSemaphoreTake(ctxSwtchTestSemaphore, portMAX_DELAY);
            ctx_swch_end_cycles = rdtsc();
            total_cycles = ctx_swch_end_cycles - ctx_swch_start_cycles;
            printk("xSemaphoreGive(task waiting, context switch to pending task): %d\n", total_cycles);
            test_completed = 1;
            break;
        case ISR_TEST:
            ctx_swch_start_cycles = rdtsc();
            asm volatile("int $0x60");
            isr_complete_time = rdtsc();
            test_completed = 1;
            printk("Interrupt service time (FreeRTOS): %d\n",ctx_swch_end_cycles - ctx_swch_start_cycles);
            printk("Time to return from an ISR (FreeRTOS, no task switch): %d\n",isr_complete_time - ctx_swch_end_cycles);
            break;
        case EVGRP_WAIT_CTX_SWTCH_ISR:
            xEventGroupWaitBits(ctxSwtchTestEventGroup, EVENT_BIT_0, pdTRUE, pdTRUE, portMAX_DELAY);
            ctx_swch_end_cycles = rdtsc();
            total_cycles = ctx_swch_end_cycles - ctx_swch_start_cycles;
            printk("xEventGroupSetBits (from an ISR, switching to a pending task): %d\n", total_cycles);
            test_completed = 1;
            break;
        case QRECV_WAIT_CTX_SWTCH_ISR:
            xQueueReceive(ctxSwtchTestQueue, &ulReceivedValue, portMAX_DELAY );
            ctx_swch_end_cycles = rdtsc();
            total_cycles = ctx_swch_end_cycles - ctx_swch_start_cycles;
            printk("xQueueSend(from an ISR, switching to a pending task): %d\n", total_cycles);
            test_completed = 1;
            break;
        case SEMRECV_WAIT_CTX_SWTCH_ISR:
            xSemaphoreTake(ctxSwtchTestSemaphore, portMAX_DELAY);
            ctx_swch_end_cycles = rdtsc();
            total_cycles = ctx_swch_end_cycles - ctx_swch_start_cycles;
            printk("xSemaphoreGive (from an ISR, switching to a pending task): %d\n", total_cycles);
            test_completed = 1;
            break;
        }
    }
}

static BaseType_t prvRunPerformancetest(char * pcWriteBuffer,
                                  size_t xWriteBufferLen,
                                  const char * pcCommandString )
{    
    extern int stop_blinky_app_timer_processing;
    stop_blinky_app_timer_processing = 1;
    int dummy; 
    int_enable(0x60);
    int_handler_install(0x40, irq_hander);

#if !defined(__x86_64__)
    extern void (*test_irq_handler)(void);
    test_irq_handler = irq_hander;
#endif

    memset(pcWriteBuffer, 0x00, xWriteBufferLen);
    test_to_run = NO_CTX_SWTCH_TESTS;
    test_completed = 0;
    xTimerStart( xTimer, 0 );
    while (!test_completed) vTaskDelay(1);

    test_to_run = EVGRP_WAIT_CTX_SWTCH;
    test_completed = 0;
    xTimerStart( xTimer, 0 );
    while (!test_completed)
        vTaskDelay(1);
    xEventGroupSetBits(ctxSwtchTestEventGroup, EVENT_BIT_0);

    test_to_run = QRECV_WAIT_CTX_SWTCH;
    test_completed = 0;
    xTimerStart( xTimer, 0 );
    while (!test_completed)
        vTaskDelay(1);
    xQueueSend(ctxSwtchTestQueue, &dummy, 0U );

    test_to_run = MTXRECV_WAIT_CTX_SWTCH;
    test_completed = 0;
    xSemaphoreTake(ctxSwtchTestMutex, portMAX_DELAY);
    xTimerStart( xTimer, 0 );
    while (!test_completed)
        vTaskDelay(1);
    xSemaphoreGive(ctxSwtchTestMutex);

    test_to_run = SEMRECV_WAIT_CTX_SWTCH;
    test_completed = 0;
    xTimerStart( xTimer, 0 );
    while (!test_completed)
        vTaskDelay(1);
    xSemaphoreGive(ctxSwtchTestSemaphore);

    test_to_run = EVGRP_WAIT_CTX_SWTCH_PENDING;
    test_completed = 0;
    xTimerStart( xTimer, 0 );
    xTimerStart( xTestTimer, 0 );
    while (!test_completed)
        vTaskDelay(1);
   
    test_to_run = QRECV_WAIT_CTX_SWTCH_PENDING;
    test_completed = 0;
    xTimerStart( xTimer, 0 );
    xTimerStart( xTestTimer, 0 );
    while (!test_completed)
        vTaskDelay(1);
   
    test_to_run = MTXRECV_WAIT_CTX_SWTCH_PENDING;
    test_completed = 0;
    xTimerStart( xTimer, 0 );
    xTimerStart( xTestTimer, 0 );
    while (!test_completed)
        vTaskDelay(1);
   
    test_to_run = SEMRECV_WAIT_CTX_SWTCH_PENDING;
    test_completed = 0;
    xTimerStart( xTimer, 0 );
    xTimerStart( xTestTimer, 0 );
    while (!test_completed)
        vTaskDelay(1);
   
    test_to_run = ISR_TEST;
    test_completed = 0;
    xTimerStart( xTimer, 0 );
    while (!test_completed)
        vTaskDelay(1);

    test_to_run = EVGRP_WAIT_CTX_SWTCH_ISR;
    test_completed = 0;
    xTimerStart( xTimer, 0 );
    xTimerStart( xTestTimer, 0 );
    while (!test_completed)
        vTaskDelay(1);

    test_to_run = QRECV_WAIT_CTX_SWTCH_ISR;
    test_completed = 0;
    xTimerStart( xTimer, 0 );
    xTimerStart( xTestTimer, 0 );
    while (!test_completed)
        vTaskDelay(1);

    test_to_run = SEMRECV_WAIT_CTX_SWTCH_ISR;
    test_completed = 0;
    xTimerStart( xTimer, 0 );
    xTimerStart( xTestTimer, 0 );
    while (!test_completed)
        vTaskDelay(1);

    stop_blinky_app_timer_processing = 0;
    return pdFALSE;
}

static void prvQueueTestTimerCallback(TimerHandle_t xTimerHandle )
{
    ( void ) xTimerHandle;
    int dummy=0;
    switch(test_to_run) {
    case EVGRP_WAIT_CTX_SWTCH_PENDING:
        ctx_swch_start_cycles = rdtsc();
        xEventGroupSetBits(ctxSwtchTestEventGroup, EVENT_BIT_0);;
        break;
    case QRECV_WAIT_CTX_SWTCH_PENDING:
        ctx_swch_start_cycles = rdtsc();
        xQueueSend(ctxSwtchTestQueue, &dummy, 0U );
        break;
    case MTXRECV_WAIT_CTX_SWTCH_PENDING:
        ctx_swch_start_cycles = rdtsc();
        xSemaphoreGive(ctxSwtchTestMutex);
        break;
    case SEMRECV_WAIT_CTX_SWTCH_PENDING:
        ctx_swch_start_cycles = rdtsc();
        xSemaphoreGive(ctxSwtchTestSemaphore);
        break;
    case EVGRP_WAIT_CTX_SWTCH_ISR:
    case QRECV_WAIT_CTX_SWTCH_ISR:
    case SEMRECV_WAIT_CTX_SWTCH_ISR:
        asm volatile("int $0x60");
        break;
    }
}

static void prvQueueSendTimerCallback( TimerHandle_t xTimerHandle )
{
    ( void ) xTimerHandle;
    if (test_to_run == MTXRECV_WAIT_CTX_SWTCH_PENDING)
         xSemaphoreTake(ctxSwtchTestMutex, portMAX_DELAY);
    xQueueSend( xQueue, &test_to_run, 0U );
}

void startTasks(void)
{
    BaseType_t result;
    /* Create the queue. */
    waitTaskEventGroup = xEventGroupCreate();
    ctxSwtchTestEventGroup = xEventGroupCreate();
    ctxSwtchTestMutex = xSemaphoreCreateMutex();
    ctxSwtchTestSemaphore = xSemaphoreCreateBinary();
    ctxSwtchTestQueue = xQueueCreate( QUEUE_LENGTH, sizeof( uint32_t ) );
    xQueue = xQueueCreate( QUEUE_LENGTH, sizeof( uint32_t ) );
    /* Create the software timer, but don't start it yet. */
    xTimer = xTimerCreate( "Timer",
                            1,
                            pdFALSE,
                            NULL,
                            prvQueueSendTimerCallback);
    xTestTimer = xTimerCreate( "TestTimer",
                            100,
                            pdFALSE,
                            NULL,
                            prvQueueTestTimerCallback);

    if( xQueue != NULL )
    {
        result = xTaskCreate( perfTask,
                              "Perf",
                              configMINIMAL_STACK_SIZE,
                              NULL,
                              14|portPRIVILEGE_BIT,
                              NULL);
        result = xTaskCreate( waitingTask,
                              "Wait",
                              configMINIMAL_STACK_SIZE,
                              NULL,
                              13|portPRIVILEGE_BIT,
                              NULL);

    } 
    else {
        printk("startPerformance: failed to create queue\n");
    }
    return;
}

static const CLI_Command_Definition_t run_performance_test = {
    "run-performance-test",
    "\r\nrun-performance-test:\r\n Runs performance test and prints the result for each.\r\n\r\n",
    prvRunPerformancetest,
    0
};

void register_performance_test(void) {
    startTasks();
    FreeRTOS_CLIRegisterCommand(&run_performance_test);
}

