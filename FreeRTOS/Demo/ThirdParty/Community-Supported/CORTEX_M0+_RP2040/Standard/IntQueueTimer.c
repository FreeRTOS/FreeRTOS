/*
 * FreeRTOS V202112.00
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

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo includes. */
#include "IntQueueTimer.h"
#include "IntQueue.h"

/* SDK APIs.*/
#include "pico/time.h"
#include "hardware/irq.h"

/* The priorities for the two timers.  Note that a priority of 0 is the highest
possible on Cortex-M devices. */
#define tmrMAX_PRIORITY				( 0UL )
#define trmSECOND_HIGHEST_PRIORITY ( tmrMAX_PRIORITY + 0x40 )

#define FIRST_TIMER_PERIOD_US 500
#define SECOND_TIMER_PERIOD_US 487

void prvAlarm0Callback( uint timer )
{
    configASSERT(timer == 0);
    BaseType_t xHigherPriorityTaskWoken = xFirstTimerHandler();
    hardware_alarm_set_target(0, make_timeout_time_us( FIRST_TIMER_PERIOD_US) );
    portEND_SWITCHING_ISR(xHigherPriorityTaskWoken);
}

void prvAlarm1Callback( uint timer )
{
    configASSERT(timer == 1);
    BaseType_t xHigherPriorityTaskWoken = xSecondTimerHandler();
    hardware_alarm_set_target(1, make_timeout_time_us( SECOND_TIMER_PERIOD_US) );
    portEND_SWITCHING_ISR(xHigherPriorityTaskWoken);
}

void vInitialiseTimerForIntQueueTest( void )
{
    /* Use raw hardware alarms so we have nested interrupts */
    hardware_alarm_claim(0);
    hardware_alarm_claim(1);

    /* Don't generate interrupts until the scheduler has been started.
       Interrupts will be automatically enabled when the first task starts
       running. */
    taskDISABLE_INTERRUPTS();

    /* Initialize timers. */

    /* Set the timer interrupts to be above the kernel.  The interrupts are
    assigned different priorities so they nest with each other. */
    irq_set_priority(TIMER_IRQ_0, tmrMAX_PRIORITY);
    irq_set_priority(TIMER_IRQ_1, trmSECOND_HIGHEST_PRIORITY);
    hardware_alarm_set_callback(0, prvAlarm0Callback);
    hardware_alarm_set_callback(1, prvAlarm1Callback);
    hardware_alarm_set_target(0, make_timeout_time_us( FIRST_TIMER_PERIOD_US) );
    hardware_alarm_set_target(1, make_timeout_time_us( SECOND_TIMER_PERIOD_US) );
}
