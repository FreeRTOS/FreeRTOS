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

/**
 * Creates two tasks that operate on an interrupt driven serial port.  A loopback
 * connector should be used so that everything that is transmitted is also received.
 * The serial port does not use any flow control.  On a standard 9way 'D' connector
 * pins two and three should be connected together.
 *
 * The first task repeatedly sends a string to a queue, character at a time.  The
 * serial port interrupt will empty the queue and transmit the characters.  The
 * task blocks for a pseudo random period before resending the string.
 *
 * The second task blocks on a queue waiting for a character to be received.
 * Characters received by the serial port interrupt routine are posted onto the
 * queue - unblocking the task making it ready to execute.  If this is then the
 * highest priority task ready to run it will run immediately - with a context
 * switch occurring at the end of the interrupt service routine.  The task
 * receiving characters is spawned with a higher priority than the task
 * transmitting the characters.
 *
 * With the loop back connector in place, one task will transmit a string and the
 * other will immediately receive it.  The receiving task knows the string it
 * expects to receive so can detect an error.
 *
 * This also creates a third task.  This is used to test semaphore usage from an
 * ISR and does nothing interesting.
 *
 * \page ComTestC comtest.c
 * \ingroup DemoFiles
 * <HR>
 */

/*
 * Changes from V1.00:
 *
 + The priority of the Rx task has been lowered.  Received characters are
 +    now processed (read from the queue) at the idle priority, allowing low
 +    priority tasks to run evenly at times of a high communications overhead.
 +
 + Changes from V1.01:
 +
 + The Tx task now waits a pseudo random time between transmissions.
 +    Previously a fixed period was used but this was not such a good test as
 +    interrupts fired at regular intervals.
 +
 + Changes From V1.2.0:
 +
 + Use vSerialPutString() instead of single character puts.
 + Only stop the check variable incrementing after two consecutive errors.
 +
 + Changed from V1.2.5
 +
 + Made the Rx task 2 priorities higher than the Tx task.  Previously it was
 +    only 1.  This is done to tie in better with the other demo application
 +    tasks.
 +
 + Changes from V2.0.0
 +
 + Delay periods are now specified using variables and constants of
 +    TickType_t rather than unsigned long.
 + Slight modification to task priorities.
 +
 */


/* Scheduler include files. */
#include <stdlib.h>
#include <string.h>
#include "FreeRTOS.h"
#include "task.h"

/* Demo program include files. */
#include "serial.h"
#include "comtest.h"
#include "print.h"

/* The Tx task will transmit the sequence of characters at a pseudo random
 * interval.  This is the maximum and minimum block time between sends. */
#define comTX_MAX_BLOCK_TIME         ( ( TickType_t ) 0x15e )
#define comTX_MIN_BLOCK_TIME         ( ( TickType_t ) 0xc8 )

#define comMAX_CONSECUTIVE_ERRORS    ( 2 )

#define comSTACK_SIZE                ( ( unsigned short ) 256 )

#define comRX_RELATIVE_PRIORITY      ( 1 )

/* Handle to the com port used by both tasks. */
static xComPortHandle xPort;

/* The transmit function as described at the top of the file. */
static void vComTxTask( void * pvParameters );

/* The receive function as described at the top of the file. */
static void vComRxTask( void * pvParameters );

/* The semaphore test function as described at the top of the file. */
static void vSemTestTask( void * pvParameters );

/* The string that is repeatedly transmitted. */
const char * const pcMessageToExchange = "Send this message over and over again to check communications interrupts. "
                                         "0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ\r\n";

/* Variables that are incremented on each cycle of each task.  These are used to
 * check that both tasks are still executing. */
volatile short sTxCount = 0, sRxCount = 0, sSemCount = 0;

/* The handle to the semaphore test task. */
static TaskHandle_t xSemTestTaskHandle = NULL;

/*-----------------------------------------------------------*/

void vStartComTestTasks( unsigned portBASE_TYPE uxPriority,
                         eCOMPort ePort,
                         eBaud eBaudRate )
{
    const unsigned portBASE_TYPE uxBufferLength = 255;

    /* Initialise the com port then spawn both tasks. */
    xPort = xSerialPortInit( ePort, eBaudRate, serNO_PARITY, serBITS_8, serSTOP_1, uxBufferLength );
    xTaskCreate( vComTxTask, "COMTx", comSTACK_SIZE, NULL, uxPriority, NULL );
    xTaskCreate( vComRxTask, "COMRx", comSTACK_SIZE, NULL, uxPriority + comRX_RELATIVE_PRIORITY, NULL );
    xTaskCreate( vSemTestTask, "ISRSem", comSTACK_SIZE, NULL, tskIDLE_PRIORITY, &xSemTestTaskHandle );
}
/*-----------------------------------------------------------*/

static void vComTxTask( void * pvParameters )
{
    const char * const pcTaskStartMsg = "COM Tx task started.\r\n";
    TickType_t xTimeToWait;

    /* Stop warnings. */
    ( void ) pvParameters;

    /* Queue a message for printing to say the task has started. */
    vPrintDisplayMessage( &pcTaskStartMsg );

    for( ; ; )
    {
        /* Send the string to the serial port. */
        vSerialPutString( xPort, pcMessageToExchange, strlen( pcMessageToExchange ) );

        /* We have posted all the characters in the string - increment the variable
         * used to check that this task is still running, then wait before re-sending
         * the string. */
        sTxCount++;

        xTimeToWait = xTaskGetTickCount();

        /* Make sure we don't wait too long... */
        xTimeToWait %= comTX_MAX_BLOCK_TIME;

        /* ...but we do want to wait. */
        if( xTimeToWait < comTX_MIN_BLOCK_TIME )
        {
            xTimeToWait = comTX_MIN_BLOCK_TIME;
        }

        vTaskDelay( xTimeToWait );
    }
} /*lint !e715 !e818 pvParameters is required for a task function even if it is not referenced. */
/*-----------------------------------------------------------*/

static void vComRxTask( void * pvParameters )
{
    const char * const pcTaskStartMsg = "COM Rx task started.\r\n";
    const char * const pcTaskErrorMsg = "COM read error\r\n";
    const char * const pcTaskRestartMsg = "COM resynced\r\n";
    const char * const pcTaskTimeoutMsg = "COM Rx timed out\r\n";
    const TickType_t xBlockTime = ( TickType_t ) 0xffff / portTICK_PERIOD_MS;
    const char * pcExpectedChar;
    portBASE_TYPE xGotChar;
    char cRxedChar;
    short sResyncRequired, sConsecutiveErrors, sLatchedError;

    /* Stop warnings. */
    ( void ) pvParameters;

    /* Queue a message for printing to say the task has started. */
    vPrintDisplayMessage( &pcTaskStartMsg );

    /* The first expected character is the first character in the string. */
    pcExpectedChar = pcMessageToExchange;
    sResyncRequired = pdFALSE;
    sConsecutiveErrors = 0;
    sLatchedError = pdFALSE;

    for( ; ; )
    {
        /* Receive a message from the com port interrupt routine.  If a message is
         * not yet available the call will block the task. */
        xGotChar = xSerialGetChar( xPort, &cRxedChar, xBlockTime );

        if( xGotChar == pdTRUE )
        {
            if( sResyncRequired == pdTRUE )
            {
                /* We got out of sequence and are waiting for the start of the next
                 * transmission of the string. */
                if( cRxedChar == '\n' )
                {
                    /* This is the end of the message so we can start again - with
                     * the first character in the string being the next thing we expect
                     * to receive. */
                    pcExpectedChar = pcMessageToExchange;
                    sResyncRequired = pdFALSE;

                    /* Queue a message for printing to say that we are going to try
                     * again. */
                    vPrintDisplayMessage( &pcTaskRestartMsg );

                    /* Stop incrementing the check variable, if consecutive errors occur. */
                    sConsecutiveErrors++;

                    if( sConsecutiveErrors >= comMAX_CONSECUTIVE_ERRORS )
                    {
                        sLatchedError = pdTRUE;
                    }
                }
            }
            else
            {
                /* We have received a character, but is it the expected character? */
                if( cRxedChar != *pcExpectedChar )
                {
                    /* This was not the expected character so post a message for
                     * printing to say that an error has occurred.  We will then wait
                     * to resynchronise. */
                    vPrintDisplayMessage( &pcTaskErrorMsg );
                    sResyncRequired = pdTRUE;
                }
                else
                {
                    /* This was the expected character so next time we will expect
                     * the next character in the string.  Wrap back to the beginning
                     * of the string when the null terminator has been reached. */
                    pcExpectedChar++;

                    if( *pcExpectedChar == '\0' )
                    {
                        pcExpectedChar = pcMessageToExchange;

                        /* We have got through the entire string without error. */
                        sConsecutiveErrors = 0;
                    }
                }
            }

            /* Increment the count that is used to check that this task is still
             * running.  This is only done if an error has never occurred. */
            if( sLatchedError == pdFALSE )
            {
                sRxCount++;
            }
        }
        else
        {
            vPrintDisplayMessage( &pcTaskTimeoutMsg );
        }
    }
} /*lint !e715 !e818 pvParameters is required for a task function even if it is not referenced. */
/*-----------------------------------------------------------*/

static void vSemTestTask( void * pvParameters )
{
    const char * const pcTaskStartMsg = "ISR Semaphore test started.\r\n";
    portBASE_TYPE xError = pdFALSE;

    /* Stop warnings. */
    ( void ) pvParameters;

    /* Queue a message for printing to say the task has started. */
    vPrintDisplayMessage( &pcTaskStartMsg );

    for( ; ; )
    {
        if( xSerialWaitForSemaphore( xPort ) )
        {
            if( xError == pdFALSE )
            {
                sSemCount++;
            }
        }
        else
        {
            xError = pdTRUE;
        }
    }
} /*lint !e715 !e830 !e818 pvParameters not used but function prototype must be standard for task function. */
/*-----------------------------------------------------------*/

/* This is called to check that all the created tasks are still running. */
portBASE_TYPE xAreComTestTasksStillRunning( void )
{
    static short sLastTxCount = 0, sLastRxCount = 0, sLastSemCount = 0;
    portBASE_TYPE xReturn;

    /* Not too worried about mutual exclusion on these variables as they are 16
     * bits and we are only reading them.  We also only care to see if they have
     * changed or not. */

    if( ( sTxCount == sLastTxCount ) || ( sRxCount == sLastRxCount ) || ( sSemCount == sLastSemCount ) )
    {
        xReturn = pdFALSE;
    }
    else
    {
        xReturn = pdTRUE;
    }

    sLastTxCount = sTxCount;
    sLastRxCount = sRxCount;
    sLastSemCount = sSemCount;

    return xReturn;
}
/*-----------------------------------------------------------*/

void vComTestUnsuspendTask( void )
{
    /* The task that is suspended on the semaphore will be referenced from the
     * Suspended list as it is blocking indefinitely.  This call just checks that
     * the kernel correctly detects this and does not attempt to unsuspend the
     * task. */
    xTaskResumeFromISR( xSemTestTaskHandle );
}
