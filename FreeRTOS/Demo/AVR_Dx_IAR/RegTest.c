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

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo file headers. */
#include "regtest.h"

/* Test tasks that sets registers to known values, then checks to ensure the
values remain as expected.  Test 1 and test 2 use different values. */
static void prvRegisterCheck1( void *pvParameters );
static void prvRegisterCheck2( void *pvParameters );

/* Set to a non zero value should an error be found. */
portBASE_TYPE xRegTestError = pdFALSE;

/*-----------------------------------------------------------*/

void vStartRegTestTasks( void )
{
    xTaskCreate( prvRegisterCheck1, "Reg1", configMINIMAL_STACK_SIZE, NULL, tskIDLE_PRIORITY, NULL );
    xTaskCreate( prvRegisterCheck2, "Reg2", configMINIMAL_STACK_SIZE, NULL, tskIDLE_PRIORITY, NULL );
}
/*-----------------------------------------------------------*/

portBASE_TYPE xAreRegTestTasksStillRunning( void )
{
portBASE_TYPE xReturn;

    /* If a register was found to contain an unexpected value then the
    xRegTestError variable would have been set to a non zero value. */
    if( xRegTestError == pdFALSE )
    {
        xReturn = pdTRUE;
    }
    else
    {
        xReturn = pdFALSE;
    }
    
    return xReturn;
}
/*-----------------------------------------------------------*/

static void prvRegisterCheck1( void *pvParameters )
{
    ( void ) pvParameters;

    for( ;; )
    {
        asm(    "LDI    r31,    5           \n"
                "MOV    r0,     r31         \n"
                "LDI    r31,    6           \n"
                "MOV    r1,     r31         \n"
                "LDI    r31,    7           \n"
                "MOV    r2,     r31         \n"
                "LDI    r31,    8           \n"
                "MOV    r3,     r31         \n"
                "LDI    r31,    9           \n"
                "MOV    r4,     r31         \n"
                "LDI    r31,    10          \n"
                "MOV    r5,     r31         \n"
                "LDI    r31,    11          \n"
                "MOV    r6,     r31         \n"
                "LDI    r31,    12          \n"
                "MOV    r7,     r31         \n"
                "LDI    r31,    13          \n"
                "MOV    r8,     r31         \n"
                "LDI    r31,    14          \n"
                "MOV    r9,     r31         \n"
                "LDI    r31,    15          \n"
                "MOV    r10,    r31         \n"
                "LDI    r31,    16          \n"
                "MOV    r11,    r31         \n"
                "LDI    r31,    17          \n"
                "MOV    r12,    r31         \n"
                "LDI    r31,    18          \n"
                "MOV    r13,    r31         \n"
                "LDI    r31,    19          \n"
                "MOV    r14,    r31         \n"
                "LDI    r31,    20          \n"
                "MOV    r15,    r31         \n"
                "LDI    r16,    21          \n"
                "LDI    r17,    22          \n"
                "LDI    r18,    23          \n"
                "LDI    r19,    24          \n"
                "LDI    r20,    25          \n"
                "LDI    r21,    26          \n"
                "LDI    r22,    27          \n"
                "LDI    r23,    28          \n"
                "LDI    r24,    29          \n"
                "LDI    r25,    30          \n"
                "LDI    r26,    31          \n"
                "LDI    r27,    32          \n"
                "LDI    r28,    33          \n"
                "LDI    r29,    34          \n"
                "LDI    r30,    35            " );

        taskYIELD();

        asm(    "CPI    r31,    20          \n"
                "BREQ   no_err_1            \n"
                "STS    xRegTestError, r0   \n"
                "no_err_1:                  \n"
                "LDI    r31,    5           \n"
                "CPSE   r31,    r0          \n"
                "STS    xRegTestError, r0   \n"
                "LDI    r31,    6           \n"
                "CPSE   r31,    r1          \n"
                "STS    xRegTestError, r0   \n"
                "LDI    r31,    7           \n"
                "CPSE   r31,    r2          \n"
                "STS    xRegTestError, r0   \n"
                "LDI    r31,    8           \n"
                "CPSE   r31,    r3          \n"
                "STS    xRegTestError, r0   \n"
                "LDI    r31,    9           \n"
                "CPSE   r31,    r4          \n"
                "STS    xRegTestError, r0   \n"
                "LDI    r31,    10          \n"
                "CPSE   r31,    r5          \n"
                "STS    xRegTestError, r0   \n"
                "LDI    r31,    11          \n"
                "CPSE   r31,    r6          \n"
                "STS    xRegTestError, r0   \n"
                "LDI    r31,    12          \n"
                "CPSE   r31,    r7          \n"
                "STS    xRegTestError, r0   \n"
                "LDI    r31,    13          \n"
                "CPSE   r31,    r8          \n"
                "STS    xRegTestError, r0   \n"
                "LDI    r31,    14          \n"
                "CPSE   r31,    r9          \n"
                "STS    xRegTestError, r0   \n"
                "LDI    r31,    15          \n"
                "CPSE   r31,    r10         \n"
                "STS    xRegTestError, r0   \n"
                "LDI    r31,    16          \n"
                "CPSE   r31,    r11         \n"
                "STS    xRegTestError, r0   \n"
                "LDI    r31,    17          \n"
                "CPSE   r31,    r12         \n"
                "STS    xRegTestError, r0   \n"
                "LDI    r31,    18          \n"
                "CPSE   r31,    r13         \n"
                "STS    xRegTestError, r0   \n"
                "LDI    r31,    19          \n"
                "CPSE   r31,    r14         \n"
                "STS    xRegTestError, r0   \n"
                "LDI    r31,    20          \n"
                "CPSE   r31,    r15         \n"
                "STS    xRegTestError, r0   \n"
                "LDI    r31,    21          \n"
                "CPSE   r31,    r16         \n"
                "STS    xRegTestError, r0   \n"
                "LDI    r31,    22          \n"
                "CPSE   r31,    r17         \n"
                "STS    xRegTestError, r0   \n"
                "LDI    r31,    23          \n"
                "CPSE   r31,    r18         \n"
                "STS    xRegTestError, r0   \n"
                "LDI    r31,    24          \n"
                "CPSE   r31,    r19         \n"
                "STS    xRegTestError, r0   \n"
                "LDI    r31,    25          \n"
                "CPSE   r31,    r20         \n"
                "STS    xRegTestError, r0   \n"
                "LDI    r31,    26          \n"
                "CPSE   r31,    r21         \n"
                "STS    xRegTestError, r0   \n"
                "LDI    r31,    27          \n"
                "CPSE   r31,    r22         \n"
                "STS    xRegTestError, r0   \n"
                "LDI    r31,    28          \n"
                "CPSE   r31,    r23         \n"
                "STS    xRegTestError, r0   \n"
                "LDI    r31,    29          \n"
                "CPSE   r31,    r24         \n"
                "STS    xRegTestError, r0   \n"
                "LDI    r31,    30          \n"
                "CPSE   r31,    r25         \n"
                "STS    xRegTestError, r0   \n"
                "LDI    r31,    31          \n"
                "CPSE   r31,    r26         \n"
                "STS    xRegTestError, r0   \n"
                "LDI    r31,    32          \n"
                "CPSE   r31,    r27         \n"
                "STS    xRegTestError, r0   \n"
                "LDI    r31,    33          \n"
                "CPSE   r31,    r28         \n"
                "STS    xRegTestError, r0   \n"
                "LDI    r31,    34          \n"
                "CPSE   r31,    r29         \n"
                "STS    xRegTestError, r0   \n"
                "LDI    r31,    35          \n"
                "CPSE   r31,    r30         \n"
                "STS    xRegTestError, r0     " );
    }
}
/*-----------------------------------------------------------*/

static void prvRegisterCheck2( void *pvParameters )
{
    ( void ) pvParameters;

    for( ;; )
    {
        asm(    "LDI    r31,    1           \n"
                "MOV    r0,     r31         \n"
                "LDI    r31,    2           \n"
                "MOV    r1,     r31         \n"
                "LDI    r31,    3           \n"
                "MOV    r2,     r31         \n"
                "LDI    r31,    4           \n"
                "MOV    r3,     r31         \n"
                "LDI    r31,    5           \n"
                "MOV    r4,     r31         \n"
                "LDI    r31,    6           \n"
                "MOV    r5,     r31         \n"
                "LDI    r31,    7           \n"
                "MOV    r6,     r31         \n"
                "LDI    r31,    8           \n"
                "MOV    r7,     r31         \n"
                "LDI    r31,    9           \n"
                "MOV    r8,     r31         \n"
                "LDI    r31,    10          \n"
                "MOV    r9,     r31         \n"
                "LDI    r31,    11          \n"
                "MOV    r10,    r31         \n"
                "LDI    r31,    12          \n"
                "MOV    r11,    r31         \n"
                "LDI    r31,    13          \n"
                "MOV    r12,    r31         \n"
                "LDI    r31,    14          \n"
                "MOV    r13,    r31         \n"
                "LDI    r31,    15          \n"
                "MOV    r14,    r31         \n"
                "LDI    r31,    16          \n"
                "MOV    r15,    r31         \n"
                "LDI    r16,    17          \n"
                "LDI    r17,    18          \n"
                "LDI    r18,    19          \n"
                "LDI    r19,    20          \n"
                "LDI    r20,    21          \n"
                "LDI    r21,    22          \n"
                "LDI    r22,    23          \n"
                "LDI    r23,    24          \n"
                "LDI    r24,    25          \n"
                "LDI    r25,    26          \n"
                "LDI    r26,    27          \n"
                "LDI    r27,    28          \n"
                "LDI    r28,    29          \n"
                "LDI    r29,    30          \n"
                "LDI    r30,    31            " );

        taskYIELD();

        asm(    "CPI    r31,    16          \n"
                "BREQ   no_err_2            \n"
                "STS    xRegTestError, r0   \n"
                "no_err_2:                  \n"
                "LDI    r31,    1           \n"
                "CPSE   r31,    r0          \n"
                "STS    xRegTestError, r0   \n"
                "LDI    r31,    2           \n"
                "CPSE   r31,    r1          \n"
                "STS    xRegTestError, r0   \n"
                "LDI    r31,    3           \n"
                "CPSE   r31,    r2          \n"
                "STS    xRegTestError, r0   \n"
                "LDI    r31,    4           \n"
                "CPSE   r31,    r3          \n"
                "STS    xRegTestError, r0   \n"
                "LDI    r31,    5           \n"
                "CPSE   r31,    r4          \n"
                "STS    xRegTestError, r0   \n"
                "LDI    r31,    6           \n"
                "CPSE   r31,    r5          \n"
                "STS    xRegTestError, r0   \n"
                "LDI    r31,    7           \n"
                "CPSE   r31,    r6          \n"
                "STS    xRegTestError, r0   \n"
                "LDI    r31,    8           \n"
                "CPSE   r31,    r7          \n"
                "STS    xRegTestError, r0   \n"
                "LDI    r31,    9           \n"
                "CPSE   r31,    r8          \n"
                "STS    xRegTestError, r0   \n"
                "LDI    r31,    10          \n"
                "CPSE   r31,    r9          \n"
                "STS    xRegTestError, r0   \n"
                "LDI    r31,    11          \n"
                "CPSE   r31,    r10         \n"
                "STS    xRegTestError, r0   \n"
                "LDI    r31,    12          \n"
                "CPSE   r31,    r11         \n"
                "STS    xRegTestError, r0   \n"
                "LDI    r31,    13          \n"
                "CPSE   r31,    r12         \n"
                "STS    xRegTestError, r0   \n"
                "LDI    r31,    14          \n"
                "CPSE   r31,    r13         \n"
                "STS    xRegTestError, r0   \n"
                "LDI    r31,    15          \n"
                "CPSE   r31,    r14         \n"
                "STS    xRegTestError, r0   \n"
                "LDI    r31,    16          \n"
                "CPSE   r31,    r15         \n"
                "STS    xRegTestError, r0   \n"
                "LDI    r31,    17          \n"
                "CPSE   r31,    r16         \n"
                "STS    xRegTestError, r0   \n"
                "LDI    r31,    18          \n"
                "CPSE   r31,    r17         \n"
                "STS    xRegTestError, r0   \n"
                "LDI    r31,    19          \n"
                "CPSE   r31,    r18         \n"
                "STS    xRegTestError, r0   \n"
                "LDI    r31,    20          \n"
                "CPSE   r31,    r19         \n"
                "STS    xRegTestError, r0   \n"
                "LDI    r31,    21          \n"
                "CPSE   r31,    r20         \n"
                "STS    xRegTestError, r0   \n"
                "LDI    r31,    22          \n"
                "CPSE   r31,    r21         \n"
                "STS    xRegTestError, r0   \n"
                "LDI    r31,    23          \n"
                "CPSE   r31,    r22         \n"
                "STS    xRegTestError, r0   \n"
                "LDI    r31,    24          \n"
                "CPSE   r31,    r23         \n"
                "STS    xRegTestError, r0   \n"
                "LDI    r31,    25          \n"
                "CPSE   r31,    r24         \n"
                "STS    xRegTestError, r0   \n"
                "LDI    r31,    26          \n"
                "CPSE   r31,    r25         \n"
                "STS    xRegTestError, r0   \n"
                "LDI    r31,    27          \n"
                "CPSE   r31,    r26         \n"
                "STS    xRegTestError, r0   \n"
                "LDI    r31,    28          \n"
                "CPSE   r31,    r27         \n"
                "STS    xRegTestError, r0   \n"
                "LDI    r31,    29          \n"
                "CPSE   r31,    r28         \n"
                "STS    xRegTestError, r0   \n"
                "LDI    r31,    30          \n"
                "CPSE   r31,    r29         \n"
                "STS    xRegTestError, r0   \n"
                "LDI    r31,    31          \n"
                "CPSE   r31,    r30         \n"
                "STS    xRegTestError, r0   \n" );
    }
}
