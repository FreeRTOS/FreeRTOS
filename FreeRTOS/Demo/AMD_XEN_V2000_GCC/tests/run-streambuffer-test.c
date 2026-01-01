/* run-streambuffer-test
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
#include "string.h"
#include "stdio.h"
#include "cli.h"
#include "task.h"
#include "StreamBufferDemo.h"
#include "register_tests.h"
#include "stream_buffer.h"
#include "timers.h"


/* The number of bytes of storage in the stream buffers used in this test. */
#define sbSTREAM_BUFFER_LENGTH_BYTES    ( ( size_t ) 64 )

/* The trigger level sets the number of bytes that must be present in the
 * stream buffer before a task that is blocked on the stream buffer is moved out of
 * the Blocked state so it can read the bytes. */
#define sbTRIGGER_LEVEL_1               ( 1 )

/* Test Parameters */
#define MAX_ITERATIONS 3
int writerSuccess = 0;
int readerSuccess = 0;

int test_started=0;

// Stream buffer handle
StreamBufferHandle_t xStreamBuffer;

// Task to send data to the stream buffer
void vSenderTask(void *pvParameters)
{
    const char *pcMessage = "Hello from Sender Task!";
    size_t xMessageLength = strlen(pcMessage);
    for (int i = 0; i < MAX_ITERATIONS; i++)
    {
        // Send the message to the stream buffer
        size_t xBytesSent = xStreamBufferSend(xStreamBuffer, (void *)pcMessage, xMessageLength, pdMS_TO_TICKS(1000));
        // If the data is successfully sent, output debug info
        if (xBytesSent == xMessageLength)
        {
            writerSuccess++;
        }
        // Delay to simulate periodic data sending
        vTaskDelay(pdMS_TO_TICKS(500));
    }
    vTaskDelete(NULL);

}

// Task to receive data from the stream buffer
void vReceiverTask(void *pvParameters)
{
    char buffer[128];  // Buffer to hold received data
    size_t xReceivedBytes;
    for (int i = 0; i < MAX_ITERATIONS; i++)
    {
        // Receive data from the stream buffer
        xReceivedBytes = xStreamBufferReceive(xStreamBuffer, buffer, sizeof(buffer), pdMS_TO_TICKS(1000));

        // If data is received, output debug info
        if (xReceivedBytes > (size_t)0)
        {
            // Ensure null-termination for printing
            buffer[xReceivedBytes] = '\0';
        }
      
        if( memcmp( buffer, "Hello from Sender Task!", xReceivedBytes ) == 0 )
        {
             readerSuccess++;
        }
        vTaskDelay(pdMS_TO_TICKS(500));
    }
    vTaskDelete(NULL);

}


int streambufferstart()
{
    BaseType_t xReturn;

    // Create a stream buffer with the defined length and trigger level
    xStreamBuffer = xStreamBufferCreate(sbSTREAM_BUFFER_LENGTH_BYTES, sbTRIGGER_LEVEL_1);
    configASSERT( xStreamBuffer != NULL );

    // Check if the stream buffer was created successfully
    if (xStreamBuffer != NULL)
    {
        // Create the sender task
        xReturn=   xTaskCreate(vSenderTask, "Sender", configMINIMAL_STACK_SIZE, NULL,tskIDLE_PRIORITY + 1, NULL);
        configASSERT( xReturn == pdPASS );

        // Create the receiver task
        xReturn= xTaskCreate(vReceiverTask, "Receiver", configMINIMAL_STACK_SIZE, NULL,tskIDLE_PRIORITY + 1, NULL);
        configASSERT( xReturn == pdPASS );
    }

    vTaskDelay(pdMS_TO_TICKS(5000));

    if ((writerSuccess  >=  MAX_ITERATIONS) && (readerSuccess  >=  MAX_ITERATIONS))
    {
        if ((writerSuccess == MAX_ITERATIONS) && (readerSuccess == MAX_ITERATIONS))
        {
            return pdPASS;
        }
        else
        {
            return pdFAIL;
        }

    }
    else{
       return pdFAIL;
    }
}

static BaseType_t  prvRunstreambuffertest( char * pcWriteBuffer,
                                  size_t xWriteBufferLen,
                                  const char * pcCommandString )
{
    memset(pcWriteBuffer, 0x00, xWriteBufferLen );
    if (test_started == 0)
    {
        if(streambufferstart()==pdFAIL){
            snprintf(pcWriteBuffer,xWriteBufferLen,"FAIL: run-streambuffer-test");
	}
	else{
            snprintf(pcWriteBuffer,xWriteBufferLen,"PASS: run-streambuffer-test");
	}
    }

    else {
        snprintf(pcWriteBuffer,xWriteBufferLen," Test already run");
        return 0;
    }
    test_started = 1;
    return 0;

}

static const CLI_Command_Definition_t run_streambuffer_test =
{
    "run-streambuffer-test",
    "\r\nrun-streambuffer-test:\r\n Run streambuffer test\r\n\r\n",
    prvRunstreambuffertest, /* The function to run. */
    0
};

void register_streambuffer_test(void) {
    FreeRTOS_CLIRegisterCommand( &run_streambuffer_test );
}


