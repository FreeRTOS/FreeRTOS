/* cli 
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
#include "task.h"
#include "timers.h"
#include "semphr.h"
#include "queue.h"
#include "freertos_serial.h"
#include "string.h"
#include "stdio.h"
#include "io.h"
#include "cli.h"
#include "application.h"
#include "console.h"
#include "freertos_version.h"
#include "FreeRTOS_CLI.h"
#include "xen/xen.h"
#include <hypervisor.h>
QueueHandle_t xCliQueue = NULL;
extern int message_received_from_task;
extern int message_received_from_timer;
extern int message_sent_by_task;
extern int message_sent_by_timer;
void vSendConsoleInputToCli(char c);
void send_char_to_cli(void);
void cliTask( void *pvParameters);
#define CLI_QUEUE_LENGTH 64
#define CMD_BUFF_LENGTH 4096
static BaseType_t prvReboot( char * pcWriteBuffer,
                             size_t xWriteBufferLen,
                             const char * pcCommandString ) {
    (void)memset( pcWriteBuffer, 0x00, xWriteBufferLen );
    (void)snprintf(pcWriteBuffer, xWriteBufferLen, "Rebooting\n");
    HYPERVISOR_shutdown(SHUTDOWN_reboot);
    return 0;
}
static BaseType_t prvShutdown( char * pcWriteBuffer,
                               size_t xWriteBufferLen,
                               const char * pcCommandString ) {
    (void)memset( pcWriteBuffer, 0x00, xWriteBufferLen );
    (void)snprintf(pcWriteBuffer, xWriteBufferLen, "Shutting Down\n");
    HYPERVISOR_shutdown(SHUTDOWN_poweroff);
    return 0;
}
static BaseType_t prvError( char * pcWriteBuffer,
                            size_t xWriteBufferLen,
                            const char * pcCommandString ) {
    (void)memset( pcWriteBuffer, 0x00, xWriteBufferLen );
    printk("Forcing Error by sending to a NULL queue\n");
    (void) xQueueSend( 0, 0, 0U );
    return 0;
}
static BaseType_t prvTaskStatsCommand( char * pcWriteBuffer,
                                       size_t xWriteBufferLen,
                                       const char * pcCommandString)
{
    (void)memset( pcWriteBuffer, 0x00, xWriteBufferLen );
    const char * const pcHeader = "     State   Priority  Stack    #\r\n************************************************\r\n";
    BaseType_t xSpacePadding;

    /* Generate a table of task stats. */
    (void)strcpy( pcWriteBuffer, "\nTask");
    pcWriteBuffer += strlen( pcWriteBuffer );

    for( xSpacePadding = strlen( "Task" ); xSpacePadding < ( configMAX_TASK_NAME_LEN - 3 ); xSpacePadding++ )
    {
        /* Add a space to align columns after the task's name. */
        *pcWriteBuffer = ' ';
        pcWriteBuffer++;

        *pcWriteBuffer = 0x00;
    }

    (void)strcpy( pcWriteBuffer, pcHeader );
    vTaskList( pcWriteBuffer + strlen( pcHeader ) );

    return 0;
}
static BaseType_t prvVersion( char * pcWriteBuffer,
                              size_t xWriteBufferLen,
			      const char * pcCommandString)
{
    (void)memset( pcWriteBuffer, 0x00, xWriteBufferLen );
#if defined(__x86_64__)
    (void)snprintf(pcWriteBuffer, xWriteBufferLen, "x86_64:%s\n", FREERTOS_VERSION);
#else
    (void)snprintf(pcWriteBuffer, xWriteBufferLen, "x86_32:%s\n", FREERTOS_VERSION);
#endif
    return 0;
}
static const CLI_Command_Definition_t xTaskStats =
{
    "task-stats",        /* The command string to type. */
    "\r\ntask-stats:\r\n Displays a table showing the state of each FreeRTOS task\r\n\r\n",
    prvTaskStatsCommand, /* The function to run. */
    0                    /* No parameters are expected. */
};
static const CLI_Command_Definition_t xVersion =
{
    "version",        /* The command string to type. */
    "\r\nversion:\r\n Display FreeRTOS version and architecture\r\n\r\n",
    prvVersion, /* The function to run. */
    0                    /* No parameters are expected. */
};

static const CLI_Command_Definition_t xReboot =
{
    "reboot",
    "\r\nreboot:\r\n Reboot FreeRTOS\r\n\r\n",
    prvReboot, /* The function to run. */
    0
};
static const CLI_Command_Definition_t xError =
{
    "force-error",
    "\r\nforce-error:\r\n Force Error\r\n\r\n",
    prvError, /* The function to run. */
    0
};
static const CLI_Command_Definition_t xShutdown =
{
    "shutdown",
    "\r\nshutdown:\r\n Shut down FreeRTOS\r\n\r\n",
    prvShutdown, /* The function to run. */
    0
};

void vSendConsoleInputToCli(char c) {
    if (xCliQueue != NULL) {
        xQueueSendFromISR( xCliQueue, &c, 0U );
    }
}
void send_char_to_cli(void) {
       if ((serial_lsr() & 0x1) != 0){
	uint8_t char_value = serial_recv();
        if (xCliQueue != NULL) {
            xQueueSendFromISR( xCliQueue, &char_value, 0U );
        }
    }
}
void cliTask( void *pvParameters)
{
    int cmdbuf_index=0;
    char cmdbuf[CMD_BUFF_LENGTH];
    FreeRTOS_CLIRegisterCommand( &xTaskStats );
    FreeRTOS_CLIRegisterCommand( &xVersion );
    register_application_cli_commands();
    FreeRTOS_CLIRegisterCommand( &xError );
    FreeRTOS_CLIRegisterCommand( &xReboot );
    FreeRTOS_CLIRegisterCommand( &xShutdown );
    uint8_t ulReceivedValue;
    xCliQueue = xQueueCreate( CLI_QUEUE_LENGTH, sizeof( uint8_t ) );
    for( ; ; )
    {
        xQueueReceive( xCliQueue, &ulReceivedValue, portMAX_DELAY );
        if (ulReceivedValue != (unsigned long)'\r'){
            printk("%c",ulReceivedValue);
	}
        if ( ulReceivedValue == (unsigned long)'\r' ) {
            if (cmdbuf_index > 0) {
                cmdbuf[cmdbuf_index] = 0;
                cmdbuf_index++;
                char output[CMD_BUFF_LENGTH];
                int more_data = 0;
                printk("\n");
                do {
                   more_data = FreeRTOS_CLIProcessCommand(cmdbuf, output, CMD_BUFF_LENGTH);
                   printk("%s",output);
                } while (more_data != 0);
            } 
            printk("\n");
            printk("FreeRTOS-CLI>");
            cmdbuf_index = 0;
        } else {
            if ((cmdbuf_index == 0) && (isspace(ulReceivedValue))){
               continue;
	    }
            if (ulReceivedValue == (unsigned long)0x08) {
               if (cmdbuf_index > 0){
                   cmdbuf_index--;
	       }
               continue;
            }
            cmdbuf[cmdbuf_index] = ulReceivedValue;
            cmdbuf_index++;
        }
    }
}
