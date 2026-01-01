/* test-cmd
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
#if defined(__x86_64__)
#include "x86_64.h"
#include "usertask.h"
#endif

extern TaskParameters_t task_definition;
// Max allocatable memory 100 1000MB unit, 10 100MB units, 10 10MB units, 10 1MBUnits;
#define MAX_ALLOCATION_COUNT 130
static void *allocated_memory[MAX_ALLOCATION_COUNT];
static uint32_t allocated_count = 0;

#if defined(__x86_64__)
TaskParameters_t task_definition;
TaskHandle_t rxTask = NULL;
extern QueueHandle_t xUserQueue;
extern QueueHandle_t xUserResponseQueue;
#define STACK_SIZE            8192
extern uint32_t user_stack_size;
extern uint8_t userStack[STACK_SIZE];
static void createUserTask(TaskFunction_t pxCode, const char *pcName) {
    extern char __usercode_start;
    extern char __usercode_end;
    extern char __userdata_start;
    extern char __userdata_end;
    task_definition.pcName = pcName;
    task_definition.uxPriority = tskIDLE_PRIORITY;;
    task_definition.pvTaskCode = pxCode;
    task_definition.usStackDepth = user_stack_size/sizeof(StackType_t);
    task_definition.pvParameters = 0;

    task_definition.puxStackBuffer = (StackType_t *)(USER_VA_START + userStack);
    uint32_t num_region_used = xInitiRegionForRestrictedTask(task_definition.xRegions);

    // TASK Specific Regiions
    task_definition.xRegions[num_region_used].pvBaseAddress = &__usercode_start;
    task_definition.xRegions[num_region_used].ulLengthInBytes = (uint32_t) (&__usercode_end - &__usercode_start);
    task_definition.xRegions[num_region_used].ulParameters = REGION_RO;
    num_region_used++;

    task_definition.xRegions[num_region_used].pvBaseAddress = &__userdata_start;
    task_definition.xRegions[num_region_used].ulLengthInBytes = (uint32_t) (&__userdata_end - &__userdata_start);
    task_definition.xRegions[num_region_used].ulParameters = REGION_RW;
    num_region_used++;

    // Set the last region to 0 to indicate end of defined memory regions.
    task_definition.xRegions[num_region_used].pvBaseAddress = 0;
    task_definition.xRegions[num_region_used].ulLengthInBytes = 0;
    task_definition.xRegions[num_region_used].ulParameters = 0;

    xTaskCreateRestricted(&task_definition, &rxTask);

}
static BaseType_t  prvCreateUserTask( char * pcWriteBuffer,
                                  size_t xWriteBufferLen,
                                  const char * pcCommandString)
{
    if (xUserQueue != NULL) {
        vQueueDelete(xUserQueue);
        vQueueDelete(xUserResponseQueue);
    }
    xUserQueue = xQueueCreate( 1, sizeof( uint64_t ) );
    xUserResponseQueue = xQueueCreate( 1, sizeof( uint64_t ) );
    memset( pcWriteBuffer, 0x00, xWriteBufferLen );
    createUserTask(user_task,"UserTask");
    snprintf(pcWriteBuffer, xWriteBufferLen, "TASK CREATED. TASK HANDLE: %p\n",rxTask);
    return 0;
}
static BaseType_t prvTaskRegions( char * pcWriteBuffer,
                                  size_t xWriteBufferLen,
                                  const char * pcCommandString )
{
    memset( pcWriteBuffer, 0x00, xWriteBufferLen );
    if (rxTask != NULL) {
        uint32_t pos=0;
        pos += snprintf(pcWriteBuffer+pos,xWriteBufferLen-pos,"User Task Region Information\n");
        const struct xMEMORY_REGION * const xRegions = task_definition.xRegions;
        for (int region_index = 0; region_index < portNUM_CONFIGURABLE_REGIONS; region_index++) {
            if (xRegions[region_index].pvBaseAddress != 0) {
                pos +=snprintf(pcWriteBuffer+pos,xWriteBufferLen-pos,"startaddr: 0x%p, endaddr: 0x%016llX length: 0x%08X\n",USER_VA_START+xRegions[region_index].pvBaseAddress,
                               USER_VA_START+((uint64_t)xRegions[region_index].pvBaseAddress) + xRegions[region_index].ulLengthInBytes,
                               xRegions[region_index].ulLengthInBytes);
            }
        }
    } else {
        snprintf(pcWriteBuffer, xWriteBufferLen, "User task not created yet\n");
    }
    return 0;
}
static BaseType_t prvTaskCheck( char * pcWriteBuffer,
                                size_t xWriteBufferLen,
                                const char * pcCommandString )
{
    memset( pcWriteBuffer, 0x00, xWriteBufferLen );
    const char * pcParameter;
    BaseType_t xParameterStringLength;
    BaseType_t  xReturn;
    static UBaseType_t uxParameterNumber = 0;
    static uint32_t device_num = 0;

    if( uxParameterNumber == 0 ) {
        uxParameterNumber = 1U;
        xReturn = 1;
    }
    else if (uxParameterNumber == 1) {
        pcParameter = FreeRTOS_CLIGetParameter(
            pcCommandString,        /* The command string itself. */
            uxParameterNumber,      /* Return the next parameter. */
            &xParameterStringLength /* Store the parameter string length. */
           );
        uint64_t addressToSend = string_to_integer(pcParameter, xParameterStringLength);
        uint32_t pos = snprintf(pcWriteBuffer, xWriteBufferLen, "addressToSend %p\n",(void *)addressToSend);
        if ((rxTask != NULL) && (xUserQueue != NULL)) {
            xQueueSend( xUserQueue, &addressToSend, 0U );
	    uint64_t ulReceivedValue = 0;
	    BaseType_t xReturn=xQueueReceive( xUserResponseQueue, &ulReceivedValue, pdMS_TO_TICKS( 3000UL));
	    if (xReturn == pdPASS) {
                snprintf(pcWriteBuffer+pos,xWriteBufferLen-pos,"Received Value: %lx\n",ulReceivedValue);
            } else {
                snprintf(pcWriteBuffer+pos,xWriteBufferLen-pos,"\nTimeout while receiving value\n");
	    }
        } else {
            snprintf(pcWriteBuffer, xWriteBufferLen, "User task not created yet\n");
        }

        uxParameterNumber = 0;
        xReturn = 0;
   }
   return xReturn;
}


static const CLI_Command_Definition_t user_task_info =
{
    "user-task-info",
    "\r\nuser-task-info:\r\n Dump Information about user mode task\r\n\r\n",
    prvTaskRegions, /* The function to run. */
    0
};
static const CLI_Command_Definition_t check_user_task =
{
    "check-user-task",
    "\r\ncheck-user-task <address>:\r\n Send an address to restricted task\r\n\r\n",
    prvTaskCheck, /* The function to run. */
    1
};
static const CLI_Command_Definition_t create_user_task =
{
    "create-user-task",
    "\r\ncreate-user-task:\r\n Create FreeRTOS Restricted Task (User Mode)\r\n\r\n",
    prvCreateUserTask, /* The function to run. */
    0
};
#endif

static BaseType_t prvReadMem( char * pcWriteBuffer,
                                size_t xWriteBufferLen,
                                const char * pcCommandString )
{
    memset( pcWriteBuffer, 0x00, xWriteBufferLen );
    const char * pcParameter;
    BaseType_t xParameterStringLength;
    BaseType_t xReturn;
    static UBaseType_t uxParameterNumber = 0;
    static uint32_t addressToSend = 0;
    if( uxParameterNumber == 0 ) {
        uxParameterNumber = 1U;
        xReturn = 1;
    }
    else if (uxParameterNumber == 1) {
        pcParameter = FreeRTOS_CLIGetParameter(
            pcCommandString,        /* The command string itself. */
            uxParameterNumber,      /* Return the next parameter. */
            &xParameterStringLength /* Store the parameter string length. */
           );
        addressToSend = string_to_integer(pcParameter, xParameterStringLength);

        uint32_t *requested_address = (uint32_t *) addressToSend;
        if (requested_address == NULL) {
            snprintf(pcWriteBuffer, xWriteBufferLen, "requested addr  0x%p is NULL",requested_address);
            return 0;
        }
        snprintf(pcWriteBuffer, xWriteBufferLen, "Value 0x%x read at 0x%p\n", *requested_address, requested_address);

        uxParameterNumber = 0;
        xReturn = 0;
   }
return xReturn;
}


static BaseType_t prvWriteMem( char * pcWriteBuffer,
                                size_t xWriteBufferLen,
                                const char * pcCommandString )
{
    memset( pcWriteBuffer, 0x00, xWriteBufferLen );
    const char * pcParameter;
    BaseType_t xParameterStringLength;
    BaseType_t xReturn;
    static UBaseType_t uxParameterNumber = 0;
    static uint32_t addressToSend = 0;

    if( uxParameterNumber == 0 ) {
        uxParameterNumber = 1U;
        xReturn = 1;
    }
    else if (uxParameterNumber == 1) {
        pcParameter = FreeRTOS_CLIGetParameter(
            pcCommandString,        /* The command string itself. */
            uxParameterNumber,      /* Return the next parameter. */
            &xParameterStringLength /* Store the parameter string length. */
           );
        addressToSend  = string_to_integer(pcParameter, xParameterStringLength);
        uxParameterNumber = 2U;
        xReturn = 1;
    } else {
           pcParameter = FreeRTOS_CLIGetParameter(
            pcCommandString,        /* The command string itself. */
            uxParameterNumber,      /* Return the next parameter. */
            &xParameterStringLength /* Store the parameter string length. */
           );
	uint32_t value = (uint32_t) string_to_integer(pcParameter, xParameterStringLength);
        uint32_t *requested_address = (uint32_t *) addressToSend;
        if (requested_address == NULL) {
            snprintf(pcWriteBuffer, xWriteBufferLen, "requested addr  0x%p is NULL",requested_address);
            return 0;
        }
	*requested_address = value;
        snprintf(pcWriteBuffer, xWriteBufferLen, "Value 0x%x written at 0x%p\n", value, requested_address);
        uxParameterNumber = 0;
        xReturn = 0;
    }

   return xReturn;
}
static const CLI_Command_Definition_t write_mem_addr =
{
    "write-mem-addr",
    "\r\nwrite-mem-addr <address> <val>:\r\n Send an address to restricted task\r\n\r\n",
    prvWriteMem, /* The function to run. */
    2
};

static const CLI_Command_Definition_t read_mem_addr =
{
    "read-mem-addr",
    "\r\nread-mem-addr <address>:\r\n Send an address to restricted task\r\n\r\n",
    prvReadMem, /* The function to run. */
    1
};


static BaseType_t prvHeapInfo( char * pcWriteBuffer,
                                  size_t xWriteBufferLen,
                                  const char * pcCommandString )
{
    memset( pcWriteBuffer, 0x00, xWriteBufferLen );
    uint32_t pos=0;
    HeapStats_t heapStats;
    vPortGetHeapStats(&heapStats);
    pos += snprintf(pcWriteBuffer+pos, xWriteBufferLen-pos,"Heap Information\n");
    pos += snprintf(pcWriteBuffer+pos, xWriteBufferLen-pos,"xSizeOfLargestFreeBlockInBytes: %zu\n",heapStats.xSizeOfLargestFreeBlockInBytes);
    pos += snprintf(pcWriteBuffer+pos, xWriteBufferLen-pos,"xSizeOfSmallestFreeBlockInBytes: %zu\n",heapStats.xSizeOfSmallestFreeBlockInBytes);
    pos += snprintf(pcWriteBuffer+pos, xWriteBufferLen-pos,"xNumberOfFreeBlocks: %zu\n",heapStats.xNumberOfFreeBlocks);
    pos += snprintf(pcWriteBuffer+pos, xWriteBufferLen-pos,"xAvailableHeapSpaceInBytes: %zu\n",heapStats.xAvailableHeapSpaceInBytes);
    pos += snprintf(pcWriteBuffer+pos, xWriteBufferLen-pos,"xNumberOfSuccessfulAllocations: %zu\n",heapStats.xNumberOfSuccessfulAllocations);
    pos += snprintf(pcWriteBuffer+pos, xWriteBufferLen-pos,"xNumberOfSuccessfulFrees: %zu\n",heapStats.xNumberOfSuccessfulFrees);
    pos += snprintf(pcWriteBuffer+pos, xWriteBufferLen-pos,"xMinimumEverFreeBytesRemaining: %zu\n",heapStats.xMinimumEverFreeBytesRemaining);
    return 0;
}
static const CLI_Command_Definition_t heap_info =
{
    "heap-info",
    "\r\nheap-info:\r\n Dump Heap Information\r\n\r\n",
    prvHeapInfo, /* The function to run. */
    0
};

#define SUCCESS_FAILED(x)  x == 0 ? "Fail":"Success"

static BaseType_t prvMalloc( char * pcWriteBuffer,
                              size_t xWriteBufferLen,
                              const char * pcCommandString )
{
    memset( pcWriteBuffer, 0x00, xWriteBufferLen );
    const char * pcParameter;
    BaseType_t xParameterStringLength;
    BaseType_t  xReturn;
    static UBaseType_t uxParameterNumber = 0;
    static uint32_t device_num = 0;

    if( uxParameterNumber == 0U ) {
        uxParameterNumber = 1U;
        xReturn = 1;
    }
    else if (uxParameterNumber == 1) {
        for (int i=0;i<allocated_count;i++) {
            vPortFree(allocated_memory[i]);
            allocated_memory[i] = NULL;
        }
        allocated_count = 0;

        uint32_t max_allocatable_memory = 100000;
        memset(allocated_memory,0,MAX_ALLOCATION_COUNT*sizeof(void *));
        pcParameter = FreeRTOS_CLIGetParameter(
            pcCommandString,        /* The command string itself. */
            uxParameterNumber,      /* Return the next parameter. */
            &xParameterStringLength /* Store the parameter string length. */
           );
        uint32_t sizeinmb = string_to_integer(pcParameter, xParameterStringLength);
        uint32_t pos=0;
        uint32_t mb=1024*1024;
        if (sizeinmb > max_allocatable_memory) {
            snprintf(pcWriteBuffer+pos,xWriteBufferLen,"This command can only work to allocate maximum %dMB memory\n",max_allocatable_memory);
        } else {
            uint32_t total_allocated = 0;
            while (sizeinmb > 0) {
                void *alloc = 0;
                uint32_t alloc_size = 1000;
                if (sizeinmb < alloc_size){
                    alloc_size = sizeinmb;
		}
                while (alloc == 0) {
                    alloc = pvPortMalloc(alloc_size*mb);
                    if (alloc == 0) {
                        if (alloc_size > 100) {
                            alloc_size = 100;
                        } else if (alloc_size > 10) {
                            alloc_size = 10;
                        } else if (alloc_size > 1) {
                            alloc_size = 1;
                        } else {
                            break;
                        }
                    } 
                }
                if (alloc == 0)
                    break;
                total_allocated += alloc_size;
                allocated_memory[allocated_count] = alloc;
                pos+=snprintf(pcWriteBuffer+pos,xWriteBufferLen,"%d:0x%p %dMB\n",allocated_count,alloc,alloc_size);
                sizeinmb -= alloc_size;
                allocated_count++;
            }
            pos+=snprintf(pcWriteBuffer+pos,xWriteBufferLen,"Total Allocated %dMB\n",total_allocated);
        }

        uxParameterNumber = 0U;
        xReturn = 0;
    } 
    return xReturn;
}
static BaseType_t prvFree( char * pcWriteBuffer,
                              size_t xWriteBufferLen,
                              const char * pcCommandString )
{
    memset( pcWriteBuffer, 0x00, xWriteBufferLen );
    for (int i=0;i<allocated_count;i++) {
        vPortFree(allocated_memory[i]);
        allocated_memory[i] = NULL;
    }
    allocated_count = 0;
    snprintf(pcWriteBuffer,xWriteBufferLen,"All allocated memory is freed back\n");
    return 0;
}
static BaseType_t prvAllocMax( char * pcWriteBuffer,
                              size_t xWriteBufferLen,
                              const char * pcCommandString )
{
    memset( pcWriteBuffer, 0x00, xWriteBufferLen );
    const char * pcParameter;
    BaseType_t xParameterStringLength;
    BaseType_t  xReturn;
    static UBaseType_t uxParameterNumber = 0;
    static uint32_t device_num = 0;

    if( uxParameterNumber == 0 ) {
        uxParameterNumber = 1U;
        xReturn = 1;
    }
    else if (uxParameterNumber == 1) {
        for (int i=0;i<allocated_count;i++) {
            vPortFree(allocated_memory[i]);
            allocated_memory[i] = NULL;
        }
        allocated_count = 0;
        pcParameter = FreeRTOS_CLIGetParameter(
            pcCommandString,        /* The command string itself. */
            uxParameterNumber,      /* Return the next parameter. */
            &xParameterStringLength /* Store the parameter string length. */
           );
        uint64_t sizeinmb = string_to_integer(pcParameter, xParameterStringLength);
	sizeinmb = sizeinmb*1024*1024;

	void *alloc = pvPortMalloc(sizeinmb);
	if (alloc == 0) {
            snprintf(pcWriteBuffer,xWriteBufferLen,"FAILED\n");
	}else {
            int xPos=snprintf(pcWriteBuffer,xWriteBufferLen,"SUCCESS: 0x%p\n", alloc);
	    vPortFree(alloc);
            snprintf(pcWriteBuffer+xPos,xWriteBufferLen-xPos,"Allocated memory is freed back\n");
	}
	xReturn = 0;
    }
    return xReturn;
}
static const CLI_Command_Definition_t free_cmd =
{
    "free-test",
    "\r\nfree-test:\r\n Free memory allocated by malloc-test\r\n\r\n",
    prvFree, /* The function to run. */
    0
};
static const CLI_Command_Definition_t malloc_cmd =
{
    "malloc-test",
    "\r\nmalloc-test <size>:\r\nAlloc size MB memory\r\n\r\n",
    prvMalloc, /* The function to run. */
    1
};
static const CLI_Command_Definition_t alloc_max_cmd =
{
    "alloc-mem",
    "\r\nalloc-mem <size>:\r\nAllocate memory in one malloc call\r\n\r\n",
    prvAllocMax, /* The function to run. */
    1
};

void register_test_command(void) {
#if defined(__x86_64__)
    FreeRTOS_CLIRegisterCommand( &create_user_task );
    FreeRTOS_CLIRegisterCommand( &user_task_info );
    FreeRTOS_CLIRegisterCommand( &check_user_task );
#endif
    FreeRTOS_CLIRegisterCommand( &write_mem_addr );
    FreeRTOS_CLIRegisterCommand( &read_mem_addr );
    FreeRTOS_CLIRegisterCommand( &heap_info );
    FreeRTOS_CLIRegisterCommand( &malloc_cmd );
    FreeRTOS_CLIRegisterCommand( &free_cmd );
    FreeRTOS_CLIRegisterCommand( &alloc_max_cmd );
}
