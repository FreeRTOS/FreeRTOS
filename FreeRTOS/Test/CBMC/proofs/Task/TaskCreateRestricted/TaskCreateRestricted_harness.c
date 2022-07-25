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
 * https://www.FreeRTOS.org
 * https://github.com/FreeRTOS
 *
 */

#include <stdint.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"

void vNondetSetCurrentTCB( void );
void vSetGlobalVariables( void );
void vPrepareTaskLists( void );
TaskHandle_t * pxNondetSetTaskHandle( void );
char * pcNondetSetString( size_t xSizeLength );
void vSetNonDeterministicListSizes( void );
TaskHandle_t pxCreateTCB();

void harness()
{
    // Set the task parameters
    TaskHandle_t * pxCreatedTask = pxNondetSetTaskHandle();
    const char * pcName = pcNondetSetString( configMAX_TASK_NAME_LEN );
    StackType_t * puxStackBuffer = pvPortMallocStack( ( ( ( size_t ) STACK_DEPTH ) * sizeof( StackType_t ) ) ); 
    TaskHandle_t tcb = pxCreateTCB();
    TaskParameters_t taskParameters = {
        .pcName=pcName, 
        .usStackDepth=STACK_DEPTH, 
        .puxStackBuffer=puxStackBuffer,
        .pxTaskBuffer=tcb,
        .uxPriority=nondet_basetype(),
    };

    // Initialize some global variables and task lists.
    vNondetSetCurrentTCB();
    vSetGlobalVariables();
    vPrepareTaskLists();
    vSetNonDeterministicListSizes();
    
    // Non-deterministically call either task-create-restricted
    // or its static version.
    if (nondet_bool()){
        xTaskCreateRestricted(&taskParameters, pxCreatedTask );
    } 
    else{
        xTaskCreateRestrictedStatic(&taskParameters, pxCreatedTask );
    }
    

    
}
