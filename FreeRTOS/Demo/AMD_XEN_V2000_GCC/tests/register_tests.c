/* register_tests
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
#include "stdio.h"
#include "task.h"
#include "cli.h"
#include "register_tests.h"

/* This file is a wrapper to register all test commands */
#define mainNO_ERROR_CHECK_TASK_PERIOD          pdMS_TO_TICKS( ( TickType_t ) 5000 )
void check_test_result(const char *testname,
                       BaseType_t (*checkfunc)(void),
                       char * pcWriteBuffer,
                       size_t xWriteBufferLen) {
    TickType_t xDelayPeriod = mainNO_ERROR_CHECK_TASK_PERIOD;
    TickType_t xLastExecutionTime = xTaskGetTickCount();
    xTaskDelayUntil( &xLastExecutionTime, xDelayPeriod );
    if (checkfunc() != pdTRUE) {
        snprintf(pcWriteBuffer, xWriteBufferLen, "FAIL: %s\n",testname);
    } else {
        snprintf(pcWriteBuffer, xWriteBufferLen, "PASS: %s\n",testname);
    }
}


void register_test_command(void);
void register_blocktim_test(void);
void register_tasknotify_test(void);
void register_mutex_test(void);
void register_streambuffer_test(void);
void register_messagebuffer_test(void);
void register_eventgroups_test(void);
void register_semtest_test(void);
void register_countsem_test(void);
void register_tasknotifyarray_test(void);
void register_genq_test(void);
void register_qpeek_test(void);
void register_blockq_test(void);
void register_pollq_test(void);
void register_dynamic_test(void);
void register_timer_demo(void);
void register_xenbus_read_test(void);
void register_xenbus_ls_test(void);
void register_gnt_test(void);
void register_gntmap_test(void);
void register_argoRegister_test(void);
void register_argoConnect_test(void);
void register_argoSendv_test(void);
void register_argoUnregister_test(void);
void register_performance_test(void);
__attribute__((weak)) void register_all_tests(void)
{
    register_test_command();
    register_blocktim_test();
    register_tasknotify_test();
    register_streambuffer_test();
    register_mutex_test();
    register_messagebuffer_test();
    register_eventgroups_test();
    register_semtest_test();
    register_countsem_test();
    register_tasknotifyarray_test();
    register_genq_test();
    register_qoverwrite_test();
    register_qpeek_test();
    register_blockq_test();
    register_pollq_test();
    register_dynamic_test();
    register_timer_demo();
    register_xenbus_read_test();
    register_xenbus_ls_test();
    register_gnt_test();
    register_gntmap_test();
    register_argoRegister_test();
    register_argoConnect_test();
    register_argoSendv_test();
    register_argoUnregister_test();
    register_performance_test();
}

