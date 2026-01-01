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

#ifndef _REGISTER_TEST_H_
#define _REGISTER_TEST_H_
#include "FreeRTOS.h"
#include "stdio.h"
#include "cli.h"
#define mainNO_ERROR_CHECK_TASK_PERIOD          pdMS_TO_TICKS( ( TickType_t ) 5000 )
void check_test_result(const char *testname, BaseType_t (*checkfunc)(void), char * pcWriteBuffer, size_t xWriteBufferLen);
void register_i2c_test_commands(void);
void register_test_command(void);
void register_blocktim_demo(void);
void register_tasknotifytest_demo(void);
void register_eventgroupstest_demo(void);
void register_tasknotifyarraytest_demo(void);
void register_genqtest_demo(void);
void register_abortdelaytest_demo(void);
void register_qpeek_demo(void);
void register_qoverwrite_demo(void);
void register_blockq_demo(void);
void register_pollq_demo(void);
void register_demo_dynamic(void);
void register_timertest_demo(void);
void register_qoverwrite_test(void);
void register_xenbus_read_test(void);
void register_xenbus_ls_test(void);
void register_gnt_test(void);
void register_gntmap_test(void);
void register_argoRegister_test(void);
void register_argoConnect_test(void);
void register_argoSendv_test(void);
void register_argoUnregister_test(void);
#endif
