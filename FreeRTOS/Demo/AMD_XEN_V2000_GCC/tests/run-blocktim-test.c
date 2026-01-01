/* run-blocktim-test
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
#include "register_tests.h"
#include "blocktim.h"

static int test_started = 0;
static BaseType_t prvRunBlocktimtest( char * pcWriteBuffer,
                                  size_t xWriteBufferLen,
                                  const char * pcCommandString )
{
    memset(pcWriteBuffer, 0x00, xWriteBufferLen );
    if (test_started == 0){
        vCreateBlockTimeTasks();
    }
    else {
        snprintf(pcWriteBuffer,xWriteBufferLen," Test already run");
        return 0;
    }
    test_started = 1;
    check_test_result("Blocktim", xAreBlockTimeTestTasksStillRunning, pcWriteBuffer, xWriteBufferLen);
    return 0;
}

static const CLI_Command_Definition_t blocktim =
{
    "run-blocktim-test",
    "\r\nrun-blocktim-test:\r\n run-blocktim-test\r\n\r\n",
    prvRunBlocktimtest, /* The function to run. */
    0
};

void register_blocktim_test(void) {
    FreeRTOS_CLIRegisterCommand(&blocktim);
}

