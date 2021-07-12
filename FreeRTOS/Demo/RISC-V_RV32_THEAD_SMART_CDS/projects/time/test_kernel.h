/*
 * Copyright (C) 2017-2019 Alibaba Group Holding Limited. All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */



/******************************************************************************
 * @file     test_kernel.h
 * @brief    header file for the kernel test
 * @version  V1.0
 * @date     02. June 2017
 ******************************************************************************/
#include <stdio.h>
#include <stdint.h>

#define testTRUE    1
#define testFALSE   0
#define TASK_TIME_QUANTA    100  //you can change time_quanta through modifing configTICK_RATE_HZ.
#define TEST_TASK_STACK_SIZE     1024
#define WAIT_FOREVER    0xffffffff
