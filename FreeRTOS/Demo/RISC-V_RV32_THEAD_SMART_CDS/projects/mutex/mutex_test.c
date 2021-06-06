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
 * @file     mutex_test.c
 * @brief    the main function for the mutex test
 * @version  V1.0
 * @date     02. June 2017
 ******************************************************************************/
#include "test_kernel.h"
#include <csi_kernel.h>
#include <stdint.h>

extern k_task_handle_t k_api_example_arr[];

#define MUTEX_TASK_HI_PRIO    7
#define MUTEX_TASK_LO_PRIO    6

#define EXAMPLE_K_MUTEX_STK_SIZE 1024

static k_mutex_handle_t  g_Testmux01;

static k_task_handle_t g_TestTask01;
static k_task_handle_t g_TestTask02;

static void Example_MutexTask1()
{
    int uwRet;

    printf("task1 try to get  mutex, wait 10 ticks.\n");

    uwRet = csi_kernel_mutex_lock(g_Testmux01, 10);

    if (uwRet == 0) {
        printf("task1 get mutex g_Testmux01.\n");
        csi_kernel_mutex_unlock(g_Testmux01);
        csi_kernel_task_del(g_TestTask01);
        return;
    } else if (uwRet == -ETIMEDOUT || uwRet < 0) {
        printf("task1 timeout and try to get  mutex, wait forever.\n");
        uwRet = csi_kernel_mutex_lock(g_Testmux01, -1);

        if (uwRet == 0) {
            printf("task1 wait forever,get mutex g_Testmux01.\n");
            csi_kernel_mutex_unlock(g_Testmux01);
        }
    }

    csi_kernel_task_del(g_TestTask01);
    return;
}

static void Example_MutexTask2()
{
    printf("task2 try to get  mutex, wait forever.\n");
    csi_kernel_mutex_lock(g_Testmux01, -1);

    printf("task2 get mutex g_Testmux01 and suspend 100 ticks.\n");
    csi_kernel_delay(200);

    printf("task2 resumed and post the g_Testmux01\n");
    csi_kernel_mutex_unlock(g_Testmux01);

    csi_kernel_task_del(g_TestTask02);
    return;
}

void example_main(void)
{
    g_Testmux01 = csi_kernel_mutex_new();

    if (g_Testmux01 == NULL) {
        printf("csi_kernel_mutex_new return error.\n");
    }

    csi_kernel_sched_suspend();

    csi_kernel_task_new((k_task_entry_t)Example_MutexTask1, "MutexTsk1", NULL, MUTEX_TASK_LO_PRIO, TASK_TIME_QUANTA,  NULL, TEST_TASK_STACK_SIZE, &g_TestTask01);

    if (g_TestTask01 == NULL) {
        printf("fail to task1 create.\n");
    }

    csi_kernel_task_new((k_task_entry_t)Example_MutexTask2, "MutexTsk2", NULL, MUTEX_TASK_HI_PRIO, TASK_TIME_QUANTA,  NULL, TEST_TASK_STACK_SIZE, &g_TestTask02);

    if (g_TestTask02 == NULL) {
        printf("fail to create task2.\n");
    }

    csi_kernel_sched_resume(0);

    csi_kernel_delay(500);

    csi_kernel_mutex_del(g_Testmux01);

    printf("test kernel mutex successfully !\n");
    csi_kernel_task_del(csi_kernel_task_get_cur());
}
