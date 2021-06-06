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
 * @file     sem_test.c
 * @brief    the main function for the sem test
 * @version  V1.0
 * @date     02. June 2017
 ******************************************************************************/
#include "test_kernel.h"
#include <csi_kernel.h>
#include <stdint.h>

#define EXAMPLE_K_SEM_STK_SIZE 1024

extern k_task_handle_t k_api_example_arr[];

static k_task_handle_t g_TestTask01;
static k_task_handle_t g_TestTask02;

#define TASK_PRIO_TEST  7

static k_sem_handle_t g_usSem;


static void Example_SemTask1(void)
{
    int uwRet;

    printf("Example_SemTask1 try get sem g_usSem ,timeout 10 ticks.\n");

    uwRet = csi_kernel_sem_wait(g_usSem, 10);

    if (0 == uwRet) {
        csi_kernel_sem_post(g_usSem);
    }

    if (uwRet < 0) {
        printf("Example_SemTask1 timeout and try get sem g_usSem wait forever.\n");

        uwRet = csi_kernel_sem_wait(g_usSem, -1);
        printf("Example_SemTask1 wait_forever and get sem g_usSem .\n");

        if (0 == uwRet) {
            csi_kernel_sem_post(g_usSem);
            csi_kernel_task_del(g_TestTask01);
        }
    }

    csi_kernel_task_del(g_TestTask01);
}

static void Example_SemTask2(void)
{
    int uwRet;
    printf("Example_SemTask2 try get sem g_usSem wait forever.\n");

    uwRet = csi_kernel_sem_wait(g_usSem, -1);

    if (0 == uwRet) {
        printf("Example_SemTask2 get sem g_usSem and then delay 20ticks .\n");
    }

    csi_kernel_delay(200);

    printf("Example_SemTask2 post sem g_usSem .\n");

    csi_kernel_sem_post(g_usSem);

    csi_kernel_task_del(g_TestTask02);
}

void example_main(void)
{
    g_usSem = csi_kernel_sem_new(1, 0);

    if (g_usSem == NULL) {
        printf("fail to create semaphore.\n");
    }

    csi_kernel_sched_suspend();

    csi_kernel_task_new((k_task_handle_t)Example_SemTask1, "MutexTsk1", NULL, TASK_PRIO_TEST - 1, TASK_TIME_QUANTA,  NULL, TEST_TASK_STACK_SIZE, &g_TestTask01);

    if (g_TestTask01 == NULL) {
        printf("fail to create task1.\n");
    }

    csi_kernel_task_new((k_task_handle_t)Example_SemTask2, "MutexTsk2", NULL, TASK_PRIO_TEST, TASK_TIME_QUANTA,  NULL, TEST_TASK_STACK_SIZE, &g_TestTask02);

    if (g_TestTask02 == NULL) {
        printf("fail to create task2.\n");
    }

    csi_kernel_sched_resume(0);

    csi_kernel_sem_post(g_usSem);

    csi_kernel_delay(400);

    csi_kernel_sem_del(g_usSem);

    printf("test kernel semaphore successfully !\n");
    csi_kernel_task_del(csi_kernel_task_get_cur());
}
