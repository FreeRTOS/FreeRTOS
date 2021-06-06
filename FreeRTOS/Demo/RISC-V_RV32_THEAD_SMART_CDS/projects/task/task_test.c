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
 * @file     task_test.c
 * @brief    the main function for the task test
 * @version  V1.0
 * @date     02. June 2017
 ******************************************************************************/
#include<stdint.h>
#include<csi_kernel.h>
#include "test_kernel.h"

extern k_task_handle_t k_api_example_arr[];

#define EXAMPLE_K_TASK_STK_SIZE 4096
//#define EXAMPLE_K_TASK_STK_SIZE 1024

k_task_handle_t g_uwTskHi;
k_task_handle_t g_uwTskLo;
#define TSK_PRIOR_HI 11
#define TSK_PRIOR_LO 10

#define TEST_TIME_QUANTA 100

void Example_TaskHi()
{
    uint32_t uwRet;

    printf("Enter TaskHi Handler.\r\n");

    uwRet = csi_kernel_delay(100);

    if (uwRet != 0) {
        printf("Kernel delay return error.\r\n");
    }

    printf("TaskHi csi_kernel_delay Done.\r\n");

    uwRet = csi_kernel_task_suspend(g_uwTskHi);

    if (uwRet != 0) {
        printf("Suspend TaskHi return error.\r\n");
    }

    printf("TaskHi csi_kernel_task_resume returned.\r\n");

    printf("test kernel task successfully !\n");
    csi_kernel_task_del(g_uwTskHi);
    printf("example task delete self return error .\n");
}


void Example_TaskLo()
{
    uint32_t uwRet;

    printf("Enter TaskLo Handler.\r\n");
    uwRet = csi_kernel_delay(100);

    if (uwRet != 0) {
        printf("Kernel delay return error.\r\n");
    }

    printf("TaskHi csi_kernel_task_suspend returned.\r\n");

    uwRet = csi_kernel_task_resume(g_uwTskHi);

    if (uwRet != 0) {
        printf("Fail to resume TaskHi.\r\n");
    }

    csi_kernel_task_del(g_uwTskLo);
    printf("Fail to delete TaskLo itself. \n");
}

void example_main(void)
{
    csi_kernel_sched_suspend();

    printf("csi_kernel_suspend returned!\r\n");

    csi_kernel_task_new((k_task_entry_t)Example_TaskHi, "HIGH_NAME", NULL, TSK_PRIOR_HI, TEST_TIME_QUANTA, NULL, EXAMPLE_K_TASK_STK_SIZE, &g_uwTskHi);

    if (g_uwTskHi == NULL) {
        csi_kernel_sched_resume(0);

        printf("Fail to create Example_TaskHi !\r\n");
    }

    csi_kernel_task_new((k_task_entry_t)Example_TaskLo, "LOW_NAME", NULL, TSK_PRIOR_LO, TEST_TIME_QUANTA, NULL, EXAMPLE_K_TASK_STK_SIZE, &g_uwTskLo);

    if (g_uwTskLo == NULL) {
        csi_kernel_sched_resume(0);

        printf("Fail to create Example_TaskLo!\r\n");
    }

    csi_kernel_sched_resume(0);


    csi_kernel_task_del(csi_kernel_task_get_cur());
    printf("Fail to delete example task itself. \n");
}
