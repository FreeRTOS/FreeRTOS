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
 * @file     message_q_test.c
 * @brief    the main function for the message_q test
 * @version  V1.0
 * @date     02. June 2017
 ******************************************************************************/
#include "test_kernel.h"
#include <csi_kernel.h>
#include <stdint.h>
#include <stdlib.h>

#define EXAMPLE_K_MSQ_STK_SIZE 1024

extern k_task_handle_t k_api_example_arr[];

static k_msgq_handle_t g_uwQueue;
static k_task_handle_t uwTask1;
static k_task_handle_t uwTask2;
static char abuf0[] = "test is message 0";
static char abuf1[] = "test is message 1";
static char abuf2[] = "test is message 2";
static char abuf3[] = "test is message 3";
static char abuf4[] = "test is message 4";
static char error_buf[] = "this is an error";
#define MSG_NUM    5

static void send_Entry(void *arg)
{
    uint32_t i = 0;
    int  uwRet = 0;

    printf("send_Entry\n");

    char *buf_p[MSG_NUM + 1] = {abuf0, abuf1, abuf2, abuf3, abuf4, error_buf};

    while (i < 5) {
        uwRet = csi_kernel_msgq_put(g_uwQueue, buf_p[i], 0, 0);
        i ++;

        if (uwRet != 0) {
            printf("fail to send message,error:%x\n", uwRet);
        }

        uint32_t count = csi_kernel_msgq_get_count(g_uwQueue);
        printf("send_Entry:number of queued mesages : %u\n", count);
        csi_kernel_delay(5);
    }

    csi_kernel_task_del(uwTask1);
}

static void recv_Entry(void *arg)
{
    int   uwRet = 0;
    void *Readbuf = malloc(64);

    printf("recv_Entry\n");

    while (1) {
        csi_kernel_delay(50);
        uwRet = csi_kernel_msgq_get(g_uwQueue, Readbuf, 0);

        if (uwRet != 0) {
            printf("in expected, fail to recv message,error:%x\n", uwRet);
            break;
        }

        printf("recv message:%s\n", (char *)Readbuf);
        uint32_t count = csi_kernel_msgq_get_count(g_uwQueue);
        printf("recv_Entry:number of queued mesages : %u\n", count);

        csi_kernel_delay(5);
    }

    while (0 != csi_kernel_msgq_del(g_uwQueue)) {
        csi_kernel_delay(1);
    }

    free(Readbuf);

    printf("delete the queue successfully!\n");

    csi_kernel_task_del(uwTask2);
}

void example_main(void)
{
    csi_kernel_sched_suspend();

    csi_kernel_task_new((k_task_entry_t)send_Entry, "sendQueue", NULL, 9, TASK_TIME_QUANTA,  NULL, TEST_TASK_STACK_SIZE, &uwTask1);

    if (uwTask1 == NULL) {
        printf("fail to create task1!\n");
    }

    csi_kernel_task_new((k_task_entry_t)recv_Entry, "receiveQueue", NULL, 9, TASK_TIME_QUANTA,  NULL, TEST_TASK_STACK_SIZE, &uwTask2);

    if (uwTask2 == NULL) {
        printf("fail to create task2!\n");
    }

    g_uwQueue = csi_kernel_msgq_new(5, 50);

    if (g_uwQueue == NULL) {
        printf("fail to create queue!\n");
    }

    csi_kernel_sched_resume(0);

    csi_kernel_task_del(csi_kernel_task_get_cur());
}
