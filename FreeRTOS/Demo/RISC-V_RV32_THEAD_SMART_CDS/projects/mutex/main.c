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
 * @file     main.c
 * @brief    CSI Source File for main
 * @version  V1.0
 * @date     02. June 2017
 ******************************************************************************/

#include <stdint.h>
#include <csi_kernel.h>

#define K_API_PARENT_PRIO    5
#define APP_START_TASK_STK_SIZE 1024

extern void example_main(void);

k_task_handle_t example_main_task;

int main(void)
{
    csi_kernel_init();

    csi_kernel_task_new((k_task_entry_t)example_main, "example_main",
                        0, K_API_PARENT_PRIO, 0, 0, APP_START_TASK_STK_SIZE, &example_main_task);

    csi_kernel_start();

    return 0;
}
