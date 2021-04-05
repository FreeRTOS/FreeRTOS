/*
 * Copyright (C) 2017-2019 Alibaba Group Holding Limited
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
