/*
 * Copyright (C) 2017-2019 Alibaba Group Holding Limited
 */


/******************************************************************************
 * @file     time_test.c
 * @brief    the main function for the time test
 * @version  V1.0
 * @date     02. June 2017
 ******************************************************************************/
#include "test_kernel.h"
#include <csi_kernel.h>
#include <stdint.h>

extern k_task_handle_t k_api_example_arr[];

void example_k_TransformTime(void)
{
    uint64_t uwMs;
    uint64_t uwTick;
    uwTick = csi_kernel_ms2tick(10000);
    printf("10000 ms to Tick = %llu \n", uwTick);
    uwMs = csi_kernel_tick2ms(100);
    printf("100 tick to ms = %llu \n", uwMs);

    csi_kernel_task_del(csi_kernel_task_get_cur());
}

void example_main(void)
{
    uint64_t uwTickCount = 0;
    uint32_t cnt;

    cnt = 10;
    printf("print cnt every 1s for %u times\n", cnt);

    while (cnt--) {
        uwTickCount += 100;
        csi_kernel_delay(100);
        printf("-----%u\n", cnt);
    }

    cnt = 3;
    printf("print cnt every 3s for %u times\n", cnt);

    while (cnt--) {
        uwTickCount += 300;
        csi_kernel_delay(300);
        printf("-----%u\n", cnt);
    }

    csi_kernel_delay(200);
    uwTickCount = csi_kernel_get_ticks();

    if (0 != uwTickCount) {
        printf("csi_kernel_get_ticks = %u \n", (uint32_t)uwTickCount);
    }

    csi_kernel_delay(200);
    uwTickCount = csi_kernel_get_ticks();

    if (0 != uwTickCount) {
        printf("csi_kernel_get_ticks after delay = %u \n", (uint32_t)uwTickCount);
    }

    printf("test kernel time successfully!\n");
    csi_kernel_task_del(csi_kernel_task_get_cur());
}
