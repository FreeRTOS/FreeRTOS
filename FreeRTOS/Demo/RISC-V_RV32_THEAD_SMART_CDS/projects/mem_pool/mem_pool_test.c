/*
 * Copyright (C) 2017-2019 Alibaba Group Holding Limited
 */


/******************************************************************************
 * @file     mem_pool_test.c
 * @brief    the main function for the mem_pool test
 * @version  V1.0
 * @date     02. June 2017
 ******************************************************************************/
#include "test_kernel.h"
#include <csi_kernel.h>
#include <stdint.h>

void example_main(void)
{
    int32_t *p_blk = NULL;
    int32_t uwBlkSize = 20, uwBlkCnt = 5;
    int32_t uwRet;
    int32_t pBoxMem[100];
    k_mpool_handle_t mp_handle = csi_kernel_mpool_new(&pBoxMem[0], uwBlkCnt, uwBlkSize);

    if (mp_handle == NULL) {
        printf("fail to create memory pool!\n");
        return;
    }

    p_blk = csi_kernel_mpool_alloc(mp_handle, 0);

    if (NULL == p_blk) {
        printf("failt to allocate block!\n");
        return;
    }

    int32_t *p_w = p_blk;
    *p_w = 444;

    printf("write block done.\n");

    uwRet = csi_kernel_mpool_free(mp_handle, p_blk);

    if (0 == uwRet) {
        printf("block free successfully!\n");
    } else {
        printf("fail to free block!\n");
    }

    csi_kernel_task_del(csi_kernel_task_get_cur());
}
