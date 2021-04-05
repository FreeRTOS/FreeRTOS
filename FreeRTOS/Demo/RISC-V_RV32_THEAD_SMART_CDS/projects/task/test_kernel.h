/*
 * Copyright (C) 2017-2019 Alibaba Group Holding Limited
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
