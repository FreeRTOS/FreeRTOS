/*
 * Copyright (C) 2017-2019 Alibaba Group Holding Limited
 */

/******************************************************************************
 * @file     board_init.c
 * @brief    CSI Source File for board init
 * @version  V1.0
 * @date     02. June 2017
 ******************************************************************************/
#include <stdio.h>
#include <stdint.h>
#include "drv_usart.h"
#include "soc.h"
#include <csi_config.h>
#include <csi_core.h>
#include "pin.h"

extern usart_handle_t console_handle;
extern void ioreuse_initial(void);

extern int clock_timer_init(void);
extern int clock_timer_start(void);

void board_init(void)
{
    int32_t ret = 0;
    /* init the console*/
    clock_timer_init();
    clock_timer_start();

    console_handle = csi_usart_initialize(CONSOLE_IDX, NULL);
    /* config the UART */
    ret = csi_usart_config(console_handle, 115200, USART_MODE_ASYNCHRONOUS, USART_PARITY_NONE, USART_STOP_BITS_1, USART_DATA_BITS_8);

    if (ret < 0) {
        return;
    }
}
