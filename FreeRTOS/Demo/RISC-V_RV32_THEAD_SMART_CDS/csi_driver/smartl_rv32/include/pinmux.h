/*
 * Copyright (C) 2017-2019 Alibaba Group Holding Limited
 */


/******************************************************************************
 * @file     pinmux.h
 * @brief    Header file for the pinmux
 * @version  V1.0
 * @date     02. June 2017
 ******************************************************************************/

#ifndef _PINMUX_H_
#define _PINMUX_H_

#include <stdint.h>
#include "pin_name.h"

#ifdef __cplusplus
extern "C" {
#endif

int32_t drv_pinmux_config(pin_name_e pin, pin_func_e pin_func);


#ifdef __cplusplus
}
#endif

#endif /* _PINMUX_H_ */

