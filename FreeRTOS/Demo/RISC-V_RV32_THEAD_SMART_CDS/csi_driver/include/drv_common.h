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
 * @file     drv_common.h
 * @brief    Header File for Common Driver
 * @version  V1.0
 * @date     19. Feb 2019
 * @model    common
 ******************************************************************************/

#ifndef _DRV_COMMON_H_
#define _DRV_COMMON_H_

#include <stdint.h>
#include <drv_errno.h>

#ifdef __cplusplus
extern "C" {
#endif

/// \details driver handle
typedef void *drv_handle_t;

#ifndef CONFIG_PARAM_NOT_CHECK
#define HANDLE_PARAM_CHK(para, err)                                                                \
    do {                                                                                           \
        if ((int32_t)para == (int32_t)NULL) {                                                      \
            return (err);                                                                          \
        }                                                                                          \
    } while (0)

#define HANDLE_PARAM_CHK_NORETVAL(para, err)                                                          \
    do {                                                                                           \
        if ((int32_t)para == (int32_t)NULL) {                                                      \
            return;                                                                                \
        }                                                                                          \
    } while (0)
#else
#define HANDLE_PARAM_CHK(para, err)
#define HANDLE_PARAM_CHK_NORETVAL(para, err)
#endif

/**
\brief General power states
*/
typedef enum  {
    DRV_POWER_OFF,                        ///< Power off: no operation possible
    DRV_POWER_LOW,                        ///< Low Power mode: retain state, detect and signal wake-up events
    DRV_POWER_FULL,                       ///< Power on: full operation at maximum performance
    DRV_POWER_SUSPEND,                    ///< Power suspend: power saving operation
} csi_power_stat_e;

#ifdef __cplusplus
}
#endif

#endif /* _DRV_COMMON_H */

