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
 * @file     test_kernel_config.h
 * @brief    head file for driver config
 * @version  V1.0
 * @date     02. June 2017
 ******************************************************************************/

#ifndef _KERNEL_CONFIG_H_
#define _KERNEL_CONFIG_H_
#ifdef __cplusplus
extern "C" {
#endif


#define TEST_EVENT
#define TEST_SEM
#define TEST_MUTEX
#define TEST_SOFTWARE_TIMER
#define TEST_MSGQ
#define TEST_TASK
#define TEST_MEMPOOL

#ifdef __cplusplus
}
#endif

#endif
