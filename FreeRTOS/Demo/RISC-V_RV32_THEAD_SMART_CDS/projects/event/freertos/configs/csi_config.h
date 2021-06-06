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

#ifndef __CSI_CONFIG_H__
#define __CSI_CONFIG_H__
#define CONFIG_ARCH_RV32 1
#define CONFIG_CPU_E906FD 1
#define CONFIG_RV32_CORETIM 1
#define CONFIG_CHIP_SMARTL_RV32 1
#define CONFIG_BOARD_SMARTL_E906_EVB 1
#define CONFIG_BOARD_NAME_STR "smartl_e906_evb"
#define CONFIG_KERNEL_FREERTOS 1
#define CONFIG_SUPPORT_TSPEND 1
#define CONFIG_ARCH_INTERRUPTSTACK 4096
#define CONFIG_NEWLIB_WRAP 1
#define CONFIG_USER_DEFINED_LD_DIR_STR ""
#endif
