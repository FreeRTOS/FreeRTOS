/*
 * Copyright (C) 2017 C-SKY Microsystems Co., Ltd. All rights reserved.
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
 * @file     ck_sys_freq.h
 * @brief    header file for setting system frequency.
 * @version  V1.0
 * @date     18. July 2017
 ******************************************************************************/
#ifndef _CK_SYS_FREQ_H_
#define _CK_SYS_FREQ_H_

#include <stdint.h>
#include "soc.h"

#define PMU_MCLK_SEL  (CSKY_CLKGEN_BASE + 0x4)
#define MCLK_REG_VAL  0x8UL

#define PMU_CLK_STABLE  (CSKY_CLKGEN_BASE + 0x18)
#define PMU_PLL_CTRL  (CSKY_CLKGEN_BASE + 0x2c)

#define TRC_ADDR (CSKY_OTP_BASE + 0x20)
#define TRC_REG_VAL  0x1UL

#define EXTERNAL_CLK_SOURCE  0x8UL
#define EXTERNAL_CLK_16M     (EXTERNAL_CLK_SOURCE * 2)
#define EXTERNAL_CLK_24M     (EXTERNAL_CLK_SOURCE * 3)
#define EXTERNAL_CLK_32M     (EXTERNAL_CLK_SOURCE * 4)
#define EXTERNAL_CLK_40M     (EXTERNAL_CLK_SOURCE * 5)
#define EXTERNAL_CLK_48M     (EXTERNAL_CLK_SOURCE * 6)

#define CLK_8M_REG_VAL        0xc0202UL
#define CLK_16M_REG_VAL       0xc0204UL
#define CLK_24M_REG_VAL       0xc0206UL
#define CLK_32M_REG_VAL       0xc0208UL
#define CLK_40M_REG_VAL       0xc020aUL
#define CLK_48M_REG_VAL       0xc020cUL

typedef enum {
    IHS_CLK       = 0,          //internal high speed clock
    EHS_CLK       = 1          //external high speed clock
} clk_gen_t;

typedef enum {
    CLK_8M       = 0,
    CLK_16M      = 1,
    CLK_24M      = 2,
    CLK_32M      = 3,
    CLK_40M      = 4,
    CLK_48M      = 5
} clk_val_t;

void ck_set_sys_freq (clk_gen_t source, clk_val_t val);

#endif /* _CK_SYS_FREQ_H_ */

