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

#ifndef _CORETIM_H_
#define _CORETIM_H_
#include <stdint.h>

#define CORETIM_BASE     (0xE000E000)

#define CORET_CSR         (volatile uint32_t *)(CORETIM_BASE + 0x10)
#define CORET_RVR         (volatile uint32_t *)(CORETIM_BASE + 0x14)
#define CORET_CVR         (volatile uint32_t *)(CORETIM_BASE + 0x18)
#define CORET_CALIB       (volatile uint32_t *)(CORETIM_BASE + 0x1c)

/*
 *  define the bits for TxControl
 */
#define CORETIM_TXCONTROL_ENABLE      (1UL << 0)
#define CORETIM_TXCONTROL_INTMASK     (1UL << 1)
#define CORETIM_TXCONTROL_MODE        (1UL << 16)

/*****************************************************************************/
/* Function Prototypes */
void coretim_init (uint32_t hz);
void coretim_clr_irq (void);
uint32_t coretim_get_currval(void);

#endif /* _CORETIM_H_ */
