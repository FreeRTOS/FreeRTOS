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
 * @file     ck_irq.c
 * @brief    CSI Source File for IRQ Driver
 * @version  V1.0
 * @date     21. Dec 2018
 ******************************************************************************/

#include <stdint.h>
#include <soc.h>
#include <csi_core.h>
#include <csi_config.h>

extern void Default_Handler(void);
extern void (*g_irqvector[])(void);
extern void (*g_nmivector)(void);

/**
  \brief       enable irq.
  \param[in]   irq_num Number of IRQ.
  \return      None.
*/
void drv_irq_enable(uint32_t irq_num)
{
    if (NMI_EXPn != irq_num) {
    #ifdef CONFIG_SYSTEM_SECURE
        csi_vic_enable_sirq(irq_num);
    #else
        csi_vic_enable_irq(irq_num);
    #endif
    }
}

/**
  \brief       disable irq.
  \param[in]   irq_num Number of IRQ.
  \return      None.
*/
void drv_irq_disable(uint32_t irq_num)
{
    if (NMI_EXPn != irq_num) {
    #ifdef CONFIG_SYSTEM_SECURE
        csi_vic_disable_sirq(irq_num);
    #else
        csi_vic_disable_irq(irq_num);
    #endif
    }
}

/**
  \brief       register irq handler.
  \param[in]   irq_num Number of IRQ.
  \param[in]   irq_handler IRQ Handler.
  \return      None.
*/
void drv_irq_register(uint32_t irq_num, void *irq_handler)
{
    if (NMI_EXPn != irq_num) {
        g_irqvector[irq_num] = irq_handler;
    } else {
        g_nmivector = irq_handler;
    }
}

/**
  \brief       unregister irq handler.
  \param[in]   irq_num Number of IRQ.
  \return      None.
*/
void drv_irq_unregister(uint32_t irq_num)
{
    if (NMI_EXPn != irq_num) {
        g_irqvector[irq_num] = (void *)Default_Handler;
    } else {
        g_nmivector = (void *)Default_Handler;
    }
}
