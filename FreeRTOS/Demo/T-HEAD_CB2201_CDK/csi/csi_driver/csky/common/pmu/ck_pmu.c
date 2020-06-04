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
 * @file     ck_pmu.c
 * @brief    CSI Source File for Embedded Flash Driver
 * @version  V1.0
 * @date     02. June 2017
 ******************************************************************************/

#include <stdio.h>
#include <string.h>
#include "drv_pmu.h"
#include "drv_tee.h"
#include "drv_eflash.h"
#include "ck_pmu.h"

#define ERR_PMU(errno) (CSI_DRV_ERRNO_PMU_BASE | errno)
#define PMU_NULL_PARAM_CHK(para)                         \
    do {                                        \
        if (para == NULL) {                     \
            return ERR_PMU(EDRV_PARAMETER);   \
        }                                       \
    } while (0)

typedef struct {
    uint8_t idx;
    uint32_t base;
    uint32_t irq;
    pmu_event_cb_t cb;
    pmu_action_cb_t callback[32];
} ck_pmu_priv_t;

extern int32_t target_get_pmu(int32_t idx, uint32_t *base, uint32_t *irq);
extern int32_t arch_do_cpu_save(void);
extern int32_t arch_do_cpu_resume(void);
extern int32_t arch_resume_context(void);

static ck_pmu_priv_t pmu_handle[CONFIG_PMU_NUM];
static uint32_t s_callback_count = 0;
#define CONFIG_PMU_REGISTER_NUM_SAVE  19
static uint32_t pmu_regs_saved[CONFIG_PMU_REGISTER_NUM_SAVE];

#define CONFIG_CPU_REGISTER_NUM_SAVE    27
uint32_t arch_cpu_saved[CONFIG_CPU_REGISTER_NUM_SAVE];
/* Driver Capabilities */
#if 0
static const pmu_capabilities_t driver_capabilities = {
    .event_ready = 1, /* event_ready */
    .data_width = 2, /* data_width = 0:8-bit, 1:16-bit, 2:32-bit */
    .erase_chip = 0  /* erase_chip */
};
#endif
//
// Functions
//

static void do_prepare_sleep_action(int32_t idx)
{
    uint8_t i;
    volatile ck_pmu_reg_t *pbase = (ck_pmu_reg_t *)pmu_handle[idx].base;
    for (i = 0; i < sizeof(pmu_regs_saved)/4; i++) {
        pmu_regs_saved[i] = *((volatile uint32_t *)pbase + i);
    }
}

static void do_wakeup_sleep_action(int32_t idx)
{
    uint8_t i;
    volatile ck_pmu_reg_t *pbase = (ck_pmu_reg_t *)pmu_handle[idx].base;
    *((volatile uint32_t *)pbase + 5) = pmu_regs_saved[5];
    while((*((volatile uint32_t *)pbase + 6) & 0xf) != 0xf);
    *((volatile uint32_t *)pbase + 11) = pmu_regs_saved[11];
    while((*((volatile uint32_t *)pbase + 6) & 0x1f) != 0x1f);
    for (i = 0; i < sizeof(pmu_regs_saved)/4; i++) {
        if (i != 5 && i != 11) {
            *((volatile uint32_t *)pbase + i) = pmu_regs_saved[i];
        }
    }

}

static uint8_t s_action[CONFIG_PMU_NUM] = {0x0};
int32_t ck_pmu_power_manager(int32_t idx)
{
    if (!(s_action[idx] % 2)) {
        do_prepare_sleep_action(idx);
        s_action[idx]++;
    } else {
        do_wakeup_sleep_action(idx);
        s_action[idx]--;
    }
    return 0;
}

int32_t ck_pmu_act_callback(pmu_handle_t handle, pmu_event_e event)
{
    ck_pmu_priv_t *pmu_priv = handle;
    uint32_t i;
    for (i = 0; i < s_callback_count; i++) {
        if (pmu_priv->callback[i]) {
            pmu_priv->callback[i](event);
        }
    }

    if (i != s_callback_count) {
        return -1;
    }
    return 0;
}

void resume_context_from_stop_mode(void)
{
    ck_pmu_priv_t *pmu_priv = &pmu_handle[0];
//    ck_pmu_power_manager(PMU_EVENT_SLEEP_DONE);
//    ck_pmu_act_callback(pmu_priv, PMU_EVENT_SLEEP_DONE);
    *((volatile uint32_t *)0x50006100) |= 0xa0000000;
    if (pmu_priv->cb) {
        pmu_priv->cb(pmu_priv->idx, PMU_EVENT_SLEEP_DONE, PMU_MODE_STDBY);
    }

    arch_do_cpu_resume();
}

#define CONFIG_LPM_RESUME_ADDR  0x1003f7f0
void set_resume_func(uint32_t *func)
{
    eflash_handle_t eflash = csi_eflash_initialize(0, NULL);
    csi_eflash_erase_sector(eflash, CONFIG_LPM_RESUME_ADDR);
    csi_eflash_program(eflash, CONFIG_LPM_RESUME_ADDR, &func, 4);
}

typedef enum {
    WAIT_MODE = 0,
    DOZE_MODE,
    STOP_MODE,
    STANDBY_MODE,
    SLEEP_MODE
} lpm_mode_t;


void soc_sleep(pmu_handle_t handle, lpm_mode_t mode)
{
#ifdef CONFIG_TEE_CA
    tee_lpm_mode_e lpm_mode = 0;

    if (mode == WAIT_MODE) {
        lpm_mode = TEE_LPM_MODE_WAIT;
    } else if (mode == DOZE_MODE) {
        lpm_mode = TEE_LPM_MODE_DOZE;
    } else if (mode == STOP_MODE) {
        lpm_mode = TEE_LPM_MODE_STOP;
    } else if (mode == STANDBY_MODE) {
        lpm_mode = TEE_LPM_MODE_STANDBY;
    } else {
        lpm_mode = TEE_LPM_MODE_WAIT;
    }

    csi_tee_enter_lpm(0, 0, lpm_mode);

    if (mode == STOP_MODE) {
        resume_context_from_stop_mode();
    }
#else

    ck_pmu_priv_t *pmu_priv = handle;
    ck_pmu_reg_t *pmu_reg = (ck_pmu_reg_t *)pmu_priv->base;

    if (mode == WAIT_MODE) {
        pmu_reg->LPCR |= CONFIG_PMU_ENTER_WAIT_MODE;
        __WFI();
    } else if (mode == DOZE_MODE) {
        pmu_reg->LPCR |= CONFIG_PMU_ENTER_DOZE_MODE;
        __DOZE();
    } else if (mode == STOP_MODE) {
        pmu_reg->LPCR |= CONFIG_PMU_ENTER_STOP_MODE;
        __STOP();
    } else if (mode == STANDBY_MODE) {
        pmu_reg->LPCR |= CONFIG_PMU_ENTER_STANDBY_MODE;
        __STOP();
    } else {
        pmu_reg->LPCR |= CONFIG_PMU_ENTER_WAIT_MODE;
        __WFI();
    }

#endif
}

/**
  \brief       Initialize PMU Interface. 1. Initializes the resources needed for the PMU interface 2.registers event callback function
  \param[in]   idx device id
  \param[in]   cb_event  Pointer to \ref pmu_event_cb_t
  \return      pointer to pmu handle
*/
pmu_handle_t drv_pmu_initialize(int32_t idx, pmu_event_cb_t cb_event)
{
    if (idx < 0 || idx >= CONFIG_PMU_NUM) {
        return NULL;
    }

    /* obtain the pmu information */
    uint32_t base = 0u;
    uint32_t irq = 0u;
    int32_t real_idx = target_get_pmu(idx, &base, &irq);

    if (real_idx != idx) {
        return NULL;
    }

    ck_pmu_priv_t *pmu_priv = &pmu_handle[idx];

    /* initialize the pmu context */
    pmu_priv->idx = idx;
    pmu_priv->base = base;
    pmu_priv->irq = irq;
    pmu_priv->cb = cb_event;

    return (pmu_handle_t)pmu_priv;
}

/**
  \brief       De-initialize PMU Interface. stops operation and releases the software resources used by the interface
  \param[in]   handle  pmu handle to operate.
  \return      error code
*/
int32_t drv_pmu_uninitialize(pmu_handle_t handle)
{
    PMU_NULL_PARAM_CHK(handle);

    ck_pmu_priv_t *pmu_priv = handle;
    pmu_priv->cb = NULL;

    return 0;
}

int32_t drv_pmu_power_control(int32_t idx, csi_power_stat_e state)
{
    switch (state) {
    case DRV_POWER_LOW:
        break;
    case DRV_POWER_FULL:
        break;
    case DRV_POWER_OFF:
        ck_pmu_power_manager(idx);
//        csi_pmu_register_module(dw_usart_power_manager);
        break;
    default:
        break;
    }

    return 0;
}

/**
  \brief       Get driver capabilities.
  \param[in]   idx device id
  \return      \ref pmu_capabilities_t
*/
#if 0
pmu_capabilities_t csi_pmu_get_capabilities(int32_t idx)
{
    if (idx < 0 || idx >= CONFIG_PMU_NUM) {
        pmu_capabilities_t ret;
        memset(&ret, 0, sizeof(pmu_capabilities_t));
        return ret;
    }

    return driver_capabilities;
}
#endif
/**
  \brief       choose the pmu mode to enter
  \param[in]   handle  pmu handle to operate.
  \param[in]   mode    \ref pmu_mode_e
  \return      error code
*/
int32_t drv_pmu_enter_sleep(pmu_handle_t handle, pmu_mode_e mode)
{
    PMU_NULL_PARAM_CHK(handle);

    switch (mode) {
    case PMU_MODE_RUN:
        break;
    case PMU_MODE_SLEEP:
        soc_sleep(handle, WAIT_MODE);
        break;
    case PMU_MODE_DORMANT:
//        soc_sleep(handle, DOZE_MODE);
        if (arch_do_cpu_save() == 0) {
            *(volatile unsigned int *)(0xe000e1c0) = 0xffffffff; // reload wakeup_IRQ
            *(volatile unsigned int *)(0xe000e280) = 0xffffffff; // clear pend IRQ
            soc_sleep(handle, STOP_MODE);
        }
        break;
    case PMU_MODE_STDBY:
        *(volatile unsigned int *)(0xe000e1c0) = 0xffffffff; // reload wakeup_IRQ
        *(volatile unsigned int *)(0xe000e280) = 0xffffffff; // clear pend IRQ
        soc_sleep(handle, STANDBY_MODE);
        break;
    case PMU_MODE_SHUTDOWN:
        *(volatile unsigned int *)(0xe000e1c0) = 0xffffffff; // reload wakeup_IRQ
        *(volatile unsigned int *)(0xe000e280) = 0xffffffff; // clear pend IRQ
        soc_sleep(handle, STANDBY_MODE);
        break;
    default:
        return ERR_PMU(EDRV_PARAMETER);
    }

    return 0;
}

/**
  \brief       register module to action pmu event
  \param[in]   handle  pmu handle to operate.
  \param[in]   callback Pointer to \ref pmu_action_cb_t
  \return      error code
*/
int32_t drv_pmu_register_module(pmu_action_cb_t callback)
{
    ck_pmu_priv_t *pmu_priv = (ck_pmu_priv_t *)&pmu_handle[0];

    if (callback == NULL) {
        return ERR_PMU(EDRV_PARAMETER);
    }
    pmu_priv->callback[s_callback_count] = callback;
    s_callback_count++;
    return 0;
}

/**
  \brief       Config the wakeup source.
  \param[in]   handle  pmu handle to operate
  \param[in]   type    \ref pmu_wakeup_type
  \param[in]   pol     \ref pmu_wakeup_pol
  \param[in]   enable  flag control the wakeup source is enable or not
  \return      error code
*/
int32_t drv_pmu_config_wakeup_source(pmu_handle_t handle, uint32_t irq_num, pmu_wakeup_type_e type, pmu_wakeup_pol_e pol, uint8_t enable)
{
    PMU_NULL_PARAM_CHK(handle);

    if (enable) {
//        csi_vic_enable_irq(irq_num);
//        csi_vic_enable_sirq(irq_num);
//        csi_vic_set_wakeup_irq(irq_num);
        drv_nvic_set_wakeup_irq(irq_num);
    } else {
//        csi_vic_disable_irq(irq_num);
//        csi_vic_disable_sirq(irq_num);
        drv_nvic_clear_wakeup_irq(irq_num);
//        csi_vic_clear_wakeup_irq(irq_num);
    }
    return 0;
}
