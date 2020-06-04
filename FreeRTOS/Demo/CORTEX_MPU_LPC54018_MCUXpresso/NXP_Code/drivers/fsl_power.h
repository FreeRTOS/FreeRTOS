/*
 * Copyright (c) 2016, Freescale Semiconductor, Inc.
 * Copyright 2016, NXP
 * All rights reserved.
 *
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */
#ifndef _FSL_POWER_H_
#define _FSL_POWER_H_

#include "fsl_common.h"

/*! @addtogroup power */
/*! @{ */

/*! @file */

/*******************************************************************************
 * Definitions
 ******************************************************************************/

/*! @name Driver version */
/*@{*/
/*! @brief power driver version 2.0.0. */
#define FSL_POWER_DRIVER_VERSION (MAKE_VERSION(2, 0, 0))
/*@}*/

#define MAKE_PD_BITS(reg, slot) (((reg) << 8) | (slot))
#define PDRCFG0 0x0U
#define PDRCFG1 0x1U

typedef enum pd_bits
{
    kPDRUNCFG_LP_REG = MAKE_PD_BITS(PDRCFG0, 2U),
    kPDRUNCFG_PD_FRO_EN = MAKE_PD_BITS(PDRCFG0, 4U),
    kPDRUNCFG_PD_TS = MAKE_PD_BITS(PDRCFG0, 6U),
    kPDRUNCFG_PD_BOD_RESET = MAKE_PD_BITS(PDRCFG0, 7U),
    kPDRUNCFG_PD_BOD_INTR = MAKE_PD_BITS(PDRCFG0, 8U),
    kPDRUNCFG_PD_VD2_ANA = MAKE_PD_BITS(PDRCFG0, 9U),
    kPDRUNCFG_PD_ADC0 = MAKE_PD_BITS(PDRCFG0, 10U),
    kPDRUNCFG_PD_RAM0 = MAKE_PD_BITS(PDRCFG0, 13U),
    kPDRUNCFG_PD_RAM1 = MAKE_PD_BITS(PDRCFG0, 14U),
    kPDRUNCFG_PD_RAM2 = MAKE_PD_BITS(PDRCFG0, 15U),
    kPDRUNCFG_PD_RAM3 = MAKE_PD_BITS(PDRCFG0, 16U),
    kPDRUNCFG_PD_ROM = MAKE_PD_BITS(PDRCFG0, 17U),
    kPDRUNCFG_PD_VDDA = MAKE_PD_BITS(PDRCFG0, 19U),
    kPDRUNCFG_PD_WDT_OSC = MAKE_PD_BITS(PDRCFG0, 20U),
    kPDRUNCFG_PD_USB0_PHY = MAKE_PD_BITS(PDRCFG0, 21U),
    kPDRUNCFG_PD_SYS_PLL0 = MAKE_PD_BITS(PDRCFG0, 22U),
    kPDRUNCFG_PD_VREFP = MAKE_PD_BITS(PDRCFG0, 23U),
    kPDRUNCFG_PD_FLASH_BG = MAKE_PD_BITS(PDRCFG0, 25U),
    kPDRUNCFG_PD_VD3 = MAKE_PD_BITS(PDRCFG0, 26U),
    kPDRUNCFG_PD_VD4 = MAKE_PD_BITS(PDRCFG0, 27U),
    kPDRUNCFG_PD_VD5 = MAKE_PD_BITS(PDRCFG0, 28U),
    kPDRUNCFG_PD_VD6 = MAKE_PD_BITS(PDRCFG0, 29U),
    kPDRUNCFG_REQ_DELAY = MAKE_PD_BITS(PDRCFG0, 30U),
    kPDRUNCFG_FORCE_RBB = MAKE_PD_BITS(PDRCFG0, 31U),

    kPDRUNCFG_PD_USB1_PHY = MAKE_PD_BITS(PDRCFG1, 0U),
    kPDRUNCFG_PD_USB_PLL = MAKE_PD_BITS(PDRCFG1, 1U),
    kPDRUNCFG_PD_AUDIO_PLL = MAKE_PD_BITS(PDRCFG1, 2U),
    kPDRUNCFG_PD_SYS_OSC = MAKE_PD_BITS(PDRCFG1, 3U),
    kPDRUNCFG_PD_EEPROM = MAKE_PD_BITS(PDRCFG1, 5U),
    kPDRUNCFG_PD_rng = MAKE_PD_BITS(PDRCFG1, 6U),

    /*
    This enum member has no practical meaning,it is used to avoid MISRA issue,
    user should not trying to use it.
    */
    kPDRUNCFG_ForceUnsigned = (int)0x80000000U,
} pd_bit_t;

/* Power mode configuration API parameter */
typedef enum _power_mode_config
{
    kPmu_Sleep = 0U,
    kPmu_Deep_Sleep = 1U,
    kPmu_Deep_PowerDown = 2U,
} power_mode_cfg_t;

/*******************************************************************************
 * API
 ******************************************************************************/

#ifdef __cplusplus
extern "C" {
#endif

/*!
* @name Power Configuration
* @{
*/

/*!
 * @brief API to enable PDRUNCFG bit in the Syscon. Note that enabling the bit powers down the peripheral
 *
 * @param en    peripheral for which to enable the PDRUNCFG bit
 * @return none
 */
static inline void POWER_EnablePD(pd_bit_t en)
{
    /* PDRUNCFGSET */
    SYSCON->PDRUNCFGSET[((uint32_t)en >> 8UL)] = (1UL << ((uint32_t)en & 0xffU));
}

/*!
 * @brief API to disable PDRUNCFG bit in the Syscon. Note that disabling the bit powers up the peripheral
 *
 * @param en    peripheral for which to disable the PDRUNCFG bit
 * @return none
 */
static inline void POWER_DisablePD(pd_bit_t en)
{
    /* PDRUNCFGCLR */
    SYSCON->PDRUNCFGCLR[((uint32_t)en >> 8UL)] = (1UL << ((uint32_t)en & 0xffU));
}

/*!
 * @brief API to enable deep sleep bit in the ARM Core.
 *
 * @param none
 * @return none
 */
static inline void POWER_EnableDeepSleep(void)
{
    SCB->SCR |= SCB_SCR_SLEEPDEEP_Msk;
}

/*!
 * @brief API to disable deep sleep bit in the ARM Core.
 *
 * @param none
 * @return none
 */
static inline void POWER_DisableDeepSleep(void)
{
    SCB->SCR |= SCB_SCR_SLEEPDEEP_Msk;
}

/*!
 * @brief Power Library API to reload OTP.
 *        This API must be called if VD6 is power down
 *        and power back again since FROHF TRIM value
 *        is store in OTP. If not, when calling FROHF settng
 *        API in clock driver then the FROHF clock out put
 *        will be inaccurate.
 * @return none
 */
void POWER_OtpReload(void);

/*!
 * @brief Power Library API to power the PLLs.
 *
 * @param none
 * @return none
 */
void POWER_SetPLL(void);

/*!
 * @brief Power Library API to power the USB PHY.
 *
 * @param none
 * @return none
 */
void POWER_SetUsbPhy(void);

/*!
 * @brief Power Library API to enter different power mode.
 *
 * @param exclude_from_pd  Bit mask of the PDRUNCFG0(low 32bits) and PDRUNCFG1(high 32bits) that needs to be powered on
 * during power mode selected.
 * @return none
 */
void POWER_EnterPowerMode(power_mode_cfg_t mode, uint64_t exclude_from_pd);

/*!
 * @brief Power Library API to enter sleep mode.
 *
 * @return none
 */
void POWER_EnterSleep(void);

/*!
 * @brief Power Library API to enter deep sleep mode.
 *
 * @param exclude_from_pd  Bit mask of the PDRUNCFG0(low 32bits) and PDRUNCFG1(high 32bits) bits that needs to be
 * powered on during deep sleep
 * @return none
 */
void POWER_EnterDeepSleep(uint64_t exclude_from_pd);

/*!
 * @brief Power Library API to enter deep power down mode.
 *
 * @param exclude_from_pd   Bit mask of the PDRUNCFG0(low 32bits) and PDRUNCFG1(high 32bits) that needs to be powered on
 during deep power
 *                          down mode, but this is has no effect as the voltages are cut off.

 * @return none
 */
void POWER_EnterDeepPowerDown(uint64_t exclude_from_pd);

/*!
 * @brief Power Library API to choose normal regulation and set the voltage for the desired operating frequency.
 *
 * @param freq  - The desired frequency at which the part would like to operate,
 *                note that the voltage and flash wait states should be set before changing frequency
 * @return none
 */
void POWER_SetVoltageForFreq(uint32_t freq);

/*!
 * @brief Power Library API to return the library version.
 *
 * @param none
 * @return version number of the power library
 */
uint32_t POWER_GetLibVersion(void);

#ifdef __cplusplus
}
#endif

#endif /* _FSL_POWER_H_ */
