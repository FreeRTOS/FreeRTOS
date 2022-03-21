/*******************************************************************************
 * Copyright 2019-2021 Microchip FPGA Embedded Systems Solutions.
 *
 * SPDX-License-Identifier: MIT
 *
 * MPFS HAL Embedded Software
 *
 */
/*******************************************************************************
 * @file mss_peripherals.c
 * @author Microchip-FPGA Embedded Systems Solutions
 * @brief PolarFire SoC MSS functions related to peripherals.
 *
 */
/*=========================================================================*//**

 *//*=========================================================================*/
#include <stdio.h>
#include <string.h>
#include "mpfs_hal/mss_hal.h"

const uint32_t LIBERO_SETTING_CONTEXT_EN[][2U] = {
                {LIBERO_SETTING_CONTEXT_A_EN,
                 LIBERO_SETTING_CONTEXT_B_EN},
                {LIBERO_SETTING_CONTEXT_A_EN_FIC,
                 LIBERO_SETTING_CONTEXT_B_EN_FIC},
};

/* offsets used in PERIPHERAL_SETUP array */
#define PERIPHERAL_INDEX_OFFSET         0U /* used for sanity check */
#define CONTEXT_EN_INDEX_OFFSET         1U
#define CONTEXT_MASK_INDEX_OFFSET       2U
#define CONTEXT_SUBCLK_INDEX_OFFSET     3U

const uint32_t PERIPHERAL_SETUP[][4U] = {
        {MSS_PERIPH_MMUART0,CONTEXT_EN_INDEX, CONTEXT_EN_MASK_MMUART0,SUBBLK_CLOCK_CR_MMUART0_MASK},
        {MSS_PERIPH_MMUART1,CONTEXT_EN_INDEX, CONTEXT_EN_MASK_MMUART1,SUBBLK_CLOCK_CR_MMUART1_MASK},
        {MSS_PERIPH_MMUART2,CONTEXT_EN_INDEX, CONTEXT_EN_MASK_MMUART2,SUBBLK_CLOCK_CR_MMUART2_MASK},
        {MSS_PERIPH_MMUART3,CONTEXT_EN_INDEX, CONTEXT_EN_MASK_MMUART3,SUBBLK_CLOCK_CR_MMUART3_MASK},
        {MSS_PERIPH_MMUART4,CONTEXT_EN_INDEX, CONTEXT_EN_MASK_MMUART4,SUBBLK_CLOCK_CR_MMUART4_MASK},
        {MSS_PERIPH_WDOG0,CONTEXT_EN_INDEX, CONTEXT_EN_MASK_WDOG0,SUBBLK_CLOCK_NA_MASK},
        {MSS_PERIPH_WDOG1,CONTEXT_EN_INDEX, CONTEXT_EN_MASK_WDOG1,SUBBLK_CLOCK_NA_MASK},
        {MSS_PERIPH_WDOG2,CONTEXT_EN_INDEX, CONTEXT_EN_MASK_WDOG2,SUBBLK_CLOCK_NA_MASK},
        {MSS_PERIPH_WDOG3,CONTEXT_EN_INDEX, CONTEXT_EN_MASK_WDOG3,SUBBLK_CLOCK_NA_MASK},
        {MSS_PERIPH_WDOG4,CONTEXT_EN_INDEX, CONTEXT_EN_MASK_WDOG4,SUBBLK_CLOCK_NA_MASK},
        {MSS_PERIPH_SPI0,CONTEXT_EN_INDEX, CONTEXT_EN_MASK_SPI0,SUBBLK_CLOCK_CR_SPI0_MASK},
        {MSS_PERIPH_SPI1,CONTEXT_EN_INDEX, CONTEXT_EN_MASK_SPI1,SUBBLK_CLOCK_CR_SPI1_MASK},
        {MSS_PERIPH_I2C0,CONTEXT_EN_INDEX, CONTEXT_EN_MASK_I2C0,SUBBLK_CLOCK_CR_I2C0_MASK},
        {MSS_PERIPH_I2C1,CONTEXT_EN_INDEX, CONTEXT_EN_MASK_I2C1,SUBBLK_CLOCK_CR_I2C1_MASK},
        {MSS_PERIPH_CAN0,CONTEXT_EN_INDEX, CONTEXT_EN_MASK_CAN0,SUBBLK_CLOCK_CR_CAN0_MASK},
        {MSS_PERIPH_CAN1,CONTEXT_EN_INDEX, CONTEXT_EN_MASK_CAN1,SUBBLK_CLOCK_CR_CAN1_MASK},
        {MSS_PERIPH_MAC0,CONTEXT_EN_INDEX, CONTEXT_EN_MASK_MAC0,SUBBLK_CLOCK_CR_MAC0_MASK},
        {MSS_PERIPH_MAC1,CONTEXT_EN_INDEX, CONTEXT_EN_MASK_MAC1,SUBBLK_CLOCK_CR_MAC1_MASK},
        {MSS_PERIPH_TIMER,CONTEXT_EN_INDEX, CONTEXT_EN_MASK_TIMER,SUBBLK_CLOCK_CR_TIMER_MASK},
        {MSS_PERIPH_GPIO0,CONTEXT_EN_INDEX, CONTEXT_EN_MASK_GPIO0,SUBBLK_CLOCK_CR_GPIO0_MASK},
        {MSS_PERIPH_GPIO1,CONTEXT_EN_INDEX, CONTEXT_EN_MASK_GPIO1,SUBBLK_CLOCK_CR_GPIO1_MASK},
        {MSS_PERIPH_GPIO2,CONTEXT_EN_INDEX, CONTEXT_EN_MASK_GPIO2,SUBBLK_CLOCK_CR_GPIO2_MASK},
        {MSS_PERIPH_RTC,CONTEXT_EN_INDEX, CONTEXT_EN_MASK_RTC,SUBBLK_CLOCK_CR_RTC_MASK},
        {MSS_PERIPH_H2FINT,CONTEXT_EN_INDEX, CONTEXT_EN_MASK_H2FINT,  SUBBLK_CLOCK_NA_MASK},
        {MSS_PERIPH_CRYPTO,CONTEXT_EN_INDEX, CONTEXT_EN_MASK_CRYPTO,SUBBLK_CLOCK_CR_ATHENA_MASK},
        {MSS_PERIPH_USB,CONTEXT_EN_INDEX, CONTEXT_EN_MASK_USB,SUBBLK_CLOCK_CR_USB_MASK},
        {MSS_PERIPH_QSPIXIP,CONTEXT_EN_INDEX, CONTEXT_EN_MASK_QSPIXIP,SUBBLK_CLOCK_CR_QSPI_MASK},
        {MSS_PERIPH_ATHENA,CONTEXT_EN_INDEX, CONTEXT_EN_MASK_ATHENA,SUBBLK_CLOCK_CR_ATHENA_MASK},
        {MSS_PERIPH_TRACE,CONTEXT_EN_INDEX, CONTEXT_EN_MASK_MMC,SUBBLK_CLOCK_CR_MMC_MASK},
        {MSS_PERIPH_MAILBOX_SC,CONTEXT_EN_INDEX, CONTEXT_EN_MASK_MMC,SUBBLK_CLOCK_CR_MMC_MASK},
        {MSS_PERIPH_EMMC,CONTEXT_EN_INDEX, CONTEXT_EN_MASK_MMC,SUBBLK_CLOCK_CR_MMC_MASK},
        {MSS_PERIPH_CFM,CONTEXT_EN_INDEX, CONTEXT_EN_MASK_CFM,SUBBLK_CLOCK_CR_CFM_MASK},
        {MSS_PERIPH_FIC0,CONTEXT_EN_INDEX_FIC, CONTEXT_EN_MASK_FIC0,SUBBLK_CLOCK_CR_FIC0_MASK},
        {MSS_PERIPH_FIC1,CONTEXT_EN_INDEX_FIC, CONTEXT_EN_MASK_FIC1,SUBBLK_CLOCK_CR_FIC1_MASK},
        {MSS_PERIPH_FIC2,CONTEXT_EN_INDEX_FIC, CONTEXT_EN_MASK_FIC2,SUBBLK_CLOCK_CR_FIC2_MASK},
        {MSS_PERIPH_FIC3,CONTEXT_EN_INDEX_FIC, CONTEXT_EN_MASK_FIC3,SUBBLK_CLOCK_CR_FIC3_MASK}
};

/**
 * If contexts set-up, verify allowed access to peripheral
 * @param option - Two option, , FIC enables set separately. CONTEXT_EN_INDEX_FIC or CONTEXT_EN_INDEX
 * @param periph_context_mask See CONTEXT_EN_MASK_ defines for options
 * @param hart The hart ID of origin of request.
 * @return
 */
static inline uint8_t verify_context_enable(uint8_t option, uint32_t periph_context_mask , uint32_t hart)
{
    uint8_t result = 1U;
#if ((LIBERO_SETTING_MEM_CONFIGS_ENABLED & PMP_ENABLED_MASK) == PMP_ENABLED_MASK)
    if (hart != (uint8_t) 0U)
    {
        if (LIBERO_SETTING_CONTEXT_A_HART_EN & hart )
        {
            if (LIBERO_SETTING_CONTEXT_EN[option][0U] & periph_context_mask)
            {
                result = 0U;
            }
        }

        if (LIBERO_SETTING_CONTEXT_B_HART_EN & hart )
        {
            if (LIBERO_SETTING_CONTEXT_EN[option][1U] & periph_context_mask)
            {
                result = 0U;
            }
        }
    }
    else
    {
        hart = 0U;
    }
#else
    (void)hart;
    (void)periph_context_mask;
    (void)option;
    result = 0U;
#endif
    return result;
}

/**
 * Turn on/off mss peripheral as required
 * @param peripheral_mask
 * @param req_state
 */
static inline void peripheral_on_off(uint32_t peripheral_mask , PERIPH_RESET_STATE req_state)
{
    if (req_state == PERIPHERAL_OFF)
    {
        /* Turn off clock */
        SYSREG->SUBBLK_CLOCK_CR &= (uint32_t)~(peripheral_mask);
        /* Hold in reset */
        SYSREG->SOFT_RESET_CR   |= (uint32_t)(peripheral_mask);
    }
    else
    {
        /* Turn on clock */
        SYSREG->SUBBLK_CLOCK_CR |= (peripheral_mask);
        /* Remove soft reset */
        SYSREG->SOFT_RESET_CR   &= (uint32_t)~(peripheral_mask);
    }
}


/***************************************************************************//**
 * See mss_peripherals.h for details of how to use this function.
 */
__attribute__((weak))  uint8_t mss_config_clk_rst(mss_peripherals peripheral, uint8_t hart, PERIPH_RESET_STATE req_state)
{
    uint8_t result = 1U;

    ASSERT(PERIPHERAL_SETUP[peripheral][PERIPHERAL_INDEX_OFFSET] == peripheral);

    result = verify_context_enable(PERIPHERAL_SETUP[peripheral][CONTEXT_EN_INDEX_OFFSET], PERIPHERAL_SETUP[peripheral][CONTEXT_MASK_INDEX_OFFSET] , hart);

    if (result == 0U)
    {
        peripheral_on_off(PERIPHERAL_SETUP[peripheral][CONTEXT_SUBCLK_INDEX_OFFSET] , req_state);
    }
    return result;
}

