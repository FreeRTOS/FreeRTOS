/*******************************************************************************
 * Copyright 2019-2021 Microchip FPGA Embedded Systems Solutions.
 *
 * SPDX-License-Identifier: MIT
 *
 * MPFS HAL Embedded Software
 *
 */
/*******************************************************************************
 * @file mss_peripherals.h
 * @author Microchip-FPGA Embedded Systems Solutions
 * @brief PolarFire SoC MSS fumnctions related to MSS peripherals.
 *
 */
/*=========================================================================*//**

 *//*=========================================================================*/
#ifndef MSS_PERIPHERALS_H
#define MSS_PERIPHERALS_H

#include <stdint.h>


#ifdef __cplusplus
extern "C" {
#endif

#if !defined (LIBERO_SETTING_CONTEXT_A_EN)
#define LIBERO_SETTING_CONTEXT_A_EN         0x00000000UL
#endif
#if !defined (LIBERO_SETTING_CONTEXT_B_EN)
#define LIBERO_SETTING_CONTEXT_B_EN         0x00000000UL
#endif
#if !defined (LIBERO_SETTING_CONTEXT_A_EN_FIC)
#define LIBERO_SETTING_CONTEXT_A_EN_FIC     0x0000000FUL
#endif
#if !defined (LIBERO_SETTING_CONTEXT_B_EN_FIC)
#define LIBERO_SETTING_CONTEXT_B_EN_FIC     0x0000000FUL
#endif

/***************************************************************************//**

 */
typedef enum PERIPH_RESET_STATE_
{

    PERIPHERAL_ON                       = 0x00,        /*!< 0 RST and clk ON  */
    PERIPHERAL_OFF                      = 0x01,        /*!< 1 RST and clk OFF */
} PERIPH_RESET_STATE;

#define CONTEXT_EN_INDEX                 0x00U
#define CONTEXT_EN_INDEX_FIC             0x01U
#define SUBBLK_CLOCK_NA_MASK             0x00U

typedef enum mss_peripherals_ {
    MSS_PERIPH_MMUART0      = 0U,
    MSS_PERIPH_MMUART1      = 1U,
    MSS_PERIPH_MMUART2      = 2U,
    MSS_PERIPH_MMUART3      = 3U,
    MSS_PERIPH_MMUART4      = 4U,
    MSS_PERIPH_WDOG0        = 5U,
    MSS_PERIPH_WDOG1        = 6U,
    MSS_PERIPH_WDOG2        = 7U,
    MSS_PERIPH_WDOG3        = 8U,
    MSS_PERIPH_WDOG4        = 9U,
    MSS_PERIPH_SPI0         = 10U,
    MSS_PERIPH_SPI1         = 11U,
    MSS_PERIPH_I2C0         = 12U,
    MSS_PERIPH_I2C1         = 13U,
    MSS_PERIPH_CAN0         = 14U,
    MSS_PERIPH_CAN1         = 15U,
    MSS_PERIPH_MAC0         = 16U,
    MSS_PERIPH_MAC1         = 17U,
    MSS_PERIPH_TIMER        = 18U,
    MSS_PERIPH_GPIO0        = 19U,
    MSS_PERIPH_GPIO1        = 20U,
    MSS_PERIPH_GPIO2        = 21U,
    MSS_PERIPH_RTC          = 22U,
    MSS_PERIPH_H2FINT       = 23U,
    MSS_PERIPH_CRYPTO       = 24U,
    MSS_PERIPH_USB          = 25U,
    MSS_PERIPH_QSPIXIP      = 26U,
    MSS_PERIPH_ATHENA       = 27U,
    MSS_PERIPH_TRACE        = 28U,
    MSS_PERIPH_MAILBOX_SC   = 29U,
    MSS_PERIPH_EMMC         = 30U,
    MSS_PERIPH_CFM          = 31U,
    MSS_PERIPH_FIC0         = 32U,
    MSS_PERIPH_FIC1         = 33U,
    MSS_PERIPH_FIC2         = 34U,
    MSS_PERIPH_FIC3         = 35U
} mss_peripherals;


/***************************************************************************//**
  This function is used to turn on or off a peripheral. If contexts have been
  configured, these will be checked to see if peripheral should be controlled
  from a particular context.

  @param peripheral
    See enum mss_peripherals for list of peripherals

  @param hart
    Origin hart of this request

  @req_state
    Turn peripheral on or off:
        - PERIPHERAL_ON
        - PERIPHERAL_OFF
  Example:
  @code
    uint8_t err_status;
    err_status = mss_config_clk_rst(MSS_PERIPH_MMUART0, (uint8_t) origin_hart_ID, PERIPHERAL_ON);

    if(0U != err_status)
    {
       print_uart0("\n\r Context not allowed to access UART0 from hart:%d\n\nr", origin_hart_ID);
    }
  @endcode
 */
uint8_t mss_config_clk_rst(mss_peripherals peripheral, uint8_t hart, PERIPH_RESET_STATE req_state);


#ifdef __cplusplus
}
#endif


#endif /* MSS_PERIPHERALS_H */
