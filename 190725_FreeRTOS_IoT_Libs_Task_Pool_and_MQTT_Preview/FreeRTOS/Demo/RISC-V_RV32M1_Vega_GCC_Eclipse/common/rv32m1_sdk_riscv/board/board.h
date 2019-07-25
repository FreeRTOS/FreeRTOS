/*
 * Copyright 2017 NXP
 * All rights reserved.
 *
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

#ifndef _BOARD_H_
#define _BOARD_H_

#include "clock_config.h"
#include "fsl_gpio.h"

/*******************************************************************************
 * Definitions
 ******************************************************************************/
/*! @brief The board name */
#define BOARD_NAME "RV32M1-VEGA"

/* The UART to use for debug messages. */
#define BOARD_DEBUG_UART_TYPE DEBUG_CONSOLE_DEVICE_TYPE_LPUART
#define BOARD_DEBUG_UART_BAUDRATE 115200U
#define BOARD_DEBUG_UART_BASEADDR (uint32_t) LPUART0
#define BOARD_DEBUG_UART_INSTANCE    0U
#define BOARD_DEBUG_UART_CLK_FREQ CLOCK_GetIpFreq(kCLOCK_Lpuart0)
#define BOARD_UART_IRQ LPUART0_IRQn
#define BOARD_UART_IRQ_HANDLER LPUART0_IRQHandler

/* Definitions for eRPC MU transport layer */
#if defined(FSL_FEATURE_MU_SIDE_A)
#define MU_BASE MUA
#define MU_IRQ MUA_IRQn
#define MU_IRQ_HANDLER MUA_IRQHandler
#endif
#if defined(FSL_FEATURE_MU_SIDE_B)
#define MU_BASE MUB
#define MU_IRQ MUB_IRQn
#define MU_IRQ_HANDLER MUB_IRQHandler
#endif
#define MU_IRQ_PRIORITY (2)

/*! @brief Define the port interrupt number for the board switches */
#define BOARD_SW2_GPIO GPIOA
#define BOARD_SW2_PORT PORTA
#define BOARD_SW2_GPIO_PIN 0U
#define BOARD_SW2_IRQ PORTA_IRQn
#define BOARD_SW2_IRQ_HANDLER PORTA_IRQHandler
#define BOARD_SW2_NAME "SW2"

/* Board led color mapping */
#define BOARD_LED_RED_GPIO GPIOA
#define BOARD_LED_RED_GPIO_PIN 24U

/*! @brief The TPM channel used for board */
#define BOARD_TPM_CHANNEL 0U

#define LOGIC_LED_ON 1U
#define LOGIC_LED_OFF 0U
#define BOARD_LED1_GPIO GPIOA
#define BOARD_LED1_GPIO_PIN 24U
#define BOARD_LED2_GPIO GPIOA
#define BOARD_LED2_GPIO_PIN 23U
#define BOARD_LED3_GPIO GPIOA
#define BOARD_LED3_GPIO_PIN 22U

#define LED1_INIT(output)                                              \
    GPIO_WritePinOutput(BOARD_LED1_GPIO, BOARD_LED1_GPIO_PIN, output); \
    BOARD_LED1_GPIO->PDDR |= (1U << BOARD_LED1_GPIO_PIN)                                /*!< Enable target LED1 */
#define LED1_ON() GPIO_SetPinsOutput(BOARD_LED1_GPIO, 1U << BOARD_LED1_GPIO_PIN)        /*!< Turn on target LED1 */
#define LED1_OFF() GPIO_ClearPinsOutput(BOARD_LED1_GPIO, 1U << BOARD_LED1_GPIO_PIN)     /*!< Turn off target LED1 */
#define LED1_TOGGLE() GPIO_TogglePinsOutput(BOARD_LED1_GPIO, 1U << BOARD_LED1_GPIO_PIN) /*!< Toggle on target LED1 */

#define LED2_INIT(output)                                              \
    GPIO_WritePinOutput(BOARD_LED2_GPIO, BOARD_LED2_GPIO_PIN, output); \
    BOARD_LED2_GPIO->PDDR |= (1U << BOARD_LED2_GPIO_PIN)                                /*!< Enable target LED2 */
#define LED2_ON() GPIO_SetPinsOutput(BOARD_LED2_GPIO, 1U << BOARD_LED2_GPIO_PIN)        /*!< Turn on target LED2 */
#define LED2_OFF() GPIO_ClearPinsOutput(BOARD_LED2_GPIO, 1U << BOARD_LED2_GPIO_PIN)     /*!< Turn off target LED2 */
#define LED2_TOGGLE() GPIO_TogglePinsOutput(BOARD_LED2_GPIO, 1U << BOARD_LED2_GPIO_PIN) /*!< Toggle on target LED2 */

#define LED3_INIT(output)                                              \
    GPIO_WritePinOutput(BOARD_LED3_GPIO, BOARD_LED3_GPIO_PIN, output); \
    BOARD_LED3_GPIO->PDDR |= (1U << BOARD_LED3_GPIO_PIN)                                /*!< Enable target LED3 */
#define LED3_ON() GPIO_SetPinsOutput(BOARD_LED3_GPIO, 1U << BOARD_LED3_GPIO_PIN)        /*!< Turn on target LED3 */
#define LED3_OFF() GPIO_ClearPinsOutput(BOARD_LED3_GPIO, 1U << BOARD_LED3_GPIO_PIN)     /*!< Turn off target LED3 */
#define LED3_TOGGLE() GPIO_TogglePinsOutput(BOARD_LED3_GPIO, 1U << BOARD_LED3_GPIO_PIN) /*!< Toggle on target LED3 */

#define BOARD_USDHC0_BASEADDR USDHC0
#define BOARD_USDHC_CD_PORT_BASE PORTC
#define BOARD_USDHC_CD_GPIO_BASE GPIOC
#define BOARD_USDHC_CD_GPIO_PIN 27
#define BOARD_USDHC_CD_PORT_IRQ PORTC_IRQn
#define BOARD_USDHC_CD_PORT_IRQ_HANDLER PORTC_IRQHandler

#define BOARD_USDHC_CD_GPIO_INIT()                                                                                \
    {                                                                                                             \
        gpio_pin_config_t sw_config = {kGPIO_DigitalInput, 0};                                                    \
        GPIO_PinInit(BOARD_USDHC_CD_GPIO_BASE, BOARD_USDHC_CD_GPIO_PIN, &sw_config);                              \
        PORT_SetPinInterruptConfig(BOARD_USDHC_CD_PORT_BASE, BOARD_USDHC_CD_GPIO_PIN, kPORT_InterruptRisingEdge); \
    }

#define BOARD_USDHC_CD_STATUS() (GPIO_ReadPinInput(BOARD_USDHC_CD_GPIO_BASE, BOARD_USDHC_CD_GPIO_PIN))

#define BOARD_USDHC_CD_INTERRUPT_STATUS() (GPIO_GetPinsInterruptFlags(BOARD_USDHC_CD_GPIO_BASE))
#define BOARD_USDHC_CD_CLEAR_INTERRUPT(flag) (GPIO_ClearPinsInterruptFlags(BOARD_USDHC_CD_GPIO_BASE, flag))
#define BOARD_USDHC_CARD_INSERT_CD_LEVEL (1U)
#define BOARD_USDHC0_CLK_FREQ (CLOCK_GetIpFreq(kCLOCK_Sdhc0))

#define BOARD_SD_HOST_BASEADDR BOARD_USDHC0_BASEADDR
#define BOARD_SD_HOST_CLK_FREQ BOARD_USDHC0_CLK_FREQ
#define BOARD_SD_HOST_IRQ USDHC0_IRQn
#define BOARD_SD_SUPPORT_180V (0U)
#define BOARD_MMC_HOST_BASEADDR BOARD_USDHC0_BASEADDR
#define BOARD_MMC_HOST_CLK_FREQ BOARD_USDHC0_CLK_FREQ
#define BOARD_MMC_HOST_IRQ USDHC0_IRQn
#define BOARD_MMC_VCCQ_SUPPLY kMMC_VoltageWindows270to360
#define BOARD_MMC_VCC_SUPPLY kMMC_VoltageWindows270to360
#define BOARD_MMC_PIN_CONFIG(speed, strength)

/* this define not implement, due to EVK board have no power reset circuit */
#define BOARD_SD_POWER_RESET_GPIO ()
#define BOARD_SD_POWER_RESET_GPIO_PIN ()
#define BOARD_USDHC_SDCARD_POWER_CONTROL_INIT()
#define BOARD_USDHC_SDCARD_POWER_CONTROL(state)
#define BOARD_SD_PIN_CONFIG(speed, strength)
#define BOARD_USDHC_MMCCARD_POWER_CONTROL(enable)
#define BOARD_USDHC_MMCCARD_POWER_CONTROL_INIT()

#define LLWU_SW_GPIO BOARD_SW2_GPIO
#define LLWU_SW_PORT BOARD_SW2_PORT
#define LLWU_SW_GPIO_PIN BOARD_SW2_GPIO_PIN
#define LLWU_SW_IRQ BOARD_SW2_IRQ
#define LLWU_SW_IRQ_HANDLER BOARD_SW2_IRQ_HANDLER
#define LLWU_SW_NAME BOARD_SW2_NAME

#define NMI_PIN                0U
#define JTAG_TCLK_PIN          1U
#define JTAG_TDI_PIN           2U
#define JTAG_TDO_PIN           3U
#define JTAG_TMS_PIN           4U

#define NMI_PORT               PORTA
#define JTAG_TCLK_PORT         PORTA
#define JTAG_TDI_PORT          PORTA
#define JTAG_TDO_PORT          PORTA
#define JTAG_TMS_PORT          PORTA 

#define NMI_GPIO               GPIOA
#define JTAG_TCLK_GPIO         GPIOA
#define JTAG_TDI_GPIO          GPIOA
#define JTAG_TDO_GPIO          GPIOA
#define JTAG_TMS_GPIO          GPIOA

#define BOARD_SPI_FLASH_SCLK_PORT       PORTB
#define BOARD_SPI_FLASH_SCLK_GPIO       GPIOB
#define BOARD_SPI_FLASH_SCLK_GPIO_PIN   20U

#define BOARD_SPI_FLASH_SI_PORT         PORTB
#define BOARD_SPI_FLASH_SI_GPIO         GPIOB
#define BOARD_SPI_FLASH_SI_GPIO_PIN     21U

#define BOARD_SPI_FLASH_CS_PORT         PORTB
#define BOARD_SPI_FLASH_CS_GPIO         GPIOB
#define BOARD_SPI_FLASH_CS_GPIO_PIN     22U

#define BOARD_SPI_FLASH_SO_PORT         PORTB
#define BOARD_SPI_FLASH_SO_GPIO         GPIOB
#define BOARD_SPI_FLASH_SO_GPIO_PIN     24U
#if defined(__cplusplus)
extern "C" {
#endif /* __cplusplus */

/*******************************************************************************
 * API
 ******************************************************************************/

void BOARD_InitDebugConsole(void);

#if defined(__cplusplus)
}
#endif /* __cplusplus */

#endif /* _BOARD_H_ */
