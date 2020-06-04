/*
 * Copyright (c) 2016, Freescale Semiconductor, Inc.
 * Copyright 2016 - 2019 , NXP
 * All rights reserved.
 *
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

#ifndef _FSL_CLOCK_H_
#define _FSL_CLOCK_H_

#include "fsl_common.h"

/*! @addtogroup clock */
/*! @{ */

/*! @file */

/*******************************************************************************
 * Definitions
 *****************************************************************************/

/*! @name Driver version */
/*@{*/
/*! @brief CLOCK driver version 2.3.1. */
#define FSL_CLOCK_DRIVER_VERSION (MAKE_VERSION(2, 3, 1))
/*@}*/

/*! @brief Configure whether driver controls clock
 *
 * When set to 0, peripheral drivers will enable clock in initialize function
 * and disable clock in de-initialize function. When set to 1, peripheral
 * driver will not control the clock, application could control the clock out of
 * the driver.
 *
 * @note All drivers share this feature switcher. If it is set to 1, application
 * should handle clock enable and disable for all drivers.
 */
#if !(defined(FSL_SDK_DISABLE_DRIVER_CLOCK_CONTROL))
#define FSL_SDK_DISABLE_DRIVER_CLOCK_CONTROL 0
#endif

/*!
 * @brief User-defined the size of cache for CLOCK_PllGetConfig() function.
 *
 * Once define this MACRO to be non-zero value, CLOCK_PllGetConfig() function
 * would cache the recent calulation and accelerate the execution to get the
 * right settings.
 */
#ifndef CLOCK_USR_CFG_PLL_CONFIG_CACHE_COUNT
#define CLOCK_USR_CFG_PLL_CONFIG_CACHE_COUNT 2U
#endif

/* Definition for delay API in clock driver, users can redefine it to the real application. */
#ifndef SDK_DEVICE_MAXIMUM_CPU_CLOCK_FREQUENCY
#define SDK_DEVICE_MAXIMUM_CPU_CLOCK_FREQUENCY (180000000UL)
#endif

/*! @brief Clock ip name array for ADC. */
#define ADC_CLOCKS  \
    {               \
        kCLOCK_Adc0 \
    }
/*! @brief Clock ip name array for ROM. */
#define ROM_CLOCKS \
    {              \
        kCLOCK_Rom \
    }
/*! @brief Clock ip name array for SRAM. */
#define SRAM_CLOCKS                              \
    {                                            \
        kCLOCK_Sram1, kCLOCK_Sram2, kCLOCK_Sram3 \
    }
/*! @brief Clock ip name array for FLASH. */
#define FLASH_CLOCKS \
    {                \
        kCLOCK_Flash \
    }
/*! @brief Clock ip name array for FMC. */
#define FMC_CLOCKS \
    {              \
        kCLOCK_Fmc \
    }
/*! @brief Clock ip name array for EEPROM. */
#define EEPROM_CLOCKS \
    {                 \
        kCLOCK_Eeprom \
    }
/*! @brief Clock ip name array for SPIFI. */
#define SPIFI_CLOCKS \
    {                \
        kCLOCK_Spifi \
    }
/*! @brief Clock ip name array for INPUTMUX. */
#define INPUTMUX_CLOCKS \
    {                   \
        kCLOCK_InputMux \
    }
/*! @brief Clock ip name array for IOCON. */
#define IOCON_CLOCKS \
    {                \
        kCLOCK_Iocon \
    }
/*! @brief Clock ip name array for GPIO. */
#define GPIO_CLOCKS                                                                        \
    {                                                                                      \
        kCLOCK_Gpio0, kCLOCK_Gpio1, kCLOCK_Gpio2, kCLOCK_Gpio3, kCLOCK_Gpio4, kCLOCK_Gpio5 \
    }
/*! @brief Clock ip name array for PINT. */
#define PINT_CLOCKS \
    {               \
        kCLOCK_Pint \
    }
/*! @brief Clock ip name array for GINT. */
#define GINT_CLOCKS              \
    {                            \
        kCLOCK_Gint, kCLOCK_Gint \
    }
/*! @brief Clock ip name array for DMA. */
#define DMA_CLOCKS \
    {              \
        kCLOCK_Dma \
    }
/*! @brief Clock ip name array for CRC. */
#define CRC_CLOCKS \
    {              \
        kCLOCK_Crc \
    }
/*! @brief Clock ip name array for WWDT. */
#define WWDT_CLOCKS \
    {               \
        kCLOCK_Wwdt \
    }
/*! @brief Clock ip name array for RTC. */
#define RTC_CLOCKS \
    {              \
        kCLOCK_Rtc \
    }
/*! @brief Clock ip name array for ADC0. */
#define ADC0_CLOCKS \
    {               \
        kCLOCK_Adc0 \
    }
/*! @brief Clock ip name array for MRT. */
#define MRT_CLOCKS \
    {              \
        kCLOCK_Mrt \
    }
/*! @brief Clock ip name array for RIT. */
#define RIT_CLOCKS \
    {              \
        kCLOCK_Rit \
    }
/*! @brief Clock ip name array for SCT0. */
#define SCT_CLOCKS  \
    {               \
        kCLOCK_Sct0 \
    }
/*! @brief Clock ip name array for MCAN. */
#define MCAN_CLOCKS                \
    {                              \
        kCLOCK_Mcan0, kCLOCK_Mcan1 \
    }
/*! @brief Clock ip name array for UTICK. */
#define UTICK_CLOCKS \
    {                \
        kCLOCK_Utick \
    }
/*! @brief Clock ip name array for FLEXCOMM. */
#define FLEXCOMM_CLOCKS                                                                                             \
    {                                                                                                               \
        kCLOCK_FlexComm0, kCLOCK_FlexComm1, kCLOCK_FlexComm2, kCLOCK_FlexComm3, kCLOCK_FlexComm4, kCLOCK_FlexComm5, \
            kCLOCK_FlexComm6, kCLOCK_FlexComm7, kCLOCK_FlexComm8, kCLOCK_FlexComm9, kCLOCK_FlexComm10               \
    }
/*! @brief Clock ip name array for LPUART. */
#define LPUART_CLOCKS                                                                                         \
    {                                                                                                         \
        kCLOCK_MinUart0, kCLOCK_MinUart1, kCLOCK_MinUart2, kCLOCK_MinUart3, kCLOCK_MinUart4, kCLOCK_MinUart5, \
            kCLOCK_MinUart6, kCLOCK_MinUart7, kCLOCK_MinUart8, kCLOCK_MinUart9                                \
    }

/*! @brief Clock ip name array for BI2C. */
#define BI2C_CLOCKS                                                                                       \
    {                                                                                                     \
        kCLOCK_BI2c0, kCLOCK_BI2c1, kCLOCK_BI2c2, kCLOCK_BI2c3, kCLOCK_BI2c4, kCLOCK_BI2c5, kCLOCK_BI2c6, \
            kCLOCK_BI2c7, kCLOCK_BI2c8, kCLOCK_BI2c9                                                      \
    }
/*! @brief Clock ip name array for LSPI. */
#define LPSI_CLOCKS                                                                                       \
    {                                                                                                     \
        kCLOCK_LSpi0, kCLOCK_LSpi1, kCLOCK_LSpi2, kCLOCK_LSpi3, kCLOCK_LSpi4, kCLOCK_LSpi5, kCLOCK_LSpi6, \
            kCLOCK_LSpi7, kCLOCK_LSpi8, kCLOCK_LSpi9                                                      \
    }
/*! @brief Clock ip name array for FLEXI2S. */
#define FLEXI2S_CLOCKS                                                                                        \
    {                                                                                                         \
        kCLOCK_FlexI2s0, kCLOCK_FlexI2s1, kCLOCK_FlexI2s2, kCLOCK_FlexI2s3, kCLOCK_FlexI2s4, kCLOCK_FlexI2s5, \
            kCLOCK_FlexI2s6, kCLOCK_FlexI2s7, kCLOCK_FlexI2s8, kCLOCK_FlexI2s9                                \
    }
/*! @brief Clock ip name array for DMIC. */
#define DMIC_CLOCKS \
    {               \
        kCLOCK_DMic \
    }
/*! @brief Clock ip name array for CT32B. */
#define CTIMER_CLOCKS                                                             \
    {                                                                             \
        kCLOCK_Ct32b0, kCLOCK_Ct32b1, kCLOCK_Ct32b2, kCLOCK_Ct32b3, kCLOCK_Ct32b4 \
    }
/*! @brief Clock ip name array for LCD. */
#define LCD_CLOCKS \
    {              \
        kCLOCK_Lcd \
    }
/*! @brief Clock ip name array for SDIO. */
#define SDIO_CLOCKS \
    {               \
        kCLOCK_Sdio \
    }
/*! @brief Clock ip name array for USBRAM. */
#define USBRAM_CLOCKS  \
    {                  \
        kCLOCK_UsbRam1 \
    }
/*! @brief Clock ip name array for EMC. */
#define EMC_CLOCKS \
    {              \
        kCLOCK_Emc \
    }
/*! @brief Clock ip name array for ETH. */
#define ETH_CLOCKS \
    {              \
        kCLOCK_Eth \
    }
/*! @brief Clock ip name array for AES. */
#define AES_CLOCKS \
    {              \
        kCLOCK_Aes \
    }
/*! @brief Clock ip name array for OTP. */
#define OTP_CLOCKS \
    {              \
        kCLOCK_Otp \
    }
/*! @brief Clock ip name array for RNG. */
#define RNG_CLOCKS \
    {              \
        kCLOCK_Rng \
    }
/*! @brief Clock ip name array for USBHMR0. */
#define USBHMR0_CLOCKS \
    {                  \
        kCLOCK_Usbhmr0 \
    }
/*! @brief Clock ip name array for USBHSL0. */
#define USBHSL0_CLOCKS \
    {                  \
        kCLOCK_Usbhsl0 \
    }
/*! @brief Clock ip name array for SHA0. */
#define SHA0_CLOCKS \
    {               \
        kCLOCK_Sha0 \
    }
/*! @brief Clock ip name array for SMARTCARD. */
#define SMARTCARD_CLOCKS                     \
    {                                        \
        kCLOCK_SmartCard0, kCLOCK_SmartCard1 \
    }
/*! @brief Clock ip name array for USBD. */
#define USBD_CLOCKS                              \
    {                                            \
        kCLOCK_Usbd0, kCLOCK_Usbh1, kCLOCK_Usbd1 \
    }
/*! @brief Clock ip name array for USBH. */
#define USBH_CLOCKS  \
    {                \
        kCLOCK_Usbh1 \
    }
/*! @brief Clock gate name used for CLOCK_EnableClock/CLOCK_DisableClock. */
/*------------------------------------------------------------------------------
 clock_ip_name_t definition:
------------------------------------------------------------------------------*/

#define CLK_GATE_REG_OFFSET_SHIFT 8U
#define CLK_GATE_REG_OFFSET_MASK 0xFFFFFF00U
#define CLK_GATE_BIT_SHIFT_SHIFT 0U
#define CLK_GATE_BIT_SHIFT_MASK 0x000000FFU

#define CLK_GATE_DEFINE(reg_offset, bit_shift)                                  \
    ((((reg_offset) << CLK_GATE_REG_OFFSET_SHIFT) & CLK_GATE_REG_OFFSET_MASK) | \
     (((bit_shift) << CLK_GATE_BIT_SHIFT_SHIFT) & CLK_GATE_BIT_SHIFT_MASK))

#define CLK_GATE_ABSTRACT_REG_OFFSET(x) (((uint32_t)(x)&CLK_GATE_REG_OFFSET_MASK) >> CLK_GATE_REG_OFFSET_SHIFT)
#define CLK_GATE_ABSTRACT_BITS_SHIFT(x) (((uint32_t)(x)&CLK_GATE_BIT_SHIFT_MASK) >> CLK_GATE_BIT_SHIFT_SHIFT)

#define AHB_CLK_CTRL0 0
#define AHB_CLK_CTRL1 1
#define AHB_CLK_CTRL2 2
#define ASYNC_CLK_CTRL0 3

/*! @brief Clock gate name used for CLOCK_EnableClock/CLOCK_DisableClock. */
typedef enum _clock_ip_name
{
    kCLOCK_IpInvalid  = 0U,
    kCLOCK_Rom        = CLK_GATE_DEFINE(AHB_CLK_CTRL0, 1),
    kCLOCK_Sram1      = CLK_GATE_DEFINE(AHB_CLK_CTRL0, 3),
    kCLOCK_Sram2      = CLK_GATE_DEFINE(AHB_CLK_CTRL0, 4),
    kCLOCK_Sram3      = CLK_GATE_DEFINE(AHB_CLK_CTRL0, 5),
    kCLOCK_Spifi      = CLK_GATE_DEFINE(AHB_CLK_CTRL0, 10),
    kCLOCK_InputMux   = CLK_GATE_DEFINE(AHB_CLK_CTRL0, 11),
    kCLOCK_Iocon      = CLK_GATE_DEFINE(AHB_CLK_CTRL0, 13),
    kCLOCK_Gpio0      = CLK_GATE_DEFINE(AHB_CLK_CTRL0, 14),
    kCLOCK_Gpio1      = CLK_GATE_DEFINE(AHB_CLK_CTRL0, 15),
    kCLOCK_Gpio2      = CLK_GATE_DEFINE(AHB_CLK_CTRL0, 16),
    kCLOCK_Gpio3      = CLK_GATE_DEFINE(AHB_CLK_CTRL0, 17),
    kCLOCK_Pint       = CLK_GATE_DEFINE(AHB_CLK_CTRL0, 18),
    kCLOCK_Gint       = CLK_GATE_DEFINE(AHB_CLK_CTRL0, 19),
    kCLOCK_Dma        = CLK_GATE_DEFINE(AHB_CLK_CTRL0, 20),
    kCLOCK_Crc        = CLK_GATE_DEFINE(AHB_CLK_CTRL0, 21),
    kCLOCK_Wwdt       = CLK_GATE_DEFINE(AHB_CLK_CTRL0, 22),
    kCLOCK_Rtc        = CLK_GATE_DEFINE(AHB_CLK_CTRL0, 23),
    kCLOCK_Adc0       = CLK_GATE_DEFINE(AHB_CLK_CTRL0, 27),
    kCLOCK_Mrt        = CLK_GATE_DEFINE(AHB_CLK_CTRL1, 0),
    kCLOCK_Rit        = CLK_GATE_DEFINE(AHB_CLK_CTRL1, 1),
    kCLOCK_Sct0       = CLK_GATE_DEFINE(AHB_CLK_CTRL1, 2),
    kCLOCK_Mcan0      = CLK_GATE_DEFINE(AHB_CLK_CTRL1, 7),
    kCLOCK_Mcan1      = CLK_GATE_DEFINE(AHB_CLK_CTRL1, 8),
    kCLOCK_Utick      = CLK_GATE_DEFINE(AHB_CLK_CTRL1, 10),
    kCLOCK_FlexComm0  = CLK_GATE_DEFINE(AHB_CLK_CTRL1, 11),
    kCLOCK_FlexComm1  = CLK_GATE_DEFINE(AHB_CLK_CTRL1, 12),
    kCLOCK_FlexComm2  = CLK_GATE_DEFINE(AHB_CLK_CTRL1, 13),
    kCLOCK_FlexComm3  = CLK_GATE_DEFINE(AHB_CLK_CTRL1, 14),
    kCLOCK_FlexComm4  = CLK_GATE_DEFINE(AHB_CLK_CTRL1, 15),
    kCLOCK_FlexComm5  = CLK_GATE_DEFINE(AHB_CLK_CTRL1, 16),
    kCLOCK_FlexComm6  = CLK_GATE_DEFINE(AHB_CLK_CTRL1, 17),
    kCLOCK_FlexComm7  = CLK_GATE_DEFINE(AHB_CLK_CTRL1, 18),
    kCLOCK_MinUart0   = CLK_GATE_DEFINE(AHB_CLK_CTRL1, 11),
    kCLOCK_MinUart1   = CLK_GATE_DEFINE(AHB_CLK_CTRL1, 12),
    kCLOCK_MinUart2   = CLK_GATE_DEFINE(AHB_CLK_CTRL1, 13),
    kCLOCK_MinUart3   = CLK_GATE_DEFINE(AHB_CLK_CTRL1, 14),
    kCLOCK_MinUart4   = CLK_GATE_DEFINE(AHB_CLK_CTRL1, 15),
    kCLOCK_MinUart5   = CLK_GATE_DEFINE(AHB_CLK_CTRL1, 16),
    kCLOCK_MinUart6   = CLK_GATE_DEFINE(AHB_CLK_CTRL1, 17),
    kCLOCK_MinUart7   = CLK_GATE_DEFINE(AHB_CLK_CTRL1, 18),
    kCLOCK_LSpi0      = CLK_GATE_DEFINE(AHB_CLK_CTRL1, 11),
    kCLOCK_LSpi1      = CLK_GATE_DEFINE(AHB_CLK_CTRL1, 12),
    kCLOCK_LSpi2      = CLK_GATE_DEFINE(AHB_CLK_CTRL1, 13),
    kCLOCK_LSpi3      = CLK_GATE_DEFINE(AHB_CLK_CTRL1, 14),
    kCLOCK_LSpi4      = CLK_GATE_DEFINE(AHB_CLK_CTRL1, 15),
    kCLOCK_LSpi5      = CLK_GATE_DEFINE(AHB_CLK_CTRL1, 16),
    kCLOCK_LSpi6      = CLK_GATE_DEFINE(AHB_CLK_CTRL1, 17),
    kCLOCK_LSpi7      = CLK_GATE_DEFINE(AHB_CLK_CTRL1, 18),
    kCLOCK_BI2c0      = CLK_GATE_DEFINE(AHB_CLK_CTRL1, 11),
    kCLOCK_BI2c1      = CLK_GATE_DEFINE(AHB_CLK_CTRL1, 12),
    kCLOCK_BI2c2      = CLK_GATE_DEFINE(AHB_CLK_CTRL1, 13),
    kCLOCK_BI2c3      = CLK_GATE_DEFINE(AHB_CLK_CTRL1, 14),
    kCLOCK_BI2c4      = CLK_GATE_DEFINE(AHB_CLK_CTRL1, 15),
    kCLOCK_BI2c5      = CLK_GATE_DEFINE(AHB_CLK_CTRL1, 16),
    kCLOCK_BI2c6      = CLK_GATE_DEFINE(AHB_CLK_CTRL1, 17),
    kCLOCK_BI2c7      = CLK_GATE_DEFINE(AHB_CLK_CTRL1, 18),
    kCLOCK_FlexI2s0   = CLK_GATE_DEFINE(AHB_CLK_CTRL1, 11),
    kCLOCK_FlexI2s1   = CLK_GATE_DEFINE(AHB_CLK_CTRL1, 12),
    kCLOCK_FlexI2s2   = CLK_GATE_DEFINE(AHB_CLK_CTRL1, 13),
    kCLOCK_FlexI2s3   = CLK_GATE_DEFINE(AHB_CLK_CTRL1, 14),
    kCLOCK_FlexI2s4   = CLK_GATE_DEFINE(AHB_CLK_CTRL1, 15),
    kCLOCK_FlexI2s5   = CLK_GATE_DEFINE(AHB_CLK_CTRL1, 16),
    kCLOCK_FlexI2s6   = CLK_GATE_DEFINE(AHB_CLK_CTRL1, 17),
    kCLOCK_FlexI2s7   = CLK_GATE_DEFINE(AHB_CLK_CTRL1, 18),
    kCLOCK_DMic       = CLK_GATE_DEFINE(AHB_CLK_CTRL1, 19),
    kCLOCK_Ct32b2     = CLK_GATE_DEFINE(AHB_CLK_CTRL1, 22),
    kCLOCK_Usbd0      = CLK_GATE_DEFINE(AHB_CLK_CTRL1, 25),
    kCLOCK_Ct32b0     = CLK_GATE_DEFINE(AHB_CLK_CTRL1, 26),
    kCLOCK_Ct32b1     = CLK_GATE_DEFINE(AHB_CLK_CTRL1, 27),
    kCLOCK_BodyBias0  = CLK_GATE_DEFINE(AHB_CLK_CTRL1, 29),
    kCLOCK_EzhArchB0  = CLK_GATE_DEFINE(AHB_CLK_CTRL1, 31),
    kCLOCK_Lcd        = CLK_GATE_DEFINE(AHB_CLK_CTRL2, 2),
    kCLOCK_Sdio       = CLK_GATE_DEFINE(AHB_CLK_CTRL2, 3),
    kCLOCK_Usbh1      = CLK_GATE_DEFINE(AHB_CLK_CTRL2, 4),
    kCLOCK_Usbd1      = CLK_GATE_DEFINE(AHB_CLK_CTRL2, 5),
    kCLOCK_UsbRam1    = CLK_GATE_DEFINE(AHB_CLK_CTRL2, 6),
    kCLOCK_Emc        = CLK_GATE_DEFINE(AHB_CLK_CTRL2, 7),
    kCLOCK_Eth        = CLK_GATE_DEFINE(AHB_CLK_CTRL2, 8),
    kCLOCK_Gpio4      = CLK_GATE_DEFINE(AHB_CLK_CTRL2, 9),
    kCLOCK_Gpio5      = CLK_GATE_DEFINE(AHB_CLK_CTRL2, 10),
    kCLOCK_Aes        = CLK_GATE_DEFINE(AHB_CLK_CTRL2, 11),
    kCLOCK_Otp        = CLK_GATE_DEFINE(AHB_CLK_CTRL2, 12),
    kCLOCK_Rng        = CLK_GATE_DEFINE(AHB_CLK_CTRL2, 13),
    kCLOCK_FlexComm8  = CLK_GATE_DEFINE(AHB_CLK_CTRL2, 14),
    kCLOCK_FlexComm9  = CLK_GATE_DEFINE(AHB_CLK_CTRL2, 15),
    kCLOCK_MinUart8   = CLK_GATE_DEFINE(AHB_CLK_CTRL2, 14),
    kCLOCK_MinUart9   = CLK_GATE_DEFINE(AHB_CLK_CTRL2, 15),
    kCLOCK_LSpi8      = CLK_GATE_DEFINE(AHB_CLK_CTRL2, 14),
    kCLOCK_LSpi9      = CLK_GATE_DEFINE(AHB_CLK_CTRL2, 15),
    kCLOCK_BI2c8      = CLK_GATE_DEFINE(AHB_CLK_CTRL2, 14),
    kCLOCK_BI2c9      = CLK_GATE_DEFINE(AHB_CLK_CTRL2, 15),
    kCLOCK_FlexI2s8   = CLK_GATE_DEFINE(AHB_CLK_CTRL2, 14),
    kCLOCK_FlexI2s9   = CLK_GATE_DEFINE(AHB_CLK_CTRL2, 15),
    kCLOCK_Usbhmr0    = CLK_GATE_DEFINE(AHB_CLK_CTRL2, 16),
    kCLOCK_Usbhsl0    = CLK_GATE_DEFINE(AHB_CLK_CTRL2, 17),
    kCLOCK_Sha0       = CLK_GATE_DEFINE(AHB_CLK_CTRL2, 18),
    kCLOCK_SmartCard0 = CLK_GATE_DEFINE(AHB_CLK_CTRL2, 19),
    kCLOCK_SmartCard1 = CLK_GATE_DEFINE(AHB_CLK_CTRL2, 20),
    kCLOCK_FlexComm10 = CLK_GATE_DEFINE(AHB_CLK_CTRL2, 21),

    kCLOCK_Ct32b3 = CLK_GATE_DEFINE(ASYNC_CLK_CTRL0, 13),
    kCLOCK_Ct32b4 = CLK_GATE_DEFINE(ASYNC_CLK_CTRL0, 14)
} clock_ip_name_t;

/*! @brief Clock name used to get clock frequency. */
typedef enum _clock_name
{
    kCLOCK_CoreSysClk,  /*!< Core/system clock  (aka MAIN_CLK)                       */
    kCLOCK_BusClk,      /*!< Bus clock (AHB clock)                                   */
    kCLOCK_ClockOut,    /*!< CLOCKOUT                                                */
    kCLOCK_FroHf,       /*!< FRO48/96                                                */
    kCLOCK_UsbPll,      /*!< USB1 PLL                                                */
    kCLOCK_Mclk,        /*!< MCLK                                                    */
    kCLOCK_Fro12M,      /*!< FRO12M                                                  */
    kCLOCK_ExtClk,      /*!< External Clock                                          */
    kCLOCK_PllOut,      /*!< PLL Output                                              */
    kCLOCK_UsbClk,      /*!< USB input                                               */
    kCLOCK_WdtOsc,      /*!< Watchdog Oscillator                                     */
    kCLOCK_Frg,         /*!< Frg Clock                                               */
    kCLOCK_AsyncApbClk, /*!< Async APB clock                                         */
} clock_name_t;

/**
 * Clock source selections for the asynchronous APB clock
 */
typedef enum _async_clock_src
{
    kCLOCK_AsyncMainClk = 0, /*!< Main System clock */
    kCLOCK_AsyncFro12Mhz,    /*!< 12MHz FRO */
    kCLOCK_AsyncAudioPllClk,
    kCLOCK_AsyncI2cClkFc6,

} async_clock_src_t;

/*! @brief Clock Mux Switches
 *  The encoding is as follows each connection identified is 32bits wide while 24bits are valuable
 *  starting from LSB upwards
 *
 *  [4 bits for choice, 0 means invalid choice] [8 bits mux ID]*
 *
 */

#define CLK_ATTACH_ID(mux, sel, pos) ((((uint32_t)(mux) << 0U) | (((uint32_t)(sel) + 1U) & 0xFU) << 8U) << ((pos)*12U))
#define MUX_A(mux, sel) CLK_ATTACH_ID((mux), (sel), 0U)
#define MUX_B(mux, sel, selector) (CLK_ATTACH_ID((mux), (sel), 1U) | ((selector) << 24U))

#define GET_ID_ITEM(connection) ((connection)&0xFFFU)
#define GET_ID_NEXT_ITEM(connection) ((connection) >> 12U)
#define GET_ID_ITEM_MUX(connection) ((uint8_t)((connection)&0xFFU))
#define GET_ID_ITEM_SEL(connection) ((uint8_t)((((connection)&0xF00U) >> 8U) - 1U))
#define GET_ID_SELECTOR(connection) ((connection)&0xF000000U)

#define CM_STICKCLKSEL 0
#define CM_MAINCLKSELA 1
#define CM_MAINCLKSELB 2
#define CM_CLKOUTCLKSELA 3
#define CM_SYSPLLCLKSEL 5
#define CM_AUDPLLCLKSEL 7
#define CM_SPIFICLKSEL 9
#define CM_ADCASYNCCLKSEL 10
#define CM_USB0CLKSEL 11
#define CM_USB1CLKSEL 12
#define CM_FXCOMCLKSEL0 13
#define CM_FXCOMCLKSEL1 14
#define CM_FXCOMCLKSEL2 15
#define CM_FXCOMCLKSEL3 16
#define CM_FXCOMCLKSEL4 17
#define CM_FXCOMCLKSEL5 18
#define CM_FXCOMCLKSEL6 19
#define CM_FXCOMCLKSEL7 20
#define CM_FXCOMCLKSEL8 21
#define CM_FXCOMCLKSEL9 22
#define CM_FXCOMCLKSEL10 23
#define CM_MCLKCLKSEL 25
#define CM_FRGCLKSEL 27
#define CM_DMICCLKSEL 28
#define CM_SCTCLKSEL 29
#define CM_LCDCLKSEL 30
#define CM_SDIOCLKSEL 31

#define CM_ASYNCAPB 32U

typedef enum _clock_attach_id
{

    kSYSTICK_DIV_CLK_to_SYSTICKCLK = MUX_A(CM_STICKCLKSEL, 0),
    kWDT_OSC_to_SYSTICKCLK         = MUX_A(CM_STICKCLKSEL, 1),
    kOSC32K_to_SYSTICKCLK          = MUX_A(CM_STICKCLKSEL, 2),
    kFRO12M_to_SYSTICKCLK          = MUX_A(CM_STICKCLKSEL, 3),
    kNONE_to_SYSTICKCLK            = MUX_A(CM_STICKCLKSEL, 7),

    kFRO12M_to_MAIN_CLK  = MUX_A(CM_MAINCLKSELA, 0) | MUX_B(CM_MAINCLKSELB, 0, 0),
    kEXT_CLK_to_MAIN_CLK = MUX_A(CM_MAINCLKSELA, 1) | MUX_B(CM_MAINCLKSELB, 0, 0),
    kWDT_OSC_to_MAIN_CLK = MUX_A(CM_MAINCLKSELA, 2) | MUX_B(CM_MAINCLKSELB, 0, 0),
    kFRO_HF_to_MAIN_CLK  = MUX_A(CM_MAINCLKSELA, 3) | MUX_B(CM_MAINCLKSELB, 0, 0),
    kSYS_PLL_to_MAIN_CLK = MUX_A(CM_MAINCLKSELA, 0) | MUX_B(CM_MAINCLKSELB, 2, 0),
    kOSC32K_to_MAIN_CLK  = MUX_A(CM_MAINCLKSELA, 0) | MUX_B(CM_MAINCLKSELB, 3, 0),

    kMAIN_CLK_to_CLKOUT   = MUX_A(CM_CLKOUTCLKSELA, 0),
    kEXT_CLK_to_CLKOUT    = MUX_A(CM_CLKOUTCLKSELA, 1),
    kWDT_OSC_to_CLKOUT    = MUX_A(CM_CLKOUTCLKSELA, 2),
    kFRO_HF_to_CLKOUT     = MUX_A(CM_CLKOUTCLKSELA, 3),
    kSYS_PLL_to_CLKOUT    = MUX_A(CM_CLKOUTCLKSELA, 4),
    kUSB_PLL_to_CLKOUT    = MUX_A(CM_CLKOUTCLKSELA, 5),
    kAUDIO_PLL_to_CLKOUT  = MUX_A(CM_CLKOUTCLKSELA, 6),
    kOSC32K_OSC_to_CLKOUT = MUX_A(CM_CLKOUTCLKSELA, 7),

    kFRO12M_to_SYS_PLL  = MUX_A(CM_SYSPLLCLKSEL, 0),
    kEXT_CLK_to_SYS_PLL = MUX_A(CM_SYSPLLCLKSEL, 1),
    kWDT_OSC_to_SYS_PLL = MUX_A(CM_SYSPLLCLKSEL, 2),
    kOSC32K_to_SYS_PLL  = MUX_A(CM_SYSPLLCLKSEL, 3),
    kNONE_to_SYS_PLL    = MUX_A(CM_SYSPLLCLKSEL, 7),

    kFRO12M_to_AUDIO_PLL  = MUX_A(CM_AUDPLLCLKSEL, 0),
    kEXT_CLK_to_AUDIO_PLL = MUX_A(CM_AUDPLLCLKSEL, 1),
    kNONE_to_AUDIO_PLL    = MUX_A(CM_AUDPLLCLKSEL, 7),

    kMAIN_CLK_to_SPIFI_CLK  = MUX_A(CM_SPIFICLKSEL, 0),
    kSYS_PLL_to_SPIFI_CLK   = MUX_A(CM_SPIFICLKSEL, 1),
    kUSB_PLL_to_SPIFI_CLK   = MUX_A(CM_SPIFICLKSEL, 2),
    kFRO_HF_to_SPIFI_CLK    = MUX_A(CM_SPIFICLKSEL, 3),
    kAUDIO_PLL_to_SPIFI_CLK = MUX_A(CM_SPIFICLKSEL, 4),
    kNONE_to_SPIFI_CLK      = MUX_A(CM_SPIFICLKSEL, 7),

    kFRO_HF_to_ADC_CLK    = MUX_A(CM_ADCASYNCCLKSEL, 0),
    kSYS_PLL_to_ADC_CLK   = MUX_A(CM_ADCASYNCCLKSEL, 1),
    kUSB_PLL_to_ADC_CLK   = MUX_A(CM_ADCASYNCCLKSEL, 2),
    kAUDIO_PLL_to_ADC_CLK = MUX_A(CM_ADCASYNCCLKSEL, 3),
    kNONE_to_ADC_CLK      = MUX_A(CM_ADCASYNCCLKSEL, 7),

    kFRO_HF_to_USB0_CLK  = MUX_A(CM_USB0CLKSEL, 0),
    kSYS_PLL_to_USB0_CLK = MUX_A(CM_USB0CLKSEL, 1),
    kUSB_PLL_to_USB0_CLK = MUX_A(CM_USB0CLKSEL, 2),
    kNONE_to_USB0_CLK    = MUX_A(CM_USB0CLKSEL, 7),

    kFRO_HF_to_USB1_CLK  = MUX_A(CM_USB1CLKSEL, 0),
    kSYS_PLL_to_USB1_CLK = MUX_A(CM_USB1CLKSEL, 1),
    kUSB_PLL_to_USB1_CLK = MUX_A(CM_USB1CLKSEL, 2),
    kNONE_to_USB1_CLK    = MUX_A(CM_USB1CLKSEL, 7),

    kFRO12M_to_FLEXCOMM0    = MUX_A(CM_FXCOMCLKSEL0, 0),
    kFRO_HF_to_FLEXCOMM0    = MUX_A(CM_FXCOMCLKSEL0, 1),
    kAUDIO_PLL_to_FLEXCOMM0 = MUX_A(CM_FXCOMCLKSEL0, 2),
    kMCLK_to_FLEXCOMM0      = MUX_A(CM_FXCOMCLKSEL0, 3),
    kFRG_to_FLEXCOMM0       = MUX_A(CM_FXCOMCLKSEL0, 4),
    kNONE_to_FLEXCOMM0      = MUX_A(CM_FXCOMCLKSEL0, 7),

    kFRO12M_to_FLEXCOMM1    = MUX_A(CM_FXCOMCLKSEL1, 0),
    kFRO_HF_to_FLEXCOMM1    = MUX_A(CM_FXCOMCLKSEL1, 1),
    kAUDIO_PLL_to_FLEXCOMM1 = MUX_A(CM_FXCOMCLKSEL1, 2),
    kMCLK_to_FLEXCOMM1      = MUX_A(CM_FXCOMCLKSEL1, 3),
    kFRG_to_FLEXCOMM1       = MUX_A(CM_FXCOMCLKSEL1, 4),
    kNONE_to_FLEXCOMM1      = MUX_A(CM_FXCOMCLKSEL1, 7),

    kFRO12M_to_FLEXCOMM2    = MUX_A(CM_FXCOMCLKSEL2, 0),
    kFRO_HF_to_FLEXCOMM2    = MUX_A(CM_FXCOMCLKSEL2, 1),
    kAUDIO_PLL_to_FLEXCOMM2 = MUX_A(CM_FXCOMCLKSEL2, 2),
    kMCLK_to_FLEXCOMM2      = MUX_A(CM_FXCOMCLKSEL2, 3),
    kFRG_to_FLEXCOMM2       = MUX_A(CM_FXCOMCLKSEL2, 4),
    kNONE_to_FLEXCOMM2      = MUX_A(CM_FXCOMCLKSEL2, 7),

    kFRO12M_to_FLEXCOMM3    = MUX_A(CM_FXCOMCLKSEL3, 0),
    kFRO_HF_to_FLEXCOMM3    = MUX_A(CM_FXCOMCLKSEL3, 1),
    kAUDIO_PLL_to_FLEXCOMM3 = MUX_A(CM_FXCOMCLKSEL3, 2),
    kMCLK_to_FLEXCOMM3      = MUX_A(CM_FXCOMCLKSEL3, 3),
    kFRG_to_FLEXCOMM3       = MUX_A(CM_FXCOMCLKSEL3, 4),
    kNONE_to_FLEXCOMM3      = MUX_A(CM_FXCOMCLKSEL3, 7),

    kFRO12M_to_FLEXCOMM4    = MUX_A(CM_FXCOMCLKSEL4, 0),
    kFRO_HF_to_FLEXCOMM4    = MUX_A(CM_FXCOMCLKSEL4, 1),
    kAUDIO_PLL_to_FLEXCOMM4 = MUX_A(CM_FXCOMCLKSEL4, 2),
    kMCLK_to_FLEXCOMM4      = MUX_A(CM_FXCOMCLKSEL4, 3),
    kFRG_to_FLEXCOMM4       = MUX_A(CM_FXCOMCLKSEL4, 4),
    kNONE_to_FLEXCOMM4      = MUX_A(CM_FXCOMCLKSEL4, 7),

    kFRO12M_to_FLEXCOMM5    = MUX_A(CM_FXCOMCLKSEL5, 0),
    kFRO_HF_to_FLEXCOMM5    = MUX_A(CM_FXCOMCLKSEL5, 1),
    kAUDIO_PLL_to_FLEXCOMM5 = MUX_A(CM_FXCOMCLKSEL5, 2),
    kMCLK_to_FLEXCOMM5      = MUX_A(CM_FXCOMCLKSEL5, 3),
    kFRG_to_FLEXCOMM5       = MUX_A(CM_FXCOMCLKSEL5, 4),
    kNONE_to_FLEXCOMM5      = MUX_A(CM_FXCOMCLKSEL5, 7),

    kFRO12M_to_FLEXCOMM6    = MUX_A(CM_FXCOMCLKSEL6, 0),
    kFRO_HF_to_FLEXCOMM6    = MUX_A(CM_FXCOMCLKSEL6, 1),
    kAUDIO_PLL_to_FLEXCOMM6 = MUX_A(CM_FXCOMCLKSEL6, 2),
    kMCLK_to_FLEXCOMM6      = MUX_A(CM_FXCOMCLKSEL6, 3),
    kFRG_to_FLEXCOMM6       = MUX_A(CM_FXCOMCLKSEL6, 4),
    kNONE_to_FLEXCOMM6      = MUX_A(CM_FXCOMCLKSEL6, 7),

    kFRO12M_to_FLEXCOMM7    = MUX_A(CM_FXCOMCLKSEL7, 0),
    kFRO_HF_to_FLEXCOMM7    = MUX_A(CM_FXCOMCLKSEL7, 1),
    kAUDIO_PLL_to_FLEXCOMM7 = MUX_A(CM_FXCOMCLKSEL7, 2),
    kMCLK_to_FLEXCOMM7      = MUX_A(CM_FXCOMCLKSEL7, 3),
    kFRG_to_FLEXCOMM7       = MUX_A(CM_FXCOMCLKSEL7, 4),
    kNONE_to_FLEXCOMM7      = MUX_A(CM_FXCOMCLKSEL7, 7),

    kFRO12M_to_FLEXCOMM8    = MUX_A(CM_FXCOMCLKSEL8, 0),
    kFRO_HF_to_FLEXCOMM8    = MUX_A(CM_FXCOMCLKSEL8, 1),
    kAUDIO_PLL_to_FLEXCOMM8 = MUX_A(CM_FXCOMCLKSEL8, 2),
    kMCLK_to_FLEXCOMM8      = MUX_A(CM_FXCOMCLKSEL8, 3),
    kFRG_to_FLEXCOMM8       = MUX_A(CM_FXCOMCLKSEL8, 4),
    kNONE_to_FLEXCOMM8      = MUX_A(CM_FXCOMCLKSEL8, 7),

    kFRO12M_to_FLEXCOMM9    = MUX_A(CM_FXCOMCLKSEL9, 0),
    kFRO_HF_to_FLEXCOMM9    = MUX_A(CM_FXCOMCLKSEL9, 1),
    kAUDIO_PLL_to_FLEXCOMM9 = MUX_A(CM_FXCOMCLKSEL9, 2),
    kMCLK_to_FLEXCOMM9      = MUX_A(CM_FXCOMCLKSEL9, 3),
    kFRG_to_FLEXCOMM9       = MUX_A(CM_FXCOMCLKSEL9, 4),
    kNONE_to_FLEXCOMM9      = MUX_A(CM_FXCOMCLKSEL9, 7),

    kMAIN_CLK_to_FLEXCOMM10  = MUX_A(CM_FXCOMCLKSEL10, 0),
    kSYS_PLL_to_FLEXCOMM10   = MUX_A(CM_FXCOMCLKSEL10, 1),
    kUSB_PLL_to_FLEXCOMM10   = MUX_A(CM_FXCOMCLKSEL10, 2),
    kFRO_HF_to_FLEXCOMM10    = MUX_A(CM_FXCOMCLKSEL10, 3),
    kAUDIO_PLL_to_FLEXCOMM10 = MUX_A(CM_FXCOMCLKSEL10, 4),
    kNONE_to_FLEXCOMM10      = MUX_A(CM_FXCOMCLKSEL10, 7),

    kFRO_HF_to_MCLK    = MUX_A(CM_MCLKCLKSEL, 0),
    kAUDIO_PLL_to_MCLK = MUX_A(CM_MCLKCLKSEL, 1),
    kNONE_to_MCLK      = MUX_A(CM_MCLKCLKSEL, 7),

    kMAIN_CLK_to_FRG = MUX_A(CM_FRGCLKSEL, 0),
    kSYS_PLL_to_FRG  = MUX_A(CM_FRGCLKSEL, 1),
    kFRO12M_to_FRG   = MUX_A(CM_FRGCLKSEL, 2),
    kFRO_HF_to_FRG   = MUX_A(CM_FRGCLKSEL, 3),
    kNONE_to_FRG     = MUX_A(CM_FRGCLKSEL, 7),

    kFRO12M_to_DMIC     = MUX_A(CM_DMICCLKSEL, 0),
    kFRO_HF_DIV_to_DMIC = MUX_A(CM_DMICCLKSEL, 1),
    kAUDIO_PLL_to_DMIC  = MUX_A(CM_DMICCLKSEL, 2),
    kMCLK_to_DMIC       = MUX_A(CM_DMICCLKSEL, 3),
    kMAIN_CLK_to_DMIC   = MUX_A(CM_DMICCLKSEL, 4),
    kWDT_OSC_to_DMIC    = MUX_A(CM_DMICCLKSEL, 5),
    kNONE_to_DMIC       = MUX_A(CM_DMICCLKSEL, 7),

    kMAIN_CLK_to_SCT_CLK  = MUX_A(CM_SCTCLKSEL, 0),
    kSYS_PLL_to_SCT_CLK   = MUX_A(CM_SCTCLKSEL, 1),
    kFRO_HF_to_SCT_CLK    = MUX_A(CM_SCTCLKSEL, 2),
    kAUDIO_PLL_to_SCT_CLK = MUX_A(CM_SCTCLKSEL, 3),
    kNONE_to_SCT_CLK      = MUX_A(CM_SCTCLKSEL, 7),

    kMAIN_CLK_to_LCD_CLK = MUX_A(CM_LCDCLKSEL, 0),
    kLCDCLKIN_to_LCD_CLK = MUX_A(CM_LCDCLKSEL, 1),
    kFRO_HF_to_LCD_CLK   = MUX_A(CM_LCDCLKSEL, 2),
    kNONE_to_LCD_CLK     = MUX_A(CM_LCDCLKSEL, 3),

    kMAIN_CLK_to_SDIO_CLK  = MUX_A(CM_SDIOCLKSEL, 0),
    kSYS_PLL_to_SDIO_CLK   = MUX_A(CM_SDIOCLKSEL, 1),
    kUSB_PLL_to_SDIO_CLK   = MUX_A(CM_SDIOCLKSEL, 2),
    kFRO_HF_to_SDIO_CLK    = MUX_A(CM_SDIOCLKSEL, 3),
    kAUDIO_PLL_to_SDIO_CLK = MUX_A(CM_SDIOCLKSEL, 4),
    kNONE_to_SDIO_CLK      = MUX_A(CM_SDIOCLKSEL, 7),

    kMAIN_CLK_to_ASYNC_APB    = MUX_A(CM_ASYNCAPB, 0),
    kFRO12M_to_ASYNC_APB      = MUX_A(CM_ASYNCAPB, 1),
    kAUDIO_PLL_to_ASYNC_APB   = MUX_A(CM_ASYNCAPB, 2),
    kI2C_CLK_FC6_to_ASYNC_APB = MUX_A(CM_ASYNCAPB, 3),
    kNONE_to_NONE             = (int)0x80000000U,
} clock_attach_id_t;

/*  Clock dividers */
typedef enum _clock_div_name
{
    kCLOCK_DivSystickClk    = 0,
    kCLOCK_DivArmTrClkDiv   = 1,
    kCLOCK_DivCan0Clk       = 2,
    kCLOCK_DivCan1Clk       = 3,
    kCLOCK_DivSmartCard0Clk = 4,
    kCLOCK_DivSmartCard1Clk = 5,
    kCLOCK_DivAhbClk        = 32,
    kCLOCK_DivClkOut        = 33,
    kCLOCK_DivFrohfClk      = 34,
    kCLOCK_DivSpifiClk      = 36,
    kCLOCK_DivAdcAsyncClk   = 37,
    kCLOCK_DivUsb0Clk       = 38,
    kCLOCK_DivUsb1Clk       = 39,
    kCLOCK_DivFrg           = 40,
    kCLOCK_DivDmicClk       = 42,
    kCLOCK_DivMClk          = 43,
    kCLOCK_DivLcdClk        = 44,
    kCLOCK_DivSctClk        = 45,
    kCLOCK_DivEmcClk        = 46,
    kCLOCK_DivSdioClk       = 47
} clock_div_name_t;

/*******************************************************************************
 * API
 ******************************************************************************/

#if defined(__cplusplus)
extern "C" {
#endif /* __cplusplus */

static inline void CLOCK_EnableClock(clock_ip_name_t clk)
{
    uint32_t index = CLK_GATE_ABSTRACT_REG_OFFSET(clk);
    if (index < 3UL)
    {
        SYSCON->AHBCLKCTRLSET[index] = (1UL << CLK_GATE_ABSTRACT_BITS_SHIFT(clk));
    }
    else
    {
        SYSCON->ASYNCAPBCTRL             = SYSCON_ASYNCAPBCTRL_ENABLE(1);
        ASYNC_SYSCON->ASYNCAPBCLKCTRLSET = (1UL << CLK_GATE_ABSTRACT_BITS_SHIFT(clk));
    }
}

static inline void CLOCK_DisableClock(clock_ip_name_t clk)
{
    uint32_t index = CLK_GATE_ABSTRACT_REG_OFFSET(clk);
    if (index < 3UL)
    {
        SYSCON->AHBCLKCTRLCLR[index] = (1UL << CLK_GATE_ABSTRACT_BITS_SHIFT(clk));
    }
    else
    {
        ASYNC_SYSCON->ASYNCAPBCLKCTRLCLR = (1UL << CLK_GATE_ABSTRACT_BITS_SHIFT(clk));
        SYSCON->ASYNCAPBCTRL             = SYSCON_ASYNCAPBCTRL_ENABLE(0);
    }
}

/**
 * @brief
 *  Initialize the Core clock to given frequency (12, 48 or 96 MHz), this API is implememnt in ROM code.
 * Turns on FRO and uses default CCO, if freq is 12000000, then high speed output is off, else high speed
 * output is enabled.
 * Usage: CLOCK_SetupFROClocking(frequency), (frequency must be one of 12, 48 or 96 MHz)
 *  Note: Need to make sure ROM and OTP has power(PDRUNCFG0[17,29]= 0U) before calling this API since this API is
 * implemented in ROM code and the FROHF TRIM value is stored in OTP
 *
 * @param froFreq target fro frequency.
 * @return   Nothing
 */

void CLOCK_SetupFROClocking(uint32_t froFreq);

/**
 * @brief	Configure the clock selection muxes.
 * @param	connection	: Clock to be configured.
 * @return	Nothing
 */
void CLOCK_AttachClk(clock_attach_id_t connection);
/**
 * @brief   Get the actual clock attach id.
 * This fuction uses the offset in input attach id, then it reads the actual source value in
 * the register and combine the offset to obtain an actual attach id.
 * @param   attachId  : Clock attach id to get.
 * @return  Clock source value.
 */
clock_attach_id_t CLOCK_GetClockAttachId(clock_attach_id_t attachId);
/**
 * @brief	Setup peripheral clock dividers.
 * @param	div_name	: Clock divider name
 * @param divided_by_value: Value to be divided
 * @param reset :  Whether to reset the divider counter.
 * @return	Nothing
 */
void CLOCK_SetClkDiv(clock_div_name_t div_name, uint32_t divided_by_value, bool reset);

/*! @brief	Return Frequency of selected clock
 *  @return	Frequency of selected clock
 */
uint32_t CLOCK_GetFreq(clock_name_t clockName);
/*! @brief	Return Frequency of FRO 12MHz
 *  @return	Frequency of FRO 12MHz
 */
uint32_t CLOCK_GetFro12MFreq(void);
/*! @brief	Return Frequency of ClockOut
 *  @return	Frequency of ClockOut
 */
uint32_t CLOCK_GetClockOutClkFreq(void);
/*! @brief	Return Frequency of Spifi Clock
 *  @return	Frequency of Spifi.
 */
uint32_t CLOCK_GetSpifiClkFreq(void);
/*! @brief	Return Frequency of Adc Clock
 *  @return	Frequency of Adc Clock.
 */
uint32_t CLOCK_GetAdcClkFreq(void);
/*! brief	Return Frequency of MCAN Clock
 *  param	MCanSel : 0U: MCAN0; 1U: MCAN1
 *  return	Frequency of MCAN Clock
 */
uint32_t CLOCK_GetMCanClkFreq(uint32_t MCanSel);
/*! @brief	Return Frequency of Usb0 Clock
 *  @return	Frequency of Usb0 Clock.
 */
uint32_t CLOCK_GetUsb0ClkFreq(void);
/*! @brief	Return Frequency of Usb1 Clock
 *  @return	Frequency of Usb1 Clock.
 */
uint32_t CLOCK_GetUsb1ClkFreq(void);
/*! @brief	Return Frequency of MClk Clock
 *  @return	Frequency of MClk Clock.
 */
uint32_t CLOCK_GetMclkClkFreq(void);
/*! @brief	Return Frequency of SCTimer Clock
 *  @return	Frequency of SCTimer Clock.
 */
uint32_t CLOCK_GetSctClkFreq(void);
/*! @brief	Return Frequency of SDIO Clock
 *  @return	Frequency of SDIO Clock.
 */
uint32_t CLOCK_GetSdioClkFreq(void);
/*! @brief	Return Frequency of LCD Clock
 *  @return	Frequency of LCD Clock.
 */
uint32_t CLOCK_GetLcdClkFreq(void);
/*! @brief	Return Frequency of LCD CLKIN Clock
 *  @return	Frequency of LCD CLKIN Clock.
 */
uint32_t CLOCK_GetLcdClkIn(void);
/*! @brief	Return Frequency of External Clock
 *  @return	Frequency of External Clock. If no external clock is used returns 0.
 */
uint32_t CLOCK_GetExtClkFreq(void);
/*! @brief	Return Frequency of Watchdog Oscillator
 *  @return	Frequency of Watchdog Oscillator
 */
uint32_t CLOCK_GetWdtOscFreq(void);
/*! @brief	Return Frequency of High-Freq output of FRO
 *  @return	Frequency of High-Freq output of FRO
 */
uint32_t CLOCK_GetFroHfFreq(void);
/*! @brief  Return Frequency of frg
 *  @return Frequency of FRG
 */
uint32_t CLOCK_GetFrgClkFreq(void);
/*! @brief  Return Frequency of dmic
 *  @return Frequency of DMIC
 */
uint32_t CLOCK_GetDmicClkFreq(void);

/*!
 * @brief Set FRG Clk
 * @return
 *        1: if set FRG CLK successfully.
 *        0: if set FRG CLK fail.
 */
uint32_t CLOCK_SetFRGClock(uint32_t freq);

/*! @brief	Return Frequency of PLL
 *  @return	Frequency of PLL
 */
uint32_t CLOCK_GetPllOutFreq(void);
/*! @brief	Return Frequency of USB PLL
 *  @return	Frequency of PLL
 */
uint32_t CLOCK_GetUsbPllOutFreq(void);
/*! @brief	Return Frequency of AUDIO PLL
 *  @return	Frequency of PLL
 */
uint32_t CLOCK_GetAudioPllOutFreq(void);
/*! @brief	Return Frequency of 32kHz osc
 *  @return	Frequency of 32kHz osc
 */
uint32_t CLOCK_GetOsc32KFreq(void);
/*! @brief	Return Frequency of Core System
 *  @return	Frequency of Core System
 */
uint32_t CLOCK_GetCoreSysClkFreq(void);
/*! @brief	Return Frequency of I2S MCLK Clock
 *  @return	Frequency of I2S MCLK Clock
 */
uint32_t CLOCK_GetI2SMClkFreq(void);
/*! @brief	Return Frequency of Flexcomm functional Clock
 *  @return	Frequency of Flexcomm functional Clock
 */
uint32_t CLOCK_GetFlexCommClkFreq(uint32_t id);

/*! @brief return FRG Clk
 *  @return Frequency of FRG CLK.
 */
uint32_t CLOCK_GetFRGInputClock(void);
/*! @brief	Return Asynchronous APB Clock source
 *  @return	Asynchronous APB CLock source
 */
__STATIC_INLINE async_clock_src_t CLOCK_GetAsyncApbClkSrc(void)
{
    return (async_clock_src_t)(uint32_t)(ASYNC_SYSCON->ASYNCAPBCLKSELA & 0x3U);
}
/*! @brief	Return Frequency of Asynchronous APB Clock
 *  @return	Frequency of Asynchronous APB Clock Clock
 */
uint32_t CLOCK_GetAsyncApbClkFreq(void);
/*! @brief	Return EMC source
 *  @return	EMC source
 */
__STATIC_INLINE uint32_t CLOCK_GetEmcClkFreq(void)
{
    uint32_t freqtmp;

    freqtmp = CLOCK_GetCoreSysClkFreq() / ((SYSCON->AHBCLKDIV & 0xffU) + 1U);
    return freqtmp / ((SYSCON->EMCCLKDIV & 0xffU) + 1U);
}
/*! @brief	Return Audio PLL input clock rate
 *  @return	Audio PLL input clock rate
 */
uint32_t CLOCK_GetAudioPLLInClockRate(void);
/*! @brief	Return System PLL input clock rate
 *  @return	System PLL input clock rate
 */
uint32_t CLOCK_GetSystemPLLInClockRate(void);

/*! @brief	Return System PLL output clock rate
 *  @param	recompute	: Forces a PLL rate recomputation if true
 *  @return	System PLL output clock rate
 *  @note	The PLL rate is cached in the driver in a variable as
 *  the rate computation function can take some time to perform. It
 *  is recommended to use 'false' with the 'recompute' parameter.
 */
uint32_t CLOCK_GetSystemPLLOutClockRate(bool recompute);

/*! @brief	Return System AUDIO PLL output clock rate
 *  @param	recompute	: Forces a AUDIO PLL rate recomputation if true
 *  @return	System AUDIO PLL output clock rate
 *  @note	The AUDIO PLL rate is cached in the driver in a variable as
 *  the rate computation function can take some time to perform. It
 *  is recommended to use 'false' with the 'recompute' parameter.
 */
uint32_t CLOCK_GetAudioPLLOutClockRate(bool recompute);

/*! @brief	Return System USB PLL output clock rate
 *  @param	recompute	: Forces a USB PLL rate recomputation if true
 *  @return	System USB PLL output clock rate
 *  @note	The USB PLL rate is cached in the driver in a variable as
 *  the rate computation function can take some time to perform. It
 *  is recommended to use 'false' with the 'recompute' parameter.
 */
uint32_t CLOCK_GetUsbPLLOutClockRate(bool recompute);

/*! @brief	Enables and disables PLL bypass mode
 *  @brief	bypass	: true to bypass PLL (PLL output = PLL input, false to disable bypass
 *  @return	System PLL output clock rate
 */
__STATIC_INLINE void CLOCK_SetBypassPLL(bool bypass)
{
    if (bypass)
    {
        SYSCON->SYSPLLCTRL |= (1UL << SYSCON_SYSPLLCTRL_BYPASS_SHIFT);
    }
    else
    {
        SYSCON->SYSPLLCTRL &= ~(1UL << SYSCON_SYSPLLCTRL_BYPASS_SHIFT);
    }
}

/*! @brief	Check if PLL is locked or not
 *  @return	true if the PLL is locked, false if not locked
 */
__STATIC_INLINE bool CLOCK_IsSystemPLLLocked(void)
{
    return (bool)((SYSCON->SYSPLLSTAT & SYSCON_SYSPLLSTAT_LOCK_MASK) != 0U);
}

/*! @brief	Check if USB PLL is locked or not
 *  @return	true if the USB PLL is locked, false if not locked
 */
__STATIC_INLINE bool CLOCK_IsUsbPLLLocked(void)
{
    return (bool)((SYSCON->USBPLLSTAT & SYSCON_USBPLLSTAT_LOCK_MASK) != 0U);
}

/*! @brief	Check if AUDIO PLL is locked or not
 *  @return	true if the AUDIO PLL is locked, false if not locked
 */
__STATIC_INLINE bool CLOCK_IsAudioPLLLocked(void)
{
    return (bool)((SYSCON->AUDPLLSTAT & SYSCON_AUDPLLSTAT_LOCK_MASK) != 0U);
}

/*! @brief	Enables and disables SYS OSC
 *  @brief	enable	: true to enable SYS OSC, false to disable SYS OSC
 */
__STATIC_INLINE void CLOCK_Enable_SysOsc(bool enable)
{
    if (enable)
    {
        SYSCON->PDRUNCFGCLR[0] |= SYSCON_PDRUNCFG_PDEN_VD2_ANA_MASK;
        SYSCON->PDRUNCFGCLR[1] |= SYSCON_PDRUNCFG_PDEN_SYSOSC_MASK;
    }

    else
    {
        SYSCON->PDRUNCFGSET[0] = SYSCON_PDRUNCFG_PDEN_VD2_ANA_MASK;
        SYSCON->PDRUNCFGSET[1] = SYSCON_PDRUNCFG_PDEN_SYSOSC_MASK;
    }
}

/*! @brief Store the current PLL rate
 *  @param	rate: Current rate of the PLL
 *  @return	Nothing
 **/
void CLOCK_SetStoredPLLClockRate(uint32_t rate);

/*! @brief Store the current AUDIO PLL rate
 *  @param	rate: Current rate of the PLL
 *  @return	Nothing
 **/
void CLOCK_SetStoredAudioPLLClockRate(uint32_t rate);

/*! @brief PLL configuration structure flags for 'flags' field
 * These flags control how the PLL configuration function sets up the PLL setup structure.<br>
 *
 * When the PLL_CONFIGFLAG_USEINRATE flag is selected, the 'InputRate' field in the
 * configuration structure must be assigned with the expected PLL frequency. If the
 * PLL_CONFIGFLAG_USEINRATE is not used, 'InputRate' is ignored in the configuration
 * function and the driver will determine the PLL rate from the currently selected
 * PLL source. This flag might be used to configure the PLL input clock more accurately
 * when using the WDT oscillator or a more dyanmic CLKIN source.<br>
 *
 * When the PLL_CONFIGFLAG_FORCENOFRACT flag is selected, the PLL hardware for the
 * automatic bandwidth selection, Spread Spectrum (SS) support, and fractional M-divider
 * are not used.<br>
 */
#define PLL_CONFIGFLAG_USEINRATE (1U << 0U) /*!< Flag to use InputRate in PLL configuration structure for setup */
#define PLL_CONFIGFLAG_FORCENOFRACT                                                                                   \
    (1U << 2U) /*!< Force non-fractional output mode, PLL output will not use the fractional, automatic bandwidth, or \
                  SS hardware */

/*! @brief PLL configuration structure
 *
 * This structure can be used to configure the settings for a PLL
 * setup structure. Fill in the desired configuration for the PLL
 * and call the PLL setup function to fill in a PLL setup structure.
 */
typedef struct _pll_config
{
    uint32_t desiredRate; /*!< Desired PLL rate in Hz */
    uint32_t inputRate;   /*!< PLL input clock in Hz, only used if PLL_CONFIGFLAG_USEINRATE flag is set */
    uint32_t flags;       /*!< PLL configuration flags, Or'ed value of PLL_CONFIGFLAG_* definitions */
} pll_config_t;

/*! @brief PLL setup structure flags for 'flags' field
 * These flags control how the PLL setup function sets up the PLL
 */
#define PLL_SETUPFLAG_POWERUP (1U << 0U)  /*!< Setup will power on the PLL after setup */
#define PLL_SETUPFLAG_WAITLOCK (1U << 1U) /*!< Setup will wait for PLL lock, implies the PLL will be pwoered on */
#define PLL_SETUPFLAG_ADGVOLT (1U << 2U)  /*!< Optimize system voltage for the new PLL rate */

/*! @brief PLL setup structure
 * This structure can be used to pre-build a PLL setup configuration
 * at run-time and quickly set the PLL to the configuration. It can be
 * populated with the PLL setup function. If powering up or waiting
 * for PLL lock, the PLL input clock source should be configured prior
 * to PLL setup.
 */
typedef struct _pll_setup
{
    uint32_t pllctrl;    /*!< PLL control register SYSPLLCTRL */
    uint32_t pllndec;    /*!< PLL NDEC register SYSPLLNDEC */
    uint32_t pllpdec;    /*!< PLL PDEC register SYSPLLPDEC */
    uint32_t pllmdec;    /*!< PLL MDEC registers SYSPLLPDEC */
    uint32_t pllRate;    /*!< Acutal PLL rate */
    uint32_t audpllfrac; /*!< only aduio PLL has this function*/
    uint32_t flags;      /*!< PLL setup flags, Or'ed value of PLL_SETUPFLAG_* definitions */
} pll_setup_t;

/*! @brief PLL status definitions
 */
typedef enum _pll_error
{
    kStatus_PLL_Success         = MAKE_STATUS(kStatusGroup_Generic, 0), /*!< PLL operation was successful */
    kStatus_PLL_OutputTooLow    = MAKE_STATUS(kStatusGroup_Generic, 1), /*!< PLL output rate request was too low */
    kStatus_PLL_OutputTooHigh   = MAKE_STATUS(kStatusGroup_Generic, 2), /*!< PLL output rate request was too high */
    kStatus_PLL_InputTooLow     = MAKE_STATUS(kStatusGroup_Generic, 3), /*!< PLL input rate is too low */
    kStatus_PLL_InputTooHigh    = MAKE_STATUS(kStatusGroup_Generic, 4), /*!< PLL input rate is too high */
    kStatus_PLL_OutsideIntLimit = MAKE_STATUS(kStatusGroup_Generic, 5), /*!< Requested output rate isn't possible */
    kStatus_PLL_CCOTooLow       = MAKE_STATUS(kStatusGroup_Generic, 6), /*!< Requested CCO rate isn't possible */
    kStatus_PLL_CCOTooHigh      = MAKE_STATUS(kStatusGroup_Generic, 7)  /*!< Requested CCO rate isn't possible */
} pll_error_t;

/*! @brief USB clock source definition. */
typedef enum _clock_usb_src
{
    kCLOCK_UsbSrcFro       = (uint32_t)kCLOCK_FroHf,      /*!< Use FRO 96 or 48 MHz. */
    kCLOCK_UsbSrcSystemPll = (uint32_t)kCLOCK_PllOut,     /*!< Use System PLL output. */
    kCLOCK_UsbSrcMainClock = (uint32_t)kCLOCK_CoreSysClk, /*!< Use Main clock.    */
    kCLOCK_UsbSrcUsbPll    = (uint32_t)kCLOCK_UsbPll,     /*!< Use USB PLL clock.    */

    kCLOCK_UsbSrcNone = SYSCON_USB0CLKSEL_SEL(
        7U) /*!< Use None, this may be selected in order to reduce power when no output is needed.. */
} clock_usb_src_t;

/*! @brief USB PDEL Divider. */
typedef enum _usb_pll_psel
{
    pSel_Divide_1 = 0U,
    pSel_Divide_2,
    pSel_Divide_4,
    pSel_Divide_8
} usb_pll_psel;

/*! @brief PLL setup structure
 * This structure can be used to pre-build a USB PLL setup configuration
 * at run-time and quickly set the usb PLL to the configuration. It can be
 * populated with the USB PLL setup function. If powering up or waiting
 * for USB PLL lock, the PLL input clock source should be configured prior
 * to USB PLL setup.
 */
typedef struct _usb_pll_setup
{
    uint8_t msel;       /*!< USB PLL control register msel:1U-256U */
    uint8_t psel;       /*!< USB PLL control register psel:only support inter 1U 2U 4U 8U */
    uint8_t nsel;       /*!< USB PLL control register nsel:only suppoet inter 1U 2U 3U 4U */
    bool direct;        /*!< USB PLL CCO output control */
    bool bypass;        /*!< USB PLL inout clock bypass control  */
    bool fbsel;         /*!< USB PLL ineter mode and non-integer mode control*/
    uint32_t inputRate; /*!< USB PLL input rate */
} usb_pll_setup_t;

/*! @brief	Return System PLL output clock rate from setup structure
 *  @param	pSetup	: Pointer to a PLL setup structure
 *  @return	System PLL output clock rate the setup structure will generate
 */
uint32_t CLOCK_GetSystemPLLOutFromSetup(pll_setup_t *pSetup);

/*! @brief	Return System AUDIO PLL output clock rate from setup structure
 *  @param	pSetup	: Pointer to a PLL setup structure
 *  @return	System PLL output clock rate the setup structure will generate
 */
uint32_t CLOCK_GetAudioPLLOutFromSetup(pll_setup_t *pSetup);

/*! @brief	Return System AUDIO PLL output clock rate from audio fractioanl setup structure
 *  @param	pSetup	: Pointer to a PLL setup structure
 *  @return	System PLL output clock rate the setup structure will generate
 */
uint32_t CLOCK_GetAudioPLLOutFromFractSetup(pll_setup_t *pSetup);

/*! @brief	Return System USB PLL output clock rate from setup structure
 *  @param	pSetup	: Pointer to a PLL setup structure
 *  @return	System PLL output clock rate the setup structure will generate
 */
uint32_t CLOCK_GetUsbPLLOutFromSetup(const usb_pll_setup_t *pSetup);

/*! @brief	Set PLL output based on the passed PLL setup data
 *  @param	pControl	: Pointer to populated PLL control structure to generate setup with
 *  @param	pSetup		: Pointer to PLL setup structure to be filled
 *  @return	PLL_ERROR_SUCCESS on success, or PLL setup error code
 *  @note	Actual frequency for setup may vary from the desired frequency based on the
 *  accuracy of input clocks, rounding, non-fractional PLL mode, etc.
 */
pll_error_t CLOCK_SetupPLLData(pll_config_t *pControl, pll_setup_t *pSetup);

/*! @brief	Set AUDIO PLL output based on the passed AUDIO PLL setup data
 *  @param	pControl	: Pointer to populated PLL control structure to generate setup with
 *  @param	pSetup		: Pointer to PLL setup structure to be filled
 *  @return	PLL_ERROR_SUCCESS on success, or PLL setup error code
 *  @note	Actual frequency for setup may vary from the desired frequency based on the
 *  accuracy of input clocks, rounding, non-fractional PLL mode, etc.
 */
pll_error_t CLOCK_SetupAudioPLLData(pll_config_t *pControl, pll_setup_t *pSetup);

/*! @brief	Set PLL output from PLL setup structure (precise frequency)
 * @param	pSetup	: Pointer to populated PLL setup structure
 * @param flagcfg : Flag configuration for PLL config structure
 * @return	PLL_ERROR_SUCCESS on success, or PLL setup error code
 * @note	This function will power off the PLL, setup the PLL with the
 * new setup data, and then optionally powerup the PLL, wait for PLL lock,
 * and adjust system voltages to the new PLL rate. The function will not
 * alter any source clocks (ie, main systen clock) that may use the PLL,
 * so these should be setup prior to and after exiting the function.
 */
pll_error_t CLOCK_SetupSystemPLLPrec(pll_setup_t *pSetup, uint32_t flagcfg);

/*! @brief	Set AUDIO PLL output from AUDIOPLL setup structure (precise frequency)
 * @param	pSetup	: Pointer to populated PLL setup structure
 * @param flagcfg : Flag configuration for PLL config structure
 * @return	PLL_ERROR_SUCCESS on success, or PLL setup error code
 * @note	This function will power off the PLL, setup the PLL with the
 * new setup data, and then optionally powerup the AUDIO PLL, wait for PLL lock,
 * and adjust system voltages to the new AUDIOPLL rate. The function will not
 * alter any source clocks (ie, main systen clock) that may use the AUDIO PLL,
 * so these should be setup prior to and after exiting the function.
 */
pll_error_t CLOCK_SetupAudioPLLPrec(pll_setup_t *pSetup, uint32_t flagcfg);

/*! @brief	Set AUDIO PLL output from AUDIOPLL setup structure using the Audio Fractional divider register(precise
 * frequency)
 * @param	pSetup	: Pointer to populated PLL setup structure
 * @param flagcfg : Flag configuration for PLL config structure
 * @return	PLL_ERROR_SUCCESS on success, or PLL setup error code
 * @note	This function will power off the PLL, setup the PLL with the
 * new setup data, and then optionally powerup the AUDIO PLL, wait for PLL lock,
 * and adjust system voltages to the new AUDIOPLL rate. The function will not
 * alter any source clocks (ie, main systen clock) that may use the AUDIO PLL,
 * so these should be setup prior to and after exiting the function.
 */
pll_error_t CLOCK_SetupAudioPLLPrecFract(pll_setup_t *pSetup, uint32_t flagcfg);

/**
 * @brief	Set PLL output from PLL setup structure (precise frequency)
 * @param	pSetup	: Pointer to populated PLL setup structure
 * @return	kStatus_PLL_Success on success, or PLL setup error code
 * @note	This function will power off the PLL, setup the PLL with the
 * new setup data, and then optionally powerup the PLL, wait for PLL lock,
 * and adjust system voltages to the new PLL rate. The function will not
 * alter any source clocks (ie, main systen clock) that may use the PLL,
 * so these should be setup prior to and after exiting the function.
 */
pll_error_t CLOCK_SetPLLFreq(const pll_setup_t *pSetup);

/**
 * @brief	Set Audio PLL output from Audio PLL setup structure (precise frequency)
 * @param	pSetup	: Pointer to populated PLL setup structure
 * @return	kStatus_PLL_Success on success, or Audio PLL setup error code
 * @note	This function will power off the PLL, setup the Audio PLL with the
 * new setup data, and then optionally powerup the PLL, wait for Audio PLL lock,
 * and adjust system voltages to the new PLL rate. The function will not
 * alter any source clocks (ie, main systen clock) that may use the Audio PLL,
 * so these should be setup prior to and after exiting the function.
 */
pll_error_t CLOCK_SetAudioPLLFreq(const pll_setup_t *pSetup);

/**
 * @brief	Set USB PLL output from USB PLL setup structure (precise frequency)
 * @param	pSetup	: Pointer to populated USB PLL setup structure
 * @return	kStatus_PLL_Success on success, or USB PLL setup error code
 * @note	This function will power off the USB PLL, setup the PLL with the
 * new setup data, and then optionally powerup the USB PLL, wait for USB PLL lock,
 * and adjust system voltages to the new USB PLL rate. The function will not
 * alter any source clocks (ie, usb pll clock) that may use the USB PLL,
 * so these should be setup prior to and after exiting the function.
 */
pll_error_t CLOCK_SetUsbPLLFreq(const usb_pll_setup_t *pSetup);

/*! @brief	Set PLL output based on the multiplier and input frequency
 * @param	multiply_by	: multiplier
 * @param	input_freq	: Clock input frequency of the PLL
 * @return	Nothing
 * @note	Unlike the Chip_Clock_SetupSystemPLLPrec() function, this
 * function does not disable or enable PLL power, wait for PLL lock,
 * or adjust system voltages. These must be done in the application.
 * The function will not alter any source clocks (ie, main systen clock)
 * that may use the PLL, so these should be setup prior to and after
 * exiting the function.
 */
void CLOCK_SetupSystemPLLMult(uint32_t multiply_by, uint32_t input_freq);

/*! @brief Disable USB clock.
 *
 * Disable USB clock.
 */
static inline void CLOCK_DisableUsbDevicefs0Clock(clock_ip_name_t clk)
{
    CLOCK_DisableClock(clk);
}

/*! @brief Enable USB Device FS clock.
 * @param	src	: clock source
 * @param	freq: clock frequency
 * Enable USB Device Full Speed clock.
 */
bool CLOCK_EnableUsbfs0DeviceClock(clock_usb_src_t src, uint32_t freq);

/*! @brief Enable USB HOST FS clock.
 * @param	src	: clock source
 * @param	freq: clock frequency
 * Enable USB HOST Full Speed clock.
 */
bool CLOCK_EnableUsbfs0HostClock(clock_usb_src_t src, uint32_t freq);

/*! @brief Set the current Usb PLL Rate
 */
void CLOCK_SetStoredUsbPLLClockRate(uint32_t rate);

/*! @brief Enable USB Device HS clock.
 * @param	src	: clock source
 * @param	freq: clock frequency
 * Enable USB Device High Speed clock.
 */
bool CLOCK_EnableUsbhs0DeviceClock(clock_usb_src_t src, uint32_t freq);

/*! @brief Enable USB HOST HS clock.
 * @param	src	: clock source
 * @param	freq: clock frequency
 * Enable USB HOST High Speed clock.
 */
bool CLOCK_EnableUsbhs0HostClock(clock_usb_src_t src, uint32_t freq);

#if defined(__cplusplus)
}
#endif /* __cplusplus */

/*! @} */

#endif /* _FSL_CLOCK_H_ */
