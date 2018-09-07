/*
 * Copyright (c) 2016, Texas Instruments Incorporated
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * *  Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *
 * *  Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * *  Neither the name of Texas Instruments Incorporated nor the names of
 *    its contributors may be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO,
 * THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 * PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR
 * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS;
 * OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
 * WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR
 * OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */
/** ============================================================================
 *  @file       C3220SF_LAUNCHXL.h
 *
 *  @brief      CC3220 Board Specific APIs
 *
 *  The CC3220SF_LAUNCHXL header file should be included in an application as
 *  follows:
 *  @code
 *  #include <CC3220SF_LAUNCHXL.h>
 *  @endcode
 *
 *  ============================================================================
 */
#ifndef __CC3220SF_LAUNCHXL_H
#define __CC3220SF_LAUNCHXL_H

#ifdef __cplusplus
extern "C" {
#endif

#define CC3220SF_LAUNCHXL_GPIO_LED_OFF (0)
#define CC3220SF_LAUNCHXL_GPIO_LED_ON  (1)

/*!
 *  @def    CC3220SF_LAUNCHXL_ADCName
 *  @brief  Enum of ADC names on the CC3220SF_LAUNCHXL dev board
 */
typedef enum CC3220SF_LAUNCHXL_ADCName {
    CC3220SF_LAUNCHXL_ADC0 = 0,
    CC3220SF_LAUNCHXL_ADC1,

    CC3220SF_LAUNCHXL_ADCCOUNT
} CC3220SF_LAUNCHXL_ADCName;

/*!
 *  @def    CC3220SF_LAUNCHXL_CryptoName
 *  @brief  Enum of Crypto names on the CC3220SF_LAUNCHXL dev board
 */
typedef enum CC3220SF_LAUNCHXL_CryptoName {
    CC3220SF_LAUNCHXL_CRYPTO0 = 0,

    CC3220SF_LAUNCHXL_CRYPTOCOUNT
} CC3220SF_LAUNCHXL_CryptoName;

/*!
 *  @def    CC3220SF_LAUNCHXL_GPIOName
 *  @brief  Enum of GPIO names on the CC3220SF_LAUNCHXL dev board
 */
typedef enum CC3220SF_LAUNCHXL_GPIOName {
    CC3220SF_LAUNCHXL_GPIO_SW2 = 0,
    CC3220SF_LAUNCHXL_GPIO_SW3,
    CC3220SF_LAUNCHXL_GPIO_LED_D7,

    /*
     *  CC3220SF_LAUNCHXL_GPIO_LED_D5 and CC3220SF_LAUNCHXL_GPIO_LED_D6 are shared with the
     *  I2C and PWM peripherals. In order for those examples to work, these
     *  LEDs are  taken out of gpioPinCOnfig[]
     */
    //CC3220SF_LAUNCHXL_GPIO_LED_D6,
    //CC3220SF_LAUNCHXL_GPIO_LED_D5,

    CC3220SF_LAUNCHXL_GPIOCOUNT
} CC3220SF_LAUNCHXL_GPIOName;

/*!
 *  @def    CC3220SF_LAUNCHXL_I2CName
 *  @brief  Enum of I2C names on the CC3220SF_LAUNCHXL dev board
 */
typedef enum CC3220SF_LAUNCHXL_I2CName {
    CC3220SF_LAUNCHXL_I2C0 = 0,

    CC3220SF_LAUNCHXL_I2CCOUNT
} CC3220SF_LAUNCHXL_I2CName;

/*!
 *  @def    CC3220SF_LAUNCHXL_I2SName
 *  @brief  Enum of I2S names on the CC3220SF_LAUNCHXL dev board
 */
typedef enum CC3220SF_LAUNCHXL_I2SName {
    CC3220SF_LAUNCHXL_I2S0 = 0,

    CC3220SF_LAUNCHXL_I2SCOUNT
} CC3220SF_LAUNCHXL_I2SName;

/*!
 *  @def    CC3220SF_LAUNCHXL_PWMName
 *  @brief  Enum of PWM names on the CC3220SF_LAUNCHXL dev board
 */
typedef enum CC3220SF_LAUNCHXL_PWMName {
    CC3220SF_LAUNCHXL_PWM6 = 0,
    CC3220SF_LAUNCHXL_PWM7,

    CC3220SF_LAUNCHXL_PWMCOUNT
} CC3220SF_LAUNCHXL_PWMName;

/*!
 *  @def    CC3220SF_LAUNCHXL_SDFatFSName
 *  @brief  Enum of SDFatFS names on the CC3220SF_LAUNCHXL dev board
 */
typedef enum CC3220SF_LAUNCHXL_SDFatFSName {
    CC3220SF_LAUNCHXL_SDFatFS0 = 0,

    CC3220SF_LAUNCHXL_SDFatFSCOUNT
} CC3220SF_LAUNCHXL_SDFatFSName;

/*!
 *  @def    CC3220SF_LAUNCHXL_SDName
 *  @brief  Enum of SD names on the CC3220SF_LAUNCHXL dev board
 */
typedef enum CC3220SF_LAUNCHXL_SDName {
    CC3220SF_LAUNCHXL_SD0 = 0,

    CC3220SF_LAUNCHXL_SDCOUNT
} CC3220SF_LAUNCHXL_SDName;
/*!
 *  @def    CC3220SF_LAUNCHXL_SDSPIName
 *  @brief  Enum of SDSPI names on the CC3220SF_LAUNCHXL dev board
 */
typedef enum CC3220SF_LAUNCHXL_SDSPIName {
    CC3220SF_LAUNCHXL_SDSPI0 = 0,

    CC3220SF_LAUNCHXL_SDSPICOUNT
} CC3220SF_LAUNCHXL_SDSPIName;

/*!
 *  @def    CC3220SF_LAUNCHXL_SPIName
 *  @brief  Enum of SPI names on the CC3220SF_LAUNCHXL dev board
 */
typedef enum CC3220SF_LAUNCHXL_SPIName {
    CC3220SF_LAUNCHXL_SPI0 = 0,
    CC3220SF_LAUNCHXL_SPI1,

    CC3220SF_LAUNCHXL_SPICOUNT
} CC3220SF_LAUNCHXL_SPIName;

/*!
 *  @def    CC3220SF_LAUNCHXL_UARTName
 *  @brief  Enum of UARTs on the CC3220SF_LAUNCHXL dev board
 */
typedef enum CC3220SF_LAUNCHXL_UARTName {
    CC3220SF_LAUNCHXL_UART0 = 0,
    CC3220SF_LAUNCHXL_UART1,

    CC3220SF_LAUNCHXL_UARTCOUNT
} CC3220SF_LAUNCHXL_UARTName;

/*!
 *  @def    CC3220SF_LAUNCHXL_WatchdogName
 *  @brief  Enum of Watchdogs on the CC3220SF_LAUNCHXL dev board
 */
typedef enum CC3220SF_LAUNCHXL_WatchdogName {
    CC3220SF_LAUNCHXL_WATCHDOG0 = 0,

    CC3220SF_LAUNCHXL_WATCHDOGCOUNT
} CC3220SF_LAUNCHXL_WatchdogName;

/*!
 *  @brief  Initialize the general board specific settings
 *
 *  This function initializes the general board specific settings.
 */
extern void CC3220SF_LAUNCHXL_initGeneral(void);

#ifdef __cplusplus
}
#endif

#endif /* __CC3220SF_LAUNCHXL_H */
