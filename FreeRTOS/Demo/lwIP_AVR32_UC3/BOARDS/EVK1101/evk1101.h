/*This file is prepared for Doxygen automatic documentation generation.*/
/*! \file *********************************************************************
 *
 * \brief AT32UC3B EVK1101 board header file.
 *
 * This file contains definitions and services related to the features of the
 * EVK1101 board.
 *
 * - Compiler:           IAR EWAVR32 and GNU GCC for AVR32
 * - Supported devices:  All AVR32 AT32UC3B devices can be used.
 * - AppNote:
 *
 * \author               Atmel Corporation: http://www.atmel.com \n
 *                       Support and FAQ: http://support.atmel.no/
 *
 ******************************************************************************/

/* Copyright (c) 2007, Atmel Corporation All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 * this list of conditions and the following disclaimer in the documentation
 * and/or other materials provided with the distribution.
 *
 * 3. The name of ATMEL may not be used to endorse or promote products derived
 * from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY ATMEL ``AS IS'' AND ANY EXPRESS OR IMPLIED
 * WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE EXPRESSLY AND
 * SPECIFICALLY DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT,
 * INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
 * ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
 * THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */


#ifndef _EVK1101_H_
#define _EVK1101_H_

#include "compiler.h"

#ifdef __AVR32_ABI_COMPILER__ // Automatically defined when compiling for AVR32, not when assembling.
#  include "led.h"
#endif  // __AVR32_ABI_COMPILER__


/*! \name Oscillator Definitions
 */
//! @{

// RCOsc has no custom calibration by default. Set the following definition to
// the appropriate value if a custom RCOsc calibration has been applied to your
// part.
//#define FRCOSC          115200    //!< RCOsc frequency: Hz.

#define FOSC32          32768     //!< Osc32 frequency: Hz.
#define OSC32_STARTUP   3         //!< Osc32 startup time: RCOsc periods.

#define FOSC0           12000000  //!< Osc0 frequency: Hz.
#define OSC0_STARTUP    3         //!< Osc0 startup time: RCOsc periods.

// Osc1 crystal is not mounted by default. Set the following definitions to the
// appropriate values if a custom Osc1 crystal is mounted on your board.
//#define FOSC1           12000000  //!< Osc1 frequency: Hz.
//#define OSC1_STARTUP    3         //!< Osc1 startup time: RCOsc periods.

//! @}


/*! \name USB Definitions
 */
//! @{

//! Multiplexed pin used for USB_ID: AVR32_USBB_USB_ID_x_x.
//! To be selected according to the AVR32_USBB_USB_ID_x_x_PIN and
//! AVR32_USBB_USB_ID_x_x_FUNCTION definitions from <avr32/uc3bxxxx.h>.
#define USB_ID                      AVR32_USBB_USB_ID_0_0

//! Multiplexed pin used for USB_VBOF: AVR32_USBB_USB_VBOF_x_x.
//! To be selected according to the AVR32_USBB_USB_VBOF_x_x_PIN and
//! AVR32_USBB_USB_VBOF_x_x_FUNCTION definitions from <avr32/uc3bxxxx.h>.
#define USB_VBOF                    AVR32_USBB_USB_VBOF_0_0

//! Active level of the USB_VBOF output pin.
#define USB_VBOF_ACTIVE_LEVEL       LOW

//! USB overcurrent detection pin.
#define USB_OVERCURRENT_DETECT_PIN  AVR32_PIN_PA20

//! @}


//! Number of LEDs.
#define LED_COUNT   4

/*! \name GPIO Connections of LEDs
 */
//! @{
#define LED0_GPIO   AVR32_PIN_PA07
#define LED1_GPIO   AVR32_PIN_PA08
#define LED2_GPIO   AVR32_PIN_PA21
#define LED3_GPIO   AVR32_PIN_PA22
//! @}

/*! \name PWM Channels of LEDs
 */
//! @{
#define LED0_PWM    0
#define LED1_PWM    1
#define LED2_PWM    2
#define LED3_PWM    6
//! @}

/*! \name PWM Functions of LEDs
 */
//! @{
#define LED0_PWM_FUNCTION   AVR32_PWM_PWM_0_0_FUNCTION
#define LED1_PWM_FUNCTION   AVR32_PWM_PWM_1_0_FUNCTION
#define LED2_PWM_FUNCTION   AVR32_PWM_PWM_2_0_FUNCTION
#define LED3_PWM_FUNCTION   AVR32_PWM_PWM_6_0_FUNCTION
//! @}

/*! \name Color Identifiers of LEDs to Use with LED Functions
 */
//! @{
#define LED_MONO0_GREEN   LED0
#define LED_MONO1_GREEN   LED1
#define LED_MONO2_GREEN   LED2
#define LED_MONO3_GREEN   LED3
//! @}


/*! \name GPIO Connections of Push Buttons
 */
//! @{
#define GPIO_PUSH_BUTTON_0    AVR32_PIN_PB02
#define GPIO_PUSH_BUTTON_1    AVR32_PIN_PB03
//! @}


/*! \name GPIO Connections of the Joystick
 */
//! @{
#define GPIO_JOYSTICK_PUSH    AVR32_PIN_PA13
#define GPIO_JOYSTICK_LEFT    AVR32_PIN_PB06
#define GPIO_JOYSTICK_RIGHT   AVR32_PIN_PB09
#define GPIO_JOYSTICK_UP      AVR32_PIN_PB07
#define GPIO_JOYSTICK_DOWN    AVR32_PIN_PB08
//! @}


/*! \name ADC Connection of the Temperature Sensor
 */
//! @{
#define ADC_TEMPERATURE_CHANNEL     7
#define ADC_TEMPERATURE_PIN         AVR32_ADC_AD_7_PIN
#define ADC_TEMPERATURE_FUNCTION    AVR32_ADC_AD_7_FUNCTION
//! @}


/*! \name ADC Connection of the Light Sensor
 */
//! @{
#define ADC_LIGHT_CHANNEL           6
#define ADC_LIGHT_PIN               AVR32_ADC_AD_6_PIN
#define ADC_LIGHT_FUNCTION          AVR32_ADC_AD_6_FUNCTION
//! @}


/*! \name ADC Connections of the Accelerometer
 */
//! @{
#define ADC_ACC_X_CHANNEL           1
#define ADC_ACC_X_PIN               AVR32_ADC_AD_1_PIN
#define ADC_ACC_X_FUNCTION          AVR32_ADC_AD_1_FUNCTION
#define ADC_ACC_Y_CHANNEL           2
#define ADC_ACC_Y_PIN               AVR32_ADC_AD_2_PIN
#define ADC_ACC_Y_FUNCTION          AVR32_ADC_AD_2_FUNCTION
#define ADC_ACC_Z_CHANNEL           3
#define ADC_ACC_Z_PIN               AVR32_ADC_AD_3_PIN
#define ADC_ACC_Z_FUNCTION          AVR32_ADC_AD_3_FUNCTION
//! @}


/*! \name PWM Connections of Audio
 */
//! @{
#define AUDIO_LOW_PWM_CHANNEL       5
#define AUDIO_LOW_PWM_PIN           AVR32_PWM_PWM_5_0_PIN
#define AUDIO_LOW_PWM_FUNCTION      AVR32_PWM_PWM_5_0_FUNCTION
#define AUDIO_HIGH_PWM_CHANNEL      6
#define AUDIO_HIGH_PWM_PIN          AVR32_PWM_PWM_6_1_PIN
#define AUDIO_HIGH_PWM_FUNCTION     AVR32_PWM_PWM_6_1_FUNCTION
//! @}


/*! \name SPI Connections of the AT45DBX Data Flash Memory
 */
//! @{
#define AT45DBX_SPI                 (&AVR32_SPI)
#define AT45DBX_SPI_SCK_PIN         AVR32_SPI_SCK_0_0_PIN
#define AT45DBX_SPI_SCK_FUNCTION    AVR32_SPI_SCK_0_0_FUNCTION
#define AT45DBX_SPI_MISO_PIN        AVR32_SPI_MISO_0_0_PIN
#define AT45DBX_SPI_MISO_FUNCTION   AVR32_SPI_MISO_0_0_FUNCTION
#define AT45DBX_SPI_MOSI_PIN        AVR32_SPI_MOSI_0_0_PIN
#define AT45DBX_SPI_MOSI_FUNCTION   AVR32_SPI_MOSI_0_0_FUNCTION
#define AT45DBX_SPI_NPCS0_PIN       AVR32_SPI_NPCS_0_0_PIN
#define AT45DBX_SPI_NPCS0_FUNCTION  AVR32_SPI_NPCS_0_0_FUNCTION
//! @}


/*! \name GPIO and SPI Connections of the SD/MMC Connector
 */
//! @{
#define SD_MMC_CARD_DETECT_PIN      AVR32_PIN_PB00
#define SD_MMC_WRITE_PROTECT_PIN    AVR32_PIN_PB01
#define SD_MMC_SPI                  (&AVR32_SPI)
#define SD_MMC_SPI_CS               1
#define SD_MMC_SPI_SCK_PIN          AVR32_SPI_SCK_0_0_PIN
#define SD_MMC_SPI_SCK_FUNCTION     AVR32_SPI_SCK_0_0_FUNCTION
#define SD_MMC_SPI_MISO_PIN         AVR32_SPI_MISO_0_0_PIN
#define SD_MMC_SPI_MISO_FUNCTION    AVR32_SPI_MISO_0_0_FUNCTION
#define SD_MMC_SPI_MOSI_PIN         AVR32_SPI_MOSI_0_0_PIN
#define SD_MMC_SPI_MOSI_FUNCTION    AVR32_SPI_MOSI_0_0_FUNCTION
#define SD_MMC_SPI_NPCS_PIN         AVR32_SPI_NPCS_1_0_PIN
#define SD_MMC_SPI_NPCS_FUNCTION    AVR32_SPI_NPCS_1_0_FUNCTION
//! @}


#endif  // _EVK1101_H_
