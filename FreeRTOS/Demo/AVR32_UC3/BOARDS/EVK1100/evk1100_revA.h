/* This header file is part of the ATMEL AVR32-SoftwareFramework-AT32UC3-1.5.0 Release */

/*This file is prepared for Doxygen automatic documentation generation.*/
/*! \file *********************************************************************
 *
 * \brief AT32UC3A EVK1100 board header file.
 *
 * This file contains definitions and services related to the features of the
 * EVK1100 board rev. A.
 *
 * To use this board, define BOARD=EVK1100 and EVK1100_REVA.
 *
 * - Compiler:           IAR EWAVR32 and GNU GCC for AVR32
 * - Supported devices:  All AVR32 AT32UC3A devices can be used.
 * - AppNote:
 *
 * \author               Atmel Corporation: http://www.atmel.com \n
 *                       Support and FAQ: http://support.atmel.no/
 *
 ******************************************************************************/

/* Copyright (c) 2009 Atmel Corporation. All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice, this
 * list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 * this list of conditions and the following disclaimer in the documentation
 * and/or other materials provided with the distribution.
 *
 * 3. The name of Atmel may not be used to endorse or promote products derived
 * from this software without specific prior written permission.
 *
 * 4. This software may only be redistributed and used in connection with an Atmel
 * AVR product.
 *
 * THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR IMPLIED
 * WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * EXPRESSLY AND SPECIFICALLY DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR
 * ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
 * ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE
 *
 */

#ifndef _EVK1100_REVA_H_
#define _EVK1100_REVA_H_

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
//#define FRCOSC          AVR32_PM_RCOSC_FREQUENCY              //!< RCOsc frequency: Hz.

#define FOSC32          32768                                 //!< Osc32 frequency: Hz.
#define OSC32_STARTUP   AVR32_PM_OSCCTRL32_STARTUP_8192_RCOSC //!< Osc32 startup time: RCOsc periods.

#define FOSC0           12000000                              //!< Osc0 frequency: Hz.
#define OSC0_STARTUP    AVR32_PM_OSCCTRL0_STARTUP_2048_RCOSC  //!< Osc0 startup time: RCOsc periods.

// Osc1 crystal is not mounted by default. Set the following definitions to the
// appropriate values if a custom Osc1 crystal is mounted on your board.
//#define FOSC1           12000000                              //!< Osc1 frequency: Hz.
//#define OSC1_STARTUP    AVR32_PM_OSCCTRL1_STARTUP_2048_RCOSC  //!< Osc1 startup time: RCOsc periods.

//! @}


/*! \name SDRAM Definitions
 */
//! @{

//! Part header file of used SDRAM(s).
#define SDRAM_PART_HDR  "MT48LC16M16A2TG7E/mt48lc16m16a2tg7e.h"

//! Data bus width to use the SDRAM(s) with (16 or 32 bits; always 16 bits on
//! UC3).
#define SDRAM_DBW       16

//! @}


/*! \name USB Definitions
 */
//! @{

//! Multiplexed pin used for USB_ID: AVR32_USBB_USB_ID_x_x.
//! To be selected according to the AVR32_USBB_USB_ID_x_x_PIN and
//! AVR32_USBB_USB_ID_x_x_FUNCTION definitions from <avr32/uc3axxxx.h>.
#define USB_ID                      AVR32_USBB_USB_ID_0_0

//! Multiplexed pin used for USB_VBOF: AVR32_USBB_USB_VBOF_x_x.
//! To be selected according to the AVR32_USBB_USB_VBOF_x_x_PIN and
//! AVR32_USBB_USB_VBOF_x_x_FUNCTION definitions from <avr32/uc3axxxx.h>.
#define USB_VBOF                    AVR32_USBB_USB_VBOF_0_0

//! Active level of the USB_VBOF output pin.
#define USB_VBOF_ACTIVE_LEVEL       HIGH

//! USB overcurrent detection pin.
#define USB_OVERCURRENT_DETECT_PIN  AVR32_PIN_PB18

//! @}


//! GPIO connection of the MAC PHY PWR_DOWN/INT signal.
#define MACB_INTERRUPT_PIN  AVR32_PIN_PX12


//! Number of LEDs.
#define LED_COUNT   8

/*! \name GPIO Connections of LEDs
 */
//! @{
#define LED0_GPIO   AVR32_PIN_PX13
#define LED1_GPIO   AVR32_PIN_PX14
#define LED2_GPIO   AVR32_PIN_PX15
#define LED3_GPIO   AVR32_PIN_PX16
#define LED4_GPIO   AVR32_PIN_PB19
#define LED5_GPIO   AVR32_PIN_PB20
#define LED6_GPIO   AVR32_PIN_PB21
#define LED7_GPIO   AVR32_PIN_PB22
//! @}

/*! \name PWM Channels of LEDs
 */
//! @{
#define LED0_PWM    (-1)
#define LED1_PWM    (-1)
#define LED2_PWM    (-1)
#define LED3_PWM    (-1)
#define LED4_PWM      0
#define LED5_PWM      1
#define LED6_PWM      2
#define LED7_PWM      3
//! @}

/*! \name PWM Functions of LEDs
 */
//! @{
#define LED0_PWM_FUNCTION   (-1)
#define LED1_PWM_FUNCTION   (-1)
#define LED2_PWM_FUNCTION   (-1)
#define LED3_PWM_FUNCTION   (-1)
#define LED4_PWM_FUNCTION   AVR32_PWM_0_FUNCTION
#define LED5_PWM_FUNCTION   AVR32_PWM_1_FUNCTION
#define LED6_PWM_FUNCTION   AVR32_PWM_2_FUNCTION
#define LED7_PWM_FUNCTION   AVR32_PWM_3_FUNCTION
//! @}

/*! \name Color Identifiers of LEDs to Use with LED Functions
 */
//! @{
#define LED_MONO0_GREEN   LED4
#define LED_MONO1_GREEN   LED5
#define LED_MONO2_GREEN   LED6
#define LED_MONO3_GREEN   LED7
#define LED_BI0_GREEN     LED1
#define LED_BI0_RED       LED0
#define LED_BI1_GREEN     LED3
#define LED_BI1_RED       LED2
//! @}


/*! \name GPIO Connections of Push Buttons
 */
//! @{
#define GPIO_PUSH_BUTTON_0            AVR32_PIN_PB28
#define GPIO_PUSH_BUTTON_0_PRESSED    0
#define GPIO_PUSH_BUTTON_1            AVR32_PIN_PB29
#define GPIO_PUSH_BUTTON_1_PRESSED    0
#define GPIO_PUSH_BUTTON_2            AVR32_PIN_PB27
#define GPIO_PUSH_BUTTON_2_PRESSED    0
//! @}


/*! \name GPIO Connections of the Joystick
 */
//! @{
#define GPIO_JOYSTICK_PUSH            AVR32_PIN_PA20
#define GPIO_JOYSTICK_PUSH_PRESSED    0
#define GPIO_JOYSTICK_LEFT            AVR32_PIN_PA25
#define GPIO_JOYSTICK_LEFT_PRESSED    0
#define GPIO_JOYSTICK_RIGHT           AVR32_PIN_PA28
#define GPIO_JOYSTICK_RIGHT_PRESSED   0
#define GPIO_JOYSTICK_UP              AVR32_PIN_PA26
#define GPIO_JOYSTICK_UP_PRESSED      0
#define GPIO_JOYSTICK_DOWN            AVR32_PIN_PA27
#define GPIO_JOYSTICK_DOWN_PRESSED    0
//! @}


/*! \name ADC Connection of the Potentiometer
 */
//! @{
#define ADC_POTENTIOMETER_CHANNEL   1
#define ADC_POTENTIOMETER_PIN       AVR32_ADC_AD_1_PIN
#define ADC_POTENTIOMETER_FUNCTION  AVR32_ADC_AD_1_FUNCTION
//! @}


/*! \name ADC Connection of the Temperature Sensor
 */
//! @{
#define ADC_TEMPERATURE_CHANNEL     0
#define ADC_TEMPERATURE_PIN         AVR32_ADC_AD_0_PIN
#define ADC_TEMPERATURE_FUNCTION    AVR32_ADC_AD_0_FUNCTION
//! @}


/*! \name ADC Connection of the Light Sensor
 */
//! @{
#define ADC_LIGHT_CHANNEL           2
#define ADC_LIGHT_PIN               AVR32_ADC_AD_2_PIN
#define ADC_LIGHT_FUNCTION          AVR32_ADC_AD_2_FUNCTION
//! @}


/*! \name SPI Connections of the DIP204 LCD
 */
//! @{
#define DIP204_SPI                  (&AVR32_SPI1)
#define DIP204_SPI_NPCS             2
#define DIP204_SPI_SCK_PIN          AVR32_SPI1_SCK_0_0_PIN
#define DIP204_SPI_SCK_FUNCTION     AVR32_SPI1_SCK_0_0_FUNCTION
#define DIP204_SPI_MISO_PIN         AVR32_SPI1_MISO_0_0_PIN
#define DIP204_SPI_MISO_FUNCTION    AVR32_SPI1_MISO_0_0_FUNCTION
#define DIP204_SPI_MOSI_PIN         AVR32_SPI1_MOSI_0_0_PIN
#define DIP204_SPI_MOSI_FUNCTION    AVR32_SPI1_MOSI_0_0_FUNCTION
#define DIP204_SPI_NPCS_PIN         AVR32_SPI1_NPCS_2_0_PIN
#define DIP204_SPI_NPCS_FUNCTION    AVR32_SPI1_NPCS_2_0_FUNCTION
//! @}

/*! \name GPIO and PWM Connections of the DIP204 LCD Backlight
 */
//! @{
#define DIP204_BACKLIGHT_PIN        AVR32_PIN_PB18
#define DIP204_PWM_CHANNEL          6
#define DIP204_PWM_PIN              AVR32_PWM_6_PIN
#define DIP204_PWM_FUNCTION         AVR32_PWM_6_FUNCTION
//! @}


/*! \name SPI Connections of the AT45DBX Data Flash Memory
 */
//! @{
#define AT45DBX_SPI                 (&AVR32_SPI1)
#define AT45DBX_SPI_NPCS            0
#define AT45DBX_SPI_SCK_PIN         AVR32_SPI1_SCK_0_0_PIN
#define AT45DBX_SPI_SCK_FUNCTION    AVR32_SPI1_SCK_0_0_FUNCTION
#define AT45DBX_SPI_MISO_PIN        AVR32_SPI1_MISO_0_0_PIN
#define AT45DBX_SPI_MISO_FUNCTION   AVR32_SPI1_MISO_0_0_FUNCTION
#define AT45DBX_SPI_MOSI_PIN        AVR32_SPI1_MOSI_0_0_PIN
#define AT45DBX_SPI_MOSI_FUNCTION   AVR32_SPI1_MOSI_0_0_FUNCTION
#define AT45DBX_SPI_NPCS0_PIN       AVR32_SPI1_NPCS_0_0_PIN
#define AT45DBX_SPI_NPCS0_FUNCTION  AVR32_SPI1_NPCS_0_0_FUNCTION
//! @}


/*! \name GPIO and SPI Connections of the SD/MMC Connector
 */
//! @{
#define SD_MMC_CARD_DETECT_PIN      AVR32_PIN_PA02
#define SD_MMC_WRITE_PROTECT_PIN    AVR32_PIN_PA07
#define SD_MMC_SPI                  (&AVR32_SPI1)
#define SD_MMC_SPI_NPCS             1
#define SD_MMC_SPI_SCK_PIN          AVR32_SPI1_SCK_0_0_PIN
#define SD_MMC_SPI_SCK_FUNCTION     AVR32_SPI1_SCK_0_0_FUNCTION
#define SD_MMC_SPI_MISO_PIN         AVR32_SPI1_MISO_0_0_PIN
#define SD_MMC_SPI_MISO_FUNCTION    AVR32_SPI1_MISO_0_0_FUNCTION
#define SD_MMC_SPI_MOSI_PIN         AVR32_SPI1_MOSI_0_0_PIN
#define SD_MMC_SPI_MOSI_FUNCTION    AVR32_SPI1_MOSI_0_0_FUNCTION
#define SD_MMC_SPI_NPCS_PIN         AVR32_SPI1_NPCS_1_0_PIN
#define SD_MMC_SPI_NPCS_FUNCTION    AVR32_SPI1_NPCS_1_0_FUNCTION
//! @}


/*! \name TWI Connections of the Spare TWI Connector
 */
//! @{
#define SPARE_TWI                   (&AVR32_TWI)
#define SPARE_TWI_SCL_PIN           AVR32_TWI_SCL_0_0_PIN
#define SPARE_TWI_SCL_FUNCTION      AVR32_TWI_SCL_0_0_FUNCTION
#define SPARE_TWI_SDA_PIN           AVR32_TWI_SDA_0_0_PIN
#define SPARE_TWI_SDA_FUNCTION      AVR32_TWI_SDA_0_0_FUNCTION
//! @}


/*! \name SPI Connections of the Spare SPI Connector
 */
//! @{
#define SPARE_SPI                   (&AVR32_SPI0)
#define SPARE_SPI_NPCS              0
#define SPARE_SPI_SCK_PIN           AVR32_SPI0_SCK_0_0_PIN
#define SPARE_SPI_SCK_FUNCTION      AVR32_SPI0_SCK_0_0_FUNCTION
#define SPARE_SPI_MISO_PIN          AVR32_SPI0_MISO_0_0_PIN
#define SPARE_SPI_MISO_FUNCTION     AVR32_SPI0_MISO_0_0_FUNCTION
#define SPARE_SPI_MOSI_PIN          AVR32_SPI0_MOSI_0_0_PIN
#define SPARE_SPI_MOSI_FUNCTION     AVR32_SPI0_MOSI_0_0_FUNCTION
#define SPARE_SPI_NPCS_PIN          AVR32_SPI0_NPCS_0_0_PIN
#define SPARE_SPI_NPCS_FUNCTION     AVR32_SPI0_NPCS_0_0_FUNCTION
//! @}


#endif  // _EVK1100_REVA_H_
