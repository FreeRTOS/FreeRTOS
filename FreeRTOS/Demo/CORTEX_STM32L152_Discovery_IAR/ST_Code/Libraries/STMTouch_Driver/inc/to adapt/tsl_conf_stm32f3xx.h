/**
  ******************************************************************************
  * @file    tsl_conf_stm32f3xx.h
  * @author  MCD Application Team
  * @version V1.3.2
  * @date    22-January-2013
  * @brief   Acquisition parameters for STM32F3xx products.
  * @note    This file must be copied in the application project and values
  *          changed for the application.
  ******************************************************************************
  * @attention
  *
  * <h2><center>&copy; COPYRIGHT 2013 STMicroelectronics</center></h2>
  *
  * Licensed under MCD-ST Liberty SW License Agreement V2, (the "License");
  * You may not use this file except in compliance with the License.
  * You may obtain a copy of the License at:
  *
  *        http://www.st.com/software_license_agreement_liberty_v2
  *
  * Unless required by applicable law or agreed to in writing, software
  * distributed under the License is distributed on an "AS IS" BASIS,
  * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  * See the License for the specific language governing permissions and
  * limitations under the License.
  *
  ******************************************************************************
  */

/* Define to prevent recursive inclusion -------------------------------------*/
#ifndef __TSL_CONF_STM32F3XX_H
#define __TSL_CONF_STM32F3XX_H

//++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
//+++++++++++++++++++++++++++ COMMON PARAMETERS ++++++++++++++++++++++++++++++++
//++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

/** @defgroup Common_Parameters Common Parameters
  * @{ */

//==============================================================================
// Number of elements
//==============================================================================

/** @defgroup Common_Parameters_Number_Of_Elements 01 - Number of elements
  * @{ */

/** Total number of channels in application (range=1..255)
*/
#define TSLPRM_TOTAL_CHANNELS (1)

/** Total number of banks in application (range=1..255)
*/
#define TSLPRM_TOTAL_BANKS (1)

/** Total number of "Extended" TouchKeys in application (range=0..255)
*/
#define TSLPRM_TOTAL_TOUCHKEYS (1)

/** Total number of "Basic" TouchKeys in application (range=0..255)
*/
#define TSLPRM_TOTAL_TOUCHKEYS_B (1)

/** Total number of "Extended" Linear and Rotary sensors in application (range=0..255)
  - Count also the 1-channel linear sensor used as TouchKey
*/
#define TSLPRM_TOTAL_LINROTS (1)

/** Total number of "Basic" Linear and Rotary sensors in application (range=0..255)
  - Count also the 1-channel linear sensor used as TouchKey
*/
#define TSLPRM_TOTAL_LINROTS_B (1)

/** Total number of sensors/objects in application (range=1..255)
  - Count all TouchKeys, Linear and Rotary sensors
*/
#define TSLPRM_TOTAL_OBJECTS (1)

/** @} Common_Parameters_Number_Of_Elements */

//==============================================================================
// Optional features
//==============================================================================

/** @defgroup Common_Parameters_Options 02 - Optional features
  * @{ */

/** Record the last measure (0=No, 1=Yes)
  - If No the measure is recalculated using the Reference and Delta
*/
#define TSLPRM_USE_MEAS (1)

/** Zone management usage (0=No, 1=Yes)
*/
#define TSLPRM_USE_ZONE (1)

/** Proximity detection usage (0=No, 1=Yes)
*/
#define TSLPRM_USE_PROX (1)

/** Use the Timer tick callback (0=No, 1=Yes)
  - When equal to 1, the function TSL_CallBack_TimerTick must be defined in
    the application code. It is called for each timer interruption.
*/
#define TSLPRM_USE_TIMER_CALLBACK (1)

/** Acquisition interrupt mode (0=No, 1=Yes)
  - If No the TS interrupt is not used.
  - If Yes the TS interrupt is used.
*/
#define TSLPRM_USE_ACQ_INTERRUPT (1)

/** @} Common_Parameters_Options */

//==============================================================================
// Acquisition limits
//==============================================================================

/** @defgroup Common_Parameters_Acquisition_Limits 03 - Acquisition limits
  * @{ */

/** Minimum acquisition measurement (range=0..65535)
  - This is the minimum acceptable value for the acquisition measure.
  - The acquisition will be in error if the measure is below this value.
*/
#define TSLPRM_ACQ_MIN (10)

/** Maximum acquisition measurement (range=255, 511, 1023, 2047, 8191, 16383)
  - This is the maximum acceptable value for the acquisition measure.
  - The acquisition will be in error if the measure is above this value.
*/
#define TSLPRM_ACQ_MAX (8191)

/** @} Common_Parameters_Acquisition_Limits */

//==============================================================================
// Calibration
//==============================================================================

/** @defgroup Common_Parameters_Calibration 04 - Calibration
  * @{ */

/** Number of calibration samples (range=4, 8, 16)
  - Low value = faster calibration but less precision.
  - High value = slower calibration but more precision.
*/
#define TSLPRM_CALIB_SAMPLES (8)

/** Delay in measurement samples before starting the calibration (range=0..40)
  - This is usefull if a noise filter is used.
  - Write 0 to disable the delay.
*/
#define TSLPRM_CALIB_DELAY (10)

/** @} Common_Parameters_Calibration */

//==============================================================================
// Thresholds for TouchKey sensors
//==============================================================================

/** @defgroup Common_Parameters_TouchKey_Thresholds 05 - Thresholds for TouchKey sensors
  * @{ */

/** TouchKeys Proximity state input threshold (range=0..255)
  - Enter Proximity state if delta is above
*/
#define TSLPRM_TKEY_PROX_IN_TH (10)

/** TouchKeys Proximity state output threshold (range=0..255)
  - Exit Proximity state if delta is below
*/
#define TSLPRM_TKEY_PROX_OUT_TH (5)

/** TouchKeys Detect state input threshold (range=0..255)
  - Enter Detect state if delta is above
*/
#define TSLPRM_TKEY_DETECT_IN_TH (20)

/** TouchKeys Detect state output threshold (range=0..255)
  - Exit Detect state if delta is below
*/
#define TSLPRM_TKEY_DETECT_OUT_TH (15)

/** TouchKeys re-Calibration threshold (range=0..255)
  - @warning The value is inverted in the sensor state machine
  - Enter Calibration state if delta is below
*/
#define TSLPRM_TKEY_CALIB_TH (20)

/** TouchKey, Linear and Rotary sensors thresholds coefficient (range=0..4)
    This multiplier coefficient is applied on Detect thresholds only.
  - 0: feature disabled
  - 1: thresholds x 2
  - 2: thresholds x 4
  - 3: thresholds x 8
  - 4: thresholds x 16
*/
#define TSLPRM_COEFF_TH (1)

/** @} Common_Parameters_TouchKey_Thresholds */

//==============================================================================
// Thresholds for Linear and Rotary sensors
//==============================================================================

/** @defgroup Common_Parameters_LinRot_Thresholds 06 - Thresholds for Linear and Rotary sensors
  * @{ */

/** Linear/Rotary Proximity state input threshold (range=0..255)
  - Enter Proximity state if delta is above
*/
#define TSLPRM_LINROT_PROX_IN_TH (10)

/** Linear/Rotary Proximity state output threshold (range=0..255)
  - Exit Proximity state if delta is below
*/
#define TSLPRM_LINROT_PROX_OUT_TH (5)

/** Linear/Rotary Detect state input threshold (range=0..255)
  - Enter Detect state if delta is above
*/
#define TSLPRM_LINROT_DETECT_IN_TH (20)

/** Linear/Rotary Detect state output threshold (range=0..255)
  - Exit Detect state if delta is below
*/
#define TSLPRM_LINROT_DETECT_OUT_TH (15)

/** Linear/Rotary re-Calibration threshold (range=0..255)
  - @warning The value is inverted in the sensor state machine
  - Enter Calibration state if delta is below
  - A low absolute value will result in a higher sensitivity and thus some spurious
    recalibration may be issued.
*/
#define TSLPRM_LINROT_CALIB_TH (20)

/** Linear/Rotary Delta normalization (0=No, 1=Yes)
  - When this parameter is set, a coefficient is applied on all Delta of all sensors
    in order to normalize them and to improve the position calculation.
  - These coefficients must be defined in a constant table in the application (see Library examples).
  - The MSB is the coefficient integer part, the LSB is the coefficient real part.
  - Examples:
    - To apply a factor 1.10:
      0x01 to the MSB
      0x1A to the LSB (0.10 x 256 = 25.6 -> rounded to 26 = 0x1A)
    - To apply a factor 0.90:
      0x00 to the MSB
      0xE6 to the LSB (0.90 x 256 = 230.4 -> rounded to 230 = 0xE6)
    - To apply no factor:
      0x01 to the MSB
      0x00 to the LSB
*/
#define TSLPRM_LINROT_USE_NORMDELTA (1)

/** @} Common_Parameters_LinRot_Thresholds */

//==============================================================================
// Linear/Rotary sensors used
//==============================================================================

/** @defgroup Common_Parameters_LinRot_Used 07 - Linear/Rotary sensors used
  * @{ */

/** Select which Linear and Rotary sensors you use in your application.
    - 0 = Not Used
    - 1 = Used

  LIN = Linear sensor
  ROT = Rotary sensor
  M1 = Mono electrodes design with 0/255 position at extremities of the sensor
  M2 = Mono electrodes design
  H = Half-ended electrodes design
  D = Dual electrodes design
*/
#define TSLPRM_USE_3CH_LIN_M1 (1)
#define TSLPRM_USE_3CH_LIN_M2 (1)
#define TSLPRM_USE_3CH_LIN_H (1)
#define TSLPRM_USE_3CH_ROT_M (1)

#define TSLPRM_USE_4CH_LIN_M1 (1)
#define TSLPRM_USE_4CH_LIN_M2 (1)
#define TSLPRM_USE_4CH_LIN_H (1)
#define TSLPRM_USE_4CH_ROT_M (1)

#define TSLPRM_USE_5CH_LIN_M1 (1)
#define TSLPRM_USE_5CH_LIN_M2 (1)
#define TSLPRM_USE_5CH_LIN_H (1)
#define TSLPRM_USE_5CH_ROT_M (1)
#define TSLPRM_USE_5CH_ROT_D (1)

#define TSLPRM_USE_6CH_LIN_M1 (1)
#define TSLPRM_USE_6CH_LIN_M2 (1)
#define TSLPRM_USE_6CH_LIN_H (1)
#define TSLPRM_USE_6CH_ROT_M (1)

/** @} Common_Parameters_LinRot_used */

//==============================================================================
// Linear/Rotary sensors position
//==============================================================================

/** @defgroup Common_Parameters_LinRot_Position 08 - Linear/Rotary sensors position
  * @{ */

/** Position resolution in number of bits (range=1..8)
  - A Low value will result in a low resolution and will be less subject to noise.
  - A High value will result in a high resolution and will be more subject to noise.
*/
#define TSLPRM_LINROT_RESOLUTION (7)

/** Direction change threshold in position unit (range=0..255)
  - Defines the default threshold used during the change direction process.
  - A Low value will result in a faster direction change.
  - A High value will result in a slower direction change.
*/
#define TSLPRM_LINROT_DIR_CHG_POS (10)

/** Direction change debounce (range=0..63)
  - Defines the default integrator counter used during the change direction process.
  - This counter is decremented when the same change in the position is detected and the direction will
    change after this counter reaches zero.
  - A Low value will result in a faster direction change.
  - A High value will result in a slower direction change.
*/
#define TSLPRM_LINROT_DIR_CHG_DEB (1)

/** @} Common_Parameters_LinRot_Position */

//==============================================================================
// Debounce counters
//==============================================================================

/** @defgroup Common_Parameters_Debounce 09 - Debounce counters
  * @{ */

/** Proximity state debounce in samples unit (range=0..63)
  - A Low value will result in a higher sensitivity during the Proximity detection but with less noise filtering.
  - A High value will result in improving the system noise immunity but will increase the system response time.
*/
#define TSLPRM_DEBOUNCE_PROX (3)

/** Detect state debounce in samples unit (range=0..63)
  - A Low value will result in a higher sensitivity during the detection but with less noise filtering.
  - A High value will result in improving the system noise immunity but will increase the system response time.
*/
#define TSLPRM_DEBOUNCE_DETECT (3)

/** Release state debounce in samples unit (range=0..63)
  - A Low value will result in a higher sensitivity during the end-detection but with less noise filtering.
  - A High value will result in a lower sensitivity during the end-detection but with more noise filtering.
*/
#define TSLPRM_DEBOUNCE_RELEASE (3)

/** Re-calibration state debounce in samples unit (range=0..63)
  - A Low value will result in a higher sensitivity during the recalibration but with less noise filtering.
  - A High value will result in a lower sensitivity during the recalibration but with more noise filtering.
*/
#define TSLPRM_DEBOUNCE_CALIB (3)

/** Error state debounce in samples unit (range=0..63)
  - A Low value will result in a higher sensitivity to enter in error state.
  - A High value will result in a lower sensitivity to enter in error state.
*/
#define TSLPRM_DEBOUNCE_ERROR (3)

/** @} Common_Parameters_Debounce */

//==============================================================================
// Environment Change System (ECS)
//==============================================================================

/** @defgroup Common_Parameters_ECS 10 - ECS
  * @{ */

/** Environment Change System Slow K factor (range=0..255)
  - The higher value is K, the faster is the response time.
*/
#define TSLPRM_ECS_K_SLOW (10)

/** Environment Change System Fast K factor (range=0..255)
  - The higher value is K, the faster is the response time.
*/
#define TSLPRM_ECS_K_FAST (20)

/** Environment Change System delay in msec (range=0..5000)
  - The ECS will be started after this delay and when all sensors are in Release state.
*/
#define TSLPRM_ECS_DELAY (500)

/** @} Common_Parameters_ECS */

//==============================================================================
// Detection Time Out (DTO)
//==============================================================================

/** @defgroup Common_Parameters_DTO 11 - DTO
  * @{ */

/** Detection Time Out delay in seconds (range=0..63)
  - Value 0: DTO processing not compiled in the code (to gain size if not used).
  - Value 1: Default time out infinite.
  - Value between 2 and 63: Default time out between value n-1 and n.
  - Examples:
      - With a DTO equal to 2, the time out is between 1s and 2s.
      - With a DTO equal to 63, the time out is between 62s and 63s.

@note The DTO can be changed in run-time by the application only if the
      default value is between 1 and 63.
*/
#define TSLPRM_DTO (5)

/** @} Common_Parameters_DTO */

//==============================================================================
// Detection Exclusion System (DXS)
//==============================================================================

/** @defgroup Common_Parameters_DXS 12 - DXS
  * @{ */

/** Detection Exclusion System (0=No, 1=Yes)
*/
#define TSLPRM_USE_DXS (1)

/** @} Common_Parameters_DXS */

//==============================================================================
// Miscellaneous parameters
//==============================================================================

/** @defgroup Common_Parameters_Misc 13 - Miscellaneous
  * @{ */

/** Timing tick frequency in Hz (range=125, 250, 500, 1000, 2000)
  - Result to a timing interrupt respectively every 8ms, 4ms, 2ms, 1ms, 0.5ms
*/
#define TSLPRM_TICK_FREQ (1000)

/** @} Common_Parameters_Misc */

/** @} Common_Parameters */

//++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
//++++++++++++++++++++++++++++++ MCU PARAMETERS ++++++++++++++++++++++++++++++++
//++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

/** @defgroup STM32F3xx_Parameters STM32F3xx Parameters
  * @{ */

//==============================================================================
// GPIO configuration
//==============================================================================

/** @defgroup STM32F3xx_Parameters_GPIO_Config 01 - TSC GPIOs Configuration
  * @{ */

/** TSC GPIOs Configuration selection (range=0..1)
    - 0: Manual. The TSC GPIOs configuration must be done by the application code.
    - 1: Automatic. The TSLPRM_TSC_GROUPx_IOy parameters below must be filled up.
         The TSC GPIOs configuration is automatically done by the STMTouch driver.
*/
#define TSLPRM_TSC_GPIO_CONFIG (1)

//+++ DO NOT CHANGE THESE VALUES +++++++++++++++++++++++++++++++++
// These defines must be applied to the TSLPRM_TSC_GROUPx_IOy parameters below.
#define NU      (0) // Not Used IO
#define CHANNEL (1) // Channel IO
#define SHIELD  (2) // Shield IO (= Channel IO but not acquired)
#define SAMPCAP (3) // Sampling Capacitor IO
//++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

// If TSLPRM_TSC_GPIO_CONFIG=1 assign each TSLPRM_TSC_GROUPx_IOy parameters below.
// If TSLPRM_TSC_GPIO_CONFIG=0 these parameters are ignored.
//                                         STM32F30X STM32F37X
#define TSLPRM_TSC_GROUP1_IO1  NU       // PA0       PA0
#define TSLPRM_TSC_GROUP1_IO2  NU       // PA1       PA1
#define TSLPRM_TSC_GROUP1_IO3  NU       // PA2       PA2
#define TSLPRM_TSC_GROUP1_IO4  NU       // PA3       PA3

#define TSLPRM_TSC_GROUP2_IO1  NU       // PA4       PA4
#define TSLPRM_TSC_GROUP2_IO2  NU       // PA5       PA5
#define TSLPRM_TSC_GROUP2_IO3  NU       // PA6       PA6
#define TSLPRM_TSC_GROUP2_IO4  NU       // PA7       PA7

#define TSLPRM_TSC_GROUP3_IO1  NU       // PC5       PC4   << diff
#define TSLPRM_TSC_GROUP3_IO2  NU       // PB0       PC5   << diff
#define TSLPRM_TSC_GROUP3_IO3  NU       // PB1       PB0   << diff
#define TSLPRM_TSC_GROUP3_IO4  NU       // PB2       PB1   << diff

#define TSLPRM_TSC_GROUP4_IO1  NU       // PA9       PA9
#define TSLPRM_TSC_GROUP4_IO2  NU       // PA10      PA10
#define TSLPRM_TSC_GROUP4_IO3  NU       // PA13      PA13
#define TSLPRM_TSC_GROUP4_IO4  NU       // PA14      PA14

#define TSLPRM_TSC_GROUP5_IO1  NU       // PB3       PB3
#define TSLPRM_TSC_GROUP5_IO2  NU       // PB4       PB4
#define TSLPRM_TSC_GROUP5_IO3  NU       // PB6       PB6
#define TSLPRM_TSC_GROUP5_IO4  NU       // PB7       PB7

#define TSLPRM_TSC_GROUP6_IO1  NU       // PB11      PB14  << diff
#define TSLPRM_TSC_GROUP6_IO2  NU       // PB12      PB15  << diff
#define TSLPRM_TSC_GROUP6_IO3  NU       // PB13      PD8   << diff
#define TSLPRM_TSC_GROUP6_IO4  NU       // PB14      PD9   << diff

#define TSLPRM_TSC_GROUP7_IO1  NU       // PE2       PE2
#define TSLPRM_TSC_GROUP7_IO2  NU       // PE3       PE3
#define TSLPRM_TSC_GROUP7_IO3  NU       // PE4       PE4
#define TSLPRM_TSC_GROUP7_IO4  NU       // PE5       PE5

#define TSLPRM_TSC_GROUP8_IO1  NU       // PD12      PD12
#define TSLPRM_TSC_GROUP8_IO2  NU       // PD13      PD13
#define TSLPRM_TSC_GROUP8_IO3  NU       // PD14      PD14
#define TSLPRM_TSC_GROUP8_IO4  NU       // PD15      PD15

/** @} STM32F3xx_Parameters_GPIO_Config */

//==============================================================================
// Charge Transfer Pulses
//==============================================================================

/** @defgroup STM32F3xx_Parameters_CT_Pulses 02 - Charge Transfer Pulses
  * @{ */

/** Charge Transfer Pulse High (range=0..15)
    - 0: 1 x tPGCLK
    - 1: 2 x tPGCLK
    - ...
    - 15: 16 x tPGCLK
*/
#define TSLPRM_TSC_CTPH (1)

/** Charge Transfer Pulse Low (range=0..15)
    - 0: 1 x tPGCLK
    - 1: 2 x tPGCLK
    - ...
    - 15: 16 x tPGCLK
*/
#define TSLPRM_TSC_CTPL (1)

/** Pulse Generator Prescaler (range=0..7)
    - 0: fPGCLK = fHCLK
    - 1: fPGCLK = fHCLK/2
    - ...
    - 7: fPGCLK = fHCLK/128
*/
#define TSLPRM_TSC_PGPSC (5)

/** @} STM32F3xx_Parameters_CT_Pulses */

//==============================================================================
// IOs
//==============================================================================

/** @defgroup STM32F3xx_Parameters_IOs 03 - I/Os
  * @{ */

/** TSC IOs default mode when no on-going acquisition (range=0..1)
    - 0: Output push-pull low
    - 1: Input floating
*/
#define TSLPRM_TSC_IODEF (0)

/** Acquisition Mode (range=0..1)
    - 0: Normal acquisition mode
    - 1: Synchronized acquisition mode
*/
#define TSLPRM_TSC_AM (0)

/** Synchronization Pin (range=0..1)
    - 0: PB08
    - 1: PB10
*/
#define TSLPRM_TSC_SYNC_PIN (0)

/** Synchronization Polarity (range=0..1)
    - 0: Falling edge only
    - 1: Rising edge and high level
*/
#define TSLPRM_TSC_SYNC_POL (0)

/** @} STM32F3xx_Parameters_Misc */

//==============================================================================
// Spread Spectrum
//==============================================================================

/** @defgroup STM32F3xx_Parameters_SpreadSpectrum 04 - Spread Spectrum
  * @{ */

/** Use Spread Spectrum (0=No, 1=Yes)
*/
#define TSLPRM_TSC_USE_SS (0)

/** Spread Spectrum Deviation (range=0..127)
    - 0: 1 x tSSCLK
    - 1: 2 x tSSCLK
    - ...
    - 127: 128 x tSSCLK
*/
#define TSLPRM_TSC_SSD (0)

/** Spread Spectrum Prescaler (range=0..1)
    - 0: fSSCLK = fHCLK
    - 1: fSSCLK = fHCLK/2
*/
#define TSLPRM_TSC_SSPSC (0)

/** @} STM32F3xx_Parameters_SpreadSpectrum */

/** @} STM32F3xx_Parameters */

// DO NOT REMOVE !!!
#include "tsl_check_config.h"

#endif /* __TSL_CONF_STM32F3XX_H */

/************************ (C) COPYRIGHT STMicroelectronics *****END OF FILE****/
