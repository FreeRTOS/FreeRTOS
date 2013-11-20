/**
  ******************************************************************************
  * @file    tsl_conf_stm8tl5x.h
  * @author  MCD Application Team
  * @version V1.3.2
  * @date    22-January-2013
  * @brief   Acquisition parameters for STM8TL5x products.
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
#ifndef __TSL_CONF_STM8TL5X_H
#define __TSL_CONF_STM8TL5X_H

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
  - If No the acquisition is managed in the main routine using polling mode.
  - If Yes the acquisition is managed in the interrupt routines.
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
#define TSLPRM_ACQ_MIN (50)

/** Maximum acquisition measurement (range=0..65535)
  - This is the maximum acceptable value for the acquisition measure.
  - The acquisition will be in error if the measure is above this value.
*/
#define TSLPRM_ACQ_MAX (4000)

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
#define TSLPRM_TKEY_PROX_IN_TH (15)

/** TouchKeys Proximity state output threshold (range=0..255)
  - Exit Proximity state if delta is below
*/
#define TSLPRM_TKEY_PROX_OUT_TH (5)

/** TouchKeys Detect state input threshold (range=0..255)
  - Enter Detect state if delta is above
*/
#define TSLPRM_TKEY_DETECT_IN_TH (50)

/** TouchKeys Detect state output threshold (range=0..255)
  - Exit Detect state if delta is below
*/
#define TSLPRM_TKEY_DETECT_OUT_TH (40)

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
#define TSLPRM_LINROT_PROX_IN_TH (15)

/** Linear/Rotary Proximity state output threshold (range=0..255)
  - Exit Proximity state if delta is below
*/
#define TSLPRM_LINROT_PROX_OUT_TH (5)

/** Linear/Rotary Detect state input threshold (range=0..255)
  - Enter Detect state if delta is above
*/
#define TSLPRM_LINROT_DETECT_IN_TH (50)

/** Linear/Rotary Detect state output threshold (range=0..255)
  - Exit Detect state if delta is below
*/
#define TSLPRM_LINROT_DETECT_OUT_TH (30)

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
#define TSLPRM_ECS_K_SLOW (5)

/** Environment Change System Fast K factor (range=0..255)
  - The higher value is K, the faster is the response time.
*/
#define TSLPRM_ECS_K_FAST (40)

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

// DO NOT MODIFY THE LINES BELOW!!!
#define STM8TL53C4 (0)
#define STM8TL53G4 (1)
#define STM8TL53F4 (2)
#define STM8TL52G4 (3)
#define STM8TL52F4 (4)

/** @defgroup STM8TL5x_Parameters STM8TL5x Parameters
  * @{ */

//==============================================================================
// Device selection
//==============================================================================

/** @defgroup STM8TL5x_Parameters_Device_Selection 01 - Device Selection
  * @{ */

/** STM8TL5x device selection (range=0..4)
  - Select a MCU in the above list
*/
#define TSLPRM_MCU STM8TL53C4

/** @} STM8TL5x_Parameters_Device_Selection */

//==============================================================================
// Reference adjustment
//==============================================================================

/** @defgroup STM8TL5x_Parameters_Reference_Adjustment 02 - Reference adjustment
  * @{ */

/** Used to calibrate the EPCC to get the Reference closed to this value (range=100..2000)
  - The range values are recommended values.
  - The higher the Reference, the higher the sensitivity
*/
#define TSLPRM_KEY_TARGET_REFERENCE (500)

/** Used to calibrate the EPCC (range=1..TSLPRM_KEY_TARGET_REFERENCE)
*/
#define TSLPRM_KEY_TARGET_REFERENCE_ERROR (25)

/** Number of iteration after the dichotomy to fine tune the EPCC value (range=3..5)
*/
#define TSLPRM_PXS_EPCC_FINE_TUNING_ITERATION (3)

/** Used to calibrate the CS (range=1,2,4,8)
*/
#define TSLPRM_KEY_TARGET_ATTENUATION (4)

/** Below (TSLPRM_KEY_TARGET_REFERENCE - TSLPRM_TOUCHKEY_REFERENCE_RANGE) the EPCC is updated for the TKeys (range=1..TSLPRM_KEY_TARGET_REFERENCE)
*/
#define TSLPRM_TOUCHKEY_REFERENCE_RANGE (75)

/** Below (TSLPRM_KEY_TARGET_REFERENCE - TSLPRM_LINROT_REFERENCE_RANGE) the EPCC is updated for the Linear/Rotary (range=1..TSLPRM_KEY_TARGET_REFERENCE)
*/
#define TSLPRM_LINROT_REFERENCE_RANGE (75)

/** @} STM8TL5x_Parameters_Reference_Adjustment */

//==============================================================================
// PXS Clock
//==============================================================================

/** @defgroup STM8TL5x_Parameters_PXS_Clock 03 - PXS Clock
  - These parameters define the acquisition clock settings.
  * @{ */

/** Acquisition frequency (values are 16000, 8000, 4000, 2000, 1000, 500, 250 or 125)
*/
#define TSLPRM_PXS_HSI (16000)

/** Up phase length (range=1..7)
*/
#define TSLPRM_PXS_UP_LENGTH (1)

/** Pass phase length (range=1..7)
*/
#define TSLPRM_PXS_PASS_LENGTH (1)

/** @} STM8TL5x_Parameters_PXS_Clock */

//==============================================================================
// PXS Synchro
//==============================================================================

/** @defgroup STM8TL5x_Parameters_PXS_Synchro 04 - PXS Synchro
  * @{ */

/** Acquisition synchronized with SYNCHRO pin (0=No, 1=Yes)
*/
#define TSLPRM_PXS_SYNCHRONIZE (1)

/** Synchronization edge (0=Fall, 1=Rise)
*/
#define TSLPRM_PXS_SYNCHRO_EDGE (1)

/** @} STM8TL5x_Parameters_PXS_Synchro */

//==============================================================================
// PXS Miscellaneous
//==============================================================================

/** @defgroup STM8TL5x_Parameters_PXS_Miscellaneous 05 - PXS Miscellaneous
  * @{ */

/** Low power mode between acquisition (0=No, 1=Yes)
*/
#define TSLPRM_PXS_LOW_POWER_MODE (1)

/** RF detection (0=No, 1=Yes)
*/
#define TSLPRM_PXS_RF_DETECTION (1)

/** Transmitter inactive state (0=Grounded, 1=Floating)
*/
#define TSLPRM_PXS_INACTIVE_TX (1)

/** Receiver inactive state (0=Grounded, 1=Floating)
*/
#define TSLPRM_PXS_INACTIVE_RX (1)

/** Charge/Discharge cycle behaviour after VTHR is reached (0=stop, 1=continue)
*/
#define TSLPRM_PXS_RX_COUPLING (1)

/** Stabilization time (values are LONG_STAB, MEDIUM_STAB, SHORT_STAB)
*/
#define TSLPRM_PXS_STAB LONG_STAB

/** Bias (values are HIGH_BIAS, MEDIUM_BIAS, LOW_BIAS, VERY_LOW_BIAS)
*/
#define TSLPRM_PXS_BIAS HIGH_BIAS

/** Index maximum of Rx channels ("N" of RxN)
  - This value must not exceed 9 with STM8TL53C4 and 7 with STM8TL53G4
*/
#define TSLPRM_HIGH_CHANNEL_NB (9)

/** @} STM8TL5x_Parameters_PXS_Miscellaneous */

/** @} STM8TL5x_Parameters */

// DO NOT REMOVE !!!
#include "tsl_check_config.h"

#endif /* __TSL_CONF_STM8TL5X_H */

/************************ (C) COPYRIGHT STMicroelectronics *****END OF FILE****/
