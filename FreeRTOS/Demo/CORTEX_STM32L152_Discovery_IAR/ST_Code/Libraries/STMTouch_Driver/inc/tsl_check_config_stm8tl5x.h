/**
  ******************************************************************************
  * @file    tsl_check_config_stm8tl5x.h
  * @author  MCD Application Team
  * @version V1.3.2
  * @date    22-January-2013
  * @brief   This file contains the check of all parameters defined in the
  *          STM8TL5X configuration file.
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
#ifndef __TSL_CHECK_CONFIG_STM8TL5X_H
#define __TSL_CHECK_CONFIG_STM8TL5X_H

//------------------------------------------------------------------------------

#if ((TSLPRM_MCU < 0) && (TSLPRM_MCU > 4))
#error "The MCU selected is not in the STM8TL5x MCU list !"
#endif

#if (TSLPRM_MCU > 0)
#define __MAX_RX 7
#else
#define __MAX_RX 9
#endif

//------------------------------------------------------------------------------

#if ((TSLPRM_TOTAL_CHANNELS < 1) || (TSLPRM_TOTAL_CHANNELS > 300))
#error "TSLPRM_TOTAL_CHANNELS is out of range (1 .. 300)."
#endif

#if ((TSLPRM_TOTAL_BANKS < 1) || (TSLPRM_TOTAL_BANKS > 15))
#error "TSLPRM_TOTAL_BANKS is out of range (1 .. 15)."
#endif

#if ((TSLPRM_TOTAL_TOUCHKEYS < 0) || (TSLPRM_TOTAL_TOUCHKEYS > 256))
#error "TSLPRM_TOTAL_TOUCHKEYS is out of range (0 .. 256)."
#endif

#if ((TSLPRM_TOTAL_TOUCHKEYS_B < 0) || (TSLPRM_TOTAL_TOUCHKEYS_B > 256))
#error "TSLPRM_TOTAL_TOUCHKEYS_B is out of range (0 .. 256)."
#endif

#if ((TSLPRM_TOTAL_LINROTS < 0) || (TSLPRM_TOTAL_LINROTS > 256))
#error "TSLPRM_TOTAL_LINROTS is out of range (0 .. 256)."
#endif

#if ((TSLPRM_TOTAL_LINROTS_B < 0) || (TSLPRM_TOTAL_LINROTS_B > 256))
#error "TSLPRM_TOTAL_LINROTS_B is out of range (0 .. 256)."
#endif

#if ((TSLPRM_TOTAL_OBJECTS < 1) || (TSLPRM_TOTAL_OBJECTS > 256))
#error "TSLPRM_TOTAL_OBJECTS is out of range (1 .. 256)."
#endif

//------------------------------------------------------------------------------

#ifndef TSLPRM_KEY_TARGET_REFERENCE
#error "TSLPRM_KEY_TARGET_REFERENCE is not defined."
#endif

#if ((TSLPRM_KEY_TARGET_REFERENCE < 100) || (TSLPRM_KEY_TARGET_REFERENCE > 2000))
#error "TSLPRM_KEY_TARGET_REFERENCE is out of range (100 .. 2000)."
#endif

//------------------------------------------------------------------------------

#ifndef TSLPRM_KEY_TARGET_REFERENCE_ERROR
#error "TSLPRM_KEY_TARGET_REFERENCE_ERROR is not defined."
#endif

#if ((TSLPRM_KEY_TARGET_REFERENCE_ERROR < 1) || (TSLPRM_KEY_TARGET_REFERENCE_ERROR > TSLPRM_KEY_TARGET_REFERENCE))
#error "TSLPRM_KEY_TARGET_REFERENCE_ERROR is out of range (1 .. TSLPRM_KEY_TARGET_REFERENCE)."
#endif

//------------------------------------------------------------------------------

#ifndef TSLPRM_PXS_EPCC_FINE_TUNING_ITERATION
#error "TSLPRM_PXS_EPCC_FINE_TUNING_ITERATION is not defined."
#endif

#if ((TSLPRM_PXS_EPCC_FINE_TUNING_ITERATION < 3) || (TSLPRM_PXS_EPCC_FINE_TUNING_ITERATION > 5))
#error "TSLPRM_PXS_EPCC_FINE_TUNING_ITERATION is out of range (3 .. 5)."
#endif

//------------------------------------------------------------------------------

#ifndef TSLPRM_KEY_TARGET_ATTENUATION
#error "TSLPRM_KEY_TARGET_ATTENUATION is not defined."
#endif

#if ((TSLPRM_KEY_TARGET_ATTENUATION != 1) && (TSLPRM_KEY_TARGET_ATTENUATION != 2) &&\
     (TSLPRM_KEY_TARGET_ATTENUATION != 4) && (TSLPRM_KEY_TARGET_ATTENUATION != 8))
#error "TSLPRM_KEY_TARGET_ATTENUATION is out of range (1,2,4,8)."
#endif

//------------------------------------------------------------------------------

#ifndef TSLPRM_TOUCHKEY_REFERENCE_RANGE
#error "TSLPRM_TOUCHKEY_REFERENCE_RANGE is not defined."
#endif

#if ((TSLPRM_TOUCHKEY_REFERENCE_RANGE < 1) || (TSLPRM_TOUCHKEY_REFERENCE_RANGE > TSLPRM_KEY_TARGET_REFERENCE))
#error "TSLPRM_TOUCHKEY_REFERENCE_RANGE is out of range (1 .. TSLPRM_KEY_TARGET_REFERENCE)."
#endif

//------------------------------------------------------------------------------

#ifndef TSLPRM_LINROT_REFERENCE_RANGE
#error "TSLPRM_LINROT_REFERENCE_RANGE is not defined."
#endif

#if ((TSLPRM_LINROT_REFERENCE_RANGE < 1) || (TSLPRM_LINROT_REFERENCE_RANGE > TSLPRM_KEY_TARGET_REFERENCE))
#error "TSLPRM_LINROT_REFERENCE_RANGE is out of range (1 .. TSLPRM_KEY_TARGET_REFERENCE)."
#endif

//------------------------------------------------------------------------------

#ifndef TSLPRM_PXS_HSI
#error "TSLPRM_PXS_HSI is not defined."
#endif

#if ((TSLPRM_PXS_HSI != 16000) && (TSLPRM_PXS_HSI != 8000) && (TSLPRM_PXS_HSI != 4000) && \
     (TSLPRM_PXS_HSI !=  2000) && (TSLPRM_PXS_HSI != 1000) && (TSLPRM_PXS_HSI !=  500) && \
     (TSLPRM_PXS_HSI !=   250) && (TSLPRM_PXS_HSI !=  125))
#error "TSLPRM_PXS_HSI is out of range (16000, 8000, 4000, 2000, 1000, 500, 250, 125)."
#endif

//------------------------------------------------------------------------------

#ifndef TSLPRM_PXS_UP_LENGTH
#error "TSLPRM_PXS_UP_LENGTH is not defined."
#endif

#if ((TSLPRM_PXS_UP_LENGTH < 1) || (TSLPRM_PXS_UP_LENGTH > 7))
#error "TSLPRM_PXS_UP_LENGTH is out of range (1 .. 7)."
#endif

//------------------------------------------------------------------------------

#ifndef TSLPRM_PXS_PASS_LENGTH
#error "TSLPRM_PXS_PASS_LENGTH is not defined."
#endif

#if ((TSLPRM_PXS_PASS_LENGTH < 1) || (TSLPRM_PXS_PASS_LENGTH > 7))
#error "TSLPRM_PXS_PASS_LENGTH is out of range (1 .. 7)."
#endif

//------------------------------------------------------------------------------

#ifndef TSLPRM_PXS_LOW_POWER_MODE
#error "TSLPRM_PXS_LOW_POWER_MODE is not defined."
#endif

#if ((TSLPRM_PXS_LOW_POWER_MODE != 0) && (TSLPRM_PXS_LOW_POWER_MODE != 1))
#error "TSLPRM_PXS_LOW_POWER_MODE is out of range (0 .. 1)."
#endif

//------------------------------------------------------------------------------

#ifndef TSLPRM_PXS_RF_DETECTION
#error "TSLPRM_PXS_RF_DETECTION is not defined."
#endif

#if ((TSLPRM_PXS_RF_DETECTION != 0) && (TSLPRM_PXS_RF_DETECTION != 1))
#error "TSLPRM_PXS_RF_DETECTION is out of range (0 .. 1)."
#endif

//------------------------------------------------------------------------------

#ifndef TSLPRM_PXS_SYNCHRONIZE
#error "TSLPRM_PXS_SYNCHRONIZE is not defined."
#endif

#if ((TSLPRM_PXS_SYNCHRONIZE != 0) && (TSLPRM_PXS_SYNCHRONIZE != 1))
#error "TSLPRM_PXS_SYNCHRONIZE is out of range (0 .. 1)."
#endif

//------------------------------------------------------------------------------

#ifndef TSLPRM_PXS_SYNCHRO_EDGE
#error "TSLPRM_PXS_SYNCHRO_EDGE is not defined."
#endif

#if ((TSLPRM_PXS_SYNCHRO_EDGE != 0) && (TSLPRM_PXS_SYNCHRO_EDGE != 1))
#error "TSLPRM_PXS_SYNCHRO_EDGE is out of range (0 .. 1)."
#endif

//------------------------------------------------------------------------------

#ifndef TSLPRM_PXS_INACTIVE_TX
#error "TSLPRM_PXS_INACTIVE_TX is not defined."
#endif

#if ((TSLPRM_PXS_INACTIVE_TX != 0) && (TSLPRM_PXS_INACTIVE_TX != 1))
#error "TSLPRM_PXS_INACTIVE_TX is out of range (0 .. 1)."
#endif

//------------------------------------------------------------------------------

#ifndef TSLPRM_PXS_INACTIVE_RX
#error "TSLPRM_PXS_INACTIVE_RX is not defined."
#endif

#if ((TSLPRM_PXS_INACTIVE_RX != 0) && (TSLPRM_PXS_INACTIVE_RX != 1))
#error "TSLPRM_PXS_INACTIVE_RX is out of range (0 .. 1)."
#endif

//------------------------------------------------------------------------------

#ifndef TSLPRM_PXS_RX_COUPLING
#error "TSLPRM_PXS_RX_COUPLING is not defined."
#endif

#if ((TSLPRM_PXS_RX_COUPLING != 0) && (TSLPRM_PXS_RX_COUPLING != 1))
#error "TSLPRM_PXS_RX_COUPLING is out of range (0 .. 1)."
#endif

//------------------------------------------------------------------------------

#ifndef TSLPRM_PXS_STAB
#error "TSLPRM_PXS_STAB is not defined."
#endif

#if ((TSLPRM_PXS_STAB != LONG_STAB) && (TSLPRM_PXS_STAB != MEDIUM_STAB) && (TSLPRM_PXS_STAB != SHORT_STAB))
#error "TSLPRM_PXS_STAB is out of range (LONG_STAB, MEDIUM_STAB, SHORT_STAB)."
#endif

//------------------------------------------------------------------------------

#ifndef TSLPRM_PXS_BIAS
#error "TSLPRM_PXS_BIAS is not defined."
#endif

#if ((TSLPRM_PXS_BIAS != HIGH_BIAS) && (TSLPRM_PXS_BIAS != MEDIUM_BIAS) && (TSLPRM_PXS_BIAS != LOW_BIAS) && (TSLPRM_PXS_BIAS != VERY_LOW_BIAS))
#error "TSLPRM_PXS_BIAS is out of range (HIGH_BIAS, MEDIUM_BIAS, LOW_BIAS, VERY_LOW_BIAS)."
#endif

//------------------------------------------------------------------------------

#ifndef TSLPRM_HIGH_CHANNEL_NB
#error "TSLPRM_HIGH_CHANNEL_NB is not defined."
#endif

#if ((TSLPRM_HIGH_CHANNEL_NB < 0) || (TSLPRM_HIGH_CHANNEL_NB > __MAX_RX))
#error "TSLPRM_HIGH_CHANNEL_NB is out of range (0..9 for STM8TL53C4, 0..7 for STM8TL53G4)."
#endif

#endif /* __TSL_CHECK_CONFIG_STM8TL5X_H */

/************************ (C) COPYRIGHT STMicroelectronics *****END OF FILE****/
