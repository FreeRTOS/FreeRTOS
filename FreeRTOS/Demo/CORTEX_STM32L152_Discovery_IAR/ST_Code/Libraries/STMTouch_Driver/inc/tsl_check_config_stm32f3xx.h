/**
  ******************************************************************************
  * @file    tsl_check_config_stm32f3xx.h
  * @author  MCD Application Team
  * @version V1.3.2
  * @date    22-January-2013
  * @brief   This file contains the check of all parameters defined in the
  *          STM32F3XX configuration file.
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
#ifndef __TSL_CHECK_CONFIG_STM32F3XX_H
#define __TSL_CHECK_CONFIG_STM32F3XX_H

//------------------------------------------------------------------------------

#if ((TSLPRM_TOTAL_CHANNELS < 1) || (TSLPRM_TOTAL_CHANNELS > 24))
#error "TSLPRM_TOTAL_CHANNELS is out of range (1 .. 24)."
#endif

#if ((TSLPRM_TOTAL_BANKS < 1) || (TSLPRM_TOTAL_BANKS > 8))
#error "TSLPRM_TOTAL_BANKS is out of range (1 .. 8)."
#endif

#if ((TSLPRM_TOTAL_TOUCHKEYS < 0) || (TSLPRM_TOTAL_TOUCHKEYS > 24))
#error "TSLPRM_TOTAL_TOUCHKEYS is out of range (0 .. 24)."
#endif

#if ((TSLPRM_TOTAL_TOUCHKEYS_B < 0) || (TSLPRM_TOTAL_TOUCHKEYS_B > 24))
#error "TSLPRM_TOTAL_TOUCHKEYS_B is out of range (0 .. 24)."
#endif

#if ((TSLPRM_TOTAL_LINROTS < 0) || (TSLPRM_TOTAL_LINROTS > 24))
#error "TSLPRM_TOTAL_LINROTS is out of range (0 .. 24)."
#endif

#if ((TSLPRM_TOTAL_LINROTS_B < 0) || (TSLPRM_TOTAL_LINROTS_B > 24))
#error "TSLPRM_TOTAL_LINROTS_B is out of range (0 .. 24)."
#endif

#if ((TSLPRM_TOTAL_OBJECTS < 1) || (TSLPRM_TOTAL_OBJECTS > 24))
#error "TSLPRM_TOTAL_OBJECTS is out of range (1 .. 24)."
#endif

#if ((TSLPRM_TOTAL_TKEYS + TSLPRM_TOTAL_LNRTS) > 24)
#error "The Sum of TouchKeys and Linear/Rotary sensors exceeds 24."
#endif

//------------------------------------------------------------------------------

#ifndef TSLPRM_TSC_GPIO_CONFIG
#error "TSLPRM_TSC_GPIO_CONFIG is not defined."
#endif

#if ((TSLPRM_TSC_GPIO_CONFIG < 0) || (TSLPRM_TSC_GPIO_CONFIG > 1))
#error "TSLPRM_TSC_GPIO_CONFIG is out of range (0 .. 1)."
#endif

//------------------------------------------------------------------------------

#ifndef TSLPRM_TSC_CTPH
#error "TSLPRM_TSC_CTPH is not defined."
#endif

#if ((TSLPRM_TSC_CTPH < 0) || (TSLPRM_TSC_CTPH > 15))
#error "TSLPRM_TSC_CTPH is out of range (0 .. 15)."
#endif

//------------------------------------------------------------------------------

#ifndef TSLPRM_TSC_CTPL
#error "TSLPRM_TSC_CTPL is not defined."
#endif

#if ((TSLPRM_TSC_CTPL < 0) || (TSLPRM_TSC_CTPL > 15))
#error "TSLPRM_TSC_CTPL is out of range (0 .. 15)."
#endif

//------------------------------------------------------------------------------

#ifndef TSLPRM_TSC_PGPSC
#error "TSLPRM_TSC_PGPSC is not defined."
#endif

#if ((TSLPRM_TSC_PGPSC < 0) || (TSLPRM_TSC_PGPSC > 7))
#error "TSLPRM_TSC_PGPSC is out of range (0 .. 7)."
#endif

//------------------------------------------------------------------------------

#if (TSLPRM_ACQ_MAX > 0) && (TSLPRM_ACQ_MAX < 256)
#define TSLPRM_TSC_MCV 0 // 255
#endif

#if (TSLPRM_ACQ_MAX > 255) && (TSLPRM_ACQ_MAX < 512)
#define TSLPRM_TSC_MCV 1 // 511
#endif

#if (TSLPRM_ACQ_MAX > 511) && (TSLPRM_ACQ_MAX < 1024)
#define TSLPRM_TSC_MCV 2 // 1023
#endif

#if (TSLPRM_ACQ_MAX > 1023) && (TSLPRM_ACQ_MAX < 2048)
#define TSLPRM_TSC_MCV 3 // 2047
#endif

#if (TSLPRM_ACQ_MAX > 2047) && (TSLPRM_ACQ_MAX < 4096)
#define TSLPRM_TSC_MCV 4 // 4095
#endif

#if (TSLPRM_ACQ_MAX > 4095) && (TSLPRM_ACQ_MAX < 8192)
#define TSLPRM_TSC_MCV 5 // 8191
#endif

#if (TSLPRM_ACQ_MAX > 8191)
#define TSLPRM_TSC_MCV 6 // 16383
#endif

#ifndef TSLPRM_TSC_MCV
#error "TSLPRM_TSC_MCV is not defined."
#endif

#if ((TSLPRM_TSC_MCV < 0) || (TSLPRM_TSC_MCV > 6))
#error "TSLPRM_TSC_MCV is out of range (0 .. 6)."
#endif

//------------------------------------------------------------------------------

#ifndef TSLPRM_TSC_IODEF
#error "TSLPRM_TSC_IODEF is not defined."
#endif

#if ((TSLPRM_TSC_IODEF < 0) || (TSLPRM_TSC_IODEF > 1))
#error "TSLPRM_TSC_IODEF is out of range (0 .. 1)."
#endif

//------------------------------------------------------------------------------

#ifndef TSLPRM_TSC_AM
#error "TSLPRM_TSC_AM is not defined."
#endif

#if ((TSLPRM_TSC_AM < 0) || (TSLPRM_TSC_AM > 1))
#error "TSLPRM_TSC_AM is out of range (0 .. 1)."
#endif

//------------------------------------------------------------------------------

#ifndef TSLPRM_TSC_SYNC_PIN
#error "TSLPRM_TSC_SYNC_PIN is not defined."
#endif

#if ((TSLPRM_TSC_SYNC_PIN < 0) || (TSLPRM_TSC_SYNC_PIN > 1))
#error "TSLPRM_TSC_SYNC_PIN is out of range (0 .. 1)."
#endif

//------------------------------------------------------------------------------

#ifndef TSLPRM_TSC_SYNC_POL
#error "TSLPRM_TSC_SYNC_POL is not defined."
#endif

#if ((TSLPRM_TSC_SYNC_POL < 0) || (TSLPRM_TSC_SYNC_POL > 1))
#error "TSLPRM_TSC_SYNC_POL is out of range (0 .. 1)."
#endif

//------------------------------------------------------------------------------

#ifndef TSLPRM_TSC_USE_SS
#error "TSLPRM_TSC_USE_SS is not defined."
#endif

#if ((TSLPRM_TSC_USE_SS < 0) || (TSLPRM_TSC_USE_SS > 1))
#error "TSLPRM_TSC_USE_SS is out of range (0 .. 1)."
#endif

//------------------------------------------------------------------------------

#ifndef TSLPRM_TSC_SSD
#error "TSLPRM_TSC_SSD is not defined."
#endif

#if ((TSLPRM_TSC_SSD < 0) || (TSLPRM_TSC_SSD > 127))
#error "TSLPRM_TSC_SSD is out of range (0 .. 127)."
#endif

//------------------------------------------------------------------------------

#ifndef TSLPRM_TSC_SSPSC
#error "TSLPRM_TSC_SSPSC is not defined."
#endif

#if ((TSLPRM_TSC_SSPSC < 0) || (TSLPRM_TSC_SSPSC > 1))
#error "TSLPRM_TSC_SSPSC is out of range (0 .. 1)."
#endif

#endif /* __TSL_CHECK_CONFIG_STM32F3XX_H */

/************************ (C) COPYRIGHT STMicroelectronics *****END OF FILE****/
