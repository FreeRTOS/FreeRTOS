/**
  ******************************************************************************
  * @file    tsl_check_config_stm32l1xx.h
  * @author  MCD Application Team
  * @version V1.3.2
  * @date    22-January-2013
  * @brief   This file contains the check of all parameters defined in the
  *          STM32L1XX configuration file.
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
#ifndef __TSL_CHECK_CONFIG_STM32L1XX_H
#define __TSL_CHECK_CONFIG_STM32L1XX_H

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

#ifndef TSLPRM_USE_SHIELD
#error "TSLPRM_USE_SHIELD is not defined."
#endif

#if ((TSLPRM_USE_SHIELD < 0) || (TSLPRM_USE_SHIELD > 1))
#error "TSLPRM_USE_SHIELD is out of range (0 .. 1)."
#endif

//------------------------------------------------------------------------------

#ifndef TSLPRM_IODEF
#error "TSLPRM_IODEF is not defined."
#endif

#if ((TSLPRM_IODEF < 0) || (TSLPRM_IODEF > 1))
#error "TSLPRM_IODEF is out of range (0 .. 1)."
#endif

//------------------------------------------------------------------------------

#if defined(STM32L1XX_HD) && !defined(TSLPRM_STM32L1XX_HD_SW)

#ifndef TSLPRM_TIM_PRESCALER
#error "TSLPRM_TIM_PRESCALER is not defined."
#endif

#if ((TSLPRM_TIM_PRESCALER < 0) || (TSLPRM_TIM_PRESCALER > 65535))
#error "TSLPRM_TIM_PRESCALER is out of range (0 .. 65535)."
#endif

#endif

//------------------------------------------------------------------------------

#if defined(STM32L1XX_HD) && !defined(TSLPRM_STM32L1XX_HD_SW)

#ifndef TSLPRM_TIM_RELOAD
#error "TSLPRM_TIM_RELOAD is not defined."
#endif

#if ((TSLPRM_TIM_RELOAD < 4) || (TSLPRM_TIM_RELOAD > 65534))
#error "TSLPRM_TIM_RELOAD is out of range (4 .. 65534)."
#endif

#if ((TSLPRM_TIM_RELOAD % 2) != (0))
#error "TSLPRM_TIM_RELOAD is odd and must be even."
#endif

#endif

//------------------------------------------------------------------------------

#if defined(STM32L1XX_HD) && defined(TSLPRM_STM32L1XX_HD_SW)

#ifndef TSLPRM_PROTECT_IO_ACCESS
#error "TSLPRM_PROTECT_IO_ACCESS is not defined."
#endif

#if ((TSLPRM_PROTECT_IO_ACCESS < 0) || (TSLPRM_PROTECT_IO_ACCESS > 1))
#error "TSLPRM_PROTECT_IO_ACCESS is out of range (0 .. 1)."
#endif

#endif

//------------------------------------------------------------------------------

#if defined(STM32L1XX_HD) && defined(TSLPRM_STM32L1XX_HD_SW)

#ifndef TSLPRM_USE_GPIOA
#error "TSLPRM_USE_GPIOA is not defined."
#endif

#if ((TSLPRM_USE_GPIOA < 0) || (TSLPRM_USE_GPIOA > 1))
#error "TSLPRM_USE_GPIOA is out of range (0 .. 1)."
#endif

#ifndef TSLPRM_USE_GPIOB
#error "TSLPRM_USE_GPIOB is not defined."
#endif

#if ((TSLPRM_USE_GPIOB < 0) || (TSLPRM_USE_GPIOB > 1))
#error "TSLPRM_USE_GPIOB is out of range (0 .. 1)."
#endif

#ifndef TSLPRM_USE_GPIOC
#error "TSLPRM_USE_GPIOC is not defined."
#endif

#if ((TSLPRM_USE_GPIOC < 0) || (TSLPRM_USE_GPIOC > 1))
#error "TSLPRM_USE_GPIOC is out of range (0 .. 1)."
#endif

#ifndef TSLPRM_USE_GPIOF
#error "TSLPRM_USE_GPIOA is not defined."
#endif

#if ((TSLPRM_USE_GPIOF < 0) || (TSLPRM_USE_GPIOF > 1))
#error "TSLPRM_USE_GPIOF is out of range (0 .. 1)."
#endif

#ifndef TSLPRM_USE_GPIOG
#error "TSLPRM_USE_GPIOG is not defined."
#endif

#if ((TSLPRM_USE_GPIOG < 0) || (TSLPRM_USE_GPIOG > 1))
#error "TSLPRM_USE_GPIOG is out of range (0 .. 1)."
#endif

#endif

//------------------------------------------------------------------------------

#if defined(STM32L1XX_MD)

#ifndef TSLPRM_PROTECT_IO_ACCESS
#error "TSLPRM_PROTECT_IO_ACCESS is not defined."
#endif

#if ((TSLPRM_PROTECT_IO_ACCESS < 0) || (TSLPRM_PROTECT_IO_ACCESS > 1))
#error "TSLPRM_PROTECT_IO_ACCESS is out of range (0 .. 1)."
#endif

#endif

//------------------------------------------------------------------------------

#if defined(STM32L1XX_MD)

#ifndef TSLPRM_USE_GPIOA
#error "TSLPRM_USE_GPIOA is not defined."
#endif

#if ((TSLPRM_USE_GPIOA < 0) || (TSLPRM_USE_GPIOA > 1))
#error "TSLPRM_USE_GPIOA is out of range (0 .. 1)."
#endif

#ifndef TSLPRM_USE_GPIOB
#error "TSLPRM_USE_GPIOB is not defined."
#endif

#if ((TSLPRM_USE_GPIOB < 0) || (TSLPRM_USE_GPIOB > 1))
#error "TSLPRM_USE_GPIOB is out of range (0 .. 1)."
#endif

#ifndef TSLPRM_USE_GPIOC
#error "TSLPRM_USE_GPIOC is not defined."
#endif

#if ((TSLPRM_USE_GPIOC < 0) || (TSLPRM_USE_GPIOC > 1))
#error "TSLPRM_USE_GPIOC is out of range (0 .. 1)."
#endif

#ifndef TSLPRM_USE_GPIOF
#error "TSLPRM_USE_GPIOA is not defined."
#endif

#if ((TSLPRM_USE_GPIOF < 0) || (TSLPRM_USE_GPIOF > 1))
#error "TSLPRM_USE_GPIOF is out of range (0 .. 1)."
#endif

#ifndef TSLPRM_USE_GPIOG
#error "TSLPRM_USE_GPIOG is not defined."
#endif

#if ((TSLPRM_USE_GPIOG < 0) || (TSLPRM_USE_GPIOG > 1))
#error "TSLPRM_USE_GPIOG is out of range (0 .. 1)."
#endif

#endif

//------------------------------------------------------------------------------

#if defined(STM32L1XX_MDP) && !defined(TSLPRM_STM32L1XX_MDP_SW)

#ifndef TSLPRM_TIM_PRESCALER
#error "TSLPRM_TIM_PRESCALER is not defined."
#endif

#if ((TSLPRM_TIM_PRESCALER < 0) || (TSLPRM_TIM_PRESCALER > 65535))
#error "TSLPRM_TIM_PRESCALER is out of range (0 .. 65535)."
#endif

#endif

//------------------------------------------------------------------------------

#if defined(STM32L1XX_MDP) && !defined(TSLPRM_STM32L1XX_MDP_SW)

#ifndef TSLPRM_TIM_RELOAD
#error "TSLPRM_TIM_RELOAD is not defined."
#endif

#if ((TSLPRM_TIM_RELOAD < 4) || (TSLPRM_TIM_RELOAD > 65534))
#error "TSLPRM_TIM_RELOAD is out of range (4 .. 65534)."
#endif

#if ((TSLPRM_TIM_RELOAD % 2) != (0))
#error "TSLPRM_TIM_RELOAD is odd and must be even."
#endif

#endif

//------------------------------------------------------------------------------

#if defined(STM32L1XX_MDP) && defined(TSLPRM_STM32L1XX_MDP_SW)

#ifndef TSLPRM_PROTECT_IO_ACCESS
#error "TSLPRM_PROTECT_IO_ACCESS is not defined."
#endif

#if ((TSLPRM_PROTECT_IO_ACCESS < 0) || (TSLPRM_PROTECT_IO_ACCESS > 1))
#error "TSLPRM_PROTECT_IO_ACCESS is out of range (0 .. 1)."
#endif

#endif

//------------------------------------------------------------------------------

#if defined(STM32L1XX_MDP) && defined(TSLPRM_STM32L1XX_MDP_SW)

#ifndef TSLPRM_USE_GPIOA
#error "TSLPRM_USE_GPIOA is not defined."
#endif

#if ((TSLPRM_USE_GPIOA < 0) || (TSLPRM_USE_GPIOA > 1))
#error "TSLPRM_USE_GPIOA is out of range (0 .. 1)."
#endif

#ifndef TSLPRM_USE_GPIOB
#error "TSLPRM_USE_GPIOB is not defined."
#endif

#if ((TSLPRM_USE_GPIOB < 0) || (TSLPRM_USE_GPIOB > 1))
#error "TSLPRM_USE_GPIOB is out of range (0 .. 1)."
#endif

#ifndef TSLPRM_USE_GPIOC
#error "TSLPRM_USE_GPIOC is not defined."
#endif

#if ((TSLPRM_USE_GPIOC < 0) || (TSLPRM_USE_GPIOC > 1))
#error "TSLPRM_USE_GPIOC is out of range (0 .. 1)."
#endif

#ifndef TSLPRM_USE_GPIOF
#error "TSLPRM_USE_GPIOA is not defined."
#endif

#if ((TSLPRM_USE_GPIOF < 0) || (TSLPRM_USE_GPIOF > 1))
#error "TSLPRM_USE_GPIOF is out of range (0 .. 1)."
#endif

#ifndef TSLPRM_USE_GPIOG
#error "TSLPRM_USE_GPIOG is not defined."
#endif

#if ((TSLPRM_USE_GPIOG < 0) || (TSLPRM_USE_GPIOG > 1))
#error "TSLPRM_USE_GPIOG is out of range (0 .. 1)."
#endif

#endif

#endif /* __TSL_CHECK_CONFIG_STM32L1XX_H */

/************************ (C) COPYRIGHT STMicroelectronics *****END OF FILE****/
