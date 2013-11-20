/**
  ******************************************************************************
  * @file    tsl_acq_stm32f0xx.c
  * @author  MCD Application Team
  * @version V1.3.2
  * @date    22-January-2013
  * @brief   This file contains all functions to manage the TSC acquisition
  *          on STM32F0xx products.
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

/* Includes ------------------------------------------------------------------*/
#include "tsl_acq_stm32f0xx.h"
#include "tsl_globals.h"
#include "stm32f0xx_it.h"

/* Private typedefs ----------------------------------------------------------*/
/* Private defines -----------------------------------------------------------*/
#define TSL_DELAY_DISCHARGE (1000)

#define NU      (0) // Not Used IO
#define CHANNEL (1) // Channel IO
#define SHIELD  (2) // Shield IO (= Channel IO but not acquired)
#define SAMPCAP (3) // Sampling Capacitor IO

/* Private macros ------------------------------------------------------------*/
#define IS_BANK_INDEX_OK(INDEX)   (((INDEX) == 0) || (((INDEX) > 0) && ((INDEX) < TSLPRM_TOTAL_BANKS)))
#define IS_SOURCE_INDEX_OK(INDEX) (((INDEX) == 0) || (((INDEX) > 0) && ((INDEX) < TSLPRM_TOTAL_CHANNELS)))

/* Private variables ---------------------------------------------------------*/

/* Private functions prototype -----------------------------------------------*/
void SoftDelay(uint32_t val);

/**
  * @brief  Initializes the TouchSensing GPIOs.
  * @param  None
  * @retval None
  */
void TSL_acq_InitGPIOs(void)
{

  GPIO_InitTypeDef GPIO_InitStructure;
  uint32_t tmp_value_0;
  uint32_t tmp_value_1;

  //====================
  // GPIOs configuration
  //====================

  // Enable GPIOs clocks
  RCC->AHBENR |= (RCC_AHBENR_GPIOAEN | RCC_AHBENR_GPIOBEN | RCC_AHBENR_GPIOCEN);

  // Alternate function Output Open-Drain for Sampling Capacitor IOs
  //----------------------------------------------------------------

  GPIO_InitStructure.GPIO_Mode = GPIO_Mode_AF;
  GPIO_InitStructure.GPIO_OType = GPIO_OType_OD;
  GPIO_InitStructure.GPIO_Speed = GPIO_Speed_2MHz;
  GPIO_InitStructure.GPIO_PuPd = GPIO_PuPd_NOPULL;

  // GPIOA
  GPIO_InitStructure.GPIO_Pin = 0;
#if TSLPRM_TSC_GROUP1_IO1 == SAMPCAP
  GPIO_InitStructure.GPIO_Pin |= GPIO_Pin_0;
#endif
#if TSLPRM_TSC_GROUP1_IO2 == SAMPCAP
  GPIO_InitStructure.GPIO_Pin |= GPIO_Pin_1;
#endif
#if TSLPRM_TSC_GROUP1_IO3 == SAMPCAP
  GPIO_InitStructure.GPIO_Pin |= GPIO_Pin_2;
#endif
#if TSLPRM_TSC_GROUP1_IO4 == SAMPCAP
  GPIO_InitStructure.GPIO_Pin |= GPIO_Pin_3;
#endif
#if TSLPRM_TSC_GROUP2_IO1 == SAMPCAP
  GPIO_InitStructure.GPIO_Pin |= GPIO_Pin_4;
#endif
#if TSLPRM_TSC_GROUP2_IO2 == SAMPCAP
  GPIO_InitStructure.GPIO_Pin |= GPIO_Pin_5;
#endif
#if TSLPRM_TSC_GROUP2_IO3 == SAMPCAP
  GPIO_InitStructure.GPIO_Pin |= GPIO_Pin_6;
#endif
#if TSLPRM_TSC_GROUP2_IO4 == SAMPCAP
  GPIO_InitStructure.GPIO_Pin |= GPIO_Pin_7;
#endif
#if TSLPRM_TSC_GROUP4_IO1 == SAMPCAP
  GPIO_InitStructure.GPIO_Pin |= GPIO_Pin_9;
#endif
#if TSLPRM_TSC_GROUP4_IO2 == SAMPCAP
  GPIO_InitStructure.GPIO_Pin |= GPIO_Pin_10;
#endif
#if TSLPRM_TSC_GROUP4_IO3 == SAMPCAP
  GPIO_InitStructure.GPIO_Pin |= GPIO_Pin_11;
#endif
#if TSLPRM_TSC_GROUP4_IO4 == SAMPCAP
  GPIO_InitStructure.GPIO_Pin |= GPIO_Pin_12;
#endif
  if (GPIO_InitStructure.GPIO_Pin != 0)
  {
    GPIO_Init(GPIOA, &GPIO_InitStructure);
  }

  // GPIOB
  GPIO_InitStructure.GPIO_Pin = 0;
#if TSLPRM_TSC_GROUP3_IO2 == SAMPCAP
  GPIO_InitStructure.GPIO_Pin |= GPIO_Pin_0;
#endif
#if TSLPRM_TSC_GROUP3_IO3 == SAMPCAP
  GPIO_InitStructure.GPIO_Pin |= GPIO_Pin_1;
#endif
#if TSLPRM_TSC_GROUP3_IO4 == SAMPCAP
  GPIO_InitStructure.GPIO_Pin |= GPIO_Pin_2;
#endif
#if TSLPRM_TSC_GROUP5_IO1 == SAMPCAP
  GPIO_InitStructure.GPIO_Pin |= GPIO_Pin_3;
#endif
#if TSLPRM_TSC_GROUP5_IO2 == SAMPCAP
  GPIO_InitStructure.GPIO_Pin |= GPIO_Pin_4;
#endif
#if TSLPRM_TSC_GROUP5_IO3 == SAMPCAP
  GPIO_InitStructure.GPIO_Pin |= GPIO_Pin_6;
#endif
#if TSLPRM_TSC_GROUP5_IO4 == SAMPCAP
  GPIO_InitStructure.GPIO_Pin |= GPIO_Pin_7;
#endif
#if TSLPRM_TSC_GROUP6_IO1 == SAMPCAP
  GPIO_InitStructure.GPIO_Pin |= GPIO_Pin_11;
#endif
#if TSLPRM_TSC_GROUP6_IO2 == SAMPCAP
  GPIO_InitStructure.GPIO_Pin |= GPIO_Pin_12;
#endif
#if TSLPRM_TSC_GROUP6_IO3 == SAMPCAP
  GPIO_InitStructure.GPIO_Pin |= GPIO_Pin_13;
#endif
#if TSLPRM_TSC_GROUP6_IO4 == SAMPCAP
  GPIO_InitStructure.GPIO_Pin |= GPIO_Pin_14;
#endif
  if (GPIO_InitStructure.GPIO_Pin != 0)
  {
    GPIO_Init(GPIOB, &GPIO_InitStructure);
  }

  // GPIOC
#if TSLPRM_TSC_GROUP3_IO1 == SAMPCAP
  GPIO_InitStructure.GPIO_Pin = GPIO_Pin_5;
  GPIO_Init(GPIOC, &GPIO_InitStructure);
#endif

  // Alternate function Output Push-Pull for Channel and Shield IOs
  //---------------------------------------------------------------

  GPIO_InitStructure.GPIO_OType = GPIO_OType_PP;

  // GPIOA
  GPIO_InitStructure.GPIO_Pin = 0;
#if (TSLPRM_TSC_GROUP1_IO1 == CHANNEL) || (TSLPRM_TSC_GROUP1_IO1 == SHIELD)
  GPIO_InitStructure.GPIO_Pin |= GPIO_Pin_0;
#endif
#if (TSLPRM_TSC_GROUP1_IO2 == CHANNEL) || (TSLPRM_TSC_GROUP1_IO2 == SHIELD)
  GPIO_InitStructure.GPIO_Pin |= GPIO_Pin_1;
#endif
#if (TSLPRM_TSC_GROUP1_IO3 == CHANNEL) || (TSLPRM_TSC_GROUP1_IO3 == SHIELD)
  GPIO_InitStructure.GPIO_Pin |= GPIO_Pin_2;
#endif
#if (TSLPRM_TSC_GROUP1_IO4 == CHANNEL) || (TSLPRM_TSC_GROUP1_IO4 == SHIELD)
  GPIO_InitStructure.GPIO_Pin |= GPIO_Pin_3;
#endif
#if (TSLPRM_TSC_GROUP2_IO1 == CHANNEL) || (TSLPRM_TSC_GROUP2_IO1 == SHIELD)
  GPIO_InitStructure.GPIO_Pin |= GPIO_Pin_4;
#endif
#if (TSLPRM_TSC_GROUP2_IO2 == CHANNEL) || (TSLPRM_TSC_GROUP2_IO2 == SHIELD)
  GPIO_InitStructure.GPIO_Pin |= GPIO_Pin_5;
#endif
#if (TSLPRM_TSC_GROUP2_IO3 == CHANNEL) || (TSLPRM_TSC_GROUP2_IO3 == SHIELD)
  GPIO_InitStructure.GPIO_Pin |= GPIO_Pin_6;
#endif
#if (TSLPRM_TSC_GROUP2_IO4 == CHANNEL) || (TSLPRM_TSC_GROUP2_IO4 == SHIELD)
  GPIO_InitStructure.GPIO_Pin |= GPIO_Pin_7;
#endif
#if (TSLPRM_TSC_GROUP4_IO1 == CHANNEL) || (TSLPRM_TSC_GROUP4_IO1 == SHIELD)
  GPIO_InitStructure.GPIO_Pin |= GPIO_Pin_9;
#endif
#if (TSLPRM_TSC_GROUP4_IO2 == CHANNEL) || (TSLPRM_TSC_GROUP4_IO2 == SHIELD)
  GPIO_InitStructure.GPIO_Pin |= GPIO_Pin_10;
#endif
#if (TSLPRM_TSC_GROUP4_IO3 == CHANNEL) || (TSLPRM_TSC_GROUP4_IO3 == SHIELD)
  GPIO_InitStructure.GPIO_Pin |= GPIO_Pin_11;
#endif
#if (TSLPRM_TSC_GROUP4_IO4 == CHANNEL) || (TSLPRM_TSC_GROUP4_IO4 == SHIELD)
  GPIO_InitStructure.GPIO_Pin |= GPIO_Pin_12;
#endif
  if (GPIO_InitStructure.GPIO_Pin != 0)
  {
    GPIO_Init(GPIOA, &GPIO_InitStructure);
  }

  // GPIOB
  GPIO_InitStructure.GPIO_Pin = 0;
#if (TSLPRM_TSC_GROUP3_IO2 == CHANNEL) || (TSLPRM_TSC_GROUP3_IO2 == SHIELD)
  GPIO_InitStructure.GPIO_Pin |= GPIO_Pin_0;
#endif
#if (TSLPRM_TSC_GROUP3_IO3 == CHANNEL) || (TSLPRM_TSC_GROUP3_IO3 == SHIELD)
  GPIO_InitStructure.GPIO_Pin |= GPIO_Pin_1;
#endif
#if (TSLPRM_TSC_GROUP3_IO4 == CHANNEL) || (TSLPRM_TSC_GROUP3_IO4 == SHIELD)
  GPIO_InitStructure.GPIO_Pin |= GPIO_Pin_2;
#endif
#if (TSLPRM_TSC_GROUP5_IO1 == CHANNEL) || (TSLPRM_TSC_GROUP5_IO1 == SHIELD)
  GPIO_InitStructure.GPIO_Pin |= GPIO_Pin_3;
#endif
#if (TSLPRM_TSC_GROUP5_IO2 == CHANNEL) || (TSLPRM_TSC_GROUP5_IO2 == SHIELD)
  GPIO_InitStructure.GPIO_Pin |= GPIO_Pin_4;
#endif
#if (TSLPRM_TSC_GROUP5_IO3 == CHANNEL) || (TSLPRM_TSC_GROUP5_IO3 == SHIELD)
  GPIO_InitStructure.GPIO_Pin |= GPIO_Pin_6;
#endif
#if (TSLPRM_TSC_GROUP5_IO4 == CHANNEL) || (TSLPRM_TSC_GROUP5_IO4 == SHIELD)
  GPIO_InitStructure.GPIO_Pin |= GPIO_Pin_7;
#endif
#if (TSLPRM_TSC_GROUP6_IO1 == CHANNEL) || (TSLPRM_TSC_GROUP6_IO1 == SHIELD)
  GPIO_InitStructure.GPIO_Pin |= GPIO_Pin_11;
#endif
#if (TSLPRM_TSC_GROUP6_IO2 == CHANNEL) || (TSLPRM_TSC_GROUP6_IO2 == SHIELD)
  GPIO_InitStructure.GPIO_Pin |= GPIO_Pin_12;
#endif
#if (TSLPRM_TSC_GROUP6_IO3 == CHANNEL) || (TSLPRM_TSC_GROUP6_IO3 == SHIELD)
  GPIO_InitStructure.GPIO_Pin |= GPIO_Pin_13;
#endif
#if (TSLPRM_TSC_GROUP6_IO4 == CHANNEL) || (TSLPRM_TSC_GROUP6_IO4 == SHIELD)
  GPIO_InitStructure.GPIO_Pin |= GPIO_Pin_14;
#endif
  if (GPIO_InitStructure.GPIO_Pin != 0)
  {
    GPIO_Init(GPIOB, &GPIO_InitStructure);
  }

  // GPIOC
#if (TSLPRM_TSC_GROUP3_IO1 == CHANNEL) || (TSLPRM_TSC_GROUP3_IO1 == SHIELD)
  GPIO_InitStructure.GPIO_Pin = GPIO_Pin_5;
  GPIO_Init(GPIOC, &GPIO_InitStructure);
#endif

  // Set Alternate-Function AF3 for GPIOA and GPIOB
  //-----------------------------------------------

  // GPIOA
  tmp_value_0 = 0;
  tmp_value_1 = 0;
#if TSLPRM_TSC_GROUP1_IO1 != NU
  tmp_value_0 |= (uint32_t)((uint32_t)3 << (0 * 4));
#endif
#if TSLPRM_TSC_GROUP1_IO2 != NU
  tmp_value_0 |= (uint32_t)((uint32_t)3 << (1 * 4));
#endif
#if TSLPRM_TSC_GROUP1_IO3 != NU
  tmp_value_0 |= (uint32_t)((uint32_t)3 << (2 * 4));
#endif
#if TSLPRM_TSC_GROUP1_IO4 != NU
  tmp_value_0 |= (uint32_t)((uint32_t)3 << (3 * 4));
#endif
#if TSLPRM_TSC_GROUP2_IO1 != NU
  tmp_value_0 |= (uint32_t)((uint32_t)3 << (4 * 4));
#endif
#if TSLPRM_TSC_GROUP2_IO2 != NU
  tmp_value_0 |= (uint32_t)((uint32_t)3 << (5 * 4));
#endif
#if TSLPRM_TSC_GROUP2_IO3 != NU
  tmp_value_0 |= (uint32_t)((uint32_t)3 << (6 * 4));
#endif
#if TSLPRM_TSC_GROUP2_IO4 != NU
  tmp_value_0 |= (uint32_t)((uint32_t)3 << (7 * 4));
#endif
#if TSLPRM_TSC_GROUP4_IO1 != NU
  tmp_value_1 |= (uint32_t)((uint32_t)3 << (1 * 4));
#endif
#if TSLPRM_TSC_GROUP4_IO2 != NU
  tmp_value_1 |= (uint32_t)((uint32_t)3 << (2 * 4));
#endif
#if TSLPRM_TSC_GROUP4_IO3 != NU
  tmp_value_1 |= (uint32_t)((uint32_t)3 << (3 * 4));
#endif
#if TSLPRM_TSC_GROUP4_IO4 != NU
  tmp_value_1 |= (uint32_t)((uint32_t)3 << (4 * 4));
#endif
  if (tmp_value_0 != 0) {GPIOA->AFR[0] |= tmp_value_0;}
  if (tmp_value_1 != 0) {GPIOA->AFR[1] |= tmp_value_1;}

  // GPIOB
  tmp_value_0 = 0;
  tmp_value_1 = 0;
#if TSLPRM_TSC_GROUP3_IO2 != NU
  tmp_value_0 |= (uint32_t)((uint32_t)3 << (0 * 4));
#endif
#if TSLPRM_TSC_GROUP3_IO3 != NU
  tmp_value_0 |= (uint32_t)((uint32_t)3 << (1 * 4));
#endif
#if TSLPRM_TSC_GROUP3_IO4 != NU
  tmp_value_0 |= (uint32_t)((uint32_t)3 << (2 * 4));
#endif
#if TSLPRM_TSC_GROUP5_IO1 != NU
  tmp_value_0 |= (uint32_t)((uint32_t)3 << (3 * 4));
#endif
#if TSLPRM_TSC_GROUP5_IO2 != NU
  tmp_value_0 |= (uint32_t)((uint32_t)3 << (4 * 4));
#endif
#if TSLPRM_TSC_GROUP5_IO3 != NU
  tmp_value_0 |= (uint32_t)((uint32_t)3 << (6 * 4));
#endif
#if TSLPRM_TSC_GROUP5_IO4 != NU
  tmp_value_0 |= (uint32_t)((uint32_t)3 << (7 * 4));
#endif
#if TSLPRM_TSC_GROUP6_IO1 != NU
  tmp_value_1 |= (uint32_t)((uint32_t)3 << (3 * 4));
#endif
#if TSLPRM_TSC_GROUP6_IO2 != NU
  tmp_value_1 |= (uint32_t)((uint32_t)3 << (4 * 4));
#endif
#if TSLPRM_TSC_GROUP6_IO3 != NU
  tmp_value_1 |= (uint32_t)((uint32_t)3 << (5 * 4));
#endif
#if TSLPRM_TSC_GROUP6_IO4 != NU
  tmp_value_1 |= (uint32_t)((uint32_t)3 << (6 * 4));
#endif
  if (tmp_value_0 != 0) {GPIOB->AFR[0] |= tmp_value_0;}
  if (tmp_value_1 != 0) {GPIOB->AFR[1] |= tmp_value_1;}

  //==================
  // TSC configuration
  //==================

  // Enable TSC clock
  RCC->AHBENR |= RCC_AHBENR_TSEN;

  // Disable Schmitt trigger hysteresis on all used TS IOs (Channel, Shield and Sampling IOs)
  //-----------------------------------------------------------------------------------------

  tmp_value_0 = 0xFFFFFFFF;
#if TSLPRM_TSC_GROUP1_IO1 != NU
  tmp_value_0 &= (uint32_t)~((uint32_t)1 << 0);
#endif
#if TSLPRM_TSC_GROUP1_IO2 != NU
  tmp_value_0 &= (uint32_t)~((uint32_t)1 << 1);
#endif
#if TSLPRM_TSC_GROUP1_IO3 != NU
  tmp_value_0 &= (uint32_t)~((uint32_t)1 << 2);
#endif
#if TSLPRM_TSC_GROUP1_IO4 != NU
  tmp_value_0 &= (uint32_t)~((uint32_t)1 << 3);
#endif
#if TSLPRM_TSC_GROUP2_IO1 != NU
  tmp_value_0 &= (uint32_t)~((uint32_t)1 << 4);
#endif
#if TSLPRM_TSC_GROUP2_IO2 != NU
  tmp_value_0 &= (uint32_t)~((uint32_t)1 << 5);
#endif
#if TSLPRM_TSC_GROUP2_IO3 != NU
  tmp_value_0 &= (uint32_t)~((uint32_t)1 << 6);
#endif
#if TSLPRM_TSC_GROUP2_IO4 != NU
  tmp_value_0 &= (uint32_t)~((uint32_t)1 << 7);
#endif
#if TSLPRM_TSC_GROUP3_IO1 != NU
  tmp_value_0 &= (uint32_t)~((uint32_t)1 << 8);
#endif
#if TSLPRM_TSC_GROUP3_IO2 != NU
  tmp_value_0 &= (uint32_t)~((uint32_t)1 << 9);
#endif
#if TSLPRM_TSC_GROUP3_IO3 != NU
  tmp_value_0 &= (uint32_t)~((uint32_t)1 << 10);
#endif
#if TSLPRM_TSC_GROUP3_IO4 != NU
  tmp_value_0 &= (uint32_t)~((uint32_t)1 << 11);
#endif
#if TSLPRM_TSC_GROUP4_IO1 != NU
  tmp_value_0 &= (uint32_t)~((uint32_t)1 << 12);
#endif
#if TSLPRM_TSC_GROUP4_IO2 != NU
  tmp_value_0 &= (uint32_t)~((uint32_t)1 << 13);
#endif
#if TSLPRM_TSC_GROUP4_IO3 != NU
  tmp_value_0 &= (uint32_t)~((uint32_t)1 << 14);
#endif
#if TSLPRM_TSC_GROUP4_IO4 != NU
  tmp_value_0 &= (uint32_t)~((uint32_t)1 << 15);
#endif
#if TSLPRM_TSC_GROUP5_IO1 != NU
  tmp_value_0 &= (uint32_t)~((uint32_t)1 << 16);
#endif
#if TSLPRM_TSC_GROUP5_IO2 != NU
  tmp_value_0 &= (uint32_t)~((uint32_t)1 << 17);
#endif
#if TSLPRM_TSC_GROUP5_IO3 != NU
  tmp_value_0 &= (uint32_t)~((uint32_t)1 << 18);
#endif
#if TSLPRM_TSC_GROUP5_IO4 != NU
  tmp_value_0 &= (uint32_t)~((uint32_t)1 << 19);
#endif
#if TSLPRM_TSC_GROUP6_IO1 != NU
  tmp_value_0 &= (uint32_t)~((uint32_t)1 << 20);
#endif
#if TSLPRM_TSC_GROUP6_IO2 != NU
  tmp_value_0 &= (uint32_t)~((uint32_t)1 << 21);
#endif
#if TSLPRM_TSC_GROUP6_IO3 != NU
  tmp_value_0 &= (uint32_t)~((uint32_t)1 << 22);
#endif
#if TSLPRM_TSC_GROUP6_IO4 != NU
  tmp_value_0 &= (uint32_t)~((uint32_t)1 << 23);
#endif
  if (tmp_value_0 != 0xFFFFFFFF) {TSC->IOHCR &= tmp_value_0;}

  // Set Sampling Capacitor IOs
  //---------------------------

  tmp_value_0 = 0;
#if TSLPRM_TSC_GROUP1_IO1 == SAMPCAP
  tmp_value_0 |= (uint32_t)((uint32_t)1 << 0);
#endif
#if TSLPRM_TSC_GROUP1_IO2 == SAMPCAP
  tmp_value_0 |= (uint32_t)((uint32_t)1 << 1);
#endif
#if TSLPRM_TSC_GROUP1_IO3 == SAMPCAP
  tmp_value_0 |= (uint32_t)((uint32_t)1 << 2);
#endif
#if TSLPRM_TSC_GROUP1_IO4 == SAMPCAP
  tmp_value_0 |= (uint32_t)((uint32_t)1 << 3);
#endif
#if TSLPRM_TSC_GROUP2_IO1 == SAMPCAP
  tmp_value_0 |= (uint32_t)((uint32_t)1 << 4);
#endif
#if TSLPRM_TSC_GROUP2_IO2 == SAMPCAP
  tmp_value_0 |= (uint32_t)((uint32_t)1 << 5);
#endif
#if TSLPRM_TSC_GROUP2_IO3 == SAMPCAP
  tmp_value_0 |= (uint32_t)((uint32_t)1 << 6);
#endif
#if TSLPRM_TSC_GROUP2_IO4 == SAMPCAP
  tmp_value_0 |= (uint32_t)((uint32_t)1 << 7);
#endif
#if TSLPRM_TSC_GROUP3_IO1 == SAMPCAP
  tmp_value_0 |= (uint32_t)((uint32_t)1 << 8);
#endif
#if TSLPRM_TSC_GROUP3_IO2 == SAMPCAP
  tmp_value_0 |= (uint32_t)((uint32_t)1 << 9);
#endif
#if TSLPRM_TSC_GROUP3_IO3 == SAMPCAP
  tmp_value_0 |= (uint32_t)((uint32_t)1 << 10);
#endif
#if TSLPRM_TSC_GROUP3_IO4 == SAMPCAP
  tmp_value_0 |= (uint32_t)((uint32_t)1 << 11);
#endif
#if TSLPRM_TSC_GROUP4_IO1 == SAMPCAP
  tmp_value_0 |= (uint32_t)((uint32_t)1 << 12);
#endif
#if TSLPRM_TSC_GROUP4_IO2 == SAMPCAP
  tmp_value_0 |= (uint32_t)((uint32_t)1 << 13);
#endif
#if TSLPRM_TSC_GROUP4_IO3 == SAMPCAP
  tmp_value_0 |= (uint32_t)((uint32_t)1 << 14);
#endif
#if TSLPRM_TSC_GROUP4_IO4 == SAMPCAP
  tmp_value_0 |= (uint32_t)((uint32_t)1 << 15);
#endif
#if TSLPRM_TSC_GROUP5_IO1 == SAMPCAP
  tmp_value_0 |= (uint32_t)((uint32_t)1 << 16);
#endif
#if TSLPRM_TSC_GROUP5_IO2 == SAMPCAP
  tmp_value_0 |= (uint32_t)((uint32_t)1 << 17);
#endif
#if TSLPRM_TSC_GROUP5_IO3 == SAMPCAP
  tmp_value_0 |= (uint32_t)((uint32_t)1 << 18);
#endif
#if TSLPRM_TSC_GROUP5_IO4 == SAMPCAP
  tmp_value_0 |= (uint32_t)((uint32_t)1 << 19);
#endif
#if TSLPRM_TSC_GROUP6_IO1 == SAMPCAP
  tmp_value_0 |= (uint32_t)((uint32_t)1 << 20);
#endif
#if TSLPRM_TSC_GROUP6_IO2 == SAMPCAP
  tmp_value_0 |= (uint32_t)((uint32_t)1 << 21);
#endif
#if TSLPRM_TSC_GROUP6_IO3 == SAMPCAP
  tmp_value_0 |= (uint32_t)((uint32_t)1 << 22);
#endif
#if TSLPRM_TSC_GROUP6_IO4 == SAMPCAP
  tmp_value_0 |= (uint32_t)((uint32_t)1 << 23);
#endif
  if (tmp_value_0 != 0) {TSC->IOSCR |= tmp_value_0;}

}


/**
  * @brief  Initializes the acquisition module.
  * @param  None
  * @retval Status
  */
TSL_Status_enum_T TSL_acq_Init(void)
{

#if TSLPRM_TSC_GPIO_CONFIG > 0
  TSL_acq_InitGPIOs();
#endif

  // Enable TSC clock
  RCC->AHBENR |= RCC_AHBENR_TSEN;

  // TSC enabled
  TSC->CR = 0x01;

  // Set CTPH
  TSC->CR |= (uint32_t)((uint32_t)TSLPRM_TSC_CTPH << 28) & 0xF0000000;

  // Set CTPL
  TSC->CR |= (uint32_t)((uint32_t)TSLPRM_TSC_CTPL << 24) & 0x0F000000;

  // Set SpreadSpectrum
  TSC->CR |= (uint32_t)((uint32_t)TSLPRM_TSC_USE_SS << 16) & 0x00010000;
  TSC->CR |= (uint32_t)((uint32_t)TSLPRM_TSC_SSD << 17) & 0x00FE0000;
  TSC->CR |= (uint32_t)((uint32_t)TSLPRM_TSC_SSPSC << 15) & 0x00008000;

  // Set Prescaler
  TSC->CR |= (uint32_t)((uint32_t)TSLPRM_TSC_PGPSC << 12) & 0x00007000;

  // Set Max Count
  TSC->CR |= (uint32_t)((uint32_t)TSLPRM_TSC_MCV << 5) & 0x000000E0;

  // Set IO default in Output PP Low to discharge all capacitors
  TSC->CR &= (uint32_t)(~(1 << 4));

  // Set Synchronization Mode
#if TSLPRM_TSC_AM > 0

  // Set Synchronization Pin in Alternate-Function mode
  RCC->AHBENR |= RCC_AHBENR_GPIOBEN; // Set GPIOB clock

#if TSLPRM_TSC_SYNC_PIN == 0 // PB08
  GPIOB->MODER  &= 0xFFFCFFFF;
  GPIOB->MODER  |= 0x00020000;
  GPIOB->AFR[1] |= 0x00000003;
#else // PB10
  GPIOB->MODER  &= 0xFFCFFFFF;
  GPIOB->MODER  |= 0x00200000;
  GPIOB->AFR[1] |= 0x00000300;
#endif

  // Set Synchronization Polarity
  TSC->CR |= (uint32_t)((uint32_t)TSLPRM_TSC_SYNC_POL << 3) & 0x00000008;

#endif

  // Set acquisition mode
  TSC->CR |= (uint32_t)((uint32_t)TSLPRM_TSC_AM << 2) & 0x00000004;

#if TSLPRM_USE_ACQ_INTERRUPT > 0

  // Set both EOA and MCE interrupts
  TSC->IER |= 0x03;

  // Configure NVIC
  NVIC_SetPriority(TS_IRQn, 0);
  NVIC_EnableIRQ(TS_IRQn);

#endif

  return TSL_STATUS_OK;

}


/**
  * @brief Configures a Bank.
  * @param[in] idx_bk  Index of the Bank to configure
  * @retval Status
  */
TSL_Status_enum_T TSL_acq_BankConfig(TSL_tIndex_T idx_bk)
{
  TSL_tIndex_T idx_ch;
  uint32_t objs; /* bit field of TSL_ObjStatus_enum_T type */
  uint32_t gx;
  uint32_t ioy;
  CONST TSL_Bank_T *bank = &(TSL_Globals.Bank_Array[idx_bk]);
  CONST TSL_ChannelSrc_T *pchSrc = bank->p_chSrc;
  CONST TSL_ChannelDest_T *pchDest = bank->p_chDest;

  // Check parameters (if USE_FULL_ASSERT is defined)
  assert_param(IS_BANK_INDEX_OK(idx_bk));

  // Mark the current bank processed
  TSL_Globals.This_Bank = idx_bk;

  //++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
  // Enable the Gx_IOy used as channels (channels + shield)
  TSC->IOCCR = bank->msk_IOCCR_channels;
  // Enable acquisition on selected Groups
  TSC->IOGCSR = bank->msk_IOGCSR_groups;
  //++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

  // For all channels of the bank check if they are OFF or BURST_ONLY
  // and set acquisition status flag
  for (idx_ch = 0; idx_ch < bank->NbChannels; idx_ch++)
  {

    // Check Object status flag
    objs = bank->p_chData[pchDest->IdxDest].Flags.ObjStatus;

    if (objs != TSL_OBJ_STATUS_ON)
    {
      //++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
      // Get the Channel Group mask
      gx = pchSrc->msk_IOGCSR_group;
      // Stop acquisition of the Group
      TSC->IOGCSR &= (uint32_t)~gx;
      //++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

      if (objs == TSL_OBJ_STATUS_OFF)
      {
        //++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
        // Get the Channel IO mask
        ioy = pchSrc->msk_IOCCR_channel;
        // Stop Burst of the Channel
        TSC->IOCCR &= (uint32_t)~ioy;
        //++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
      }
    }

    // Next channel
    pchSrc++;
    pchDest++;
  }

  return TSL_STATUS_OK;
}


/**
  * @brief Start acquisition on a previously configured bank
  * @param None
  * @retval None
  */
void TSL_acq_BankStartAcq(void)
{
  // Clear both EOAIC and MCEIC flags
  TSC->ICR |= 0x03;

  // Wait capacitors discharge
  SoftDelay(TSL_DELAY_DISCHARGE);

#if TSLPRM_TSC_IODEF > 0 // Default = Input Floating
  // Set IO default in Input Floating
  TSC->CR |= (1 << 4);
#endif

  // Start acquisition
  TSC->CR |= 0x02;
}


/**
  * @brief Wait end of acquisition
  * @param None
  * @retval Status
  */
TSL_Status_enum_T TSL_acq_BankWaitEOC(void)
{
  TSL_Status_enum_T retval = TSL_STATUS_BUSY;

  // Check EOAF flag
  if (TSC->ISR & 0x01)
  {

#if TSLPRM_TSC_IODEF > 0 // Default = Input Floating
    // Set IO default in Output PP Low to discharge all capacitors
    TSC->CR &= (uint32_t)(~(1 << 4));
#endif

    // Check MCEF flag
    if (TSC->ISR & 0x02)
    {
      retval = TSL_STATUS_ERROR;
    }
    else
    {
      retval = TSL_STATUS_OK;
    }
  }

  return retval;
}


/**
  * @brief Return the current measure
  * @param[in] index Index of the measure source
  * @retval Measure
  */
TSL_tMeas_T TSL_acq_GetMeas(TSL_tIndex_T index)
{
  return(TSC->IOGXCR[index]);
}


/**
  * @brief Compute the Delta value
  * @param[in] ref Reference value
  * @param[in] meas Last Measurement value
  * @retval Delta value
  */
TSL_tDelta_T TSL_acq_ComputeDelta(TSL_tRef_T ref, TSL_tMeas_T meas)
{
  return((TSL_tDelta_T)(ref - meas));
}


/**
  * @brief Compute the Measurement value
  * @param[in] ref Reference value
  * @param[in] delta Delta value
  * @retval Measurement value
  */
TSL_tMeas_T TSL_acq_ComputeMeas(TSL_tRef_T ref, TSL_tDelta_T delta)
{
  return((TSL_tMeas_T)(ref - delta));
}


/**
  * @brief  Check noise (not used)
  * @param  None
  * @retval Status
  */
TSL_AcqStatus_enum_T TSL_acq_CheckNoise(void)
{
  return TSL_ACQ_STATUS_OK;
}


/**
  * @brief Check if a filter must be used on the current channel (not used)
  * @param[in] pCh Pointer on the channel data information
  * @retval Result TRUE if a filter can be applied
  */
TSL_Bool_enum_T TSL_acq_UseFilter(TSL_ChannelData_T *pCh)
{
  return TSL_TRUE;
}


/**
  * @brief Test if the Reference is incorrect (not used)
  * @param[in] pCh Pointer on the channel data information
  * @retval Result TRUE if the Reference is out of range
  */
TSL_Bool_enum_T TSL_acq_TestReferenceOutOfRange(TSL_ChannelData_T *pCh)
{
  return TSL_FALSE;
}


/**
  * @brief Test if the measure has crossed the reference target (not used)
  * @param[in] pCh Pointer on the channel data information
  * @param[in] new_meas Measure of the last acquisition on this channel
  * @retval Result TRUE if the Reference is valid
  */
TSL_Bool_enum_T TSL_acq_TestFirstReferenceIsValid(TSL_ChannelData_T *pCh, TSL_tMeas_T new_meas)
{
  return TSL_TRUE;
}


#if defined(__IAR_SYSTEMS_ICC__) // IAR/EWARM
#pragma optimize=low
#elif defined(__CC_ARM) // Keil/MDK-ARM
#pragma O1
#pragma Ospace
#elif defined(__TASKING__) // Altium/Tasking
#pragma optimize O0
#elif defined(__GNUC__) // Atollic/True Studio + Raisonance/RKit
#pragma GCC push_options
#pragma GCC optimize ("O0")
#endif
/**
  * @brief  Software delay (private routine)
  * @param  val Wait delay
  * @retval None
  */
void SoftDelay(uint32_t val)
{
  __IO uint32_t i;
  for (i = val; i > 0; i--)
  {}
}
#if defined(__TASKING__)
#pragma endoptimize
#endif

/************************ (C) COPYRIGHT STMicroelectronics *****END OF FILE****/
