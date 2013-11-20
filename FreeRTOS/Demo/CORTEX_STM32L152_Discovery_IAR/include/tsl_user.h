/**
  ******************************************************************************
  * @file    STM32L152_Ex06_Linear_DISC\inc\tsl_user.h
  * @author  MCD Application Team
  * @version V1.0.3
  * @date    May-2013
  * @brief   Touch-Sensing user configuration and api file.
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
#ifndef __TSL_USER_H
#define __TSL_USER_H

#include "tsl.h"

// LEDs definition on STM32L152B-DISC board
// PB7 = LED_GREEN
#define LED_GREEN_TOGGLE {GPIOB->ODR ^=  (1<<7);}
#define LED_GREEN_OFF    {GPIOB->ODR &= ~(1<<7);}
#define LED_GREEN_ON     {GPIOB->ODR |=  (1<<7);}
// PB6 = LED_BLUE
#define LED_BLUE_TOGGLE  {GPIOB->ODR ^=  (1<<6);}
#define LED_BLUE_OFF     {GPIOB->ODR &= ~(1<<6);}
#define LED_BLUE_ON      {GPIOB->ODR |=  (1<<6);}

//==============================================================================
// IOs definition
//==============================================================================

// Channel IOs definition
#define CHANNEL_0_SRC              ((uint32_t)(GR2))
#define CHANNEL_0_DEST             (0)
#define CHANNEL_0_SAMPLE_CONFIG    TSL_GROUP2_IO2
#define CHANNEL_0_CHANNEL_CONFIG   TSL_GROUP2_IO1

#define CHANNEL_1_SRC              ((uint32_t)(GR9))
#define CHANNEL_1_DEST             (1)
#define CHANNEL_1_SAMPLE_CONFIG    TSL_GROUP9_IO2
#define CHANNEL_1_CHANNEL_CONFIG   TSL_GROUP9_IO1

#define CHANNEL_2_SRC              ((uint32_t)(GR3))
#define CHANNEL_2_DEST             (2)
#define CHANNEL_2_SAMPLE_CONFIG    TSL_GROUP3_IO2
#define CHANNEL_2_CHANNEL_CONFIG   TSL_GROUP3_IO1

// Banks definition
#define BANK_0_NBCHANNELS          (3)
#define BANK_0_INDEX               (0) // Index of 1st channel used
#define BANK_0_SHIELD_SAMPLE       (0)
#define BANK_0_SHIELD_CHANNEL      (0)

// User Parameters
extern TSL_ObjectGroup_T MyObjGroup;
extern CONST TSL_Object_T MyObjects[];
extern CONST TSL_Bank_T MyBanks[];
extern CONST TSL_LinRot_T MyLinRots[];

void MyLinRots_ErrorStateProcess(void);
void MyLinRots_OffStateProcess(void);

void TSL_user_Init(void);
TSL_Status_enum_T TSL_user_Action(void);
void ProcessSensors(void);
void ProcessSensorsButtons(void);


#endif /* __TSL_USER_H */

/************************ (C) COPYRIGHT STMicroelectronics *****END OF FILE****/
