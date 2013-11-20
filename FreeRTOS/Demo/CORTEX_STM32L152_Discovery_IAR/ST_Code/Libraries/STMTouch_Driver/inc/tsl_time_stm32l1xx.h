/**
  ******************************************************************************
  * @file    tsl_time_stm32l1xx.h
  * @author  MCD Application Team
  * @version V1.3.2
  * @date    22-January-2013
  * @brief   This file contains external declarations of the tsl_time_stm32l1xx.c file.
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
#ifndef __TSL_TIME_STM32L1XX_H
#define __TSL_TIME_STM32L1XX_H

/* Includes ------------------------------------------------------------------*/
#include "stm32l1xx.h"
#include "tsl_conf_stm32l1xx.h"
#include "tsl_types.h"

/* Exported types ------------------------------------------------------------*/

TSL_Status_enum_T TSL_tim_Init(void);

#endif /* __TSL_TIME_STM32L1XX_H */

/************************ (C) COPYRIGHT STMicroelectronics *****END OF FILE****/
