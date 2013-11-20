/**
  ******************************************************************************
  * @file    tsl.c
  * @author  MCD Application Team
  * @version V1.3.2
  * @date    22-January-2013
  * @brief   This file contains the STMTouch Driver main functions.
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
#include "tsl.h"

/* Private typedefs ----------------------------------------------------------*/
/* Private defines -----------------------------------------------------------*/
/* Private macros ------------------------------------------------------------*/
/* Private variables ---------------------------------------------------------*/
/* Private functions prototype -----------------------------------------------*/

/**
  * @brief  Initializes the TS interface.
  * @param  bank  Array holding all the banks
  * @retval Status
  */
TSL_Status_enum_T TSL_Init(CONST TSL_Bank_T *bank)
{
  TSL_Status_enum_T retval;

  // Get banks array
  TSL_Globals.Bank_Array = bank;

  // Initialization of the timing module
  retval = TSL_tim_Init();

  if (retval == TSL_STATUS_OK)
  {
    // Initialization of the acquisition module
    retval = TSL_acq_Init();
  }

  return retval;
}

/************************ (C) COPYRIGHT STMicroelectronics *****END OF FILE****/
