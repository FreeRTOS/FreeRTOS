/**
  ******************************************************************************
  * @file    stm32l1xx_opamp.h
  * @author  MCD Application Team
  * @version V1.1.1
  * @date    05-March-2012
  * @brief   This file contains all the functions prototypes for the operational
  *          amplifiers (opamp) firmware library.
  ******************************************************************************
  * @attention
  *
  * <h2><center>&copy; COPYRIGHT 2012 STMicroelectronics</center></h2>
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
#ifndef __STM32L1xx_OPAMP_H
#define __STM32L1xx_OPAMP_H

#ifdef __cplusplus
 extern "C" {
#endif

/* Includes ------------------------------------------------------------------*/
#include "stm32l1xx.h"

/** @addtogroup STM32L1xx_StdPeriph_Driver
  * @{
  */

/** @addtogroup OPAMP
  * @{
  */

/* Exported types ------------------------------------------------------------*/
/* Exported constants --------------------------------------------------------*/

/** @defgroup OPAMP_Exported_Constants
  * @{
  */ 

/** @defgroup OPAMP_Selection
  * @{
  */

#define OPAMP_Selection_OPAMP1                    OPAMP_CSR_OPA1PD
#define OPAMP_Selection_OPAMP2                    OPAMP_CSR_OPA2PD
#define OPAMP_Selection_OPAMP3                    OPAMP_CSR_OPA3PD

#define IS_OPAMP_ALL_PERIPH(PERIPH) (((PERIPH) == OPAMP_Selection_OPAMP1) || \
                                     ((PERIPH) == OPAMP_Selection_OPAMP2) || \
                                     ((PERIPH) == OPAMP_Selection_OPAMP3))

/**
  * @}
  */ 

/** @defgroup OPAMP_Switches
  * @{
  */

/* OPAMP1 Switches */
#define OPAMP_OPAMP1Switch3           OPAMP_CSR_S3SEL1 /*!< OPAMP1 Switch 3 */
#define OPAMP_OPAMP1Switch4           OPAMP_CSR_S4SEL1 /*!< OPAMP1 Switch 4 */
#define OPAMP_OPAMP1Switch5           OPAMP_CSR_S5SEL1 /*!< OPAMP1 Switch 5 */
#define OPAMP_OPAMP1Switch6           OPAMP_CSR_S6SEL1 /*!< OPAMP1 Switch 6 */
#define OPAMP_OPAMP1SwitchANA         OPAMP_CSR_ANAWSEL1 /*!< OPAMP1 Switch ANA */

/* OPAMP2 Switches */
#define OPAMP_OPAMP2Switch3           OPAMP_CSR_S3SEL2 /*!< OPAMP2 Switch 3 */
#define OPAMP_OPAMP2Switch4           OPAMP_CSR_S4SEL2 /*!< OPAMP2 Switch 4 */
#define OPAMP_OPAMP2Switch5           OPAMP_CSR_S5SEL2 /*!< OPAMP2 Switch 5 */
#define OPAMP_OPAMP2Switch6           OPAMP_CSR_S6SEL2 /*!< OPAMP2 Switch 6 */
#define OPAMP_OPAMP2Switch7           OPAMP_CSR_S7SEL2 /*!< OPAMP2 Switch 7 */
#define OPAMP_OPAMP2SwitchANA         OPAMP_CSR_ANAWSEL2 /*!< OPAMP2 Switch ANA */

/* OPAMP3 Switches */
#define OPAMP_OPAMP3Switch3           OPAMP_CSR_S3SEL3 /*!< OPAMP3 Switch 3 */
#define OPAMP_OPAMP3Switch4           OPAMP_CSR_S4SEL3 /*!< OPAMP3 Switch 4 */
#define OPAMP_OPAMP3Switch5           OPAMP_CSR_S5SEL3 /*!< OPAMP3 Switch 5 */
#define OPAMP_OPAMP3Switch6           OPAMP_CSR_S6SEL3 /*!< OPAMP3 Switch 6 */
#define OPAMP_OPAMP3SwitchANA         OPAMP_CSR_ANAWSEL3 /*!< OPAMP3 Switch ANA */

#define IS_OPAMP_SWITCH(SWITCH) ((((SWITCH) & (uint32_t)0xF0E1E1E1) == 0x00) && ((SWITCH) != 0x00))

/**
  * @}
  */ 

/** @defgroup OPAMP_Trimming
  * @{
  */

#define OPAMP_Trimming_Factory        ((uint32_t)0x00000000) /*!< Factory trimming */
#define OPAMP_Trimming_User           OPAMP_OTR_OT_USER /*!< User trimming */

#define IS_OPAMP_TRIMMING(TRIMMING) (((TRIMMING) == OPAMP_Trimming_Factory) || \
                                     ((TRIMMING) == OPAMP_Trimming_User))

/**
  * @}
  */ 

/** @defgroup OPAMP_Input
  * @{
  */

#define OPAMP_Input_NMOS              OPAMP_CSR_OPA1CAL_H /*!< NMOS input */
#define OPAMP_Input_PMOS              OPAMP_CSR_OPA1CAL_L /*!< PMOS input */

#define IS_OPAMP_INPUT(INPUT) (((INPUT) == OPAMP_Input_NMOS) || \
                               ((INPUT) == OPAMP_Input_PMOS))

/**
  * @}
  */ 

/** @defgroup OPAMP_TrimValue
  * @{
  */

#define IS_OPAMP_TRIMMINGVALUE(VALUE) ((VALUE) <= 0x0000001F) /*!< Trimming value */

/**
  * @}
  */

/** @defgroup OPAMP_PowerRange
  * @{
  */

#define OPAMP_PowerRange_Low          ((uint32_t)0x00000000) /*!< Low power range is selected (VDDA is lower than 2.4V) */
#define OPAMP_PowerRange_High         OPAMP_CSR_AOP_RANGE    /*!< High power range is selected (VDDA is higher than 2.4V) */

#define IS_OPAMP_RANGE(RANGE) (((RANGE) == OPAMP_PowerRange_Low) || \
                               ((RANGE) == OPAMP_PowerRange_High))

/**
  * @}
  */ 
/**
  * @}
  */

/* Exported macro ------------------------------------------------------------*/
/* Exported functions ------------------------------------------------------- */
/* Initialization and Configuration functions *********************************/
void OPAMP_DeInit(void);
void OPAMP_SwitchCmd(uint32_t OPAMP_OPAMPxSwitchy, FunctionalState NewState);
void OPAMP_Cmd(uint32_t OPAMP_Selection, FunctionalState NewState);
void OPAMP_LowPowerCmd(uint32_t OPAMP_Selection, FunctionalState NewState);
void OPAMP_PowerRangeSelect(uint32_t OPAMP_PowerRange);

/* Calibration functions ******************************************************/
void OPAMP_OffsetTrimmingModeSelect(uint32_t OPAMP_Trimming);
void OPAMP_OffsetTrimConfig(uint32_t OPAMP_Selection, uint32_t OPAMP_Input, uint32_t OPAMP_TrimValue);
void OPAMP_OffsetTrimLowPowerConfig(uint32_t OPAMP_Selection, uint32_t OPAMP_Input, uint32_t OPAMP_TrimValue);
FlagStatus OPAMP_GetFlagStatus(uint32_t OPAMP_Selection);

#ifdef __cplusplus
}
#endif

#endif /*__STM32L1xx_OPAMP_H */

/**
  * @}
  */ 

/**
  * @}
  */

/************************ (C) COPYRIGHT STMicroelectronics *****END OF FILE****/
