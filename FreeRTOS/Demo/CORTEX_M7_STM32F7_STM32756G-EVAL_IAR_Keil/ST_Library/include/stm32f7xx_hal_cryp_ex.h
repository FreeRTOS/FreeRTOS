/**
  ******************************************************************************
  * @file    stm32f7xx_hal_cryp_ex.h
  * @author  MCD Application Team
  * @version V1.0.0
  * @date    12-May-2015
  * @brief   Header file of CRYP HAL Extension module.
  ******************************************************************************
  * @attention
  *
  * <h2><center>&copy; COPYRIGHT(c) 2015 STMicroelectronics</center></h2>
  *
  * Redistribution and use in source and binary forms, with or without modification,
  * are permitted provided that the following conditions are met:
  *   1. Redistributions of source code must retain the above copyright notice,
  *      this list of conditions and the following disclaimer.
  *   2. Redistributions in binary form must reproduce the above copyright notice,
  *      this list of conditions and the following disclaimer in the documentation
  *      and/or other materials provided with the distribution.
  *   3. Neither the name of STMicroelectronics nor the names of its contributors
  *      may be used to endorse or promote products derived from this software
  *      without specific prior written permission.
  *
  * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
  * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
  * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
  * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
  * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
  * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
  * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
  * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
  * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
  * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
  *
  ******************************************************************************
  */ 

/* Define to prevent recursive inclusion -------------------------------------*/
#ifndef __STM32F7xx_HAL_CRYP_EX_H
#define __STM32F7xx_HAL_CRYP_EX_H

#ifdef __cplusplus
 extern "C" {
#endif

#if defined(STM32F756xx)
/* Includes ------------------------------------------------------------------*/
#include "stm32f7xx_hal_def.h"

/** @addtogroup STM32F7xx_HAL_Driver
  * @{
  */

/** @addtogroup CRYPEx
  * @{
  */

/* Exported types ------------------------------------------------------------*/ 
/* Exported constants --------------------------------------------------------*/
   
/** @defgroup CRYPEx_Exported_Constants   CRYPEx Exported Constants
  * @{
  */

/** @defgroup CRYPEx_Exported_Constants_Group1 CRYP AlgoModeDirection
  * @{
  */ 
#define CRYP_CR_ALGOMODE_AES_GCM_ENCRYPT   ((uint32_t)0x00080000)
#define CRYP_CR_ALGOMODE_AES_GCM_DECRYPT   ((uint32_t)0x00080004)
#define CRYP_CR_ALGOMODE_AES_CCM_ENCRYPT   ((uint32_t)0x00080008)
#define CRYP_CR_ALGOMODE_AES_CCM_DECRYPT   ((uint32_t)0x0008000C)
/**
  * @}
  */

/** @defgroup CRYPEx_Exported_Constants_Group3 CRYP PhaseConfig
  * @brief    The phases are relevant only to AES-GCM and AES-CCM
  * @{
  */ 
#define CRYP_PHASE_INIT           ((uint32_t)0x00000000)
#define CRYP_PHASE_HEADER         CRYP_CR_GCM_CCMPH_0
#define CRYP_PHASE_PAYLOAD        CRYP_CR_GCM_CCMPH_1
#define CRYP_PHASE_FINAL          CRYP_CR_GCM_CCMPH
/**
  * @}
  */
  
/**
  * @}
  */

/* Exported macro ------------------------------------------------------------*/
/** @defgroup CRYPEx_Exported_Macros CRYP Exported Macros
  * @{
  */
  
/**
  * @brief  Set the phase: Init, header, payload, final. 
  *         This is relevant only for GCM and CCM modes.
  * @param  __HANDLE__: specifies the CRYP handle.
  * @param  __PHASE__: The phase.
  * @retval None
  */
#define __HAL_CRYP_SET_PHASE(__HANDLE__, __PHASE__)  do{(__HANDLE__)->Instance->CR &= (uint32_t)(~CRYP_CR_GCM_CCMPH);\
                                                        (__HANDLE__)->Instance->CR |= (uint32_t)(__PHASE__);\
                                                       }while(0)

/**
  * @}
  */

/* Exported functions --------------------------------------------------------*/
/** @defgroup CRYPEx_Exported_Functions CRYPEx Exported Functions
  * @{
  */

/** @addtogroup CRYPEx_Exported_Functions_Group1
  * @{
  */  
    
/* AES encryption/decryption using polling  ***********************************/
HAL_StatusTypeDef HAL_CRYPEx_AESGCM_Encrypt(CRYP_HandleTypeDef *hcryp, uint8_t *pPlainData, uint16_t Size, uint8_t *pCypherData, uint32_t Timeout);
HAL_StatusTypeDef HAL_CRYPEx_AESGCM_Decrypt(CRYP_HandleTypeDef *hcryp, uint8_t *pCypherData, uint16_t Size, uint8_t *pPlainData, uint32_t Timeout);
HAL_StatusTypeDef HAL_CRYPEx_AESGCM_Finish(CRYP_HandleTypeDef *hcryp, uint32_t Size, uint8_t *AuthTag, uint32_t Timeout);
HAL_StatusTypeDef HAL_CRYPEx_AESCCM_Encrypt(CRYP_HandleTypeDef *hcryp, uint8_t *pPlainData, uint16_t Size, uint8_t *pCypherData, uint32_t Timeout);
HAL_StatusTypeDef HAL_CRYPEx_AESCCM_Decrypt(CRYP_HandleTypeDef *hcryp, uint8_t *pCypherData, uint16_t Size, uint8_t *pPlainData, uint32_t Timeout);
HAL_StatusTypeDef HAL_CRYPEx_AESCCM_Finish(CRYP_HandleTypeDef *hcryp, uint8_t *AuthTag, uint32_t Timeout);

/* AES encryption/decryption using interrupt  *********************************/
HAL_StatusTypeDef HAL_CRYPEx_AESGCM_Encrypt_IT(CRYP_HandleTypeDef *hcryp, uint8_t *pPlainData, uint16_t Size, uint8_t *pCypherData);
HAL_StatusTypeDef HAL_CRYPEx_AESGCM_Decrypt_IT(CRYP_HandleTypeDef *hcryp, uint8_t *pCypherData, uint16_t Size, uint8_t *pPlainData);
HAL_StatusTypeDef HAL_CRYPEx_AESCCM_Encrypt_IT(CRYP_HandleTypeDef *hcryp, uint8_t *pPlainData, uint16_t Size, uint8_t *pCypherData);
HAL_StatusTypeDef HAL_CRYPEx_AESCCM_Decrypt_IT(CRYP_HandleTypeDef *hcryp, uint8_t *pCypherData, uint16_t Size, uint8_t *pPlainData);

/* AES encryption/decryption using DMA  ***************************************/
HAL_StatusTypeDef HAL_CRYPEx_AESGCM_Encrypt_DMA(CRYP_HandleTypeDef *hcryp, uint8_t *pPlainData, uint16_t Size, uint8_t *pCypherData);
HAL_StatusTypeDef HAL_CRYPEx_AESGCM_Decrypt_DMA(CRYP_HandleTypeDef *hcryp, uint8_t *pCypherData, uint16_t Size, uint8_t *pPlainData);
HAL_StatusTypeDef HAL_CRYPEx_AESCCM_Encrypt_DMA(CRYP_HandleTypeDef *hcryp, uint8_t *pPlainData, uint16_t Size, uint8_t *pCypherData);
HAL_StatusTypeDef HAL_CRYPEx_AESCCM_Decrypt_DMA(CRYP_HandleTypeDef *hcryp, uint8_t *pCypherData, uint16_t Size, uint8_t *pPlainData);

/**
  * @}
  */ 
  
/** @addtogroup CRYPEx_Exported_Functions_Group2
  * @{
  */  
    
void HAL_CRYPEx_GCMCCM_IRQHandler(CRYP_HandleTypeDef *hcryp);

/**
  * @}
  */ 
 
 /**
  * @}
  */ 
 

 /* Private types -------------------------------------------------------------*/
/** @defgroup CRYPEx_Private_Types CRYPEx Private Types
  * @{
  */

/**
  * @}
  */ 

/* Private variables ---------------------------------------------------------*/
/** @defgroup CRYPEx_Private_Variables CRYPEx Private Variables
  * @{
  */

/**
  * @}
  */ 

/* Private constants ---------------------------------------------------------*/
/** @defgroup CRYPEx_Private_Constants CRYPEx Private Constants
  * @{
  */

/**
  * @}
  */ 

/* Private macros ------------------------------------------------------------*/
/** @defgroup CRYPEx_Private_Macros CRYPEx Private Macros
  * @{
  */

 /**
  * @}
  */ 
  
/* Private functions ---------------------------------------------------------*/
/** @defgroup CRYPEx_Private_Functions CRYPEx Private Functions
  * @{
  */

/**
  * @}
  */
   
/**
  * @}
  */ 

#endif /* STM32F756xx */

/**
  * @}
  */ 
  
#ifdef __cplusplus
}
#endif

#endif /* __STM32F7xx_HAL_CRYP_EX_H */

/************************ (C) COPYRIGHT STMicroelectronics *****END OF FILE****/
