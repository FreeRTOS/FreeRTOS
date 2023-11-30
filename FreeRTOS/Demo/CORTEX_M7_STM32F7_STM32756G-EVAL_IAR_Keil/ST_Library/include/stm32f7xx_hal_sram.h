/**
  ******************************************************************************
  * @file    stm32f7xx_hal_sram.h
  * @author  MCD Application Team
  * @version V1.0.0
  * @date    12-May-2015
  * @brief   Header file of SRAM HAL module.
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
#ifndef __STM32F7xx_HAL_SRAM_H
#define __STM32F7xx_HAL_SRAM_H

#ifdef __cplusplus
 extern "C" {
#endif

/* Includes ------------------------------------------------------------------*/
#include "stm32f7xx_ll_fmc.h"

/** @addtogroup STM32F7xx_HAL_Driver
  * @{
  */
/** @addtogroup SRAM
  * @{
  */ 

/* Exported typedef ----------------------------------------------------------*/

/** @defgroup SRAM_Exported_Types SRAM Exported Types
  * @{
  */
/** 
  * @brief  HAL SRAM State structures definition  
  */ 
typedef enum
{
  HAL_SRAM_STATE_RESET     = 0x00,  /*!< SRAM not yet initialized or disabled           */
  HAL_SRAM_STATE_READY     = 0x01,  /*!< SRAM initialized and ready for use             */
  HAL_SRAM_STATE_BUSY      = 0x02,  /*!< SRAM internal process is ongoing               */
  HAL_SRAM_STATE_ERROR     = 0x03,  /*!< SRAM error state                               */
  HAL_SRAM_STATE_PROTECTED = 0x04   /*!< SRAM peripheral NORSRAM device write protected */
  
}HAL_SRAM_StateTypeDef;

/** 
  * @brief  SRAM handle Structure definition  
  */ 
typedef struct
{
  FMC_NORSRAM_TypeDef           *Instance;  /*!< Register base address                        */ 
  
  FMC_NORSRAM_EXTENDED_TypeDef  *Extended;  /*!< Extended mode register base address          */
  
  FMC_NORSRAM_InitTypeDef       Init;       /*!< SRAM device control configuration parameters */

  HAL_LockTypeDef               Lock;       /*!< SRAM locking object                          */ 
  
  __IO HAL_SRAM_StateTypeDef    State;      /*!< SRAM device access state                     */
  
  DMA_HandleTypeDef             *hdma;      /*!< Pointer DMA handler                          */
  
}SRAM_HandleTypeDef; 

/**
  * @}
  */

/* Exported constants --------------------------------------------------------*/
/* Exported macro ------------------------------------------------------------*/

/** @defgroup SRAM_Exported_Macros SRAM Exported Macros
 * @{
 */

/** @brief Reset SRAM handle state
  * @param  __HANDLE__: SRAM handle
  * @retval None
  */
#define __HAL_SRAM_RESET_HANDLE_STATE(__HANDLE__) ((__HANDLE__)->State = HAL_SRAM_STATE_RESET)

/**
  * @}
  */

/* Exported functions --------------------------------------------------------*/
/** @addtogroup SRAM_Exported_Functions SRAM Exported Functions
  * @{
  */

/** @addtogroup SRAM_Exported_Functions_Group1 Initialization and de-initialization functions
 * @{
 */

/* Initialization/de-initialization functions  ********************************/
HAL_StatusTypeDef HAL_SRAM_Init(SRAM_HandleTypeDef *hsram, FMC_NORSRAM_TimingTypeDef *Timing, FMC_NORSRAM_TimingTypeDef *ExtTiming);
HAL_StatusTypeDef HAL_SRAM_DeInit(SRAM_HandleTypeDef *hsram);
void HAL_SRAM_MspInit(SRAM_HandleTypeDef *hsram);
void HAL_SRAM_MspDeInit(SRAM_HandleTypeDef *hsram);

/**
  * @}
  */

/** @addtogroup SRAM_Exported_Functions_Group2 Input Output and memory control functions
 * @{
 */

/* I/O operation functions  ***************************************************/
HAL_StatusTypeDef HAL_SRAM_Read_8b(SRAM_HandleTypeDef *hsram, uint32_t *pAddress, uint8_t *pDstBuffer, uint32_t BufferSize);
HAL_StatusTypeDef HAL_SRAM_Write_8b(SRAM_HandleTypeDef *hsram, uint32_t *pAddress, uint8_t *pSrcBuffer, uint32_t BufferSize);
HAL_StatusTypeDef HAL_SRAM_Read_16b(SRAM_HandleTypeDef *hsram, uint32_t *pAddress, uint16_t *pDstBuffer, uint32_t BufferSize);
HAL_StatusTypeDef HAL_SRAM_Write_16b(SRAM_HandleTypeDef *hsram, uint32_t *pAddress, uint16_t *pSrcBuffer, uint32_t BufferSize);
HAL_StatusTypeDef HAL_SRAM_Read_32b(SRAM_HandleTypeDef *hsram, uint32_t *pAddress, uint32_t *pDstBuffer, uint32_t BufferSize);
HAL_StatusTypeDef HAL_SRAM_Write_32b(SRAM_HandleTypeDef *hsram, uint32_t *pAddress, uint32_t *pSrcBuffer, uint32_t BufferSize);
HAL_StatusTypeDef HAL_SRAM_Read_DMA(SRAM_HandleTypeDef *hsram, uint32_t *pAddress, uint32_t *pDstBuffer, uint32_t BufferSize);
HAL_StatusTypeDef HAL_SRAM_Write_DMA(SRAM_HandleTypeDef *hsram, uint32_t *pAddress, uint32_t *pSrcBuffer, uint32_t BufferSize);

void HAL_SRAM_DMA_XferCpltCallback(DMA_HandleTypeDef *hdma);
void HAL_SRAM_DMA_XferErrorCallback(DMA_HandleTypeDef *hdma);

/**
  * @}
  */
  
/** @addtogroup SRAM_Exported_Functions_Group3 Control functions
 * @{
 */

/* SRAM Control functions  ****************************************************/
HAL_StatusTypeDef HAL_SRAM_WriteOperation_Enable(SRAM_HandleTypeDef *hsram);
HAL_StatusTypeDef HAL_SRAM_WriteOperation_Disable(SRAM_HandleTypeDef *hsram);

/**
  * @}
  */

/** @addtogroup SRAM_Exported_Functions_Group4 Peripheral State functions
 * @{
 */

/* SRAM  State functions ******************************************************/
HAL_SRAM_StateTypeDef HAL_SRAM_GetState(SRAM_HandleTypeDef *hsram);

/**
  * @}
  */ 

/**
  * @}
  */
  
/**
  * @}
  */ 

/**
  * @}
  */
  
#ifdef __cplusplus
}
#endif

#endif /* __STM32F7xx_HAL_SRAM_H */

/************************ (C) COPYRIGHT STMicroelectronics *****END OF FILE****/
