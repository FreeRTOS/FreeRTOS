/**
  ******************************************************************************
  * @file    stm32f7xx_hal_wwdg.h
  * @author  MCD Application Team
  * @version V1.0.0
  * @date    12-May-2015
  * @brief   Header file of WWDG HAL module.
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
#ifndef __STM32F7xx_HAL_WWDG_H
#define __STM32F7xx_HAL_WWDG_H

#ifdef __cplusplus
 extern "C" {
#endif

/* Includes ------------------------------------------------------------------*/
#include "stm32f7xx_hal_def.h"

/** @addtogroup STM32F7xx_HAL_Driver
  * @{
  */

/** @addtogroup WWDG
  * @{
  */ 

/* Exported types ------------------------------------------------------------*/
/** @defgroup WWDG_Exported_Types WWDG Exported Types
  * @{
  */
   
/**
  * @brief  WWDG HAL State Structure definition
  */
typedef enum
{
  HAL_WWDG_STATE_RESET     = 0x00,  /*!< WWDG not yet initialized or disabled */
  HAL_WWDG_STATE_READY     = 0x01,  /*!< WWDG initialized and ready for use   */
  HAL_WWDG_STATE_BUSY      = 0x02,  /*!< WWDG internal process is ongoing     */
  HAL_WWDG_STATE_TIMEOUT   = 0x03,  /*!< WWDG timeout state                   */
  HAL_WWDG_STATE_ERROR     = 0x04   /*!< WWDG error state                     */
}HAL_WWDG_StateTypeDef;

/** 
  * @brief  WWDG Init structure definition  
  */ 
typedef struct
{
  uint32_t Prescaler;  /*!< Specifies the prescaler value of the WWDG.
                            This parameter can be a value of @ref WWDG_Prescaler */
  
  uint32_t Window;     /*!< Specifies the WWDG window value to be compared to the downcounter.
                            This parameter must be a number lower than Max_Data = 0x80 */ 
  
  uint32_t Counter;    /*!< Specifies the WWDG free-running downcounter value.
                            This parameter must be a number between Min_Data = 0x40 and Max_Data = 0x7F */

}WWDG_InitTypeDef;

/** 
  * @brief  WWDG handle Structure definition  
  */ 
typedef struct
{
  WWDG_TypeDef                 *Instance;  /*!< Register base address    */
  
  WWDG_InitTypeDef             Init;       /*!< WWDG required parameters */
  
  HAL_LockTypeDef              Lock;       /*!< WWDG locking object      */
  
  __IO HAL_WWDG_StateTypeDef   State;      /*!< WWDG communication state */
  
}WWDG_HandleTypeDef;
/**
  * @}
  */ 

/* Exported constants --------------------------------------------------------*/
/** @defgroup WWDG_Exported_Constants WWDG Exported Constants
  * @{
  */

/** @defgroup WWDG_Interrupt_definition WWDG Interrupt definition
  * @{
  */ 
#define WWDG_IT_EWI                       WWDG_CFR_EWI  /*!< Early wakeup interrupt */
/**
  * @}
  */

/** @defgroup WWDG_Flag_definition WWDG Flag definition
  * @brief WWDG Flag definition
  * @{
  */ 
#define WWDG_FLAG_EWIF                    WWDG_SR_EWIF  /*!< Early wakeup interrupt flag */
/**
  * @}
  */

/** @defgroup WWDG_Prescaler WWDG Prescaler
  * @{
  */ 
#define WWDG_PRESCALER_1                 ((uint32_t)0x00000000)  /*!< WWDG counter clock = (PCLK1/4096)/1 */
#define WWDG_PRESCALER_2                  WWDG_CFR_WDGTB0  /*!< WWDG counter clock = (PCLK1/4096)/2 */
#define WWDG_PRESCALER_4                  WWDG_CFR_WDGTB1  /*!< WWDG counter clock = (PCLK1/4096)/4 */
#define WWDG_PRESCALER_8                  WWDG_CFR_WDGTB  /*!< WWDG counter clock = (PCLK1/4096)/8 */
/**
  * @}
  */ 

/**
  * @}
  */ 

/* Exported macro ------------------------------------------------------------*/
/** @defgroup WWDG_Exported_Macros WWDG Exported Macros
  * @{
  */

/** @brief Reset WWDG handle state
  * @param  __HANDLE__: WWDG handle
  * @retval None
  */
#define __HAL_WWDG_RESET_HANDLE_STATE(__HANDLE__) ((__HANDLE__)->State = HAL_WWDG_STATE_RESET)

/**
  * @brief  Enables the WWDG peripheral.
  * @param  __HANDLE__: WWDG handle
  * @retval None
  */
#define __HAL_WWDG_ENABLE(__HANDLE__) SET_BIT((__HANDLE__)->Instance->CR, WWDG_CR_WDGA)

/**
  * @brief  Disables the WWDG peripheral.
  * @param  __HANDLE__: WWDG handle
  * @note   WARNING: This is a dummy macro for HAL code alignment.
  *         Once enable, WWDG Peripheral cannot be disabled except by a system reset.
  * @retval None
  */
#define __HAL_WWDG_DISABLE(__HANDLE__)                      /* dummy  macro */

/**
  * @brief  Gets the selected WWDG's it status.
  * @param  __HANDLE__: WWDG handle
  * @param  __INTERRUPT__: specifies the it to check.
  *        This parameter can be one of the following values:
  *            @arg WWDG_FLAG_EWIF: Early wakeup interrupt IT
  * @retval The new state of WWDG_FLAG (SET or RESET).
  */
#define __HAL_WWDG_GET_IT(__HANDLE__, __INTERRUPT__)       __HAL_WWDG_GET_FLAG((__HANDLE__),(__INTERRUPT__))

/** @brief  Clear the WWDG's interrupt pending bits
  *         bits to clear the selected interrupt pending bits.
  * @param  __HANDLE__: WWDG handle
  * @param  __INTERRUPT__: specifies the interrupt pending bit to clear.
  *         This parameter can be one of the following values:
  *            @arg WWDG_FLAG_EWIF: Early wakeup interrupt flag
  */
#define __HAL_WWDG_CLEAR_IT(__HANDLE__, __INTERRUPT__)     __HAL_WWDG_CLEAR_FLAG((__HANDLE__), (__INTERRUPT__))

/**
  * @brief  Enables the WWDG early wakeup interrupt.
  * @param  __HANDLE__: WWDG handle
  * @param  __INTERRUPT__: specifies the interrupt to enable.
  *         This parameter can be one of the following values:
  *            @arg WWDG_IT_EWI: Early wakeup interrupt
  * @note   Once enabled this interrupt cannot be disabled except by a system reset.
  * @retval None
  */
#define __HAL_WWDG_ENABLE_IT(__HANDLE__, __INTERRUPT__) SET_BIT((__HANDLE__)->Instance->CFR, (__INTERRUPT__))
    
/**
  * @brief  Disables the WWDG early wakeup interrupt.
  * @param  __HANDLE__: WWDG handle
  * @param  __INTERRUPT__: specifies the interrupt to disable.
  *         This parameter can be one of the following values:
  *            @arg WWDG_IT_EWI: Early wakeup interrupt
  * @note   WARNING: This is a dummy macro for HAL code alignment. 
  *         Once enabled this interrupt cannot be disabled except by a system reset.
  * @retval None
  */
#define __HAL_WWDG_DISABLE_IT(__HANDLE__, __INTERRUPT__)                   /* dummy  macro */
    
/**
  * @brief  Gets the selected WWDG's flag status.
  * @param  __HANDLE__: WWDG handle
  * @param  __FLAG__: specifies the flag to check.
  *         This parameter can be one of the following values:
  *            @arg WWDG_FLAG_EWIF: Early wakeup interrupt flag
  * @retval The new state of WWDG_FLAG (SET or RESET).
  */
#define __HAL_WWDG_GET_FLAG(__HANDLE__, __FLAG__) (((__HANDLE__)->Instance->SR & (__FLAG__)) == (__FLAG__))

/**
  * @brief  Clears the WWDG's pending flags.
  * @param  __HANDLE__: WWDG handle
  * @param  __FLAG__: specifies the flag to clear.
  *         This parameter can be one of the following values:
  *            @arg WWDG_FLAG_EWIF: Early wakeup interrupt flag
  * @retval None
  */
#define __HAL_WWDG_CLEAR_FLAG(__HANDLE__, __FLAG__) (((__HANDLE__)->Instance->SR) = ~(__FLAG__))

/** @brief  Checks if the specified WWDG interrupt source is enabled or disabled.
  * @param  __HANDLE__: WWDG Handle.
  * @param  __INTERRUPT__: specifies the WWDG interrupt source to check.
  *          This parameter can be one of the following values:
  *            @arg WWDG_IT_EWI: Early Wakeup Interrupt
  * @retval state of __INTERRUPT__ (TRUE or FALSE).
  */
#define __HAL_WWDG_GET_IT_SOURCE(__HANDLE__, __INTERRUPT__) (((__HANDLE__)->Instance->CFR & (__INTERRUPT__)) == (__INTERRUPT__))

/**
  * @}
  */

/* Exported functions --------------------------------------------------------*/
/** @addtogroup WWDG_Exported_Functions
  * @{
  */

/** @addtogroup WWDG_Exported_Functions_Group1
  * @{
  */
/* Initialization/de-initialization functions  **********************************/
HAL_StatusTypeDef HAL_WWDG_Init(WWDG_HandleTypeDef *hwwdg);
HAL_StatusTypeDef HAL_WWDG_DeInit(WWDG_HandleTypeDef *hwwdg);
void HAL_WWDG_MspInit(WWDG_HandleTypeDef *hwwdg);
void HAL_WWDG_MspDeInit(WWDG_HandleTypeDef *hwwdg);
void HAL_WWDG_WakeupCallback(WWDG_HandleTypeDef* hwwdg);
/**
  * @}
  */

/** @addtogroup WWDG_Exported_Functions_Group2
  * @{
  */
/* I/O operation functions ******************************************************/
HAL_StatusTypeDef HAL_WWDG_Start(WWDG_HandleTypeDef *hwwdg);
HAL_StatusTypeDef HAL_WWDG_Start_IT(WWDG_HandleTypeDef *hwwdg);
HAL_StatusTypeDef HAL_WWDG_Refresh(WWDG_HandleTypeDef *hwwdg, uint32_t Counter);
void HAL_WWDG_IRQHandler(WWDG_HandleTypeDef *hwwdg);
/**
  * @}
  */

/** @addtogroup WWDG_Exported_Functions_Group3
  * @{
  */
/* Peripheral State functions  **************************************************/
HAL_WWDG_StateTypeDef HAL_WWDG_GetState(WWDG_HandleTypeDef *hwwdg);
/**
  * @}
  */ 

/**
  * @}
  */

/* Private types -------------------------------------------------------------*/
/* Private variables ---------------------------------------------------------*/
/* Private constants ---------------------------------------------------------*/
/** @defgroup WWDG_Private_Constants WWDG Private Constants
  * @{
  */

/**
  * @}
  */

/* Private macros ------------------------------------------------------------*/
/** @defgroup WWDG_Private_Macros WWDG Private Macros
  * @{
  */
#define IS_WWDG_PRESCALER(__PRESCALER__) (((__PRESCALER__) == WWDG_PRESCALER_1) || \
                                          ((__PRESCALER__) == WWDG_PRESCALER_2) || \
                                          ((__PRESCALER__) == WWDG_PRESCALER_4) || \
                                          ((__PRESCALER__) == WWDG_PRESCALER_8))
#define IS_WWDG_WINDOW(__WINDOW__) ((__WINDOW__) <= 0x7F)
#define IS_WWDG_COUNTER(__COUNTER__) (((__COUNTER__) >= 0x40) && ((__COUNTER__) <= 0x7F))
/**
  * @}
  */

/* Private functions ---------------------------------------------------------*/
/** @defgroup WWDG_Private_Functions WWDG Private Functions
  * @{
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

#endif /* __STM32F7xx_HAL_WWDG_H */

/************************ (C) COPYRIGHT STMicroelectronics *****END OF FILE****/
