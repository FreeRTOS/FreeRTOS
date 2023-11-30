/**
  ******************************************************************************
  * @file    stm32f7xx_hal_dcmi.h
  * @author  MCD Application Team
  * @version V1.0.0
  * @date    12-May-2015
  * @brief   Header file of DCMI HAL module.
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
#ifndef __STM32F7xx_HAL_DCMI_H
#define __STM32F7xx_HAL_DCMI_H

#ifdef __cplusplus
 extern "C" {
#endif

/* Includes ------------------------------------------------------------------*/
#include "stm32f7xx_hal_def.h"

/* Include DCMI HAL Extended module */
/* (include on top of file since DCMI structures are defined in extended file) */
#include "stm32f7xx_hal_dcmi_ex.h"
	 
/** @addtogroup STM32F7xx_HAL_Driver
  * @{
  */

/** @addtogroup DCMI DCMI
  * @brief DCMI HAL module driver
  * @{
  */  

/* Exported types ------------------------------------------------------------*/
/** @defgroup DCMI_Exported_Types DCMI Exported Types
  * @{
  */
/** 
  * @brief  HAL DCMI State structures definition
  */ 
typedef enum
{
  HAL_DCMI_STATE_RESET             = 0x00,  /*!< DCMI not yet initialized or disabled  */
  HAL_DCMI_STATE_READY             = 0x01,  /*!< DCMI initialized and ready for use    */
  HAL_DCMI_STATE_BUSY              = 0x02,  /*!< DCMI internal processing is ongoing   */
  HAL_DCMI_STATE_TIMEOUT           = 0x03,  /*!< DCMI timeout state                    */
  HAL_DCMI_STATE_ERROR             = 0x04   /*!< DCMI error state                      */
}HAL_DCMI_StateTypeDef;

/** 
  * @brief  DCMI handle Structure definition
  */
typedef struct
{
  DCMI_TypeDef                  *Instance;           /*!< DCMI Register base address   */

  DCMI_InitTypeDef              Init;                /*!< DCMI parameters              */

  HAL_LockTypeDef               Lock;                /*!< DCMI locking object          */

  __IO HAL_DCMI_StateTypeDef    State;               /*!< DCMI state                   */

  __IO uint32_t                 XferCount;           /*!< DMA transfer counter         */

  __IO uint32_t                 XferSize;            /*!< DMA transfer size            */

  uint32_t                      XferTransferNumber;  /*!< DMA transfer number          */

  uint32_t                      pBuffPtr;            /*!< Pointer to DMA output buffer */

  DMA_HandleTypeDef             *DMA_Handle;         /*!< Pointer to the DMA handler   */

  __IO uint32_t                 ErrorCode;           /*!< DCMI Error code              */

}DCMI_HandleTypeDef;
/**
  * @}
  */
/* Exported constants --------------------------------------------------------*/

/** @defgroup DCMI_Exported_Constants DCMI Exported Constants
  * @{
  */

/** @defgroup DCMI_Error_Code DCMI Error Code
  * @{
  */
#define HAL_DCMI_ERROR_NONE      ((uint32_t)0x00000000)    /*!< No error              */
#define HAL_DCMI_ERROR_OVF       ((uint32_t)0x00000001)    /*!< Overflow error        */
#define HAL_DCMI_ERROR_SYNC      ((uint32_t)0x00000002)    /*!< Synchronization error */
#define HAL_DCMI_ERROR_TIMEOUT   ((uint32_t)0x00000020)    /*!< Timeout error         */
/**
  * @}
  */

/** @defgroup DCMI_Capture_Mode DCMI Capture Mode
  * @{
  */ 
#define DCMI_MODE_CONTINUOUS           ((uint32_t)0x00000000)  /*!< The received data are transferred continuously 
                                                                    into the destination memory through the DMA             */
#define DCMI_MODE_SNAPSHOT             ((uint32_t)DCMI_CR_CM)  /*!< Once activated, the interface waits for the start of 
                                                                    frame and then transfers a single frame through the DMA */
/**
  * @}
  */

/** @defgroup DCMI_Synchronization_Mode DCMI Synchronization Mode
  * @{
  */ 
#define DCMI_SYNCHRO_HARDWARE        ((uint32_t)0x00000000)   /*!< Hardware synchronization data capture (frame/line start/stop)
                                                                   is synchronized with the HSYNC/VSYNC signals                  */
#define DCMI_SYNCHRO_EMBEDDED        ((uint32_t)DCMI_CR_ESS)  /*!< Embedded synchronization data capture is synchronized with 
                                                                   synchronization codes embedded in the data flow               */

/**
  * @}
  */

/** @defgroup DCMI_PIXCK_Polarity DCMI PIXCK Polarity
  * @{
  */
#define DCMI_PCKPOLARITY_FALLING    ((uint32_t)0x00000000)      /*!< Pixel clock active on Falling edge */
#define DCMI_PCKPOLARITY_RISING     ((uint32_t)DCMI_CR_PCKPOL)  /*!< Pixel clock active on Rising edge  */

/**
  * @}
  */

/** @defgroup DCMI_VSYNC_Polarity DCMI VSYNC Polarity
  * @{
  */
#define DCMI_VSPOLARITY_LOW     ((uint32_t)0x00000000)     /*!< Vertical synchronization active Low  */
#define DCMI_VSPOLARITY_HIGH    ((uint32_t)DCMI_CR_VSPOL)  /*!< Vertical synchronization active High */

/**
  * @}
  */

/** @defgroup DCMI_HSYNC_Polarity DCMI HSYNC Polarity
  * @{
  */ 
#define DCMI_HSPOLARITY_LOW     ((uint32_t)0x00000000)     /*!< Horizontal synchronization active Low  */
#define DCMI_HSPOLARITY_HIGH    ((uint32_t)DCMI_CR_HSPOL)  /*!< Horizontal synchronization active High */

/**
  * @}
  */

/** @defgroup DCMI_MODE_JPEG DCMI MODE JPEG
  * @{
  */
#define DCMI_JPEG_DISABLE   ((uint32_t)0x00000000)    /*!< Mode JPEG Disabled  */
#define DCMI_JPEG_ENABLE    ((uint32_t)DCMI_CR_JPEG)  /*!< Mode JPEG Enabled   */

/**
  * @}
  */

/** @defgroup DCMI_Capture_Rate DCMI Capture Rate
  * @{
  */
#define DCMI_CR_ALL_FRAME            ((uint32_t)0x00000000)      /*!< All frames are captured        */
#define DCMI_CR_ALTERNATE_2_FRAME    ((uint32_t)DCMI_CR_FCRC_0)  /*!< Every alternate frame captured */
#define DCMI_CR_ALTERNATE_4_FRAME    ((uint32_t)DCMI_CR_FCRC_1)  /*!< One frame in 4 frames captured */

/**
  * @}
  */

/** @defgroup DCMI_Extended_Data_Mode DCMI Extended Data Mode
  * @{
  */
#define DCMI_EXTEND_DATA_8B     ((uint32_t)0x00000000)                       /*!< Interface captures 8-bit data on every pixel clock  */
#define DCMI_EXTEND_DATA_10B    ((uint32_t)DCMI_CR_EDM_0)                    /*!< Interface captures 10-bit data on every pixel clock */
#define DCMI_EXTEND_DATA_12B    ((uint32_t)DCMI_CR_EDM_1)                    /*!< Interface captures 12-bit data on every pixel clock */
#define DCMI_EXTEND_DATA_14B    ((uint32_t)(DCMI_CR_EDM_0 | DCMI_CR_EDM_1))  /*!< Interface captures 14-bit data on every pixel clock */

/**
  * @}
  */

/** @defgroup DCMI_Window_Coordinate DCMI Window Coordinate 
  * @{
  */
#define DCMI_WINDOW_COORDINATE    ((uint32_t)0x3FFF)  /*!< Window coordinate */

/**
  * @}
  */

/** @defgroup DCMI_Window_Height DCMI Window Height
  * @{
  */ 
#define DCMI_WINDOW_HEIGHT    ((uint32_t)0x1FFF)  /*!< Window Height */

/**
  * @}
  */

/** @defgroup DCMI_interrupt_sources  DCMI interrupt sources
  * @{
  */
#define DCMI_IT_FRAME    ((uint32_t)DCMI_IER_FRAME_IE)
#define DCMI_IT_OVF      ((uint32_t)DCMI_IER_OVF_IE)
#define DCMI_IT_ERR      ((uint32_t)DCMI_IER_ERR_IE)
#define DCMI_IT_VSYNC    ((uint32_t)DCMI_IER_VSYNC_IE)
#define DCMI_IT_LINE     ((uint32_t)DCMI_IER_LINE_IE)
/**
  * @}
  */

/** @defgroup DCMI_Flags DCMI Flags
  * @{
  */

/** 
  * @brief   DCMI SR register
  */ 
#define DCMI_FLAG_HSYNC     ((uint32_t)0x2001)
#define DCMI_FLAG_VSYNC     ((uint32_t)0x2002)
#define DCMI_FLAG_FNE       ((uint32_t)0x2004)
/** 
  * @brief   DCMI RISR register  
  */ 
#define DCMI_FLAG_FRAMERI    ((uint32_t)DCMI_RISR_FRAME_RIS)
#define DCMI_FLAG_OVFRI      ((uint32_t)DCMI_RISR_OVF_RIS)
#define DCMI_FLAG_ERRRI      ((uint32_t)DCMI_RISR_ERR_RIS)
#define DCMI_FLAG_VSYNCRI    ((uint32_t)DCMI_RISR_VSYNC_RIS)
#define DCMI_FLAG_LINERI     ((uint32_t)DCMI_RISR_LINE_RIS)
/** 
  * @brief   DCMI MISR register  
  */ 
#define DCMI_FLAG_FRAMEMI    ((uint32_t)0x1001)
#define DCMI_FLAG_OVFMI      ((uint32_t)0x1002)
#define DCMI_FLAG_ERRMI      ((uint32_t)0x1004)
#define DCMI_FLAG_VSYNCMI    ((uint32_t)0x1008)
#define DCMI_FLAG_LINEMI     ((uint32_t)0x1010)
/**
  * @}
  */ 

/**
  * @}
  */
 
/* Exported macro ------------------------------------------------------------*/
/** @defgroup DCMI_Exported_Macros DCMI Exported Macros
  * @{
  */
  
/** @brief Reset DCMI handle state
  * @param  __HANDLE__: specifies the DCMI handle.
  * @retval None
  */
#define __HAL_DCMI_RESET_HANDLE_STATE(__HANDLE__) ((__HANDLE__)->State = HAL_DCMI_STATE_RESET)

/**
  * @brief  Enable the DCMI.
  * @param  __HANDLE__: DCMI handle
  * @retval None
  */
#define __HAL_DCMI_ENABLE(__HANDLE__)    ((__HANDLE__)->Instance->CR |= DCMI_CR_ENABLE)

/**
  * @brief  Disable the DCMI.
  * @param  __HANDLE__: DCMI handle
  * @retval None
  */
#define __HAL_DCMI_DISABLE(__HANDLE__)   ((__HANDLE__)->Instance->CR &= ~(DCMI_CR_ENABLE))

/* Interrupt & Flag management */
/**
  * @brief  Get the DCMI pending flags.
  * @param  __HANDLE__: DCMI handle
  * @param  __FLAG__: Get the specified flag.
  *         This parameter can be any combination of the following values:
  *            @arg DCMI_FLAG_FRAMERI: Frame capture complete flag mask
  *            @arg DCMI_FLAG_OVFRI: Overflow flag mask
  *            @arg DCMI_FLAG_ERRRI: Synchronization error flag mask
  *            @arg DCMI_FLAG_VSYNCRI: VSYNC flag mask
  *            @arg DCMI_FLAG_LINERI: Line flag mask
  * @retval The state of FLAG.
  */
#define __HAL_DCMI_GET_FLAG(__HANDLE__, __FLAG__)\
((((__FLAG__) & 0x3000) == 0x0)? ((__HANDLE__)->Instance->RISR & (__FLAG__)) :\
 (((__FLAG__) & 0x2000) == 0x0)? ((__HANDLE__)->Instance->MISR & (__FLAG__)) : ((__HANDLE__)->Instance->SR & (__FLAG__)))

/**
  * @brief  Clear the DCMI pending flags.
  * @param  __HANDLE__: DCMI handle
  * @param  __FLAG__: specifies the flag to clear.
  *         This parameter can be any combination of the following values:
  *            @arg DCMI_FLAG_FRAMERI: Frame capture complete flag mask
  *            @arg DCMI_FLAG_OVFRI: Overflow flag mask
  *            @arg DCMI_FLAG_ERRRI: Synchronization error flag mask
  *            @arg DCMI_FLAG_VSYNCRI: VSYNC flag mask
  *            @arg DCMI_FLAG_LINERI: Line flag mask
  * @retval None
  */
#define __HAL_DCMI_CLEAR_FLAG(__HANDLE__, __FLAG__) ((__HANDLE__)->Instance->ICR = (__FLAG__))

/**
  * @brief  Enable the specified DCMI interrupts.
  * @param  __HANDLE__:    DCMI handle
  * @param  __INTERRUPT__: specifies the DCMI interrupt sources to be enabled. 
  *         This parameter can be any combination of the following values:
  *            @arg DCMI_IT_FRAME: Frame capture complete interrupt mask
  *            @arg DCMI_IT_OVF: Overflow interrupt mask
  *            @arg DCMI_IT_ERR: Synchronization error interrupt mask
  *            @arg DCMI_IT_VSYNC: VSYNC interrupt mask
  *            @arg DCMI_IT_LINE: Line interrupt mask
  * @retval None
  */
#define __HAL_DCMI_ENABLE_IT(__HANDLE__, __INTERRUPT__) ((__HANDLE__)->Instance->IER |= (__INTERRUPT__))

/**
  * @brief  Disable the specified DCMI interrupts.
  * @param  __HANDLE__: DCMI handle
  * @param  __INTERRUPT__: specifies the DCMI interrupt sources to be enabled. 
  *         This parameter can be any combination of the following values:
  *            @arg DCMI_IT_FRAME: Frame capture complete interrupt mask
  *            @arg DCMI_IT_OVF: Overflow interrupt mask
  *            @arg DCMI_IT_ERR: Synchronization error interrupt mask
  *            @arg DCMI_IT_VSYNC: VSYNC interrupt mask
  *            @arg DCMI_IT_LINE: Line interrupt mask
  * @retval None
  */
#define __HAL_DCMI_DISABLE_IT(__HANDLE__, __INTERRUPT__) ((__HANDLE__)->Instance->IER &= ~(__INTERRUPT__))

/**
  * @brief  Check whether the specified DCMI interrupt has occurred or not.
  * @param  __HANDLE__: DCMI handle
  * @param  __INTERRUPT__: specifies the DCMI interrupt source to check.
  *         This parameter can be one of the following values:
  *            @arg DCMI_IT_FRAME: Frame capture complete interrupt mask
  *            @arg DCMI_IT_OVF: Overflow interrupt mask
  *            @arg DCMI_IT_ERR: Synchronization error interrupt mask
  *            @arg DCMI_IT_VSYNC: VSYNC interrupt mask
  *            @arg DCMI_IT_LINE: Line interrupt mask
  * @retval The state of INTERRUPT.
  */
#define __HAL_DCMI_GET_IT_SOURCE(__HANDLE__, __INTERRUPT__) ((__HANDLE__)->Instance->MISR & (__INTERRUPT__))

/**
  * @}
  */
  
/* Exported functions --------------------------------------------------------*/
/** @addtogroup DCMI_Exported_Functions DCMI Exported Functions
  * @{
  */

/** @addtogroup DCMI_Exported_Functions_Group1 Initialization and Configuration functions
 * @{
 */
/* Initialization and de-initialization functions *****************************/
HAL_StatusTypeDef HAL_DCMI_Init(DCMI_HandleTypeDef *hdcmi);
HAL_StatusTypeDef HAL_DCMI_DeInit(DCMI_HandleTypeDef *hdcmi);
void       HAL_DCMI_MspInit(DCMI_HandleTypeDef* hdcmi);
void       HAL_DCMI_MspDeInit(DCMI_HandleTypeDef* hdcmi);
/**
  * @}
  */
  
/** @addtogroup DCMI_Exported_Functions_Group2 IO operation functions
 * @{
 */
/* IO operation functions *****************************************************/
HAL_StatusTypeDef HAL_DCMI_Start_DMA(DCMI_HandleTypeDef* hdcmi, uint32_t DCMI_Mode, uint32_t pData, uint32_t Length);
HAL_StatusTypeDef HAL_DCMI_Stop(DCMI_HandleTypeDef* hdcmi);
void       HAL_DCMI_ErrorCallback(DCMI_HandleTypeDef *hdcmi);
void       HAL_DCMI_LineEventCallback(DCMI_HandleTypeDef *hdcmi);
void       HAL_DCMI_FrameEventCallback(DCMI_HandleTypeDef *hdcmi);
void       HAL_DCMI_VsyncEventCallback(DCMI_HandleTypeDef *hdcmi);
void       HAL_DCMI_IRQHandler(DCMI_HandleTypeDef *hdcmi);
/**
  * @}
  */
  
/** @addtogroup DCMI_Exported_Functions_Group3 Peripheral Control functions
 * @{
 */
/* Peripheral Control functions ***********************************************/
HAL_StatusTypeDef     HAL_DCMI_ConfigCROP(DCMI_HandleTypeDef *hdcmi, uint32_t X0, uint32_t Y0, uint32_t XSize, uint32_t YSize);
HAL_StatusTypeDef     HAL_DCMI_EnableCROP(DCMI_HandleTypeDef *hdcmi);
HAL_StatusTypeDef     HAL_DCMI_DisableCROP(DCMI_HandleTypeDef *hdcmi);
/**
  * @}
  */
  
/** @addtogroup DCMI_Exported_Functions_Group4 Peripheral State functions
 * @{
 */
/* Peripheral State functions *************************************************/
HAL_DCMI_StateTypeDef HAL_DCMI_GetState(DCMI_HandleTypeDef *hdcmi);
uint32_t              HAL_DCMI_GetError(DCMI_HandleTypeDef *hdcmi);
/**
  * @}
  */

/**
  * @}
  */

/* Private types -------------------------------------------------------------*/
/* Private variables ---------------------------------------------------------*/
/* Private constants ---------------------------------------------------------*/   
/* Private macro -------------------------------------------------------------*/
/** @defgroup DCMI_Private_Macros DCMI Private Macros
  * @{
  */
#define IS_DCMI_CAPTURE_MODE(MODE)(((MODE) == DCMI_MODE_CONTINUOUS) || \
                                   ((MODE) == DCMI_MODE_SNAPSHOT))
																			 
#define IS_DCMI_SYNCHRO(MODE)(((MODE) == DCMI_SYNCHRO_HARDWARE) || \
                              ((MODE) == DCMI_SYNCHRO_EMBEDDED))
																	
#define IS_DCMI_PCKPOLARITY(POLARITY)(((POLARITY) == DCMI_PCKPOLARITY_FALLING) || \
                                      ((POLARITY) == DCMI_PCKPOLARITY_RISING))
																					
#define IS_DCMI_VSPOLARITY(POLARITY)(((POLARITY) == DCMI_VSPOLARITY_LOW) || \
                                     ((POLARITY) == DCMI_VSPOLARITY_HIGH))
																				 
#define IS_DCMI_HSPOLARITY(POLARITY)(((POLARITY) == DCMI_HSPOLARITY_LOW) || \
                                     ((POLARITY) == DCMI_HSPOLARITY_HIGH))
																				 
#define IS_DCMI_MODE_JPEG(JPEG_MODE)(((JPEG_MODE) == DCMI_JPEG_DISABLE) || \
                                     ((JPEG_MODE) == DCMI_JPEG_ENABLE))
																				 
#define IS_DCMI_CAPTURE_RATE(RATE) (((RATE) == DCMI_CR_ALL_FRAME)         || \
                                    ((RATE) == DCMI_CR_ALTERNATE_2_FRAME) || \
                                    ((RATE) == DCMI_CR_ALTERNATE_4_FRAME))
																				
#define IS_DCMI_EXTENDED_DATA(DATA)(((DATA) == DCMI_EXTEND_DATA_8B)  || \
                                    ((DATA) == DCMI_EXTEND_DATA_10B) || \
                                    ((DATA) == DCMI_EXTEND_DATA_12B) || \
                                    ((DATA) == DCMI_EXTEND_DATA_14B))
																				
#define IS_DCMI_WINDOW_COORDINATE(COORDINATE) ((COORDINATE) <= DCMI_WINDOW_COORDINATE)

#define IS_DCMI_WINDOW_HEIGHT(HEIGHT) ((HEIGHT) <= DCMI_WINDOW_HEIGHT)

/**
  * @}
  */

/* Private functions ---------------------------------------------------------*/
/** @addtogroup DCMI_Private_Functions DCMI Private Functions
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

#endif /* __STM32F7xx_HAL_DCMI_H */

/************************ (C) COPYRIGHT STMicroelectronics *****END OF FILE****/
