/**
  ******************************************************************************
  * @file    stm32f7xx_hal_dac.h
  * @author  MCD Application Team
  * @version V1.0.0
  * @date    12-May-2015
  * @brief   Header file of DAC HAL Extension module.
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
#ifndef __STM32F7xx_HAL_DAC_EX_H
#define __STM32F7xx_HAL_DAC_EX_H

#ifdef __cplusplus
 extern "C" {
#endif

/* Includes ------------------------------------------------------------------*/
#include "stm32f7xx_hal_def.h"

/** @addtogroup STM32F7xx_HAL_Driver
  * @{
  */

/** @addtogroup DACEx
  * @{
  */

/* Exported types ------------------------------------------------------------*/
/* Exported constants --------------------------------------------------------*/
/** @defgroup DACEx_Exported_Constants DAC Exported Constants
  * @{
  */
   
/** @defgroup DACEx_lfsrunmask_triangleamplitude DAC LFS Run Mask Triangle Amplitude
  * @{
  */
#define DAC_LFSRUNMASK_BIT0                ((uint32_t)0x00000000) /*!< Unmask DAC channel LFSR bit0 for noise wave generation */
#define DAC_LFSRUNMASK_BITS1_0             ((uint32_t)DAC_CR_MAMP1_0) /*!< Unmask DAC channel LFSR bit[1:0] for noise wave generation */
#define DAC_LFSRUNMASK_BITS2_0             ((uint32_t)DAC_CR_MAMP1_1) /*!< Unmask DAC channel LFSR bit[2:0] for noise wave generation */
#define DAC_LFSRUNMASK_BITS3_0             ((uint32_t)DAC_CR_MAMP1_1 | DAC_CR_MAMP1_0)/*!< Unmask DAC channel LFSR bit[3:0] for noise wave generation */
#define DAC_LFSRUNMASK_BITS4_0             ((uint32_t)DAC_CR_MAMP1_2) /*!< Unmask DAC channel LFSR bit[4:0] for noise wave generation */
#define DAC_LFSRUNMASK_BITS5_0             ((uint32_t)DAC_CR_MAMP1_2 | DAC_CR_MAMP1_0) /*!< Unmask DAC channel LFSR bit[5:0] for noise wave generation */
#define DAC_LFSRUNMASK_BITS6_0             ((uint32_t)DAC_CR_MAMP1_2 | DAC_CR_MAMP1_1) /*!< Unmask DAC channel LFSR bit[6:0] for noise wave generation */
#define DAC_LFSRUNMASK_BITS7_0             ((uint32_t)DAC_CR_MAMP1_2 | DAC_CR_MAMP1_1 | DAC_CR_MAMP1_0) /*!< Unmask DAC channel LFSR bit[7:0] for noise wave generation */
#define DAC_LFSRUNMASK_BITS8_0             ((uint32_t)DAC_CR_MAMP1_3) /*!< Unmask DAC channel LFSR bit[8:0] for noise wave generation */
#define DAC_LFSRUNMASK_BITS9_0             ((uint32_t)DAC_CR_MAMP1_3 | DAC_CR_MAMP1_0) /*!< Unmask DAC channel LFSR bit[9:0] for noise wave generation */
#define DAC_LFSRUNMASK_BITS10_0            ((uint32_t)DAC_CR_MAMP1_3 | DAC_CR_MAMP1_1) /*!< Unmask DAC channel LFSR bit[10:0] for noise wave generation */
#define DAC_LFSRUNMASK_BITS11_0            ((uint32_t)DAC_CR_MAMP1_3 | DAC_CR_MAMP1_1 | DAC_CR_MAMP1_0) /*!< Unmask DAC channel LFSR bit[11:0] for noise wave generation */
#define DAC_TRIANGLEAMPLITUDE_1            ((uint32_t)0x00000000) /*!< Select max triangle amplitude of 1 */
#define DAC_TRIANGLEAMPLITUDE_3            ((uint32_t)DAC_CR_MAMP1_0) /*!< Select max triangle amplitude of 3 */
#define DAC_TRIANGLEAMPLITUDE_7            ((uint32_t)DAC_CR_MAMP1_1) /*!< Select max triangle amplitude of 7 */
#define DAC_TRIANGLEAMPLITUDE_15           ((uint32_t)DAC_CR_MAMP1_1 | DAC_CR_MAMP1_0) /*!< Select max triangle amplitude of 15 */
#define DAC_TRIANGLEAMPLITUDE_31           ((uint32_t)DAC_CR_MAMP1_2) /*!< Select max triangle amplitude of 31 */
#define DAC_TRIANGLEAMPLITUDE_63           ((uint32_t)DAC_CR_MAMP1_2 | DAC_CR_MAMP1_0) /*!< Select max triangle amplitude of 63 */
#define DAC_TRIANGLEAMPLITUDE_127          ((uint32_t)DAC_CR_MAMP1_2 | DAC_CR_MAMP1_1) /*!< Select max triangle amplitude of 127 */
#define DAC_TRIANGLEAMPLITUDE_255          ((uint32_t)DAC_CR_MAMP1_2 | DAC_CR_MAMP1_1 | DAC_CR_MAMP1_0) /*!< Select max triangle amplitude of 255 */
#define DAC_TRIANGLEAMPLITUDE_511          ((uint32_t)DAC_CR_MAMP1_3) /*!< Select max triangle amplitude of 511 */
#define DAC_TRIANGLEAMPLITUDE_1023         ((uint32_t)DAC_CR_MAMP1_3 | DAC_CR_MAMP1_0) /*!< Select max triangle amplitude of 1023 */
#define DAC_TRIANGLEAMPLITUDE_2047         ((uint32_t)DAC_CR_MAMP1_3 | DAC_CR_MAMP1_1) /*!< Select max triangle amplitude of 2047 */
#define DAC_TRIANGLEAMPLITUDE_4095         ((uint32_t)DAC_CR_MAMP1_3 | DAC_CR_MAMP1_1 | DAC_CR_MAMP1_0) /*!< Select max triangle amplitude of 4095 */
/**
  * @}
  */

/**
  * @}
  */
/* Exported macro ------------------------------------------------------------*/
/* Exported functions --------------------------------------------------------*/
/** @addtogroup DACEx_Exported_Functions
  * @{
  */

/** @addtogroup DACEx_Exported_Functions_Group1
  * @{
  */
/* Extension features functions ***********************************************/
uint32_t HAL_DACEx_DualGetValue(DAC_HandleTypeDef* hdac);
HAL_StatusTypeDef HAL_DACEx_TriangleWaveGenerate(DAC_HandleTypeDef* hdac, uint32_t Channel, uint32_t Amplitude);
HAL_StatusTypeDef HAL_DACEx_NoiseWaveGenerate(DAC_HandleTypeDef* hdac, uint32_t Channel, uint32_t Amplitude);
HAL_StatusTypeDef HAL_DACEx_DualSetValue(DAC_HandleTypeDef* hdac, uint32_t Alignment, uint32_t Data1, uint32_t Data2);

void HAL_DACEx_ConvCpltCallbackCh2(DAC_HandleTypeDef* hdac);
void HAL_DACEx_ConvHalfCpltCallbackCh2(DAC_HandleTypeDef* hdac);
void HAL_DACEx_ErrorCallbackCh2(DAC_HandleTypeDef* hdac);
void HAL_DACEx_DMAUnderrunCallbackCh2(DAC_HandleTypeDef* hdac);
/**
  * @}
  */

/**
  * @}
  */
/* Private types -------------------------------------------------------------*/
/* Private variables ---------------------------------------------------------*/
/* Private constants ---------------------------------------------------------*/
/** @defgroup DACEx_Private_Constants DAC Private Constants
  * @{
  */

/**
  * @}
  */

/* Private macros ------------------------------------------------------------*/
/** @defgroup DACEx_Private_Macros DAC Private Macros
  * @{
  */
#define IS_DAC_LFSR_UNMASK_TRIANGLE_AMPLITUDE(VALUE) (((VALUE) == DAC_LFSRUNMASK_BIT0) || \
                                                      ((VALUE) == DAC_LFSRUNMASK_BITS1_0) || \
                                                      ((VALUE) == DAC_LFSRUNMASK_BITS2_0) || \
                                                      ((VALUE) == DAC_LFSRUNMASK_BITS3_0) || \
                                                      ((VALUE) == DAC_LFSRUNMASK_BITS4_0) || \
                                                      ((VALUE) == DAC_LFSRUNMASK_BITS5_0) || \
                                                      ((VALUE) == DAC_LFSRUNMASK_BITS6_0) || \
                                                      ((VALUE) == DAC_LFSRUNMASK_BITS7_0) || \
                                                      ((VALUE) == DAC_LFSRUNMASK_BITS8_0) || \
                                                      ((VALUE) == DAC_LFSRUNMASK_BITS9_0) || \
                                                      ((VALUE) == DAC_LFSRUNMASK_BITS10_0) || \
                                                      ((VALUE) == DAC_LFSRUNMASK_BITS11_0) || \
                                                      ((VALUE) == DAC_TRIANGLEAMPLITUDE_1) || \
                                                      ((VALUE) == DAC_TRIANGLEAMPLITUDE_3) || \
                                                      ((VALUE) == DAC_TRIANGLEAMPLITUDE_7) || \
                                                      ((VALUE) == DAC_TRIANGLEAMPLITUDE_15) || \
                                                      ((VALUE) == DAC_TRIANGLEAMPLITUDE_31) || \
                                                      ((VALUE) == DAC_TRIANGLEAMPLITUDE_63) || \
                                                      ((VALUE) == DAC_TRIANGLEAMPLITUDE_127) || \
                                                      ((VALUE) == DAC_TRIANGLEAMPLITUDE_255) || \
                                                      ((VALUE) == DAC_TRIANGLEAMPLITUDE_511) || \
                                                      ((VALUE) == DAC_TRIANGLEAMPLITUDE_1023) || \
                                                      ((VALUE) == DAC_TRIANGLEAMPLITUDE_2047) || \
                                                      ((VALUE) == DAC_TRIANGLEAMPLITUDE_4095))
/**
  * @}
  */

/* Private functions ---------------------------------------------------------*/
/** @defgroup DACEx_Private_Functions DAC Private Functions
  * @{
  */
void DAC_DMAConvCpltCh2(DMA_HandleTypeDef *hdma);
void DAC_DMAErrorCh2(DMA_HandleTypeDef *hdma);
void DAC_DMAHalfConvCpltCh2(DMA_HandleTypeDef *hdma); 
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

#endif /*__STM32F7xx_HAL_DAC_EX_H */

/************************ (C) COPYRIGHT STMicroelectronics *****END OF FILE****/
