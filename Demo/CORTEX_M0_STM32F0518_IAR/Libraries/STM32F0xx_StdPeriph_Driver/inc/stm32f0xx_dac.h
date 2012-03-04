/**
  ******************************************************************************
  * @file    stm32f0xx_dac.h
  * @author  MCD Application Team
  * @version V1.0.0RC1
  * @date    27-January-2012
  * @brief   This file contains all the functions prototypes for the DAC firmware 
  *          library.
  ******************************************************************************
  * @attention
  *
  * THE PRESENT FIRMWARE WHICH IS FOR GUIDANCE ONLY AIMS AT PROVIDING CUSTOMERS
  * WITH CODING INFORMATION REGARDING THEIR PRODUCTS IN ORDER FOR THEM TO SAVE
  * TIME. AS A RESULT, STMICROELECTRONICS SHALL NOT BE HELD LIABLE FOR ANY
  * DIRECT, INDIRECT OR CONSEQUENTIAL DAMAGES WITH RESPECT TO ANY CLAIMS ARISING
  * FROM THE CONTENT OF SUCH FIRMWARE AND/OR THE USE MADE BY CUSTOMERS OF THE
  * CODING INFORMATION CONTAINED HEREIN IN CONNECTION WITH THEIR PRODUCTS.
  *
  * FOR MORE INFORMATION PLEASE READ CAREFULLY THE LICENSE AGREEMENT FILE
  * LOCATED IN THE ROOT DIRECTORY OF THIS FIRMWARE PACKAGE.
  *
  * <h2><center>&copy; COPYRIGHT 2012 STMicroelectronics</center></h2>
  ******************************************************************************
  */

/* Define to prevent recursive inclusion -------------------------------------*/
#ifndef __STM32F0XX_DAC_H
#define __STM32F0XX_DAC_H

#ifdef __cplusplus
 extern "C" {
#endif

/* Includes ------------------------------------------------------------------*/
#include "stm32f0xx.h"
 
/** @addtogroup STM32F0xx_StdPeriph_Driver
  * @{
  */

/** @addtogroup DAC
  * @{
  */

/* Exported types ------------------------------------------------------------*/

/** 
  * @brief  DAC Init structure definition
  */
  
typedef struct
{
  uint32_t DAC_Trigger;                      /*!< Specifies the external trigger for the selected DAC channel.
                                                  This parameter can be a value of @ref DAC_Trigger */

  uint32_t DAC_OutputBuffer;                 /*!< Specifies whether the DAC channel output buffer is enabled or disabled.
                                                  This parameter can be a value of @ref DAC_OutputBuffer */
}DAC_InitTypeDef;

/* Exported constants --------------------------------------------------------*/

/** @defgroup DAC_Exported_Constants
  * @{
  */

/** @defgroup DAC_Trigger 
  * @{
  */
  
#define DAC_Trigger_None                   ((uint32_t)0x00000000) /*!< Conversion is automatic once the DAC1_DHRxxxx register 
                                                                       has been loaded, and not by external trigger */
#define DAC_Trigger_T6_TRGO                ((uint32_t)0x00000004) /*!< TIM6 TRGO selected as external conversion trigger for DAC channel */
#define DAC_Trigger_T3_TRGO                ((uint32_t)0x0000000C) /*!< TIM3 TRGO selected as external conversion trigger for DAC channel */
#define DAC_Trigger_T15_TRGO               ((uint32_t)0x0000001C) /*!< TIM15 TRGO selected as external conversion trigger for DAC channel */
#define DAC_Trigger_T2_TRGO                ((uint32_t)0x00000024) /*!< TIM2 TRGO selected as external conversion trigger for DAC channel */
#define DAC_Trigger_Ext_IT9                ((uint32_t)0x00000034) /*!< EXTI Line9 event selected as external conversion trigger for DAC channel */
#define DAC_Trigger_Software               ((uint32_t)0x0000003C) /*!< Conversion started by software trigger for DAC channel */

#define IS_DAC_TRIGGER(TRIGGER) (((TRIGGER) == DAC_Trigger_None) || \
                                 ((TRIGGER) == DAC_Trigger_T6_TRGO) || \
                                 ((TRIGGER) == DAC_Trigger_T3_TRGO) || \
                                 ((TRIGGER) == DAC_Trigger_T15_TRGO) || \
                                 ((TRIGGER) == DAC_Trigger_T2_TRGO) || \
                                 ((TRIGGER) == DAC_Trigger_Ext_IT9) || \
                                 ((TRIGGER) == DAC_Trigger_Software))
                                 
/**
  * @}
  */

/** @defgroup DAC_OutputBuffer 
  * @{
  */

#define DAC_OutputBuffer_Enable            ((uint32_t)0x00000000)
#define DAC_OutputBuffer_Disable           DAC_CR_BOFF1
#define IS_DAC_OUTPUT_BUFFER_STATE(STATE) (((STATE) == DAC_OutputBuffer_Enable) || \
                                           ((STATE) == DAC_OutputBuffer_Disable))
/**
  * @}
  */
  
/** @defgroup DAC_Channel_selection 
  * @{
  */

#define DAC_Channel_1                      ((uint32_t)0x00000000)
#define IS_DAC_CHANNEL(CHANNEL) (((CHANNEL) == DAC_Channel_1))

/**
  * @}
  */

/** @defgroup DAC_data_alignment
  * @{
  */

#define DAC_Align_12b_R                    ((uint32_t)0x00000000)
#define DAC_Align_12b_L                    ((uint32_t)0x00000004)
#define DAC_Align_8b_R                     ((uint32_t)0x00000008)
#define IS_DAC_ALIGN(ALIGN) (((ALIGN) == DAC_Align_12b_R) || \
                             ((ALIGN) == DAC_Align_12b_L) || \
                             ((ALIGN) == DAC_Align_8b_R))
/**
  * @}
  */

/** @defgroup DAC_data 
  * @{
  */

#define IS_DAC_DATA(DATA) ((DATA) <= 0xFFF0) 

/**
  * @}
  */

/** @defgroup DAC_interrupts_definition 
  * @{
  */ 
  
#define DAC_IT_DMAUDR                      DAC_SR_DMAUDR1
#define IS_DAC_IT(IT) (((IT) == DAC_IT_DMAUDR)) 

/**
  * @}
  */ 


/** @defgroup DAC_flags_definition 
  * @{
  */ 
  
#define DAC_FLAG_DMAUDR                    DAC_SR_DMAUDR1
  
#define IS_DAC_FLAG(FLAG) (((FLAG) == DAC_FLAG_DMAUDR))

/**
  * @}
  */ 

/**
  * @}
  */ 

/* Exported macro ------------------------------------------------------------*/
/* Exported functions ------------------------------------------------------- */

/*  Function used to set the DAC configuration to the default reset state *****/
void DAC_DeInit(void);

/*  DAC channels configuration: trigger, output buffer, data format functions */
void DAC_Init(uint32_t DAC_Channel, DAC_InitTypeDef* DAC_InitStruct);
void DAC_StructInit(DAC_InitTypeDef* DAC_InitStruct);
void DAC_Cmd(uint32_t DAC_Channel, FunctionalState NewState);
void DAC_SoftwareTriggerCmd(uint32_t DAC_Channel, FunctionalState NewState);
void DAC_SetChannel1Data(uint32_t DAC_Align, uint16_t Data);
uint16_t DAC_GetDataOutputValue(uint32_t DAC_Channel);

/* DMA management functions ***************************************************/
void DAC_DMACmd(uint32_t DAC_Channel, FunctionalState NewState);

/* Interrupts and flags management functions **********************************/
void DAC_ITConfig(uint32_t DAC_Channel, uint32_t DAC_IT, FunctionalState NewState);
FlagStatus DAC_GetFlagStatus(uint32_t DAC_Channel, uint32_t DAC_FLAG);
void DAC_ClearFlag(uint32_t DAC_Channel, uint32_t DAC_FLAG);
ITStatus DAC_GetITStatus(uint32_t DAC_Channel, uint32_t DAC_IT);
void DAC_ClearITPendingBit(uint32_t DAC_Channel, uint32_t DAC_IT);

#ifdef __cplusplus
}
#endif

#endif /*__STM32F0XX_DAC_H */

/**
  * @}
  */ 

/**
  * @}
  */ 

/******************* (C) COPYRIGHT 2012 STMicroelectronics *****END OF FILE****/
