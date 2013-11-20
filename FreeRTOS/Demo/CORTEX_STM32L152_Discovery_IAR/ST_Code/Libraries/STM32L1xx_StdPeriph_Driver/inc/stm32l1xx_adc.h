/**
  ******************************************************************************
  * @file    stm32l1xx_adc.h
  * @author  MCD Application Team
  * @version V1.1.1
  * @date    05-March-2012
  * @brief   This file contains all the functions prototypes for the ADC firmware 
  *          library.
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
#ifndef __STM32L1xx_ADC_H
#define __STM32L1xx_ADC_H

#ifdef __cplusplus
 extern "C" {
#endif

/* Includes ------------------------------------------------------------------*/
#include "stm32l1xx.h"

/** @addtogroup STM32L1xx_StdPeriph_Driver
  * @{
  */

/** @addtogroup ADC
  * @{
  */

/* Exported types ------------------------------------------------------------*/

/** 
  * @brief  ADC Init structure definition  
  */
  
typedef struct
{
  uint32_t ADC_Resolution;                /*!< Selects the resolution of the conversion.
                                               This parameter can be a value of @ref ADC_Resolution */
  
  FunctionalState ADC_ScanConvMode;       /*!< Specifies whether the conversion is performed in
                                               Scan (multichannel) or Single (one channel) mode.
                                               This parameter can be set to ENABLE or DISABLE */
  
  FunctionalState ADC_ContinuousConvMode; /*!< Specifies whether the conversion is performed in
                                               Continuous or Single mode.
                                               This parameter can be set to ENABLE or DISABLE. */
  
  uint32_t ADC_ExternalTrigConvEdge;      /*!< Selects the external trigger Edge and enables the
                                               trigger of a regular group. This parameter can be a value
                                               of @ref ADC_external_trigger_edge_for_regular_channels_conversion */
  
  uint32_t ADC_ExternalTrigConv;          /*!< Defines the external trigger used to start the analog
                                               to digital conversion of regular channels. This parameter
                                               can be a value of @ref ADC_external_trigger_sources_for_regular_channels_conversion */
  
  uint32_t ADC_DataAlign;                 /*!< Specifies whether the ADC data alignment is left or right.
                                               This parameter can be a value of @ref ADC_data_align */
  
  uint8_t  ADC_NbrOfConversion;           /*!< Specifies the number of ADC conversions that will be done
                                               using the sequencer for regular channel group.
                                               This parameter must range from 1 to 27. */
}ADC_InitTypeDef;

typedef struct 
{                                              
  uint32_t ADC_Prescaler;                 /*!< Selects the ADC prescaler.
                                               This parameter can be a value 
                                               of @ref ADC_Prescaler */
}ADC_CommonInitTypeDef;

/* Exported constants --------------------------------------------------------*/

/** @defgroup ADC_Exported_Constants
  * @{
  */ 
#define IS_ADC_ALL_PERIPH(PERIPH)                  ((PERIPH) == ADC1)
#define IS_ADC_DMA_PERIPH(PERIPH)                  ((PERIPH) == ADC1)

/** @defgroup ADC_Power_down_during_Idle_and_or_Delay_phase 
  * @{
  */ 
#define ADC_PowerDown_Delay                        ((uint32_t)0x00010000)
#define ADC_PowerDown_Idle                         ((uint32_t)0x00020000)
#define ADC_PowerDown_Idle_Delay                   ((uint32_t)0x00030000)

#define IS_ADC_POWER_DOWN(DWON) (((DWON) == ADC_PowerDown_Delay) || \
                                 ((DWON) == ADC_PowerDown_Idle) || \
                                 ((DWON) == ADC_PowerDown_Idle_Delay))
/**
  * @}
  */ 


/** @defgroup ADC_Prescaler 
  * @{
  */ 
#define ADC_Prescaler_Div1                         ((uint32_t)0x00000000)
#define ADC_Prescaler_Div2                         ((uint32_t)0x00010000)
#define ADC_Prescaler_Div4                         ((uint32_t)0x00020000)

#define IS_ADC_PRESCALER(PRESCALER) (((PRESCALER) == ADC_Prescaler_Div1) || \
                                     ((PRESCALER) == ADC_Prescaler_Div2) || \
                                     ((PRESCALER) == ADC_Prescaler_Div4))
/**
  * @}
  */ 



/** @defgroup ADC_Resolution 
  * @{
  */ 
#define ADC_Resolution_12b                         ((uint32_t)0x00000000)
#define ADC_Resolution_10b                         ((uint32_t)0x01000000)
#define ADC_Resolution_8b                          ((uint32_t)0x02000000)
#define ADC_Resolution_6b                          ((uint32_t)0x03000000)

#define IS_ADC_RESOLUTION(RESOLUTION) (((RESOLUTION) == ADC_Resolution_12b) || \
                                       ((RESOLUTION) == ADC_Resolution_10b) || \
                                       ((RESOLUTION) == ADC_Resolution_8b) || \
                                       ((RESOLUTION) == ADC_Resolution_6b))

/**
  * @}
  */ 

/** @defgroup ADC_external_trigger_edge_for_regular_channels_conversion 
  * @{
  */ 
#define ADC_ExternalTrigConvEdge_None              ((uint32_t)0x00000000)
#define ADC_ExternalTrigConvEdge_Rising            ((uint32_t)0x10000000)
#define ADC_ExternalTrigConvEdge_Falling           ((uint32_t)0x20000000)
#define ADC_ExternalTrigConvEdge_RisingFalling     ((uint32_t)0x30000000)

#define IS_ADC_EXT_TRIG_EDGE(EDGE) (((EDGE) == ADC_ExternalTrigConvEdge_None) || \
                                    ((EDGE) == ADC_ExternalTrigConvEdge_Rising) || \
                                    ((EDGE) == ADC_ExternalTrigConvEdge_Falling) || \
                                    ((EDGE) == ADC_ExternalTrigConvEdge_RisingFalling))
/**
  * @}
  */ 

/** @defgroup ADC_external_trigger_sources_for_regular_channels_conversion
  * @{
  */ 

/* TIM2 */
#define ADC_ExternalTrigConv_T2_CC3                ((uint32_t)0x02000000)
#define ADC_ExternalTrigConv_T2_CC2                ((uint32_t)0x03000000)
#define ADC_ExternalTrigConv_T2_TRGO               ((uint32_t)0x06000000)

/* TIM3 */
#define ADC_ExternalTrigConv_T3_CC1                ((uint32_t)0x07000000)
#define ADC_ExternalTrigConv_T3_CC3                ((uint32_t)0x08000000)
#define ADC_ExternalTrigConv_T3_TRGO               ((uint32_t)0x04000000)

/* TIM4 */
#define ADC_ExternalTrigConv_T4_CC4                ((uint32_t)0x05000000)
#define ADC_ExternalTrigConv_T4_TRGO               ((uint32_t)0x09000000)

/* TIM6 */
#define ADC_ExternalTrigConv_T6_TRGO               ((uint32_t)0x0A000000)

/* TIM9 */
#define ADC_ExternalTrigConv_T9_CC2                ((uint32_t)0x00000000)
#define ADC_ExternalTrigConv_T9_TRGO               ((uint32_t)0x01000000)

/* EXTI */
#define ADC_ExternalTrigConv_Ext_IT11              ((uint32_t)0x0F000000)

#define IS_ADC_EXT_TRIG(REGTRIG) (((REGTRIG) == ADC_ExternalTrigConv_T9_CC2)  || \
                                  ((REGTRIG) == ADC_ExternalTrigConv_T9_TRGO) || \
                                  ((REGTRIG) == ADC_ExternalTrigConv_T2_CC3)  || \
                                  ((REGTRIG) == ADC_ExternalTrigConv_T2_CC2)  || \
                                  ((REGTRIG) == ADC_ExternalTrigConv_T3_TRGO) || \
                                  ((REGTRIG) == ADC_ExternalTrigConv_T4_CC4)  || \
                                  ((REGTRIG) == ADC_ExternalTrigConv_T2_TRGO) || \
                                  ((REGTRIG) == ADC_ExternalTrigConv_T3_CC1)  || \
                                  ((REGTRIG) == ADC_ExternalTrigConv_T3_CC3)  || \
                                  ((REGTRIG) == ADC_ExternalTrigConv_T4_TRGO) || \
                                  ((REGTRIG) == ADC_ExternalTrigConv_T6_TRGO) || \
                                  ((REGTRIG) == ADC_ExternalTrigConv_Ext_IT11))
/**
  * @}
  */ 

/** @defgroup ADC_data_align 
  * @{
  */ 
  
#define ADC_DataAlign_Right                        ((uint32_t)0x00000000)
#define ADC_DataAlign_Left                         ((uint32_t)0x00000800)

#define IS_ADC_DATA_ALIGN(ALIGN) (((ALIGN) == ADC_DataAlign_Right) || \
                                  ((ALIGN) == ADC_DataAlign_Left))
/**
  * @}
  */ 

/** @defgroup ADC_channels 
  * @{
  */ 
/* ADC Bank A Channels -------------------------------------------------------*/  
#define ADC_Channel_0                              ((uint8_t)0x00)
#define ADC_Channel_1                              ((uint8_t)0x01)
#define ADC_Channel_2                              ((uint8_t)0x02)
#define ADC_Channel_3                              ((uint8_t)0x03)

#define ADC_Channel_6                              ((uint8_t)0x06)
#define ADC_Channel_7                              ((uint8_t)0x07)
#define ADC_Channel_8                              ((uint8_t)0x08)
#define ADC_Channel_9                              ((uint8_t)0x09)
#define ADC_Channel_10                             ((uint8_t)0x0A)
#define ADC_Channel_11                             ((uint8_t)0x0B)
#define ADC_Channel_12                             ((uint8_t)0x0C)


/* ADC Bank B Channels -------------------------------------------------------*/  
#define ADC_Channel_0b                             ADC_Channel_0
#define ADC_Channel_1b                             ADC_Channel_1
#define ADC_Channel_2b                             ADC_Channel_2
#define ADC_Channel_3b                             ADC_Channel_3

#define ADC_Channel_6b                             ADC_Channel_6
#define ADC_Channel_7b                             ADC_Channel_7
#define ADC_Channel_8b                             ADC_Channel_8
#define ADC_Channel_9b                             ADC_Channel_9
#define ADC_Channel_10b                            ADC_Channel_10
#define ADC_Channel_11b                            ADC_Channel_11
#define ADC_Channel_12b                            ADC_Channel_12

/* ADC Common Channels (ADC Bank A and B) ------------------------------------*/
#define ADC_Channel_4                              ((uint8_t)0x04)
#define ADC_Channel_5                              ((uint8_t)0x05)

#define ADC_Channel_13                             ((uint8_t)0x0D)
#define ADC_Channel_14                             ((uint8_t)0x0E)
#define ADC_Channel_15                             ((uint8_t)0x0F)
#define ADC_Channel_16                             ((uint8_t)0x10)
#define ADC_Channel_17                             ((uint8_t)0x11)
#define ADC_Channel_18                             ((uint8_t)0x12)
#define ADC_Channel_19                             ((uint8_t)0x13)
#define ADC_Channel_20                             ((uint8_t)0x14)
#define ADC_Channel_21                             ((uint8_t)0x15)
#define ADC_Channel_22                             ((uint8_t)0x16)
#define ADC_Channel_23                             ((uint8_t)0x17)
#define ADC_Channel_24                             ((uint8_t)0x18)
#define ADC_Channel_25                             ((uint8_t)0x19)

#define ADC_Channel_27                             ((uint8_t)0x1B)
#define ADC_Channel_28                             ((uint8_t)0x1C)
#define ADC_Channel_29                             ((uint8_t)0x1D)
#define ADC_Channel_30                             ((uint8_t)0x1E)
#define ADC_Channel_31                             ((uint8_t)0x1F)

#define ADC_Channel_TempSensor                     ((uint8_t)ADC_Channel_16)
#define ADC_Channel_Vrefint                        ((uint8_t)ADC_Channel_17)

#define IS_ADC_CHANNEL(CHANNEL) (((CHANNEL) == ADC_Channel_0)  || ((CHANNEL) == ADC_Channel_1)  || \
                                 ((CHANNEL) == ADC_Channel_2)  || ((CHANNEL) == ADC_Channel_3)  || \
                                 ((CHANNEL) == ADC_Channel_4)  || ((CHANNEL) == ADC_Channel_5)  || \
                                 ((CHANNEL) == ADC_Channel_6)  || ((CHANNEL) == ADC_Channel_7)  || \
                                 ((CHANNEL) == ADC_Channel_8)  || ((CHANNEL) == ADC_Channel_9)  || \
                                 ((CHANNEL) == ADC_Channel_10) || ((CHANNEL) == ADC_Channel_11) || \
                                 ((CHANNEL) == ADC_Channel_12) || ((CHANNEL) == ADC_Channel_13) || \
                                 ((CHANNEL) == ADC_Channel_14) || ((CHANNEL) == ADC_Channel_15) || \
                                 ((CHANNEL) == ADC_Channel_16) || ((CHANNEL) == ADC_Channel_17) || \
                                 ((CHANNEL) == ADC_Channel_18) || ((CHANNEL) == ADC_Channel_19) || \
                                 ((CHANNEL) == ADC_Channel_20) || ((CHANNEL) == ADC_Channel_21) || \
                                 ((CHANNEL) == ADC_Channel_22) || ((CHANNEL) == ADC_Channel_23) || \
                                 ((CHANNEL) == ADC_Channel_24) || ((CHANNEL) == ADC_Channel_25) || \
                                 ((CHANNEL) == ADC_Channel_27) || ((CHANNEL) == ADC_Channel_28) || \
                                 ((CHANNEL) == ADC_Channel_29) || ((CHANNEL) == ADC_Channel_30) || \
                                 ((CHANNEL) == ADC_Channel_31))
/**
  * @}
  */ 

/** @defgroup ADC_sampling_times 
  * @{
  */ 

#define ADC_SampleTime_4Cycles                     ((uint8_t)0x00)
#define ADC_SampleTime_9Cycles                     ((uint8_t)0x01)
#define ADC_SampleTime_16Cycles                    ((uint8_t)0x02)
#define ADC_SampleTime_24Cycles                    ((uint8_t)0x03)
#define ADC_SampleTime_48Cycles                    ((uint8_t)0x04)
#define ADC_SampleTime_96Cycles                    ((uint8_t)0x05)
#define ADC_SampleTime_192Cycles                   ((uint8_t)0x06)
#define ADC_SampleTime_384Cycles                   ((uint8_t)0x07)

#define IS_ADC_SAMPLE_TIME(TIME) (((TIME) == ADC_SampleTime_4Cycles)   || \
                                  ((TIME) == ADC_SampleTime_9Cycles)   || \
                                  ((TIME) == ADC_SampleTime_16Cycles)  || \
                                  ((TIME) == ADC_SampleTime_24Cycles)  || \
                                  ((TIME) == ADC_SampleTime_48Cycles)  || \
                                  ((TIME) == ADC_SampleTime_96Cycles)  || \
                                  ((TIME) == ADC_SampleTime_192Cycles) || \
                                  ((TIME) == ADC_SampleTime_384Cycles))
/**
  * @}
  */ 

/** @defgroup ADC_Delay_length 
  * @{
  */ 

#define ADC_DelayLength_None                       ((uint8_t)0x00)
#define ADC_DelayLength_Freeze                     ((uint8_t)0x10)
#define ADC_DelayLength_7Cycles                    ((uint8_t)0x20)
#define ADC_DelayLength_15Cycles                   ((uint8_t)0x30)
#define ADC_DelayLength_31Cycles                   ((uint8_t)0x40)
#define ADC_DelayLength_63Cycles                   ((uint8_t)0x50)
#define ADC_DelayLength_127Cycles                  ((uint8_t)0x60)
#define ADC_DelayLength_255Cycles                  ((uint8_t)0x70)

#define IS_ADC_DELAY_LENGTH(LENGTH) (((LENGTH) == ADC_DelayLength_None)      || \
                                     ((LENGTH) == ADC_DelayLength_Freeze)    || \
                                     ((LENGTH) == ADC_DelayLength_7Cycles)   || \
                                     ((LENGTH) == ADC_DelayLength_15Cycles)  || \
                                     ((LENGTH) == ADC_DelayLength_31Cycles)  || \
                                     ((LENGTH) == ADC_DelayLength_63Cycles)  || \
                                     ((LENGTH) == ADC_DelayLength_127Cycles) || \
                                     ((LENGTH) == ADC_DelayLength_255Cycles))

/**
  * @}
  */

/** @defgroup ADC_external_trigger_edge_for_injected_channels_conversion 
  * @{
  */ 
#define ADC_ExternalTrigInjecConvEdge_None          ((uint32_t)0x00000000)
#define ADC_ExternalTrigInjecConvEdge_Rising        ((uint32_t)0x00100000)
#define ADC_ExternalTrigInjecConvEdge_Falling       ((uint32_t)0x00200000)
#define ADC_ExternalTrigInjecConvEdge_RisingFalling ((uint32_t)0x00300000)

#define IS_ADC_EXT_INJEC_TRIG_EDGE(EDGE) (((EDGE) == ADC_ExternalTrigInjecConvEdge_None)    || \
                                          ((EDGE) == ADC_ExternalTrigInjecConvEdge_Rising)  || \
                                          ((EDGE) == ADC_ExternalTrigInjecConvEdge_Falling) || \
                                          ((EDGE) == ADC_ExternalTrigInjecConvEdge_RisingFalling))
/**
  * @}
  */ 


/** @defgroup ADC_external_trigger_sources_for_injected_channels_conversion 
  * @{
  */ 


/* TIM2 */
#define ADC_ExternalTrigInjecConv_T2_TRGO          ((uint32_t)0x00020000)
#define ADC_ExternalTrigInjecConv_T2_CC1           ((uint32_t)0x00030000)

/* TIM3 */
#define ADC_ExternalTrigInjecConv_T3_CC4           ((uint32_t)0x00040000)

/* TIM4 */
#define ADC_ExternalTrigInjecConv_T4_TRGO          ((uint32_t)0x00050000)
#define ADC_ExternalTrigInjecConv_T4_CC1           ((uint32_t)0x00060000)
#define ADC_ExternalTrigInjecConv_T4_CC2           ((uint32_t)0x00070000)
#define ADC_ExternalTrigInjecConv_T4_CC3           ((uint32_t)0x00080000)

/* TIM7 */
#define ADC_ExternalTrigInjecConv_T7_TRGO          ((uint32_t)0x000A0000)

/* TIM9 */
#define ADC_ExternalTrigInjecConv_T9_CC1           ((uint32_t)0x00000000)
#define ADC_ExternalTrigInjecConv_T9_TRGO          ((uint32_t)0x00010000)

/* TIM10 */
#define ADC_ExternalTrigInjecConv_T10_CC1          ((uint32_t)0x00090000)

/* EXTI */
#define ADC_ExternalTrigInjecConv_Ext_IT15         ((uint32_t)0x000F0000)

#define IS_ADC_EXT_INJEC_TRIG(INJTRIG) (((INJTRIG) == ADC_ExternalTrigInjecConv_T9_CC1)  || \
                                        ((INJTRIG) == ADC_ExternalTrigInjecConv_T9_TRGO) || \
                                        ((INJTRIG) == ADC_ExternalTrigInjecConv_T2_TRGO) || \
                                        ((INJTRIG) == ADC_ExternalTrigInjecConv_T2_CC1)  || \
                                        ((INJTRIG) == ADC_ExternalTrigInjecConv_T3_CC4)  || \
                                        ((INJTRIG) == ADC_ExternalTrigInjecConv_T4_TRGO) || \
                                        ((INJTRIG) == ADC_ExternalTrigInjecConv_T4_CC1)  || \
                                        ((INJTRIG) == ADC_ExternalTrigInjecConv_T4_CC2)  || \
                                        ((INJTRIG) == ADC_ExternalTrigInjecConv_T4_CC3)  || \
                                        ((INJTRIG) == ADC_ExternalTrigInjecConv_T10_CC1) || \
                                        ((INJTRIG) == ADC_ExternalTrigInjecConv_T7_TRGO) || \
                                        ((INJTRIG) == ADC_ExternalTrigInjecConv_Ext_IT15))
/**
  * @}
  */ 

/** @defgroup ADC_injected_channel_selection 
  * @{
  */ 
#define ADC_InjectedChannel_1                      ((uint8_t)0x18)
#define ADC_InjectedChannel_2                      ((uint8_t)0x1C)
#define ADC_InjectedChannel_3                      ((uint8_t)0x20)
#define ADC_InjectedChannel_4                      ((uint8_t)0x24)

#define IS_ADC_INJECTED_CHANNEL(CHANNEL) (((CHANNEL) == ADC_InjectedChannel_1) || \
                                          ((CHANNEL) == ADC_InjectedChannel_2) || \
                                          ((CHANNEL) == ADC_InjectedChannel_3) || \
                                          ((CHANNEL) == ADC_InjectedChannel_4))
/**
  * @}
  */ 

/** @defgroup ADC_analog_watchdog_selection 
  * @{
  */ 
  
#define ADC_AnalogWatchdog_SingleRegEnable         ((uint32_t)0x00800200)
#define ADC_AnalogWatchdog_SingleInjecEnable       ((uint32_t)0x00400200)
#define ADC_AnalogWatchdog_SingleRegOrInjecEnable  ((uint32_t)0x00C00200) 
#define ADC_AnalogWatchdog_AllRegEnable            ((uint32_t)0x00800000)
#define ADC_AnalogWatchdog_AllInjecEnable          ((uint32_t)0x00400000)
#define ADC_AnalogWatchdog_AllRegAllInjecEnable    ((uint32_t)0x00C00000)
#define ADC_AnalogWatchdog_None                    ((uint32_t)0x00000000)

#define IS_ADC_ANALOG_WATCHDOG(WATCHDOG) (((WATCHDOG) == ADC_AnalogWatchdog_SingleRegEnable)        || \
                                          ((WATCHDOG) == ADC_AnalogWatchdog_SingleInjecEnable)      || \
                                          ((WATCHDOG) == ADC_AnalogWatchdog_SingleRegOrInjecEnable) || \
                                          ((WATCHDOG) == ADC_AnalogWatchdog_AllRegEnable)           || \
                                          ((WATCHDOG) == ADC_AnalogWatchdog_AllInjecEnable)         || \
                                          ((WATCHDOG) == ADC_AnalogWatchdog_AllRegAllInjecEnable)   || \
                                          ((WATCHDOG) == ADC_AnalogWatchdog_None))
/**
  * @}
  */ 

/** @defgroup ADC_interrupts_definition 
  * @{
  */ 
  
#define ADC_IT_AWD                                 ((uint16_t)0x0106) 
#define ADC_IT_EOC                                 ((uint16_t)0x0205) 
#define ADC_IT_JEOC                                ((uint16_t)0x0407)  
#define ADC_IT_OVR                                 ((uint16_t)0x201A) 
 
#define IS_ADC_IT(IT) (((IT) == ADC_IT_AWD) || ((IT) == ADC_IT_EOC) || \
                       ((IT) == ADC_IT_JEOC)|| ((IT) == ADC_IT_OVR)) 
/**
  * @}
  */ 

/** @defgroup ADC_flags_definition 
  * @{
  */ 
  
#define ADC_FLAG_AWD                               ((uint16_t)0x0001)
#define ADC_FLAG_EOC                               ((uint16_t)0x0002)
#define ADC_FLAG_JEOC                              ((uint16_t)0x0004)
#define ADC_FLAG_JSTRT                             ((uint16_t)0x0008)
#define ADC_FLAG_STRT                              ((uint16_t)0x0010)
#define ADC_FLAG_OVR                               ((uint16_t)0x0020)
#define ADC_FLAG_ADONS                             ((uint16_t)0x0040)
#define ADC_FLAG_RCNR                              ((uint16_t)0x0100)
#define ADC_FLAG_JCNR                              ((uint16_t)0x0200) 
  
#define IS_ADC_CLEAR_FLAG(FLAG) ((((FLAG) & (uint16_t)0xFFC0) == 0x00) && ((FLAG) != 0x00))
   
#define IS_ADC_GET_FLAG(FLAG) (((FLAG) == ADC_FLAG_AWD)   || ((FLAG) == ADC_FLAG_EOC)  || \
                               ((FLAG) == ADC_FLAG_JEOC)  || ((FLAG)== ADC_FLAG_JSTRT) || \
                               ((FLAG) == ADC_FLAG_STRT)  || ((FLAG)== ADC_FLAG_OVR)   || \
                               ((FLAG) == ADC_FLAG_ADONS) || ((FLAG)== ADC_FLAG_RCNR)  || \
                               ((FLAG) == ADC_FLAG_JCNR))
/**
  * @}
  */ 

/** @defgroup ADC_thresholds 
  * @{
  */ 
  
#define IS_ADC_THRESHOLD(THRESHOLD) ((THRESHOLD) <= 0xFFF)

/**
  * @}
  */ 

/** @defgroup ADC_injected_offset 
  * @{
  */
   
#define IS_ADC_OFFSET(OFFSET) ((OFFSET) <= 0xFFF)

/**
  * @}
  */ 

/** @defgroup ADC_injected_length 
  * @{
  */
   
#define IS_ADC_INJECTED_LENGTH(LENGTH) (((LENGTH) >= 0x1) && ((LENGTH) <= 0x4))

/**
  * @}
  */ 

/** @defgroup ADC_injected_rank 
  * @{
  */ 
  
#define IS_ADC_INJECTED_RANK(RANK) (((RANK) >= 0x1) && ((RANK) <= 0x4))

/**
  * @}
  */ 

/** @defgroup ADC_regular_length 
  * @{
  */
   
#define IS_ADC_REGULAR_LENGTH(LENGTH) (((LENGTH) >= 1) && ((LENGTH) <= 28))

/**
  * @}
  */ 

/** @defgroup ADC_regular_rank 
  * @{
  */ 
  
#define IS_ADC_REGULAR_RANK(RANK) (((RANK) >= 1) && ((RANK) <= 28))

/**
  * @}
  */ 

/** @defgroup ADC_regular_discontinuous_mode_number 
  * @{
  */
   
#define IS_ADC_REGULAR_DISC_NUMBER(NUMBER) (((NUMBER) >= 0x1) && ((NUMBER) <= 0x8))

/**
  * @}
  */ 

/** @defgroup ADC_Bank_Selection 
  * @{
  */ 
#define ADC_Bank_A                                 ((uint8_t)0x00)
#define ADC_Bank_B                                 ((uint8_t)0x01)  
#define IS_ADC_BANK(BANK) (((BANK) == ADC_Bank_A)   || ((BANK) == ADC_Bank_B))

/**
  * @}
  */ 

/**
  * @}
  */ 

/* Exported macro ------------------------------------------------------------*/
/* Exported functions ------------------------------------------------------- */ 

/*  Function used to set the ADC configuration to the default reset state *****/   
void ADC_DeInit(ADC_TypeDef* ADCx); 

/* Initialization and Configuration functions *********************************/ 
void ADC_Init(ADC_TypeDef* ADCx, ADC_InitTypeDef* ADC_InitStruct);
void ADC_StructInit(ADC_InitTypeDef* ADC_InitStruct);
void ADC_CommonInit(ADC_CommonInitTypeDef* ADC_CommonInitStruct);
void ADC_CommonStructInit(ADC_CommonInitTypeDef* ADC_CommonInitStruct);
void ADC_Cmd(ADC_TypeDef* ADCx, FunctionalState NewState);
void ADC_BankSelection(ADC_TypeDef* ADCx, uint8_t ADC_Bank);

/* Power saving functions *****************************************************/
void ADC_PowerDownCmd(ADC_TypeDef* ADCx, uint32_t ADC_PowerDown, FunctionalState NewState);
void ADC_DelaySelectionConfig(ADC_TypeDef* ADCx, uint8_t ADC_DelayLength);

/* Analog Watchdog configuration functions ************************************/
void ADC_AnalogWatchdogCmd(ADC_TypeDef* ADCx, uint32_t ADC_AnalogWatchdog);
void ADC_AnalogWatchdogThresholdsConfig(ADC_TypeDef* ADCx, uint16_t HighThreshold,uint16_t LowThreshold);
void ADC_AnalogWatchdogSingleChannelConfig(ADC_TypeDef* ADCx, uint8_t ADC_Channel);

/* Temperature Sensor & Vrefint (Voltage Reference internal) management function */
void ADC_TempSensorVrefintCmd(FunctionalState NewState);

/* Regular Channels Configuration functions ***********************************/
void ADC_RegularChannelConfig(ADC_TypeDef* ADCx, uint8_t ADC_Channel, uint8_t Rank, uint8_t ADC_SampleTime);
void ADC_SoftwareStartConv(ADC_TypeDef* ADCx);
FlagStatus ADC_GetSoftwareStartConvStatus(ADC_TypeDef* ADCx);
void ADC_EOCOnEachRegularChannelCmd(ADC_TypeDef* ADCx, FunctionalState NewState);
void ADC_ContinuousModeCmd(ADC_TypeDef* ADCx, FunctionalState NewState);
void ADC_DiscModeChannelCountConfig(ADC_TypeDef* ADCx, uint8_t Number);
void ADC_DiscModeCmd(ADC_TypeDef* ADCx, FunctionalState NewState);
uint16_t ADC_GetConversionValue(ADC_TypeDef* ADCx);

/* Regular Channels DMA Configuration functions *******************************/
void ADC_DMACmd(ADC_TypeDef* ADCx, FunctionalState NewState);
void ADC_DMARequestAfterLastTransferCmd(ADC_TypeDef* ADCx, FunctionalState NewState);

/* Injected channels Configuration functions **********************************/
void ADC_InjectedChannelConfig(ADC_TypeDef* ADCx, uint8_t ADC_Channel, uint8_t Rank, uint8_t ADC_SampleTime);
void ADC_InjectedSequencerLengthConfig(ADC_TypeDef* ADCx, uint8_t Length);
void ADC_SetInjectedOffset(ADC_TypeDef* ADCx, uint8_t ADC_InjectedChannel, uint16_t Offset);
void ADC_ExternalTrigInjectedConvConfig(ADC_TypeDef* ADCx, uint32_t ADC_ExternalTrigInjecConv);
void ADC_ExternalTrigInjectedConvEdgeConfig(ADC_TypeDef* ADCx, uint32_t ADC_ExternalTrigInjecConvEdge);
void ADC_SoftwareStartInjectedConv(ADC_TypeDef* ADCx);
FlagStatus ADC_GetSoftwareStartInjectedConvCmdStatus(ADC_TypeDef* ADCx);
void ADC_AutoInjectedConvCmd(ADC_TypeDef* ADCx, FunctionalState NewState);
void ADC_InjectedDiscModeCmd(ADC_TypeDef* ADCx, FunctionalState NewState);
uint16_t ADC_GetInjectedConversionValue(ADC_TypeDef* ADCx, uint8_t ADC_InjectedChannel);

/* Interrupts and flags management functions **********************************/
void ADC_ITConfig(ADC_TypeDef* ADCx, uint16_t ADC_IT, FunctionalState NewState);
FlagStatus ADC_GetFlagStatus(ADC_TypeDef* ADCx, uint16_t ADC_FLAG);
void ADC_ClearFlag(ADC_TypeDef* ADCx, uint16_t ADC_FLAG);
ITStatus ADC_GetITStatus(ADC_TypeDef* ADCx, uint16_t ADC_IT);
void ADC_ClearITPendingBit(ADC_TypeDef* ADCx, uint16_t ADC_IT);

#ifdef __cplusplus
}
#endif

#endif /*__STM32L1xx_ADC_H */

/**
  * @}
  */ 

/**
  * @}
  */ 

/************************ (C) COPYRIGHT STMicroelectronics *****END OF FILE****/
