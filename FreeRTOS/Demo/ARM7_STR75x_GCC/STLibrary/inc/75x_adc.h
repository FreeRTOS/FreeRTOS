/******************** (C) COPYRIGHT 2006 STMicroelectronics ********************
* File Name          : 75x_adc.h
* Author             : MCD Application Team
* Date First Issued  : 03/10/2006  
* Description        : This file contains all the functions prototypes for the
*                      ADC software library.
********************************************************************************
* History:
* 07/17/2006 : V1.0
* 03/10/2006 : V0.1 
********************************************************************************
* THE PRESENT SOFTWARE WHICH IS FOR GUIDANCE ONLY AIMS AT PROVIDING CUSTOMERS
* WITH CODING INFORMATION REGARDING THEIR PRODUCTS IN ORDER FOR THEM TO SAVE TIME.
* AS A RESULT, STMICROELECTRONICS SHALL NOT BE HELD LIABLE FOR ANY DIRECT, 
* INDIRECT OR CONSEQUENTIAL DAMAGES WITH RESPECT TO ANY CLAIMS ARISING FROM THE
* CONTENT OF SUCH SOFTWARE AND/OR THE USE MADE BY CUSTOMERS OF THE CODING 
* INFORMATION CONTAINED HEREIN IN CONNECTION WITH THEIR PRODUCTS.
*******************************************************************************/

/* Define to prevent recursive inclusion -------------------------------------*/
#ifndef __75x_ADC_H
#define __75x_ADC_H

/* Includes ------------------------------------------------------------------*/
#include "75x_map.h"

/* Exported types ------------------------------------------------------------*/
/* ADC Init structure definition */
typedef struct
{
  u16 ADC_ConversionMode;
  u16 ADC_ExtTrigger;
  u16 ADC_AutoClockOff;
  u8  ADC_SamplingPrescaler;
  u8  ADC_ConversionPrescaler;
  u8  ADC_FirstChannel;
  u8  ADC_ChannelNumber;
 }ADC_InitTypeDef;

/* Exported constants --------------------------------------------------------*/
/* ADC control status flags */
#define ADC_FLAG_ECH                            0x0001
#define ADC_FLAG_EOC                            0x0002
#define ADC_FLAG_JECH                           0x0004
#define ADC_FLAG_JEOC                           0x0008
#define ADC_FLAG_AnalogWatchdog0_LowThreshold   0x0010
#define ADC_FLAG_AnalogWatchdog0_HighThreshold  0x0020
#define ADC_FLAG_AnalogWatchdog1_LowThreshold   0x0040
#define ADC_FLAG_AnalogWatchdog1_HighThreshold  0x0080
#define ADC_FLAG_AnalogWatchdog2_LowThreshold   0x0100
#define ADC_FLAG_AnalogWatchdog2_HighThreshold  0x0200
#define ADC_FLAG_AnalogWatchdog3_LowThreshold   0x0400
#define ADC_FLAG_AnalogWatchdog3_HighThreshold  0x0800

/* ADC Interrupt sources */
#define ADC_IT_ECH                            0x0001
#define ADC_IT_EOC                            0x0002
#define ADC_IT_JECH                           0x0004
#define ADC_IT_JEOC                           0x0008
#define ADC_IT_AnalogWatchdog0_LowThreshold   0x0010
#define ADC_IT_AnalogWatchdog0_HighThreshold  0x0020
#define ADC_IT_AnalogWatchdog1_LowThreshold   0x0040
#define ADC_IT_AnalogWatchdog1_HighThreshold  0x0080
#define ADC_IT_AnalogWatchdog2_LowThreshold   0x0100
#define ADC_IT_AnalogWatchdog2_HighThreshold  0x0200
#define ADC_IT_AnalogWatchdog3_LowThreshold   0x0400
#define ADC_IT_AnalogWatchdog3_HighThreshold  0x0800
#define ADC_IT_ALL                            0x0FFF

/* ADC Watchdogs Thresholds */
#define ADC_AnalogWatchdog0   0x0030
#define ADC_AnalogWatchdog1   0x00C0
#define ADC_AnalogWatchdog2   0x0300
#define ADC_AnalogWatchdog3   0x0C00

/* ADC Channels */
#define ADC_CHANNEL0   0x0
#define ADC_CHANNEL1   0x1
#define ADC_CHANNEL2   0x2
#define ADC_CHANNEL3   0x3
#define ADC_CHANNEL4   0x4
#define ADC_CHANNEL5   0x5
#define ADC_CHANNEL6   0x6
#define ADC_CHANNEL7   0x7
#define ADC_CHANNEL8   0x8
#define ADC_CHANNEL9   0x9
#define ADC_CHANNEL10  0xA
#define ADC_CHANNEL11  0xB
#define ADC_CHANNEL12  0xC
#define ADC_CHANNEL13  0xD
#define ADC_CHANNEL14  0xE
#define ADC_CHANNEL15  0xF

/* ADC DMA Channels */
#define ADC_DMA_CHANNEL0   0x0001
#define ADC_DMA_CHANNEL1   0x0002
#define ADC_DMA_CHANNEL2   0x0004
#define ADC_DMA_CHANNEL3   0x0008
#define ADC_DMA_CHANNEL4   0x0010
#define ADC_DMA_CHANNEL5   0x0020
#define ADC_DMA_CHANNEL6   0x0040
#define ADC_DMA_CHANNEL7   0x0080
#define ADC_DMA_CHANNEL8   0x0100
#define ADC_DMA_CHANNEL9   0x0200
#define ADC_DMA_CHANNEL10  0x0400
#define ADC_DMA_CHANNEL11  0x0800
#define ADC_DMA_CHANNEL12  0x1000
#define ADC_DMA_CHANNEL13  0x2000
#define ADC_DMA_CHANNEL14  0x4000
#define ADC_DMA_CHANNEL15  0x8000

/* Trigger conversion detection */
#define ADC_ExtTrigger_LowLevel    0x4FFF
#define ADC_ExtTrigger_HighLevel   0x5000
#define ADC_ExtTrigger_FallingEdge 0x6000
#define ADC_ExtTrigger_RisingEdge  0x7000
#define ADC_ExtTrigger_Disable     0x8FFF

/* DMA enable config */
#define ADC_DMA_ExtTrigger_HighLevel  0x6000
#define ADC_DMA_ExtTrigger_LowLevel   0x4FFF
#define ADC_DMA_Enable                0x8000
#define ADC_DMA_Disable               0x3FFF

/* Injected Trigger conversion detection */
#define ADC_Injec_ExtTrigger_RisingEdge  0x6000
#define ADC_Injec_ExtTrigger_FallingEdge 0xDFFF
#define ADC_Injec_ExtTrigger_Disable     0x3FFF

/* Start Conversion */
#define ADC_Conversion_Start   0x0001
#define ADC_Conversion_Stop    0xFFFE

/* ADC Conversion Modes */
#define ADC_ConversionMode_Scan     0x8000
#define ADC_ConversionMode_OneShot  0x7FFF

/* Auto Clock Off */
#define ADC_AutoClockOff_Enable  0x4000
#define ADC_AutoClockOff_Disable 0xBFFF

/* Calibration */
#define ADC_Calibration_ON       0x0002
#define ADC_CalibAverage_Disable 0x0020
#define ADC_CalibAverage_Enable  0xFFDF

/* Exported macro ------------------------------------------------------------*/
/* Exported functions --------------------------------------------------------*/

void ADC_DeInit(void);
void ADC_Init(ADC_InitTypeDef *ADC_InitStruct);
void ADC_StructInit(ADC_InitTypeDef *ADC_InitStruct);
void ADC_Cmd(FunctionalState NewState);
void ADC_StartCalibration(u16 ADC_CalibAverage);
FlagStatus ADC_GetCalibrationStatus(void);
void ADC_ConversionCmd(u16 ADC_Conversion);
FlagStatus ADC_GetSTARTBitStatus(void);
void ADC_AutoClockOffConfig(FunctionalState NewState);
u16 ADC_GetConversionValue(u8 ADC_CHANNEL);
void ADC_ITConfig(u16 ADC_IT, FunctionalState NewState);
void ADC_AnalogWatchdogConfig(u16 ADC_AnalogWatchdog, u8 ADC_CHANNEL, 
                              u16 LowThreshold, u16 HighThreshold);
void ADC_AnalogWatchdogCmd(u16 ADC_AnalogWatchdog, FunctionalState NewState);
u16 ADC_GetAnalogWatchdogResult(u16 ADC_AnalogWatchdog);
void ADC_StartInjectedConversion(void);
void ADC_InjectedConversionConfig(u16 ADC_Injec_ExtTrigger, u8 FirstChannel, u8 ChannelNumber);
void ADC_DMAConfig(u16 ADC_DMA_CHANNEL, FunctionalState NewState);
void ADC_DMACmd(u16 ADC_DMA);
u16 ADC_GetDMAFirstEnabledChannel(void);
FlagStatus ADC_GetFlagStatus(u16 ADC_FLAG);
void ADC_ClearFlag(u16 ADC_FLAG);
ITStatus ADC_GetITStatus(u16 ADC_IT);
void ADC_ClearITPendingBit(u16 ADC_IT);

#endif /*__75x_ADC_H */

/******************* (C) COPYRIGHT 2006 STMicroelectronics *****END OF FILE****/
