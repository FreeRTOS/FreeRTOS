/**
  ******************************************************************************
  * @file    stm32l1xx_syscfg.h
  * @author  MCD Application Team
  * @version V1.1.1
  * @date    05-March-2012
  * @brief   This file contains all the functions prototypes for the SYSCFG 
  *          firmware library.
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

/*!< Define to prevent recursive inclusion -------------------------------------*/
#ifndef __STM32L1xx_SYSCFG_H
#define __STM32L1xx_SYSCFG_H

#ifdef __cplusplus
 extern "C" {
#endif

/*!< Includes ------------------------------------------------------------------*/
#include "stm32l1xx.h"

/** @addtogroup STM32L1xx_StdPeriph_Driver
  * @{
  */

/** @addtogroup SYSCFG
  * @{
  */ 
  
/* Exported types ------------------------------------------------------------*/
/* Exported constants --------------------------------------------------------*/

/** @defgroup SYSCFG_Exported_Constants
  * @{
  */ 
  
/** @defgroup EXTI_Port_Sources 
  * @{
  */ 
#define EXTI_PortSourceGPIOA       ((uint8_t)0x00)
#define EXTI_PortSourceGPIOB       ((uint8_t)0x01)
#define EXTI_PortSourceGPIOC       ((uint8_t)0x02)
#define EXTI_PortSourceGPIOD       ((uint8_t)0x03)
#define EXTI_PortSourceGPIOE       ((uint8_t)0x04)
#define EXTI_PortSourceGPIOH       ((uint8_t)0x05)
#define EXTI_PortSourceGPIOF       ((uint8_t)0x06)
#define EXTI_PortSourceGPIOG       ((uint8_t)0x07)
                                      
#define IS_EXTI_PORT_SOURCE(PORTSOURCE) (((PORTSOURCE) == EXTI_PortSourceGPIOA) || \
                                         ((PORTSOURCE) == EXTI_PortSourceGPIOB) || \
                                         ((PORTSOURCE) == EXTI_PortSourceGPIOC) || \
                                         ((PORTSOURCE) == EXTI_PortSourceGPIOD) || \
                                         ((PORTSOURCE) == EXTI_PortSourceGPIOE) || \
                                         ((PORTSOURCE) == EXTI_PortSourceGPIOF) || \
                                         ((PORTSOURCE) == EXTI_PortSourceGPIOG) || \
                                         ((PORTSOURCE) == EXTI_PortSourceGPIOH)) 
/**
  * @}
  */

/** @defgroup EXTI_Pin_sources 
  * @{
  */ 
#define EXTI_PinSource0            ((uint8_t)0x00)
#define EXTI_PinSource1            ((uint8_t)0x01)
#define EXTI_PinSource2            ((uint8_t)0x02)
#define EXTI_PinSource3            ((uint8_t)0x03)
#define EXTI_PinSource4            ((uint8_t)0x04)
#define EXTI_PinSource5            ((uint8_t)0x05)
#define EXTI_PinSource6            ((uint8_t)0x06)
#define EXTI_PinSource7            ((uint8_t)0x07)
#define EXTI_PinSource8            ((uint8_t)0x08)
#define EXTI_PinSource9            ((uint8_t)0x09)
#define EXTI_PinSource10           ((uint8_t)0x0A)
#define EXTI_PinSource11           ((uint8_t)0x0B)
#define EXTI_PinSource12           ((uint8_t)0x0C)
#define EXTI_PinSource13           ((uint8_t)0x0D)
#define EXTI_PinSource14           ((uint8_t)0x0E)
#define EXTI_PinSource15           ((uint8_t)0x0F)
#define IS_EXTI_PIN_SOURCE(PINSOURCE) (((PINSOURCE) == EXTI_PinSource0) || \
                                       ((PINSOURCE) == EXTI_PinSource1) || \
                                       ((PINSOURCE) == EXTI_PinSource2) || \
                                       ((PINSOURCE) == EXTI_PinSource3) || \
                                       ((PINSOURCE) == EXTI_PinSource4) || \
                                       ((PINSOURCE) == EXTI_PinSource5) || \
                                       ((PINSOURCE) == EXTI_PinSource6) || \
                                       ((PINSOURCE) == EXTI_PinSource7) || \
                                       ((PINSOURCE) == EXTI_PinSource8) || \
                                       ((PINSOURCE) == EXTI_PinSource9) || \
                                       ((PINSOURCE) == EXTI_PinSource10) || \
                                       ((PINSOURCE) == EXTI_PinSource11) || \
                                       ((PINSOURCE) == EXTI_PinSource12) || \
                                       ((PINSOURCE) == EXTI_PinSource13) || \
                                       ((PINSOURCE) == EXTI_PinSource14) || \
                                       ((PINSOURCE) == EXTI_PinSource15))
/**
  * @}
  */

/** @defgroup SYSCFG_Memory_Remap_Config 
  * @{
  */ 
#define SYSCFG_MemoryRemap_Flash       ((uint8_t)0x00)
#define SYSCFG_MemoryRemap_SystemFlash ((uint8_t)0x01)
#define SYSCFG_MemoryRemap_FSMC        ((uint8_t)0x02)
#define SYSCFG_MemoryRemap_SRAM        ((uint8_t)0x03)
   
#define IS_SYSCFG_MEMORY_REMAP_CONFING(REMAP) (((REMAP) == SYSCFG_MemoryRemap_Flash) || \
                                               ((REMAP) == SYSCFG_MemoryRemap_SystemFlash) || \
                                               ((REMAP) == SYSCFG_MemoryRemap_FSMC) || \
                                               ((REMAP) == SYSCFG_MemoryRemap_SRAM))

/**
  * @}
  */
  
/** @defgroup RI_Resistor
  * @{
  */

#define RI_Resistor_10KPU              COMP_CSR_10KPU
#define RI_Resistor_400KPU             COMP_CSR_400KPU
#define RI_Resistor_10KPD              COMP_CSR_10KPD
#define RI_Resistor_400KPD             COMP_CSR_400KPD

#define IS_RI_RESISTOR(RESISTOR)  (((RESISTOR) == COMP_CSR_10KPU) || \
                                   ((RESISTOR) == COMP_CSR_400KPU) || \
                                   ((RESISTOR) == COMP_CSR_10KPD) || \
                                   ((RESISTOR) == COMP_CSR_400KPD))
 
/**
  * @}
  */ 

/** @defgroup RI_Channel
  * @{
  */

#define RI_Channel_3                   ((uint32_t)0x04000000)
#define RI_Channel_8                   ((uint32_t)0x08000000)
#define RI_Channel_13                  ((uint32_t)0x10000000)

#define IS_RI_CHANNEL(CHANNEL)  (((CHANNEL) == RI_Channel_3) || \
                                 ((CHANNEL) == RI_Channel_8) || \
                                 ((CHANNEL) == RI_Channel_13))

/**
  * @}
  */ 

/** @defgroup RI_ChannelSpeed
  * @{
  */

#define RI_ChannelSpeed_Fast           ((uint32_t)0x00000000)
#define RI_ChannelSpeed_Slow           ((uint32_t)0x00000001)

#define IS_RI_CHANNELSPEED(SPEED)  (((SPEED) == RI_ChannelSpeed_Fast) || \
                                    ((SPEED) == RI_ChannelSpeed_Slow))

/**
  * @}
  */ 

/** @defgroup RI_InputCapture
  * @{
  */ 
  
#define RI_InputCapture_IC1  RI_ICR_IC1    /*!< Input Capture 1 */
#define RI_InputCapture_IC2  RI_ICR_IC2    /*!< Input Capture 2 */
#define RI_InputCapture_IC3  RI_ICR_IC3    /*!< Input Capture 3 */
#define RI_InputCapture_IC4  RI_ICR_IC4    /*!< Input Capture 4 */

#define IS_RI_INPUTCAPTURE(INPUTCAPTURE) ((((INPUTCAPTURE) & (uint32_t)0xFFC2FFFF) == 0x00) && ((INPUTCAPTURE) != (uint32_t)0x00))
/**
  * @}
  */ 
  
/** @defgroup TIM_Select
  * @{
  */ 
  
#define TIM_Select_None  ((uint32_t)0x00000000)    /*!< None selected */
#define TIM_Select_TIM2  ((uint32_t)0x00010000)    /*!< Timer 2 selected */
#define TIM_Select_TIM3  ((uint32_t)0x00020000)    /*!< Timer 3 selected */
#define TIM_Select_TIM4  ((uint32_t)0x00030000)    /*!< Timer 4 selected */

#define IS_RI_TIM(TIM) (((TIM) == TIM_Select_None) || \
                        ((TIM) == TIM_Select_TIM2) || \
                        ((TIM) == TIM_Select_TIM3) || \
                        ((TIM) == TIM_Select_TIM4))

/**
  * @}
  */ 
  
/** @defgroup RI_InputCaptureRouting
  * @{
  */ 
                                                          /* TIMx_IC1 TIMx_IC2  TIMx_IC3  TIMx_IC4 */  
#define RI_InputCaptureRouting_0   ((uint32_t)0x00000000) /* PA0       PA1      PA2       PA3      */
#define RI_InputCaptureRouting_1   ((uint32_t)0x00000001) /* PA4       PA5      PA6       PA7      */
#define RI_InputCaptureRouting_2   ((uint32_t)0x00000002) /* PA8       PA9      PA10      PA11     */
#define RI_InputCaptureRouting_3   ((uint32_t)0x00000003) /* PA12      PA13     PA14      PA15     */
#define RI_InputCaptureRouting_4   ((uint32_t)0x00000004) /* PC0       PC1      PC2       PC3      */
#define RI_InputCaptureRouting_5   ((uint32_t)0x00000005) /* PC4       PC5      PC6       PC7      */
#define RI_InputCaptureRouting_6   ((uint32_t)0x00000006) /* PC8       PC9      PC10      PC11     */
#define RI_InputCaptureRouting_7   ((uint32_t)0x00000007) /* PC12      PC13     PC14      PC15     */
#define RI_InputCaptureRouting_8   ((uint32_t)0x00000008) /* PD0       PD1      PD2       PD3      */
#define RI_InputCaptureRouting_9   ((uint32_t)0x00000009) /* PD4       PD5      PD6       PD7      */
#define RI_InputCaptureRouting_10  ((uint32_t)0x0000000A) /* PD8       PD9      PD10      PD11     */
#define RI_InputCaptureRouting_11  ((uint32_t)0x0000000B) /* PD12      PD13     PD14      PD15     */
#define RI_InputCaptureRouting_12  ((uint32_t)0x0000000C) /* PE0       PE1      PE2       PE3      */
#define RI_InputCaptureRouting_13  ((uint32_t)0x0000000D) /* PE4       PE5      PE6       PE7      */
#define RI_InputCaptureRouting_14  ((uint32_t)0x0000000E) /* PE8       PE9      PE10      PE11     */
#define RI_InputCaptureRouting_15  ((uint32_t)0x0000000F) /* PE12      PE13     PE14      PE15     */

#define IS_RI_INPUTCAPTURE_ROUTING(ROUTING) (((ROUTING) == RI_InputCaptureRouting_0) || \
                                             ((ROUTING) == RI_InputCaptureRouting_1) || \
                                             ((ROUTING) == RI_InputCaptureRouting_2) || \
                                             ((ROUTING) == RI_InputCaptureRouting_3) || \
                                             ((ROUTING) == RI_InputCaptureRouting_4) || \
                                             ((ROUTING) == RI_InputCaptureRouting_5) || \
                                             ((ROUTING) == RI_InputCaptureRouting_6) || \
                                             ((ROUTING) == RI_InputCaptureRouting_7) || \
                                             ((ROUTING) == RI_InputCaptureRouting_8) || \
                                             ((ROUTING) == RI_InputCaptureRouting_9) || \
                                             ((ROUTING) == RI_InputCaptureRouting_10) || \
                                             ((ROUTING) == RI_InputCaptureRouting_11) || \
                                             ((ROUTING) == RI_InputCaptureRouting_12) || \
                                             ((ROUTING) == RI_InputCaptureRouting_13) || \
                                             ((ROUTING) == RI_InputCaptureRouting_14) || \
                                             ((ROUTING) == RI_InputCaptureRouting_15))

/**
  * @}
  */ 

/** @defgroup RI_IOSwitch
  * @{
  */ 
  
/* ASCR1 I/O switch: bit 31 is set to '1' to indicate that the mask is in ASCR1 register */
#define RI_IOSwitch_CH0        ((uint32_t)0x80000001)
#define RI_IOSwitch_CH1        ((uint32_t)0x80000002)
#define RI_IOSwitch_CH2        ((uint32_t)0x80000004)
#define RI_IOSwitch_CH3        ((uint32_t)0x80000008)
#define RI_IOSwitch_CH4        ((uint32_t)0x80000010)
#define RI_IOSwitch_CH5        ((uint32_t)0x80000020)
#define RI_IOSwitch_CH6        ((uint32_t)0x80000040)
#define RI_IOSwitch_CH7        ((uint32_t)0x80000080)
#define RI_IOSwitch_CH8        ((uint32_t)0x80000100)
#define RI_IOSwitch_CH9        ((uint32_t)0x80000200)
#define RI_IOSwitch_CH10       ((uint32_t)0x80000400)
#define RI_IOSwitch_CH11       ((uint32_t)0x80000800)
#define RI_IOSwitch_CH12       ((uint32_t)0x80001000)
#define RI_IOSwitch_CH13       ((uint32_t)0x80002000)
#define RI_IOSwitch_CH14       ((uint32_t)0x80004000)
#define RI_IOSwitch_CH15       ((uint32_t)0x80008000)
#define RI_IOSwitch_CH31       ((uint32_t)0x80010000)
#define RI_IOSwitch_CH18       ((uint32_t)0x80040000)
#define RI_IOSwitch_CH19       ((uint32_t)0x80080000)
#define RI_IOSwitch_CH20       ((uint32_t)0x80100000)
#define RI_IOSwitch_CH21       ((uint32_t)0x80200000)
#define RI_IOSwitch_CH22       ((uint32_t)0x80400000)
#define RI_IOSwitch_CH23       ((uint32_t)0x80800000)
#define RI_IOSwitch_CH24       ((uint32_t)0x81000000)
#define RI_IOSwitch_CH25       ((uint32_t)0x82000000)
#define RI_IOSwitch_VCOMP      ((uint32_t)0x84000000) /* VCOMP is an internal switch used to connect 
                                                         selected channel to COMP1 non inverting input */
#define RI_IOSwitch_CH27       ((uint32_t)0x88000000)
#define RI_IOSwitch_CH28       ((uint32_t)0x90000000)
#define RI_IOSwitch_CH29       ((uint32_t)0xA0000000)
#define RI_IOSwitch_CH30       ((uint32_t)0xC0000000)

/* ASCR2 IO switch: bit 31 is set to '0' to indicate that the mask is in ASCR2 register */  
#define RI_IOSwitch_GR10_1     ((uint32_t)0x00000001)
#define RI_IOSwitch_GR10_2     ((uint32_t)0x00000002)
#define RI_IOSwitch_GR10_3     ((uint32_t)0x00000004)
#define RI_IOSwitch_GR10_4     ((uint32_t)0x00000008)
#define RI_IOSwitch_GR6_1      ((uint32_t)0x00000010)
#define RI_IOSwitch_GR6_2      ((uint32_t)0x00000020)
#define RI_IOSwitch_GR5_1      ((uint32_t)0x00000040)
#define RI_IOSwitch_GR5_2      ((uint32_t)0x00000080)
#define RI_IOSwitch_GR5_3      ((uint32_t)0x00000100)
#define RI_IOSwitch_GR4_1      ((uint32_t)0x00000200)
#define RI_IOSwitch_GR4_2      ((uint32_t)0x00000400)
#define RI_IOSwitch_GR4_3      ((uint32_t)0x00000800)
#define RI_IOSwitch_GR4_4      ((uint32_t)0x00008000)
#define RI_IOSwitch_CH0b       ((uint32_t)0x00010000)
#define RI_IOSwitch_CH1b       ((uint32_t)0x00020000)
#define RI_IOSwitch_CH2b       ((uint32_t)0x00040000)
#define RI_IOSwitch_CH3b       ((uint32_t)0x00080000)
#define RI_IOSwitch_CH6b       ((uint32_t)0x00100000)
#define RI_IOSwitch_CH7b       ((uint32_t)0x00200000)
#define RI_IOSwitch_CH8b       ((uint32_t)0x00400000)
#define RI_IOSwitch_CH9b       ((uint32_t)0x00800000)
#define RI_IOSwitch_CH10b      ((uint32_t)0x01000000)
#define RI_IOSwitch_CH11b      ((uint32_t)0x02000000)
#define RI_IOSwitch_CH12b      ((uint32_t)0x04000000)
#define RI_IOSwitch_GR6_3      ((uint32_t)0x08000000)
#define RI_IOSwitch_GR6_4      ((uint32_t)0x10000000)
#define RI_IOSwitch_GR5_4      ((uint32_t)0x20000000)


#define IS_RI_IOSWITCH(IOSWITCH) (((IOSWITCH) == RI_IOSwitch_CH0) || \
                                  ((IOSWITCH) == RI_IOSwitch_CH1) || \
                                  ((IOSWITCH) == RI_IOSwitch_CH2) || \
                                  ((IOSWITCH) == RI_IOSwitch_CH3) || \
                                  ((IOSWITCH) == RI_IOSwitch_CH4) || \
                                  ((IOSWITCH) == RI_IOSwitch_CH5) || \
                                  ((IOSWITCH) == RI_IOSwitch_CH6) || \
                                  ((IOSWITCH) == RI_IOSwitch_CH7) || \
                                  ((IOSWITCH) == RI_IOSwitch_CH8) || \
                                  ((IOSWITCH) == RI_IOSwitch_CH9) || \
                                  ((IOSWITCH) == RI_IOSwitch_CH10) || \
                                  ((IOSWITCH) == RI_IOSwitch_CH11) || \
                                  ((IOSWITCH) == RI_IOSwitch_CH12) || \
                                  ((IOSWITCH) == RI_IOSwitch_CH13) || \
                                  ((IOSWITCH) == RI_IOSwitch_CH14) || \
                                  ((IOSWITCH) == RI_IOSwitch_CH15) || \
                                  ((IOSWITCH) == RI_IOSwitch_CH18) || \
                                  ((IOSWITCH) == RI_IOSwitch_CH19) || \
                                  ((IOSWITCH) == RI_IOSwitch_CH20) || \
                                  ((IOSWITCH) == RI_IOSwitch_CH21) || \
                                  ((IOSWITCH) == RI_IOSwitch_CH22) || \
                                  ((IOSWITCH) == RI_IOSwitch_CH23) || \
                                  ((IOSWITCH) == RI_IOSwitch_CH24) || \
                                  ((IOSWITCH) == RI_IOSwitch_CH25) || \
                                  ((IOSWITCH) == RI_IOSwitch_VCOMP) || \
                                  ((IOSWITCH) == RI_IOSwitch_CH27) || \
                                  ((IOSWITCH) == RI_IOSwitch_CH28) || \
                                  ((IOSWITCH) == RI_IOSwitch_CH29) || \
                                  ((IOSWITCH) == RI_IOSwitch_CH30) || \
                                  ((IOSWITCH) == RI_IOSwitch_CH31) || \
                                  ((IOSWITCH) == RI_IOSwitch_GR10_1) || \
                                  ((IOSWITCH) == RI_IOSwitch_GR10_2) || \
                                  ((IOSWITCH) == RI_IOSwitch_GR10_3) || \
                                  ((IOSWITCH) == RI_IOSwitch_GR10_4) || \
                                  ((IOSWITCH) == RI_IOSwitch_GR6_1) || \
                                  ((IOSWITCH) == RI_IOSwitch_GR6_2) || \
                                  ((IOSWITCH) == RI_IOSwitch_GR6_3) || \
                                  ((IOSWITCH) == RI_IOSwitch_GR6_4) || \
                                  ((IOSWITCH) == RI_IOSwitch_GR5_1) || \
                                  ((IOSWITCH) == RI_IOSwitch_GR5_2) || \
                                  ((IOSWITCH) == RI_IOSwitch_GR5_3) || \
                                  ((IOSWITCH) == RI_IOSwitch_GR5_4) || \
                                  ((IOSWITCH) == RI_IOSwitch_GR4_1) || \
                                  ((IOSWITCH) == RI_IOSwitch_GR4_2) || \
                                  ((IOSWITCH) == RI_IOSwitch_GR4_3) || \
                                  ((IOSWITCH) == RI_IOSwitch_GR4_4) || \
                                  ((IOSWITCH) == RI_IOSwitch_CH0b) || \
                                  ((IOSWITCH) == RI_IOSwitch_CH1b) || \
                                  ((IOSWITCH) == RI_IOSwitch_CH2b) || \
                                  ((IOSWITCH) == RI_IOSwitch_CH3b) || \
                                  ((IOSWITCH) == RI_IOSwitch_CH6b) || \
                                  ((IOSWITCH) == RI_IOSwitch_CH7b) || \
                                  ((IOSWITCH) == RI_IOSwitch_CH8b) || \
                                  ((IOSWITCH) == RI_IOSwitch_CH9b) || \
                                  ((IOSWITCH) == RI_IOSwitch_CH10b) || \
                                  ((IOSWITCH) == RI_IOSwitch_CH11b) || \
                                  ((IOSWITCH) == RI_IOSwitch_CH12b))

/**
  * @}
  */

/** @defgroup RI_Port
  * @{
  */

#define RI_PortA                 ((uint8_t)0x01)   /*!< GPIOA selected */
#define RI_PortB                 ((uint8_t)0x02)   /*!< GPIOB selected */
#define RI_PortC                 ((uint8_t)0x03)   /*!< GPIOC selected */
#define RI_PortD                 ((uint8_t)0x04)   /*!< GPIOD selected */
#define RI_PortE                 ((uint8_t)0x05)   /*!< GPIOE selected */
#define RI_PortF                 ((uint8_t)0x06)   /*!< GPIOF selected */
#define RI_PortG                 ((uint8_t)0x07)   /*!< GPIOG selected */

#define IS_RI_PORT(PORT) (((PORT) == RI_PortA) || \
                          ((PORT) == RI_PortB) || \
                          ((PORT) == RI_PortC) || \
                          ((PORT) == RI_PortD) || \
                          ((PORT) == RI_PortE) || \
                          ((PORT) == RI_PortF) || \
                          ((PORT) == RI_PortG))
/**
  * @}
  */

/** @defgroup RI_Pin define 
  * @{
  */
#define RI_Pin_0                 ((uint16_t)0x0001)  /*!< Pin 0 selected */
#define RI_Pin_1                 ((uint16_t)0x0002)  /*!< Pin 1 selected */
#define RI_Pin_2                 ((uint16_t)0x0004)  /*!< Pin 2 selected */
#define RI_Pin_3                 ((uint16_t)0x0008)  /*!< Pin 3 selected */
#define RI_Pin_4                 ((uint16_t)0x0010)  /*!< Pin 4 selected */
#define RI_Pin_5                 ((uint16_t)0x0020)  /*!< Pin 5 selected */
#define RI_Pin_6                 ((uint16_t)0x0040)  /*!< Pin 6 selected */
#define RI_Pin_7                 ((uint16_t)0x0080)  /*!< Pin 7 selected */
#define RI_Pin_8                 ((uint16_t)0x0100)  /*!< Pin 8 selected */
#define RI_Pin_9                 ((uint16_t)0x0200)  /*!< Pin 9 selected */
#define RI_Pin_10                ((uint16_t)0x0400)  /*!< Pin 10 selected */
#define RI_Pin_11                ((uint16_t)0x0800)  /*!< Pin 11 selected */
#define RI_Pin_12                ((uint16_t)0x1000)  /*!< Pin 12 selected */
#define RI_Pin_13                ((uint16_t)0x2000)  /*!< Pin 13 selected */
#define RI_Pin_14                ((uint16_t)0x4000)  /*!< Pin 14 selected */
#define RI_Pin_15                ((uint16_t)0x8000)  /*!< Pin 15 selected */
#define RI_Pin_All               ((uint16_t)0xFFFF)  /*!< All pins selected */

#define IS_RI_PIN(PIN) ((PIN) != (uint16_t)0x00)

/**
  * @}
  */

/**
  * @}
  */

/* Exported macro ------------------------------------------------------------*/
/* Exported functions ------------------------------------------------------- */

/*  Function used to set the SYSCFG and RI configuration to the default reset state **/
void SYSCFG_DeInit(void);
void SYSCFG_RIDeInit(void);

/* SYSCFG Initialization and Configuration functions **************************/ 
void SYSCFG_MemoryRemapConfig(uint8_t SYSCFG_MemoryRemap);
uint32_t SYSCFG_GetBootMode(void);
void SYSCFG_USBPuCmd(FunctionalState NewState);
void SYSCFG_EXTILineConfig(uint8_t EXTI_PortSourceGPIOx, uint8_t EXTI_PinSourcex);

/* RI Initialization and Configuration functions ******************************/ 
void SYSCFG_RITIMSelect(uint32_t TIM_Select);
void SYSCFG_RITIMInputCaptureConfig(uint32_t RI_InputCapture, uint32_t RI_InputCaptureRouting);
void SYSCFG_RIResistorConfig(uint32_t RI_Resistor, FunctionalState NewState);
void SYSCFG_RIChannelSpeedConfig(uint32_t RI_Channel, uint32_t RI_ChannelSpeed);
void SYSCFG_RISwitchControlModeCmd(FunctionalState NewState);
void SYSCFG_RIIOSwitchConfig(uint32_t RI_IOSwitch, FunctionalState NewState);
void SYSCFG_RIHysteresisConfig(uint8_t RI_Port, uint16_t RI_Pin, FunctionalState NewState);

#ifdef __cplusplus
}
#endif

#endif /*__STM32L1xx_SYSCFG_H */

/**
  * @}
  */ 

/**
  * @}
  */ 

/************************ (C) COPYRIGHT STMicroelectronics *****END OF FILE****/
