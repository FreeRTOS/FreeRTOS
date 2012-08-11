/******************** (C) COPYRIGHT 2007 STMicroelectronics ********************
* File Name          : stm32f10x_dma.h
* Author             : MCD Application Team
* Date First Issued  : 09/29/2006
* Description        : This file contains all the functions prototypes for the
*                      DMA firmware library.
********************************************************************************
* History:
* 04/02/2007: V0.2
* 02/05/2007: V0.1
* 09/29/2006: V0.01
********************************************************************************
* THE PRESENT SOFTWARE WHICH IS FOR GUIDANCE ONLY AIMS AT PROVIDING CUSTOMERS
* WITH CODING INFORMATION REGARDING THEIR PRODUCTS IN ORDER FOR THEM TO SAVE TIME.
* AS A RESULT, STMICROELECTRONICS SHALL NOT BE HELD LIABLE FOR ANY DIRECT,
* INDIRECT OR CONSEQUENTIAL DAMAGES WITH RESPECT TO ANY CLAIMS ARISING FROM THE
* CONTENT OF SUCH SOFTWARE AND/OR THE USE MADE BY CUSTOMERS OF THE CODING
* INFORMATION CONTAINED HEREIN IN CONNECTION WITH THEIR PRODUCTS.
*******************************************************************************/

/* Define to prevent recursive inclusion -------------------------------------*/
#ifndef __STM32F10x_DMA_H
#define __STM32F10x_DMA_H

/* Includes ------------------------------------------------------------------*/
#include "stm32f10x_map.h"

/* Exported types ------------------------------------------------------------*/
/* DMA Init structure definition */
typedef struct
{
  u32 DMA_PeripheralBaseAddr;
  u32 DMA_MemoryBaseAddr;	
  u32 DMA_DIR;	
  u32 DMA_BufferSize;   
  u32 DMA_PeripheralInc; 
  u32 DMA_MemoryInc;
  u32 DMA_PeripheralDataSize;
  u32 DMA_MemoryDataSize;
  u32 DMA_Mode;  
  u32 DMA_Priority; 
  u32 DMA_M2M; 
}DMA_InitTypeDef;

/* Exported constants --------------------------------------------------------*/
/* DMA data transfer direction -----------------------------------------------*/
#define DMA_DIR_PeripheralDST              ((u32)0x00000010)
#define DMA_DIR_PeripheralSRC              ((u32)0x00000000)

#define IS_DMA_DIR(DIR) ((DIR == DMA_DIR_PeripheralDST) || \
                         (DIR == DMA_DIR_PeripheralSRC))

/* DMA peripheral incremented mode -------------------------------------------*/
#define DMA_PeripheralInc_Enable           ((u32)0x00000040)
#define DMA_PeripheralInc_Disable          ((u32)0x00000000)

#define IS_DMA_PERIPHERAL_INC_STATE(STATE) ((STATE == DMA_PeripheralInc_Enable) || \
                                            (STATE == DMA_PeripheralInc_Disable))

/* DMA memory incremented mode -----------------------------------------------*/
#define DMA_MemoryInc_Enable               ((u32)0x00000080)
#define DMA_MemoryInc_Disable              ((u32)0x00000000)

#define IS_DMA_MEMORY_INC_STATE(STATE) ((STATE == DMA_MemoryInc_Enable) || \
                                        (STATE == DMA_MemoryInc_Disable))

/* DMA peripheral data size --------------------------------------------------*/
#define DMA_PeripheralDataSize_Byte        ((u32)0x00000000)
#define DMA_PeripheralDataSize_HalfWord    ((u32)0x00000100)
#define DMA_PeripheralDataSize_Word        ((u32)0x00000200)

#define IS_DMA_PERIPHERAL_DATA_SIZE(SIZE) ((SIZE == DMA_PeripheralDataSize_Byte) || \
                                           (SIZE == DMA_PeripheralDataSize_HalfWord) || \
                                           (SIZE == DMA_PeripheralDataSize_Word))

/* DMA memory data size ------------------------------------------------------*/
#define DMA_MemoryDataSize_Byte            ((u32)0x00000000)
#define DMA_MemoryDataSize_HalfWord        ((u32)0x00000400)
#define DMA_MemoryDataSize_Word            ((u32)0x00000800)

#define IS_DMA_MEMORY_DATA_SIZE(SIZE) ((SIZE == DMA_MemoryDataSize_Byte) || \
                                       (SIZE == DMA_MemoryDataSize_HalfWord) || \
                                       (SIZE == DMA_MemoryDataSize_Word))

/* DMA circular/normal mode --------------------------------------------------*/
#define DMA_Mode_Circular                  ((u32)0x00000020)
#define DMA_Mode_Normal                    ((u32)0x00000000)

#define IS_DMA_MODE(MODE) ((MODE == DMA_Mode_Circular) || (MODE == DMA_Mode_Normal))

/* DMA priority level --------------------------------------------------------*/
#define DMA_Priority_VeryHigh              ((u32)0x00003000)
#define DMA_Priority_High                  ((u32)0x00002000)
#define DMA_Priority_Medium                ((u32)0x00001000)
#define DMA_Priority_Low                   ((u32)0x00000000)

#define IS_DMA_PRIORITY(PRIORITY) ((PRIORITY == DMA_Priority_VeryHigh) || \
                                   (PRIORITY == DMA_Priority_High) || \
                                   (PRIORITY == DMA_Priority_Medium) || \
                                   (PRIORITY == DMA_Priority_Low))

/* DMA memory to memory ------------------------------------------------------*/
#define DMA_M2M_Enable                     ((u32)0x00004000)
#define DMA_M2M_Disable                    ((u32)0x00000000)

#define IS_DMA_M2M_STATE(STATE) ((STATE == DMA_M2M_Enable) || (STATE == DMA_M2M_Disable))

/* DMA interrupts definition -------------------------------------------------*/
#define DMA_IT_TC                          ((u32)0x00000002)
#define DMA_IT_HT                          ((u32)0x00000004)
#define DMA_IT_TE                          ((u32)0x00000008)

#define IS_DMA_CONFIG_IT(IT) (((IT & 0xFFFFFFF1) == 0x00) && (IT != 0x00))

#define DMA_IT_GL1                         ((u32)0x00000001)
#define DMA_IT_TC1                         ((u32)0x00000002)
#define DMA_IT_HT1                         ((u32)0x00000004)
#define DMA_IT_TE1                         ((u32)0x00000008)
#define DMA_IT_GL2                         ((u32)0x00000010)
#define DMA_IT_TC2                         ((u32)0x00000020)
#define DMA_IT_HT2                         ((u32)0x00000040)
#define DMA_IT_TE2                         ((u32)0x00000080)
#define DMA_IT_GL3                         ((u32)0x00000100)
#define DMA_IT_TC3                         ((u32)0x00000200)
#define DMA_IT_HT3                         ((u32)0x00000400)
#define DMA_IT_TE3                         ((u32)0x00000800)
#define DMA_IT_GL4                         ((u32)0x00001000)
#define DMA_IT_TC4                         ((u32)0x00002000)
#define DMA_IT_HT4                         ((u32)0x00004000)
#define DMA_IT_TE4                         ((u32)0x00008000)
#define DMA_IT_GL5                         ((u32)0x00010000)
#define DMA_IT_TC5                         ((u32)0x00020000)
#define DMA_IT_HT5                         ((u32)0x00040000)
#define DMA_IT_TE5                         ((u32)0x00080000)
#define DMA_IT_GL6                         ((u32)0x00100000)
#define DMA_IT_TC6                         ((u32)0x00200000)
#define DMA_IT_HT6                         ((u32)0x00400000)
#define DMA_IT_TE6                         ((u32)0x00800000)
#define DMA_IT_GL7                         ((u32)0x01000000)
#define DMA_IT_TC7                         ((u32)0x02000000)
#define DMA_IT_HT7                         ((u32)0x04000000)
#define DMA_IT_TE7                         ((u32)0x08000000)

#define IS_DMA_CLEAR_IT(IT) (((IT & 0xF0000000) == 0x00) && (IT != 0x00))
#define IS_DMA_GET_IT(IT) ((IT == DMA_IT_GL1) || (IT == DMA_IT_TC1) || \
                           (IT == DMA_IT_HT1) || (IT == DMA_IT_TE1) || \
                           (IT == DMA_IT_GL2) || (IT == DMA_IT_TC2) || \
                           (IT == DMA_IT_HT2) || (IT == DMA_IT_TE2) || \
                           (IT == DMA_IT_GL3) || (IT == DMA_IT_TC3) || \
                           (IT == DMA_IT_HT3) || (IT == DMA_IT_TE3) || \
                           (IT == DMA_IT_GL4) || (IT == DMA_IT_TC4) || \
                           (IT == DMA_IT_HT4) || (IT == DMA_IT_TE4) || \
                           (IT == DMA_IT_GL5) || (IT == DMA_IT_TC5) || \
                           (IT == DMA_IT_HT5) || (IT == DMA_IT_TE5) || \
                           (IT == DMA_IT_GL6) || (IT == DMA_IT_TC6) || \
                           (IT == DMA_IT_HT6) || (IT == DMA_IT_TE6) || \
                           (IT == DMA_IT_GL7) || (IT == DMA_IT_TC7) || \
                           (IT == DMA_IT_HT7) || (IT == DMA_IT_TE7))

/* DMA flags definition ------------------------------------------------------*/
#define DMA_FLAG_GL1                       ((u32)0x00000001)
#define DMA_FLAG_TC1                       ((u32)0x00000002)
#define DMA_FLAG_HT1                       ((u32)0x00000004)
#define DMA_FLAG_TE1                       ((u32)0x00000008)
#define DMA_FLAG_GL2                       ((u32)0x00000010)
#define DMA_FLAG_TC2                       ((u32)0x00000020)
#define DMA_FLAG_HT2                       ((u32)0x00000040)
#define DMA_FLAG_TE2                       ((u32)0x00000080)
#define DMA_FLAG_GL3                       ((u32)0x00000100)
#define DMA_FLAG_TC3                       ((u32)0x00000200)
#define DMA_FLAG_HT3                       ((u32)0x00000400)
#define DMA_FLAG_TE3                       ((u32)0x00000800)
#define DMA_FLAG_GL4                       ((u32)0x00001000)
#define DMA_FLAG_TC4                       ((u32)0x00002000)
#define DMA_FLAG_HT4                       ((u32)0x00004000)
#define DMA_FLAG_TE4                       ((u32)0x00008000)
#define DMA_FLAG_GL5                       ((u32)0x00010000)
#define DMA_FLAG_TC5                       ((u32)0x00020000)
#define DMA_FLAG_HT5                       ((u32)0x00040000)
#define DMA_FLAG_TE5                       ((u32)0x00080000)
#define DMA_FLAG_GL6                       ((u32)0x00100000)
#define DMA_FLAG_TC6                       ((u32)0x00200000)
#define DMA_FLAG_HT6                       ((u32)0x00400000)
#define DMA_FLAG_TE6                       ((u32)0x00800000)
#define DMA_FLAG_GL7                       ((u32)0x01000000)
#define DMA_FLAG_TC7                       ((u32)0x02000000)
#define DMA_FLAG_HT7                       ((u32)0x04000000)
#define DMA_FLAG_TE7                       ((u32)0x08000000)

#define IS_DMA_CLEAR_FLAG(FLAG) (((FLAG & 0xF0000000) == 0x00) && (FLAG != 0x00))
#define IS_DMA_GET_FLAG(FLAG) ((FLAG == DMA_FLAG_GL1) || (FLAG == DMA_FLAG_TC1) || \
                               (FLAG == DMA_FLAG_HT1) || (FLAG == DMA_FLAG_TE1) || \
                               (FLAG == DMA_FLAG_GL2) || (FLAG == DMA_FLAG_TC2) || \
                               (FLAG == DMA_FLAG_HT2) || (FLAG == DMA_FLAG_TE2) || \
                               (FLAG == DMA_FLAG_GL3) || (FLAG == DMA_FLAG_TC3) || \
                               (FLAG == DMA_FLAG_HT3) || (FLAG == DMA_FLAG_TE3) || \
                               (FLAG == DMA_FLAG_GL4) || (FLAG == DMA_FLAG_TC4) || \
                               (FLAG == DMA_FLAG_HT4) || (FLAG == DMA_FLAG_TE4) || \
                               (FLAG == DMA_FLAG_GL5) || (FLAG == DMA_FLAG_TC5) || \
                               (FLAG == DMA_FLAG_HT5) || (FLAG == DMA_FLAG_TE5) || \
                               (FLAG == DMA_FLAG_GL6) || (FLAG == DMA_FLAG_TC6) || \
                               (FLAG == DMA_FLAG_HT6) || (FLAG == DMA_FLAG_TE6) || \
                               (FLAG == DMA_FLAG_GL7) || (FLAG == DMA_FLAG_TC7) || \
                               (FLAG == DMA_FLAG_HT7) || (FLAG == DMA_FLAG_TE7))

/* DMA Buffer Size -----------------------------------------------------------*/
#define IS_DMA_BUFFER_SIZE(SIZE) ((SIZE >= 0x1) && (SIZE < 0x10000))

/* Exported macro ------------------------------------------------------------*/
/* Exported functions ------------------------------------------------------- */
void DMA_DeInit(DMA_Channel_TypeDef* DMA_Channelx);
void DMA_Init(DMA_Channel_TypeDef*  DMA_Channelx, DMA_InitTypeDef* DMA_InitStruct);
void DMA_StructInit(DMA_InitTypeDef* DMA_InitStruct);
void DMA_Cmd(DMA_Channel_TypeDef*  DMA_Channelx, FunctionalState NewState);
void DMA_ITConfig(DMA_Channel_TypeDef*  DMA_Channelx, u32 DMA_IT, FunctionalState NewState);
u16 DMA_GetCurrDataCounter(DMA_Channel_TypeDef*  DMA_Channelx);
FlagStatus DMA_GetFlagStatus(u32 DMA_FLAG);
void DMA_ClearFlag(u32 DMA_FLAG);
ITStatus DMA_GetITStatus(u32 DMA_IT);
void DMA_ClearITPendingBit(u32 DMA_IT);

#endif /*__STM32F10x_DMA_H */

/******************* (C) COPYRIGHT 2007 STMicroelectronics *****END OF FILE****/
