/******************** (C) COPYRIGHT 2006 STMicroelectronics ********************
* File Name          : 75x_dma.h
* Author             : MCD Application Team
* Date First Issued  : 03/10/2006 
* Description        : This file contains all the functions prototypes for the
*                      DMA software library.
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

/* Define to prevent recursive inclusion ------------------------------------ */
#ifndef __75x_DMA_H
#define __75x_DMA_H

/* Includes ------------------------------------------------------------------*/
#include "75x_map.h"

/* Exported types ------------------------------------------------------------*/
/* DMA Init structure definition */
typedef struct
{
  u32 DMA_SRCBaseAddr;
  u32 DMA_DSTBaseAddr;	
  u16 DMA_BufferSize;	
  u16 DMA_SRC;   
  u16 DMA_DST; 
  u16 DMA_SRCSize;
  u16 DMA_SRCBurst;
  u16 DMA_DSTSize;
  u16 DMA_Mode;  
  u16 DMA_M2M; 
  u16 DMA_DIR; 
}DMA_InitTypeDef;

/* Exported constants --------------------------------------------------------*/
/* DMA interrupt Mask */
#define DMA_IT_SI0    0x0001
#define DMA_IT_SI1    0x0002
#define DMA_IT_SI2    0x0004
#define DMA_IT_SI3    0x0008
#define DMA_IT_SE0    0x0010
#define DMA_IT_SE1    0x0020
#define DMA_IT_SE2    0x0040
#define DMA_IT_SE3    0x0080
#define DMA_IT_ALL    0x00FF

/* DMA Flags */
#define DMA_FLAG_SI0     0x0001
#define DMA_FLAG_SI1     0x0002
#define DMA_FLAG_SI2     0x0004
#define DMA_FLAG_SI3     0x0008
#define DMA_FLAG_SE0     0x0010
#define DMA_FLAG_SE1     0x0020
#define DMA_FLAG_SE2     0x0040
#define DMA_FLAG_SE3     0x0080
#define DMA_FLAG_ACT0    0x0100
#define DMA_FLAG_ACT1    0x0200
#define DMA_FLAG_ACT2    0x0400
#define DMA_FLAG_ACT3    0x0800

/* DMA Increment Current Source Register */
#define DMA_SRC_INCR        0x0002
#define DMA_SRC_NOT_INCR    0xFFFD

/* DMA Increment Current Destination Register */
#define DMA_DST_INCR        0x0004
#define DMA_DST_NOT_INCR    0xFFFB

/* Source to DMA data width */
#define DMA_SRCSize_Byte        0x0000
#define DMA_SRCSize_HalfWord    0x0008
#define DMA_SRCSize_Word        0x0010

/* DMA source burst size */
#define DMA_SRCBurst_1Data     0x0000
#define DMA_SRCBurst_4Data     0x0020
#define DMA_SRCBurst_8Data     0x0040
#define DMA_SRCBurst_16Data    0x0060

/* DMA destination data width */
#define DMA_DSTSize_Byte        0x0000
#define DMA_DSTSize_HalfWord    0x0080
#define DMA_DSTSize_Word        0x0100

/* DMA mode */
#define DMA_Mode_Circular    0x0200
#define DMA_Mode_Normal      0xFDFF

/* Memory to Memory Transfer */
#define DMA_M2M_Enable     0x0800
#define DMA_M2M_Disable    0xF7FF

/* Direction Transfer */
#define DMA_DIR_PeriphDST    0x2000
#define DMA_DIR_PeriphSRC    0xDFFF

/* DMA streamx Registers */
#define DMA_SOURCEL   0x00000000  /* source base address low register */
#define DMA_SOURCEH   0x00000004  /* source base address high register */
#define DMA_DESTL     0x00000008  /* destination base address low register */
#define DMA_DESTH     0x0000000C  /* destination base address high register */
#define DMA_MAX       0x00000010  /* Maximum count register */
#define DMA_CTRL      0x00000014  /* Control register */
#define DMA_SOCURRH   0x00000018  /* Current Source address high register */
#define DMA_SOCURRL   0x0000001C  /* Current Source address low register */
#define DMA_DECURRH   0x00000020  /* Current Destination address high register */
#define DMA_DECURRL   0x00000024  /* Current Destination address low register */
#define DMA_TCNT      0x00000028  /* Terminal Counter Register */
#define DMA_LUBUFF    0x0000002C  /* Last Used Buffer location */

/* Exported macro ------------------------------------------------------------*/
/* Exported functions ------------------------------------------------------- */

void DMA_DeInit(DMA_Stream_TypeDef* DMA_Streamx);
void DMA_Init(DMA_Stream_TypeDef* DMA_Streamx, DMA_InitTypeDef* DMA_InitStruct);
void DMA_StructInit(DMA_InitTypeDef* DMA_InitStruct);
void DMA_Cmd(DMA_Stream_TypeDef* DMA_Streamx, FunctionalState NewState);
void DMA_ITConfig(u16 DMA_IT, FunctionalState NewState);
u32 DMA_GetCurrDSTAddr(DMA_Stream_TypeDef* DMA_Streamx);
u32 DMA_GetCurrSRCAddr(DMA_Stream_TypeDef* DMA_Streamx);
u16 DMA_GetTerminalCounter(DMA_Stream_TypeDef* DMA_Streamx);
void DMA_LastBufferSweepConfig(DMA_Stream_TypeDef* DMA_Streamx, FunctionalState NewState);
void DMA_LastBufferAddrConfig(DMA_Stream_TypeDef* DMA_Streamx, u16 DMA_LastBufferAddr);
FlagStatus DMA_GetFlagStatus(u16 DMA_FLAG);
void DMA_ClearFlag(u16 DMA_FLAG);
ITStatus DMA_GetITStatus(u16 DMA_IT);
void DMA_ClearITPendingBit(u16 DMA_IT);

#endif /* __75x_DMA_H */

/******************* (C) COPYRIGHT 2006 STMicroelectronics *****END OF FILE****/
