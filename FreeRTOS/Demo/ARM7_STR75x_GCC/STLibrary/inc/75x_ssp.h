/******************** (C) COPYRIGHT 2006 STMicroelectronics ********************
* File Name          : 75x_SSP.h
* Author             : MCD Application Team
* Date First Issued  : 03/10/2006
* Description        : This file contains all the functions prototypes for the
*                      SSP software library.
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
#ifndef __75x_SSP_H
#define __75x_SSP_H

/* Includes ------------------------------------------------------------------*/
#include "75x_map.h"

/* Exported types ------------------------------------------------------------*/
/* SSP Init structure definition */
typedef struct
{
  u16 SSP_FrameFormat;
  u16 SSP_Mode;
  u16 SSP_CPOL;
  u16 SSP_CPHA;
  u16 SSP_DataSize;
  u16 SSP_NSS;
  u16 SSP_SlaveOutput;
  u8 SSP_ClockRate;
  u8 SSP_ClockPrescaler;
}SSP_InitTypeDef;

/* Exported constants --------------------------------------------------------*/
/* SSP Frame Format Select */
#define SSP_FrameFormat_TI          0x0010
#define SSP_FrameFormat_Motorola    0xFFCF

/* SSP Master/Slave Select */
#define SSP_Mode_Master    0xFFFB
#define SSP_Mode_Slave     0x0004

/* SSP Clock Polarity */
#define SSP_CPOL_Low     0xFFBF
#define SSP_CPOL_High    0x0040

/* SSP Clock Phase */
#define SSP_CPHA_1Edge    0xFF7F
#define SSP_CPHA_2Edge    0x0080

/* SSP Data Size */
#define SSP_DataSize_16b    0x000F
#define SSP_DataSize_15b    0x000E
#define SSP_DataSize_14b    0x000D
#define SSP_DataSize_13b    0x000C
#define SSP_DataSize_12b    0x000B
#define SSP_DataSize_11b    0x000A
#define SSP_DataSize_10b    0x0009
#define SSP_DataSize_9b     0x0008
#define SSP_DataSize_8b     0x0007
#define SSP_DataSize_7b     0x0006
#define SSP_DataSize_6b     0x0005
#define SSP_DataSize_5b     0x0004
#define SSP_DataSize_4b     0x0003

/* SSP Slave Select management config */
#define SSP_NSS_Hard    0xFFEF
#define SSP_NSS_Soft    0x0010

/* SSP NSS internal config */
#define SSP_NSSInternal_Set      0x0020
#define SSP_NSSInternal_Reset    0xFFDF

/* SSP Slave output config */
#define SSP_SlaveOutput_Enable     0xFFF7
#define SSP_SlaveOutput_Disable    0x0008

/* SSP Interrupts */
#define SSP_IT_TxFifo       0x0008
#define SSP_IT_RxFifo       0x0004
#define SSP_IT_RxTimeOut    0x0002
#define SSP_IT_RxOverrun    0x0001

/* SSP Flags */
#define SSP_FLAG_Busy              0x0024
#define SSP_FLAG_RxFifoFull        0x0023
#define SSP_FLAG_RxFifoNotEmpty    0x0022
#define SSP_FLAG_TxFifoNotFull     0x0021
#define SSP_FLAG_TxFifoEmpty       0x0020
#define SSP_FLAG_TxFifo            0x0043
#define SSP_FLAG_RxFifo            0x0042
#define SSP_FLAG_RxTimeOut         0x0041
#define SSP_FLAG_RxOverrun         0x0040

/* SSP DMA Requests */
#define SSP0_DMA_Transmit    0x0002
#define SSP0_DMA_Receive     0x0001

#define SSP0_DMATxReq_Single     0xFFF7
#define SSP0_DMATxReq_Burst      0x0008

#define SSP0_DMARxReq_Single     0xFFFB
#define SSP0_DMARxReq_Burst      0x0004

/* Exported macro ------------------------------------------------------------*/
/* Exported functions ------------------------------------------------------- */

void SSP_DeInit(SSP_TypeDef* SSPx);
void SSP_Init(SSP_TypeDef* SSPx, SSP_InitTypeDef* SSP_InitStruct);
void SSP_StructInit(SSP_InitTypeDef* SSP_InitStruct);
void SSP_Cmd(SSP_TypeDef* SSPx, FunctionalState NewState);
void SSP_ITConfig(SSP_TypeDef* SSPx, u16 SSP_IT, FunctionalState NewState);
void SSP_DMACmd(u16 SSP0_DMAtransfer, FunctionalState NewState);
void SSP_DMATxConfig(u16 SSP0_DMATxReq);
void SSP_DMARxConfig(u16 SSP0_DMARxReq);
void SSP_SendData(SSP_TypeDef* SSPx, u16 Data);
u16 SSP_ReceiveData(SSP_TypeDef* SSPx);
void SSP_LoopBackConfig(SSP_TypeDef* SSPx, FunctionalState NewState);
void SSP_NSSInternalConfig(SSP_TypeDef* SSPx, u16 SSP_NSSState);
FlagStatus SSP_GetFlagStatus(SSP_TypeDef* SSPx, u16 SSP_FLAG);
void SSP_ClearFlag(SSP_TypeDef* SSPx, u16 SSP_FLAG);
ITStatus SSP_GetITStatus(SSP_TypeDef* SSPx, u16 SSP_IT);
void SSP_ClearITPendingBit(SSP_TypeDef* SSPx, u16 SSP_IT);

#endif /* __75x_SSP_H */

/******************* (C) COPYRIGHT 2006 STMicroelectronics *****END OF FILE****/
