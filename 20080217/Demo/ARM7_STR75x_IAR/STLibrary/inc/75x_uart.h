/******************** (C) COPYRIGHT 2006 STMicroelectronics ********************
* File Name          : 75x_uart.h
* Author             : MCD Application Team
* Date First Issued  : 03/10/2006
* Description        : This file contains all the functions prototypes for the
*                      UART software library.
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
#ifndef __75x_UART_H
#define __75x_UART_H

/* Includes ------------------------------------------------------------------*/
#include "75x_map.h"

/* Exported types ------------------------------------------------------------*/
/* UART FIFO Level enumeration */
typedef enum
{
  UART_FIFOLevel_1_8 = 0x0000,  /* FIFO size 16 bytes, FIFO level 2 bytes */
  UART_FIFOLevel_1_4 = 0x0001,  /* FIFO size 16 bytes, FIFO level 4 bytes */
  UART_FIFOLevel_1_2 = 0x0002,  /* FIFO size 16 bytes, FIFO level 8 bytes */
  UART_FIFOLevel_3_4 = 0x0003,  /* FIFO size 16 bytes, FIFO level 12 bytes */
  UART_FIFOLevel_7_8 = 0x0004   /* FIFO size 16 bytes, FIFO level 14 bytes */
}UART_FIFOLevel;

/* UART Init Structure definition */
typedef struct
{
  u16 UART_WordLength;
  u16 UART_StopBits;
  u16 UART_Parity;
  u32 UART_BaudRate;
  u16 UART_HardwareFlowControl;
  u16 UART_Mode;
  u16 UART_FIFO;
  UART_FIFOLevel UART_TxFIFOLevel;
  UART_FIFOLevel UART_RxFIFOLevel;
}UART_InitTypeDef;


/* UART RTS enumeration */
typedef enum
{
  RTSRESET = 1,
  RTSSET
}UART_RTSTypeDef;


/* Exported constants --------------------------------------------------------*/
/* UART Data Length */
#define UART_WordLength_5D          0x0000  /* 5 bits Data */
#define UART_WordLength_6D          0x0020  /* 6 bits Data */
#define UART_WordLength_7D          0x0040  /* 7 bits Data */
#define UART_WordLength_8D          0x0060  /* 8 bits Data */
                                                                                               
/* UART Stop Bits */
#define UART_StopBits_1             0xFFF7  /* One stop bit is transmitted at 
                                               the end of frame */
#define UART_StopBits_2             0x0008  /* Tow stop bits are transmitted 
                                               at the end of frame */

/* UART Parity */
#define UART_Parity_No              0x0000  /* Parity Disable */
#define UART_Parity_Even            0x0006  /* Even Parity */
#define UART_Parity_Odd             0x0002  /* Odd Parity */
#define UART_Parity_OddStick        0x0082  /* 1 is transmitted as bit parity */
#define UART_Parity_EvenStick       0x0086  /* 0 is transmitted as bit parity */

/* UART Hardware Flow Control */
#define UART_HardwareFlowControl_None       0x0000/* HFC Disable */
#define UART_HardwareFlowControl_RTS        0x4000/* RTS Enable */
#define UART_HardwareFlowControl_CTS        0x8000/* CTS Enable */
#define UART_HardwareFlowControl_RTS_CTS    0xC000/* CTS and RTS Enable */

/* UART Mode */
#define UART_Mode_Rx                0x0200  /* UART Rx Enabled */
#define UART_Mode_Tx                0x0100  /* UART Tx Enbled */
#define UART_Mode_Tx_Rx             0x0300  /* UART Tx and Rx Enabled */

/* UART FIFO */
#define UART_FIFO_Disable           0xFFEF  /* FIFOs Disable */
#define UART_FIFO_Enable            0x0010  /* FIFOs Enable */

/* UART Interrupt definition */
#define UART_IT_OverrunError        0x0400  /* Overrun Error interrupt */
#define UART_IT_BreakError          0x0200  /* Break Error interrupt */
#define UART_IT_ParityError         0x0100  /* Parity Error interrupt */
#define UART_IT_FrameError          0x0080  /* Frame Error interrupt */
#define UART_IT_ReceiveTimeOut      0x0040  /* Receive Time Out interrupt */
#define UART_IT_Transmit            0x0020  /* Transmit interrupt */
#define UART_IT_Receive             0x0010  /* Receive interrupt */
#define UART_IT_CTS                 0x0002  /* CTS interrupt */

/* UART0 DMA transfer */
#define UART0_DMATransfer_Single    0xFFF7  /* Single DMA transfer */
#define UART0_DMATransfer_Burst     0x0008  /* Burst DMA transfer */

/* UART0 DMA On Error */
#define UART0_DMAOnError_Enable     0xFFFB  /* DMA receive request enabled
                                                when the UART0 error interrupt
                                                is asserted. */
#define UART0_DMAOnError_Disable    0x0004  /* DMA receive request disabled
                                                when the UART0 error interrupt
                                                is asserted. */

/* UART0 DMA Request */
#define UART0_DMAReq_Tx             0x0002  /* Transmit DMA Enable */
#define UART0_DMAReq_Rx             0x0001  /* Receive DMA Enable */

/* UART FLAG */
#define UART_FLAG_OverrunError      0x23    /* Overrun error flag */
#define UART_FLAG_Break             0x22    /* break error flag */
#define UART_FLAG_ParityError       0x21    /* parity error flag */
#define UART_FLAG_FrameError        0x20    /* frame error flag */
#define UART_FLAG_TxFIFOEmpty       0x47    /* Transmit FIFO Empty flag */
#define UART_FLAG_RxFIFOFull        0x46    /* Receive FIFO Full flag */
#define UART_FLAG_TxFIFOFull        0x45    /* Transmit FIFO Full flag */
#define UART_FLAG_RxFIFOEmpty       0x44    /* Receive FIFO Empty flag */
#define UART_FLAG_Busy              0x43    /* UART Busy flag */
#define UART_FLAG_CTS               0x40    /* CTS flag */
#define UART_RawIT_OverrunError     0x6A    /* Overrun Error Masked IT flag */
#define UART_RawIT_BreakError       0x69    /* Break Error Masked IT flag */
#define UART_RawIT_ParityError      0x68    /* Parity Error Masked IT flag */
#define UART_RawIT_FrameError       0x67    /* Frame Error Masked IT flag */
#define UART_RawIT_ReceiveTimeOut   0x66    /* ReceiveTimeOut Masked IT flag */
#define UART_RawIT_Transmit         0x65    /* Transmit Masked IT flag */
#define UART_RawIT_Receive          0x64    /* Receive Masked IT flag */
#define UART_RawIT_CTS              0x61    /* CTS Masked IT flag */

/* UART LIN break length */
#define UART_LINBreakLength_10      0x0000  /* 10 low bits */
#define UART_LINBreakLength_11      0x0200  /* 11 low bits */
#define UART_LINBreakLength_12      0x0400  /* 12 low bits */
#define UART_LINBreakLength_13      0x0600  /* 13 low bits */
#define UART_LINBreakLength_14      0x0800  /* 14 low bits */
#define UART_LINBreakLength_15      0x0A00  /* 15 low bits */
#define UART_LINBreakLength_16      0x0C00  /* 16 low bits */
#define UART_LINBreakLength_17      0x0E00  /* 17 low bits */
#define UART_LINBreakLength_18      0x1000  /* 18 low bits */
#define UART_LINBreakLength_19      0x1200  /* 19 low bits */
#define UART_LINBreakLength_20      0x1400  /* 20 low bits */
/* Exported macro ------------------------------------------------------------*/
/* Exported functions ------------------------------------------------------- */

void UART_DeInit(UART_TypeDef* UARTx);
void UART_Init(UART_TypeDef* UARTx, UART_InitTypeDef* UART_InitStruct);
void UART_StructInit(UART_InitTypeDef* UART_InitStruct);
void UART_Cmd(UART_TypeDef* UARTx, FunctionalState NewState);
void UART_ITConfig(UART_TypeDef* UARTx, u16 UART_IT, FunctionalState NewState);
void UART_DMAConfig(u16 UART0_DMATransfer, u16 UART0_DMAOnError);
void UART_DMACmd(u16 UART0_DMAReq, FunctionalState NewState);
void UART_LoopBackConfig(UART_TypeDef* UARTx, FunctionalState NewState);
void UART_LINConfig(UART_TypeDef* UARTx, u16 UART_LINBreakLength);
void UART_LINCmd(UART_TypeDef* UARTx, FunctionalState NewState);
void UART_SendData(UART_TypeDef* UARTx, u8 Data);
u8 UART_ReceiveData(UART_TypeDef* UARTx);
void UART_SendBreak(UART_TypeDef* UARTx);
void UART_RTSConfig(UART_TypeDef* UARTx,UART_RTSTypeDef RTSState);
FlagStatus UART_GetFlagStatus(UART_TypeDef* UARTx, u16 UART_FLAG);
void UART_ClearFlag(UART_TypeDef* UARTx, u16 UART_FLAG);
ITStatus UART_GetITStatus(UART_TypeDef* UARTx, u16 UART_IT);
void UART_ClearITPendingBit(UART_TypeDef* UARTx, u16 UART_IT);

#endif /* __75x_UART_H */

/******************* (C) COPYRIGHT 2006 STMicroelectronics *****END OF FILE****/
