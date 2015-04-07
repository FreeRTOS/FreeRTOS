/******************** (C) COPYRIGHT 2006 STMicroelectronics ********************
* File Name          : 91x_uart.h
* Author             : MCD Application Team
* Date First Issued  : 05/18/2006 : Version 1.0
* Description        : This file contains all the functions prototypes for the
*                      UART software library.
********************************************************************************
* History:
* 05/24/2006 : Version 1.1
* 05/18/2006 : Version 1.0
********************************************************************************
* THE PRESENT SOFTWARE WHICH IS FOR GUIDANCE ONLY AIMS AT PROVIDING CUSTOMERS
* WITH CODING INFORMATION REGARDING THEIR PRODUCTS IN ORDER FOR THEM TO SAVE TIME.
* AS A RESULT, STMICROELECTRONICS SHALL NOT BE HELD LIABLE FOR ANY DIRECT,
* INDIRECT OR CONSEQUENTIAL DAMAGES WITH RESPECT TO ANY CLAIMS ARISING FROM THE
* CONTENT OF SUCH SOFTWARE AND/OR THE USE MADE BY CUSTOMERS OF THE CODING
* INFORMATION CONTAINED HEREIN IN CONNECTION WITH THEIR PRODUCTS.
*******************************************************************************/

/* Define to prevent recursive inclusion -------------------------------------*/
#ifndef __91x_UART_H
#define __91x_UART_H

/* Includes ------------------------------------------------------------------*/
#include <91x_map.h>

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
  LowLevel = 0,
  HighLevel
}UART_LevelTypeDef;

/* Exported constants --------------------------------------------------------*/
/* UART Data Length */
#define UART_WordLength_5D	      0x0000  /* 5 bits Data */
#define UART_WordLength_6D	      0x0020  /* 6 bits Data */
#define UART_WordLength_7D	      0x0040  /* 7 bits Data */
#define UART_WordLength_8D	      0x0060  /* 8 bits Data */

/* UART Stop Bits */
#define UART_StopBits_1         0xFFF7  /* Disable two stop bit is transmitted
                                                 at the end of frame */
#define UART_StopBits_2         0x0008  /* Enable Two stop bits are transmitted
                                                 at the end of frame */
/* UART Parity */
#define UART_Parity_No	              0x0000  /* Parity Disable */
#define UART_Parity_Even	      0x0006  /* Even Parity */
#define UART_Parity_Odd	              0x0002  /* Odd Parity */
#define UART_Parity_OddStick	      0x0082  /* 1 is transmitted as bit parity */
#define UART_Parity_EvenStick	      0x0086  /* 0 is transmitted as bit parity */

/* UART Hardware Flow Control */
#define UART_HardwareFlowControl_None	   0x0000  /* HFC Disable */
#define UART_HardwareFlowControl_RTS	   0x4000  /* RTS Enable */
#define UART_HardwareFlowControl_CTS	   0x8000  /* CTS Enable */
#define UART_HardwareFlowControl_RTS_CTS   0xC000  /* CTS and RTS Enable */

/* UART Mode */
#define UART_Mode_Rx                  0x0200  /* UART Rx Enabled */
#define UART_Mode_Tx                  0x0100  /* UART Tx Enbled */
#define UART_Mode_Tx_Rx               0x0300  /* UART Tx and Rx Enabled */

/* UART FIFO */
#define UART_FIFO_Disable           0xFFEF  /* FIFOs Disable */
#define UART_FIFO_Enable            0x0010  /* FIFOs Enable */

/* UART Interrupt definition */
#define UART_IT_OverrunError	      0x0400  /* Overrun Error interrupt mask */
#define UART_IT_BreakError	      0x0200  /* Break Error interrupt mask */
#define UART_IT_ParityError	      0x0100  /* Parity Error interrupt mask */
#define UART_IT_FrameError	      0x0080  /* Frame Error interrupt mask */
#define UART_IT_ReceiveTimeOut	      0x0040  /* Receive Time Out interrupt mask */
#define UART_IT_Transmit              0x0020  /* Transmit interrupt mask */
#define UART_IT_Receive	              0x0010  /* Receive interrupt mask */
#define UART_IT_DSR	              0x0008  /* DSR interrupt mask */
#define UART_IT_DCD	              0x0004  /* DCD interrupt mask */
#define UART_IT_CTS	              0x0002  /* CTS interrupt mask */
#define UART_IT_RI	              0x0001  /* RI interrupt mask */

/* UART DMA On Error */
#define UART_DMAOnError_Enable	      0xFFFB  /* DMA receive request enabled
                                                 when the UART error interrupt
                                                 is asserted. */
#define UART_DMAOnError_Disable	      0x0004  /* DMA receive request disabled
                                                 when the UART error interrupt
                                                 is asserted. */
/* UART DMA Request */
#define UART_DMAReq_Tx	              0x02      /* Transmit DMA Enable */
#define UART_DMAReq_Rx	              0x01      /* Receive DMA Enable */

/* UART FLAG */
#define UART_FLAG_OverrunError	      0x23    /* Overrun error flag */
#define UART_FLAG_Break	              0x22    /* break error flag */
#define UART_FLAG_ParityError	      0x21    /* parity error flag */
#define UART_FLAG_FrameError	      0x20    /* frame error flag */
#define UART_FLAG_RI	              0x48    /* RI flag */
#define UART_FLAG_TxFIFOEmpty	      0x47    /* Transmit FIFO Empty flag */
#define UART_FLAG_RxFIFOFull	      0x46    /* Receive FIFO Full flag */
#define UART_FLAG_TxFIFOFull	      0x45    /* Transmit FIFO Full flag */
#define UART_FLAG_RxFIFOEmpty	      0x44    /* Receive FIFO Empty flag */
#define UART_FLAG_Busy	              0x43    /* UART Busy flag */
#define UART_FLAG_DCD	              0x42    /* DCD flag */
#define UART_FLAG_DSR	              0x41    /* DSR flag */
#define UART_FLAG_CTS	              0x40    /* CTS flag */
#define UART_RawIT_OverrunError       0x6A    /* Overrun Error Raw IT flag */
#define UART_RawIT_BreakError         0x69    /* Break Error Raw IT flag */
#define UART_RawIT_ParityError        0x68    /* Parity Error Raw IT flag */
#define UART_RawIT_FrameError         0x67    /* Frame Error Raw IT flag */
#define UART_RawIT_ReceiveTimeOut     0x66    /* ReceiveTimeOut Raw IT flag */
#define UART_RawIT_Transmit	      0x65    /* Transmit Raw IT flag */
#define UART_RawIT_Receive	      0x64    /* Receive Raw IT flag */
#define UART_RawIT_DSR	              0x63    /* DSR Raw IT flag */
#define UART_RawIT_DCD	              0x62    /* DCD Raw IT flag */
#define UART_RawIT_CTS	              0x61    /* CTS Raw IT flag */
#define UART_RawIT_RI	              0x60    /* RI Raw IT flag */

/*IrDAx select*/
#define IrDA0 0x01                             /*IrDA0 select*/
#define IrDA1 0x02                             /*IrDA0 select*/
#define IrDA2 0x03                             /*IrDA0 select*/

/* Exported macro ------------------------------------------------------------*/
/* Exported functions ------------------------------------------------------- */
void UART_DeInit(UART_TypeDef* UARTx);
void UART_Init(UART_TypeDef* UARTx, UART_InitTypeDef* UART_InitStruct);
void UART_StructInit(UART_InitTypeDef* UART_InitStruct);
void UART_Cmd(UART_TypeDef* UARTx, FunctionalState NewState);
void UART_ITConfig(UART_TypeDef* UARTx, u16 UART_IT, FunctionalState NewState);
void UART_DMAConfig(UART_TypeDef* UARTx, u16 UART_DMAOnError);
void UART_DMACmd(UART_TypeDef* UARTx, u8 UART_DMAReq, FunctionalState NewState);
void UART_LoopBackConfig(UART_TypeDef* UARTx, FunctionalState NewState);
FlagStatus UART_GetFlagStatus(UART_TypeDef* UARTx, u16 UART_FLAG);
void UART_ClearFlag(UART_TypeDef* UARTx);
void UART_ClearITPendingBit(UART_TypeDef* UARTx, u16 UART_IT);
void UART_IrDALowPowerConfig(u8 IrDAx, FunctionalState NewState);
void UART_IrDACmd(u8 IrDAx, FunctionalState NewState);
void UART_IrDASetCounter(u8 IrDAx, u32 IrDA_Counter);
void UART_SendData(UART_TypeDef* UARTx, u8 Data);
u8 UART_ReceiveData(UART_TypeDef* UARTx);
void UART_SendBreak(UART_TypeDef* UARTx);
void UART_DTRConfig(UART_LevelTypeDef LevelState);
void UART_RTSConfig(UART_LevelTypeDef LevelState);
ITStatus UART_GetITStatus(UART_TypeDef* UARTx, u16 UART_IT);

#endif /* __91x_UART_H */

/******************* (C) COPYRIGHT 2006 STMicroelectronics *****END OF FILE****/
