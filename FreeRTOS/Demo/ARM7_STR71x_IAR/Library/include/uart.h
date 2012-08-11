/******************** (C) COPYRIGHT 2003 STMicroelectronics ********************
* File Name          : uart.h
* Author             : MCD Application Team
* Date First Issued  : 16/05/2003
* Description        : This file contains all the functions prototypes for the
*                      UART software library.
********************************************************************************
* History:
*  30/11/2004 : V2.0
*  14/07/2004 : V1.3
*  01/01/2004 : V1.2
*******************************************************************************
 THE PRESENT SOFTWARE WHICH IS FOR GUIDANCE ONLY AIMS AT PROVIDING CUSTOMERS WITH
 CODING INFORMATION REGARDING THEIR PRODUCTS IN ORDER FOR THEM TO SAVE TIME.
 AS A RESULT, STMICROELECTRONICS SHALL NOT BE HELD LIABLE FOR ANY DIRECT, INDIRECT
 OR CONSEQUENTIAL DAMAGES WITH RESPECT TO ANY CLAIMS ARISING FROM THE CONTENT
 OF SUCH SOFTWARE AND/OR THE USE MADE BY CUSTOMERS OF THE CODING INFORMATION
 CONTAINED HEREIN IN CONNECTION WITH THEIR PRODUCTS.
*******************************************************************************/
#ifndef _UART_H
#define _UART_H

#include "71x_map.h"
#include "rccu.h"

typedef enum
{
  UART_RxFIFO,
  UART_TxFIFO
} UARTFIFO_TypeDef;

typedef enum
{
  UART_EVEN_PARITY = 0x0000,
  UART_ODD_PARITY  = 0x0020,
  UART_NO_PARITY
} UARTParity_TypeDef;

typedef enum
{
  UART_0_5_StopBits  = 0x00,
  UART_1_StopBits    = 0x08,
  UART_1_5_StopBits  = 0x10,
  UART_2_StopBits    = 0x18
} UARTStopBits_TypeDef;

typedef enum
{
  UARTM_8D   = 0x01,
  UARTM_7D_P = 0x03,
  UARTM_9D   = 0x04,
  UARTM_8D_W = 0x05,
  UARTM_8D_P = 0x07
} UARTMode_TypeDef;


#define DUMMY 0

// UART flags definition
#define UART_TxFull          0x0200
#define UART_RxHalfFull      0x0100
#define UART_TimeOutIdle     0x0080
#define UART_TimeOutNotEmpty 0x0040
#define UART_OverrunError    0x0020
#define UART_FrameError      0x0010
#define UART_ParityError     0x0008
#define UART_TxHalfEmpty     0x0004
#define UART_TxEmpty         0x0002
#define UART_RxBufFull       0x0001

// CR regiter bit definition
#define UART_FIFOEnableBit 10
#define UART_RxEnableBit   8
#define UART_RunBit        7
#define UART_LoopBackBit   6
#define UART_ParityOddBit  5
#define UART_StopBits      3

// Stop bits definition
#define UART_05StopBits     0x00
#define UART_1StopBit       (0x01<<3)
#define UART_15StopBits     (0x02<<3)
#define UART_2StopBits      (0x03<<3)

// Modes definition
#define UART_8BitsData       0x01
#define UART_7BitsData       0x03
#define UART_9BitsData       0x04
#define UART_8BitsDataWakeUp 0x05
#define UART_8BitsDataParity 0x07

/*******************************************************************************
* Function Name  : UART_Init
* Description    : This function initializes the selected UART.
* Input 1        : UARTx (x can be 0,1, 2 or 3) the desired UART
* Output         : None
* Return         : None
*******************************************************************************/
void UART_Init(UART_TypeDef *UARTx);

/*******************************************************************************
* Function Name  : UART_ModeConfig
* Description    : This function configures the mode of the selected UART.
* Input 1        : UARTx (x can be 0,1, 2 or 3) the desired UART
* Input 2        : The UART mode
* Output         : None
* Return         : None
*******************************************************************************/
inline void UART_ModeConfig(UART_TypeDef *UARTx, UARTMode_TypeDef UART_Mode)
{
  UARTx->CR = (UARTx->CR&0xFFF8)|(u16)UART_Mode;
}

/*******************************************************************************
* Function Name  : UART_BaudRateConfig
* Description    : This function configures the baud rate of the selected UART.
* Input 1        : UARTx (x can be 0,1, 2 or 3) the desired UART
* Input 2        : The baudrate value
* Output         : None
* Return         : None
*******************************************************************************/
void UART_BaudRateConfig(UART_TypeDef *UARTx, u32 BaudRate);

/*******************************************************************************
* Function Name  : UART_ParityConfig
* Description    : This function configures the data parity of the selected UART.
* Input 1        : UARTx (x can be 0,1, 2 or 3) the desired UART
* Input 2        : The parity type
* Output         : None
* Return         : None
*******************************************************************************/
inline void UART_ParityConfig(UART_TypeDef *UARTx, UARTParity_TypeDef Parity)
{
  UARTx->CR = (UARTx->CR&0xFFDF)|(u16)Parity;
}

/*******************************************************************************
* Function Name  : UART_StopBitsConfig
* Description    : This function configures the number of stop bits of the
*                  selected UART.
* Input 1        : UARTx (x can be 0,1, 2 or 3) the desired UART
* Input 2        : The number of stop bits
* Output         : None
* Return         : None
*******************************************************************************/
inline void UART_StopBitsConfig(UART_TypeDef *UARTx, UARTStopBits_TypeDef StopBits)
{
  UARTx->CR = (UARTx->CR&0xFFE7)|(u16)StopBits;
}

/*******************************************************************************
* Function Name  : UART_Config
* Description    : This function configures the baudrate, the mode, the data
*                  parity and the number of stop bits of the selected UART.
* Input 1        : UARTx (x can be 0,1, 2 or 3) the desired UART
* Input 2        : The baudrate value
* Input 3        : The parity type
* Input 4        : The number of stop bits
* Input 5        : The UART mode
* Output         : None
* Return         : None
*******************************************************************************/
void UART_Config(UART_TypeDef *UARTx, u32 BaudRate, UARTParity_TypeDef Parity,
                 UARTStopBits_TypeDef StopBits, UARTMode_TypeDef Mode);

/*******************************************************************************
* Function Name  : UART_ItConfig
* Description    : This function enables or disables the interrupts of the
*                  selected UART.
* Input 1        : UARTx (x can be 0,1, 2 or 3) the desired UART
* Input 2        : The new interrupt flag
* Input 3        : ENABLE or DISABLE
* Output         : None
* Return         : None
*******************************************************************************/
void UART_ItConfig(UART_TypeDef *UARTx, u16 UART_Flag, FunctionalState NewState);

/*******************************************************************************
* Function Name  : UART_FifoConfig
* Description    : This function enables or disables the Rx and Tx FIFOs of
*                  the selected UART.
* Input 1        : UARTx (x can be 0,1, 2 or 3) the desired UART
* Input 2        : ENABLE or DISABLE
* Output         : None
* Return         : None
*******************************************************************************/
void UART_FifoConfig(UART_TypeDef *UARTx, FunctionalState NewState);

/*******************************************************************************
* Function Name  : UART_FifoReset
* Description    : This function resets the Rx and the Tx FIFOs of the
*                  selected UART.
* Input 1        : UARTx (x can be 0,1, 2 or 3) the desired UART
* Input 2        : RxFIFO or TxFIFO
* Output         : None
* Return         : None
*******************************************************************************/
void UART_FifoReset(UART_TypeDef *UARTx, UARTFIFO_TypeDef FIFO);

/*******************************************************************************
* Function Name  : UART_LoopBackConfig
* Description    : This function enables or disables the loop back mode of
*                  the selected UART.
* Input 1        : UARTx (x can be 0,1, 2 or 3) the desired UART
* Input 2        : ENABLE or DISABLE
* Output         : None
* Return         : None
*******************************************************************************/
void UART_LoopBackConfig(UART_TypeDef *UARTx, FunctionalState NewState);

/*******************************************************************************
* Function Name  : UART_TimeOutPeriodConfig
* Description    : This function configure the Time Out Period.
* Input 1        : UARTx (x can be 0,1, 2 or 3) the desired UART
* Input 2        : The time-out period value
* Output         : None
* Return         : None
*******************************************************************************/
inline void UART_TimeOutPeriodConfig(UART_TypeDef *UARTx, u16 TimeOutPeriod)
{
  UARTx->TOR = TimeOutPeriod;
}

/*******************************************************************************
* Function Name  : UART_GuardTimeConfig
* Description    : This function configure the Guard Time.
* Input 1        : UARTx (x can be 0,1, 2 or 3) the desired UART
* Input 2        : The guard time value
* Output         : None
* Return         : None
*******************************************************************************/
inline void UART_GuardTimeConfig(UART_TypeDef *UARTx, u16 GuardTime)
{
  UARTx->GTR = GuardTime;
}

/*******************************************************************************
* Function Name  : UART_RxConfig
* Description    : This function enable and disable the UART data reception.
* Input 1        : UARTx (x can be 0,1, 2 or 3) the desired UART
* Input 2        : ENABLE or DISABLE
* Output         : None
* Return         : None
*******************************************************************************/
void UART_RxConfig(UART_TypeDef *UARTx, FunctionalState NewState);

/*******************************************************************************
* Function Name  : UART_OnOffConfig
* Description    : This function sets On/Off the selected UART.
* Input 1        : UARTx (x can be 0,1, 2 or 3) the desired UART
* Input 2        : ENABLE or DISABLE
* Output         : None
* Return         : None
*******************************************************************************/
void UART_OnOffConfig(UART_TypeDef *UARTx, FunctionalState NewState);

/*******************************************************************************
* Function Name  : UART_ByteSend
* Description    : This function sends a data byte to the selected UART.
* Input 1        : UARTx (x can be 0,1, 2 or 3) the desired UART
* Input 2        : A pointer to the data byte to send
* Output         : None
* Return         : None
*******************************************************************************/
void UART_ByteSend(UART_TypeDef *UARTx, u8 *Data);

/*******************************************************************************
* Function Name  : UART_9BitByteSend
* Description    : This function sends a 9 bits data byte to the selected UART.
* Input 1        : UARTx (x can be 0,1, 2 or 3) the desired UART
* Input 2        : A pointer to the data to send
* Output         : None
* Return         : None
*******************************************************************************/
void UART_9BitByteSend(UART_TypeDef *UARTx, u16 *Data);

/*******************************************************************************
* Function Name  : UART_DataSend
* Description    : This function sends several data bytes to the selected UART.
* Input 1        : UARTx (x can be 0,1, 2 or 3) the desired UART
* Input 2        : A pointer to the data to send
* Input 3        : The data length in bytes
* Output         : None
* Return         : None
*******************************************************************************/
void UART_DataSend(UART_TypeDef *UARTx, u8 *Data, u8 DataLength);

/*******************************************************************************
* Function Name  : UART_9BitDataSend
* Description    : This function sends several 9 bits data bytes to the selected UART.
* Input 1        : UARTx (x can be 0,1, 2 or 3) the desired UART
* Input 2        : A pointer to the data to send
* Input 3        : The data length
* Output         : None
* Return         : None
*******************************************************************************/
void UART_9BitDataSend(UART_TypeDef *UARTx, u16 *Data, u8 DataLength);

/*******************************************************************************
* Function Name  : UART_StringSend
* Description    : This function sends a string to the selected UART.
* Input 1        : UARTx (x can be 0,1, 2 or 3) the desired UART
* Input 2        : A pointer to the string to send
* Output         : None
* Return         : None
*******************************************************************************/
void UART_StringSend(UART_TypeDef *UARTx, u8 *String);

/*******************************************************************************
* Function Name  : UART_ByteReceive
* Description    : This function gets a data byte from the selected UART.
* Input 1        : UARTx (x can be 0,1, 2 or 3) the desired UART
* Input 2        : A pointer to the buffer where the data will be stored
* Input 3        : The time-out period
* Output         : The received data
* Return         : The UARTx.SR register contents
*******************************************************************************/
u16 UART_ByteReceive(UART_TypeDef *UARTx, u8 *Data, u8 TimeOut);

/*******************************************************************************
* Function Name  : UART_9BitByteReceive
* Description    : This function gets a 9 bits data byte from the selected UART.
* Input 1        : UARTx (x can be 0,1, 2 or 3) the desired UART
* Input 2        : A pointer to the buffer where the data will be stored
* Input 3        : The time-out period value
* Output         : The received data
* Return         : The UARTx.SR register contents
*******************************************************************************/
u16 UART_9BitByteReceive(UART_TypeDef *UARTx, u16 *Data, u8 TimeOut);

/*******************************************************************************
* Function Name  : UART_DataReceive
* Description    : This function gets 8 bits data bytes from the selected UART.
* Input 1        : UARTx (x can be 0,1, 2 or 3) the desired UART
* Input 2        : A pointer to the buffer where the data will be stored
* Input 3        : The data length
* Input 4        : The time-out period value
* Output         : The received data
* Return         : The UARTx.SR register contents
*******************************************************************************/
u16 UART_DataReceive(UART_TypeDef *UARTx, u8 *Data, u8 DataLength, u8 TimeOut);

/*******************************************************************************
* Function Name  : UART_9BitDataReceive
* Description    : This function gets 9 bits data bytes from the selected UART.
* Input 1        : UARTx (x can be 0,1, 2 or 3) the desired UART
* Input 2        : A pointer to the buffer where the data will be stored
* Input 3        : The data length
* Input 4        : The time-out value
* Output         : The received data
* Return         : The UARTx.SR register contents
*******************************************************************************/
u16 UART_9BitDataReceive(UART_TypeDef *UARTx, u16 *Data, u8 DataLength, u8 TimeOut);

/*******************************************************************************
* Function Name  : UART_StringReceive
* Description    : This function gets 8 bits data bytes from the selected UART.
* Input 1        : UARTx (x can be 0,1, 2 or 3) the desired UART
* Input 2        : A pointer to the buffer where the string will be stored
* Output         : None
* Return         : None
*******************************************************************************/
u16 UART_StringReceive(UART_TypeDef *UARTx, u8 *Data);

/*******************************************************************************
* Function Name  : UART_FlagStatus
* Description    : This function gets the flags status of the selected UART.
* Input 1        : UARTx (x can be 0,1, 2 or 3) the desired UART
* Output         : None
* Return         : None
*******************************************************************************/
inline u16 UART_FlagStatus(UART_TypeDef *UARTx)
{
  return UARTx->SR;
}

#ifdef USE_SERIAL_PORT
/*******************************************************************************
* Function Name  : sendchar
* Description    : This function sends a character to the selected UART.
* Input 1        : A pointer to the character to send.
* Output         : None
* Return         : None
*******************************************************************************/
void sendchar( char *ch );
#endif /* USE_SERIAL_PORT */

#endif /* _UART_H */

/******************* (C) COPYRIGHT 2003 STMicroelectronics *****END OF FILE****/
