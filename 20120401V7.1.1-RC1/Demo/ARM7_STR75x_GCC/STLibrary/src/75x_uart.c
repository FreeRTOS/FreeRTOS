/******************** (C) COPYRIGHT 2006 STMicroelectronics ********************
* File Name          : 75x_uart.c
* Author             : MCD Application Team
* Date First Issued  : 03/10/2006
* Description        : This file provides all the UART software functions.
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

/* Includes ------------------------------------------------------------------*/
#include "75x_uart.h"
#include "75x_mrcc.h"

/* Private typedef -----------------------------------------------------------*/
/* Private define ------------------------------------------------------------*/
/* UART LIN Mask */
#define UART_LIN_Disable_Mask           0xFEFF /* LIN Disable Mask */
#define UART_LIN_Enable_Mask            0x0100 /* LIN Enable Mask */

/* UART Mask */
#define UART_Enable_Mask                0x0001 /* UART Enable Mask */
#define UART_Disable_Mask               0xFFFE /* UART Disable Mask */

/* UART LoopBack */
#define UART_LoopBack_Disable_Mask      0xFF7F/* LoopBack Disable Mask */
#define UART_LoopBack_Enable_Mask       0x0080/* LoopBack Enable Mask */

#define UART_WordLength_Mask            0xFF9F  /* UART Word Length Mask */
#define UART_Parity_Mask                0xFF79  /* UART Parity Mask */
#define UART_HardwareFlowControl_Mask   0x3FFF  /* UART Hardware Flow Control Mask */
#define UART_TxRxFIFOLevel_Mask         0xFFC0  /* UART Tx Rx FIFO Level Mask */
#define UART_LINBreakLength_Mask        0xE1FF  /* UART LIN Break Length Mask */
#define UART_BreakChar_Mask             0x0001  /* UART Break Character send Mask */
#define UART_FLAG_Mask                  0x1F    /* UART Flag Mask */
#define UART_Mode_Mask                  0xFCFF  /* UART Mode Mask */
#define UART_RTSSET_Mask                0xF7FF  /* RTS signal is high */
#define UART_RTSRESET_Mask              0x0800  /* RTS signal is low */

/* Private macro -------------------------------------------------------------*/
/* Private variables ---------------------------------------------------------*/
/* Private function prototypes -----------------------------------------------*/
/* Private functions ---------------------------------------------------------*/

/*******************************************************************************
* Function Name  : UART_DeInit
* Description    : Deinitializes the UARTx peripheral registers to their default
*                  reset values.
* Input          : UARTx: where x can be 0,1 or 2 to select the UART peripheral.
* Output         : None
* Return         : None
*******************************************************************************/
void UART_DeInit(UART_TypeDef* UARTx)
{
  /* Reset the UARTx registers values */
  if(UARTx == UART0)
  {
    MRCC_PeripheralSWResetConfig(MRCC_Peripheral_UART0,ENABLE);
    MRCC_PeripheralSWResetConfig(MRCC_Peripheral_UART0,DISABLE);
  }
  else if(UARTx == UART1)
  {
    MRCC_PeripheralSWResetConfig(MRCC_Peripheral_UART1,ENABLE);
    MRCC_PeripheralSWResetConfig(MRCC_Peripheral_UART1,DISABLE);
  }
  else if(UARTx == UART2)
  {
    MRCC_PeripheralSWResetConfig(MRCC_Peripheral_UART2,ENABLE);
    MRCC_PeripheralSWResetConfig(MRCC_Peripheral_UART2,DISABLE);
  }
}

/*******************************************************************************
* Function Name  : UART_Init
* Description    : Initializes the UARTx peripheral according to the specified
*                  parameters in the UART_InitStruct .
* Input          : - UARTx: where x can be 0,1or 2 to select the UART peripheral.
*                  - UART_InitStruct: pointer to a UART_InitTypeDef structure
*                    that contains the configuration information for the
*                    specified UART peripheral.
* Output         : None
* Return         : None
*******************************************************************************/
void UART_Init(UART_TypeDef* UARTx, UART_InitTypeDef* UART_InitStruct)
{

  u32 APBClock = 0;
  u32 IntegerDivider = 0;
  u32 FractionalDivider = 0;
  MRCC_ClocksTypeDef  MRCC_ClocksStatus;
     
  /* Clear the WLEN bits */
  UARTx->LCR &= UART_WordLength_Mask;
  /* Set the WLEN bits according to UART_WordLength value */
  UARTx->LCR |= UART_InitStruct->UART_WordLength;

  /* Choose Stop Bits */
  if(UART_InitStruct->UART_StopBits == UART_StopBits_1)
  {
    /* One Stop Bit */
    UARTx->LCR &= UART_StopBits_1;
  }
  else
  {
    /* Two Stop Bits */
    UARTx->LCR |= UART_StopBits_2;
  }

  /* Clear SPS, EPS and PEN bits */
  UARTx->LCR &= UART_Parity_Mask;
  /* Set PS, EPS and PEN bits according to UART_Parity value */
  UARTx->LCR |= UART_InitStruct->UART_Parity;

  /* Configure the BaudRate --------------------------------------------------*/
  /* Get the APB frequency */
  MRCC_GetClocksStatus(&MRCC_ClocksStatus);
  APBClock = MRCC_ClocksStatus.PCLK_Frequency;
  
  /* Determine the integer part */
  IntegerDivider = ((100) * (APBClock) / (16 * (UART_InitStruct->UART_BaudRate)));
  UARTx->IBRD = IntegerDivider / 100; 

  /* Determine the fractional part */
  FractionalDivider = IntegerDivider - (100 * (UARTx->IBRD));
  UARTx->FBRD = ((((FractionalDivider * 64) + 50) / 100));
  
  /* Choose the Hardware Flow Control */
  /* Clear RTSEn and CTSEn bits */
  UARTx->CR &=  UART_HardwareFlowControl_Mask;
  /* Set RTSEn and CTSEn bits according to UART_HardwareFlowControl value */
  UARTx->CR |= UART_InitStruct->UART_HardwareFlowControl;

  /* Configure the UART mode */
  /* Clear TXE and RXE bits */
  UARTx->CR &= UART_Mode_Mask;
  /* Set TXE and RXE bits according to UART_Mode value */
  UARTx->CR |= UART_InitStruct->UART_Mode;

  /* Enable or disable the FIFOs */
  /* Set the FIFOs Levels */
  if(UART_InitStruct->UART_FIFO == UART_FIFO_Enable)
  {
    /* Enable the FIFOs */
    UARTx->LCR |= UART_FIFO_Enable;
    
    /* Clear TXIFLSEL and RXIFLSEL bits */
    UARTx->IFLS &=  UART_TxRxFIFOLevel_Mask;
    
    /* Set RXIFLSEL bits according to UART_RxFIFOLevel value */
    UARTx->IFLS |= (UART_InitStruct->UART_RxFIFOLevel << 3);
    
    /* Set TXIFLSEL bits according to UART_TxFIFOLevel value */
    UARTx->IFLS |= UART_InitStruct->UART_TxFIFOLevel;
  }
  else
  {
    /* Disable the FIFOs */
    UARTx->LCR &= UART_FIFO_Disable;
  }
}

/*******************************************************************************
* Function Name  : UART_StructInit
* Description    : Fills each UART_InitStruct member with its default value.
* Input          : UART_InitStruct: pointer to a UART_InitTypeDef structure which
*                  will be initialized.
* Output         : None
* Return         : None
*******************************************************************************/
void UART_StructInit(UART_InitTypeDef* UART_InitStruct)
{
  /* UART_InitStruct members default value */
  UART_InitStruct->UART_WordLength = UART_WordLength_8D;
  UART_InitStruct->UART_StopBits = UART_StopBits_1;
  UART_InitStruct->UART_Parity = UART_Parity_Odd ;
  UART_InitStruct->UART_BaudRate = 9600;
  UART_InitStruct->UART_HardwareFlowControl = UART_HardwareFlowControl_None;
  UART_InitStruct->UART_Mode = UART_Mode_Tx_Rx;
  UART_InitStruct->UART_FIFO = UART_FIFO_Enable;
  UART_InitStruct->UART_TxFIFOLevel = UART_FIFOLevel_1_2;
  UART_InitStruct->UART_RxFIFOLevel = UART_FIFOLevel_1_2;
}

/*******************************************************************************
* Function Name  : UART_Cmd
* Description    : Enables or disables the specified UART peripheral.
* Input          : - UARTx: where x can be 0,1 or 2 to select the UART peripheral
*                  - NewState: new state of the UARTx peripheral.
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void UART_Cmd(UART_TypeDef* UARTx, FunctionalState NewState)
{
  if (NewState == ENABLE)
  {
    /* Enable the selected UART by setting the UARTEN bit in the CR register */
    UARTx->CR |= UART_Enable_Mask;
  }
  else
  {
    /* Disable the selected UART by clearing the UARTEN bit in the CR register */
    UARTx->CR &= UART_Disable_Mask;
  }
}

/*******************************************************************************
* Function Name  : UART_ITConfig
* Description    : Enables or disables the specified UART interrupts.
* Input          : - UARTx: where x can be 0,1 or 2 to select the UART peripheral
*                  - UART_IT: specifies the UART interrupts sources to be 
*                    enabled or disabled. This parameter can be any combination 
*                    of the following values:                   
*                       - UART_IT_OverrunError: Overrun Error interrupt
*                       - UART_IT_BreakError: Break Error interrupt
*                       - UART_IT_ParityError: Parity Error interrupt
*                       - UART_IT_FrameError: Frame Error interrupt
*                       - UART_IT_ReceiveTimeOut: Receive Time Out interrupt
*                       - UART_IT_Transmit: Transmit interrupt
*                       - UART_IT_Receive: Receive interrupt
*                       - UART_IT_CTS: CTS interrupt 
*                  - NewState: new state of the UARTx peripheral.
*                  This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void UART_ITConfig(UART_TypeDef* UARTx, u16 UART_IT, FunctionalState NewState)
{
  if(NewState == ENABLE)
  {
    /* Enables the selected interrupts */
    UARTx->IMSC |= UART_IT;
  }
  else
  {
    /* Disables the selected interrupts */
    UARTx->IMSC &= ~UART_IT;
  }
}

/*******************************************************************************
* Function Name  : UART_DMAConfig
* Description    : Configures the UART0 DMA interface.
* Input          : - UART0_DMAtransfer : specifies the configuration of DMA request.
*                    This parameter can be:
*                         - UART0_DMATransfer_Single: Single DMA transfer
*                         - UART0_DMATransfer_Burst: Burst DMA transfer
*                  - UART0_DMAOnError: specifies the DMA on error request.
*                    This parameter can be:
*                         - UART0_DMAOnError_Enable: DMA receive request enabled
*                           when the UART error interrupt is asserted.
*                         - UART0_DMAOnError_Disable: DMA receive request disabled
*                           when the UART error interrupt is asserted.
* Output         : None
* Return         : None
*******************************************************************************/
void UART_DMAConfig(u16 UART0_DMATransfer, u16 UART0_DMAOnError)
{
  if(UART0_DMATransfer == UART0_DMATransfer_Single)
  {
    /* Configure the DMA request from the UART0 as single transfer */
    UART0->DMACR &= UART0_DMATransfer_Single;
  }
  else
  {
    UART0->DMACR |= UART0_DMATransfer_Burst;
  }
  
  if(UART0_DMAOnError == UART0_DMAOnError_Enable)
  {
    UART0->DMACR &= UART0_DMAOnError_Enable;
  }
  else
  {
    UART0->DMACR |= UART0_DMAOnError_Disable;
  }
}

/*******************************************************************************
* Function Name  : UART_DMACmd
* Description    : Enables or disables the UART0’s DMA interface.
* Input          : - UART0_DMAReq: specifies the DMA request.
*                    This parameter can be:
*                     - UART0_DMAReq_Tx: Transmit DMA request
*                     - UART0_DMAReq_Rx: Receive DMA request
*                  - NewState: new state of the UART0’s DMA request.
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void UART_DMACmd(u16 UART0_DMAReq, FunctionalState NewState)
{
  if(UART0_DMAReq == UART0_DMAReq_Tx)
  {
    if(NewState == ENABLE)
    {
      UART0->DMACR |=  UART0_DMAReq_Tx;
    }
    else
    {
      UART0->DMACR &= ~UART0_DMAReq_Tx;
    }
  }
  else
  {
    if(NewState == ENABLE)
    {
      UART0->DMACR |=  UART0_DMAReq_Rx;
    }
    else
    {
      UART0->DMACR &= ~UART0_DMAReq_Rx;
    }
  }
}

/*******************************************************************************
* Function Name  : UART_LoopBackConfig
* Description    : Enables or disables LoopBack mode in UARTx.
* Input          : - UARTx: where x can be 0,1 or 2 to select the UART peripheral
*                  - NewState: new state of the UARTx’s LoopBack mode.
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void UART_LoopBackConfig(UART_TypeDef* UARTx, FunctionalState NewState)
{
  if (NewState == ENABLE)
  {
    /* Enable the LoopBack mode of the specified UART */
    UARTx->CR |= UART_LoopBack_Enable_Mask;
  }
  else
  {
    /* Disable the LoopBack mode of the specified UART */
    UARTx->CR &= UART_LoopBack_Disable_Mask;
  }
}

/*******************************************************************************
* Function Name  : UART_LINConfig
* Description    : Sets the LIN break length.
* Input          : - UARTx: where x can be 0,1 or 2 to select the UART peripheral.
*                  - UART_LINBreakLength: Break length value.
*                    This parameter can be:
*                         - UART_LINBreakLength_10: 10 low bits
*                         - UART_LINBreakLength_11: 11 low bits
*                         - UART_LINBreakLength_12: 12 low bits
*                         - UART_LINBreakLength_13: 13 low bits
*                         - UART_LINBreakLength_14: 14 low bits
*                         - UART_LINBreakLength_15: 15 low bits
*                         - UART_LINBreakLength_16: 16 low bits
*                         - UART_LINBreakLength_17: 17 low bits
*                         - UART_LINBreakLength_18: 18 low bits
*                         - UART_LINBreakLength_19: 19 low bits
*                         - UART_LINBreakLength_20: 20 low bits
* Output         : None
* Return         : None
*******************************************************************************/
void UART_LINConfig(UART_TypeDef* UARTx, u16 UART_LINBreakLength)
{
  /* Clear LBKLEN bits */
  UARTx->LCR &= UART_LINBreakLength_Mask;

  /* Set LBKLEN bits according to UART_LINBreakLength value */
  UARTx->LCR |= UART_LINBreakLength;
}

/*******************************************************************************
* Function Name  : UART_LINCmd
* Description    : Enables or disables LIN master mode in UARTx.
* Input          : - UARTx: where x can be 0,1 or 2 to select the UART peripheral
*                  - NewState: new state of the UARTx’s LIN interface. 
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void UART_LINCmd(UART_TypeDef* UARTx, FunctionalState NewState)
{
  if(NewState == ENABLE)
  {
    /* Enable the LIN mode of the specified UART */
    UARTx->LCR |= UART_LIN_Enable_Mask;
  }
  else
  {
    /* Disable the LIN mode of the specified UART */
    UARTx->LCR &= UART_LIN_Disable_Mask;
  }
}

/*******************************************************************************
* Function Name  : UART_SendData
* Description    : Transmits a signle Byte of data through the UARTx peripheral.
* Input          : - UARTx: where x can be 0,1 or 2 to select the UART peripheral.
*                  - Data: the byte to transmit
* Output         : None
* Return         : None
*******************************************************************************/
void UART_SendData(UART_TypeDef* UARTx, u8 Data)
{
  /* Transmit one byte */
  UARTx->DR = Data;
}

/*******************************************************************************
* Function Name  : UART_ReceiveData
* Description    : Returns the most recent received Byte by the UARTx peripheral.
* Input          : UARTx: where x can be 0,1 or 2 to select the UART peripheral.
* Output         : None
* Return         : The received data
*******************************************************************************/
u8 UART_ReceiveData(UART_TypeDef* UARTx)
{
  /* Receive one byte */
  return ((u8)UARTx->DR);
}

/*******************************************************************************
* Function Name  : UART_SendBreak
* Description    : Transmits break characters.
* Input          : UARTx: where x can be 0,1 or 2 to select the UART peripheral.
* Output         : None
* Return         : None
*******************************************************************************/
void UART_SendBreak(UART_TypeDef* UARTx)
{
  /* Send break characters */
  UARTx->BKR |= UART_BreakChar_Mask;
}

/*******************************************************************************
* Function Name  : UART_RTSConfig
* Description    : Sets or Resets the RTS signal
* Input          : - UARTx: where x can be 0,1 or 2 to select the UART peripheral.
*                  - RTSState: new state of the RTS signal.
*                    This parameter can be: RTSSET or RTSRESET
* Output         : None
* Return         : None
*******************************************************************************/
void UART_RTSConfig(UART_TypeDef* UARTx, UART_RTSTypeDef RTSState)
{
  if(RTSState == RTSRESET)
  {
    UARTx->CR |= UART_RTSRESET_Mask;
  }
  else if(RTSState == RTSSET)
  {
    UARTx->CR &= UART_RTSSET_Mask;
  }
}

/*******************************************************************************
* Function Name  : UART_GetFlagStatus
* Description    : Checks whether the specified UART flag is set or not.
* Input          : - UARTx: where x can be 0,1 or 2 to select the UART peripheral
*                  - UART_FLAG: specifies the flag to check.
*                    This parameter can be one of the following values:
*                     - UART_FLAG_OverrunError: Overrun error flag
*                     - UART_FLAG_Break: break error flag
*                     - UART_FLAG_ParityError: parity error flag
*                     - UART_FLAG_FrameError: frame error flag
*                     - UART_FLAG_TxFIFOEmpty: Transmit FIFO Empty flag
*                     - UART_FLAG_RxFIFOFull: Receive FIFO Full flag
*                     - UART_FLAG_TxFIFOFull: Transmit FIFO Full flag
*                     - UART_FLAG_RxFIFOEmpty: Receive FIFO Empty flag
*                     - UART_FLAG_Busy: Busy flag
*                     - UART_FLAG_CTS: CTS flag
*                     - UART_RawIT_OverrunError: Overrun Error interrupt flag
*                     - UART_RawIT_BreakError: Break Error interrupt flag
*                     - UART_RawIT_ParityError: Parity Error interrupt flag
*                     - UART_RawIT_FrameError: Frame Error interrupt flag
*                     - UART_RawIT_ReceiveTimeOut: ReceiveTimeOut interrupt flag
*                     - UART_RawIT_Transmit: Transmit interrupt flag
*                     - UART_RawIT_Receive: Receive interrupt flag
*                     - UART_RawIT_CTS: CTS interrupt flag
* Output         : None
* Return         : The new state of UART_FLAG (SET or RESET).
*******************************************************************************/
FlagStatus UART_GetFlagStatus(UART_TypeDef* UARTx, u16 UART_FLAG)
{
  u32 UARTReg = 0, FlagPos = 0;
  u32 StatusReg = 0;

  /* Get the UART register index */
  UARTReg = UART_FLAG >> 5;

  /* Get the flag position */
  FlagPos = UART_FLAG & UART_FLAG_Mask;

  if(UARTReg == 1) /* The flag to check is in RSR register */
  {
    StatusReg = UARTx->RSR;
  }
  else if (UARTReg == 2) /* The flag to check is in FR register */
  {
    StatusReg = UARTx->FR;
  }
  else if(UARTReg == 3) /* The flag to check is in RIS register */
  {
    StatusReg = UARTx->RIS;
  }

  if((StatusReg & (1 << FlagPos))!= RESET)
  {
    return SET;
  }
  else
  {
    return RESET;
  }
}

/*******************************************************************************
* Function Name  : UART_ClearFlag
* Description    : Clears the UARTx’s pending flags.
* Input          : - UARTx: where x can be 0,1or 2 to select the UART peripheral.
*                  - UART_FLAG: specifies the flag to clear.
*                    This parameter can be one of the following values:
*                       - UART_FLAG_OverrunError: Overrun error flag
*                       - UART_FLAG_Break: break error flag
*                       - UART_FLAG_ParityError: parity error flag
*                       - UART_FLAG_FrameError: frame error flag
* Output         : None
* Return         : None
*******************************************************************************/
void UART_ClearFlag(UART_TypeDef* UARTx, u16 UART_FLAG)
{
  u8 FlagPos = 0;

  /* Get the flag position */
  FlagPos = UART_FLAG & UART_FLAG_Mask;

  /* Clear the sepecified flag */
  UARTx->RSR &= ~(1 << FlagPos);
}

/*******************************************************************************
* Function Name  : UART_GetITStatus
* Description    : Checks whether the specified UART interrupt has occurred or not.
* Input          : - UARTx: where x can be 0,1or 2 to select the UART peripheral.
*                  - UART_IT: specifies the interrupt source to check.
*                    This parameter can be one of the following values:
*                       - UART_IT_OverrunError: Overrun Error interrupt 
*                       - UART_IT_BreakError: Break Error interrupt 
*                       - UART_IT_ParityError: Parity Error interrupt 
*                       - UART_IT_FrameError: Frame Error interrupt 
*                       - UART_IT_ReceiveTimeOut: Receive Time Out interrupt 
*                       - UART_IT_Transmit: Transmit interrupt 
*                       - UART_IT_Receive: Receive interrupt 
*                       - UART_IT_CTS: CTS interrupt 
* Output         : None
* Return         : The new state of UART_IT (SET or RESET).
*******************************************************************************/
ITStatus UART_GetITStatus(UART_TypeDef* UARTx, u16 UART_IT)
{
  if((UARTx->MIS & UART_IT) != RESET)
  {
    return SET;
  }
  else
  {
    return RESET;
  }
}

/*******************************************************************************
* Function Name  : UART_ClearITPendingBit
* Description    : Clears the UARTx’s interrupt pending bits.
* Input          : - UARTx: where x can be 0,1or 2 to select the UART peripheral.
*                  - UART_IT: specifies the interrupt pending bit to clear.
*                    More than one interrupt can be cleared using the “|” operator.
*                    This parameter can be:
*                       - UART_IT_OverrunError: Overrun Error interrupt
*                       - UART_IT_BreakError: Break Error interrupt
*                       - UART_IT_ParityError: Parity Error interrupt
*                       - UART_IT_FrameError: Frame Error interrupt
*                       - UART_IT_ReceiveTimeOut: Receive Time Out interrupt
*                       - UART_IT_Transmit: Transmit interrupt
*                       - UART_IT_Receive: Receive interrupt
*                       - UART_IT_CTS: CTS interrupt
* Output         : None
* Return         : None
*******************************************************************************/
void UART_ClearITPendingBit(UART_TypeDef* UARTx, u16 UART_IT)
{
  /* Clear the specified interrupt */
  UARTx->ICR = UART_IT;
}

/******************* (C) COPYRIGHT 2006 STMicroelectronics *****END OF FILE****/
