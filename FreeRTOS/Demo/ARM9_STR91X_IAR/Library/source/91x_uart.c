/******************** (C) COPYRIGHT 2006 STMicroelectronics ********************
* File Name          : 91x_uart.c
* Author             : MCD Application Team
* Date First Issued  : 05/18/2006 : Version 1.0
* Description        : This file provides all the UART software functions.
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

/* Includes ------------------------------------------------------------------*/
#include "91x_uart.h"
#include "91x_scu.h"

/* Private typedef -----------------------------------------------------------*/
/* Private define ------------------------------------------------------------*/
/* UART IrDA Mask */
#define UART_IrDA_Disable_Mask	        0xFFFD	/* IrDA Disable Mask */
#define UART_IrDA_Enable_Mask           0x0002	/* IrDA Enable Mask */
#define IrDA_LowPower_Enable_Mask       0x0004 /*IrDA lower power mode enable*/
#define IrDA_LowPower_Disable_Mask      0xFFFB /*IrDA lower power mode enable*/

/* UART Mask */
#define UART_Enable_Mask	        0x0001	/* UART Enable Mask */
#define UART_Disable_Mask	        0xFFFE	/* UART Disable Mask */

/* UART LoopBack */
#define UART_LoopBack_Disable_Mask      0xFF7F	/* LoopBack Disable Mask */
#define UART_LoopBack_Enable_Mask       0x0080	/* LoopBack Enable Mask */

#define UART_WordLength_Mask            0xFF9F  /* UART Word Length Mask */
#define UART_Parity_Mask                0xFF79  /* UART Parity Mask */
#define UART_HardwareFlowControl_Mask   0x3FFF  /* UART Hardware Flow Control Mask */
#define UART_TxRxFIFOLevel_Mask         0xFFC0  /* UART Tx Rx FIFO Level Mask */
#define UART_BreakChar_Mask             0x0001  /* UART Break Character send Mask*/
#define UART_FLAG_Mask                  0x1F    /* UART Flag Mask */
#define UART_Mode_Mask                  0xFCFF  /* UART Mode Mask */
#define UART_RTS_LowLevel_Mask          0x0800  /* RTS signal is low */
#define UART_RTS_HighLevel_Mask         0xF7FF  /* RTS signal is High */
#define UART_DTR_LowLevel_Mask          0x0400  /* DTR signal is low */
#define UART_DTR_HighLevel_Mask         0xFBFF  /* DTR signal is High */
#define UART_ClearFlag_Mask             0xAA    /* Clear Flag Mask */

/* Private macro -------------------------------------------------------------*/
/* Private variables ---------------------------------------------------------*/
/* Private function prototypes -----------------------------------------------*/
/* Private functions ---------------------------------------------------------*/

  /*******************************************************************************
* Function Name  : UART_DeInit
* Description    : Deinitializes the UARTx peripheral registers
*                  to their default reset values.
* Input          : UARTx: where x can be 0,1 or 2 to select the UART peripheral.
* Output         : None
* Return         : None
*******************************************************************************/
void UART_DeInit(UART_TypeDef* UARTx)
{
  /* Reset the UARTx registers values */
  if(UARTx == UART0)
  {
    SCU_APBPeriphReset(__UART0,ENABLE);
    SCU_APBPeriphReset(__UART0,DISABLE);
  }
  else if(UARTx == UART1)
  {
    SCU_APBPeriphReset(__UART1,ENABLE);
    SCU_APBPeriphReset(__UART1,DISABLE);
  }
  else if(UARTx == UART2)
  {
    SCU_APBPeriphReset(__UART2,ENABLE);
    SCU_APBPeriphReset(__UART2,DISABLE);
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

  u64 UART_MainClock = 0;
  u32 IntegerDivider = 0;
  u32 FractionalDivider = 0;

  /* Clear the LCR[6:5] bits */
  UARTx->LCR &= UART_WordLength_Mask;
  /* Set the LCR[6:5] bits according to UART_WordLength value */
  UARTx->LCR |= UART_InitStruct->UART_WordLength;

  /* Choose Stop Bits */
  if(UART_InitStruct->UART_StopBits == UART_StopBits_2)
  {
    /* 2 Stop Bit */
    UARTx->LCR |= UART_StopBits_2;
  }
  else
  {
    /* One Stop Bits */
    UARTx->LCR &= UART_StopBits_1;
  }

  /* Configure the Parity */
  /* Clear the LCR[7]and LCR[2:1] bits */
  UARTx->LCR &= UART_Parity_Mask;
  /* Set the LCR[7]and LCR[2:1] bits according to UART_Parity value */
  UARTx->LCR |= UART_InitStruct->UART_Parity;

  /* Configure the BaudRate */
  UART_MainClock = (SCU_GetMCLKFreqValue())*1000;
  if((SCU->CLKCNTR & 0x200) != 0x200)
  {
    UART_MainClock = UART_MainClock/2;
  }
  /* Determine the integer part */
  IntegerDivider = ((100) * (UART_MainClock) / (16 * (UART_InitStruct->UART_BaudRate)));
  UARTx->IBRD = IntegerDivider / 100;

  /* Determine the fractional part */
  FractionalDivider = IntegerDivider - (100 * (UARTx->IBRD));
  UARTx->FBRD = ((((FractionalDivider * 64) + 50) / 100));

  /* Choose the Hardware Flow Control */
  /* Clear the CR[15:14] bits */
  UARTx->CR &=  UART_HardwareFlowControl_Mask;
  /* Set the CR[15:14] bits according to UART_HardwareFlowControl value */
  UARTx->CR |= UART_InitStruct->UART_HardwareFlowControl;

  /* Configure the UART mode */
  /* Clear the CR[9:8] bits */
  UARTx->CR &= UART_Mode_Mask;
  /* Set the CR[9:8] bits according to UART_Mode value */
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
* Description    : Fills each UART_InitStruct member with its reset value.
* Input          : UART_InitStruct: pointer to a UART_InitTypeDef structure which
*                  will be initialized.
* Output         : None
* Return         : None
*******************************************************************************/
void UART_StructInit(UART_InitTypeDef* UART_InitStruct)
{
  /* Reset the  UART_InitStruct members */
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
*                       - UART_IT_DSR: DSR interrupt
*                       - UART_IT_DCD: DCD interrupt
*                       - UART_IT_CTS: CTS interrupt
*                       - UART_IT_RI: RI interrupt
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
* Description    : Configures the UARTx’s DMA interface.
* Input          : - UARTx: where x can be 1 or 2 to select the UART peripheral
*                  - UART_DMAOnError: specifies the DMA on error request.
*                    This parameter can be:
*                         - UART_DMAOnError_Enable: DMA receive request enabled
*                           when the UART error interrupt is asserted.
*                         - UART_DMAOnError_Disable: DMA receive request disabled
*                           when the UART error interrupt is asserted.
* Output         : None
* Return         : None
*******************************************************************************/
void UART_DMAConfig(UART_TypeDef* UARTx, u16 UART_DMAOnError)
{
  if(UART_DMAOnError == UART_DMAOnError_Enable)
  {
    UARTx->DMACR &= UART_DMAOnError_Enable;
  }
  else
  {
    UARTx->DMACR |= UART_DMAOnError_Disable;
  }
}

/*******************************************************************************
* Function Name  : UART_DMACmd
* Description    : Enables or disables the UARTx’s DMA interface.
* Input          : - UARTx: where x can be 1 or 2 to select the UART peripheral
*                  - UART_DMAReq: enables or disables the request of DMA from UART.
*                    This parameter can be:
*                     - UART_DMAReq_Tx: Transmit DMA Enable
*                     - UART_DMAReq_Rx: Receive DMA Enable
*                  - NewState: new state of the UARTx peripheral.
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void UART_DMACmd(UART_TypeDef* UARTx, u8 UART_DMAReq, FunctionalState NewState)
{
  if(UART_DMAReq == UART_DMAReq_Tx)
  {
    if(NewState == ENABLE)
    {
      UARTx->DMACR |=  UART_DMAReq_Tx;
    }
    else
    {
      UARTx->DMACR &= ~UART_DMAReq_Tx;
    }
  }

   if(UART_DMAReq == UART_DMAReq_Rx)
  {
    if(NewState == ENABLE)
    {
      UARTx->DMACR |=  UART_DMAReq_Rx;
    }
    else
    {
      UARTx->DMACR &= ~UART_DMAReq_Rx;
    }
  }
}

/*******************************************************************************
* Function Name  : UART_LoopBackConfig
* Description    : Enables or disables the LoopBack mode.
* Input          : - UARTx: where x can be 0,1 or 2 to select the UART peripheral
*                  - NewState: new state of the UARTx peripheral.
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
* Function Name  : UART_GetFlagStatus
* Description    : Checks whether the specified UART flag is set or not.
* Input          : - UARTx: where x can be 0,1 or 2 to select the UART peripheral
*                  - UART_FLAG: specifies the flag to check.
*                    This parameter can be one of the following values:
*                     - UART_FLAG_OverrunError: Overrun error flag
*                     - UART_FLAG_Break: break error flag
*                     - UART_FLAG_ParityError: parity error flag
*                     - UART_FLAG_FrameError: frame error flag
*                     - UART_FLAG_RI: RI flag
*                     - UART_FLAG_TxFIFOEmpty: Transmit FIFO Empty flag
*                     - UART_FLAG_RxFIFOFull: Receive FIFO Full flag
*                     - UART_FLAG_TxFIFOFull: Transmit FIFO Full flag
*                     - UART_FLAG_RxFIFOEmpty: Receive FIFO Empty flag
*                     - UART_FLAG_Busy: UART Busy flag
*                     - UART_FLAG_CTS: CTS flag
*                     - UART_FLAG_DCD: DCD flag
*                     - UART_FLAG_DSR: DSR flag
*                     - UART_RawIT_OverrunError: Overrun Error interrupt flag
*                     - UART_RawIT_BreakError: Break Error interrupt flag
*                     - UART_RawIT_ParityError: Parity Error interrupt flag
*                     - UART_RawIT_FrameError: Frame Error interrupt flag
*                     - UART_RawIT_ReceiveTimeOut: ReceiveTimeOut interrupt flag
*                     - UART_RawIT_Transmit: Transmit interrupt flag
*                     - UART_RawIT_Receive: Receive interrupt flag
*                     - UART_RawIT_DSR: DSR interrupt flag
*                     - UART_RawIT_DCD: DCD interrupt flag
*                     - UART_RawIT_CTS: CTS interrupt flag
*                     - UART_RawIT_RI: RI interrupt flag
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
    StatusReg = UARTx->RSECR;
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
* Description    : Clears the UARTx’s flags(Frame, Parity, Break, Overrun error).
* Input          : - UARTx: where x can be 0,1or 2 to select the UART peripheral.
* Output         : None
* Return         : None
*******************************************************************************/
void UART_ClearFlag(UART_TypeDef* UARTx)
{
  /* Clear the flag */
  UARTx->RSECR = UART_ClearFlag_Mask;
}

/*******************************************************************************
* Function Name  : UART_GetITStatus
* Description    : Checks whether the specified UART interrupt has occured or not.
* Input          : - UARTx: where x can be 0,1or 2 to select the UART peripheral.
*                  - UART_IT: specifies the interrupt pending bit to be checked.
*                    This parameter can be one of the following values:
*                       - UART_IT_OverrunError: Overrun Error interrupt
*                       - UART_IT_BreakError: Break Error interrupt
*                       - UART_IT_ParityError: Parity Error interrupt
*                       - UART_IT_FrameError: Frame Error interrupt
*                       - UART_IT_ReceiveTimeOut: Receive Time Out interrupt
*                       - UART_IT_Transmit: Transmit interrupt
*                       - UART_IT_Receive: Receive interrupt
*                       - UART_IT_DSR: DSR interrupt
*                       - UART_IT_DCD: DCD interrupt
*                       - UART_IT_CTS: CTS interrupt
*                       - UART_IT_RI: RI interrupt
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
*                       - UART_IT_DSR: DSR interrupt
*                       - UART_IT_DCD: DCD interrupt
*                       - UART_IT_CTS: CTS interrupt
*                       - UART_IT_RI: RI interrupt
* Output         : None
* Return         : None
*******************************************************************************/
void UART_ClearITPendingBit(UART_TypeDef* UARTx, u16 UART_IT)
{
  /* Clear the specified interrupt */
  UARTx->ICR &= UART_IT;
}

/*******************************************************************************
* Function Name  : UART_IrDALowPowerConfig
* Description    : Sets the IrDA low power mode
* Input          : - IrDAx: where x can be 0,1 or 2 to select the UART/IrDA peripheral.
*                  - NewState: new state of the UARTIrDA peripheral.
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void UART_IrDALowPowerConfig(u8 IrDAx, FunctionalState NewState)
{
  UART_TypeDef* UARTx;

  switch(IrDAx)
  {
    case IrDA0: UARTx = UART0;
    break;
    case IrDA1: UARTx = UART1;
    break;
    case IrDA2: UARTx = UART2;
    break;
  }

  if (NewState == ENABLE)
  {
    UARTx->CR |= IrDA_LowPower_Enable_Mask;
  }
  else
  {
    UARTx->CR &= IrDA_LowPower_Disable_Mask;
  }
}

/*******************************************************************************
* Function Name  : UART_IrDASetCounter
* Description    : Sets the IrDA counter divisor value.
* Input          : - UARTx: where x can be 0,1 or 2 to select the UART/IrDA peripheral.
*                  - IrDA_Counter: IrDA counter divisor new value n low power mode(Hz).
* Output         : None
* Return         : None
*******************************************************************************/
void UART_IrDASetCounter(u8 IrDAx, u32 IrDA_Counter)
{
  UART_TypeDef* UARTx;
  u32 APBClock;
  switch(IrDAx)
  {
    case IrDA0: UARTx = UART0;
    break;
    case IrDA1: UARTx = UART1;
    break;
    case IrDA2: UARTx = UART2;
    break;
  }
   /* Get the APB frequency */
  APBClock = (SCU_GetPCLKFreqValue())*1000;
  /* Determine the Counter Divisor part */
  UARTx->ILPR = (((APBClock*10) / ( IrDA_Counter)) + 5 )/10;
 }

/*******************************************************************************
* Function Name  : UART_IrDACmd
* Description    : Enables or disables the UARTx’s IrDA interface.
* Input          : - IrDAx: where x can be 0,1 or 2 to select the UART/IrDA peripheral
*                  - NewState: new state of the UARTx peripheral.
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void UART_IrDACmd(u8 IrDAx, FunctionalState NewState)
{
  UART_TypeDef* UARTx;

  switch(IrDAx)
  {
    case IrDA0: UARTx = UART0;
    break;
    case IrDA1: UARTx = UART1;
    break;
    case IrDA2: UARTx = UART2;
    break;
  }
  if(NewState == ENABLE)
  {
    /* Enable the IrDA mode of the specified UART */
    UARTx->CR |= UART_IrDA_Enable_Mask;
  }
  else
  {
    /* Disable the IrDA mode of the specified UART */
    UARTx->CR &= UART_IrDA_Disable_Mask;
  }
}

/*******************************************************************************
* Function Name  : UART_SendData
* Description    : Transmits signle Byte of data through the UARTx peripheral.
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
  UARTx->LCR |= UART_BreakChar_Mask;
}

/*******************************************************************************
* Function Name  : UART_RTSConfig
* Description    : Sets or Resets the RTS signal
* Input          : - LevelState: new state of the RTS signal for UART0 only.
*                    This parameter can be: LowLevel or HighLevel
* Output         : None
* Return         : None
*******************************************************************************/
void UART_RTSConfig(UART_LevelTypeDef LevelState)
{
  if(LevelState == LowLevel)
  {
    UART0->CR |= UART_RTS_LowLevel_Mask;
  }
  else
  {
    UART0->CR &= UART_RTS_HighLevel_Mask;
  }
}

/*******************************************************************************
* Function Name  : UART_DTRConfig
* Description    : Sets or Resets the DTR signal for UART0 only
* Input          : - LevelState: new state of the DTR signal.
*                    This parameter can be: LowLevel or HighLevel
* Output         : None
* Return         : None
*******************************************************************************/
void UART_DTRConfig(UART_LevelTypeDef LevelState)
{
  if(LevelState == LowLevel)
  {
    UART0->CR |= UART_DTR_LowLevel_Mask;
  }
  else
  {
    UART0->CR &= UART_DTR_HighLevel_Mask;
  }
}
/******************* (C) COPYRIGHT 2006 STMicroelectronics *****END OF FILE****/
