/******************** (C) COPYRIGHT 2006 STMicroelectronics ********************
* File Name          : 75x_ssp.c
* Author             : MCD Application Team
* Date First Issued  : 03/10/2006 
* Description        : This file provides all the SSP software functions.
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
#include "75x_ssp.h"
#include "75x_mrcc.h"

/* Private typedef -----------------------------------------------------------*/
/* Private define ------------------------------------------------------------*/
/* Private macro -------------------------------------------------------------*/
/* Private variables ---------------------------------------------------------*/

/* SSP peripheral Enable */
#define SSP_Enable   0x0002
#define SSP_Disable  0xFFFD

/* SSP Loop Back Mode Enable */
#define SSP_LoopBackMode_Enable   0x0001
#define SSP_LoopBackMode_Disable  0xFFFE

/* SSP Flag Mask */
#define SSP_Flag_Mask  0x001F

/* SSP DMA transmit/ receive enable/disable Masks */
#define SSP0_DMA_TransmitEnable   0x0002
#define SSP0_DMA_TransmitDisable  0xFFFD
#define SSP0_DMA_ReceiveEnable    0x0001
#define SSP0_DMA_ReceiveDisable   0xFFFE

/* SSP Masks */
#define SSP_FrameFormat_Mask     0xFFCF
#define SSP_DataSize_Mask        0xFFF0
#define SSP_ClockRate_Mask       0x00FF
#define SSP_ClockPrescaler_Mask  0xFF00
#define SSP_SSI_Set_Mask         0x0020
#define SSP_SSI_Reset_Mask       0xFFDF


/* Private function prototypes -----------------------------------------------*/
/* Private functions ---------------------------------------------------------*/

/*******************************************************************************
* Function Name  : SSP_DeInit
* Description    : Deinitializes the SSPx peripheral registers to their default
*                  reset values.
* Input          : SSPx: where x can be 0 or 1 to select the SSP peripheral.
* Output         : None
* Return         : None
*******************************************************************************/
void SSP_DeInit(SSP_TypeDef* SSPx)
{
  if(SSPx == SSP0)
  {
    /* Reset the SSP0 registers values*/
    MRCC_PeripheralSWResetConfig(MRCC_Peripheral_SSP0,ENABLE);
    MRCC_PeripheralSWResetConfig(MRCC_Peripheral_SSP0,DISABLE); 
  }
  else if (SSPx == SSP1)
  {
    /* Reset the SSP1 registers values*/
    MRCC_PeripheralSWResetConfig(MRCC_Peripheral_SSP1,ENABLE);
    MRCC_PeripheralSWResetConfig(MRCC_Peripheral_SSP1,DISABLE); 
  } 
}

/*******************************************************************************
* Function Name  : SSP_Init
* Description    : Initializes the SSPx  peripheral according to the specified
*                  parameters in the SSP_InitTypeDef structure.
* Input          : - SSPx: where x can be 0 or 1 to select the SSP peripheral.
*                  - SSP_InitStruct: pointer to a SSP_InitTypeDef structure that
*                    contains the configuration information for the specified SSP
*                    peripheral.
* Output         : None
* Return         : None
*******************************************************************************/
void SSP_Init(SSP_TypeDef* SSPx, SSP_InitTypeDef* SSP_InitStruct)
{ 
  /* Configure the Frame format */
  if(SSP_InitStruct->SSP_FrameFormat == SSP_FrameFormat_TI)
  {   
    /* Clear the FRF[1:0] bits */
    SSPx->CR0 &= SSP_FrameFormat_Mask;
    /* Set the TI frame format */
    SSPx->CR0 |= SSP_FrameFormat_TI;
  }
  else
  {
    /* Set the Motorola frame format */
    SSPx->CR0 &= SSP_FrameFormat_Motorola;
    /* Configure the Clock polarity */
    if(SSP_InitStruct->SSP_CPOL == SSP_CPOL_High)
    {   
      /* SCK is held high when no data is being transfered */    
      SSPx->CR0 |= SSP_CPOL_High;
    }
    else
    {
      /* SCK is held low when no data is being transfered */ 
      SSPx->CR0 &= SSP_CPOL_Low;
    }
    /* Configure the Clock Phase */
    if(SSP_InitStruct->SSP_CPHA == SSP_CPHA_2Edge)
    {    
      /* Data captured on second clock edge */   
      SSPx->CR0 |= SSP_CPHA_2Edge;
    }
    else
    {
      /* Data captured on first clock edge */
      SSPx->CR0 &= SSP_CPHA_1Edge;
    }
  }
  
  /* Configure the Mode */
  if(SSP_InitStruct->SSP_Mode == SSP_Mode_Slave)
  {  
    /* Set the slave mode */ 
    SSPx->CR1 |= SSP_Mode_Slave;
    /* Configure the Slave output */
    if(SSP_InitStruct->SSP_SlaveOutput == SSP_SlaveOutput_Disable)
    {  
      /* Slave output disabled */     
      SSPx->CR1 |= SSP_SlaveOutput_Disable;
    }
    else
    {
      /* Slave output enabled */     
      SSPx->CR1 &= SSP_SlaveOutput_Enable;
    }
    /* Configure the NSS pin */
    if(SSP_InitStruct->SSP_NSS == SSP_NSS_Soft)
    {  
      /* Slave selected by software through SSI bit */     
      SSPx->CR1 |= SSP_NSS_Soft;
      SSPx->CR1 &= SSP_SSI_Reset_Mask;
    }
    else
    {
      /* Slave selected by hardware through external SSpin */
      SSPx->CR1 &= SSP_NSS_Hard;
    }
    /* Configure the Clock rate and prescaler in TI slave mode */
    if(SSP_InitStruct->SSP_FrameFormat == SSP_FrameFormat_TI)
    { 
      /* Clear clock rate SCR[7:0] bits */
      SSPx->CR0 &= SSP_ClockRate_Mask; 
      /* Set the serial clock rate */
      SSPx->CR0 |= (SSP_InitStruct->SSP_ClockRate<<8);
      /* Clear clock prescaler CPSDVSR[7:0] bits */
      SSPx->PR &= SSP_ClockPrescaler_Mask;
      /* Set the serial clock prescaler */
      SSPx->PR |= SSP_InitStruct->SSP_ClockPrescaler;
    }
  }
  else
  {
    /* Set the master mode */
    SSPx->CR1 &= SSP_Mode_Master;
    /* Configure the NSS pin */
    if(SSP_InitStruct->SSP_NSS == SSP_NSS_Soft)
    {  
      /* Master selected by software through SSI bit */     
      SSPx->CR1 |= SSP_NSS_Soft;
      SSPx->CR1 |= SSP_SSI_Set_Mask;
    }
    else
    {
      /* Master selected by hardware through external SSpin */
      SSPx->CR1 &= SSP_NSS_Hard;
    }
    /* Clear clock rate SCR[7:0] bits */
    SSPx->CR0 &= SSP_ClockRate_Mask; 
    /* Set the serial clock rate */
    SSPx->CR0 |= (SSP_InitStruct->SSP_ClockRate<<8);
    /* Clear clock prescaler CPSDVSR[7:0] bits */
    SSPx->PR &= SSP_ClockPrescaler_Mask;
    /* Set the serial clock prescaler */
    SSPx->PR |= SSP_InitStruct->SSP_ClockPrescaler;
  }
  
  /* Clear data size DSS[3:0] bits */
  SSPx->CR0 &= SSP_DataSize_Mask;
  /* Set the data size */
  SSPx->CR0 |= SSP_InitStruct->SSP_DataSize;
}

/*******************************************************************************
* Function Name  : SSP_StructInit
* Description    : Fills each SSP_InitStruct member with its default value.
* Input          : SSP_InitStruct : pointer to a SSP_InitTypeDef structure
                   which will be initialized.
* Output         : None
* Return         : None
*******************************************************************************/
void SSP_StructInit(SSP_InitTypeDef* SSP_InitStruct)
{
  /* Initialize the SSP_FrameFormat member */
  SSP_InitStruct->SSP_FrameFormat = SSP_FrameFormat_Motorola;

  /* Initialize the SSP_Mode member */
  SSP_InitStruct->SSP_Mode = SSP_Mode_Master;

  /* Initialize the SSP_CPOL member */
  SSP_InitStruct->SSP_CPOL = SSP_CPOL_Low;

  /* Initialize the SSP_CPHA member */
  SSP_InitStruct->SSP_CPHA = SSP_CPHA_1Edge;

  /* Initialize the SSP_DataSize member */
  SSP_InitStruct->SSP_DataSize = SSP_DataSize_8b;
  
  /* Initialize the SSP_NSS  member */
  SSP_InitStruct->SSP_NSS = SSP_NSS_Hard;
  
  /* Initialize the SSP_SlaveOutput member */
  SSP_InitStruct->SSP_SlaveOutput = SSP_SlaveOutput_Enable;
  
  /* Initialize the SSP_ClockRate member */
  SSP_InitStruct->SSP_ClockRate = 0;
  
  /* Initialize the SSP_ClockPrescaler member */
  SSP_InitStruct->SSP_ClockPrescaler = 0;
}

/*******************************************************************************
* Function Name  : SSP_Cmd
* Description    : Enables or disables the specified SSP peripheral.
* Input          : - SSPx: where x can be 0 or 1 to select the SSP peripheral.
*                  - NewState: new state of the SSPx peripheral. 
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void SSP_Cmd(SSP_TypeDef* SSPx, FunctionalState NewState)
{
  if(NewState == ENABLE)
  {
    /* Enable the SSP peripheral */
    SSPx->CR1 |= SSP_Enable;
  }
  else
  {
    /* Disable the SSP peripheral */
    SSPx->CR1 &= SSP_Disable;
  }
}

/*******************************************************************************
* Function Name  : SSP_ITConfig
* Description    : Enables or disables the specified SSP interrupts.
* Input          : - SSPx: where x can be 0 or 1 to select the SSP peripheral.
*                  - SSP_IT: specifies the SSP interrupts sources to be enabled
*                    or disabled. This parameter can be any combination of the
*                    following values:
*                         - SSP_IT_TxFifo: Transmit FIFO half empty or less interrupt 
*                         - SSP_IT_RxFifo: Receive FIFO half full or less interrupt 
*                         - SSP_IT_RxTimeOut: Receive timeout interrupt 
*                         - SSP_IT_RxOverrun: Receive overrun interrupt 
*                  - NewState: new state of the specified SSP interrupts.
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void SSP_ITConfig(SSP_TypeDef* SSPx, u16 SSP_IT, FunctionalState NewState)
{
  if(NewState == ENABLE)
  {
    /* Enable the selected SSP interrupts */
    SSPx->IMSCR |= SSP_IT;
  }
  else
  {
    /* Disable the selected SSP interrupts */
    SSPx->IMSCR &= ~SSP_IT;
  }
}

/*******************************************************************************
* Function Name  : SSP_DMACmd
* Description    : Configures the SSP0 DMA interface.
* Input          : - SSP0_DMAtransfer : specifies the DMA transfer to be 
*                    enabled or disabled. This parameter can be one of the
*                    following values:
*                         - SSP0_DMA_Transmit: transmit Fifo DMA transfer
*                         - SSP0_DMA_Receive: receive Fifo DMA transfer 
*                  - NewState: new state of SSP0 DMA transfer.
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void SSP_DMACmd(u16 SSP0_DMAtransfer, FunctionalState NewState)
{
  if(NewState == ENABLE) 
  {
    if(SSP0_DMAtransfer == SSP0_DMA_Transmit) 
    {
      /* Enable DMA for the transmit FIFO */
      SSP0->DMACR |= SSP0_DMA_TransmitEnable;
    }
    else 
    {
      /* Enable DMA for the receive FIFO */
      SSP0->DMACR |= SSP0_DMA_ReceiveEnable;
    }
  }
  else 
  {
    if(SSP0_DMAtransfer == SSP0_DMA_Transmit) 
    {
      /* Disable DMA for the transmit FIFO */
      SSP0->DMACR &= SSP0_DMA_TransmitDisable;
    }
    else 
    {
      /* Disable DMA for the receive FIFO */
      SSP0->DMACR &= SSP0_DMA_ReceiveDisable;
    }
  }
}

/*******************************************************************************
* Function Name  : SSP_DMATxConfig
* Description    : Configures the SSP0 DMA transmit transfer.
* Input          : - SSP0_DMATxReq : specifies the SSP0 DMA transmit request to  
*                    be enabled. This parameter can be one of the following
*                    values:
*                         - SSP0_DMATxReq_Single: Transmit FIFO DMA single 
*                           request enabled
*                         - SSP0_DMATxReq_Burst: Transmit FIFO DMA burst request
*                           enabled
* Output         : None
* Return         : None
*******************************************************************************/
void SSP_DMATxConfig(u16 SSP0_DMATxReq)
{
  if(SSP0_DMATxReq == SSP0_DMATxReq_Burst) 
  {
    /* Enable DMA transmit burst request */
    SSP0->DMACR |= SSP0_DMATxReq_Burst;
  }
  else   
  {
    /* Enable DMA transmit single request */
    SSP0->DMACR &= SSP0_DMATxReq_Single;
  }
}

/*******************************************************************************
* Function Name  : SSP_DMARxConfig
* Description    : Configures the SSP0 DMA receive transfer.
* Input          : - SSP0_DMARxReq : specifies the SSP0 DMA receive request to  
*                    be enabled. This parameter can be one of the following
*                    values:
*                         - SSP0_DMARxReq_Single: Receive FIFO DMA burst request
*                           enabled
*                         - SSP0_DMARxReq_Burst: Receive FIFO DMA single request
*                          enabled
* Output         : None
* Return         : None
*******************************************************************************/
void SSP_DMARxConfig(u16 SSP0_DMARxReq)
{
  if(SSP0_DMARxReq == SSP0_DMARxReq_Burst) 
  {
    /* Enable DMA receive burst request */
    SSP0->DMACR |= SSP0_DMARxReq_Burst;
  }
  else   
  {
    /* Enable DMA receive single request */
    SSP0->DMACR &= SSP0_DMARxReq_Single;
  }  
}

/*******************************************************************************
* Function Name  : SSP_SendData
* Description    : Transmits a Data through the SSP peripheral.
* Input          : - SSPx: where x can be 0 or 1 to select the SSP peripheral.
*                  - Data : Data to be transmitted.
* Output         : None
* Return         : None
*******************************************************************************/
void SSP_SendData(SSP_TypeDef* SSPx, u16 Data)
{
  /* Write in the DR register the data to be sent */
  SSPx->DR = Data;
}

/*******************************************************************************
* Function Name  : SSP_ReceiveData
* Description    : Returns the most recent received data by the SSP peripheral.
* Input          : SSPx: where x can be 0 or 1 to select the SSP peripheral.
* Output         : None
* Return         : The value of the received data.
*******************************************************************************/
u16 SSP_ReceiveData(SSP_TypeDef* SSPx)
{
  /* Return the data in the DR register */	
  return SSPx->DR;
}

/*******************************************************************************
* Function Name  : SSP_LoopBackConfig
* Description    : Enables or disables the Loop back mode for the selected SSP
*                  peripheral.
* Input          : - SSPx: where x can be 0 or 1 to select the SSP peripheral.
*                  - NewState: new state of the Loop Back mode.
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void SSP_LoopBackConfig(SSP_TypeDef* SSPx, FunctionalState NewState)
{
  if(NewState == ENABLE)
  {
    /* Enable loop back mode */
    SSPx->CR1 |= SSP_LoopBackMode_Enable;
  }
  else
  {
    /* Disable loop back mode */
    SSPx->CR1 &= SSP_LoopBackMode_Disable;
  }
}

/*******************************************************************************
* Function Name  : SSP_NSSInternalConfig
* Description    : Configures by software the NSS pin.
* Input          : - SSPx: where x can be 0 or 1 to select the SSP peripheral.
*                  - SSP_NSSState: NSS internal state.This parameter can be one
*                    of the following values:
*                         - SSP_NSSInternal_Set: Set NSS pin internally
*                         - SSP_NSSInternal_Reset: Reset NSS pin internally
* Output         : None
* Return         : None
*******************************************************************************/
void SSP_NSSInternalConfig(SSP_TypeDef* SSPx, u16 SSP_NSSState)
{
  if(SSP_NSSState == SSP_NSSInternal_Set)
  {
    /* Set NSS pin internally */
    SSPx->CR1 |= SSP_NSSInternal_Set;
  }
  else
  {
    /* Reset NSS pin internally */
    SSPx->CR1 &= SSP_NSSInternal_Reset;
  }
}

/*******************************************************************************
* Function Name  : SSP_GetFlagStatus
* Description    : Checks whether the specified SSP flag is set or not.
* Input          : - SSPx: where x can be 0 or 1 to select the SSP peripheral.
*                  - SSP_FLAG: specifies the flag to check.  This parameter can 
*                    be one of the following values:
*                         - SSP_FLAG_Busy: busy flag
*                         - SSP_FLAG_RxFifoFull: Receive FIFO full flag
*                         - SSP_FLAG_RxFifoNotEmpty: Receive FIFO not empty flag 
*                         - SSP_FLAG_TxFifoNotFull: Transmit FIFO not full flag 
*                         - SSP_FLAG_TxFifoEmpty: Transmit FIFO empty flag 
*                         - SSP_FLAG_TxFifo: Transmit FIFO half empty or less flag
*                         - SSP_FLAG_RxFifo: Receive FIFO half full or less flag
*                         - SSP_FLAG_RxTimeOut: Receive timeout flag
*                         - SSP_FLAG_RxOverrun: Receive overrun flag
* Output         : None
* Return         : The new state of SSP_FLAG(SET or RESET).
*******************************************************************************/
FlagStatus SSP_GetFlagStatus(SSP_TypeDef* SSPx, u16 SSP_FLAG)
{
  u32 SSPReg = 0, FlagPos = 0;
  u32 StatusReg = 0;

  /* Get the SSP register index */
  SSPReg = SSP_FLAG >> 5;

  /* Get the flag position */
  FlagPos = SSP_FLAG & SSP_Flag_Mask;

  /* Find the register of the flag to check */
  if(SSPReg == 1) 
  {
    /* The flag to check is in SR register */
    StatusReg = SSPx->SR;  	
  }
  else if (SSPReg == 2) 
  {
    /* The flag to check is in RISR register */
    StatusReg = SSPx->RISR;
  }
  
  /* Check the status of the specified SSP flag */
  if((StatusReg & (1 << FlagPos)) != RESET)
  {
    /* Return SET if the SSP flag is set */
    return SET;
  }
  else
  {
    /* Return RESET if the SSP flag is reset */
    return RESET;
  }
}

/*******************************************************************************
* Function Name  : SSP_ClearFlag
* Description    : Clears the SSPx’s pending flags.
* Input          : - SSPx: where x can be 0 or 1 to select the SSP peripheral.
*                  - SSP_FLAG: specifies the flag to clear.  This parameter can  
*                    be one of the following values:
*                         - SSP_FLAG_RxTimeOut: Receive timeout flag 
*                         - SSP_FLAG_RxOverrun: Receive overrun flag 
* Output         : None
* Return         : None
*******************************************************************************/
void SSP_ClearFlag(SSP_TypeDef* SSPx, u16 SSP_FLAG)
{ 
  u8 FlagPos = 0;

  /* Get the flag position */
  FlagPos = SSP_FLAG & SSP_Flag_Mask;
  
  /* Clear the selected SSP flag */  
  SSPx->ICR = (1 << FlagPos);  
}

/*******************************************************************************
* Function Name  : SSP_GetITStatus
* Description    : Checks whether the specified SSP interrupt has occurred or not.
* Input          : - SSPx: where x can be 0 or 1 to select the SSP peripheral.
*                  - SSP_IT: specifies the interrupt source to check.   
*                    This parameter can be one of the following values:
*                         - SSP_IT_TxFifo: Transmit FIFO half empty or less interrupt 
*                         - SSP_IT_RxFifo: Receive FIFO half full or less interrupt 
*                         - SSP_IT_RxTimeOut: Receive timeout interrupt 
*                         - SSP_IT_RxOverrun: Receive overrun interrupt 
* Output         : None
* Return         : The new state of SSP_IT(SET or RESET).
*******************************************************************************/
ITStatus SSP_GetITStatus(SSP_TypeDef* SSPx, u16 SSP_IT)
{
  /* Check the status of the specified interrupt flag */
  if((SSPx->MISR & SSP_IT) != RESET)
  {
    /* Return SET if the SSP interrupt flag is set */
    return SET;
  }
  else
  {
    /* Return RESET if SSP interrupt flag is reset */
    return RESET;
  }
}

/*******************************************************************************
* Function Name  : SSP_ClearITPendingBit
* Description    : Clears the SSPx’s interrupt pending bits.
* Input          : - SSPx: where x can be 0 or 1 to select the SSP peripheral.
*                  - SSP_IT: specifies the interrupt pending bit to clear.  
*                    This parameter can be any combination of the following values:
*                         - SSP_IT_RxTimeOut: Receive timeout interrupt 
*                         - SSP_IT_RxOverrun: Receive overrun interrupt 
* Output         : None
* Return         : None
*******************************************************************************/
void SSP_ClearITPendingBit(SSP_TypeDef* SSPx, u16 SSP_IT)
{
  /* Clear the selected SSP interrupts pending bits */
  SSPx->ICR = SSP_IT;
}

/******************* (C) COPYRIGHT 2006 STMicroelectronics *****END OF FILE****/
