/******************** (C) COPYRIGHT 2006 STMicroelectronics ********************
* File Name          : 75x_dma.c
* Author             : MCD Application Team
* Date First Issued  : 03/10/2006 
* Description        : This file provides all the DMA software functions.
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
#include "75x_dma.h"
#include "75x_mrcc.h"

/* Private typedef -----------------------------------------------------------*/
/* Private define ------------------------------------------------------------*/
/* Private macro -------------------------------------------------------------*/
/* Private variables ---------------------------------------------------------*/

/* DMA enable */
#define DMA_Enable     0x0001
#define DMA_Disable    0xFFFE

/* DMA Last Buffer Sweep */
#define DMA_Last0_Enable_Mask    0x0001
#define DMA_Last0_Disable_Mask   0xFFFE
#define DMA_Last1_Enable_Mask    0x0002
#define DMA_Last1_Disable_Mask   0xFFFD
#define DMA_Last2_Enable_Mask    0x0004
#define DMA_Last2_Disable_Mask   0xFFFB
#define DMA_Last3_Enable_Mask    0x0008
#define DMA_Last3_Disable_Mask   0xFFF7

/* DMA Masks */
#define DMA_Stream0_MASK_Mask  0xFFEE
#define DMA_Stream0_CLR_Mask   0x0011
#define DMA_Stream0_LAST_Mask  0xFFFE

#define DMA_Stream1_MASK_Mask  0xFFDD
#define DMA_Stream1_CLR_Mask   0x0022
#define DMA_Stream1_LAST_Mask  0xFFFD

#define DMA_Stream2_MASK_Mask  0xFFBB
#define DMA_Stream2_CLR_Mask   0x0044
#define DMA_Stream2_LAST_Mask  0xFFFB

#define DMA_Stream3_MASK_Mask  0xFF77
#define DMA_Stream3_CLR_Mask   0x0088
#define DMA_Stream3_LAST_Mask  0xFFF7

#define DMA_SRCSize_Mask   0xFFE7
#define DMA_SRCBurst_Mask  0xFF9F
#define DMA_DSTSize_Mask   0xFE7F     

/* Private function prototypes -----------------------------------------------*/
/* Private functions ---------------------------------------------------------*/
/*******************************************************************************
* Function Name  : DMA_DeInit
* Description    : Deinitializes the DMA streamx registers to their default reset
*                  values.
* Input          : - DMA_Streamx: where x can be 0, 1, 2 or 3 to select the DMA
*                    Stream.
* Output         : None
* Return         : None
*******************************************************************************/
void DMA_DeInit(DMA_Stream_TypeDef* DMA_Streamx)
{
  /* Reset streamx source base address register */
  DMA_Streamx->SOURCEL = 0;
  DMA_Streamx->SOURCEH = 0;

  /* Reset streamx destination base address register */
  DMA_Streamx->DESTL = 0;
  DMA_Streamx->DESTH = 0;

  /* Reset streamx maximum count register */
  DMA_Streamx->MAX  = 0;
  /* Reset streamx control register */
  DMA_Streamx->CTRL = 0;
  /* Reset streamx last used buffer location register */
  DMA_Streamx->LUBUFF = 0;

  switch(*(u32*)&DMA_Streamx)
  {
    case DMA_Stream0_BASE:
      /* Reset interrupt mask, clear and flag bits for stream0 */
      DMA->MASK &= DMA_Stream0_MASK_Mask;
      DMA->CLR |= DMA_Stream0_CLR_Mask;
      DMA->LAST &= DMA_Stream0_LAST_Mask;
      break;

    case DMA_Stream1_BASE:
      /* Reset interrupt mask, clear and flag bits for stream1 */
      DMA->MASK &= DMA_Stream1_MASK_Mask;
      DMA->CLR |= DMA_Stream1_CLR_Mask;
      DMA->LAST &= DMA_Stream1_LAST_Mask;
      break;

    case DMA_Stream2_BASE:
    /* Reset interrupt mask, clear and flag bits for stream2 */
      DMA->MASK &= DMA_Stream2_MASK_Mask;
      DMA->CLR |= DMA_Stream2_CLR_Mask;
      DMA->LAST &= DMA_Stream2_LAST_Mask;
      break;

    case DMA_Stream3_BASE:
      /* Reset interrupt mask, clear and flag bits for stream3 */
      DMA->MASK &= DMA_Stream3_MASK_Mask;
      DMA->CLR |= DMA_Stream3_CLR_Mask;
      DMA->LAST &= DMA_Stream3_LAST_Mask;
      break;
      
    default:
      break;
  }
}

/*******************************************************************************
* Function Name  : DMA_Init
* Description    : Initializes the DMAx stream according to the specified
*                  parameters in the DMA_InitStruct.
* Input          : - DMA_Streamx: where x can be 0, 1, 2 or 3 to select the DMA
*                    Stream.
*                  - DMA_InitStruct: pointer to a DMA_InitTypeDef structure that
*                    contains the configuration information for the specified
*                    DMA stream.
* Output         : None
* Return         : None
******************************************************************************/
void DMA_Init(DMA_Stream_TypeDef*  DMA_Streamx, DMA_InitTypeDef* DMA_InitStruct)
{
  /* set the buffer Size */
   DMA_Streamx->MAX = DMA_InitStruct->DMA_BufferSize ;

  /* Configure the incrementation of the current source Register */
  if(DMA_InitStruct->DMA_SRC == DMA_SRC_INCR)
  {
    /* Increment current source register */
    DMA_Streamx->CTRL |= DMA_SRC_INCR;
  }
  else 
  {
    /* Current source register unchanged */
    DMA_Streamx->CTRL &= DMA_SRC_NOT_INCR;
  }
  
  /* Configure the incrementation of the current destination Register */
  if(DMA_InitStruct->DMA_DST == DMA_DST_INCR)
  {
    /* Increment current source register */
    DMA_Streamx->CTRL |= DMA_DST_INCR;
  }
  else 
  {
    /* Current source register unchanged */
    DMA_Streamx->CTRL &= DMA_DST_NOT_INCR;
  }
  
  /* Clear source to DMA data width SOSIZE[1:0] bits */
  DMA_Streamx->CTRL &= DMA_SRCSize_Mask;
  /* Set the source to DMA data width */
  DMA_Streamx->CTRL |= DMA_InitStruct->DMA_SRCSize;
  
  /* Clear the DMA peripheral burst size SOBURST[1:0] bits */
  DMA_Streamx->CTRL &= DMA_SRCBurst_Mask;
  /* Set the DMA peripheral burst size */
  DMA_Streamx->CTRL |= DMA_InitStruct->DMA_SRCBurst;
  
  /* Clear destination to DMA dat width DESIZE[1:0] bits */
  DMA_Streamx->CTRL &= DMA_DSTSize_Mask;
  /* Set the destination to DMA data width */
  DMA_Streamx->CTRL |= DMA_InitStruct->DMA_DSTSize;
  
  /* Configure the circular mode */
  if(DMA_InitStruct->DMA_Mode == DMA_Mode_Circular)
  {
    /* Set circular mode */
    DMA_Streamx->CTRL |= DMA_Mode_Circular;
  }
  else 
  {
    /* Set normal mode */
    DMA_Streamx->CTRL &= DMA_Mode_Normal;
  } 
  
  /* Configure the direction transfer */
  if(DMA_InitStruct->DMA_DIR == DMA_DIR_PeriphDST)
  {
    /* Set peripheral as destination */
    DMA_Streamx->CTRL |= DMA_DIR_PeriphDST;
  }
  else 
  {
    /* Set peripheral as source */
    DMA_Streamx->CTRL &= DMA_DIR_PeriphSRC;
  } 
  
  /* Configure the memory to memory transfer only for stream3 */
  if(DMA_Streamx == DMA_Stream3)
  {
    if(DMA_InitStruct->DMA_M2M == DMA_M2M_Enable)
    {
      /* Enable memory to memory transfer for stream3 */
      DMA_Streamx->CTRL |= DMA_M2M_Enable;
    }
    else 
    {
      /* Disable memory to memory transfer for stream3 */
      DMA_Streamx->CTRL &= DMA_M2M_Disable;
    } 	
  }

  /* Configure the source base address */
  DMA_Streamx->SOURCEL = DMA_InitStruct->DMA_SRCBaseAddr;
  DMA_Streamx->SOURCEH = DMA_InitStruct->DMA_SRCBaseAddr >> 16;

  /* Configure the destination base address */
  DMA_Streamx->DESTL = DMA_InitStruct->DMA_DSTBaseAddr;
  DMA_Streamx->DESTH = DMA_InitStruct->DMA_DSTBaseAddr >> 16;
}

/*******************************************************************************
* Function Name  : DMA_StructInit
* Description    : Fills each DMA_InitStruct member with its default value.
* Input          : DMA_InitStruct : pointer to a DMA_InitTypeDef structure
*                  which will be initialized.
* Output         : None
* Return         : None
*******************************************************************************/
void DMA_StructInit(DMA_InitTypeDef* DMA_InitStruct)
{
  /* Initialize the DMA_BufferSize member */
  DMA_InitStruct->DMA_BufferSize = 0;

  /* initialize the DMA_SRCBaseAddr member */
  DMA_InitStruct->DMA_SRCBaseAddr = 0;

  /* Initialize the DMA_DSTBaseAddr member */
  DMA_InitStruct ->DMA_DSTBaseAddr = 0;
  
  /* Initialize the DMA_SRC member */
  DMA_InitStruct->DMA_SRC = DMA_SRC_NOT_INCR;
  
  /* Initialize the DMA_DST member */
  DMA_InitStruct->DMA_DST = DMA_DST_NOT_INCR;
  
  /* Initialize the DMA_SRCSize member */
  DMA_InitStruct->DMA_SRCSize = DMA_SRCSize_Byte;
  
  /* Initialize the DMA_SRCBurst member */
  DMA_InitStruct->DMA_SRCBurst = DMA_SRCBurst_1Data;
  
  /* Initialize the DMA_DSTSize member */
  DMA_InitStruct->DMA_DSTSize = DMA_DSTSize_Byte;
  
  /* Initialize the DMA_Mode member */
  DMA_InitStruct->DMA_Mode = DMA_Mode_Normal;
  
  /* Initialize the DMA_M2M member */
  DMA_InitStruct->DMA_M2M =  DMA_M2M_Disable;

  /* Initialize the DMA_DIR member */
  DMA_InitStruct->DMA_DIR = DMA_DIR_PeriphSRC;
}

/*******************************************************************************
* Function Name  : DMA_Cmd
* Description    : Enables or disables the specified DMA stream.
* Input          : - DMA_Streamx: where x can be 0, 1, 2 or 3 to select the DMA
*                    Stream.
*                  - NewState: new state of the DMAx stream. This parameter can
*                  be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void DMA_Cmd(DMA_Stream_TypeDef*  DMA_Streamx, FunctionalState NewState)
{
  if(NewState == ENABLE)
  {
    /* Enable the selected DMA streamx */
    DMA_Streamx->CTRL |= DMA_Enable;
  }
  else
  {
    /* Disable the selected DMA streamx */
    DMA_Streamx->CTRL &= DMA_Disable;
  }
}

/*******************************************************************************
* Function Name  : DMA_ITConfig
* Description    : Enables or disables the specified DMA interrupts.
* Input          : - DMA_IT: specifies the DMA interrupts sources to be enabled
*                    or disabled. This parameter can be any combination of the
*                    following values:
*                         - DMA_IT_SI0: Stream0 transfer end interrupt mask
*                         - DMA_IT_SI1: Stream1 transfer end interrupt mask
*                         - DMA_IT_SI2: Stream2 transfer end interrupt mask
*                         - DMA_IT_SI3: Stream3 transfer end interrupt mask
*                         - DMA_IT_SE0: Stream0 transfer error interrupt mask
*                         - DMA_IT_SE1: Stream1 transfer error interrupt mask
*                         - DMA_IT_SE2: Stream2 transfer error interrupt mask
*                         - DMA_IT_SE3: Stream3 transfer error interrupt mask
*                         - DMA_IT_ALL: ALL DMA interrupts mask
*                  - NewState: new state of the specified DMA interrupts.
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void DMA_ITConfig(u16 DMA_IT, FunctionalState NewState)
{
  if(NewState == ENABLE)
  {
    /* Enable the selected DMA interrupts */
    DMA->MASK |= DMA_IT;
  }
  else
  {
    /* Disable the selected DMA interrupts */
    DMA->MASK &= ~DMA_IT;
  }
}

/*******************************************************************************
* Function Name  : DMA_GetCurrDSTAddr
* Description    : Returns the current value of the destination address pointer
*                  related to the specified DMA stream.
* Input          : - DMA_Streamx: where x can be 0, 1, 2 or 3 to select the DMA
*                    Stream.
* Output         : None
* Return         : The current value of the destination address pointer related
*                  to the specified DMA stream.
*******************************************************************************/
u32 DMA_GetCurrDSTAddr(DMA_Stream_TypeDef*  DMA_Streamx)
{ 
  u32 Tmp = 0;

  /* Get high current destination address */
  Tmp = (DMA_Streamx->DECURRH)<<16;
  /* Get low current destination address */
  Tmp |= DMA_Streamx->DECURRL;

  /* Return the current destination address value for streamx */
  return Tmp;
}

/*******************************************************************************
* Function Name  : DMA_GetCurrSRCAddr
* Description    : Returns the current value of the source address pointer
*                  related to the specified DMA stream.
* Input          : - DMA_Streamx: where x can be 0, 1, 2 or 3 to select the DMA
*                    Stream.
* Output         : None
* Return         : The current value of the source address pointer related to
*                  the specified DMA stream.
*******************************************************************************/
u32 DMA_GetCurrSRCAddr(DMA_Stream_TypeDef*  DMA_Streamx)
{
  u32 Tmp = 0;

  /* Get high current source address */
  Tmp = (DMA_Streamx->SOCURRH)<<16;
  /* Get slow current source address */
  Tmp |= DMA_Streamx->SOCURRL;

  /* Return the current source address value for streamx */
  return Tmp;
}

/*******************************************************************************
* Function Name  : DMA_GetTerminalCounter
* Description    : Returns the number of data units remaining in the current
*                  DMA stream transfer.
* Input          : - DMA_Streamx: where x can be 0, 1, 2 or 3 to select the DMA
*                    Stream.
* Output         : None
* Return         : The number of data units remaining in the current DMA stream
*                  transfer.
*******************************************************************************/
u16 DMA_GetTerminalCounter(DMA_Stream_TypeDef*  DMA_Streamx)
{
  /* Return the terminal counter value for streamx */
  return(DMA_Streamx->TCNT);
}

/*******************************************************************************
* Function Name  : DMA_LastBufferSweepConfig
* Description    : Activates or disactivates the last buffer sweep mode for the 
*                  DMA streamx configured in circular buffer mode.
* Input          : - DMA_Streamx: where x can be 0, 1, 2 or 3 to select the DMA
*                    Stream.
*                  - NewState: new state of the Last buffer sweep DMA_Streamx.                 
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void DMA_LastBufferSweepConfig(DMA_Stream_TypeDef* DMA_Streamx, FunctionalState NewState)
{  
  switch(*(u32*)&DMA_Streamx)
  {
    case DMA_Stream0_BASE:
      if(NewState == ENABLE)
      {
        /* Activates the last circular buffer sweep mode for stream0 */
        DMA->LAST |= DMA_Last0_Enable_Mask;
      }
      else
      {
        /* Disactivates the last circular buffer sweep mode for stream0 */
        DMA->LAST &= DMA_Last0_Disable_Mask;
      }	
      break;

    case DMA_Stream1_BASE:
      if(NewState == ENABLE)
      {
        /* Activates the last circular buffer sweep mode for stream1 */
        DMA->LAST |= DMA_Last1_Enable_Mask;
      }
      else
      {
        /* Disactivates the last circular buffer sweep mode for stream1 */
        DMA->LAST &= DMA_Last1_Disable_Mask;
      }	
      break;

    case DMA_Stream2_BASE:
      if(NewState == ENABLE)
      {
        /* Activates the last circular buffer sweep mode for stream2 */
        DMA->LAST |= DMA_Last2_Enable_Mask;
      }
      else
      {
        /* Disactivates the last circular buffer sweep mode for stream2 */
        DMA->LAST &= DMA_Last2_Disable_Mask;
      }	
      break;

    case DMA_Stream3_BASE:
      if(NewState == ENABLE)
      {
        /* Activates the last circular buffer sweep mode for stream3 */
        DMA->LAST |= DMA_Last3_Enable_Mask;
      }
      else
      {
        /* Disactivates the last circular buffer sweep mode for stream3 */
        DMA->LAST &= DMA_Last3_Disable_Mask;
      }	
      break;
    
    default:
      break;      
  }
}

/*******************************************************************************
* Function Name  : DMA_LastBufferAddrConfig
* Description    : Configures the circular buffer position where the last data 
*                  to be used by the specified DMA stream is located.
* Input          : - DMA_Streamx: where x can be 0, 1, 2 or 3 to select the DMA
*                    Stream.
*                  - DMA_LastBufferAddr: specifies the circular buffer position
*                    where the last data to be used by the specified DMA stream
*                    is located.
*                    This member must be a number between 0 and the stream BufferSize-1.
* Output         : None
* Return         : None
*******************************************************************************/
void DMA_LastBufferAddrConfig(DMA_Stream_TypeDef*  DMA_Streamx, u16 DMA_LastBufferAddr)
{
  /* Set the streamx last data circular buffer location */
  DMA_Streamx->LUBUFF = DMA_LastBufferAddr;
}

/*******************************************************************************
* Function Name  : DMA_GetFlagStatus
* Description    : Checks whether the specified DMA flag is set or not.
* Input          : - DMA_FLAG: specifies the flag to check. This parameter can 
*                    be one of the following values:
*                         - DMA_FLAG_SI0:  Stream0 transfer end flag.
*                         - DMA_FLAG_SI1:  Stream1 transfer end flag.
*                         - DMA_FLAG_SI2:  Stream2 transfer end flag.
*                         - DMA_FLAG_SI3:  Stream3 transfer end flag.
*                         - DMA_FLAG_SE0:  Stream0 transfer error flag.
*                         - DMA_FLAG_SE1:  Stream1 transfer error flag.
*                         - DMA_FLAG_SE2:  Stream2 transfer error flag.
*                         - DMA_FLAG_SE3:  Stream3 transfer error flag.
*                         - DMA_FLAG_ACT0: Stream0 status.
*                         - DMA_FLAG_ACT1: Stream1 status.
*                         - DMA_FLAG_ACT2: Stream2 status.
*                         - DMA_FLAG_ACT3: Stream3 status.
* Output         : None
* Return         : The new state of DMA_FLAG (SET or RESET).
*******************************************************************************/
FlagStatus DMA_GetFlagStatus(u16 DMA_FLAG)
{
  /* Check the status of the specified DMA flag */
  if((DMA->STATUS & DMA_FLAG) != RESET)
  {
    /* Return SET if DMA_FLAG is set */
    return SET;
  }
  else
  {
    /* Return RESET if DMA_FLAG is reset */
    return RESET;
  }
}

/*******************************************************************************
* Function Name  : DMA_ClearFlag
* Description    : Clears the DMA’s pending flags.
* Input          : - DMA_FLAG: specifies the flag to clear. This parameter can 
*                    be any combination of the following values:
*                         - DMA_FLAG_SI0:  Stream0 transfer end flag.
*                         - DMA_FLAG_SI1:  Stream1 transfer end flag.
*                         - DMA_FLAG_SI2:  Stream2 transfer end flag.
*                         - DMA_FLAG_SI3:  Stream3 transfer end flag.
*                         - DMA_FLAG_SE0:  Stream0 transfer error flag.
*                         - DMA_FLAG_SE1:  Stream1 transfer error flag.
*                         - DMA_FLAG_SE2:  Stream2 transfer error flag.
*                         - DMA_FLAG_SE3:  Stream3 transfer error flag.
* Output         : None
* Return         : None
*******************************************************************************/
void DMA_ClearFlag(u16 DMA_FLAG)
{
  /* Clear the selected DMA flags */ 
  DMA->CLR = DMA_FLAG ;
}

/*******************************************************************************
* Function Name  : DMA_GetITStatus
* Description    : Checks whether the specified DMA interrupt has occured or not.
* Input          : - DMA_IT: specifies the DMA interrupt source to check.  
*                    This parameter can be one of the following values:
*                         - DMA_IT_SI0: Stream0 transfer end interrupt 
*                         - DMA_IT_SI1: Stream1 transfer end interrupt 
*                         - DMA_IT_SI2: Stream2 transfer end interrupt 
*                         - DMA_IT_SI3: Stream3 transfer end interrupt 
*                         - DMA_IT_SE0: Stream0 transfer error interrupt 
*                         - DMA_IT_SE1: Stream1 transfer error interrupt 
*                         - DMA_IT_SE2: Stream2 transfer error interrupt 
*                         - DMA_IT_SE3: Stream3 transfer error interrupt 
* Output         : None
* Return         : The new state of DMA_IT (SET or RESET).
*******************************************************************************/
ITStatus DMA_GetITStatus(u16 DMA_IT)
{
  /* Check the status of the specified DMA interrupt */
  if((DMA->STATUS & DMA_IT) != RESET)
  {
    /* Return SET if the DMA interrupt flag is set */
    return SET;
  }
  else
  {
    /* Return RESET if the DMA interrupt flag is reset */
    return RESET;
  }
}

/*******************************************************************************
* Function Name  : DMA_ClearITPendingBit
* Description    : Clears the DMA’s interrupt pending bits. 
* Input          : - DMA_IT: specifies the interrupt pending bit to clear.  
*                    This parameter can be any combination of the following values:
*                         - DMA_IT_SI0:  Stream0 transfer end interrupt.
*                         - DMA_IT_SI1:  Stream1 transfer end interrupt.
*                         - DMA_IT_SI2:  Stream2 transfer end interrupt.
*                         - DMA_IT_SI3:  Stream3 transfer end interrupt.
*                         - DMA_IT_SE0:  Stream0 transfer error interrupt.
*                         - DMA_IT_SE1:  Stream1 transfer error interrupt.
*                         - DMA_IT_SE2:  Stream2 transfer error interrupt.
*                         - DMA_IT_SE3:  Stream3 transfer error interrupt.
*                         - DMA_IT_ALL:  All DMA interrupts.
* Output         : None
* Return         : None
*******************************************************************************/
void DMA_ClearITPendingBit(u16 DMA_IT)
{
  /* Clear the selected DMA interrupts pending bits */
  DMA->CLR = DMA_IT ;
}

/******************* (C) COPYRIGHT 2006 STMicroelectronics *****END OF FILE****/
