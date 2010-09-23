/******************** (C) COPYRIGHT 2007 STMicroelectronics ********************
* File Name          : stm32f10x_dma.c
* Author             : MCD Application Team
* Date First Issued  : 09/29/2006
* Description        : This file provides all the DMA firmware functions.
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

/* Includes ------------------------------------------------------------------*/
#include "stm32f10x_dma.h"
#include "stm32f10x_rcc.h"

/* Private typedef -----------------------------------------------------------*/
/* Private define ------------------------------------------------------------*/
/* DMA ENABLE mask */
#define CCR_ENABLE_Set          ((u32)0x00000001)
#define CCR_ENABLE_Reset        ((u32)0xFFFFFFFE)

/* DMA Channelx interrupt pending bit masks */
#define DMA_Channel1_IT_Mask    ((u32)0x0000000F)
#define DMA_Channel2_IT_Mask    ((u32)0x000000F0)
#define DMA_Channel3_IT_Mask    ((u32)0x00000F00)
#define DMA_Channel4_IT_Mask    ((u32)0x0000F000)
#define DMA_Channel5_IT_Mask    ((u32)0x000F0000)
#define DMA_Channel6_IT_Mask    ((u32)0x00F00000)
#define DMA_Channel7_IT_Mask    ((u32)0x0F000000)

/* DMA registers Masks */
#define CCR_CLEAR_Mask          ((u32)0xFFFF800F)

/* Private macro -------------------------------------------------------------*/
/* Private variables ---------------------------------------------------------*/
/* Private function prototypes -----------------------------------------------*/
/* Private functions ---------------------------------------------------------*/

/*******************************************************************************
* Function Name  : DMA_DeInit
* Description    : Deinitializes the DMA Channelx registers to their default reset
*                  values.
* Input          : - DMA_Channelx: where x can be 1, 2 to 7 to select the DMA
*                    Channel.
* Output         : None
* Return         : None
*******************************************************************************/
void DMA_DeInit(DMA_Channel_TypeDef* DMA_Channelx)
{
  /* DMA Channelx disable */
  DMA_Cmd(DMA_Channelx, DISABLE);

  /* Reset Channelx control register */
  DMA_Channelx->CCR  = 0;
  
  /* Reset Channelx remaining bytes register */
  DMA_Channelx->CNDTR = 0;
  
  /* Reset Channelx peripheral address register */
  DMA_Channelx->CPAR  = 0;
  
  /* Reset Channelx memory address register */
  DMA_Channelx->CMAR = 0;

  switch (*(u32*)&DMA_Channelx)
  {
    case DMA_Channel1_BASE:
      /* Reset interrupt pending bits for Channel1 */
      DMA->IFCR |= DMA_Channel1_IT_Mask;
      break;

    case DMA_Channel2_BASE:
      /* Reset interrupt pending bits for Channel2 */
      DMA->IFCR |= DMA_Channel2_IT_Mask;
      break;

    case DMA_Channel3_BASE:
      /* Reset interrupt pending bits for Channel3 */
      DMA->IFCR |= DMA_Channel3_IT_Mask;
      break;

    case DMA_Channel4_BASE:
      /* Reset interrupt pending bits for Channel4 */
      DMA->IFCR |= DMA_Channel4_IT_Mask;
      break;

    case DMA_Channel5_BASE:
      /* Reset interrupt pending bits for Channel5 */
      DMA->IFCR |= DMA_Channel5_IT_Mask;
      break;

    case DMA_Channel6_BASE:
      /* Reset interrupt pending bits for Channel6 */
      DMA->IFCR |= DMA_Channel6_IT_Mask;
      break;

    case DMA_Channel7_BASE:
      /* Reset interrupt pending bits for Channel7 */
      DMA->IFCR |= DMA_Channel7_IT_Mask;
      break;

    default:
      break;
  }
}

/*******************************************************************************
* Function Name  : DMA_Init
* Description    : Initializes the DMA Channelx according to the specified
*                  parameters in the DMA_InitStruct.
* Input          : - DMA_Channelx: where x can be 1, 2 to 7 to select the DMA
*                    Channel.
*                  - DMA_InitStruct: pointer to a DMA_InitTypeDef structure that
*                    contains the configuration information for the specified
*                    DMA Channel.
* Output         : None
* Return         : None
******************************************************************************/
void DMA_Init(DMA_Channel_TypeDef* DMA_Channelx, DMA_InitTypeDef* DMA_InitStruct)
{
  u32 tmpreg = 0;

  /* Check the parameters */
  assert(IS_DMA_DIR(DMA_InitStruct->DMA_DIR));
  assert(IS_DMA_BUFFER_SIZE(DMA_InitStruct->DMA_BufferSize));	   
  assert(IS_DMA_PERIPHERAL_INC_STATE(DMA_InitStruct->DMA_PeripheralInc));  
  assert(IS_DMA_MEMORY_INC_STATE(DMA_InitStruct->DMA_MemoryInc));   
  assert(IS_DMA_PERIPHERAL_DATA_SIZE(DMA_InitStruct->DMA_PeripheralDataSize));
  assert(IS_DMA_MEMORY_DATA_SIZE(DMA_InitStruct->DMA_MemoryDataSize));
  assert(IS_DMA_MODE(DMA_InitStruct->DMA_Mode));
  assert(IS_DMA_PRIORITY(DMA_InitStruct->DMA_Priority));
  assert(IS_DMA_M2M_STATE(DMA_InitStruct->DMA_M2M));

/*--------------------------- DMA Channelx CCR Configuration -----------------*/
  /* Get the DMA_Channelx CCR value */
  tmpreg = DMA_Channelx->CCR;
  /* Clear MEM2MEM, PL, MSIZE, PSIZE, MINC, PINC, CIRCULAR and DIR bits */
  tmpreg &= CCR_CLEAR_Mask;
  /* Configure DMA Channelx: data transfer, data size, priority level and mode */
  /* Set DIR bit according to DMA_DIR value */
  /* Set CIRCULAR bit according to DMA_Mode value */
  /* Set PINC bit according to DMA_PeripheralInc value */
  /* Set MINC bit according to DMA_MemoryInc value */
  /* Set PSIZE bits according to DMA_PeripheralDataSize value */
  /* Set MSIZE bits according to DMA_MemoryDataSize value */
  /* Set PL bits according to DMA_Priority value */
  /* Set the MEM2MEM bit according to DMA_M2M value */
  tmpreg |= DMA_InitStruct->DMA_DIR | DMA_InitStruct->DMA_Mode |
            DMA_InitStruct->DMA_PeripheralInc | DMA_InitStruct->DMA_MemoryInc |
            DMA_InitStruct->DMA_PeripheralDataSize | DMA_InitStruct->DMA_MemoryDataSize |
            DMA_InitStruct->DMA_Priority | DMA_InitStruct->DMA_M2M;
  /* Write to DMA Channelx CCR */
  DMA_Channelx->CCR = tmpreg;

/*--------------------------- DMA Channelx CNBTR Configuration ---------------*/
  /* Write to DMA Channelx CNBTR */
  DMA_Channelx->CNDTR = DMA_InitStruct->DMA_BufferSize;

/*--------------------------- DMA Channelx CPAR Configuration ----------------*/
  /* Write to DMA Channelx CPAR */
  DMA_Channelx->CPAR = DMA_InitStruct->DMA_PeripheralBaseAddr;

/*--------------------------- DMA Channelx CMAR Configuration ----------------*/
  /* Write to DMA Channelx CMAR */
  DMA_Channelx->CMAR = DMA_InitStruct->DMA_MemoryBaseAddr;
}

/*******************************************************************************
* Function Name  : DMA_StructInit
* Description    : Fills each DMA_InitStruct member with its default value.
* Input          : - DMA_InitStruct : pointer to a DMA_InitTypeDef structure
*                    which will be initialized.
* Output         : None
* Return         : None
*******************************************************************************/
void DMA_StructInit(DMA_InitTypeDef* DMA_InitStruct)
{
/*-------------- Reset DMA init structure parameters values ------------------*/
  /* Initialize the DMA_PeripheralBaseAddr member */
  DMA_InitStruct->DMA_PeripheralBaseAddr = 0;

  /* Initialize the DMA_MemoryBaseAddr member */
  DMA_InitStruct->DMA_MemoryBaseAddr = 0;

  /* Initialize the DMA_DIR member */
  DMA_InitStruct->DMA_DIR = DMA_DIR_PeripheralSRC;

  /* Initialize the DMA_BufferSize member */
  DMA_InitStruct->DMA_BufferSize = 0;

  /* Initialize the DMA_PeripheralInc member */
  DMA_InitStruct->DMA_PeripheralInc = DMA_PeripheralInc_Disable;

  /* Initialize the DMA_MemoryInc member */
  DMA_InitStruct->DMA_MemoryInc = DMA_MemoryInc_Disable;

  /* Initialize the DMA_PeripheralDataSize member */
  DMA_InitStruct->DMA_PeripheralDataSize = DMA_PeripheralDataSize_Byte;

  /* Initialize the DMA_MemoryDataSize member */
  DMA_InitStruct->DMA_MemoryDataSize = DMA_MemoryDataSize_Byte;

  /* Initialize the DMA_Mode member */
  DMA_InitStruct->DMA_Mode = DMA_Mode_Normal;

  /* Initialize the DMA_Priority member */
  DMA_InitStruct->DMA_Priority = DMA_Priority_Low;

  /* Initialize the DMA_M2M member */
  DMA_InitStruct->DMA_M2M = DMA_M2M_Disable;
}

/*******************************************************************************
* Function Name  : DMA_Cmd
* Description    : Enables or disables the specified DMA Channel.
* Input          : - DMA_Channelx: where x can be 1, 2 to 7 to select the DMA
*                    Channel.
*                  - NewState: new state of the DMAx Channel. 
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void DMA_Cmd(DMA_Channel_TypeDef*  DMA_Channelx, FunctionalState NewState)
{
  /* Check the parameters */
  assert(IS_FUNCTIONAL_STATE(NewState));

  if (NewState != DISABLE)
  {
    /* Enable the selected DMA Channelx */
    DMA_Channelx->CCR |= CCR_ENABLE_Set;
  }
  else
  {
    /* Disable the selected DMA Channelx */
    DMA_Channelx->CCR &= CCR_ENABLE_Reset;
  }
}

/*******************************************************************************
* Function Name  : DMA_ITConfig
* Description    : Enables or disables the specified DMA interrupts.
* Input          : - DMA_IT: specifies the DMA interrupts sources to be enabled
*                    or disabled. 
*                    This parameter can be any combination of the following values:
*                       - DMA_IT_TC:  Transfer complete interrupt mask
*                       - DMA_IT_HT:  Half transfer interrupt mask
*                       - DMA_IT_TE:  Transfer error interrupt mask
*                  - NewState: new state of the specified DMA interrupts.
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void DMA_ITConfig(DMA_Channel_TypeDef* DMA_Channelx, u32 DMA_IT, FunctionalState NewState)
{
  /* Check the parameters */
  assert(IS_DMA_CONFIG_IT(DMA_IT));
  assert(IS_FUNCTIONAL_STATE(NewState));

  if (NewState != DISABLE)
  {
    /* Enable the selected DMA interrupts */
    DMA_Channelx->CCR |= DMA_IT;
  }
  else
  {
    /* Disable the selected DMA interrupts */
    DMA_Channelx->CCR &= ~DMA_IT;
  }
}

/*******************************************************************************
* Function Name  : DMA_GetCurrDataCounter
* Description    : Returns the number of remaining data units in the current
*                  DMA Channel transfer.
* Input          : - DMA_Channelx: where x can be 1, 2 to 7 to select the DMA
*                    Channel.
* Output         : None
* Return         : The number of remaining data units in the current DMA Channel
*                  transfer..
*******************************************************************************/
u16 DMA_GetCurrDataCounter(DMA_Channel_TypeDef*  DMA_Channelx)
{
  /* Return the current memory address value for Channelx */
  return ((u16)(DMA_Channelx->CNDTR));
}

/*******************************************************************************
* Function Name  : DMA_GetFlagStatus
* Description    : Checks whether the specified DMA flag is set or not.
* Input          : - DMA_FLAG: specifies the flag to check. 
*                    This parameter can be one of the following values:
*                       - DMA_FLAG_GL1: Channel1 global flag.
*                       - DMA_FLAG_TC1: Channel1 transfer complete flag.
*                       - DMA_FLAG_HT1: Channel1 half transfer flag.
*                       - DMA_FLAG_TE1: Channel1 transfer error flag.
*                       - DMA_FLAG_GL2: Channel2 global flag.
*                       - DMA_FLAG_TC2: Channel2 transfer complete flag.
*                       - DMA_FLAG_HT2: Channel2 half transfer flag.
*                       - DMA_FLAG_TE2: Channel2 transfer error flag.
*                       - DMA_FLAG_GL3: Channel3 global flag.
*                       - DMA_FLAG_TC3: Channel3 transfer complete flag.
*                       - DMA_FLAG_HT3: Channel3 half transfer flag.
*                       - DMA_FLAG_TE3: Channel3 transfer error flag.
*                       - DMA_FLAG_GL4: Channel4 global flag.
*                       - DMA_FLAG_TC4: Channel4 transfer complete flag.
*                       - DMA_FLAG_HT4: Channel4 half transfer flag.
*                       - DMA_FLAG_TE4: Channel4 transfer error flag.
*                       - DMA_FLAG_GL5: Channel5 global flag.
*                       - DMA_FLAG_TC5: Channel5 transfer complete flag.
*                       - DMA_FLAG_HT5: Channel5 half transfer flag.
*                       - DMA_FLAG_TE5: Channel5 transfer error flag.
*                       - DMA_FLAG_GL6: Channel6 global flag.
*                       - DMA_FLAG_TC6: Channel6 transfer complete flag.
*                       - DMA_FLAG_HT6: Channel6 half transfer flag.
*                       - DMA_FLAG_TE6: Channel6 transfer error flag.
*                       - DMA_FLAG_GL7: Channel7 global flag.
*                       - DMA_FLAG_TC7: Channel7 transfer complete flag.
*                       - DMA_FLAG_HT7: Channel7 half transfer flag.
*                       - DMA_FLAG_TE7: Channel7 transfer error flag.
* Output         : None
* Return         : The new state of DMA_FLAG (SET or RESET).
*******************************************************************************/
FlagStatus DMA_GetFlagStatus(u32 DMA_FLAG)
{
  FlagStatus bitstatus = RESET;

  /* Check the parameters */
  assert(IS_DMA_GET_FLAG(DMA_FLAG));

  /* Check the status of the specified DMA flag */
  if ((DMA->ISR & DMA_FLAG) != (u32)RESET)
  {
    /* DMA_FLAG is set */
    bitstatus = SET;
  }
  else
  {
    /* DMA_FLAG is reset */
    bitstatus = RESET;
  }
  /* Return the DMA_FLAG status */
  return  bitstatus;
}

/*******************************************************************************
* Function Name  : DMA_ClearFlag
* Description    : Clears the DMA's pending flags.
* Input          : - DMA_FLAG: specifies the flag to clear. 
*                    This parameter can be any combination of the following values:
*                       - DMA_FLAG_GL1: Channel1 global flag.
*                       - DMA_FLAG_TC1: Channel1 transfer complete flag.
*                       - DMA_FLAG_HT1: Channel1 half transfer flag.
*                       - DMA_FLAG_TE1: Channel1 transfer error flag.
*                       - DMA_FLAG_GL2: Channel2 global flag.
*                       - DMA_FLAG_TC2: Channel2 transfer complete flag.
*                       - DMA_FLAG_HT2: Channel2 half transfer flag.
*                       - DMA_FLAG_TE2: Channel2 transfer error flag.
*                       - DMA_FLAG_GL3: Channel3 global flag.
*                       - DMA_FLAG_TC3: Channel3 transfer complete flag.
*                       - DMA_FLAG_HT3: Channel3 half transfer flag.
*                       - DMA_FLAG_TE3: Channel3 transfer error flag.
*                       - DMA_FLAG_GL4: Channel4 global flag.
*                       - DMA_FLAG_TC4: Channel4 transfer complete flag.
*                       - DMA_FLAG_HT4: Channel4 half transfer flag.
*                       - DMA_FLAG_TE4: Channel4 transfer error flag.
*                       - DMA_FLAG_GL5: Channel5 global flag.
*                       - DMA_FLAG_TC5: Channel5 transfer complete flag.
*                       - DMA_FLAG_HT5: Channel5 half transfer flag.
*                       - DMA_FLAG_TE5: Channel5 transfer error flag.
*                       - DMA_FLAG_GL6: Channel6 global flag.
*                       - DMA_FLAG_TC6: Channel6 transfer complete flag.
*                       - DMA_FLAG_HT6: Channel6 half transfer flag.
*                       - DMA_FLAG_TE6: Channel6 transfer error flag.
*                       - DMA_FLAG_GL7: Channel7 global flag.
*                       - DMA_FLAG_TC7: Channel7 transfer complete flag.
*                       - DMA_FLAG_HT7: Channel7 half transfer flag.
*                       - DMA_FLAG_TE7: Channel7 transfer error flag.
* Output         : None
* Return         : None
*******************************************************************************/
void DMA_ClearFlag(u32 DMA_FLAG)
{
  /* Check the parameters */
  assert(IS_DMA_CLEAR_FLAG(DMA_FLAG));

  /* Clear the selected DMA flags */
  DMA->IFCR = DMA_FLAG;
}

/*******************************************************************************
* Function Name  : DMA_GetITStatus
* Description    : Checks whether the specified DMA interrupt has occurred or not.
* Input          : - DMA_IT: specifies the DMA interrupt source to check. 
*                    This parameter can be one of the following values:
*                       - DMA_IT_GL1: Channel1 global interrupt.
*                       - DMA_IT_TC1: Channel1 transfer complete interrupt.
*                       - DMA_IT_HT1: Channel1 half transfer interrupt.
*                       - DMA_IT_TE1: Channel1 transfer error interrupt.
*                       - DMA_IT_GL2: Channel2 global interrupt.
*                       - DMA_IT_TC2: Channel2 transfer complete interrupt.
*                       - DMA_IT_HT2: Channel2 half transfer interrupt.
*                       - DMA_IT_TE2: Channel2 transfer error interrupt.
*                       - DMA_IT_GL3: Channel3 global interrupt.
*                       - DMA_IT_TC3: Channel3 transfer complete interrupt.
*                       - DMA_IT_HT3: Channel3 half transfer interrupt.
*                       - DMA_IT_TE3: Channel3 transfer error interrupt.
*                       - DMA_IT_GL4: Channel4 global interrupt.
*                       - DMA_IT_TC4: Channel4 transfer complete interrupt.
*                       - DMA_IT_HT4: Channel4 half transfer interrupt.
*                       - DMA_IT_TE4: Channel4 transfer error interrupt.
*                       - DMA_IT_GL5: Channel5 global interrupt.
*                       - DMA_IT_TC5: Channel5 transfer complete interrupt.
*                       - DMA_IT_HT5: Channel5 half transfer interrupt.
*                       - DMA_IT_TE5: Channel5 transfer error interrupt.
*                       - DMA_IT_GL6: Channel6 global interrupt.
*                       - DMA_IT_TC6: Channel6 transfer complete interrupt.
*                       - DMA_IT_HT6: Channel6 half transfer interrupt.
*                       - DMA_IT_TE6: Channel6 transfer error interrupt.
*                       - DMA_IT_GL7: Channel7 global interrupt.
*                       - DMA_IT_TC7: Channel7 transfer complete interrupt.
*                       - DMA_IT_HT7: Channel7 half transfer interrupt.
*                       - DMA_IT_TE7: Channel7 transfer error interrupt.
* Output         : None
* Return         : The new state of DMA_IT (SET or RESET).
*******************************************************************************/
ITStatus DMA_GetITStatus(u32 DMA_IT)
{
  ITStatus bitstatus = RESET;

  /* Check the parameters */
  assert(IS_DMA_GET_IT(DMA_IT));

  /* Check the status of the specified DMA interrupt */
  if ((DMA->ISR & DMA_IT) != (u32)RESET)
  {
    /* DMA_IT is set */
    bitstatus = SET;
  }
  else
  {
    /* DMA_IT is reset */
    bitstatus = RESET;
  }
  /* Return the DMA_IT status */
  return  bitstatus;
}

/*******************************************************************************
* Function Name  : DMA_ClearITPendingBit
* Description    : Clears the DMA’s interrupt pending bits.
* Input          : - DMA_IT: specifies the DMA interrupt pending bit to clear.
*                    This parameter can be any combination of the following values:
*                       - DMA_IT_GL1: Channel1 global interrupt.
*                       - DMA_IT_TC1: Channel1 transfer complete interrupt.
*                       - DMA_IT_HT1: Channel1 half transfer interrupt.
*                       - DMA_IT_TE1: Channel1 transfer error interrupt.
*                       - DMA_IT_GL2: Channel2 global interrupt.
*                       - DMA_IT_TC2: Channel2 transfer complete interrupt.
*                       - DMA_IT_HT2: Channel2 half transfer interrupt.
*                       - DMA_IT_TE2: Channel2 transfer error interrupt.
*                       - DMA_IT_GL3: Channel3 global interrupt.
*                       - DMA_IT_TC3: Channel3 transfer complete interrupt.
*                       - DMA_IT_HT3: Channel3 half transfer interrupt.
*                       - DMA_IT_TE3: Channel3 transfer error interrupt.
*                       - DMA_IT_GL4: Channel4 global interrupt.
*                       - DMA_IT_TC4: Channel4 transfer complete interrupt.
*                       - DMA_IT_HT4: Channel4 half transfer interrupt.
*                       - DMA_IT_TE4: Channel4 transfer error interrupt.
*                       - DMA_IT_GL5: Channel5 global interrupt.
*                       - DMA_IT_TC5: Channel5 transfer complete interrupt.
*                       - DMA_IT_HT5: Channel5 half transfer interrupt.
*                       - DMA_IT_TE5: Channel5 transfer error interrupt.
*                       - DMA_IT_GL6: Channel6 global interrupt.
*                       - DMA_IT_TC6: Channel6 transfer complete interrupt.
*                       - DMA_IT_HT6: Channel6 half transfer interrupt.
*                       - DMA_IT_TE6: Channel6 transfer error interrupt.
*                       - DMA_IT_GL7: Channel7 global interrupt.
*                       - DMA_IT_TC7: Channel7 transfer complete interrupt.
*                       - DMA_IT_HT7: Channel7 half transfer interrupt.
*                       - DMA_IT_TE7: Channel7 transfer error interrupt.
* Output         : None
* Return         : None
*******************************************************************************/
void DMA_ClearITPendingBit(u32 DMA_IT)
{
  /* Check the parameters */
  assert(IS_DMA_CLEAR_IT(DMA_IT));

  /* Clear the selected DMA interrupt pending bits */
  DMA->IFCR = DMA_IT;
}

/******************* (C) COPYRIGHT 2007 STMicroelectronics *****END OF FILE****/

