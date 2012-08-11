/******************** (C) COPYRIGHT 2006 STMicroelectronics ********************
* File Name          : 75x_eic.c
* Author             : MCD Application Team
* Date First Issued  : 03/10/2006
* Description        : This file provides all the EIC software functions.
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
#include "75x_eic.h"

/* Private typedef -----------------------------------------------------------*/
/* Private define ------------------------------------------------------------*/
#define EIC_IRQEnable_Mask     0x00000001
#define EIC_IRQDisable_Mask    0xFFFFFFFE

#define EIC_FIQEnable_Mask     0x00000002
#define EIC_FIQDisable_Mask    0xFFFFFFFD

#define EIC_SIPL_Mask          0x0000000F
#define EIC_SIPL_Reset_Mask    0xFFFFFFF0

/* Private macro -------------------------------------------------------------*/
/* Private variables ---------------------------------------------------------*/
/* Private function prototypes -----------------------------------------------*/
/* Private functions ---------------------------------------------------------*/

/*******************************************************************************
* Function Name  : EIC_DeInit
* Description    : Deinitializes the EIC peripheral registers to their default
*                  reset values.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void EIC_DeInit(void)
{
  EIC->ICR = 0x00;
  EIC->CIPR = 0x00;
  EIC->FIR = 0x0C;
  EIC->IER = 0x00;
  EIC->IPR = 0xFFFFFFFF;
}

/*******************************************************************************
* Function Name  : EIC_IRQInit
* Description    : Configures the IRQ channels according to the specified
*                  parameters in the EIC_IRQInitStruct.
* Input          : EIC_IRQInitStruct: pointer to a EIC_IRQInitTypeDef structure.
* Output         : None
* Return         : None
*******************************************************************************/
void EIC_IRQInit(EIC_IRQInitTypeDef* EIC_IRQInitStruct)
{
  u32 Tmp = 0;

  if(EIC_IRQInitStruct->EIC_IRQChannelCmd == ENABLE)
  {
    /* Enable the selected IRQ channel */
    EIC->IER |= 1 << EIC_IRQInitStruct->EIC_IRQChannel;

    /* Configure the selected IRQ channel priority ***************************/
    /* Clear SIPL[3:0] bits */
    EIC->SIRn[EIC_IRQInitStruct->EIC_IRQChannel] &= EIC_SIPL_Reset_Mask;

    /* Configure SIPL[3:0] bits according to EIC_IRQChannelPriority parameter */
    Tmp = EIC_IRQInitStruct->EIC_IRQChannelPriority & EIC_SIPL_Mask;
    EIC->SIRn[EIC_IRQInitStruct->EIC_IRQChannel] |= Tmp;
  }
  else
  {
    /* Disable the select IRQ channel */
    EIC->IER &=~ (1 << EIC_IRQInitStruct->EIC_IRQChannel);
  }
}

/*******************************************************************************
* Function Name  : EIC_FIQInit
* Description    : Configures the FIQ channels according to the specified
*                  parameters in the EIC_FIQInitStruct.
* Input          : EIC_FIQInitStruct: pointer to a EIC_FIQInitTypeDef structure.
* Output         : None
* Return         : None
*******************************************************************************/
void EIC_FIQInit(EIC_FIQInitTypeDef* EIC_FIQInitStruct)
{
  if(EIC_FIQInitStruct->EIC_FIQChannelCmd == ENABLE)
  {
    /* Enable the selected FIQ channel */
    EIC->FIER |= EIC_FIQInitStruct->EIC_FIQChannel ;
  }
  else
  {
    /* Disable the selected FIQ channel */
    EIC->FIER &= ~EIC_FIQInitStruct->EIC_FIQChannel;
  }
}

/*******************************************************************************
* Function Name  : EIC_IRQStructInit
* Description    : Fills each EIC_IRQInitStruct member with its default value.
* Input          : EIC_IRQInitStruct: pointer to a EIC_IRQInitTypeDef structure
*                  which will be initialized.
* Output         : None
* Return         : None
*******************************************************************************/
void EIC_IRQStructInit(EIC_IRQInitTypeDef* EIC_IRQInitStruct)
{
  EIC_IRQInitStruct->EIC_IRQChannel = 0x1F;
  EIC_IRQInitStruct->EIC_IRQChannelPriority = 0;
  EIC_IRQInitStruct->EIC_IRQChannelCmd = DISABLE;
}

/*******************************************************************************
* Function Name  : EIC_FIQStructInit
* Description    : Fills each EIC_FIQInitStruct member with its default value.
* Input          : EIC_FIQInitStruct: pointer to a EIC_FIQInitTypeDef structure
*                  which will be initialized.
* Output         : None
* Return         : None
*******************************************************************************/
void EIC_FIQStructInit(EIC_FIQInitTypeDef* EIC_FIQInitStruct)
{
  EIC_FIQInitStruct->EIC_FIQChannel = 0x03;
  EIC_FIQInitStruct->EIC_FIQChannelCmd = DISABLE;
}

/*******************************************************************************
* Function Name  : EIC_IRQCmd
* Description    : Enables or disables EIC IRQ output request to CPU.
* Input          : NewState: new state of the EIC IRQ output request to CPU.
*                  This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void EIC_IRQCmd(FunctionalState NewState)
{
  if(NewState == ENABLE)
  {
    /* Enable EIC IRQ output request to CPU */
    EIC->ICR |= EIC_IRQEnable_Mask;
  }
  else
  {
    /* Disable EIC IRQ output request to CPU */
    EIC->ICR &= EIC_IRQDisable_Mask;
  }
}

/*******************************************************************************
* Function Name  : EIC_FIQCmd
* Description    : Enables or disables EIC FIQ output request to CPU.
* Input          : NewState: new state of the EIC FIQ output request to CPU.
*                  This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void EIC_FIQCmd(FunctionalState NewState)
{
  if(NewState == ENABLE)
  {
    /* Enable EIC FIQ output request to CPU */
    EIC->ICR |= EIC_FIQEnable_Mask;
  }
  else
  {
    /* Disable EIC FIQ output request to CPU */
    EIC->ICR &= EIC_FIQDisable_Mask;
  }
}

/*******************************************************************************
* Function Name  : EIC_GetCurrentIRQChannel
* Description    : Returns the current served IRQ channel identifier.
* Input          : None
* Output         : None
* Return         : The current served IRQ channel.
*******************************************************************************/
u8 EIC_GetCurrentIRQChannel(void)
{
  /* Read and return the CIC[4:0] bits of CICR register */
  return ((u8) (EIC->CICR));
}

/*******************************************************************************
* Function Name  : EIC_GetCurrentIRQChannelPriority
* Description    : Returns the priority level of the current served IRQ channel.
* Input          : None
* Output         : None
* Return         : The priority level of the current served IRQ channel.
*******************************************************************************/
u8 EIC_GetCurrentIRQChannelPriority(void)
{
  /* Read and return the CIP[3:0] bits of CIPR register */
  return ((u8) (EIC->CIPR));
}

/*******************************************************************************
* Function Name  : EIC_CurrentIRQPriorityConfig
* Description    : Changes the priority of the current served IRQ channel.
*                  The new priority value must be higher, or equal, than the
*                  priority value associated to the interrupt channel currently
*                  serviced.
* Input          : NewPriority: new priority value of the IRQ interrupt routine
*                  currently serviced.
* Output         : None
* Return         : None
*******************************************************************************/
void EIC_CurrentIRQPriorityConfig(u8 NewPriority)
{
  /* Disable EIC IRQ output request to CPU */
  EIC->ICR &= EIC_IRQDisable_Mask;

  /* Change the current priority */
  EIC->CIPR = NewPriority;

  /* Enable EIC IRQ output request to CPU  */
  EIC->ICR |= EIC_IRQEnable_Mask;
}

/*******************************************************************************
* Function Name  : EIC_GetCurrentFIQChannel
* Description    : Returns the current served FIQ channel identifier.
* Input          : None
* Output         : None
* Return         : The current served FIQ channel.
*******************************************************************************/
u8 EIC_GetCurrentFIQChannel(void)
{
  /* Read and return the FIP[1:0] bits of FIPR register */
  return ((u8) (EIC->FIPR));
}

/*******************************************************************************
* Function Name  : EIC_ClearFIQPendingBit
* Description    : Clears the pending bit of the selected FIQ Channel.
* Input          : EIC_FIQChannel: specifies the FIQ channel to clear its
*                  pending bit.
* Output         : None
* Return         : None
*******************************************************************************/
void EIC_ClearFIQPendingBit(u8 EIC_FIQChannel)
{
  /* Clear the correspondent FIQ pending bit */
  EIC->FIPR = EIC_FIQChannel ;
}

/******************* (C) COPYRIGHT 2006 STMicroelectronics *****END OF FILE****/
