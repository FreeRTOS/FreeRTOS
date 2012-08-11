/******************** (C) COPYRIGHT 2006 STMicroelectronics ********************
* File Name          : 75x_extit.c
* Author             : MCD Application Team
* Date First Issued  : 03/10/2006
* Description        : This file provides all the EXTIT software functions.
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
#include "75x_extit.h"
#include "75x_mrcc.h"

/* Private typedef -----------------------------------------------------------*/
/* Private define ------------------------------------------------------------*/
/* Private macro -------------------------------------------------------------*/
/* Private variables ---------------------------------------------------------*/
/* Private function prototypes -----------------------------------------------*/
/* Private functions ---------------------------------------------------------*/

/*******************************************************************************
* Function Name  : EXTIT_DeInit
* Description    : Deinitializes the EXTIT peripheral registers to their default
*                  reset values.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void EXTIT_DeInit(void)
{
  MRCC_PeripheralSWResetConfig(MRCC_Peripheral_EXTIT,ENABLE);
  MRCC_PeripheralSWResetConfig(MRCC_Peripheral_EXTIT,DISABLE);
}

/*******************************************************************************
* Function Name  : EXTIT_Init
* Description    : Initializes the EXTIT peripheral according to the specified
*                  parameters in the EXTIT_InitStruct .
* Input          : - EXTIT_InitStruct: pointer to a EXTIT_InitTypeDef structure
*                    that contains the configuration information for the EXTIT
*                    peripheral.
* Output         : None
* Return         : None
*******************************************************************************/
void EXTIT_Init(EXTIT_InitTypeDef* EXTIT_InitStruct)
{
  if(EXTIT_InitStruct->EXTIT_ITLineCmd == ENABLE)
  {
    /* Enable the selected external interrupts */
    EXTIT->MR |= EXTIT_InitStruct->EXTIT_ITLine;
    
    /* Select the trigger for the selected external interrupts */
    if(EXTIT_InitStruct->EXTIT_ITTrigger == EXTIT_ITTrigger_Falling)
    {
      /* Falling edge */
      EXTIT->TSR &= ~EXTIT_InitStruct->EXTIT_ITLine;
    }
    else if (EXTIT_InitStruct->EXTIT_ITTrigger == EXTIT_ITTrigger_Rising)
    {
      /* Rising edge */
      EXTIT->TSR |= EXTIT_InitStruct->EXTIT_ITLine;
    }
  }
  else if(EXTIT_InitStruct->EXTIT_ITLineCmd == DISABLE)
  {
    /* Disable the selected external interrupts */
    EXTIT->MR &= ~EXTIT_InitStruct->EXTIT_ITLine;
  }
}

/*******************************************************************************
* Function Name  : EXTIT_StructInit
* Description    : Fills each EXTIT_InitStruct member with its reset value.
* Input          : - EXTIT_InitStruct: pointer to a EXTIT_InitTypeDef structure
*                    which will be initialized.
* Output         : None
* Return         : None
*******************************************************************************/
void EXTIT_StructInit(EXTIT_InitTypeDef* EXTIT_InitStruct)
{
  EXTIT_InitStruct->EXTIT_ITLine = EXTIT_ITLineNone;
  EXTIT_InitStruct->EXTIT_ITTrigger = EXTIT_ITTrigger_Falling;
  EXTIT_InitStruct->EXTIT_ITLineCmd = DISABLE;
}

/*******************************************************************************
* Function Name  : EXTIT_GenerateSWInterrupt
* Description    : Generates a Software interrupt.
* Input          : - EXTIT_ITLine: specifies the EXTIT lines to be enabled or
*                    disabled. This parameter can be:
*                     - EXTIT_ITLinex: External interrupt line x where x(0..15)
* Output         : None
* Return         : None
*******************************************************************************/
void EXTIT_GenerateSWInterrupt(u16 EXTIT_ITLine)
{
  EXTIT->SWIR |= EXTIT_ITLine;
}

/*******************************************************************************
* Function Name  : EXTIT_GetFlagStatus
* Description    : Checks whether the specified EXTIT line flag is set or not.
* Input          : - EXTIT_ITLine: specifies the EXTIT lines flag to check.  
*                    This parameter can be:
*                     - EXTIT_ITLinex: External interrupt line x where x(0..15)
* Output         : None
* Return         : The new state of EXTIT_ITLine (SET or RESET).
*******************************************************************************/
FlagStatus EXTIT_GetFlagStatus(u16 EXTIT_ITLine)
{
  if((EXTIT->PR & EXTIT_ITLine) != RESET)
  {
    return SET;
  }
  else
  {
    return RESET;
  }
}

/*******************************************************************************
* Function Name  : EXTIT_ClearFlag
* Description    : Clears the EXTIT’s line pending flags.
* Input          : - EXTIT_ITLine: specifies the EXTIT lines flags to clear. 
*                    This parameter can be:
*                     - EXTIT_ITLinex: External interrupt line x where x(0..15)
* Output         : None
* Return         : None
*******************************************************************************/
void EXTIT_ClearFlag(u16 EXTIT_ITLine)
{
  EXTIT->PR = EXTIT_ITLine;
}

/*******************************************************************************
* Function Name  : EXTIT_GetITStatus
* Description    : Checks whether the specified EXTIT line is asserted or not.
* Input          : - EXTIT_ITLine: specifies the EXTIT lines to check. 
*                    This parameter can be:
*                     - EXTIT_ITLinex: External interrupt line x where x(0..15)
* Output         : None
* Return         : The new state of EXTIT_ITLine (SET or RESET).
*******************************************************************************/
ITStatus EXTIT_GetITStatus(u16 EXTIT_ITLine)
{
  if(((EXTIT->PR & EXTIT_ITLine) != RESET)&& ((EXTIT->MR & EXTIT_ITLine) != RESET))
  {
    return SET;
  }
  else
  {
    return RESET;
  }
}

/*******************************************************************************
* Function Name  : EXTIT_ClearITPendingBit
* Description    : Clears the EXTIT’s line pending bits.
* Input          : - EXTIT_ITLine: specifies the EXTIT lines to clear. 
*                    This parameter can be:
*                     - EXTIT_ITLinex: External interrupt line x where x(0..15)
* Output         : None
* Return         : None
*******************************************************************************/
void EXTIT_ClearITPendingBit(u16 EXTIT_ITLine)
{
  EXTIT->PR = EXTIT_ITLine;
}

/******************* (C) COPYRIGHT 2006 STMicroelectronics *****END OF FILE****/
