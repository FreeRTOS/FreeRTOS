/******************** (C) COPYRIGHT 2006 STMicroelectronics ********************
* File Name          : 75x_gpio.c
* Author             : MCD Application Team
* Date First Issued  : 03/10/2006
* Description        : This file provides all the GPIO software functions.
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
#include "75x_gpio.h"
#include "75x_mrcc.h"

/* Private typedef -----------------------------------------------------------*/
/* Private define ------------------------------------------------------------*/
#define GPIO_Remap_Mask    0x1F       /* GPIO remapping mask */
#define GPIO_Pin_Mask      0x000FFFFF /* GPIO1 and GPIO2 all pins mask */

/* Private macro -------------------------------------------------------------*/
/* Private variables ---------------------------------------------------------*/
/* Private function prototypes -----------------------------------------------*/
/* Private functions ---------------------------------------------------------*/

/*******************************************************************************
* Function Name  : GPIO_DeInit
* Description    : Deinitializes the GPIOx peripheral registers to their default
*                  reset values.
*                  The I/O remapping register 0 and 1 are not reset by this function.
* Input          : GPIOx: where x can be 0,1 or 2 to select the GPIO peripheral.
* Output         : None
* Return         : None
*******************************************************************************/
void GPIO_DeInit(GPIO_TypeDef* GPIOx)
{
  /* Reset the GPIOx registers values */
  GPIOx->PC0 = 0xFFFFFFFF;
  GPIOx->PC1 = 0x0;
  GPIOx->PC2 = 0x0;
  GPIOx->PM = 0x0;
}

/*******************************************************************************
* Function Name  : GPIO_Init
* Description    : Initializes the GPIOx peripheral according to the specified
*                  parameters in the GPIO_InitStruct. This function will not
*                  change the configuration for a pin if the corresponding mask
*                  bit is set, except pins configured as input pull-up or pull-down.
*                  These pins are automatically masked after each configuration.
* Input          :- GPIOx: where x can be (0..2) to select the GPIO peripheral.
*                 - GPIO_InitStruct: pointer to a GPIO_InitTypeDef structure that
*                   contains the configuration information for the specified GPIO
*                   peripheral.
* Output         : None
* Return         : None
*******************************************************************************/
void GPIO_Init(GPIO_TypeDef* GPIOx, GPIO_InitTypeDef* GPIO_InitStruct)
{
  /* GPIOx Mode and Pins Set */
  if((GPIOx != GPIO0) && (GPIO_InitStruct->GPIO_Pin == GPIO_Pin_All))
  {
    GPIO_InitStruct->GPIO_Pin = GPIO_Pin_Mask;
  }

  switch(GPIO_InitStruct->GPIO_Mode)
  {
    case GPIO_Mode_AIN:
      GPIOx->PC0 &= ~GPIO_InitStruct->GPIO_Pin;
      GPIOx->PC1 &= ~GPIO_InitStruct->GPIO_Pin;
      GPIOx->PC2 &= ~GPIO_InitStruct->GPIO_Pin;
      break;

    case GPIO_Mode_IN_FLOATING:
      GPIOx->PC0 |=  GPIO_InitStruct->GPIO_Pin;
      GPIOx->PC1 &= ~GPIO_InitStruct->GPIO_Pin;
      GPIOx->PC2 &= ~GPIO_InitStruct->GPIO_Pin;
      break;

    case GPIO_Mode_IPD:
      GPIOx->PM  &= ~GPIO_InitStruct->GPIO_Pin;
      GPIOx->PC0 |=  GPIO_InitStruct->GPIO_Pin;
      GPIOx->PC1 |=  GPIO_InitStruct->GPIO_Pin;
      GPIOx->PC2 &= ~GPIO_InitStruct->GPIO_Pin;
      GPIOx->PD  &= ~GPIO_InitStruct->GPIO_Pin;
      GPIOx->PM  |=  GPIO_InitStruct->GPIO_Pin;
      break;

    case GPIO_Mode_IPU:
      GPIOx->PM  &= ~GPIO_InitStruct->GPIO_Pin;
      GPIOx->PC0 |=  GPIO_InitStruct->GPIO_Pin;
      GPIOx->PC1 |=  GPIO_InitStruct->GPIO_Pin;
      GPIOx->PC2 &= ~GPIO_InitStruct->GPIO_Pin;
      GPIOx->PD  |=  GPIO_InitStruct->GPIO_Pin;
      GPIOx->PM  |=  GPIO_InitStruct->GPIO_Pin;
      break;

    case GPIO_Mode_Out_OD:
      GPIOx->PC0 &= ~GPIO_InitStruct->GPIO_Pin;
      GPIOx->PC1 &= ~GPIO_InitStruct->GPIO_Pin;
      GPIOx->PC2 |=  GPIO_InitStruct->GPIO_Pin;
      break;

    case GPIO_Mode_Out_PP:
      GPIOx->PC0 |=  GPIO_InitStruct->GPIO_Pin;
      GPIOx->PC1 &= ~GPIO_InitStruct->GPIO_Pin;
      GPIOx->PC2 |=  GPIO_InitStruct->GPIO_Pin;
      break;

    case GPIO_Mode_AF_OD:
      GPIOx->PD  |=  GPIO_InitStruct->GPIO_Pin;          
      GPIOx->PC1 |=  GPIO_InitStruct->GPIO_Pin;
      GPIOx->PC0 &= ~GPIO_InitStruct->GPIO_Pin;
      GPIOx->PC2 |=  GPIO_InitStruct->GPIO_Pin;
      break;

    case GPIO_Mode_AF_PP:
      GPIOx->PC0 |=  GPIO_InitStruct->GPIO_Pin;
      GPIOx->PC1 |=  GPIO_InitStruct->GPIO_Pin;
      GPIOx->PC2 |=  GPIO_InitStruct->GPIO_Pin;
      break;

    default :
      GPIOx->PC0 |=  GPIO_InitStruct->GPIO_Pin;
      GPIOx->PC1 &= ~GPIO_InitStruct->GPIO_Pin;
      GPIOx->PC2 &= ~GPIO_InitStruct->GPIO_Pin;
      break;
  }
}

/*******************************************************************************
* Function Name  : GPIO_StructInit
* Description    : Fills each GPIO_InitStruct member with its default value.
* Input          : GPIO_InitStruct : pointer to a GPIO_InitTypeDef structure
*                  which will be initialized.
* Output         : None
* Return         : None
*******************************************************************************/
void GPIO_StructInit(GPIO_InitTypeDef* GPIO_InitStruct)
{
  /* Reset GPIO init structure parameters values */
  GPIO_InitStruct->GPIO_Pin  = GPIO_Pin_All;
  GPIO_InitStruct->GPIO_Mode = GPIO_Mode_IN_FLOATING;
}

/*******************************************************************************
* Function Name  : GPIO_Read
* Description    : Reads the specified GPIO data port.
* Input          : GPIOx: where x can be 0,1 or 2 to select the GPIO peripheral.
* Output         : None
* Return         : GPIO data port word value.
*******************************************************************************/
u32 GPIO_Read(GPIO_TypeDef* GPIOx)
{
  return GPIOx->PD;
}

/*******************************************************************************
* Function Name  : GPIO_ReadBit
* Description    : Reads the specified data port bit.
* Input          : - GPIOx: where x can be (0..2) to select the GPIO peripheral.
*                : - GPIO_Pin:  specifies the port bit to read.
*                    This parameter can be GPIO_Pin_x where x can be (0..31) for
*                    GPIO0 and x(0..19) for GPIO1 and GPIO2.
* Output         : None
* Return         : The port pin value
*******************************************************************************/
u8 GPIO_ReadBit(GPIO_TypeDef* GPIOx, u32 GPIO_Pin)
{
  if ((GPIOx->PD & GPIO_Pin) != Bit_RESET)
  {
    return Bit_SET;
  }
  else
  {
    return Bit_RESET;
  }
}

/*******************************************************************************
* Function Name  : GPIO_Write
* Description    : Writes data to the specified GPIO data port.
* Input          :- GPIOx: where x can be 0,1 or 2 to select the GPIO peripheral.
*                 - PortVal: specifies the value to be written to the data port
*                   register.
* Output         : None
* Return         : None
*******************************************************************************/
void GPIO_Write(GPIO_TypeDef* GPIOx, u32 PortVal)
{
  GPIOx->PD = PortVal;
}

/*******************************************************************************
* Function Name  : GPIO_WriteBit
* Description    : Sets or clears the selected data port bit.
* Input          : - GPIOx: where x can be (0..2) to select the GPIO peripheral.
*                  - GPIO_Pin: specifies the port bit to be written.
*                    This parameter can be GPIO_Pin_x where x can be (0..31) for
*                    GPIO0 and x(0..19) for GPIO1 and GPIO2.
*                  - BitVal: specifies the value to be written to the selected bit.
*                    This parameter must be one of the BitAction enum values:
*                       - Bit_RESET: to clear the port pin
*                       - Bit_SET: to set the port pin
* Output         : None
* Return         : None
*******************************************************************************/
void GPIO_WriteBit(GPIO_TypeDef* GPIOx, u32 GPIO_Pin, BitAction BitVal)
{
  if(BitVal != Bit_RESET)
  {
    GPIOx->PD |= GPIO_Pin;
  }
  else
  {
    GPIOx->PD &= ~GPIO_Pin;
  }
}

/*******************************************************************************
* Function Name  : GPIO_PinMaskConfig
* Description    : Enables or disables write protection to the selected bits in
*                  the I/O port registers (PxC2, PxC1, PxC0 and PxD).
* Input          :- GPIOx: where x can be 0,1 or 2 to select the GPIO peripheral.
*                 - GPIO_Pin: specifies the port bit to be protected.
*                   This parameter can be GPIO_Pin_x where x can be (0..31) for
*                   GPIO0 and x(0..19) for GPIO1 and GPIO2.
*                 - NewState: new state of the port pin.
*                   This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void GPIO_PinMaskConfig(GPIO_TypeDef* GPIOx, u32 GPIO_Pin, FunctionalState NewState)
{
  if(NewState == ENABLE)
  {
    GPIOx->PM |= GPIO_Pin;
  }
  else
  {
    GPIOx->PM &= ~GPIO_Pin;
  }
}

/*******************************************************************************
* Function Name  : GPIO_GetPortMask
* Description    : Gets the GPIOx port mask value.
* Input          : GPIOx: where x can be 0,1 or 2 to select the GPIO peripheral.
* Output         : None
* Return         : GPIO port mask value.
*******************************************************************************/
u32 GPIO_GetPortMask(GPIO_TypeDef* GPIOx)
{
  return GPIOx->PM;
}

/*******************************************************************************
* Function Name  : GPIO_PinRemapConfig
* Description    : Changes the mapping of the specified pin.
* Input          :- GPIO_Remap: selects the pin to remap.
*                   This parameter can be one of the following values:
*                     - GPIO_Remap_SMI_CS3_EN: Enable SMI CS3 
*                     - GPIO_Remap_SMI_CS2_EN: Enable SMI CS2
*                     - GPIO_Remap_SMI_CS1_EN: Enable SMI CS1
*                     - GPIO_Remap_SMI_EN: Enable SMI Alternate Functions: 
*                       SMI_CS0, SMI_CK, SMI_DIN and SMI_DOUT
*                     - GPIO_Remap_DBGOFF: JTAG Disable
*                     - GPIO_Remap_UART1: UART1 Alternate Function mapping
*                     - GPIO_Remap_UART2: UART2 Alternate Function mapping
*                     - GPIO_Remap_SSP1: SSP1 Alternate Function mapping
*                     - GPIO_Remap_TIM2: TIM2 Alternate Function mapping
*                     - GPIO_Remap_TIM0: TIM0 Alternate Function mapping
*                 - NewState: new state of the port pin.
*                   This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void GPIO_PinRemapConfig(u16 GPIO_Remap, FunctionalState NewState)
{
  u32 GPIOReg = 0;
  u32 PinPos = 0;

  /* Get the GPIO register index */
  GPIOReg = GPIO_Remap >> 5;

  /* Get the pin position */
  PinPos = GPIO_Remap & GPIO_Remap_Mask;

  if(GPIOReg == 1) /* The pin to remap is in REMAP0R register */
  {
    if(NewState == ENABLE)
    {
      GPIOREMAP->REMAP0R |= (1 << PinPos);
    }
    else
    {
      GPIOREMAP->REMAP0R &= ~(1 << PinPos);
    }
  }
  else if(GPIOReg == 2) /* The pin to remap is in REMAP1R register */
  {
    if(NewState == ENABLE)
    {
      GPIOREMAP->REMAP1R |= (1 << PinPos);
    }
    else
    {
      GPIOREMAP->REMAP1R &= ~(1 << PinPos);
    }
  }
}

/******************* (C) COPYRIGHT 2006 STMicroelectronics *****END OF FILE****/
