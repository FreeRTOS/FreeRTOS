/******************** (C) COPYRIGHT 2006 STMicroelectronics ********************
* File Name          : 91x_gpio.c
* Author             : MCD Application Team
* Date First Issued  : 05/18/2006 : Version 1.0
* Description        : This file provides all the GPIO software functions.
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
#include "91x_gpio.h"
#include "91x_scu.h"

/* Private typedef -----------------------------------------------------------*/
/* Private define ------------------------------------------------------------*/

/* Private macro -------------------------------------------------------------*/
/* Private variables ---------------------------------------------------------*/
/* Private function prototypes -----------------------------------------------*/
   static u8 GPIO_GetGPIONumber(GPIO_TypeDef* GPIOx);

/* Private functions ---------------------------------------------------------*/

/*******************************************************************************
* Function Name  : GPIO_DeInit
* Description    : Deinitializes the GPIOx peripheral registers to their default
*                  reset values.
* Input          : GPIOx: where x can be (0..9) to select the GPIO peripheral.
* Output         : None
* Return         : None
*******************************************************************************/
void GPIO_DeInit(GPIO_TypeDef* GPIOx)
{

  /* Reset the GPIO registers values */
  if(GPIOx == GPIO0)
  {
    SCU_APBPeriphReset(__GPIO0,ENABLE);
    SCU_APBPeriphReset(__GPIO0,DISABLE);
    SCU->GPIOTYPE[0x00] = 0x0000 ;
    SCU->GPIOOUT[0x00]  = 0x0000;
    SCU->GPIOIN[0x00]   = 0x0000;
  }

   if(GPIOx == GPIO1)
  {
    SCU_APBPeriphReset(__GPIO1,ENABLE);
    SCU_APBPeriphReset(__GPIO1,DISABLE);
    SCU->GPIOTYPE[0x01] = 0x0000 ;
    SCU->GPIOOUT[0x01]  = 0x0000;
    SCU->GPIOIN[0x01]   = 0x0000;
  }

   if(GPIOx == GPIO2)
  {
    SCU_APBPeriphReset(__GPIO2,ENABLE);
    SCU_APBPeriphReset(__GPIO2,DISABLE);
    SCU->GPIOTYPE[0x02] = 0x0000 ;
    SCU->GPIOOUT[0x02]  = 0x0000;
    SCU->GPIOIN[0x02]   = 0x0000;
  }

   if(GPIOx == GPIO3)
  {
    SCU_APBPeriphReset(__GPIO3,ENABLE);
    SCU_APBPeriphReset(__GPIO3,DISABLE);
    SCU->GPIOTYPE[0x03] = 0x0000 ;
    SCU->GPIOOUT[0x03]  = 0x0000;
    SCU->GPIOIN[0x03]   = 0x0000;
  }

   if(GPIOx == GPIO4)
  {
    SCU_APBPeriphReset(__GPIO4,ENABLE);
    SCU_APBPeriphReset(__GPIO4,DISABLE);
    SCU->GPIOTYPE[0x04] = 0x0000 ;
    SCU->GPIOOUT[0x04]  = 0x0000;
    SCU->GPIOIN[0x04]   = 0x0000;
    SCU->GPIOANA = 0x00;
  }

   if(GPIOx == GPIO5)
  {
    SCU_APBPeriphReset(__GPIO5,ENABLE);
    SCU_APBPeriphReset(__GPIO5,DISABLE);
    SCU->GPIOTYPE[0x05] = 0x0000 ;
    SCU->GPIOOUT[0x05]  = 0x0000;
    SCU->GPIOIN[0x05]   = 0x0000;
  }

   if(GPIOx == GPIO6)
  {
    SCU_APBPeriphReset(__GPIO6,ENABLE);
    SCU_APBPeriphReset(__GPIO6,DISABLE);
    SCU->GPIOTYPE[0x06] = 0x0000 ;
    SCU->GPIOOUT[0x06]  = 0x0000;
    SCU->GPIOIN[0x06]   = 0x0000;
  }

   if(GPIOx == GPIO7)
  {
    SCU_APBPeriphReset(__GPIO7,ENABLE);
    SCU_APBPeriphReset(__GPIO7,DISABLE);
    SCU->GPIOOUT[0x07]  = 0xAAAA;
    SCU->GPIOOUT[0x07]  = 0x0000;
    SCU->GPIOIN[0x07]   = 0x0000;
  }

   if(GPIOx == GPIO8)
  {
    SCU_APBPeriphReset(__GPIO8,ENABLE);
    SCU_APBPeriphReset(__GPIO8,DISABLE);
    SCU->GPIOEMI = 0x00;
  }

   if(GPIOx == GPIO9)
  {
    SCU_APBPeriphReset(__GPIO9,ENABLE);
    SCU_APBPeriphReset(__GPIO9,DISABLE);
    SCU->GPIOEMI = 0x00;
  }
}
/*******************************************************************************
* Function Name  : GPIO_Init
* Description    : Initializes the GPIOx peripheral according to the specified
*                  parameters in the GPIO_InitStruct .
* Input          :- GPIOx: where x can be (0..9) to select the GPIO peripheral.
*                 - GPIO_InitStruct: pointer to a GPIO_InitTypeDef structure that
*                   contains the configuration information for the specified GPIO
*                   peripheral.
* Output         : None
* Return         : None
*******************************************************************************/
void GPIO_Init(GPIO_TypeDef* GPIOx, GPIO_InitTypeDef* GPIO_InitStruct)
{
  /* Select pin direction */
  u8 PinNumber = 0;
  u8 Counter = 0;
  u8 GPIO_Number = 0;

  GPIO_Number = GPIO_GetGPIONumber(GPIOx);


  if(GPIO_InitStruct->GPIO_Direction == GPIO_PinOutput)
  {
  GPIOx->DDR |= GPIO_InitStruct->GPIO_Pin;
  }
  else
  {
   GPIOx->DDR &= ~GPIO_InitStruct->GPIO_Pin;
  }

   for (Counter = 0; Counter < 8;Counter++)
    {
     /*Search pin number*/
     PinNumber = (GPIO_InitStruct->GPIO_Pin & (1 <<Counter));
     if((PinNumber >> Counter) == 1)
     {
        /*Output ALternate 0*/
        SCU->GPIOOUT[GPIO_Number] &= ~(0x3 <<(Counter *2));
        if(GPIO_InitStruct->GPIO_Alternate == GPIO_OutputAlt1)
        {
          /*Output ALternate 1*/
          SCU->GPIOOUT[GPIO_Number] |= 1 << (Counter *2);
        }
        if(GPIO_InitStruct->GPIO_Alternate == GPIO_OutputAlt2)
        {
          /*Output ALternate 2*/
          SCU->GPIOOUT[GPIO_Number] |= 0x2 << (Counter *2);
        }
        if(GPIO_InitStruct->GPIO_Alternate == GPIO_OutputAlt3)
        {
          /*Output ALternate 3*/
          SCU->GPIOOUT[GPIO_Number] |= 0x3 << (Counter *2);
        }

       /*Type configuration: PushPull or Open Collector*/
        SCU->GPIOTYPE[GPIO_Number] &= ~(0x1 << Counter) ;
       if(GPIO_InitStruct->GPIO_Type == GPIO_Type_OpenCollector)
       {
         /*Open Drain configuration*/
        SCU->GPIOTYPE[GPIO_Number] |= 0x1 << Counter;
       }

       /*IP Connected disable*/
       SCU->GPIOIN[GPIO_Number] &= ~(0x1 << Counter) ;
       if(GPIO_InitStruct->GPIO_IPConnected == GPIO_IPConnected_Enable)
       {
         /*IP Connected enable*/
         SCU->GPIOIN[GPIO_Number] |= 0x1 << Counter;
       }
    }
 }
}

/*******************************************************************************
* Function Name  : GPIO_StructInit
* Description    : Initialize the GPIO Init Structure parameters
* Input          : GPIO_InitStruct : pointer to a GPIO_InitTypeDef structure
*                  which will be initialized.
* Output         : None
* Return         : None
*******************************************************************************/
void GPIO_StructInit(GPIO_InitTypeDef* GPIO_InitStruct)
{
  /* Reset GPIO init structure parameters values */
  GPIO_InitStruct->GPIO_Pin  = GPIO_Pin_All;
  GPIO_InitStruct->GPIO_Direction = GPIO_PinInput;
  GPIO_InitStruct->GPIO_Type = GPIO_Type_PushPull;
  GPIO_InitStruct->GPIO_IPConnected = GPIO_IPConnected_Disable;
  GPIO_InitStruct->GPIO_Alternate = GPIO_InputAlt1;
}

/*******************************************************************************
* Function Name  : GPIO_ReadBit
* Description    : Reads the specified port pin
* Input          : - GPIOx: where x can be (0..9) to select the GPIO peripheral.
*                : - GPIO_Pin: the Pin number. This parameter can be GPIO_Pin_x
*                    where x can be (0..7).
* Output         : None
* Return         : The port pin value
*******************************************************************************/
u8 GPIO_ReadBit(GPIO_TypeDef* GPIOx, u8 GPIO_Pin)
{
 if ((((GPIOx->DR[GPIO_Pin<<2])) & GPIO_Pin) != Bit_RESET )
  {
    return Bit_SET;
  }
  else
  {
    return Bit_RESET;
  }
}

/*******************************************************************************
* Function Name  : GPIO_Read
* Description    : Reads the specified GPIO data port
* Input          : - GPIOx: where x can be (0..9) to select the GPIO peripheral.
* Output         : None
* Return         : GPIO data port word value.
*******************************************************************************/
u8 GPIO_Read(GPIO_TypeDef* GPIOx)
{
  return (GPIOx->DR[0x3FC]);
}

/*******************************************************************************
* Function Name  : GPIO_WriteBit
* Description    : Sets or clears the selected data port bit.
* Input          : - GPIOx: where x can be (0..9) to select the GPIO peripheral.
*                  - GPIO_Pin: the Pin number. This parameter can be GPIO_Pin_x
*                    where x can be (0..7).
*                  - BitVal: this parameter specifies the value to be written
*                    to the selected bit.
*                    BitVal must be one of the BitAction enum values:
*                       - Bit_RESET: to clear the port pin
*                       - Bit_SET: to set the port pin
* Output         : None
* Return         : None
*******************************************************************************/
void GPIO_WriteBit(GPIO_TypeDef* GPIOx, u8 GPIO_Pin, BitAction BitVal)
{
  if(BitVal == Bit_SET)
  {
    GPIOx->DR[GPIO_Pin <<2] = GPIO_Pin;
  }
  else
  {
    GPIOx->DR[GPIO_Pin <<2] = 0x00;
  }
}

/*******************************************************************************
* Function Name  : GPIO_Write
* Description    : Writes the passed value in the selected data GPIOx port
*                  register.
* Input          :- GPIOx: where x can be (0..9) to select the GPIO peripheral.
*                 - PortVal: the value to be written to the data port register.
* Output         : None
* Return         : None
*******************************************************************************/
void GPIO_Write(GPIO_TypeDef* GPIOx, u8 PortVal)
{
  GPIOx->DR[0x3FC] = PortVal;
}

/*******************************************************************************
* Function Name  : GPIO_EMIConfig
* Description    : Enables or disables GPIO 8 and 9 in EMI mode.
* Input          : - NewState: new state of the EMI.
*                   This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void GPIO_EMIConfig(FunctionalState NewState)
{
  if(NewState == ENABLE)
  {
    SCU->GPIOEMI = 0x01;
  }
  else
  {
    SCU->GPIOEMI = 0x00;
  }
}

/*******************************************************************************
* Function Name  : GPIO_ANAPinConfig
* Description    : Enables or disables pins from GPIO 4 in Analogue mode.
* Input          :- GPIO_ANAChannel: selects the ADC channel pin.
*                   This parameter can be one of the following values:
*                      GPIO_ANAChannel0
*                      GPIO_ANAChannel1
*                      GPIO_ANAChannel2
*                      GPIO_ANAChannel3
*                      GPIO_ANAChannel4
*                      GPIO_ANAChannel5
*                      GPIO_ANAChannel6
*                      GPIO_ANAChannel7
*                      GPIO_ANAChannelALL
*                 - NewState: new state of the port pin.
*                   This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void GPIO_ANAPinConfig(u8 GPIO_ANAChannel, FunctionalState NewState)
{

  if(NewState == ENABLE)
  {
    if(GPIO_ANAChannel == GPIO_ANAChannelALL)
    {
      SCU->GPIOOUT[4] = 0x0000;
      SCU->GPIOIN[4] = 0x00;
    }
    else
    {
      SCU->GPIOOUT[4] &= ~(0x3<<(GPIO_ANAChannel-1));
      SCU->GPIOIN[4] &= ~GPIO_ANAChannel;
    }
    SCU->GPIOANA |= GPIO_ANAChannel;

  }
  else
  {
    SCU->GPIOANA &= ~GPIO_ANAChannel;
  }
}

/*******************************************************************************
* Function Name  : GPIO_GetGPIONumber
* Description    : searche the GPIO number.
* Input          : GPIOx: where x can be (0..9) to select the GPIO peripheral.
* Output         : None
* Return         : GPIO number
*******************************************************************************/
u8 GPIO_GetGPIONumber(GPIO_TypeDef* GPIOx)
{
 
  if(GPIOx == GPIO1)
  {
    return  1;
  }
  if(GPIOx == GPIO2)
  {
    return  2;
  }
  if(GPIOx == GPIO3)
  {
    return  3;
  }
  if(GPIOx == GPIO4)
  {
    return  4;
  }
  if(GPIOx == GPIO5)
  {
    return  5;
  }
  if(GPIOx == GPIO6)
  {
    return  6;
  }
  if(GPIOx == GPIO7)
  {
    return  7;
  }
  if(GPIOx == GPIO8)
  {
    return  8;
  }
  if(GPIOx == GPIO9)
  {
    return  9;
  }
  return 0;
}
/******************* (C) COPYRIGHT 2006 STMicroelectronics *****END OF FILE****/
