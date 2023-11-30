/**
  ******************************************************************************
  * @file    stm32l1xx_syscfg.c
  * @author  MCD Application Team
  * @version V1.1.1
  * @date    05-March-2012
  * @brief   This file provides firmware functions to manage the following
  *          functionalities of the SYSCFG and RI peripherals:
  *           + SYSCFG Initialization and Configuration
  *           + RI Initialization and Configuration
  *
@verbatim
 ===============================================================================
                     ##### How to use this driver #####
 ===============================================================================
    [..] This driver provides functions for:
         (#) Remapping the memory accessible in the code area using
          SYSCFG_MemoryRemapConfig().
         (#) Manage the EXTI lines connection to the GPIOs using
             SYSCFG_EXTILineConfig().
         (#) Routing of I/Os toward the input captures of timers (TIM2, TIM3 and TIM4).
         (#) Input routing of COMP1 and COMP2.
         (#) Routing of internal reference voltage VREFINT to PB0 and PB1.
         (#) The RI registers can be accessed only when the comparator
             APB interface clock is enabled.
             To enable comparator clock use:
             RCC_APB1PeriphClockCmd(RCC_APB1Periph_COMP, ENABLE).
             Following functions uses RI registers:
             (++) SYSCFG_RIDeInit()
             (++) SYSCFG_RITIMSelect()
             (++) SYSCFG_RITIMInputCaptureConfig()
             (++) SYSCFG_RIResistorConfig()
             (++) SYSCFG_RIChannelSpeedConfig()
             (++) SYSCFG_RIIOSwitchConfig()
             (++) SYSCFG_RISwitchControlModeCmd()
             (++) SYSCFG_RIHysteresisConfig()
         (#) The SYSCFG registers can be accessed only when the SYSCFG
             interface APB clock is enabled.
             To enable SYSCFG APB clock use:
             RCC_APB2PeriphClockCmd(RCC_APB2Periph_SYSCFG, ENABLE);
             Following functions uses SYSCFG registers:
             (++) SYSCFG_DeInit()  
             (++) SYSCFG_MemoryRemapConfig()
             (++) SYSCFG_GetBootMode()  
             (++) SYSCFG_USBPuCmd()
             (++) SYSCFG_EXTILineConfig()
@endverbatim
  *
  ******************************************************************************
  * @attention
  *
  * <h2><center>&copy; COPYRIGHT 2012 STMicroelectronics</center></h2>
  *
  * Licensed under MCD-ST Liberty SW License Agreement V2, (the "License");
  * You may not use this file except in compliance with the License.
  * You may obtain a copy of the License at:
  *
  *        http://www.st.com/software_license_agreement_liberty_v2
  *
  * Unless required by applicable law or agreed to in writing, software 
  * distributed under the License is distributed on an "AS IS" BASIS, 
  * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  * See the License for the specific language governing permissions and
  * limitations under the License.
  *
  ******************************************************************************
  */

/* Includes ------------------------------------------------------------------*/
#include "stm32l1xx_syscfg.h"
#include "stm32l1xx_rcc.h"

/** @addtogroup STM32L1xx_StdPeriph_Driver
  * @{
  */

/** @defgroup SYSCFG 
  * @brief SYSCFG driver modules
  * @{
  */

/* Private typedef -----------------------------------------------------------*/
/* Private define ------------------------------------------------------------*/
#define TIM_SELECT_MASK             ((uint32_t)0xFFFCFFFF) /*!< TIM select mask */
#define IC_ROUTING_MASK             ((uint32_t)0x0000000F) /*!< Input Capture routing mask */

/* Private macro -------------------------------------------------------------*/
/* Private variables ---------------------------------------------------------*/
/* Private function prototypes -----------------------------------------------*/
/* Private functions ---------------------------------------------------------*/

/** @defgroup SYSCFG_Private_Functions
  * @{
  */

/** @defgroup SYSCFG_Group1 SYSCFG Initialization and Configuration functions
 *  @brief   SYSCFG Initialization and Configuration functions
 *
@verbatim
 ===============================================================================
        ##### SYSCFG Initialization and Configuration functions #####
 ===============================================================================

@endverbatim
  * @{
  */

/**
  * @brief  Deinitializes the SYSCFG registers to their default reset values.
  * @param  None.
  * @retval None.
  * @Note: MEMRMP bits are not reset by APB2 reset.
  */
void SYSCFG_DeInit(void)
{
   RCC_APB2PeriphResetCmd(RCC_APB2Periph_SYSCFG, ENABLE);
   RCC_APB2PeriphResetCmd(RCC_APB2Periph_SYSCFG, DISABLE);
}

/**
  * @brief Deinitializes the RI registers to their default reset values.
  * @param  None.
  * @retval None.
  */
void SYSCFG_RIDeInit(void)
{
  RI->ICR     = ((uint32_t)0x00000000);    /*!< Set RI->ICR to reset value */
  RI->ASCR1   = ((uint32_t)0x00000000);    /*!< Set RI->ASCR1 to reset value */
  RI->ASCR2   = ((uint32_t)0x00000000);    /*!< Set RI->ASCR2 to reset value */
  RI->HYSCR1  = ((uint32_t)0x00000000);    /*!< Set RI->HYSCR1 to reset value */
  RI->HYSCR2  = ((uint32_t)0x00000000);    /*!< Set RI->HYSCR2 to reset value */
  RI->HYSCR3  = ((uint32_t)0x00000000);    /*!< Set RI->HYSCR3 to reset value */
  RI->HYSCR4  = ((uint32_t)0x00000000);    /*!< Set RI->HYSCR4 to reset value */
}

/**
  * @brief  Changes the mapping of the specified memory.
  * @param  SYSCFG_Memory: selects the memory remapping.
  *   This parameter can be one of the following values:
  *     @arg SYSCFG_MemoryRemap_Flash: Main Flash memory mapped at 0x00000000  
  *     @arg SYSCFG_MemoryRemap_SystemFlash: System Flash memory mapped at 0x00000000
  *     @arg SYSCFG_MemoryRemap_FSMC: FSMC memory mapped at 0x00000000  
  *     @arg SYSCFG_MemoryRemap_SRAM: Embedded SRAM mapped at 0x00000000
  * @retval None
  */
void SYSCFG_MemoryRemapConfig(uint8_t SYSCFG_MemoryRemap)
{
  /* Check the parameters */
  assert_param(IS_SYSCFG_MEMORY_REMAP_CONFING(SYSCFG_MemoryRemap));
  SYSCFG->MEMRMP = SYSCFG_MemoryRemap;
}

/**
  * @brief  Returns the boot mode as configured by user.
  * @param  None.
  * @retval The boot mode as configured by user. The returned value can be one 
  *         of the following values:
  *              - 0x00000000: Boot is configured in Main Flash memory
  *              - 0x00000100: Boot is configured in System Flash memory
  *              - 0x00000200: Boot is configured in FSMC memory
  *              - 0x00000300: Boot is configured in Embedded SRAM memory
  */
uint32_t SYSCFG_GetBootMode(void)
{
  return (SYSCFG->MEMRMP & SYSCFG_MEMRMP_BOOT_MODE);
}

/**
  * @brief  Control the internal pull-up on USB DP line.
  * @param  NewState: New state of the internal pull-up on USB DP line. 
  *   This parameter can be ENABLE: Connect internal pull-up on USB DP line.
  *                      or DISABLE: Disconnect internal pull-up on USB DP line.
  * @retval None
  */
void SYSCFG_USBPuCmd(FunctionalState NewState)
{
  /* Check the parameters */
  assert_param(IS_FUNCTIONAL_STATE(NewState));

  if (NewState != DISABLE)
  {
    /* Connect internal pull-up on USB DP line */
    SYSCFG->PMC |= (uint32_t) SYSCFG_PMC_USB_PU;
  }
  else
  {
    /* Disconnect internal pull-up on USB DP line */
    SYSCFG->PMC &= (uint32_t)(~SYSCFG_PMC_USB_PU);
  }
}

/**
  * @brief  Selects the GPIO pin used as EXTI Line.
  * @param  EXTI_PortSourceGPIOx : selects the GPIO port to be used as source 
  *                                for EXTI lines where x can be (A, B, C, D, E, F, G or H).
  * @param  EXTI_PinSourcex: specifies the EXTI line to be configured.
  *         This parameter can be EXTI_PinSourcex where x can be (0..15).
  * @retval None
  */
void SYSCFG_EXTILineConfig(uint8_t EXTI_PortSourceGPIOx, uint8_t EXTI_PinSourcex)
{
  uint32_t tmp = 0x00;

  /* Check the parameters */
  assert_param(IS_EXTI_PORT_SOURCE(EXTI_PortSourceGPIOx));
  assert_param(IS_EXTI_PIN_SOURCE(EXTI_PinSourcex));
  
  tmp = ((uint32_t)0x0F) << (0x04 * (EXTI_PinSourcex & (uint8_t)0x03));
  SYSCFG->EXTICR[EXTI_PinSourcex >> 0x02] &= ~tmp;
  SYSCFG->EXTICR[EXTI_PinSourcex >> 0x02] |= (((uint32_t)EXTI_PortSourceGPIOx) << (0x04 * (EXTI_PinSourcex & (uint8_t)0x03)));
}

/**
  * @}
  */

/** @defgroup SYSCFG_Group2 RI Initialization and Configuration functions
 *  @brief   RI Initialization and Configuration functions
 *
@verbatim   
 ===============================================================================
        ##### RI Initialization and Configuration functions #####
 ===============================================================================

@endverbatim
  * @{
  */

/**
  * @brief  Configures the routing interface to select which Timer to be routed.
  * @note   Routing capability can be applied only on one of the three timers
  *         (TIM2, TIM3 or TIM4) at a time.
  * @param  TIM_Select: Timer select.
  *   This parameter can be one of the following values:
  *     @arg TIM_Select_None: No timer selected and default Timer mapping is enabled.
  *     @arg TIM_Select_TIM2: Timer 2 Input Captures to be routed.
  *     @arg TIM_Select_TIM3: Timer 3 Input Captures to be routed.
  *     @arg TIM_Select_TIM4: Timer 4 Input Captures to be routed.
  * @retval None.
  */
void SYSCFG_RITIMSelect(uint32_t TIM_Select)
{
  uint32_t tmpreg = 0;

  /* Check the parameters */
  assert_param(IS_RI_TIM(TIM_Select));

  /* Get the old register value */
  tmpreg = RI->ICR;

  /* Clear the TIMx select bits */
  tmpreg &= TIM_SELECT_MASK;

  /* Select the Timer */
  tmpreg |= (TIM_Select);

  /* Write to RI->ICR register */
  RI->ICR = tmpreg;
}

/**
  * @brief  Configures the routing interface to map Input Capture 1, 2, 3 or 4
  *         to a selected I/O pin.
  * @param  RI_InputCapture selects which input capture to be routed.
  *   This parameter can be one (or combination) of the following parameters:
  *     @arg  RI_InputCapture_IC1: Input capture 1 is selected.
  *     @arg  RI_InputCapture_IC2: Input capture 2 is selected.
  *     @arg  RI_InputCapture_IC3: Input capture 3 is selected.
  *     @arg  RI_InputCapture_IC4: Input capture 4 is selected.
  * @param  RI_InputCaptureRouting: selects which pin to be routed to Input Capture.
  *   This parameter can be one of the following values:
  * @param  RI_InputCaptureRouting_0 to RI_InputCaptureRouting_15
  *     e.g.
  *       SYSCFG_RITIMSelect(TIM_Select_TIM2)
  *       SYSCFG_RITIMInputCaptureConfig(RI_InputCapture_IC1, RI_InputCaptureRouting_1)
  *       allows routing of Input capture IC1 of TIM2 to PA4.
  *       For details about correspondence between RI_InputCaptureRouting_x 
  *       and I/O pins refer to the parameters' description in the header file
  *       or refer to the product reference manual.
  * @note Input capture selection bits are not reset by this function.
  *       To reset input capture selection bits, use SYSCFG_RIDeInit() function.
  * @note The I/O should be configured in alternate function mode (AF14) using
  *       GPIO_PinAFConfig() function.
  * @retval None.
  */
void SYSCFG_RITIMInputCaptureConfig(uint32_t RI_InputCapture, uint32_t RI_InputCaptureRouting)
{
  uint32_t tmpreg = 0;

  /* Check the parameters */
  assert_param(IS_RI_INPUTCAPTURE(RI_InputCapture));
  assert_param(IS_RI_INPUTCAPTURE_ROUTING(RI_InputCaptureRouting));

  /* Get the old register value */
  tmpreg = RI->ICR;

  /* Select input captures to be routed */
  tmpreg |= (RI_InputCapture);

  if((RI_InputCapture & RI_InputCapture_IC1) == RI_InputCapture_IC1)
  {
    /* Clear the input capture select bits */
    tmpreg &= (uint32_t)(~IC_ROUTING_MASK);

    /* Set RI_InputCaptureRouting bits  */
    tmpreg |= (uint32_t)( RI_InputCaptureRouting);
  }

  if((RI_InputCapture & RI_InputCapture_IC2) == RI_InputCapture_IC2)
  {
    /* Clear the input capture select bits */
    tmpreg &= (uint32_t)(~(IC_ROUTING_MASK << 4));

    /* Set RI_InputCaptureRouting bits  */
    tmpreg |= (uint32_t)( (RI_InputCaptureRouting << 4));
  }

  if((RI_InputCapture & RI_InputCapture_IC3) == RI_InputCapture_IC3)
  {
    /* Clear the input capture select bits */
    tmpreg &= (uint32_t)(~(IC_ROUTING_MASK << 8));

    /* Set RI_InputCaptureRouting bits  */
    tmpreg |= (uint32_t)( (RI_InputCaptureRouting << 8));
  }

  if((RI_InputCapture & RI_InputCapture_IC4) == RI_InputCapture_IC4)
  {
    /* Clear the input capture select bits */
    tmpreg &= (uint32_t)(~(IC_ROUTING_MASK << 12));

    /* Set RI_InputCaptureRouting bits  */
    tmpreg |= (uint32_t)( (RI_InputCaptureRouting << 12));
  }

  /* Write to RI->ICR register */
  RI->ICR = tmpreg;
}

/**
  * @brief  Configures the Pull-up and Pull-down Resistors 
  * @param  RI_Resistor selects the resistor to connect. 
  *   This parameter can be  one of the following values:
  *     @arg RI_Resistor_10KPU: 10K pull-up resistor.
  *     @arg RI_Resistor_400KPU: 400K pull-up resistor.
  *     @arg RI_Resistor_10KPD: 10K pull-down resistor.
  *     @arg RI_Resistor_400KPD: 400K pull-down resistor.
  * @param  NewState: New state of the analog switch associated to the selected 
  *         resistor.
  *   This parameter can be:
  *      ENABLE so the selected resistor is connected
  *      or DISABLE so the selected resistor is disconnected.
  * @note To avoid extra power consumption, only one resistor should be enabled
  *       at a time.  
  * @retval None
  */
void SYSCFG_RIResistorConfig(uint32_t RI_Resistor, FunctionalState NewState)
{
  /* Check the parameters */
  assert_param(IS_RI_RESISTOR(RI_Resistor));
  assert_param(IS_FUNCTIONAL_STATE(NewState));
  
  if (NewState != DISABLE)
  {
    /* Enable the resistor */
    COMP->CSR |= (uint32_t) RI_Resistor;
  }
  else
  {
    /* Disable the Resistor */
    COMP->CSR &= (uint32_t) (~RI_Resistor);
  }
}

/**
  * @brief  Configures the ADC channels speed.
  * @param  RI_Channel selects the channel.
  *   This parameter can be  one of the following values:
  *     @arg RI_Channel_3: Channel 3 is selected.
  *     @arg RI_Channel_8: Channel 8 is selected.
  *     @arg RI_Channel_13: Channel 13 is selected.
  * @param  RI_ChannelSpeed: The speed of the selected ADC channel
  *   This parameter can be:
  *      RI_ChannelSpeed_Fast: The selected channel is a fast ADC channel 
  *      or RI_ChannelSpeed_Slow: The selected channel is a slow ADC channel.
  * @retval None
  */
void SYSCFG_RIChannelSpeedConfig(uint32_t RI_Channel, uint32_t RI_ChannelSpeed)
{
  /* Check the parameters */
  assert_param(IS_RI_CHANNEL(RI_Channel));
  assert_param(IS_RI_CHANNELSPEED(RI_ChannelSpeed));

  if(RI_ChannelSpeed != RI_ChannelSpeed_Fast)
  {
    /* Set the selected channel as a slow ADC channel */
    COMP->CSR &= (uint32_t) (~RI_Channel);
  }
  else
  {
    /* Set the selected channel as a fast ADC channel */
    COMP->CSR |= (uint32_t) (RI_Channel);
  }
}

/**
  * @brief  Close or Open the routing interface Input Output switches.
  * @param  RI_IOSwitch: selects the I/O analog switch number.
  *   This parameter can be one of the following values:
  * @param RI_IOSwitch_CH0 --> RI_IOSwitch_CH15.
  * @param RI_IOSwitch_CH18 --> RI_IOSwitch_CH25.
  * @param RI_IOSwitch_GR10_1 --> RI_IOSwitch_GR10_4.
  * @param RI_IOSwitch_GR6_1 --> RI_IOSwitch_GR6_2.
  * @param RI_IOSwitch_GR5_1 --> RI_IOSwitch_GR5_3.
  * @param RI_IOSwitch_GR4_1 --> RI_IOSwitch_GR4_3.
  * @param RI_IOSwitch_VCOMP
  * RI_IOSwitch_CH27
  * @param RI_IOSwitch_CH28 --> RI_IOSwitch_CH30
  * @param RI_IOSwitch_GR10_1 --> RI_IOSwitch_GR10_4
  * @param RI_IOSwitch_GR6_1
  * @param RI_IOSwitch_GR6_2
  * @param RI_IOSwitch_GR5_1 --> RI_IOSwitch_GR5_3
  * @param RI_IOSwitch_GR4_1 --> RI_IOSwitch_GR4_4
  * @param RI_IOSwitch_CH0b --> RI_IOSwitch_CH3b
  * @param RI_IOSwitch_CH6b --> RI_IOSwitch_CH12b
  * @param RI_IOSwitch_GR6_3
  * @param RI_IOSwitch_GR6_4
  * @param RI_IOSwitch_GR5_4
  
  * @param  NewState: New state of the analog switch. 
  *   This parameter can be 
  *     ENABLE so the Input Output switch is closed
  *     or DISABLE so the Input Output switch is open.
  * @retval None
  */
void SYSCFG_RIIOSwitchConfig(uint32_t RI_IOSwitch, FunctionalState NewState)
{
  uint32_t ioswitchmask = 0;
  
  /* Check the parameters */
  assert_param(IS_RI_IOSWITCH(RI_IOSwitch));
  
  /* Read Analog switch register index */
  ioswitchmask = RI_IOSwitch >> 31;
  
  /* Get Bits[30:0] of the IO switch */
  RI_IOSwitch  &= 0x7FFFFFFF;
  
  
  if (NewState != DISABLE)
  {
    if (ioswitchmask != 0)
    {
      /* Close the analog switches */
      RI->ASCR1 |= RI_IOSwitch;
    }
    else
    {
      /* Open the analog switches */
      RI->ASCR2 |= RI_IOSwitch;
    }
  }
  else
  {
    if (ioswitchmask != 0)
    {
      /* Close the analog switches */
      RI->ASCR1 &= (~ (uint32_t)RI_IOSwitch);
    }
    else
    {
      /* Open the analog switches */
      RI->ASCR2 &= (~ (uint32_t)RI_IOSwitch);
    }
  }
}

/**
  * @brief  Enable or disable the switch control mode.
  * @param  NewState: New state of the switch control mode. This parameter can
  *         be ENABLE: ADC analog switches closed if the corresponding 
  *                    I/O switch is also closed.
  *                    When using COMP1, switch control mode must be enabled.
  *         or DISABLE: ADC analog switches open or controlled by the ADC interface.
  *                    When using the ADC for acquisition, switch control mode 
  *                    must be disabled.
  * @note COMP1 comparator and ADC cannot be used at the same time since 
  *       they share the ADC switch matrix.
  * @retval None
  */
void SYSCFG_RISwitchControlModeCmd(FunctionalState NewState)
{
  /* Check the parameters */
  assert_param(IS_FUNCTIONAL_STATE(NewState));
  
  if (NewState != DISABLE)
  {
    /* Enable the Switch control mode */
    RI->ASCR1 |= (uint32_t) RI_ASCR1_SCM;
  }
  else
  {
    /* Disable the Switch control mode */
    RI->ASCR1 &= (uint32_t)(~RI_ASCR1_SCM);
  }
}

/**
  * @brief  Enable or disable Hysteresis of the input schmitt triger of Ports A..E
  *         When the I/Os are programmed in input mode by standard I/O port 
  *         registers, the Schmitt trigger and the hysteresis are enabled by default.
  *         When hysteresis is disabled, it is possible to read the 
  *         corresponding port with a trigger level of VDDIO/2.
  * @param  RI_Port: selects the GPIO Port.
  *   This parameter can be one of the following values:
  *     @arg RI_PortA: Port A is selected
  *     @arg RI_PortB: Port B is selected
  *     @arg RI_PortC: Port C is selected
  *     @arg RI_PortD: Port D is selected
  *     @arg RI_PortE: Port E is selected
  *     @arg RI_PortF: Port F is selected
  *     @arg RI_PortG: Port G is selected
  *  @param RI_Pin : Selects the pin(s) on which to enable or disable hysteresis.
  *    This parameter can any value from RI_Pin_x where x can be (0..15) or RI_Pin_All.
  *  @param  NewState new state of the Hysteresis.
  *   This parameter can be:
  *      ENABLE so the Hysteresis is on
  *      or DISABLE so the Hysteresis is off
  * @retval None
  */
void SYSCFG_RIHysteresisConfig(uint8_t RI_Port, uint16_t RI_Pin,
                             FunctionalState NewState)
{
  /* Check the parameters */
  assert_param(IS_RI_PORT(RI_Port));
  assert_param(IS_RI_PIN(RI_Pin));
  assert_param(IS_FUNCTIONAL_STATE(NewState));
  
  if(RI_Port == RI_PortA)
  {  
    if (NewState != DISABLE)
    {
      /* Hysteresis on */
      RI->HYSCR1 &= (uint32_t)~((uint32_t)RI_Pin);
    }
    else
    {
      /* Hysteresis off */
      RI->HYSCR1 |= (uint32_t) RI_Pin;
    }
  }
  
  else if(RI_Port == RI_PortB)
  {
  
    if (NewState != DISABLE)
    {
      /* Hysteresis on */
      RI->HYSCR1 &= (uint32_t) (~((uint32_t)RI_Pin) << 16);
    }
    else
    {
      /* Hysteresis off */
      RI->HYSCR1 |= (uint32_t) ((uint32_t)(RI_Pin) << 16);
    }
  }  
 
  else if(RI_Port == RI_PortC)
  {
  
    if (NewState != DISABLE)
    {
      /* Hysteresis on */
      RI->HYSCR2 &= (uint32_t) (~((uint32_t)RI_Pin));
    }
    else
    {
      /* Hysteresis off */
      RI->HYSCR2 |= (uint32_t) (RI_Pin );
    }
  } 
  else if(RI_Port == RI_PortD)
  {
    if (NewState != DISABLE)
    {
      /* Hysteresis on */
      RI->HYSCR2 &= (uint32_t) (~((uint32_t)RI_Pin) << 16);
    }
    else
    {
      /* Hysteresis off */
      RI->HYSCR2 |= (uint32_t) ((uint32_t)(RI_Pin) << 16);

    }
  }
  else if(RI_Port == RI_PortE)
  {
    if (NewState != DISABLE)
    {
      /* Hysteresis on */
      RI->HYSCR3 &= (uint32_t) (~((uint32_t)RI_Pin));
    }
    else
    {
      /* Hysteresis off */
      RI->HYSCR3 |= (uint32_t) (RI_Pin );
    }
  }
  else if(RI_Port == RI_PortF)
  {
    if (NewState != DISABLE)
    {
      /* Hysteresis on */
      RI->HYSCR3 &= (uint32_t) (~((uint32_t)RI_Pin) << 16);
    }
    else
    {
      /* Hysteresis off */
      RI->HYSCR3 |= (uint32_t) ((uint32_t)(RI_Pin) << 16);
    }
  }
  else /* RI_Port == RI_PortG */
  {
    if (NewState != DISABLE)
    {
      /* Hysteresis on */
      RI->HYSCR4 &= (uint32_t) (~((uint32_t)RI_Pin));
    }
    else
    {
      /* Hysteresis off */
      RI->HYSCR4 |= (uint32_t) (RI_Pin);
    }
  }
}

/**
  * @}
  */

/**
  * @}
  */ 

/**
  * @}
  */ 

/**
  * @}
  */
/************************ (C) COPYRIGHT STMicroelectronics *****END OF FILE****/
