/**
  ******************************************************************************
  * @file    stm32l1xx_syscfg.c
  * @author  MCD Application Team
  * @version V1.0.0RC1
  * @date    07/02/2010
  * @brief   This file provides all the SYSCFG and RI firmware functions.
  ******************************************************************************
  * @copy
  *
  * THE PRESENT FIRMWARE WHICH IS FOR GUIDANCE ONLY AIMS AT PROVIDING CUSTOMERS
  * WITH CODING INFORMATION REGARDING THEIR PRODUCTS IN ORDER FOR THEM TO SAVE
  * TIME. AS A RESULT, STMICROELECTRONICS SHALL NOT BE HELD LIABLE FOR ANY
  * DIRECT, INDIRECT OR CONSEQUENTIAL DAMAGES WITH RESPECT TO ANY CLAIMS ARISING
  * FROM THE CONTENT OF SUCH FIRMWARE AND/OR THE USE MADE BY CUSTOMERS OF THE
  * CODING INFORMATION CONTAINED HEREIN IN CONNECTION WITH THEIR PRODUCTS.
  *
  * <h2><center>&copy; COPYRIGHT 2010 STMicroelectronics</center></h2>
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

/** @defgroup SYSCFG_Private_TypesDefinitions
  * @{
  */ 
/**
  * @}
  */ 

/** @defgroup SYSCFG_Private_Defines
  * @{
  */ 
  
#define RI_ICR_RESET_VALUE          ((uint32_t)0x00000000) /*!< ICR Reset value */
#define RI_ASCR1_RESET_VALUE        ((uint32_t)0x00000000) /*!< ASCR1 Reset value */
#define RI_ASCR2_RESET_VALUE        ((uint32_t)0x00000000) /*!< ASCR2 Reset value */
#define RI_HYSCR1_RESET_VALUE       ((uint32_t)0x00000000) /*!< HYSCR1 Reset value */
#define RI_HYSCR2_RESET_VALUE       ((uint32_t)0x00000000) /*!< HYSCR2 Reset value */
#define RI_HYSCR3_RESET_VALUE       ((uint32_t)0x00000000) /*!< HYSCR3 Reset value */

#define TIM_SELECT_MASK             ((uint32_t)0xFFFCFFFF) /*!< TIM select mask */
#define IC_ROUTING_MASK             ((uint32_t)0x0000000F) /*!< Input Capture routing mask */

/**
  * @}
  */ 

/** @defgroup SYSCFG_Private_Macros
  * @{
  */ 
/**
  * @}
  */ 

/** @defgroup SYSCFG_Private_Variables
  * @{
  */ 
/**
  * @}
  */ 

/** @defgroup SYSCFG_Private_FunctionPrototypes
  * @{
  */ 
/**
  * @}
  */ 

/** @defgroup SYSCFG_Private_Functions
  * @{
  */ 

/**
  * @brief  Deinitializes the syscfg registers to their default reset values.
  * @param  None
  * @retval None
  * @ Note: MEMRMP bits are not reset by APB2 reset.
  */
void SYSCFG_DeInit(void)
{
   RCC_APB2PeriphResetCmd(RCC_APB2Periph_SYSCFG, ENABLE);
   RCC_APB2PeriphResetCmd(RCC_APB2Periph_SYSCFG, DISABLE);
}

/**
  * @brief  Changes the mapping of the specified pin.
  * @param  SYSCFG_Memory: selects the memory remapping.
  *   This parameter can be one of the following values:
  *     @arg SYSCFG_MemoryRemap_Flash: Main Flash memory mapped at 0x00000000  
  *     @arg SYSCFG_MemoryRemap_SystemFlash: System Flash memory mapped at 0x00000000
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
  * @brief  Control the internal pull-up on USB DP line.
  * @param  NewState: New state of the switch control mode. 
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
  *                                for EXTI lines where x can be (A, B, C, D, E or H).
  * @param  EXTI_PinSourcex: specifies the EXTI line to be configured.
  *   This parameter can be EXTI_PinSourcex where x can be (0..15)
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
  * @brief Deinitializes the RI registers to their default reset values.
  * @param  None
  * @retval None
  */
void SYSCFG_RIDeInit(void)
{
  RI->ICR     = RI_ICR_RESET_VALUE;         /*!< Set RI->ICR to reset value */
  RI->ASCR1   = RI_ASCR1_RESET_VALUE;       /*!< Set RI->ASCR1 to reset value */  
  RI->ASCR2   = RI_ASCR2_RESET_VALUE;       /*!< Set RI->ASCR2 to reset value */  
  RI->HYSCR1  = RI_HYSCR1_RESET_VALUE;      /*!< Set RI->HYSCR1 to reset value */
  RI->HYSCR2  = RI_HYSCR2_RESET_VALUE;      /*!< Set RI->HYSCR2 to reset value */
  RI->HYSCR3  = RI_HYSCR3_RESET_VALUE;      /*!< Set RI->HYSCR3 to reset value */
}

/**
  * @brief  Configures the routing interface to select which Timer to be routed.
  * @param  TIM_Select: Timer select.
  *   This parameter can be one of the following values:
  *     @arg TIM_Select_None : No timer selected
  *     @arg TIM_Select_TIM2 : Timer 2 selected 
  *     @arg TIM_Select_TIM3 : Timer 3 selected 
  *     @arg TIM_Select_TIM4 : Timer 4 selected 
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
  * @brief  Configures the routing interface to select which Timer Input Capture
  *         to be routed to a selected pin.
  * @param  RI_InputCapture selects which input capture to be routed.
  *   This parameter can be one of the following values:
  *     @arg  RI_InputCapture_IC1: Input capture 1 is slected.
  *     @arg  RI_InputCapture_IC2: Input capture 2 is slected.
  *     @arg  RI_InputCapture_IC3: Input capture 3 is slected.
  *     @arg  RI_InputCapture_IC4: Input capture 4 is slected.
  * @param  RI_InputCaptureRouting: selects which pin to be routed to Input Capture.
  *   This parameter can be one of the following values:
  *     @arg  RI_InputCaptureRouting_0 to RI_InputCaptureRouting_15
  * @Note Input capture selection bits are not reset by this function.
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
  *     @arg RI_Resistor_10KPU : 10K pull-up resistor
  *     @arg RI_Resistor_400KPU : 400K pull-up resistor 
  *     @arg RI_Resistor_10KPD : 10K pull-down resistor 
  *     @arg RI_Resistor_400KPD : 400K pull-down resistor
  * @param  NewState: New state of the analog switch associated to the selected resistor.
  *   This parameter can be:
  *      ENABLE so the selected resistor is connected
  *   or DISABLE so the selected resistor is disconnected
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
  * @brief  Close or Open the routing interface Input Output switches.
  * @param  RI_IOSwitch: selects the I/O analog switch number.
  *   This parameter can be one of the following values:
  *     @arg RI_IOSwitch_CH0 --> RI_IOSwitch_CH15
  *     @argRI_IOSwitch_CH18 --> RI_IOSwitch_CH25
  *     @arg RI_IOSwitch_GR10_1 --> RI_IOSwitch_GR10_4
  *     @arg RI_IOSwitch_GR6_1 --> RI_IOSwitch_GR6_2
  *     @arg RI_IOSwitch_GR5_1 --> RI_IOSwitch_GR5_3
  *     @arg RI_IOSwitch_GR4_1 --> RI_IOSwitch_GR4_3
  *     @arg  RI_IOSwitch_VCOMP
  * @param  NewState: New state of the analog switch. 
  *   This parameter can be 
  *     ENABLE so the Input Output switch is closed
  *     or DISABLE so the Input Output switch is open
  * @retval None
  */
void SYSCFG_RIIOSwitchConfig(uint32_t RI_IOSwitch, FunctionalState NewState)
{
  uint32_t IOSwitchmask = 0;
  
  /* Check the parameters */
  assert_param(IS_RI_IOSWITCH(RI_IOSwitch));
  
  /* Read Analog switch register index*/
  IOSwitchmask = RI_IOSwitch >> 28;
  
  /** Get Bits[27:0] of the IO switch */
  RI_IOSwitch  &= 0x0FFFFFFF;
  
  
  if (NewState != DISABLE)
  { 
    if (IOSwitchmask != 0)
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
    if (IOSwitchmask != 0)
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
  *         or DISABLE: ADC analog switches open or controlled by the ADC interface.
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
  * @param  RI_Port: selects the GPIO Port.
  *   This parameter can be one of the following values:
  *     @arg RI_PortA : Port A is selected
  *     @arg RI_PortB : Port B is selected
  *     @arg RI_PortC : Port C is selected
  *     @arg RI_PortD : Port D is selected
  *     @arg RI_PortE : Port E is selected
  *  @param RI_Pin : Selects the pin(s) on which to enable or disable hysteresis.
  *    This parameter can any value from RI_Pin_x where x can be (0..15) or RI_Pin_All.
  *  @param  NewState new state of the Hysteresis.
  *   This parameter can be:
  *      ENABLE so the Hysteresis is on
  *   or DISABLE so the Hysteresis is off
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
  else /* RI_Port == RI_PortE */
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
/******************* (C) COPYRIGHT 2010 STMicroelectronics *****END OF FILE****/   
