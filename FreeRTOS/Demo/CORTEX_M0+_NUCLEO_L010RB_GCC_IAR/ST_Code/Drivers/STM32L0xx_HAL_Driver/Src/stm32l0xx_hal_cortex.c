/**
  ******************************************************************************
  * @file    stm32l0xx_hal_cortex.c
  * @author  MCD Application Team
  * @brief   CORTEX HAL module driver.
  *          This file provides firmware functions to manage the following 
  *          functionalities of the CORTEX:
  *           + Initialization and Configuration functions
  *           + Peripheral Control functions 
  *
  @verbatim  
  ==============================================================================
                        ##### How to use this driver #####
  ==============================================================================
    [..]  
    *** How to configure Interrupts using CORTEX HAL driver ***
    ===========================================================
    [..]     
    This section provides functions allowing to configure the NVIC interrupts (IRQ).
    The Cortex M0+ exceptions are managed by CMSIS functions.
      (#) Enable and Configure the priority of the selected IRQ Channels. 
             The priority can be 0..3. 

        -@- Lower priority values gives higher priority.
        -@- Priority Order:
            (#@) Lowest priority.
            (#@) Lowest hardware priority (IRQn position).  
    
     (#)  Configure the priority of the selected IRQ Channels using HAL_NVIC_SetPriority() 

     (#)  Enable the selected IRQ Channels using HAL_NVIC_EnableIRQ() 
      
    [..]  
    *** How to configure Systick using CORTEX HAL driver ***
    ========================================================
    [..]
    Setup SysTick Timer for time base.
           
   (+) The HAL_SYSTICK_Config()function calls the SysTick_Config() function which
       is a CMSIS function that:
        (++) Configures the SysTick Reload register with value passed as function parameter.
        (++) Configures the SysTick IRQ priority to the lowest value (0x03).
        (++) Resets the SysTick Counter register.
        (++) Configures the SysTick Counter clock source to be Core Clock Source (HCLK).
        (++) Enables the SysTick Interrupt.
        (++) Starts the SysTick Counter.
	
   (+) You can change the SysTick Clock source to be HCLK_Div8 by calling the function
       HAL_SYSTICK_CLKSourceConfig(SYSTICK_CLKSOURCE_HCLK_DIV8) just after the
       HAL_SYSTICK_Config() function call. The HAL_SYSTICK_CLKSourceConfig() function is defined
       inside the stm32l0xx_hal_cortex.c file.

   (+) You can change the SysTick IRQ priority by calling the
       HAL_NVIC_SetPriority(SysTick_IRQn,...) function just after the HAL_SYSTICK_Config() function 
       call. The HAL_NVIC_SetPriority() call the NVIC_SetPriority() function which is a CMSIS function.

   (+) To adjust the SysTick time base, use the following formula:
                            
       Reload Value = SysTick Counter Clock (Hz) x  Desired Time base (s)
       (++) Reload Value is the parameter to be passed for HAL_SYSTICK_Config() function
       (++) Reload Value should not exceed 0xFFFFFF
   
  @endverbatim
  ******************************************************************************
  * @attention
  *
  * <h2><center>&copy; Copyright(c) 2016 STMicroelectronics.
  * All rights reserved.</center></h2>
  *
  * This software component is licensed by ST under BSD 3-Clause license,
  * the "License"; You may not use this file except in compliance with the
  * License. You may obtain a copy of the License at:
  *                        opensource.org/licenses/BSD-3-Clause
  *
  ******************************************************************************  
  */

/* Includes ------------------------------------------------------------------*/
#include "stm32l0xx_hal.h"

/** @addtogroup STM32L0xx_HAL_Driver
  * @{
  */

#ifdef HAL_CORTEX_MODULE_ENABLED

/** @addtogroup CORTEX
  * @brief CORTEX HAL module driver
  * @{
  */

/* Private types -------------------------------------------------------------*/
/* Private variables ---------------------------------------------------------*/
/* Private constants ---------------------------------------------------------*/
/* Private macros ------------------------------------------------------------*/
/* Private functions ---------------------------------------------------------*/
/* Exported functions --------------------------------------------------------*/

/** @addtogroup CORTEX_Exported_Functions
  * @{
  */


/** @addtogroup CORTEX_Exported_Functions_Group1 Initialization and de-initialization functions 
 *  @brief    Initialization and Configuration functions 
 *
@verbatim    
  ==============================================================================
              ##### Initialization and Configuration functions #####
  ==============================================================================
    [..]
      This section provides the CORTEX HAL driver functions allowing to configure Interrupts
      Systick functionalities 

@endverbatim
  * @{
  */

/**
  * @brief  Sets the priority of an interrupt.
  * @param  IRQn External interrupt number .
  *         This parameter can be an enumerator of  IRQn_Type enumeration
  *         (For the complete STM32 Devices IRQ Channels list, please refer to stm32l0xx.h file)
  * @param  PreemptPriority The pre-emption priority for the IRQn channel.
  *         This parameter can be a value between 0 and 3.
  *         A lower priority value indicates a higher priority 
  * @param  SubPriority the subpriority level for the IRQ channel.
  *         with stm32l0xx devices, this parameter is a dummy value and it is ignored, because 
  *         no subpriority supported in Cortex M0+ based products.   
  * @retval None
  */
void HAL_NVIC_SetPriority(IRQn_Type IRQn, uint32_t PreemptPriority, uint32_t SubPriority)
{ 
    /* Check the parameters */
  assert_param(IS_NVIC_PREEMPTION_PRIORITY(PreemptPriority));
  NVIC_SetPriority(IRQn,PreemptPriority);
}

/**
  * @brief  Enable a device specific interrupt in the NVIC interrupt controller.
  * @note   To configure interrupts priority correctly, the NVIC_PriorityGroupConfig()
  *         function should be called before. 
  * @param  IRQn External interrupt number .
  *         This parameter can be an enumerator of  IRQn_Type enumeration
  *         (For the complete STM32 Devices IRQ Channels list, please refer to stm32l0xx.h file)  
  * @retval None
  */
void HAL_NVIC_EnableIRQ(IRQn_Type IRQn)
{
  /* Check the parameters */
  assert_param(IS_NVIC_DEVICE_IRQ(IRQn));
  
  /* Enable interrupt */
  NVIC_EnableIRQ(IRQn);
}

/**
  * @brief  Disable a device specific interrupt in the NVIC interrupt controller.
  * @param  IRQn External interrupt number .
  *         This parameter can be an enumerator of IRQn_Type enumeration
  *         (For the complete STM32 Devices IRQ Channels list, please refer to stm32l0xx.h file)  
  * @retval None
  */
void HAL_NVIC_DisableIRQ(IRQn_Type IRQn)
{
    /* Check the parameters */
  assert_param(IS_NVIC_DEVICE_IRQ(IRQn));
  
  /* Disable interrupt */
  NVIC_DisableIRQ(IRQn);
}

/**
  * @brief  Initiate a system reset request to reset the MCU.
  * @retval None
  */
void HAL_NVIC_SystemReset(void)
{
  /* System Reset */
  NVIC_SystemReset();
}

/**
  * @brief  Initialize the System Timer with interrupt enabled and start the System Tick Timer (SysTick)
  *         Counter is in free running mode to generate periodic interrupts.
  * @param  TicksNumb Specifies the ticks Number of ticks between two interrupts.
  * @retval status:  - 0  Function succeeded.
  *                  - 1  Function failed.
  */
uint32_t HAL_SYSTICK_Config(uint32_t TicksNumb)
{
   return SysTick_Config(TicksNumb);
}
/**
  * @}
  */

/** @addtogroup CORTEX_Exported_Functions_Group2 Peripheral Control functions 
 *  @brief   Cortex control functions 
 *
@verbatim   
  ==============================================================================
                      ##### Peripheral Control functions #####
  ==============================================================================  
    [..]
      This subsection provides a set of functions allowing to control the CORTEX
      (NVIC, SYSTICK) functionalities. 
 
      
@endverbatim
  * @{
  */


/**
  * @brief  Gets the priority of an interrupt.
  * @param  IRQn External interrupt number.
  *         This parameter can be an enumerator of IRQn_Type enumeration
  *         (For the complete STM32 Devices IRQ Channels list, please refer to the appropriate CMSIS device file (stm32l0xxxx.h))
  * @retval None
  */
uint32_t HAL_NVIC_GetPriority(IRQn_Type IRQn)
{
  /* Get priority for Cortex-M system or device specific interrupts */
  return NVIC_GetPriority(IRQn);
}

/**
  * @brief  Sets Pending bit of an external interrupt.
  * @param  IRQn External interrupt number
  *         This parameter can be an enumerator of IRQn_Type enumeration
  *         (For the complete STM32 Devices IRQ Channels list, please refer to stm32l0xx.h file)  
  * @retval None
  */
void HAL_NVIC_SetPendingIRQ(IRQn_Type IRQn)
{ 
  /* Set interrupt pending */
  NVIC_SetPendingIRQ(IRQn);
}

/**
  * @brief  Get Pending Interrupt (read the pending register in the NVIC 
  *         and return the pending bit for the specified interrupt).
  * @param  IRQn External interrupt number .
  *          This parameter can be an enumerator of  IRQn_Type enumeration
  *          (For the complete STM32 Devices IRQ Channels list, please refer to stm32l0xx.h file)  
  * @retval status: - 0  Interrupt status is not pending.
  *                 - 1  Interrupt status is pending.
  */
uint32_t HAL_NVIC_GetPendingIRQ(IRQn_Type IRQn)
{ 
  /* Return 1 if pending else 0 */
  return NVIC_GetPendingIRQ(IRQn);
}

/**
  * @brief  Clear the pending bit of an external interrupt.
  * @param  IRQn External interrupt number .
  *         This parameter can be an enumerator of IRQn_Type enumeration
  *         (For the complete STM32 Devices IRQ Channels list, please refer to stm32l0xx.h file)  
  * @retval None
  */
void HAL_NVIC_ClearPendingIRQ(IRQn_Type IRQn)
{ 
  /* Clear pending interrupt */
  NVIC_ClearPendingIRQ(IRQn);
}


/**
  * @brief  Configure the SysTick clock source.
  * @param  CLKSource specifies the SysTick clock source.
  *          This parameter can be one of the following values:
  *             @arg SYSTICK_CLKSOURCE_HCLK_DIV8: AHB clock divided by 8 selected as SysTick clock source.
  *             @arg SYSTICK_CLKSOURCE_HCLK: AHB clock selected as SysTick clock source.
  * @retval None
  */
void HAL_SYSTICK_CLKSourceConfig(uint32_t CLKSource)
{
  /* Check the parameters */
  assert_param(IS_SYSTICK_CLK_SOURCE(CLKSource));
  if (CLKSource == SYSTICK_CLKSOURCE_HCLK)
  {
    SysTick->CTRL |= SYSTICK_CLKSOURCE_HCLK;
  }
  else
  {
    SysTick->CTRL &= ~SYSTICK_CLKSOURCE_HCLK;
  }
}

/**
  * @brief  Handle SYSTICK interrupt request.
  * @retval None
  */
void HAL_SYSTICK_IRQHandler(void)
{
  HAL_SYSTICK_Callback();
}

/**
  * @brief  SYSTICK callback.
  * @retval None
  */
__weak void HAL_SYSTICK_Callback(void)
{
  /* NOTE : This function should not be modified, when the callback is needed,
            the HAL_SYSTICK_Callback could be implemented in the user file
   */
}

#if (__MPU_PRESENT == 1U)
/**
  * @brief  Disable the MPU.
  * @retval None
  */
void HAL_MPU_Disable(void)
{

  /*Data Memory Barrier setup */
  __DMB();
  /* Disable the MPU */
  MPU->CTRL = 0;
}

/**
  * @brief  Enable the MPU.
  * @param  MPU_Control Specifies the control mode of the MPU during hard fault,
  *          NMI, FAULTMASK and privileged access to the default memory
  *          This parameter can be one of the following values:
  *            @arg MPU_HFNMI_PRIVDEF_NONE
  *            @arg MPU_HARDFAULT_NMI
  *            @arg MPU_PRIVILEGED_DEFAULT
  *            @arg MPU_HFNMI_PRIVDEF
  * @retval None
  */

void HAL_MPU_Enable(uint32_t MPU_Control)
{
  /* Enable the MPU */
   MPU->CTRL   = MPU_Control | MPU_CTRL_ENABLE_Msk;
  /* Data Synchronization Barrier setup */
  __DSB();
  /* Instruction Synchronization Barrier setup */
  __ISB();

}

/**
  * @brief  Initialize and configure the Region and the memory to be protected.
  * @param  MPU_Init Pointer to a MPU_Region_InitTypeDef structure that contains
  *                the initialization and configuration information.
  * @retval None
  */
void HAL_MPU_ConfigRegion(MPU_Region_InitTypeDef *MPU_Init)
{
  /* Check the parameters */
  assert_param(IS_MPU_REGION_NUMBER(MPU_Init->Number));
  assert_param(IS_MPU_REGION_ENABLE(MPU_Init->Enable));

  /* Set the Region number */
  MPU->RNR = MPU_Init->Number;

  if ((MPU_Init->Enable) == MPU_REGION_ENABLE)
  {
    /* Check the parameters */
    assert_param(IS_MPU_INSTRUCTION_ACCESS(MPU_Init->DisableExec));
    assert_param(IS_MPU_REGION_PERMISSION_ATTRIBUTE(MPU_Init->AccessPermission));
    assert_param(IS_MPU_ACCESS_SHAREABLE(MPU_Init->IsShareable));
    assert_param(IS_MPU_ACCESS_CACHEABLE(MPU_Init->IsCacheable));
    assert_param(IS_MPU_ACCESS_BUFFERABLE(MPU_Init->IsBufferable));
    assert_param(IS_MPU_SUB_REGION_DISABLE(MPU_Init->SubRegionDisable));
    assert_param(IS_MPU_REGION_SIZE(MPU_Init->Size));

    /* Set the base adsress and set the 4 LSB to 0 */
    MPU->RBAR = (MPU_Init->BaseAddress) & 0xfffffff0U;

    /* Fill the field RASR */
    MPU->RASR = ((uint32_t)MPU_Init->DisableExec        << MPU_RASR_XN_Pos)   |
                ((uint32_t)MPU_Init->AccessPermission   << MPU_RASR_AP_Pos)   |
                ((uint32_t)MPU_Init->IsShareable        << MPU_RASR_S_Pos)    |
                ((uint32_t)MPU_Init->IsCacheable        << MPU_RASR_C_Pos)    |
                ((uint32_t)MPU_Init->IsBufferable       << MPU_RASR_B_Pos)    |
                ((uint32_t)MPU_Init->SubRegionDisable   << MPU_RASR_SRD_Pos)  |
                ((uint32_t)MPU_Init->Size               << MPU_RASR_SIZE_Pos) |
                ((uint32_t)MPU_Init->Enable             << MPU_RASR_ENABLE_Pos);
  }
  else
  {
    MPU->RBAR = 0x00U;
    MPU->RASR = 0x00U;
  }
}
#endif /* __MPU_PRESENT */


/**
  * @}
  */

/**
  * @}
  */

/**
  * @}
  */

#endif /* HAL_CORTEX_MODULE_ENABLED */
/**
  * @}
  */

/************************ (C) COPYRIGHT STMicroelectronics *****END OF FILE****/

