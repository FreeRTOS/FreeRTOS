/**
  ******************************************************************************
  * @file    icc_measure_Ram.c
  * @author  Microcontroller Division
  * @version V1.0.3
  * @date    May-2013
  * @brief   Ram functions used for ICC current measurments
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
  * <h2><center>&copy; COPYRIGHT 2011 STMicroelectronics</center></h2>
  */
 
/* Includes ------------------------------------------------------------------*/
#include "misc.h"
#include "stm32l1xx.h"
#include "stm32l1xx_adc.h"
#include "stm32l1xx_lcd.h"
#include "stm32l1xx_rcc.h"
#include "stm32l1xx_rtc.h"
#include "stm32l1xx_pwr.h"
#include "stm32l1xx_gpio.h"
#include "discover_board.h"
#include "icc_measure.h"
#include "discover_functions.h"
#include "stm32l1xx_conf.h"

#define CR_DS_MASK               ((uint32_t)0xFFFFFFFC)


#if   (defined ( __CC_ARM ))
  #define __RAMFUNC void          
#elif (defined (__ICCARM__))
  #define __RAMFUNC  __ramfunc void
#elif defined   (  __GNUC__  )
#define __RAMFUNC void __attribute__((section(".data")))
#endif
/**
  * @brief  Enable or disable the power down mode during RUN mode .
  * @param  NewState: new state of the power down mode during RUN mode.
  *   This parameter can be: ENABLE or DISABLE.
  * @retval None
  */
__RAMFUNC RAM_FLASH_RUNPowerDownCmd(FunctionalState NewState)
{

  if (NewState != DISABLE)
  {
     /* Unlock the RUN_PD bit */
     FLASH->PDKEYR = FLASH_PDKEY1;
     FLASH->PDKEYR = FLASH_PDKEY2;

   /* Set the RUN_PD bit in  FLASH_ACR register to put Flash in power down mode */
     FLASH->ACR |= (uint32_t)FLASH_ACR_RUN_PD;
  }
  else
  {
    /* Clear the RUN_PD bit in  FLASH_ACR register to put Flash in idle  mode */
    FLASH->ACR &= (uint32_t)(~(uint32_t)FLASH_ACR_RUN_PD);
  }

}

/**
  * @brief  Enters/Exits the Low Power Run mode.
  * @param  NewState: new state of the Low Power Run mode.
  *   This parameter can be: ENABLE or DISABLE.
  * @retval None
  */
__RAMFUNC RAM_PWR_LowPowerRunModeCmd(FunctionalState NewState)
{

  if (NewState != DISABLE)
  {
    PWR->CR |= PWR_CR_LPSDSR;
    PWR->CR |= PWR_CR_LPRUN;
  }
  else
  {
    PWR->CR &= (uint32_t)~((uint32_t)PWR_CR_LPRUN);
    PWR->CR &= (uint32_t)~((uint32_t)PWR_CR_LPSDSR);
  }
}

/**
  * @brief Function in RAM for Low Power RUN current measurment
  * @caller ADC_Icc_Test
  * @param None
  * @retval None
  */
__RAMFUNC EnterLPRUNModeRAM(void)
{
  
  RAM_FLASH_RUNPowerDownCmd(ENABLE);
  RAM_PWR_LowPowerRunModeCmd(ENABLE);
    
  /* The application Run with delay */
  GPIO_LOW(CTN_GPIO_PORT,CTN_CNTEN_GPIO_PIN);
  
  do{
    __NOP();  __NOP();    __NOP();  __NOP();
    __NOP();  __NOP();    __NOP();  __NOP();
    __NOP();  __NOP();    __NOP();  __NOP();
    __NOP();  __NOP();    __NOP();  __NOP();
    __NOP();  __NOP();    __NOP();  __NOP();
    __NOP();  __NOP();    __NOP();  __NOP();
    __NOP();  __NOP();    __NOP();  __NOP();
    __NOP();  __NOP();    __NOP();  __NOP();
  } while((USERBUTTON_GPIO_PORT->IDR & USERBUTTON_GPIO_PIN) == 0);
  
  
  RAM_FLASH_RUNPowerDownCmd(DISABLE);
  RAM_PWR_LowPowerRunModeCmd(DISABLE);
}

/**
  * @brief Function in RAM for Low Power Sleep current measurment 
  * @caller ADC_Icc_Test
  * @param None
  * @retval None
  */
__RAMFUNC EnterLPSLEEPModeRAM(void)
{
  uint32_t tmpreg = 0;
   
  RAM_FLASH_RUNPowerDownCmd(ENABLE);
  RAM_PWR_LowPowerRunModeCmd(ENABLE);
  
  /* The application Run with delay */
  GPIO_LOW(CTN_GPIO_PORT,CTN_CNTEN_GPIO_PIN);

  /* Select the regulator state in Sleep mode ---------------------------------*/
  tmpreg = PWR->CR;

  /* Clear PDDS and LPDSR bits */
  tmpreg &= CR_DS_MASK;
  
  /* Set LPDSR bit according to PWR_Regulator value */
  tmpreg |= PWR_Regulator_LowPower;
  
  /* Store the new value */
  PWR->CR = tmpreg;
  
   /* Clear SLEEPDEEP bit of Cortex System Control Register */
  SCB->SCR &= (uint32_t)~((uint32_t)SCB_SCR_SLEEPDEEP);

    /* Request Wait For Event */
   __WFE();
  
  RAM_FLASH_RUNPowerDownCmd(DISABLE);
  RAM_PWR_LowPowerRunModeCmd(DISABLE);
}

/**
  * @brief Function in RAM for Sleep current measurment 
  * @caller ADC_Icc_Test
  * @param None
  * @retval None
  */

__RAMFUNC EnterSLEEPModeRAM(void)
{
  uint32_t tmpreg = 0;
   
  RAM_FLASH_RUNPowerDownCmd(ENABLE);
  RAM_PWR_LowPowerRunModeCmd(ENABLE);
  
  /* Select the regulator state in Sleep mode ---------------------------------*/
  tmpreg = PWR->CR;

  /* Clear PDDS and LPDSR bits */
  tmpreg &= CR_DS_MASK;
  
  /* Set LPDSR bit according to PWR_Regulator value */
  tmpreg |= PWR_Regulator_LowPower;
  
  /* Store the new value */
  PWR->CR = tmpreg;
  
   /* Clear SLEEPDEEP bit of Cortex System Control Register */
  SCB->SCR &= (uint32_t)~((uint32_t)SCB_SCR_SLEEPDEEP);

  
  /* Request Wait For Event */
   __WFE();
  
  RAM_FLASH_RUNPowerDownCmd(DISABLE);
  RAM_PWR_LowPowerRunModeCmd(DISABLE);
}



/******************* (C) COPYRIGHT 2011 STMicroelectronics *****END OF FILE****/
