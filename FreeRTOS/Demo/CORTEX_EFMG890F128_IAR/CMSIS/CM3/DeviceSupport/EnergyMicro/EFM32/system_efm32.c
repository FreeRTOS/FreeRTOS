/**************************************************************************//**
 * @file
 * @brief CMSIS Cortex-M3 Peripheral Access Layer for EFM32 devices
 *
 * @author Energy Micro AS
 * @version 1.0.2
 ******************************************************************************
 * @section License
 * <b>(C) Copyright 2009 Energy Micro AS, http://www.energymicro.com</b>
 ******************************************************************************
 *
 * This source code is the property of Energy Micro AS. The source and compiled
 * code may only be used on Energy Micro "EFM32" microcontrollers.
 *
 * This copyright notice may not be removed from the source code nor changed.
 *
 * DISCLAIMER OF WARRANTY/LIMITATION OF REMEDIES: Energy Micro AS has no
 * obligation to support this Software. Energy Micro AS is providing the
 * Software "AS IS", with no express or implied warranties of any kind,
 * including, but not limited to, any implied warranties of merchantability
 * or fitness for any particular purpose or warranties against infringement
 * of any proprietary rights of a third party.
 *
 * Energy Micro AS will not be liable for any consequential, incidental, or
 * special damages, or any other relief, or for any claim by any third party,
 * arising from your use of this Software.
 *
 *****************************************************************************/

#include <stdint.h>
#include "efm32.h"

uint32_t SystemCoreClock;     /**< System Clock Frequency (Core Clock)  */

#ifndef EFM32_HFXO_FREQ
#define EFM32_HFXO_FREQ 32000000
#endif
#ifndef EFM32_LFXO_FREQ 
#define EFM32_LFXO_FREQ 32768
#endif
#ifndef EFM32_LFRCO_FREQ
#define EFM32_LFRCO_FREQ 32768
#endif

/**************************************************************************//**
 * @brief Initialize the system
 *
 * @param  none
 * @return none
 *
 * @brief  Setup the microcontroller system.
 *         Initialize the System and update the SystemCoreClock variable.
 *****************************************************************************/
void SystemInit(void)
{
#if EFM32_AUXHFROCO_ENABLE
  CMU_TypeDef *cmu = CMU;

  /* Enable clocks to debug modules in Cortex */
  /* This will enable Debug Trace and MSC Flash programming clocks */
  cmu->OSCENCMD = CMU_OSCENCMD_AUXHFRCOEN;
#endif
}

/**************************************************************************//**
 * @brief Update SystemCoreClock variable
 *
 * @param  none
 * @return none
 *
 * @brief  Updates the SystemCoreClock with current core Clock
 *         retrieved from cpu registers.
 *****************************************************************************/
void SystemCoreClockUpdate(void)
{
  CMU_TypeDef *cmu = CMU;
  uint32_t inputClock;

  /* Check source for core clock */
  switch (cmu->STATUS &
          (CMU_STATUS_HFRCOSEL |
           CMU_STATUS_HFXOSEL |
           CMU_STATUS_LFRCOSEL |
           CMU_STATUS_LFXOSEL))
  {
  case CMU_STATUS_HFXOSEL:
    inputClock = EFM32_HFXO_FREQ;
    break;
  case CMU_STATUS_LFRCOSEL:
    inputClock = EFM32_LFRCO_FREQ;
    break;
  case CMU_STATUS_LFXOSEL:
    inputClock = EFM32_LFXO_FREQ;
    break;
  case CMU_STATUS_HFRCOSEL:
  default:
    switch ((cmu->HFRCOCTRL & _CMU_HFRCOCTRL_BAND_MASK) >> _CMU_HFRCOCTRL_BAND_SHIFT)
    {
    case _CMU_HFRCOCTRL_BAND_28MHZ:
      inputClock = 28000000;
      break;
    case _CMU_HFRCOCTRL_BAND_21MHZ:
      inputClock = 21000000;
      break;
    case _CMU_HFRCOCTRL_BAND_14MHZ:
      inputClock = 14000000;
      break;
    case _CMU_HFRCOCTRL_BAND_11MHZ:
      inputClock = 11000000;
      break;
    case _CMU_HFRCOCTRL_BAND_7MHZ:
      inputClock = 7000000;
      break;
    case _CMU_HFRCOCTRL_BAND_1MHZ:
      inputClock = 1500000;
      break;
    default:
      inputClock = 0;
      break;
    }
    break;
  }
  /* Adjust according to clock divisor */
  SystemCoreClock = inputClock / (1<<((cmu->HFCORECLKDIV & _CMU_HFCORECLKDIV_MASK)>>_CMU_HFCORECLKDIV_HFCORECLKDIV_SHIFT));
}

