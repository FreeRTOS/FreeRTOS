/**************************************************************************//**
 * @file
 * @brief API for enabling SWO and ETM trace.
 * @version 4.2.1
 ******************************************************************************
 * @section License
 * <b>(C) Copyright 2014 Silicon Labs, http://www.silabs.com</b>
 *******************************************************************************
 *
 * This file is licensed under the Silabs License Agreement. See the file
 * "Silabs_License_Agreement.txt" for details. Before using this software for
 * any purpose, you must agree to the terms of that agreement.
 *
 ******************************************************************************/



#include <stdbool.h>
#include "em_device.h"
#include "em_gpio.h"
#include "em_cmu.h"
#include "bsp_trace.h"
#include "bsp.h"

#if defined( BSP_ETM_TRACE ) && defined( ETM_PRESENT )
/**************************************************************************//**
 * @brief Configure EFM32 for ETM trace output.
 * @note You need to configure ETM trace on kit config menu as well!
 *****************************************************************************/
void BSP_TraceEtmSetup(void)
{
  /* Enable peripheral clocks */
  CMU->HFCORECLKEN0 |= CMU_HFCORECLKEN0_LE;
  CMU->HFPERCLKEN0  |= CMU_HFPERCLKEN0_GPIO;
  CMU->OSCENCMD      = CMU_OSCENCMD_AUXHFRCOEN;

  /* Wait until AUXHFRCO clock is ready */
  while (!(CMU->STATUS & CMU_STATUS_AUXHFRCORDY)) ;

  /* Enable Port D, pins 3,4,5,6 for ETM Trace Data output */
  GPIO->P[3].MODEL = (GPIO->P[3].MODEL & ~_GPIO_P_MODEL_MODE3_MASK) | GPIO_P_MODEL_MODE3_PUSHPULL;
  GPIO->P[3].MODEL = (GPIO->P[3].MODEL & ~_GPIO_P_MODEL_MODE4_MASK) | GPIO_P_MODEL_MODE4_PUSHPULL;
  GPIO->P[3].MODEL = (GPIO->P[3].MODEL & ~_GPIO_P_MODEL_MODE5_MASK) | GPIO_P_MODEL_MODE5_PUSHPULL;
  GPIO->P[3].MODEL = (GPIO->P[3].MODEL & ~_GPIO_P_MODEL_MODE6_MASK) | GPIO_P_MODEL_MODE6_PUSHPULL;

  /* Enable Port D, pin 7 for DBG_TCLK */
  GPIO->P[3].MODEL = (GPIO->P[3].MODEL & ~_GPIO_P_MODEL_MODE7_MASK) | GPIO_P_MODEL_MODE7_PUSHPULL;

  /* Configure trace output for alternate location */
  GPIO->ROUTE = GPIO->ROUTE | GPIO_ROUTE_TCLKPEN | GPIO_ROUTE_TD0PEN | GPIO_ROUTE_TD1PEN
                | GPIO_ROUTE_TD2PEN | GPIO_ROUTE_TD3PEN
                | GPIO_ROUTE_ETMLOCATION_LOC0;
}
#endif

#if defined( _GPIO_ROUTE_SWOPEN_MASK ) || defined( _GPIO_ROUTEPEN_SWVPEN_MASK )
/**************************************************************************//**
 * @brief Configure trace output for energyAware Profiler
 * @note  Enabling trace will add 80uA current for the EFM32_Gxxx_STK.
 *        DK's needs to be initialized with SPI-mode:
 * @verbatim BSP_Init(BSP_INIT_DK_SPI); @endverbatim
 *****************************************************************************/
void BSP_TraceSwoSetup(void)
{
  /* Enable GPIO clock */
#if defined( _CMU_HFPERCLKEN0_GPIO_MASK )
  CMU->HFPERCLKEN0 |= CMU_HFPERCLKEN0_GPIO;
#elif defined( _CMU_HFBUSCLKEN0_GPIO_MASK )
  CMU->HFBUSCLKEN0 |= CMU_HFBUSCLKEN0_GPIO;
#endif

  /* Enable Serial wire output pin */
#if defined( _GPIO_ROUTE_SWOPEN_MASK )
  GPIO->ROUTE |= GPIO_ROUTE_SWOPEN;
#elif defined( _GPIO_ROUTEPEN_SWVPEN_MASK )
  GPIO->ROUTEPEN |= GPIO_ROUTEPEN_SWVPEN;
#endif

  /* Set correct location */
#if defined( _GPIO_ROUTE_SWOPEN_MASK )
  GPIO->ROUTE = (GPIO->ROUTE & ~(_GPIO_ROUTE_SWLOCATION_MASK)) | BSP_TRACE_SWO_LOCATION;
#elif defined( _GPIO_ROUTEPEN_SWVPEN_MASK )
  GPIO->ROUTELOC0 = (GPIO->ROUTELOC0 & ~(_GPIO_ROUTELOC0_SWVLOC_MASK)) | BSP_TRACE_SWO_LOCATION;
#endif

  /* Enable output on correct pin. */
  TRACE_ENABLE_PINS();

  /* Enable debug clock AUXHFRCO */
  CMU->OSCENCMD = CMU_OSCENCMD_AUXHFRCOEN;

  /* Wait until clock is ready */
  while (!(CMU->STATUS & CMU_STATUS_AUXHFRCORDY)) ;

  /* Enable trace in core debug */
  CoreDebug->DHCSR |= CoreDebug_DHCSR_C_DEBUGEN_Msk;
  CoreDebug->DEMCR |= CoreDebug_DEMCR_TRCENA_Msk;

  /* Enable PC and IRQ sampling output */
  DWT->CTRL = 0x400113FF;

  /* Set TPIU prescaler to 16. */
  TPI->ACPR = 15;

  /* Set protocol to NRZ */
  TPI->SPPR = 2;

  /* Disable continuous formatting */
  TPI->FFCR = 0x100;

  /* Unlock ITM and output data */
  ITM->LAR = 0xC5ACCE55;
  ITM->TCR = 0x10009;

  /* ITM Channel 0 is used for UART output */
  ITM->TER |= (1UL << 0);
}
#endif


#if defined( _GPIO_ROUTE_SWOPEN_MASK ) || defined( _GPIO_ROUTEPEN_SWVPEN_MASK )
/**************************************************************************//**
 * @brief  Profiler configuration.
 * @return true if energyAware Profiler/SWO is enabled, false if not
 * @note   If first word of the user page is zero, this will not
 *         enable SWO profiler output.
 *****************************************************************************/
bool BSP_TraceProfilerSetup(void)
{
  volatile uint32_t *userData = (uint32_t *) USER_PAGE;

  /* Check magic "trace" word in user page */
  if (*userData == 0x00000000UL)
  {
    return false;
  }
  else
  {
    BSP_TraceSwoSetup();
    return true;
  }
}
#endif
