/***************************************************************************//**
 * @file
 * @brief Board support package API for GPIO leds on STK's.
 * @version 4.2.1
 *******************************************************************************
 * @section License
 * <b>(C) Copyright 2014 Silicon Labs, http://www.silabs.com</b>
 *******************************************************************************
 *
 * This file is licensed under the Silabs License Agreement. See the file
 * "Silabs_License_Agreement.txt" for details. Before using this software for
 * any purpose, you must agree to the terms of that agreement.
 *
 ******************************************************************************/



#include "em_device.h"
#include "em_cmu.h"
#include "em_gpio.h"
#include "bsp.h"

#if defined( BSP_GPIO_LEDS )
/** @cond DO_NOT_INCLUDE_WITH_DOXYGEN */

typedef struct
{
  GPIO_Port_TypeDef   port;
  unsigned int        pin;
} tLedArray;

static const tLedArray ledArray[ BSP_NO_OF_LEDS ] = BSP_GPIO_LEDARRAY_INIT;

int BSP_LedsInit(void)
{
  int i;

  CMU_ClockEnable(cmuClock_HFPER, true);
  CMU_ClockEnable(cmuClock_GPIO, true);
  for ( i=0; i<BSP_NO_OF_LEDS; i++ )
  {
    GPIO_PinModeSet(ledArray[i].port, ledArray[i].pin, gpioModePushPull, 0);
  }
  return BSP_STATUS_OK;
}

uint32_t BSP_LedsGet(void)
{
  int i;
  uint32_t retVal, mask;

  for ( i=0, retVal=0, mask=0x1; i<BSP_NO_OF_LEDS; i++, mask <<= 1 )
  {
    if (GPIO_PinOutGet(ledArray[i].port, ledArray[i].pin))
      retVal |= mask;
  }
  return retVal;
}

int BSP_LedsSet(uint32_t leds)
{
  int i;
  uint32_t mask;

  for ( i=0, mask=0x1; i<BSP_NO_OF_LEDS; i++, mask <<= 1 )
  {
    if ( leds & mask )
      GPIO_PinOutSet(ledArray[i].port, ledArray[i].pin);
    else
      GPIO_PinOutClear(ledArray[i].port, ledArray[i].pin);
  }
  return BSP_STATUS_OK;
}

int BSP_LedClear(int ledNo)
{
  if ((ledNo >= 0) && (ledNo < BSP_NO_OF_LEDS))
  {
    GPIO_PinOutClear(ledArray[ledNo].port, ledArray[ledNo].pin);
    return BSP_STATUS_OK;
  }
  return BSP_STATUS_ILLEGAL_PARAM;
}

int BSP_LedGet(int ledNo)
{
  int retVal = BSP_STATUS_ILLEGAL_PARAM;

  if ((ledNo >= 0) && (ledNo < BSP_NO_OF_LEDS))
  {
    retVal = (int)GPIO_PinOutGet(ledArray[ledNo].port, ledArray[ledNo].pin);
  }
  return retVal;
}

int BSP_LedSet(int ledNo)
{
  if ((ledNo >= 0) && (ledNo < BSP_NO_OF_LEDS))
  {
    GPIO_PinOutSet(ledArray[ledNo].port, ledArray[ledNo].pin);
    return BSP_STATUS_OK;
  }
  return BSP_STATUS_ILLEGAL_PARAM;
}

int BSP_LedToggle(int ledNo)
{
  if ((ledNo >= 0) && (ledNo < BSP_NO_OF_LEDS))
  {
    GPIO_PinOutToggle(ledArray[ledNo].port, ledArray[ledNo].pin);
    return BSP_STATUS_OK;
  }
  return BSP_STATUS_ILLEGAL_PARAM;
}

/** @endcond */
#endif  /* BSP_GPIO_LEDS */
