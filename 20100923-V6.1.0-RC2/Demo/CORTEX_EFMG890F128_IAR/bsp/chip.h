/**************************************************************************//**
 * @file
 * @brief Chip initialization, SW workarounds for chip errata issues
 * @author Energy Micro AS
 * @version 1.1.1
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

#ifndef __CHIP_H
#define __CHIP_H

#include <stdint.h>

/**************************************************************************//**
 * @brief Chip errata workarounds
 *****************************************************************************/
static inline void CHIP_init(void)
{
  uint32_t          rev;
  volatile uint32_t *reg;

  rev = *(volatile uint32_t *)(0x0FE081FC);
  /* Engineering Sample calibration setup */
  if ((rev >> 24) == 0)
  {
    reg   = (volatile uint32_t *) 0x400CA00C;
    *reg &= ~(0x70UL);
    /* DREG */
    reg   = (volatile uint32_t *) 0x400C6020;
    *reg &= ~(0xE0000000UL);
    *reg |= ~(7 << 25);
  }
  if ((rev >> 24) <= 1)
  {
    /* DREG */
    reg   = (volatile uint32_t *) 0x400C6020;
    *reg &= ~(0x00001F80UL);
    /* Update CMU reset values */
    reg  = (volatile uint32_t *) 0x400C8040;
    *reg = 0;
    reg  = (volatile uint32_t *) 0x400C8044;
    *reg = 0;
    reg  = (volatile uint32_t *) 0x400C8058;
    *reg = 0;
    reg  = (volatile uint32_t *) 0x400C8060;
    *reg = 0;
    reg  = (volatile uint32_t *) 0x400C8078;
    *reg = 0;
  }
}

#endif
