/* ----------------------------------------------------------------------------
 *         SAM Software Package License 
 * ----------------------------------------------------------------------------
 * Copyright (c) 2011, Atmel Corporation
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the disclaimer below.
 *
 * Atmel's name may not be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * DISCLAIMER: THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * ----------------------------------------------------------------------------
 */

/**
 * \file
 *
 * Collection of LEDs for using the USB device controller on AT91
 * Microcontrollers.
 */

#ifndef USBDLEDS_H
#define USBDLEDS_H

/*----------------------------------------------------------------------------
 *      Headers
 *----------------------------------------------------------------------------*/

#include "board.h"

/** \addtogroup usbd_hal
 *@{
 */
/*----------------------------------------------------------------------------
 *      Constants
 *----------------------------------------------------------------------------*/

/** \addtogroup usbd_leds USB Device LEDs
 *      @{
 * This page lists the LEDs used in the USB %device driver.
 *
 * - USBD_LEDPOWER
 * - USBD_LEDUSB
 * - USBD_LEDOTHER
 */

/** LED for indicating that the device is powered. */
#define USBD_LEDPOWER                   0
/** LED for custom usage. */
#define USBD_LEDOTHER                   1
/**     @}*/

/**@}*/

#endif //#ifndef USBDLEDS_H

