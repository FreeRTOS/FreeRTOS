/*
 * Copyright (c) 2017-2019, Texas Instruments Incorporated
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * *  Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *
 * *  Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * *  Neither the name of Texas Instruments Incorporated nor the names of
 *    its contributors may be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO,
 * THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 * PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR
 * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS;
 * OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
 * WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR
 * OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */
/*!****************************************************************************
 *  @file       EMACMSP432E4.h
 *  @brief      Ethernet Media Access Control (EMAC) MSP432E4 Driver
 *
 ******************************************************************************
 */

#ifndef custom_drivers_emac_EMACMSP432E4__include
#define custom_drivers_emac_EMACMSP432E4__include

/* @cond */
/*!
 * @brief Required by ti/devices/msp432e4/inc/msp432.h
 */
#ifndef __MSP432E411Y__
#define __MSP432E411Y__ 1
#endif

#include <stdint.h>
#include <ti/devices/msp432e4/inc/msp432.h>
#include <ti/devices/msp432e4/driverlib/pin_map.h>
/* @endcond */

#include <ti/drivers/gpio/GPIOMSP432E4.h>

/* FreeRTOS+TCP includes. */

#ifdef __cplusplus
extern "C" {
#endif



/*!
 * @brief PF0 is used for EN0LED0
 */
#define EMACMSP432E4_PF0_EN0LED0 GPIOMSP432E4_pinConfigMask(GPIOMSP432E4_PORTF, 0, GPIO_PF0_EN0LED0)

/*!
 * @brief PK4 is used for EN0LED0
 */
#define EMACMSP432E4_PK4_EN0LED0 GPIOMSP432E4_pinConfigMask(GPIOMSP432E4_PORTK, 4, GPIO_PK4_EN0LED0)

/*!
 * @brief PF4 is used for EN0LED1
 */
#define EMACMSP432E4_PF4_EN0LED1 GPIOMSP432E4_pinConfigMask(GPIOMSP432E4_PORTF, 4, GPIO_PF4_EN0LED1)

/*!
 * @brief PK6 is used for EN0LED1
 */
#define EMACMSP432E4_PK6_EN0LED1 GPIOMSP432E4_pinConfigMask(GPIOMSP432E4_PORTK, 6, GPIO_PK6_EN0LED1)

/*!
 * @brief PF1 is used for EN0LED2
 */
#define EMACMSP432E4_PF1_EN0LED2 GPIOMSP432E4_pinConfigMask(GPIOMSP432E4_PORTF, 1, GPIO_PF1_EN0LED2)

/*!
 * @brief PK5 is used for EN0LED2
 */
#define EMACMSP432E4_PK5_EN0LED2 GPIOMSP432E4_pinConfigMask(GPIOMSP432E4_PORTK, 5, GPIO_PK5_EN0LED2)


/*!
 *  @brief  EMACMSP432E4 Hardware attributes
 *
 */
typedef struct {
    /*! @brief Base address of the EMAC peripheral. */
    uint32_t baseAddr;

    /*!
     *  @brief The EMAC peripheral's interrupt number.
     */
    uint32_t intNum;

    /*!
     *  @brief The EMAC peripheral's interrupt priority.
     *
     *  The interrupt priority is operating system dependent.
     *  This value is passed unmodified to the underlying interrupt handler
     *  creation code.
     */
    uint32_t intPriority;

    /*!
     *  @brief Pin connected to an LED used to indicate the Ethernet link
     *  is nominal.
     */
    uint32_t led0Pin;

    /*!
     *  @brief Pin connected to an LED used to indicate the Ethernet transmit
     *  (TX) and receive (RX) activity.
     */
    uint32_t led1Pin;

     /*!
      *  @brief Pointer to a MAC address.
      *
      *  If this points to a value of @p ff:ff:ff:ff:ff:ff, the driver reads
      *  the MAC address stored in flash. Otherwise, the value pointed to is
      *  used. An example declaration is provided below.
      *
      *  @code
      *  uint8_t macAddress[6] = {0x01, 0x1A, 0xB6, 0x02, 0xC4, 0xE5};
      *  @endcode
      *
      */
    uint8_t *macAddress;

} EMACMSP432E4_HWAttrs;


#ifdef __cplusplus
}
#endif

#endif /* custom_drivers_emac_EMACMSP432E4__include */
