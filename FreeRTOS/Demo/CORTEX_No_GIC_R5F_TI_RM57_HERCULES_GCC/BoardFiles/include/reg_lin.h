/** @file reg_lin.h
 *   @brief LIN Register Layer Header File
 *   @date 11-Dec-2018
 *   @version 04.07.01
 *
 *   This file contains:
 *   - Definitions
 *   - Types
 *   - Interface Prototypes
 *   .
 *   which are relevant for the LIN driver.
 */

/*
 * Copyright (C) 2009-2018 Texas Instruments Incorporated - www.ti.com
 *
 *
 *  Redistribution and use in source and binary forms, with or without
 *  modification, are permitted provided that the following conditions
 *  are met:
 *
 *    Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *
 *    Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the
 *    distribution.
 *
 *    Neither the name of Texas Instruments Incorporated nor the names of
 *    its contributors may be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 *  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 *  "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 *  LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 *  A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 *  OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 *  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 *  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 *  DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 *  THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 *  (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 *  OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 */

#ifndef __REG_LIN_H__
#define __REG_LIN_H__

#include "sys_common.h"
#include "reg_gio.h"

/* USER CODE BEGIN (0) */
/* USER CODE END */

/* Lin Register Frame Definition */
/** @struct linBase
 *   @brief LIN Base Register Definition
 *
 *   This structure is used to access the LIN module registers.
 */
/** @typedef linBASE_t
 *   @brief LIN  Register Frame Type Definition
 *
 *   This type is used to access the LIN Registers.
 */

typedef volatile struct linBase
{
    uint32 GCR0;        /**< 0x0000: Global control register 0              */
    uint32 GCR1;        /**< 0x0004: Global control register 1              */
    uint32 GCR2;        /**< 0x0008: Global control register 2              */
    uint32 SETINT;      /**< 0x000C: Set interrupt enable register          */
    uint32 CLEARINT;    /**< 0x0010: Clear interrupt enable register        */
    uint32 SETINTLVL;   /**< 0x0014: Set interrupt level register           */
    uint32 CLEARINTLVL; /**< 0x0018: Set interrupt level register           */
    uint32 FLR;         /**< 0x001C: interrupt flag register                */
    uint32 INTVECT0;    /**< 0x0020: interrupt vector Offset 0              */
    uint32 INTVECT1;    /**< 0x0024: interrupt vector Offset 1              */
    uint32 FORMAT;      /**< 0x0028: Format Control Register                */
    uint32 BRS;         /**< 0x002C: Baud rate selection register           */
    uint32 ED;          /**< 0x0030: Emulation register                     */
    uint32 RD;          /**< 0x0034: Receive data register                  */
    uint32 TD;          /**< 0x0038: Transmit data register                 */
    uint32 PIO0;        /**< 0x003C: Pin function register                  */
    uint32 PIO1;        /**< 0x0040: Pin direction register                 */
    uint32 PIO2;        /**< 0x0044: Pin data in register                   */
    uint32 PIO3;        /**< 0x0048: Pin data out register                  */
    uint32 PIO4;        /**< 0x004C: Pin data set register                  */
    uint32 PIO5;        /**< 0x0050: Pin data clr register                  */
    uint32 PIO6;        /**< 0x0054: Pin open drain output enable register  */
    uint32 PIO7;        /**< 0x0058: Pin pullup/pulldown disable register   */
    uint32 PIO8;        /**< 0x005C: Pin pullup/pulldown selection register */
    uint32 COMP;        /**< 0x0060: Compare register                       */
    uint8 RDx[ 8U ];    /**< 0x0064-0x0068: RX buffer register              */
    uint32 MASK;        /**< 0x006C: Mask register                          */
    uint32 ID;          /**< 0x0070: Identification Register                */
    uint8 TDx[ 8U ];    /**< 0x0074-0x0078: TX buffer register              */
    uint32 MBRSR;       /**< 0x007C: Maximum baud rate selection register   */
    uint32 rsvd1[ 4U ]; /**< 0x0080 - 0x8C: Reserved                               */
    uint32 IODFTCTRL;   /**< 0x0090: IODFT loopback register                */
} linBASE_t;

/** @def linREG1
 *   @brief LIN1 Register Frame Pointer
 *
 *   This pointer is used by the LIN driver to access the lin1 module registers.
 */
#define linREG1  ( ( linBASE_t * ) 0xFFF7E400U )

/** @def linPORT1
 *   @brief LIN1 GIO Port Register Pointer
 *
 *   Pointer used by the GIO driver to access I/O PORT of LIN1
 *   (use the GIO drivers to access the port pins).
 */
#define linPORT1 ( ( gioPORT_t * ) 0xFFF7E440U )

/** @def linREG2
 *   @brief LIN2 Register Frame Pointer
 *
 *   This pointer is used by the LIN driver to access the lin2 module registers.
 */
#define linREG2  ( ( linBASE_t * ) 0xFFF7E600U )

/** @def linPORT2
 *   @brief LIN2 GIO Port Register Pointer
 *
 *   Pointer used by the GIO driver to access I/O PORT of LIN2
 *   (use the GIO drivers to access the port pins).
 */
#define linPORT2 ( ( gioPORT_t * ) 0xFFF7E640U )

/* USER CODE BEGIN (1) */
/* USER CODE END */

#endif
