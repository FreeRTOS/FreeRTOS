/** @file reg_gio.h
 *   @brief GIO Register Layer Header File
 *   @date 11-Dec-2018
 *   @version 04.07.01
 *
 *   This file contains:
 *   - Definitions
 *   - Types
 *   - Interface Prototypes
 *   .
 *   which are relevant for the GIO driver.
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

#ifndef __REG_GIO_H__
#define __REG_GIO_H__

#include "sys_common.h"

/* USER CODE BEGIN (0) */
/* USER CODE END */

/* Gio Register Frame Definition */

/** @struct gioBase
 *   @brief GIO Base Register Definition
 *
 *   This structure is used to access the GIO module registers.
 */

/** @typedef gioBASE_t
 *   @brief GIO Register Frame Type Definition
 *
 *   This type is used to access the GIO Registers.
 */
typedef volatile struct gioBase
{
    uint32 GCR0;   /**< 0x0000: Global Control Register */
    uint32 rsvd;   /**< 0x0004: Reserved*/
    uint32 INTDET; /**< 0x0008: Interrupt Detect Register*/
    uint32 POL;    /**< 0x000C: Interrupt Polarity Register */
    uint32 ENASET; /**< 0x0010: Interrupt Enable Set Register */
    uint32 ENACLR; /**< 0x0014: Interrupt Enable Clear Register */
    uint32 LVLSET; /**< 0x0018: Interrupt Priority Set Register */
    uint32 LVLCLR; /**< 0x001C: Interrupt Priority Clear Register */
    uint32 FLG;    /**< 0x0020: Interrupt Flag Register */
    uint32 OFF1;   /**< 0x0024: Interrupt Offset A Register */
    uint32 OFF2;   /**< 0x0028: Interrupt Offset B Register */
    uint32 EMU1;   /**< 0x002C: Emulation 1 Register */
    uint32 EMU2;   /**< 0x0030: Emulation 2 Register */
} gioBASE_t;

/** @struct gioPort
 *   @brief GIO Port Register Definition
 */

/** @typedef gioPORT_t
 *   @brief GIO Port Register Type Definition
 *
 *   This type is used to access the GIO Port Registers.
 */
typedef volatile struct gioPort
{
    uint32 DIR;    /**< 0x0000: Data Direction Register */
    uint32 DIN;    /**< 0x0004: Data Input Register */
    uint32 DOUT;   /**< 0x0008: Data Output Register */
    uint32 DSET;   /**< 0x000C: Data Output Set Register */
    uint32 DCLR;   /**< 0x0010: Data Output Clear Register */
    uint32 PDR;    /**< 0x0014: Open Drain Register */
    uint32 PULDIS; /**< 0x0018: Pullup Disable Register */
    uint32 PSL;    /**< 0x001C: Pull Up/Down Selection Register */
} gioPORT_t;

/** @def gioREG
 *   @brief GIO Register Frame Pointer
 *
 *   This pointer is used by the GIO driver to access the gio module registers.
 */
#define gioREG   ( ( gioBASE_t * ) 0xFFF7BC00U )

/** @def gioPORTA
 *   @brief GIO Port (A) Register Pointer
 *
 *   Pointer used by the GIO driver to access PORTA
 */
#define gioPORTA ( ( gioPORT_t * ) 0xFFF7BC34U )

/** @def gioPORTB
 *   @brief GIO Port (B) Register Pointer
 *
 *   Pointer used by the GIO driver to access PORTB
 */
#define gioPORTB ( ( gioPORT_t * ) 0xFFF7BC54U )

/* USER CODE BEGIN (1) */
/* USER CODE END */

#endif /* ifndef __REG_GIO_H__ */
