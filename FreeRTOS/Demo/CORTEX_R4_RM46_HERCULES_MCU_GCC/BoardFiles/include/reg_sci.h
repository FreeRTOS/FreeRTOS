/** @file reg_sci.h
 *   @brief SCI Register Layer Header File
 *   @date 11-Dec-2018
 *   @version 04.07.01
 *
 *   This file contains:
 *   - Definitions
 *   - Types
 *   - Interface Prototypes
 *   .
 *   which are relevant for the SCI driver.
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

#ifndef __REG_SCI_H__
#define __REG_SCI_H__

#include "sys_common.h"
#include "reg_gio.h"

/* USER CODE BEGIN (0) */
/* USER CODE END */

/* Sci Register Frame Definition */

/** @struct sciBase
 *   @brief SCI Base Register Definition
 *
 *   This structure is used to access the SCI module registers.
 */

/** @typedef sciBASE_t
 *   @brief SCI Register Frame Type Definition
 *
 *   This type is used to access the SCI Registers.
 */
typedef volatile struct sciBase
{
    uint32 GCR0; /**< 0x0000 Global Control Register 0 */
    uint32 GCR1; /**< 0x0004 Global Control Register 1 */
    uint32 GCR2; /**< 0x0008 Global Control Register 2. Note: Applicable only to LIN – SCI
                    Compatibility Mode,Reserved for standalone SCI*/
    uint32 SETINT;       /**< 0x000C Set Interrupt Enable Register */
    uint32 CLEARINT;     /**< 0x0010 Clear Interrupt Enable Register */
    uint32 SETINTLVL;    /**< 0x0014 Set Interrupt Level Register */
    uint32 CLEARINTLVL;  /**< 0x0018 Set Interrupt Level Register */
    uint32 FLR;          /**< 0x001C Interrupt Flag Register */
    uint32 INTVECT0;     /**< 0x0020 Interrupt Vector Offset 0 */
    uint32 INTVECT1;     /**< 0x0024 Interrupt Vector Offset 1 */
    uint32 FORMAT;       /**< 0x0028 Format Control Register */
    uint32 BRS;          /**< 0x002C Baud Rate Selection Register */
    uint32 ED;           /**< 0x0030 Emulation Register */
    uint32 RD;           /**< 0x0034 Receive Data Buffer */
    uint32 TD;           /**< 0x0038 Transmit Data Buffer */
    uint32 PIO0;         /**< 0x003C Pin Function Register */
    uint32 PIO1;         /**< 0x0040 Pin Direction Register */
    uint32 PIO2;         /**< 0x0044 Pin Data In Register */
    uint32 PIO3;         /**< 0x0048 Pin Data Out Register */
    uint32 PIO4;         /**< 0x004C Pin Data Set Register */
    uint32 PIO5;         /**< 0x0050 Pin Data Clr Register */
    uint32 PIO6;         /**< 0x0054: Pin Open Drain Output Enable Register */
    uint32 PIO7;         /**< 0x0058: Pin Pullup/Pulldown Disable Register */
    uint32 PIO8;         /**< 0x005C: Pin Pullup/Pulldown Selection Register */
    uint32 rsdv2[ 12U ]; /**< 0x0060: Reserved                               */
    uint32 IODFTCTRL;    /**< 0x0090: I/O Error Enable Register */
} sciBASE_t;

/** @def sciREG
 *   @brief  Register Frame Pointer
 *
 *   This pointer is used by the SCI driver to access the sci module registers.
 */
#define sciREG     ( ( sciBASE_t * ) 0xFFF7E500U )

/** @def sciPORT
 *   @brief SCI GIO Port Register Pointer
 *
 *   Pointer used by the GIO driver to access I/O PORT of SCI
 *   (use the GIO drivers to access the port pins).
 */
#define sciPORT    ( ( gioPORT_t * ) 0xFFF7E540U )

/** @def scilinREG
 *   @brief SCILIN (LIN - Compatibility Mode)  Register Frame Pointer
 *
 *   This pointer is used by the SCI driver to access the sci module registers.
 */
#define scilinREG  ( ( sciBASE_t * ) 0xFFF7E400U )

/** @def scilinPORT
 *   @brief SCILIN (LIN - Compatibility Mode)  Register Frame Pointer
 *
 *   Pointer used by the GIO driver to access I/O PORT of LIN
 *   (use the GIO drivers to access the port pins).
 */
#define scilinPORT ( ( gioPORT_t * ) 0xFFF7E440U )

/* USER CODE BEGIN (1) */
/* USER CODE END */

#endif /* ifndef __REG_SCI_H__ */
