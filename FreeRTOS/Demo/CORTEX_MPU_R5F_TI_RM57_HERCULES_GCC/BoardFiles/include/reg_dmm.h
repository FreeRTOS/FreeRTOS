/** @file reg_dmm.h
 *   @brief DMM Register Layer Header File
 *   @date 11-Dec-2018
 *   @version 04.07.01
 *
 *   This file contains:
 *   - Definitions
 *   - Types
 *   - Interface Prototypes
 *   .
 *   which are relevant for the DMM driver.
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

#ifndef __REG_DMM_H__
#define __REG_DMM_H__

#include "sys_common.h"
#include "reg_gio.h"

/* USER CODE BEGIN (0) */
/* USER CODE END */

/* Dmm Register Frame Definition */
/** @struct dmmBase
 *   @brief DMM Base Register Definition
 *
 *   This structure is used to access the DMM module registers.
 */
/** @typedef dmmBASE_t
 *   @brief DMM Register Frame Type Definition
 *
 *   This type is used to access the DMM Registers.
 */

typedef volatile struct dmmBase
{
    uint32 GLBCTRL;   /**< 0x0000: Global control register 0         */
    uint32 INTSET;    /**< 0x0004: DMM Interrupt Set Register        */
    uint32 INTCLR;    /**< 0x0008: DMM Interrupt Clear Register      */
    uint32 INTLVL;    /**< 0x000C: DMM Interrupt Level Register      */
    uint32 INTFLG;    /**< 0x0010: DMM Interrupt Flag Register       */
    uint32 OFF1;      /**< 0x0014: DMM Interrupt Offset 1 Register           */
    uint32 OFF2;      /**< 0x0018: DMM Interrupt Offset 2 Register           */
    uint32 DDMDEST;   /**< 0x001C: DMM Direct Data Mode Destination Register   */
    uint32 DDMBL;     /**< 0x0020: DMM Direct Data Mode Blocksize Register           */
    uint32 DDMPT;     /**< 0x0024: DMM Direct Data Mode Pointer Register        */
    uint32 INTPT;     /**< 0x0028: DMM Direct Data Mode Interrupt Pointer Register     */
    uint32 DEST0REG1; /**< 0x002C: DMM Destination 0 Region 1           */
    uint32 DEST0BL1;  /**< 0x0030: DMM Destination 0 Blocksize 1                     */
    uint32 DEST0REG2; /**< 0x0034: DMM Destination 0 Region 2                  */
    uint32 DEST0BL2;  /**< 0x0038: DMM Destination 0 Blocksize 2                 */
    uint32 DEST1REG1; /**< 0x003C: DMM Destination 1 Region 1                  */
    uint32 DEST1BL1;  /**< 0x0040: DMM Destination 1 Blocksize 1                 */
    uint32 DEST1REG2; /**< 0x0044: DMM Destination 1 Region 2                   */
    uint32 DEST1BL2;  /**< 0x0048: DMM Destination 1 Blocksize 2                  */
    uint32 DEST2REG1; /**< 0x004C: DMM Destination 2 Region 1                  */
    uint32 DEST2BL1;  /**< 0x0050: DMM Destination 2 Blocksize 1                  */
    uint32 DEST2REG2; /**< 0x0054: DMM Destination 2 Region 2  */
    uint32 DEST2BL2;  /**< 0x0058: DMM Destination 2 Blocksize 2   */
    uint32 DEST3REG1; /**< 0x005C: DMM Destination 3 Region 1 */
    uint32 DEST3BL1;  /**< 0x0060: DMM Destination 3 Blocksize 1                       */
    uint32 DEST3REG2; /**< 0x0064: DMM Destination 3 Region 2              */
    uint32 DEST3BL2;  /**< 0x0068: DMM Destination 3 Blocksize 2              */
    uint32 PC0;       /**< 0x006C: DMM Pin Control 0                          */
    uint32 PC1;       /**< 0x0070: DMM Pin Control 1              */
    uint32 PC2;       /**< 0x0074: DMM Pin Control 2              */
    uint32 PC3;       /**< 0x0078: DMM Pin Control 3              */
    uint32 PC4;       /**< 0x007C: DMM Pin Control 4              */
    uint32 PC5;       /**< 0x0080: DMM Pin Control 5              */
    uint32 PC6;       /**< 0x0084: DMM Pin Control 6              */
    uint32 PC7;       /**< 0x0088: DMM Pin Control 7              */
    uint32 PC8;       /**< 0x008C: DMM Pin Control 8              */
} dmmBASE_t;

/** @def dmmREG
 *   @brief DMM Register Frame Pointer
 *
 *   This pointer is used by the DMM driver to access the DMM module registers.
 */
#define dmmREG  ( ( dmmBASE_t * ) 0xFFFFF700U )

/** @def dmmPORT
 *   @brief DMM Port Register Pointer
 *
 *   Pointer used by the GIO driver to access I/O PORT of DMM
 *   (use the GIO drivers to access the port pins).
 */
#define dmmPORT ( ( gioPORT_t * ) 0xFFFFF770U )

/* USER CODE BEGIN (1) */
/* USER CODE END */

#endif
