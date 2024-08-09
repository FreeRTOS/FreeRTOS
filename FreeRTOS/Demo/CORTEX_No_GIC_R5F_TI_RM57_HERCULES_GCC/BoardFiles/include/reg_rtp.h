/** @file reg_rtp.h
 *   @brief RTP Register Layer Header File
 *   @date 11-Dec-2018
 *   @version 04.07.01
 *
 *   This file contains:
 *   - Definitions
 *   - Types
 *   - Interface Prototypes
 *   .
 *   which are relevant for the RTP driver.
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

#ifndef __REG_RTP_H__
#define __REG_RTP_H__

#include "sys_common.h"
#include "reg_gio.h"

/* USER CODE BEGIN (0) */
/* USER CODE END */

/* Rtp Register Frame Definition */
/** @struct rtpBase
 *   @brief RTP Base Register Definition
 *
 *   This structure is used to access the RTP module registers.
 */
/** @typedef rtpBASE_t
 *   @brief RTP Register Frame Type Definition
 *
 *   This type is used to access the RTP Registers.
 */
typedef volatile struct rtpBase
{
    uint32 GLBCTRL;     /**< 0x0000: RTP Global Control Register             */
    uint32 TRENA;       /**< 0x0004: RTP Trace Enable Register               */
    uint32 GSR;         /**< 0x0008: RTP Global Status Register              */
    uint32 RAM1REG1;    /**< 0x000C: RTP RAM 1 Trace Region 1 Register       */
    uint32 RAM1REG2;    /**< 0x0010: RTP RAM 1 Trace Region 2 Register       */
    uint32 RAM2REG1;    /**< 0x0014: RTP RAM 2 Trace Region 1  Register      */
    uint32 RAM2REG2;    /**< 0x0018: RTP RAM 2 Trace Region 2  Register      */
    uint32 rsvd1[ 2U ]; /**< 0x001C: Reserved
                         */
    uint32 ERREG1;      /**< 0x0024: RTP Peripheral Trace Region 1 Register  */
    uint32 ERREG2;      /**< 0x0028: RTP Peripheral Trace Region 2 Register  */
    uint32 DDMW;        /**< 0x002C: RTP Direct Data Mode Write Register     */
    uint32 rsvd2;       /**< 0x0030: Reserved                                */
    uint32 PC0;         /**< 0x0034: RTP Pin Control 0 Register              */
    uint32 PC1;         /**< 0x0038: RTP Pin Control 1 Register              */
    uint32 PC2;         /**< 0x003C: RTP Pin Control 2 Register              */
    uint32 PC3;         /**< 0x0040: RTP Pin Control 3 Register              */
    uint32 PC4;         /**< 0x0044: RTP Pin Control 4 Register              */
    uint32 PC5;         /**< 0x0048: RTP Pin Control 5 Register              */
    uint32 PC6;         /**< 0x004C: RTP Pin Control 6 Register              */
    uint32 PC7;         /**< 0x0050: RTP Pin Control 7 Register              */
    uint32 PC8;         /**< 0x0054: RTP Pin Control 8 Register              */
} rtpBASE_t;

/** @def rtpREG
 *   @brief RTP Register Frame Pointer
 *
 *   This pointer is used by the RTP driver to access the RTP module registers.
 */
#define rtpREG  ( ( rtpBASE_t * ) 0xFFFFFA00U )

/** @def rtpPORT
 *   @brief RTP Port Register Pointer
 *
 *   Pointer used by the GIO driver to access I/O PORT of RTP
 *   (use the GIO drivers to access the port pins).
 */
#define rtpPORT ( ( gioPORT_t * ) 0xFFFFFA38U )

/* USER CODE BEGIN (1) */
/* USER CODE END */

#endif
