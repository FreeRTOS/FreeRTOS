/** @file reg_pinmux.h
 *   @brief PINMUX Register Layer Header File
 *   @date 11-Dec-2018
 *   @version 04.07.01
 *
 *   This file contains:
 *   - Definitions
 *   - Types
 *   - Interface Prototypes
 *   .
 *   which are relevant for the PINMUX driver.
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

#ifndef __REG_PINMUX_H__
#define __REG_PINMUX_H__

#include "sys_common.h"

/* USER CODE BEGIN (0) */
/* USER CODE END */

/* IOMM Revision and Boot Register */
#define REVISION_REG ( *( volatile uint32 * ) 0xFFFFEA00U )
#define ENDIAN_REG   ( *( volatile uint32 * ) 0xFFFFEA20U )

/* IOMM Error and Fault Registers */

/** @struct iommErrFault
 *   @brief IOMM Error and Fault Register Definition
 *
 *   This structure is used to access the IOMM Error and Fault registers.
 */
typedef volatile struct iommErrFault
{
    uint32 ERR_RAW_STATUS_REG;     /* Error Raw Status / Set Register */
    uint32 ERR_ENABLED_STATUS_REG; /* Error Enabled Status / Clear Register */
    uint32 ERR_ENABLE_REG;         /* Error Signaling Enable Register */
    uint32 ERR_ENABLE_CLR_REG;     /* Error Signaling Enable Clear Register */
    uint32 rsvd;                   /* Reserved */
    uint32 FAULT_ADDRESS_REG;      /* Fault Address Register */
    uint32 FAULT_STATUS_REG;       /* Fault Status Register */
    uint32 FAULT_CLEAR_REG;        /* Fault Clear Register */
} iommErrFault_t;
/* Pinmux Register Frame Definition */

/** @struct pinMuxKicker
 *   @brief Pin Muxing Kicker Register Definition
 *
 *   This structure is used to access the Pin Muxing Kicker registers.
 */
typedef volatile struct pinMuxKicker
{
    uint32 KICKER0; /* kicker 0 register */
    uint32 KICKER1; /* kicker 1 register */
} pinMuxKICKER_t;

/** @struct pinMuxBase
 *   @brief PINMUX Register Definition
 *
 *   This structure is used to access the PINMUX module registers.
 */

/** @typedef pinMuxBASE_t
 *   @brief PINMUX Register Frame Type Definition
 *
 *   This type is used to access the PINMUX Registers.
 */
typedef volatile struct pinMuxBase
{
    uint32 PINMMR0;  /**< 0xEB10 Pin Mux 0 register*/
    uint32 PINMMR1;  /**< 0xEB14 Pin Mux 1 register*/
    uint32 PINMMR2;  /**< 0xEB18 Pin Mux 2 register*/
    uint32 PINMMR3;  /**< 0xEB1C Pin Mux 3 register*/
    uint32 PINMMR4;  /**< 0xEB20 Pin Mux 4 register*/
    uint32 PINMMR5;  /**< 0xEB24 Pin Mux 5 register*/
    uint32 PINMMR6;  /**< 0xEB28 Pin Mux 6 register*/
    uint32 PINMMR7;  /**< 0xEB2C Pin Mux 7 register*/
    uint32 PINMMR8;  /**< 0xEB30 Pin Mux 8 register*/
    uint32 PINMMR9;  /**< 0xEB34 Pin Mux 9 register*/
    uint32 PINMMR10; /**< 0xEB38 Pin Mux 10 register*/
    uint32 PINMMR11; /**< 0xEB3C Pin Mux 11 register*/
    uint32 PINMMR12; /**< 0xEB40 Pin Mux 12 register*/
    uint32 PINMMR13; /**< 0xEB44 Pin Mux 13 register*/
    uint32 PINMMR14; /**< 0xEB48 Pin Mux 14 register*/
    uint32 PINMMR15; /**< 0xEB4C Pin Mux 15 register*/
    uint32 PINMMR16; /**< 0xEB50 Pin Mux 16 register*/
    uint32 PINMMR17; /**< 0xEB54 Pin Mux 17 register*/
    uint32 PINMMR18; /**< 0xEB58 Pin Mux 18 register*/
    uint32 PINMMR19; /**< 0xEB5C Pin Mux 19 register*/
    uint32 PINMMR20; /**< 0xEB60 Pin Mux 20 register*/
    uint32 PINMMR21; /**< 0xEB64 Pin Mux 21 register*/
    uint32 PINMMR22; /**< 0xEB68 Pin Mux 22 register*/
    uint32 PINMMR23; /**< 0xEB6C Pin Mux 23 register*/
    uint32 PINMMR24; /**< 0xEB70 Pin Mux 24 register*/
    uint32 PINMMR25; /**< 0xEB74 Pin Mux 25 register*/
    uint32 PINMMR26; /**< 0xEB78 Pin Mux 26 register*/
    uint32 PINMMR27; /**< 0xEB7C Pin Mux 27 register*/
    uint32 PINMMR28; /**< 0xEB80 Pin Mux 28 register*/
    uint32 PINMMR29; /**< 0xEB84 Pin Mux 29 register*/
    uint32 PINMMR30; /**< 0xEB88 Pin Mux 30 register*/
    uint32 PINMMR31; /**< 0xEB8C Pin Mux 31 register*/
    uint32 PINMMR32; /**< 0xEB90 Pin Mux 32 register*/
    uint32 PINMMR33; /**< 0xEB94 Pin Mux 33 register*/
    uint32 PINMMR34; /**< 0xEB98 Pin Mux 34 register*/
    uint32 PINMMR35; /**< 0xEB9C Pin Mux 35 register*/
    uint32 PINMMR36; /**< 0xEBA0 Pin Mux 36 register*/
    uint32 PINMMR37; /**< 0xEBA4 Pin Mux 37 register*/
    uint32 PINMMR38; /**< 0xEBA8 Pin Mux 38 register*/
    uint32 PINMMR39; /**< 0xEBAC Pin Mux 39 register*/
    uint32 PINMMR40; /**< 0xEBB0 Pin Mux 40 register*/
    uint32 PINMMR41; /**< 0xEBB4 Pin Mux 41 register*/
    uint32 PINMMR42; /**< 0xEBB8 Pin Mux 42 register*/
    uint32 PINMMR43; /**< 0xEBBC Pin Mux 43 register*/
    uint32 PINMMR44; /**< 0xEBC0 Pin Mux 44 register*/
    uint32 PINMMR45; /**< 0xEBC4 Pin Mux 45 register*/
    uint32 PINMMR46; /**< 0xEBC8 Pin Mux 46 register*/
    uint32 PINMMR47; /**< 0xEBCC Pin Mux 47 register*/
} pinMuxBASE_t;

/** @def iommErrFaultReg
 *       @brief IOMM Error Fault Register Frame Pointer
 *
 *               This pointer is used to control IOMM Error and Fault across the device.
 */
#define iommErrFaultReg ( ( iommErrFault_t * ) 0xFFFFEAE0U )

/** @def kickerReg
 *       @brief Pin Muxing Kicker Register Frame Pointer
 *
 *               This pointer is used to enable and disable muxing accross the device.
 */
#define kickerReg       ( ( pinMuxKICKER_t * ) 0xFFFFEA38U )

/** @def pinMuxReg
 *       @brief Pin Muxing Control Register Frame Pointer
 *
 *               This pointer is used to set the muxing registers accross the device.
 */
#define pinMuxReg       ( ( pinMuxBASE_t * ) 0xFFFFEB10U )

/* USER CODE BEGIN (1) */
/* USER CODE END */

#endif /* ifndef __REG_PINMUX_H__ */
