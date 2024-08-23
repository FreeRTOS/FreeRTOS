/** @file reg_esm.h
 *   @brief ESM Register Layer Header File
 *   @date 11-Dec-2018
 *   @version 04.07.01
 *
 *   This file contains:
 *   - Definitions
 *   - Types
 *   - Interface Prototypes
 *   .
 *   which are relevant for the ESM driver.
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

#ifndef __REG_ESM_H__
#define __REG_ESM_H__

#include "sys_common.h"

/* USER CODE BEGIN (0) */
/* USER CODE END */

/* Esm Register Frame Definition */
/** @struct esmBase
 *   @brief Esm Register Frame Definition
 *
 *   This type is used to access the Esm Registers.
 */
/** @typedef esmBASE_t
 *   @brief Esm Register Frame Type Definition
 *
 *   This type is used to access the Esm Registers.
 */
typedef volatile struct esmBase
{
    uint32 EEPAPR1;     /* 0x0000                 */
    uint32 DEPAPR1;     /* 0x0004                 */
    uint32 IESR1;       /* 0x0008                 */
    uint32 IECR1;       /* 0x000C                 */
    uint32 ILSR1;       /* 0x0010                 */
    uint32 ILCR1;       /* 0x0014                 */
    uint32 SR1[ 3U ];   /* 0x0018, 0x001C, 0x0020 */
    uint32 EPSR;        /* 0x0024                 */
    uint32 IOFFHR;      /* 0x0028                 */
    uint32 IOFFLR;      /* 0x002C                 */
    uint32 LTCR;        /* 0x0030                 */
    uint32 LTCPR;       /* 0x0034                 */
    uint32 EKR;         /* 0x0038                 */
    uint32 SSR2;        /* 0x003C                 */
    uint32 IEPSR4;      /* 0x0040                 */
    uint32 IEPCR4;      /* 0x0044                 */
    uint32 IESR4;       /* 0x0048                 */
    uint32 IECR4;       /* 0x004C                 */
    uint32 ILSR4;       /* 0x0050                 */
    uint32 ILCR4;       /* 0x0054                 */
    uint32 SR4[ 3U ];   /* 0x0058, 0x005C, 0x0060 */
    uint32 rsvd1[ 7U ]; /* 0x0064 - 0x007C        */
    uint32 IEPSR7;      /* 0x0080                 */
    uint32 IEPCR7;      /* 0x0084                 */
    uint32 IESR7;       /* 0x0088                 */
    uint32 IECR7;       /* 0x008C                 */
    uint32 ILSR7;       /* 0x0090                 */
    uint32 ILCR7;       /* 0x0094                 */
    uint32 SR7[ 3U ];   /* 0x0098, 0x009C, 0x00A0 */
} esmBASE_t;

/** @def esmREG
 *   @brief Esm Register Frame Pointer
 *
 *   This pointer is used by the Esm driver to access the Esm registers.
 */
#define esmREG ( ( esmBASE_t * ) 0xFFFFF500U )

/* USER CODE BEGIN (1) */
/* USER CODE END */

#endif
