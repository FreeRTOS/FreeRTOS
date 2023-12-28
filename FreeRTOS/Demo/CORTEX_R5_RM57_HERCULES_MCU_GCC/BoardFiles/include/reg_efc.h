/** @file reg_efc.h
 *   @brief EFC Register Layer Header File
 *   @date 11-Dec-2018
 *   @version 04.07.01
 *
 *   This file contains:
 *   - Definitions
 *   - Types
 *   .
 *   which are relevant for the System driver.
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

#ifndef __REG_EFC_H__
#define __REG_EFC_H__

#include "sys_common.h"

/* USER CODE BEGIN (0) */
/* USER CODE END */

/* Efc Register Frame Definition */
/** @struct efcBase
 *   @brief Efc Register Frame Definition
 *
 *   This type is used to access the Efc Registers.
 */
/** @typedef efcBASE_t
 *   @brief Efc Register Frame Type Definition
 *
 *   This type is used to access the Efc Registers.
 */
typedef volatile struct efcBase
{
    uint32 rsvd1;    /* 0x00 RESERVED                             */
    uint32 rsvd2;    /* 0x04 RESERVED                             */
    uint32 rsvd3;    /* 0x08 RESERVED                             */
    uint32 rsvd4;    /* 0x0C RESERVED                             */
    uint32 rsvd5;    /* 0x10 RESERVED                             */
    uint32 rsvd6;    /* 0x14 RESERVED                             */
    uint32 rsvd7;    /* 0x18 RESERVED                             */
    uint32 BOUND;    /* 0x1C RESERVED                             */
    uint32 rsvd8;    /* 0x20 RESERVED                             */
    uint32 rsvd9;    /* 0x24 RESERVED                             */
    uint32 rsvd10;   /* 0x28 RESERVED                             */
    uint32 PINS;     /* 0x2C RESERVED                             */
    uint32 rsvd11;   /* 0x30 RESERVED                             */
    uint32 rsvd12;   /* 0x34 RESERVED                             */
    uint32 rsvd13;   /* 0x38 RESERVED                             */
    uint32 ERR_STAT; /* 0x3C RESERVED                             */
    uint32 rsvd14;   /* 0x40 RESERVED                             */
    uint32 rsvd15;   /* 0x44 RESERVED                             */
    uint32 ST_CY;    /* 0x48 RESERVED                             */
    uint32 ST_SIG;   /* 0x4C RESERVED                             */
} efcBASE_t;

#define efcREG ( ( efcBASE_t * ) 0xFFF8C000U )
/* USER CODE BEGIN (1) */
/* USER CODE END */

#endif
