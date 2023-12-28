/** @file reg_l2ramw.h
 *   @brief L2RAMW Register Layer Header File
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

#ifndef __REG_L2RAMW_H__
#define __REG_L2RAMW_H__

/* USER CODE BEGIN (0) */
/* USER CODE END */

#include "sys_common.h"

/* USER CODE BEGIN (1) */
/* USER CODE END */

/* L2ram Register Frame Definition */
/** @struct l2ramwBase
 *   @brief L2RAMW Wrapper Register Frame Definition
 *
 *   This type is used to access the L2RAMW Wrapper Registers.
 */
/** @typedef l2ramwBASE_t
 *   @brief L2RAMW Wrapper Register Frame Type Definition
 *
 *   This type is used to access the L2RAMW Wrapper Registers.
 */

typedef volatile struct l2ramwBase
{
    uint32 RAMCTRL;          /* 0x0000 */
    uint32 rsvd1[ 3 ];       /* 0x0004 */
    uint32 RAMERRSTATUS;     /* 0x0010 */
    uint32 rsvd2[ 4 ];       /* 0x0014 */
    uint32 DIAGDATAVECTOR_H; /* 0x0024 */
    uint32 DIAGDATAVECTOR_L; /* 0x0028 */
    uint32 DIAG_ECC;         /* 0x002C */
    uint32 RAMTEST;          /* 0x0030 */
    uint32 rsvd3;            /* 0x0034 */
    uint32 RAMADDRDECVECT;   /* 0x0038 */
    uint32 MEMINITDOMAIN;    /* 0x003C */
    uint32 rsvd4;            /* 0x0040 */
    uint32 BANKDOMAINMAP0;   /* 0x0044 */
    uint32 BANKDOMAINMAP1;   /* 0x0048 */
} l2ramwBASE_t;

#define l2ramwREG ( ( l2ramwBASE_t * ) ( 0xFFFFF900U ) )

/* USER CODE BEGIN (2) */
/* USER CODE END */

#endif
