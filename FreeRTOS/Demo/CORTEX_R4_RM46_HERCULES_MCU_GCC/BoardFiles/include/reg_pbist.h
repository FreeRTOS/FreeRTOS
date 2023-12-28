/** @file reg_pbist.h
 *   @brief PBIST Register Layer Header File
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

#ifndef __REG_PBIST_H__
#define __REG_PBIST_H__

#include "sys_common.h"

/* USER CODE BEGIN (0) */
/* USER CODE END */

/* PBIST Register Frame Definition */

/** @struct pbistBase
 *   @brief PBIST Base Register Definition
 *
 *   This structure is used to access the PBIST module registers.
 */

/** @typedef pbistBASE_t
 *   @brief PBIST Register Frame Type Definition
 *
 *   This type is used to access the PBIST Registers.
 */
typedef volatile struct pbistBase
{
    uint32 RAMT;        /* 0x0160: RAM Configuration Register */
    uint32 DLR;         /* 0x0164: Datalogger Register */
    uint32 rsvd1[ 6U ]; /* 0x0168 */
    uint32 PACT;        /* 0x0180: PBIST Activate Register */
    uint32 PBISTID;     /* 0x0184: PBIST ID Register */
    uint32 OVER;        /* 0x0188: Override Register */
    uint32 rsvd2;       /* 0x018C */
    uint32 FSRF0;       /* 0x0190: Fail Status Fail Register 0 */
    uint32 rsvd5;       /* 0x0194 */
    uint32 FSRC0;       /* 0x0198: Fail Status Count Register 0 */
    uint32 FSRC1;       /* 0x019C: Fail Status Count Register 1 */
    uint32 FSRA0;       /* 0x01A0: Fail Status Address 0 Register */
    uint32 FSRA1;       /* 0x01A4: Fail Status Address 1 Register */
    uint32 FSRDL0;      /* 0x01A8: Fail Status Data Register 0 */
    uint32 rsvd3;       /* 0x01AC */
    uint32 FSRDL1;      /* 0x01B0: Fail Status Data Register 1 */
    uint32 rsvd4[ 3U ]; /* 0x01B4 */
    uint32 ROM;         /* 0x01C0: ROM Mask Register */
    uint32 ALGO;        /* 0x01C4: Algorithm Mask Register */
    uint32 RINFOL;      /* 0x01C8: RAM Info Mask Lower Register */
    uint32 RINFOU;      /* 0x01CC: RAM Info Mask Upper Register */
} pbistBASE_t;

#define pbistREG ( ( pbistBASE_t * ) 0xFFFFE560U )

/* USER CODE BEGIN (1) */
/* USER CODE END */

#endif /* ifndef __REG_PBIST_H__ */
