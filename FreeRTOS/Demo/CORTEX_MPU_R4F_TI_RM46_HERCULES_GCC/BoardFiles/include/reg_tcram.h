/** @file reg_tcram.h
 *   @brief TCRAM Register Layer Header File
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

#ifndef __REG_TCRAM_H__
#define __REG_TCRAM_H__

/* USER CODE BEGIN (0) */
/* USER CODE END */

#include "sys_common.h"

/* USER CODE BEGIN (1) */
/* USER CODE END */

/* Tcram Register Frame Definition */

/** @struct tcramBase
 *   @brief TCRAM Wrapper Register Frame Definition
 *
 *   This type is used to access the TCRAM Wrapper Registers.
 */

/** @typedef tcramBASE_t
 *   @brief TCRAM Wrapper Register Frame Type Definition
 *
 *   This type is used to access the TCRAM Wrapper Registers.
 */

typedef volatile struct tcramBase
{
    uint32 RAMCTRL;        /* 0x0000 */
    uint32 RAMTHRESHOLD;   /* 0x0004 */
    uint32 RAMOCCUR;       /* 0x0008 */
    uint32 RAMINTCTRL;     /* 0x000C */
    uint32 RAMERRSTATUS;   /* 0x0010 */
    uint32 RAMSERRADDR;    /* 0x0014 */
    uint32 rsvd1;          /* 0x0018 */
    uint32 RAMUERRADDR;    /* 0x001C */
    uint32 rsvd2[ 4U ];    /* 0x0020 */
    uint32 RAMTEST;        /* 0x0030 */
    uint32 rsvd3;          /* 0x0034 */
    uint32 RAMADDRDECVECT; /* 0x0038 */
    uint32 RAMPERADDR;     /* 0x003C */
} tcramBASE_t;

#define tcram1REG ( ( tcramBASE_t * ) ( 0xFFFFF800U ) )
#define tcram2REG ( ( tcramBASE_t * ) ( 0xFFFFF900U ) )

/* USER CODE BEGIN (2) */
/* USER CODE END */

#endif /* ifndef __REG_TCRAM_H__ */
