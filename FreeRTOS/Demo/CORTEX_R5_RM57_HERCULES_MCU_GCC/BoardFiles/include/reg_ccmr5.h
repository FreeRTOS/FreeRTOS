/** @file reg_ccmr5.h
 *   @brief CCMR5 Register Layer Header File
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

#ifndef __REG_CCMR5_H__
#define __REG_CCMR5_H__

#include "sys_common.h"

/* USER CODE BEGIN (0) */
/* USER CODE END */

/* Efc Register Frame Definition */
/** @struct ccmr5Base
 *   @brief Efc Register Frame Definition
 *
 *   This type is used to access the Efc Registers.
 */
/** @typedef ccmr5BASE_t
 *   @brief Efc Register Frame Type Definition
 *
 *   This type is used to access the Efc Registers.
 */
typedef volatile struct ccmr5Base
{
    uint32 CCMSR1;      /* 0x00 Status Register 1              */
    uint32 CCMKEYR1;    /* 0x04 Key Register 1                 */
    uint32 CCMSR2;      /* 0x08 Status Register 2              */
    uint32 CCMKEYR2;    /* 0x0C Key Register 2                 */
    uint32 CCMSR3;      /* 0x10 Status Register 3              */
    uint32 CCMKEYR3;    /* 0x14 Key Register 3                 */
    uint32 CCMPOLCNTRL; /* 0x18 Polarity Control Register      */
    uint32 CCMSR4;      /* 0x1C Status Register 4              */
    uint32 CCMKEYR4;    /* 0x20 Key Register 4                 */
    uint32 CCMPDSTAT0;  /* 0x24 Power Domain Status Register 0 */
} ccmr5BASE_t;

#define ccmr5REG ( ( ccmr5BASE_t * ) 0xFFFFF600U )
/* USER CODE BEGIN (1) */
/* USER CODE END */

#endif
