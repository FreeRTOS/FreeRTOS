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
    uint32 INSTRUCTION;      /* 0x0  INSTRUCTION AN DUMPWORD REGISTER    */
    uint32 ADDRESS;          /* 0x4  ADDRESS REGISTER                    */
    uint32 DATA_UPPER;       /* 0x8  DATA UPPER REGISTER                 */
    uint32 DATA_LOWER;       /* 0xc  DATA LOWER REGISTER                 */
    uint32 SYSTEM_CONFIG;    /* 0x10 SYSTEM CONFIG REGISTER              */
    uint32 SYSTEM_STATUS;    /* 0x14 SYSTEM STATUS REGISTER              */
    uint32 ACCUMULATOR;      /* 0x18 ACCUMULATOR REGISTER                */
    uint32 BOUNDARY;         /* 0x1C BOUNDARY REGISTER                   */
    uint32 KEY_FLAG;         /* 0x20 KEY FLAG REGISTER                   */
    uint32 KEY;              /* 0x24 KEY REGISTER                        */
    uint32 rsvd1;            /* 0x28 RESERVED                            */
    uint32 PINS;             /* 0x2C PINS REGISTER                       */
    uint32 CRA;              /* 0x30 CRA                                 */
    uint32 READ;             /* 0x34 READ REGISTER                       */
    uint32 PROGRAMME;        /* 0x38 PROGRAMME REGISTER                  */
    uint32 ERROR;            /* 0x3C ERROR STATUS REGISTER               */
    uint32 SINGLE_BIT;       /* 0x40 SINGLE BIT ERROR                    */
    uint32 TWO_BIT_ERROR;    /* 0x44 DOUBLE BIT ERROR                    */
    uint32 SELF_TEST_CYCLES; /* 0x48 SELF TEST CYCLEX                    */
    uint32 SELF_TEST_SIGN;   /* 0x4C SELF TEST SIGNATURE                 */
} efcBASE_t;

#define efcREG ( ( efcBASE_t * ) 0xFFF8C000U )
/* USER CODE BEGIN (1) */
/* USER CODE END */

#endif /* ifndef __REG_EFC_H__ */
