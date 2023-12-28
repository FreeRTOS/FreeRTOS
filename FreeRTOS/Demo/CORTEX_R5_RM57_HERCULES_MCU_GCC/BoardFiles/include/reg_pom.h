/** @file reg_pom.h
 *   @brief POM Register Layer Header File
 *   @date 11-Dec-2018
 *   @version 04.07.01
 *
 *   This file contains:
 *   - Definitions
 *   - Types
 *   - Interface Prototypes
 *   .
 *   which are relevant for the POM driver.
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

#ifndef __REG_POM_H__
#define __REG_POM_H__

#include "sys_common.h"

/* USER CODE BEGIN (0) */
/* USER CODE END */

/* Pom Register Frame Definition */
/** @struct POMBase
 *   @brief POM Register Frame Definition
 *
 *   This structure is used to access the POM module registers(POM Register Map).
 */
typedef struct
{
    uint32 POMGLBCTRL; /* 0x00      */
    uint32 POMREV;     /* 0x04      */
    uint32 rsvd1;      /* 0x08      */
    uint32 POMFLG;     /* 0x0C      */
    struct
    {
        uint32 rsdv2;
    } RESERVED_REG[ 124U ];
    struct /* 0x200 ...    */
    {
        uint32 POMPROGSTART;
        uint32 POMOVLSTART;
        uint32 POMREGSIZE;
        uint32 rsdv3;
    } POMRGNCONF_ST[ 32U ];
} pomBASE_t;

/** @struct POM_CORESIGHT_ST
 *   @brief POM_CORESIGHT_ST Register Definition
 *
 *   This structure is used to access the POM module registers(POM CoreSight Registers ).
 */
typedef struct
{
    uint32 POMITCTRL; /* 0xF00            */
    struct            /* 0xF04 to 0xF9C   */
    {
        uint32 Reserved_Reg;
    } Reserved1_ST[ 39U ];
    uint32 POMCLAIMSET;      /* 0xFA0      */
    uint32 POMCLAIMCLR;      /* 0xFA4      */
    uint32 rsvd1[ 2U ];      /* 0xFA8      */
    uint32 POMLOCKACCESS;    /* 0xFB0      */
    uint32 POMLOCKSTATUS;    /* 0xFB4      */
    uint32 POMAUTHSTATUS;    /* 0xFB8      */
    uint32 rsvd2[ 3U ];      /* 0xFBC      */
    uint32 POMDEVID;         /* 0xFC8      */
    uint32 POMDEVTYPE;       /* 0xFCC      */
    uint32 POMPERIPHERALID4; /* 0xFD0      */
    uint32 POMPERIPHERALID5; /* 0xFD4      */
    uint32 POMPERIPHERALID6; /* 0xFD8      */
    uint32 POMPERIPHERALID7; /* 0xFDC      */
    uint32 POMPERIPHERALID0; /* 0xFE0      */
    uint32 POMPERIPHERALID1; /* 0xFE4      */
    uint32 POMPERIPHERALID2; /* 0xFE8      */
    uint32 POMPERIPHERALID3; /* 0xFEC      */
    uint32 POMCOMPONENTID0;  /* 0xFF0      */
    uint32 POMCOMPONENTID1;  /* 0xFF4      */
    uint32 POMCOMPONENTID2;  /* 0xFF8      */
    uint32 POMCOMPONENTID3;  /* 0xFFC      */
} POM_CORESIGHT_ST;

#define pomREG ( ( pomBASE_t * ) 0xFFA04000U )

/* USER CODE BEGIN (1) */
/* USER CODE END */

#endif
