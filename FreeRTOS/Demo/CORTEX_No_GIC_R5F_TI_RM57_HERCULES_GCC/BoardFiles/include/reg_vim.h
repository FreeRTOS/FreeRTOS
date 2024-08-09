/** @file reg_vim.h
 *   @brief VIM Register Layer Header File
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

#ifndef __REG_VIM_H__
#define __REG_VIM_H__

#include "sys_common.h"

/* USER CODE BEGIN (0) */
/* USER CODE END */

/* Vim Register Frame Definition */
/** @struct vimBase
 *   @brief Vim Register Frame Definition
 *
 *   This type is used to access the Vim Registers.
 */
/** @typedef vimBASE_t
 *   @brief VIM Register Frame Type Definition
 *
 *   This type is used to access the VIM Registers.
 */
typedef volatile struct vimBase
{
    uint32 rsvd1[ 59U ];    /* 0x0000 - 0x00E8 Reserved */
    uint32 ECCSTAT;         /* 0x00EC        */
    uint32 ECCCTL;          /* 0x00F0        */
    uint32 UERRADDR;        /* 0x00F4        */
    uint32 FBVECADDR;       /* 0x00F8        */
    uint32 SBERRADDR;       /* 0x00FC        */
    uint32 IRQINDEX;        /* 0x0100        */
    uint32 FIQINDEX;        /* 0x0104        */
    uint32 rsvd2;           /* 0x0108        */
    uint32 rsvd3;           /* 0x010C        */
    uint32 FIRQPR0;         /* 0x0110        */
    uint32 FIRQPR1;         /* 0x0114        */
    uint32 FIRQPR2;         /* 0x0118        */
    uint32 FIRQPR3;         /* 0x011C        */
    uint32 INTREQ0;         /* 0x0120        */
    uint32 INTREQ1;         /* 0x0124        */
    uint32 INTREQ2;         /* 0x0128        */
    uint32 INTREQ3;         /* 0x012C        */
    uint32 REQMASKSET0;     /* 0x0130        */
    uint32 REQMASKSET1;     /* 0x0134        */
    uint32 REQMASKSET2;     /* 0x0138        */
    uint32 REQMASKSET3;     /* 0x013C        */
    uint32 REQMASKCLR0;     /* 0x0140        */
    uint32 REQMASKCLR1;     /* 0x0144        */
    uint32 REQMASKCLR2;     /* 0x0148        */
    uint32 REQMASKCLR3;     /* 0x014C        */
    uint32 WAKEMASKSET0;    /* 0x0150        */
    uint32 WAKEMASKSET1;    /* 0x0154        */
    uint32 WAKEMASKSET2;    /* 0x0158        */
    uint32 WAKEMASKSET3;    /* 0x015C        */
    uint32 WAKEMASKCLR0;    /* 0x0160        */
    uint32 WAKEMASKCLR1;    /* 0x0164        */
    uint32 WAKEMASKCLR2;    /* 0x0168        */
    uint32 WAKEMASKCLR3;    /* 0x016C        */
    uint32 IRQVECREG;       /* 0x0170        */
    uint32 FIQVECREG;       /* 0x0174        */
    uint32 CAPEVT;          /* 0x0178        */
    uint32 rsvd4;           /* 0x017C        */
    uint32 CHANCTRL[ 32U ]; /* 0x0180-0x02FC */
} vimBASE_t;

#define vimREG ( ( vimBASE_t * ) 0xFFFFFD00U )

/* USER CODE BEGIN (1) */
/* USER CODE END */

#endif
