/** @file reg_system.h
 *   @brief System Register Layer Header File
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

#ifndef __REG_SYSTEM_H__
#define __REG_SYSTEM_H__

#include "sys_common.h"
#include "reg_gio.h"

/* System Register Frame 1 Definition */

/** @struct systemBase1
 *   @brief System Register Frame 1 Definition
 *
 *   This type is used to access the System 1 Registers.
 */

/** @typedef systemBASE1_t
 *   @brief System Register Frame 1 Type Definition
 *
 *   This type is used to access the System 1 Registers.
 */
typedef volatile struct systemBase1
{
    uint32 SYSPC1;      /* 0x0000 */
    uint32 SYSPC2;      /* 0x0004 */
    uint32 SYSPC3;      /* 0x0008 */
    uint32 SYSPC4;      /* 0x000C */
    uint32 SYSPC5;      /* 0x0010 */
    uint32 SYSPC6;      /* 0x0014 */
    uint32 SYSPC7;      /* 0x0018 */
    uint32 SYSPC8;      /* 0x001C */
    uint32 SYSPC9;      /* 0x0020 */
    uint32 SSWPLL1;     /* 0x0024 */
    uint32 SSWPLL2;     /* 0x0028 */
    uint32 SSWPLL3;     /* 0x002C */
    uint32 CSDIS;       /* 0x0030 */
    uint32 CSDISSET;    /* 0x0034 */
    uint32 CSDISCLR;    /* 0x0038 */
    uint32 CDDIS;       /* 0x003C */
    uint32 CDDISSET;    /* 0x0040 */
    uint32 CDDISCLR;    /* 0x0044 */
    uint32 GHVSRC;      /* 0x0048 */
    uint32 VCLKASRC;    /* 0x004C */
    uint32 RCLKSRC;     /* 0x0050 */
    uint32 CSVSTAT;     /* 0x0054 */
    uint32 MSTGCR;      /* 0x0058 */
    uint32 MINITGCR;    /* 0x005C */
    uint32 MSINENA;     /* 0x0060 */
    uint32 MSTFAIL;     /* 0x0064 */
    uint32 MSTCGSTAT;   /* 0x0068 */
    uint32 MINISTAT;    /* 0x006C */
    uint32 PLLCTL1;     /* 0x0070 */
    uint32 PLLCTL2;     /* 0x0074 */
    uint32 SYSPC10;     /* 0x0078 */
    uint32 DIEIDL;      /* 0x007C */
    uint32 DIEIDH;      /* 0x0080 */
    uint32 VRCTL;       /* 0x0084 */
    uint32 LPOMONCTL;   /* 0x0088 */
    uint32 CLKTEST;     /* 0x008C */
    uint32 DFTCTRLREG1; /* 0x0090 */
    uint32 DFTCTRLREG2; /* 0x0094 */
    uint32 rsvd1;       /* 0x0098 */
    uint32 rsvd2;       /* 0x009C */
    uint32 GPREG1;      /* 0x00A0 */
    uint32 BTRMSEL;     /* 0x00A4 */
    uint32 IMPFASTS;    /* 0x00A8 */
    uint32 IMPFTADD;    /* 0x00AC */
    uint32 SSISR1;      /* 0x00B0 */
    uint32 SSISR2;      /* 0x00B4 */
    uint32 SSISR3;      /* 0x00B8 */
    uint32 SSISR4;      /* 0x00BC */
    uint32 RAMGCR;      /* 0x00C0 */
    uint32 BMMCR1;      /* 0x00C4 */
    uint32 BMMCR2;      /* 0x00C8 */
    uint32 CPURSTCR;    /* 0x00CC */
    uint32 CLKCNTL;     /* 0x00D0 */
    uint32 ECPCNTL;     /* 0x00D4 */
    uint32 DSPGCR;      /* 0x00D8 */
    uint32 DEVCR1;      /* 0x00DC */
    uint32 SYSECR;      /* 0x00E0 */
    uint32 SYSESR;      /* 0x00E4 */
    uint32 SYSTASR;     /* 0x00E8 */
    uint32 GBLSTAT;     /* 0x00EC */
    uint32 DEV;         /* 0x00F0 */
    uint32 SSIVEC;      /* 0x00F4 */
    uint32 SSIF;        /* 0x00F8 */
} systemBASE1_t;

/** @def systemREG1
 *   @brief System Register Frame 1 Pointer
 *
 *   This pointer is used by the system driver to access the system frame 1 registers.
 */
#define systemREG1 ( ( systemBASE1_t * ) 0xFFFFFF00U )

/** @def systemPORT
 *   @brief ECLK GIO Port Register Pointer
 *
 *   Pointer used by the GIO driver to access I/O PORT of System/Eclk
 *   (use the GIO drivers to access the port pins).
 */
#define systemPORT ( ( gioPORT_t * ) 0xFFFFFF04U )

/* USER CODE BEGIN (0) */
/* USER CODE END */

/* System Register Frame 2 Definition */

/** @struct systemBase2
 *   @brief System Register Frame 2 Definition
 *
 *   This type is used to access the System 2 Registers.
 */

/** @typedef systemBASE2_t
 *   @brief System Register Frame 2 Type Definition
 *
 *   This type is used to access the System 2 Registers.
 */
typedef volatile struct systemBase2
{
    uint32 PLLCTL3;      /* 0x0000 */
    uint32 rsvd1;        /* 0x0004 */
    uint32 STCCLKDIV;    /* 0x0008 */
    uint32 rsvd2[ 6U ];  /* 0x000C */
    uint32 ECPCNTRL0;    /* 0x0024 */
    uint32 rsvd3[ 5U ];  /* 0x0028 */
    uint32 CLK2CNTL;     /* 0x003C */
    uint32 VCLKACON1;    /* 0x0040 */
    uint32 rsvd4[ 11U ]; /* 0x0044 */
    uint32 CLKSLIP;      /* 0x0070 */
    uint32 rsvd5[ 30U ]; /* 0x0074 */
    uint32 EFC_CTLEN;    /* 0x00EC */
    uint32 DIEIDL_REG0;  /* 0x00F0 */
    uint32 DIEIDH_REG1;  /* 0x00F4 */
    uint32 DIEIDL_REG2;  /* 0x00F8 */
    uint32 DIEIDH_REG3;  /* 0x00FC */
} systemBASE2_t;

/** @def systemREG2
 *   @brief System Register Frame 2 Pointer
 *
 *   This pointer is used by the system driver to access the system frame 2 registers.
 */
#define systemREG2 ( ( systemBASE2_t * ) 0xFFFFE100U )

#endif /* ifndef __REG_SYSTEM_H__ */
