/** @file reg_flash.h
 *   @brief Flash Register Layer Header File
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

#ifndef __REG_FLASH_H__
#define __REG_FLASH_H__

/* USER CODE BEGIN (0) */
/* USER CODE END */

#include "sys_common.h"

/* USER CODE BEGIN (1) */
/* USER CODE END */

/* Flash Register Frame Definition */

/** @struct flashWBase
 *   @brief Flash Wrapper Register Frame Definition
 *
 *   This type is used to access the Flash Wrapper Registers.
 */

/** @typedef flashWBASE_t
 *   @brief Flash Wrapper Register Frame Type Definition
 *
 *   This type is used to access the Flash Wrapper Registers.
 */
typedef volatile struct flashWBase
{
    uint32 FRDCNTL;      /* 0x0000 */
    uint32 rsvd1;        /* 0x0004 */
    uint32 FEDACCTRL1;   /* 0x0008 */
    uint32 FEDACCTRL2;   /* 0x000C */
    uint32 FCORERRCNT;   /* 0x0010 */
    uint32 FCORERRADD;   /* 0x0014 */
    uint32 FCORERRPOS;   /* 0x0018 */
    uint32 FEDACSTATUS;  /* 0x001C */
    uint32 FUNCERRADD;   /* 0x0020 */
    uint32 FEDACSDIS;    /* 0x0024 */
    uint32 FPRIMADDTAG;  /* 0x0028 */
    uint32 FREDUADDTAG;  /* 0x002C */
    uint32 FBPROT;       /* 0x0030 */
    uint32 FBSE;         /* 0x0034 */
    uint32 FBBUSY;       /* 0x0038 */
    uint32 FBAC;         /* 0x003C */
    uint32 FBFALLBACK;   /* 0x0040 */
    uint32 FBPRDY;       /* 0x0044 */
    uint32 FPAC1;        /* 0x0048 */
    uint32 FPAC2;        /* 0x004C */
    uint32 FMAC;         /* 0x0050 */
    uint32 FMSTAT;       /* 0x0054 */
    uint32 FEMUDMSW;     /* 0x0058 */
    uint32 FEMUDLSW;     /* 0x005C */
    uint32 FEMUECC;      /* 0x0060 */
    uint32 FLOCK;        /* 0x0064 */
    uint32 FEMUADDR;     /* 0x0068 */
    uint32 FDIAGCTRL;    /* 0x006C */
    uint32 FRAWDATAH;    /* 0x0070 */
    uint32 FRAWDATAL;    /* 0x0074 */
    uint32 FRAWECC;      /* 0x0078 */
    uint32 FPAROVR;      /* 0x007C */
    uint32 rsvd2[ 16U ]; /* 0x009C */
    uint32 FEDACSDIS2;   /* 0x00C0 */
    uint32 rsvd3[ 15U ]; /* 0x00C4 */
    uint32 rsvd4[ 13U ]; /* 0x0100 */
    uint32 rsvd5[ 85U ]; /* 0x0134 */
    uint32 FSMWRENA;     /* 0x0288 */
    uint32 rsvd6[ 6U ];  /* 0x028C */
    uint32 FSMSECTOR;    /* 0x02A4 */
    uint32 rsvd7[ 4U ];  /* 0x02A8 */
    uint32 EEPROMCONFIG; /* 0x02B8 */
    uint32 rsvd8[ 19U ]; /* 0x02BC */
    uint32 EECTRL1;      /* 0x0308 */
    uint32 EECTRL2;      /* 0x030C */
    uint32 EECORRERRCNT; /* 0x0310 */
    uint32 EECORRERRADD; /* 0x0314 */
    uint32 EECORRERRPOS; /* 0x0318 */
    uint32 EESTATUS;     /* 0x031C */
    uint32 EEUNCERRADD;  /* 0x0320 */
} flashWBASE_t;

/** @def flashWREG
 *   @brief Flash Wrapper Register Frame Pointer
 *
 *   This pointer is used by the system driver to access the flash wrapper registers.
 */
#define flashWREG ( ( flashWBASE_t * ) ( 0xFFF87000U ) )

/* USER CODE BEGIN (2) */
/* USER CODE END */

#endif /* ifndef __REG_FLASH_H__ */
