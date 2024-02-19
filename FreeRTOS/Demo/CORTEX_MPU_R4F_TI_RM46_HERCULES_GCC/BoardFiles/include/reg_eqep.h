/** @file reg_eqep.h
 *   @brief EQEP Register Layer Header File
 *   @date 11-Dec-2018
 *   @version 04.07.01
 *
 *   This file contains:
 *   - Definitions
 *   - Types
 *   - Interface Prototypes
 *   .
 *   which are relevant for the EQEP driver.
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

#ifndef __REG_EQEP_H__
#define __REG_EQEP_H__

#include "sys_common.h"

/* USER CODE BEGIN (0) */
/* USER CODE END */

/* Eqep Register Frame Definition */

/** @struct eqepBASE
 *   @brief EQEP Register Frame Definition
 *
 *   This type is used to access the EQEP Registers.
 */

/** @typedef eqepBASE_t
 *   @brief EQEP Register Frame Type Definition
 *
 *   This type is used to access the EQEP Registers.
 */
#if( ( __little_endian__ == 1 ) || ( __LITTLE_ENDIAN__ == 1 ) )

typedef volatile struct eqepBASE
{
    uint32 QPOSCNT;  /*< 0x0000 eQEP Position Counter*/
    uint32 QPOSINIT; /*< 0x0004 eQEP Initialization Position Count*/
    uint32 QPOSMAX;  /*< 0x0008 eQEP Maximum Position Count*/
    uint32 QPOSCMP;  /*< 0x000C eQEP Position Compare*/
    uint32 QPOSILAT; /*< 0x0010 eQEP Index Position Latch*/
    uint32 QPOSSLAT; /*< 0x0014 eQEP Strobe Position Latch*/
    uint32 QPOSLAT;  /*< 0x0018 eQEP Position Latch*/
    uint32 QUTMR;    /*< 0x001C eQEP Unit Timer*/
    uint32 QUPRD;    /*< 0x0020 eQEP Unit Period*/
    uint16 QWDTMR;   /*< 0x0024 eQEP Watchdog Timer*/
    uint16 QWDPRD;   /*< 0x0026 eQEP Watchdog Period*/
    uint16 QDECCTL;  /*< 0x0028 eQEP Decoder Control*/
    uint16 QEPCTL;   /*< 0x002A eQEP Control*/
    uint16 QCAPCTL;  /*< 0x002C eQEP Capture Control*/
    uint16 QPOSCTL;  /*< 0x002E eQEP Position Compare Control*/
    uint16 QEINT;    /*< 0x0030 eQEP Interrupt Enable Register*/
    uint16 QFLG;     /*< 0x0032 eQEP Interrupt Flag Register*/
    uint16 QCLR;     /*< 0x0034 eQEP Interrupt Clear Register*/
    uint16 QFRC;     /*< 0x0036 eQEP Interrupt Force Register*/
    uint16 QEPSTS;   /*< 0x0038 eQEP Status Register*/
    uint16 QCTMR;    /*< 0x003A eQEP Capture Timer*/
    uint16 QCPRD;    /*< 0x003C eQEP Capture Period*/
    uint16 QCTMRLAT; /*< 0x003E eQEP Capture Timer Latch*/
    uint16 QCPRDLAT; /*< 0x0040 eQEP Capture Period Latch*/
    uint16 rsvd_1;   /*< 0x0042 Reserved*/
} eqepBASE_t;

#else /* if ( ( __little_endian__ == 1 ) || ( __LITTLE_ENDIAN__ == 1 ) ) */

typedef volatile struct eqepBASE
{
    uint32 QPOSCNT;  /*< 0x0000 eQEP Position Counter*/
    uint32 QPOSINIT; /*< 0x0004 eQEP Initialization Position Count*/
    uint32 QPOSMAX;  /*< 0x0008 eQEP Maximum Position Count*/
    uint32 QPOSCMP;  /*< 0x000C eQEP Position Compare*/
    uint32 QPOSILAT; /*< 0x0010 eQEP Index Position Latch*/
    uint32 QPOSSLAT; /*< 0x0014 eQEP Strobe Position Latch*/
    uint32 QPOSLAT;  /*< 0x0018 eQEP Position Latch*/
    uint32 QUTMR;    /*< 0x001C eQEP Unit Timer*/
    uint32 QUPRD;    /*< 0x0020 eQEP Unit Period*/
    uint16 QWDPRD;   /*< 0x0026 eQEP Watchdog Period*/
    uint16 QWDTMR;   /*< 0x0024 eQEP Watchdog Timer*/
    uint16 QEPCTL;   /*< 0x002A eQEP Control*/
    uint16 QDECCTL;  /*< 0x0028 eQEP Decoder Control*/
    uint16 QPOSCTL;  /*< 0x002E eQEP Position Compare Control*/
    uint16 QCAPCTL;  /*< 0x002C eQEP Capture Control*/
    uint16 QFLG;     /*< 0x0032 eQEP Interrupt Flag Register*/
    uint16 QEINT;    /*< 0x0030 eQEP Interrupt Enable Register*/
    uint16 QFRC;     /*< 0x0036 eQEP Interrupt Force Register*/
    uint16 QCLR;     /*< 0x0034 eQEP Interrupt Clear Register*/
    uint16 QCTMR;    /*< 0x003A eQEP Capture Timer*/
    uint16 QEPSTS;   /*< 0x0038 eQEP Status Register*/
    uint16 QCTMRLAT; /*< 0x003E eQEP Capture Timer Latch*/
    uint16 QCPRD;    /*< 0x003C eQEP Capture Period*/
    uint16 rsvd_1;   /*< 0x0042 Reserved*/
    uint16 QCPRDLAT; /*< 0x0040 eQEP Capture Period Latch*/
} eqepBASE_t;

#endif /* if ( ( __little_endian__ == 1 ) || ( __LITTLE_ENDIAN__ == 1 ) ) */

/** @def eqepREG1
 *   @brief eQEP1 Register Frame Pointer
 *
 *   This pointer is used by the eQEP driver to access the eQEP1 registers.
 */
#define eqepREG1 ( ( eqepBASE_t * ) 0xFCF79900U )

/** @def eqepREG2
 *   @brief eQEP2 Register Frame Pointer
 *
 *   This pointer is used by the eQEP driver to access the eQEP2 registers.
 */
#define eqepREG2 ( ( eqepBASE_t * ) 0xFCF79A00U )

/* USER CODE BEGIN (1) */
/* USER CODE END */

#endif /* ifndef __REG_EQEP_H__ */
