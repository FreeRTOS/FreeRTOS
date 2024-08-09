/** @file reg_nmpu.h
 *   @brief NMPU Register Layer Header File
 *   @date 11-Dec-2018
 *   @version 04.07.01
 *
 *   This file contains:
 *   - Definitions
 *   - Types
 *   - Interface Prototypes
 *   .
 *   which are relevant for the NMPU driver.
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

#ifndef __REG_NMPU_H__
#define __REG_NMPU_H__

#include "sys_common.h"

#ifdef __cplusplus
extern "C" {
#endif

/* USER CODE BEGIN (0) */
/* USER CODE END */

/* NMPU Register Frame Definition */
/** @struct nmpuBASE_t
 *   @brief nmpuBASE Register Definition
 *
 *   This structure is used to access the NMPU module registers.
 */
typedef volatile struct nmpuBase
{
    uint32 MPUREV;      /**< 0x0000 MPU Revision ID Register                */
    uint32 MPULOCK;     /**< 0x0004 MPU Lock Register                       */
    uint32 MPUDIAGCTRL; /**< 0x0008 MPU Diagnostics Control Register        */
    uint32 MPUDIAGADDR; /**< 0x000C MPU Diagnostic Address Register         */
    uint32 MPUERRSTAT;  /**< 0x0010 MPU Error Status Register               */
    uint32 MPUERRADDR;  /**< 0x0014 MPU Error Address Register              */
    uint32 MPUIAM;      /**< 0x0018 MPU Input Address Mask Register         */
    uint32 rsvd1;       /**< 0x001C Reserved                                */
    uint32 MPUCTRL1;    /**< 0x0020 MPU Control Register 1                  */
    uint32 MPUCTRL2;    /**< 0x0024 MPU Control Register 2                  */
    uint32 rsvd2;       /**< 0x0028 Reserved                                */
    uint32 MPUTYPE;     /**< 0x002C MPU Type Register                       */
    uint32 MPUREGBASE;  /**< 0x0030 MPU Region Base Address Register        */
    uint32 MPUREGSENA;  /**< 0x0034 MPU Region Size and Enable Register     */
    uint32 MPUREGACR;   /**< 0x0038 MPU Region Access Control Register      */
    uint32 MPUREGNUM;   /**< 0x003C MPU Region Number Register              */
} nmpuBASE_t;

#define nmpu_emacREG     ( ( nmpuBASE_t * ) 0xFCFF1800U )
#define nmpu_dmaREG      ( ( nmpuBASE_t * ) 0xFFFF1A00U )
#define nmpu_ps_scr_sREG ( ( nmpuBASE_t * ) 0xFFFF1800U )

/* USER CODE BEGIN (1) */
/* USER CODE END */

/**@}*/
#ifdef __cplusplus
}
#endif

#endif
