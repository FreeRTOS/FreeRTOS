/** @file reg_het.h
 *   @brief HET Register Layer Header File
 *   @date 11-Dec-2018
 *   @version 04.07.01
 *
 *   This file contains:
 *   - Definitions
 *   - Types
 *   - Interface Prototypes
 *   .
 *   which are relevant for the HET driver.
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

#ifndef __REG_HET_H__
#define __REG_HET_H__

#include "sys_common.h"
#include "reg_gio.h"

/* USER CODE BEGIN (0) */
/* USER CODE END */

/* Het Register Frame Definition */
/** @struct hetBase
 *   @brief HET Base Register Definition
 *
 *   This structure is used to access the HET module registers.
 */
/** @typedef hetBASE_t
 *   @brief HET Register Frame Type Definition
 *
 *   This type is used to access the HET Registers.
 */

typedef volatile struct hetBase
{
    uint32 GCR;     /**< 0x0000: Global control register              */
    uint32 PFR;     /**< 0x0004: Prescale factor register             */
    uint32 ADDR;    /**< 0x0008: Current address register             */
    uint32 OFF1;    /**< 0x000C: Interrupt offset register 1          */
    uint32 OFF2;    /**< 0x0010: Interrupt offset register 2          */
    uint32 INTENAS; /**< 0x0014: Interrupt enable set register        */
    uint32 INTENAC; /**< 0x0018: Interrupt enable clear register      */
    uint32 EXC1;    /**< 0x001C: Exception control register 1          */
    uint32 EXC2;    /**< 0x0020: Exception control register 2          */
    uint32 PRY;     /**< 0x0024: Interrupt priority register          */
    uint32 FLG;     /**< 0x0028: Interrupt flag register              */
    uint32 AND;     /**< 0x002C: AND share control register         */
    uint32 rsvd1;   /**< 0x0030: Reserved                             */
    uint32 HRSH;    /**< 0x0034: High resolution share register        */
    uint32 XOR;     /**< 0x0038: XOR share register                   */
    uint32 REQENS;  /**< 0x003C: Request enable set register          */
    uint32 REQENC;  /**< 0x0040: Request enable clear register        */
    uint32 REQDS;   /**< 0x0044: Request destination select register  */
    uint32 rsvd2;   /**< 0x0048: Reserved                             */
    uint32 DIR;     /**< 0x004C: Direction register                   */
    uint32 DIN;     /**< 0x0050: Data input register                  */
    uint32 DOUT;    /**< 0x0054: Data output register                 */
    uint32 DSET;    /**< 0x0058: Data output set register             */
    uint32 DCLR;    /**< 0x005C: Data output clear register           */
    uint32 PDR;     /**< 0x0060: Open drain register                  */
    uint32 PULDIS;  /**< 0x0064: Pull disable register                */
    uint32 PSL;     /**< 0x0068: Pull select register                 */
    uint32 rsvd3;   /**< 0x006C: Reserved                             */
    uint32 rsvd4;   /**< 0x0070: Reserved                             */
    uint32 PCR;     /**< 0x0074: Parity control register              */
    uint32 PAR;     /**< 0x0078: Parity address register              */
    uint32 PPR;     /**< 0x007C: Parity pin select register           */
    uint32 SFPRLD;  /**< 0x0080: Suppression filter preload register  */
    uint32 SFENA;   /**< 0x0084: Suppression filter enable register   */
    uint32 rsvd5;   /**< 0x0088: Reserved                             */
    uint32 LBPSEL;  /**< 0x008C: Loop back pair select register       */
    uint32 LBPDIR;  /**< 0x0090: Loop back pair direction register    */
    uint32 PINDIS;  /**< 0x0094: Pin disable register                 */
} hetBASE_t;

/** @struct hetInstructionBase
 *   @brief HET Instruction Definition
 *
 *   This structure is used to access the HET RAM.
 */
/** @typedef hetINSTRUCTION_t
 *   @brief HET Instruction Type Definition
 *
 *   This type is used to access a HET Instruction.
 */
typedef volatile struct hetInstructionBase
{
    uint32 Program;
    uint32 Control;
    uint32 Data;
    uint32 rsvd1;
} hetINSTRUCTION_t;

/** @struct hetRamBase
 *   @brief HET RAM Definition
 *
 *   This structure is used to access the HET RAM.
 */
/** @typedef hetRAMBASE_t
 *   @brief HET RAM Type Definition
 *
 *   This type is used to access the HET RAM.
 */
typedef volatile struct het1RamBase
{
    hetINSTRUCTION_t Instruction[ 160U ];
} hetRAMBASE_t;

/** @def hetREG1
 *   @brief HET Register Frame Pointer
 *
 *   This pointer is used by the HET driver to access the het module registers.
 */
#define hetREG1        ( ( hetBASE_t * ) 0xFFF7B800U )

/** @def hetPORT1
 *   @brief HET GIO Port Register Pointer
 *
 *   Pointer used by the GIO driver to access I/O PORT of HET1
 *   (use the GIO drivers to access the port pins).
 */
#define hetPORT1       ( ( gioPORT_t * ) 0xFFF7B84CU )

/** @def hetREG2
 *   @brief HET2 Register Frame Pointer
 *
 *   This pointer is used by the HET driver to access the het module registers.
 */
#define hetREG2        ( ( hetBASE_t * ) 0xFFF7B900U )

/** @def hetPORT2
 *   @brief HET2 GIO Port Register Pointer
 *
 *   Pointer used by the GIO driver to access I/O PORT of HET2
 *   (use the GIO drivers to access the port pins).
 */
#define hetPORT2       ( ( gioPORT_t * ) 0xFFF7B94CU )

#define hetRAM1        ( ( hetRAMBASE_t * ) 0xFF460000U )

#define hetRAM2        ( ( hetRAMBASE_t * ) 0xFF440000U )

#define NHET1RAMPARLOC ( *( volatile uint32 * ) 0xFF462000U )
#define NHET1RAMLOC    ( *( volatile uint32 * ) 0xFF460000U )

#define NHET2RAMPARLOC ( *( volatile uint32 * ) 0xFF442000U )
#define NHET2RAMLOC    ( *( volatile uint32 * ) 0xFF440000U )

/* USER CODE BEGIN (1) */
/* USER CODE END */

#endif
