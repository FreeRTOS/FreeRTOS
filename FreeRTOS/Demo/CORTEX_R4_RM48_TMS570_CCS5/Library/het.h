/*
 * FreeRTOS Kernel V10.1.0
 * Copyright (C) 2017 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * http://www.FreeRTOS.org
 * http://aws.amazon.com/freertos
 *
 * 1 tab == 4 spaces!
 */

#ifndef __HET_H__
#define __HET_H__

#include "gio.h"

/** @struct hetBase
*   @brief HET Register Definition
*
*   This structure is used to access the HET module egisters.
*/
/** @typedef hetBASE_t
*   @brief HET Register Frame Type Definition
*
*   This type is used to access the HET Registers.
*/
typedef volatile struct hetBase
{
    unsigned GCR;     /**< 0x0000: Global control register              */
    unsigned PFR;     /**< 0x0004: Prescale factor register             */
    unsigned ADDR;    /**< 0x0008: Current address register             */
    unsigned OFF1;    /**< 0x000C: Interrupt offset register 1          */
    unsigned OFF2;    /**< 0x0010: Interrupt offset register 2          */
    unsigned INTENAS; /**< 0x0014: Interrupt enable set register        */
    unsigned INTENAC; /**< 0x0018: Interrupt enable clear register      */
    unsigned EXC1;    /**< 0x001C: Exeption control register 1          */
    unsigned EXC2;    /**< 0x0020: Exeption control register 2          */
    unsigned PRY;     /**< 0x0024: Interrupt priority register          */
    unsigned FLG;     /**< 0x0028: Interrupt flag register              */
    unsigned : 32U;   /**< 0x002C: Reserved                             */
    unsigned : 32U;   /**< 0x0030: Reserved                             */
    unsigned HRSH;    /**< 0x0034: High resoltion share register        */
    unsigned XOR;     /**< 0x0038: XOR share register                   */
    unsigned REQENS;  /**< 0x003C: Request enable set register          */
    unsigned REQENC;  /**< 0x0040: Request enable clear register        */
    unsigned REQDS;   /**< 0x0044: Request destination select register  */
    unsigned : 32U;   /**< 0x0048: Reserved                             */
    unsigned DIR;     /**< 0x004C: Direction register                   */
    unsigned DIN;     /**< 0x0050: Data input register                  */
    unsigned DOUT;    /**< 0x0054: Data output register                 */
    unsigned DSET;    /**< 0x0058: Data output set register             */
    unsigned DCLR;    /**< 0x005C: Data output clear register           */
    unsigned PDR;     /**< 0x0060: Open drain register                  */
    unsigned PULDIS;  /**< 0x0064: Pull disable register                */
    unsigned PSL;     /**< 0x0068: Pull select register                 */
    unsigned : 32U;   /**< 0x006C: Reserved                             */
    unsigned : 32U;   /**< 0x0070: Reserved                             */
    unsigned PCREG;   /**< 0x0074: Parity control register              */
    unsigned PAR;     /**< 0x0078: Parity address register              */
    unsigned PPR;     /**< 0x007C: Parity pin select register           */
    unsigned SFPRLD;  /**< 0x0080: Suppression filter preload register  */
    unsigned SFENA;   /**< 0x0084: Suppression filter enable register   */
    unsigned : 32U;   /**< 0x0088: Reserved                             */
    unsigned LBPSEL;  /**< 0x008C: Loop back pair select register       */
    unsigned LBPDIR;  /**< 0x0090: Loop back pair direction register    */
} hetBASE_t;


/** @def hetREG
*   @brief HET Register Frame Pointer
*
*   This pointer is used by the HET driver to access the het module registers.
*/
#define hetREG ((hetBASE_t *)0xFFF7B800U)


/** @def hetPORT
*   @brief HET GIO Port Register Pointer
*
*   Pointer used by the GIO driver to access I/O PORT of HET
*   (use the GIO drivers to access the port pins).
*/
#define hetPORT ((gioPORT_t *)0xFFF7B84CU)

#endif
