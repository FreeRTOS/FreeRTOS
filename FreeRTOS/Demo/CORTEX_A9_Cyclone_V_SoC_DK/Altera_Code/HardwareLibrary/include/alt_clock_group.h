/******************************************************************************
 *
 * Copyright 2013 Altera Corporation. All Rights Reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 * this list of conditions and the following disclaimer in the documentation
 * and/or other materials provided with the distribution.
 *
 * 3. The name of the author may not be used to endorse or promote products
 * derived from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDER "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE, ARE DISCLAIMED. IN NO
 * EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT
 * OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING
 * IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY
 * OF SUCH DAMAGE.
 *
 ******************************************************************************/

/*!
 * \file
 *
 * Contains the definition of an opaque data structure that contains raw
 * configuration information for a clock group.
 */

#ifndef __ALT_CLK_GRP_H__
#define __ALT_CLK_GRP_H__

#include "hwlib.h"
#include "socal/alt_clkmgr.h"

#ifdef __cplusplus
extern "C"
{
#endif  /* __cplusplus */

/*!
 * This type definition enumerates the clock groups
 */
typedef enum ALT_CLK_GRP_e
{
    ALT_MAIN_PLL_CLK_GRP,        /*!< Main PLL clock group */

    ALT_PERIPH_PLL_CLK_GRP,      /*!< Peripheral PLL clock group */

    ALT_SDRAM_PLL_CLK_GRP        /*!< SDRAM PLL clock group */

} ALT_CLK_GRP_t;

/*!
 * This type definition defines an opaque data structure for holding the
 * configuration settings for a complete clock group.
 */
typedef struct ALT_CLK_GROUP_RAW_CFG_s
{
    uint32_t      verid;     /*!< SoC FPGA version identifier. This field
                              *   encapsulates the silicon identifier and
                              *   version information associated with this
                              *   clock group configuration. It is used to
                              *   assert that this clock group configuration
                              *   is valid for this device. */

    uint32_t      siliid2;   /*!< Reserved register - reserved for future
                              *   device IDs or capability flags. */

    ALT_CLK_GRP_t clkgrpsel; /*!< Clock group union discriminator. */

    /*!
     * This union holds the register values for configuration of the set of
     * possible clock groups on the SoC FPGA. The \e clkgrpsel discriminator
     * identifies the valid clock group union data member.
     */
    union ALT_CLK_GROUP_RAW_CFG_u
    {
        /*! Clock group configuration for Main PLL group. */
        union
        {
            ALT_CLKMGR_MAINPLL_t     fld; /*!< Field access. */
            ALT_CLKMGR_MAINPLL_raw_t raw; /*!< Raw access. */
        } mainpllgrp;

        /*! Clock group configuration for Peripheral PLL group. */
        union
        {
            ALT_CLKMGR_PERPLL_t     fld; /*!< Field access. */
            ALT_CLKMGR_PERPLL_raw_t raw; /*!< Raw access. */
        } perpllgrp;

        /*! Clock group configuration for SDRAM PLL group. */
        union
        {
            ALT_CLKMGR_SDRPLL_t     fld; /*!< Field access. */
            ALT_CLKMGR_SDRPLL_raw_t raw; /*!< Raw access. */
        } sdrpllgrp;

    } clkgrp;
} ALT_CLK_GROUP_RAW_CFG_t;

#ifdef __cplusplus
}
#endif  /* __cplusplus */
#endif  /* __ALT_CLK_GRP_H__ */
