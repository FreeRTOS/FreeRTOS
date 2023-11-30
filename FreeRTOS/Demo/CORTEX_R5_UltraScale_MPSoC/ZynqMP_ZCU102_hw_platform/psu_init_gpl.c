/******************************************************************************
*
* Copyright (C) 2015 Xilinx, Inc.  All rights reserved.
*
*  This program is free software; you can redistribute it and/or modify
*  it under the terms of the GNU General Public License as published by
*  the Free Software Foundation; either version 2 of the License, or
*  (at your option) any later version.
*
*  This program is distributed in the hope that it will be useful,
*  but WITHOUT ANY WARRANTY; without even the implied warranty of
*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
*  GNU General Public License for more details.
*
*  You should have received a copy of the GNU General Public License along
*  with this program; if not, see <http://www.gnu.org/licenses/>
*
*
******************************************************************************/

#include <xil_io.h>
#include <sleep.h>
#include "psu_init_gpl.h"
#define    DPLL_CFG_LOCK_DLY        63
#define    DPLL_CFG_LOCK_CNT        625
#define    DPLL_CFG_LFHF            3
#define    DPLL_CFG_CP              3
#define    DPLL_CFG_RES             2

static int mask_pollOnValue(u32 add, u32 mask, u32 value);

static int mask_poll(u32 add, u32 mask);

static void mask_delay(u32 delay);

static u32 mask_read(u32 add, u32 mask);

static void dpll_prog(int ddr_pll_fbdiv, int d_lock_dly,
	int d_lock_cnt, int d_lfhf, int d_cp, int d_res);

static
void PSU_Mask_Write(unsigned long offset, unsigned long mask,
	unsigned long val)
{
	unsigned long RegVal = 0x0;

	RegVal = Xil_In32(offset);
	RegVal &= ~(mask);
	RegVal |= (val & mask);
	Xil_Out32(offset, RegVal);
}

static
void prog_reg(unsigned long addr, unsigned long mask,
	unsigned long shift,
		unsigned long value)
{
	    int rdata = 0;

	    rdata  = Xil_In32(addr);
	    rdata  = rdata & (~mask);
	    rdata  = rdata | (value << shift);
	    Xil_Out32(addr, rdata);
	    }

unsigned long psu_pll_init_data(void)
{
    /*
    * RPLL INIT
    */
    /*
    * Register : RPLL_CFG @ 0XFF5E0034

    * PLL loop filter resistor control
    *  PSU_CRL_APB_RPLL_CFG_RES                                    0xc

    * PLL charge pump control
    *  PSU_CRL_APB_RPLL_CFG_CP                                     0x3

    * PLL loop filter high frequency capacitor control
    *  PSU_CRL_APB_RPLL_CFG_LFHF                                   0x3

    * Lock circuit counter setting
    *  PSU_CRL_APB_RPLL_CFG_LOCK_CNT                               0x339

    * Lock circuit configuration settings for lock windowsize
    *  PSU_CRL_APB_RPLL_CFG_LOCK_DLY                               0x3f

    * Helper data. Values are to be looked up in a table from Data Sheet
    * (OFFSET, MASK, VALUE)      (0XFF5E0034, 0xFE7FEDEFU ,0x7E672C6CU)
    */
	PSU_Mask_Write(CRL_APB_RPLL_CFG_OFFSET, 0xFE7FEDEFU, 0x7E672C6CU);
/*##################################################################### */

    /*
    * UPDATE FB_DIV
    */
    /*
    * Register : RPLL_CTRL @ 0XFF5E0030

    * Mux select for determining which clock feeds this PLL. 0XX pss_ref_clk i
    * s the source 100 video clk is the source 101 pss_alt_ref_clk is the sour
    * ce 110 aux_refclk[X] is the source 111 gt_crx_ref_clk is the source
    *  PSU_CRL_APB_RPLL_CTRL_PRE_SRC                               0x0

    * The integer portion of the feedback divider to the PLL
    *  PSU_CRL_APB_RPLL_CTRL_FBDIV                                 0x2d

    * This turns on the divide by 2 that is inside of the PLL. This does not c
    * hange the VCO frequency, just the output frequency
    *  PSU_CRL_APB_RPLL_CTRL_DIV2                                  0x1

    * PLL Basic Control
    * (OFFSET, MASK, VALUE)      (0XFF5E0030, 0x00717F00U ,0x00012D00U)
    */
	PSU_Mask_Write(CRL_APB_RPLL_CTRL_OFFSET, 0x00717F00U, 0x00012D00U);
/*##################################################################### */

    /*
    * BY PASS PLL
    */
    /*
    * Register : RPLL_CTRL @ 0XFF5E0030

    * Bypasses the PLL clock. The usable clock will be determined from the POS
    * T_SRC field. (This signal may only be toggled after 4 cycles of the old
    * clock and 4 cycles of the new clock. This is not usually an issue, but d
    * esigners must be aware.)
    *  PSU_CRL_APB_RPLL_CTRL_BYPASS                                1

    * PLL Basic Control
    * (OFFSET, MASK, VALUE)      (0XFF5E0030, 0x00000008U ,0x00000008U)
    */
	PSU_Mask_Write(CRL_APB_RPLL_CTRL_OFFSET, 0x00000008U, 0x00000008U);
/*##################################################################### */

    /*
    * ASSERT RESET
    */
    /*
    * Register : RPLL_CTRL @ 0XFF5E0030

    * Asserts Reset to the PLL. When asserting reset, the PLL must already be
    * in BYPASS.
    *  PSU_CRL_APB_RPLL_CTRL_RESET                                 1

    * PLL Basic Control
    * (OFFSET, MASK, VALUE)      (0XFF5E0030, 0x00000001U ,0x00000001U)
    */
	PSU_Mask_Write(CRL_APB_RPLL_CTRL_OFFSET, 0x00000001U, 0x00000001U);
/*##################################################################### */

    /*
    * DEASSERT RESET
    */
    /*
    * Register : RPLL_CTRL @ 0XFF5E0030

    * Asserts Reset to the PLL. When asserting reset, the PLL must already be
    * in BYPASS.
    *  PSU_CRL_APB_RPLL_CTRL_RESET                                 0

    * PLL Basic Control
    * (OFFSET, MASK, VALUE)      (0XFF5E0030, 0x00000001U ,0x00000000U)
    */
	PSU_Mask_Write(CRL_APB_RPLL_CTRL_OFFSET, 0x00000001U, 0x00000000U);
/*##################################################################### */

    /*
    * CHECK PLL STATUS
    */
    /*
    * Register : PLL_STATUS @ 0XFF5E0040

    * RPLL is locked
    *  PSU_CRL_APB_PLL_STATUS_RPLL_LOCK                            1
    * (OFFSET, MASK, VALUE)      (0XFF5E0040, 0x00000002U ,0x00000002U)
		*/
	mask_poll(CRL_APB_PLL_STATUS_OFFSET, 0x00000002U);

/*##################################################################### */

    /*
    * REMOVE PLL BY PASS
    */
    /*
    * Register : RPLL_CTRL @ 0XFF5E0030

    * Bypasses the PLL clock. The usable clock will be determined from the POS
    * T_SRC field. (This signal may only be toggled after 4 cycles of the old
    * clock and 4 cycles of the new clock. This is not usually an issue, but d
    * esigners must be aware.)
    *  PSU_CRL_APB_RPLL_CTRL_BYPASS                                0

    * PLL Basic Control
    * (OFFSET, MASK, VALUE)      (0XFF5E0030, 0x00000008U ,0x00000000U)
    */
	PSU_Mask_Write(CRL_APB_RPLL_CTRL_OFFSET, 0x00000008U, 0x00000000U);
/*##################################################################### */

    /*
    * Register : RPLL_TO_FPD_CTRL @ 0XFF5E0048

    * Divisor value for this clock.
    *  PSU_CRL_APB_RPLL_TO_FPD_CTRL_DIVISOR0                       0x2

    * Control for a clock that will be generated in the LPD, but used in the F
    * PD as a clock source for the peripheral clock muxes.
    * (OFFSET, MASK, VALUE)      (0XFF5E0048, 0x00003F00U ,0x00000200U)
    */
	PSU_Mask_Write(CRL_APB_RPLL_TO_FPD_CTRL_OFFSET,
		0x00003F00U, 0x00000200U);
/*##################################################################### */

    /*
    * RPLL FRAC CFG
    */
    /*
    * IOPLL INIT
    */
    /*
    * Register : IOPLL_CFG @ 0XFF5E0024

    * PLL loop filter resistor control
    *  PSU_CRL_APB_IOPLL_CFG_RES                                   0x2

    * PLL charge pump control
    *  PSU_CRL_APB_IOPLL_CFG_CP                                    0x4

    * PLL loop filter high frequency capacitor control
    *  PSU_CRL_APB_IOPLL_CFG_LFHF                                  0x3

    * Lock circuit counter setting
    *  PSU_CRL_APB_IOPLL_CFG_LOCK_CNT                              0x258

    * Lock circuit configuration settings for lock windowsize
    *  PSU_CRL_APB_IOPLL_CFG_LOCK_DLY                              0x3f

    * Helper data. Values are to be looked up in a table from Data Sheet
    * (OFFSET, MASK, VALUE)      (0XFF5E0024, 0xFE7FEDEFU ,0x7E4B0C82U)
    */
	PSU_Mask_Write(CRL_APB_IOPLL_CFG_OFFSET, 0xFE7FEDEFU, 0x7E4B0C82U);
/*##################################################################### */

    /*
    * UPDATE FB_DIV
    */
    /*
    * Register : IOPLL_CTRL @ 0XFF5E0020

    * Mux select for determining which clock feeds this PLL. 0XX pss_ref_clk i
    * s the source 100 video clk is the source 101 pss_alt_ref_clk is the sour
    * ce 110 aux_refclk[X] is the source 111 gt_crx_ref_clk is the source
    *  PSU_CRL_APB_IOPLL_CTRL_PRE_SRC                              0x0

    * The integer portion of the feedback divider to the PLL
    *  PSU_CRL_APB_IOPLL_CTRL_FBDIV                                0x5a

    * This turns on the divide by 2 that is inside of the PLL. This does not c
    * hange the VCO frequency, just the output frequency
    *  PSU_CRL_APB_IOPLL_CTRL_DIV2                                 0x1

    * PLL Basic Control
    * (OFFSET, MASK, VALUE)      (0XFF5E0020, 0x00717F00U ,0x00015A00U)
    */
	PSU_Mask_Write(CRL_APB_IOPLL_CTRL_OFFSET, 0x00717F00U, 0x00015A00U);
/*##################################################################### */

    /*
    * BY PASS PLL
    */
    /*
    * Register : IOPLL_CTRL @ 0XFF5E0020

    * Bypasses the PLL clock. The usable clock will be determined from the POS
    * T_SRC field. (This signal may only be toggled after 4 cycles of the old
    * clock and 4 cycles of the new clock. This is not usually an issue, but d
    * esigners must be aware.)
    *  PSU_CRL_APB_IOPLL_CTRL_BYPASS                               1

    * PLL Basic Control
    * (OFFSET, MASK, VALUE)      (0XFF5E0020, 0x00000008U ,0x00000008U)
    */
	PSU_Mask_Write(CRL_APB_IOPLL_CTRL_OFFSET, 0x00000008U, 0x00000008U);
/*##################################################################### */

    /*
    * ASSERT RESET
    */
    /*
    * Register : IOPLL_CTRL @ 0XFF5E0020

    * Asserts Reset to the PLL. When asserting reset, the PLL must already be
    * in BYPASS.
    *  PSU_CRL_APB_IOPLL_CTRL_RESET                                1

    * PLL Basic Control
    * (OFFSET, MASK, VALUE)      (0XFF5E0020, 0x00000001U ,0x00000001U)
    */
	PSU_Mask_Write(CRL_APB_IOPLL_CTRL_OFFSET, 0x00000001U, 0x00000001U);
/*##################################################################### */

    /*
    * DEASSERT RESET
    */
    /*
    * Register : IOPLL_CTRL @ 0XFF5E0020

    * Asserts Reset to the PLL. When asserting reset, the PLL must already be
    * in BYPASS.
    *  PSU_CRL_APB_IOPLL_CTRL_RESET                                0

    * PLL Basic Control
    * (OFFSET, MASK, VALUE)      (0XFF5E0020, 0x00000001U ,0x00000000U)
    */
	PSU_Mask_Write(CRL_APB_IOPLL_CTRL_OFFSET, 0x00000001U, 0x00000000U);
/*##################################################################### */

    /*
    * CHECK PLL STATUS
    */
    /*
    * Register : PLL_STATUS @ 0XFF5E0040

    * IOPLL is locked
    *  PSU_CRL_APB_PLL_STATUS_IOPLL_LOCK                           1
    * (OFFSET, MASK, VALUE)      (0XFF5E0040, 0x00000001U ,0x00000001U)
		*/
	mask_poll(CRL_APB_PLL_STATUS_OFFSET, 0x00000001U);

/*##################################################################### */

    /*
    * REMOVE PLL BY PASS
    */
    /*
    * Register : IOPLL_CTRL @ 0XFF5E0020

    * Bypasses the PLL clock. The usable clock will be determined from the POS
    * T_SRC field. (This signal may only be toggled after 4 cycles of the old
    * clock and 4 cycles of the new clock. This is not usually an issue, but d
    * esigners must be aware.)
    *  PSU_CRL_APB_IOPLL_CTRL_BYPASS                               0

    * PLL Basic Control
    * (OFFSET, MASK, VALUE)      (0XFF5E0020, 0x00000008U ,0x00000000U)
    */
	PSU_Mask_Write(CRL_APB_IOPLL_CTRL_OFFSET, 0x00000008U, 0x00000000U);
/*##################################################################### */

    /*
    * Register : IOPLL_TO_FPD_CTRL @ 0XFF5E0044

    * Divisor value for this clock.
    *  PSU_CRL_APB_IOPLL_TO_FPD_CTRL_DIVISOR0                      0x3

    * Control for a clock that will be generated in the LPD, but used in the F
    * PD as a clock source for the peripheral clock muxes.
    * (OFFSET, MASK, VALUE)      (0XFF5E0044, 0x00003F00U ,0x00000300U)
    */
	PSU_Mask_Write(CRL_APB_IOPLL_TO_FPD_CTRL_OFFSET,
		0x00003F00U, 0x00000300U);
/*##################################################################### */

    /*
    * IOPLL FRAC CFG
    */
    /*
    * APU_PLL INIT
    */
    /*
    * Register : APLL_CFG @ 0XFD1A0024

    * PLL loop filter resistor control
    *  PSU_CRF_APB_APLL_CFG_RES                                    0x2

    * PLL charge pump control
    *  PSU_CRF_APB_APLL_CFG_CP                                     0x3

    * PLL loop filter high frequency capacitor control
    *  PSU_CRF_APB_APLL_CFG_LFHF                                   0x3

    * Lock circuit counter setting
    *  PSU_CRF_APB_APLL_CFG_LOCK_CNT                               0x258

    * Lock circuit configuration settings for lock windowsize
    *  PSU_CRF_APB_APLL_CFG_LOCK_DLY                               0x3f

    * Helper data. Values are to be looked up in a table from Data Sheet
    * (OFFSET, MASK, VALUE)      (0XFD1A0024, 0xFE7FEDEFU ,0x7E4B0C62U)
    */
	PSU_Mask_Write(CRF_APB_APLL_CFG_OFFSET, 0xFE7FEDEFU, 0x7E4B0C62U);
/*##################################################################### */

    /*
    * UPDATE FB_DIV
    */
    /*
    * Register : APLL_CTRL @ 0XFD1A0020

    * Mux select for determining which clock feeds this PLL. 0XX pss_ref_clk i
    * s the source 100 video clk is the source 101 pss_alt_ref_clk is the sour
    * ce 110 aux_refclk[X] is the source 111 gt_crx_ref_clk is the source
    *  PSU_CRF_APB_APLL_CTRL_PRE_SRC                               0x0

    * The integer portion of the feedback divider to the PLL
    *  PSU_CRF_APB_APLL_CTRL_FBDIV                                 0x48

    * This turns on the divide by 2 that is inside of the PLL. This does not c
    * hange the VCO frequency, just the output frequency
    *  PSU_CRF_APB_APLL_CTRL_DIV2                                  0x1

    * PLL Basic Control
    * (OFFSET, MASK, VALUE)      (0XFD1A0020, 0x00717F00U ,0x00014800U)
    */
	PSU_Mask_Write(CRF_APB_APLL_CTRL_OFFSET, 0x00717F00U, 0x00014800U);
/*##################################################################### */

    /*
    * BY PASS PLL
    */
    /*
    * Register : APLL_CTRL @ 0XFD1A0020

    * Bypasses the PLL clock. The usable clock will be determined from the POS
    * T_SRC field. (This signal may only be toggled after 4 cycles of the old
    * clock and 4 cycles of the new clock. This is not usually an issue, but d
    * esigners must be aware.)
    *  PSU_CRF_APB_APLL_CTRL_BYPASS                                1

    * PLL Basic Control
    * (OFFSET, MASK, VALUE)      (0XFD1A0020, 0x00000008U ,0x00000008U)
    */
	PSU_Mask_Write(CRF_APB_APLL_CTRL_OFFSET, 0x00000008U, 0x00000008U);
/*##################################################################### */

    /*
    * ASSERT RESET
    */
    /*
    * Register : APLL_CTRL @ 0XFD1A0020

    * Asserts Reset to the PLL. When asserting reset, the PLL must already be
    * in BYPASS.
    *  PSU_CRF_APB_APLL_CTRL_RESET                                 1

    * PLL Basic Control
    * (OFFSET, MASK, VALUE)      (0XFD1A0020, 0x00000001U ,0x00000001U)
    */
	PSU_Mask_Write(CRF_APB_APLL_CTRL_OFFSET, 0x00000001U, 0x00000001U);
/*##################################################################### */

    /*
    * DEASSERT RESET
    */
    /*
    * Register : APLL_CTRL @ 0XFD1A0020

    * Asserts Reset to the PLL. When asserting reset, the PLL must already be
    * in BYPASS.
    *  PSU_CRF_APB_APLL_CTRL_RESET                                 0

    * PLL Basic Control
    * (OFFSET, MASK, VALUE)      (0XFD1A0020, 0x00000001U ,0x00000000U)
    */
	PSU_Mask_Write(CRF_APB_APLL_CTRL_OFFSET, 0x00000001U, 0x00000000U);
/*##################################################################### */

    /*
    * CHECK PLL STATUS
    */
    /*
    * Register : PLL_STATUS @ 0XFD1A0044

    * APLL is locked
    *  PSU_CRF_APB_PLL_STATUS_APLL_LOCK                            1
    * (OFFSET, MASK, VALUE)      (0XFD1A0044, 0x00000001U ,0x00000001U)
		*/
	mask_poll(CRF_APB_PLL_STATUS_OFFSET, 0x00000001U);

/*##################################################################### */

    /*
    * REMOVE PLL BY PASS
    */
    /*
    * Register : APLL_CTRL @ 0XFD1A0020

    * Bypasses the PLL clock. The usable clock will be determined from the POS
    * T_SRC field. (This signal may only be toggled after 4 cycles of the old
    * clock and 4 cycles of the new clock. This is not usually an issue, but d
    * esigners must be aware.)
    *  PSU_CRF_APB_APLL_CTRL_BYPASS                                0

    * PLL Basic Control
    * (OFFSET, MASK, VALUE)      (0XFD1A0020, 0x00000008U ,0x00000000U)
    */
	PSU_Mask_Write(CRF_APB_APLL_CTRL_OFFSET, 0x00000008U, 0x00000000U);
/*##################################################################### */

    /*
    * Register : APLL_TO_LPD_CTRL @ 0XFD1A0048

    * Divisor value for this clock.
    *  PSU_CRF_APB_APLL_TO_LPD_CTRL_DIVISOR0                       0x3

    * Control for a clock that will be generated in the FPD, but used in the L
    * PD as a clock source for the peripheral clock muxes.
    * (OFFSET, MASK, VALUE)      (0XFD1A0048, 0x00003F00U ,0x00000300U)
    */
	PSU_Mask_Write(CRF_APB_APLL_TO_LPD_CTRL_OFFSET,
		0x00003F00U, 0x00000300U);
/*##################################################################### */

    /*
    * APLL FRAC CFG
    */
    /*
    * DDR_PLL INIT
    */
    /*
    * Register : DPLL_CFG @ 0XFD1A0030

    * PLL loop filter resistor control
    *  PSU_CRF_APB_DPLL_CFG_RES                                    0x2

    * PLL charge pump control
    *  PSU_CRF_APB_DPLL_CFG_CP                                     0x3

    * PLL loop filter high frequency capacitor control
    *  PSU_CRF_APB_DPLL_CFG_LFHF                                   0x3

    * Lock circuit counter setting
    *  PSU_CRF_APB_DPLL_CFG_LOCK_CNT                               0x258

    * Lock circuit configuration settings for lock windowsize
    *  PSU_CRF_APB_DPLL_CFG_LOCK_DLY                               0x3f

    * Helper data. Values are to be looked up in a table from Data Sheet
    * (OFFSET, MASK, VALUE)      (0XFD1A0030, 0xFE7FEDEFU ,0x7E4B0C62U)
    */
	PSU_Mask_Write(CRF_APB_DPLL_CFG_OFFSET, 0xFE7FEDEFU, 0x7E4B0C62U);
/*##################################################################### */

    /*
    * UPDATE FB_DIV
    */
    /*
    * Register : DPLL_CTRL @ 0XFD1A002C

    * Mux select for determining which clock feeds this PLL. 0XX pss_ref_clk i
    * s the source 100 video clk is the source 101 pss_alt_ref_clk is the sour
    * ce 110 aux_refclk[X] is the source 111 gt_crx_ref_clk is the source
    *  PSU_CRF_APB_DPLL_CTRL_PRE_SRC                               0x0

    * The integer portion of the feedback divider to the PLL
    *  PSU_CRF_APB_DPLL_CTRL_FBDIV                                 0x40

    * This turns on the divide by 2 that is inside of the PLL. This does not c
    * hange the VCO frequency, just the output frequency
    *  PSU_CRF_APB_DPLL_CTRL_DIV2                                  0x1

    * PLL Basic Control
    * (OFFSET, MASK, VALUE)      (0XFD1A002C, 0x00717F00U ,0x00014000U)
    */
	PSU_Mask_Write(CRF_APB_DPLL_CTRL_OFFSET, 0x00717F00U, 0x00014000U);
/*##################################################################### */

    /*
    * BY PASS PLL
    */
    /*
    * Register : DPLL_CTRL @ 0XFD1A002C

    * Bypasses the PLL clock. The usable clock will be determined from the POS
    * T_SRC field. (This signal may only be toggled after 4 cycles of the old
    * clock and 4 cycles of the new clock. This is not usually an issue, but d
    * esigners must be aware.)
    *  PSU_CRF_APB_DPLL_CTRL_BYPASS                                1

    * PLL Basic Control
    * (OFFSET, MASK, VALUE)      (0XFD1A002C, 0x00000008U ,0x00000008U)
    */
	PSU_Mask_Write(CRF_APB_DPLL_CTRL_OFFSET, 0x00000008U, 0x00000008U);
/*##################################################################### */

    /*
    * ASSERT RESET
    */
    /*
    * Register : DPLL_CTRL @ 0XFD1A002C

    * Asserts Reset to the PLL. When asserting reset, the PLL must already be
    * in BYPASS.
    *  PSU_CRF_APB_DPLL_CTRL_RESET                                 1

    * PLL Basic Control
    * (OFFSET, MASK, VALUE)      (0XFD1A002C, 0x00000001U ,0x00000001U)
    */
	PSU_Mask_Write(CRF_APB_DPLL_CTRL_OFFSET, 0x00000001U, 0x00000001U);
/*##################################################################### */

    /*
    * DEASSERT RESET
    */
    /*
    * Register : DPLL_CTRL @ 0XFD1A002C

    * Asserts Reset to the PLL. When asserting reset, the PLL must already be
    * in BYPASS.
    *  PSU_CRF_APB_DPLL_CTRL_RESET                                 0

    * PLL Basic Control
    * (OFFSET, MASK, VALUE)      (0XFD1A002C, 0x00000001U ,0x00000000U)
    */
	PSU_Mask_Write(CRF_APB_DPLL_CTRL_OFFSET, 0x00000001U, 0x00000000U);
/*##################################################################### */

    /*
    * CHECK PLL STATUS
    */
    /*
    * Register : PLL_STATUS @ 0XFD1A0044

    * DPLL is locked
    *  PSU_CRF_APB_PLL_STATUS_DPLL_LOCK                            1
    * (OFFSET, MASK, VALUE)      (0XFD1A0044, 0x00000002U ,0x00000002U)
		*/
	mask_poll(CRF_APB_PLL_STATUS_OFFSET, 0x00000002U);

/*##################################################################### */

    /*
    * REMOVE PLL BY PASS
    */
    /*
    * Register : DPLL_CTRL @ 0XFD1A002C

    * Bypasses the PLL clock. The usable clock will be determined from the POS
    * T_SRC field. (This signal may only be toggled after 4 cycles of the old
    * clock and 4 cycles of the new clock. This is not usually an issue, but d
    * esigners must be aware.)
    *  PSU_CRF_APB_DPLL_CTRL_BYPASS                                0

    * PLL Basic Control
    * (OFFSET, MASK, VALUE)      (0XFD1A002C, 0x00000008U ,0x00000000U)
    */
	PSU_Mask_Write(CRF_APB_DPLL_CTRL_OFFSET, 0x00000008U, 0x00000000U);
/*##################################################################### */

    /*
    * Register : DPLL_TO_LPD_CTRL @ 0XFD1A004C

    * Divisor value for this clock.
    *  PSU_CRF_APB_DPLL_TO_LPD_CTRL_DIVISOR0                       0x2

    * Control for a clock that will be generated in the FPD, but used in the L
    * PD as a clock source for the peripheral clock muxes.
    * (OFFSET, MASK, VALUE)      (0XFD1A004C, 0x00003F00U ,0x00000200U)
    */
	PSU_Mask_Write(CRF_APB_DPLL_TO_LPD_CTRL_OFFSET,
		0x00003F00U, 0x00000200U);
/*##################################################################### */

    /*
    * DPLL FRAC CFG
    */
    /*
    * VIDEO_PLL INIT
    */
    /*
    * Register : VPLL_CFG @ 0XFD1A003C

    * PLL loop filter resistor control
    *  PSU_CRF_APB_VPLL_CFG_RES                                    0x2

    * PLL charge pump control
    *  PSU_CRF_APB_VPLL_CFG_CP                                     0x4

    * PLL loop filter high frequency capacitor control
    *  PSU_CRF_APB_VPLL_CFG_LFHF                                   0x3

    * Lock circuit counter setting
    *  PSU_CRF_APB_VPLL_CFG_LOCK_CNT                               0x258

    * Lock circuit configuration settings for lock windowsize
    *  PSU_CRF_APB_VPLL_CFG_LOCK_DLY                               0x3f

    * Helper data. Values are to be looked up in a table from Data Sheet
    * (OFFSET, MASK, VALUE)      (0XFD1A003C, 0xFE7FEDEFU ,0x7E4B0C82U)
    */
	PSU_Mask_Write(CRF_APB_VPLL_CFG_OFFSET, 0xFE7FEDEFU, 0x7E4B0C82U);
/*##################################################################### */

    /*
    * UPDATE FB_DIV
    */
    /*
    * Register : VPLL_CTRL @ 0XFD1A0038

    * Mux select for determining which clock feeds this PLL. 0XX pss_ref_clk i
    * s the source 100 video clk is the source 101 pss_alt_ref_clk is the sour
    * ce 110 aux_refclk[X] is the source 111 gt_crx_ref_clk is the source
    *  PSU_CRF_APB_VPLL_CTRL_PRE_SRC                               0x0

    * The integer portion of the feedback divider to the PLL
    *  PSU_CRF_APB_VPLL_CTRL_FBDIV                                 0x5a

    * This turns on the divide by 2 that is inside of the PLL. This does not c
    * hange the VCO frequency, just the output frequency
    *  PSU_CRF_APB_VPLL_CTRL_DIV2                                  0x1

    * PLL Basic Control
    * (OFFSET, MASK, VALUE)      (0XFD1A0038, 0x00717F00U ,0x00015A00U)
    */
	PSU_Mask_Write(CRF_APB_VPLL_CTRL_OFFSET, 0x00717F00U, 0x00015A00U);
/*##################################################################### */

    /*
    * BY PASS PLL
    */
    /*
    * Register : VPLL_CTRL @ 0XFD1A0038

    * Bypasses the PLL clock. The usable clock will be determined from the POS
    * T_SRC field. (This signal may only be toggled after 4 cycles of the old
    * clock and 4 cycles of the new clock. This is not usually an issue, but d
    * esigners must be aware.)
    *  PSU_CRF_APB_VPLL_CTRL_BYPASS                                1

    * PLL Basic Control
    * (OFFSET, MASK, VALUE)      (0XFD1A0038, 0x00000008U ,0x00000008U)
    */
	PSU_Mask_Write(CRF_APB_VPLL_CTRL_OFFSET, 0x00000008U, 0x00000008U);
/*##################################################################### */

    /*
    * ASSERT RESET
    */
    /*
    * Register : VPLL_CTRL @ 0XFD1A0038

    * Asserts Reset to the PLL. When asserting reset, the PLL must already be
    * in BYPASS.
    *  PSU_CRF_APB_VPLL_CTRL_RESET                                 1

    * PLL Basic Control
    * (OFFSET, MASK, VALUE)      (0XFD1A0038, 0x00000001U ,0x00000001U)
    */
	PSU_Mask_Write(CRF_APB_VPLL_CTRL_OFFSET, 0x00000001U, 0x00000001U);
/*##################################################################### */

    /*
    * DEASSERT RESET
    */
    /*
    * Register : VPLL_CTRL @ 0XFD1A0038

    * Asserts Reset to the PLL. When asserting reset, the PLL must already be
    * in BYPASS.
    *  PSU_CRF_APB_VPLL_CTRL_RESET                                 0

    * PLL Basic Control
    * (OFFSET, MASK, VALUE)      (0XFD1A0038, 0x00000001U ,0x00000000U)
    */
	PSU_Mask_Write(CRF_APB_VPLL_CTRL_OFFSET, 0x00000001U, 0x00000000U);
/*##################################################################### */

    /*
    * CHECK PLL STATUS
    */
    /*
    * Register : PLL_STATUS @ 0XFD1A0044

    * VPLL is locked
    *  PSU_CRF_APB_PLL_STATUS_VPLL_LOCK                            1
    * (OFFSET, MASK, VALUE)      (0XFD1A0044, 0x00000004U ,0x00000004U)
		*/
	mask_poll(CRF_APB_PLL_STATUS_OFFSET, 0x00000004U);

/*##################################################################### */

    /*
    * REMOVE PLL BY PASS
    */
    /*
    * Register : VPLL_CTRL @ 0XFD1A0038

    * Bypasses the PLL clock. The usable clock will be determined from the POS
    * T_SRC field. (This signal may only be toggled after 4 cycles of the old
    * clock and 4 cycles of the new clock. This is not usually an issue, but d
    * esigners must be aware.)
    *  PSU_CRF_APB_VPLL_CTRL_BYPASS                                0

    * PLL Basic Control
    * (OFFSET, MASK, VALUE)      (0XFD1A0038, 0x00000008U ,0x00000000U)
    */
	PSU_Mask_Write(CRF_APB_VPLL_CTRL_OFFSET, 0x00000008U, 0x00000000U);
/*##################################################################### */

    /*
    * Register : VPLL_TO_LPD_CTRL @ 0XFD1A0050

    * Divisor value for this clock.
    *  PSU_CRF_APB_VPLL_TO_LPD_CTRL_DIVISOR0                       0x3

    * Control for a clock that will be generated in the FPD, but used in the L
    * PD as a clock source for the peripheral clock muxes.
    * (OFFSET, MASK, VALUE)      (0XFD1A0050, 0x00003F00U ,0x00000300U)
    */
	PSU_Mask_Write(CRF_APB_VPLL_TO_LPD_CTRL_OFFSET,
		0x00003F00U, 0x00000300U);
/*##################################################################### */

    /*
    * VIDEO FRAC CFG
    */

	return 1;
}
unsigned long psu_clock_init_data(void)
{
    /*
    * CLOCK CONTROL SLCR REGISTER
    */
    /*
    * Register : GEM3_REF_CTRL @ 0XFF5E005C

    * Clock active for the RX channel
    *  PSU_CRL_APB_GEM3_REF_CTRL_RX_CLKACT                         0x1

    * Clock active signal. Switch to 0 to disable the clock
    *  PSU_CRL_APB_GEM3_REF_CTRL_CLKACT                            0x1

    * 6 bit divider
    *  PSU_CRL_APB_GEM3_REF_CTRL_DIVISOR1                          0x1

    * 6 bit divider
    *  PSU_CRL_APB_GEM3_REF_CTRL_DIVISOR0                          0xc

    * 000 = IOPLL; 010 = RPLL; 011 = DPLL; (This signal may only be toggled af
    * ter 4 cycles of the old clock and 4 cycles of the new clock. This is not
    *  usually an issue, but designers must be aware.)
    *  PSU_CRL_APB_GEM3_REF_CTRL_SRCSEL                            0x0

    * This register controls this reference clock
    * (OFFSET, MASK, VALUE)      (0XFF5E005C, 0x063F3F07U ,0x06010C00U)
    */
	PSU_Mask_Write(CRL_APB_GEM3_REF_CTRL_OFFSET,
		0x063F3F07U, 0x06010C00U);
/*##################################################################### */

    /*
    * Register : GEM_TSU_REF_CTRL @ 0XFF5E0100

    * 6 bit divider
    *  PSU_CRL_APB_GEM_TSU_REF_CTRL_DIVISOR0                       0x6

    * 000 = IOPLL; 010 = RPLL; 011 = DPLL; (This signal may only be toggled af
    * ter 4 cycles of the old clock and 4 cycles of the new clock. This is not
    *  usually an issue, but designers must be aware.)
    *  PSU_CRL_APB_GEM_TSU_REF_CTRL_SRCSEL                         0x0

    * 6 bit divider
    *  PSU_CRL_APB_GEM_TSU_REF_CTRL_DIVISOR1                       0x1

    * Clock active signal. Switch to 0 to disable the clock
    *  PSU_CRL_APB_GEM_TSU_REF_CTRL_CLKACT                         0x1

    * This register controls this reference clock
    * (OFFSET, MASK, VALUE)      (0XFF5E0100, 0x013F3F07U ,0x01010600U)
    */
	PSU_Mask_Write(CRL_APB_GEM_TSU_REF_CTRL_OFFSET,
		0x013F3F07U, 0x01010600U);
/*##################################################################### */

    /*
    * Register : USB0_BUS_REF_CTRL @ 0XFF5E0060

    * Clock active signal. Switch to 0 to disable the clock
    *  PSU_CRL_APB_USB0_BUS_REF_CTRL_CLKACT                        0x1

    * 6 bit divider
    *  PSU_CRL_APB_USB0_BUS_REF_CTRL_DIVISOR1                      0x1

    * 6 bit divider
    *  PSU_CRL_APB_USB0_BUS_REF_CTRL_DIVISOR0                      0x6

    * 000 = IOPLL; 010 = RPLL; 011 = DPLL; (This signal may only be toggled af
    * ter 4 cycles of the old clock and 4 cycles of the new clock. This is not
    *  usually an issue, but designers must be aware.)
    *  PSU_CRL_APB_USB0_BUS_REF_CTRL_SRCSEL                        0x0

    * This register controls this reference clock
    * (OFFSET, MASK, VALUE)      (0XFF5E0060, 0x023F3F07U ,0x02010600U)
    */
	PSU_Mask_Write(CRL_APB_USB0_BUS_REF_CTRL_OFFSET,
		0x023F3F07U, 0x02010600U);
/*##################################################################### */

    /*
    * Register : USB3_DUAL_REF_CTRL @ 0XFF5E004C

    * Clock active signal. Switch to 0 to disable the clock
    *  PSU_CRL_APB_USB3_DUAL_REF_CTRL_CLKACT                       0x1

    * 6 bit divider
    *  PSU_CRL_APB_USB3_DUAL_REF_CTRL_DIVISOR1                     0x3

    * 6 bit divider
    *  PSU_CRL_APB_USB3_DUAL_REF_CTRL_DIVISOR0                     0x19

    * 000 = IOPLL; 010 = RPLL; 011 = DPLL. (This signal may only be toggled af
    * ter 4 cycles of the old clock and 4 cycles of the new clock. This is not
    *  usually an issue, but designers must be aware.)
    *  PSU_CRL_APB_USB3_DUAL_REF_CTRL_SRCSEL                       0x0

    * This register controls this reference clock
    * (OFFSET, MASK, VALUE)      (0XFF5E004C, 0x023F3F07U ,0x02031900U)
    */
	PSU_Mask_Write(CRL_APB_USB3_DUAL_REF_CTRL_OFFSET,
		0x023F3F07U, 0x02031900U);
/*##################################################################### */

    /*
    * Register : QSPI_REF_CTRL @ 0XFF5E0068

    * Clock active signal. Switch to 0 to disable the clock
    *  PSU_CRL_APB_QSPI_REF_CTRL_CLKACT                            0x1

    * 6 bit divider
    *  PSU_CRL_APB_QSPI_REF_CTRL_DIVISOR1                          0x1

    * 6 bit divider
    *  PSU_CRL_APB_QSPI_REF_CTRL_DIVISOR0                          0xc

    * 000 = IOPLL; 010 = RPLL; 011 = DPLL; (This signal may only be toggled af
    * ter 4 cycles of the old clock and 4 cycles of the new clock. This is not
    *  usually an issue, but designers must be aware.)
    *  PSU_CRL_APB_QSPI_REF_CTRL_SRCSEL                            0x0

    * This register controls this reference clock
    * (OFFSET, MASK, VALUE)      (0XFF5E0068, 0x013F3F07U ,0x01010C00U)
    */
	PSU_Mask_Write(CRL_APB_QSPI_REF_CTRL_OFFSET,
		0x013F3F07U, 0x01010C00U);
/*##################################################################### */

    /*
    * Register : SDIO1_REF_CTRL @ 0XFF5E0070

    * Clock active signal. Switch to 0 to disable the clock
    *  PSU_CRL_APB_SDIO1_REF_CTRL_CLKACT                           0x1

    * 6 bit divider
    *  PSU_CRL_APB_SDIO1_REF_CTRL_DIVISOR1                         0x1

    * 6 bit divider
    *  PSU_CRL_APB_SDIO1_REF_CTRL_DIVISOR0                         0x8

    * 000 = IOPLL; 010 = RPLL; 011 = VPLL; (This signal may only be toggled af
    * ter 4 cycles of the old clock and 4 cycles of the new clock. This is not
    *  usually an issue, but designers must be aware.)
    *  PSU_CRL_APB_SDIO1_REF_CTRL_SRCSEL                           0x0

    * This register controls this reference clock
    * (OFFSET, MASK, VALUE)      (0XFF5E0070, 0x013F3F07U ,0x01010800U)
    */
	PSU_Mask_Write(CRL_APB_SDIO1_REF_CTRL_OFFSET,
		0x013F3F07U, 0x01010800U);
/*##################################################################### */

    /*
    * Register : SDIO_CLK_CTRL @ 0XFF18030C

    * MIO pad selection for sdio1_rx_clk (feedback clock from the PAD) 0: MIO
    * [51] 1: MIO [76]
    *  PSU_IOU_SLCR_SDIO_CLK_CTRL_SDIO1_RX_SRC_SEL                 0

    * SoC Debug Clock Control
    * (OFFSET, MASK, VALUE)      (0XFF18030C, 0x00020000U ,0x00000000U)
    */
	PSU_Mask_Write(IOU_SLCR_SDIO_CLK_CTRL_OFFSET,
		0x00020000U, 0x00000000U);
/*##################################################################### */

    /*
    * Register : UART0_REF_CTRL @ 0XFF5E0074

    * Clock active signal. Switch to 0 to disable the clock
    *  PSU_CRL_APB_UART0_REF_CTRL_CLKACT                           0x1

    * 6 bit divider
    *  PSU_CRL_APB_UART0_REF_CTRL_DIVISOR1                         0x1

    * 6 bit divider
    *  PSU_CRL_APB_UART0_REF_CTRL_DIVISOR0                         0xf

    * 000 = IOPLL; 010 = RPLL; 011 = DPLL; (This signal may only be toggled af
    * ter 4 cycles of the old clock and 4 cycles of the new clock. This is not
    *  usually an issue, but designers must be aware.)
    *  PSU_CRL_APB_UART0_REF_CTRL_SRCSEL                           0x0

    * This register controls this reference clock
    * (OFFSET, MASK, VALUE)      (0XFF5E0074, 0x013F3F07U ,0x01010F00U)
    */
	PSU_Mask_Write(CRL_APB_UART0_REF_CTRL_OFFSET,
		0x013F3F07U, 0x01010F00U);
/*##################################################################### */

    /*
    * Register : UART1_REF_CTRL @ 0XFF5E0078

    * Clock active signal. Switch to 0 to disable the clock
    *  PSU_CRL_APB_UART1_REF_CTRL_CLKACT                           0x1

    * 6 bit divider
    *  PSU_CRL_APB_UART1_REF_CTRL_DIVISOR1                         0x1

    * 6 bit divider
    *  PSU_CRL_APB_UART1_REF_CTRL_DIVISOR0                         0xf

    * 000 = IOPLL; 010 = RPLL; 011 = DPLL; (This signal may only be toggled af
    * ter 4 cycles of the old clock and 4 cycles of the new clock. This is not
    *  usually an issue, but designers must be aware.)
    *  PSU_CRL_APB_UART1_REF_CTRL_SRCSEL                           0x0

    * This register controls this reference clock
    * (OFFSET, MASK, VALUE)      (0XFF5E0078, 0x013F3F07U ,0x01010F00U)
    */
	PSU_Mask_Write(CRL_APB_UART1_REF_CTRL_OFFSET,
		0x013F3F07U, 0x01010F00U);
/*##################################################################### */

    /*
    * Register : I2C0_REF_CTRL @ 0XFF5E0120

    * Clock active signal. Switch to 0 to disable the clock
    *  PSU_CRL_APB_I2C0_REF_CTRL_CLKACT                            0x1

    * 6 bit divider
    *  PSU_CRL_APB_I2C0_REF_CTRL_DIVISOR1                          0x1

    * 6 bit divider
    *  PSU_CRL_APB_I2C0_REF_CTRL_DIVISOR0                          0xf

    * 000 = IOPLL; 010 = RPLL; 011 = DPLL; (This signal may only be toggled af
    * ter 4 cycles of the old clock and 4 cycles of the new clock. This is not
    *  usually an issue, but designers must be aware.)
    *  PSU_CRL_APB_I2C0_REF_CTRL_SRCSEL                            0x0

    * This register controls this reference clock
    * (OFFSET, MASK, VALUE)      (0XFF5E0120, 0x013F3F07U ,0x01010F00U)
    */
	PSU_Mask_Write(CRL_APB_I2C0_REF_CTRL_OFFSET,
		0x013F3F07U, 0x01010F00U);
/*##################################################################### */

    /*
    * Register : I2C1_REF_CTRL @ 0XFF5E0124

    * Clock active signal. Switch to 0 to disable the clock
    *  PSU_CRL_APB_I2C1_REF_CTRL_CLKACT                            0x1

    * 6 bit divider
    *  PSU_CRL_APB_I2C1_REF_CTRL_DIVISOR1                          0x1

    * 6 bit divider
    *  PSU_CRL_APB_I2C1_REF_CTRL_DIVISOR0                          0xf

    * 000 = IOPLL; 010 = RPLL; 011 = DPLL; (This signal may only be toggled af
    * ter 4 cycles of the old clock and 4 cycles of the new clock. This is not
    *  usually an issue, but designers must be aware.)
    *  PSU_CRL_APB_I2C1_REF_CTRL_SRCSEL                            0x0

    * This register controls this reference clock
    * (OFFSET, MASK, VALUE)      (0XFF5E0124, 0x013F3F07U ,0x01010F00U)
    */
	PSU_Mask_Write(CRL_APB_I2C1_REF_CTRL_OFFSET,
		0x013F3F07U, 0x01010F00U);
/*##################################################################### */

    /*
    * Register : CAN1_REF_CTRL @ 0XFF5E0088

    * Clock active signal. Switch to 0 to disable the clock
    *  PSU_CRL_APB_CAN1_REF_CTRL_CLKACT                            0x1

    * 6 bit divider
    *  PSU_CRL_APB_CAN1_REF_CTRL_DIVISOR1                          0x1

    * 6 bit divider
    *  PSU_CRL_APB_CAN1_REF_CTRL_DIVISOR0                          0xf

    * 000 = IOPLL; 010 = RPLL; 011 = DPLL; (This signal may only be toggled af
    * ter 4 cycles of the old clock and 4 cycles of the new clock. This is not
    *  usually an issue, but designers must be aware.)
    *  PSU_CRL_APB_CAN1_REF_CTRL_SRCSEL                            0x0

    * This register controls this reference clock
    * (OFFSET, MASK, VALUE)      (0XFF5E0088, 0x013F3F07U ,0x01010F00U)
    */
	PSU_Mask_Write(CRL_APB_CAN1_REF_CTRL_OFFSET,
		0x013F3F07U, 0x01010F00U);
/*##################################################################### */

    /*
    * Register : CPU_R5_CTRL @ 0XFF5E0090

    * Turing this off will shut down the OCM, some parts of the APM, and preve
    * nt transactions going from the FPD to the LPD and could lead to system h
    * ang
    *  PSU_CRL_APB_CPU_R5_CTRL_CLKACT                              0x1

    * 6 bit divider
    *  PSU_CRL_APB_CPU_R5_CTRL_DIVISOR0                            0x3

    * 000 = RPLL; 010 = IOPLL; 011 = DPLL; (This signal may only be toggled af
    * ter 4 cycles of the old clock and 4 cycles of the new clock. This is not
    *  usually an issue, but designers must be aware.)
    *  PSU_CRL_APB_CPU_R5_CTRL_SRCSEL                              0x2

    * This register controls this reference clock
    * (OFFSET, MASK, VALUE)      (0XFF5E0090, 0x01003F07U ,0x01000302U)
    */
	PSU_Mask_Write(CRL_APB_CPU_R5_CTRL_OFFSET, 0x01003F07U, 0x01000302U);
/*##################################################################### */

    /*
    * Register : IOU_SWITCH_CTRL @ 0XFF5E009C

    * Clock active signal. Switch to 0 to disable the clock
    *  PSU_CRL_APB_IOU_SWITCH_CTRL_CLKACT                          0x1

    * 6 bit divider
    *  PSU_CRL_APB_IOU_SWITCH_CTRL_DIVISOR0                        0x6

    * 000 = RPLL; 010 = IOPLL; 011 = DPLL; (This signal may only be toggled af
    * ter 4 cycles of the old clock and 4 cycles of the new clock. This is not
    *  usually an issue, but designers must be aware.)
    *  PSU_CRL_APB_IOU_SWITCH_CTRL_SRCSEL                          0x2

    * This register controls this reference clock
    * (OFFSET, MASK, VALUE)      (0XFF5E009C, 0x01003F07U ,0x01000602U)
    */
	PSU_Mask_Write(CRL_APB_IOU_SWITCH_CTRL_OFFSET,
		0x01003F07U, 0x01000602U);
/*##################################################################### */

    /*
    * Register : PCAP_CTRL @ 0XFF5E00A4

    * Clock active signal. Switch to 0 to disable the clock
    *  PSU_CRL_APB_PCAP_CTRL_CLKACT                                0x1

    * 6 bit divider
    *  PSU_CRL_APB_PCAP_CTRL_DIVISOR0                              0x8

    * 000 = IOPLL; 010 = RPLL; 011 = DPLL; (This signal may only be toggled af
    * ter 4 cycles of the old clock and 4 cycles of the new clock. This is not
    *  usually an issue, but designers must be aware.)
    *  PSU_CRL_APB_PCAP_CTRL_SRCSEL                                0x0

    * This register controls this reference clock
    * (OFFSET, MASK, VALUE)      (0XFF5E00A4, 0x01003F07U ,0x01000800U)
    */
	PSU_Mask_Write(CRL_APB_PCAP_CTRL_OFFSET, 0x01003F07U, 0x01000800U);
/*##################################################################### */

    /*
    * Register : LPD_SWITCH_CTRL @ 0XFF5E00A8

    * Clock active signal. Switch to 0 to disable the clock
    *  PSU_CRL_APB_LPD_SWITCH_CTRL_CLKACT                          0x1

    * 6 bit divider
    *  PSU_CRL_APB_LPD_SWITCH_CTRL_DIVISOR0                        0x3

    * 000 = RPLL; 010 = IOPLL; 011 = DPLL; (This signal may only be toggled af
    * ter 4 cycles of the old clock and 4 cycles of the new clock. This is not
    *  usually an issue, but designers must be aware.)
    *  PSU_CRL_APB_LPD_SWITCH_CTRL_SRCSEL                          0x2

    * This register controls this reference clock
    * (OFFSET, MASK, VALUE)      (0XFF5E00A8, 0x01003F07U ,0x01000302U)
    */
	PSU_Mask_Write(CRL_APB_LPD_SWITCH_CTRL_OFFSET,
		0x01003F07U, 0x01000302U);
/*##################################################################### */

    /*
    * Register : LPD_LSBUS_CTRL @ 0XFF5E00AC

    * Clock active signal. Switch to 0 to disable the clock
    *  PSU_CRL_APB_LPD_LSBUS_CTRL_CLKACT                           0x1

    * 6 bit divider
    *  PSU_CRL_APB_LPD_LSBUS_CTRL_DIVISOR0                         0xf

    * 000 = RPLL; 010 = IOPLL; 011 = DPLL; (This signal may only be toggled af
    * ter 4 cycles of the old clock and 4 cycles of the new clock. This is not
    *  usually an issue, but designers must be aware.)
    *  PSU_CRL_APB_LPD_LSBUS_CTRL_SRCSEL                           0x2

    * This register controls this reference clock
    * (OFFSET, MASK, VALUE)      (0XFF5E00AC, 0x01003F07U ,0x01000F02U)
    */
	PSU_Mask_Write(CRL_APB_LPD_LSBUS_CTRL_OFFSET,
		0x01003F07U, 0x01000F02U);
/*##################################################################### */

    /*
    * Register : DBG_LPD_CTRL @ 0XFF5E00B0

    * Clock active signal. Switch to 0 to disable the clock
    *  PSU_CRL_APB_DBG_LPD_CTRL_CLKACT                             0x1

    * 6 bit divider
    *  PSU_CRL_APB_DBG_LPD_CTRL_DIVISOR0                           0x6

    * 000 = RPLL; 010 = IOPLL; 011 = DPLL; (This signal may only be toggled af
    * ter 4 cycles of the old clock and 4 cycles of the new clock. This is not
    *  usually an issue, but designers must be aware.)
    *  PSU_CRL_APB_DBG_LPD_CTRL_SRCSEL                             0x2

    * This register controls this reference clock
    * (OFFSET, MASK, VALUE)      (0XFF5E00B0, 0x01003F07U ,0x01000602U)
    */
	PSU_Mask_Write(CRL_APB_DBG_LPD_CTRL_OFFSET,
		0x01003F07U, 0x01000602U);
/*##################################################################### */

    /*
    * Register : ADMA_REF_CTRL @ 0XFF5E00B8

    * Clock active signal. Switch to 0 to disable the clock
    *  PSU_CRL_APB_ADMA_REF_CTRL_CLKACT                            0x1

    * 6 bit divider
    *  PSU_CRL_APB_ADMA_REF_CTRL_DIVISOR0                          0x3

    * 000 = RPLL; 010 = IOPLL; 011 = DPLL; (This signal may only be toggled af
    * ter 4 cycles of the old clock and 4 cycles of the new clock. This is not
    *  usually an issue, but designers must be aware.)
    *  PSU_CRL_APB_ADMA_REF_CTRL_SRCSEL                            0x2

    * This register controls this reference clock
    * (OFFSET, MASK, VALUE)      (0XFF5E00B8, 0x01003F07U ,0x01000302U)
    */
	PSU_Mask_Write(CRL_APB_ADMA_REF_CTRL_OFFSET,
		0x01003F07U, 0x01000302U);
/*##################################################################### */

    /*
    * Register : PL0_REF_CTRL @ 0XFF5E00C0

    * Clock active signal. Switch to 0 to disable the clock
    *  PSU_CRL_APB_PL0_REF_CTRL_CLKACT                             0x1

    * 6 bit divider
    *  PSU_CRL_APB_PL0_REF_CTRL_DIVISOR1                           0x1

    * 6 bit divider
    *  PSU_CRL_APB_PL0_REF_CTRL_DIVISOR0                           0xf

    * 000 = IOPLL; 010 = RPLL; 011 = DPLL; (This signal may only be toggled af
    * ter 4 cycles of the old clock and 4 cycles of the new clock. This is not
    *  usually an issue, but designers must be aware.)
    *  PSU_CRL_APB_PL0_REF_CTRL_SRCSEL                             0x0

    * This register controls this reference clock
    * (OFFSET, MASK, VALUE)      (0XFF5E00C0, 0x013F3F07U ,0x01010F00U)
    */
	PSU_Mask_Write(CRL_APB_PL0_REF_CTRL_OFFSET,
		0x013F3F07U, 0x01010F00U);
/*##################################################################### */

    /*
    * Register : AMS_REF_CTRL @ 0XFF5E0108

    * 6 bit divider
    *  PSU_CRL_APB_AMS_REF_CTRL_DIVISOR1                           0x1

    * 6 bit divider
    *  PSU_CRL_APB_AMS_REF_CTRL_DIVISOR0                           0x1e

    * 000 = RPLL; 010 = IOPLL; 011 = DPLL; (This signal may only be toggled af
    * ter 4 cycles of the old clock and 4 cycles of the new clock. This is not
    *  usually an issue, but designers must be aware.)
    *  PSU_CRL_APB_AMS_REF_CTRL_SRCSEL                             0x2

    * Clock active signal. Switch to 0 to disable the clock
    *  PSU_CRL_APB_AMS_REF_CTRL_CLKACT                             0x1

    * This register controls this reference clock
    * (OFFSET, MASK, VALUE)      (0XFF5E0108, 0x013F3F07U ,0x01011E02U)
    */
	PSU_Mask_Write(CRL_APB_AMS_REF_CTRL_OFFSET,
		0x013F3F07U, 0x01011E02U);
/*##################################################################### */

    /*
    * Register : DLL_REF_CTRL @ 0XFF5E0104

    * 000 = IOPLL; 001 = RPLL; (This signal may only be toggled after 4 cycles
    *  of the old clock and 4 cycles of the new clock. This is not usually an
    * issue, but designers must be aware.)
    *  PSU_CRL_APB_DLL_REF_CTRL_SRCSEL                             0

    * This register controls this reference clock
    * (OFFSET, MASK, VALUE)      (0XFF5E0104, 0x00000007U ,0x00000000U)
    */
	PSU_Mask_Write(CRL_APB_DLL_REF_CTRL_OFFSET,
		0x00000007U, 0x00000000U);
/*##################################################################### */

    /*
    * Register : TIMESTAMP_REF_CTRL @ 0XFF5E0128

    * 6 bit divider
    *  PSU_CRL_APB_TIMESTAMP_REF_CTRL_DIVISOR0                     0xf

    * 1XX = pss_ref_clk; 000 = IOPLL; 010 = RPLL; 011 = DPLL; (This signal may
    *  only be toggled after 4 cycles of the old clock and 4 cycles of the new
    *  clock. This is not usually an issue, but designers must be aware.)
    *  PSU_CRL_APB_TIMESTAMP_REF_CTRL_SRCSEL                       0x0

    * Clock active signal. Switch to 0 to disable the clock
    *  PSU_CRL_APB_TIMESTAMP_REF_CTRL_CLKACT                       0x1

    * This register controls this reference clock
    * (OFFSET, MASK, VALUE)      (0XFF5E0128, 0x01003F07U ,0x01000F00U)
    */
	PSU_Mask_Write(CRL_APB_TIMESTAMP_REF_CTRL_OFFSET,
		0x01003F07U, 0x01000F00U);
/*##################################################################### */

    /*
    * Register : SATA_REF_CTRL @ 0XFD1A00A0

    * 000 = IOPLL_TO_FPD; 010 = APLL; 011 = DPLL; (This signal may only be tog
    * gled after 4 cycles of the old clock and 4 cycles of the new clock. This
    *  is not usually an issue, but designers must be aware.)
    *  PSU_CRF_APB_SATA_REF_CTRL_SRCSEL                            0x0

    * Clock active signal. Switch to 0 to disable the clock
    *  PSU_CRF_APB_SATA_REF_CTRL_CLKACT                            0x1

    * 6 bit divider
    *  PSU_CRF_APB_SATA_REF_CTRL_DIVISOR0                          0x2

    * This register controls this reference clock
    * (OFFSET, MASK, VALUE)      (0XFD1A00A0, 0x01003F07U ,0x01000200U)
    */
	PSU_Mask_Write(CRF_APB_SATA_REF_CTRL_OFFSET,
		0x01003F07U, 0x01000200U);
/*##################################################################### */

    /*
    * Register : PCIE_REF_CTRL @ 0XFD1A00B4

    * 000 = IOPLL_TO_FPD; 010 = RPLL_TO_FPD; 011 = DPLL; (This signal may only
    *  be toggled after 4 cycles of the old clock and 4 cycles of the new cloc
    * k. This is not usually an issue, but designers must be aware.)
    *  PSU_CRF_APB_PCIE_REF_CTRL_SRCSEL                            0x0

    * Clock active signal. Switch to 0 to disable the clock
    *  PSU_CRF_APB_PCIE_REF_CTRL_CLKACT                            0x1

    * 6 bit divider
    *  PSU_CRF_APB_PCIE_REF_CTRL_DIVISOR0                          0x2

    * This register controls this reference clock
    * (OFFSET, MASK, VALUE)      (0XFD1A00B4, 0x01003F07U ,0x01000200U)
    */
	PSU_Mask_Write(CRF_APB_PCIE_REF_CTRL_OFFSET,
		0x01003F07U, 0x01000200U);
/*##################################################################### */

    /*
    * Register : DP_VIDEO_REF_CTRL @ 0XFD1A0070

    * 6 bit divider
    *  PSU_CRF_APB_DP_VIDEO_REF_CTRL_DIVISOR1                      0x1

    * 6 bit divider
    *  PSU_CRF_APB_DP_VIDEO_REF_CTRL_DIVISOR0                      0x5

    * 000 = VPLL; 010 = DPLL; 011 = RPLL_TO_FPD - might be using extra mux; (T
    * his signal may only be toggled after 4 cycles of the old clock and 4 cyc
    * les of the new clock. This is not usually an issue, but designers must b
    * e aware.)
    *  PSU_CRF_APB_DP_VIDEO_REF_CTRL_SRCSEL                        0x0

    * Clock active signal. Switch to 0 to disable the clock
    *  PSU_CRF_APB_DP_VIDEO_REF_CTRL_CLKACT                        0x1

    * This register controls this reference clock
    * (OFFSET, MASK, VALUE)      (0XFD1A0070, 0x013F3F07U ,0x01010500U)
    */
	PSU_Mask_Write(CRF_APB_DP_VIDEO_REF_CTRL_OFFSET,
		0x013F3F07U, 0x01010500U);
/*##################################################################### */

    /*
    * Register : DP_AUDIO_REF_CTRL @ 0XFD1A0074

    * 6 bit divider
    *  PSU_CRF_APB_DP_AUDIO_REF_CTRL_DIVISOR1                      0x1

    * 6 bit divider
    *  PSU_CRF_APB_DP_AUDIO_REF_CTRL_DIVISOR0                      0xf

    * 000 = VPLL; 010 = DPLL; 011 = RPLL_TO_FPD - might be using extra mux; (T
    * his signal may only be toggled after 4 cycles of the old clock and 4 cyc
    * les of the new clock. This is not usually an issue, but designers must b
    * e aware.)
    *  PSU_CRF_APB_DP_AUDIO_REF_CTRL_SRCSEL                        0x3

    * Clock active signal. Switch to 0 to disable the clock
    *  PSU_CRF_APB_DP_AUDIO_REF_CTRL_CLKACT                        0x1

    * This register controls this reference clock
    * (OFFSET, MASK, VALUE)      (0XFD1A0074, 0x013F3F07U ,0x01010F03U)
    */
	PSU_Mask_Write(CRF_APB_DP_AUDIO_REF_CTRL_OFFSET,
		0x013F3F07U, 0x01010F03U);
/*##################################################################### */

    /*
    * Register : DP_STC_REF_CTRL @ 0XFD1A007C

    * 6 bit divider
    *  PSU_CRF_APB_DP_STC_REF_CTRL_DIVISOR1                        0x1

    * 6 bit divider
    *  PSU_CRF_APB_DP_STC_REF_CTRL_DIVISOR0                        0xe

    * 000 = VPLL; 010 = DPLL; 011 = RPLL_TO_FPD; (This signal may only be togg
    * led after 4 cycles of the old clock and 4 cycles of the new clock. This
    * is not usually an issue, but designers must be aware.)
    *  PSU_CRF_APB_DP_STC_REF_CTRL_SRCSEL                          0x3

    * Clock active signal. Switch to 0 to disable the clock
    *  PSU_CRF_APB_DP_STC_REF_CTRL_CLKACT                          0x1

    * This register controls this reference clock
    * (OFFSET, MASK, VALUE)      (0XFD1A007C, 0x013F3F07U ,0x01010E03U)
    */
	PSU_Mask_Write(CRF_APB_DP_STC_REF_CTRL_OFFSET,
		0x013F3F07U, 0x01010E03U);
/*##################################################################### */

    /*
    * Register : ACPU_CTRL @ 0XFD1A0060

    * 6 bit divider
    *  PSU_CRF_APB_ACPU_CTRL_DIVISOR0                              0x1

    * 000 = APLL; 010 = DPLL; 011 = VPLL; (This signal may only be toggled aft
    * er 4 cycles of the old clock and 4 cycles of the new clock. This is not
    * usually an issue, but designers must be aware.)
    *  PSU_CRF_APB_ACPU_CTRL_SRCSEL                                0x0

    * Clock active signal. Switch to 0 to disable the clock. For the half spee
    * d APU Clock
    *  PSU_CRF_APB_ACPU_CTRL_CLKACT_HALF                           0x1

    * Clock active signal. Switch to 0 to disable the clock. For the full spee
    * d ACPUX Clock. This will shut off the high speed clock to the entire APU
    *  PSU_CRF_APB_ACPU_CTRL_CLKACT_FULL                           0x1

    * This register controls this reference clock
    * (OFFSET, MASK, VALUE)      (0XFD1A0060, 0x03003F07U ,0x03000100U)
    */
	PSU_Mask_Write(CRF_APB_ACPU_CTRL_OFFSET, 0x03003F07U, 0x03000100U);
/*##################################################################### */

    /*
    * Register : DBG_FPD_CTRL @ 0XFD1A0068

    * 6 bit divider
    *  PSU_CRF_APB_DBG_FPD_CTRL_DIVISOR0                           0x2

    * 000 = IOPLL_TO_FPD; 010 = DPLL; 011 = APLL; (This signal may only be tog
    * gled after 4 cycles of the old clock and 4 cycles of the new clock. This
    *  is not usually an issue, but designers must be aware.)
    *  PSU_CRF_APB_DBG_FPD_CTRL_SRCSEL                             0x0

    * Clock active signal. Switch to 0 to disable the clock
    *  PSU_CRF_APB_DBG_FPD_CTRL_CLKACT                             0x1

    * This register controls this reference clock
    * (OFFSET, MASK, VALUE)      (0XFD1A0068, 0x01003F07U ,0x01000200U)
    */
	PSU_Mask_Write(CRF_APB_DBG_FPD_CTRL_OFFSET,
		0x01003F07U, 0x01000200U);
/*##################################################################### */

    /*
    * Register : DDR_CTRL @ 0XFD1A0080

    * 6 bit divider
    *  PSU_CRF_APB_DDR_CTRL_DIVISOR0                               0x2

    * 000 = DPLL; 001 = VPLL; (This signal may only be toggled after 4 cycles
    * of the old clock and 4 cycles of the new clock. This is not usually an i
    * ssue, but designers must be aware.)
    *  PSU_CRF_APB_DDR_CTRL_SRCSEL                                 0x0

    * This register controls this reference clock
    * (OFFSET, MASK, VALUE)      (0XFD1A0080, 0x00003F07U ,0x00000200U)
    */
	PSU_Mask_Write(CRF_APB_DDR_CTRL_OFFSET, 0x00003F07U, 0x00000200U);
/*##################################################################### */

    /*
    * Register : GPU_REF_CTRL @ 0XFD1A0084

    * 6 bit divider
    *  PSU_CRF_APB_GPU_REF_CTRL_DIVISOR0                           0x1

    * 000 = IOPLL_TO_FPD; 010 = VPLL; 011 = DPLL; (This signal may only be tog
    * gled after 4 cycles of the old clock and 4 cycles of the new clock. This
    *  is not usually an issue, but designers must be aware.)
    *  PSU_CRF_APB_GPU_REF_CTRL_SRCSEL                             0x0

    * Clock active signal. Switch to 0 to disable the clock, which will stop c
    * lock for GPU (and both Pixel Processors).
    *  PSU_CRF_APB_GPU_REF_CTRL_CLKACT                             0x1

    * Clock active signal for Pixel Processor. Switch to 0 to disable the cloc
    * k only to this Pixel Processor
    *  PSU_CRF_APB_GPU_REF_CTRL_PP0_CLKACT                         0x1

    * Clock active signal for Pixel Processor. Switch to 0 to disable the cloc
    * k only to this Pixel Processor
    *  PSU_CRF_APB_GPU_REF_CTRL_PP1_CLKACT                         0x1

    * This register controls this reference clock
    * (OFFSET, MASK, VALUE)      (0XFD1A0084, 0x07003F07U ,0x07000100U)
    */
	PSU_Mask_Write(CRF_APB_GPU_REF_CTRL_OFFSET,
		0x07003F07U, 0x07000100U);
/*##################################################################### */

    /*
    * Register : GDMA_REF_CTRL @ 0XFD1A00B8

    * 6 bit divider
    *  PSU_CRF_APB_GDMA_REF_CTRL_DIVISOR0                          0x2

    * 000 = APLL; 010 = VPLL; 011 = DPLL; (This signal may only be toggled aft
    * er 4 cycles of the old clock and 4 cycles of the new clock. This is not
    * usually an issue, but designers must be aware.)
    *  PSU_CRF_APB_GDMA_REF_CTRL_SRCSEL                            0x0

    * Clock active signal. Switch to 0 to disable the clock
    *  PSU_CRF_APB_GDMA_REF_CTRL_CLKACT                            0x1

    * This register controls this reference clock
    * (OFFSET, MASK, VALUE)      (0XFD1A00B8, 0x01003F07U ,0x01000200U)
    */
	PSU_Mask_Write(CRF_APB_GDMA_REF_CTRL_OFFSET,
		0x01003F07U, 0x01000200U);
/*##################################################################### */

    /*
    * Register : DPDMA_REF_CTRL @ 0XFD1A00BC

    * 6 bit divider
    *  PSU_CRF_APB_DPDMA_REF_CTRL_DIVISOR0                         0x2

    * 000 = APLL; 010 = VPLL; 011 = DPLL; (This signal may only be toggled aft
    * er 4 cycles of the old clock and 4 cycles of the new clock. This is not
    * usually an issue, but designers must be aware.)
    *  PSU_CRF_APB_DPDMA_REF_CTRL_SRCSEL                           0x0

    * Clock active signal. Switch to 0 to disable the clock
    *  PSU_CRF_APB_DPDMA_REF_CTRL_CLKACT                           0x1

    * This register controls this reference clock
    * (OFFSET, MASK, VALUE)      (0XFD1A00BC, 0x01003F07U ,0x01000200U)
    */
	PSU_Mask_Write(CRF_APB_DPDMA_REF_CTRL_OFFSET,
		0x01003F07U, 0x01000200U);
/*##################################################################### */

    /*
    * Register : TOPSW_MAIN_CTRL @ 0XFD1A00C0

    * 6 bit divider
    *  PSU_CRF_APB_TOPSW_MAIN_CTRL_DIVISOR0                        0x2

    * 000 = APLL; 010 = VPLL; 011 = DPLL; (This signal may only be toggled aft
    * er 4 cycles of the old clock and 4 cycles of the new clock. This is not
    * usually an issue, but designers must be aware.)
    *  PSU_CRF_APB_TOPSW_MAIN_CTRL_SRCSEL                          0x3

    * Clock active signal. Switch to 0 to disable the clock
    *  PSU_CRF_APB_TOPSW_MAIN_CTRL_CLKACT                          0x1

    * This register controls this reference clock
    * (OFFSET, MASK, VALUE)      (0XFD1A00C0, 0x01003F07U ,0x01000203U)
    */
	PSU_Mask_Write(CRF_APB_TOPSW_MAIN_CTRL_OFFSET,
		0x01003F07U, 0x01000203U);
/*##################################################################### */

    /*
    * Register : TOPSW_LSBUS_CTRL @ 0XFD1A00C4

    * 6 bit divider
    *  PSU_CRF_APB_TOPSW_LSBUS_CTRL_DIVISOR0                       0x5

    * 000 = APLL; 010 = IOPLL_TO_FPD; 011 = DPLL; (This signal may only be tog
    * gled after 4 cycles of the old clock and 4 cycles of the new clock. This
    *  is not usually an issue, but designers must be aware.)
    *  PSU_CRF_APB_TOPSW_LSBUS_CTRL_SRCSEL                         0x2

    * Clock active signal. Switch to 0 to disable the clock
    *  PSU_CRF_APB_TOPSW_LSBUS_CTRL_CLKACT                         0x1

    * This register controls this reference clock
    * (OFFSET, MASK, VALUE)      (0XFD1A00C4, 0x01003F07U ,0x01000502U)
    */
	PSU_Mask_Write(CRF_APB_TOPSW_LSBUS_CTRL_OFFSET,
		0x01003F07U, 0x01000502U);
/*##################################################################### */

    /*
    * Register : DBG_TSTMP_CTRL @ 0XFD1A00F8

    * 6 bit divider
    *  PSU_CRF_APB_DBG_TSTMP_CTRL_DIVISOR0                         0x2

    * 000 = IOPLL_TO_FPD; 010 = DPLL; 011 = APLL; (This signal may only be tog
    * gled after 4 cycles of the old clock and 4 cycles of the new clock. This
    *  is not usually an issue, but designers must be aware.)
    *  PSU_CRF_APB_DBG_TSTMP_CTRL_SRCSEL                           0x0

    * This register controls this reference clock
    * (OFFSET, MASK, VALUE)      (0XFD1A00F8, 0x00003F07U ,0x00000200U)
    */
	PSU_Mask_Write(CRF_APB_DBG_TSTMP_CTRL_OFFSET,
		0x00003F07U, 0x00000200U);
/*##################################################################### */

    /*
    * Register : IOU_TTC_APB_CLK @ 0XFF180380

    * 00" = Select the APB switch clock for the APB interface of TTC0'01" = Se
    * lect the PLL ref clock for the APB interface of TTC0'10" = Select the R5
    *  clock for the APB interface of TTC0
    *  PSU_IOU_SLCR_IOU_TTC_APB_CLK_TTC0_SEL                       0

    * 00" = Select the APB switch clock for the APB interface of TTC1'01" = Se
    * lect the PLL ref clock for the APB interface of TTC1'10" = Select the R5
    *  clock for the APB interface of TTC1
    *  PSU_IOU_SLCR_IOU_TTC_APB_CLK_TTC1_SEL                       0

    * 00" = Select the APB switch clock for the APB interface of TTC2'01" = Se
    * lect the PLL ref clock for the APB interface of TTC2'10" = Select the R5
    *  clock for the APB interface of TTC2
    *  PSU_IOU_SLCR_IOU_TTC_APB_CLK_TTC2_SEL                       0

    * 00" = Select the APB switch clock for the APB interface of TTC3'01" = Se
    * lect the PLL ref clock for the APB interface of TTC3'10" = Select the R5
    *  clock for the APB interface of TTC3
    *  PSU_IOU_SLCR_IOU_TTC_APB_CLK_TTC3_SEL                       0

    * TTC APB clock select
    * (OFFSET, MASK, VALUE)      (0XFF180380, 0x000000FFU ,0x00000000U)
    */
	PSU_Mask_Write(IOU_SLCR_IOU_TTC_APB_CLK_OFFSET,
		0x000000FFU, 0x00000000U);
/*##################################################################### */

    /*
    * Register : WDT_CLK_SEL @ 0XFD610100

    * System watchdog timer clock source selection: 0: Internal APB clock 1: E
    * xternal (PL clock via EMIO or Pinout clock via MIO)
    *  PSU_FPD_SLCR_WDT_CLK_SEL_SELECT                             0

    * SWDT clock source select
    * (OFFSET, MASK, VALUE)      (0XFD610100, 0x00000001U ,0x00000000U)
    */
	PSU_Mask_Write(FPD_SLCR_WDT_CLK_SEL_OFFSET,
		0x00000001U, 0x00000000U);
/*##################################################################### */

    /*
    * Register : WDT_CLK_SEL @ 0XFF180300

    * System watchdog timer clock source selection: 0: internal clock APB cloc
    * k 1: external clock from PL via EMIO, or from pinout via MIO
    *  PSU_IOU_SLCR_WDT_CLK_SEL_SELECT                             0

    * SWDT clock source select
    * (OFFSET, MASK, VALUE)      (0XFF180300, 0x00000001U ,0x00000000U)
    */
	PSU_Mask_Write(IOU_SLCR_WDT_CLK_SEL_OFFSET,
		0x00000001U, 0x00000000U);
/*##################################################################### */

    /*
    * Register : CSUPMU_WDT_CLK_SEL @ 0XFF410050

    * System watchdog timer clock source selection: 0: internal clock APB cloc
    * k 1: external clock pss_ref_clk
    *  PSU_LPD_SLCR_CSUPMU_WDT_CLK_SEL_SELECT                      0

    * SWDT clock source select
    * (OFFSET, MASK, VALUE)      (0XFF410050, 0x00000001U ,0x00000000U)
    */
	PSU_Mask_Write(LPD_SLCR_CSUPMU_WDT_CLK_SEL_OFFSET,
		0x00000001U, 0x00000000U);
/*##################################################################### */


	return 1;
}
unsigned long psu_ddr_init_data(void)
{
    /*
    * DDR INITIALIZATION
    */
    /*
    * DDR CONTROLLER RESET
    */
    /*
    * Register : RST_DDR_SS @ 0XFD1A0108

    * DDR block level reset inside of the DDR Sub System
    *  PSU_CRF_APB_RST_DDR_SS_DDR_RESET                            0X1

    * DDR sub system block level reset
    * (OFFSET, MASK, VALUE)      (0XFD1A0108, 0x00000008U ,0x00000008U)
    */
	PSU_Mask_Write(CRF_APB_RST_DDR_SS_OFFSET, 0x00000008U, 0x00000008U);
/*##################################################################### */

    /*
    * Register : MSTR @ 0XFD070000

    * Indicates the configuration of the device used in the system. - 00 - x4
    * device - 01 - x8 device - 10 - x16 device - 11 - x32 device
    *  PSU_DDRC_MSTR_DEVICE_CONFIG                                 0x1

    * Choose which registers are used. - 0 - Original registers - 1 - Shadow r
    * egisters
    *  PSU_DDRC_MSTR_FREQUENCY_MODE                                0x0

    * Only present for multi-rank configurations. Each bit represents one rank
    * . For two-rank configurations, only bits[25:24] are present. - 1 - popul
    * ated - 0 - unpopulated LSB is the lowest rank number. For 2 ranks follow
    * ing combinations are legal: - 01 - One rank - 11 - Two ranks - Others -
    * Reserved. For 4 ranks following combinations are legal: - 0001 - One ran
    * k - 0011 - Two ranks - 1111 - Four ranks
    *  PSU_DDRC_MSTR_ACTIVE_RANKS                                  0x1

    * SDRAM burst length used: - 0001 - Burst length of 2 (only supported for
    * mDDR) - 0010 - Burst length of 4 - 0100 - Burst length of 8 - 1000 - Bur
    * st length of 16 (only supported for mDDR, LPDDR2, and LPDDR4) All other
    * values are reserved. This controls the burst size used to access the SDR
    * AM. This must match the burst length mode register setting in the SDRAM.
    *  (For BC4/8 on-the-fly mode of DDR3 and DDR4, set this field to 0x0100)
    * Burst length of 2 is not supported with AXI ports when MEMC_BURST_LENGTH
    *  is 8. Burst length of 2 is only supported with MEMC_FREQ_RATIO = 1
    *  PSU_DDRC_MSTR_BURST_RDWR                                    0x4

    * Set to 1 when the uMCTL2 and DRAM has to be put in DLL-off mode for low
    * frequency operation. Set to 0 to put uMCTL2 and DRAM in DLL-on mode for
    * normal frequency operation. If DDR4 CRC/parity retry is enabled (CRCPARC
    * TL1.crc_parity_retry_enable = 1), dll_off_mode is not supported, and thi
    * s bit must be set to '0'.
    *  PSU_DDRC_MSTR_DLL_OFF_MODE                                  0x0

    * Selects proportion of DQ bus width that is used by the SDRAM - 00 - Full
    *  DQ bus width to SDRAM - 01 - Half DQ bus width to SDRAM - 10 - Quarter
    * DQ bus width to SDRAM - 11 - Reserved. Note that half bus width mode is
    * only supported when the SDRAM bus width is a multiple of 16, and quarter
    *  bus width mode is only supported when the SDRAM bus width is a multiple
    *  of 32 and the configuration parameter MEMC_QBUS_SUPPORT is set. Bus wid
    * th refers to DQ bus width (excluding any ECC width).
    *  PSU_DDRC_MSTR_DATA_BUS_WIDTH                                0x0

    * 1 indicates put the DRAM in geardown mode (2N) and 0 indicates put the D
    * RAM in normal mode (1N). This register can be changed, only when the Con
    * troller is in self-refresh mode. This signal must be set the same value
    * as MR3 bit A3. Note: Geardown mode is not supported if the configuration
    *  parameter MEMC_CMD_RTN2IDLE is set
    *  PSU_DDRC_MSTR_GEARDOWN_MODE                                 0x0

    * If 1, then uMCTL2 uses 2T timing. Otherwise, uses 1T timing. In 2T timin
    * g, all command signals (except chip select) are held for 2 clocks on the
    *  SDRAM bus. Chip select is asserted on the second cycle of the command N
    * ote: 2T timing is not supported in LPDDR2/LPDDR3/LPDDR4 mode Note: 2T ti
    * ming is not supported if the configuration parameter MEMC_CMD_RTN2IDLE i
    * s set Note: 2T timing is not supported in DDR4 geardown mode.
    *  PSU_DDRC_MSTR_EN_2T_TIMING_MODE                             0x0

    * When set, enable burst-chop in DDR3/DDR4. Burst Chop for Reads is exerci
    * sed only in HIF configurations (UMCTL2_INCL_ARB not set) and if in full
    * bus width mode (MSTR.data_bus_width = 00). Burst Chop for Writes is exer
    * cised only if Partial Writes enabled (UMCTL2_PARTIAL_WR=1) and if CRC is
    *  disabled (CRCPARCTL1.crc_enable = 0). If DDR4 CRC/parity retry is enabl
    * ed (CRCPARCTL1.crc_parity_retry_enable = 1), burst chop is not supported
    * , and this bit must be set to '0'
    *  PSU_DDRC_MSTR_BURSTCHOP                                     0x0

    * Select LPDDR4 SDRAM - 1 - LPDDR4 SDRAM device in use. - 0 - non-LPDDR4 d
    * evice in use Present only in designs configured to support LPDDR4.
    *  PSU_DDRC_MSTR_LPDDR4                                        0x0

    * Select DDR4 SDRAM - 1 - DDR4 SDRAM device in use. - 0 - non-DDR4 device
    * in use Present only in designs configured to support DDR4.
    *  PSU_DDRC_MSTR_DDR4                                          0x1

    * Select LPDDR3 SDRAM - 1 - LPDDR3 SDRAM device in use. - 0 - non-LPDDR3 d
    * evice in use Present only in designs configured to support LPDDR3.
    *  PSU_DDRC_MSTR_LPDDR3                                        0x0

    * Select LPDDR2 SDRAM - 1 - LPDDR2 SDRAM device in use. - 0 - non-LPDDR2 d
    * evice in use Present only in designs configured to support LPDDR2.
    *  PSU_DDRC_MSTR_LPDDR2                                        0x0

    * Select DDR3 SDRAM - 1 - DDR3 SDRAM device in use - 0 - non-DDR3 SDRAM de
    * vice in use Only present in designs that support DDR3.
    *  PSU_DDRC_MSTR_DDR3                                          0x0

    * Master Register
    * (OFFSET, MASK, VALUE)      (0XFD070000, 0xE30FBE3DU ,0x41040010U)
    */
	PSU_Mask_Write(DDRC_MSTR_OFFSET, 0xE30FBE3DU, 0x41040010U);
/*##################################################################### */

    /*
    * Register : MRCTRL0 @ 0XFD070010

    * Setting this register bit to 1 triggers a mode register read or write op
    * eration. When the MR operation is complete, the uMCTL2 automatically cle
    * ars this bit. The other register fields of this register must be written
    *  in a separate APB transaction, before setting this mr_wr bit. It is rec
    * ommended NOT to set this signal if in Init, Deep power-down or MPSM oper
    * ating modes.
    *  PSU_DDRC_MRCTRL0_MR_WR                                      0x0

    * Address of the mode register that is to be written to. - 0000 - MR0 - 00
    * 01 - MR1 - 0010 - MR2 - 0011 - MR3 - 0100 - MR4 - 0101 - MR5 - 0110 - MR
    * 6 - 0111 - MR7 Don't Care for LPDDR2/LPDDR3/LPDDR4 (see MRCTRL1.mr_data
    * for mode register addressing in LPDDR2/LPDDR3/LPDDR4) This signal is als
    * o used for writing to control words of RDIMMs. In that case, it correspo
    * nds to the bank address bits sent to the RDIMM In case of DDR4, the bit[
    * 3:2] corresponds to the bank group bits. Therefore, the bit[3] as well a
    * s the bit[2:0] must be set to an appropriate value which is considered b
    * oth the Address Mirroring of UDIMMs/RDIMMs and the Output Inversion of R
    * DIMMs.
    *  PSU_DDRC_MRCTRL0_MR_ADDR                                    0x0

    * Controls which rank is accessed by MRCTRL0.mr_wr. Normally, it is desire
    * d to access all ranks, so all bits should be set to 1. However, for mult
    * i-rank UDIMMs/RDIMMs which implement address mirroring, it may be necess
    * ary to access ranks individually. Examples (assume uMCTL2 is configured
    * for 4 ranks): - 0x1 - select rank 0 only - 0x2 - select rank 1 only - 0x
    * 5 - select ranks 0 and 2 - 0xA - select ranks 1 and 3 - 0xF - select ran
    * ks 0, 1, 2 and 3
    *  PSU_DDRC_MRCTRL0_MR_RANK                                    0x3

    * Indicates whether Software intervention is allowed via MRCTRL0/MRCTRL1 b
    * efore automatic SDRAM initialization routine or not. For DDR4, this bit
    * can be used to initialize the DDR4 RCD (MR7) before automatic SDRAM init
    * ialization. For LPDDR4, this bit can be used to program additional mode
    * registers before automatic SDRAM initialization if necessary. Note: This
    *  must be cleared to 0 after completing Software operation. Otherwise, SD
    * RAM initialization routine will not re-start. - 0 - Software interventio
    * n is not allowed - 1 - Software intervention is allowed
    *  PSU_DDRC_MRCTRL0_SW_INIT_INT                                0x0

    * Indicates whether the mode register operation is MRS in PDA mode or not
    * - 0 - MRS - 1 - MRS in Per DRAM Addressability mode
    *  PSU_DDRC_MRCTRL0_PDA_EN                                     0x0

    * Indicates whether the mode register operation is MRS or WR/RD for MPR (o
    * nly supported for DDR4) - 0 - MRS - 1 - WR/RD for MPR
    *  PSU_DDRC_MRCTRL0_MPR_EN                                     0x0

    * Indicates whether the mode register operation is read or write. Only use
    * d for LPDDR2/LPDDR3/LPDDR4/DDR4. - 0 - Write - 1 - Read
    *  PSU_DDRC_MRCTRL0_MR_TYPE                                    0x0

    * Mode Register Read/Write Control Register 0. Note: Do not enable more th
    * an one of the following fields simultaneously: - sw_init_int - pda_en -
    * mpr_en
    * (OFFSET, MASK, VALUE)      (0XFD070010, 0x8000F03FU ,0x00000030U)
    */
	PSU_Mask_Write(DDRC_MRCTRL0_OFFSET, 0x8000F03FU, 0x00000030U);
/*##################################################################### */

    /*
    * Register : DERATEEN @ 0XFD070020

    * Derate value of tRC for LPDDR4 - 0 - Derating uses +1. - 1 - Derating us
    * es +2. - 2 - Derating uses +3. - 3 - Derating uses +4. Present only in d
    * esigns configured to support LPDDR4. The required number of cycles for d
    * erating can be determined by dividing 3.75ns by the core_ddrc_core_clk p
    * eriod, and rounding up the next integer.
    *  PSU_DDRC_DERATEEN_RC_DERATE_VALUE                           0x2

    * Derate byte Present only in designs configured to support LPDDR2/LPDDR3/
    * LPDDR4 Indicates which byte of the MRR data is used for derating. The ma
    * ximum valid value depends on MEMC_DRAM_TOTAL_DATA_WIDTH.
    *  PSU_DDRC_DERATEEN_DERATE_BYTE                               0x0

    * Derate value - 0 - Derating uses +1. - 1 - Derating uses +2. Present onl
    * y in designs configured to support LPDDR2/LPDDR3/LPDDR4 Set to 0 for all
    *  LPDDR2 speed grades as derating value of +1.875 ns is less than a core_
    * ddrc_core_clk period. Can be 0 or 1 for LPDDR3/LPDDR4, depending if +1.8
    * 75 ns is less than a core_ddrc_core_clk period or not.
    *  PSU_DDRC_DERATEEN_DERATE_VALUE                              0x0

    * Enables derating - 0 - Timing parameter derating is disabled - 1 - Timin
    * g parameter derating is enabled using MR4 read value. Present only in de
    * signs configured to support LPDDR2/LPDDR3/LPDDR4 This field must be set
    * to '0' for non-LPDDR2/LPDDR3/LPDDR4 mode.
    *  PSU_DDRC_DERATEEN_DERATE_ENABLE                             0x0

    * Temperature Derate Enable Register
    * (OFFSET, MASK, VALUE)      (0XFD070020, 0x000003F3U ,0x00000200U)
    */
	PSU_Mask_Write(DDRC_DERATEEN_OFFSET, 0x000003F3U, 0x00000200U);
/*##################################################################### */

    /*
    * Register : DERATEINT @ 0XFD070024

    * Interval between two MR4 reads, used to derate the timing parameters. Pr
    * esent only in designs configured to support LPDDR2/LPDDR3/LPDDR4. This r
    * egister must not be set to zero
    *  PSU_DDRC_DERATEINT_MR4_READ_INTERVAL                        0x800000

    * Temperature Derate Interval Register
    * (OFFSET, MASK, VALUE)      (0XFD070024, 0xFFFFFFFFU ,0x00800000U)
    */
	PSU_Mask_Write(DDRC_DERATEINT_OFFSET, 0xFFFFFFFFU, 0x00800000U);
/*##################################################################### */

    /*
    * Register : PWRCTL @ 0XFD070030

    * Self refresh state is an intermediate state to enter to Self refresh pow
    * er down state or exit Self refresh power down state for LPDDR4. This reg
    * ister controls transition from the Self refresh state. - 1 - Prohibit tr
    * ansition from Self refresh state - 0 - Allow transition from Self refres
    * h state
    *  PSU_DDRC_PWRCTL_STAY_IN_SELFREF                             0x0

    * A value of 1 to this register causes system to move to Self Refresh stat
    * e immediately, as long as it is not in INIT or DPD/MPSM operating_mode.
    * This is referred to as Software Entry/Exit to Self Refresh. - 1 - Softwa
    * re Entry to Self Refresh - 0 - Software Exit from Self Refresh
    *  PSU_DDRC_PWRCTL_SELFREF_SW                                  0x0

    * When this is 1, the uMCTL2 puts the SDRAM into maximum power saving mode
    *  when the transaction store is empty. This register must be reset to '0'
    *  to bring uMCTL2 out of maximum power saving mode. Present only in desig
    * ns configured to support DDR4. For non-DDR4, this register should not be
    *  set to 1. Note that MPSM is not supported when using a DWC DDR PHY, if
    * the PHY parameter DWC_AC_CS_USE is disabled, as the MPSM exit sequence r
    * equires the chip-select signal to toggle. FOR PERFORMANCE ONLY.
    *  PSU_DDRC_PWRCTL_MPSM_EN                                     0x0

    * Enable the assertion of dfi_dram_clk_disable whenever a clock is not req
    * uired by the SDRAM. If set to 0, dfi_dram_clk_disable is never asserted.
    *  Assertion of dfi_dram_clk_disable is as follows: In DDR2/DDR3, can only
    *  be asserted in Self Refresh. In DDR4, can be asserted in following: - i
    * n Self Refresh. - in Maximum Power Saving Mode In mDDR/LPDDR2/LPDDR3, ca
    * n be asserted in following: - in Self Refresh - in Power Down - in Deep
    * Power Down - during Normal operation (Clock Stop) In LPDDR4, can be asse
    * rted in following: - in Self Refresh Power Down - in Power Down - during
    *  Normal operation (Clock Stop)
    *  PSU_DDRC_PWRCTL_EN_DFI_DRAM_CLK_DISABLE                     0x0

    * When this is 1, uMCTL2 puts the SDRAM into deep power-down mode when the
    *  transaction store is empty. This register must be reset to '0' to bring
    *  uMCTL2 out of deep power-down mode. Controller performs automatic SDRAM
    *  initialization on deep power-down exit. Present only in designs configu
    * red to support mDDR or LPDDR2 or LPDDR3. For non-mDDR/non-LPDDR2/non-LPD
    * DR3, this register should not be set to 1. FOR PERFORMANCE ONLY.
    *  PSU_DDRC_PWRCTL_DEEPPOWERDOWN_EN                            0x0

    * If true then the uMCTL2 goes into power-down after a programmable number
    *  of cycles 'maximum idle clocks before power down' (PWRTMG.powerdown_to_
    * x32). This register bit may be re-programmed during the course of normal
    *  operation.
    *  PSU_DDRC_PWRCTL_POWERDOWN_EN                                0x0

    * If true then the uMCTL2 puts the SDRAM into Self Refresh after a program
    * mable number of cycles 'maximum idle clocks before Self Refresh (PWRTMG.
    * selfref_to_x32)'. This register bit may be re-programmed during the cour
    * se of normal operation.
    *  PSU_DDRC_PWRCTL_SELFREF_EN                                  0x0

    * Low Power Control Register
    * (OFFSET, MASK, VALUE)      (0XFD070030, 0x0000007FU ,0x00000000U)
    */
	PSU_Mask_Write(DDRC_PWRCTL_OFFSET, 0x0000007FU, 0x00000000U);
/*##################################################################### */

    /*
    * Register : PWRTMG @ 0XFD070034

    * After this many clocks of NOP or deselect the uMCTL2 automatically puts
    * the SDRAM into Self Refresh. This must be enabled in the PWRCTL.selfref_
    * en. Unit: Multiples of 32 clocks. FOR PERFORMANCE ONLY.
    *  PSU_DDRC_PWRTMG_SELFREF_TO_X32                              0x40

    * Minimum deep power-down time. For mDDR, value from the JEDEC specificati
    * on is 0 as mDDR exits from deep power-down mode immediately after PWRCTL
    * .deeppowerdown_en is de-asserted. For LPDDR2/LPDDR3, value from the JEDE
    * C specification is 500us. Unit: Multiples of 4096 clocks. Present only i
    * n designs configured to support mDDR, LPDDR2 or LPDDR3. FOR PERFORMANCE
    * ONLY.
    *  PSU_DDRC_PWRTMG_T_DPD_X4096                                 0x84

    * After this many clocks of NOP or deselect the uMCTL2 automatically puts
    * the SDRAM into power-down. This must be enabled in the PWRCTL.powerdown_
    * en. Unit: Multiples of 32 clocks FOR PERFORMANCE ONLY.
    *  PSU_DDRC_PWRTMG_POWERDOWN_TO_X32                            0x10

    * Low Power Timing Register
    * (OFFSET, MASK, VALUE)      (0XFD070034, 0x00FFFF1FU ,0x00408410U)
    */
	PSU_Mask_Write(DDRC_PWRTMG_OFFSET, 0x00FFFF1FU, 0x00408410U);
/*##################################################################### */

    /*
    * Register : RFSHCTL0 @ 0XFD070050

    * Threshold value in number of clock cycles before the critical refresh or
    *  page timer expires. A critical refresh is to be issued before this thre
    * shold is reached. It is recommended that this not be changed from the de
    * fault value, currently shown as 0x2. It must always be less than interna
    * lly used t_rfc_nom_x32. Note that, in LPDDR2/LPDDR3/LPDDR4, internally u
    * sed t_rfc_nom_x32 may be equal to RFSHTMG.t_rfc_nom_x32>>2 if derating i
    * s enabled (DERATEEN.derate_enable=1). Otherwise, internally used t_rfc_n
    * om_x32 will be equal to RFSHTMG.t_rfc_nom_x32. Unit: Multiples of 32 clo
    * cks.
    *  PSU_DDRC_RFSHCTL0_REFRESH_MARGIN                            0x2

    * If the refresh timer (tRFCnom, also known as tREFI) has expired at least
    *  once, but it has not expired (RFSHCTL0.refresh_burst+1) times yet, then
    *  a speculative refresh may be performed. A speculative refresh is a refr
    * esh performed at a time when refresh would be useful, but before it is a
    * bsolutely required. When the SDRAM bus is idle for a period of time dete
    * rmined by this RFSHCTL0.refresh_to_x32 and the refresh timer has expired
    *  at least once since the last refresh, then a speculative refresh is per
    * formed. Speculative refreshes continues successively until there are no
    * refreshes pending or until new reads or writes are issued to the uMCTL2.
    *  FOR PERFORMANCE ONLY.
    *  PSU_DDRC_RFSHCTL0_REFRESH_TO_X32                            0x10

    * The programmed value + 1 is the number of refresh timeouts that is allow
    * ed to accumulate before traffic is blocked and the refreshes are forced
    * to execute. Closing pages to perform a refresh is a one-time penalty tha
    * t must be paid for each group of refreshes. Therefore, performing refres
    * hes in a burst reduces the per-refresh penalty of these page closings. H
    * igher numbers for RFSHCTL.refresh_burst slightly increases utilization;
    * lower numbers decreases the worst-case latency associated with refreshes
    * . - 0 - single refresh - 1 - burst-of-2 refresh - 7 - burst-of-8 refresh
    *  For information on burst refresh feature refer to section 3.9 of DDR2 J
    * EDEC specification - JESD79-2F.pdf. For DDR2/3, the refresh is always pe
    * r-rank and not per-bank. The rank refresh can be accumulated over 8*tREF
    * I cycles using the burst refresh feature. In DDR4 mode, according to Fin
    * e Granularity feature, 8 refreshes can be postponed in 1X mode, 16 refre
    * shes in 2X mode and 32 refreshes in 4X mode. If using PHY-initiated upda
    * tes, care must be taken in the setting of RFSHCTL0.refresh_burst, to ens
    * ure that tRFCmax is not violated due to a PHY-initiated update occurring
    *  shortly before a refresh burst was due. In this situation, the refresh
    * burst will be delayed until the PHY-initiated update is complete.
    *  PSU_DDRC_RFSHCTL0_REFRESH_BURST                             0x0

    * - 1 - Per bank refresh; - 0 - All bank refresh. Per bank refresh allows
    * traffic to flow to other banks. Per bank refresh is not supported by all
    *  LPDDR2 devices but should be supported by all LPDDR3/LPDDR4 devices. Pr
    * esent only in designs configured to support LPDDR2/LPDDR3/LPDDR4
    *  PSU_DDRC_RFSHCTL0_PER_BANK_REFRESH                          0x0

    * Refresh Control Register 0
    * (OFFSET, MASK, VALUE)      (0XFD070050, 0x00F1F1F4U ,0x00210000U)
    */
	PSU_Mask_Write(DDRC_RFSHCTL0_OFFSET, 0x00F1F1F4U, 0x00210000U);
/*##################################################################### */

    /*
    * Register : RFSHCTL1 @ 0XFD070054

    * Refresh timer start for rank 1 (only present in multi-rank configuration
    * s). This is useful in staggering the refreshes to multiple ranks to help
    *  traffic to proceed. This is explained in Refresh Controls section of ar
    * chitecture chapter. Unit: Multiples of 32 clocks. FOR PERFORMANCE ONLY.
    *  PSU_DDRC_RFSHCTL1_REFRESH_TIMER1_START_VALUE_X32            0x0

    * Refresh timer start for rank 0 (only present in multi-rank configuration
    * s). This is useful in staggering the refreshes to multiple ranks to help
    *  traffic to proceed. This is explained in Refresh Controls section of ar
    * chitecture chapter. Unit: Multiples of 32 clocks. FOR PERFORMANCE ONLY.
    *  PSU_DDRC_RFSHCTL1_REFRESH_TIMER0_START_VALUE_X32            0x0

    * Refresh Control Register 1
    * (OFFSET, MASK, VALUE)      (0XFD070054, 0x0FFF0FFFU ,0x00000000U)
    */
	PSU_Mask_Write(DDRC_RFSHCTL1_OFFSET, 0x0FFF0FFFU, 0x00000000U);
/*##################################################################### */

    /*
    * Register : RFSHCTL3 @ 0XFD070060

    * Fine Granularity Refresh Mode - 000 - Fixed 1x (Normal mode) - 001 - Fix
    * ed 2x - 010 - Fixed 4x - 101 - Enable on the fly 2x (not supported) - 11
    * 0 - Enable on the fly 4x (not supported) - Everything else - reserved No
    * te: The on-the-fly modes is not supported in this version of the uMCTL2.
    *  Note: This must be set up while the Controller is in reset or while the
    *  Controller is in self-refresh mode. Changing this during normal operati
    * on is not allowed. Making this a dynamic register will be supported in f
    * uture version of the uMCTL2.
    *  PSU_DDRC_RFSHCTL3_REFRESH_MODE                              0x0

    * Toggle this signal (either from 0 to 1 or from 1 to 0) to indicate that
    * the refresh register(s) have been updated. The value is automatically up
    * dated when exiting reset, so it does not need to be toggled initially.
    *  PSU_DDRC_RFSHCTL3_REFRESH_UPDATE_LEVEL                      0x0

    * When '1', disable auto-refresh generated by the uMCTL2. When auto-refres
    * h is disabled, the SoC core must generate refreshes using the registers
    * reg_ddrc_rank0_refresh, reg_ddrc_rank1_refresh, reg_ddrc_rank2_refresh a
    * nd reg_ddrc_rank3_refresh. When dis_auto_refresh transitions from 0 to 1
    * , any pending refreshes are immediately scheduled by the uMCTL2. If DDR4
    *  CRC/parity retry is enabled (CRCPARCTL1.crc_parity_retry_enable = 1), d
    * isable auto-refresh is not supported, and this bit must be set to '0'. T
    * his register field is changeable on the fly.
    *  PSU_DDRC_RFSHCTL3_DIS_AUTO_REFRESH                          0x1

    * Refresh Control Register 3
    * (OFFSET, MASK, VALUE)      (0XFD070060, 0x00000073U ,0x00000001U)
    */
	PSU_Mask_Write(DDRC_RFSHCTL3_OFFSET, 0x00000073U, 0x00000001U);
/*##################################################################### */

    /*
    * Register : RFSHTMG @ 0XFD070064

    * tREFI: Average time interval between refreshes per rank (Specification:
    * 7.8us for DDR2, DDR3 and DDR4. See JEDEC specification for mDDR, LPDDR2,
    *  LPDDR3 and LPDDR4). For LPDDR2/LPDDR3/LPDDR4: - if using all-bank refre
    * shes (RFSHCTL0.per_bank_refresh = 0), this register should be set to tRE
    * FIab - if using per-bank refreshes (RFSHCTL0.per_bank_refresh = 1), this
    *  register should be set to tREFIpb For configurations with MEMC_FREQ_RAT
    * IO=2, program this to (tREFI/2), no rounding up. In DDR4 mode, tREFI val
    * ue is different depending on the refresh mode. The user should program t
    * he appropriate value from the spec based on the value programmed in the
    * refresh mode register. Note that RFSHTMG.t_rfc_nom_x32 * 32 must be grea
    * ter than RFSHTMG.t_rfc_min, and RFSHTMG.t_rfc_nom_x32 must be greater th
    * an 0x1. Unit: Multiples of 32 clocks.
    *  PSU_DDRC_RFSHTMG_T_RFC_NOM_X32                              0x81

    * Used only when LPDDR3 memory type is connected. Should only be changed w
    * hen uMCTL2 is in reset. Specifies whether to use the tREFBW parameter (r
    * equired by some LPDDR3 devices which comply with earlier versions of the
    *  LPDDR3 JEDEC specification) or not: - 0 - tREFBW parameter not used - 1
    *  - tREFBW parameter used
    *  PSU_DDRC_RFSHTMG_LPDDR3_TREFBW_EN                           0x1

    * tRFC (min): Minimum time from refresh to refresh or activate. For MEMC_F
    * REQ_RATIO=1 configurations, t_rfc_min should be set to RoundUp(tRFCmin/t
    * CK). For MEMC_FREQ_RATIO=2 configurations, t_rfc_min should be set to Ro
    * undUp(RoundUp(tRFCmin/tCK)/2). In LPDDR2/LPDDR3/LPDDR4 mode: - if using
    * all-bank refreshes, the tRFCmin value in the above equations is equal to
    *  tRFCab - if using per-bank refreshes, the tRFCmin value in the above eq
    * uations is equal to tRFCpb In DDR4 mode, the tRFCmin value in the above
    * equations is different depending on the refresh mode (fixed 1X,2X,4X) an
    * d the device density. The user should program the appropriate value from
    *  the spec based on the 'refresh_mode' and the device density that is use
    * d. Unit: Clocks.
    *  PSU_DDRC_RFSHTMG_T_RFC_MIN                                  0x8b

    * Refresh Timing Register
    * (OFFSET, MASK, VALUE)      (0XFD070064, 0x0FFF83FFU ,0x0081808BU)
    */
	PSU_Mask_Write(DDRC_RFSHTMG_OFFSET, 0x0FFF83FFU, 0x0081808BU);
/*##################################################################### */

    /*
    * Register : ECCCFG0 @ 0XFD070070

    * Disable ECC scrubs. Valid only when ECCCFG0.ecc_mode = 3'b100 and MEMC_U
    * SE_RMW is defined
    *  PSU_DDRC_ECCCFG0_DIS_SCRUB                                  0x1

    * ECC mode indicator - 000 - ECC disabled - 100 - ECC enabled - SEC/DED ov
    * er 1 beat - all other settings are reserved for future use
    *  PSU_DDRC_ECCCFG0_ECC_MODE                                   0x0

    * ECC Configuration Register 0
    * (OFFSET, MASK, VALUE)      (0XFD070070, 0x00000017U ,0x00000010U)
    */
	PSU_Mask_Write(DDRC_ECCCFG0_OFFSET, 0x00000017U, 0x00000010U);
/*##################################################################### */

    /*
    * Register : ECCCFG1 @ 0XFD070074

    * Selects whether to poison 1 or 2 bits - if 0 -> 2-bit (uncorrectable) da
    * ta poisoning, if 1 -> 1-bit (correctable) data poisoning, if ECCCFG1.dat
    * a_poison_en=1
    *  PSU_DDRC_ECCCFG1_DATA_POISON_BIT                            0x0

    * Enable ECC data poisoning - introduces ECC errors on writes to address s
    * pecified by the ECCPOISONADDR0/1 registers
    *  PSU_DDRC_ECCCFG1_DATA_POISON_EN                             0x0

    * ECC Configuration Register 1
    * (OFFSET, MASK, VALUE)      (0XFD070074, 0x00000003U ,0x00000000U)
    */
	PSU_Mask_Write(DDRC_ECCCFG1_OFFSET, 0x00000003U, 0x00000000U);
/*##################################################################### */

    /*
    * Register : CRCPARCTL1 @ 0XFD0700C4

    * The maximum number of DFI PHY clock cycles allowed from the assertion of
    *  the dfi_rddata_en signal to the assertion of each of the corresponding
    * bits of the dfi_rddata_valid signal. This corresponds to the DFI timing
    * parameter tphy_rdlat. Refer to PHY specification for correct value. This
    *  value it only used for detecting read data timeout when DDR4 retry is e
    * nabled by CRCPARCTL1.crc_parity_retry_enable=1. Maximum supported value:
    *  - 1:1 Frequency mode : DFITMG0.dfi_t_rddata_en + CRCPARCTL1.dfi_t_phy_r
    * dlat < 'd114 - 1:2 Frequency mode ANDAND DFITMG0.dfi_rddata_use_sdr == 1
    *  : CRCPARCTL1.dfi_t_phy_rdlat < 64 - 1:2 Frequency mode ANDAND DFITMG0.d
    * fi_rddata_use_sdr == 0 : DFITMG0.dfi_t_rddata_en + CRCPARCTL1.dfi_t_phy_
    * rdlat < 'd114 Unit: DFI Clocks
    *  PSU_DDRC_CRCPARCTL1_DFI_T_PHY_RDLAT                         0x10

    * After a Parity or CRC error is flagged on dfi_alert_n signal, the softwa
    * re has an option to read the mode registers in the DRAM before the hardw
    * are begins the retry process - 1: Wait for software to read/write the mo
    * de registers before hardware begins the retry. After software is done wi
    * th its operations, it will clear the alert interrupt register bit - 0: H
    * ardware can begin the retry right away after the dfi_alert_n pulse goes
    * away. The value on this register is valid only when retry is enabled (PA
    * RCTRL.crc_parity_retry_enable = 1) If this register is set to 1 and if t
    * he software doesn't clear the interrupt register after handling the pari
    * ty/CRC error, then the hardware will not begin the retry process and the
    *  system will hang. In the case of Parity/CRC error, there are two possib
    * ilities when the software doesn't reset MR5[4] to 0. - (i) If 'Persisten
    * t parity' mode register bit is NOT set: the commands sent during retry a
    * nd normal operation are executed without parity checking. The value in t
    * he Parity error log register MPR Page 1 is valid. - (ii) If 'Persistent
    * parity' mode register bit is SET: Parity checking is done for commands s
    * ent during retry and normal operation. If multiple errors occur before M
    * R5[4] is cleared, the error log in MPR Page 1 should be treated as 'Don'
    * t care'.
    *  PSU_DDRC_CRCPARCTL1_ALERT_WAIT_FOR_SW                       0x1

    * - 1: Enable command retry mechanism in case of C/A Parity or CRC error -
    *  0: Disable command retry mechanism when C/A Parity or CRC features are
    * enabled. Note that retry functionality is not supported if burst chop is
    *  enabled (MSTR.burstchop = 1) and/or disable auto-refresh is enabled (RF
    * SHCTL3.dis_auto_refresh = 1)
    *  PSU_DDRC_CRCPARCTL1_CRC_PARITY_RETRY_ENABLE                 0x0

    * CRC Calculation setting register - 1: CRC includes DM signal - 0: CRC no
    * t includes DM signal Present only in designs configured to support DDR4.
    *  PSU_DDRC_CRCPARCTL1_CRC_INC_DM                              0x0

    * CRC enable Register - 1: Enable generation of CRC - 0: Disable generatio
    * n of CRC The setting of this register should match the CRC mode register
    *  setting in the DRAM.
    *  PSU_DDRC_CRCPARCTL1_CRC_ENABLE                              0x0

    * C/A Parity enable register - 1: Enable generation of C/A parity and dete
    * ction of C/A parity error - 0: Disable generation of C/A parity and disa
    * ble detection of C/A parity error If RCD's parity error detection or SDR
    * AM's parity detection is enabled, this register should be 1.
    *  PSU_DDRC_CRCPARCTL1_PARITY_ENABLE                           0x0

    * CRC Parity Control Register1
    * (OFFSET, MASK, VALUE)      (0XFD0700C4, 0x3F000391U ,0x10000200U)
    */
	PSU_Mask_Write(DDRC_CRCPARCTL1_OFFSET, 0x3F000391U, 0x10000200U);
/*##################################################################### */

    /*
    * Register : CRCPARCTL2 @ 0XFD0700C8

    * Value from the DRAM spec indicating the maximum width of the dfi_alert_n
    *  pulse when a parity error occurs. Recommended values: - tPAR_ALERT_PW.M
    * AX For configurations with MEMC_FREQ_RATIO=2, program this to tPAR_ALERT
    * _PW.MAX/2 and round up to next integer value. Values of 0, 1 and 2 are i
    * llegal. This value must be greater than CRCPARCTL2.t_crc_alert_pw_max.
    *  PSU_DDRC_CRCPARCTL2_T_PAR_ALERT_PW_MAX                      0x40

    * Value from the DRAM spec indicating the maximum width of the dfi_alert_n
    *  pulse when a CRC error occurs. Recommended values: - tCRC_ALERT_PW.MAX
    * For configurations with MEMC_FREQ_RATIO=2, program this to tCRC_ALERT_PW
    * .MAX/2 and round up to next integer value. Values of 0, 1 and 2 are ille
    * gal. This value must be less than CRCPARCTL2.t_par_alert_pw_max.
    *  PSU_DDRC_CRCPARCTL2_T_CRC_ALERT_PW_MAX                      0x5

    * Indicates the maximum duration in number of DRAM clock cycles for which
    * a command should be held in the Command Retry FIFO before it is popped o
    * ut. Every location in the Command Retry FIFO has an associated down coun
    * ting timer that will use this register as the start value. The down coun
    * ting starts when a command is loaded into the FIFO. The timer counts dow
    * n every 4 DRAM cycles. When the counter reaches zero, the entry is poppe
    * d from the FIFO. All the counters are frozen, if a C/A Parity or CRC err
    * or occurs before the counter reaches zero. The counter is reset to 0, af
    * ter all the commands in the FIFO are retried. Recommended(minimum) value
    * s: - Only C/A Parity is enabled. RoundUp((PHY Command Latency(DRAM CLK)
    * + CAL + RDIMM delay + tPAR_ALERT_ON.max + tPAR_UNKNOWN + PHY Alert Laten
    * cy(DRAM CLK) + board delay) / 4) + 2 - Both C/A Parity and CRC is enable
    * d/ Only CRC is enabled. RoundUp((PHY Command Latency(DRAM CLK) + CAL + R
    * DIMM delay + WL + 5(BL10)+ tCRC_ALERT.max + PHY Alert Latency(DRAM CLK)
    * + board delay) / 4) + 2 Note 1: All value (e.g. tPAR_ALERT_ON) should be
    *  in terms of DRAM Clock and round up Note 2: Board delay(Command/Alert_n
    * ) should be considered. Note 3: Use the worst case(longer) value for PHY
    *  Latencies/Board delay Note 4: The Recommended values are minimum value
    * to be set. For mode detail, See 'Calculation of FIFO Depth' section. Max
    *  value can be set to this register is defined below: - MEMC_BURST_LENGTH
    *  == 16 Full bus Mode (CRC=OFF) Max value = UMCTL2_RETRY_CMD_FIFO_DEPTH-2
    *  Full bus Mode (CRC=ON) Max value = UMCTL2_RETRY_CMD_FIFO_DEPTH-3 Half b
    * us Mode (CRC=OFF) Max value = UMCTL2_RETRY_CMD_FIFO_DEPTH-4 Half bus Mod
    * e (CRC=ON) Max value = UMCTL2_RETRY_CMD_FIFO_DEPTH-6 Quarter bus Mode (C
    * RC=OFF) Max value = UMCTL2_RETRY_CMD_FIFO_DEPTH-8 Quarter bus Mode (CRC=
    * ON) Max value = UMCTL2_RETRY_CMD_FIFO_DEPTH-12 - MEMC_BURST_LENGTH != 16
    *  Full bus Mode (CRC=OFF) Max value = UMCTL2_RETRY_CMD_FIFO_DEPTH-1 Full
    * bus Mode (CRC=ON) Max value = UMCTL2_RETRY_CMD_FIFO_DEPTH-2 Half bus Mod
    * e (CRC=OFF) Max value = UMCTL2_RETRY_CMD_FIFO_DEPTH-2 Half bus Mode (CRC
    * =ON) Max value = UMCTL2_RETRY_CMD_FIFO_DEPTH-3 Quarter bus Mode (CRC=OFF
    * ) Max value = UMCTL2_RETRY_CMD_FIFO_DEPTH-4 Quarter bus Mode (CRC=ON) Ma
    * x value = UMCTL2_RETRY_CMD_FIFO_DEPTH-6 Values of 0, 1 and 2 are illegal
    * .
    *  PSU_DDRC_CRCPARCTL2_RETRY_FIFO_MAX_HOLD_TIMER_X4            0x1f

    * CRC Parity Control Register2
    * (OFFSET, MASK, VALUE)      (0XFD0700C8, 0x01FF1F3FU ,0x0040051FU)
    */
	PSU_Mask_Write(DDRC_CRCPARCTL2_OFFSET, 0x01FF1F3FU, 0x0040051FU);
/*##################################################################### */

    /*
    * Register : INIT0 @ 0XFD0700D0

    * If lower bit is enabled the SDRAM initialization routine is skipped. The
    *  upper bit decides what state the controller starts up in when reset is
    * removed - 00 - SDRAM Intialization routine is run after power-up - 01 -
    * SDRAM Intialization routine is skipped after power-up. Controller starts
    *  up in Normal Mode - 11 - SDRAM Intialization routine is skipped after p
    * ower-up. Controller starts up in Self-refresh Mode - 10 - SDRAM Intializ
    * ation routine is run after power-up. Note: The only 2'b00 is supported f
    * or LPDDR4 in this version of the uMCTL2.
    *  PSU_DDRC_INIT0_SKIP_DRAM_INIT                               0x0

    * Cycles to wait after driving CKE high to start the SDRAM initialization
    * sequence. Unit: 1024 clocks. DDR2 typically requires a 400 ns delay, req
    * uiring this value to be programmed to 2 at all clock speeds. LPDDR2/LPDD
    * R3 typically requires this to be programmed for a delay of 200 us. LPDDR
    * 4 typically requires this to be programmed for a delay of 2 us. For conf
    * igurations with MEMC_FREQ_RATIO=2, program this to JEDEC spec value divi
    * ded by 2, and round it up to next integer value.
    *  PSU_DDRC_INIT0_POST_CKE_X1024                               0x2

    * Cycles to wait after reset before driving CKE high to start the SDRAM in
    * itialization sequence. Unit: 1024 clock cycles. DDR2 specifications typi
    * cally require this to be programmed for a delay of >= 200 us. LPDDR2/LPD
    * DR3: tINIT1 of 100 ns (min) LPDDR4: tINIT3 of 2 ms (min) For configurati
    * ons with MEMC_FREQ_RATIO=2, program this to JEDEC spec value divided by
    * 2, and round it up to next integer value.
    *  PSU_DDRC_INIT0_PRE_CKE_X1024                                0x106

    * SDRAM Initialization Register 0
    * (OFFSET, MASK, VALUE)      (0XFD0700D0, 0xC3FF0FFFU ,0x00020106U)
    */
	PSU_Mask_Write(DDRC_INIT0_OFFSET, 0xC3FF0FFFU, 0x00020106U);
/*##################################################################### */

    /*
    * Register : INIT1 @ 0XFD0700D4

    * Number of cycles to assert SDRAM reset signal during init sequence. This
    *  is only present for designs supporting DDR3, DDR4 or LPDDR4 devices. Fo
    * r use with a DDR PHY, this should be set to a minimum of 1
    *  PSU_DDRC_INIT1_DRAM_RSTN_X1024                              0x2

    * Cycles to wait after completing the SDRAM initialization sequence before
    *  starting the dynamic scheduler. Unit: Counts of a global timer that pul
    * ses every 32 clock cycles. There is no known specific requirement for th
    * is; it may be set to zero.
    *  PSU_DDRC_INIT1_FINAL_WAIT_X32                               0x0

    * Wait period before driving the OCD complete command to SDRAM. Unit: Coun
    * ts of a global timer that pulses every 32 clock cycles. There is no know
    * n specific requirement for this; it may be set to zero.
    *  PSU_DDRC_INIT1_PRE_OCD_X32                                  0x0

    * SDRAM Initialization Register 1
    * (OFFSET, MASK, VALUE)      (0XFD0700D4, 0x01FF7F0FU ,0x00020000U)
    */
	PSU_Mask_Write(DDRC_INIT1_OFFSET, 0x01FF7F0FU, 0x00020000U);
/*##################################################################### */

    /*
    * Register : INIT2 @ 0XFD0700D8

    * Idle time after the reset command, tINIT4. Present only in designs confi
    * gured to support LPDDR2. Unit: 32 clock cycles.
    *  PSU_DDRC_INIT2_IDLE_AFTER_RESET_X32                         0x23

    * Time to wait after the first CKE high, tINIT2. Present only in designs c
    * onfigured to support LPDDR2/LPDDR3. Unit: 1 clock cycle. LPDDR2/LPDDR3 t
    * ypically requires 5 x tCK delay.
    *  PSU_DDRC_INIT2_MIN_STABLE_CLOCK_X1                          0x5

    * SDRAM Initialization Register 2
    * (OFFSET, MASK, VALUE)      (0XFD0700D8, 0x0000FF0FU ,0x00002305U)
    */
	PSU_Mask_Write(DDRC_INIT2_OFFSET, 0x0000FF0FU, 0x00002305U);
/*##################################################################### */

    /*
    * Register : INIT3 @ 0XFD0700DC

    * DDR2: Value to write to MR register. Bit 8 is for DLL and the setting he
    * re is ignored. The uMCTL2 sets this bit appropriately. DDR3/DDR4: Value
    * loaded into MR0 register. mDDR: Value to write to MR register. LPDDR2/LP
    * DDR3/LPDDR4 - Value to write to MR1 register
    *  PSU_DDRC_INIT3_MR                                           0x730

    * DDR2: Value to write to EMR register. Bits 9:7 are for OCD and the setti
    * ng in this register is ignored. The uMCTL2 sets those bits appropriately
    * . DDR3/DDR4: Value to write to MR1 register Set bit 7 to 0. If PHY-evalu
    * ation mode training is enabled, this bit is set appropriately by the uMC
    * TL2 during write leveling. mDDR: Value to write to EMR register. LPDDR2/
    * LPDDR3/LPDDR4 - Value to write to MR2 register
    *  PSU_DDRC_INIT3_EMR                                          0x301

    * SDRAM Initialization Register 3
    * (OFFSET, MASK, VALUE)      (0XFD0700DC, 0xFFFFFFFFU ,0x07300301U)
    */
	PSU_Mask_Write(DDRC_INIT3_OFFSET, 0xFFFFFFFFU, 0x07300301U);
/*##################################################################### */

    /*
    * Register : INIT4 @ 0XFD0700E0

    * DDR2: Value to write to EMR2 register. DDR3/DDR4: Value to write to MR2
    * register LPDDR2/LPDDR3/LPDDR4: Value to write to MR3 register mDDR: Unus
    * ed
    *  PSU_DDRC_INIT4_EMR2                                         0x20

    * DDR2: Value to write to EMR3 register. DDR3/DDR4: Value to write to MR3
    * register mDDR/LPDDR2/LPDDR3: Unused LPDDR4: Value to write to MR13 regis
    * ter
    *  PSU_DDRC_INIT4_EMR3                                         0x200

    * SDRAM Initialization Register 4
    * (OFFSET, MASK, VALUE)      (0XFD0700E0, 0xFFFFFFFFU ,0x00200200U)
    */
	PSU_Mask_Write(DDRC_INIT4_OFFSET, 0xFFFFFFFFU, 0x00200200U);
/*##################################################################### */

    /*
    * Register : INIT5 @ 0XFD0700E4

    * ZQ initial calibration, tZQINIT. Present only in designs configured to s
    * upport DDR3 or DDR4 or LPDDR2/LPDDR3. Unit: 32 clock cycles. DDR3 typica
    * lly requires 512 clocks. DDR4 requires 1024 clocks. LPDDR2/LPDDR3 requir
    * es 1 us.
    *  PSU_DDRC_INIT5_DEV_ZQINIT_X32                               0x21

    * Maximum duration of the auto initialization, tINIT5. Present only in des
    * igns configured to support LPDDR2/LPDDR3. LPDDR2/LPDDR3 typically requir
    * es 10 us.
    *  PSU_DDRC_INIT5_MAX_AUTO_INIT_X1024                          0x4

    * SDRAM Initialization Register 5
    * (OFFSET, MASK, VALUE)      (0XFD0700E4, 0x00FF03FFU ,0x00210004U)
    */
	PSU_Mask_Write(DDRC_INIT5_OFFSET, 0x00FF03FFU, 0x00210004U);
/*##################################################################### */

    /*
    * Register : INIT6 @ 0XFD0700E8

    * DDR4- Value to be loaded into SDRAM MR4 registers. Used in DDR4 designs
    * only.
    *  PSU_DDRC_INIT6_MR4                                          0x0

    * DDR4- Value to be loaded into SDRAM MR5 registers. Used in DDR4 designs
    * only.
    *  PSU_DDRC_INIT6_MR5                                          0x6c0

    * SDRAM Initialization Register 6
    * (OFFSET, MASK, VALUE)      (0XFD0700E8, 0xFFFFFFFFU ,0x000006C0U)
    */
	PSU_Mask_Write(DDRC_INIT6_OFFSET, 0xFFFFFFFFU, 0x000006C0U);
/*##################################################################### */

    /*
    * Register : INIT7 @ 0XFD0700EC

    * DDR4- Value to be loaded into SDRAM MR6 registers. Used in DDR4 designs
    * only.
    *  PSU_DDRC_INIT7_MR6                                          0x819

    * SDRAM Initialization Register 7
    * (OFFSET, MASK, VALUE)      (0XFD0700EC, 0xFFFF0000U ,0x08190000U)
    */
	PSU_Mask_Write(DDRC_INIT7_OFFSET, 0xFFFF0000U, 0x08190000U);
/*##################################################################### */

    /*
    * Register : DIMMCTL @ 0XFD0700F0

    * Disabling Address Mirroring for BG bits. When this is set to 1, BG0 and
    * BG1 are NOT swapped even if Address Mirroring is enabled. This will be r
    * equired for DDR4 DIMMs with x16 devices. - 1 - BG0 and BG1 are NOT swapp
    * ed. - 0 - BG0 and BG1 are swapped if address mirroring is enabled.
    *  PSU_DDRC_DIMMCTL_DIMM_DIS_BG_MIRRORING                      0x0

    * Enable for BG1 bit of MRS command. BG1 bit of the mode register address
    * is specified as RFU (Reserved for Future Use) and must be programmed to
    * 0 during MRS. In case where DRAMs which do not have BG1 are attached and
    *  both the CA parity and the Output Inversion are enabled, this must be s
    * et to 0, so that the calculation of CA parity will not include BG1 bit.
    * Note: This has no effect on the address of any other memory accesses, or
    *  of software-driven mode register accesses. If address mirroring is enab
    * led, this is applied to BG1 of even ranks and BG0 of odd ranks. - 1 - En
    * abled - 0 - Disabled
    *  PSU_DDRC_DIMMCTL_MRS_BG1_EN                                 0x1

    * Enable for A17 bit of MRS command. A17 bit of the mode register address
    * is specified as RFU (Reserved for Future Use) and must be programmed to
    * 0 during MRS. In case where DRAMs which do not have A17 are attached and
    *  the Output Inversion are enabled, this must be set to 0, so that the ca
    * lculation of CA parity will not include A17 bit. Note: This has no effec
    * t on the address of any other memory accesses, or of software-driven mod
    * e register accesses. - 1 - Enabled - 0 - Disabled
    *  PSU_DDRC_DIMMCTL_MRS_A17_EN                                 0x0

    * Output Inversion Enable (for DDR4 RDIMM implementations only). DDR4 RDIM
    * M implements the Output Inversion feature by default, which means that t
    * he following address, bank address and bank group bits of B-side DRAMs a
    * re inverted: A3-A9, A11, A13, A17, BA0-BA1, BG0-BG1. Setting this bit en
    * sures that, for mode register accesses generated by the uMCTL2 during th
    * e automatic initialization routine and enabling of a particular DDR4 fea
    * ture, separate A-side and B-side mode register accesses are generated. F
    * or B-side mode register accesses, these bits are inverted within the uMC
    * TL2 to compensate for this RDIMM inversion. Note: This has no effect on
    * the address of any other memory accesses, or of software-driven mode reg
    * ister accesses. - 1 - Implement output inversion for B-side DRAMs. - 0 -
    *  Do not implement output inversion for B-side DRAMs.
    *  PSU_DDRC_DIMMCTL_DIMM_OUTPUT_INV_EN                         0x0

    * Address Mirroring Enable (for multi-rank UDIMM implementations and multi
    * -rank DDR4 RDIMM implementations). Some UDIMMs and DDR4 RDIMMs implement
    *  address mirroring for odd ranks, which means that the following address
    * , bank address and bank group bits are swapped: (A3, A4), (A5, A6), (A7,
    *  A8), (BA0, BA1) and also (A11, A13), (BG0, BG1) for the DDR4. Setting t
    * his bit ensures that, for mode register accesses during the automatic in
    * itialization routine, these bits are swapped within the uMCTL2 to compen
    * sate for this UDIMM/RDIMM swapping. In addition to the automatic initial
    * ization routine, in case of DDR4 UDIMM/RDIMM, they are swapped during th
    * e automatic MRS access to enable/disable of a particular DDR4 feature. N
    * ote: This has no effect on the address of any other memory accesses, or
    * of software-driven mode register accesses. This is not supported for mDD
    * R, LPDDR2, LPDDR3 or LPDDR4 SDRAMs. Note: In case of x16 DDR4 DIMMs, BG1
    *  output of MRS for the odd ranks is same as BG0 because BG1 is invalid,
    * hence dimm_dis_bg_mirroring register must be set to 1. - 1 - For odd ran
    * ks, implement address mirroring for MRS commands to during initializatio
    * n and for any automatic DDR4 MRS commands (to be used if UDIMM/RDIMM imp
    * lements address mirroring) - 0 - Do not implement address mirroring
    *  PSU_DDRC_DIMMCTL_DIMM_ADDR_MIRR_EN                          0x0

    * Staggering enable for multi-rank accesses (for multi-rank UDIMM and RDIM
    * M implementations only). This is not supported for mDDR, LPDDR2, LPDDR3
    * or LPDDR4 SDRAMs. Note: Even if this bit is set it does not take care of
    *  software driven MR commands (via MRCTRL0/MRCTRL1), where software is re
    * sponsible to send them to seperate ranks as appropriate. - 1 - (DDR4) Se
    * nd MRS commands to each ranks seperately - 1 - (non-DDR4) Send all comma
    * nds to even and odd ranks seperately - 0 - Do not stagger accesses
    *  PSU_DDRC_DIMMCTL_DIMM_STAGGER_CS_EN                         0x0

    * DIMM Control Register
    * (OFFSET, MASK, VALUE)      (0XFD0700F0, 0x0000003FU ,0x00000010U)
    */
	PSU_Mask_Write(DDRC_DIMMCTL_OFFSET, 0x0000003FU, 0x00000010U);
/*##################################################################### */

    /*
    * Register : RANKCTL @ 0XFD0700F4

    * Only present for multi-rank configurations. Indicates the number of cloc
    * ks of gap in data responses when performing consecutive writes to differ
    * ent ranks. This is used to switch the delays in the PHY to match the ran
    * k requirements. This value should consider both PHY requirement and ODT
    * requirement. - PHY requirement: tphy_wrcsgap + 1 (see PHY databook for v
    * alue of tphy_wrcsgap) If CRC feature is enabled, should be increased by
    * 1. If write preamble is set to 2tCK(DDR4/LPDDR4 only), should be increas
    * ed by 1. If write postamble is set to 1.5tCK(LPDDR4 only), should be inc
    * reased by 1. - ODT requirement: The value programmed in this register ta
    * kes care of the ODT switch off timing requirement when switching ranks d
    * uring writes. For LPDDR4, the requirement is ODTLoff - ODTLon - BL/2 + 1
    *  For configurations with MEMC_FREQ_RATIO=1, program this to the larger o
    * f PHY requirement or ODT requirement. For configurations with MEMC_FREQ_
    * RATIO=2, program this to the larger value divided by two and round it up
    *  to the next integer.
    *  PSU_DDRC_RANKCTL_DIFF_RANK_WR_GAP                           0x6

    * Only present for multi-rank configurations. Indicates the number of cloc
    * ks of gap in data responses when performing consecutive reads to differe
    * nt ranks. This is used to switch the delays in the PHY to match the rank
    *  requirements. This value should consider both PHY requirement and ODT r
    * equirement. - PHY requirement: tphy_rdcsgap + 1 (see PHY databook for va
    * lue of tphy_rdcsgap) If read preamble is set to 2tCK(DDR4/LPDDR4 only),
    * should be increased by 1. If read postamble is set to 1.5tCK(LPDDR4 only
    * ), should be increased by 1. - ODT requirement: The value programmed in
    * this register takes care of the ODT switch off timing requirement when s
    * witching ranks during reads. For configurations with MEMC_FREQ_RATIO=1,
    * program this to the larger of PHY requirement or ODT requirement. For co
    * nfigurations with MEMC_FREQ_RATIO=2, program this to the larger value di
    * vided by two and round it up to the next integer.
    *  PSU_DDRC_RANKCTL_DIFF_RANK_RD_GAP                           0x6

    * Only present for multi-rank configurations. Background: Reads to the sam
    * e rank can be performed back-to-back. Reads to different ranks require a
    * dditional gap dictated by the register RANKCTL.diff_rank_rd_gap. This is
    *  to avoid possible data bus contention as well as to give PHY enough tim
    * e to switch the delay when changing ranks. The uMCTL2 arbitrates for bus
    *  access on a cycle-by-cycle basis; therefore after a read is scheduled,
    * there are few clock cycles (determined by the value on RANKCTL.diff_rank
    * _rd_gap register) in which only reads from the same rank are eligible to
    *  be scheduled. This prevents reads from other ranks from having fair acc
    * ess to the data bus. This parameter represents the maximum number of rea
    * ds that can be scheduled consecutively to the same rank. After this numb
    * er is reached, a delay equal to RANKCTL.diff_rank_rd_gap is inserted by
    * the scheduler to allow all ranks a fair opportunity to be scheduled. Hig
    * her numbers increase bandwidth utilization, lower numbers increase fairn
    * ess. This feature can be DISABLED by setting this register to 0. When se
    * t to 0, the Controller will stay on the same rank as long as commands ar
    * e available for it. Minimum programmable value is 0 (feature disabled) a
    * nd maximum programmable value is 0xF. FOR PERFORMANCE ONLY.
    *  PSU_DDRC_RANKCTL_MAX_RANK_RD                                0xf

    * Rank Control Register
    * (OFFSET, MASK, VALUE)      (0XFD0700F4, 0x00000FFFU ,0x0000066FU)
    */
	PSU_Mask_Write(DDRC_RANKCTL_OFFSET, 0x00000FFFU, 0x0000066FU);
/*##################################################################### */

    /*
    * Register : DRAMTMG0 @ 0XFD070100

    * Minimum time between write and precharge to same bank. Unit: Clocks Spec
    * ifications: WL + BL/2 + tWR = approximately 8 cycles + 15 ns = 14 clocks
    *  @400MHz and less for lower frequencies where: - WL = write latency - BL
    *  = burst length. This must match the value programmed in the BL bit of t
    * he mode register to the SDRAM. BST (burst terminate) is not supported at
    *  present. - tWR = Write recovery time. This comes directly from the SDRA
    * M specification. Add one extra cycle for LPDDR2/LPDDR3/LPDDR4 for this p
    * arameter. For configurations with MEMC_FREQ_RATIO=2, 1T mode, divide the
    *  above value by 2. No rounding up. For configurations with MEMC_FREQ_RAT
    * IO=2, 2T mode or LPDDR4 mode, divide the above value by 2 and round it u
    * p to the next integer value.
    *  PSU_DDRC_DRAMTMG0_WR2PRE                                    0x11

    * tFAW Valid only when 8 or more banks(or banks x bank groups) are present
    * . In 8-bank design, at most 4 banks must be activated in a rolling windo
    * w of tFAW cycles. For configurations with MEMC_FREQ_RATIO=2, program thi
    * s to (tFAW/2) and round up to next integer value. In a 4-bank design, se
    * t this register to 0x1 independent of the MEMC_FREQ_RATIO configuration.
    *  Unit: Clocks
    *  PSU_DDRC_DRAMTMG0_T_FAW                                     0x10

    * tRAS(max): Maximum time between activate and precharge to same bank. Thi
    * s is the maximum time that a page can be kept open Minimum value of this
    *  register is 1. Zero is invalid. For configurations with MEMC_FREQ_RATIO
    * =2, program this to (tRAS(max)-1)/2. No rounding up. Unit: Multiples of
    * 1024 clocks.
    *  PSU_DDRC_DRAMTMG0_T_RAS_MAX                                 0x24

    * tRAS(min): Minimum time between activate and precharge to the same bank.
    *  For configurations with MEMC_FREQ_RATIO=2, 1T mode, program this to tRA
    * S(min)/2. No rounding up. For configurations with MEMC_FREQ_RATIO=2, 2T
    * mode or LPDDR4 mode, program this to (tRAS(min)/2) and round it up to th
    * e next integer value. Unit: Clocks
    *  PSU_DDRC_DRAMTMG0_T_RAS_MIN                                 0x12

    * SDRAM Timing Register 0
    * (OFFSET, MASK, VALUE)      (0XFD070100, 0x7F3F7F3FU ,0x11102412U)
    */
	PSU_Mask_Write(DDRC_DRAMTMG0_OFFSET, 0x7F3F7F3FU, 0x11102412U);
/*##################################################################### */

    /*
    * Register : DRAMTMG1 @ 0XFD070104

    * tXP: Minimum time after power-down exit to any operation. For DDR3, this
    *  should be programmed to tXPDLL if slow powerdown exit is selected in MR
    * 0[12]. If C/A parity for DDR4 is used, set to (tXP+PL) instead. For conf
    * igurations with MEMC_FREQ_RATIO=2, program this to (tXP/2) and round it
    * up to the next integer value. Units: Clocks
    *  PSU_DDRC_DRAMTMG1_T_XP                                      0x4

    * tRTP: Minimum time from read to precharge of same bank. - DDR2: tAL + BL
    * /2 + max(tRTP, 2) - 2 - DDR3: tAL + max (tRTP, 4) - DDR4: Max of followi
    * ng two equations: tAL + max (tRTP, 4) or, RL + BL/2 - tRP. - mDDR: BL/2
    * - LPDDR2: Depends on if it's LPDDR2-S2 or LPDDR2-S4: LPDDR2-S2: BL/2 + t
    * RTP - 1. LPDDR2-S4: BL/2 + max(tRTP,2) - 2. - LPDDR3: BL/2 + max(tRTP,4)
    *  - 4 - LPDDR4: BL/2 + max(tRTP,8) - 8 For configurations with MEMC_FREQ_
    * RATIO=2, 1T mode, divide the above value by 2. No rounding up. For confi
    * gurations with MEMC_FREQ_RATIO=2, 2T mode or LPDDR4 mode, divide the abo
    * ve value by 2 and round it up to the next integer value. Unit: Clocks.
    *  PSU_DDRC_DRAMTMG1_RD2PRE                                    0x4

    * tRC: Minimum time between activates to same bank. For configurations wit
    * h MEMC_FREQ_RATIO=2, program this to (tRC/2) and round up to next intege
    * r value. Unit: Clocks.
    *  PSU_DDRC_DRAMTMG1_T_RC                                      0x1a

    * SDRAM Timing Register 1
    * (OFFSET, MASK, VALUE)      (0XFD070104, 0x001F1F7FU ,0x0004041AU)
    */
	PSU_Mask_Write(DDRC_DRAMTMG1_OFFSET, 0x001F1F7FU, 0x0004041AU);
/*##################################################################### */

    /*
    * Register : DRAMTMG2 @ 0XFD070108

    * Set to WL Time from write command to write data on SDRAM interface. This
    *  must be set to WL. For mDDR, it should normally be set to 1. Note that,
    *  depending on the PHY, if using RDIMM, it may be necessary to use a valu
    * e of WL + 1 to compensate for the extra cycle of latency through the RDI
    * MM For configurations with MEMC_FREQ_RATIO=2, divide the value calculate
    * d using the above equation by 2, and round it up to next integer. This r
    * egister field is not required for DDR2 and DDR3 (except if MEMC_TRAINING
    *  is set), as the DFI read and write latencies defined in DFITMG0 and DFI
    * TMG1 are sufficient for those protocols Unit: clocks
    *  PSU_DDRC_DRAMTMG2_WRITE_LATENCY                             0x7

    * Set to RL Time from read command to read data on SDRAM interface. This m
    * ust be set to RL. Note that, depending on the PHY, if using RDIMM, it ma
    * t be necessary to use a value of RL + 1 to compensate for the extra cycl
    * e of latency through the RDIMM For configurations with MEMC_FREQ_RATIO=2
    * , divide the value calculated using the above equation by 2, and round i
    * t up to next integer. This register field is not required for DDR2 and D
    * DR3 (except if MEMC_TRAINING is set), as the DFI read and write latencie
    * s defined in DFITMG0 and DFITMG1 are sufficient for those protocols Unit
    * : clocks
    *  PSU_DDRC_DRAMTMG2_READ_LATENCY                              0x8

    * DDR2/3/mDDR: RL + BL/2 + 2 - WL DDR4: RL + BL/2 + 1 + WR_PREAMBLE - WL L
    * PDDR2/LPDDR3: RL + BL/2 + RU(tDQSCKmax/tCK) + 1 - WL LPDDR4(DQ ODT is Di
    * sabled): RL + BL/2 + RU(tDQSCKmax/tCK) + WR_PREAMBLE + RD_POSTAMBLE - WL
    *  LPDDR4(DQ ODT is Enabled) : RL + BL/2 + RU(tDQSCKmax/tCK) + RD_POSTAMBL
    * E - ODTLon - RU(tODTon(min)/tCK) Minimum time from read command to write
    *  command. Include time for bus turnaround and all per-bank, per-rank, an
    * d global constraints. Unit: Clocks. Where: - WL = write latency - BL = b
    * urst length. This must match the value programmed in the BL bit of the m
    * ode register to the SDRAM - RL = read latency = CAS latency - WR_PREAMBL
    * E = write preamble. This is unique to DDR4 and LPDDR4. - RD_POSTAMBLE =
    * read postamble. This is unique to LPDDR4. For LPDDR2/LPDDR3/LPDDR4, if d
    * erating is enabled (DERATEEN.derate_enable=1), derated tDQSCKmax should
    * be used. For configurations with MEMC_FREQ_RATIO=2, divide the value cal
    * culated using the above equation by 2, and round it up to next integer.
    *  PSU_DDRC_DRAMTMG2_RD2WR                                     0x6

    * DDR4: CWL + PL + BL/2 + tWTR_L Others: CWL + BL/2 + tWTR In DDR4, minimu
    * m time from write command to read command for same bank group. In others
    * , minimum time from write command to read command. Includes time for bus
    *  turnaround, recovery times, and all per-bank, per-rank, and global cons
    * traints. Unit: Clocks. Where: - CWL = CAS write latency - PL = Parity la
    * tency - BL = burst length. This must match the value programmed in the B
    * L bit of the mode register to the SDRAM - tWTR_L = internal write to rea
    * d command delay for same bank group. This comes directly from the SDRAM
    * specification. - tWTR = internal write to read command delay. This comes
    *  directly from the SDRAM specification. Add one extra cycle for LPDDR2/L
    * PDDR3/LPDDR4 operation. For configurations with MEMC_FREQ_RATIO=2, divid
    * e the value calculated using the above equation by 2, and round it up to
    *  next integer.
    *  PSU_DDRC_DRAMTMG2_WR2RD                                     0xd

    * SDRAM Timing Register 2
    * (OFFSET, MASK, VALUE)      (0XFD070108, 0x3F3F3F3FU ,0x0708060DU)
    */
	PSU_Mask_Write(DDRC_DRAMTMG2_OFFSET, 0x3F3F3F3FU, 0x0708060DU);
/*##################################################################### */

    /*
    * Register : DRAMTMG3 @ 0XFD07010C

    * Time to wait after a mode register write or read (MRW or MRR). Present o
    * nly in designs configured to support LPDDR2, LPDDR3 or LPDDR4. LPDDR2 ty
    * pically requires value of 5. LPDDR3 typically requires value of 10. LPDD
    * R4: Set this to the larger of tMRW and tMRWCKEL. For LPDDR2, this regist
    * er is used for the time from a MRW/MRR to all other commands. For LDPDR3
    * , this register is used for the time from a MRW/MRR to a MRW/MRR.
    *  PSU_DDRC_DRAMTMG3_T_MRW                                     0x5

    * tMRD: Cycles to wait after a mode register write or read. Depending on t
    * he connected SDRAM, tMRD represents: DDR2/mDDR: Time from MRS to any com
    * mand DDR3/4: Time from MRS to MRS command LPDDR2: not used LPDDR3/4: Tim
    * e from MRS to non-MRS command For configurations with MEMC_FREQ_RATIO=2,
    *  program this to (tMRD/2) and round it up to the next integer value. If
    * C/A parity for DDR4 is used, set to tMRD_PAR(tMOD+PL) instead.
    *  PSU_DDRC_DRAMTMG3_T_MRD                                     0x4

    * tMOD: Parameter used only in DDR3 and DDR4. Cycles between load mode com
    * mand and following non-load mode command. If C/A parity for DDR4 is used
    * , set to tMOD_PAR(tMOD+PL) instead. Set to tMOD if MEMC_FREQ_RATIO=1, or
    *  tMOD/2 (rounded up to next integer) if MEMC_FREQ_RATIO=2. Note that if
    * using RDIMM, depending on the PHY, it may be necessary to use a value of
    *  tMOD + 1 or (tMOD + 1)/2 to compensate for the extra cycle of latency a
    * pplied to mode register writes by the RDIMM chip.
    *  PSU_DDRC_DRAMTMG3_T_MOD                                     0xc

    * SDRAM Timing Register 3
    * (OFFSET, MASK, VALUE)      (0XFD07010C, 0x3FF3F3FFU ,0x0050400CU)
    */
	PSU_Mask_Write(DDRC_DRAMTMG3_OFFSET, 0x3FF3F3FFU, 0x0050400CU);
/*##################################################################### */

    /*
    * Register : DRAMTMG4 @ 0XFD070110

    * tRCD - tAL: Minimum time from activate to read or write command to same
    * bank. For configurations with MEMC_FREQ_RATIO=2, program this to ((tRCD
    * - tAL)/2) and round it up to the next integer value. Minimum value allow
    * ed for this register is 1, which implies minimum (tRCD - tAL) value to b
    * e 2 in configurations with MEMC_FREQ_RATIO=2. Unit: Clocks.
    *  PSU_DDRC_DRAMTMG4_T_RCD                                     0x8

    * DDR4: tCCD_L: This is the minimum time between two reads or two writes f
    * or same bank group. Others: tCCD: This is the minimum time between two r
    * eads or two writes. For configurations with MEMC_FREQ_RATIO=2, program t
    * his to (tCCD_L/2 or tCCD/2) and round it up to the next integer value. U
    * nit: clocks.
    *  PSU_DDRC_DRAMTMG4_T_CCD                                     0x3

    * DDR4: tRRD_L: Minimum time between activates from bank 'a' to bank 'b' f
    * or same bank group. Others: tRRD: Minimum time between activates from ba
    * nk 'a' to bank 'b'For configurations with MEMC_FREQ_RATIO=2, program thi
    * s to (tRRD_L/2 or tRRD/2) and round it up to the next integer value. Uni
    * t: Clocks.
    *  PSU_DDRC_DRAMTMG4_T_RRD                                     0x3

    * tRP: Minimum time from precharge to activate of same bank. For MEMC_FREQ
    * _RATIO=1 configurations, t_rp should be set to RoundUp(tRP/tCK). For MEM
    * C_FREQ_RATIO=2 configurations, t_rp should be set to RoundDown(RoundUp(t
    * RP/tCK)/2) + 1. For MEMC_FREQ_RATIO=2 configurations in LPDDR4, t_rp sho
    * uld be set to RoundUp(RoundUp(tRP/tCK)/2). Unit: Clocks.
    *  PSU_DDRC_DRAMTMG4_T_RP                                      0x9

    * SDRAM Timing Register 4
    * (OFFSET, MASK, VALUE)      (0XFD070110, 0x1F0F0F1FU ,0x08030309U)
    */
	PSU_Mask_Write(DDRC_DRAMTMG4_OFFSET, 0x1F0F0F1FU, 0x08030309U);
/*##################################################################### */

    /*
    * Register : DRAMTMG5 @ 0XFD070114

    * This is the time before Self Refresh Exit that CK is maintained as a val
    * id clock before issuing SRX. Specifies the clock stable time before SRX.
    *  Recommended settings: - mDDR: 1 - LPDDR2: 2 - LPDDR3: 2 - LPDDR4: tCKCK
    * EH - DDR2: 1 - DDR3: tCKSRX - DDR4: tCKSRX For configurations with MEMC_
    * FREQ_RATIO=2, program this to recommended value divided by two and round
    *  it up to next integer.
    *  PSU_DDRC_DRAMTMG5_T_CKSRX                                   0x6

    * This is the time after Self Refresh Down Entry that CK is maintained as
    * a valid clock. Specifies the clock disable delay after SRE. Recommended
    * settings: - mDDR: 0 - LPDDR2: 2 - LPDDR3: 2 - LPDDR4: tCKCKEL - DDR2: 1
    * - DDR3: max (10 ns, 5 tCK) - DDR4: max (10 ns, 5 tCK) For configurations
    *  with MEMC_FREQ_RATIO=2, program this to recommended value divided by tw
    * o and round it up to next integer.
    *  PSU_DDRC_DRAMTMG5_T_CKSRE                                   0x6

    * Minimum CKE low width for Self refresh or Self refresh power down entry
    * to exit timing in memory clock cycles. Recommended settings: - mDDR: tRF
    * C - LPDDR2: tCKESR - LPDDR3: tCKESR - LPDDR4: max(tCKELPD, tSR) - DDR2:
    * tCKE - DDR3: tCKE + 1 - DDR4: tCKE + 1 For configurations with MEMC_FREQ
    * _RATIO=2, program this to recommended value divided by two and round it
    * up to next integer.
    *  PSU_DDRC_DRAMTMG5_T_CKESR                                   0x4

    * Minimum number of cycles of CKE HIGH/LOW during power-down and self refr
    * esh. - LPDDR2/LPDDR3 mode: Set this to the larger of tCKE or tCKESR - LP
    * DDR4 mode: Set this to the larger of tCKE, tCKELPD or tSR. - Non-LPDDR2/
    * non-LPDDR3/non-LPDDR4 designs: Set this to tCKE value. For configuration
    * s with MEMC_FREQ_RATIO=2, program this to (value described above)/2 and
    * round it up to the next integer value. Unit: Clocks.
    *  PSU_DDRC_DRAMTMG5_T_CKE                                     0x3

    * SDRAM Timing Register 5
    * (OFFSET, MASK, VALUE)      (0XFD070114, 0x0F0F3F1FU ,0x06060403U)
    */
	PSU_Mask_Write(DDRC_DRAMTMG5_OFFSET, 0x0F0F3F1FU, 0x06060403U);
/*##################################################################### */

    /*
    * Register : DRAMTMG6 @ 0XFD070118

    * This is the time after Deep Power Down Entry that CK is maintained as a
    * valid clock. Specifies the clock disable delay after DPDE. Recommended s
    * ettings: - mDDR: 0 - LPDDR2: 2 - LPDDR3: 2 For configurations with MEMC_
    * FREQ_RATIO=2, program this to recommended value divided by two and round
    *  it up to next integer. This is only present for designs supporting mDDR
    *  or LPDDR2/LPDDR3 devices.
    *  PSU_DDRC_DRAMTMG6_T_CKDPDE                                  0x1

    * This is the time before Deep Power Down Exit that CK is maintained as a
    * valid clock before issuing DPDX. Specifies the clock stable time before
    * DPDX. Recommended settings: - mDDR: 1 - LPDDR2: 2 - LPDDR3: 2 For config
    * urations with MEMC_FREQ_RATIO=2, program this to recommended value divid
    * ed by two and round it up to next integer. This is only present for desi
    * gns supporting mDDR or LPDDR2 devices.
    *  PSU_DDRC_DRAMTMG6_T_CKDPDX                                  0x1

    * This is the time before Clock Stop Exit that CK is maintained as a valid
    *  clock before issuing Clock Stop Exit. Specifies the clock stable time b
    * efore next command after Clock Stop Exit. Recommended settings: - mDDR:
    * 1 - LPDDR2: tXP + 2 - LPDDR3: tXP + 2 - LPDDR4: tXP + 2 For configuratio
    * ns with MEMC_FREQ_RATIO=2, program this to recommended value divided by
    * two and round it up to next integer. This is only present for designs su
    * pporting mDDR or LPDDR2/LPDDR3/LPDDR4 devices.
    *  PSU_DDRC_DRAMTMG6_T_CKCSX                                   0x4

    * SDRAM Timing Register 6
    * (OFFSET, MASK, VALUE)      (0XFD070118, 0x0F0F000FU ,0x01010004U)
    */
	PSU_Mask_Write(DDRC_DRAMTMG6_OFFSET, 0x0F0F000FU, 0x01010004U);
/*##################################################################### */

    /*
    * Register : DRAMTMG7 @ 0XFD07011C

    * This is the time after Power Down Entry that CK is maintained as a valid
    *  clock. Specifies the clock disable delay after PDE. Recommended setting
    * s: - mDDR: 0 - LPDDR2: 2 - LPDDR3: 2 - LPDDR4: tCKCKEL For configuration
    * s with MEMC_FREQ_RATIO=2, program this to recommended value divided by t
    * wo and round it up to next integer. This is only present for designs sup
    * porting mDDR or LPDDR2/LPDDR3/LPDDR4 devices.
    *  PSU_DDRC_DRAMTMG7_T_CKPDE                                   0x6

    * This is the time before Power Down Exit that CK is maintained as a valid
    *  clock before issuing PDX. Specifies the clock stable time before PDX. R
    * ecommended settings: - mDDR: 0 - LPDDR2: 2 - LPDDR3: 2 - LPDDR4: 2 For c
    * onfigurations with MEMC_FREQ_RATIO=2, program this to recommended value
    * divided by two and round it up to next integer. This is only present for
    *  designs supporting mDDR or LPDDR2/LPDDR3/LPDDR4 devices.
    *  PSU_DDRC_DRAMTMG7_T_CKPDX                                   0x6

    * SDRAM Timing Register 7
    * (OFFSET, MASK, VALUE)      (0XFD07011C, 0x00000F0FU ,0x00000606U)
    */
	PSU_Mask_Write(DDRC_DRAMTMG7_OFFSET, 0x00000F0FU, 0x00000606U);
/*##################################################################### */

    /*
    * Register : DRAMTMG8 @ 0XFD070120

    * tXS_FAST: Exit Self Refresh to ZQCL, ZQCS and MRS (only CL, WR, RTP and
    * Geardown mode). For configurations with MEMC_FREQ_RATIO=2, program this
    * to the above value divided by 2 and round up to next integer value. Unit
    * : Multiples of 32 clocks. Note: This is applicable to only ZQCL/ZQCS com
    * mands. Note: Ensure this is less than or equal to t_xs_x32.
    *  PSU_DDRC_DRAMTMG8_T_XS_FAST_X32                             0x3

    * tXS_ABORT: Exit Self Refresh to commands not requiring a locked DLL in S
    * elf Refresh Abort. For configurations with MEMC_FREQ_RATIO=2, program th
    * is to the above value divided by 2 and round up to next integer value. U
    * nit: Multiples of 32 clocks. Note: Ensure this is less than or equal to
    * t_xs_x32.
    *  PSU_DDRC_DRAMTMG8_T_XS_ABORT_X32                            0x3

    * tXSDLL: Exit Self Refresh to commands requiring a locked DLL. For config
    * urations with MEMC_FREQ_RATIO=2, program this to the above value divided
    *  by 2 and round up to next integer value. Unit: Multiples of 32 clocks.
    * Note: Used only for DDR2, DDR3 and DDR4 SDRAMs.
    *  PSU_DDRC_DRAMTMG8_T_XS_DLL_X32                              0xd

    * tXS: Exit Self Refresh to commands not requiring a locked DLL. For confi
    * gurations with MEMC_FREQ_RATIO=2, program this to the above value divide
    * d by 2 and round up to next integer value. Unit: Multiples of 32 clocks.
    *  Note: Used only for DDR2, DDR3 and DDR4 SDRAMs.
    *  PSU_DDRC_DRAMTMG8_T_XS_X32                                  0x6

    * SDRAM Timing Register 8
    * (OFFSET, MASK, VALUE)      (0XFD070120, 0x7F7F7F7FU ,0x03030D06U)
    */
	PSU_Mask_Write(DDRC_DRAMTMG8_OFFSET, 0x7F7F7F7FU, 0x03030D06U);
/*##################################################################### */

    /*
    * Register : DRAMTMG9 @ 0XFD070124

    * DDR4 Write preamble mode - 0: 1tCK preamble - 1: 2tCK preamble Present o
    * nly with MEMC_FREQ_RATIO=2
    *  PSU_DDRC_DRAMTMG9_DDR4_WR_PREAMBLE                          0x0

    * tCCD_S: This is the minimum time between two reads or two writes for dif
    * ferent bank group. For bank switching (from bank 'a' to bank 'b'), the m
    * inimum time is this value + 1. For configurations with MEMC_FREQ_RATIO=2
    * , program this to (tCCD_S/2) and round it up to the next integer value.
    * Present only in designs configured to support DDR4. Unit: clocks.
    *  PSU_DDRC_DRAMTMG9_T_CCD_S                                   0x2

    * tRRD_S: Minimum time between activates from bank 'a' to bank 'b' for dif
    * ferent bank group. For configurations with MEMC_FREQ_RATIO=2, program th
    * is to (tRRD_S/2) and round it up to the next integer value. Present only
    *  in designs configured to support DDR4. Unit: Clocks.
    *  PSU_DDRC_DRAMTMG9_T_RRD_S                                   0x2

    * CWL + PL + BL/2 + tWTR_S Minimum time from write command to read command
    *  for different bank group. Includes time for bus turnaround, recovery ti
    * mes, and all per-bank, per-rank, and global constraints. Present only in
    *  designs configured to support DDR4. Unit: Clocks. Where: - CWL = CAS wr
    * ite latency - PL = Parity latency - BL = burst length. This must match t
    * he value programmed in the BL bit of the mode register to the SDRAM - tW
    * TR_S = internal write to read command delay for different bank group. Th
    * is comes directly from the SDRAM specification. For configurations with
    * MEMC_FREQ_RATIO=2, divide the value calculated using the above equation
    * by 2, and round it up to next integer.
    *  PSU_DDRC_DRAMTMG9_WR2RD_S                                   0xb

    * SDRAM Timing Register 9
    * (OFFSET, MASK, VALUE)      (0XFD070124, 0x40070F3FU ,0x0002020BU)
    */
	PSU_Mask_Write(DDRC_DRAMTMG9_OFFSET, 0x40070F3FU, 0x0002020BU);
/*##################################################################### */

    /*
    * Register : DRAMTMG11 @ 0XFD07012C

    * tXMPDLL: This is the minimum Exit MPSM to commands requiring a locked DL
    * L. For configurations with MEMC_FREQ_RATIO=2, program this to (tXMPDLL/2
    * ) and round it up to the next integer value. Present only in designs con
    * figured to support DDR4. Unit: Multiples of 32 clocks.
    *  PSU_DDRC_DRAMTMG11_POST_MPSM_GAP_X32                        0x70

    * tMPX_LH: This is the minimum CS_n Low hold time to CKE rising edge. For
    * configurations with MEMC_FREQ_RATIO=2, program this to RoundUp(tMPX_LH/2
    * )+1. Present only in designs configured to support DDR4. Unit: clocks.
    *  PSU_DDRC_DRAMTMG11_T_MPX_LH                                 0x7

    * tMPX_S: Minimum time CS setup time to CKE. For configurations with MEMC_
    * FREQ_RATIO=2, program this to (tMPX_S/2) and round it up to the next int
    * eger value. Present only in designs configured to support DDR4. Unit: Cl
    * ocks.
    *  PSU_DDRC_DRAMTMG11_T_MPX_S                                  0x1

    * tCKMPE: Minimum valid clock requirement after MPSM entry. Present only i
    * n designs configured to support DDR4. Unit: Clocks. For configurations w
    * ith MEMC_FREQ_RATIO=2, divide the value calculated using the above equat
    * ion by 2, and round it up to next integer.
    *  PSU_DDRC_DRAMTMG11_T_CKMPE                                  0xe

    * SDRAM Timing Register 11
    * (OFFSET, MASK, VALUE)      (0XFD07012C, 0x7F1F031FU ,0x7007010EU)
    */
	PSU_Mask_Write(DDRC_DRAMTMG11_OFFSET, 0x7F1F031FU, 0x7007010EU);
/*##################################################################### */

    /*
    * Register : DRAMTMG12 @ 0XFD070130

    * tCMDCKE: Delay from valid command to CKE input LOW. Set this to the larg
    * er of tESCKE or tCMDCKE For configurations with MEMC_FREQ_RATIO=2, progr
    * am this to (max(tESCKE, tCMDCKE)/2) and round it up to next integer valu
    * e.
    *  PSU_DDRC_DRAMTMG12_T_CMDCKE                                 0x2

    * tCKEHCMD: Valid command requirement after CKE input HIGH. For configurat
    * ions with MEMC_FREQ_RATIO=2, program this to (tCKEHCMD/2) and round it u
    * p to next integer value.
    *  PSU_DDRC_DRAMTMG12_T_CKEHCMD                                0x6

    * tMRD_PDA: This is the Mode Register Set command cycle time in PDA mode.
    * For configurations with MEMC_FREQ_RATIO=2, program this to (tMRD_PDA/2)
    * and round it up to next integer value.
    *  PSU_DDRC_DRAMTMG12_T_MRD_PDA                                0x8

    * SDRAM Timing Register 12
    * (OFFSET, MASK, VALUE)      (0XFD070130, 0x00030F1FU ,0x00020608U)
    */
	PSU_Mask_Write(DDRC_DRAMTMG12_OFFSET, 0x00030F1FU, 0x00020608U);
/*##################################################################### */

    /*
    * Register : ZQCTL0 @ 0XFD070180

    * - 1 - Disable uMCTL2 generation of ZQCS/MPC(ZQ calibration) command. Reg
    * ister DBGCMD.zq_calib_short can be used instead to issue ZQ calibration
    * request from APB module. - 0 - Internally generate ZQCS/MPC(ZQ calibrati
    * on) commands based on ZQCTL1.t_zq_short_interval_x1024. This is only pre
    * sent for designs supporting DDR3/DDR4 or LPDDR2/LPDDR3/LPDDR4 devices.
    *  PSU_DDRC_ZQCTL0_DIS_AUTO_ZQ                                 0x1

    * - 1 - Disable issuing of ZQCL/MPC(ZQ calibration) command at Self-Refres
    * h/SR-Powerdown exit. Only applicable when run in DDR3 or DDR4 or LPDDR2
    * or LPDDR3 or LPDDR4 mode. - 0 - Enable issuing of ZQCL/MPC(ZQ calibratio
    * n) command at Self-Refresh/SR-Powerdown exit. Only applicable when run i
    * n DDR3 or DDR4 or LPDDR2 or LPDDR3 or LPDDR4 mode. This is only present
    * for designs supporting DDR3/DDR4 or LPDDR2/LPDDR3/LPDDR4 devices.
    *  PSU_DDRC_ZQCTL0_DIS_SRX_ZQCL                                0x0

    * - 1 - Denotes that ZQ resistor is shared between ranks. Means ZQinit/ZQC
    * L/ZQCS/MPC(ZQ calibration) commands are sent to one rank at a time with
    * tZQinit/tZQCL/tZQCS/tZQCAL/tZQLAT timing met between commands so that co
    * mmands to different ranks do not overlap. - 0 - ZQ resistor is not share
    * d. This is only present for designs supporting DDR3/DDR4 or LPDDR2/LPDDR
    * 3/LPDDR4 devices.
    *  PSU_DDRC_ZQCTL0_ZQ_RESISTOR_SHARED                          0x0

    * - 1 - Disable issuing of ZQCL command at Maximum Power Saving Mode exit.
    *  Only applicable when run in DDR4 mode. - 0 - Enable issuing of ZQCL com
    * mand at Maximum Power Saving Mode exit. Only applicable when run in DDR4
    *  mode. This is only present for designs supporting DDR4 devices.
    *  PSU_DDRC_ZQCTL0_DIS_MPSMX_ZQCL                              0x0

    * tZQoper for DDR3/DDR4, tZQCL for LPDDR2/LPDDR3, tZQCAL for LPDDR4: Numbe
    * r of cycles of NOP required after a ZQCL (ZQ calibration long)/MPC(ZQ St
    * art) command is issued to SDRAM. For configurations with MEMC_FREQ_RATIO
    * =2: DDR3/DDR4: program this to tZQoper/2 and round it up to the next int
    * eger value. LPDDR2/LPDDR3: program this to tZQCL/2 and round it up to th
    * e next integer value. LPDDR4: program this to tZQCAL/2 and round it up t
    * o the next integer value. Unit: Clock cycles. This is only present for d
    * esigns supporting DDR3/DDR4 or LPDDR2/LPDDR3/LPDDR4 devices.
    *  PSU_DDRC_ZQCTL0_T_ZQ_LONG_NOP                               0x100

    * tZQCS for DDR3/DD4/LPDDR2/LPDDR3, tZQLAT for LPDDR4: Number of cycles of
    *  NOP required after a ZQCS (ZQ calibration short)/MPC(ZQ Latch) command
    * is issued to SDRAM. For configurations with MEMC_FREQ_RATIO=2, program t
    * his to tZQCS/2 and round it up to the next integer value. Unit: Clock cy
    * cles. This is only present for designs supporting DDR3/DDR4 or LPDDR2/LP
    * DDR3/LPDDR4 devices.
    *  PSU_DDRC_ZQCTL0_T_ZQ_SHORT_NOP                              0x40

    * ZQ Control Register 0
    * (OFFSET, MASK, VALUE)      (0XFD070180, 0xF7FF03FFU ,0x81000040U)
    */
	PSU_Mask_Write(DDRC_ZQCTL0_OFFSET, 0xF7FF03FFU, 0x81000040U);
/*##################################################################### */

    /*
    * Register : ZQCTL1 @ 0XFD070184

    * tZQReset: Number of cycles of NOP required after a ZQReset (ZQ calibrati
    * on Reset) command is issued to SDRAM. For configurations with MEMC_FREQ_
    * RATIO=2, program this to tZQReset/2 and round it up to the next integer
    * value. Unit: Clock cycles. This is only present for designs supporting L
    * PDDR2/LPDDR3/LPDDR4 devices.
    *  PSU_DDRC_ZQCTL1_T_ZQ_RESET_NOP                              0x20

    * Average interval to wait between automatically issuing ZQCS (ZQ calibrat
    * ion short)/MPC(ZQ calibration) commands to DDR3/DDR4/LPDDR2/LPDDR3/LPDDR
    * 4 devices. Meaningless, if ZQCTL0.dis_auto_zq=1. Unit: 1024 clock cycles
    * . This is only present for designs supporting DDR3/DDR4 or LPDDR2/LPDDR3
    * /LPDDR4 devices.
    *  PSU_DDRC_ZQCTL1_T_ZQ_SHORT_INTERVAL_X1024                   0x196dc

    * ZQ Control Register 1
    * (OFFSET, MASK, VALUE)      (0XFD070184, 0x3FFFFFFFU ,0x020196DCU)
    */
	PSU_Mask_Write(DDRC_ZQCTL1_OFFSET, 0x3FFFFFFFU, 0x020196DCU);
/*##################################################################### */

    /*
    * Register : DFITMG0 @ 0XFD070190

    * Specifies the number of DFI clock cycles after an assertion or de-assert
    * ion of the DFI control signals that the control signals at the PHY-DRAM
    * interface reflect the assertion or de-assertion. If the DFI clock and th
    * e memory clock are not phase-aligned, this timing parameter should be ro
    * unded up to the next integer value. Note that if using RDIMM, it is nece
    * ssary to increment this parameter by RDIMM's extra cycle of latency in t
    * erms of DFI clock.
    *  PSU_DDRC_DFITMG0_DFI_T_CTRL_DELAY                           0x4

    * Defines whether dfi_rddata_en/dfi_rddata/dfi_rddata_valid is generated u
    * sing HDR or SDR values Selects whether value in DFITMG0.dfi_t_rddata_en
    * is in terms of SDR or HDR clock cycles: - 0 in terms of HDR clock cycles
    *  - 1 in terms of SDR clock cycles Refer to PHY specification for correct
    *  value.
    *  PSU_DDRC_DFITMG0_DFI_RDDATA_USE_SDR                         0x1

    * Time from the assertion of a read command on the DFI interface to the as
    * sertion of the dfi_rddata_en signal. Refer to PHY specification for corr
    * ect value. This corresponds to the DFI parameter trddata_en. Note that,
    * depending on the PHY, if using RDIMM, it may be necessary to use the val
    * ue (CL + 1) in the calculation of trddata_en. This is to compensate for
    * the extra cycle of latency through the RDIMM. Unit: Clocks
    *  PSU_DDRC_DFITMG0_DFI_T_RDDATA_EN                            0xb

    * Defines whether dfi_wrdata_en/dfi_wrdata/dfi_wrdata_mask is generated us
    * ing HDR or SDR values Selects whether value in DFITMG0.dfi_tphy_wrlat is
    *  in terms of SDR or HDR clock cycles Selects whether value in DFITMG0.df
    * i_tphy_wrdata is in terms of SDR or HDR clock cycles - 0 in terms of HDR
    *  clock cycles - 1 in terms of SDR clock cycles Refer to PHY specificatio
    * n for correct value.
    *  PSU_DDRC_DFITMG0_DFI_WRDATA_USE_SDR                         0x1

    * Specifies the number of clock cycles between when dfi_wrdata_en is asser
    * ted to when the associated write data is driven on the dfi_wrdata signal
    * . This corresponds to the DFI timing parameter tphy_wrdata. Refer to PHY
    *  specification for correct value. Note, max supported value is 8. Unit:
    * Clocks
    *  PSU_DDRC_DFITMG0_DFI_TPHY_WRDATA                            0x2

    * Write latency Number of clocks from the write command to write data enab
    * le (dfi_wrdata_en). This corresponds to the DFI timing parameter tphy_wr
    * lat. Refer to PHY specification for correct value.Note that, depending o
    * n the PHY, if using RDIMM, it may be necessary to use the value (CL + 1)
    *  in the calculation of tphy_wrlat. This is to compensate for the extra c
    * ycle of latency through the RDIMM.
    *  PSU_DDRC_DFITMG0_DFI_TPHY_WRLAT                             0xb

    * DFI Timing Register 0
    * (OFFSET, MASK, VALUE)      (0XFD070190, 0x1FBFBF3FU ,0x048B820BU)
    */
	PSU_Mask_Write(DDRC_DFITMG0_OFFSET, 0x1FBFBF3FU, 0x048B820BU);
/*##################################################################### */

    /*
    * Register : DFITMG1 @ 0XFD070194

    * Specifies the number of DFI PHY clocks between when the dfi_cs signal is
    *  asserted and when the associated command is driven. This field is used
    * for CAL mode, should be set to '0' or the value which matches the CAL mo
    * de register setting in the DRAM. If the PHY can add the latency for CAL
    * mode, this should be set to '0'. Valid Range: 0, 3, 4, 5, 6, and 8
    *  PSU_DDRC_DFITMG1_DFI_T_CMD_LAT                              0x0

    * Specifies the number of DFI PHY clocks between when the dfi_cs signal is
    *  asserted and when the associated dfi_parity_in signal is driven.
    *  PSU_DDRC_DFITMG1_DFI_T_PARIN_LAT                            0x0

    * Specifies the number of DFI clocks between when the dfi_wrdata_en signal
    *  is asserted and when the corresponding write data transfer is completed
    *  on the DRAM bus. This corresponds to the DFI timing parameter twrdata_d
    * elay. Refer to PHY specification for correct value. For DFI 3.0 PHY, set
    *  to twrdata_delay, a new timing parameter introduced in DFI 3.0. For DFI
    *  2.1 PHY, set to tphy_wrdata + (delay of DFI write data to the DRAM). Va
    * lue to be programmed is in terms of DFI clocks, not PHY clocks. In FREQ_
    * RATIO=2, divide PHY's value by 2 and round up to next integer. If using
    * DFITMG0.dfi_wrdata_use_sdr=1, add 1 to the value. Unit: Clocks
    *  PSU_DDRC_DFITMG1_DFI_T_WRDATA_DELAY                         0x3

    * Specifies the number of DFI clock cycles from the assertion of the dfi_d
    * ram_clk_disable signal on the DFI until the clock to the DRAM memory dev
    * ices, at the PHY-DRAM boundary, maintains a low value. If the DFI clock
    * and the memory clock are not phase aligned, this timing parameter should
    *  be rounded up to the next integer value.
    *  PSU_DDRC_DFITMG1_DFI_T_DRAM_CLK_DISABLE                     0x3

    * Specifies the number of DFI clock cycles from the de-assertion of the df
    * i_dram_clk_disable signal on the DFI until the first valid rising edge o
    * f the clock to the DRAM memory devices, at the PHY-DRAM boundary. If the
    *  DFI clock and the memory clock are not phase aligned, this timing param
    * eter should be rounded up to the next integer value.
    *  PSU_DDRC_DFITMG1_DFI_T_DRAM_CLK_ENABLE                      0x4

    * DFI Timing Register 1
    * (OFFSET, MASK, VALUE)      (0XFD070194, 0xF31F0F0FU ,0x00030304U)
    */
	PSU_Mask_Write(DDRC_DFITMG1_OFFSET, 0xF31F0F0FU, 0x00030304U);
/*##################################################################### */

    /*
    * Register : DFILPCFG0 @ 0XFD070198

    * Setting for DFI's tlp_resp time. Same value is used for both Power Down,
    *  Self Refresh, Deep Power Down and Maximum Power Saving modes. DFI 2.1 s
    * pecification onwards, recommends using a fixed value of 7 always.
    *  PSU_DDRC_DFILPCFG0_DFI_TLP_RESP                             0x7

    * Value to drive on dfi_lp_wakeup signal when Deep Power Down mode is ente
    * red. Determines the DFI's tlp_wakeup time: - 0x0 - 16 cycles - 0x1 - 32
    * cycles - 0x2 - 64 cycles - 0x3 - 128 cycles - 0x4 - 256 cycles - 0x5 - 5
    * 12 cycles - 0x6 - 1024 cycles - 0x7 - 2048 cycles - 0x8 - 4096 cycles -
    * 0x9 - 8192 cycles - 0xA - 16384 cycles - 0xB - 32768 cycles - 0xC - 6553
    * 6 cycles - 0xD - 131072 cycles - 0xE - 262144 cycles - 0xF - Unlimited T
    * his is only present for designs supporting mDDR or LPDDR2/LPDDR3 devices
    * .
    *  PSU_DDRC_DFILPCFG0_DFI_LP_WAKEUP_DPD                        0x0

    * Enables DFI Low Power interface handshaking during Deep Power Down Entry
    * /Exit. - 0 - Disabled - 1 - Enabled This is only present for designs sup
    * porting mDDR or LPDDR2/LPDDR3 devices.
    *  PSU_DDRC_DFILPCFG0_DFI_LP_EN_DPD                            0x0

    * Value to drive on dfi_lp_wakeup signal when Self Refresh mode is entered
    * . Determines the DFI's tlp_wakeup time: - 0x0 - 16 cycles - 0x1 - 32 cyc
    * les - 0x2 - 64 cycles - 0x3 - 128 cycles - 0x4 - 256 cycles - 0x5 - 512
    * cycles - 0x6 - 1024 cycles - 0x7 - 2048 cycles - 0x8 - 4096 cycles - 0x9
    *  - 8192 cycles - 0xA - 16384 cycles - 0xB - 32768 cycles - 0xC - 65536 c
    * ycles - 0xD - 131072 cycles - 0xE - 262144 cycles - 0xF - Unlimited
    *  PSU_DDRC_DFILPCFG0_DFI_LP_WAKEUP_SR                         0x0

    * Enables DFI Low Power interface handshaking during Self Refresh Entry/Ex
    * it. - 0 - Disabled - 1 - Enabled
    *  PSU_DDRC_DFILPCFG0_DFI_LP_EN_SR                             0x1

    * Value to drive on dfi_lp_wakeup signal when Power Down mode is entered.
    * Determines the DFI's tlp_wakeup time: - 0x0 - 16 cycles - 0x1 - 32 cycle
    * s - 0x2 - 64 cycles - 0x3 - 128 cycles - 0x4 - 256 cycles - 0x5 - 512 cy
    * cles - 0x6 - 1024 cycles - 0x7 - 2048 cycles - 0x8 - 4096 cycles - 0x9 -
    *  8192 cycles - 0xA - 16384 cycles - 0xB - 32768 cycles - 0xC - 65536 cyc
    * les - 0xD - 131072 cycles - 0xE - 262144 cycles - 0xF - Unlimited
    *  PSU_DDRC_DFILPCFG0_DFI_LP_WAKEUP_PD                         0x0

    * Enables DFI Low Power interface handshaking during Power Down Entry/Exit
    * . - 0 - Disabled - 1 - Enabled
    *  PSU_DDRC_DFILPCFG0_DFI_LP_EN_PD                             0x1

    * DFI Low Power Configuration Register 0
    * (OFFSET, MASK, VALUE)      (0XFD070198, 0x0FF1F1F1U ,0x07000101U)
    */
	PSU_Mask_Write(DDRC_DFILPCFG0_OFFSET, 0x0FF1F1F1U, 0x07000101U);
/*##################################################################### */

    /*
    * Register : DFILPCFG1 @ 0XFD07019C

    * Value to drive on dfi_lp_wakeup signal when Maximum Power Saving Mode is
    *  entered. Determines the DFI's tlp_wakeup time: - 0x0 - 16 cycles - 0x1
    * - 32 cycles - 0x2 - 64 cycles - 0x3 - 128 cycles - 0x4 - 256 cycles - 0x
    * 5 - 512 cycles - 0x6 - 1024 cycles - 0x7 - 2048 cycles - 0x8 - 4096 cycl
    * es - 0x9 - 8192 cycles - 0xA - 16384 cycles - 0xB - 32768 cycles - 0xC -
    *  65536 cycles - 0xD - 131072 cycles - 0xE - 262144 cycles - 0xF - Unlimi
    * ted This is only present for designs supporting DDR4 devices.
    *  PSU_DDRC_DFILPCFG1_DFI_LP_WAKEUP_MPSM                       0x2

    * Enables DFI Low Power interface handshaking during Maximum Power Saving
    * Mode Entry/Exit. - 0 - Disabled - 1 - Enabled This is only present for d
    * esigns supporting DDR4 devices.
    *  PSU_DDRC_DFILPCFG1_DFI_LP_EN_MPSM                           0x1

    * DFI Low Power Configuration Register 1
    * (OFFSET, MASK, VALUE)      (0XFD07019C, 0x000000F1U ,0x00000021U)
    */
	PSU_Mask_Write(DDRC_DFILPCFG1_OFFSET, 0x000000F1U, 0x00000021U);
/*##################################################################### */

    /*
    * Register : DFIUPD0 @ 0XFD0701A0

    * When '1', disable the automatic dfi_ctrlupd_req generation by the uMCTL2
    * . The core must issue the dfi_ctrlupd_req signal using register reg_ddrc
    * _ctrlupd. When '0', uMCTL2 issues dfi_ctrlupd_req periodically.
    *  PSU_DDRC_DFIUPD0_DIS_AUTO_CTRLUPD                           0x0

    * When '1', disable the automatic dfi_ctrlupd_req generation by the uMCTL2
    *  following a self-refresh exit. The core must issue the dfi_ctrlupd_req
    * signal using register reg_ddrc_ctrlupd. When '0', uMCTL2 issues a dfi_ct
    * rlupd_req after exiting self-refresh.
    *  PSU_DDRC_DFIUPD0_DIS_AUTO_CTRLUPD_SRX                       0x0

    * Specifies the maximum number of clock cycles that the dfi_ctrlupd_req si
    * gnal can assert. Lowest value to assign to this variable is 0x40. Unit:
    * Clocks
    *  PSU_DDRC_DFIUPD0_DFI_T_CTRLUP_MAX                           0x40

    * Specifies the minimum number of clock cycles that the dfi_ctrlupd_req si
    * gnal must be asserted. The uMCTL2 expects the PHY to respond within this
    *  time. If the PHY does not respond, the uMCTL2 will de-assert dfi_ctrlup
    * d_req after dfi_t_ctrlup_min + 2 cycles. Lowest value to assign to this
    * variable is 0x3. Unit: Clocks
    *  PSU_DDRC_DFIUPD0_DFI_T_CTRLUP_MIN                           0x3

    * DFI Update Register 0
    * (OFFSET, MASK, VALUE)      (0XFD0701A0, 0xC3FF03FFU ,0x00400003U)
    */
	PSU_Mask_Write(DDRC_DFIUPD0_OFFSET, 0xC3FF03FFU, 0x00400003U);
/*##################################################################### */

    /*
    * Register : DFIUPD1 @ 0XFD0701A4

    * This is the minimum amount of time between uMCTL2 initiated DFI update r
    * equests (which is executed whenever the uMCTL2 is idle). Set this number
    *  higher to reduce the frequency of update requests, which can have a sma
    * ll impact on the latency of the first read request when the uMCTL2 is id
    * le. Unit: 1024 clocks
    *  PSU_DDRC_DFIUPD1_DFI_T_CTRLUPD_INTERVAL_MIN_X1024           0x41

    * This is the maximum amount of time between uMCTL2 initiated DFI update r
    * equests. This timer resets with each update request; when the timer expi
    * res dfi_ctrlupd_req is sent and traffic is blocked until the dfi_ctrlupd
    * _ackx is received. PHY can use this idle time to recalibrate the delay l
    * ines to the DLLs. The DFI controller update is also used to reset PHY FI
    * FO pointers in case of data capture errors. Updates are required to main
    * tain calibration over PVT, but frequent updates may impact performance.
    * Note: Value programmed for DFIUPD1.dfi_t_ctrlupd_interval_max_x1024 must
    *  be greater than DFIUPD1.dfi_t_ctrlupd_interval_min_x1024. Unit: 1024 cl
    * ocks
    *  PSU_DDRC_DFIUPD1_DFI_T_CTRLUPD_INTERVAL_MAX_X1024           0xe1

    * DFI Update Register 1
    * (OFFSET, MASK, VALUE)      (0XFD0701A4, 0x00FF00FFU ,0x004100E1U)
    */
	PSU_Mask_Write(DDRC_DFIUPD1_OFFSET, 0x00FF00FFU, 0x004100E1U);
/*##################################################################### */

    /*
    * Register : DFIMISC @ 0XFD0701B0

    * Defines polarity of dfi_wrdata_cs and dfi_rddata_cs signals. - 0: Signal
    * s are active low - 1: Signals are active high
    *  PSU_DDRC_DFIMISC_DFI_DATA_CS_POLARITY                       0x0

    * DBI implemented in DDRC or PHY. - 0 - DDRC implements DBI functionality.
    *  - 1 - PHY implements DBI functionality. Present only in designs configu
    * red to support DDR4 and LPDDR4.
    *  PSU_DDRC_DFIMISC_PHY_DBI_MODE                               0x0

    * PHY initialization complete enable signal. When asserted the dfi_init_co
    * mplete signal can be used to trigger SDRAM initialisation
    *  PSU_DDRC_DFIMISC_DFI_INIT_COMPLETE_EN                       0x0

    * DFI Miscellaneous Control Register
    * (OFFSET, MASK, VALUE)      (0XFD0701B0, 0x00000007U ,0x00000000U)
    */
	PSU_Mask_Write(DDRC_DFIMISC_OFFSET, 0x00000007U, 0x00000000U);
/*##################################################################### */

    /*
    * Register : DFITMG2 @ 0XFD0701B4

    * >Number of clocks between when a read command is sent on the DFI control
    *  interface and when the associated dfi_rddata_cs signal is asserted. Thi
    * s corresponds to the DFI timing parameter tphy_rdcslat. Refer to PHY spe
    * cification for correct value.
    *  PSU_DDRC_DFITMG2_DFI_TPHY_RDCSLAT                           0x9

    * Number of clocks between when a write command is sent on the DFI control
    *  interface and when the associated dfi_wrdata_cs signal is asserted. Thi
    * s corresponds to the DFI timing parameter tphy_wrcslat. Refer to PHY spe
    * cification for correct value.
    *  PSU_DDRC_DFITMG2_DFI_TPHY_WRCSLAT                           0x6

    * DFI Timing Register 2
    * (OFFSET, MASK, VALUE)      (0XFD0701B4, 0x00003F3FU ,0x00000906U)
    */
	PSU_Mask_Write(DDRC_DFITMG2_OFFSET, 0x00003F3FU, 0x00000906U);
/*##################################################################### */

    /*
    * Register : DBICTL @ 0XFD0701C0

    * Read DBI enable signal in DDRC. - 0 - Read DBI is disabled. - 1 - Read D
    * BI is enabled. This signal must be set the same value as DRAM's mode reg
    * ister. - DDR4: MR5 bit A12. When x4 devices are used, this signal must b
    * e set to 0. - LPDDR4: MR3[6]
    *  PSU_DDRC_DBICTL_RD_DBI_EN                                   0x0

    * Write DBI enable signal in DDRC. - 0 - Write DBI is disabled. - 1 - Writ
    * e DBI is enabled. This signal must be set the same value as DRAM's mode
    * register. - DDR4: MR5 bit A11. When x4 devices are used, this signal mus
    * t be set to 0. - LPDDR4: MR3[7]
    *  PSU_DDRC_DBICTL_WR_DBI_EN                                   0x0

    * DM enable signal in DDRC. - 0 - DM is disabled. - 1 - DM is enabled. Thi
    * s signal must be set the same logical value as DRAM's mode register. - D
    * DR4: Set this to same value as MR5 bit A10. When x4 devices are used, th
    * is signal must be set to 0. - LPDDR4: Set this to inverted value of MR13
    * [5] which is opposite polarity from this signal
    *  PSU_DDRC_DBICTL_DM_EN                                       0x1

    * DM/DBI Control Register
    * (OFFSET, MASK, VALUE)      (0XFD0701C0, 0x00000007U ,0x00000001U)
    */
	PSU_Mask_Write(DDRC_DBICTL_OFFSET, 0x00000007U, 0x00000001U);
/*##################################################################### */

    /*
    * Register : ADDRMAP0 @ 0XFD070200

    * Selects the HIF address bit used as rank address bit 0. Valid Range: 0 t
    * o 27, and 31 Internal Base: 6 The selected HIF address bit is determined
    *  by adding the internal base to the value of this field. If set to 31, r
    * ank address bit 0 is set to 0.
    *  PSU_DDRC_ADDRMAP0_ADDRMAP_CS_BIT0                           0x1f

    * Address Map Register 0
    * (OFFSET, MASK, VALUE)      (0XFD070200, 0x0000001FU ,0x0000001FU)
    */
	PSU_Mask_Write(DDRC_ADDRMAP0_OFFSET, 0x0000001FU, 0x0000001FU);
/*##################################################################### */

    /*
    * Register : ADDRMAP1 @ 0XFD070204

    * Selects the HIF address bit used as bank address bit 2. Valid Range: 0 t
    * o 29 and 31 Internal Base: 4 The selected HIF address bit is determined
    * by adding the internal base to the value of this field. If set to 31, ba
    * nk address bit 2 is set to 0.
    *  PSU_DDRC_ADDRMAP1_ADDRMAP_BANK_B2                           0x1f

    * Selects the HIF address bits used as bank address bit 1. Valid Range: 0
    * to 30 Internal Base: 3 The selected HIF address bit for each of the bank
    *  address bits is determined by adding the internal base to the value of
    * this field.
    *  PSU_DDRC_ADDRMAP1_ADDRMAP_BANK_B1                           0xa

    * Selects the HIF address bits used as bank address bit 0. Valid Range: 0
    * to 30 Internal Base: 2 The selected HIF address bit for each of the bank
    *  address bits is determined by adding the internal base to the value of
    * this field.
    *  PSU_DDRC_ADDRMAP1_ADDRMAP_BANK_B0                           0xa

    * Address Map Register 1
    * (OFFSET, MASK, VALUE)      (0XFD070204, 0x001F1F1FU ,0x001F0A0AU)
    */
	PSU_Mask_Write(DDRC_ADDRMAP1_OFFSET, 0x001F1F1FU, 0x001F0A0AU);
/*##################################################################### */

    /*
    * Register : ADDRMAP2 @ 0XFD070208

    * - Full bus width mode: Selects the HIF address bit used as column addres
    * s bit 5. - Half bus width mode: Selects the HIF address bit used as colu
    * mn address bit 6. - Quarter bus width mode: Selects the HIF address bit
    * used as column address bit 7 . Valid Range: 0 to 7, and 15 Internal Base
    * : 5 The selected HIF address bit is determined by adding the internal ba
    * se to the value of this field. If set to 15, this column address bit is
    * set to 0.
    *  PSU_DDRC_ADDRMAP2_ADDRMAP_COL_B5                            0x0

    * - Full bus width mode: Selects the HIF address bit used as column addres
    * s bit 4. - Half bus width mode: Selects the HIF address bit used as colu
    * mn address bit 5. - Quarter bus width mode: Selects the HIF address bit
    * used as column address bit 6. Valid Range: 0 to 7, and 15 Internal Base:
    *  4 The selected HIF address bit is determined by adding the internal bas
    * e to the value of this field. If set to 15, this column address bit is s
    * et to 0.
    *  PSU_DDRC_ADDRMAP2_ADDRMAP_COL_B4                            0x0

    * - Full bus width mode: Selects the HIF address bit used as column addres
    * s bit 3. - Half bus width mode: Selects the HIF address bit used as colu
    * mn address bit 4. - Quarter bus width mode: Selects the HIF address bit
    * used as column address bit 5. Valid Range: 0 to 7 Internal Base: 3 The s
    * elected HIF address bit is determined by adding the internal base to the
    *  value of this field. Note, if UMCTL2_INCL_ARB=1 and MEMC_BURST_LENGTH=1
    * 6, it is required to program this to 0, hence register does not exist in
    *  this case.
    *  PSU_DDRC_ADDRMAP2_ADDRMAP_COL_B3                            0x0

    * - Full bus width mode: Selects the HIF address bit used as column addres
    * s bit 2. - Half bus width mode: Selects the HIF address bit used as colu
    * mn address bit 3. - Quarter bus width mode: Selects the HIF address bit
    * used as column address bit 4. Valid Range: 0 to 7 Internal Base: 2 The s
    * elected HIF address bit is determined by adding the internal base to the
    *  value of this field. Note, if UMCTL2_INCL_ARB=1 and MEMC_BURST_LENGTH=8
    *  or 16, it is required to program this to 0.
    *  PSU_DDRC_ADDRMAP2_ADDRMAP_COL_B2                            0x0

    * Address Map Register 2
    * (OFFSET, MASK, VALUE)      (0XFD070208, 0x0F0F0F0FU ,0x00000000U)
    */
	PSU_Mask_Write(DDRC_ADDRMAP2_OFFSET, 0x0F0F0F0FU, 0x00000000U);
/*##################################################################### */

    /*
    * Register : ADDRMAP3 @ 0XFD07020C

    * - Full bus width mode: Selects the HIF address bit used as column addres
    * s bit 9. - Half bus width mode: Selects the HIF address bit used as colu
    * mn address bit 11 (10 in LPDDR2/LPDDR3 mode). - Quarter bus width mode:
    * Selects the HIF address bit used as column address bit 13 (11 in LPDDR2/
    * LPDDR3 mode). Valid Range: 0 to 7, and 15 Internal Base: 9 The selected
    * HIF address bit is determined by adding the internal base to the value o
    * f this field. If set to 15, this column address bit is set to 0. Note: P
    * er JEDEC DDR2/3/mDDR specification, column address bit 10 is reserved fo
    * r indicating auto-precharge, and hence no source address bit can be mapp
    * ed to column address bit 10. In LPDDR2/LPDDR3, there is a dedicated bit
    * for auto-precharge in the CA bus and hence column bit 10 is used.
    *  PSU_DDRC_ADDRMAP3_ADDRMAP_COL_B9                            0x0

    * - Full bus width mode: Selects the HIF address bit used as column addres
    * s bit 8. - Half bus width mode: Selects the HIF address bit used as colu
    * mn address bit 9. - Quarter bus width mode: Selects the HIF address bit
    * used as column address bit 11 (10 in LPDDR2/LPDDR3 mode). Valid Range: 0
    *  to 7, and 15 Internal Base: 8 The selected HIF address bit is determine
    * d by adding the internal base to the value of this field. If set to 15,
    * this column address bit is set to 0. Note: Per JEDEC DDR2/3/mDDR specifi
    * cation, column address bit 10 is reserved for indicating auto-precharge,
    *  and hence no source address bit can be mapped to column address bit 10.
    *  In LPDDR2/LPDDR3, there is a dedicated bit for auto-precharge in the CA
    *  bus and hence column bit 10 is used.
    *  PSU_DDRC_ADDRMAP3_ADDRMAP_COL_B8                            0x0

    * - Full bus width mode: Selects the HIF address bit used as column addres
    * s bit 7. - Half bus width mode: Selects the HIF address bit used as colu
    * mn address bit 8. - Quarter bus width mode: Selects the HIF address bit
    * used as column address bit 9. Valid Range: 0 to 7, and 15 Internal Base:
    *  7 The selected HIF address bit is determined by adding the internal bas
    * e to the value of this field. If set to 15, this column address bit is s
    * et to 0.
    *  PSU_DDRC_ADDRMAP3_ADDRMAP_COL_B7                            0x0

    * - Full bus width mode: Selects the HIF address bit used as column addres
    * s bit 6. - Half bus width mode: Selects the HIF address bit used as colu
    * mn address bit 7. - Quarter bus width mode: Selects the HIF address bit
    * used as column address bit 8. Valid Range: 0 to 7, and 15 Internal Base:
    *  6 The selected HIF address bit is determined by adding the internal bas
    * e to the value of this field. If set to 15, this column address bit is s
    * et to 0.
    *  PSU_DDRC_ADDRMAP3_ADDRMAP_COL_B6                            0x0

    * Address Map Register 3
    * (OFFSET, MASK, VALUE)      (0XFD07020C, 0x0F0F0F0FU ,0x00000000U)
    */
	PSU_Mask_Write(DDRC_ADDRMAP3_OFFSET, 0x0F0F0F0FU, 0x00000000U);
/*##################################################################### */

    /*
    * Register : ADDRMAP4 @ 0XFD070210

    * - Full bus width mode: Selects the HIF address bit used as column addres
    * s bit 13 (11 in LPDDR2/LPDDR3 mode). - Half bus width mode: Unused. To m
    * ake it unused, this should be tied to 4'hF. - Quarter bus width mode: Un
    * used. To make it unused, this must be tied to 4'hF. Valid Range: 0 to 7,
    *  and 15 Internal Base: 11 The selected HIF address bit is determined by
    * adding the internal base to the value of this field. If set to 15, this
    * column address bit is set to 0. Note: Per JEDEC DDR2/3/mDDR specificatio
    * n, column address bit 10 is reserved for indicating auto-precharge, and
    * hence no source address bit can be mapped to column address bit 10. In L
    * PDDR2/LPDDR3, there is a dedicated bit for auto-precharge in the CA bus
    * and hence column bit 10 is used.
    *  PSU_DDRC_ADDRMAP4_ADDRMAP_COL_B11                           0xf

    * - Full bus width mode: Selects the HIF address bit used as column addres
    * s bit 11 (10 in LPDDR2/LPDDR3 mode). - Half bus width mode: Selects the
    * HIF address bit used as column address bit 13 (11 in LPDDR2/LPDDR3 mode)
    * . - Quarter bus width mode: UNUSED. To make it unused, this must be tied
    *  to 4'hF. Valid Range: 0 to 7, and 15 Internal Base: 10 The selected HIF
    *  address bit is determined by adding the internal base to the value of t
    * his field. If set to 15, this column address bit is set to 0. Note: Per
    * JEDEC DDR2/3/mDDR specification, column address bit 10 is reserved for i
    * ndicating auto-precharge, and hence no source address bit can be mapped
    * to column address bit 10. In LPDDR2/LPDDR3, there is a dedicated bit for
    *  auto-precharge in the CA bus and hence column bit 10 is used.
    *  PSU_DDRC_ADDRMAP4_ADDRMAP_COL_B10                           0xf

    * Address Map Register 4
    * (OFFSET, MASK, VALUE)      (0XFD070210, 0x00000F0FU ,0x00000F0FU)
    */
	PSU_Mask_Write(DDRC_ADDRMAP4_OFFSET, 0x00000F0FU, 0x00000F0FU);
/*##################################################################### */

    /*
    * Register : ADDRMAP5 @ 0XFD070214

    * Selects the HIF address bit used as row address bit 11. Valid Range: 0 t
    * o 11, and 15 Internal Base: 17 The selected HIF address bit is determine
    * d by adding the internal base to the value of this field. If set to 15,
    * row address bit 11 is set to 0.
    *  PSU_DDRC_ADDRMAP5_ADDRMAP_ROW_B11                           0x8

    * Selects the HIF address bits used as row address bits 2 to 10. Valid Ran
    * ge: 0 to 11, and 15 Internal Base: 8 (for row address bit 2), 9 (for row
    *  address bit 3), 10 (for row address bit 4) etc increasing to 16 (for ro
    * w address bit 10) The selected HIF address bit for each of the row addre
    * ss bits is determined by adding the internal base to the value of this f
    * ield. When value 15 is used the values of row address bits 2 to 10 are d
    * efined by registers ADDRMAP9, ADDRMAP10, ADDRMAP11.
    *  PSU_DDRC_ADDRMAP5_ADDRMAP_ROW_B2_10                         0xf

    * Selects the HIF address bits used as row address bit 1. Valid Range: 0 t
    * o 11 Internal Base: 7 The selected HIF address bit for each of the row a
    * ddress bits is determined by adding the internal base to the value of th
    * is field.
    *  PSU_DDRC_ADDRMAP5_ADDRMAP_ROW_B1                            0x8

    * Selects the HIF address bits used as row address bit 0. Valid Range: 0 t
    * o 11 Internal Base: 6 The selected HIF address bit for each of the row a
    * ddress bits is determined by adding the internal base to the value of th
    * is field.
    *  PSU_DDRC_ADDRMAP5_ADDRMAP_ROW_B0                            0x8

    * Address Map Register 5
    * (OFFSET, MASK, VALUE)      (0XFD070214, 0x0F0F0F0FU ,0x080F0808U)
    */
	PSU_Mask_Write(DDRC_ADDRMAP5_OFFSET, 0x0F0F0F0FU, 0x080F0808U);
/*##################################################################### */

    /*
    * Register : ADDRMAP6 @ 0XFD070218

    * Set this to 1 if there is an LPDDR3 SDRAM 6Gb or 12Gb device in use. - 1
    *  - LPDDR3 SDRAM 6Gb/12Gb device in use. Every address having row[14:13]=
    * =2'b11 is considered as invalid - 0 - non-LPDDR3 6Gb/12Gb device in use.
    *  All addresses are valid Present only in designs configured to support L
    * PDDR3.
    *  PSU_DDRC_ADDRMAP6_LPDDR3_6GB_12GB                           0x0

    * Selects the HIF address bit used as row address bit 15. Valid Range: 0 t
    * o 11, and 15 Internal Base: 21 The selected HIF address bit is determine
    * d by adding the internal base to the value of this field. If set to 15,
    * row address bit 15 is set to 0.
    *  PSU_DDRC_ADDRMAP6_ADDRMAP_ROW_B15                           0xf

    * Selects the HIF address bit used as row address bit 14. Valid Range: 0 t
    * o 11, and 15 Internal Base: 20 The selected HIF address bit is determine
    * d by adding the internal base to the value of this field. If set to 15,
    * row address bit 14 is set to 0.
    *  PSU_DDRC_ADDRMAP6_ADDRMAP_ROW_B14                           0x8

    * Selects the HIF address bit used as row address bit 13. Valid Range: 0 t
    * o 11, and 15 Internal Base: 19 The selected HIF address bit is determine
    * d by adding the internal base to the value of this field. If set to 15,
    * row address bit 13 is set to 0.
    *  PSU_DDRC_ADDRMAP6_ADDRMAP_ROW_B13                           0x8

    * Selects the HIF address bit used as row address bit 12. Valid Range: 0 t
    * o 11, and 15 Internal Base: 18 The selected HIF address bit is determine
    * d by adding the internal base to the value of this field. If set to 15,
    * row address bit 12 is set to 0.
    *  PSU_DDRC_ADDRMAP6_ADDRMAP_ROW_B12                           0x8

    * Address Map Register 6
    * (OFFSET, MASK, VALUE)      (0XFD070218, 0x8F0F0F0FU ,0x0F080808U)
    */
	PSU_Mask_Write(DDRC_ADDRMAP6_OFFSET, 0x8F0F0F0FU, 0x0F080808U);
/*##################################################################### */

    /*
    * Register : ADDRMAP7 @ 0XFD07021C

    * Selects the HIF address bit used as row address bit 17. Valid Range: 0 t
    * o 10, and 15 Internal Base: 23 The selected HIF address bit is determine
    * d by adding the internal base to the value of this field. If set to 15,
    * row address bit 17 is set to 0.
    *  PSU_DDRC_ADDRMAP7_ADDRMAP_ROW_B17                           0xf

    * Selects the HIF address bit used as row address bit 16. Valid Range: 0 t
    * o 11, and 15 Internal Base: 22 The selected HIF address bit is determine
    * d by adding the internal base to the value of this field. If set to 15,
    * row address bit 16 is set to 0.
    *  PSU_DDRC_ADDRMAP7_ADDRMAP_ROW_B16                           0xf

    * Address Map Register 7
    * (OFFSET, MASK, VALUE)      (0XFD07021C, 0x00000F0FU ,0x00000F0FU)
    */
	PSU_Mask_Write(DDRC_ADDRMAP7_OFFSET, 0x00000F0FU, 0x00000F0FU);
/*##################################################################### */

    /*
    * Register : ADDRMAP8 @ 0XFD070220

    * Selects the HIF address bits used as bank group address bit 1. Valid Ran
    * ge: 0 to 30, and 31 Internal Base: 3 The selected HIF address bit for ea
    * ch of the bank group address bits is determined by adding the internal b
    * ase to the value of this field. If set to 31, bank group address bit 1 i
    * s set to 0.
    *  PSU_DDRC_ADDRMAP8_ADDRMAP_BG_B1                             0x8

    * Selects the HIF address bits used as bank group address bit 0. Valid Ran
    * ge: 0 to 30 Internal Base: 2 The selected HIF address bit for each of th
    * e bank group address bits is determined by adding the internal base to t
    * he value of this field.
    *  PSU_DDRC_ADDRMAP8_ADDRMAP_BG_B0                             0x8

    * Address Map Register 8
    * (OFFSET, MASK, VALUE)      (0XFD070220, 0x00001F1FU ,0x00000808U)
    */
	PSU_Mask_Write(DDRC_ADDRMAP8_OFFSET, 0x00001F1FU, 0x00000808U);
/*##################################################################### */

    /*
    * Register : ADDRMAP9 @ 0XFD070224

    * Selects the HIF address bits used as row address bit 5. Valid Range: 0 t
    * o 11 Internal Base: 11 The selected HIF address bit for each of the row
    * address bits is determined by adding the internal base to the value of t
    * his field. This register field is used only when ADDRMAP5.addrmap_row_b2
    * _10 is set to value 15.
    *  PSU_DDRC_ADDRMAP9_ADDRMAP_ROW_B5                            0x8

    * Selects the HIF address bits used as row address bit 4. Valid Range: 0 t
    * o 11 Internal Base: 10 The selected HIF address bit for each of the row
    * address bits is determined by adding the internal base to the value of t
    * his field. This register field is used only when ADDRMAP5.addrmap_row_b2
    * _10 is set to value 15.
    *  PSU_DDRC_ADDRMAP9_ADDRMAP_ROW_B4                            0x8

    * Selects the HIF address bits used as row address bit 3. Valid Range: 0 t
    * o 11 Internal Base: 9 The selected HIF address bit for each of the row a
    * ddress bits is determined by adding the internal base to the value of th
    * is field. This register field is used only when ADDRMAP5.addrmap_row_b2_
    * 10 is set to value 15.
    *  PSU_DDRC_ADDRMAP9_ADDRMAP_ROW_B3                            0x8

    * Selects the HIF address bits used as row address bit 2. Valid Range: 0 t
    * o 11 Internal Base: 8 The selected HIF address bit for each of the row a
    * ddress bits is determined by adding the internal base to the value of th
    * is field. This register field is used only when ADDRMAP5.addrmap_row_b2_
    * 10 is set to value 15.
    *  PSU_DDRC_ADDRMAP9_ADDRMAP_ROW_B2                            0x8

    * Address Map Register 9
    * (OFFSET, MASK, VALUE)      (0XFD070224, 0x0F0F0F0FU ,0x08080808U)
    */
	PSU_Mask_Write(DDRC_ADDRMAP9_OFFSET, 0x0F0F0F0FU, 0x08080808U);
/*##################################################################### */

    /*
    * Register : ADDRMAP10 @ 0XFD070228

    * Selects the HIF address bits used as row address bit 9. Valid Range: 0 t
    * o 11 Internal Base: 15 The selected HIF address bit for each of the row
    * address bits is determined by adding the internal base to the value of t
    * his field. This register field is used only when ADDRMAP5.addrmap_row_b2
    * _10 is set to value 15.
    *  PSU_DDRC_ADDRMAP10_ADDRMAP_ROW_B9                           0x8

    * Selects the HIF address bits used as row address bit 8. Valid Range: 0 t
    * o 11 Internal Base: 14 The selected HIF address bit for each of the row
    * address bits is determined by adding the internal base to the value of t
    * his field. This register field is used only when ADDRMAP5.addrmap_row_b2
    * _10 is set to value 15.
    *  PSU_DDRC_ADDRMAP10_ADDRMAP_ROW_B8                           0x8

    * Selects the HIF address bits used as row address bit 7. Valid Range: 0 t
    * o 11 Internal Base: 13 The selected HIF address bit for each of the row
    * address bits is determined by adding the internal base to the value of t
    * his field. This register field is used only when ADDRMAP5.addrmap_row_b2
    * _10 is set to value 15.
    *  PSU_DDRC_ADDRMAP10_ADDRMAP_ROW_B7                           0x8

    * Selects the HIF address bits used as row address bit 6. Valid Range: 0 t
    * o 11 Internal Base: 12 The selected HIF address bit for each of the row
    * address bits is determined by adding the internal base to the value of t
    * his field. This register field is used only when ADDRMAP5.addrmap_row_b2
    * _10 is set to value 15.
    *  PSU_DDRC_ADDRMAP10_ADDRMAP_ROW_B6                           0x8

    * Address Map Register 10
    * (OFFSET, MASK, VALUE)      (0XFD070228, 0x0F0F0F0FU ,0x08080808U)
    */
	PSU_Mask_Write(DDRC_ADDRMAP10_OFFSET, 0x0F0F0F0FU, 0x08080808U);
/*##################################################################### */

    /*
    * Register : ADDRMAP11 @ 0XFD07022C

    * Selects the HIF address bits used as row address bit 10. Valid Range: 0
    * to 11 Internal Base: 16 The selected HIF address bit for each of the row
    *  address bits is determined by adding the internal base to the value of
    * this field. This register field is used only when ADDRMAP5.addrmap_row_b
    * 2_10 is set to value 15.
    *  PSU_DDRC_ADDRMAP11_ADDRMAP_ROW_B10                          0x8

    * Address Map Register 11
    * (OFFSET, MASK, VALUE)      (0XFD07022C, 0x0000000FU ,0x00000008U)
    */
	PSU_Mask_Write(DDRC_ADDRMAP11_OFFSET, 0x0000000FU, 0x00000008U);
/*##################################################################### */

    /*
    * Register : ODTCFG @ 0XFD070240

    * Cycles to hold ODT for a write command. The minimum supported value is 2
    * . Recommended values: DDR2: - BL8: 0x5 (DDR2-400/533/667), 0x6 (DDR2-800
    * ), 0x7 (DDR2-1066) - BL4: 0x3 (DDR2-400/533/667), 0x4 (DDR2-800), 0x5 (D
    * DR2-1066) DDR3: - BL8: 0x6 DDR4: - BL8: 5 + WR_PREAMBLE + CRC_MODE WR_PR
    * EAMBLE = 1 (1tCK write preamble), 2 (2tCK write preamble) CRC_MODE = 0 (
    * not CRC mode), 1 (CRC mode) LPDDR3: - BL8: 7 + RU(tODTon(max)/tCK)
    *  PSU_DDRC_ODTCFG_WR_ODT_HOLD                                 0x6

    * The delay, in clock cycles, from issuing a write command to setting ODT
    * values associated with that command. ODT setting must remain constant fo
    * r the entire time that DQS is driven by the uMCTL2. Recommended values:
    * DDR2: - CWL + AL - 3 (DDR2-400/533/667), CWL + AL - 4 (DDR2-800), CWL +
    * AL - 5 (DDR2-1066) If (CWL + AL - 3 < 0), uMCTL2 does not support ODT fo
    * r write operation. DDR3: - 0x0 DDR4: - DFITMG1.dfi_t_cmd_lat (to adjust
    * for CAL mode) LPDDR3: - WL - 1 - RU(tODTon(max)/tCK))
    *  PSU_DDRC_ODTCFG_WR_ODT_DELAY                                0x0

    * Cycles to hold ODT for a read command. The minimum supported value is 2.
    *  Recommended values: DDR2: - BL8: 0x6 (not DDR2-1066), 0x7 (DDR2-1066) -
    *  BL4: 0x4 (not DDR2-1066), 0x5 (DDR2-1066) DDR3: - BL8 - 0x6 DDR4: - BL8
    * : 5 + RD_PREAMBLE RD_PREAMBLE = 1 (1tCK write preamble), 2 (2tCK write p
    * reamble) LPDDR3: - BL8: 5 + RU(tDQSCK(max)/tCK) - RD(tDQSCK(min)/tCK) +
    * RU(tODTon(max)/tCK)
    *  PSU_DDRC_ODTCFG_RD_ODT_HOLD                                 0x6

    * The delay, in clock cycles, from issuing a read command to setting ODT v
    * alues associated with that command. ODT setting must remain constant for
    *  the entire time that DQS is driven by the uMCTL2. Recommended values: D
    * DR2: - CL + AL - 4 (not DDR2-1066), CL + AL - 5 (DDR2-1066) If (CL + AL
    * - 4 < 0), uMCTL2 does not support ODT for read operation. DDR3: - CL - C
    * WL DDR4: - CL - CWL - RD_PREAMBLE + WR_PREAMBLE + DFITMG1.dfi_t_cmd_lat
    * (to adjust for CAL mode) WR_PREAMBLE = 1 (1tCK write preamble), 2 (2tCK
    * write preamble) RD_PREAMBLE = 1 (1tCK write preamble), 2 (2tCK write pre
    * amble) If (CL - CWL - RD_PREAMBLE + WR_PREAMBLE) < 0, uMCTL2 does not su
    * pport ODT for read operation. LPDDR3: - RL + RD(tDQSCK(min)/tCK) - 1 - R
    * U(tODTon(max)/tCK)
    *  PSU_DDRC_ODTCFG_RD_ODT_DELAY                                0x0

    * ODT Configuration Register
    * (OFFSET, MASK, VALUE)      (0XFD070240, 0x0F1F0F7CU ,0x06000600U)
    */
	PSU_Mask_Write(DDRC_ODTCFG_OFFSET, 0x0F1F0F7CU, 0x06000600U);
/*##################################################################### */

    /*
    * Register : ODTMAP @ 0XFD070244

    * Indicates which remote ODTs must be turned on during a read from rank 1.
    *  Each rank has a remote ODT (in the SDRAM) which can be turned on by set
    * ting the appropriate bit here. Rank 0 is controlled by the LSB; rank 1 i
    * s controlled by bit next to the LSB, etc. For each rank, set its bit to
    * 1 to enable its ODT. Present only in configurations that have 2 or more
    * ranks
    *  PSU_DDRC_ODTMAP_RANK1_RD_ODT                                0x0

    * Indicates which remote ODTs must be turned on during a write to rank 1.
    * Each rank has a remote ODT (in the SDRAM) which can be turned on by sett
    * ing the appropriate bit here. Rank 0 is controlled by the LSB; rank 1 is
    *  controlled by bit next to the LSB, etc. For each rank, set its bit to 1
    *  to enable its ODT. Present only in configurations that have 2 or more r
    * anks
    *  PSU_DDRC_ODTMAP_RANK1_WR_ODT                                0x0

    * Indicates which remote ODTs must be turned on during a read from rank 0.
    *  Each rank has a remote ODT (in the SDRAM) which can be turned on by set
    * ting the appropriate bit here. Rank 0 is controlled by the LSB; rank 1 i
    * s controlled by bit next to the LSB, etc. For each rank, set its bit to
    * 1 to enable its ODT.
    *  PSU_DDRC_ODTMAP_RANK0_RD_ODT                                0x0

    * Indicates which remote ODTs must be turned on during a write to rank 0.
    * Each rank has a remote ODT (in the SDRAM) which can be turned on by sett
    * ing the appropriate bit here. Rank 0 is controlled by the LSB; rank 1 is
    *  controlled by bit next to the LSB, etc. For each rank, set its bit to 1
    *  to enable its ODT.
    *  PSU_DDRC_ODTMAP_RANK0_WR_ODT                                0x1

    * ODT/Rank Map Register
    * (OFFSET, MASK, VALUE)      (0XFD070244, 0x00003333U ,0x00000001U)
    */
	PSU_Mask_Write(DDRC_ODTMAP_OFFSET, 0x00003333U, 0x00000001U);
/*##################################################################### */

    /*
    * Register : SCHED @ 0XFD070250

    * When the preferred transaction store is empty for these many clock cycle
    * s, switch to the alternate transaction store if it is non-empty. The rea
    * d transaction store (both high and low priority) is the default preferre
    * d transaction store and the write transaction store is the alternative s
    * tore. When prefer write over read is set this is reversed. 0x0 is a lega
    * l value for this register. When set to 0x0, the transaction store switch
    * ing will happen immediately when the switching conditions become true. F
    * OR PERFORMANCE ONLY
    *  PSU_DDRC_SCHED_RDWR_IDLE_GAP                                0x1

    * UNUSED
    *  PSU_DDRC_SCHED_GO2CRITICAL_HYSTERESIS                       0x0

    * Number of entries in the low priority transaction store is this value +
    * 1. (MEMC_NO_OF_ENTRY - (SCHED.lpr_num_entries + 1)) is the number of ent
    * ries available for the high priority transaction store. Setting this to
    * maximum value allocates all entries to low priority transaction store. S
    * etting this to 0 allocates 1 entry to low priority transaction store and
    *  the rest to high priority transaction store. Note: In ECC configuration
    * s, the numbers of write and low priority read credits issued is one less
    *  than in the non-ECC case. One entry each is reserved in the write and l
    * ow-priority read CAMs for storing the RMW requests arising out of single
    *  bit error correction RMW operation.
    *  PSU_DDRC_SCHED_LPR_NUM_ENTRIES                              0x20

    * If true, bank is kept open only while there are page hit transactions av
    * ailable in the CAM to that bank. The last read or write command in the C
    * AM with a bank and page hit will be executed with auto-precharge if SCHE
    * D1.pageclose_timer=0. Even if this register set to 1 and SCHED1.pageclos
    * e_timer is set to 0, explicit precharge (and not auto-precharge) may be
    * issued in some cases where there is a mode switch between Write and Read
    *  or between LPR and HPR. The Read and Write commands that are executed a
    * s part of the ECC scrub requests are also executed without auto-precharg
    * e. If false, the bank remains open until there is a need to close it (to
    *  open a different page, or for page timeout or refresh timeout) - also k
    * nown as open page policy. The open page policy can be overridden by sett
    * ing the per-command-autopre bit on the HIF interface (hif_cmd_autopre).
    * The pageclose feature provids a midway between Open and Close page polic
    * ies. FOR PERFORMANCE ONLY.
    *  PSU_DDRC_SCHED_PAGECLOSE                                    0x0

    * If set then the bank selector prefers writes over reads. FOR DEBUG ONLY.
    *  PSU_DDRC_SCHED_PREFER_WRITE                                 0x0

    * Active low signal. When asserted ('0'), all incoming transactions are fo
    * rced to low priority. This implies that all High Priority Read (HPR) and
    *  Variable Priority Read commands (VPR) will be treated as Low Priority R
    * ead (LPR) commands. On the write side, all Variable Priority Write (VPW)
    *  commands will be treated as Normal Priority Write (NPW) commands. Forci
    * ng the incoming transactions to low priority implicitly turns off Bypass
    *  path for read commands. FOR PERFORMANCE ONLY.
    *  PSU_DDRC_SCHED_FORCE_LOW_PRI_N                              0x1

    * Scheduler Control Register
    * (OFFSET, MASK, VALUE)      (0XFD070250, 0x7FFF3F07U ,0x01002001U)
    */
	PSU_Mask_Write(DDRC_SCHED_OFFSET, 0x7FFF3F07U, 0x01002001U);
/*##################################################################### */

    /*
    * Register : PERFLPR1 @ 0XFD070264

    * Number of transactions that are serviced once the LPR queue goes critica
    * l is the smaller of: - (a) This number - (b) Number of transactions avai
    * lable. Unit: Transaction. FOR PERFORMANCE ONLY.
    *  PSU_DDRC_PERFLPR1_LPR_XACT_RUN_LENGTH                       0x8

    * Number of clocks that the LPR queue can be starved before it goes critic
    * al. The minimum valid functional value for this register is 0x1. Program
    * ming it to 0x0 will disable the starvation functionality; during normal
    * operation, this function should not be disabled as it will cause excessi
    * ve latencies. Unit: Clock cycles. FOR PERFORMANCE ONLY.
    *  PSU_DDRC_PERFLPR1_LPR_MAX_STARVE                            0x40

    * Low Priority Read CAM Register 1
    * (OFFSET, MASK, VALUE)      (0XFD070264, 0xFF00FFFFU ,0x08000040U)
    */
	PSU_Mask_Write(DDRC_PERFLPR1_OFFSET, 0xFF00FFFFU, 0x08000040U);
/*##################################################################### */

    /*
    * Register : PERFWR1 @ 0XFD07026C

    * Number of transactions that are serviced once the WR queue goes critical
    *  is the smaller of: - (a) This number - (b) Number of transactions avail
    * able. Unit: Transaction. FOR PERFORMANCE ONLY.
    *  PSU_DDRC_PERFWR1_W_XACT_RUN_LENGTH                          0x8

    * Number of clocks that the WR queue can be starved before it goes critica
    * l. The minimum valid functional value for this register is 0x1. Programm
    * ing it to 0x0 will disable the starvation functionality; during normal o
    * peration, this function should not be disabled as it will cause excessiv
    * e latencies. Unit: Clock cycles. FOR PERFORMANCE ONLY.
    *  PSU_DDRC_PERFWR1_W_MAX_STARVE                               0x40

    * Write CAM Register 1
    * (OFFSET, MASK, VALUE)      (0XFD07026C, 0xFF00FFFFU ,0x08000040U)
    */
	PSU_Mask_Write(DDRC_PERFWR1_OFFSET, 0xFF00FFFFU, 0x08000040U);
/*##################################################################### */

    /*
    * Register : DQMAP0 @ 0XFD070280

    * DQ nibble map for DQ bits [12-15] Present only in designs configured to
    * support DDR4.
    *  PSU_DDRC_DQMAP0_DQ_NIBBLE_MAP_12_15                         0x0

    * DQ nibble map for DQ bits [8-11] Present only in designs configured to s
    * upport DDR4.
    *  PSU_DDRC_DQMAP0_DQ_NIBBLE_MAP_8_11                          0x0

    * DQ nibble map for DQ bits [4-7] Present only in designs configured to su
    * pport DDR4.
    *  PSU_DDRC_DQMAP0_DQ_NIBBLE_MAP_4_7                           0x0

    * DQ nibble map for DQ bits [0-3] Present only in designs configured to su
    * pport DDR4.
    *  PSU_DDRC_DQMAP0_DQ_NIBBLE_MAP_0_3                           0x0

    * DQ Map Register 0
    * (OFFSET, MASK, VALUE)      (0XFD070280, 0xFFFFFFFFU ,0x00000000U)
    */
	PSU_Mask_Write(DDRC_DQMAP0_OFFSET, 0xFFFFFFFFU, 0x00000000U);
/*##################################################################### */

    /*
    * Register : DQMAP1 @ 0XFD070284

    * DQ nibble map for DQ bits [28-31] Present only in designs configured to
    * support DDR4.
    *  PSU_DDRC_DQMAP1_DQ_NIBBLE_MAP_28_31                         0x0

    * DQ nibble map for DQ bits [24-27] Present only in designs configured to
    * support DDR4.
    *  PSU_DDRC_DQMAP1_DQ_NIBBLE_MAP_24_27                         0x0

    * DQ nibble map for DQ bits [20-23] Present only in designs configured to
    * support DDR4.
    *  PSU_DDRC_DQMAP1_DQ_NIBBLE_MAP_20_23                         0x0

    * DQ nibble map for DQ bits [16-19] Present only in designs configured to
    * support DDR4.
    *  PSU_DDRC_DQMAP1_DQ_NIBBLE_MAP_16_19                         0x0

    * DQ Map Register 1
    * (OFFSET, MASK, VALUE)      (0XFD070284, 0xFFFFFFFFU ,0x00000000U)
    */
	PSU_Mask_Write(DDRC_DQMAP1_OFFSET, 0xFFFFFFFFU, 0x00000000U);
/*##################################################################### */

    /*
    * Register : DQMAP2 @ 0XFD070288

    * DQ nibble map for DQ bits [44-47] Present only in designs configured to
    * support DDR4.
    *  PSU_DDRC_DQMAP2_DQ_NIBBLE_MAP_44_47                         0x0

    * DQ nibble map for DQ bits [40-43] Present only in designs configured to
    * support DDR4.
    *  PSU_DDRC_DQMAP2_DQ_NIBBLE_MAP_40_43                         0x0

    * DQ nibble map for DQ bits [36-39] Present only in designs configured to
    * support DDR4.
    *  PSU_DDRC_DQMAP2_DQ_NIBBLE_MAP_36_39                         0x0

    * DQ nibble map for DQ bits [32-35] Present only in designs configured to
    * support DDR4.
    *  PSU_DDRC_DQMAP2_DQ_NIBBLE_MAP_32_35                         0x0

    * DQ Map Register 2
    * (OFFSET, MASK, VALUE)      (0XFD070288, 0xFFFFFFFFU ,0x00000000U)
    */
	PSU_Mask_Write(DDRC_DQMAP2_OFFSET, 0xFFFFFFFFU, 0x00000000U);
/*##################################################################### */

    /*
    * Register : DQMAP3 @ 0XFD07028C

    * DQ nibble map for DQ bits [60-63] Present only in designs configured to
    * support DDR4.
    *  PSU_DDRC_DQMAP3_DQ_NIBBLE_MAP_60_63                         0x0

    * DQ nibble map for DQ bits [56-59] Present only in designs configured to
    * support DDR4.
    *  PSU_DDRC_DQMAP3_DQ_NIBBLE_MAP_56_59                         0x0

    * DQ nibble map for DQ bits [52-55] Present only in designs configured to
    * support DDR4.
    *  PSU_DDRC_DQMAP3_DQ_NIBBLE_MAP_52_55                         0x0

    * DQ nibble map for DQ bits [48-51] Present only in designs configured to
    * support DDR4.
    *  PSU_DDRC_DQMAP3_DQ_NIBBLE_MAP_48_51                         0x0

    * DQ Map Register 3
    * (OFFSET, MASK, VALUE)      (0XFD07028C, 0xFFFFFFFFU ,0x00000000U)
    */
	PSU_Mask_Write(DDRC_DQMAP3_OFFSET, 0xFFFFFFFFU, 0x00000000U);
/*##################################################################### */

    /*
    * Register : DQMAP4 @ 0XFD070290

    * DQ nibble map for DIMM ECC check bits [4-7] Present only in designs conf
    * igured to support DDR4.
    *  PSU_DDRC_DQMAP4_DQ_NIBBLE_MAP_CB_4_7                        0x0

    * DQ nibble map for DIMM ECC check bits [0-3] Present only in designs conf
    * igured to support DDR4.
    *  PSU_DDRC_DQMAP4_DQ_NIBBLE_MAP_CB_0_3                        0x0

    * DQ Map Register 4
    * (OFFSET, MASK, VALUE)      (0XFD070290, 0x0000FFFFU ,0x00000000U)
    */
	PSU_Mask_Write(DDRC_DQMAP4_OFFSET, 0x0000FFFFU, 0x00000000U);
/*##################################################################### */

    /*
    * Register : DQMAP5 @ 0XFD070294

    * All even ranks have the same DQ mapping controled by DQMAP0-4 register a
    * s rank 0. This register provides DQ swap function for all odd ranks to s
    * upport CRC feature. rank based DQ swapping is: swap bit 0 with 1, swap b
    * it 2 with 3, swap bit 4 with 5 and swap bit 6 with 7. 1: Disable rank ba
    * sed DQ swapping 0: Enable rank based DQ swapping Present only in designs
    *  configured to support DDR4.
    *  PSU_DDRC_DQMAP5_DIS_DQ_RANK_SWAP                            0x1

    * DQ Map Register 5
    * (OFFSET, MASK, VALUE)      (0XFD070294, 0x00000001U ,0x00000001U)
    */
	PSU_Mask_Write(DDRC_DQMAP5_OFFSET, 0x00000001U, 0x00000001U);
/*##################################################################### */

    /*
    * Register : DBG0 @ 0XFD070300

    * When this is set to '0', auto-precharge is disabled for the flushed comm
    * and in a collision case. Collision cases are write followed by read to s
    * ame address, read followed by write to same address, or write followed b
    * y write to same address with DBG0.dis_wc bit = 1 (where same address com
    * parisons exclude the two address bits representing critical word). FOR D
    * EBUG ONLY.
    *  PSU_DDRC_DBG0_DIS_COLLISION_PAGE_OPT                        0x0

    * When 1, disable write combine. FOR DEBUG ONLY
    *  PSU_DDRC_DBG0_DIS_WC                                        0x0

    * Debug Register 0
    * (OFFSET, MASK, VALUE)      (0XFD070300, 0x00000011U ,0x00000000U)
    */
	PSU_Mask_Write(DDRC_DBG0_OFFSET, 0x00000011U, 0x00000000U);
/*##################################################################### */

    /*
    * Register : DBGCMD @ 0XFD07030C

    * Setting this register bit to 1 allows refresh and ZQCS commands to be tr
    * iggered from hardware via the IOs ext_*. If set to 1, the fields DBGCMD.
    * zq_calib_short and DBGCMD.rank*_refresh have no function, and are ignore
    * d by the uMCTL2 logic. Setting this register bit to 0 allows refresh and
    *  ZQCS to be triggered from software, via the fields DBGCMD.zq_calib_shor
    * t and DBGCMD.rank*_refresh. If set to 0, the hardware pins ext_* have no
    *  function, and are ignored by the uMCTL2 logic. This register is static,
    *  and may only be changed when the DDRC reset signal, core_ddrc_rstn, is
    * asserted (0).
    *  PSU_DDRC_DBGCMD_HW_REF_ZQ_EN                                0x0

    * Setting this register bit to 1 indicates to the uMCTL2 to issue a dfi_ct
    * rlupd_req to the PHY. When this request is stored in the uMCTL2, the bit
    *  is automatically cleared. This operation must only be performed when DF
    * IUPD0.dis_auto_ctrlupd=1.
    *  PSU_DDRC_DBGCMD_CTRLUPD                                     0x0

    * Setting this register bit to 1 indicates to the uMCTL2 to issue a ZQCS (
    * ZQ calibration short)/MPC(ZQ calibration) command to the SDRAM. When thi
    * s request is stored in the uMCTL2, the bit is automatically cleared. Thi
    * s operation can be performed only when ZQCTL0.dis_auto_zq=1. It is recom
    * mended NOT to set this register bit if in Init operating mode. This regi
    * ster bit is ignored when in Self-Refresh(except LPDDR4) and SR-Powerdown
    * (LPDDR4) and Deep power-down operating modes and Maximum Power Saving Mo
    * de.
    *  PSU_DDRC_DBGCMD_ZQ_CALIB_SHORT                              0x0

    * Setting this register bit to 1 indicates to the uMCTL2 to issue a refres
    * h to rank 1. Writing to this bit causes DBGSTAT.rank1_refresh_busy to be
    *  set. When DBGSTAT.rank1_refresh_busy is cleared, the command has been s
    * tored in uMCTL2. This operation can be performed only when RFSHCTL3.dis_
    * auto_refresh=1. It is recommended NOT to set this register bit if in Ini
    * t or Deep power-down operating modes or Maximum Power Saving Mode.
    *  PSU_DDRC_DBGCMD_RANK1_REFRESH                               0x0

    * Setting this register bit to 1 indicates to the uMCTL2 to issue a refres
    * h to rank 0. Writing to this bit causes DBGSTAT.rank0_refresh_busy to be
    *  set. When DBGSTAT.rank0_refresh_busy is cleared, the command has been s
    * tored in uMCTL2. This operation can be performed only when RFSHCTL3.dis_
    * auto_refresh=1. It is recommended NOT to set this register bit if in Ini
    * t or Deep power-down operating modes or Maximum Power Saving Mode.
    *  PSU_DDRC_DBGCMD_RANK0_REFRESH                               0x0

    * Command Debug Register
    * (OFFSET, MASK, VALUE)      (0XFD07030C, 0x80000033U ,0x00000000U)
    */
	PSU_Mask_Write(DDRC_DBGCMD_OFFSET, 0x80000033U, 0x00000000U);
/*##################################################################### */

    /*
    * Register : SWCTL @ 0XFD070320

    * Enable quasi-dynamic register programming outside reset. Program registe
    * r to 0 to enable quasi-dynamic programming. Set back register to 1 once
    * programming is done.
    *  PSU_DDRC_SWCTL_SW_DONE                                      0x0

    * Software register programming control enable
    * (OFFSET, MASK, VALUE)      (0XFD070320, 0x00000001U ,0x00000000U)
    */
	PSU_Mask_Write(DDRC_SWCTL_OFFSET, 0x00000001U, 0x00000000U);
/*##################################################################### */

    /*
    * Register : PCCFG @ 0XFD070400

    * Burst length expansion mode. By default (i.e. bl_exp_mode==0) XPI expand
    * s every AXI burst into multiple HIF commands, using the memory burst len
    * gth as a unit. If set to 1, then XPI will use half of the memory burst l
    * ength as a unit. This applies to both reads and writes. When MSTR.data_b
    * us_width==00, setting bl_exp_mode to 1 has no effect. This can be used i
    * n cases where Partial Writes is enabled (UMCTL2_PARTIAL_WR=1) and DBG0.d
    * is_wc=1, in order to avoid or minimize t_ccd_l penalty in DDR4 and t_ccd
    * _mw penalty in LPDDR4. Note that if DBICTL.reg_ddrc_dm_en=0, functionali
    * ty is not supported in the following cases: - UMCTL2_PARTIAL_WR=0 - UMCT
    * L2_PARTIAL_WR=1, MSTR.reg_ddrc_data_bus_width=01, MEMC_BURST_LENGTH=8 an
    * d MSTR.reg_ddrc_burst_rdwr=1000 (LPDDR4 only) - UMCTL2_PARTIAL_WR=1, MST
    * R.reg_ddrc_data_bus_width=01, MEMC_BURST_LENGTH=4 and MSTR.reg_ddrc_burs
    * t_rdwr=0100 (DDR4 only), with either MSTR.reg_ddrc_burstchop=0 or CRCPAR
    * CTL1.reg_ddrc_crc_enable=1 Functionality is also not supported if Shared
    * -AC is enabled
    *  PSU_DDRC_PCCFG_BL_EXP_MODE                                  0x0

    * Page match four limit. If set to 1, limits the number of consecutive sam
    * e page DDRC transactions that can be granted by the Port Arbiter to four
    *  when Page Match feature is enabled. If set to 0, there is no limit impo
    * sed on number of consecutive same page DDRC transactions.
    *  PSU_DDRC_PCCFG_PAGEMATCH_LIMIT                              0x0

    * If set to 1 (enabled), sets co_gs_go2critical_wr and co_gs_go2critical_l
    * pr/co_gs_go2critical_hpr signals going to DDRC based on urgent input (aw
    * urgent, arurgent) coming from AXI master. If set to 0 (disabled), co_gs_
    * go2critical_wr and co_gs_go2critical_lpr/co_gs_go2critical_hpr signals a
    * t DDRC are driven to 1b'0.
    *  PSU_DDRC_PCCFG_GO2CRITICAL_EN                               0x1

    * Port Common Configuration Register
    * (OFFSET, MASK, VALUE)      (0XFD070400, 0x00000111U ,0x00000001U)
    */
	PSU_Mask_Write(DDRC_PCCFG_OFFSET, 0x00000111U, 0x00000001U);
/*##################################################################### */

    /*
    * Register : PCFGR_0 @ 0XFD070404

    * If set to 1, enables the Page Match feature. If enabled, once a requesti
    * ng port is granted, the port is continued to be granted if the following
    *  immediate commands are to the same memory page (same bank and same row)
    * . See also related PCCFG.pagematch_limit register.
    *  PSU_DDRC_PCFGR_0_RD_PORT_PAGEMATCH_EN                       0x0

    * If set to 1, enables the AXI urgent sideband signal (arurgent). When ena
    * bled and arurgent is asserted by the master, that port becomes the highe
    * st priority and co_gs_go2critical_lpr/co_gs_go2critical_hpr signal to DD
    * RC is asserted if enabled in PCCFG.go2critical_en register. Note that ar
    * urgent signal can be asserted anytime and as long as required which is i
    * ndependent of address handshaking (it is not associated with any particu
    * lar command).
    *  PSU_DDRC_PCFGR_0_RD_PORT_URGENT_EN                          0x1

    * If set to 1, enables aging function for the read channel of the port.
    *  PSU_DDRC_PCFGR_0_RD_PORT_AGING_EN                           0x0

    * Determines the initial load value of read aging counters. These counters
    *  will be parallel loaded after reset, or after each grant to the corresp
    * onding port. The aging counters down-count every clock cycle where the p
    * ort is requesting but not granted. The higher significant 5-bits of the
    * read aging counter sets the priority of the read channel of a given port
    * . Port's priority will increase as the higher significant 5-bits of the
    * counter starts to decrease. When the aging counter becomes 0, the corres
    * ponding port channel will have the highest priority level (timeout condi
    * tion - Priority0). For multi-port configurations, the aging counters can
    * not be used to set port priorities when external dynamic priority inputs
    *  (arqos) are enabled (timeout is still applicable). For single port conf
    * igurations, the aging counters are only used when they timeout (become 0
    * ) to force read-write direction switching. In this case, external dynami
    * c priority input, arqos (for reads only) can still be used to set the DD
    * RC read priority (2 priority levels: low priority read - LPR, high prior
    * ity read - HPR) on a command by command basis. Note: The two LSBs of thi
    * s register field are tied internally to 2'b00.
    *  PSU_DDRC_PCFGR_0_RD_PORT_PRIORITY                           0xf

    * Port n Configuration Read Register
    * (OFFSET, MASK, VALUE)      (0XFD070404, 0x000073FFU ,0x0000200FU)
    */
	PSU_Mask_Write(DDRC_PCFGR_0_OFFSET, 0x000073FFU, 0x0000200FU);
/*##################################################################### */

    /*
    * Register : PCFGW_0 @ 0XFD070408

    * If set to 1, enables the Page Match feature. If enabled, once a requesti
    * ng port is granted, the port is continued to be granted if the following
    *  immediate commands are to the same memory page (same bank and same row)
    * . See also related PCCFG.pagematch_limit register.
    *  PSU_DDRC_PCFGW_0_WR_PORT_PAGEMATCH_EN                       0x0

    * If set to 1, enables the AXI urgent sideband signal (awurgent). When ena
    * bled and awurgent is asserted by the master, that port becomes the highe
    * st priority and co_gs_go2critical_wr signal to DDRC is asserted if enabl
    * ed in PCCFG.go2critical_en register. Note that awurgent signal can be as
    * serted anytime and as long as required which is independent of address h
    * andshaking (it is not associated with any particular command).
    *  PSU_DDRC_PCFGW_0_WR_PORT_URGENT_EN                          0x1

    * If set to 1, enables aging function for the write channel of the port.
    *  PSU_DDRC_PCFGW_0_WR_PORT_AGING_EN                           0x0

    * Determines the initial load value of write aging counters. These counter
    * s will be parallel loaded after reset, or after each grant to the corres
    * ponding port. The aging counters down-count every clock cycle where the
    * port is requesting but not granted. The higher significant 5-bits of the
    *  write aging counter sets the initial priority of the write channel of a
    *  given port. Port's priority will increase as the higher significant 5-b
    * its of the counter starts to decrease. When the aging counter becomes 0,
    *  the corresponding port channel will have the highest priority level. Fo
    * r multi-port configurations, the aging counters cannot be used to set po
    * rt priorities when external dynamic priority inputs (awqos) are enabled
    * (timeout is still applicable). For single port configurations, the aging
    *  counters are only used when they timeout (become 0) to force read-write
    *  direction switching. Note: The two LSBs of this register field are tied
    *  internally to 2'b00.
    *  PSU_DDRC_PCFGW_0_WR_PORT_PRIORITY                           0xf

    * Port n Configuration Write Register
    * (OFFSET, MASK, VALUE)      (0XFD070408, 0x000073FFU ,0x0000200FU)
    */
	PSU_Mask_Write(DDRC_PCFGW_0_OFFSET, 0x000073FFU, 0x0000200FU);
/*##################################################################### */

    /*
    * Register : PCTRL_0 @ 0XFD070490

    * Enables port n.
    *  PSU_DDRC_PCTRL_0_PORT_EN                                    0x1

    * Port n Control Register
    * (OFFSET, MASK, VALUE)      (0XFD070490, 0x00000001U ,0x00000001U)
    */
	PSU_Mask_Write(DDRC_PCTRL_0_OFFSET, 0x00000001U, 0x00000001U);
/*##################################################################### */

    /*
    * Register : PCFGQOS0_0 @ 0XFD070494

    * This bitfield indicates the traffic class of region 1. Valid values are:
    *  0 : LPR, 1: VPR, 2: HPR. For dual address queue configurations, region1
    *  maps to the blue address queue. In this case, valid values are 0: LPR a
    * nd 1: VPR only. When VPR support is disabled (UMCTL2_VPR_EN = 0) and tra
    * ffic class of region 1 is set to 1 (VPR), VPR traffic is aliased to LPR
    * traffic.
    *  PSU_DDRC_PCFGQOS0_0_RQOS_MAP_REGION1                        0x2

    * This bitfield indicates the traffic class of region 0. Valid values are:
    *  0: LPR, 1: VPR, 2: HPR. For dual address queue configurations, region 0
    *  maps to the blue address queue. In this case, valid values are: 0: LPR
    * and 1: VPR only. When VPR support is disabled (UMCTL2_VPR_EN = 0) and tr
    * affic class of region0 is set to 1 (VPR), VPR traffic is aliased to LPR
    * traffic.
    *  PSU_DDRC_PCFGQOS0_0_RQOS_MAP_REGION0                        0x0

    * Separation level1 indicating the end of region0 mapping; start of region
    * 0 is 0. Possible values for level1 are 0 to 13 (for dual RAQ) or 0 to 14
    *  (for single RAQ) which corresponds to arqos. Note that for PA, arqos va
    * lues are used directly as port priorities, where the higher the value co
    * rresponds to higher port priority. All of the map_level* registers must
    * be set to distinct values.
    *  PSU_DDRC_PCFGQOS0_0_RQOS_MAP_LEVEL1                         0xb

    * Port n Read QoS Configuration Register 0
    * (OFFSET, MASK, VALUE)      (0XFD070494, 0x0033000FU ,0x0020000BU)
    */
	PSU_Mask_Write(DDRC_PCFGQOS0_0_OFFSET, 0x0033000FU, 0x0020000BU);
/*##################################################################### */

    /*
    * Register : PCFGQOS1_0 @ 0XFD070498

    * Specifies the timeout value for transactions mapped to the red address q
    * ueue.
    *  PSU_DDRC_PCFGQOS1_0_RQOS_MAP_TIMEOUTR                       0x0

    * Specifies the timeout value for transactions mapped to the blue address
    * queue.
    *  PSU_DDRC_PCFGQOS1_0_RQOS_MAP_TIMEOUTB                       0x0

    * Port n Read QoS Configuration Register 1
    * (OFFSET, MASK, VALUE)      (0XFD070498, 0x07FF07FFU ,0x00000000U)
    */
	PSU_Mask_Write(DDRC_PCFGQOS1_0_OFFSET, 0x07FF07FFU, 0x00000000U);
/*##################################################################### */

    /*
    * Register : PCFGR_1 @ 0XFD0704B4

    * If set to 1, enables the Page Match feature. If enabled, once a requesti
    * ng port is granted, the port is continued to be granted if the following
    *  immediate commands are to the same memory page (same bank and same row)
    * . See also related PCCFG.pagematch_limit register.
    *  PSU_DDRC_PCFGR_1_RD_PORT_PAGEMATCH_EN                       0x0

    * If set to 1, enables the AXI urgent sideband signal (arurgent). When ena
    * bled and arurgent is asserted by the master, that port becomes the highe
    * st priority and co_gs_go2critical_lpr/co_gs_go2critical_hpr signal to DD
    * RC is asserted if enabled in PCCFG.go2critical_en register. Note that ar
    * urgent signal can be asserted anytime and as long as required which is i
    * ndependent of address handshaking (it is not associated with any particu
    * lar command).
    *  PSU_DDRC_PCFGR_1_RD_PORT_URGENT_EN                          0x1

    * If set to 1, enables aging function for the read channel of the port.
    *  PSU_DDRC_PCFGR_1_RD_PORT_AGING_EN                           0x0

    * Determines the initial load value of read aging counters. These counters
    *  will be parallel loaded after reset, or after each grant to the corresp
    * onding port. The aging counters down-count every clock cycle where the p
    * ort is requesting but not granted. The higher significant 5-bits of the
    * read aging counter sets the priority of the read channel of a given port
    * . Port's priority will increase as the higher significant 5-bits of the
    * counter starts to decrease. When the aging counter becomes 0, the corres
    * ponding port channel will have the highest priority level (timeout condi
    * tion - Priority0). For multi-port configurations, the aging counters can
    * not be used to set port priorities when external dynamic priority inputs
    *  (arqos) are enabled (timeout is still applicable). For single port conf
    * igurations, the aging counters are only used when they timeout (become 0
    * ) to force read-write direction switching. In this case, external dynami
    * c priority input, arqos (for reads only) can still be used to set the DD
    * RC read priority (2 priority levels: low priority read - LPR, high prior
    * ity read - HPR) on a command by command basis. Note: The two LSBs of thi
    * s register field are tied internally to 2'b00.
    *  PSU_DDRC_PCFGR_1_RD_PORT_PRIORITY                           0xf

    * Port n Configuration Read Register
    * (OFFSET, MASK, VALUE)      (0XFD0704B4, 0x000073FFU ,0x0000200FU)
    */
	PSU_Mask_Write(DDRC_PCFGR_1_OFFSET, 0x000073FFU, 0x0000200FU);
/*##################################################################### */

    /*
    * Register : PCFGW_1 @ 0XFD0704B8

    * If set to 1, enables the Page Match feature. If enabled, once a requesti
    * ng port is granted, the port is continued to be granted if the following
    *  immediate commands are to the same memory page (same bank and same row)
    * . See also related PCCFG.pagematch_limit register.
    *  PSU_DDRC_PCFGW_1_WR_PORT_PAGEMATCH_EN                       0x0

    * If set to 1, enables the AXI urgent sideband signal (awurgent). When ena
    * bled and awurgent is asserted by the master, that port becomes the highe
    * st priority and co_gs_go2critical_wr signal to DDRC is asserted if enabl
    * ed in PCCFG.go2critical_en register. Note that awurgent signal can be as
    * serted anytime and as long as required which is independent of address h
    * andshaking (it is not associated with any particular command).
    *  PSU_DDRC_PCFGW_1_WR_PORT_URGENT_EN                          0x1

    * If set to 1, enables aging function for the write channel of the port.
    *  PSU_DDRC_PCFGW_1_WR_PORT_AGING_EN                           0x0

    * Determines the initial load value of write aging counters. These counter
    * s will be parallel loaded after reset, or after each grant to the corres
    * ponding port. The aging counters down-count every clock cycle where the
    * port is requesting but not granted. The higher significant 5-bits of the
    *  write aging counter sets the initial priority of the write channel of a
    *  given port. Port's priority will increase as the higher significant 5-b
    * its of the counter starts to decrease. When the aging counter becomes 0,
    *  the corresponding port channel will have the highest priority level. Fo
    * r multi-port configurations, the aging counters cannot be used to set po
    * rt priorities when external dynamic priority inputs (awqos) are enabled
    * (timeout is still applicable). For single port configurations, the aging
    *  counters are only used when they timeout (become 0) to force read-write
    *  direction switching. Note: The two LSBs of this register field are tied
    *  internally to 2'b00.
    *  PSU_DDRC_PCFGW_1_WR_PORT_PRIORITY                           0xf

    * Port n Configuration Write Register
    * (OFFSET, MASK, VALUE)      (0XFD0704B8, 0x000073FFU ,0x0000200FU)
    */
	PSU_Mask_Write(DDRC_PCFGW_1_OFFSET, 0x000073FFU, 0x0000200FU);
/*##################################################################### */

    /*
    * Register : PCTRL_1 @ 0XFD070540

    * Enables port n.
    *  PSU_DDRC_PCTRL_1_PORT_EN                                    0x1

    * Port n Control Register
    * (OFFSET, MASK, VALUE)      (0XFD070540, 0x00000001U ,0x00000001U)
    */
	PSU_Mask_Write(DDRC_PCTRL_1_OFFSET, 0x00000001U, 0x00000001U);
/*##################################################################### */

    /*
    * Register : PCFGQOS0_1 @ 0XFD070544

    * This bitfield indicates the traffic class of region2. For dual address q
    * ueue configurations, region2 maps to the red address queue. Valid values
    *  are 1: VPR and 2: HPR only. When VPR support is disabled (UMCTL2_VPR_EN
    *  = 0) and traffic class of region2 is set to 1 (VPR), VPR traffic is ali
    * ased to LPR traffic.
    *  PSU_DDRC_PCFGQOS0_1_RQOS_MAP_REGION2                        0x2

    * This bitfield indicates the traffic class of region 1. Valid values are:
    *  0 : LPR, 1: VPR, 2: HPR. For dual address queue configurations, region1
    *  maps to the blue address queue. In this case, valid values are 0: LPR a
    * nd 1: VPR only. When VPR support is disabled (UMCTL2_VPR_EN = 0) and tra
    * ffic class of region 1 is set to 1 (VPR), VPR traffic is aliased to LPR
    * traffic.
    *  PSU_DDRC_PCFGQOS0_1_RQOS_MAP_REGION1                        0x0

    * This bitfield indicates the traffic class of region 0. Valid values are:
    *  0: LPR, 1: VPR, 2: HPR. For dual address queue configurations, region 0
    *  maps to the blue address queue. In this case, valid values are: 0: LPR
    * and 1: VPR only. When VPR support is disabled (UMCTL2_VPR_EN = 0) and tr
    * affic class of region0 is set to 1 (VPR), VPR traffic is aliased to LPR
    * traffic.
    *  PSU_DDRC_PCFGQOS0_1_RQOS_MAP_REGION0                        0x0

    * Separation level2 indicating the end of region1 mapping; start of region
    * 1 is (level1 + 1). Possible values for level2 are (level1 + 1) to 14 whi
    * ch corresponds to arqos. Region2 starts from (level2 + 1) up to 15. Note
    *  that for PA, arqos values are used directly as port priorities, where t
    * he higher the value corresponds to higher port priority. All of the map_
    * level* registers must be set to distinct values.
    *  PSU_DDRC_PCFGQOS0_1_RQOS_MAP_LEVEL2                         0xb

    * Separation level1 indicating the end of region0 mapping; start of region
    * 0 is 0. Possible values for level1 are 0 to 13 (for dual RAQ) or 0 to 14
    *  (for single RAQ) which corresponds to arqos. Note that for PA, arqos va
    * lues are used directly as port priorities, where the higher the value co
    * rresponds to higher port priority. All of the map_level* registers must
    * be set to distinct values.
    *  PSU_DDRC_PCFGQOS0_1_RQOS_MAP_LEVEL1                         0x3

    * Port n Read QoS Configuration Register 0
    * (OFFSET, MASK, VALUE)      (0XFD070544, 0x03330F0FU ,0x02000B03U)
    */
	PSU_Mask_Write(DDRC_PCFGQOS0_1_OFFSET, 0x03330F0FU, 0x02000B03U);
/*##################################################################### */

    /*
    * Register : PCFGQOS1_1 @ 0XFD070548

    * Specifies the timeout value for transactions mapped to the red address q
    * ueue.
    *  PSU_DDRC_PCFGQOS1_1_RQOS_MAP_TIMEOUTR                       0x0

    * Specifies the timeout value for transactions mapped to the blue address
    * queue.
    *  PSU_DDRC_PCFGQOS1_1_RQOS_MAP_TIMEOUTB                       0x0

    * Port n Read QoS Configuration Register 1
    * (OFFSET, MASK, VALUE)      (0XFD070548, 0x07FF07FFU ,0x00000000U)
    */
	PSU_Mask_Write(DDRC_PCFGQOS1_1_OFFSET, 0x07FF07FFU, 0x00000000U);
/*##################################################################### */

    /*
    * Register : PCFGR_2 @ 0XFD070564

    * If set to 1, enables the Page Match feature. If enabled, once a requesti
    * ng port is granted, the port is continued to be granted if the following
    *  immediate commands are to the same memory page (same bank and same row)
    * . See also related PCCFG.pagematch_limit register.
    *  PSU_DDRC_PCFGR_2_RD_PORT_PAGEMATCH_EN                       0x0

    * If set to 1, enables the AXI urgent sideband signal (arurgent). When ena
    * bled and arurgent is asserted by the master, that port becomes the highe
    * st priority and co_gs_go2critical_lpr/co_gs_go2critical_hpr signal to DD
    * RC is asserted if enabled in PCCFG.go2critical_en register. Note that ar
    * urgent signal can be asserted anytime and as long as required which is i
    * ndependent of address handshaking (it is not associated with any particu
    * lar command).
    *  PSU_DDRC_PCFGR_2_RD_PORT_URGENT_EN                          0x1

    * If set to 1, enables aging function for the read channel of the port.
    *  PSU_DDRC_PCFGR_2_RD_PORT_AGING_EN                           0x0

    * Determines the initial load value of read aging counters. These counters
    *  will be parallel loaded after reset, or after each grant to the corresp
    * onding port. The aging counters down-count every clock cycle where the p
    * ort is requesting but not granted. The higher significant 5-bits of the
    * read aging counter sets the priority of the read channel of a given port
    * . Port's priority will increase as the higher significant 5-bits of the
    * counter starts to decrease. When the aging counter becomes 0, the corres
    * ponding port channel will have the highest priority level (timeout condi
    * tion - Priority0). For multi-port configurations, the aging counters can
    * not be used to set port priorities when external dynamic priority inputs
    *  (arqos) are enabled (timeout is still applicable). For single port conf
    * igurations, the aging counters are only used when they timeout (become 0
    * ) to force read-write direction switching. In this case, external dynami
    * c priority input, arqos (for reads only) can still be used to set the DD
    * RC read priority (2 priority levels: low priority read - LPR, high prior
    * ity read - HPR) on a command by command basis. Note: The two LSBs of thi
    * s register field are tied internally to 2'b00.
    *  PSU_DDRC_PCFGR_2_RD_PORT_PRIORITY                           0xf

    * Port n Configuration Read Register
    * (OFFSET, MASK, VALUE)      (0XFD070564, 0x000073FFU ,0x0000200FU)
    */
	PSU_Mask_Write(DDRC_PCFGR_2_OFFSET, 0x000073FFU, 0x0000200FU);
/*##################################################################### */

    /*
    * Register : PCFGW_2 @ 0XFD070568

    * If set to 1, enables the Page Match feature. If enabled, once a requesti
    * ng port is granted, the port is continued to be granted if the following
    *  immediate commands are to the same memory page (same bank and same row)
    * . See also related PCCFG.pagematch_limit register.
    *  PSU_DDRC_PCFGW_2_WR_PORT_PAGEMATCH_EN                       0x0

    * If set to 1, enables the AXI urgent sideband signal (awurgent). When ena
    * bled and awurgent is asserted by the master, that port becomes the highe
    * st priority and co_gs_go2critical_wr signal to DDRC is asserted if enabl
    * ed in PCCFG.go2critical_en register. Note that awurgent signal can be as
    * serted anytime and as long as required which is independent of address h
    * andshaking (it is not associated with any particular command).
    *  PSU_DDRC_PCFGW_2_WR_PORT_URGENT_EN                          0x1

    * If set to 1, enables aging function for the write channel of the port.
    *  PSU_DDRC_PCFGW_2_WR_PORT_AGING_EN                           0x0

    * Determines the initial load value of write aging counters. These counter
    * s will be parallel loaded after reset, or after each grant to the corres
    * ponding port. The aging counters down-count every clock cycle where the
    * port is requesting but not granted. The higher significant 5-bits of the
    *  write aging counter sets the initial priority of the write channel of a
    *  given port. Port's priority will increase as the higher significant 5-b
    * its of the counter starts to decrease. When the aging counter becomes 0,
    *  the corresponding port channel will have the highest priority level. Fo
    * r multi-port configurations, the aging counters cannot be used to set po
    * rt priorities when external dynamic priority inputs (awqos) are enabled
    * (timeout is still applicable). For single port configurations, the aging
    *  counters are only used when they timeout (become 0) to force read-write
    *  direction switching. Note: The two LSBs of this register field are tied
    *  internally to 2'b00.
    *  PSU_DDRC_PCFGW_2_WR_PORT_PRIORITY                           0xf

    * Port n Configuration Write Register
    * (OFFSET, MASK, VALUE)      (0XFD070568, 0x000073FFU ,0x0000200FU)
    */
	PSU_Mask_Write(DDRC_PCFGW_2_OFFSET, 0x000073FFU, 0x0000200FU);
/*##################################################################### */

    /*
    * Register : PCTRL_2 @ 0XFD0705F0

    * Enables port n.
    *  PSU_DDRC_PCTRL_2_PORT_EN                                    0x1

    * Port n Control Register
    * (OFFSET, MASK, VALUE)      (0XFD0705F0, 0x00000001U ,0x00000001U)
    */
	PSU_Mask_Write(DDRC_PCTRL_2_OFFSET, 0x00000001U, 0x00000001U);
/*##################################################################### */

    /*
    * Register : PCFGQOS0_2 @ 0XFD0705F4

    * This bitfield indicates the traffic class of region2. For dual address q
    * ueue configurations, region2 maps to the red address queue. Valid values
    *  are 1: VPR and 2: HPR only. When VPR support is disabled (UMCTL2_VPR_EN
    *  = 0) and traffic class of region2 is set to 1 (VPR), VPR traffic is ali
    * ased to LPR traffic.
    *  PSU_DDRC_PCFGQOS0_2_RQOS_MAP_REGION2                        0x2

    * This bitfield indicates the traffic class of region 1. Valid values are:
    *  0 : LPR, 1: VPR, 2: HPR. For dual address queue configurations, region1
    *  maps to the blue address queue. In this case, valid values are 0: LPR a
    * nd 1: VPR only. When VPR support is disabled (UMCTL2_VPR_EN = 0) and tra
    * ffic class of region 1 is set to 1 (VPR), VPR traffic is aliased to LPR
    * traffic.
    *  PSU_DDRC_PCFGQOS0_2_RQOS_MAP_REGION1                        0x0

    * This bitfield indicates the traffic class of region 0. Valid values are:
    *  0: LPR, 1: VPR, 2: HPR. For dual address queue configurations, region 0
    *  maps to the blue address queue. In this case, valid values are: 0: LPR
    * and 1: VPR only. When VPR support is disabled (UMCTL2_VPR_EN = 0) and tr
    * affic class of region0 is set to 1 (VPR), VPR traffic is aliased to LPR
    * traffic.
    *  PSU_DDRC_PCFGQOS0_2_RQOS_MAP_REGION0                        0x0

    * Separation level2 indicating the end of region1 mapping; start of region
    * 1 is (level1 + 1). Possible values for level2 are (level1 + 1) to 14 whi
    * ch corresponds to arqos. Region2 starts from (level2 + 1) up to 15. Note
    *  that for PA, arqos values are used directly as port priorities, where t
    * he higher the value corresponds to higher port priority. All of the map_
    * level* registers must be set to distinct values.
    *  PSU_DDRC_PCFGQOS0_2_RQOS_MAP_LEVEL2                         0xb

    * Separation level1 indicating the end of region0 mapping; start of region
    * 0 is 0. Possible values for level1 are 0 to 13 (for dual RAQ) or 0 to 14
    *  (for single RAQ) which corresponds to arqos. Note that for PA, arqos va
    * lues are used directly as port priorities, where the higher the value co
    * rresponds to higher port priority. All of the map_level* registers must
    * be set to distinct values.
    *  PSU_DDRC_PCFGQOS0_2_RQOS_MAP_LEVEL1                         0x3

    * Port n Read QoS Configuration Register 0
    * (OFFSET, MASK, VALUE)      (0XFD0705F4, 0x03330F0FU ,0x02000B03U)
    */
	PSU_Mask_Write(DDRC_PCFGQOS0_2_OFFSET, 0x03330F0FU, 0x02000B03U);
/*##################################################################### */

    /*
    * Register : PCFGQOS1_2 @ 0XFD0705F8

    * Specifies the timeout value for transactions mapped to the red address q
    * ueue.
    *  PSU_DDRC_PCFGQOS1_2_RQOS_MAP_TIMEOUTR                       0x0

    * Specifies the timeout value for transactions mapped to the blue address
    * queue.
    *  PSU_DDRC_PCFGQOS1_2_RQOS_MAP_TIMEOUTB                       0x0

    * Port n Read QoS Configuration Register 1
    * (OFFSET, MASK, VALUE)      (0XFD0705F8, 0x07FF07FFU ,0x00000000U)
    */
	PSU_Mask_Write(DDRC_PCFGQOS1_2_OFFSET, 0x07FF07FFU, 0x00000000U);
/*##################################################################### */

    /*
    * Register : PCFGR_3 @ 0XFD070614

    * If set to 1, enables the Page Match feature. If enabled, once a requesti
    * ng port is granted, the port is continued to be granted if the following
    *  immediate commands are to the same memory page (same bank and same row)
    * . See also related PCCFG.pagematch_limit register.
    *  PSU_DDRC_PCFGR_3_RD_PORT_PAGEMATCH_EN                       0x0

    * If set to 1, enables the AXI urgent sideband signal (arurgent). When ena
    * bled and arurgent is asserted by the master, that port becomes the highe
    * st priority and co_gs_go2critical_lpr/co_gs_go2critical_hpr signal to DD
    * RC is asserted if enabled in PCCFG.go2critical_en register. Note that ar
    * urgent signal can be asserted anytime and as long as required which is i
    * ndependent of address handshaking (it is not associated with any particu
    * lar command).
    *  PSU_DDRC_PCFGR_3_RD_PORT_URGENT_EN                          0x1

    * If set to 1, enables aging function for the read channel of the port.
    *  PSU_DDRC_PCFGR_3_RD_PORT_AGING_EN                           0x0

    * Determines the initial load value of read aging counters. These counters
    *  will be parallel loaded after reset, or after each grant to the corresp
    * onding port. The aging counters down-count every clock cycle where the p
    * ort is requesting but not granted. The higher significant 5-bits of the
    * read aging counter sets the priority of the read channel of a given port
    * . Port's priority will increase as the higher significant 5-bits of the
    * counter starts to decrease. When the aging counter becomes 0, the corres
    * ponding port channel will have the highest priority level (timeout condi
    * tion - Priority0). For multi-port configurations, the aging counters can
    * not be used to set port priorities when external dynamic priority inputs
    *  (arqos) are enabled (timeout is still applicable). For single port conf
    * igurations, the aging counters are only used when they timeout (become 0
    * ) to force read-write direction switching. In this case, external dynami
    * c priority input, arqos (for reads only) can still be used to set the DD
    * RC read priority (2 priority levels: low priority read - LPR, high prior
    * ity read - HPR) on a command by command basis. Note: The two LSBs of thi
    * s register field are tied internally to 2'b00.
    *  PSU_DDRC_PCFGR_3_RD_PORT_PRIORITY                           0xf

    * Port n Configuration Read Register
    * (OFFSET, MASK, VALUE)      (0XFD070614, 0x000073FFU ,0x0000200FU)
    */
	PSU_Mask_Write(DDRC_PCFGR_3_OFFSET, 0x000073FFU, 0x0000200FU);
/*##################################################################### */

    /*
    * Register : PCFGW_3 @ 0XFD070618

    * If set to 1, enables the Page Match feature. If enabled, once a requesti
    * ng port is granted, the port is continued to be granted if the following
    *  immediate commands are to the same memory page (same bank and same row)
    * . See also related PCCFG.pagematch_limit register.
    *  PSU_DDRC_PCFGW_3_WR_PORT_PAGEMATCH_EN                       0x0

    * If set to 1, enables the AXI urgent sideband signal (awurgent). When ena
    * bled and awurgent is asserted by the master, that port becomes the highe
    * st priority and co_gs_go2critical_wr signal to DDRC is asserted if enabl
    * ed in PCCFG.go2critical_en register. Note that awurgent signal can be as
    * serted anytime and as long as required which is independent of address h
    * andshaking (it is not associated with any particular command).
    *  PSU_DDRC_PCFGW_3_WR_PORT_URGENT_EN                          0x1

    * If set to 1, enables aging function for the write channel of the port.
    *  PSU_DDRC_PCFGW_3_WR_PORT_AGING_EN                           0x0

    * Determines the initial load value of write aging counters. These counter
    * s will be parallel loaded after reset, or after each grant to the corres
    * ponding port. The aging counters down-count every clock cycle where the
    * port is requesting but not granted. The higher significant 5-bits of the
    *  write aging counter sets the initial priority of the write channel of a
    *  given port. Port's priority will increase as the higher significant 5-b
    * its of the counter starts to decrease. When the aging counter becomes 0,
    *  the corresponding port channel will have the highest priority level. Fo
    * r multi-port configurations, the aging counters cannot be used to set po
    * rt priorities when external dynamic priority inputs (awqos) are enabled
    * (timeout is still applicable). For single port configurations, the aging
    *  counters are only used when they timeout (become 0) to force read-write
    *  direction switching. Note: The two LSBs of this register field are tied
    *  internally to 2'b00.
    *  PSU_DDRC_PCFGW_3_WR_PORT_PRIORITY                           0xf

    * Port n Configuration Write Register
    * (OFFSET, MASK, VALUE)      (0XFD070618, 0x000073FFU ,0x0000200FU)
    */
	PSU_Mask_Write(DDRC_PCFGW_3_OFFSET, 0x000073FFU, 0x0000200FU);
/*##################################################################### */

    /*
    * Register : PCTRL_3 @ 0XFD0706A0

    * Enables port n.
    *  PSU_DDRC_PCTRL_3_PORT_EN                                    0x1

    * Port n Control Register
    * (OFFSET, MASK, VALUE)      (0XFD0706A0, 0x00000001U ,0x00000001U)
    */
	PSU_Mask_Write(DDRC_PCTRL_3_OFFSET, 0x00000001U, 0x00000001U);
/*##################################################################### */

    /*
    * Register : PCFGQOS0_3 @ 0XFD0706A4

    * This bitfield indicates the traffic class of region 1. Valid values are:
    *  0 : LPR, 1: VPR, 2: HPR. For dual address queue configurations, region1
    *  maps to the blue address queue. In this case, valid values are 0: LPR a
    * nd 1: VPR only. When VPR support is disabled (UMCTL2_VPR_EN = 0) and tra
    * ffic class of region 1 is set to 1 (VPR), VPR traffic is aliased to LPR
    * traffic.
    *  PSU_DDRC_PCFGQOS0_3_RQOS_MAP_REGION1                        0x1

    * This bitfield indicates the traffic class of region 0. Valid values are:
    *  0: LPR, 1: VPR, 2: HPR. For dual address queue configurations, region 0
    *  maps to the blue address queue. In this case, valid values are: 0: LPR
    * and 1: VPR only. When VPR support is disabled (UMCTL2_VPR_EN = 0) and tr
    * affic class of region0 is set to 1 (VPR), VPR traffic is aliased to LPR
    * traffic.
    *  PSU_DDRC_PCFGQOS0_3_RQOS_MAP_REGION0                        0x0

    * Separation level1 indicating the end of region0 mapping; start of region
    * 0 is 0. Possible values for level1 are 0 to 13 (for dual RAQ) or 0 to 14
    *  (for single RAQ) which corresponds to arqos. Note that for PA, arqos va
    * lues are used directly as port priorities, where the higher the value co
    * rresponds to higher port priority. All of the map_level* registers must
    * be set to distinct values.
    *  PSU_DDRC_PCFGQOS0_3_RQOS_MAP_LEVEL1                         0x3

    * Port n Read QoS Configuration Register 0
    * (OFFSET, MASK, VALUE)      (0XFD0706A4, 0x0033000FU ,0x00100003U)
    */
	PSU_Mask_Write(DDRC_PCFGQOS0_3_OFFSET, 0x0033000FU, 0x00100003U);
/*##################################################################### */

    /*
    * Register : PCFGQOS1_3 @ 0XFD0706A8

    * Specifies the timeout value for transactions mapped to the red address q
    * ueue.
    *  PSU_DDRC_PCFGQOS1_3_RQOS_MAP_TIMEOUTR                       0x0

    * Specifies the timeout value for transactions mapped to the blue address
    * queue.
    *  PSU_DDRC_PCFGQOS1_3_RQOS_MAP_TIMEOUTB                       0x4f

    * Port n Read QoS Configuration Register 1
    * (OFFSET, MASK, VALUE)      (0XFD0706A8, 0x07FF07FFU ,0x0000004FU)
    */
	PSU_Mask_Write(DDRC_PCFGQOS1_3_OFFSET, 0x07FF07FFU, 0x0000004FU);
/*##################################################################### */

    /*
    * Register : PCFGWQOS0_3 @ 0XFD0706AC

    * This bitfield indicates the traffic class of region 1. Valid values are:
    *  0: NPW, 1: VPW. When VPW support is disabled (UMCTL2_VPW_EN = 0) and tr
    * affic class of region 1 is set to 1 (VPW), VPW traffic is aliased to LPW
    *  traffic.
    *  PSU_DDRC_PCFGWQOS0_3_WQOS_MAP_REGION1                       0x1

    * This bitfield indicates the traffic class of region 0. Valid values are:
    *  0: NPW, 1: VPW. When VPW support is disabled (UMCTL2_VPW_EN = 0) and tr
    * affic class of region0 is set to 1 (VPW), VPW traffic is aliased to NPW
    * traffic.
    *  PSU_DDRC_PCFGWQOS0_3_WQOS_MAP_REGION0                       0x0

    * Separation level indicating the end of region0 mapping; start of region0
    *  is 0. Possible values for level1 are 0 to 14 which corresponds to awqos
    * . Note that for PA, awqos values are used directly as port priorities, w
    * here the higher the value corresponds to higher port priority.
    *  PSU_DDRC_PCFGWQOS0_3_WQOS_MAP_LEVEL                         0x3

    * Port n Write QoS Configuration Register 0
    * (OFFSET, MASK, VALUE)      (0XFD0706AC, 0x0033000FU ,0x00100003U)
    */
	PSU_Mask_Write(DDRC_PCFGWQOS0_3_OFFSET, 0x0033000FU, 0x00100003U);
/*##################################################################### */

    /*
    * Register : PCFGWQOS1_3 @ 0XFD0706B0

    * Specifies the timeout value for write transactions.
    *  PSU_DDRC_PCFGWQOS1_3_WQOS_MAP_TIMEOUT                       0x4f

    * Port n Write QoS Configuration Register 1
    * (OFFSET, MASK, VALUE)      (0XFD0706B0, 0x000007FFU ,0x0000004FU)
    */
	PSU_Mask_Write(DDRC_PCFGWQOS1_3_OFFSET, 0x000007FFU, 0x0000004FU);
/*##################################################################### */

    /*
    * Register : PCFGR_4 @ 0XFD0706C4

    * If set to 1, enables the Page Match feature. If enabled, once a requesti
    * ng port is granted, the port is continued to be granted if the following
    *  immediate commands are to the same memory page (same bank and same row)
    * . See also related PCCFG.pagematch_limit register.
    *  PSU_DDRC_PCFGR_4_RD_PORT_PAGEMATCH_EN                       0x0

    * If set to 1, enables the AXI urgent sideband signal (arurgent). When ena
    * bled and arurgent is asserted by the master, that port becomes the highe
    * st priority and co_gs_go2critical_lpr/co_gs_go2critical_hpr signal to DD
    * RC is asserted if enabled in PCCFG.go2critical_en register. Note that ar
    * urgent signal can be asserted anytime and as long as required which is i
    * ndependent of address handshaking (it is not associated with any particu
    * lar command).
    *  PSU_DDRC_PCFGR_4_RD_PORT_URGENT_EN                          0x1

    * If set to 1, enables aging function for the read channel of the port.
    *  PSU_DDRC_PCFGR_4_RD_PORT_AGING_EN                           0x0

    * Determines the initial load value of read aging counters. These counters
    *  will be parallel loaded after reset, or after each grant to the corresp
    * onding port. The aging counters down-count every clock cycle where the p
    * ort is requesting but not granted. The higher significant 5-bits of the
    * read aging counter sets the priority of the read channel of a given port
    * . Port's priority will increase as the higher significant 5-bits of the
    * counter starts to decrease. When the aging counter becomes 0, the corres
    * ponding port channel will have the highest priority level (timeout condi
    * tion - Priority0). For multi-port configurations, the aging counters can
    * not be used to set port priorities when external dynamic priority inputs
    *  (arqos) are enabled (timeout is still applicable). For single port conf
    * igurations, the aging counters are only used when they timeout (become 0
    * ) to force read-write direction switching. In this case, external dynami
    * c priority input, arqos (for reads only) can still be used to set the DD
    * RC read priority (2 priority levels: low priority read - LPR, high prior
    * ity read - HPR) on a command by command basis. Note: The two LSBs of thi
    * s register field are tied internally to 2'b00.
    *  PSU_DDRC_PCFGR_4_RD_PORT_PRIORITY                           0xf

    * Port n Configuration Read Register
    * (OFFSET, MASK, VALUE)      (0XFD0706C4, 0x000073FFU ,0x0000200FU)
    */
	PSU_Mask_Write(DDRC_PCFGR_4_OFFSET, 0x000073FFU, 0x0000200FU);
/*##################################################################### */

    /*
    * Register : PCFGW_4 @ 0XFD0706C8

    * If set to 1, enables the Page Match feature. If enabled, once a requesti
    * ng port is granted, the port is continued to be granted if the following
    *  immediate commands are to the same memory page (same bank and same row)
    * . See also related PCCFG.pagematch_limit register.
    *  PSU_DDRC_PCFGW_4_WR_PORT_PAGEMATCH_EN                       0x0

    * If set to 1, enables the AXI urgent sideband signal (awurgent). When ena
    * bled and awurgent is asserted by the master, that port becomes the highe
    * st priority and co_gs_go2critical_wr signal to DDRC is asserted if enabl
    * ed in PCCFG.go2critical_en register. Note that awurgent signal can be as
    * serted anytime and as long as required which is independent of address h
    * andshaking (it is not associated with any particular command).
    *  PSU_DDRC_PCFGW_4_WR_PORT_URGENT_EN                          0x1

    * If set to 1, enables aging function for the write channel of the port.
    *  PSU_DDRC_PCFGW_4_WR_PORT_AGING_EN                           0x0

    * Determines the initial load value of write aging counters. These counter
    * s will be parallel loaded after reset, or after each grant to the corres
    * ponding port. The aging counters down-count every clock cycle where the
    * port is requesting but not granted. The higher significant 5-bits of the
    *  write aging counter sets the initial priority of the write channel of a
    *  given port. Port's priority will increase as the higher significant 5-b
    * its of the counter starts to decrease. When the aging counter becomes 0,
    *  the corresponding port channel will have the highest priority level. Fo
    * r multi-port configurations, the aging counters cannot be used to set po
    * rt priorities when external dynamic priority inputs (awqos) are enabled
    * (timeout is still applicable). For single port configurations, the aging
    *  counters are only used when they timeout (become 0) to force read-write
    *  direction switching. Note: The two LSBs of this register field are tied
    *  internally to 2'b00.
    *  PSU_DDRC_PCFGW_4_WR_PORT_PRIORITY                           0xf

    * Port n Configuration Write Register
    * (OFFSET, MASK, VALUE)      (0XFD0706C8, 0x000073FFU ,0x0000200FU)
    */
	PSU_Mask_Write(DDRC_PCFGW_4_OFFSET, 0x000073FFU, 0x0000200FU);
/*##################################################################### */

    /*
    * Register : PCTRL_4 @ 0XFD070750

    * Enables port n.
    *  PSU_DDRC_PCTRL_4_PORT_EN                                    0x1

    * Port n Control Register
    * (OFFSET, MASK, VALUE)      (0XFD070750, 0x00000001U ,0x00000001U)
    */
	PSU_Mask_Write(DDRC_PCTRL_4_OFFSET, 0x00000001U, 0x00000001U);
/*##################################################################### */

    /*
    * Register : PCFGQOS0_4 @ 0XFD070754

    * This bitfield indicates the traffic class of region 1. Valid values are:
    *  0 : LPR, 1: VPR, 2: HPR. For dual address queue configurations, region1
    *  maps to the blue address queue. In this case, valid values are 0: LPR a
    * nd 1: VPR only. When VPR support is disabled (UMCTL2_VPR_EN = 0) and tra
    * ffic class of region 1 is set to 1 (VPR), VPR traffic is aliased to LPR
    * traffic.
    *  PSU_DDRC_PCFGQOS0_4_RQOS_MAP_REGION1                        0x1

    * This bitfield indicates the traffic class of region 0. Valid values are:
    *  0: LPR, 1: VPR, 2: HPR. For dual address queue configurations, region 0
    *  maps to the blue address queue. In this case, valid values are: 0: LPR
    * and 1: VPR only. When VPR support is disabled (UMCTL2_VPR_EN = 0) and tr
    * affic class of region0 is set to 1 (VPR), VPR traffic is aliased to LPR
    * traffic.
    *  PSU_DDRC_PCFGQOS0_4_RQOS_MAP_REGION0                        0x0

    * Separation level1 indicating the end of region0 mapping; start of region
    * 0 is 0. Possible values for level1 are 0 to 13 (for dual RAQ) or 0 to 14
    *  (for single RAQ) which corresponds to arqos. Note that for PA, arqos va
    * lues are used directly as port priorities, where the higher the value co
    * rresponds to higher port priority. All of the map_level* registers must
    * be set to distinct values.
    *  PSU_DDRC_PCFGQOS0_4_RQOS_MAP_LEVEL1                         0x3

    * Port n Read QoS Configuration Register 0
    * (OFFSET, MASK, VALUE)      (0XFD070754, 0x0033000FU ,0x00100003U)
    */
	PSU_Mask_Write(DDRC_PCFGQOS0_4_OFFSET, 0x0033000FU, 0x00100003U);
/*##################################################################### */

    /*
    * Register : PCFGQOS1_4 @ 0XFD070758

    * Specifies the timeout value for transactions mapped to the red address q
    * ueue.
    *  PSU_DDRC_PCFGQOS1_4_RQOS_MAP_TIMEOUTR                       0x0

    * Specifies the timeout value for transactions mapped to the blue address
    * queue.
    *  PSU_DDRC_PCFGQOS1_4_RQOS_MAP_TIMEOUTB                       0x4f

    * Port n Read QoS Configuration Register 1
    * (OFFSET, MASK, VALUE)      (0XFD070758, 0x07FF07FFU ,0x0000004FU)
    */
	PSU_Mask_Write(DDRC_PCFGQOS1_4_OFFSET, 0x07FF07FFU, 0x0000004FU);
/*##################################################################### */

    /*
    * Register : PCFGWQOS0_4 @ 0XFD07075C

    * This bitfield indicates the traffic class of region 1. Valid values are:
    *  0: NPW, 1: VPW. When VPW support is disabled (UMCTL2_VPW_EN = 0) and tr
    * affic class of region 1 is set to 1 (VPW), VPW traffic is aliased to LPW
    *  traffic.
    *  PSU_DDRC_PCFGWQOS0_4_WQOS_MAP_REGION1                       0x1

    * This bitfield indicates the traffic class of region 0. Valid values are:
    *  0: NPW, 1: VPW. When VPW support is disabled (UMCTL2_VPW_EN = 0) and tr
    * affic class of region0 is set to 1 (VPW), VPW traffic is aliased to NPW
    * traffic.
    *  PSU_DDRC_PCFGWQOS0_4_WQOS_MAP_REGION0                       0x0

    * Separation level indicating the end of region0 mapping; start of region0
    *  is 0. Possible values for level1 are 0 to 14 which corresponds to awqos
    * . Note that for PA, awqos values are used directly as port priorities, w
    * here the higher the value corresponds to higher port priority.
    *  PSU_DDRC_PCFGWQOS0_4_WQOS_MAP_LEVEL                         0x3

    * Port n Write QoS Configuration Register 0
    * (OFFSET, MASK, VALUE)      (0XFD07075C, 0x0033000FU ,0x00100003U)
    */
	PSU_Mask_Write(DDRC_PCFGWQOS0_4_OFFSET, 0x0033000FU, 0x00100003U);
/*##################################################################### */

    /*
    * Register : PCFGWQOS1_4 @ 0XFD070760

    * Specifies the timeout value for write transactions.
    *  PSU_DDRC_PCFGWQOS1_4_WQOS_MAP_TIMEOUT                       0x4f

    * Port n Write QoS Configuration Register 1
    * (OFFSET, MASK, VALUE)      (0XFD070760, 0x000007FFU ,0x0000004FU)
    */
	PSU_Mask_Write(DDRC_PCFGWQOS1_4_OFFSET, 0x000007FFU, 0x0000004FU);
/*##################################################################### */

    /*
    * Register : PCFGR_5 @ 0XFD070774

    * If set to 1, enables the Page Match feature. If enabled, once a requesti
    * ng port is granted, the port is continued to be granted if the following
    *  immediate commands are to the same memory page (same bank and same row)
    * . See also related PCCFG.pagematch_limit register.
    *  PSU_DDRC_PCFGR_5_RD_PORT_PAGEMATCH_EN                       0x0

    * If set to 1, enables the AXI urgent sideband signal (arurgent). When ena
    * bled and arurgent is asserted by the master, that port becomes the highe
    * st priority and co_gs_go2critical_lpr/co_gs_go2critical_hpr signal to DD
    * RC is asserted if enabled in PCCFG.go2critical_en register. Note that ar
    * urgent signal can be asserted anytime and as long as required which is i
    * ndependent of address handshaking (it is not associated with any particu
    * lar command).
    *  PSU_DDRC_PCFGR_5_RD_PORT_URGENT_EN                          0x1

    * If set to 1, enables aging function for the read channel of the port.
    *  PSU_DDRC_PCFGR_5_RD_PORT_AGING_EN                           0x0

    * Determines the initial load value of read aging counters. These counters
    *  will be parallel loaded after reset, or after each grant to the corresp
    * onding port. The aging counters down-count every clock cycle where the p
    * ort is requesting but not granted. The higher significant 5-bits of the
    * read aging counter sets the priority of the read channel of a given port
    * . Port's priority will increase as the higher significant 5-bits of the
    * counter starts to decrease. When the aging counter becomes 0, the corres
    * ponding port channel will have the highest priority level (timeout condi
    * tion - Priority0). For multi-port configurations, the aging counters can
    * not be used to set port priorities when external dynamic priority inputs
    *  (arqos) are enabled (timeout is still applicable). For single port conf
    * igurations, the aging counters are only used when they timeout (become 0
    * ) to force read-write direction switching. In this case, external dynami
    * c priority input, arqos (for reads only) can still be used to set the DD
    * RC read priority (2 priority levels: low priority read - LPR, high prior
    * ity read - HPR) on a command by command basis. Note: The two LSBs of thi
    * s register field are tied internally to 2'b00.
    *  PSU_DDRC_PCFGR_5_RD_PORT_PRIORITY                           0xf

    * Port n Configuration Read Register
    * (OFFSET, MASK, VALUE)      (0XFD070774, 0x000073FFU ,0x0000200FU)
    */
	PSU_Mask_Write(DDRC_PCFGR_5_OFFSET, 0x000073FFU, 0x0000200FU);
/*##################################################################### */

    /*
    * Register : PCFGW_5 @ 0XFD070778

    * If set to 1, enables the Page Match feature. If enabled, once a requesti
    * ng port is granted, the port is continued to be granted if the following
    *  immediate commands are to the same memory page (same bank and same row)
    * . See also related PCCFG.pagematch_limit register.
    *  PSU_DDRC_PCFGW_5_WR_PORT_PAGEMATCH_EN                       0x0

    * If set to 1, enables the AXI urgent sideband signal (awurgent). When ena
    * bled and awurgent is asserted by the master, that port becomes the highe
    * st priority and co_gs_go2critical_wr signal to DDRC is asserted if enabl
    * ed in PCCFG.go2critical_en register. Note that awurgent signal can be as
    * serted anytime and as long as required which is independent of address h
    * andshaking (it is not associated with any particular command).
    *  PSU_DDRC_PCFGW_5_WR_PORT_URGENT_EN                          0x1

    * If set to 1, enables aging function for the write channel of the port.
    *  PSU_DDRC_PCFGW_5_WR_PORT_AGING_EN                           0x0

    * Determines the initial load value of write aging counters. These counter
    * s will be parallel loaded after reset, or after each grant to the corres
    * ponding port. The aging counters down-count every clock cycle where the
    * port is requesting but not granted. The higher significant 5-bits of the
    *  write aging counter sets the initial priority of the write channel of a
    *  given port. Port's priority will increase as the higher significant 5-b
    * its of the counter starts to decrease. When the aging counter becomes 0,
    *  the corresponding port channel will have the highest priority level. Fo
    * r multi-port configurations, the aging counters cannot be used to set po
    * rt priorities when external dynamic priority inputs (awqos) are enabled
    * (timeout is still applicable). For single port configurations, the aging
    *  counters are only used when they timeout (become 0) to force read-write
    *  direction switching. Note: The two LSBs of this register field are tied
    *  internally to 2'b00.
    *  PSU_DDRC_PCFGW_5_WR_PORT_PRIORITY                           0xf

    * Port n Configuration Write Register
    * (OFFSET, MASK, VALUE)      (0XFD070778, 0x000073FFU ,0x0000200FU)
    */
	PSU_Mask_Write(DDRC_PCFGW_5_OFFSET, 0x000073FFU, 0x0000200FU);
/*##################################################################### */

    /*
    * Register : PCTRL_5 @ 0XFD070800

    * Enables port n.
    *  PSU_DDRC_PCTRL_5_PORT_EN                                    0x1

    * Port n Control Register
    * (OFFSET, MASK, VALUE)      (0XFD070800, 0x00000001U ,0x00000001U)
    */
	PSU_Mask_Write(DDRC_PCTRL_5_OFFSET, 0x00000001U, 0x00000001U);
/*##################################################################### */

    /*
    * Register : PCFGQOS0_5 @ 0XFD070804

    * This bitfield indicates the traffic class of region 1. Valid values are:
    *  0 : LPR, 1: VPR, 2: HPR. For dual address queue configurations, region1
    *  maps to the blue address queue. In this case, valid values are 0: LPR a
    * nd 1: VPR only. When VPR support is disabled (UMCTL2_VPR_EN = 0) and tra
    * ffic class of region 1 is set to 1 (VPR), VPR traffic is aliased to LPR
    * traffic.
    *  PSU_DDRC_PCFGQOS0_5_RQOS_MAP_REGION1                        0x1

    * This bitfield indicates the traffic class of region 0. Valid values are:
    *  0: LPR, 1: VPR, 2: HPR. For dual address queue configurations, region 0
    *  maps to the blue address queue. In this case, valid values are: 0: LPR
    * and 1: VPR only. When VPR support is disabled (UMCTL2_VPR_EN = 0) and tr
    * affic class of region0 is set to 1 (VPR), VPR traffic is aliased to LPR
    * traffic.
    *  PSU_DDRC_PCFGQOS0_5_RQOS_MAP_REGION0                        0x0

    * Separation level1 indicating the end of region0 mapping; start of region
    * 0 is 0. Possible values for level1 are 0 to 13 (for dual RAQ) or 0 to 14
    *  (for single RAQ) which corresponds to arqos. Note that for PA, arqos va
    * lues are used directly as port priorities, where the higher the value co
    * rresponds to higher port priority. All of the map_level* registers must
    * be set to distinct values.
    *  PSU_DDRC_PCFGQOS0_5_RQOS_MAP_LEVEL1                         0x3

    * Port n Read QoS Configuration Register 0
    * (OFFSET, MASK, VALUE)      (0XFD070804, 0x0033000FU ,0x00100003U)
    */
	PSU_Mask_Write(DDRC_PCFGQOS0_5_OFFSET, 0x0033000FU, 0x00100003U);
/*##################################################################### */

    /*
    * Register : PCFGQOS1_5 @ 0XFD070808

    * Specifies the timeout value for transactions mapped to the red address q
    * ueue.
    *  PSU_DDRC_PCFGQOS1_5_RQOS_MAP_TIMEOUTR                       0x0

    * Specifies the timeout value for transactions mapped to the blue address
    * queue.
    *  PSU_DDRC_PCFGQOS1_5_RQOS_MAP_TIMEOUTB                       0x4f

    * Port n Read QoS Configuration Register 1
    * (OFFSET, MASK, VALUE)      (0XFD070808, 0x07FF07FFU ,0x0000004FU)
    */
	PSU_Mask_Write(DDRC_PCFGQOS1_5_OFFSET, 0x07FF07FFU, 0x0000004FU);
/*##################################################################### */

    /*
    * Register : PCFGWQOS0_5 @ 0XFD07080C

    * This bitfield indicates the traffic class of region 1. Valid values are:
    *  0: NPW, 1: VPW. When VPW support is disabled (UMCTL2_VPW_EN = 0) and tr
    * affic class of region 1 is set to 1 (VPW), VPW traffic is aliased to LPW
    *  traffic.
    *  PSU_DDRC_PCFGWQOS0_5_WQOS_MAP_REGION1                       0x1

    * This bitfield indicates the traffic class of region 0. Valid values are:
    *  0: NPW, 1: VPW. When VPW support is disabled (UMCTL2_VPW_EN = 0) and tr
    * affic class of region0 is set to 1 (VPW), VPW traffic is aliased to NPW
    * traffic.
    *  PSU_DDRC_PCFGWQOS0_5_WQOS_MAP_REGION0                       0x0

    * Separation level indicating the end of region0 mapping; start of region0
    *  is 0. Possible values for level1 are 0 to 14 which corresponds to awqos
    * . Note that for PA, awqos values are used directly as port priorities, w
    * here the higher the value corresponds to higher port priority.
    *  PSU_DDRC_PCFGWQOS0_5_WQOS_MAP_LEVEL                         0x3

    * Port n Write QoS Configuration Register 0
    * (OFFSET, MASK, VALUE)      (0XFD07080C, 0x0033000FU ,0x00100003U)
    */
	PSU_Mask_Write(DDRC_PCFGWQOS0_5_OFFSET, 0x0033000FU, 0x00100003U);
/*##################################################################### */

    /*
    * Register : PCFGWQOS1_5 @ 0XFD070810

    * Specifies the timeout value for write transactions.
    *  PSU_DDRC_PCFGWQOS1_5_WQOS_MAP_TIMEOUT                       0x4f

    * Port n Write QoS Configuration Register 1
    * (OFFSET, MASK, VALUE)      (0XFD070810, 0x000007FFU ,0x0000004FU)
    */
	PSU_Mask_Write(DDRC_PCFGWQOS1_5_OFFSET, 0x000007FFU, 0x0000004FU);
/*##################################################################### */

    /*
    * Register : SARBASE0 @ 0XFD070F04

    * Base address for address region n specified as awaddr[UMCTL2_A_ADDRW-1:x
    * ] and araddr[UMCTL2_A_ADDRW-1:x] where x is determined by the minimum bl
    * ock size parameter UMCTL2_SARMINSIZE: (x=log2(block size)).
    *  PSU_DDRC_SARBASE0_BASE_ADDR                                 0x0

    * SAR Base Address Register n
    * (OFFSET, MASK, VALUE)      (0XFD070F04, 0x000001FFU ,0x00000000U)
    */
	PSU_Mask_Write(DDRC_SARBASE0_OFFSET, 0x000001FFU, 0x00000000U);
/*##################################################################### */

    /*
    * Register : SARSIZE0 @ 0XFD070F08

    * Number of blocks for address region n. This register determines the tota
    * l size of the region in multiples of minimum block size as specified by
    * the hardware parameter UMCTL2_SARMINSIZE. The register value is encoded
    * as number of blocks = nblocks + 1. For example, if register is programme
    * d to 0, region will have 1 block.
    *  PSU_DDRC_SARSIZE0_NBLOCKS                                   0x0

    * SAR Size Register n
    * (OFFSET, MASK, VALUE)      (0XFD070F08, 0x000000FFU ,0x00000000U)
    */
	PSU_Mask_Write(DDRC_SARSIZE0_OFFSET, 0x000000FFU, 0x00000000U);
/*##################################################################### */

    /*
    * Register : SARBASE1 @ 0XFD070F0C

    * Base address for address region n specified as awaddr[UMCTL2_A_ADDRW-1:x
    * ] and araddr[UMCTL2_A_ADDRW-1:x] where x is determined by the minimum bl
    * ock size parameter UMCTL2_SARMINSIZE: (x=log2(block size)).
    *  PSU_DDRC_SARBASE1_BASE_ADDR                                 0x10

    * SAR Base Address Register n
    * (OFFSET, MASK, VALUE)      (0XFD070F0C, 0x000001FFU ,0x00000010U)
    */
	PSU_Mask_Write(DDRC_SARBASE1_OFFSET, 0x000001FFU, 0x00000010U);
/*##################################################################### */

    /*
    * Register : SARSIZE1 @ 0XFD070F10

    * Number of blocks for address region n. This register determines the tota
    * l size of the region in multiples of minimum block size as specified by
    * the hardware parameter UMCTL2_SARMINSIZE. The register value is encoded
    * as number of blocks = nblocks + 1. For example, if register is programme
    * d to 0, region will have 1 block.
    *  PSU_DDRC_SARSIZE1_NBLOCKS                                   0xf

    * SAR Size Register n
    * (OFFSET, MASK, VALUE)      (0XFD070F10, 0x000000FFU ,0x0000000FU)
    */
	PSU_Mask_Write(DDRC_SARSIZE1_OFFSET, 0x000000FFU, 0x0000000FU);
/*##################################################################### */

    /*
    * Register : DFITMG0_SHADOW @ 0XFD072190

    * Specifies the number of DFI clock cycles after an assertion or de-assert
    * ion of the DFI control signals that the control signals at the PHY-DRAM
    * interface reflect the assertion or de-assertion. If the DFI clock and th
    * e memory clock are not phase-aligned, this timing parameter should be ro
    * unded up to the next integer value. Note that if using RDIMM, it is nece
    * ssary to increment this parameter by RDIMM's extra cycle of latency in t
    * erms of DFI clock.
    *  PSU_DDRC_DFITMG0_SHADOW_DFI_T_CTRL_DELAY                    0x7

    * Defines whether dfi_rddata_en/dfi_rddata/dfi_rddata_valid is generated u
    * sing HDR or SDR values Selects whether value in DFITMG0.dfi_t_rddata_en
    * is in terms of SDR or HDR clock cycles: - 0 in terms of HDR clock cycles
    *  - 1 in terms of SDR clock cycles Refer to PHY specification for correct
    *  value.
    *  PSU_DDRC_DFITMG0_SHADOW_DFI_RDDATA_USE_SDR                  0x1

    * Time from the assertion of a read command on the DFI interface to the as
    * sertion of the dfi_rddata_en signal. Refer to PHY specification for corr
    * ect value. This corresponds to the DFI parameter trddata_en. Note that,
    * depending on the PHY, if using RDIMM, it may be necessary to use the val
    * ue (CL + 1) in the calculation of trddata_en. This is to compensate for
    * the extra cycle of latency through the RDIMM. Unit: Clocks
    *  PSU_DDRC_DFITMG0_SHADOW_DFI_T_RDDATA_EN                     0x2

    * Defines whether dfi_wrdata_en/dfi_wrdata/dfi_wrdata_mask is generated us
    * ing HDR or SDR values Selects whether value in DFITMG0.dfi_tphy_wrlat is
    *  in terms of SDR or HDR clock cycles Selects whether value in DFITMG0.df
    * i_tphy_wrdata is in terms of SDR or HDR clock cycles - 0 in terms of HDR
    *  clock cycles - 1 in terms of SDR clock cycles Refer to PHY specificatio
    * n for correct value.
    *  PSU_DDRC_DFITMG0_SHADOW_DFI_WRDATA_USE_SDR                  0x1

    * Specifies the number of clock cycles between when dfi_wrdata_en is asser
    * ted to when the associated write data is driven on the dfi_wrdata signal
    * . This corresponds to the DFI timing parameter tphy_wrdata. Refer to PHY
    *  specification for correct value. Note, max supported value is 8. Unit:
    * Clocks
    *  PSU_DDRC_DFITMG0_SHADOW_DFI_TPHY_WRDATA                     0x0

    * Write latency Number of clocks from the write command to write data enab
    * le (dfi_wrdata_en). This corresponds to the DFI timing parameter tphy_wr
    * lat. Refer to PHY specification for correct value.Note that, depending o
    * n the PHY, if using RDIMM, it may be necessary to use the value (CL + 1)
    *  in the calculation of tphy_wrlat. This is to compensate for the extra c
    * ycle of latency through the RDIMM.
    *  PSU_DDRC_DFITMG0_SHADOW_DFI_TPHY_WRLAT                      0x2

    * DFI Timing Shadow Register 0
    * (OFFSET, MASK, VALUE)      (0XFD072190, 0x1FBFBF3FU ,0x07828002U)
    */
	PSU_Mask_Write(DDRC_DFITMG0_SHADOW_OFFSET, 0x1FBFBF3FU, 0x07828002U);
/*##################################################################### */

    /*
    * DDR CONTROLLER RESET
    */
    /*
    * Register : RST_DDR_SS @ 0XFD1A0108

    * DDR block level reset inside of the DDR Sub System
    *  PSU_CRF_APB_RST_DDR_SS_DDR_RESET                            0X0

    * APM block level reset inside of the DDR Sub System
    *  PSU_CRF_APB_RST_DDR_SS_APM_RESET                            0X0

    * DDR sub system block level reset
    * (OFFSET, MASK, VALUE)      (0XFD1A0108, 0x0000000CU ,0x00000000U)
    */
	PSU_Mask_Write(CRF_APB_RST_DDR_SS_OFFSET, 0x0000000CU, 0x00000000U);
/*##################################################################### */

    /*
    * DDR PHY
    */
    /*
    * Register : PGCR0 @ 0XFD080010

    * Address Copy
    *  PSU_DDR_PHY_PGCR0_ADCP                                      0x0

    * Reserved. Returns zeroes on reads.
    *  PSU_DDR_PHY_PGCR0_RESERVED_30_27                            0x0

    * PHY FIFO Reset
    *  PSU_DDR_PHY_PGCR0_PHYFRST                                   0x1

    * Oscillator Mode Address/Command Delay Line Select
    *  PSU_DDR_PHY_PGCR0_OSCACDL                                   0x3

    * Reserved. Returns zeroes on reads.
    *  PSU_DDR_PHY_PGCR0_RESERVED_23_19                            0x0

    * Digital Test Output Select
    *  PSU_DDR_PHY_PGCR0_DTOSEL                                    0x0

    * Reserved. Returns zeroes on reads.
    *  PSU_DDR_PHY_PGCR0_RESERVED_13                               0x0

    * Oscillator Mode Division
    *  PSU_DDR_PHY_PGCR0_OSCDIV                                    0xf

    * Oscillator Enable
    *  PSU_DDR_PHY_PGCR0_OSCEN                                     0x0

    * Reserved. Returns zeroes on reads.
    *  PSU_DDR_PHY_PGCR0_RESERVED_7_0                              0x0

    * PHY General Configuration Register 0
    * (OFFSET, MASK, VALUE)      (0XFD080010, 0xFFFFFFFFU ,0x07001E00U)
    */
	PSU_Mask_Write(DDR_PHY_PGCR0_OFFSET, 0xFFFFFFFFU, 0x07001E00U);
/*##################################################################### */

    /*
    * Register : PGCR2 @ 0XFD080018

    * Clear Training Status Registers
    *  PSU_DDR_PHY_PGCR2_CLRTSTAT                                  0x0

    * Clear Impedance Calibration
    *  PSU_DDR_PHY_PGCR2_CLRZCAL                                   0x0

    * Clear Parity Error
    *  PSU_DDR_PHY_PGCR2_CLRPERR                                   0x0

    * Initialization Complete Pin Configuration
    *  PSU_DDR_PHY_PGCR2_ICPC                                      0x0

    * Data Training PUB Mode Exit Timer
    *  PSU_DDR_PHY_PGCR2_DTPMXTMR                                  0xf

    * Initialization Bypass
    *  PSU_DDR_PHY_PGCR2_INITFSMBYP                                0x0

    * PLL FSM Bypass
    *  PSU_DDR_PHY_PGCR2_PLLFSMBYP                                 0x0

    * Refresh Period
    *  PSU_DDR_PHY_PGCR2_TREFPRD                                   0x10010

    * PHY General Configuration Register 2
    * (OFFSET, MASK, VALUE)      (0XFD080018, 0xFFFFFFFFU ,0x00F10010U)
    */
	PSU_Mask_Write(DDR_PHY_PGCR2_OFFSET, 0xFFFFFFFFU, 0x00F10010U);
/*##################################################################### */

    /*
    * Register : PGCR3 @ 0XFD08001C

    * CKN Enable
    *  PSU_DDR_PHY_PGCR3_CKNEN                                     0x55

    * CK Enable
    *  PSU_DDR_PHY_PGCR3_CKEN                                      0xaa

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_PGCR3_RESERVED_15                               0x0

    * Enable Clock Gating for AC [0] ctl_rd_clk
    *  PSU_DDR_PHY_PGCR3_GATEACRDCLK                               0x2

    * Enable Clock Gating for AC [0] ddr_clk
    *  PSU_DDR_PHY_PGCR3_GATEACDDRCLK                              0x2

    * Enable Clock Gating for AC [0] ctl_clk
    *  PSU_DDR_PHY_PGCR3_GATEACCTLCLK                              0x2

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_PGCR3_RESERVED_8                                0x0

    * Controls DDL Bypass Modes
    *  PSU_DDR_PHY_PGCR3_DDLBYPMODE                                0x2

    * IO Loop-Back Select
    *  PSU_DDR_PHY_PGCR3_IOLB                                      0x0

    * AC Receive FIFO Read Mode
    *  PSU_DDR_PHY_PGCR3_RDMODE                                    0x0

    * Read FIFO Reset Disable
    *  PSU_DDR_PHY_PGCR3_DISRST                                    0x0

    * Clock Level when Clock Gating
    *  PSU_DDR_PHY_PGCR3_CLKLEVEL                                  0x0

    * PHY General Configuration Register 3
    * (OFFSET, MASK, VALUE)      (0XFD08001C, 0xFFFFFFFFU ,0x55AA5480U)
    */
	PSU_Mask_Write(DDR_PHY_PGCR3_OFFSET, 0xFFFFFFFFU, 0x55AA5480U);
/*##################################################################### */

    /*
    * Register : PGCR5 @ 0XFD080024

    * Frequency B Ratio Term
    *  PSU_DDR_PHY_PGCR5_FRQBT                                     0x1

    * Frequency A Ratio Term
    *  PSU_DDR_PHY_PGCR5_FRQAT                                     0x1

    * DFI Disconnect Time Period
    *  PSU_DDR_PHY_PGCR5_DISCNPERIOD                               0x0

    * Receiver bias core side control
    *  PSU_DDR_PHY_PGCR5_VREF_RBCTRL                               0xf

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_PGCR5_RESERVED_3                                0x0

    * Internal VREF generator REFSEL ragne select
    *  PSU_DDR_PHY_PGCR5_DXREFISELRANGE                            0x1

    * DDL Page Read Write select
    *  PSU_DDR_PHY_PGCR5_DDLPGACT                                  0x0

    * DDL Page Read Write select
    *  PSU_DDR_PHY_PGCR5_DDLPGRW                                   0x0

    * PHY General Configuration Register 5
    * (OFFSET, MASK, VALUE)      (0XFD080024, 0xFFFFFFFFU ,0x010100F4U)
    */
	PSU_Mask_Write(DDR_PHY_PGCR5_OFFSET, 0xFFFFFFFFU, 0x010100F4U);
/*##################################################################### */

    /*
    * Register : PTR0 @ 0XFD080040

    * PLL Power-Down Time
    *  PSU_DDR_PHY_PTR0_TPLLPD                                     0x56

    * PLL Gear Shift Time
    *  PSU_DDR_PHY_PTR0_TPLLGS                                     0x2155

    * PHY Reset Time
    *  PSU_DDR_PHY_PTR0_TPHYRST                                    0x10

    * PHY Timing Register 0
    * (OFFSET, MASK, VALUE)      (0XFD080040, 0xFFFFFFFFU ,0x0AC85550U)
    */
	PSU_Mask_Write(DDR_PHY_PTR0_OFFSET, 0xFFFFFFFFU, 0x0AC85550U);
/*##################################################################### */

    /*
    * Register : PTR1 @ 0XFD080044

    * PLL Lock Time
    *  PSU_DDR_PHY_PTR1_TPLLLOCK                                   0x4141

    * Reserved. Returns zeroes on reads.
    *  PSU_DDR_PHY_PTR1_RESERVED_15_13                             0x0

    * PLL Reset Time
    *  PSU_DDR_PHY_PTR1_TPLLRST                                    0xaff

    * PHY Timing Register 1
    * (OFFSET, MASK, VALUE)      (0XFD080044, 0xFFFFFFFFU ,0x41410AFFU)
    */
	PSU_Mask_Write(DDR_PHY_PTR1_OFFSET, 0xFFFFFFFFU, 0x41410AFFU);
/*##################################################################### */

    /*
    * Register : PLLCR0 @ 0XFD080068

    * PLL Bypass
    *  PSU_DDR_PHY_PLLCR0_PLLBYP                                   0x0

    * PLL Reset
    *  PSU_DDR_PHY_PLLCR0_PLLRST                                   0x0

    * PLL Power Down
    *  PSU_DDR_PHY_PLLCR0_PLLPD                                    0x0

    * Reference Stop Mode
    *  PSU_DDR_PHY_PLLCR0_RSTOPM                                   0x0

    * PLL Frequency Select
    *  PSU_DDR_PHY_PLLCR0_FRQSEL                                   0x1

    * Relock Mode
    *  PSU_DDR_PHY_PLLCR0_RLOCKM                                   0x0

    * Charge Pump Proportional Current Control
    *  PSU_DDR_PHY_PLLCR0_CPPC                                     0x8

    * Charge Pump Integrating Current Control
    *  PSU_DDR_PHY_PLLCR0_CPIC                                     0x0

    * Gear Shift
    *  PSU_DDR_PHY_PLLCR0_GSHIFT                                   0x0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_PLLCR0_RESERVED_11_9                            0x0

    * Analog Test Enable
    *  PSU_DDR_PHY_PLLCR0_ATOEN                                    0x0

    * Analog Test Control
    *  PSU_DDR_PHY_PLLCR0_ATC                                      0x0

    * Digital Test Control
    *  PSU_DDR_PHY_PLLCR0_DTC                                      0x0

    * PLL Control Register 0 (Type B PLL Only)
    * (OFFSET, MASK, VALUE)      (0XFD080068, 0xFFFFFFFFU ,0x01100000U)
    */
	PSU_Mask_Write(DDR_PHY_PLLCR0_OFFSET, 0xFFFFFFFFU, 0x01100000U);
/*##################################################################### */

    /*
    * Register : DSGCR @ 0XFD080090

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DSGCR_RESERVED_31_28                            0x0

    * When RDBI enabled, this bit is used to select RDBI CL calculation, if it
    *  is 1b1, calculation will use RDBICL, otherwise use default calculation.
    *  PSU_DDR_PHY_DSGCR_RDBICLSEL                                 0x0

    * When RDBI enabled, if RDBICLSEL is asserted, RDBI CL adjust using this v
    * alue.
    *  PSU_DDR_PHY_DSGCR_RDBICL                                    0x2

    * PHY Impedance Update Enable
    *  PSU_DDR_PHY_DSGCR_PHYZUEN                                   0x1

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DSGCR_RESERVED_22                               0x0

    * SDRAM Reset Output Enable
    *  PSU_DDR_PHY_DSGCR_RSTOE                                     0x1

    * Single Data Rate Mode
    *  PSU_DDR_PHY_DSGCR_SDRMODE                                   0x0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DSGCR_RESERVED_18                               0x0

    * ATO Analog Test Enable
    *  PSU_DDR_PHY_DSGCR_ATOAE                                     0x0

    * DTO Output Enable
    *  PSU_DDR_PHY_DSGCR_DTOOE                                     0x0

    * DTO I/O Mode
    *  PSU_DDR_PHY_DSGCR_DTOIOM                                    0x0

    * DTO Power Down Receiver
    *  PSU_DDR_PHY_DSGCR_DTOPDR                                    0x1

    * Reserved. Return zeroes on reads
    *  PSU_DDR_PHY_DSGCR_RESERVED_13                               0x0

    * DTO On-Die Termination
    *  PSU_DDR_PHY_DSGCR_DTOODT                                    0x0

    * PHY Update Acknowledge Delay
    *  PSU_DDR_PHY_DSGCR_PUAD                                      0x5

    * Controller Update Acknowledge Enable
    *  PSU_DDR_PHY_DSGCR_CUAEN                                     0x1

    * Reserved. Return zeroes on reads
    *  PSU_DDR_PHY_DSGCR_RESERVED_4_3                              0x0

    * Controller Impedance Update Enable
    *  PSU_DDR_PHY_DSGCR_CTLZUEN                                   0x0

    * Reserved. Return zeroes on reads
    *  PSU_DDR_PHY_DSGCR_RESERVED_1                                0x0

    * PHY Update Request Enable
    *  PSU_DDR_PHY_DSGCR_PUREN                                     0x1

    * DDR System General Configuration Register
    * (OFFSET, MASK, VALUE)      (0XFD080090, 0xFFFFFFFFU ,0x02A04161U)
    */
	PSU_Mask_Write(DDR_PHY_DSGCR_OFFSET, 0xFFFFFFFFU, 0x02A04161U);
/*##################################################################### */

    /*
    * Register : GPR0 @ 0XFD0800C0

    * General Purpose Register 0
    *  PSU_DDR_PHY_GPR0_GPR0                                       0xd3

    * General Purpose Register 0
    * (OFFSET, MASK, VALUE)      (0XFD0800C0, 0xFFFFFFFFU ,0x000000D3U)
    */
	PSU_Mask_Write(DDR_PHY_GPR0_OFFSET, 0xFFFFFFFFU, 0x000000D3U);
/*##################################################################### */

    /*
    * Register : DCR @ 0XFD080100

    * DDR4 Gear Down Timing.
    *  PSU_DDR_PHY_DCR_GEARDN                                      0x0

    * Un-used Bank Group
    *  PSU_DDR_PHY_DCR_UBG                                         0x0

    * Un-buffered DIMM Address Mirroring
    *  PSU_DDR_PHY_DCR_UDIMM                                       0x0

    * DDR 2T Timing
    *  PSU_DDR_PHY_DCR_DDR2T                                       0x0

    * No Simultaneous Rank Access
    *  PSU_DDR_PHY_DCR_NOSRA                                       0x1

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DCR_RESERVED_26_18                              0x0

    * Byte Mask
    *  PSU_DDR_PHY_DCR_BYTEMASK                                    0x1

    * DDR Type
    *  PSU_DDR_PHY_DCR_DDRTYPE                                     0x0

    * Multi-Purpose Register (MPR) DQ (DDR3 Only)
    *  PSU_DDR_PHY_DCR_MPRDQ                                       0x0

    * Primary DQ (DDR3 Only)
    *  PSU_DDR_PHY_DCR_PDQ                                         0x0

    * DDR 8-Bank
    *  PSU_DDR_PHY_DCR_DDR8BNK                                     0x1

    * DDR Mode
    *  PSU_DDR_PHY_DCR_DDRMD                                       0x4

    * DRAM Configuration Register
    * (OFFSET, MASK, VALUE)      (0XFD080100, 0xFFFFFFFFU ,0x0800040CU)
    */
	PSU_Mask_Write(DDR_PHY_DCR_OFFSET, 0xFFFFFFFFU, 0x0800040CU);
/*##################################################################### */

    /*
    * Register : DTPR0 @ 0XFD080110

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DTPR0_RESERVED_31_29                            0x0

    * Activate to activate command delay (different banks)
    *  PSU_DDR_PHY_DTPR0_TRRD                                      0x6

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DTPR0_RESERVED_23                               0x0

    * Activate to precharge command delay
    *  PSU_DDR_PHY_DTPR0_TRAS                                      0x24

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DTPR0_RESERVED_15                               0x0

    * Precharge command period
    *  PSU_DDR_PHY_DTPR0_TRP                                       0xf

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DTPR0_RESERVED_7_5                              0x0

    * Internal read to precharge command delay
    *  PSU_DDR_PHY_DTPR0_TRTP                                      0x8

    * DRAM Timing Parameters Register 0
    * (OFFSET, MASK, VALUE)      (0XFD080110, 0xFFFFFFFFU ,0x06240F08U)
    */
	PSU_Mask_Write(DDR_PHY_DTPR0_OFFSET, 0xFFFFFFFFU, 0x06240F08U);
/*##################################################################### */

    /*
    * Register : DTPR1 @ 0XFD080114

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DTPR1_RESERVED_31                               0x0

    * Minimum delay from when write leveling mode is programmed to the first D
    * QS/DQS# rising edge.
    *  PSU_DDR_PHY_DTPR1_TWLMRD                                    0x28

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DTPR1_RESERVED_23                               0x0

    * 4-bank activate period
    *  PSU_DDR_PHY_DTPR1_TFAW                                      0x20

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DTPR1_RESERVED_15_11                            0x0

    * Load mode update delay (DDR4 and DDR3 only)
    *  PSU_DDR_PHY_DTPR1_TMOD                                      0x0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DTPR1_RESERVED_7_5                              0x0

    * Load mode cycle time
    *  PSU_DDR_PHY_DTPR1_TMRD                                      0x8

    * DRAM Timing Parameters Register 1
    * (OFFSET, MASK, VALUE)      (0XFD080114, 0xFFFFFFFFU ,0x28200008U)
    */
	PSU_Mask_Write(DDR_PHY_DTPR1_OFFSET, 0xFFFFFFFFU, 0x28200008U);
/*##################################################################### */

    /*
    * Register : DTPR2 @ 0XFD080118

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DTPR2_RESERVED_31_29                            0x0

    * Read to Write command delay. Valid values are
    *  PSU_DDR_PHY_DTPR2_TRTW                                      0x0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DTPR2_RESERVED_27_25                            0x0

    * Read to ODT delay (DDR3 only)
    *  PSU_DDR_PHY_DTPR2_TRTODT                                    0x0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DTPR2_RESERVED_23_20                            0x0

    * CKE minimum pulse width
    *  PSU_DDR_PHY_DTPR2_TCKE                                      0x7

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DTPR2_RESERVED_15_10                            0x0

    * Self refresh exit delay
    *  PSU_DDR_PHY_DTPR2_TXS                                       0x300

    * DRAM Timing Parameters Register 2
    * (OFFSET, MASK, VALUE)      (0XFD080118, 0xFFFFFFFFU ,0x00070300U)
    */
	PSU_Mask_Write(DDR_PHY_DTPR2_OFFSET, 0xFFFFFFFFU, 0x00070300U);
/*##################################################################### */

    /*
    * Register : DTPR3 @ 0XFD08011C

    * ODT turn-off delay extension
    *  PSU_DDR_PHY_DTPR3_TOFDX                                     0x4

    * Read to read and write to write command delay
    *  PSU_DDR_PHY_DTPR3_TCCD                                      0x0

    * DLL locking time
    *  PSU_DDR_PHY_DTPR3_TDLLK                                     0x300

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DTPR3_RESERVED_15_12                            0x0

    * Maximum DQS output access time from CK/CK# (LPDDR2/3 only)
    *  PSU_DDR_PHY_DTPR3_TDQSCKMAX                                 0x8

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DTPR3_RESERVED_7_3                              0x0

    * DQS output access time from CK/CK# (LPDDR2/3 only)
    *  PSU_DDR_PHY_DTPR3_TDQSCK                                    0x0

    * DRAM Timing Parameters Register 3
    * (OFFSET, MASK, VALUE)      (0XFD08011C, 0xFFFFFFFFU ,0x83000800U)
    */
	PSU_Mask_Write(DDR_PHY_DTPR3_OFFSET, 0xFFFFFFFFU, 0x83000800U);
/*##################################################################### */

    /*
    * Register : DTPR4 @ 0XFD080120

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DTPR4_RESERVED_31_30                            0x0

    * ODT turn-on/turn-off delays (DDR2 only)
    *  PSU_DDR_PHY_DTPR4_TAOND_TAOFD                               0x0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DTPR4_RESERVED_27_26                            0x0

    * Refresh-to-Refresh
    *  PSU_DDR_PHY_DTPR4_TRFC                                      0x116

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DTPR4_RESERVED_15_14                            0x0

    * Write leveling output delay
    *  PSU_DDR_PHY_DTPR4_TWLO                                      0x2b

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DTPR4_RESERVED_7_5                              0x0

    * Power down exit delay
    *  PSU_DDR_PHY_DTPR4_TXP                                       0x7

    * DRAM Timing Parameters Register 4
    * (OFFSET, MASK, VALUE)      (0XFD080120, 0xFFFFFFFFU ,0x01162B07U)
    */
	PSU_Mask_Write(DDR_PHY_DTPR4_OFFSET, 0xFFFFFFFFU, 0x01162B07U);
/*##################################################################### */

    /*
    * Register : DTPR5 @ 0XFD080124

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DTPR5_RESERVED_31_24                            0x0

    * Activate to activate command delay (same bank)
    *  PSU_DDR_PHY_DTPR5_TRC                                       0x33

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DTPR5_RESERVED_15                               0x0

    * Activate to read or write delay
    *  PSU_DDR_PHY_DTPR5_TRCD                                      0xf

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DTPR5_RESERVED_7_5                              0x0

    * Internal write to read command delay
    *  PSU_DDR_PHY_DTPR5_TWTR                                      0x8

    * DRAM Timing Parameters Register 5
    * (OFFSET, MASK, VALUE)      (0XFD080124, 0xFFFFFFFFU ,0x00330F08U)
    */
	PSU_Mask_Write(DDR_PHY_DTPR5_OFFSET, 0xFFFFFFFFU, 0x00330F08U);
/*##################################################################### */

    /*
    * Register : DTPR6 @ 0XFD080128

    * PUB Write Latency Enable
    *  PSU_DDR_PHY_DTPR6_PUBWLEN                                   0x0

    * PUB Read Latency Enable
    *  PSU_DDR_PHY_DTPR6_PUBRLEN                                   0x0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DTPR6_RESERVED_29_14                            0x0

    * Write Latency
    *  PSU_DDR_PHY_DTPR6_PUBWL                                     0xe

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DTPR6_RESERVED_7_6                              0x0

    * Read Latency
    *  PSU_DDR_PHY_DTPR6_PUBRL                                     0xf

    * DRAM Timing Parameters Register 6
    * (OFFSET, MASK, VALUE)      (0XFD080128, 0xFFFFFFFFU ,0x00000E0FU)
    */
	PSU_Mask_Write(DDR_PHY_DTPR6_OFFSET, 0xFFFFFFFFU, 0x00000E0FU);
/*##################################################################### */

    /*
    * Register : RDIMMGCR0 @ 0XFD080140

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_RDIMMGCR0_RESERVED_31                           0x0

    * RDMIMM Quad CS Enable
    *  PSU_DDR_PHY_RDIMMGCR0_QCSEN                                 0x0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_RDIMMGCR0_RESERVED_29_28                        0x0

    * RDIMM Outputs I/O Mode
    *  PSU_DDR_PHY_RDIMMGCR0_RDIMMIOM                              0x1

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_RDIMMGCR0_RESERVED_26_24                        0x0

    * ERROUT# Output Enable
    *  PSU_DDR_PHY_RDIMMGCR0_ERROUTOE                              0x0

    * ERROUT# I/O Mode
    *  PSU_DDR_PHY_RDIMMGCR0_ERROUTIOM                             0x1

    * ERROUT# Power Down Receiver
    *  PSU_DDR_PHY_RDIMMGCR0_ERROUTPDR                             0x0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_RDIMMGCR0_RESERVED_20                           0x0

    * ERROUT# On-Die Termination
    *  PSU_DDR_PHY_RDIMMGCR0_ERROUTODT                             0x0

    * Load Reduced DIMM
    *  PSU_DDR_PHY_RDIMMGCR0_LRDIMM                                0x0

    * PAR_IN I/O Mode
    *  PSU_DDR_PHY_RDIMMGCR0_PARINIOM                              0x0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_RDIMMGCR0_RESERVED_16_8                         0x0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_RDIMMGCR0_RNKMRREN_RSVD                         0x0

    * Rank Mirror Enable.
    *  PSU_DDR_PHY_RDIMMGCR0_RNKMRREN                              0x2

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_RDIMMGCR0_RESERVED_3                            0x0

    * Stop on Parity Error
    *  PSU_DDR_PHY_RDIMMGCR0_SOPERR                                0x0

    * Parity Error No Registering
    *  PSU_DDR_PHY_RDIMMGCR0_ERRNOREG                              0x0

    * Registered DIMM
    *  PSU_DDR_PHY_RDIMMGCR0_RDIMM                                 0x0

    * RDIMM General Configuration Register 0
    * (OFFSET, MASK, VALUE)      (0XFD080140, 0xFFFFFFFFU ,0x08400020U)
    */
	PSU_Mask_Write(DDR_PHY_RDIMMGCR0_OFFSET, 0xFFFFFFFFU, 0x08400020U);
/*##################################################################### */

    /*
    * Register : RDIMMGCR1 @ 0XFD080144

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_RDIMMGCR1_RESERVED_31_29                        0x0

    * Address [17] B-side Inversion Disable
    *  PSU_DDR_PHY_RDIMMGCR1_A17BID                                0x0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_RDIMMGCR1_RESERVED_27                           0x0

    * Command word to command word programming delay
    *  PSU_DDR_PHY_RDIMMGCR1_TBCMRD_L2                             0x0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_RDIMMGCR1_RESERVED_23                           0x0

    * Command word to command word programming delay
    *  PSU_DDR_PHY_RDIMMGCR1_TBCMRD_L                              0x0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_RDIMMGCR1_RESERVED_19                           0x0

    * Command word to command word programming delay
    *  PSU_DDR_PHY_RDIMMGCR1_TBCMRD                                0x0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_RDIMMGCR1_RESERVED_15_14                        0x0

    * Stabilization time
    *  PSU_DDR_PHY_RDIMMGCR1_TBCSTAB                               0xc80

    * RDIMM General Configuration Register 1
    * (OFFSET, MASK, VALUE)      (0XFD080144, 0xFFFFFFFFU ,0x00000C80U)
    */
	PSU_Mask_Write(DDR_PHY_RDIMMGCR1_OFFSET, 0xFFFFFFFFU, 0x00000C80U);
/*##################################################################### */

    /*
    * Register : RDIMMCR0 @ 0XFD080150

    * DDR4/DDR3 Control Word 7
    *  PSU_DDR_PHY_RDIMMCR0_RC7                                    0x0

    * DDR4 Control Word 6 (Comman space Control Word) / DDR3 Reserved
    *  PSU_DDR_PHY_RDIMMCR0_RC6                                    0x0

    * DDR4/DDR3 Control Word 5 (CK Driver Characteristics Control Word)
    *  PSU_DDR_PHY_RDIMMCR0_RC5                                    0x0

    * DDR4 Control Word 4 (ODT and CKE Signals Driver Characteristics Control
    * Word) / DDR3 Control Word 4 (Control Signals Driver Characteristics Cont
    * rol Word)
    *  PSU_DDR_PHY_RDIMMCR0_RC4                                    0x0

    * DDR4 Control Word 3 (CA and CS Signals Driver Characteristics Control Wo
    * rd) / DDR3 Control Word 3 (Command/Address Signals Driver Characteristri
    * cs Control Word)
    *  PSU_DDR_PHY_RDIMMCR0_RC3                                    0x0

    * DDR4 Control Word 2 (Timing and IBT Control Word) / DDR3 Control Word 2
    * (Timing Control Word)
    *  PSU_DDR_PHY_RDIMMCR0_RC2                                    0x0

    * DDR4/DDR3 Control Word 1 (Clock Driver Enable Control Word)
    *  PSU_DDR_PHY_RDIMMCR0_RC1                                    0x0

    * DDR4/DDR3 Control Word 0 (Global Features Control Word)
    *  PSU_DDR_PHY_RDIMMCR0_RC0                                    0x0

    * RDIMM Control Register 0
    * (OFFSET, MASK, VALUE)      (0XFD080150, 0xFFFFFFFFU ,0x00000000U)
    */
	PSU_Mask_Write(DDR_PHY_RDIMMCR0_OFFSET, 0xFFFFFFFFU, 0x00000000U);
/*##################################################################### */

    /*
    * Register : RDIMMCR1 @ 0XFD080154

    * Control Word 15
    *  PSU_DDR_PHY_RDIMMCR1_RC15                                   0x0

    * DDR4 Control Word 14 (Parity Control Word) / DDR3 Reserved
    *  PSU_DDR_PHY_RDIMMCR1_RC14                                   0x0

    * DDR4 Control Word 13 (DIMM Configuration Control Word) / DDR3 Reserved
    *  PSU_DDR_PHY_RDIMMCR1_RC13                                   0x0

    * DDR4 Control Word 12 (Training Control Word) / DDR3 Reserved
    *  PSU_DDR_PHY_RDIMMCR1_RC12                                   0x0

    * DDR4 Control Word 11 (Operating Voltage VDD and VREFCA Source Control Wo
    * rd) / DDR3 Control Word 11 (Operation Voltage VDD Control Word)
    *  PSU_DDR_PHY_RDIMMCR1_RC11                                   0x0

    * DDR4/DDR3 Control Word 10 (RDIMM Operating Speed Control Word)
    *  PSU_DDR_PHY_RDIMMCR1_RC10                                   0x2

    * DDR4/DDR3 Control Word 9 (Power Saving Settings Control Word)
    *  PSU_DDR_PHY_RDIMMCR1_RC9                                    0x0

    * DDR4 Control Word 8 (Input/Output Configuration Control Word) / DDR3 Con
    * trol Word 8 (Additional Input Bus Termination Setting Control Word)
    *  PSU_DDR_PHY_RDIMMCR1_RC8                                    0x0

    * RDIMM Control Register 1
    * (OFFSET, MASK, VALUE)      (0XFD080154, 0xFFFFFFFFU ,0x00000200U)
    */
	PSU_Mask_Write(DDR_PHY_RDIMMCR1_OFFSET, 0xFFFFFFFFU, 0x00000200U);
/*##################################################################### */

    /*
    * Register : MR0 @ 0XFD080180

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_MR0_RESERVED_31_8                               0x6

    * CA Terminating Rank
    *  PSU_DDR_PHY_MR0_CATR                                        0x0

    * Reserved. These are JEDEC reserved bits and are recommended by JEDEC to
    * be programmed to 0x0.
    *  PSU_DDR_PHY_MR0_RSVD_6_5                                    0x1

    * Built-in Self-Test for RZQ
    *  PSU_DDR_PHY_MR0_RZQI                                        0x2

    * Reserved. These are JEDEC reserved bits and are recommended by JEDEC to
    * be programmed to 0x0.
    *  PSU_DDR_PHY_MR0_RSVD_2_0                                    0x0

    * LPDDR4 Mode Register 0
    * (OFFSET, MASK, VALUE)      (0XFD080180, 0xFFFFFFFFU ,0x00000630U)
    */
	PSU_Mask_Write(DDR_PHY_MR0_OFFSET, 0xFFFFFFFFU, 0x00000630U);
/*##################################################################### */

    /*
    * Register : MR1 @ 0XFD080184

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_MR1_RESERVED_31_8                               0x3

    * Read Postamble Length
    *  PSU_DDR_PHY_MR1_RDPST                                       0x0

    * Write-recovery for auto-precharge command
    *  PSU_DDR_PHY_MR1_NWR                                         0x0

    * Read Preamble Length
    *  PSU_DDR_PHY_MR1_RDPRE                                       0x0

    * Write Preamble Length
    *  PSU_DDR_PHY_MR1_WRPRE                                       0x0

    * Burst Length
    *  PSU_DDR_PHY_MR1_BL                                          0x1

    * LPDDR4 Mode Register 1
    * (OFFSET, MASK, VALUE)      (0XFD080184, 0xFFFFFFFFU ,0x00000301U)
    */
	PSU_Mask_Write(DDR_PHY_MR1_OFFSET, 0xFFFFFFFFU, 0x00000301U);
/*##################################################################### */

    /*
    * Register : MR2 @ 0XFD080188

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_MR2_RESERVED_31_8                               0x0

    * Write Leveling
    *  PSU_DDR_PHY_MR2_WRL                                         0x0

    * Write Latency Set
    *  PSU_DDR_PHY_MR2_WLS                                         0x0

    * Write Latency
    *  PSU_DDR_PHY_MR2_WL                                          0x4

    * Read Latency
    *  PSU_DDR_PHY_MR2_RL                                          0x0

    * LPDDR4 Mode Register 2
    * (OFFSET, MASK, VALUE)      (0XFD080188, 0xFFFFFFFFU ,0x00000020U)
    */
	PSU_Mask_Write(DDR_PHY_MR2_OFFSET, 0xFFFFFFFFU, 0x00000020U);
/*##################################################################### */

    /*
    * Register : MR3 @ 0XFD08018C

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_MR3_RESERVED_31_8                               0x2

    * DBI-Write Enable
    *  PSU_DDR_PHY_MR3_DBIWR                                       0x0

    * DBI-Read Enable
    *  PSU_DDR_PHY_MR3_DBIRD                                       0x0

    * Pull-down Drive Strength
    *  PSU_DDR_PHY_MR3_PDDS                                        0x0

    * These are JEDEC reserved bits and are recommended by JEDEC to be program
    * med to 0x0.
    *  PSU_DDR_PHY_MR3_RSVD                                        0x0

    * Write Postamble Length
    *  PSU_DDR_PHY_MR3_WRPST                                       0x0

    * Pull-up Calibration Point
    *  PSU_DDR_PHY_MR3_PUCAL                                       0x0

    * LPDDR4 Mode Register 3
    * (OFFSET, MASK, VALUE)      (0XFD08018C, 0xFFFFFFFFU ,0x00000200U)
    */
	PSU_Mask_Write(DDR_PHY_MR3_OFFSET, 0xFFFFFFFFU, 0x00000200U);
/*##################################################################### */

    /*
    * Register : MR4 @ 0XFD080190

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_MR4_RESERVED_31_16                              0x0

    * These are JEDEC reserved bits and are recommended by JEDEC to be program
    * med to 0x0.
    *  PSU_DDR_PHY_MR4_RSVD_15_13                                  0x0

    * Write Preamble
    *  PSU_DDR_PHY_MR4_WRP                                         0x0

    * Read Preamble
    *  PSU_DDR_PHY_MR4_RDP                                         0x0

    * Read Preamble Training Mode
    *  PSU_DDR_PHY_MR4_RPTM                                        0x0

    * Self Refresh Abort
    *  PSU_DDR_PHY_MR4_SRA                                         0x0

    * CS to Command Latency Mode
    *  PSU_DDR_PHY_MR4_CS2CMDL                                     0x0

    * These are JEDEC reserved bits and are recommended by JEDEC to be program
    * med to 0x0.
    *  PSU_DDR_PHY_MR4_RSVD1                                       0x0

    * Internal VREF Monitor
    *  PSU_DDR_PHY_MR4_IVM                                         0x0

    * Temperature Controlled Refresh Mode
    *  PSU_DDR_PHY_MR4_TCRM                                        0x0

    * Temperature Controlled Refresh Range
    *  PSU_DDR_PHY_MR4_TCRR                                        0x0

    * Maximum Power Down Mode
    *  PSU_DDR_PHY_MR4_MPDM                                        0x0

    * This is a JEDEC reserved bit and is recommended by JEDEC to be programme
    * d to 0x0.
    *  PSU_DDR_PHY_MR4_RSVD_0                                      0x0

    * DDR4 Mode Register 4
    * (OFFSET, MASK, VALUE)      (0XFD080190, 0xFFFFFFFFU ,0x00000000U)
    */
	PSU_Mask_Write(DDR_PHY_MR4_OFFSET, 0xFFFFFFFFU, 0x00000000U);
/*##################################################################### */

    /*
    * Register : MR5 @ 0XFD080194

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_MR5_RESERVED_31_16                              0x0

    * These are JEDEC reserved bits and are recommended by JEDEC to be program
    * med to 0x0.
    *  PSU_DDR_PHY_MR5_RSVD                                        0x0

    * Read DBI
    *  PSU_DDR_PHY_MR5_RDBI                                        0x0

    * Write DBI
    *  PSU_DDR_PHY_MR5_WDBI                                        0x0

    * Data Mask
    *  PSU_DDR_PHY_MR5_DM                                          0x1

    * CA Parity Persistent Error
    *  PSU_DDR_PHY_MR5_CAPPE                                       0x1

    * RTT_PARK
    *  PSU_DDR_PHY_MR5_RTTPARK                                     0x3

    * ODT Input Buffer during Power Down mode
    *  PSU_DDR_PHY_MR5_ODTIBPD                                     0x0

    * C/A Parity Error Status
    *  PSU_DDR_PHY_MR5_CAPES                                       0x0

    * CRC Error Clear
    *  PSU_DDR_PHY_MR5_CRCEC                                       0x0

    * C/A Parity Latency Mode
    *  PSU_DDR_PHY_MR5_CAPM                                        0x0

    * DDR4 Mode Register 5
    * (OFFSET, MASK, VALUE)      (0XFD080194, 0xFFFFFFFFU ,0x000006C0U)
    */
	PSU_Mask_Write(DDR_PHY_MR5_OFFSET, 0xFFFFFFFFU, 0x000006C0U);
/*##################################################################### */

    /*
    * Register : MR6 @ 0XFD080198

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_MR6_RESERVED_31_16                              0x0

    * These are JEDEC reserved bits and are recommended by JEDEC to be program
    * med to 0x0.
    *  PSU_DDR_PHY_MR6_RSVD_15_13                                  0x0

    * CAS_n to CAS_n command delay for same bank group (tCCD_L)
    *  PSU_DDR_PHY_MR6_TCCDL                                       0x2

    * These are JEDEC reserved bits and are recommended by JEDEC to be program
    * med to 0x0.
    *  PSU_DDR_PHY_MR6_RSVD_9_8                                    0x0

    * VrefDQ Training Enable
    *  PSU_DDR_PHY_MR6_VDDQTEN                                     0x0

    * VrefDQ Training Range
    *  PSU_DDR_PHY_MR6_VDQTRG                                      0x0

    * VrefDQ Training Values
    *  PSU_DDR_PHY_MR6_VDQTVAL                                     0x19

    * DDR4 Mode Register 6
    * (OFFSET, MASK, VALUE)      (0XFD080198, 0xFFFFFFFFU ,0x00000819U)
    */
	PSU_Mask_Write(DDR_PHY_MR6_OFFSET, 0xFFFFFFFFU, 0x00000819U);
/*##################################################################### */

    /*
    * Register : MR11 @ 0XFD0801AC

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_MR11_RESERVED_31_8                              0x0

    * These are JEDEC reserved bits and are recommended by JEDEC to be program
    * med to 0x0.
    *  PSU_DDR_PHY_MR11_RSVD                                       0x0

    * Power Down Control
    *  PSU_DDR_PHY_MR11_PDCTL                                      0x0

    * DQ Bus Receiver On-Die-Termination
    *  PSU_DDR_PHY_MR11_DQODT                                      0x0

    * LPDDR4 Mode Register 11
    * (OFFSET, MASK, VALUE)      (0XFD0801AC, 0xFFFFFFFFU ,0x00000000U)
    */
	PSU_Mask_Write(DDR_PHY_MR11_OFFSET, 0xFFFFFFFFU, 0x00000000U);
/*##################################################################### */

    /*
    * Register : MR12 @ 0XFD0801B0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_MR12_RESERVED_31_8                              0x0

    * These are JEDEC reserved bits and are recommended by JEDEC to be program
    * med to 0x0.
    *  PSU_DDR_PHY_MR12_RSVD                                       0x0

    * VREF_CA Range Select.
    *  PSU_DDR_PHY_MR12_VR_CA                                      0x1

    * Controls the VREF(ca) levels for Frequency-Set-Point[1:0].
    *  PSU_DDR_PHY_MR12_VREF_CA                                    0xd

    * LPDDR4 Mode Register 12
    * (OFFSET, MASK, VALUE)      (0XFD0801B0, 0xFFFFFFFFU ,0x0000004DU)
    */
	PSU_Mask_Write(DDR_PHY_MR12_OFFSET, 0xFFFFFFFFU, 0x0000004DU);
/*##################################################################### */

    /*
    * Register : MR13 @ 0XFD0801B4

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_MR13_RESERVED_31_8                              0x0

    * Frequency Set Point Operation Mode
    *  PSU_DDR_PHY_MR13_FSPOP                                      0x0

    * Frequency Set Point Write Enable
    *  PSU_DDR_PHY_MR13_FSPWR                                      0x0

    * Data Mask Enable
    *  PSU_DDR_PHY_MR13_DMD                                        0x0

    * Refresh Rate Option
    *  PSU_DDR_PHY_MR13_RRO                                        0x0

    * VREF Current Generator
    *  PSU_DDR_PHY_MR13_VRCG                                       0x1

    * VREF Output
    *  PSU_DDR_PHY_MR13_VRO                                        0x0

    * Read Preamble Training Mode
    *  PSU_DDR_PHY_MR13_RPT                                        0x0

    * Command Bus Training
    *  PSU_DDR_PHY_MR13_CBT                                        0x0

    * LPDDR4 Mode Register 13
    * (OFFSET, MASK, VALUE)      (0XFD0801B4, 0xFFFFFFFFU ,0x00000008U)
    */
	PSU_Mask_Write(DDR_PHY_MR13_OFFSET, 0xFFFFFFFFU, 0x00000008U);
/*##################################################################### */

    /*
    * Register : MR14 @ 0XFD0801B8

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_MR14_RESERVED_31_8                              0x0

    * These are JEDEC reserved bits and are recommended by JEDEC to be program
    * med to 0x0.
    *  PSU_DDR_PHY_MR14_RSVD                                       0x0

    * VREFDQ Range Selects.
    *  PSU_DDR_PHY_MR14_VR_DQ                                      0x1

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_MR14_VREF_DQ                                    0xd

    * LPDDR4 Mode Register 14
    * (OFFSET, MASK, VALUE)      (0XFD0801B8, 0xFFFFFFFFU ,0x0000004DU)
    */
	PSU_Mask_Write(DDR_PHY_MR14_OFFSET, 0xFFFFFFFFU, 0x0000004DU);
/*##################################################################### */

    /*
    * Register : MR22 @ 0XFD0801D8

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_MR22_RESERVED_31_8                              0x0

    * These are JEDEC reserved bits and are recommended by JEDEC to be program
    * med to 0x0.
    *  PSU_DDR_PHY_MR22_RSVD                                       0x0

    * CA ODT termination disable.
    *  PSU_DDR_PHY_MR22_ODTD_CA                                    0x0

    * ODT CS override.
    *  PSU_DDR_PHY_MR22_ODTE_CS                                    0x0

    * ODT CK override.
    *  PSU_DDR_PHY_MR22_ODTE_CK                                    0x0

    * Controller ODT value for VOH calibration.
    *  PSU_DDR_PHY_MR22_CODT                                       0x0

    * LPDDR4 Mode Register 22
    * (OFFSET, MASK, VALUE)      (0XFD0801D8, 0xFFFFFFFFU ,0x00000000U)
    */
	PSU_Mask_Write(DDR_PHY_MR22_OFFSET, 0xFFFFFFFFU, 0x00000000U);
/*##################################################################### */

    /*
    * Register : DTCR0 @ 0XFD080200

    * Refresh During Training
    *  PSU_DDR_PHY_DTCR0_RFSHDT                                    0x8

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DTCR0_RESERVED_27_26                            0x0

    * Data Training Debug Rank Select
    *  PSU_DDR_PHY_DTCR0_DTDRS                                     0x0

    * Data Training with Early/Extended Gate
    *  PSU_DDR_PHY_DTCR0_DTEXG                                     0x0

    * Data Training Extended Write DQS
    *  PSU_DDR_PHY_DTCR0_DTEXD                                     0x0

    * Data Training Debug Step
    *  PSU_DDR_PHY_DTCR0_DTDSTP                                    0x0

    * Data Training Debug Enable
    *  PSU_DDR_PHY_DTCR0_DTDEN                                     0x0

    * Data Training Debug Byte Select
    *  PSU_DDR_PHY_DTCR0_DTDBS                                     0x0

    * Data Training read DBI deskewing configuration
    *  PSU_DDR_PHY_DTCR0_DTRDBITR                                  0x2

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DTCR0_RESERVED_13                               0x0

    * Data Training Write Bit Deskew Data Mask
    *  PSU_DDR_PHY_DTCR0_DTWBDDM                                   0x1

    * Refreshes Issued During Entry to Training
    *  PSU_DDR_PHY_DTCR0_RFSHEN                                    0x1

    * Data Training Compare Data
    *  PSU_DDR_PHY_DTCR0_DTCMPD                                    0x1

    * Data Training Using MPR
    *  PSU_DDR_PHY_DTCR0_DTMPR                                     0x1

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DTCR0_RESERVED_5_4                              0x0

    * Data Training Repeat Number
    *  PSU_DDR_PHY_DTCR0_DTRPTN                                    0x7

    * Data Training Configuration Register 0
    * (OFFSET, MASK, VALUE)      (0XFD080200, 0xFFFFFFFFU ,0x800091C7U)
    */
	PSU_Mask_Write(DDR_PHY_DTCR0_OFFSET, 0xFFFFFFFFU, 0x800091C7U);
/*##################################################################### */

    /*
    * Register : DTCR1 @ 0XFD080204

    * Rank Enable.
    *  PSU_DDR_PHY_DTCR1_RANKEN_RSVD                               0x0

    * Rank Enable.
    *  PSU_DDR_PHY_DTCR1_RANKEN                                    0x1

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DTCR1_RESERVED_15_14                            0x0

    * Data Training Rank
    *  PSU_DDR_PHY_DTCR1_DTRANK                                    0x0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DTCR1_RESERVED_11                               0x0

    * Read Leveling Gate Sampling Difference
    *  PSU_DDR_PHY_DTCR1_RDLVLGDIFF                                0x2

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DTCR1_RESERVED_7                                0x0

    * Read Leveling Gate Shift
    *  PSU_DDR_PHY_DTCR1_RDLVLGS                                   0x3

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DTCR1_RESERVED_3                                0x0

    * Read Preamble Training enable
    *  PSU_DDR_PHY_DTCR1_RDPRMVL_TRN                               0x1

    * Read Leveling Enable
    *  PSU_DDR_PHY_DTCR1_RDLVLEN                                   0x1

    * Basic Gate Training Enable
    *  PSU_DDR_PHY_DTCR1_BSTEN                                     0x0

    * Data Training Configuration Register 1
    * (OFFSET, MASK, VALUE)      (0XFD080204, 0xFFFFFFFFU ,0x00010236U)
    */
	PSU_Mask_Write(DDR_PHY_DTCR1_OFFSET, 0xFFFFFFFFU, 0x00010236U);
/*##################################################################### */

    /*
    * Register : CATR0 @ 0XFD080240

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_CATR0_RESERVED_31_21                            0x0

    * Minimum time (in terms of number of dram clocks) between two consectuve
    * CA calibration command
    *  PSU_DDR_PHY_CATR0_CACD                                      0x14

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_CATR0_RESERVED_15_13                            0x0

    * Minimum time (in terms of number of dram clocks) PUB should wait before
    * sampling the CA response after Calibration command has been sent to the
    * memory
    *  PSU_DDR_PHY_CATR0_CAADR                                     0x10

    * CA_1 Response Byte Lane 1
    *  PSU_DDR_PHY_CATR0_CA1BYTE1                                  0x5

    * CA_1 Response Byte Lane 0
    *  PSU_DDR_PHY_CATR0_CA1BYTE0                                  0x4

    * CA Training Register 0
    * (OFFSET, MASK, VALUE)      (0XFD080240, 0xFFFFFFFFU ,0x00141054U)
    */
	PSU_Mask_Write(DDR_PHY_CATR0_OFFSET, 0xFFFFFFFFU, 0x00141054U);
/*##################################################################### */

    /*
    * Register : DQSDR0 @ 0XFD080250

    * Number of delay taps by which the DQS gate LCDL will be updated when DQS
    *  drift is detected
    *  PSU_DDR_PHY_DQSDR0_DFTDLY                                   0x0

    * Drift Impedance Update
    *  PSU_DDR_PHY_DQSDR0_DFTZQUP                                  0x0

    * Drift DDL Update
    *  PSU_DDR_PHY_DQSDR0_DFTDDLUP                                 0x0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DQSDR0_RESERVED_25_22                           0x0

    * Drift Read Spacing
    *  PSU_DDR_PHY_DQSDR0_DFTRDSPC                                 0x0

    * Drift Back-to-Back Reads
    *  PSU_DDR_PHY_DQSDR0_DFTB2BRD                                 0x8

    * Drift Idle Reads
    *  PSU_DDR_PHY_DQSDR0_DFTIDLRD                                 0x8

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DQSDR0_RESERVED_11_8                            0x0

    * Gate Pulse Enable
    *  PSU_DDR_PHY_DQSDR0_DFTGPULSE                                0x0

    * DQS Drift Update Mode
    *  PSU_DDR_PHY_DQSDR0_DFTUPMODE                                0x0

    * DQS Drift Detection Mode
    *  PSU_DDR_PHY_DQSDR0_DFTDTMODE                                0x0

    * DQS Drift Detection Enable
    *  PSU_DDR_PHY_DQSDR0_DFTDTEN                                  0x0

    * DQS Drift Register 0
    * (OFFSET, MASK, VALUE)      (0XFD080250, 0xFFFFFFFFU ,0x00088000U)
    */
	PSU_Mask_Write(DDR_PHY_DQSDR0_OFFSET, 0xFFFFFFFFU, 0x00088000U);
/*##################################################################### */

    /*
    * Register : BISTLSR @ 0XFD080414

    * LFSR seed for pseudo-random BIST patterns
    *  PSU_DDR_PHY_BISTLSR_SEED                                    0x12341000

    * BIST LFSR Seed Register
    * (OFFSET, MASK, VALUE)      (0XFD080414, 0xFFFFFFFFU ,0x12341000U)
    */
	PSU_Mask_Write(DDR_PHY_BISTLSR_OFFSET, 0xFFFFFFFFU, 0x12341000U);
/*##################################################################### */

    /*
    * Register : RIOCR5 @ 0XFD0804F4

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_RIOCR5_RESERVED_31_16                           0x0

    * Reserved. Return zeros on reads.
    *  PSU_DDR_PHY_RIOCR5_ODTOEMODE_RSVD                           0x0

    * SDRAM On-die Termination Output Enable (OE) Mode Selection.
    *  PSU_DDR_PHY_RIOCR5_ODTOEMODE                                0x5

    * Rank I/O Configuration Register 5
    * (OFFSET, MASK, VALUE)      (0XFD0804F4, 0xFFFFFFFFU ,0x00000005U)
    */
	PSU_Mask_Write(DDR_PHY_RIOCR5_OFFSET, 0xFFFFFFFFU, 0x00000005U);
/*##################################################################### */

    /*
    * Register : ACIOCR0 @ 0XFD080500

    * Address/Command Slew Rate (D3F I/O Only)
    *  PSU_DDR_PHY_ACIOCR0_ACSR                                    0x0

    * SDRAM Reset I/O Mode
    *  PSU_DDR_PHY_ACIOCR0_RSTIOM                                  0x1

    * SDRAM Reset Power Down Receiver
    *  PSU_DDR_PHY_ACIOCR0_RSTPDR                                  0x1

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_ACIOCR0_RESERVED_27                             0x0

    * SDRAM Reset On-Die Termination
    *  PSU_DDR_PHY_ACIOCR0_RSTODT                                  0x0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_ACIOCR0_RESERVED_25_10                          0x0

    * CK Duty Cycle Correction
    *  PSU_DDR_PHY_ACIOCR0_CKDCC                                   0x0

    * AC Power Down Receiver Mode
    *  PSU_DDR_PHY_ACIOCR0_ACPDRMODE                               0x2

    * AC On-die Termination Mode
    *  PSU_DDR_PHY_ACIOCR0_ACODTMODE                               0x2

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_ACIOCR0_RESERVED_1                              0x0

    * Control delayed or non-delayed clock to CS_N/ODT?CKE AC slices.
    *  PSU_DDR_PHY_ACIOCR0_ACRANKCLKSEL                            0x0

    * AC I/O Configuration Register 0
    * (OFFSET, MASK, VALUE)      (0XFD080500, 0xFFFFFFFFU ,0x30000028U)
    */
	PSU_Mask_Write(DDR_PHY_ACIOCR0_OFFSET, 0xFFFFFFFFU, 0x30000028U);
/*##################################################################### */

    /*
    * Register : ACIOCR2 @ 0XFD080508

    * Clock gating for glue logic inside CLKGEN and glue logic inside CONTROL
    * slice
    *  PSU_DDR_PHY_ACIOCR2_CLKGENCLKGATE                           0x0

    * Clock gating for Output Enable D slices [0]
    *  PSU_DDR_PHY_ACIOCR2_ACOECLKGATE0                            0x0

    * Clock gating for Power Down Receiver D slices [0]
    *  PSU_DDR_PHY_ACIOCR2_ACPDRCLKGATE0                           0x0

    * Clock gating for Termination Enable D slices [0]
    *  PSU_DDR_PHY_ACIOCR2_ACTECLKGATE0                            0x0

    * Clock gating for CK# D slices [1:0]
    *  PSU_DDR_PHY_ACIOCR2_CKNCLKGATE0                             0x2

    * Clock gating for CK D slices [1:0]
    *  PSU_DDR_PHY_ACIOCR2_CKCLKGATE0                              0x2

    * Clock gating for AC D slices [23:0]
    *  PSU_DDR_PHY_ACIOCR2_ACCLKGATE0                              0x0

    * AC I/O Configuration Register 2
    * (OFFSET, MASK, VALUE)      (0XFD080508, 0xFFFFFFFFU ,0x0A000000U)
    */
	PSU_Mask_Write(DDR_PHY_ACIOCR2_OFFSET, 0xFFFFFFFFU, 0x0A000000U);
/*##################################################################### */

    /*
    * Register : ACIOCR3 @ 0XFD08050C

    * SDRAM Parity Output Enable (OE) Mode Selection
    *  PSU_DDR_PHY_ACIOCR3_PAROEMODE                               0x0

    * SDRAM Bank Group Output Enable (OE) Mode Selection
    *  PSU_DDR_PHY_ACIOCR3_BGOEMODE                                0x0

    * SDRAM Bank Address Output Enable (OE) Mode Selection
    *  PSU_DDR_PHY_ACIOCR3_BAOEMODE                                0x0

    * SDRAM A[17] Output Enable (OE) Mode Selection
    *  PSU_DDR_PHY_ACIOCR3_A17OEMODE                               0x0

    * SDRAM A[16] / RAS_n Output Enable (OE) Mode Selection
    *  PSU_DDR_PHY_ACIOCR3_A16OEMODE                               0x0

    * SDRAM ACT_n Output Enable (OE) Mode Selection (DDR4 only)
    *  PSU_DDR_PHY_ACIOCR3_ACTOEMODE                               0x0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_ACIOCR3_RESERVED_15_8                           0x0

    * Reserved. Return zeros on reads.
    *  PSU_DDR_PHY_ACIOCR3_CKOEMODE_RSVD                           0x0

    * SDRAM CK Output Enable (OE) Mode Selection.
    *  PSU_DDR_PHY_ACIOCR3_CKOEMODE                                0x9

    * AC I/O Configuration Register 3
    * (OFFSET, MASK, VALUE)      (0XFD08050C, 0xFFFFFFFFU ,0x00000009U)
    */
	PSU_Mask_Write(DDR_PHY_ACIOCR3_OFFSET, 0xFFFFFFFFU, 0x00000009U);
/*##################################################################### */

    /*
    * Register : ACIOCR4 @ 0XFD080510

    * Clock gating for AC LB slices and loopback read valid slices
    *  PSU_DDR_PHY_ACIOCR4_LBCLKGATE                               0x0

    * Clock gating for Output Enable D slices [1]
    *  PSU_DDR_PHY_ACIOCR4_ACOECLKGATE1                            0x0

    * Clock gating for Power Down Receiver D slices [1]
    *  PSU_DDR_PHY_ACIOCR4_ACPDRCLKGATE1                           0x0

    * Clock gating for Termination Enable D slices [1]
    *  PSU_DDR_PHY_ACIOCR4_ACTECLKGATE1                            0x0

    * Clock gating for CK# D slices [3:2]
    *  PSU_DDR_PHY_ACIOCR4_CKNCLKGATE1                             0x2

    * Clock gating for CK D slices [3:2]
    *  PSU_DDR_PHY_ACIOCR4_CKCLKGATE1                              0x2

    * Clock gating for AC D slices [47:24]
    *  PSU_DDR_PHY_ACIOCR4_ACCLKGATE1                              0x0

    * AC I/O Configuration Register 4
    * (OFFSET, MASK, VALUE)      (0XFD080510, 0xFFFFFFFFU ,0x0A000000U)
    */
	PSU_Mask_Write(DDR_PHY_ACIOCR4_OFFSET, 0xFFFFFFFFU, 0x0A000000U);
/*##################################################################### */

    /*
    * Register : IOVCR0 @ 0XFD080520

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_IOVCR0_RESERVED_31_29                           0x0

    * Address/command lane VREF Pad Enable
    *  PSU_DDR_PHY_IOVCR0_ACREFPEN                                 0x0

    * Address/command lane Internal VREF Enable
    *  PSU_DDR_PHY_IOVCR0_ACREFEEN                                 0x0

    * Address/command lane Single-End VREF Enable
    *  PSU_DDR_PHY_IOVCR0_ACREFSEN                                 0x1

    * Address/command lane Internal VREF Enable
    *  PSU_DDR_PHY_IOVCR0_ACREFIEN                                 0x1

    * External VREF generato REFSEL range select
    *  PSU_DDR_PHY_IOVCR0_ACREFESELRANGE                           0x0

    * Address/command lane External VREF Select
    *  PSU_DDR_PHY_IOVCR0_ACREFESEL                                0x0

    * Single ended VREF generator REFSEL range select
    *  PSU_DDR_PHY_IOVCR0_ACREFSSELRANGE                           0x1

    * Address/command lane Single-End VREF Select
    *  PSU_DDR_PHY_IOVCR0_ACREFSSEL                                0x30

    * Internal VREF generator REFSEL ragne select
    *  PSU_DDR_PHY_IOVCR0_ACVREFISELRANGE                          0x1

    * REFSEL Control for internal AC IOs
    *  PSU_DDR_PHY_IOVCR0_ACVREFISEL                               0x4e

    * IO VREF Control Register 0
    * (OFFSET, MASK, VALUE)      (0XFD080520, 0xFFFFFFFFU ,0x0300B0CEU)
    */
	PSU_Mask_Write(DDR_PHY_IOVCR0_OFFSET, 0xFFFFFFFFU, 0x0300B0CEU);
/*##################################################################### */

    /*
    * Register : VTCR0 @ 0XFD080528

    * Number of ctl_clk required to meet (> 150ns) timing requirements during
    * DRAM DQ VREF training
    *  PSU_DDR_PHY_VTCR0_TVREF                                     0x7

    * DRM DQ VREF training Enable
    *  PSU_DDR_PHY_VTCR0_DVEN                                      0x1

    * Per Device Addressability Enable
    *  PSU_DDR_PHY_VTCR0_PDAEN                                     0x1

    * Reserved. Returns zeroes on reads.
    *  PSU_DDR_PHY_VTCR0_RESERVED_26                               0x0

    * VREF Word Count
    *  PSU_DDR_PHY_VTCR0_VWCR                                      0x4

    * DRAM DQ VREF step size used during DRAM VREF training
    *  PSU_DDR_PHY_VTCR0_DVSS                                      0x0

    * Maximum VREF limit value used during DRAM VREF training
    *  PSU_DDR_PHY_VTCR0_DVMAX                                     0x32

    * Minimum VREF limit value used during DRAM VREF training
    *  PSU_DDR_PHY_VTCR0_DVMIN                                     0x0

    * Initial DRAM DQ VREF value used during DRAM VREF training
    *  PSU_DDR_PHY_VTCR0_DVINIT                                    0x19

    * VREF Training Control Register 0
    * (OFFSET, MASK, VALUE)      (0XFD080528, 0xFFFFFFFFU ,0xF9032019U)
    */
	PSU_Mask_Write(DDR_PHY_VTCR0_OFFSET, 0xFFFFFFFFU, 0xF9032019U);
/*##################################################################### */

    /*
    * Register : VTCR1 @ 0XFD08052C

    * Host VREF step size used during VREF training. The register value of N i
    * ndicates step size of (N+1)
    *  PSU_DDR_PHY_VTCR1_HVSS                                      0x0

    * Reserved. Returns zeroes on reads.
    *  PSU_DDR_PHY_VTCR1_RESERVED_27                               0x0

    * Maximum VREF limit value used during DRAM VREF training.
    *  PSU_DDR_PHY_VTCR1_HVMAX                                     0x7f

    * Reserved. Returns zeroes on reads.
    *  PSU_DDR_PHY_VTCR1_RESERVED_19                               0x0

    * Minimum VREF limit value used during DRAM VREF training.
    *  PSU_DDR_PHY_VTCR1_HVMIN                                     0x0

    * Reserved. Returns zeroes on reads.
    *  PSU_DDR_PHY_VTCR1_RESERVED_11                               0x0

    * Static Host Vref Rank Value
    *  PSU_DDR_PHY_VTCR1_SHRNK                                     0x0

    * Static Host Vref Rank Enable
    *  PSU_DDR_PHY_VTCR1_SHREN                                     0x1

    * Number of ctl_clk required to meet (> 200ns) VREF Settling timing requir
    * ements during Host IO VREF training
    *  PSU_DDR_PHY_VTCR1_TVREFIO                                   0x7

    * Eye LCDL Offset value for VREF training
    *  PSU_DDR_PHY_VTCR1_EOFF                                      0x0

    * Number of LCDL Eye points for which VREF training is repeated
    *  PSU_DDR_PHY_VTCR1_ENUM                                      0x0

    * HOST (IO) internal VREF training Enable
    *  PSU_DDR_PHY_VTCR1_HVEN                                      0x1

    * Host IO Type Control
    *  PSU_DDR_PHY_VTCR1_HVIO                                      0x1

    * VREF Training Control Register 1
    * (OFFSET, MASK, VALUE)      (0XFD08052C, 0xFFFFFFFFU ,0x07F001E3U)
    */
	PSU_Mask_Write(DDR_PHY_VTCR1_OFFSET, 0xFFFFFFFFU, 0x07F001E3U);
/*##################################################################### */

    /*
    * Register : ACBDLR1 @ 0XFD080544

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_ACBDLR1_RESERVED_31_30                          0x0

    * Delay select for the BDL on Parity.
    *  PSU_DDR_PHY_ACBDLR1_PARBD                                   0x0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_ACBDLR1_RESERVED_23_22                          0x0

    * Delay select for the BDL on Address A[16]. In DDR3 mode this pin is conn
    * ected to WE.
    *  PSU_DDR_PHY_ACBDLR1_A16BD                                   0x0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_ACBDLR1_RESERVED_15_14                          0x0

    * Delay select for the BDL on Address A[17]. When not in DDR4 modemode thi
    * s pin is connected to CAS.
    *  PSU_DDR_PHY_ACBDLR1_A17BD                                   0x0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_ACBDLR1_RESERVED_7_6                            0x0

    * Delay select for the BDL on ACTN.
    *  PSU_DDR_PHY_ACBDLR1_ACTBD                                   0x0

    * AC Bit Delay Line Register 1
    * (OFFSET, MASK, VALUE)      (0XFD080544, 0xFFFFFFFFU ,0x00000000U)
    */
	PSU_Mask_Write(DDR_PHY_ACBDLR1_OFFSET, 0xFFFFFFFFU, 0x00000000U);
/*##################################################################### */

    /*
    * Register : ACBDLR2 @ 0XFD080548

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_ACBDLR2_RESERVED_31_30                          0x0

    * Delay select for the BDL on BG[1].
    *  PSU_DDR_PHY_ACBDLR2_BG1BD                                   0x0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_ACBDLR2_RESERVED_23_22                          0x0

    * Delay select for the BDL on BG[0].
    *  PSU_DDR_PHY_ACBDLR2_BG0BD                                   0x0

    * Reser.ved Return zeroes on reads.
    *  PSU_DDR_PHY_ACBDLR2_RESERVED_15_14                          0x0

    * Delay select for the BDL on BA[1].
    *  PSU_DDR_PHY_ACBDLR2_BA1BD                                   0x0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_ACBDLR2_RESERVED_7_6                            0x0

    * Delay select for the BDL on BA[0].
    *  PSU_DDR_PHY_ACBDLR2_BA0BD                                   0x0

    * AC Bit Delay Line Register 2
    * (OFFSET, MASK, VALUE)      (0XFD080548, 0xFFFFFFFFU ,0x00000000U)
    */
	PSU_Mask_Write(DDR_PHY_ACBDLR2_OFFSET, 0xFFFFFFFFU, 0x00000000U);
/*##################################################################### */

    /*
    * Register : ACBDLR6 @ 0XFD080558

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_ACBDLR6_RESERVED_31_30                          0x0

    * Delay select for the BDL on Address A[3].
    *  PSU_DDR_PHY_ACBDLR6_A03BD                                   0x0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_ACBDLR6_RESERVED_23_22                          0x0

    * Delay select for the BDL on Address A[2].
    *  PSU_DDR_PHY_ACBDLR6_A02BD                                   0x0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_ACBDLR6_RESERVED_15_14                          0x0

    * Delay select for the BDL on Address A[1].
    *  PSU_DDR_PHY_ACBDLR6_A01BD                                   0x0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_ACBDLR6_RESERVED_7_6                            0x0

    * Delay select for the BDL on Address A[0].
    *  PSU_DDR_PHY_ACBDLR6_A00BD                                   0x0

    * AC Bit Delay Line Register 6
    * (OFFSET, MASK, VALUE)      (0XFD080558, 0xFFFFFFFFU ,0x00000000U)
    */
	PSU_Mask_Write(DDR_PHY_ACBDLR6_OFFSET, 0xFFFFFFFFU, 0x00000000U);
/*##################################################################### */

    /*
    * Register : ACBDLR7 @ 0XFD08055C

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_ACBDLR7_RESERVED_31_30                          0x0

    * Delay select for the BDL on Address A[7].
    *  PSU_DDR_PHY_ACBDLR7_A07BD                                   0x0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_ACBDLR7_RESERVED_23_22                          0x0

    * Delay select for the BDL on Address A[6].
    *  PSU_DDR_PHY_ACBDLR7_A06BD                                   0x0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_ACBDLR7_RESERVED_15_14                          0x0

    * Delay select for the BDL on Address A[5].
    *  PSU_DDR_PHY_ACBDLR7_A05BD                                   0x0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_ACBDLR7_RESERVED_7_6                            0x0

    * Delay select for the BDL on Address A[4].
    *  PSU_DDR_PHY_ACBDLR7_A04BD                                   0x0

    * AC Bit Delay Line Register 7
    * (OFFSET, MASK, VALUE)      (0XFD08055C, 0xFFFFFFFFU ,0x00000000U)
    */
	PSU_Mask_Write(DDR_PHY_ACBDLR7_OFFSET, 0xFFFFFFFFU, 0x00000000U);
/*##################################################################### */

    /*
    * Register : ACBDLR8 @ 0XFD080560

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_ACBDLR8_RESERVED_31_30                          0x0

    * Delay select for the BDL on Address A[11].
    *  PSU_DDR_PHY_ACBDLR8_A11BD                                   0x0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_ACBDLR8_RESERVED_23_22                          0x0

    * Delay select for the BDL on Address A[10].
    *  PSU_DDR_PHY_ACBDLR8_A10BD                                   0x0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_ACBDLR8_RESERVED_15_14                          0x0

    * Delay select for the BDL on Address A[9].
    *  PSU_DDR_PHY_ACBDLR8_A09BD                                   0x0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_ACBDLR8_RESERVED_7_6                            0x0

    * Delay select for the BDL on Address A[8].
    *  PSU_DDR_PHY_ACBDLR8_A08BD                                   0x0

    * AC Bit Delay Line Register 8
    * (OFFSET, MASK, VALUE)      (0XFD080560, 0xFFFFFFFFU ,0x00000000U)
    */
	PSU_Mask_Write(DDR_PHY_ACBDLR8_OFFSET, 0xFFFFFFFFU, 0x00000000U);
/*##################################################################### */

    /*
    * Register : ACBDLR9 @ 0XFD080564

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_ACBDLR9_RESERVED_31_30                          0x0

    * Delay select for the BDL on Address A[15].
    *  PSU_DDR_PHY_ACBDLR9_A15BD                                   0x0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_ACBDLR9_RESERVED_23_22                          0x0

    * Delay select for the BDL on Address A[14].
    *  PSU_DDR_PHY_ACBDLR9_A14BD                                   0x0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_ACBDLR9_RESERVED_15_14                          0x0

    * Delay select for the BDL on Address A[13].
    *  PSU_DDR_PHY_ACBDLR9_A13BD                                   0x0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_ACBDLR9_RESERVED_7_6                            0x0

    * Delay select for the BDL on Address A[12].
    *  PSU_DDR_PHY_ACBDLR9_A12BD                                   0x0

    * AC Bit Delay Line Register 9
    * (OFFSET, MASK, VALUE)      (0XFD080564, 0xFFFFFFFFU ,0x00000000U)
    */
	PSU_Mask_Write(DDR_PHY_ACBDLR9_OFFSET, 0xFFFFFFFFU, 0x00000000U);
/*##################################################################### */

    /*
    * Register : ZQCR @ 0XFD080680

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_ZQCR_RESERVED_31_26                             0x0

    * ZQ VREF Range
    *  PSU_DDR_PHY_ZQCR_ZQREFISELRANGE                             0x0

    * Programmable Wait for Frequency B
    *  PSU_DDR_PHY_ZQCR_PGWAIT_FRQB                                0x11

    * Programmable Wait for Frequency A
    *  PSU_DDR_PHY_ZQCR_PGWAIT_FRQA                                0x15

    * ZQ VREF Pad Enable
    *  PSU_DDR_PHY_ZQCR_ZQREFPEN                                   0x0

    * ZQ Internal VREF Enable
    *  PSU_DDR_PHY_ZQCR_ZQREFIEN                                   0x1

    * Choice of termination mode
    *  PSU_DDR_PHY_ZQCR_ODT_MODE                                   0x1

    * Force ZCAL VT update
    *  PSU_DDR_PHY_ZQCR_FORCE_ZCAL_VT_UPDATE                       0x0

    * IO VT Drift Limit
    *  PSU_DDR_PHY_ZQCR_IODLMT                                     0x2

    * Averaging algorithm enable, if set, enables averaging algorithm
    *  PSU_DDR_PHY_ZQCR_AVGEN                                      0x1

    * Maximum number of averaging rounds to be used by averaging algorithm
    *  PSU_DDR_PHY_ZQCR_AVGMAX                                     0x2

    * ZQ Calibration Type
    *  PSU_DDR_PHY_ZQCR_ZCALT                                      0x0

    * ZQ Power Down
    *  PSU_DDR_PHY_ZQCR_ZQPD                                       0x0

    * ZQ Impedance Control Register
    * (OFFSET, MASK, VALUE)      (0XFD080680, 0xFFFFFFFFU ,0x008AAA58U)
    */
	PSU_Mask_Write(DDR_PHY_ZQCR_OFFSET, 0xFFFFFFFFU, 0x008AAA58U);
/*##################################################################### */

    /*
    * Register : ZQ0PR0 @ 0XFD080684

    * Pull-down drive strength ZCTRL over-ride enable
    *  PSU_DDR_PHY_ZQ0PR0_PD_DRV_ZDEN                              0x0

    * Pull-up drive strength ZCTRL over-ride enable
    *  PSU_DDR_PHY_ZQ0PR0_PU_DRV_ZDEN                              0x0

    * Pull-down termination ZCTRL over-ride enable
    *  PSU_DDR_PHY_ZQ0PR0_PD_ODT_ZDEN                              0x0

    * Pull-up termination ZCTRL over-ride enable
    *  PSU_DDR_PHY_ZQ0PR0_PU_ODT_ZDEN                              0x0

    * Calibration segment bypass
    *  PSU_DDR_PHY_ZQ0PR0_ZSEGBYP                                  0x0

    * VREF latch mode controls the mode in which the ZLE pin of the PVREF cell
    *  is driven by the PUB
    *  PSU_DDR_PHY_ZQ0PR0_ZLE_MODE                                 0x0

    * Termination adjustment
    *  PSU_DDR_PHY_ZQ0PR0_ODT_ADJUST                               0x0

    * Pulldown drive strength adjustment
    *  PSU_DDR_PHY_ZQ0PR0_PD_DRV_ADJUST                            0x0

    * Pullup drive strength adjustment
    *  PSU_DDR_PHY_ZQ0PR0_PU_DRV_ADJUST                            0x0

    * DRAM Impedance Divide Ratio
    *  PSU_DDR_PHY_ZQ0PR0_ZPROG_DRAM_ODT                           0x7

    * HOST Impedance Divide Ratio
    *  PSU_DDR_PHY_ZQ0PR0_ZPROG_HOST_ODT                           0x9

    * Impedance Divide Ratio (pulldown drive calibration during asymmetric dri
    * ve strength calibration)
    *  PSU_DDR_PHY_ZQ0PR0_ZPROG_ASYM_DRV_PD                        0xd

    * Impedance Divide Ratio (pullup drive calibration during asymmetric drive
    *  strength calibration)
    *  PSU_DDR_PHY_ZQ0PR0_ZPROG_ASYM_DRV_PU                        0xd

    * ZQ n Impedance Control Program Register 0
    * (OFFSET, MASK, VALUE)      (0XFD080684, 0xFFFFFFFFU ,0x000079DDU)
    */
	PSU_Mask_Write(DDR_PHY_ZQ0PR0_OFFSET, 0xFFFFFFFFU, 0x000079DDU);
/*##################################################################### */

    /*
    * Register : ZQ0OR0 @ 0XFD080694

    * Reserved. Return zeros on reads.
    *  PSU_DDR_PHY_ZQ0OR0_RESERVED_31_26                           0x0

    * Override value for the pull-up output impedance
    *  PSU_DDR_PHY_ZQ0OR0_ZDATA_PU_DRV_OVRD                        0x1e1

    * Reserved. Return zeros on reads.
    *  PSU_DDR_PHY_ZQ0OR0_RESERVED_15_10                           0x0

    * Override value for the pull-down output impedance
    *  PSU_DDR_PHY_ZQ0OR0_ZDATA_PD_DRV_OVRD                        0x210

    * ZQ n Impedance Control Override Data Register 0
    * (OFFSET, MASK, VALUE)      (0XFD080694, 0xFFFFFFFFU ,0x01E10210U)
    */
	PSU_Mask_Write(DDR_PHY_ZQ0OR0_OFFSET, 0xFFFFFFFFU, 0x01E10210U);
/*##################################################################### */

    /*
    * Register : ZQ0OR1 @ 0XFD080698

    * Reserved. Return zeros on reads.
    *  PSU_DDR_PHY_ZQ0OR1_RESERVED_31_26                           0x0

    * Override value for the pull-up termination
    *  PSU_DDR_PHY_ZQ0OR1_ZDATA_PU_ODT_OVRD                        0x1e1

    * Reserved. Return zeros on reads.
    *  PSU_DDR_PHY_ZQ0OR1_RESERVED_15_10                           0x0

    * Override value for the pull-down termination
    *  PSU_DDR_PHY_ZQ0OR1_ZDATA_PD_ODT_OVRD                        0x0

    * ZQ n Impedance Control Override Data Register 1
    * (OFFSET, MASK, VALUE)      (0XFD080698, 0xFFFFFFFFU ,0x01E10000U)
    */
	PSU_Mask_Write(DDR_PHY_ZQ0OR1_OFFSET, 0xFFFFFFFFU, 0x01E10000U);
/*##################################################################### */

    /*
    * Register : ZQ1PR0 @ 0XFD0806A4

    * Pull-down drive strength ZCTRL over-ride enable
    *  PSU_DDR_PHY_ZQ1PR0_PD_DRV_ZDEN                              0x0

    * Pull-up drive strength ZCTRL over-ride enable
    *  PSU_DDR_PHY_ZQ1PR0_PU_DRV_ZDEN                              0x0

    * Pull-down termination ZCTRL over-ride enable
    *  PSU_DDR_PHY_ZQ1PR0_PD_ODT_ZDEN                              0x0

    * Pull-up termination ZCTRL over-ride enable
    *  PSU_DDR_PHY_ZQ1PR0_PU_ODT_ZDEN                              0x0

    * Calibration segment bypass
    *  PSU_DDR_PHY_ZQ1PR0_ZSEGBYP                                  0x0

    * VREF latch mode controls the mode in which the ZLE pin of the PVREF cell
    *  is driven by the PUB
    *  PSU_DDR_PHY_ZQ1PR0_ZLE_MODE                                 0x0

    * Termination adjustment
    *  PSU_DDR_PHY_ZQ1PR0_ODT_ADJUST                               0x0

    * Pulldown drive strength adjustment
    *  PSU_DDR_PHY_ZQ1PR0_PD_DRV_ADJUST                            0x1

    * Pullup drive strength adjustment
    *  PSU_DDR_PHY_ZQ1PR0_PU_DRV_ADJUST                            0x0

    * DRAM Impedance Divide Ratio
    *  PSU_DDR_PHY_ZQ1PR0_ZPROG_DRAM_ODT                           0x7

    * HOST Impedance Divide Ratio
    *  PSU_DDR_PHY_ZQ1PR0_ZPROG_HOST_ODT                           0xb

    * Impedance Divide Ratio (pulldown drive calibration during asymmetric dri
    * ve strength calibration)
    *  PSU_DDR_PHY_ZQ1PR0_ZPROG_ASYM_DRV_PD                        0xd

    * Impedance Divide Ratio (pullup drive calibration during asymmetric drive
    *  strength calibration)
    *  PSU_DDR_PHY_ZQ1PR0_ZPROG_ASYM_DRV_PU                        0xb

    * ZQ n Impedance Control Program Register 0
    * (OFFSET, MASK, VALUE)      (0XFD0806A4, 0xFFFFFFFFU ,0x00087BDBU)
    */
	PSU_Mask_Write(DDR_PHY_ZQ1PR0_OFFSET, 0xFFFFFFFFU, 0x00087BDBU);
/*##################################################################### */

    /*
    * Register : DX0GCR0 @ 0XFD080700

    * Calibration Bypass
    *  PSU_DDR_PHY_DX0GCR0_CALBYP                                  0x0

    * Master Delay Line Enable
    *  PSU_DDR_PHY_DX0GCR0_MDLEN                                   0x1

    * Configurable ODT(TE) Phase Shift
    *  PSU_DDR_PHY_DX0GCR0_CODTSHFT                                0x0

    * DQS Duty Cycle Correction
    *  PSU_DDR_PHY_DX0GCR0_DQSDCC                                  0x0

    * Number of Cycles ( in terms of ctl_clk) to generate ctl_dx_get_static_rd
    *  input for the respective bypte lane of the PHY
    *  PSU_DDR_PHY_DX0GCR0_RDDLY                                   0x8

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX0GCR0_RESERVED_19_14                          0x0

    * DQSNSE Power Down Receiver
    *  PSU_DDR_PHY_DX0GCR0_DQSNSEPDR                               0x0

    * DQSSE Power Down Receiver
    *  PSU_DDR_PHY_DX0GCR0_DQSSEPDR                                0x0

    * RTT On Additive Latency
    *  PSU_DDR_PHY_DX0GCR0_RTTOAL                                  0x0

    * RTT Output Hold
    *  PSU_DDR_PHY_DX0GCR0_RTTOH                                   0x3

    * Configurable PDR Phase Shift
    *  PSU_DDR_PHY_DX0GCR0_CPDRSHFT                                0x0

    * DQSR Power Down
    *  PSU_DDR_PHY_DX0GCR0_DQSRPD                                  0x0

    * DQSG Power Down Receiver
    *  PSU_DDR_PHY_DX0GCR0_DQSGPDR                                 0x0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX0GCR0_RESERVED_4                              0x0

    * DQSG On-Die Termination
    *  PSU_DDR_PHY_DX0GCR0_DQSGODT                                 0x0

    * DQSG Output Enable
    *  PSU_DDR_PHY_DX0GCR0_DQSGOE                                  0x1

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX0GCR0_RESERVED_1_0                            0x0

    * DATX8 n General Configuration Register 0
    * (OFFSET, MASK, VALUE)      (0XFD080700, 0xFFFFFFFFU ,0x40800604U)
    */
	PSU_Mask_Write(DDR_PHY_DX0GCR0_OFFSET, 0xFFFFFFFFU, 0x40800604U);
/*##################################################################### */

    /*
    * Register : DX0GCR4 @ 0XFD080710

    * Byte lane VREF IOM (Used only by D4MU IOs)
    *  PSU_DDR_PHY_DX0GCR4_RESERVED_31_29                          0x0

    * Byte Lane VREF Pad Enable
    *  PSU_DDR_PHY_DX0GCR4_DXREFPEN                                0x0

    * Byte Lane Internal VREF Enable
    *  PSU_DDR_PHY_DX0GCR4_DXREFEEN                                0x3

    * Byte Lane Single-End VREF Enable
    *  PSU_DDR_PHY_DX0GCR4_DXREFSEN                                0x1

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX0GCR4_RESERVED_24                             0x0

    * External VREF generator REFSEL range select
    *  PSU_DDR_PHY_DX0GCR4_DXREFESELRANGE                          0x0

    * Byte Lane External VREF Select
    *  PSU_DDR_PHY_DX0GCR4_DXREFESEL                               0x0

    * Single ended VREF generator REFSEL range select
    *  PSU_DDR_PHY_DX0GCR4_DXREFSSELRANGE                          0x1

    * Byte Lane Single-End VREF Select
    *  PSU_DDR_PHY_DX0GCR4_DXREFSSEL                               0x30

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX0GCR4_RESERVED_7_6                            0x0

    * VREF Enable control for DQ IO (Single Ended) buffers of a byte lane.
    *  PSU_DDR_PHY_DX0GCR4_DXREFIEN                                0xf

    * VRMON control for DQ IO (Single Ended) buffers of a byte lane.
    *  PSU_DDR_PHY_DX0GCR4_DXREFIMON                               0x0

    * DATX8 n General Configuration Register 4
    * (OFFSET, MASK, VALUE)      (0XFD080710, 0xFFFFFFFFU ,0x0E00B03CU)
    */
	PSU_Mask_Write(DDR_PHY_DX0GCR4_OFFSET, 0xFFFFFFFFU, 0x0E00B03CU);
/*##################################################################### */

    /*
    * Register : DX0GCR5 @ 0XFD080714

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX0GCR5_RESERVED_31                             0x0

    * Byte Lane internal VREF Select for Rank 3
    *  PSU_DDR_PHY_DX0GCR5_DXREFISELR3                             0x9

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX0GCR5_RESERVED_23                             0x0

    * Byte Lane internal VREF Select for Rank 2
    *  PSU_DDR_PHY_DX0GCR5_DXREFISELR2                             0x9

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX0GCR5_RESERVED_15                             0x0

    * Byte Lane internal VREF Select for Rank 1
    *  PSU_DDR_PHY_DX0GCR5_DXREFISELR1                             0x55

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX0GCR5_RESERVED_7                              0x0

    * Byte Lane internal VREF Select for Rank 0
    *  PSU_DDR_PHY_DX0GCR5_DXREFISELR0                             0x55

    * DATX8 n General Configuration Register 5
    * (OFFSET, MASK, VALUE)      (0XFD080714, 0xFFFFFFFFU ,0x09095555U)
    */
	PSU_Mask_Write(DDR_PHY_DX0GCR5_OFFSET, 0xFFFFFFFFU, 0x09095555U);
/*##################################################################### */

    /*
    * Register : DX0GCR6 @ 0XFD080718

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX0GCR6_RESERVED_31_30                          0x0

    * DRAM DQ VREF Select for Rank3
    *  PSU_DDR_PHY_DX0GCR6_DXDQVREFR3                              0x9

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX0GCR6_RESERVED_23_22                          0x0

    * DRAM DQ VREF Select for Rank2
    *  PSU_DDR_PHY_DX0GCR6_DXDQVREFR2                              0x9

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX0GCR6_RESERVED_15_14                          0x0

    * DRAM DQ VREF Select for Rank1
    *  PSU_DDR_PHY_DX0GCR6_DXDQVREFR1                              0x2b

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX0GCR6_RESERVED_7_6                            0x0

    * DRAM DQ VREF Select for Rank0
    *  PSU_DDR_PHY_DX0GCR6_DXDQVREFR0                              0x2b

    * DATX8 n General Configuration Register 6
    * (OFFSET, MASK, VALUE)      (0XFD080718, 0xFFFFFFFFU ,0x09092B2BU)
    */
	PSU_Mask_Write(DDR_PHY_DX0GCR6_OFFSET, 0xFFFFFFFFU, 0x09092B2BU);
/*##################################################################### */

    /*
    * Register : DX1GCR0 @ 0XFD080800

    * Calibration Bypass
    *  PSU_DDR_PHY_DX1GCR0_CALBYP                                  0x0

    * Master Delay Line Enable
    *  PSU_DDR_PHY_DX1GCR0_MDLEN                                   0x1

    * Configurable ODT(TE) Phase Shift
    *  PSU_DDR_PHY_DX1GCR0_CODTSHFT                                0x0

    * DQS Duty Cycle Correction
    *  PSU_DDR_PHY_DX1GCR0_DQSDCC                                  0x0

    * Number of Cycles ( in terms of ctl_clk) to generate ctl_dx_get_static_rd
    *  input for the respective bypte lane of the PHY
    *  PSU_DDR_PHY_DX1GCR0_RDDLY                                   0x8

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX1GCR0_RESERVED_19_14                          0x0

    * DQSNSE Power Down Receiver
    *  PSU_DDR_PHY_DX1GCR0_DQSNSEPDR                               0x0

    * DQSSE Power Down Receiver
    *  PSU_DDR_PHY_DX1GCR0_DQSSEPDR                                0x0

    * RTT On Additive Latency
    *  PSU_DDR_PHY_DX1GCR0_RTTOAL                                  0x0

    * RTT Output Hold
    *  PSU_DDR_PHY_DX1GCR0_RTTOH                                   0x3

    * Configurable PDR Phase Shift
    *  PSU_DDR_PHY_DX1GCR0_CPDRSHFT                                0x0

    * DQSR Power Down
    *  PSU_DDR_PHY_DX1GCR0_DQSRPD                                  0x0

    * DQSG Power Down Receiver
    *  PSU_DDR_PHY_DX1GCR0_DQSGPDR                                 0x0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX1GCR0_RESERVED_4                              0x0

    * DQSG On-Die Termination
    *  PSU_DDR_PHY_DX1GCR0_DQSGODT                                 0x0

    * DQSG Output Enable
    *  PSU_DDR_PHY_DX1GCR0_DQSGOE                                  0x1

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX1GCR0_RESERVED_1_0                            0x0

    * DATX8 n General Configuration Register 0
    * (OFFSET, MASK, VALUE)      (0XFD080800, 0xFFFFFFFFU ,0x40800604U)
    */
	PSU_Mask_Write(DDR_PHY_DX1GCR0_OFFSET, 0xFFFFFFFFU, 0x40800604U);
/*##################################################################### */

    /*
    * Register : DX1GCR4 @ 0XFD080810

    * Byte lane VREF IOM (Used only by D4MU IOs)
    *  PSU_DDR_PHY_DX1GCR4_RESERVED_31_29                          0x0

    * Byte Lane VREF Pad Enable
    *  PSU_DDR_PHY_DX1GCR4_DXREFPEN                                0x0

    * Byte Lane Internal VREF Enable
    *  PSU_DDR_PHY_DX1GCR4_DXREFEEN                                0x3

    * Byte Lane Single-End VREF Enable
    *  PSU_DDR_PHY_DX1GCR4_DXREFSEN                                0x1

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX1GCR4_RESERVED_24                             0x0

    * External VREF generator REFSEL range select
    *  PSU_DDR_PHY_DX1GCR4_DXREFESELRANGE                          0x0

    * Byte Lane External VREF Select
    *  PSU_DDR_PHY_DX1GCR4_DXREFESEL                               0x0

    * Single ended VREF generator REFSEL range select
    *  PSU_DDR_PHY_DX1GCR4_DXREFSSELRANGE                          0x1

    * Byte Lane Single-End VREF Select
    *  PSU_DDR_PHY_DX1GCR4_DXREFSSEL                               0x30

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX1GCR4_RESERVED_7_6                            0x0

    * VREF Enable control for DQ IO (Single Ended) buffers of a byte lane.
    *  PSU_DDR_PHY_DX1GCR4_DXREFIEN                                0xf

    * VRMON control for DQ IO (Single Ended) buffers of a byte lane.
    *  PSU_DDR_PHY_DX1GCR4_DXREFIMON                               0x0

    * DATX8 n General Configuration Register 4
    * (OFFSET, MASK, VALUE)      (0XFD080810, 0xFFFFFFFFU ,0x0E00B03CU)
    */
	PSU_Mask_Write(DDR_PHY_DX1GCR4_OFFSET, 0xFFFFFFFFU, 0x0E00B03CU);
/*##################################################################### */

    /*
    * Register : DX1GCR5 @ 0XFD080814

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX1GCR5_RESERVED_31                             0x0

    * Byte Lane internal VREF Select for Rank 3
    *  PSU_DDR_PHY_DX1GCR5_DXREFISELR3                             0x9

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX1GCR5_RESERVED_23                             0x0

    * Byte Lane internal VREF Select for Rank 2
    *  PSU_DDR_PHY_DX1GCR5_DXREFISELR2                             0x9

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX1GCR5_RESERVED_15                             0x0

    * Byte Lane internal VREF Select for Rank 1
    *  PSU_DDR_PHY_DX1GCR5_DXREFISELR1                             0x55

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX1GCR5_RESERVED_7                              0x0

    * Byte Lane internal VREF Select for Rank 0
    *  PSU_DDR_PHY_DX1GCR5_DXREFISELR0                             0x55

    * DATX8 n General Configuration Register 5
    * (OFFSET, MASK, VALUE)      (0XFD080814, 0xFFFFFFFFU ,0x09095555U)
    */
	PSU_Mask_Write(DDR_PHY_DX1GCR5_OFFSET, 0xFFFFFFFFU, 0x09095555U);
/*##################################################################### */

    /*
    * Register : DX1GCR6 @ 0XFD080818

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX1GCR6_RESERVED_31_30                          0x0

    * DRAM DQ VREF Select for Rank3
    *  PSU_DDR_PHY_DX1GCR6_DXDQVREFR3                              0x9

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX1GCR6_RESERVED_23_22                          0x0

    * DRAM DQ VREF Select for Rank2
    *  PSU_DDR_PHY_DX1GCR6_DXDQVREFR2                              0x9

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX1GCR6_RESERVED_15_14                          0x0

    * DRAM DQ VREF Select for Rank1
    *  PSU_DDR_PHY_DX1GCR6_DXDQVREFR1                              0x2b

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX1GCR6_RESERVED_7_6                            0x0

    * DRAM DQ VREF Select for Rank0
    *  PSU_DDR_PHY_DX1GCR6_DXDQVREFR0                              0x2b

    * DATX8 n General Configuration Register 6
    * (OFFSET, MASK, VALUE)      (0XFD080818, 0xFFFFFFFFU ,0x09092B2BU)
    */
	PSU_Mask_Write(DDR_PHY_DX1GCR6_OFFSET, 0xFFFFFFFFU, 0x09092B2BU);
/*##################################################################### */

    /*
    * Register : DX2GCR0 @ 0XFD080900

    * Calibration Bypass
    *  PSU_DDR_PHY_DX2GCR0_CALBYP                                  0x0

    * Master Delay Line Enable
    *  PSU_DDR_PHY_DX2GCR0_MDLEN                                   0x1

    * Configurable ODT(TE) Phase Shift
    *  PSU_DDR_PHY_DX2GCR0_CODTSHFT                                0x0

    * DQS Duty Cycle Correction
    *  PSU_DDR_PHY_DX2GCR0_DQSDCC                                  0x0

    * Number of Cycles ( in terms of ctl_clk) to generate ctl_dx_get_static_rd
    *  input for the respective bypte lane of the PHY
    *  PSU_DDR_PHY_DX2GCR0_RDDLY                                   0x8

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX2GCR0_RESERVED_19_14                          0x0

    * DQSNSE Power Down Receiver
    *  PSU_DDR_PHY_DX2GCR0_DQSNSEPDR                               0x0

    * DQSSE Power Down Receiver
    *  PSU_DDR_PHY_DX2GCR0_DQSSEPDR                                0x0

    * RTT On Additive Latency
    *  PSU_DDR_PHY_DX2GCR0_RTTOAL                                  0x0

    * RTT Output Hold
    *  PSU_DDR_PHY_DX2GCR0_RTTOH                                   0x3

    * Configurable PDR Phase Shift
    *  PSU_DDR_PHY_DX2GCR0_CPDRSHFT                                0x0

    * DQSR Power Down
    *  PSU_DDR_PHY_DX2GCR0_DQSRPD                                  0x0

    * DQSG Power Down Receiver
    *  PSU_DDR_PHY_DX2GCR0_DQSGPDR                                 0x0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX2GCR0_RESERVED_4                              0x0

    * DQSG On-Die Termination
    *  PSU_DDR_PHY_DX2GCR0_DQSGODT                                 0x0

    * DQSG Output Enable
    *  PSU_DDR_PHY_DX2GCR0_DQSGOE                                  0x1

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX2GCR0_RESERVED_1_0                            0x0

    * DATX8 n General Configuration Register 0
    * (OFFSET, MASK, VALUE)      (0XFD080900, 0xFFFFFFFFU ,0x40800604U)
    */
	PSU_Mask_Write(DDR_PHY_DX2GCR0_OFFSET, 0xFFFFFFFFU, 0x40800604U);
/*##################################################################### */

    /*
    * Register : DX2GCR1 @ 0XFD080904

    * Enables the PDR mode for DQ[7:0]
    *  PSU_DDR_PHY_DX2GCR1_DXPDRMODE                               0x0

    * Reserved. Returns zeroes on reads.
    *  PSU_DDR_PHY_DX2GCR1_RESERVED_15                             0x0

    * Select the delayed or non-delayed read data strobe #
    *  PSU_DDR_PHY_DX2GCR1_QSNSEL                                  0x1

    * Select the delayed or non-delayed read data strobe
    *  PSU_DDR_PHY_DX2GCR1_QSSEL                                   0x1

    * Enables Read Data Strobe in a byte lane
    *  PSU_DDR_PHY_DX2GCR1_OEEN                                    0x1

    * Enables PDR in a byte lane
    *  PSU_DDR_PHY_DX2GCR1_PDREN                                   0x1

    * Enables ODT/TE in a byte lane
    *  PSU_DDR_PHY_DX2GCR1_TEEN                                    0x1

    * Enables Write Data strobe in a byte lane
    *  PSU_DDR_PHY_DX2GCR1_DSEN                                    0x1

    * Enables DM pin in a byte lane
    *  PSU_DDR_PHY_DX2GCR1_DMEN                                    0x1

    * Enables DQ corresponding to each bit in a byte
    *  PSU_DDR_PHY_DX2GCR1_DQEN                                    0xff

    * DATX8 n General Configuration Register 1
    * (OFFSET, MASK, VALUE)      (0XFD080904, 0xFFFFFFFFU ,0x00007FFFU)
    */
	PSU_Mask_Write(DDR_PHY_DX2GCR1_OFFSET, 0xFFFFFFFFU, 0x00007FFFU);
/*##################################################################### */

    /*
    * Register : DX2GCR4 @ 0XFD080910

    * Byte lane VREF IOM (Used only by D4MU IOs)
    *  PSU_DDR_PHY_DX2GCR4_RESERVED_31_29                          0x0

    * Byte Lane VREF Pad Enable
    *  PSU_DDR_PHY_DX2GCR4_DXREFPEN                                0x0

    * Byte Lane Internal VREF Enable
    *  PSU_DDR_PHY_DX2GCR4_DXREFEEN                                0x3

    * Byte Lane Single-End VREF Enable
    *  PSU_DDR_PHY_DX2GCR4_DXREFSEN                                0x1

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX2GCR4_RESERVED_24                             0x0

    * External VREF generator REFSEL range select
    *  PSU_DDR_PHY_DX2GCR4_DXREFESELRANGE                          0x0

    * Byte Lane External VREF Select
    *  PSU_DDR_PHY_DX2GCR4_DXREFESEL                               0x0

    * Single ended VREF generator REFSEL range select
    *  PSU_DDR_PHY_DX2GCR4_DXREFSSELRANGE                          0x1

    * Byte Lane Single-End VREF Select
    *  PSU_DDR_PHY_DX2GCR4_DXREFSSEL                               0x30

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX2GCR4_RESERVED_7_6                            0x0

    * VREF Enable control for DQ IO (Single Ended) buffers of a byte lane.
    *  PSU_DDR_PHY_DX2GCR4_DXREFIEN                                0xf

    * VRMON control for DQ IO (Single Ended) buffers of a byte lane.
    *  PSU_DDR_PHY_DX2GCR4_DXREFIMON                               0x0

    * DATX8 n General Configuration Register 4
    * (OFFSET, MASK, VALUE)      (0XFD080910, 0xFFFFFFFFU ,0x0E00B03CU)
    */
	PSU_Mask_Write(DDR_PHY_DX2GCR4_OFFSET, 0xFFFFFFFFU, 0x0E00B03CU);
/*##################################################################### */

    /*
    * Register : DX2GCR5 @ 0XFD080914

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX2GCR5_RESERVED_31                             0x0

    * Byte Lane internal VREF Select for Rank 3
    *  PSU_DDR_PHY_DX2GCR5_DXREFISELR3                             0x9

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX2GCR5_RESERVED_23                             0x0

    * Byte Lane internal VREF Select for Rank 2
    *  PSU_DDR_PHY_DX2GCR5_DXREFISELR2                             0x9

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX2GCR5_RESERVED_15                             0x0

    * Byte Lane internal VREF Select for Rank 1
    *  PSU_DDR_PHY_DX2GCR5_DXREFISELR1                             0x55

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX2GCR5_RESERVED_7                              0x0

    * Byte Lane internal VREF Select for Rank 0
    *  PSU_DDR_PHY_DX2GCR5_DXREFISELR0                             0x55

    * DATX8 n General Configuration Register 5
    * (OFFSET, MASK, VALUE)      (0XFD080914, 0xFFFFFFFFU ,0x09095555U)
    */
	PSU_Mask_Write(DDR_PHY_DX2GCR5_OFFSET, 0xFFFFFFFFU, 0x09095555U);
/*##################################################################### */

    /*
    * Register : DX2GCR6 @ 0XFD080918

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX2GCR6_RESERVED_31_30                          0x0

    * DRAM DQ VREF Select for Rank3
    *  PSU_DDR_PHY_DX2GCR6_DXDQVREFR3                              0x9

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX2GCR6_RESERVED_23_22                          0x0

    * DRAM DQ VREF Select for Rank2
    *  PSU_DDR_PHY_DX2GCR6_DXDQVREFR2                              0x9

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX2GCR6_RESERVED_15_14                          0x0

    * DRAM DQ VREF Select for Rank1
    *  PSU_DDR_PHY_DX2GCR6_DXDQVREFR1                              0x2b

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX2GCR6_RESERVED_7_6                            0x0

    * DRAM DQ VREF Select for Rank0
    *  PSU_DDR_PHY_DX2GCR6_DXDQVREFR0                              0x2b

    * DATX8 n General Configuration Register 6
    * (OFFSET, MASK, VALUE)      (0XFD080918, 0xFFFFFFFFU ,0x09092B2BU)
    */
	PSU_Mask_Write(DDR_PHY_DX2GCR6_OFFSET, 0xFFFFFFFFU, 0x09092B2BU);
/*##################################################################### */

    /*
    * Register : DX3GCR0 @ 0XFD080A00

    * Calibration Bypass
    *  PSU_DDR_PHY_DX3GCR0_CALBYP                                  0x0

    * Master Delay Line Enable
    *  PSU_DDR_PHY_DX3GCR0_MDLEN                                   0x1

    * Configurable ODT(TE) Phase Shift
    *  PSU_DDR_PHY_DX3GCR0_CODTSHFT                                0x0

    * DQS Duty Cycle Correction
    *  PSU_DDR_PHY_DX3GCR0_DQSDCC                                  0x0

    * Number of Cycles ( in terms of ctl_clk) to generate ctl_dx_get_static_rd
    *  input for the respective bypte lane of the PHY
    *  PSU_DDR_PHY_DX3GCR0_RDDLY                                   0x8

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX3GCR0_RESERVED_19_14                          0x0

    * DQSNSE Power Down Receiver
    *  PSU_DDR_PHY_DX3GCR0_DQSNSEPDR                               0x0

    * DQSSE Power Down Receiver
    *  PSU_DDR_PHY_DX3GCR0_DQSSEPDR                                0x0

    * RTT On Additive Latency
    *  PSU_DDR_PHY_DX3GCR0_RTTOAL                                  0x0

    * RTT Output Hold
    *  PSU_DDR_PHY_DX3GCR0_RTTOH                                   0x3

    * Configurable PDR Phase Shift
    *  PSU_DDR_PHY_DX3GCR0_CPDRSHFT                                0x0

    * DQSR Power Down
    *  PSU_DDR_PHY_DX3GCR0_DQSRPD                                  0x0

    * DQSG Power Down Receiver
    *  PSU_DDR_PHY_DX3GCR0_DQSGPDR                                 0x0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX3GCR0_RESERVED_4                              0x0

    * DQSG On-Die Termination
    *  PSU_DDR_PHY_DX3GCR0_DQSGODT                                 0x0

    * DQSG Output Enable
    *  PSU_DDR_PHY_DX3GCR0_DQSGOE                                  0x1

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX3GCR0_RESERVED_1_0                            0x0

    * DATX8 n General Configuration Register 0
    * (OFFSET, MASK, VALUE)      (0XFD080A00, 0xFFFFFFFFU ,0x40800604U)
    */
	PSU_Mask_Write(DDR_PHY_DX3GCR0_OFFSET, 0xFFFFFFFFU, 0x40800604U);
/*##################################################################### */

    /*
    * Register : DX3GCR1 @ 0XFD080A04

    * Enables the PDR mode for DQ[7:0]
    *  PSU_DDR_PHY_DX3GCR1_DXPDRMODE                               0x0

    * Reserved. Returns zeroes on reads.
    *  PSU_DDR_PHY_DX3GCR1_RESERVED_15                             0x0

    * Select the delayed or non-delayed read data strobe #
    *  PSU_DDR_PHY_DX3GCR1_QSNSEL                                  0x1

    * Select the delayed or non-delayed read data strobe
    *  PSU_DDR_PHY_DX3GCR1_QSSEL                                   0x1

    * Enables Read Data Strobe in a byte lane
    *  PSU_DDR_PHY_DX3GCR1_OEEN                                    0x1

    * Enables PDR in a byte lane
    *  PSU_DDR_PHY_DX3GCR1_PDREN                                   0x1

    * Enables ODT/TE in a byte lane
    *  PSU_DDR_PHY_DX3GCR1_TEEN                                    0x1

    * Enables Write Data strobe in a byte lane
    *  PSU_DDR_PHY_DX3GCR1_DSEN                                    0x1

    * Enables DM pin in a byte lane
    *  PSU_DDR_PHY_DX3GCR1_DMEN                                    0x1

    * Enables DQ corresponding to each bit in a byte
    *  PSU_DDR_PHY_DX3GCR1_DQEN                                    0xff

    * DATX8 n General Configuration Register 1
    * (OFFSET, MASK, VALUE)      (0XFD080A04, 0xFFFFFFFFU ,0x00007FFFU)
    */
	PSU_Mask_Write(DDR_PHY_DX3GCR1_OFFSET, 0xFFFFFFFFU, 0x00007FFFU);
/*##################################################################### */

    /*
    * Register : DX3GCR4 @ 0XFD080A10

    * Byte lane VREF IOM (Used only by D4MU IOs)
    *  PSU_DDR_PHY_DX3GCR4_RESERVED_31_29                          0x0

    * Byte Lane VREF Pad Enable
    *  PSU_DDR_PHY_DX3GCR4_DXREFPEN                                0x0

    * Byte Lane Internal VREF Enable
    *  PSU_DDR_PHY_DX3GCR4_DXREFEEN                                0x3

    * Byte Lane Single-End VREF Enable
    *  PSU_DDR_PHY_DX3GCR4_DXREFSEN                                0x1

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX3GCR4_RESERVED_24                             0x0

    * External VREF generator REFSEL range select
    *  PSU_DDR_PHY_DX3GCR4_DXREFESELRANGE                          0x0

    * Byte Lane External VREF Select
    *  PSU_DDR_PHY_DX3GCR4_DXREFESEL                               0x0

    * Single ended VREF generator REFSEL range select
    *  PSU_DDR_PHY_DX3GCR4_DXREFSSELRANGE                          0x1

    * Byte Lane Single-End VREF Select
    *  PSU_DDR_PHY_DX3GCR4_DXREFSSEL                               0x30

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX3GCR4_RESERVED_7_6                            0x0

    * VREF Enable control for DQ IO (Single Ended) buffers of a byte lane.
    *  PSU_DDR_PHY_DX3GCR4_DXREFIEN                                0xf

    * VRMON control for DQ IO (Single Ended) buffers of a byte lane.
    *  PSU_DDR_PHY_DX3GCR4_DXREFIMON                               0x0

    * DATX8 n General Configuration Register 4
    * (OFFSET, MASK, VALUE)      (0XFD080A10, 0xFFFFFFFFU ,0x0E00B03CU)
    */
	PSU_Mask_Write(DDR_PHY_DX3GCR4_OFFSET, 0xFFFFFFFFU, 0x0E00B03CU);
/*##################################################################### */

    /*
    * Register : DX3GCR5 @ 0XFD080A14

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX3GCR5_RESERVED_31                             0x0

    * Byte Lane internal VREF Select for Rank 3
    *  PSU_DDR_PHY_DX3GCR5_DXREFISELR3                             0x9

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX3GCR5_RESERVED_23                             0x0

    * Byte Lane internal VREF Select for Rank 2
    *  PSU_DDR_PHY_DX3GCR5_DXREFISELR2                             0x9

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX3GCR5_RESERVED_15                             0x0

    * Byte Lane internal VREF Select for Rank 1
    *  PSU_DDR_PHY_DX3GCR5_DXREFISELR1                             0x55

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX3GCR5_RESERVED_7                              0x0

    * Byte Lane internal VREF Select for Rank 0
    *  PSU_DDR_PHY_DX3GCR5_DXREFISELR0                             0x55

    * DATX8 n General Configuration Register 5
    * (OFFSET, MASK, VALUE)      (0XFD080A14, 0xFFFFFFFFU ,0x09095555U)
    */
	PSU_Mask_Write(DDR_PHY_DX3GCR5_OFFSET, 0xFFFFFFFFU, 0x09095555U);
/*##################################################################### */

    /*
    * Register : DX3GCR6 @ 0XFD080A18

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX3GCR6_RESERVED_31_30                          0x0

    * DRAM DQ VREF Select for Rank3
    *  PSU_DDR_PHY_DX3GCR6_DXDQVREFR3                              0x9

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX3GCR6_RESERVED_23_22                          0x0

    * DRAM DQ VREF Select for Rank2
    *  PSU_DDR_PHY_DX3GCR6_DXDQVREFR2                              0x9

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX3GCR6_RESERVED_15_14                          0x0

    * DRAM DQ VREF Select for Rank1
    *  PSU_DDR_PHY_DX3GCR6_DXDQVREFR1                              0x2b

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX3GCR6_RESERVED_7_6                            0x0

    * DRAM DQ VREF Select for Rank0
    *  PSU_DDR_PHY_DX3GCR6_DXDQVREFR0                              0x2b

    * DATX8 n General Configuration Register 6
    * (OFFSET, MASK, VALUE)      (0XFD080A18, 0xFFFFFFFFU ,0x09092B2BU)
    */
	PSU_Mask_Write(DDR_PHY_DX3GCR6_OFFSET, 0xFFFFFFFFU, 0x09092B2BU);
/*##################################################################### */

    /*
    * Register : DX4GCR0 @ 0XFD080B00

    * Calibration Bypass
    *  PSU_DDR_PHY_DX4GCR0_CALBYP                                  0x0

    * Master Delay Line Enable
    *  PSU_DDR_PHY_DX4GCR0_MDLEN                                   0x1

    * Configurable ODT(TE) Phase Shift
    *  PSU_DDR_PHY_DX4GCR0_CODTSHFT                                0x0

    * DQS Duty Cycle Correction
    *  PSU_DDR_PHY_DX4GCR0_DQSDCC                                  0x0

    * Number of Cycles ( in terms of ctl_clk) to generate ctl_dx_get_static_rd
    *  input for the respective bypte lane of the PHY
    *  PSU_DDR_PHY_DX4GCR0_RDDLY                                   0x8

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX4GCR0_RESERVED_19_14                          0x0

    * DQSNSE Power Down Receiver
    *  PSU_DDR_PHY_DX4GCR0_DQSNSEPDR                               0x0

    * DQSSE Power Down Receiver
    *  PSU_DDR_PHY_DX4GCR0_DQSSEPDR                                0x0

    * RTT On Additive Latency
    *  PSU_DDR_PHY_DX4GCR0_RTTOAL                                  0x0

    * RTT Output Hold
    *  PSU_DDR_PHY_DX4GCR0_RTTOH                                   0x3

    * Configurable PDR Phase Shift
    *  PSU_DDR_PHY_DX4GCR0_CPDRSHFT                                0x0

    * DQSR Power Down
    *  PSU_DDR_PHY_DX4GCR0_DQSRPD                                  0x0

    * DQSG Power Down Receiver
    *  PSU_DDR_PHY_DX4GCR0_DQSGPDR                                 0x0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX4GCR0_RESERVED_4                              0x0

    * DQSG On-Die Termination
    *  PSU_DDR_PHY_DX4GCR0_DQSGODT                                 0x0

    * DQSG Output Enable
    *  PSU_DDR_PHY_DX4GCR0_DQSGOE                                  0x1

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX4GCR0_RESERVED_1_0                            0x0

    * DATX8 n General Configuration Register 0
    * (OFFSET, MASK, VALUE)      (0XFD080B00, 0xFFFFFFFFU ,0x40800604U)
    */
	PSU_Mask_Write(DDR_PHY_DX4GCR0_OFFSET, 0xFFFFFFFFU, 0x40800604U);
/*##################################################################### */

    /*
    * Register : DX4GCR1 @ 0XFD080B04

    * Enables the PDR mode for DQ[7:0]
    *  PSU_DDR_PHY_DX4GCR1_DXPDRMODE                               0x0

    * Reserved. Returns zeroes on reads.
    *  PSU_DDR_PHY_DX4GCR1_RESERVED_15                             0x0

    * Select the delayed or non-delayed read data strobe #
    *  PSU_DDR_PHY_DX4GCR1_QSNSEL                                  0x1

    * Select the delayed or non-delayed read data strobe
    *  PSU_DDR_PHY_DX4GCR1_QSSEL                                   0x1

    * Enables Read Data Strobe in a byte lane
    *  PSU_DDR_PHY_DX4GCR1_OEEN                                    0x1

    * Enables PDR in a byte lane
    *  PSU_DDR_PHY_DX4GCR1_PDREN                                   0x1

    * Enables ODT/TE in a byte lane
    *  PSU_DDR_PHY_DX4GCR1_TEEN                                    0x1

    * Enables Write Data strobe in a byte lane
    *  PSU_DDR_PHY_DX4GCR1_DSEN                                    0x1

    * Enables DM pin in a byte lane
    *  PSU_DDR_PHY_DX4GCR1_DMEN                                    0x1

    * Enables DQ corresponding to each bit in a byte
    *  PSU_DDR_PHY_DX4GCR1_DQEN                                    0xff

    * DATX8 n General Configuration Register 1
    * (OFFSET, MASK, VALUE)      (0XFD080B04, 0xFFFFFFFFU ,0x00007FFFU)
    */
	PSU_Mask_Write(DDR_PHY_DX4GCR1_OFFSET, 0xFFFFFFFFU, 0x00007FFFU);
/*##################################################################### */

    /*
    * Register : DX4GCR4 @ 0XFD080B10

    * Byte lane VREF IOM (Used only by D4MU IOs)
    *  PSU_DDR_PHY_DX4GCR4_RESERVED_31_29                          0x0

    * Byte Lane VREF Pad Enable
    *  PSU_DDR_PHY_DX4GCR4_DXREFPEN                                0x0

    * Byte Lane Internal VREF Enable
    *  PSU_DDR_PHY_DX4GCR4_DXREFEEN                                0x3

    * Byte Lane Single-End VREF Enable
    *  PSU_DDR_PHY_DX4GCR4_DXREFSEN                                0x1

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX4GCR4_RESERVED_24                             0x0

    * External VREF generator REFSEL range select
    *  PSU_DDR_PHY_DX4GCR4_DXREFESELRANGE                          0x0

    * Byte Lane External VREF Select
    *  PSU_DDR_PHY_DX4GCR4_DXREFESEL                               0x0

    * Single ended VREF generator REFSEL range select
    *  PSU_DDR_PHY_DX4GCR4_DXREFSSELRANGE                          0x1

    * Byte Lane Single-End VREF Select
    *  PSU_DDR_PHY_DX4GCR4_DXREFSSEL                               0x30

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX4GCR4_RESERVED_7_6                            0x0

    * VREF Enable control for DQ IO (Single Ended) buffers of a byte lane.
    *  PSU_DDR_PHY_DX4GCR4_DXREFIEN                                0xf

    * VRMON control for DQ IO (Single Ended) buffers of a byte lane.
    *  PSU_DDR_PHY_DX4GCR4_DXREFIMON                               0x0

    * DATX8 n General Configuration Register 4
    * (OFFSET, MASK, VALUE)      (0XFD080B10, 0xFFFFFFFFU ,0x0E00B03CU)
    */
	PSU_Mask_Write(DDR_PHY_DX4GCR4_OFFSET, 0xFFFFFFFFU, 0x0E00B03CU);
/*##################################################################### */

    /*
    * Register : DX4GCR5 @ 0XFD080B14

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX4GCR5_RESERVED_31                             0x0

    * Byte Lane internal VREF Select for Rank 3
    *  PSU_DDR_PHY_DX4GCR5_DXREFISELR3                             0x9

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX4GCR5_RESERVED_23                             0x0

    * Byte Lane internal VREF Select for Rank 2
    *  PSU_DDR_PHY_DX4GCR5_DXREFISELR2                             0x9

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX4GCR5_RESERVED_15                             0x0

    * Byte Lane internal VREF Select for Rank 1
    *  PSU_DDR_PHY_DX4GCR5_DXREFISELR1                             0x55

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX4GCR5_RESERVED_7                              0x0

    * Byte Lane internal VREF Select for Rank 0
    *  PSU_DDR_PHY_DX4GCR5_DXREFISELR0                             0x55

    * DATX8 n General Configuration Register 5
    * (OFFSET, MASK, VALUE)      (0XFD080B14, 0xFFFFFFFFU ,0x09095555U)
    */
	PSU_Mask_Write(DDR_PHY_DX4GCR5_OFFSET, 0xFFFFFFFFU, 0x09095555U);
/*##################################################################### */

    /*
    * Register : DX4GCR6 @ 0XFD080B18

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX4GCR6_RESERVED_31_30                          0x0

    * DRAM DQ VREF Select for Rank3
    *  PSU_DDR_PHY_DX4GCR6_DXDQVREFR3                              0x9

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX4GCR6_RESERVED_23_22                          0x0

    * DRAM DQ VREF Select for Rank2
    *  PSU_DDR_PHY_DX4GCR6_DXDQVREFR2                              0x9

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX4GCR6_RESERVED_15_14                          0x0

    * DRAM DQ VREF Select for Rank1
    *  PSU_DDR_PHY_DX4GCR6_DXDQVREFR1                              0x2b

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX4GCR6_RESERVED_7_6                            0x0

    * DRAM DQ VREF Select for Rank0
    *  PSU_DDR_PHY_DX4GCR6_DXDQVREFR0                              0x2b

    * DATX8 n General Configuration Register 6
    * (OFFSET, MASK, VALUE)      (0XFD080B18, 0xFFFFFFFFU ,0x09092B2BU)
    */
	PSU_Mask_Write(DDR_PHY_DX4GCR6_OFFSET, 0xFFFFFFFFU, 0x09092B2BU);
/*##################################################################### */

    /*
    * Register : DX5GCR0 @ 0XFD080C00

    * Calibration Bypass
    *  PSU_DDR_PHY_DX5GCR0_CALBYP                                  0x0

    * Master Delay Line Enable
    *  PSU_DDR_PHY_DX5GCR0_MDLEN                                   0x1

    * Configurable ODT(TE) Phase Shift
    *  PSU_DDR_PHY_DX5GCR0_CODTSHFT                                0x0

    * DQS Duty Cycle Correction
    *  PSU_DDR_PHY_DX5GCR0_DQSDCC                                  0x0

    * Number of Cycles ( in terms of ctl_clk) to generate ctl_dx_get_static_rd
    *  input for the respective bypte lane of the PHY
    *  PSU_DDR_PHY_DX5GCR0_RDDLY                                   0x8

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX5GCR0_RESERVED_19_14                          0x0

    * DQSNSE Power Down Receiver
    *  PSU_DDR_PHY_DX5GCR0_DQSNSEPDR                               0x0

    * DQSSE Power Down Receiver
    *  PSU_DDR_PHY_DX5GCR0_DQSSEPDR                                0x0

    * RTT On Additive Latency
    *  PSU_DDR_PHY_DX5GCR0_RTTOAL                                  0x0

    * RTT Output Hold
    *  PSU_DDR_PHY_DX5GCR0_RTTOH                                   0x3

    * Configurable PDR Phase Shift
    *  PSU_DDR_PHY_DX5GCR0_CPDRSHFT                                0x0

    * DQSR Power Down
    *  PSU_DDR_PHY_DX5GCR0_DQSRPD                                  0x0

    * DQSG Power Down Receiver
    *  PSU_DDR_PHY_DX5GCR0_DQSGPDR                                 0x0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX5GCR0_RESERVED_4                              0x0

    * DQSG On-Die Termination
    *  PSU_DDR_PHY_DX5GCR0_DQSGODT                                 0x0

    * DQSG Output Enable
    *  PSU_DDR_PHY_DX5GCR0_DQSGOE                                  0x1

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX5GCR0_RESERVED_1_0                            0x0

    * DATX8 n General Configuration Register 0
    * (OFFSET, MASK, VALUE)      (0XFD080C00, 0xFFFFFFFFU ,0x40800604U)
    */
	PSU_Mask_Write(DDR_PHY_DX5GCR0_OFFSET, 0xFFFFFFFFU, 0x40800604U);
/*##################################################################### */

    /*
    * Register : DX5GCR1 @ 0XFD080C04

    * Enables the PDR mode for DQ[7:0]
    *  PSU_DDR_PHY_DX5GCR1_DXPDRMODE                               0x0

    * Reserved. Returns zeroes on reads.
    *  PSU_DDR_PHY_DX5GCR1_RESERVED_15                             0x0

    * Select the delayed or non-delayed read data strobe #
    *  PSU_DDR_PHY_DX5GCR1_QSNSEL                                  0x1

    * Select the delayed or non-delayed read data strobe
    *  PSU_DDR_PHY_DX5GCR1_QSSEL                                   0x1

    * Enables Read Data Strobe in a byte lane
    *  PSU_DDR_PHY_DX5GCR1_OEEN                                    0x1

    * Enables PDR in a byte lane
    *  PSU_DDR_PHY_DX5GCR1_PDREN                                   0x1

    * Enables ODT/TE in a byte lane
    *  PSU_DDR_PHY_DX5GCR1_TEEN                                    0x1

    * Enables Write Data strobe in a byte lane
    *  PSU_DDR_PHY_DX5GCR1_DSEN                                    0x1

    * Enables DM pin in a byte lane
    *  PSU_DDR_PHY_DX5GCR1_DMEN                                    0x1

    * Enables DQ corresponding to each bit in a byte
    *  PSU_DDR_PHY_DX5GCR1_DQEN                                    0xff

    * DATX8 n General Configuration Register 1
    * (OFFSET, MASK, VALUE)      (0XFD080C04, 0xFFFFFFFFU ,0x00007FFFU)
    */
	PSU_Mask_Write(DDR_PHY_DX5GCR1_OFFSET, 0xFFFFFFFFU, 0x00007FFFU);
/*##################################################################### */

    /*
    * Register : DX5GCR4 @ 0XFD080C10

    * Byte lane VREF IOM (Used only by D4MU IOs)
    *  PSU_DDR_PHY_DX5GCR4_RESERVED_31_29                          0x0

    * Byte Lane VREF Pad Enable
    *  PSU_DDR_PHY_DX5GCR4_DXREFPEN                                0x0

    * Byte Lane Internal VREF Enable
    *  PSU_DDR_PHY_DX5GCR4_DXREFEEN                                0x3

    * Byte Lane Single-End VREF Enable
    *  PSU_DDR_PHY_DX5GCR4_DXREFSEN                                0x1

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX5GCR4_RESERVED_24                             0x0

    * External VREF generator REFSEL range select
    *  PSU_DDR_PHY_DX5GCR4_DXREFESELRANGE                          0x0

    * Byte Lane External VREF Select
    *  PSU_DDR_PHY_DX5GCR4_DXREFESEL                               0x0

    * Single ended VREF generator REFSEL range select
    *  PSU_DDR_PHY_DX5GCR4_DXREFSSELRANGE                          0x1

    * Byte Lane Single-End VREF Select
    *  PSU_DDR_PHY_DX5GCR4_DXREFSSEL                               0x30

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX5GCR4_RESERVED_7_6                            0x0

    * VREF Enable control for DQ IO (Single Ended) buffers of a byte lane.
    *  PSU_DDR_PHY_DX5GCR4_DXREFIEN                                0xf

    * VRMON control for DQ IO (Single Ended) buffers of a byte lane.
    *  PSU_DDR_PHY_DX5GCR4_DXREFIMON                               0x0

    * DATX8 n General Configuration Register 4
    * (OFFSET, MASK, VALUE)      (0XFD080C10, 0xFFFFFFFFU ,0x0E00B03CU)
    */
	PSU_Mask_Write(DDR_PHY_DX5GCR4_OFFSET, 0xFFFFFFFFU, 0x0E00B03CU);
/*##################################################################### */

    /*
    * Register : DX5GCR5 @ 0XFD080C14

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX5GCR5_RESERVED_31                             0x0

    * Byte Lane internal VREF Select for Rank 3
    *  PSU_DDR_PHY_DX5GCR5_DXREFISELR3                             0x9

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX5GCR5_RESERVED_23                             0x0

    * Byte Lane internal VREF Select for Rank 2
    *  PSU_DDR_PHY_DX5GCR5_DXREFISELR2                             0x9

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX5GCR5_RESERVED_15                             0x0

    * Byte Lane internal VREF Select for Rank 1
    *  PSU_DDR_PHY_DX5GCR5_DXREFISELR1                             0x55

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX5GCR5_RESERVED_7                              0x0

    * Byte Lane internal VREF Select for Rank 0
    *  PSU_DDR_PHY_DX5GCR5_DXREFISELR0                             0x55

    * DATX8 n General Configuration Register 5
    * (OFFSET, MASK, VALUE)      (0XFD080C14, 0xFFFFFFFFU ,0x09095555U)
    */
	PSU_Mask_Write(DDR_PHY_DX5GCR5_OFFSET, 0xFFFFFFFFU, 0x09095555U);
/*##################################################################### */

    /*
    * Register : DX5GCR6 @ 0XFD080C18

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX5GCR6_RESERVED_31_30                          0x0

    * DRAM DQ VREF Select for Rank3
    *  PSU_DDR_PHY_DX5GCR6_DXDQVREFR3                              0x9

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX5GCR6_RESERVED_23_22                          0x0

    * DRAM DQ VREF Select for Rank2
    *  PSU_DDR_PHY_DX5GCR6_DXDQVREFR2                              0x9

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX5GCR6_RESERVED_15_14                          0x0

    * DRAM DQ VREF Select for Rank1
    *  PSU_DDR_PHY_DX5GCR6_DXDQVREFR1                              0x2b

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX5GCR6_RESERVED_7_6                            0x0

    * DRAM DQ VREF Select for Rank0
    *  PSU_DDR_PHY_DX5GCR6_DXDQVREFR0                              0x2b

    * DATX8 n General Configuration Register 6
    * (OFFSET, MASK, VALUE)      (0XFD080C18, 0xFFFFFFFFU ,0x09092B2BU)
    */
	PSU_Mask_Write(DDR_PHY_DX5GCR6_OFFSET, 0xFFFFFFFFU, 0x09092B2BU);
/*##################################################################### */

    /*
    * Register : DX6GCR0 @ 0XFD080D00

    * Calibration Bypass
    *  PSU_DDR_PHY_DX6GCR0_CALBYP                                  0x0

    * Master Delay Line Enable
    *  PSU_DDR_PHY_DX6GCR0_MDLEN                                   0x1

    * Configurable ODT(TE) Phase Shift
    *  PSU_DDR_PHY_DX6GCR0_CODTSHFT                                0x0

    * DQS Duty Cycle Correction
    *  PSU_DDR_PHY_DX6GCR0_DQSDCC                                  0x0

    * Number of Cycles ( in terms of ctl_clk) to generate ctl_dx_get_static_rd
    *  input for the respective bypte lane of the PHY
    *  PSU_DDR_PHY_DX6GCR0_RDDLY                                   0x8

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX6GCR0_RESERVED_19_14                          0x0

    * DQSNSE Power Down Receiver
    *  PSU_DDR_PHY_DX6GCR0_DQSNSEPDR                               0x0

    * DQSSE Power Down Receiver
    *  PSU_DDR_PHY_DX6GCR0_DQSSEPDR                                0x0

    * RTT On Additive Latency
    *  PSU_DDR_PHY_DX6GCR0_RTTOAL                                  0x0

    * RTT Output Hold
    *  PSU_DDR_PHY_DX6GCR0_RTTOH                                   0x3

    * Configurable PDR Phase Shift
    *  PSU_DDR_PHY_DX6GCR0_CPDRSHFT                                0x0

    * DQSR Power Down
    *  PSU_DDR_PHY_DX6GCR0_DQSRPD                                  0x0

    * DQSG Power Down Receiver
    *  PSU_DDR_PHY_DX6GCR0_DQSGPDR                                 0x0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX6GCR0_RESERVED_4                              0x0

    * DQSG On-Die Termination
    *  PSU_DDR_PHY_DX6GCR0_DQSGODT                                 0x0

    * DQSG Output Enable
    *  PSU_DDR_PHY_DX6GCR0_DQSGOE                                  0x1

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX6GCR0_RESERVED_1_0                            0x0

    * DATX8 n General Configuration Register 0
    * (OFFSET, MASK, VALUE)      (0XFD080D00, 0xFFFFFFFFU ,0x40800604U)
    */
	PSU_Mask_Write(DDR_PHY_DX6GCR0_OFFSET, 0xFFFFFFFFU, 0x40800604U);
/*##################################################################### */

    /*
    * Register : DX6GCR1 @ 0XFD080D04

    * Enables the PDR mode for DQ[7:0]
    *  PSU_DDR_PHY_DX6GCR1_DXPDRMODE                               0x0

    * Reserved. Returns zeroes on reads.
    *  PSU_DDR_PHY_DX6GCR1_RESERVED_15                             0x0

    * Select the delayed or non-delayed read data strobe #
    *  PSU_DDR_PHY_DX6GCR1_QSNSEL                                  0x1

    * Select the delayed or non-delayed read data strobe
    *  PSU_DDR_PHY_DX6GCR1_QSSEL                                   0x1

    * Enables Read Data Strobe in a byte lane
    *  PSU_DDR_PHY_DX6GCR1_OEEN                                    0x1

    * Enables PDR in a byte lane
    *  PSU_DDR_PHY_DX6GCR1_PDREN                                   0x1

    * Enables ODT/TE in a byte lane
    *  PSU_DDR_PHY_DX6GCR1_TEEN                                    0x1

    * Enables Write Data strobe in a byte lane
    *  PSU_DDR_PHY_DX6GCR1_DSEN                                    0x1

    * Enables DM pin in a byte lane
    *  PSU_DDR_PHY_DX6GCR1_DMEN                                    0x1

    * Enables DQ corresponding to each bit in a byte
    *  PSU_DDR_PHY_DX6GCR1_DQEN                                    0xff

    * DATX8 n General Configuration Register 1
    * (OFFSET, MASK, VALUE)      (0XFD080D04, 0xFFFFFFFFU ,0x00007FFFU)
    */
	PSU_Mask_Write(DDR_PHY_DX6GCR1_OFFSET, 0xFFFFFFFFU, 0x00007FFFU);
/*##################################################################### */

    /*
    * Register : DX6GCR4 @ 0XFD080D10

    * Byte lane VREF IOM (Used only by D4MU IOs)
    *  PSU_DDR_PHY_DX6GCR4_RESERVED_31_29                          0x0

    * Byte Lane VREF Pad Enable
    *  PSU_DDR_PHY_DX6GCR4_DXREFPEN                                0x0

    * Byte Lane Internal VREF Enable
    *  PSU_DDR_PHY_DX6GCR4_DXREFEEN                                0x3

    * Byte Lane Single-End VREF Enable
    *  PSU_DDR_PHY_DX6GCR4_DXREFSEN                                0x1

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX6GCR4_RESERVED_24                             0x0

    * External VREF generator REFSEL range select
    *  PSU_DDR_PHY_DX6GCR4_DXREFESELRANGE                          0x0

    * Byte Lane External VREF Select
    *  PSU_DDR_PHY_DX6GCR4_DXREFESEL                               0x0

    * Single ended VREF generator REFSEL range select
    *  PSU_DDR_PHY_DX6GCR4_DXREFSSELRANGE                          0x1

    * Byte Lane Single-End VREF Select
    *  PSU_DDR_PHY_DX6GCR4_DXREFSSEL                               0x30

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX6GCR4_RESERVED_7_6                            0x0

    * VREF Enable control for DQ IO (Single Ended) buffers of a byte lane.
    *  PSU_DDR_PHY_DX6GCR4_DXREFIEN                                0xf

    * VRMON control for DQ IO (Single Ended) buffers of a byte lane.
    *  PSU_DDR_PHY_DX6GCR4_DXREFIMON                               0x0

    * DATX8 n General Configuration Register 4
    * (OFFSET, MASK, VALUE)      (0XFD080D10, 0xFFFFFFFFU ,0x0E00B03CU)
    */
	PSU_Mask_Write(DDR_PHY_DX6GCR4_OFFSET, 0xFFFFFFFFU, 0x0E00B03CU);
/*##################################################################### */

    /*
    * Register : DX6GCR5 @ 0XFD080D14

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX6GCR5_RESERVED_31                             0x0

    * Byte Lane internal VREF Select for Rank 3
    *  PSU_DDR_PHY_DX6GCR5_DXREFISELR3                             0x9

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX6GCR5_RESERVED_23                             0x0

    * Byte Lane internal VREF Select for Rank 2
    *  PSU_DDR_PHY_DX6GCR5_DXREFISELR2                             0x9

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX6GCR5_RESERVED_15                             0x0

    * Byte Lane internal VREF Select for Rank 1
    *  PSU_DDR_PHY_DX6GCR5_DXREFISELR1                             0x55

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX6GCR5_RESERVED_7                              0x0

    * Byte Lane internal VREF Select for Rank 0
    *  PSU_DDR_PHY_DX6GCR5_DXREFISELR0                             0x55

    * DATX8 n General Configuration Register 5
    * (OFFSET, MASK, VALUE)      (0XFD080D14, 0xFFFFFFFFU ,0x09095555U)
    */
	PSU_Mask_Write(DDR_PHY_DX6GCR5_OFFSET, 0xFFFFFFFFU, 0x09095555U);
/*##################################################################### */

    /*
    * Register : DX6GCR6 @ 0XFD080D18

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX6GCR6_RESERVED_31_30                          0x0

    * DRAM DQ VREF Select for Rank3
    *  PSU_DDR_PHY_DX6GCR6_DXDQVREFR3                              0x9

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX6GCR6_RESERVED_23_22                          0x0

    * DRAM DQ VREF Select for Rank2
    *  PSU_DDR_PHY_DX6GCR6_DXDQVREFR2                              0x9

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX6GCR6_RESERVED_15_14                          0x0

    * DRAM DQ VREF Select for Rank1
    *  PSU_DDR_PHY_DX6GCR6_DXDQVREFR1                              0x2b

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX6GCR6_RESERVED_7_6                            0x0

    * DRAM DQ VREF Select for Rank0
    *  PSU_DDR_PHY_DX6GCR6_DXDQVREFR0                              0x2b

    * DATX8 n General Configuration Register 6
    * (OFFSET, MASK, VALUE)      (0XFD080D18, 0xFFFFFFFFU ,0x09092B2BU)
    */
	PSU_Mask_Write(DDR_PHY_DX6GCR6_OFFSET, 0xFFFFFFFFU, 0x09092B2BU);
/*##################################################################### */

    /*
    * Register : DX7GCR0 @ 0XFD080E00

    * Calibration Bypass
    *  PSU_DDR_PHY_DX7GCR0_CALBYP                                  0x0

    * Master Delay Line Enable
    *  PSU_DDR_PHY_DX7GCR0_MDLEN                                   0x1

    * Configurable ODT(TE) Phase Shift
    *  PSU_DDR_PHY_DX7GCR0_CODTSHFT                                0x0

    * DQS Duty Cycle Correction
    *  PSU_DDR_PHY_DX7GCR0_DQSDCC                                  0x0

    * Number of Cycles ( in terms of ctl_clk) to generate ctl_dx_get_static_rd
    *  input for the respective bypte lane of the PHY
    *  PSU_DDR_PHY_DX7GCR0_RDDLY                                   0x8

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX7GCR0_RESERVED_19_14                          0x0

    * DQSNSE Power Down Receiver
    *  PSU_DDR_PHY_DX7GCR0_DQSNSEPDR                               0x0

    * DQSSE Power Down Receiver
    *  PSU_DDR_PHY_DX7GCR0_DQSSEPDR                                0x0

    * RTT On Additive Latency
    *  PSU_DDR_PHY_DX7GCR0_RTTOAL                                  0x0

    * RTT Output Hold
    *  PSU_DDR_PHY_DX7GCR0_RTTOH                                   0x3

    * Configurable PDR Phase Shift
    *  PSU_DDR_PHY_DX7GCR0_CPDRSHFT                                0x0

    * DQSR Power Down
    *  PSU_DDR_PHY_DX7GCR0_DQSRPD                                  0x0

    * DQSG Power Down Receiver
    *  PSU_DDR_PHY_DX7GCR0_DQSGPDR                                 0x0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX7GCR0_RESERVED_4                              0x0

    * DQSG On-Die Termination
    *  PSU_DDR_PHY_DX7GCR0_DQSGODT                                 0x0

    * DQSG Output Enable
    *  PSU_DDR_PHY_DX7GCR0_DQSGOE                                  0x1

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX7GCR0_RESERVED_1_0                            0x0

    * DATX8 n General Configuration Register 0
    * (OFFSET, MASK, VALUE)      (0XFD080E00, 0xFFFFFFFFU ,0x40800604U)
    */
	PSU_Mask_Write(DDR_PHY_DX7GCR0_OFFSET, 0xFFFFFFFFU, 0x40800604U);
/*##################################################################### */

    /*
    * Register : DX7GCR1 @ 0XFD080E04

    * Enables the PDR mode for DQ[7:0]
    *  PSU_DDR_PHY_DX7GCR1_DXPDRMODE                               0x0

    * Reserved. Returns zeroes on reads.
    *  PSU_DDR_PHY_DX7GCR1_RESERVED_15                             0x0

    * Select the delayed or non-delayed read data strobe #
    *  PSU_DDR_PHY_DX7GCR1_QSNSEL                                  0x1

    * Select the delayed or non-delayed read data strobe
    *  PSU_DDR_PHY_DX7GCR1_QSSEL                                   0x1

    * Enables Read Data Strobe in a byte lane
    *  PSU_DDR_PHY_DX7GCR1_OEEN                                    0x1

    * Enables PDR in a byte lane
    *  PSU_DDR_PHY_DX7GCR1_PDREN                                   0x1

    * Enables ODT/TE in a byte lane
    *  PSU_DDR_PHY_DX7GCR1_TEEN                                    0x1

    * Enables Write Data strobe in a byte lane
    *  PSU_DDR_PHY_DX7GCR1_DSEN                                    0x1

    * Enables DM pin in a byte lane
    *  PSU_DDR_PHY_DX7GCR1_DMEN                                    0x1

    * Enables DQ corresponding to each bit in a byte
    *  PSU_DDR_PHY_DX7GCR1_DQEN                                    0xff

    * DATX8 n General Configuration Register 1
    * (OFFSET, MASK, VALUE)      (0XFD080E04, 0xFFFFFFFFU ,0x00007FFFU)
    */
	PSU_Mask_Write(DDR_PHY_DX7GCR1_OFFSET, 0xFFFFFFFFU, 0x00007FFFU);
/*##################################################################### */

    /*
    * Register : DX7GCR4 @ 0XFD080E10

    * Byte lane VREF IOM (Used only by D4MU IOs)
    *  PSU_DDR_PHY_DX7GCR4_RESERVED_31_29                          0x0

    * Byte Lane VREF Pad Enable
    *  PSU_DDR_PHY_DX7GCR4_DXREFPEN                                0x0

    * Byte Lane Internal VREF Enable
    *  PSU_DDR_PHY_DX7GCR4_DXREFEEN                                0x3

    * Byte Lane Single-End VREF Enable
    *  PSU_DDR_PHY_DX7GCR4_DXREFSEN                                0x1

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX7GCR4_RESERVED_24                             0x0

    * External VREF generator REFSEL range select
    *  PSU_DDR_PHY_DX7GCR4_DXREFESELRANGE                          0x0

    * Byte Lane External VREF Select
    *  PSU_DDR_PHY_DX7GCR4_DXREFESEL                               0x0

    * Single ended VREF generator REFSEL range select
    *  PSU_DDR_PHY_DX7GCR4_DXREFSSELRANGE                          0x1

    * Byte Lane Single-End VREF Select
    *  PSU_DDR_PHY_DX7GCR4_DXREFSSEL                               0x30

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX7GCR4_RESERVED_7_6                            0x0

    * VREF Enable control for DQ IO (Single Ended) buffers of a byte lane.
    *  PSU_DDR_PHY_DX7GCR4_DXREFIEN                                0xf

    * VRMON control for DQ IO (Single Ended) buffers of a byte lane.
    *  PSU_DDR_PHY_DX7GCR4_DXREFIMON                               0x0

    * DATX8 n General Configuration Register 4
    * (OFFSET, MASK, VALUE)      (0XFD080E10, 0xFFFFFFFFU ,0x0E00B03CU)
    */
	PSU_Mask_Write(DDR_PHY_DX7GCR4_OFFSET, 0xFFFFFFFFU, 0x0E00B03CU);
/*##################################################################### */

    /*
    * Register : DX7GCR5 @ 0XFD080E14

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX7GCR5_RESERVED_31                             0x0

    * Byte Lane internal VREF Select for Rank 3
    *  PSU_DDR_PHY_DX7GCR5_DXREFISELR3                             0x9

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX7GCR5_RESERVED_23                             0x0

    * Byte Lane internal VREF Select for Rank 2
    *  PSU_DDR_PHY_DX7GCR5_DXREFISELR2                             0x9

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX7GCR5_RESERVED_15                             0x0

    * Byte Lane internal VREF Select for Rank 1
    *  PSU_DDR_PHY_DX7GCR5_DXREFISELR1                             0x55

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX7GCR5_RESERVED_7                              0x0

    * Byte Lane internal VREF Select for Rank 0
    *  PSU_DDR_PHY_DX7GCR5_DXREFISELR0                             0x55

    * DATX8 n General Configuration Register 5
    * (OFFSET, MASK, VALUE)      (0XFD080E14, 0xFFFFFFFFU ,0x09095555U)
    */
	PSU_Mask_Write(DDR_PHY_DX7GCR5_OFFSET, 0xFFFFFFFFU, 0x09095555U);
/*##################################################################### */

    /*
    * Register : DX7GCR6 @ 0XFD080E18

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX7GCR6_RESERVED_31_30                          0x0

    * DRAM DQ VREF Select for Rank3
    *  PSU_DDR_PHY_DX7GCR6_DXDQVREFR3                              0x9

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX7GCR6_RESERVED_23_22                          0x0

    * DRAM DQ VREF Select for Rank2
    *  PSU_DDR_PHY_DX7GCR6_DXDQVREFR2                              0x9

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX7GCR6_RESERVED_15_14                          0x0

    * DRAM DQ VREF Select for Rank1
    *  PSU_DDR_PHY_DX7GCR6_DXDQVREFR1                              0x2b

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX7GCR6_RESERVED_7_6                            0x0

    * DRAM DQ VREF Select for Rank0
    *  PSU_DDR_PHY_DX7GCR6_DXDQVREFR0                              0x2b

    * DATX8 n General Configuration Register 6
    * (OFFSET, MASK, VALUE)      (0XFD080E18, 0xFFFFFFFFU ,0x09092B2BU)
    */
	PSU_Mask_Write(DDR_PHY_DX7GCR6_OFFSET, 0xFFFFFFFFU, 0x09092B2BU);
/*##################################################################### */

    /*
    * Register : DX8GCR0 @ 0XFD080F00

    * Calibration Bypass
    *  PSU_DDR_PHY_DX8GCR0_CALBYP                                  0x0

    * Master Delay Line Enable
    *  PSU_DDR_PHY_DX8GCR0_MDLEN                                   0x1

    * Configurable ODT(TE) Phase Shift
    *  PSU_DDR_PHY_DX8GCR0_CODTSHFT                                0x0

    * DQS Duty Cycle Correction
    *  PSU_DDR_PHY_DX8GCR0_DQSDCC                                  0x0

    * Number of Cycles ( in terms of ctl_clk) to generate ctl_dx_get_static_rd
    *  input for the respective bypte lane of the PHY
    *  PSU_DDR_PHY_DX8GCR0_RDDLY                                   0x8

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX8GCR0_RESERVED_19_14                          0x0

    * DQSNSE Power Down Receiver
    *  PSU_DDR_PHY_DX8GCR0_DQSNSEPDR                               0x0

    * DQSSE Power Down Receiver
    *  PSU_DDR_PHY_DX8GCR0_DQSSEPDR                                0x0

    * RTT On Additive Latency
    *  PSU_DDR_PHY_DX8GCR0_RTTOAL                                  0x0

    * RTT Output Hold
    *  PSU_DDR_PHY_DX8GCR0_RTTOH                                   0x3

    * Configurable PDR Phase Shift
    *  PSU_DDR_PHY_DX8GCR0_CPDRSHFT                                0x0

    * DQSR Power Down
    *  PSU_DDR_PHY_DX8GCR0_DQSRPD                                  0x0

    * DQSG Power Down Receiver
    *  PSU_DDR_PHY_DX8GCR0_DQSGPDR                                 0x1

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX8GCR0_RESERVED_4                              0x0

    * DQSG On-Die Termination
    *  PSU_DDR_PHY_DX8GCR0_DQSGODT                                 0x0

    * DQSG Output Enable
    *  PSU_DDR_PHY_DX8GCR0_DQSGOE                                  0x1

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX8GCR0_RESERVED_1_0                            0x0

    * DATX8 n General Configuration Register 0
    * (OFFSET, MASK, VALUE)      (0XFD080F00, 0xFFFFFFFFU ,0x40800624U)
    */
	PSU_Mask_Write(DDR_PHY_DX8GCR0_OFFSET, 0xFFFFFFFFU, 0x40800624U);
/*##################################################################### */

    /*
    * Register : DX8GCR1 @ 0XFD080F04

    * Enables the PDR mode for DQ[7:0]
    *  PSU_DDR_PHY_DX8GCR1_DXPDRMODE                               0x0

    * Reserved. Returns zeroes on reads.
    *  PSU_DDR_PHY_DX8GCR1_RESERVED_15                             0x0

    * Select the delayed or non-delayed read data strobe #
    *  PSU_DDR_PHY_DX8GCR1_QSNSEL                                  0x1

    * Select the delayed or non-delayed read data strobe
    *  PSU_DDR_PHY_DX8GCR1_QSSEL                                   0x1

    * Enables Read Data Strobe in a byte lane
    *  PSU_DDR_PHY_DX8GCR1_OEEN                                    0x1

    * Enables PDR in a byte lane
    *  PSU_DDR_PHY_DX8GCR1_PDREN                                   0x1

    * Enables ODT/TE in a byte lane
    *  PSU_DDR_PHY_DX8GCR1_TEEN                                    0x1

    * Enables Write Data strobe in a byte lane
    *  PSU_DDR_PHY_DX8GCR1_DSEN                                    0x1

    * Enables DM pin in a byte lane
    *  PSU_DDR_PHY_DX8GCR1_DMEN                                    0x1

    * Enables DQ corresponding to each bit in a byte
    *  PSU_DDR_PHY_DX8GCR1_DQEN                                    0x0

    * DATX8 n General Configuration Register 1
    * (OFFSET, MASK, VALUE)      (0XFD080F04, 0xFFFFFFFFU ,0x00007F00U)
    */
	PSU_Mask_Write(DDR_PHY_DX8GCR1_OFFSET, 0xFFFFFFFFU, 0x00007F00U);
/*##################################################################### */

    /*
    * Register : DX8GCR4 @ 0XFD080F10

    * Byte lane VREF IOM (Used only by D4MU IOs)
    *  PSU_DDR_PHY_DX8GCR4_RESERVED_31_29                          0x0

    * Byte Lane VREF Pad Enable
    *  PSU_DDR_PHY_DX8GCR4_DXREFPEN                                0x0

    * Byte Lane Internal VREF Enable
    *  PSU_DDR_PHY_DX8GCR4_DXREFEEN                                0x3

    * Byte Lane Single-End VREF Enable
    *  PSU_DDR_PHY_DX8GCR4_DXREFSEN                                0x1

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX8GCR4_RESERVED_24                             0x0

    * External VREF generator REFSEL range select
    *  PSU_DDR_PHY_DX8GCR4_DXREFESELRANGE                          0x0

    * Byte Lane External VREF Select
    *  PSU_DDR_PHY_DX8GCR4_DXREFESEL                               0x0

    * Single ended VREF generator REFSEL range select
    *  PSU_DDR_PHY_DX8GCR4_DXREFSSELRANGE                          0x1

    * Byte Lane Single-End VREF Select
    *  PSU_DDR_PHY_DX8GCR4_DXREFSSEL                               0x30

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX8GCR4_RESERVED_7_6                            0x0

    * VREF Enable control for DQ IO (Single Ended) buffers of a byte lane.
    *  PSU_DDR_PHY_DX8GCR4_DXREFIEN                                0xf

    * VRMON control for DQ IO (Single Ended) buffers of a byte lane.
    *  PSU_DDR_PHY_DX8GCR4_DXREFIMON                               0x0

    * DATX8 n General Configuration Register 4
    * (OFFSET, MASK, VALUE)      (0XFD080F10, 0xFFFFFFFFU ,0x0E00B03CU)
    */
	PSU_Mask_Write(DDR_PHY_DX8GCR4_OFFSET, 0xFFFFFFFFU, 0x0E00B03CU);
/*##################################################################### */

    /*
    * Register : DX8GCR5 @ 0XFD080F14

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX8GCR5_RESERVED_31                             0x0

    * Byte Lane internal VREF Select for Rank 3
    *  PSU_DDR_PHY_DX8GCR5_DXREFISELR3                             0x9

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX8GCR5_RESERVED_23                             0x0

    * Byte Lane internal VREF Select for Rank 2
    *  PSU_DDR_PHY_DX8GCR5_DXREFISELR2                             0x9

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX8GCR5_RESERVED_15                             0x0

    * Byte Lane internal VREF Select for Rank 1
    *  PSU_DDR_PHY_DX8GCR5_DXREFISELR1                             0x55

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX8GCR5_RESERVED_7                              0x0

    * Byte Lane internal VREF Select for Rank 0
    *  PSU_DDR_PHY_DX8GCR5_DXREFISELR0                             0x55

    * DATX8 n General Configuration Register 5
    * (OFFSET, MASK, VALUE)      (0XFD080F14, 0xFFFFFFFFU ,0x09095555U)
    */
	PSU_Mask_Write(DDR_PHY_DX8GCR5_OFFSET, 0xFFFFFFFFU, 0x09095555U);
/*##################################################################### */

    /*
    * Register : DX8GCR6 @ 0XFD080F18

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX8GCR6_RESERVED_31_30                          0x0

    * DRAM DQ VREF Select for Rank3
    *  PSU_DDR_PHY_DX8GCR6_DXDQVREFR3                              0x9

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX8GCR6_RESERVED_23_22                          0x0

    * DRAM DQ VREF Select for Rank2
    *  PSU_DDR_PHY_DX8GCR6_DXDQVREFR2                              0x9

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX8GCR6_RESERVED_15_14                          0x0

    * DRAM DQ VREF Select for Rank1
    *  PSU_DDR_PHY_DX8GCR6_DXDQVREFR1                              0x2b

    * Reserved. Returns zeros on reads.
    *  PSU_DDR_PHY_DX8GCR6_RESERVED_7_6                            0x0

    * DRAM DQ VREF Select for Rank0
    *  PSU_DDR_PHY_DX8GCR6_DXDQVREFR0                              0x2b

    * DATX8 n General Configuration Register 6
    * (OFFSET, MASK, VALUE)      (0XFD080F18, 0xFFFFFFFFU ,0x09092B2BU)
    */
	PSU_Mask_Write(DDR_PHY_DX8GCR6_OFFSET, 0xFFFFFFFFU, 0x09092B2BU);
/*##################################################################### */

    /*
    * Register : DX8SL0OSC @ 0XFD081400

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX8SL0OSC_RESERVED_31_30                        0x0

    * Enable Clock Gating for DX ddr_clk
    *  PSU_DDR_PHY_DX8SL0OSC_GATEDXRDCLK                           0x2

    * Enable Clock Gating for DX ctl_rd_clk
    *  PSU_DDR_PHY_DX8SL0OSC_GATEDXDDRCLK                          0x2

    * Enable Clock Gating for DX ctl_clk
    *  PSU_DDR_PHY_DX8SL0OSC_GATEDXCTLCLK                          0x2

    * Selects the level to which clocks will be stalled when clock gating is e
    * nabled.
    *  PSU_DDR_PHY_DX8SL0OSC_CLKLEVEL                              0x0

    * Loopback Mode
    *  PSU_DDR_PHY_DX8SL0OSC_LBMODE                                0x0

    * Load GSDQS LCDL with 2x the calibrated GSDQSPRD value
    *  PSU_DDR_PHY_DX8SL0OSC_LBGSDQS                               0x0

    * Loopback DQS Gating
    *  PSU_DDR_PHY_DX8SL0OSC_LBGDQS                                0x0

    * Loopback DQS Shift
    *  PSU_DDR_PHY_DX8SL0OSC_LBDQSS                                0x0

    * PHY High-Speed Reset
    *  PSU_DDR_PHY_DX8SL0OSC_PHYHRST                               0x1

    * PHY FIFO Reset
    *  PSU_DDR_PHY_DX8SL0OSC_PHYFRST                               0x1

    * Delay Line Test Start
    *  PSU_DDR_PHY_DX8SL0OSC_DLTST                                 0x0

    * Delay Line Test Mode
    *  PSU_DDR_PHY_DX8SL0OSC_DLTMODE                               0x0

    * Reserved. Caution, do not write to this register field.
    *  PSU_DDR_PHY_DX8SL0OSC_RESERVED_12_11                        0x3

    * Oscillator Mode Write-Data Delay Line Select
    *  PSU_DDR_PHY_DX8SL0OSC_OSCWDDL                               0x3

    * Reserved. Caution, do not write to this register field.
    *  PSU_DDR_PHY_DX8SL0OSC_RESERVED_8_7                          0x3

    * Oscillator Mode Write-Leveling Delay Line Select
    *  PSU_DDR_PHY_DX8SL0OSC_OSCWDL                                0x3

    * Oscillator Mode Division
    *  PSU_DDR_PHY_DX8SL0OSC_OSCDIV                                0xf

    * Oscillator Enable
    *  PSU_DDR_PHY_DX8SL0OSC_OSCEN                                 0x0

    * DATX8 0-1 Oscillator, Delay Line Test, PHY FIFO and High Speed Reset, Lo
    * opback, and Gated Clock Control Register
    * (OFFSET, MASK, VALUE)      (0XFD081400, 0xFFFFFFFFU ,0x2A019FFEU)
    */
	PSU_Mask_Write(DDR_PHY_DX8SL0OSC_OFFSET, 0xFFFFFFFFU, 0x2A019FFEU);
/*##################################################################### */

    /*
    * Register : DX8SL0PLLCR0 @ 0XFD081404

    * PLL Bypass
    *  PSU_DDR_PHY_DX8SL0PLLCR0_PLLBYP                             0x0

    * PLL Reset
    *  PSU_DDR_PHY_DX8SL0PLLCR0_PLLRST                             0x0

    * PLL Power Down
    *  PSU_DDR_PHY_DX8SL0PLLCR0_PLLPD                              0x0

    * Reference Stop Mode
    *  PSU_DDR_PHY_DX8SL0PLLCR0_RSTOPM                             0x0

    * PLL Frequency Select
    *  PSU_DDR_PHY_DX8SL0PLLCR0_FRQSEL                             0x1

    * Relock Mode
    *  PSU_DDR_PHY_DX8SL0PLLCR0_RLOCKM                             0x0

    * Charge Pump Proportional Current Control
    *  PSU_DDR_PHY_DX8SL0PLLCR0_CPPC                               0x8

    * Charge Pump Integrating Current Control
    *  PSU_DDR_PHY_DX8SL0PLLCR0_CPIC                               0x0

    * Gear Shift
    *  PSU_DDR_PHY_DX8SL0PLLCR0_GSHIFT                             0x0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX8SL0PLLCR0_RESERVED_11_9                      0x0

    * Analog Test Enable (ATOEN)
    *  PSU_DDR_PHY_DX8SL0PLLCR0_ATOEN                              0x0

    * Analog Test Control
    *  PSU_DDR_PHY_DX8SL0PLLCR0_ATC                                0x0

    * Digital Test Control
    *  PSU_DDR_PHY_DX8SL0PLLCR0_DTC                                0x0

    * DAXT8 0-1 PLL Control Register 0
    * (OFFSET, MASK, VALUE)      (0XFD081404, 0xFFFFFFFFU ,0x01100000U)
    */
	PSU_Mask_Write(DDR_PHY_DX8SL0PLLCR0_OFFSET,
		0xFFFFFFFFU, 0x01100000U);
/*##################################################################### */

    /*
    * Register : DX8SL0DQSCTL @ 0XFD08141C

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX8SL0DQSCTL_RESERVED_31_25                     0x0

    * Read Path Rise-to-Rise Mode
    *  PSU_DDR_PHY_DX8SL0DQSCTL_RRRMODE                            0x1

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX8SL0DQSCTL_RESERVED_23_22                     0x0

    * Write Path Rise-to-Rise Mode
    *  PSU_DDR_PHY_DX8SL0DQSCTL_WRRMODE                            0x1

    * DQS Gate Extension
    *  PSU_DDR_PHY_DX8SL0DQSCTL_DQSGX                              0x0

    * Low Power PLL Power Down
    *  PSU_DDR_PHY_DX8SL0DQSCTL_LPPLLPD                            0x1

    * Low Power I/O Power Down
    *  PSU_DDR_PHY_DX8SL0DQSCTL_LPIOPD                             0x1

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX8SL0DQSCTL_RESERVED_16_15                     0x0

    * QS Counter Enable
    *  PSU_DDR_PHY_DX8SL0DQSCTL_QSCNTEN                            0x1

    * Unused DQ I/O Mode
    *  PSU_DDR_PHY_DX8SL0DQSCTL_UDQIOM                             0x0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX8SL0DQSCTL_RESERVED_12_10                     0x0

    * Data Slew Rate
    *  PSU_DDR_PHY_DX8SL0DQSCTL_DXSR                               0x3

    * DQS_N Resistor
    *  PSU_DDR_PHY_DX8SL0DQSCTL_DQSNRES                            0x0

    * DQS Resistor
    *  PSU_DDR_PHY_DX8SL0DQSCTL_DQSRES                             0x0

    * DATX8 0-1 DQS Control Register
    * (OFFSET, MASK, VALUE)      (0XFD08141C, 0xFFFFFFFFU ,0x01264300U)
    */
	PSU_Mask_Write(DDR_PHY_DX8SL0DQSCTL_OFFSET,
		0xFFFFFFFFU, 0x01264300U);
/*##################################################################### */

    /*
    * Register : DX8SL0DXCTL2 @ 0XFD08142C

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX8SL0DXCTL2_RESERVED_31_24                     0x0

    * Configurable Read Data Enable
    *  PSU_DDR_PHY_DX8SL0DXCTL2_CRDEN                              0x0

    * OX Extension during Post-amble
    *  PSU_DDR_PHY_DX8SL0DXCTL2_POSOEX                             0x0

    * OE Extension during Pre-amble
    *  PSU_DDR_PHY_DX8SL0DXCTL2_PREOEX                             0x1

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX8SL0DXCTL2_RESERVED_17                        0x0

    * I/O Assisted Gate Select
    *  PSU_DDR_PHY_DX8SL0DXCTL2_IOAG                               0x0

    * I/O Loopback Select
    *  PSU_DDR_PHY_DX8SL0DXCTL2_IOLB                               0x0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX8SL0DXCTL2_RESERVED_14_13                     0x0

    * Low Power Wakeup Threshold
    *  PSU_DDR_PHY_DX8SL0DXCTL2_LPWAKEUP_THRSH                     0xc

    * Read Data Bus Inversion Enable
    *  PSU_DDR_PHY_DX8SL0DXCTL2_RDBI                               0x0

    * Write Data Bus Inversion Enable
    *  PSU_DDR_PHY_DX8SL0DXCTL2_WDBI                               0x0

    * PUB Read FIFO Bypass
    *  PSU_DDR_PHY_DX8SL0DXCTL2_PRFBYP                             0x0

    * DATX8 Receive FIFO Read Mode
    *  PSU_DDR_PHY_DX8SL0DXCTL2_RDMODE                             0x0

    * Disables the Read FIFO Reset
    *  PSU_DDR_PHY_DX8SL0DXCTL2_DISRST                             0x0

    * Read DQS Gate I/O Loopback
    *  PSU_DDR_PHY_DX8SL0DXCTL2_DQSGLB                             0x0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX8SL0DXCTL2_RESERVED_0                         0x0

    * DATX8 0-1 DX Control Register 2
    * (OFFSET, MASK, VALUE)      (0XFD08142C, 0xFFFFFFFFU ,0x00041800U)
    */
	PSU_Mask_Write(DDR_PHY_DX8SL0DXCTL2_OFFSET,
		0xFFFFFFFFU, 0x00041800U);
/*##################################################################### */

    /*
    * Register : DX8SL0IOCR @ 0XFD081430

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX8SL0IOCR_RESERVED_31                          0x0

    * PVREF_DAC REFSEL range select
    *  PSU_DDR_PHY_DX8SL0IOCR_DXDACRANGE                           0x7

    * IOM bits for PVREF, PVREF_DAC and PVREFE cells in DX IO ring
    *  PSU_DDR_PHY_DX8SL0IOCR_DXVREFIOM                            0x0

    * DX IO Mode
    *  PSU_DDR_PHY_DX8SL0IOCR_DXIOM                                0x2

    * DX IO Transmitter Mode
    *  PSU_DDR_PHY_DX8SL0IOCR_DXTXM                                0x0

    * DX IO Receiver Mode
    *  PSU_DDR_PHY_DX8SL0IOCR_DXRXM                                0x0

    * DATX8 0-1 I/O Configuration Register
    * (OFFSET, MASK, VALUE)      (0XFD081430, 0xFFFFFFFFU ,0x70800000U)
    */
	PSU_Mask_Write(DDR_PHY_DX8SL0IOCR_OFFSET, 0xFFFFFFFFU, 0x70800000U);
/*##################################################################### */

    /*
    * Register : DX8SL1OSC @ 0XFD081440

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX8SL1OSC_RESERVED_31_30                        0x0

    * Enable Clock Gating for DX ddr_clk
    *  PSU_DDR_PHY_DX8SL1OSC_GATEDXRDCLK                           0x2

    * Enable Clock Gating for DX ctl_rd_clk
    *  PSU_DDR_PHY_DX8SL1OSC_GATEDXDDRCLK                          0x2

    * Enable Clock Gating for DX ctl_clk
    *  PSU_DDR_PHY_DX8SL1OSC_GATEDXCTLCLK                          0x2

    * Selects the level to which clocks will be stalled when clock gating is e
    * nabled.
    *  PSU_DDR_PHY_DX8SL1OSC_CLKLEVEL                              0x0

    * Loopback Mode
    *  PSU_DDR_PHY_DX8SL1OSC_LBMODE                                0x0

    * Load GSDQS LCDL with 2x the calibrated GSDQSPRD value
    *  PSU_DDR_PHY_DX8SL1OSC_LBGSDQS                               0x0

    * Loopback DQS Gating
    *  PSU_DDR_PHY_DX8SL1OSC_LBGDQS                                0x0

    * Loopback DQS Shift
    *  PSU_DDR_PHY_DX8SL1OSC_LBDQSS                                0x0

    * PHY High-Speed Reset
    *  PSU_DDR_PHY_DX8SL1OSC_PHYHRST                               0x1

    * PHY FIFO Reset
    *  PSU_DDR_PHY_DX8SL1OSC_PHYFRST                               0x1

    * Delay Line Test Start
    *  PSU_DDR_PHY_DX8SL1OSC_DLTST                                 0x0

    * Delay Line Test Mode
    *  PSU_DDR_PHY_DX8SL1OSC_DLTMODE                               0x0

    * Reserved. Caution, do not write to this register field.
    *  PSU_DDR_PHY_DX8SL1OSC_RESERVED_12_11                        0x3

    * Oscillator Mode Write-Data Delay Line Select
    *  PSU_DDR_PHY_DX8SL1OSC_OSCWDDL                               0x3

    * Reserved. Caution, do not write to this register field.
    *  PSU_DDR_PHY_DX8SL1OSC_RESERVED_8_7                          0x3

    * Oscillator Mode Write-Leveling Delay Line Select
    *  PSU_DDR_PHY_DX8SL1OSC_OSCWDL                                0x3

    * Oscillator Mode Division
    *  PSU_DDR_PHY_DX8SL1OSC_OSCDIV                                0xf

    * Oscillator Enable
    *  PSU_DDR_PHY_DX8SL1OSC_OSCEN                                 0x0

    * DATX8 0-1 Oscillator, Delay Line Test, PHY FIFO and High Speed Reset, Lo
    * opback, and Gated Clock Control Register
    * (OFFSET, MASK, VALUE)      (0XFD081440, 0xFFFFFFFFU ,0x2A019FFEU)
    */
	PSU_Mask_Write(DDR_PHY_DX8SL1OSC_OFFSET, 0xFFFFFFFFU, 0x2A019FFEU);
/*##################################################################### */

    /*
    * Register : DX8SL1PLLCR0 @ 0XFD081444

    * PLL Bypass
    *  PSU_DDR_PHY_DX8SL1PLLCR0_PLLBYP                             0x0

    * PLL Reset
    *  PSU_DDR_PHY_DX8SL1PLLCR0_PLLRST                             0x0

    * PLL Power Down
    *  PSU_DDR_PHY_DX8SL1PLLCR0_PLLPD                              0x0

    * Reference Stop Mode
    *  PSU_DDR_PHY_DX8SL1PLLCR0_RSTOPM                             0x0

    * PLL Frequency Select
    *  PSU_DDR_PHY_DX8SL1PLLCR0_FRQSEL                             0x1

    * Relock Mode
    *  PSU_DDR_PHY_DX8SL1PLLCR0_RLOCKM                             0x0

    * Charge Pump Proportional Current Control
    *  PSU_DDR_PHY_DX8SL1PLLCR0_CPPC                               0x8

    * Charge Pump Integrating Current Control
    *  PSU_DDR_PHY_DX8SL1PLLCR0_CPIC                               0x0

    * Gear Shift
    *  PSU_DDR_PHY_DX8SL1PLLCR0_GSHIFT                             0x0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX8SL1PLLCR0_RESERVED_11_9                      0x0

    * Analog Test Enable (ATOEN)
    *  PSU_DDR_PHY_DX8SL1PLLCR0_ATOEN                              0x0

    * Analog Test Control
    *  PSU_DDR_PHY_DX8SL1PLLCR0_ATC                                0x0

    * Digital Test Control
    *  PSU_DDR_PHY_DX8SL1PLLCR0_DTC                                0x0

    * DAXT8 0-1 PLL Control Register 0
    * (OFFSET, MASK, VALUE)      (0XFD081444, 0xFFFFFFFFU ,0x01100000U)
    */
	PSU_Mask_Write(DDR_PHY_DX8SL1PLLCR0_OFFSET,
		0xFFFFFFFFU, 0x01100000U);
/*##################################################################### */

    /*
    * Register : DX8SL1DQSCTL @ 0XFD08145C

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX8SL1DQSCTL_RESERVED_31_25                     0x0

    * Read Path Rise-to-Rise Mode
    *  PSU_DDR_PHY_DX8SL1DQSCTL_RRRMODE                            0x1

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX8SL1DQSCTL_RESERVED_23_22                     0x0

    * Write Path Rise-to-Rise Mode
    *  PSU_DDR_PHY_DX8SL1DQSCTL_WRRMODE                            0x1

    * DQS Gate Extension
    *  PSU_DDR_PHY_DX8SL1DQSCTL_DQSGX                              0x0

    * Low Power PLL Power Down
    *  PSU_DDR_PHY_DX8SL1DQSCTL_LPPLLPD                            0x1

    * Low Power I/O Power Down
    *  PSU_DDR_PHY_DX8SL1DQSCTL_LPIOPD                             0x1

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX8SL1DQSCTL_RESERVED_16_15                     0x0

    * QS Counter Enable
    *  PSU_DDR_PHY_DX8SL1DQSCTL_QSCNTEN                            0x1

    * Unused DQ I/O Mode
    *  PSU_DDR_PHY_DX8SL1DQSCTL_UDQIOM                             0x0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX8SL1DQSCTL_RESERVED_12_10                     0x0

    * Data Slew Rate
    *  PSU_DDR_PHY_DX8SL1DQSCTL_DXSR                               0x3

    * DQS_N Resistor
    *  PSU_DDR_PHY_DX8SL1DQSCTL_DQSNRES                            0x0

    * DQS Resistor
    *  PSU_DDR_PHY_DX8SL1DQSCTL_DQSRES                             0x0

    * DATX8 0-1 DQS Control Register
    * (OFFSET, MASK, VALUE)      (0XFD08145C, 0xFFFFFFFFU ,0x01264300U)
    */
	PSU_Mask_Write(DDR_PHY_DX8SL1DQSCTL_OFFSET,
		0xFFFFFFFFU, 0x01264300U);
/*##################################################################### */

    /*
    * Register : DX8SL1DXCTL2 @ 0XFD08146C

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX8SL1DXCTL2_RESERVED_31_24                     0x0

    * Configurable Read Data Enable
    *  PSU_DDR_PHY_DX8SL1DXCTL2_CRDEN                              0x0

    * OX Extension during Post-amble
    *  PSU_DDR_PHY_DX8SL1DXCTL2_POSOEX                             0x0

    * OE Extension during Pre-amble
    *  PSU_DDR_PHY_DX8SL1DXCTL2_PREOEX                             0x1

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX8SL1DXCTL2_RESERVED_17                        0x0

    * I/O Assisted Gate Select
    *  PSU_DDR_PHY_DX8SL1DXCTL2_IOAG                               0x0

    * I/O Loopback Select
    *  PSU_DDR_PHY_DX8SL1DXCTL2_IOLB                               0x0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX8SL1DXCTL2_RESERVED_14_13                     0x0

    * Low Power Wakeup Threshold
    *  PSU_DDR_PHY_DX8SL1DXCTL2_LPWAKEUP_THRSH                     0xc

    * Read Data Bus Inversion Enable
    *  PSU_DDR_PHY_DX8SL1DXCTL2_RDBI                               0x0

    * Write Data Bus Inversion Enable
    *  PSU_DDR_PHY_DX8SL1DXCTL2_WDBI                               0x0

    * PUB Read FIFO Bypass
    *  PSU_DDR_PHY_DX8SL1DXCTL2_PRFBYP                             0x0

    * DATX8 Receive FIFO Read Mode
    *  PSU_DDR_PHY_DX8SL1DXCTL2_RDMODE                             0x0

    * Disables the Read FIFO Reset
    *  PSU_DDR_PHY_DX8SL1DXCTL2_DISRST                             0x0

    * Read DQS Gate I/O Loopback
    *  PSU_DDR_PHY_DX8SL1DXCTL2_DQSGLB                             0x0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX8SL1DXCTL2_RESERVED_0                         0x0

    * DATX8 0-1 DX Control Register 2
    * (OFFSET, MASK, VALUE)      (0XFD08146C, 0xFFFFFFFFU ,0x00041800U)
    */
	PSU_Mask_Write(DDR_PHY_DX8SL1DXCTL2_OFFSET,
		0xFFFFFFFFU, 0x00041800U);
/*##################################################################### */

    /*
    * Register : DX8SL1IOCR @ 0XFD081470

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX8SL1IOCR_RESERVED_31                          0x0

    * PVREF_DAC REFSEL range select
    *  PSU_DDR_PHY_DX8SL1IOCR_DXDACRANGE                           0x7

    * IOM bits for PVREF, PVREF_DAC and PVREFE cells in DX IO ring
    *  PSU_DDR_PHY_DX8SL1IOCR_DXVREFIOM                            0x0

    * DX IO Mode
    *  PSU_DDR_PHY_DX8SL1IOCR_DXIOM                                0x2

    * DX IO Transmitter Mode
    *  PSU_DDR_PHY_DX8SL1IOCR_DXTXM                                0x0

    * DX IO Receiver Mode
    *  PSU_DDR_PHY_DX8SL1IOCR_DXRXM                                0x0

    * DATX8 0-1 I/O Configuration Register
    * (OFFSET, MASK, VALUE)      (0XFD081470, 0xFFFFFFFFU ,0x70800000U)
    */
	PSU_Mask_Write(DDR_PHY_DX8SL1IOCR_OFFSET, 0xFFFFFFFFU, 0x70800000U);
/*##################################################################### */

    /*
    * Register : DX8SL2OSC @ 0XFD081480

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX8SL2OSC_RESERVED_31_30                        0x0

    * Enable Clock Gating for DX ddr_clk
    *  PSU_DDR_PHY_DX8SL2OSC_GATEDXRDCLK                           0x2

    * Enable Clock Gating for DX ctl_rd_clk
    *  PSU_DDR_PHY_DX8SL2OSC_GATEDXDDRCLK                          0x2

    * Enable Clock Gating for DX ctl_clk
    *  PSU_DDR_PHY_DX8SL2OSC_GATEDXCTLCLK                          0x2

    * Selects the level to which clocks will be stalled when clock gating is e
    * nabled.
    *  PSU_DDR_PHY_DX8SL2OSC_CLKLEVEL                              0x0

    * Loopback Mode
    *  PSU_DDR_PHY_DX8SL2OSC_LBMODE                                0x0

    * Load GSDQS LCDL with 2x the calibrated GSDQSPRD value
    *  PSU_DDR_PHY_DX8SL2OSC_LBGSDQS                               0x0

    * Loopback DQS Gating
    *  PSU_DDR_PHY_DX8SL2OSC_LBGDQS                                0x0

    * Loopback DQS Shift
    *  PSU_DDR_PHY_DX8SL2OSC_LBDQSS                                0x0

    * PHY High-Speed Reset
    *  PSU_DDR_PHY_DX8SL2OSC_PHYHRST                               0x1

    * PHY FIFO Reset
    *  PSU_DDR_PHY_DX8SL2OSC_PHYFRST                               0x1

    * Delay Line Test Start
    *  PSU_DDR_PHY_DX8SL2OSC_DLTST                                 0x0

    * Delay Line Test Mode
    *  PSU_DDR_PHY_DX8SL2OSC_DLTMODE                               0x0

    * Reserved. Caution, do not write to this register field.
    *  PSU_DDR_PHY_DX8SL2OSC_RESERVED_12_11                        0x3

    * Oscillator Mode Write-Data Delay Line Select
    *  PSU_DDR_PHY_DX8SL2OSC_OSCWDDL                               0x3

    * Reserved. Caution, do not write to this register field.
    *  PSU_DDR_PHY_DX8SL2OSC_RESERVED_8_7                          0x3

    * Oscillator Mode Write-Leveling Delay Line Select
    *  PSU_DDR_PHY_DX8SL2OSC_OSCWDL                                0x3

    * Oscillator Mode Division
    *  PSU_DDR_PHY_DX8SL2OSC_OSCDIV                                0xf

    * Oscillator Enable
    *  PSU_DDR_PHY_DX8SL2OSC_OSCEN                                 0x0

    * DATX8 0-1 Oscillator, Delay Line Test, PHY FIFO and High Speed Reset, Lo
    * opback, and Gated Clock Control Register
    * (OFFSET, MASK, VALUE)      (0XFD081480, 0xFFFFFFFFU ,0x2A019FFEU)
    */
	PSU_Mask_Write(DDR_PHY_DX8SL2OSC_OFFSET, 0xFFFFFFFFU, 0x2A019FFEU);
/*##################################################################### */

    /*
    * Register : DX8SL2PLLCR0 @ 0XFD081484

    * PLL Bypass
    *  PSU_DDR_PHY_DX8SL2PLLCR0_PLLBYP                             0x0

    * PLL Reset
    *  PSU_DDR_PHY_DX8SL2PLLCR0_PLLRST                             0x0

    * PLL Power Down
    *  PSU_DDR_PHY_DX8SL2PLLCR0_PLLPD                              0x0

    * Reference Stop Mode
    *  PSU_DDR_PHY_DX8SL2PLLCR0_RSTOPM                             0x0

    * PLL Frequency Select
    *  PSU_DDR_PHY_DX8SL2PLLCR0_FRQSEL                             0x1

    * Relock Mode
    *  PSU_DDR_PHY_DX8SL2PLLCR0_RLOCKM                             0x0

    * Charge Pump Proportional Current Control
    *  PSU_DDR_PHY_DX8SL2PLLCR0_CPPC                               0x8

    * Charge Pump Integrating Current Control
    *  PSU_DDR_PHY_DX8SL2PLLCR0_CPIC                               0x0

    * Gear Shift
    *  PSU_DDR_PHY_DX8SL2PLLCR0_GSHIFT                             0x0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX8SL2PLLCR0_RESERVED_11_9                      0x0

    * Analog Test Enable (ATOEN)
    *  PSU_DDR_PHY_DX8SL2PLLCR0_ATOEN                              0x0

    * Analog Test Control
    *  PSU_DDR_PHY_DX8SL2PLLCR0_ATC                                0x0

    * Digital Test Control
    *  PSU_DDR_PHY_DX8SL2PLLCR0_DTC                                0x0

    * DAXT8 0-1 PLL Control Register 0
    * (OFFSET, MASK, VALUE)      (0XFD081484, 0xFFFFFFFFU ,0x01100000U)
    */
	PSU_Mask_Write(DDR_PHY_DX8SL2PLLCR0_OFFSET,
		0xFFFFFFFFU, 0x01100000U);
/*##################################################################### */

    /*
    * Register : DX8SL2DQSCTL @ 0XFD08149C

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX8SL2DQSCTL_RESERVED_31_25                     0x0

    * Read Path Rise-to-Rise Mode
    *  PSU_DDR_PHY_DX8SL2DQSCTL_RRRMODE                            0x1

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX8SL2DQSCTL_RESERVED_23_22                     0x0

    * Write Path Rise-to-Rise Mode
    *  PSU_DDR_PHY_DX8SL2DQSCTL_WRRMODE                            0x1

    * DQS Gate Extension
    *  PSU_DDR_PHY_DX8SL2DQSCTL_DQSGX                              0x0

    * Low Power PLL Power Down
    *  PSU_DDR_PHY_DX8SL2DQSCTL_LPPLLPD                            0x1

    * Low Power I/O Power Down
    *  PSU_DDR_PHY_DX8SL2DQSCTL_LPIOPD                             0x1

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX8SL2DQSCTL_RESERVED_16_15                     0x0

    * QS Counter Enable
    *  PSU_DDR_PHY_DX8SL2DQSCTL_QSCNTEN                            0x1

    * Unused DQ I/O Mode
    *  PSU_DDR_PHY_DX8SL2DQSCTL_UDQIOM                             0x0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX8SL2DQSCTL_RESERVED_12_10                     0x0

    * Data Slew Rate
    *  PSU_DDR_PHY_DX8SL2DQSCTL_DXSR                               0x3

    * DQS_N Resistor
    *  PSU_DDR_PHY_DX8SL2DQSCTL_DQSNRES                            0x0

    * DQS Resistor
    *  PSU_DDR_PHY_DX8SL2DQSCTL_DQSRES                             0x0

    * DATX8 0-1 DQS Control Register
    * (OFFSET, MASK, VALUE)      (0XFD08149C, 0xFFFFFFFFU ,0x01264300U)
    */
	PSU_Mask_Write(DDR_PHY_DX8SL2DQSCTL_OFFSET,
		0xFFFFFFFFU, 0x01264300U);
/*##################################################################### */

    /*
    * Register : DX8SL2DXCTL2 @ 0XFD0814AC

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX8SL2DXCTL2_RESERVED_31_24                     0x0

    * Configurable Read Data Enable
    *  PSU_DDR_PHY_DX8SL2DXCTL2_CRDEN                              0x0

    * OX Extension during Post-amble
    *  PSU_DDR_PHY_DX8SL2DXCTL2_POSOEX                             0x0

    * OE Extension during Pre-amble
    *  PSU_DDR_PHY_DX8SL2DXCTL2_PREOEX                             0x1

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX8SL2DXCTL2_RESERVED_17                        0x0

    * I/O Assisted Gate Select
    *  PSU_DDR_PHY_DX8SL2DXCTL2_IOAG                               0x0

    * I/O Loopback Select
    *  PSU_DDR_PHY_DX8SL2DXCTL2_IOLB                               0x0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX8SL2DXCTL2_RESERVED_14_13                     0x0

    * Low Power Wakeup Threshold
    *  PSU_DDR_PHY_DX8SL2DXCTL2_LPWAKEUP_THRSH                     0xc

    * Read Data Bus Inversion Enable
    *  PSU_DDR_PHY_DX8SL2DXCTL2_RDBI                               0x0

    * Write Data Bus Inversion Enable
    *  PSU_DDR_PHY_DX8SL2DXCTL2_WDBI                               0x0

    * PUB Read FIFO Bypass
    *  PSU_DDR_PHY_DX8SL2DXCTL2_PRFBYP                             0x0

    * DATX8 Receive FIFO Read Mode
    *  PSU_DDR_PHY_DX8SL2DXCTL2_RDMODE                             0x0

    * Disables the Read FIFO Reset
    *  PSU_DDR_PHY_DX8SL2DXCTL2_DISRST                             0x0

    * Read DQS Gate I/O Loopback
    *  PSU_DDR_PHY_DX8SL2DXCTL2_DQSGLB                             0x0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX8SL2DXCTL2_RESERVED_0                         0x0

    * DATX8 0-1 DX Control Register 2
    * (OFFSET, MASK, VALUE)      (0XFD0814AC, 0xFFFFFFFFU ,0x00041800U)
    */
	PSU_Mask_Write(DDR_PHY_DX8SL2DXCTL2_OFFSET,
		0xFFFFFFFFU, 0x00041800U);
/*##################################################################### */

    /*
    * Register : DX8SL2IOCR @ 0XFD0814B0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX8SL2IOCR_RESERVED_31                          0x0

    * PVREF_DAC REFSEL range select
    *  PSU_DDR_PHY_DX8SL2IOCR_DXDACRANGE                           0x7

    * IOM bits for PVREF, PVREF_DAC and PVREFE cells in DX IO ring
    *  PSU_DDR_PHY_DX8SL2IOCR_DXVREFIOM                            0x0

    * DX IO Mode
    *  PSU_DDR_PHY_DX8SL2IOCR_DXIOM                                0x2

    * DX IO Transmitter Mode
    *  PSU_DDR_PHY_DX8SL2IOCR_DXTXM                                0x0

    * DX IO Receiver Mode
    *  PSU_DDR_PHY_DX8SL2IOCR_DXRXM                                0x0

    * DATX8 0-1 I/O Configuration Register
    * (OFFSET, MASK, VALUE)      (0XFD0814B0, 0xFFFFFFFFU ,0x70800000U)
    */
	PSU_Mask_Write(DDR_PHY_DX8SL2IOCR_OFFSET, 0xFFFFFFFFU, 0x70800000U);
/*##################################################################### */

    /*
    * Register : DX8SL3OSC @ 0XFD0814C0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX8SL3OSC_RESERVED_31_30                        0x0

    * Enable Clock Gating for DX ddr_clk
    *  PSU_DDR_PHY_DX8SL3OSC_GATEDXRDCLK                           0x2

    * Enable Clock Gating for DX ctl_rd_clk
    *  PSU_DDR_PHY_DX8SL3OSC_GATEDXDDRCLK                          0x2

    * Enable Clock Gating for DX ctl_clk
    *  PSU_DDR_PHY_DX8SL3OSC_GATEDXCTLCLK                          0x2

    * Selects the level to which clocks will be stalled when clock gating is e
    * nabled.
    *  PSU_DDR_PHY_DX8SL3OSC_CLKLEVEL                              0x0

    * Loopback Mode
    *  PSU_DDR_PHY_DX8SL3OSC_LBMODE                                0x0

    * Load GSDQS LCDL with 2x the calibrated GSDQSPRD value
    *  PSU_DDR_PHY_DX8SL3OSC_LBGSDQS                               0x0

    * Loopback DQS Gating
    *  PSU_DDR_PHY_DX8SL3OSC_LBGDQS                                0x0

    * Loopback DQS Shift
    *  PSU_DDR_PHY_DX8SL3OSC_LBDQSS                                0x0

    * PHY High-Speed Reset
    *  PSU_DDR_PHY_DX8SL3OSC_PHYHRST                               0x1

    * PHY FIFO Reset
    *  PSU_DDR_PHY_DX8SL3OSC_PHYFRST                               0x1

    * Delay Line Test Start
    *  PSU_DDR_PHY_DX8SL3OSC_DLTST                                 0x0

    * Delay Line Test Mode
    *  PSU_DDR_PHY_DX8SL3OSC_DLTMODE                               0x0

    * Reserved. Caution, do not write to this register field.
    *  PSU_DDR_PHY_DX8SL3OSC_RESERVED_12_11                        0x3

    * Oscillator Mode Write-Data Delay Line Select
    *  PSU_DDR_PHY_DX8SL3OSC_OSCWDDL                               0x3

    * Reserved. Caution, do not write to this register field.
    *  PSU_DDR_PHY_DX8SL3OSC_RESERVED_8_7                          0x3

    * Oscillator Mode Write-Leveling Delay Line Select
    *  PSU_DDR_PHY_DX8SL3OSC_OSCWDL                                0x3

    * Oscillator Mode Division
    *  PSU_DDR_PHY_DX8SL3OSC_OSCDIV                                0xf

    * Oscillator Enable
    *  PSU_DDR_PHY_DX8SL3OSC_OSCEN                                 0x0

    * DATX8 0-1 Oscillator, Delay Line Test, PHY FIFO and High Speed Reset, Lo
    * opback, and Gated Clock Control Register
    * (OFFSET, MASK, VALUE)      (0XFD0814C0, 0xFFFFFFFFU ,0x2A019FFEU)
    */
	PSU_Mask_Write(DDR_PHY_DX8SL3OSC_OFFSET, 0xFFFFFFFFU, 0x2A019FFEU);
/*##################################################################### */

    /*
    * Register : DX8SL3PLLCR0 @ 0XFD0814C4

    * PLL Bypass
    *  PSU_DDR_PHY_DX8SL3PLLCR0_PLLBYP                             0x0

    * PLL Reset
    *  PSU_DDR_PHY_DX8SL3PLLCR0_PLLRST                             0x0

    * PLL Power Down
    *  PSU_DDR_PHY_DX8SL3PLLCR0_PLLPD                              0x0

    * Reference Stop Mode
    *  PSU_DDR_PHY_DX8SL3PLLCR0_RSTOPM                             0x0

    * PLL Frequency Select
    *  PSU_DDR_PHY_DX8SL3PLLCR0_FRQSEL                             0x1

    * Relock Mode
    *  PSU_DDR_PHY_DX8SL3PLLCR0_RLOCKM                             0x0

    * Charge Pump Proportional Current Control
    *  PSU_DDR_PHY_DX8SL3PLLCR0_CPPC                               0x8

    * Charge Pump Integrating Current Control
    *  PSU_DDR_PHY_DX8SL3PLLCR0_CPIC                               0x0

    * Gear Shift
    *  PSU_DDR_PHY_DX8SL3PLLCR0_GSHIFT                             0x0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX8SL3PLLCR0_RESERVED_11_9                      0x0

    * Analog Test Enable (ATOEN)
    *  PSU_DDR_PHY_DX8SL3PLLCR0_ATOEN                              0x0

    * Analog Test Control
    *  PSU_DDR_PHY_DX8SL3PLLCR0_ATC                                0x0

    * Digital Test Control
    *  PSU_DDR_PHY_DX8SL3PLLCR0_DTC                                0x0

    * DAXT8 0-1 PLL Control Register 0
    * (OFFSET, MASK, VALUE)      (0XFD0814C4, 0xFFFFFFFFU ,0x01100000U)
    */
	PSU_Mask_Write(DDR_PHY_DX8SL3PLLCR0_OFFSET,
		0xFFFFFFFFU, 0x01100000U);
/*##################################################################### */

    /*
    * Register : DX8SL3DQSCTL @ 0XFD0814DC

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX8SL3DQSCTL_RESERVED_31_25                     0x0

    * Read Path Rise-to-Rise Mode
    *  PSU_DDR_PHY_DX8SL3DQSCTL_RRRMODE                            0x1

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX8SL3DQSCTL_RESERVED_23_22                     0x0

    * Write Path Rise-to-Rise Mode
    *  PSU_DDR_PHY_DX8SL3DQSCTL_WRRMODE                            0x1

    * DQS Gate Extension
    *  PSU_DDR_PHY_DX8SL3DQSCTL_DQSGX                              0x0

    * Low Power PLL Power Down
    *  PSU_DDR_PHY_DX8SL3DQSCTL_LPPLLPD                            0x1

    * Low Power I/O Power Down
    *  PSU_DDR_PHY_DX8SL3DQSCTL_LPIOPD                             0x1

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX8SL3DQSCTL_RESERVED_16_15                     0x0

    * QS Counter Enable
    *  PSU_DDR_PHY_DX8SL3DQSCTL_QSCNTEN                            0x1

    * Unused DQ I/O Mode
    *  PSU_DDR_PHY_DX8SL3DQSCTL_UDQIOM                             0x0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX8SL3DQSCTL_RESERVED_12_10                     0x0

    * Data Slew Rate
    *  PSU_DDR_PHY_DX8SL3DQSCTL_DXSR                               0x3

    * DQS_N Resistor
    *  PSU_DDR_PHY_DX8SL3DQSCTL_DQSNRES                            0x0

    * DQS Resistor
    *  PSU_DDR_PHY_DX8SL3DQSCTL_DQSRES                             0x0

    * DATX8 0-1 DQS Control Register
    * (OFFSET, MASK, VALUE)      (0XFD0814DC, 0xFFFFFFFFU ,0x01264300U)
    */
	PSU_Mask_Write(DDR_PHY_DX8SL3DQSCTL_OFFSET,
		0xFFFFFFFFU, 0x01264300U);
/*##################################################################### */

    /*
    * Register : DX8SL3DXCTL2 @ 0XFD0814EC

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX8SL3DXCTL2_RESERVED_31_24                     0x0

    * Configurable Read Data Enable
    *  PSU_DDR_PHY_DX8SL3DXCTL2_CRDEN                              0x0

    * OX Extension during Post-amble
    *  PSU_DDR_PHY_DX8SL3DXCTL2_POSOEX                             0x0

    * OE Extension during Pre-amble
    *  PSU_DDR_PHY_DX8SL3DXCTL2_PREOEX                             0x1

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX8SL3DXCTL2_RESERVED_17                        0x0

    * I/O Assisted Gate Select
    *  PSU_DDR_PHY_DX8SL3DXCTL2_IOAG                               0x0

    * I/O Loopback Select
    *  PSU_DDR_PHY_DX8SL3DXCTL2_IOLB                               0x0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX8SL3DXCTL2_RESERVED_14_13                     0x0

    * Low Power Wakeup Threshold
    *  PSU_DDR_PHY_DX8SL3DXCTL2_LPWAKEUP_THRSH                     0xc

    * Read Data Bus Inversion Enable
    *  PSU_DDR_PHY_DX8SL3DXCTL2_RDBI                               0x0

    * Write Data Bus Inversion Enable
    *  PSU_DDR_PHY_DX8SL3DXCTL2_WDBI                               0x0

    * PUB Read FIFO Bypass
    *  PSU_DDR_PHY_DX8SL3DXCTL2_PRFBYP                             0x0

    * DATX8 Receive FIFO Read Mode
    *  PSU_DDR_PHY_DX8SL3DXCTL2_RDMODE                             0x0

    * Disables the Read FIFO Reset
    *  PSU_DDR_PHY_DX8SL3DXCTL2_DISRST                             0x0

    * Read DQS Gate I/O Loopback
    *  PSU_DDR_PHY_DX8SL3DXCTL2_DQSGLB                             0x0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX8SL3DXCTL2_RESERVED_0                         0x0

    * DATX8 0-1 DX Control Register 2
    * (OFFSET, MASK, VALUE)      (0XFD0814EC, 0xFFFFFFFFU ,0x00041800U)
    */
	PSU_Mask_Write(DDR_PHY_DX8SL3DXCTL2_OFFSET,
		0xFFFFFFFFU, 0x00041800U);
/*##################################################################### */

    /*
    * Register : DX8SL3IOCR @ 0XFD0814F0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX8SL3IOCR_RESERVED_31                          0x0

    * PVREF_DAC REFSEL range select
    *  PSU_DDR_PHY_DX8SL3IOCR_DXDACRANGE                           0x7

    * IOM bits for PVREF, PVREF_DAC and PVREFE cells in DX IO ring
    *  PSU_DDR_PHY_DX8SL3IOCR_DXVREFIOM                            0x0

    * DX IO Mode
    *  PSU_DDR_PHY_DX8SL3IOCR_DXIOM                                0x2

    * DX IO Transmitter Mode
    *  PSU_DDR_PHY_DX8SL3IOCR_DXTXM                                0x0

    * DX IO Receiver Mode
    *  PSU_DDR_PHY_DX8SL3IOCR_DXRXM                                0x0

    * DATX8 0-1 I/O Configuration Register
    * (OFFSET, MASK, VALUE)      (0XFD0814F0, 0xFFFFFFFFU ,0x70800000U)
    */
	PSU_Mask_Write(DDR_PHY_DX8SL3IOCR_OFFSET, 0xFFFFFFFFU, 0x70800000U);
/*##################################################################### */

    /*
    * Register : DX8SL4OSC @ 0XFD081500

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX8SL4OSC_RESERVED_31_30                        0x0

    * Enable Clock Gating for DX ddr_clk
    *  PSU_DDR_PHY_DX8SL4OSC_GATEDXRDCLK                           0x2

    * Enable Clock Gating for DX ctl_rd_clk
    *  PSU_DDR_PHY_DX8SL4OSC_GATEDXDDRCLK                          0x2

    * Enable Clock Gating for DX ctl_clk
    *  PSU_DDR_PHY_DX8SL4OSC_GATEDXCTLCLK                          0x2

    * Selects the level to which clocks will be stalled when clock gating is e
    * nabled.
    *  PSU_DDR_PHY_DX8SL4OSC_CLKLEVEL                              0x0

    * Loopback Mode
    *  PSU_DDR_PHY_DX8SL4OSC_LBMODE                                0x0

    * Load GSDQS LCDL with 2x the calibrated GSDQSPRD value
    *  PSU_DDR_PHY_DX8SL4OSC_LBGSDQS                               0x0

    * Loopback DQS Gating
    *  PSU_DDR_PHY_DX8SL4OSC_LBGDQS                                0x0

    * Loopback DQS Shift
    *  PSU_DDR_PHY_DX8SL4OSC_LBDQSS                                0x0

    * PHY High-Speed Reset
    *  PSU_DDR_PHY_DX8SL4OSC_PHYHRST                               0x1

    * PHY FIFO Reset
    *  PSU_DDR_PHY_DX8SL4OSC_PHYFRST                               0x1

    * Delay Line Test Start
    *  PSU_DDR_PHY_DX8SL4OSC_DLTST                                 0x0

    * Delay Line Test Mode
    *  PSU_DDR_PHY_DX8SL4OSC_DLTMODE                               0x0

    * Reserved. Caution, do not write to this register field.
    *  PSU_DDR_PHY_DX8SL4OSC_RESERVED_12_11                        0x3

    * Oscillator Mode Write-Data Delay Line Select
    *  PSU_DDR_PHY_DX8SL4OSC_OSCWDDL                               0x3

    * Reserved. Caution, do not write to this register field.
    *  PSU_DDR_PHY_DX8SL4OSC_RESERVED_8_7                          0x3

    * Oscillator Mode Write-Leveling Delay Line Select
    *  PSU_DDR_PHY_DX8SL4OSC_OSCWDL                                0x3

    * Oscillator Mode Division
    *  PSU_DDR_PHY_DX8SL4OSC_OSCDIV                                0xf

    * Oscillator Enable
    *  PSU_DDR_PHY_DX8SL4OSC_OSCEN                                 0x0

    * DATX8 0-1 Oscillator, Delay Line Test, PHY FIFO and High Speed Reset, Lo
    * opback, and Gated Clock Control Register
    * (OFFSET, MASK, VALUE)      (0XFD081500, 0xFFFFFFFFU ,0x2A019FFEU)
    */
	PSU_Mask_Write(DDR_PHY_DX8SL4OSC_OFFSET, 0xFFFFFFFFU, 0x2A019FFEU);
/*##################################################################### */

    /*
    * Register : DX8SL4PLLCR0 @ 0XFD081504

    * PLL Bypass
    *  PSU_DDR_PHY_DX8SL4PLLCR0_PLLBYP                             0x0

    * PLL Reset
    *  PSU_DDR_PHY_DX8SL4PLLCR0_PLLRST                             0x0

    * PLL Power Down
    *  PSU_DDR_PHY_DX8SL4PLLCR0_PLLPD                              0x0

    * Reference Stop Mode
    *  PSU_DDR_PHY_DX8SL4PLLCR0_RSTOPM                             0x0

    * PLL Frequency Select
    *  PSU_DDR_PHY_DX8SL4PLLCR0_FRQSEL                             0x1

    * Relock Mode
    *  PSU_DDR_PHY_DX8SL4PLLCR0_RLOCKM                             0x0

    * Charge Pump Proportional Current Control
    *  PSU_DDR_PHY_DX8SL4PLLCR0_CPPC                               0x8

    * Charge Pump Integrating Current Control
    *  PSU_DDR_PHY_DX8SL4PLLCR0_CPIC                               0x0

    * Gear Shift
    *  PSU_DDR_PHY_DX8SL4PLLCR0_GSHIFT                             0x0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX8SL4PLLCR0_RESERVED_11_9                      0x0

    * Analog Test Enable (ATOEN)
    *  PSU_DDR_PHY_DX8SL4PLLCR0_ATOEN                              0x0

    * Analog Test Control
    *  PSU_DDR_PHY_DX8SL4PLLCR0_ATC                                0x0

    * Digital Test Control
    *  PSU_DDR_PHY_DX8SL4PLLCR0_DTC                                0x0

    * DAXT8 0-1 PLL Control Register 0
    * (OFFSET, MASK, VALUE)      (0XFD081504, 0xFFFFFFFFU ,0x01100000U)
    */
	PSU_Mask_Write(DDR_PHY_DX8SL4PLLCR0_OFFSET,
		0xFFFFFFFFU, 0x01100000U);
/*##################################################################### */

    /*
    * Register : DX8SL4DQSCTL @ 0XFD08151C

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX8SL4DQSCTL_RESERVED_31_25                     0x0

    * Read Path Rise-to-Rise Mode
    *  PSU_DDR_PHY_DX8SL4DQSCTL_RRRMODE                            0x1

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX8SL4DQSCTL_RESERVED_23_22                     0x0

    * Write Path Rise-to-Rise Mode
    *  PSU_DDR_PHY_DX8SL4DQSCTL_WRRMODE                            0x1

    * DQS Gate Extension
    *  PSU_DDR_PHY_DX8SL4DQSCTL_DQSGX                              0x0

    * Low Power PLL Power Down
    *  PSU_DDR_PHY_DX8SL4DQSCTL_LPPLLPD                            0x1

    * Low Power I/O Power Down
    *  PSU_DDR_PHY_DX8SL4DQSCTL_LPIOPD                             0x1

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX8SL4DQSCTL_RESERVED_16_15                     0x0

    * QS Counter Enable
    *  PSU_DDR_PHY_DX8SL4DQSCTL_QSCNTEN                            0x1

    * Unused DQ I/O Mode
    *  PSU_DDR_PHY_DX8SL4DQSCTL_UDQIOM                             0x0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX8SL4DQSCTL_RESERVED_12_10                     0x0

    * Data Slew Rate
    *  PSU_DDR_PHY_DX8SL4DQSCTL_DXSR                               0x3

    * DQS_N Resistor
    *  PSU_DDR_PHY_DX8SL4DQSCTL_DQSNRES                            0x0

    * DQS Resistor
    *  PSU_DDR_PHY_DX8SL4DQSCTL_DQSRES                             0x0

    * DATX8 0-1 DQS Control Register
    * (OFFSET, MASK, VALUE)      (0XFD08151C, 0xFFFFFFFFU ,0x01264300U)
    */
	PSU_Mask_Write(DDR_PHY_DX8SL4DQSCTL_OFFSET,
		0xFFFFFFFFU, 0x01264300U);
/*##################################################################### */

    /*
    * Register : DX8SL4DXCTL2 @ 0XFD08152C

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX8SL4DXCTL2_RESERVED_31_24                     0x0

    * Configurable Read Data Enable
    *  PSU_DDR_PHY_DX8SL4DXCTL2_CRDEN                              0x0

    * OX Extension during Post-amble
    *  PSU_DDR_PHY_DX8SL4DXCTL2_POSOEX                             0x0

    * OE Extension during Pre-amble
    *  PSU_DDR_PHY_DX8SL4DXCTL2_PREOEX                             0x1

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX8SL4DXCTL2_RESERVED_17                        0x0

    * I/O Assisted Gate Select
    *  PSU_DDR_PHY_DX8SL4DXCTL2_IOAG                               0x0

    * I/O Loopback Select
    *  PSU_DDR_PHY_DX8SL4DXCTL2_IOLB                               0x0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX8SL4DXCTL2_RESERVED_14_13                     0x0

    * Low Power Wakeup Threshold
    *  PSU_DDR_PHY_DX8SL4DXCTL2_LPWAKEUP_THRSH                     0xc

    * Read Data Bus Inversion Enable
    *  PSU_DDR_PHY_DX8SL4DXCTL2_RDBI                               0x0

    * Write Data Bus Inversion Enable
    *  PSU_DDR_PHY_DX8SL4DXCTL2_WDBI                               0x0

    * PUB Read FIFO Bypass
    *  PSU_DDR_PHY_DX8SL4DXCTL2_PRFBYP                             0x0

    * DATX8 Receive FIFO Read Mode
    *  PSU_DDR_PHY_DX8SL4DXCTL2_RDMODE                             0x0

    * Disables the Read FIFO Reset
    *  PSU_DDR_PHY_DX8SL4DXCTL2_DISRST                             0x0

    * Read DQS Gate I/O Loopback
    *  PSU_DDR_PHY_DX8SL4DXCTL2_DQSGLB                             0x0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX8SL4DXCTL2_RESERVED_0                         0x0

    * DATX8 0-1 DX Control Register 2
    * (OFFSET, MASK, VALUE)      (0XFD08152C, 0xFFFFFFFFU ,0x00041800U)
    */
	PSU_Mask_Write(DDR_PHY_DX8SL4DXCTL2_OFFSET,
		0xFFFFFFFFU, 0x00041800U);
/*##################################################################### */

    /*
    * Register : DX8SL4IOCR @ 0XFD081530

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX8SL4IOCR_RESERVED_31                          0x0

    * PVREF_DAC REFSEL range select
    *  PSU_DDR_PHY_DX8SL4IOCR_DXDACRANGE                           0x7

    * IOM bits for PVREF, PVREF_DAC and PVREFE cells in DX IO ring
    *  PSU_DDR_PHY_DX8SL4IOCR_DXVREFIOM                            0x0

    * DX IO Mode
    *  PSU_DDR_PHY_DX8SL4IOCR_DXIOM                                0x2

    * DX IO Transmitter Mode
    *  PSU_DDR_PHY_DX8SL4IOCR_DXTXM                                0x0

    * DX IO Receiver Mode
    *  PSU_DDR_PHY_DX8SL4IOCR_DXRXM                                0x0

    * DATX8 0-1 I/O Configuration Register
    * (OFFSET, MASK, VALUE)      (0XFD081530, 0xFFFFFFFFU ,0x70800000U)
    */
	PSU_Mask_Write(DDR_PHY_DX8SL4IOCR_OFFSET, 0xFFFFFFFFU, 0x70800000U);
/*##################################################################### */

    /*
    * Register : DX8SLbPLLCR0 @ 0XFD0817C4

    * PLL Bypass
    *  PSU_DDR_PHY_DX8SLBPLLCR0_PLLBYP                             0x0

    * PLL Reset
    *  PSU_DDR_PHY_DX8SLBPLLCR0_PLLRST                             0x0

    * PLL Power Down
    *  PSU_DDR_PHY_DX8SLBPLLCR0_PLLPD                              0x0

    * Reference Stop Mode
    *  PSU_DDR_PHY_DX8SLBPLLCR0_RSTOPM                             0x0

    * PLL Frequency Select
    *  PSU_DDR_PHY_DX8SLBPLLCR0_FRQSEL                             0x1

    * Relock Mode
    *  PSU_DDR_PHY_DX8SLBPLLCR0_RLOCKM                             0x0

    * Charge Pump Proportional Current Control
    *  PSU_DDR_PHY_DX8SLBPLLCR0_CPPC                               0x8

    * Charge Pump Integrating Current Control
    *  PSU_DDR_PHY_DX8SLBPLLCR0_CPIC                               0x0

    * Gear Shift
    *  PSU_DDR_PHY_DX8SLBPLLCR0_GSHIFT                             0x0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX8SLBPLLCR0_RESERVED_11_9                      0x0

    * Analog Test Enable (ATOEN)
    *  PSU_DDR_PHY_DX8SLBPLLCR0_ATOEN                              0x0

    * Analog Test Control
    *  PSU_DDR_PHY_DX8SLBPLLCR0_ATC                                0x0

    * Digital Test Control
    *  PSU_DDR_PHY_DX8SLBPLLCR0_DTC                                0x0

    * DAXT8 0-8 PLL Control Register 0
    * (OFFSET, MASK, VALUE)      (0XFD0817C4, 0xFFFFFFFFU ,0x01100000U)
    */
	PSU_Mask_Write(DDR_PHY_DX8SLBPLLCR0_OFFSET,
		0xFFFFFFFFU, 0x01100000U);
/*##################################################################### */

    /*
    * Register : DX8SLbDQSCTL @ 0XFD0817DC

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX8SLBDQSCTL_RESERVED_31_25                     0x0

    * Read Path Rise-to-Rise Mode
    *  PSU_DDR_PHY_DX8SLBDQSCTL_RRRMODE                            0x1

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX8SLBDQSCTL_RESERVED_23_22                     0x0

    * Write Path Rise-to-Rise Mode
    *  PSU_DDR_PHY_DX8SLBDQSCTL_WRRMODE                            0x1

    * DQS Gate Extension
    *  PSU_DDR_PHY_DX8SLBDQSCTL_DQSGX                              0x0

    * Low Power PLL Power Down
    *  PSU_DDR_PHY_DX8SLBDQSCTL_LPPLLPD                            0x1

    * Low Power I/O Power Down
    *  PSU_DDR_PHY_DX8SLBDQSCTL_LPIOPD                             0x1

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX8SLBDQSCTL_RESERVED_16_15                     0x0

    * QS Counter Enable
    *  PSU_DDR_PHY_DX8SLBDQSCTL_QSCNTEN                            0x1

    * Unused DQ I/O Mode
    *  PSU_DDR_PHY_DX8SLBDQSCTL_UDQIOM                             0x0

    * Reserved. Return zeroes on reads.
    *  PSU_DDR_PHY_DX8SLBDQSCTL_RESERVED_12_10                     0x0

    * Data Slew Rate
    *  PSU_DDR_PHY_DX8SLBDQSCTL_DXSR                               0x3

    * DQS# Resistor
    *  PSU_DDR_PHY_DX8SLBDQSCTL_DQSNRES                            0xc

    * DQS Resistor
    *  PSU_DDR_PHY_DX8SLBDQSCTL_DQSRES                             0x4

    * DATX8 0-8 DQS Control Register
    * (OFFSET, MASK, VALUE)      (0XFD0817DC, 0xFFFFFFFFU ,0x012643C4U)
    */
	PSU_Mask_Write(DDR_PHY_DX8SLBDQSCTL_OFFSET,
		0xFFFFFFFFU, 0x012643C4U);
/*##################################################################### */


	return 1;
}
unsigned long psu_ddr_qos_init_data(void)
{

	return 1;
}
unsigned long psu_mio_init_data(void)
{
    /*
    * MIO PROGRAMMING
    */
    /*
    * Register : MIO_PIN_0 @ 0XFF180000

    * Level 0 Mux Select 0= Level 1 Mux Output 1= qspi, Output, qspi_sclk_out-
    *  (QSPI Clock)
    *  PSU_IOU_SLCR_MIO_PIN_0_L0_SEL                               1

    * Level 1 Mux Select 0= Level 2 Mux Output 1= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_0_L1_SEL                               0

    * Level 2 Mux Select 0= Level 3 Mux Output 1= Not Used 2= test_scan, Input
    * , test_scan_in[0]- (Test Scan Port) = test_scan, Output, test_scan_out[0
    * ]- (Test Scan Port) 3= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_0_L2_SEL                               0

    * Level 3 Mux Select 0= gpio0, Input, gpio_0_pin_in[0]- (GPIO bank 0) 0= g
    * pio0, Output, gpio_0_pin_out[0]- (GPIO bank 0) 1= can1, Output, can1_phy
    * _tx- (Can TX signal) 2= i2c1, Input, i2c1_scl_input- (SCL signal) 2= i2c
    * 1, Output, i2c1_scl_out- (SCL signal) 3= pjtag, Input, pjtag_tck- (PJTAG
    *  TCK) 4= spi0, Input, spi0_sclk_in- (SPI Clock) 4= spi0, Output, spi0_sc
    * lk_out- (SPI Clock) 5= ttc3, Input, ttc3_clk_in- (TTC Clock) 6= ua1, Out
    * put, ua1_txd- (UART transmitter serial output) 7= trace, Output, trace_c
    * lk- (Trace Port Clock)
    *  PSU_IOU_SLCR_MIO_PIN_0_L3_SEL                               0

    * Configures MIO Pin 0 peripheral interface mapping. S
    * (OFFSET, MASK, VALUE)      (0XFF180000, 0x000000FEU ,0x00000002U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_0_OFFSET, 0x000000FEU, 0x00000002U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_1 @ 0XFF180004

    * Level 0 Mux Select 0= Level 1 Mux Output 1= qspi, Input, qspi_mi_mi1- (Q
    * SPI Databus) 1= qspi, Output, qspi_so_mo1- (QSPI Databus)
    *  PSU_IOU_SLCR_MIO_PIN_1_L0_SEL                               1

    * Level 1 Mux Select 0= Level 2 Mux Output 1= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_1_L1_SEL                               0

    * Level 2 Mux Select 0= Level 3 Mux Output 1= Not Used 2= test_scan, Input
    * , test_scan_in[1]- (Test Scan Port) = test_scan, Output, test_scan_out[1
    * ]- (Test Scan Port) 3= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_1_L2_SEL                               0

    * Level 3 Mux Select 0= gpio0, Input, gpio_0_pin_in[1]- (GPIO bank 0) 0= g
    * pio0, Output, gpio_0_pin_out[1]- (GPIO bank 0) 1= can1, Input, can1_phy_
    * rx- (Can RX signal) 2= i2c1, Input, i2c1_sda_input- (SDA signal) 2= i2c1
    * , Output, i2c1_sda_out- (SDA signal) 3= pjtag, Input, pjtag_tdi- (PJTAG
    * TDI) 4= spi0, Output, spi0_n_ss_out[2]- (SPI Master Selects) 5= ttc3, Ou
    * tput, ttc3_wave_out- (TTC Waveform Clock) 6= ua1, Input, ua1_rxd- (UART
    * receiver serial input) 7= trace, Output, trace_ctl- (Trace Port Control
    * Signal)
    *  PSU_IOU_SLCR_MIO_PIN_1_L3_SEL                               0

    * Configures MIO Pin 1 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF180004, 0x000000FEU ,0x00000002U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_1_OFFSET, 0x000000FEU, 0x00000002U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_2 @ 0XFF180008

    * Level 0 Mux Select 0= Level 1 Mux Output 1= qspi, Input, qspi_mi2- (QSPI
    *  Databus) 1= qspi, Output, qspi_mo2- (QSPI Databus)
    *  PSU_IOU_SLCR_MIO_PIN_2_L0_SEL                               1

    * Level 1 Mux Select 0= Level 2 Mux Output 1= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_2_L1_SEL                               0

    * Level 2 Mux Select 0= Level 3 Mux Output 1= Not Used 2= test_scan, Input
    * , test_scan_in[2]- (Test Scan Port) = test_scan, Output, test_scan_out[2
    * ]- (Test Scan Port) 3= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_2_L2_SEL                               0

    * Level 3 Mux Select 0= gpio0, Input, gpio_0_pin_in[2]- (GPIO bank 0) 0= g
    * pio0, Output, gpio_0_pin_out[2]- (GPIO bank 0) 1= can0, Input, can0_phy_
    * rx- (Can RX signal) 2= i2c0, Input, i2c0_scl_input- (SCL signal) 2= i2c0
    * , Output, i2c0_scl_out- (SCL signal) 3= pjtag, Output, pjtag_tdo- (PJTAG
    *  TDO) 4= spi0, Output, spi0_n_ss_out[1]- (SPI Master Selects) 5= ttc2, I
    * nput, ttc2_clk_in- (TTC Clock) 6= ua0, Input, ua0_rxd- (UART receiver se
    * rial input) 7= trace, Output, tracedq[0]- (Trace Port Databus)
    *  PSU_IOU_SLCR_MIO_PIN_2_L3_SEL                               0

    * Configures MIO Pin 2 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF180008, 0x000000FEU ,0x00000002U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_2_OFFSET, 0x000000FEU, 0x00000002U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_3 @ 0XFF18000C

    * Level 0 Mux Select 0= Level 1 Mux Output 1= qspi, Input, qspi_mi3- (QSPI
    *  Databus) 1= qspi, Output, qspi_mo3- (QSPI Databus)
    *  PSU_IOU_SLCR_MIO_PIN_3_L0_SEL                               1

    * Level 1 Mux Select 0= Level 2 Mux Output 1= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_3_L1_SEL                               0

    * Level 2 Mux Select 0= Level 3 Mux Output 1= Not Used 2= test_scan, Input
    * , test_scan_in[3]- (Test Scan Port) = test_scan, Output, test_scan_out[3
    * ]- (Test Scan Port) 3= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_3_L2_SEL                               0

    * Level 3 Mux Select 0= gpio0, Input, gpio_0_pin_in[3]- (GPIO bank 0) 0= g
    * pio0, Output, gpio_0_pin_out[3]- (GPIO bank 0) 1= can0, Output, can0_phy
    * _tx- (Can TX signal) 2= i2c0, Input, i2c0_sda_input- (SDA signal) 2= i2c
    * 0, Output, i2c0_sda_out- (SDA signal) 3= pjtag, Input, pjtag_tms- (PJTAG
    *  TMS) 4= spi0, Input, spi0_n_ss_in- (SPI Master Selects) 4= spi0, Output
    * , spi0_n_ss_out[0]- (SPI Master Selects) 5= ttc2, Output, ttc2_wave_out-
    *  (TTC Waveform Clock) 6= ua0, Output, ua0_txd- (UART transmitter serial
    * output) 7= trace, Output, tracedq[1]- (Trace Port Databus)
    *  PSU_IOU_SLCR_MIO_PIN_3_L3_SEL                               0

    * Configures MIO Pin 3 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF18000C, 0x000000FEU ,0x00000002U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_3_OFFSET, 0x000000FEU, 0x00000002U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_4 @ 0XFF180010

    * Level 0 Mux Select 0= Level 1 Mux Output 1= qspi, Output, qspi_mo_mo0- (
    * QSPI Databus) 1= qspi, Input, qspi_si_mi0- (QSPI Databus)
    *  PSU_IOU_SLCR_MIO_PIN_4_L0_SEL                               1

    * Level 1 Mux Select 0= Level 2 Mux Output 1= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_4_L1_SEL                               0

    * Level 2 Mux Select 0= Level 3 Mux Output 1= Not Used 2= test_scan, Input
    * , test_scan_in[4]- (Test Scan Port) = test_scan, Output, test_scan_out[4
    * ]- (Test Scan Port) 3= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_4_L2_SEL                               0

    * Level 3 Mux Select 0= gpio0, Input, gpio_0_pin_in[4]- (GPIO bank 0) 0= g
    * pio0, Output, gpio_0_pin_out[4]- (GPIO bank 0) 1= can1, Output, can1_phy
    * _tx- (Can TX signal) 2= i2c1, Input, i2c1_scl_input- (SCL signal) 2= i2c
    * 1, Output, i2c1_scl_out- (SCL signal) 3= swdt1, Input, swdt1_clk_in- (Wa
    * tch Dog Timer Input clock) 4= spi0, Input, spi0_mi- (MISO signal) 4= spi
    * 0, Output, spi0_so- (MISO signal) 5= ttc1, Input, ttc1_clk_in- (TTC Cloc
    * k) 6= ua1, Output, ua1_txd- (UART transmitter serial output) 7= trace, O
    * utput, tracedq[2]- (Trace Port Databus)
    *  PSU_IOU_SLCR_MIO_PIN_4_L3_SEL                               0

    * Configures MIO Pin 4 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF180010, 0x000000FEU ,0x00000002U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_4_OFFSET, 0x000000FEU, 0x00000002U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_5 @ 0XFF180014

    * Level 0 Mux Select 0= Level 1 Mux Output 1= qspi, Output, qspi_n_ss_out-
    *  (QSPI Slave Select)
    *  PSU_IOU_SLCR_MIO_PIN_5_L0_SEL                               1

    * Level 1 Mux Select 0= Level 2 Mux Output 1= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_5_L1_SEL                               0

    * Level 2 Mux Select 0= Level 3 Mux Output 1= Not Used 2= test_scan, Input
    * , test_scan_in[5]- (Test Scan Port) = test_scan, Output, test_scan_out[5
    * ]- (Test Scan Port) 3= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_5_L2_SEL                               0

    * Level 3 Mux Select 0= gpio0, Input, gpio_0_pin_in[5]- (GPIO bank 0) 0= g
    * pio0, Output, gpio_0_pin_out[5]- (GPIO bank 0) 1= can1, Input, can1_phy_
    * rx- (Can RX signal) 2= i2c1, Input, i2c1_sda_input- (SDA signal) 2= i2c1
    * , Output, i2c1_sda_out- (SDA signal) 3= swdt1, Output, swdt1_rst_out- (W
    * atch Dog Timer Output clock) 4= spi0, Output, spi0_mo- (MOSI signal) 4=
    * spi0, Input, spi0_si- (MOSI signal) 5= ttc1, Output, ttc1_wave_out- (TTC
    *  Waveform Clock) 6= ua1, Input, ua1_rxd- (UART receiver serial input) 7=
    *  trace, Output, tracedq[3]- (Trace Port Databus)
    *  PSU_IOU_SLCR_MIO_PIN_5_L3_SEL                               0

    * Configures MIO Pin 5 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF180014, 0x000000FEU ,0x00000002U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_5_OFFSET, 0x000000FEU, 0x00000002U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_6 @ 0XFF180018

    * Level 0 Mux Select 0= Level 1 Mux Output 1= qspi, Output, qspi_clk_for_l
    * pbk- (QSPI Clock to be fed-back)
    *  PSU_IOU_SLCR_MIO_PIN_6_L0_SEL                               1

    * Level 1 Mux Select 0= Level 2 Mux Output 1= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_6_L1_SEL                               0

    * Level 2 Mux Select 0= Level 3 Mux Output 1= Not Used 2= test_scan, Input
    * , test_scan_in[6]- (Test Scan Port) = test_scan, Output, test_scan_out[6
    * ]- (Test Scan Port) 3= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_6_L2_SEL                               0

    * Level 3 Mux Select 0= gpio0, Input, gpio_0_pin_in[6]- (GPIO bank 0) 0= g
    * pio0, Output, gpio_0_pin_out[6]- (GPIO bank 0) 1= can0, Input, can0_phy_
    * rx- (Can RX signal) 2= i2c0, Input, i2c0_scl_input- (SCL signal) 2= i2c0
    * , Output, i2c0_scl_out- (SCL signal) 3= swdt0, Input, swdt0_clk_in- (Wat
    * ch Dog Timer Input clock) 4= spi1, Input, spi1_sclk_in- (SPI Clock) 4= s
    * pi1, Output, spi1_sclk_out- (SPI Clock) 5= ttc0, Input, ttc0_clk_in- (TT
    * C Clock) 6= ua0, Input, ua0_rxd- (UART receiver serial input) 7= trace,
    * Output, tracedq[4]- (Trace Port Databus)
    *  PSU_IOU_SLCR_MIO_PIN_6_L3_SEL                               0

    * Configures MIO Pin 6 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF180018, 0x000000FEU ,0x00000002U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_6_OFFSET, 0x000000FEU, 0x00000002U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_7 @ 0XFF18001C

    * Level 0 Mux Select 0= Level 1 Mux Output 1= qspi, Output, qspi_n_ss_out_
    * upper- (QSPI Slave Select upper)
    *  PSU_IOU_SLCR_MIO_PIN_7_L0_SEL                               1

    * Level 1 Mux Select 0= Level 2 Mux Output 1= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_7_L1_SEL                               0

    * Level 2 Mux Select 0= Level 3 Mux Output 1= Not Used 2= test_scan, Input
    * , test_scan_in[7]- (Test Scan Port) = test_scan, Output, test_scan_out[7
    * ]- (Test Scan Port) 3= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_7_L2_SEL                               0

    * Level 3 Mux Select 0= gpio0, Input, gpio_0_pin_in[7]- (GPIO bank 0) 0= g
    * pio0, Output, gpio_0_pin_out[7]- (GPIO bank 0) 1= can0, Output, can0_phy
    * _tx- (Can TX signal) 2= i2c0, Input, i2c0_sda_input- (SDA signal) 2= i2c
    * 0, Output, i2c0_sda_out- (SDA signal) 3= swdt0, Output, swdt0_rst_out- (
    * Watch Dog Timer Output clock) 4= spi1, Output, spi1_n_ss_out[2]- (SPI Ma
    * ster Selects) 5= ttc0, Output, ttc0_wave_out- (TTC Waveform Clock) 6= ua
    * 0, Output, ua0_txd- (UART transmitter serial output) 7= trace, Output, t
    * racedq[5]- (Trace Port Databus)
    *  PSU_IOU_SLCR_MIO_PIN_7_L3_SEL                               0

    * Configures MIO Pin 7 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF18001C, 0x000000FEU ,0x00000002U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_7_OFFSET, 0x000000FEU, 0x00000002U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_8 @ 0XFF180020

    * Level 0 Mux Select 0= Level 1 Mux Output 1= qspi, Input, qspi_mi_upper[0
    * ]- (QSPI Upper Databus) 1= qspi, Output, qspi_mo_upper[0]- (QSPI Upper D
    * atabus)
    *  PSU_IOU_SLCR_MIO_PIN_8_L0_SEL                               1

    * Level 1 Mux Select 0= Level 2 Mux Output 1= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_8_L1_SEL                               0

    * Level 2 Mux Select 0= Level 3 Mux Output 1= Not Used 2= test_scan, Input
    * , test_scan_in[8]- (Test Scan Port) = test_scan, Output, test_scan_out[8
    * ]- (Test Scan Port) 3= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_8_L2_SEL                               0

    * Level 3 Mux Select 0= gpio0, Input, gpio_0_pin_in[8]- (GPIO bank 0) 0= g
    * pio0, Output, gpio_0_pin_out[8]- (GPIO bank 0) 1= can1, Output, can1_phy
    * _tx- (Can TX signal) 2= i2c1, Input, i2c1_scl_input- (SCL signal) 2= i2c
    * 1, Output, i2c1_scl_out- (SCL signal) 3= swdt1, Input, swdt1_clk_in- (Wa
    * tch Dog Timer Input clock) 4= spi1, Output, spi1_n_ss_out[1]- (SPI Maste
    * r Selects) 5= ttc3, Input, ttc3_clk_in- (TTC Clock) 6= ua1, Output, ua1_
    * txd- (UART transmitter serial output) 7= trace, Output, tracedq[6]- (Tra
    * ce Port Databus)
    *  PSU_IOU_SLCR_MIO_PIN_8_L3_SEL                               0

    * Configures MIO Pin 8 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF180020, 0x000000FEU ,0x00000002U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_8_OFFSET, 0x000000FEU, 0x00000002U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_9 @ 0XFF180024

    * Level 0 Mux Select 0= Level 1 Mux Output 1= qspi, Input, qspi_mi_upper[1
    * ]- (QSPI Upper Databus) 1= qspi, Output, qspi_mo_upper[1]- (QSPI Upper D
    * atabus)
    *  PSU_IOU_SLCR_MIO_PIN_9_L0_SEL                               1

    * Level 1 Mux Select 0= Level 2 Mux Output 1= nand, Output, nfc_ce[1]- (NA
    * ND chip enable)
    *  PSU_IOU_SLCR_MIO_PIN_9_L1_SEL                               0

    * Level 2 Mux Select 0= Level 3 Mux Output 1= Not Used 2= test_scan, Input
    * , test_scan_in[9]- (Test Scan Port) = test_scan, Output, test_scan_out[9
    * ]- (Test Scan Port) 3= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_9_L2_SEL                               0

    * Level 3 Mux Select 0= gpio0, Input, gpio_0_pin_in[9]- (GPIO bank 0) 0= g
    * pio0, Output, gpio_0_pin_out[9]- (GPIO bank 0) 1= can1, Input, can1_phy_
    * rx- (Can RX signal) 2= i2c1, Input, i2c1_sda_input- (SDA signal) 2= i2c1
    * , Output, i2c1_sda_out- (SDA signal) 3= swdt1, Output, swdt1_rst_out- (W
    * atch Dog Timer Output clock) 4= spi1, Input, spi1_n_ss_in- (SPI Master S
    * elects) 4= spi1, Output, spi1_n_ss_out[0]- (SPI Master Selects) 5= ttc3,
    *  Output, ttc3_wave_out- (TTC Waveform Clock) 6= ua1, Input, ua1_rxd- (UA
    * RT receiver serial input) 7= trace, Output, tracedq[7]- (Trace Port Data
    * bus)
    *  PSU_IOU_SLCR_MIO_PIN_9_L3_SEL                               0

    * Configures MIO Pin 9 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF180024, 0x000000FEU ,0x00000002U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_9_OFFSET, 0x000000FEU, 0x00000002U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_10 @ 0XFF180028

    * Level 0 Mux Select 0= Level 1 Mux Output 1= qspi, Input, qspi_mi_upper[2
    * ]- (QSPI Upper Databus) 1= qspi, Output, qspi_mo_upper[2]- (QSPI Upper D
    * atabus)
    *  PSU_IOU_SLCR_MIO_PIN_10_L0_SEL                              1

    * Level 1 Mux Select 0= Level 2 Mux Output 1= nand, Input, nfc_rb_n[0]- (N
    * AND Ready/Busy)
    *  PSU_IOU_SLCR_MIO_PIN_10_L1_SEL                              0

    * Level 2 Mux Select 0= Level 3 Mux Output 1= Not Used 2= test_scan, Input
    * , test_scan_in[10]- (Test Scan Port) = test_scan, Output, test_scan_out[
    * 10]- (Test Scan Port) 3= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_10_L2_SEL                              0

    * Level 3 Mux Select 0= gpio0, Input, gpio_0_pin_in[10]- (GPIO bank 0) 0=
    * gpio0, Output, gpio_0_pin_out[10]- (GPIO bank 0) 1= can0, Input, can0_ph
    * y_rx- (Can RX signal) 2= i2c0, Input, i2c0_scl_input- (SCL signal) 2= i2
    * c0, Output, i2c0_scl_out- (SCL signal) 3= swdt0, Input, swdt0_clk_in- (W
    * atch Dog Timer Input clock) 4= spi1, Input, spi1_mi- (MISO signal) 4= sp
    * i1, Output, spi1_so- (MISO signal) 5= ttc2, Input, ttc2_clk_in- (TTC Clo
    * ck) 6= ua0, Input, ua0_rxd- (UART receiver serial input) 7= trace, Outpu
    * t, tracedq[8]- (Trace Port Databus)
    *  PSU_IOU_SLCR_MIO_PIN_10_L3_SEL                              0

    * Configures MIO Pin 10 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF180028, 0x000000FEU ,0x00000002U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_10_OFFSET, 0x000000FEU, 0x00000002U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_11 @ 0XFF18002C

    * Level 0 Mux Select 0= Level 1 Mux Output 1= qspi, Input, qspi_mi_upper[3
    * ]- (QSPI Upper Databus) 1= qspi, Output, qspi_mo_upper[3]- (QSPI Upper D
    * atabus)
    *  PSU_IOU_SLCR_MIO_PIN_11_L0_SEL                              1

    * Level 1 Mux Select 0= Level 2 Mux Output 1= nand, Input, nfc_rb_n[1]- (N
    * AND Ready/Busy)
    *  PSU_IOU_SLCR_MIO_PIN_11_L1_SEL                              0

    * Level 2 Mux Select 0= Level 3 Mux Output 1= Not Used 2= test_scan, Input
    * , test_scan_in[11]- (Test Scan Port) = test_scan, Output, test_scan_out[
    * 11]- (Test Scan Port) 3= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_11_L2_SEL                              0

    * Level 3 Mux Select 0= gpio0, Input, gpio_0_pin_in[11]- (GPIO bank 0) 0=
    * gpio0, Output, gpio_0_pin_out[11]- (GPIO bank 0) 1= can0, Output, can0_p
    * hy_tx- (Can TX signal) 2= i2c0, Input, i2c0_sda_input- (SDA signal) 2= i
    * 2c0, Output, i2c0_sda_out- (SDA signal) 3= swdt0, Output, swdt0_rst_out-
    *  (Watch Dog Timer Output clock) 4= spi1, Output, spi1_mo- (MOSI signal)
    * 4= spi1, Input, spi1_si- (MOSI signal) 5= ttc2, Output, ttc2_wave_out- (
    * TTC Waveform Clock) 6= ua0, Output, ua0_txd- (UART transmitter serial ou
    * tput) 7= trace, Output, tracedq[9]- (Trace Port Databus)
    *  PSU_IOU_SLCR_MIO_PIN_11_L3_SEL                              0

    * Configures MIO Pin 11 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF18002C, 0x000000FEU ,0x00000002U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_11_OFFSET, 0x000000FEU, 0x00000002U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_12 @ 0XFF180030

    * Level 0 Mux Select 0= Level 1 Mux Output 1= qspi, Output, qspi_sclk_out_
    * upper- (QSPI Upper Clock)
    *  PSU_IOU_SLCR_MIO_PIN_12_L0_SEL                              1

    * Level 1 Mux Select 0= Level 2 Mux Output 1= nand, Input, nfc_dqs_in- (NA
    * ND Strobe) 1= nand, Output, nfc_dqs_out- (NAND Strobe)
    *  PSU_IOU_SLCR_MIO_PIN_12_L1_SEL                              0

    * Level 2 Mux Select 0= Level 3 Mux Output 1= Not Used 2= test_scan, Input
    * , test_scan_in[12]- (Test Scan Port) = test_scan, Output, test_scan_out[
    * 12]- (Test Scan Port) 3= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_12_L2_SEL                              0

    * Level 3 Mux Select 0= gpio0, Input, gpio_0_pin_in[12]- (GPIO bank 0) 0=
    * gpio0, Output, gpio_0_pin_out[12]- (GPIO bank 0) 1= can1, Output, can1_p
    * hy_tx- (Can TX signal) 2= i2c1, Input, i2c1_scl_input- (SCL signal) 2= i
    * 2c1, Output, i2c1_scl_out- (SCL signal) 3= pjtag, Input, pjtag_tck- (PJT
    * AG TCK) 4= spi0, Input, spi0_sclk_in- (SPI Clock) 4= spi0, Output, spi0_
    * sclk_out- (SPI Clock) 5= ttc1, Input, ttc1_clk_in- (TTC Clock) 6= ua1, O
    * utput, ua1_txd- (UART transmitter serial output) 7= trace, Output, trace
    * dq[10]- (Trace Port Databus)
    *  PSU_IOU_SLCR_MIO_PIN_12_L3_SEL                              0

    * Configures MIO Pin 12 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF180030, 0x000000FEU ,0x00000002U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_12_OFFSET, 0x000000FEU, 0x00000002U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_13 @ 0XFF180034

    * Level 0 Mux Select 0= Level 1 Mux Output 1= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_13_L0_SEL                              0

    * Level 1 Mux Select 0= Level 2 Mux Output 1= nand, Output, nfc_ce[0]- (NA
    * ND chip enable)
    *  PSU_IOU_SLCR_MIO_PIN_13_L1_SEL                              0

    * Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Input, sd0_data_in[0]-
    * (8-bit Data bus) = sd0, Output, sdio0_data_out[0]- (8-bit Data bus) 2= t
    * est_scan, Input, test_scan_in[13]- (Test Scan Port) = test_scan, Output,
    *  test_scan_out[13]- (Test Scan Port) 3= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_13_L2_SEL                              0

    * Level 3 Mux Select 0= gpio0, Input, gpio_0_pin_in[13]- (GPIO bank 0) 0=
    * gpio0, Output, gpio_0_pin_out[13]- (GPIO bank 0) 1= can1, Input, can1_ph
    * y_rx- (Can RX signal) 2= i2c1, Input, i2c1_sda_input- (SDA signal) 2= i2
    * c1, Output, i2c1_sda_out- (SDA signal) 3= pjtag, Input, pjtag_tdi- (PJTA
    * G TDI) 4= spi0, Output, spi0_n_ss_out[2]- (SPI Master Selects) 5= ttc1,
    * Output, ttc1_wave_out- (TTC Waveform Clock) 6= ua1, Input, ua1_rxd- (UAR
    * T receiver serial input) 7= trace, Output, tracedq[11]- (Trace Port Data
    * bus)
    *  PSU_IOU_SLCR_MIO_PIN_13_L3_SEL                              0

    * Configures MIO Pin 13 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF180034, 0x000000FEU ,0x00000000U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_13_OFFSET, 0x000000FEU, 0x00000000U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_14 @ 0XFF180038

    * Level 0 Mux Select 0= Level 1 Mux Output 1= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_14_L0_SEL                              0

    * Level 1 Mux Select 0= Level 2 Mux Output 1= nand, Output, nfc_cle- (NAND
    *  Command Latch Enable)
    *  PSU_IOU_SLCR_MIO_PIN_14_L1_SEL                              0

    * Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Input, sd0_data_in[1]-
    * (8-bit Data bus) = sd0, Output, sdio0_data_out[1]- (8-bit Data bus) 2= t
    * est_scan, Input, test_scan_in[14]- (Test Scan Port) = test_scan, Output,
    *  test_scan_out[14]- (Test Scan Port) 3= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_14_L2_SEL                              0

    * Level 3 Mux Select 0= gpio0, Input, gpio_0_pin_in[14]- (GPIO bank 0) 0=
    * gpio0, Output, gpio_0_pin_out[14]- (GPIO bank 0) 1= can0, Input, can0_ph
    * y_rx- (Can RX signal) 2= i2c0, Input, i2c0_scl_input- (SCL signal) 2= i2
    * c0, Output, i2c0_scl_out- (SCL signal) 3= pjtag, Output, pjtag_tdo- (PJT
    * AG TDO) 4= spi0, Output, spi0_n_ss_out[1]- (SPI Master Selects) 5= ttc0,
    *  Input, ttc0_clk_in- (TTC Clock) 6= ua0, Input, ua0_rxd- (UART receiver
    * serial input) 7= trace, Output, tracedq[12]- (Trace Port Databus)
    *  PSU_IOU_SLCR_MIO_PIN_14_L3_SEL                              2

    * Configures MIO Pin 14 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF180038, 0x000000FEU ,0x00000040U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_14_OFFSET, 0x000000FEU, 0x00000040U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_15 @ 0XFF18003C

    * Level 0 Mux Select 0= Level 1 Mux Output 1= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_15_L0_SEL                              0

    * Level 1 Mux Select 0= Level 2 Mux Output 1= nand, Output, nfc_ale- (NAND
    *  Address Latch Enable)
    *  PSU_IOU_SLCR_MIO_PIN_15_L1_SEL                              0

    * Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Input, sd0_data_in[2]-
    * (8-bit Data bus) = sd0, Output, sdio0_data_out[2]- (8-bit Data bus) 2= t
    * est_scan, Input, test_scan_in[15]- (Test Scan Port) = test_scan, Output,
    *  test_scan_out[15]- (Test Scan Port) 3= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_15_L2_SEL                              0

    * Level 3 Mux Select 0= gpio0, Input, gpio_0_pin_in[15]- (GPIO bank 0) 0=
    * gpio0, Output, gpio_0_pin_out[15]- (GPIO bank 0) 1= can0, Output, can0_p
    * hy_tx- (Can TX signal) 2= i2c0, Input, i2c0_sda_input- (SDA signal) 2= i
    * 2c0, Output, i2c0_sda_out- (SDA signal) 3= pjtag, Input, pjtag_tms- (PJT
    * AG TMS) 4= spi0, Input, spi0_n_ss_in- (SPI Master Selects) 4= spi0, Outp
    * ut, spi0_n_ss_out[0]- (SPI Master Selects) 5= ttc0, Output, ttc0_wave_ou
    * t- (TTC Waveform Clock) 6= ua0, Output, ua0_txd- (UART transmitter seria
    * l output) 7= trace, Output, tracedq[13]- (Trace Port Databus)
    *  PSU_IOU_SLCR_MIO_PIN_15_L3_SEL                              2

    * Configures MIO Pin 15 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF18003C, 0x000000FEU ,0x00000040U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_15_OFFSET, 0x000000FEU, 0x00000040U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_16 @ 0XFF180040

    * Level 0 Mux Select 0= Level 1 Mux Output 1= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_16_L0_SEL                              0

    * Level 1 Mux Select 0= Level 2 Mux Output 1= nand, Input, nfc_dq_in[0]- (
    * NAND Data Bus) 1= nand, Output, nfc_dq_out[0]- (NAND Data Bus)
    *  PSU_IOU_SLCR_MIO_PIN_16_L1_SEL                              0

    * Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Input, sd0_data_in[3]-
    * (8-bit Data bus) = sd0, Output, sdio0_data_out[3]- (8-bit Data bus) 2= t
    * est_scan, Input, test_scan_in[16]- (Test Scan Port) = test_scan, Output,
    *  test_scan_out[16]- (Test Scan Port) 3= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_16_L2_SEL                              0

    * Level 3 Mux Select 0= gpio0, Input, gpio_0_pin_in[16]- (GPIO bank 0) 0=
    * gpio0, Output, gpio_0_pin_out[16]- (GPIO bank 0) 1= can1, Output, can1_p
    * hy_tx- (Can TX signal) 2= i2c1, Input, i2c1_scl_input- (SCL signal) 2= i
    * 2c1, Output, i2c1_scl_out- (SCL signal) 3= swdt1, Input, swdt1_clk_in- (
    * Watch Dog Timer Input clock) 4= spi0, Input, spi0_mi- (MISO signal) 4= s
    * pi0, Output, spi0_so- (MISO signal) 5= ttc3, Input, ttc3_clk_in- (TTC Cl
    * ock) 6= ua1, Output, ua1_txd- (UART transmitter serial output) 7= trace,
    *  Output, tracedq[14]- (Trace Port Databus)
    *  PSU_IOU_SLCR_MIO_PIN_16_L3_SEL                              2

    * Configures MIO Pin 16 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF180040, 0x000000FEU ,0x00000040U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_16_OFFSET, 0x000000FEU, 0x00000040U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_17 @ 0XFF180044

    * Level 0 Mux Select 0= Level 1 Mux Output 1= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_17_L0_SEL                              0

    * Level 1 Mux Select 0= Level 2 Mux Output 1= nand, Input, nfc_dq_in[1]- (
    * NAND Data Bus) 1= nand, Output, nfc_dq_out[1]- (NAND Data Bus)
    *  PSU_IOU_SLCR_MIO_PIN_17_L1_SEL                              0

    * Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Input, sd0_data_in[4]-
    * (8-bit Data bus) = sd0, Output, sdio0_data_out[4]- (8-bit Data bus) 2= t
    * est_scan, Input, test_scan_in[17]- (Test Scan Port) = test_scan, Output,
    *  test_scan_out[17]- (Test Scan Port) 3= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_17_L2_SEL                              0

    * Level 3 Mux Select 0= gpio0, Input, gpio_0_pin_in[17]- (GPIO bank 0) 0=
    * gpio0, Output, gpio_0_pin_out[17]- (GPIO bank 0) 1= can1, Input, can1_ph
    * y_rx- (Can RX signal) 2= i2c1, Input, i2c1_sda_input- (SDA signal) 2= i2
    * c1, Output, i2c1_sda_out- (SDA signal) 3= swdt1, Output, swdt1_rst_out-
    * (Watch Dog Timer Output clock) 4= spi0, Output, spi0_mo- (MOSI signal) 4
    * = spi0, Input, spi0_si- (MOSI signal) 5= ttc3, Output, ttc3_wave_out- (T
    * TC Waveform Clock) 6= ua1, Input, ua1_rxd- (UART receiver serial input)
    * 7= trace, Output, tracedq[15]- (Trace Port Databus)
    *  PSU_IOU_SLCR_MIO_PIN_17_L3_SEL                              2

    * Configures MIO Pin 17 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF180044, 0x000000FEU ,0x00000040U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_17_OFFSET, 0x000000FEU, 0x00000040U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_18 @ 0XFF180048

    * Level 0 Mux Select 0= Level 1 Mux Output 1= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_18_L0_SEL                              0

    * Level 1 Mux Select 0= Level 2 Mux Output 1= nand, Input, nfc_dq_in[2]- (
    * NAND Data Bus) 1= nand, Output, nfc_dq_out[2]- (NAND Data Bus)
    *  PSU_IOU_SLCR_MIO_PIN_18_L1_SEL                              0

    * Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Input, sd0_data_in[5]-
    * (8-bit Data bus) = sd0, Output, sdio0_data_out[5]- (8-bit Data bus) 2= t
    * est_scan, Input, test_scan_in[18]- (Test Scan Port) = test_scan, Output,
    *  test_scan_out[18]- (Test Scan Port) 3= csu, Input, csu_ext_tamper- (CSU
    *  Ext Tamper)
    *  PSU_IOU_SLCR_MIO_PIN_18_L2_SEL                              0

    * Level 3 Mux Select 0= gpio0, Input, gpio_0_pin_in[18]- (GPIO bank 0) 0=
    * gpio0, Output, gpio_0_pin_out[18]- (GPIO bank 0) 1= can0, Input, can0_ph
    * y_rx- (Can RX signal) 2= i2c0, Input, i2c0_scl_input- (SCL signal) 2= i2
    * c0, Output, i2c0_scl_out- (SCL signal) 3= swdt0, Input, swdt0_clk_in- (W
    * atch Dog Timer Input clock) 4= spi1, Input, spi1_mi- (MISO signal) 4= sp
    * i1, Output, spi1_so- (MISO signal) 5= ttc2, Input, ttc2_clk_in- (TTC Clo
    * ck) 6= ua0, Input, ua0_rxd- (UART receiver serial input) 7= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_18_L3_SEL                              6

    * Configures MIO Pin 18 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF180048, 0x000000FEU ,0x000000C0U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_18_OFFSET, 0x000000FEU, 0x000000C0U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_19 @ 0XFF18004C

    * Level 0 Mux Select 0= Level 1 Mux Output 1= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_19_L0_SEL                              0

    * Level 1 Mux Select 0= Level 2 Mux Output 1= nand, Input, nfc_dq_in[3]- (
    * NAND Data Bus) 1= nand, Output, nfc_dq_out[3]- (NAND Data Bus)
    *  PSU_IOU_SLCR_MIO_PIN_19_L1_SEL                              0

    * Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Input, sd0_data_in[6]-
    * (8-bit Data bus) = sd0, Output, sdio0_data_out[6]- (8-bit Data bus) 2= t
    * est_scan, Input, test_scan_in[19]- (Test Scan Port) = test_scan, Output,
    *  test_scan_out[19]- (Test Scan Port) 3= csu, Input, csu_ext_tamper- (CSU
    *  Ext Tamper)
    *  PSU_IOU_SLCR_MIO_PIN_19_L2_SEL                              0

    * Level 3 Mux Select 0= gpio0, Input, gpio_0_pin_in[19]- (GPIO bank 0) 0=
    * gpio0, Output, gpio_0_pin_out[19]- (GPIO bank 0) 1= can0, Output, can0_p
    * hy_tx- (Can TX signal) 2= i2c0, Input, i2c0_sda_input- (SDA signal) 2= i
    * 2c0, Output, i2c0_sda_out- (SDA signal) 3= swdt0, Output, swdt0_rst_out-
    *  (Watch Dog Timer Output clock) 4= spi1, Output, spi1_n_ss_out[2]- (SPI
    * Master Selects) 5= ttc2, Output, ttc2_wave_out- (TTC Waveform Clock) 6=
    * ua0, Output, ua0_txd- (UART transmitter serial output) 7= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_19_L3_SEL                              6

    * Configures MIO Pin 19 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF18004C, 0x000000FEU ,0x000000C0U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_19_OFFSET, 0x000000FEU, 0x000000C0U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_20 @ 0XFF180050

    * Level 0 Mux Select 0= Level 1 Mux Output 1= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_20_L0_SEL                              0

    * Level 1 Mux Select 0= Level 2 Mux Output 1= nand, Input, nfc_dq_in[4]- (
    * NAND Data Bus) 1= nand, Output, nfc_dq_out[4]- (NAND Data Bus)
    *  PSU_IOU_SLCR_MIO_PIN_20_L1_SEL                              0

    * Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Input, sd0_data_in[7]-
    * (8-bit Data bus) = sd0, Output, sdio0_data_out[7]- (8-bit Data bus) 2= t
    * est_scan, Input, test_scan_in[20]- (Test Scan Port) = test_scan, Output,
    *  test_scan_out[20]- (Test Scan Port) 3= csu, Input, csu_ext_tamper- (CSU
    *  Ext Tamper)
    *  PSU_IOU_SLCR_MIO_PIN_20_L2_SEL                              0

    * Level 3 Mux Select 0= gpio0, Input, gpio_0_pin_in[20]- (GPIO bank 0) 0=
    * gpio0, Output, gpio_0_pin_out[20]- (GPIO bank 0) 1= can1, Output, can1_p
    * hy_tx- (Can TX signal) 2= i2c1, Input, i2c1_scl_input- (SCL signal) 2= i
    * 2c1, Output, i2c1_scl_out- (SCL signal) 3= swdt1, Input, swdt1_clk_in- (
    * Watch Dog Timer Input clock) 4= spi1, Output, spi1_n_ss_out[1]- (SPI Mas
    * ter Selects) 5= ttc1, Input, ttc1_clk_in- (TTC Clock) 6= ua1, Output, ua
    * 1_txd- (UART transmitter serial output) 7= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_20_L3_SEL                              6

    * Configures MIO Pin 20 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF180050, 0x000000FEU ,0x000000C0U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_20_OFFSET, 0x000000FEU, 0x000000C0U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_21 @ 0XFF180054

    * Level 0 Mux Select 0= Level 1 Mux Output 1= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_21_L0_SEL                              0

    * Level 1 Mux Select 0= Level 2 Mux Output 1= nand, Input, nfc_dq_in[5]- (
    * NAND Data Bus) 1= nand, Output, nfc_dq_out[5]- (NAND Data Bus)
    *  PSU_IOU_SLCR_MIO_PIN_21_L1_SEL                              0

    * Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Input, sd0_cmd_in- (Com
    * mand Indicator) = sd0, Output, sdio0_cmd_out- (Command Indicator) 2= tes
    * t_scan, Input, test_scan_in[21]- (Test Scan Port) = test_scan, Output, t
    * est_scan_out[21]- (Test Scan Port) 3= csu, Input, csu_ext_tamper- (CSU E
    * xt Tamper)
    *  PSU_IOU_SLCR_MIO_PIN_21_L2_SEL                              0

    * Level 3 Mux Select 0= gpio0, Input, gpio_0_pin_in[21]- (GPIO bank 0) 0=
    * gpio0, Output, gpio_0_pin_out[21]- (GPIO bank 0) 1= can1, Input, can1_ph
    * y_rx- (Can RX signal) 2= i2c1, Input, i2c1_sda_input- (SDA signal) 2= i2
    * c1, Output, i2c1_sda_out- (SDA signal) 3= swdt1, Output, swdt1_rst_out-
    * (Watch Dog Timer Output clock) 4= spi1, Input, spi1_n_ss_in- (SPI Master
    *  Selects) 4= spi1, Output, spi1_n_ss_out[0]- (SPI Master Selects) 5= ttc
    * 1, Output, ttc1_wave_out- (TTC Waveform Clock) 6= ua1, Input, ua1_rxd- (
    * UART receiver serial input) 7= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_21_L3_SEL                              6

    * Configures MIO Pin 21 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF180054, 0x000000FEU ,0x000000C0U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_21_OFFSET, 0x000000FEU, 0x000000C0U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_22 @ 0XFF180058

    * Level 0 Mux Select 0= Level 1 Mux Output 1= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_22_L0_SEL                              0

    * Level 1 Mux Select 0= Level 2 Mux Output 1= nand, Output, nfc_we_b- (NAN
    * D Write Enable)
    *  PSU_IOU_SLCR_MIO_PIN_22_L1_SEL                              0

    * Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Output, sdio0_clk_out-
    * (SDSDIO clock) 2= test_scan, Input, test_scan_in[22]- (Test Scan Port) =
    *  test_scan, Output, test_scan_out[22]- (Test Scan Port) 3= csu, Input, c
    * su_ext_tamper- (CSU Ext Tamper)
    *  PSU_IOU_SLCR_MIO_PIN_22_L2_SEL                              0

    * Level 3 Mux Select 0= gpio0, Input, gpio_0_pin_in[22]- (GPIO bank 0) 0=
    * gpio0, Output, gpio_0_pin_out[22]- (GPIO bank 0) 1= can0, Input, can0_ph
    * y_rx- (Can RX signal) 2= i2c0, Input, i2c0_scl_input- (SCL signal) 2= i2
    * c0, Output, i2c0_scl_out- (SCL signal) 3= swdt0, Input, swdt0_clk_in- (W
    * atch Dog Timer Input clock) 4= spi1, Input, spi1_sclk_in- (SPI Clock) 4=
    *  spi1, Output, spi1_sclk_out- (SPI Clock) 5= ttc0, Input, ttc0_clk_in- (
    * TTC Clock) 6= ua0, Input, ua0_rxd- (UART receiver serial input) 7= Not U
    * sed
    *  PSU_IOU_SLCR_MIO_PIN_22_L3_SEL                              0

    * Configures MIO Pin 22 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF180058, 0x000000FEU ,0x00000000U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_22_OFFSET, 0x000000FEU, 0x00000000U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_23 @ 0XFF18005C

    * Level 0 Mux Select 0= Level 1 Mux Output 1= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_23_L0_SEL                              0

    * Level 1 Mux Select 0= Level 2 Mux Output 1= nand, Input, nfc_dq_in[6]- (
    * NAND Data Bus) 1= nand, Output, nfc_dq_out[6]- (NAND Data Bus)
    *  PSU_IOU_SLCR_MIO_PIN_23_L1_SEL                              0

    * Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Output, sdio0_bus_pow-
    * (SD card bus power) 2= test_scan, Input, test_scan_in[23]- (Test Scan Po
    * rt) = test_scan, Output, test_scan_out[23]- (Test Scan Port) 3= csu, Inp
    * ut, csu_ext_tamper- (CSU Ext Tamper)
    *  PSU_IOU_SLCR_MIO_PIN_23_L2_SEL                              0

    * Level 3 Mux Select 0= gpio0, Input, gpio_0_pin_in[23]- (GPIO bank 0) 0=
    * gpio0, Output, gpio_0_pin_out[23]- (GPIO bank 0) 1= can0, Output, can0_p
    * hy_tx- (Can TX signal) 2= i2c0, Input, i2c0_sda_input- (SDA signal) 2= i
    * 2c0, Output, i2c0_sda_out- (SDA signal) 3= swdt0, Output, swdt0_rst_out-
    *  (Watch Dog Timer Output clock) 4= spi1, Output, spi1_mo- (MOSI signal)
    * 4= spi1, Input, spi1_si- (MOSI signal) 5= ttc0, Output, ttc0_wave_out- (
    * TTC Waveform Clock) 6= ua0, Output, ua0_txd- (UART transmitter serial ou
    * tput) 7= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_23_L3_SEL                              0

    * Configures MIO Pin 23 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF18005C, 0x000000FEU ,0x00000000U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_23_OFFSET, 0x000000FEU, 0x00000000U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_24 @ 0XFF180060

    * Level 0 Mux Select 0= Level 1 Mux Output 1= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_24_L0_SEL                              0

    * Level 1 Mux Select 0= Level 2 Mux Output 1= nand, Input, nfc_dq_in[7]- (
    * NAND Data Bus) 1= nand, Output, nfc_dq_out[7]- (NAND Data Bus)
    *  PSU_IOU_SLCR_MIO_PIN_24_L1_SEL                              0

    * Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Input, sdio0_cd_n- (SD
    * card detect from connector) 2= test_scan, Input, test_scan_in[24]- (Test
    *  Scan Port) = test_scan, Output, test_scan_out[24]- (Test Scan Port) 3=
    * csu, Input, csu_ext_tamper- (CSU Ext Tamper)
    *  PSU_IOU_SLCR_MIO_PIN_24_L2_SEL                              0

    * Level 3 Mux Select 0= gpio0, Input, gpio_0_pin_in[24]- (GPIO bank 0) 0=
    * gpio0, Output, gpio_0_pin_out[24]- (GPIO bank 0) 1= can1, Output, can1_p
    * hy_tx- (Can TX signal) 2= i2c1, Input, i2c1_scl_input- (SCL signal) 2= i
    * 2c1, Output, i2c1_scl_out- (SCL signal) 3= swdt1, Input, swdt1_clk_in- (
    * Watch Dog Timer Input clock) 4= Not Used 5= ttc3, Input, ttc3_clk_in- (T
    * TC Clock) 6= ua1, Output, ua1_txd- (UART transmitter serial output) 7= N
    * ot Used
    *  PSU_IOU_SLCR_MIO_PIN_24_L3_SEL                              1

    * Configures MIO Pin 24 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF180060, 0x000000FEU ,0x00000020U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_24_OFFSET, 0x000000FEU, 0x00000020U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_25 @ 0XFF180064

    * Level 0 Mux Select 0= Level 1 Mux Output 1= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_25_L0_SEL                              0

    * Level 1 Mux Select 0= Level 2 Mux Output 1= nand, Output, nfc_re_n- (NAN
    * D Read Enable)
    *  PSU_IOU_SLCR_MIO_PIN_25_L1_SEL                              0

    * Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Input, sdio0_wp- (SD ca
    * rd write protect from connector) 2= test_scan, Input, test_scan_in[25]-
    * (Test Scan Port) = test_scan, Output, test_scan_out[25]- (Test Scan Port
    * ) 3= csu, Input, csu_ext_tamper- (CSU Ext Tamper)
    *  PSU_IOU_SLCR_MIO_PIN_25_L2_SEL                              0

    * Level 3 Mux Select 0= gpio0, Input, gpio_0_pin_in[25]- (GPIO bank 0) 0=
    * gpio0, Output, gpio_0_pin_out[25]- (GPIO bank 0) 1= can1, Input, can1_ph
    * y_rx- (Can RX signal) 2= i2c1, Input, i2c1_sda_input- (SDA signal) 2= i2
    * c1, Output, i2c1_sda_out- (SDA signal) 3= swdt1, Output, swdt1_rst_out-
    * (Watch Dog Timer Output clock) 4= Not Used 5= ttc3, Output, ttc3_wave_ou
    * t- (TTC Waveform Clock) 6= ua1, Input, ua1_rxd- (UART receiver serial in
    * put) 7= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_25_L3_SEL                              1

    * Configures MIO Pin 25 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF180064, 0x000000FEU ,0x00000020U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_25_OFFSET, 0x000000FEU, 0x00000020U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_26 @ 0XFF180068

    * Level 0 Mux Select 0= Level 1 Mux Output 1= gem0, Output, gem0_rgmii_tx_
    * clk- (TX RGMII clock)
    *  PSU_IOU_SLCR_MIO_PIN_26_L0_SEL                              0

    * Level 1 Mux Select 0= Level 2 Mux Output 1= nand, Output, nfc_ce[1]- (NA
    * ND chip enable)
    *  PSU_IOU_SLCR_MIO_PIN_26_L1_SEL                              0

    * Level 2 Mux Select 0= Level 3 Mux Output 1= pmu, Input, pmu_gpi[0]- (PMU
    *  GPI) 2= test_scan, Input, test_scan_in[26]- (Test Scan Port) = test_sca
    * n, Output, test_scan_out[26]- (Test Scan Port) 3= csu, Input, csu_ext_ta
    * mper- (CSU Ext Tamper)
    *  PSU_IOU_SLCR_MIO_PIN_26_L2_SEL                              0

    * Level 3 Mux Select 0= gpio1, Input, gpio_1_pin_in[0]- (GPIO bank 1) 0= g
    * pio1, Output, gpio_1_pin_out[0]- (GPIO bank 1) 1= can0, Input, can0_phy_
    * rx- (Can RX signal) 2= i2c0, Input, i2c0_scl_input- (SCL signal) 2= i2c0
    * , Output, i2c0_scl_out- (SCL signal) 3= pjtag, Input, pjtag_tck- (PJTAG
    * TCK) 4= spi0, Input, spi0_sclk_in- (SPI Clock) 4= spi0, Output, spi0_scl
    * k_out- (SPI Clock) 5= ttc2, Input, ttc2_clk_in- (TTC Clock) 6= ua0, Inpu
    * t, ua0_rxd- (UART receiver serial input) 7= trace, Output, tracedq[4]- (
    * Trace Port Databus)
    *  PSU_IOU_SLCR_MIO_PIN_26_L3_SEL                              0

    * Configures MIO Pin 26 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF180068, 0x000000FEU ,0x00000000U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_26_OFFSET, 0x000000FEU, 0x00000000U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_27 @ 0XFF18006C

    * Level 0 Mux Select 0= Level 1 Mux Output 1= gem0, Output, gem0_rgmii_txd
    * [0]- (TX RGMII data)
    *  PSU_IOU_SLCR_MIO_PIN_27_L0_SEL                              0

    * Level 1 Mux Select 0= Level 2 Mux Output 1= nand, Input, nfc_rb_n[0]- (N
    * AND Ready/Busy)
    *  PSU_IOU_SLCR_MIO_PIN_27_L1_SEL                              0

    * Level 2 Mux Select 0= Level 3 Mux Output 1= pmu, Input, pmu_gpi[1]- (PMU
    *  GPI) 2= test_scan, Input, test_scan_in[27]- (Test Scan Port) = test_sca
    * n, Output, test_scan_out[27]- (Test Scan Port) 3= dpaux, Input, dp_aux_d
    * ata_in- (Dp Aux Data) = dpaux, Output, dp_aux_data_out- (Dp Aux Data)
    *  PSU_IOU_SLCR_MIO_PIN_27_L2_SEL                              3

    * Level 3 Mux Select 0= gpio1, Input, gpio_1_pin_in[1]- (GPIO bank 1) 0= g
    * pio1, Output, gpio_1_pin_out[1]- (GPIO bank 1) 1= can0, Output, can0_phy
    * _tx- (Can TX signal) 2= i2c0, Input, i2c0_sda_input- (SDA signal) 2= i2c
    * 0, Output, i2c0_sda_out- (SDA signal) 3= pjtag, Input, pjtag_tdi- (PJTAG
    *  TDI) 4= spi0, Output, spi0_n_ss_out[2]- (SPI Master Selects) 5= ttc2, O
    * utput, ttc2_wave_out- (TTC Waveform Clock) 6= ua0, Output, ua0_txd- (UAR
    * T transmitter serial output) 7= trace, Output, tracedq[5]- (Trace Port D
    * atabus)
    *  PSU_IOU_SLCR_MIO_PIN_27_L3_SEL                              0

    * Configures MIO Pin 27 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF18006C, 0x000000FEU ,0x00000018U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_27_OFFSET, 0x000000FEU, 0x00000018U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_28 @ 0XFF180070

    * Level 0 Mux Select 0= Level 1 Mux Output 1= gem0, Output, gem0_rgmii_txd
    * [1]- (TX RGMII data)
    *  PSU_IOU_SLCR_MIO_PIN_28_L0_SEL                              0

    * Level 1 Mux Select 0= Level 2 Mux Output 1= nand, Input, nfc_rb_n[1]- (N
    * AND Ready/Busy)
    *  PSU_IOU_SLCR_MIO_PIN_28_L1_SEL                              0

    * Level 2 Mux Select 0= Level 3 Mux Output 1= pmu, Input, pmu_gpi[2]- (PMU
    *  GPI) 2= test_scan, Input, test_scan_in[28]- (Test Scan Port) = test_sca
    * n, Output, test_scan_out[28]- (Test Scan Port) 3= dpaux, Input, dp_hot_p
    * lug_detect- (Dp Aux Hot Plug)
    *  PSU_IOU_SLCR_MIO_PIN_28_L2_SEL                              3

    * Level 3 Mux Select 0= gpio1, Input, gpio_1_pin_in[2]- (GPIO bank 1) 0= g
    * pio1, Output, gpio_1_pin_out[2]- (GPIO bank 1) 1= can1, Output, can1_phy
    * _tx- (Can TX signal) 2= i2c1, Input, i2c1_scl_input- (SCL signal) 2= i2c
    * 1, Output, i2c1_scl_out- (SCL signal) 3= pjtag, Output, pjtag_tdo- (PJTA
    * G TDO) 4= spi0, Output, spi0_n_ss_out[1]- (SPI Master Selects) 5= ttc1,
    * Input, ttc1_clk_in- (TTC Clock) 6= ua1, Output, ua1_txd- (UART transmitt
    * er serial output) 7= trace, Output, tracedq[6]- (Trace Port Databus)
    *  PSU_IOU_SLCR_MIO_PIN_28_L3_SEL                              0

    * Configures MIO Pin 28 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF180070, 0x000000FEU ,0x00000018U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_28_OFFSET, 0x000000FEU, 0x00000018U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_29 @ 0XFF180074

    * Level 0 Mux Select 0= Level 1 Mux Output 1= gem0, Output, gem0_rgmii_txd
    * [2]- (TX RGMII data)
    *  PSU_IOU_SLCR_MIO_PIN_29_L0_SEL                              0

    * Level 1 Mux Select 0= Level 2 Mux Output 1= pcie, Input, pcie_reset_n- (
    * PCIE Reset signal)
    *  PSU_IOU_SLCR_MIO_PIN_29_L1_SEL                              0

    * Level 2 Mux Select 0= Level 3 Mux Output 1= pmu, Input, pmu_gpi[3]- (PMU
    *  GPI) 2= test_scan, Input, test_scan_in[29]- (Test Scan Port) = test_sca
    * n, Output, test_scan_out[29]- (Test Scan Port) 3= dpaux, Input, dp_aux_d
    * ata_in- (Dp Aux Data) = dpaux, Output, dp_aux_data_out- (Dp Aux Data)
    *  PSU_IOU_SLCR_MIO_PIN_29_L2_SEL                              3

    * Level 3 Mux Select 0= gpio1, Input, gpio_1_pin_in[3]- (GPIO bank 1) 0= g
    * pio1, Output, gpio_1_pin_out[3]- (GPIO bank 1) 1= can1, Input, can1_phy_
    * rx- (Can RX signal) 2= i2c1, Input, i2c1_sda_input- (SDA signal) 2= i2c1
    * , Output, i2c1_sda_out- (SDA signal) 3= pjtag, Input, pjtag_tms- (PJTAG
    * TMS) 4= spi0, Input, spi0_n_ss_in- (SPI Master Selects) 4= spi0, Output,
    *  spi0_n_ss_out[0]- (SPI Master Selects) 5= ttc1, Output, ttc1_wave_out-
    * (TTC Waveform Clock) 6= ua1, Input, ua1_rxd- (UART receiver serial input
    * ) 7= trace, Output, tracedq[7]- (Trace Port Databus)
    *  PSU_IOU_SLCR_MIO_PIN_29_L3_SEL                              0

    * Configures MIO Pin 29 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF180074, 0x000000FEU ,0x00000018U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_29_OFFSET, 0x000000FEU, 0x00000018U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_30 @ 0XFF180078

    * Level 0 Mux Select 0= Level 1 Mux Output 1= gem0, Output, gem0_rgmii_txd
    * [3]- (TX RGMII data)
    *  PSU_IOU_SLCR_MIO_PIN_30_L0_SEL                              0

    * Level 1 Mux Select 0= Level 2 Mux Output 1= pcie, Input, pcie_reset_n- (
    * PCIE Reset signal)
    *  PSU_IOU_SLCR_MIO_PIN_30_L1_SEL                              0

    * Level 2 Mux Select 0= Level 3 Mux Output 1= pmu, Input, pmu_gpi[4]- (PMU
    *  GPI) 2= test_scan, Input, test_scan_in[30]- (Test Scan Port) = test_sca
    * n, Output, test_scan_out[30]- (Test Scan Port) 3= dpaux, Input, dp_hot_p
    * lug_detect- (Dp Aux Hot Plug)
    *  PSU_IOU_SLCR_MIO_PIN_30_L2_SEL                              3

    * Level 3 Mux Select 0= gpio1, Input, gpio_1_pin_in[4]- (GPIO bank 1) 0= g
    * pio1, Output, gpio_1_pin_out[4]- (GPIO bank 1) 1= can0, Input, can0_phy_
    * rx- (Can RX signal) 2= i2c0, Input, i2c0_scl_input- (SCL signal) 2= i2c0
    * , Output, i2c0_scl_out- (SCL signal) 3= swdt0, Input, swdt0_clk_in- (Wat
    * ch Dog Timer Input clock) 4= spi0, Input, spi0_mi- (MISO signal) 4= spi0
    * , Output, spi0_so- (MISO signal) 5= ttc0, Input, ttc0_clk_in- (TTC Clock
    * ) 6= ua0, Input, ua0_rxd- (UART receiver serial input) 7= trace, Output,
    *  tracedq[8]- (Trace Port Databus)
    *  PSU_IOU_SLCR_MIO_PIN_30_L3_SEL                              0

    * Configures MIO Pin 30 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF180078, 0x000000FEU ,0x00000018U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_30_OFFSET, 0x000000FEU, 0x00000018U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_31 @ 0XFF18007C

    * Level 0 Mux Select 0= Level 1 Mux Output 1= gem0, Output, gem0_rgmii_tx_
    * ctl- (TX RGMII control)
    *  PSU_IOU_SLCR_MIO_PIN_31_L0_SEL                              0

    * Level 1 Mux Select 0= Level 2 Mux Output 1= pcie, Input, pcie_reset_n- (
    * PCIE Reset signal)
    *  PSU_IOU_SLCR_MIO_PIN_31_L1_SEL                              0

    * Level 2 Mux Select 0= Level 3 Mux Output 1= pmu, Input, pmu_gpi[5]- (PMU
    *  GPI) 2= test_scan, Input, test_scan_in[31]- (Test Scan Port) = test_sca
    * n, Output, test_scan_out[31]- (Test Scan Port) 3= csu, Input, csu_ext_ta
    * mper- (CSU Ext Tamper)
    *  PSU_IOU_SLCR_MIO_PIN_31_L2_SEL                              0

    * Level 3 Mux Select 0= gpio1, Input, gpio_1_pin_in[5]- (GPIO bank 1) 0= g
    * pio1, Output, gpio_1_pin_out[5]- (GPIO bank 1) 1= can0, Output, can0_phy
    * _tx- (Can TX signal) 2= i2c0, Input, i2c0_sda_input- (SDA signal) 2= i2c
    * 0, Output, i2c0_sda_out- (SDA signal) 3= swdt0, Output, swdt0_rst_out- (
    * Watch Dog Timer Output clock) 4= spi0, Output, spi0_mo- (MOSI signal) 4=
    *  spi0, Input, spi0_si- (MOSI signal) 5= ttc0, Output, ttc0_wave_out- (TT
    * C Waveform Clock) 6= ua0, Output, ua0_txd- (UART transmitter serial outp
    * ut) 7= trace, Output, tracedq[9]- (Trace Port Databus)
    *  PSU_IOU_SLCR_MIO_PIN_31_L3_SEL                              0

    * Configures MIO Pin 31 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF18007C, 0x000000FEU ,0x00000000U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_31_OFFSET, 0x000000FEU, 0x00000000U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_32 @ 0XFF180080

    * Level 0 Mux Select 0= Level 1 Mux Output 1= gem0, Input, gem0_rgmii_rx_c
    * lk- (RX RGMII clock)
    *  PSU_IOU_SLCR_MIO_PIN_32_L0_SEL                              0

    * Level 1 Mux Select 0= Level 2 Mux Output 1= nand, Input, nfc_dqs_in- (NA
    * ND Strobe) 1= nand, Output, nfc_dqs_out- (NAND Strobe)
    *  PSU_IOU_SLCR_MIO_PIN_32_L1_SEL                              0

    * Level 2 Mux Select 0= Level 3 Mux Output 1= pmu, Output, pmu_gpo[0]- (PM
    * U GPI) 2= test_scan, Input, test_scan_in[32]- (Test Scan Port) = test_sc
    * an, Output, test_scan_out[32]- (Test Scan Port) 3= csu, Input, csu_ext_t
    * amper- (CSU Ext Tamper)
    *  PSU_IOU_SLCR_MIO_PIN_32_L2_SEL                              1

    * Level 3 Mux Select 0= gpio1, Input, gpio_1_pin_in[6]- (GPIO bank 1) 0= g
    * pio1, Output, gpio_1_pin_out[6]- (GPIO bank 1) 1= can1, Output, can1_phy
    * _tx- (Can TX signal) 2= i2c1, Input, i2c1_scl_input- (SCL signal) 2= i2c
    * 1, Output, i2c1_scl_out- (SCL signal) 3= swdt1, Input, swdt1_clk_in- (Wa
    * tch Dog Timer Input clock) 4= spi1, Input, spi1_sclk_in- (SPI Clock) 4=
    * spi1, Output, spi1_sclk_out- (SPI Clock) 5= ttc3, Input, ttc3_clk_in- (T
    * TC Clock) 6= ua1, Output, ua1_txd- (UART transmitter serial output) 7= t
    * race, Output, tracedq[10]- (Trace Port Databus)
    *  PSU_IOU_SLCR_MIO_PIN_32_L3_SEL                              0

    * Configures MIO Pin 32 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF180080, 0x000000FEU ,0x00000008U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_32_OFFSET, 0x000000FEU, 0x00000008U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_33 @ 0XFF180084

    * Level 0 Mux Select 0= Level 1 Mux Output 1= gem0, Input, gem0_rgmii_rxd[
    * 0]- (RX RGMII data)
    *  PSU_IOU_SLCR_MIO_PIN_33_L0_SEL                              0

    * Level 1 Mux Select 0= Level 2 Mux Output 1= pcie, Input, pcie_reset_n- (
    * PCIE Reset signal)
    *  PSU_IOU_SLCR_MIO_PIN_33_L1_SEL                              0

    * Level 2 Mux Select 0= Level 3 Mux Output 1= pmu, Output, pmu_gpo[1]- (PM
    * U GPI) 2= test_scan, Input, test_scan_in[33]- (Test Scan Port) = test_sc
    * an, Output, test_scan_out[33]- (Test Scan Port) 3= csu, Input, csu_ext_t
    * amper- (CSU Ext Tamper)
    *  PSU_IOU_SLCR_MIO_PIN_33_L2_SEL                              1

    * Level 3 Mux Select 0= gpio1, Input, gpio_1_pin_in[7]- (GPIO bank 1) 0= g
    * pio1, Output, gpio_1_pin_out[7]- (GPIO bank 1) 1= can1, Input, can1_phy_
    * rx- (Can RX signal) 2= i2c1, Input, i2c1_sda_input- (SDA signal) 2= i2c1
    * , Output, i2c1_sda_out- (SDA signal) 3= swdt1, Output, swdt1_rst_out- (W
    * atch Dog Timer Output clock) 4= spi1, Output, spi1_n_ss_out[2]- (SPI Mas
    * ter Selects) 5= ttc3, Output, ttc3_wave_out- (TTC Waveform Clock) 6= ua1
    * , Input, ua1_rxd- (UART receiver serial input) 7= trace, Output, tracedq
    * [11]- (Trace Port Databus)
    *  PSU_IOU_SLCR_MIO_PIN_33_L3_SEL                              0

    * Configures MIO Pin 33 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF180084, 0x000000FEU ,0x00000008U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_33_OFFSET, 0x000000FEU, 0x00000008U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_34 @ 0XFF180088

    * Level 0 Mux Select 0= Level 1 Mux Output 1= gem0, Input, gem0_rgmii_rxd[
    * 1]- (RX RGMII data)
    *  PSU_IOU_SLCR_MIO_PIN_34_L0_SEL                              0

    * Level 1 Mux Select 0= Level 2 Mux Output 1= pcie, Input, pcie_reset_n- (
    * PCIE Reset signal)
    *  PSU_IOU_SLCR_MIO_PIN_34_L1_SEL                              0

    * Level 2 Mux Select 0= Level 3 Mux Output 1= pmu, Output, pmu_gpo[2]- (PM
    * U GPI) 2= test_scan, Input, test_scan_in[34]- (Test Scan Port) = test_sc
    * an, Output, test_scan_out[34]- (Test Scan Port) 3= dpaux, Input, dp_aux_
    * data_in- (Dp Aux Data) = dpaux, Output, dp_aux_data_out- (Dp Aux Data)
    *  PSU_IOU_SLCR_MIO_PIN_34_L2_SEL                              1

    * Level 3 Mux Select 0= gpio1, Input, gpio_1_pin_in[8]- (GPIO bank 1) 0= g
    * pio1, Output, gpio_1_pin_out[8]- (GPIO bank 1) 1= can0, Input, can0_phy_
    * rx- (Can RX signal) 2= i2c0, Input, i2c0_scl_input- (SCL signal) 2= i2c0
    * , Output, i2c0_scl_out- (SCL signal) 3= swdt0, Input, swdt0_clk_in- (Wat
    * ch Dog Timer Input clock) 4= spi1, Output, spi1_n_ss_out[1]- (SPI Master
    *  Selects) 5= ttc2, Input, ttc2_clk_in- (TTC Clock) 6= ua0, Input, ua0_rx
    * d- (UART receiver serial input) 7= trace, Output, tracedq[12]- (Trace Po
    * rt Databus)
    *  PSU_IOU_SLCR_MIO_PIN_34_L3_SEL                              0

    * Configures MIO Pin 34 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF180088, 0x000000FEU ,0x00000008U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_34_OFFSET, 0x000000FEU, 0x00000008U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_35 @ 0XFF18008C

    * Level 0 Mux Select 0= Level 1 Mux Output 1= gem0, Input, gem0_rgmii_rxd[
    * 2]- (RX RGMII data)
    *  PSU_IOU_SLCR_MIO_PIN_35_L0_SEL                              0

    * Level 1 Mux Select 0= Level 2 Mux Output 1= pcie, Input, pcie_reset_n- (
    * PCIE Reset signal)
    *  PSU_IOU_SLCR_MIO_PIN_35_L1_SEL                              0

    * Level 2 Mux Select 0= Level 3 Mux Output 1= pmu, Output, pmu_gpo[3]- (PM
    * U GPI) 2= test_scan, Input, test_scan_in[35]- (Test Scan Port) = test_sc
    * an, Output, test_scan_out[35]- (Test Scan Port) 3= dpaux, Input, dp_hot_
    * plug_detect- (Dp Aux Hot Plug)
    *  PSU_IOU_SLCR_MIO_PIN_35_L2_SEL                              1

    * Level 3 Mux Select 0= gpio1, Input, gpio_1_pin_in[9]- (GPIO bank 1) 0= g
    * pio1, Output, gpio_1_pin_out[9]- (GPIO bank 1) 1= can0, Output, can0_phy
    * _tx- (Can TX signal) 2= i2c0, Input, i2c0_sda_input- (SDA signal) 2= i2c
    * 0, Output, i2c0_sda_out- (SDA signal) 3= swdt0, Output, swdt0_rst_out- (
    * Watch Dog Timer Output clock) 4= spi1, Input, spi1_n_ss_in- (SPI Master
    * Selects) 4= spi1, Output, spi1_n_ss_out[0]- (SPI Master Selects) 5= ttc2
    * , Output, ttc2_wave_out- (TTC Waveform Clock) 6= ua0, Output, ua0_txd- (
    * UART transmitter serial output) 7= trace, Output, tracedq[13]- (Trace Po
    * rt Databus)
    *  PSU_IOU_SLCR_MIO_PIN_35_L3_SEL                              0

    * Configures MIO Pin 35 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF18008C, 0x000000FEU ,0x00000008U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_35_OFFSET, 0x000000FEU, 0x00000008U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_36 @ 0XFF180090

    * Level 0 Mux Select 0= Level 1 Mux Output 1= gem0, Input, gem0_rgmii_rxd[
    * 3]- (RX RGMII data)
    *  PSU_IOU_SLCR_MIO_PIN_36_L0_SEL                              0

    * Level 1 Mux Select 0= Level 2 Mux Output 1= pcie, Input, pcie_reset_n- (
    * PCIE Reset signal)
    *  PSU_IOU_SLCR_MIO_PIN_36_L1_SEL                              0

    * Level 2 Mux Select 0= Level 3 Mux Output 1= pmu, Output, pmu_gpo[4]- (PM
    * U GPI) 2= test_scan, Input, test_scan_in[36]- (Test Scan Port) = test_sc
    * an, Output, test_scan_out[36]- (Test Scan Port) 3= dpaux, Input, dp_aux_
    * data_in- (Dp Aux Data) = dpaux, Output, dp_aux_data_out- (Dp Aux Data)
    *  PSU_IOU_SLCR_MIO_PIN_36_L2_SEL                              1

    * Level 3 Mux Select 0= gpio1, Input, gpio_1_pin_in[10]- (GPIO bank 1) 0=
    * gpio1, Output, gpio_1_pin_out[10]- (GPIO bank 1) 1= can1, Output, can1_p
    * hy_tx- (Can TX signal) 2= i2c1, Input, i2c1_scl_input- (SCL signal) 2= i
    * 2c1, Output, i2c1_scl_out- (SCL signal) 3= swdt1, Input, swdt1_clk_in- (
    * Watch Dog Timer Input clock) 4= spi1, Input, spi1_mi- (MISO signal) 4= s
    * pi1, Output, spi1_so- (MISO signal) 5= ttc1, Input, ttc1_clk_in- (TTC Cl
    * ock) 6= ua1, Output, ua1_txd- (UART transmitter serial output) 7= trace,
    *  Output, tracedq[14]- (Trace Port Databus)
    *  PSU_IOU_SLCR_MIO_PIN_36_L3_SEL                              0

    * Configures MIO Pin 36 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF180090, 0x000000FEU ,0x00000008U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_36_OFFSET, 0x000000FEU, 0x00000008U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_37 @ 0XFF180094

    * Level 0 Mux Select 0= Level 1 Mux Output 1= gem0, Input, gem0_rgmii_rx_c
    * tl- (RX RGMII control )
    *  PSU_IOU_SLCR_MIO_PIN_37_L0_SEL                              0

    * Level 1 Mux Select 0= Level 2 Mux Output 1= pcie, Input, pcie_reset_n- (
    * PCIE Reset signal)
    *  PSU_IOU_SLCR_MIO_PIN_37_L1_SEL                              0

    * Level 2 Mux Select 0= Level 3 Mux Output 1= pmu, Output, pmu_gpo[5]- (PM
    * U GPI) 2= test_scan, Input, test_scan_in[37]- (Test Scan Port) = test_sc
    * an, Output, test_scan_out[37]- (Test Scan Port) 3= dpaux, Input, dp_hot_
    * plug_detect- (Dp Aux Hot Plug)
    *  PSU_IOU_SLCR_MIO_PIN_37_L2_SEL                              1

    * Level 3 Mux Select 0= gpio1, Input, gpio_1_pin_in[11]- (GPIO bank 1) 0=
    * gpio1, Output, gpio_1_pin_out[11]- (GPIO bank 1) 1= can1, Input, can1_ph
    * y_rx- (Can RX signal) 2= i2c1, Input, i2c1_sda_input- (SDA signal) 2= i2
    * c1, Output, i2c1_sda_out- (SDA signal) 3= swdt1, Output, swdt1_rst_out-
    * (Watch Dog Timer Output clock) 4= spi1, Output, spi1_mo- (MOSI signal) 4
    * = spi1, Input, spi1_si- (MOSI signal) 5= ttc1, Output, ttc1_wave_out- (T
    * TC Waveform Clock) 6= ua1, Input, ua1_rxd- (UART receiver serial input)
    * 7= trace, Output, tracedq[15]- (Trace Port Databus)
    *  PSU_IOU_SLCR_MIO_PIN_37_L3_SEL                              0

    * Configures MIO Pin 37 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF180094, 0x000000FEU ,0x00000008U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_37_OFFSET, 0x000000FEU, 0x00000008U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_38 @ 0XFF180098

    * Level 0 Mux Select 0= Level 1 Mux Output 1= gem1, Output, gem1_rgmii_tx_
    * clk- (TX RGMII clock)
    *  PSU_IOU_SLCR_MIO_PIN_38_L0_SEL                              0

    * Level 1 Mux Select 0= Level 2 Mux Output 1= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_38_L1_SEL                              0

    * Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Output, sdio0_clk_out-
    * (SDSDIO clock) 2= Not Used 3= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_38_L2_SEL                              0

    * Level 3 Mux Select 0= gpio1, Input, gpio_1_pin_in[12]- (GPIO bank 1) 0=
    * gpio1, Output, gpio_1_pin_out[12]- (GPIO bank 1) 1= can0, Input, can0_ph
    * y_rx- (Can RX signal) 2= i2c0, Input, i2c0_scl_input- (SCL signal) 2= i2
    * c0, Output, i2c0_scl_out- (SCL signal) 3= pjtag, Input, pjtag_tck- (PJTA
    * G TCK) 4= spi0, Input, spi0_sclk_in- (SPI Clock) 4= spi0, Output, spi0_s
    * clk_out- (SPI Clock) 5= ttc0, Input, ttc0_clk_in- (TTC Clock) 6= ua0, In
    * put, ua0_rxd- (UART receiver serial input) 7= trace, Output, trace_clk-
    * (Trace Port Clock)
    *  PSU_IOU_SLCR_MIO_PIN_38_L3_SEL                              0

    * Configures MIO Pin 38 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF180098, 0x000000FEU ,0x00000000U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_38_OFFSET, 0x000000FEU, 0x00000000U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_39 @ 0XFF18009C

    * Level 0 Mux Select 0= Level 1 Mux Output 1= gem1, Output, gem1_rgmii_txd
    * [0]- (TX RGMII data)
    *  PSU_IOU_SLCR_MIO_PIN_39_L0_SEL                              0

    * Level 1 Mux Select 0= Level 2 Mux Output 1= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_39_L1_SEL                              0

    * Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Input, sdio0_cd_n- (SD
    * card detect from connector) 2= sd1, Input, sd1_data_in[4]- (8-bit Data b
    * us) = sd1, Output, sdio1_data_out[4]- (8-bit Data bus) 3= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_39_L2_SEL                              2

    * Level 3 Mux Select 0= gpio1, Input, gpio_1_pin_in[13]- (GPIO bank 1) 0=
    * gpio1, Output, gpio_1_pin_out[13]- (GPIO bank 1) 1= can0, Output, can0_p
    * hy_tx- (Can TX signal) 2= i2c0, Input, i2c0_sda_input- (SDA signal) 2= i
    * 2c0, Output, i2c0_sda_out- (SDA signal) 3= pjtag, Input, pjtag_tdi- (PJT
    * AG TDI) 4= spi0, Output, spi0_n_ss_out[2]- (SPI Master Selects) 5= ttc0,
    *  Output, ttc0_wave_out- (TTC Waveform Clock) 6= ua0, Output, ua0_txd- (U
    * ART transmitter serial output) 7= trace, Output, trace_ctl- (Trace Port
    * Control Signal)
    *  PSU_IOU_SLCR_MIO_PIN_39_L3_SEL                              0

    * Configures MIO Pin 39 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF18009C, 0x000000FEU ,0x00000010U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_39_OFFSET, 0x000000FEU, 0x00000010U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_40 @ 0XFF1800A0

    * Level 0 Mux Select 0= Level 1 Mux Output 1= gem1, Output, gem1_rgmii_txd
    * [1]- (TX RGMII data)
    *  PSU_IOU_SLCR_MIO_PIN_40_L0_SEL                              0

    * Level 1 Mux Select 0= Level 2 Mux Output 1= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_40_L1_SEL                              0

    * Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Input, sd0_cmd_in- (Com
    * mand Indicator) = sd0, Output, sdio0_cmd_out- (Command Indicator) 2= sd1
    * , Input, sd1_data_in[5]- (8-bit Data bus) = sd1, Output, sdio1_data_out[
    * 5]- (8-bit Data bus) 3= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_40_L2_SEL                              2

    * Level 3 Mux Select 0= gpio1, Input, gpio_1_pin_in[14]- (GPIO bank 1) 0=
    * gpio1, Output, gpio_1_pin_out[14]- (GPIO bank 1) 1= can1, Output, can1_p
    * hy_tx- (Can TX signal) 2= i2c1, Input, i2c1_scl_input- (SCL signal) 2= i
    * 2c1, Output, i2c1_scl_out- (SCL signal) 3= pjtag, Output, pjtag_tdo- (PJ
    * TAG TDO) 4= spi0, Output, spi0_n_ss_out[1]- (SPI Master Selects) 5= ttc3
    * , Input, ttc3_clk_in- (TTC Clock) 6= ua1, Output, ua1_txd- (UART transmi
    * tter serial output) 7= trace, Output, tracedq[0]- (Trace Port Databus)
    *  PSU_IOU_SLCR_MIO_PIN_40_L3_SEL                              0

    * Configures MIO Pin 40 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF1800A0, 0x000000FEU ,0x00000010U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_40_OFFSET, 0x000000FEU, 0x00000010U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_41 @ 0XFF1800A4

    * Level 0 Mux Select 0= Level 1 Mux Output 1= gem1, Output, gem1_rgmii_txd
    * [2]- (TX RGMII data)
    *  PSU_IOU_SLCR_MIO_PIN_41_L0_SEL                              0

    * Level 1 Mux Select 0= Level 2 Mux Output 1= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_41_L1_SEL                              0

    * Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Input, sd0_data_in[0]-
    * (8-bit Data bus) = sd0, Output, sdio0_data_out[0]- (8-bit Data bus) 2= s
    * d1, Input, sd1_data_in[6]- (8-bit Data bus) = sd1, Output, sdio1_data_ou
    * t[6]- (8-bit Data bus) 3= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_41_L2_SEL                              2

    * Level 3 Mux Select 0= gpio1, Input, gpio_1_pin_in[15]- (GPIO bank 1) 0=
    * gpio1, Output, gpio_1_pin_out[15]- (GPIO bank 1) 1= can1, Input, can1_ph
    * y_rx- (Can RX signal) 2= i2c1, Input, i2c1_sda_input- (SDA signal) 2= i2
    * c1, Output, i2c1_sda_out- (SDA signal) 3= pjtag, Input, pjtag_tms- (PJTA
    * G TMS) 4= spi0, Input, spi0_n_ss_in- (SPI Master Selects) 4= spi0, Outpu
    * t, spi0_n_ss_out[0]- (SPI Master Selects) 5= ttc3, Output, ttc3_wave_out
    * - (TTC Waveform Clock) 6= ua1, Input, ua1_rxd- (UART receiver serial inp
    * ut) 7= trace, Output, tracedq[1]- (Trace Port Databus)
    *  PSU_IOU_SLCR_MIO_PIN_41_L3_SEL                              0

    * Configures MIO Pin 41 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF1800A4, 0x000000FEU ,0x00000010U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_41_OFFSET, 0x000000FEU, 0x00000010U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_42 @ 0XFF1800A8

    * Level 0 Mux Select 0= Level 1 Mux Output 1= gem1, Output, gem1_rgmii_txd
    * [3]- (TX RGMII data)
    *  PSU_IOU_SLCR_MIO_PIN_42_L0_SEL                              0

    * Level 1 Mux Select 0= Level 2 Mux Output 1= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_42_L1_SEL                              0

    * Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Input, sd0_data_in[1]-
    * (8-bit Data bus) = sd0, Output, sdio0_data_out[1]- (8-bit Data bus) 2= s
    * d1, Input, sd1_data_in[7]- (8-bit Data bus) = sd1, Output, sdio1_data_ou
    * t[7]- (8-bit Data bus) 3= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_42_L2_SEL                              2

    * Level 3 Mux Select 0= gpio1, Input, gpio_1_pin_in[16]- (GPIO bank 1) 0=
    * gpio1, Output, gpio_1_pin_out[16]- (GPIO bank 1) 1= can0, Input, can0_ph
    * y_rx- (Can RX signal) 2= i2c0, Input, i2c0_scl_input- (SCL signal) 2= i2
    * c0, Output, i2c0_scl_out- (SCL signal) 3= swdt0, Input, swdt0_clk_in- (W
    * atch Dog Timer Input clock) 4= spi0, Input, spi0_mi- (MISO signal) 4= sp
    * i0, Output, spi0_so- (MISO signal) 5= ttc2, Input, ttc2_clk_in- (TTC Clo
    * ck) 6= ua0, Input, ua0_rxd- (UART receiver serial input) 7= trace, Outpu
    * t, tracedq[2]- (Trace Port Databus)
    *  PSU_IOU_SLCR_MIO_PIN_42_L3_SEL                              0

    * Configures MIO Pin 42 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF1800A8, 0x000000FEU ,0x00000010U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_42_OFFSET, 0x000000FEU, 0x00000010U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_43 @ 0XFF1800AC

    * Level 0 Mux Select 0= Level 1 Mux Output 1= gem1, Output, gem1_rgmii_tx_
    * ctl- (TX RGMII control)
    *  PSU_IOU_SLCR_MIO_PIN_43_L0_SEL                              0

    * Level 1 Mux Select 0= Level 2 Mux Output 1= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_43_L1_SEL                              0

    * Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Input, sd0_data_in[2]-
    * (8-bit Data bus) = sd0, Output, sdio0_data_out[2]- (8-bit Data bus) 2= s
    * d1, Output, sdio1_bus_pow- (SD card bus power) 3= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_43_L2_SEL                              0

    * Level 3 Mux Select 0= gpio1, Input, gpio_1_pin_in[17]- (GPIO bank 1) 0=
    * gpio1, Output, gpio_1_pin_out[17]- (GPIO bank 1) 1= can0, Output, can0_p
    * hy_tx- (Can TX signal) 2= i2c0, Input, i2c0_sda_input- (SDA signal) 2= i
    * 2c0, Output, i2c0_sda_out- (SDA signal) 3= swdt0, Output, swdt0_rst_out-
    *  (Watch Dog Timer Output clock) 4= spi0, Output, spi0_mo- (MOSI signal)
    * 4= spi0, Input, spi0_si- (MOSI signal) 5= ttc2, Output, ttc2_wave_out- (
    * TTC Waveform Clock) 6= ua0, Output, ua0_txd- (UART transmitter serial ou
    * tput) 7= trace, Output, tracedq[3]- (Trace Port Databus)
    *  PSU_IOU_SLCR_MIO_PIN_43_L3_SEL                              0

    * Configures MIO Pin 43 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF1800AC, 0x000000FEU ,0x00000000U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_43_OFFSET, 0x000000FEU, 0x00000000U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_44 @ 0XFF1800B0

    * Level 0 Mux Select 0= Level 1 Mux Output 1= gem1, Input, gem1_rgmii_rx_c
    * lk- (RX RGMII clock)
    *  PSU_IOU_SLCR_MIO_PIN_44_L0_SEL                              0

    * Level 1 Mux Select 0= Level 2 Mux Output 1= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_44_L1_SEL                              0

    * Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Input, sd0_data_in[3]-
    * (8-bit Data bus) = sd0, Output, sdio0_data_out[3]- (8-bit Data bus) 2= s
    * d1, Input, sdio1_wp- (SD card write protect from connector) 3= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_44_L2_SEL                              2

    * Level 3 Mux Select 0= gpio1, Input, gpio_1_pin_in[18]- (GPIO bank 1) 0=
    * gpio1, Output, gpio_1_pin_out[18]- (GPIO bank 1) 1= can1, Output, can1_p
    * hy_tx- (Can TX signal) 2= i2c1, Input, i2c1_scl_input- (SCL signal) 2= i
    * 2c1, Output, i2c1_scl_out- (SCL signal) 3= swdt1, Input, swdt1_clk_in- (
    * Watch Dog Timer Input clock) 4= spi1, Input, spi1_sclk_in- (SPI Clock) 4
    * = spi1, Output, spi1_sclk_out- (SPI Clock) 5= ttc1, Input, ttc1_clk_in-
    * (TTC Clock) 6= ua1, Output, ua1_txd- (UART transmitter serial output) 7=
    *  Not Used
    *  PSU_IOU_SLCR_MIO_PIN_44_L3_SEL                              0

    * Configures MIO Pin 44 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF1800B0, 0x000000FEU ,0x00000010U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_44_OFFSET, 0x000000FEU, 0x00000010U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_45 @ 0XFF1800B4

    * Level 0 Mux Select 0= Level 1 Mux Output 1= gem1, Input, gem1_rgmii_rxd[
    * 0]- (RX RGMII data)
    *  PSU_IOU_SLCR_MIO_PIN_45_L0_SEL                              0

    * Level 1 Mux Select 0= Level 2 Mux Output 1= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_45_L1_SEL                              0

    * Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Input, sd0_data_in[4]-
    * (8-bit Data bus) = sd0, Output, sdio0_data_out[4]- (8-bit Data bus) 2= s
    * d1, Input, sdio1_cd_n- (SD card detect from connector) 3= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_45_L2_SEL                              2

    * Level 3 Mux Select 0= gpio1, Input, gpio_1_pin_in[19]- (GPIO bank 1) 0=
    * gpio1, Output, gpio_1_pin_out[19]- (GPIO bank 1) 1= can1, Input, can1_ph
    * y_rx- (Can RX signal) 2= i2c1, Input, i2c1_sda_input- (SDA signal) 2= i2
    * c1, Output, i2c1_sda_out- (SDA signal) 3= swdt1, Output, swdt1_rst_out-
    * (Watch Dog Timer Output clock) 4= spi1, Output, spi1_n_ss_out[2]- (SPI M
    * aster Selects) 5= ttc1, Output, ttc1_wave_out- (TTC Waveform Clock) 6= u
    * a1, Input, ua1_rxd- (UART receiver serial input) 7= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_45_L3_SEL                              0

    * Configures MIO Pin 45 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF1800B4, 0x000000FEU ,0x00000010U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_45_OFFSET, 0x000000FEU, 0x00000010U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_46 @ 0XFF1800B8

    * Level 0 Mux Select 0= Level 1 Mux Output 1= gem1, Input, gem1_rgmii_rxd[
    * 1]- (RX RGMII data)
    *  PSU_IOU_SLCR_MIO_PIN_46_L0_SEL                              0

    * Level 1 Mux Select 0= Level 2 Mux Output 1= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_46_L1_SEL                              0

    * Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Input, sd0_data_in[5]-
    * (8-bit Data bus) = sd0, Output, sdio0_data_out[5]- (8-bit Data bus) 2= s
    * d1, Input, sd1_data_in[0]- (8-bit Data bus) = sd1, Output, sdio1_data_ou
    * t[0]- (8-bit Data bus) 3= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_46_L2_SEL                              2

    * Level 3 Mux Select 0= gpio1, Input, gpio_1_pin_in[20]- (GPIO bank 1) 0=
    * gpio1, Output, gpio_1_pin_out[20]- (GPIO bank 1) 1= can0, Input, can0_ph
    * y_rx- (Can RX signal) 2= i2c0, Input, i2c0_scl_input- (SCL signal) 2= i2
    * c0, Output, i2c0_scl_out- (SCL signal) 3= swdt0, Input, swdt0_clk_in- (W
    * atch Dog Timer Input clock) 4= spi1, Output, spi1_n_ss_out[1]- (SPI Mast
    * er Selects) 5= ttc0, Input, ttc0_clk_in- (TTC Clock) 6= ua0, Input, ua0_
    * rxd- (UART receiver serial input) 7= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_46_L3_SEL                              0

    * Configures MIO Pin 46 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF1800B8, 0x000000FEU ,0x00000010U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_46_OFFSET, 0x000000FEU, 0x00000010U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_47 @ 0XFF1800BC

    * Level 0 Mux Select 0= Level 1 Mux Output 1= gem1, Input, gem1_rgmii_rxd[
    * 2]- (RX RGMII data)
    *  PSU_IOU_SLCR_MIO_PIN_47_L0_SEL                              0

    * Level 1 Mux Select 0= Level 2 Mux Output 1= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_47_L1_SEL                              0

    * Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Input, sd0_data_in[6]-
    * (8-bit Data bus) = sd0, Output, sdio0_data_out[6]- (8-bit Data bus) 2= s
    * d1, Input, sd1_data_in[1]- (8-bit Data bus) = sd1, Output, sdio1_data_ou
    * t[1]- (8-bit Data bus) 3= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_47_L2_SEL                              2

    * Level 3 Mux Select 0= gpio1, Input, gpio_1_pin_in[21]- (GPIO bank 1) 0=
    * gpio1, Output, gpio_1_pin_out[21]- (GPIO bank 1) 1= can0, Output, can0_p
    * hy_tx- (Can TX signal) 2= i2c0, Input, i2c0_sda_input- (SDA signal) 2= i
    * 2c0, Output, i2c0_sda_out- (SDA signal) 3= swdt0, Output, swdt0_rst_out-
    *  (Watch Dog Timer Output clock) 4= spi1, Input, spi1_n_ss_in- (SPI Maste
    * r Selects) 4= spi1, Output, spi1_n_ss_out[0]- (SPI Master Selects) 5= tt
    * c0, Output, ttc0_wave_out- (TTC Waveform Clock) 6= ua0, Output, ua0_txd-
    *  (UART transmitter serial output) 7= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_47_L3_SEL                              0

    * Configures MIO Pin 47 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF1800BC, 0x000000FEU ,0x00000010U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_47_OFFSET, 0x000000FEU, 0x00000010U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_48 @ 0XFF1800C0

    * Level 0 Mux Select 0= Level 1 Mux Output 1= gem1, Input, gem1_rgmii_rxd[
    * 3]- (RX RGMII data)
    *  PSU_IOU_SLCR_MIO_PIN_48_L0_SEL                              0

    * Level 1 Mux Select 0= Level 2 Mux Output 1= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_48_L1_SEL                              0

    * Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Input, sd0_data_in[7]-
    * (8-bit Data bus) = sd0, Output, sdio0_data_out[7]- (8-bit Data bus) 2= s
    * d1, Input, sd1_data_in[2]- (8-bit Data bus) = sd1, Output, sdio1_data_ou
    * t[2]- (8-bit Data bus) 3= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_48_L2_SEL                              2

    * Level 3 Mux Select 0= gpio1, Input, gpio_1_pin_in[22]- (GPIO bank 1) 0=
    * gpio1, Output, gpio_1_pin_out[22]- (GPIO bank 1) 1= can1, Output, can1_p
    * hy_tx- (Can TX signal) 2= i2c1, Input, i2c1_scl_input- (SCL signal) 2= i
    * 2c1, Output, i2c1_scl_out- (SCL signal) 3= swdt1, Input, swdt1_clk_in- (
    * Watch Dog Timer Input clock) 4= spi1, Input, spi1_mi- (MISO signal) 4= s
    * pi1, Output, spi1_so- (MISO signal) 5= ttc3, Input, ttc3_clk_in- (TTC Cl
    * ock) 6= ua1, Output, ua1_txd- (UART transmitter serial output) 7= Not Us
    * ed
    *  PSU_IOU_SLCR_MIO_PIN_48_L3_SEL                              0

    * Configures MIO Pin 48 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF1800C0, 0x000000FEU ,0x00000010U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_48_OFFSET, 0x000000FEU, 0x00000010U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_49 @ 0XFF1800C4

    * Level 0 Mux Select 0= Level 1 Mux Output 1= gem1, Input, gem1_rgmii_rx_c
    * tl- (RX RGMII control )
    *  PSU_IOU_SLCR_MIO_PIN_49_L0_SEL                              0

    * Level 1 Mux Select 0= Level 2 Mux Output 1= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_49_L1_SEL                              0

    * Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Output, sdio0_bus_pow-
    * (SD card bus power) 2= sd1, Input, sd1_data_in[3]- (8-bit Data bus) = sd
    * 1, Output, sdio1_data_out[3]- (8-bit Data bus) 3= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_49_L2_SEL                              2

    * Level 3 Mux Select 0= gpio1, Input, gpio_1_pin_in[23]- (GPIO bank 1) 0=
    * gpio1, Output, gpio_1_pin_out[23]- (GPIO bank 1) 1= can1, Input, can1_ph
    * y_rx- (Can RX signal) 2= i2c1, Input, i2c1_sda_input- (SDA signal) 2= i2
    * c1, Output, i2c1_sda_out- (SDA signal) 3= swdt1, Output, swdt1_rst_out-
    * (Watch Dog Timer Output clock) 4= spi1, Output, spi1_mo- (MOSI signal) 4
    * = spi1, Input, spi1_si- (MOSI signal) 5= ttc3, Output, ttc3_wave_out- (T
    * TC Waveform Clock) 6= ua1, Input, ua1_rxd- (UART receiver serial input)
    * 7= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_49_L3_SEL                              0

    * Configures MIO Pin 49 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF1800C4, 0x000000FEU ,0x00000010U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_49_OFFSET, 0x000000FEU, 0x00000010U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_50 @ 0XFF1800C8

    * Level 0 Mux Select 0= Level 1 Mux Output 1= gem_tsu, Input, gem_tsu_clk-
    *  (TSU clock)
    *  PSU_IOU_SLCR_MIO_PIN_50_L0_SEL                              0

    * Level 1 Mux Select 0= Level 2 Mux Output 1= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_50_L1_SEL                              0

    * Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Input, sdio0_wp- (SD ca
    * rd write protect from connector) 2= sd1, Input, sd1_cmd_in- (Command Ind
    * icator) = sd1, Output, sdio1_cmd_out- (Command Indicator) 3= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_50_L2_SEL                              2

    * Level 3 Mux Select 0= gpio1, Input, gpio_1_pin_in[24]- (GPIO bank 1) 0=
    * gpio1, Output, gpio_1_pin_out[24]- (GPIO bank 1) 1= can0, Input, can0_ph
    * y_rx- (Can RX signal) 2= i2c0, Input, i2c0_scl_input- (SCL signal) 2= i2
    * c0, Output, i2c0_scl_out- (SCL signal) 3= swdt0, Input, swdt0_clk_in- (W
    * atch Dog Timer Input clock) 4= mdio1, Output, gem1_mdc- (MDIO Clock) 5=
    * ttc2, Input, ttc2_clk_in- (TTC Clock) 6= ua0, Input, ua0_rxd- (UART rece
    * iver serial input) 7= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_50_L3_SEL                              0

    * Configures MIO Pin 50 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF1800C8, 0x000000FEU ,0x00000010U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_50_OFFSET, 0x000000FEU, 0x00000010U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_51 @ 0XFF1800CC

    * Level 0 Mux Select 0= Level 1 Mux Output 1= gem_tsu, Input, gem_tsu_clk-
    *  (TSU clock)
    *  PSU_IOU_SLCR_MIO_PIN_51_L0_SEL                              0

    * Level 1 Mux Select 0= Level 2 Mux Output 1= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_51_L1_SEL                              0

    * Level 2 Mux Select 0= Level 3 Mux Output 1= Not Used 2= sd1, Output, sdi
    * o1_clk_out- (SDSDIO clock) 3= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_51_L2_SEL                              2

    * Level 3 Mux Select 0= gpio1, Input, gpio_1_pin_in[25]- (GPIO bank 1) 0=
    * gpio1, Output, gpio_1_pin_out[25]- (GPIO bank 1) 1= can0, Output, can0_p
    * hy_tx- (Can TX signal) 2= i2c0, Input, i2c0_sda_input- (SDA signal) 2= i
    * 2c0, Output, i2c0_sda_out- (SDA signal) 3= swdt0, Output, swdt0_rst_out-
    *  (Watch Dog Timer Output clock) 4= mdio1, Input, gem1_mdio_in- (MDIO Dat
    * a) 4= mdio1, Output, gem1_mdio_out- (MDIO Data) 5= ttc2, Output, ttc2_wa
    * ve_out- (TTC Waveform Clock) 6= ua0, Output, ua0_txd- (UART transmitter
    * serial output) 7= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_51_L3_SEL                              0

    * Configures MIO Pin 51 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF1800CC, 0x000000FEU ,0x00000010U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_51_OFFSET, 0x000000FEU, 0x00000010U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_52 @ 0XFF1800D0

    * Level 0 Mux Select 0= Level 1 Mux Output 1= gem2, Output, gem2_rgmii_tx_
    * clk- (TX RGMII clock)
    *  PSU_IOU_SLCR_MIO_PIN_52_L0_SEL                              0

    * Level 1 Mux Select 0= Level 2 Mux Output 1= usb0, Input, usb0_ulpi_clk_i
    * n- (ULPI Clock)
    *  PSU_IOU_SLCR_MIO_PIN_52_L1_SEL                              1

    * Level 2 Mux Select 0= Level 3 Mux Output 1= Not Used 2= Not Used 3= Not
    * Used
    *  PSU_IOU_SLCR_MIO_PIN_52_L2_SEL                              0

    * Level 3 Mux Select 0= gpio2, Input, gpio_2_pin_in[0]- (GPIO bank 2) 0= g
    * pio2, Output, gpio_2_pin_out[0]- (GPIO bank 2) 1= can1, Output, can1_phy
    * _tx- (Can TX signal) 2= i2c1, Input, i2c1_scl_input- (SCL signal) 2= i2c
    * 1, Output, i2c1_scl_out- (SCL signal) 3= pjtag, Input, pjtag_tck- (PJTAG
    *  TCK) 4= spi0, Input, spi0_sclk_in- (SPI Clock) 4= spi0, Output, spi0_sc
    * lk_out- (SPI Clock) 5= ttc1, Input, ttc1_clk_in- (TTC Clock) 6= ua1, Out
    * put, ua1_txd- (UART transmitter serial output) 7= trace, Output, trace_c
    * lk- (Trace Port Clock)
    *  PSU_IOU_SLCR_MIO_PIN_52_L3_SEL                              0

    * Configures MIO Pin 52 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF1800D0, 0x000000FEU ,0x00000004U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_52_OFFSET, 0x000000FEU, 0x00000004U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_53 @ 0XFF1800D4

    * Level 0 Mux Select 0= Level 1 Mux Output 1= gem2, Output, gem2_rgmii_txd
    * [0]- (TX RGMII data)
    *  PSU_IOU_SLCR_MIO_PIN_53_L0_SEL                              0

    * Level 1 Mux Select 0= Level 2 Mux Output 1= usb0, Input, usb0_ulpi_dir-
    * (Data bus direction control)
    *  PSU_IOU_SLCR_MIO_PIN_53_L1_SEL                              1

    * Level 2 Mux Select 0= Level 3 Mux Output 1= Not Used 2= Not Used 3= Not
    * Used
    *  PSU_IOU_SLCR_MIO_PIN_53_L2_SEL                              0

    * Level 3 Mux Select 0= gpio2, Input, gpio_2_pin_in[1]- (GPIO bank 2) 0= g
    * pio2, Output, gpio_2_pin_out[1]- (GPIO bank 2) 1= can1, Input, can1_phy_
    * rx- (Can RX signal) 2= i2c1, Input, i2c1_sda_input- (SDA signal) 2= i2c1
    * , Output, i2c1_sda_out- (SDA signal) 3= pjtag, Input, pjtag_tdi- (PJTAG
    * TDI) 4= spi0, Output, spi0_n_ss_out[2]- (SPI Master Selects) 5= ttc1, Ou
    * tput, ttc1_wave_out- (TTC Waveform Clock) 6= ua1, Input, ua1_rxd- (UART
    * receiver serial input) 7= trace, Output, trace_ctl- (Trace Port Control
    * Signal)
    *  PSU_IOU_SLCR_MIO_PIN_53_L3_SEL                              0

    * Configures MIO Pin 53 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF1800D4, 0x000000FEU ,0x00000004U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_53_OFFSET, 0x000000FEU, 0x00000004U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_54 @ 0XFF1800D8

    * Level 0 Mux Select 0= Level 1 Mux Output 1= gem2, Output, gem2_rgmii_txd
    * [1]- (TX RGMII data)
    *  PSU_IOU_SLCR_MIO_PIN_54_L0_SEL                              0

    * Level 1 Mux Select 0= Level 2 Mux Output 1= usb0, Input, usb0_ulpi_rx_da
    * ta[2]- (ULPI data bus) 1= usb0, Output, usb0_ulpi_tx_data[2]- (ULPI data
    *  bus)
    *  PSU_IOU_SLCR_MIO_PIN_54_L1_SEL                              1

    * Level 2 Mux Select 0= Level 3 Mux Output 1= Not Used 2= Not Used 3= Not
    * Used
    *  PSU_IOU_SLCR_MIO_PIN_54_L2_SEL                              0

    * Level 3 Mux Select 0= gpio2, Input, gpio_2_pin_in[2]- (GPIO bank 2) 0= g
    * pio2, Output, gpio_2_pin_out[2]- (GPIO bank 2) 1= can0, Input, can0_phy_
    * rx- (Can RX signal) 2= i2c0, Input, i2c0_scl_input- (SCL signal) 2= i2c0
    * , Output, i2c0_scl_out- (SCL signal) 3= pjtag, Output, pjtag_tdo- (PJTAG
    *  TDO) 4= spi0, Output, spi0_n_ss_out[1]- (SPI Master Selects) 5= ttc0, I
    * nput, ttc0_clk_in- (TTC Clock) 6= ua0, Input, ua0_rxd- (UART receiver se
    * rial input) 7= trace, Output, tracedq[0]- (Trace Port Databus)
    *  PSU_IOU_SLCR_MIO_PIN_54_L3_SEL                              0

    * Configures MIO Pin 54 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF1800D8, 0x000000FEU ,0x00000004U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_54_OFFSET, 0x000000FEU, 0x00000004U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_55 @ 0XFF1800DC

    * Level 0 Mux Select 0= Level 1 Mux Output 1= gem2, Output, gem2_rgmii_txd
    * [2]- (TX RGMII data)
    *  PSU_IOU_SLCR_MIO_PIN_55_L0_SEL                              0

    * Level 1 Mux Select 0= Level 2 Mux Output 1= usb0, Input, usb0_ulpi_nxt-
    * (Data flow control signal from the PHY)
    *  PSU_IOU_SLCR_MIO_PIN_55_L1_SEL                              1

    * Level 2 Mux Select 0= Level 3 Mux Output 1= Not Used 2= Not Used 3= Not
    * Used
    *  PSU_IOU_SLCR_MIO_PIN_55_L2_SEL                              0

    * Level 3 Mux Select 0= gpio2, Input, gpio_2_pin_in[3]- (GPIO bank 2) 0= g
    * pio2, Output, gpio_2_pin_out[3]- (GPIO bank 2) 1= can0, Output, can0_phy
    * _tx- (Can TX signal) 2= i2c0, Input, i2c0_sda_input- (SDA signal) 2= i2c
    * 0, Output, i2c0_sda_out- (SDA signal) 3= pjtag, Input, pjtag_tms- (PJTAG
    *  TMS) 4= spi0, Input, spi0_n_ss_in- (SPI Master Selects) 4= spi0, Output
    * , spi0_n_ss_out[0]- (SPI Master Selects) 5= ttc0, Output, ttc0_wave_out-
    *  (TTC Waveform Clock) 6= ua0, Output, ua0_txd- (UART transmitter serial
    * output) 7= trace, Output, tracedq[1]- (Trace Port Databus)
    *  PSU_IOU_SLCR_MIO_PIN_55_L3_SEL                              0

    * Configures MIO Pin 55 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF1800DC, 0x000000FEU ,0x00000004U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_55_OFFSET, 0x000000FEU, 0x00000004U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_56 @ 0XFF1800E0

    * Level 0 Mux Select 0= Level 1 Mux Output 1= gem2, Output, gem2_rgmii_txd
    * [3]- (TX RGMII data)
    *  PSU_IOU_SLCR_MIO_PIN_56_L0_SEL                              0

    * Level 1 Mux Select 0= Level 2 Mux Output 1= usb0, Input, usb0_ulpi_rx_da
    * ta[0]- (ULPI data bus) 1= usb0, Output, usb0_ulpi_tx_data[0]- (ULPI data
    *  bus)
    *  PSU_IOU_SLCR_MIO_PIN_56_L1_SEL                              1

    * Level 2 Mux Select 0= Level 3 Mux Output 1= Not Used 2= Not Used 3= Not
    * Used
    *  PSU_IOU_SLCR_MIO_PIN_56_L2_SEL                              0

    * Level 3 Mux Select 0= gpio2, Input, gpio_2_pin_in[4]- (GPIO bank 2) 0= g
    * pio2, Output, gpio_2_pin_out[4]- (GPIO bank 2) 1= can1, Output, can1_phy
    * _tx- (Can TX signal) 2= i2c1, Input, i2c1_scl_input- (SCL signal) 2= i2c
    * 1, Output, i2c1_scl_out- (SCL signal) 3= swdt1, Input, swdt1_clk_in- (Wa
    * tch Dog Timer Input clock) 4= spi0, Input, spi0_mi- (MISO signal) 4= spi
    * 0, Output, spi0_so- (MISO signal) 5= ttc3, Input, ttc3_clk_in- (TTC Cloc
    * k) 6= ua1, Output, ua1_txd- (UART transmitter serial output) 7= trace, O
    * utput, tracedq[2]- (Trace Port Databus)
    *  PSU_IOU_SLCR_MIO_PIN_56_L3_SEL                              0

    * Configures MIO Pin 56 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF1800E0, 0x000000FEU ,0x00000004U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_56_OFFSET, 0x000000FEU, 0x00000004U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_57 @ 0XFF1800E4

    * Level 0 Mux Select 0= Level 1 Mux Output 1= gem2, Output, gem2_rgmii_tx_
    * ctl- (TX RGMII control)
    *  PSU_IOU_SLCR_MIO_PIN_57_L0_SEL                              0

    * Level 1 Mux Select 0= Level 2 Mux Output 1= usb0, Input, usb0_ulpi_rx_da
    * ta[1]- (ULPI data bus) 1= usb0, Output, usb0_ulpi_tx_data[1]- (ULPI data
    *  bus)
    *  PSU_IOU_SLCR_MIO_PIN_57_L1_SEL                              1

    * Level 2 Mux Select 0= Level 3 Mux Output 1= Not Used 2= Not Used 3= Not
    * Used
    *  PSU_IOU_SLCR_MIO_PIN_57_L2_SEL                              0

    * Level 3 Mux Select 0= gpio2, Input, gpio_2_pin_in[5]- (GPIO bank 2) 0= g
    * pio2, Output, gpio_2_pin_out[5]- (GPIO bank 2) 1= can1, Input, can1_phy_
    * rx- (Can RX signal) 2= i2c1, Input, i2c1_sda_input- (SDA signal) 2= i2c1
    * , Output, i2c1_sda_out- (SDA signal) 3= swdt1, Output, swdt1_rst_out- (W
    * atch Dog Timer Output clock) 4= spi0, Output, spi0_mo- (MOSI signal) 4=
    * spi0, Input, spi0_si- (MOSI signal) 5= ttc3, Output, ttc3_wave_out- (TTC
    *  Waveform Clock) 6= ua1, Input, ua1_rxd- (UART receiver serial input) 7=
    *  trace, Output, tracedq[3]- (Trace Port Databus)
    *  PSU_IOU_SLCR_MIO_PIN_57_L3_SEL                              0

    * Configures MIO Pin 57 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF1800E4, 0x000000FEU ,0x00000004U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_57_OFFSET, 0x000000FEU, 0x00000004U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_58 @ 0XFF1800E8

    * Level 0 Mux Select 0= Level 1 Mux Output 1= gem2, Input, gem2_rgmii_rx_c
    * lk- (RX RGMII clock)
    *  PSU_IOU_SLCR_MIO_PIN_58_L0_SEL                              0

    * Level 1 Mux Select 0= Level 2 Mux Output 1= usb0, Output, usb0_ulpi_stp-
    *  (Asserted to end or interrupt transfers)
    *  PSU_IOU_SLCR_MIO_PIN_58_L1_SEL                              1

    * Level 2 Mux Select 0= Level 3 Mux Output 1= Not Used 2= Not Used 3= Not
    * Used
    *  PSU_IOU_SLCR_MIO_PIN_58_L2_SEL                              0

    * Level 3 Mux Select 0= gpio2, Input, gpio_2_pin_in[6]- (GPIO bank 2) 0= g
    * pio2, Output, gpio_2_pin_out[6]- (GPIO bank 2) 1= can0, Input, can0_phy_
    * rx- (Can RX signal) 2= i2c0, Input, i2c0_scl_input- (SCL signal) 2= i2c0
    * , Output, i2c0_scl_out- (SCL signal) 3= pjtag, Input, pjtag_tck- (PJTAG
    * TCK) 4= spi1, Input, spi1_sclk_in- (SPI Clock) 4= spi1, Output, spi1_scl
    * k_out- (SPI Clock) 5= ttc2, Input, ttc2_clk_in- (TTC Clock) 6= ua0, Inpu
    * t, ua0_rxd- (UART receiver serial input) 7= trace, Output, tracedq[4]- (
    * Trace Port Databus)
    *  PSU_IOU_SLCR_MIO_PIN_58_L3_SEL                              0

    * Configures MIO Pin 58 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF1800E8, 0x000000FEU ,0x00000004U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_58_OFFSET, 0x000000FEU, 0x00000004U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_59 @ 0XFF1800EC

    * Level 0 Mux Select 0= Level 1 Mux Output 1= gem2, Input, gem2_rgmii_rxd[
    * 0]- (RX RGMII data)
    *  PSU_IOU_SLCR_MIO_PIN_59_L0_SEL                              0

    * Level 1 Mux Select 0= Level 2 Mux Output 1= usb0, Input, usb0_ulpi_rx_da
    * ta[3]- (ULPI data bus) 1= usb0, Output, usb0_ulpi_tx_data[3]- (ULPI data
    *  bus)
    *  PSU_IOU_SLCR_MIO_PIN_59_L1_SEL                              1

    * Level 2 Mux Select 0= Level 3 Mux Output 1= Not Used 2= Not Used 3= Not
    * Used
    *  PSU_IOU_SLCR_MIO_PIN_59_L2_SEL                              0

    * Level 3 Mux Select 0= gpio2, Input, gpio_2_pin_in[7]- (GPIO bank 2) 0= g
    * pio2, Output, gpio_2_pin_out[7]- (GPIO bank 2) 1= can0, Output, can0_phy
    * _tx- (Can TX signal) 2= i2c0, Input, i2c0_sda_input- (SDA signal) 2= i2c
    * 0, Output, i2c0_sda_out- (SDA signal) 3= pjtag, Input, pjtag_tdi- (PJTAG
    *  TDI) 4= spi1, Output, spi1_n_ss_out[2]- (SPI Master Selects) 5= ttc2, O
    * utput, ttc2_wave_out- (TTC Waveform Clock) 6= ua0, Output, ua0_txd- (UAR
    * T transmitter serial output) 7= trace, Output, tracedq[5]- (Trace Port D
    * atabus)
    *  PSU_IOU_SLCR_MIO_PIN_59_L3_SEL                              0

    * Configures MIO Pin 59 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF1800EC, 0x000000FEU ,0x00000004U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_59_OFFSET, 0x000000FEU, 0x00000004U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_60 @ 0XFF1800F0

    * Level 0 Mux Select 0= Level 1 Mux Output 1= gem2, Input, gem2_rgmii_rxd[
    * 1]- (RX RGMII data)
    *  PSU_IOU_SLCR_MIO_PIN_60_L0_SEL                              0

    * Level 1 Mux Select 0= Level 2 Mux Output 1= usb0, Input, usb0_ulpi_rx_da
    * ta[4]- (ULPI data bus) 1= usb0, Output, usb0_ulpi_tx_data[4]- (ULPI data
    *  bus)
    *  PSU_IOU_SLCR_MIO_PIN_60_L1_SEL                              1

    * Level 2 Mux Select 0= Level 3 Mux Output 1= Not Used 2= Not Used 3= Not
    * Used
    *  PSU_IOU_SLCR_MIO_PIN_60_L2_SEL                              0

    * Level 3 Mux Select 0= gpio2, Input, gpio_2_pin_in[8]- (GPIO bank 2) 0= g
    * pio2, Output, gpio_2_pin_out[8]- (GPIO bank 2) 1= can1, Output, can1_phy
    * _tx- (Can TX signal) 2= i2c1, Input, i2c1_scl_input- (SCL signal) 2= i2c
    * 1, Output, i2c1_scl_out- (SCL signal) 3= pjtag, Output, pjtag_tdo- (PJTA
    * G TDO) 4= spi1, Output, spi1_n_ss_out[1]- (SPI Master Selects) 5= ttc1,
    * Input, ttc1_clk_in- (TTC Clock) 6= ua1, Output, ua1_txd- (UART transmitt
    * er serial output) 7= trace, Output, tracedq[6]- (Trace Port Databus)
    *  PSU_IOU_SLCR_MIO_PIN_60_L3_SEL                              0

    * Configures MIO Pin 60 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF1800F0, 0x000000FEU ,0x00000004U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_60_OFFSET, 0x000000FEU, 0x00000004U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_61 @ 0XFF1800F4

    * Level 0 Mux Select 0= Level 1 Mux Output 1= gem2, Input, gem2_rgmii_rxd[
    * 2]- (RX RGMII data)
    *  PSU_IOU_SLCR_MIO_PIN_61_L0_SEL                              0

    * Level 1 Mux Select 0= Level 2 Mux Output 1= usb0, Input, usb0_ulpi_rx_da
    * ta[5]- (ULPI data bus) 1= usb0, Output, usb0_ulpi_tx_data[5]- (ULPI data
    *  bus)
    *  PSU_IOU_SLCR_MIO_PIN_61_L1_SEL                              1

    * Level 2 Mux Select 0= Level 3 Mux Output 1= Not Used 2= Not Used 3= Not
    * Used
    *  PSU_IOU_SLCR_MIO_PIN_61_L2_SEL                              0

    * Level 3 Mux Select 0= gpio2, Input, gpio_2_pin_in[9]- (GPIO bank 2) 0= g
    * pio2, Output, gpio_2_pin_out[9]- (GPIO bank 2) 1= can1, Input, can1_phy_
    * rx- (Can RX signal) 2= i2c1, Input, i2c1_sda_input- (SDA signal) 2= i2c1
    * , Output, i2c1_sda_out- (SDA signal) 3= pjtag, Input, pjtag_tms- (PJTAG
    * TMS) 4= spi1, Input, spi1_n_ss_in- (SPI Master Selects) 4= spi1, Output,
    *  spi1_n_ss_out[0]- (SPI Master Selects) 5= ttc1, Output, ttc1_wave_out-
    * (TTC Waveform Clock) 6= ua1, Input, ua1_rxd- (UART receiver serial input
    * ) 7= trace, Output, tracedq[7]- (Trace Port Databus)
    *  PSU_IOU_SLCR_MIO_PIN_61_L3_SEL                              0

    * Configures MIO Pin 61 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF1800F4, 0x000000FEU ,0x00000004U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_61_OFFSET, 0x000000FEU, 0x00000004U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_62 @ 0XFF1800F8

    * Level 0 Mux Select 0= Level 1 Mux Output 1= gem2, Input, gem2_rgmii_rxd[
    * 3]- (RX RGMII data)
    *  PSU_IOU_SLCR_MIO_PIN_62_L0_SEL                              0

    * Level 1 Mux Select 0= Level 2 Mux Output 1= usb0, Input, usb0_ulpi_rx_da
    * ta[6]- (ULPI data bus) 1= usb0, Output, usb0_ulpi_tx_data[6]- (ULPI data
    *  bus)
    *  PSU_IOU_SLCR_MIO_PIN_62_L1_SEL                              1

    * Level 2 Mux Select 0= Level 3 Mux Output 1= Not Used 2= Not Used 3= Not
    * Used
    *  PSU_IOU_SLCR_MIO_PIN_62_L2_SEL                              0

    * Level 3 Mux Select 0= gpio2, Input, gpio_2_pin_in[10]- (GPIO bank 2) 0=
    * gpio2, Output, gpio_2_pin_out[10]- (GPIO bank 2) 1= can0, Input, can0_ph
    * y_rx- (Can RX signal) 2= i2c0, Input, i2c0_scl_input- (SCL signal) 2= i2
    * c0, Output, i2c0_scl_out- (SCL signal) 3= swdt0, Input, swdt0_clk_in- (W
    * atch Dog Timer Input clock) 4= spi1, Input, spi1_mi- (MISO signal) 4= sp
    * i1, Output, spi1_so- (MISO signal) 5= ttc0, Input, ttc0_clk_in- (TTC Clo
    * ck) 6= ua0, Input, ua0_rxd- (UART receiver serial input) 7= trace, Outpu
    * t, tracedq[8]- (Trace Port Databus)
    *  PSU_IOU_SLCR_MIO_PIN_62_L3_SEL                              0

    * Configures MIO Pin 62 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF1800F8, 0x000000FEU ,0x00000004U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_62_OFFSET, 0x000000FEU, 0x00000004U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_63 @ 0XFF1800FC

    * Level 0 Mux Select 0= Level 1 Mux Output 1= gem2, Input, gem2_rgmii_rx_c
    * tl- (RX RGMII control )
    *  PSU_IOU_SLCR_MIO_PIN_63_L0_SEL                              0

    * Level 1 Mux Select 0= Level 2 Mux Output 1= usb0, Input, usb0_ulpi_rx_da
    * ta[7]- (ULPI data bus) 1= usb0, Output, usb0_ulpi_tx_data[7]- (ULPI data
    *  bus)
    *  PSU_IOU_SLCR_MIO_PIN_63_L1_SEL                              1

    * Level 2 Mux Select 0= Level 3 Mux Output 1= Not Used 2= Not Used 3= Not
    * Used
    *  PSU_IOU_SLCR_MIO_PIN_63_L2_SEL                              0

    * Level 3 Mux Select 0= gpio2, Input, gpio_2_pin_in[11]- (GPIO bank 2) 0=
    * gpio2, Output, gpio_2_pin_out[11]- (GPIO bank 2) 1= can0, Output, can0_p
    * hy_tx- (Can TX signal) 2= i2c0, Input, i2c0_sda_input- (SDA signal) 2= i
    * 2c0, Output, i2c0_sda_out- (SDA signal) 3= swdt0, Output, swdt0_rst_out-
    *  (Watch Dog Timer Output clock) 4= spi1, Output, spi1_mo- (MOSI signal)
    * 4= spi1, Input, spi1_si- (MOSI signal) 5= ttc0, Output, ttc0_wave_out- (
    * TTC Waveform Clock) 6= ua0, Output, ua0_txd- (UART transmitter serial ou
    * tput) 7= trace, Output, tracedq[9]- (Trace Port Databus)
    *  PSU_IOU_SLCR_MIO_PIN_63_L3_SEL                              0

    * Configures MIO Pin 63 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF1800FC, 0x000000FEU ,0x00000004U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_63_OFFSET, 0x000000FEU, 0x00000004U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_64 @ 0XFF180100

    * Level 0 Mux Select 0= Level 1 Mux Output 1= gem3, Output, gem3_rgmii_tx_
    * clk- (TX RGMII clock)
    *  PSU_IOU_SLCR_MIO_PIN_64_L0_SEL                              1

    * Level 1 Mux Select 0= Level 2 Mux Output 1= usb1, Input, usb1_ulpi_clk_i
    * n- (ULPI Clock)
    *  PSU_IOU_SLCR_MIO_PIN_64_L1_SEL                              0

    * Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Output, sdio0_clk_out-
    * (SDSDIO clock) 2= Not Used 3= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_64_L2_SEL                              0

    * Level 3 Mux Select 0= gpio2, Input, gpio_2_pin_in[12]- (GPIO bank 2) 0=
    * gpio2, Output, gpio_2_pin_out[12]- (GPIO bank 2) 1= can1, Output, can1_p
    * hy_tx- (Can TX signal) 2= i2c1, Input, i2c1_scl_input- (SCL signal) 2= i
    * 2c1, Output, i2c1_scl_out- (SCL signal) 3= swdt1, Input, swdt1_clk_in- (
    * Watch Dog Timer Input clock) 4= spi0, Input, spi0_sclk_in- (SPI Clock) 4
    * = spi0, Output, spi0_sclk_out- (SPI Clock) 5= ttc3, Input, ttc3_clk_in-
    * (TTC Clock) 6= ua1, Output, ua1_txd- (UART transmitter serial output) 7=
    *  trace, Output, tracedq[10]- (Trace Port Databus)
    *  PSU_IOU_SLCR_MIO_PIN_64_L3_SEL                              0

    * Configures MIO Pin 64 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF180100, 0x000000FEU ,0x00000002U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_64_OFFSET, 0x000000FEU, 0x00000002U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_65 @ 0XFF180104

    * Level 0 Mux Select 0= Level 1 Mux Output 1= gem3, Output, gem3_rgmii_txd
    * [0]- (TX RGMII data)
    *  PSU_IOU_SLCR_MIO_PIN_65_L0_SEL                              1

    * Level 1 Mux Select 0= Level 2 Mux Output 1= usb1, Input, usb1_ulpi_dir-
    * (Data bus direction control)
    *  PSU_IOU_SLCR_MIO_PIN_65_L1_SEL                              0

    * Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Input, sdio0_cd_n- (SD
    * card detect from connector) 2= Not Used 3= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_65_L2_SEL                              0

    * Level 3 Mux Select 0= gpio2, Input, gpio_2_pin_in[13]- (GPIO bank 2) 0=
    * gpio2, Output, gpio_2_pin_out[13]- (GPIO bank 2) 1= can1, Input, can1_ph
    * y_rx- (Can RX signal) 2= i2c1, Input, i2c1_sda_input- (SDA signal) 2= i2
    * c1, Output, i2c1_sda_out- (SDA signal) 3= swdt1, Output, swdt1_rst_out-
    * (Watch Dog Timer Output clock) 4= spi0, Output, spi0_n_ss_out[2]- (SPI M
    * aster Selects) 5= ttc3, Output, ttc3_wave_out- (TTC Waveform Clock) 6= u
    * a1, Input, ua1_rxd- (UART receiver serial input) 7= trace, Output, trace
    * dq[11]- (Trace Port Databus)
    *  PSU_IOU_SLCR_MIO_PIN_65_L3_SEL                              0

    * Configures MIO Pin 65 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF180104, 0x000000FEU ,0x00000002U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_65_OFFSET, 0x000000FEU, 0x00000002U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_66 @ 0XFF180108

    * Level 0 Mux Select 0= Level 1 Mux Output 1= gem3, Output, gem3_rgmii_txd
    * [1]- (TX RGMII data)
    *  PSU_IOU_SLCR_MIO_PIN_66_L0_SEL                              1

    * Level 1 Mux Select 0= Level 2 Mux Output 1= usb1, Input, usb1_ulpi_rx_da
    * ta[2]- (ULPI data bus) 1= usb1, Output, usb1_ulpi_tx_data[2]- (ULPI data
    *  bus)
    *  PSU_IOU_SLCR_MIO_PIN_66_L1_SEL                              0

    * Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Input, sd0_cmd_in- (Com
    * mand Indicator) = sd0, Output, sdio0_cmd_out- (Command Indicator) 2= Not
    *  Used 3= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_66_L2_SEL                              0

    * Level 3 Mux Select 0= gpio2, Input, gpio_2_pin_in[14]- (GPIO bank 2) 0=
    * gpio2, Output, gpio_2_pin_out[14]- (GPIO bank 2) 1= can0, Input, can0_ph
    * y_rx- (Can RX signal) 2= i2c0, Input, i2c0_scl_input- (SCL signal) 2= i2
    * c0, Output, i2c0_scl_out- (SCL signal) 3= swdt0, Input, swdt0_clk_in- (W
    * atch Dog Timer Input clock) 4= spi0, Output, spi0_n_ss_out[1]- (SPI Mast
    * er Selects) 5= ttc2, Input, ttc2_clk_in- (TTC Clock) 6= ua0, Input, ua0_
    * rxd- (UART receiver serial input) 7= trace, Output, tracedq[12]- (Trace
    * Port Databus)
    *  PSU_IOU_SLCR_MIO_PIN_66_L3_SEL                              0

    * Configures MIO Pin 66 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF180108, 0x000000FEU ,0x00000002U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_66_OFFSET, 0x000000FEU, 0x00000002U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_67 @ 0XFF18010C

    * Level 0 Mux Select 0= Level 1 Mux Output 1= gem3, Output, gem3_rgmii_txd
    * [2]- (TX RGMII data)
    *  PSU_IOU_SLCR_MIO_PIN_67_L0_SEL                              1

    * Level 1 Mux Select 0= Level 2 Mux Output 1= usb1, Input, usb1_ulpi_nxt-
    * (Data flow control signal from the PHY)
    *  PSU_IOU_SLCR_MIO_PIN_67_L1_SEL                              0

    * Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Input, sd0_data_in[0]-
    * (8-bit Data bus) = sd0, Output, sdio0_data_out[0]- (8-bit Data bus) 2= N
    * ot Used 3= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_67_L2_SEL                              0

    * Level 3 Mux Select 0= gpio2, Input, gpio_2_pin_in[15]- (GPIO bank 2) 0=
    * gpio2, Output, gpio_2_pin_out[15]- (GPIO bank 2) 1= can0, Output, can0_p
    * hy_tx- (Can TX signal) 2= i2c0, Input, i2c0_sda_input- (SDA signal) 2= i
    * 2c0, Output, i2c0_sda_out- (SDA signal) 3= swdt0, Output, swdt0_rst_out-
    *  (Watch Dog Timer Output clock) 4= spi0, Input, spi0_n_ss_in- (SPI Maste
    * r Selects) 4= spi0, Output, spi0_n_ss_out[0]- (SPI Master Selects) 5= tt
    * c2, Output, ttc2_wave_out- (TTC Waveform Clock) 6= ua0, Output, ua0_txd-
    *  (UART transmitter serial output) 7= trace, Output, tracedq[13]- (Trace
    * Port Databus)
    *  PSU_IOU_SLCR_MIO_PIN_67_L3_SEL                              0

    * Configures MIO Pin 67 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF18010C, 0x000000FEU ,0x00000002U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_67_OFFSET, 0x000000FEU, 0x00000002U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_68 @ 0XFF180110

    * Level 0 Mux Select 0= Level 1 Mux Output 1= gem3, Output, gem3_rgmii_txd
    * [3]- (TX RGMII data)
    *  PSU_IOU_SLCR_MIO_PIN_68_L0_SEL                              1

    * Level 1 Mux Select 0= Level 2 Mux Output 1= usb1, Input, usb1_ulpi_rx_da
    * ta[0]- (ULPI data bus) 1= usb1, Output, usb1_ulpi_tx_data[0]- (ULPI data
    *  bus)
    *  PSU_IOU_SLCR_MIO_PIN_68_L1_SEL                              0

    * Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Input, sd0_data_in[1]-
    * (8-bit Data bus) = sd0, Output, sdio0_data_out[1]- (8-bit Data bus) 2= N
    * ot Used 3= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_68_L2_SEL                              0

    * Level 3 Mux Select 0= gpio2, Input, gpio_2_pin_in[16]- (GPIO bank 2) 0=
    * gpio2, Output, gpio_2_pin_out[16]- (GPIO bank 2) 1= can1, Output, can1_p
    * hy_tx- (Can TX signal) 2= i2c1, Input, i2c1_scl_input- (SCL signal) 2= i
    * 2c1, Output, i2c1_scl_out- (SCL signal) 3= swdt1, Input, swdt1_clk_in- (
    * Watch Dog Timer Input clock) 4= spi0, Input, spi0_mi- (MISO signal) 4= s
    * pi0, Output, spi0_so- (MISO signal) 5= ttc1, Input, ttc1_clk_in- (TTC Cl
    * ock) 6= ua1, Output, ua1_txd- (UART transmitter serial output) 7= trace,
    *  Output, tracedq[14]- (Trace Port Databus)
    *  PSU_IOU_SLCR_MIO_PIN_68_L3_SEL                              0

    * Configures MIO Pin 68 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF180110, 0x000000FEU ,0x00000002U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_68_OFFSET, 0x000000FEU, 0x00000002U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_69 @ 0XFF180114

    * Level 0 Mux Select 0= Level 1 Mux Output 1= gem3, Output, gem3_rgmii_tx_
    * ctl- (TX RGMII control)
    *  PSU_IOU_SLCR_MIO_PIN_69_L0_SEL                              1

    * Level 1 Mux Select 0= Level 2 Mux Output 1= usb1, Input, usb1_ulpi_rx_da
    * ta[1]- (ULPI data bus) 1= usb1, Output, usb1_ulpi_tx_data[1]- (ULPI data
    *  bus)
    *  PSU_IOU_SLCR_MIO_PIN_69_L1_SEL                              0

    * Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Input, sd0_data_in[2]-
    * (8-bit Data bus) = sd0, Output, sdio0_data_out[2]- (8-bit Data bus) 2= s
    * d1, Input, sdio1_wp- (SD card write protect from connector) 3= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_69_L2_SEL                              0

    * Level 3 Mux Select 0= gpio2, Input, gpio_2_pin_in[17]- (GPIO bank 2) 0=
    * gpio2, Output, gpio_2_pin_out[17]- (GPIO bank 2) 1= can1, Input, can1_ph
    * y_rx- (Can RX signal) 2= i2c1, Input, i2c1_sda_input- (SDA signal) 2= i2
    * c1, Output, i2c1_sda_out- (SDA signal) 3= swdt1, Output, swdt1_rst_out-
    * (Watch Dog Timer Output clock) 4= spi0, Output, spi0_mo- (MOSI signal) 4
    * = spi0, Input, spi0_si- (MOSI signal) 5= ttc1, Output, ttc1_wave_out- (T
    * TC Waveform Clock) 6= ua1, Input, ua1_rxd- (UART receiver serial input)
    * 7= trace, Output, tracedq[15]- (Trace Port Databus)
    *  PSU_IOU_SLCR_MIO_PIN_69_L3_SEL                              0

    * Configures MIO Pin 69 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF180114, 0x000000FEU ,0x00000002U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_69_OFFSET, 0x000000FEU, 0x00000002U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_70 @ 0XFF180118

    * Level 0 Mux Select 0= Level 1 Mux Output 1= gem3, Input, gem3_rgmii_rx_c
    * lk- (RX RGMII clock)
    *  PSU_IOU_SLCR_MIO_PIN_70_L0_SEL                              1

    * Level 1 Mux Select 0= Level 2 Mux Output 1= usb1, Output, usb1_ulpi_stp-
    *  (Asserted to end or interrupt transfers)
    *  PSU_IOU_SLCR_MIO_PIN_70_L1_SEL                              0

    * Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Input, sd0_data_in[3]-
    * (8-bit Data bus) = sd0, Output, sdio0_data_out[3]- (8-bit Data bus) 2= s
    * d1, Output, sdio1_bus_pow- (SD card bus power) 3= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_70_L2_SEL                              0

    * Level 3 Mux Select 0= gpio2, Input, gpio_2_pin_in[18]- (GPIO bank 2) 0=
    * gpio2, Output, gpio_2_pin_out[18]- (GPIO bank 2) 1= can0, Input, can0_ph
    * y_rx- (Can RX signal) 2= i2c0, Input, i2c0_scl_input- (SCL signal) 2= i2
    * c0, Output, i2c0_scl_out- (SCL signal) 3= swdt0, Input, swdt0_clk_in- (W
    * atch Dog Timer Input clock) 4= spi1, Input, spi1_sclk_in- (SPI Clock) 4=
    *  spi1, Output, spi1_sclk_out- (SPI Clock) 5= ttc0, Input, ttc0_clk_in- (
    * TTC Clock) 6= ua0, Input, ua0_rxd- (UART receiver serial input) 7= Not U
    * sed
    *  PSU_IOU_SLCR_MIO_PIN_70_L3_SEL                              0

    * Configures MIO Pin 70 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF180118, 0x000000FEU ,0x00000002U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_70_OFFSET, 0x000000FEU, 0x00000002U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_71 @ 0XFF18011C

    * Level 0 Mux Select 0= Level 1 Mux Output 1= gem3, Input, gem3_rgmii_rxd[
    * 0]- (RX RGMII data)
    *  PSU_IOU_SLCR_MIO_PIN_71_L0_SEL                              1

    * Level 1 Mux Select 0= Level 2 Mux Output 1= usb1, Input, usb1_ulpi_rx_da
    * ta[3]- (ULPI data bus) 1= usb1, Output, usb1_ulpi_tx_data[3]- (ULPI data
    *  bus)
    *  PSU_IOU_SLCR_MIO_PIN_71_L1_SEL                              0

    * Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Input, sd0_data_in[4]-
    * (8-bit Data bus) = sd0, Output, sdio0_data_out[4]- (8-bit Data bus) 2= s
    * d1, Input, sd1_data_in[0]- (8-bit Data bus) = sd1, Output, sdio1_data_ou
    * t[0]- (8-bit Data bus) 3= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_71_L2_SEL                              0

    * Level 3 Mux Select 0= gpio2, Input, gpio_2_pin_in[19]- (GPIO bank 2) 0=
    * gpio2, Output, gpio_2_pin_out[19]- (GPIO bank 2) 1= can0, Output, can0_p
    * hy_tx- (Can TX signal) 2= i2c0, Input, i2c0_sda_input- (SDA signal) 2= i
    * 2c0, Output, i2c0_sda_out- (SDA signal) 3= swdt0, Output, swdt0_rst_out-
    *  (Watch Dog Timer Output clock) 4= spi1, Output, spi1_n_ss_out[2]- (SPI
    * Master Selects) 5= ttc0, Output, ttc0_wave_out- (TTC Waveform Clock) 6=
    * ua0, Output, ua0_txd- (UART transmitter serial output) 7= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_71_L3_SEL                              0

    * Configures MIO Pin 71 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF18011C, 0x000000FEU ,0x00000002U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_71_OFFSET, 0x000000FEU, 0x00000002U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_72 @ 0XFF180120

    * Level 0 Mux Select 0= Level 1 Mux Output 1= gem3, Input, gem3_rgmii_rxd[
    * 1]- (RX RGMII data)
    *  PSU_IOU_SLCR_MIO_PIN_72_L0_SEL                              1

    * Level 1 Mux Select 0= Level 2 Mux Output 1= usb1, Input, usb1_ulpi_rx_da
    * ta[4]- (ULPI data bus) 1= usb1, Output, usb1_ulpi_tx_data[4]- (ULPI data
    *  bus)
    *  PSU_IOU_SLCR_MIO_PIN_72_L1_SEL                              0

    * Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Input, sd0_data_in[5]-
    * (8-bit Data bus) = sd0, Output, sdio0_data_out[5]- (8-bit Data bus) 2= s
    * d1, Input, sd1_data_in[1]- (8-bit Data bus) = sd1, Output, sdio1_data_ou
    * t[1]- (8-bit Data bus) 3= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_72_L2_SEL                              0

    * Level 3 Mux Select 0= gpio2, Input, gpio_2_pin_in[20]- (GPIO bank 2) 0=
    * gpio2, Output, gpio_2_pin_out[20]- (GPIO bank 2) 1= can1, Output, can1_p
    * hy_tx- (Can TX signal) 2= i2c1, Input, i2c1_scl_input- (SCL signal) 2= i
    * 2c1, Output, i2c1_scl_out- (SCL signal) 3= swdt1, Input, swdt1_clk_in- (
    * Watch Dog Timer Input clock) 4= spi1, Output, spi1_n_ss_out[1]- (SPI Mas
    * ter Selects) 5= Not Used 6= ua1, Output, ua1_txd- (UART transmitter seri
    * al output) 7= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_72_L3_SEL                              0

    * Configures MIO Pin 72 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF180120, 0x000000FEU ,0x00000002U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_72_OFFSET, 0x000000FEU, 0x00000002U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_73 @ 0XFF180124

    * Level 0 Mux Select 0= Level 1 Mux Output 1= gem3, Input, gem3_rgmii_rxd[
    * 2]- (RX RGMII data)
    *  PSU_IOU_SLCR_MIO_PIN_73_L0_SEL                              1

    * Level 1 Mux Select 0= Level 2 Mux Output 1= usb1, Input, usb1_ulpi_rx_da
    * ta[5]- (ULPI data bus) 1= usb1, Output, usb1_ulpi_tx_data[5]- (ULPI data
    *  bus)
    *  PSU_IOU_SLCR_MIO_PIN_73_L1_SEL                              0

    * Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Input, sd0_data_in[6]-
    * (8-bit Data bus) = sd0, Output, sdio0_data_out[6]- (8-bit Data bus) 2= s
    * d1, Input, sd1_data_in[2]- (8-bit Data bus) = sd1, Output, sdio1_data_ou
    * t[2]- (8-bit Data bus) 3= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_73_L2_SEL                              0

    * Level 3 Mux Select 0= gpio2, Input, gpio_2_pin_in[21]- (GPIO bank 2) 0=
    * gpio2, Output, gpio_2_pin_out[21]- (GPIO bank 2) 1= can1, Input, can1_ph
    * y_rx- (Can RX signal) 2= i2c1, Input, i2c1_sda_input- (SDA signal) 2= i2
    * c1, Output, i2c1_sda_out- (SDA signal) 3= swdt1, Output, swdt1_rst_out-
    * (Watch Dog Timer Output clock) 4= spi1, Input, spi1_n_ss_in- (SPI Master
    *  Selects) 4= spi1, Output, spi1_n_ss_out[0]- (SPI Master Selects) 5= Not
    *  Used 6= ua1, Input, ua1_rxd- (UART receiver serial input) 7= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_73_L3_SEL                              0

    * Configures MIO Pin 73 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF180124, 0x000000FEU ,0x00000002U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_73_OFFSET, 0x000000FEU, 0x00000002U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_74 @ 0XFF180128

    * Level 0 Mux Select 0= Level 1 Mux Output 1= gem3, Input, gem3_rgmii_rxd[
    * 3]- (RX RGMII data)
    *  PSU_IOU_SLCR_MIO_PIN_74_L0_SEL                              1

    * Level 1 Mux Select 0= Level 2 Mux Output 1= usb1, Input, usb1_ulpi_rx_da
    * ta[6]- (ULPI data bus) 1= usb1, Output, usb1_ulpi_tx_data[6]- (ULPI data
    *  bus)
    *  PSU_IOU_SLCR_MIO_PIN_74_L1_SEL                              0

    * Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Input, sd0_data_in[7]-
    * (8-bit Data bus) = sd0, Output, sdio0_data_out[7]- (8-bit Data bus) 2= s
    * d1, Input, sd1_data_in[3]- (8-bit Data bus) = sd1, Output, sdio1_data_ou
    * t[3]- (8-bit Data bus) 3= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_74_L2_SEL                              0

    * Level 3 Mux Select 0= gpio2, Input, gpio_2_pin_in[22]- (GPIO bank 2) 0=
    * gpio2, Output, gpio_2_pin_out[22]- (GPIO bank 2) 1= can0, Input, can0_ph
    * y_rx- (Can RX signal) 2= i2c0, Input, i2c0_scl_input- (SCL signal) 2= i2
    * c0, Output, i2c0_scl_out- (SCL signal) 3= swdt0, Input, swdt0_clk_in- (W
    * atch Dog Timer Input clock) 4= spi1, Input, spi1_mi- (MISO signal) 4= sp
    * i1, Output, spi1_so- (MISO signal) 5= Not Used 6= ua0, Input, ua0_rxd- (
    * UART receiver serial input) 7= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_74_L3_SEL                              0

    * Configures MIO Pin 74 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF180128, 0x000000FEU ,0x00000002U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_74_OFFSET, 0x000000FEU, 0x00000002U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_75 @ 0XFF18012C

    * Level 0 Mux Select 0= Level 1 Mux Output 1= gem3, Input, gem3_rgmii_rx_c
    * tl- (RX RGMII control )
    *  PSU_IOU_SLCR_MIO_PIN_75_L0_SEL                              1

    * Level 1 Mux Select 0= Level 2 Mux Output 1= usb1, Input, usb1_ulpi_rx_da
    * ta[7]- (ULPI data bus) 1= usb1, Output, usb1_ulpi_tx_data[7]- (ULPI data
    *  bus)
    *  PSU_IOU_SLCR_MIO_PIN_75_L1_SEL                              0

    * Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Output, sdio0_bus_pow-
    * (SD card bus power) 2= sd1, Input, sd1_cmd_in- (Command Indicator) = sd1
    * , Output, sdio1_cmd_out- (Command Indicator) 3= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_75_L2_SEL                              0

    * Level 3 Mux Select 0= gpio2, Input, gpio_2_pin_in[23]- (GPIO bank 2) 0=
    * gpio2, Output, gpio_2_pin_out[23]- (GPIO bank 2) 1= can0, Output, can0_p
    * hy_tx- (Can TX signal) 2= i2c0, Input, i2c0_sda_input- (SDA signal) 2= i
    * 2c0, Output, i2c0_sda_out- (SDA signal) 3= swdt0, Output, swdt0_rst_out-
    *  (Watch Dog Timer Output clock) 4= spi1, Output, spi1_mo- (MOSI signal)
    * 4= spi1, Input, spi1_si- (MOSI signal) 5= Not Used 6= ua0, Output, ua0_t
    * xd- (UART transmitter serial output) 7= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_75_L3_SEL                              0

    * Configures MIO Pin 75 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF18012C, 0x000000FEU ,0x00000002U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_75_OFFSET, 0x000000FEU, 0x00000002U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_76 @ 0XFF180130

    * Level 0 Mux Select 0= Level 1 Mux Output 1= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_76_L0_SEL                              0

    * Level 1 Mux Select 0= Level 2 Mux Output 1= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_76_L1_SEL                              0

    * Level 2 Mux Select 0= Level 3 Mux Output 1= sd0, Input, sdio0_wp- (SD ca
    * rd write protect from connector) 2= sd1, Output, sdio1_clk_out- (SDSDIO
    * clock) 3= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_76_L2_SEL                              0

    * Level 3 Mux Select 0= gpio2, Input, gpio_2_pin_in[24]- (GPIO bank 2) 0=
    * gpio2, Output, gpio_2_pin_out[24]- (GPIO bank 2) 1= can1, Output, can1_p
    * hy_tx- (Can TX signal) 2= i2c1, Input, i2c1_scl_input- (SCL signal) 2= i
    * 2c1, Output, i2c1_scl_out- (SCL signal) 3= mdio0, Output, gem0_mdc- (MDI
    * O Clock) 4= mdio1, Output, gem1_mdc- (MDIO Clock) 5= mdio2, Output, gem2
    * _mdc- (MDIO Clock) 6= mdio3, Output, gem3_mdc- (MDIO Clock) 7= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_76_L3_SEL                              6

    * Configures MIO Pin 76 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF180130, 0x000000FEU ,0x000000C0U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_76_OFFSET, 0x000000FEU, 0x000000C0U);
/*##################################################################### */

    /*
    * Register : MIO_PIN_77 @ 0XFF180134

    * Level 0 Mux Select 0= Level 1 Mux Output 1= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_77_L0_SEL                              0

    * Level 1 Mux Select 0= Level 2 Mux Output 1= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_77_L1_SEL                              0

    * Level 2 Mux Select 0= Level 3 Mux Output 1= Not Used 2= sd1, Input, sdio
    * 1_cd_n- (SD card detect from connector) 3= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_77_L2_SEL                              0

    * Level 3 Mux Select 0= gpio2, Input, gpio_2_pin_in[25]- (GPIO bank 2) 0=
    * gpio2, Output, gpio_2_pin_out[25]- (GPIO bank 2) 1= can1, Input, can1_ph
    * y_rx- (Can RX signal) 2= i2c1, Input, i2c1_sda_input- (SDA signal) 2= i2
    * c1, Output, i2c1_sda_out- (SDA signal) 3= mdio0, Input, gem0_mdio_in- (M
    * DIO Data) 3= mdio0, Output, gem0_mdio_out- (MDIO Data) 4= mdio1, Input,
    * gem1_mdio_in- (MDIO Data) 4= mdio1, Output, gem1_mdio_out- (MDIO Data) 5
    * = mdio2, Input, gem2_mdio_in- (MDIO Data) 5= mdio2, Output, gem2_mdio_ou
    * t- (MDIO Data) 6= mdio3, Input, gem3_mdio_in- (MDIO Data) 6= mdio3, Outp
    * ut, gem3_mdio_out- (MDIO Data) 7= Not Used
    *  PSU_IOU_SLCR_MIO_PIN_77_L3_SEL                              6

    * Configures MIO Pin 77 peripheral interface mapping
    * (OFFSET, MASK, VALUE)      (0XFF180134, 0x000000FEU ,0x000000C0U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_PIN_77_OFFSET, 0x000000FEU, 0x000000C0U);
/*##################################################################### */

    /*
    * Register : MIO_MST_TRI0 @ 0XFF180204

    * Master Tri-state Enable for pin 0, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI0_PIN_00_TRI                        0

    * Master Tri-state Enable for pin 1, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI0_PIN_01_TRI                        0

    * Master Tri-state Enable for pin 2, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI0_PIN_02_TRI                        0

    * Master Tri-state Enable for pin 3, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI0_PIN_03_TRI                        0

    * Master Tri-state Enable for pin 4, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI0_PIN_04_TRI                        0

    * Master Tri-state Enable for pin 5, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI0_PIN_05_TRI                        0

    * Master Tri-state Enable for pin 6, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI0_PIN_06_TRI                        0

    * Master Tri-state Enable for pin 7, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI0_PIN_07_TRI                        0

    * Master Tri-state Enable for pin 8, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI0_PIN_08_TRI                        0

    * Master Tri-state Enable for pin 9, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI0_PIN_09_TRI                        0

    * Master Tri-state Enable for pin 10, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI0_PIN_10_TRI                        0

    * Master Tri-state Enable for pin 11, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI0_PIN_11_TRI                        0

    * Master Tri-state Enable for pin 12, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI0_PIN_12_TRI                        0

    * Master Tri-state Enable for pin 13, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI0_PIN_13_TRI                        0

    * Master Tri-state Enable for pin 14, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI0_PIN_14_TRI                        0

    * Master Tri-state Enable for pin 15, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI0_PIN_15_TRI                        0

    * Master Tri-state Enable for pin 16, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI0_PIN_16_TRI                        0

    * Master Tri-state Enable for pin 17, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI0_PIN_17_TRI                        0

    * Master Tri-state Enable for pin 18, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI0_PIN_18_TRI                        1

    * Master Tri-state Enable for pin 19, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI0_PIN_19_TRI                        0

    * Master Tri-state Enable for pin 20, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI0_PIN_20_TRI                        0

    * Master Tri-state Enable for pin 21, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI0_PIN_21_TRI                        1

    * Master Tri-state Enable for pin 22, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI0_PIN_22_TRI                        0

    * Master Tri-state Enable for pin 23, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI0_PIN_23_TRI                        0

    * Master Tri-state Enable for pin 24, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI0_PIN_24_TRI                        0

    * Master Tri-state Enable for pin 25, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI0_PIN_25_TRI                        1

    * Master Tri-state Enable for pin 26, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI0_PIN_26_TRI                        0

    * Master Tri-state Enable for pin 27, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI0_PIN_27_TRI                        0

    * Master Tri-state Enable for pin 28, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI0_PIN_28_TRI                        1

    * Master Tri-state Enable for pin 29, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI0_PIN_29_TRI                        0

    * Master Tri-state Enable for pin 30, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI0_PIN_30_TRI                        1

    * Master Tri-state Enable for pin 31, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI0_PIN_31_TRI                        0

    * MIO pin Tri-state Enables, 31:0
    * (OFFSET, MASK, VALUE)      (0XFF180204, 0xFFFFFFFFU ,0x52240000U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_MST_TRI0_OFFSET,
		0xFFFFFFFFU, 0x52240000U);
/*##################################################################### */

    /*
    * Register : MIO_MST_TRI1 @ 0XFF180208

    * Master Tri-state Enable for pin 32, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI1_PIN_32_TRI                        0

    * Master Tri-state Enable for pin 33, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI1_PIN_33_TRI                        0

    * Master Tri-state Enable for pin 34, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI1_PIN_34_TRI                        0

    * Master Tri-state Enable for pin 35, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI1_PIN_35_TRI                        0

    * Master Tri-state Enable for pin 36, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI1_PIN_36_TRI                        0

    * Master Tri-state Enable for pin 37, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI1_PIN_37_TRI                        0

    * Master Tri-state Enable for pin 38, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI1_PIN_38_TRI                        0

    * Master Tri-state Enable for pin 39, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI1_PIN_39_TRI                        0

    * Master Tri-state Enable for pin 40, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI1_PIN_40_TRI                        0

    * Master Tri-state Enable for pin 41, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI1_PIN_41_TRI                        0

    * Master Tri-state Enable for pin 42, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI1_PIN_42_TRI                        0

    * Master Tri-state Enable for pin 43, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI1_PIN_43_TRI                        0

    * Master Tri-state Enable for pin 44, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI1_PIN_44_TRI                        1

    * Master Tri-state Enable for pin 45, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI1_PIN_45_TRI                        1

    * Master Tri-state Enable for pin 46, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI1_PIN_46_TRI                        0

    * Master Tri-state Enable for pin 47, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI1_PIN_47_TRI                        0

    * Master Tri-state Enable for pin 48, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI1_PIN_48_TRI                        0

    * Master Tri-state Enable for pin 49, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI1_PIN_49_TRI                        0

    * Master Tri-state Enable for pin 50, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI1_PIN_50_TRI                        0

    * Master Tri-state Enable for pin 51, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI1_PIN_51_TRI                        0

    * Master Tri-state Enable for pin 52, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI1_PIN_52_TRI                        1

    * Master Tri-state Enable for pin 53, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI1_PIN_53_TRI                        1

    * Master Tri-state Enable for pin 54, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI1_PIN_54_TRI                        0

    * Master Tri-state Enable for pin 55, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI1_PIN_55_TRI                        1

    * Master Tri-state Enable for pin 56, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI1_PIN_56_TRI                        0

    * Master Tri-state Enable for pin 57, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI1_PIN_57_TRI                        0

    * Master Tri-state Enable for pin 58, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI1_PIN_58_TRI                        0

    * Master Tri-state Enable for pin 59, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI1_PIN_59_TRI                        0

    * Master Tri-state Enable for pin 60, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI1_PIN_60_TRI                        0

    * Master Tri-state Enable for pin 61, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI1_PIN_61_TRI                        0

    * Master Tri-state Enable for pin 62, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI1_PIN_62_TRI                        0

    * Master Tri-state Enable for pin 63, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI1_PIN_63_TRI                        0

    * MIO pin Tri-state Enables, 63:32
    * (OFFSET, MASK, VALUE)      (0XFF180208, 0xFFFFFFFFU ,0x00B03000U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_MST_TRI1_OFFSET,
		0xFFFFFFFFU, 0x00B03000U);
/*##################################################################### */

    /*
    * Register : MIO_MST_TRI2 @ 0XFF18020C

    * Master Tri-state Enable for pin 64, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI2_PIN_64_TRI                        0

    * Master Tri-state Enable for pin 65, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI2_PIN_65_TRI                        0

    * Master Tri-state Enable for pin 66, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI2_PIN_66_TRI                        0

    * Master Tri-state Enable for pin 67, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI2_PIN_67_TRI                        0

    * Master Tri-state Enable for pin 68, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI2_PIN_68_TRI                        0

    * Master Tri-state Enable for pin 69, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI2_PIN_69_TRI                        0

    * Master Tri-state Enable for pin 70, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI2_PIN_70_TRI                        1

    * Master Tri-state Enable for pin 71, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI2_PIN_71_TRI                        1

    * Master Tri-state Enable for pin 72, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI2_PIN_72_TRI                        1

    * Master Tri-state Enable for pin 73, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI2_PIN_73_TRI                        1

    * Master Tri-state Enable for pin 74, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI2_PIN_74_TRI                        1

    * Master Tri-state Enable for pin 75, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI2_PIN_75_TRI                        1

    * Master Tri-state Enable for pin 76, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI2_PIN_76_TRI                        0

    * Master Tri-state Enable for pin 77, active high
    *  PSU_IOU_SLCR_MIO_MST_TRI2_PIN_77_TRI                        0

    * MIO pin Tri-state Enables, 77:64
    * (OFFSET, MASK, VALUE)      (0XFF18020C, 0x00003FFFU ,0x00000FC0U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_MST_TRI2_OFFSET,
		0x00003FFFU, 0x00000FC0U);
/*##################################################################### */

    /*
    * Register : bank0_ctrl0 @ 0XFF180138

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL0_DRIVE0_BIT_0                       1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL0_DRIVE0_BIT_1                       1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL0_DRIVE0_BIT_2                       1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL0_DRIVE0_BIT_3                       1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL0_DRIVE0_BIT_4                       1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL0_DRIVE0_BIT_5                       1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL0_DRIVE0_BIT_6                       1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL0_DRIVE0_BIT_7                       1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL0_DRIVE0_BIT_8                       1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL0_DRIVE0_BIT_9                       1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL0_DRIVE0_BIT_10                      1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL0_DRIVE0_BIT_11                      1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL0_DRIVE0_BIT_12                      1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL0_DRIVE0_BIT_13                      1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL0_DRIVE0_BIT_14                      1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL0_DRIVE0_BIT_15                      1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL0_DRIVE0_BIT_16                      1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL0_DRIVE0_BIT_17                      1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL0_DRIVE0_BIT_18                      1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL0_DRIVE0_BIT_19                      1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL0_DRIVE0_BIT_20                      1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL0_DRIVE0_BIT_21                      1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL0_DRIVE0_BIT_22                      1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL0_DRIVE0_BIT_23                      1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL0_DRIVE0_BIT_24                      1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL0_DRIVE0_BIT_25                      1

    * Drive0 control to MIO Bank 0 - control MIO[25:0]
    * (OFFSET, MASK, VALUE)      (0XFF180138, 0x03FFFFFFU ,0x03FFFFFFU)
    */
	PSU_Mask_Write(IOU_SLCR_BANK0_CTRL0_OFFSET,
		0x03FFFFFFU, 0x03FFFFFFU);
/*##################################################################### */

    /*
    * Register : bank0_ctrl1 @ 0XFF18013C

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL1_DRIVE1_BIT_0                       1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL1_DRIVE1_BIT_1                       1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL1_DRIVE1_BIT_2                       1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL1_DRIVE1_BIT_3                       1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL1_DRIVE1_BIT_4                       1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL1_DRIVE1_BIT_5                       1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL1_DRIVE1_BIT_6                       1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL1_DRIVE1_BIT_7                       1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL1_DRIVE1_BIT_8                       1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL1_DRIVE1_BIT_9                       1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL1_DRIVE1_BIT_10                      1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL1_DRIVE1_BIT_11                      1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL1_DRIVE1_BIT_12                      1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL1_DRIVE1_BIT_13                      1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL1_DRIVE1_BIT_14                      1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL1_DRIVE1_BIT_15                      1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL1_DRIVE1_BIT_16                      1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL1_DRIVE1_BIT_17                      1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL1_DRIVE1_BIT_18                      1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL1_DRIVE1_BIT_19                      1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL1_DRIVE1_BIT_20                      1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL1_DRIVE1_BIT_21                      1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL1_DRIVE1_BIT_22                      1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL1_DRIVE1_BIT_23                      1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL1_DRIVE1_BIT_24                      1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL1_DRIVE1_BIT_25                      1

    * Drive1 control to MIO Bank 0 - control MIO[25:0]
    * (OFFSET, MASK, VALUE)      (0XFF18013C, 0x03FFFFFFU ,0x03FFFFFFU)
    */
	PSU_Mask_Write(IOU_SLCR_BANK0_CTRL1_OFFSET,
		0x03FFFFFFU, 0x03FFFFFFU);
/*##################################################################### */

    /*
    * Register : bank0_ctrl3 @ 0XFF180140

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL3_SCHMITT_CMOS_N_BIT_0               0

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL3_SCHMITT_CMOS_N_BIT_1               0

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL3_SCHMITT_CMOS_N_BIT_2               0

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL3_SCHMITT_CMOS_N_BIT_3               0

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL3_SCHMITT_CMOS_N_BIT_4               0

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL3_SCHMITT_CMOS_N_BIT_5               0

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL3_SCHMITT_CMOS_N_BIT_6               0

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL3_SCHMITT_CMOS_N_BIT_7               0

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL3_SCHMITT_CMOS_N_BIT_8               0

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL3_SCHMITT_CMOS_N_BIT_9               0

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL3_SCHMITT_CMOS_N_BIT_10              0

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL3_SCHMITT_CMOS_N_BIT_11              0

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL3_SCHMITT_CMOS_N_BIT_12              0

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL3_SCHMITT_CMOS_N_BIT_13              0

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL3_SCHMITT_CMOS_N_BIT_14              0

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL3_SCHMITT_CMOS_N_BIT_15              0

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL3_SCHMITT_CMOS_N_BIT_16              0

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL3_SCHMITT_CMOS_N_BIT_17              0

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL3_SCHMITT_CMOS_N_BIT_18              0

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL3_SCHMITT_CMOS_N_BIT_19              0

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL3_SCHMITT_CMOS_N_BIT_20              0

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL3_SCHMITT_CMOS_N_BIT_21              0

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL3_SCHMITT_CMOS_N_BIT_22              0

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL3_SCHMITT_CMOS_N_BIT_23              0

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL3_SCHMITT_CMOS_N_BIT_24              0

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL3_SCHMITT_CMOS_N_BIT_25              0

    * Selects either Schmitt or CMOS input for MIO Bank 0 - control MIO[25:0]
    * (OFFSET, MASK, VALUE)      (0XFF180140, 0x03FFFFFFU ,0x00000000U)
    */
	PSU_Mask_Write(IOU_SLCR_BANK0_CTRL3_OFFSET,
		0x03FFFFFFU, 0x00000000U);
/*##################################################################### */

    /*
    * Register : bank0_ctrl4 @ 0XFF180144

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL4_PULL_HIGH_LOW_N_BIT_0              1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL4_PULL_HIGH_LOW_N_BIT_1              1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL4_PULL_HIGH_LOW_N_BIT_2              1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL4_PULL_HIGH_LOW_N_BIT_3              1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL4_PULL_HIGH_LOW_N_BIT_4              1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL4_PULL_HIGH_LOW_N_BIT_5              1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL4_PULL_HIGH_LOW_N_BIT_6              1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL4_PULL_HIGH_LOW_N_BIT_7              1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL4_PULL_HIGH_LOW_N_BIT_8              1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL4_PULL_HIGH_LOW_N_BIT_9              1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL4_PULL_HIGH_LOW_N_BIT_10             1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL4_PULL_HIGH_LOW_N_BIT_11             1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL4_PULL_HIGH_LOW_N_BIT_12             1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL4_PULL_HIGH_LOW_N_BIT_13             1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL4_PULL_HIGH_LOW_N_BIT_14             1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL4_PULL_HIGH_LOW_N_BIT_15             1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL4_PULL_HIGH_LOW_N_BIT_16             1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL4_PULL_HIGH_LOW_N_BIT_17             1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL4_PULL_HIGH_LOW_N_BIT_18             1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL4_PULL_HIGH_LOW_N_BIT_19             1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL4_PULL_HIGH_LOW_N_BIT_20             1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL4_PULL_HIGH_LOW_N_BIT_21             1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL4_PULL_HIGH_LOW_N_BIT_22             1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL4_PULL_HIGH_LOW_N_BIT_23             1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL4_PULL_HIGH_LOW_N_BIT_24             1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL4_PULL_HIGH_LOW_N_BIT_25             1

    * When mio_bank0_pull_enable is set, this selects pull up or pull down for
    *  MIO Bank 0 - control MIO[25:0]
    * (OFFSET, MASK, VALUE)      (0XFF180144, 0x03FFFFFFU ,0x03FFFFFFU)
    */
	PSU_Mask_Write(IOU_SLCR_BANK0_CTRL4_OFFSET,
		0x03FFFFFFU, 0x03FFFFFFU);
/*##################################################################### */

    /*
    * Register : bank0_ctrl5 @ 0XFF180148

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL5_PULL_ENABLE_BIT_0                  1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL5_PULL_ENABLE_BIT_1                  1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL5_PULL_ENABLE_BIT_2                  1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL5_PULL_ENABLE_BIT_3                  1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL5_PULL_ENABLE_BIT_4                  1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL5_PULL_ENABLE_BIT_5                  1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL5_PULL_ENABLE_BIT_6                  1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL5_PULL_ENABLE_BIT_7                  1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL5_PULL_ENABLE_BIT_8                  1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL5_PULL_ENABLE_BIT_9                  1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL5_PULL_ENABLE_BIT_10                 1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL5_PULL_ENABLE_BIT_11                 1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL5_PULL_ENABLE_BIT_12                 1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL5_PULL_ENABLE_BIT_13                 1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL5_PULL_ENABLE_BIT_14                 1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL5_PULL_ENABLE_BIT_15                 1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL5_PULL_ENABLE_BIT_16                 1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL5_PULL_ENABLE_BIT_17                 1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL5_PULL_ENABLE_BIT_18                 1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL5_PULL_ENABLE_BIT_19                 1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL5_PULL_ENABLE_BIT_20                 1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL5_PULL_ENABLE_BIT_21                 1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL5_PULL_ENABLE_BIT_22                 1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL5_PULL_ENABLE_BIT_23                 1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL5_PULL_ENABLE_BIT_24                 1

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL5_PULL_ENABLE_BIT_25                 1

    * When set, this enables mio_bank0_pullupdown to selects pull up or pull d
    * own for MIO Bank 0 - control MIO[25:0]
    * (OFFSET, MASK, VALUE)      (0XFF180148, 0x03FFFFFFU ,0x03FFFFFFU)
    */
	PSU_Mask_Write(IOU_SLCR_BANK0_CTRL5_OFFSET,
		0x03FFFFFFU, 0x03FFFFFFU);
/*##################################################################### */

    /*
    * Register : bank0_ctrl6 @ 0XFF18014C

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL6_SLOW_FAST_SLEW_N_BIT_0             0

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL6_SLOW_FAST_SLEW_N_BIT_1             0

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL6_SLOW_FAST_SLEW_N_BIT_2             0

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL6_SLOW_FAST_SLEW_N_BIT_3             0

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL6_SLOW_FAST_SLEW_N_BIT_4             0

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL6_SLOW_FAST_SLEW_N_BIT_5             0

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL6_SLOW_FAST_SLEW_N_BIT_6             0

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL6_SLOW_FAST_SLEW_N_BIT_7             0

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL6_SLOW_FAST_SLEW_N_BIT_8             0

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL6_SLOW_FAST_SLEW_N_BIT_9             0

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL6_SLOW_FAST_SLEW_N_BIT_10            0

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL6_SLOW_FAST_SLEW_N_BIT_11            0

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL6_SLOW_FAST_SLEW_N_BIT_12            0

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL6_SLOW_FAST_SLEW_N_BIT_13            0

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL6_SLOW_FAST_SLEW_N_BIT_14            0

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL6_SLOW_FAST_SLEW_N_BIT_15            0

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL6_SLOW_FAST_SLEW_N_BIT_16            0

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL6_SLOW_FAST_SLEW_N_BIT_17            0

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL6_SLOW_FAST_SLEW_N_BIT_18            0

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL6_SLOW_FAST_SLEW_N_BIT_19            0

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL6_SLOW_FAST_SLEW_N_BIT_20            0

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL6_SLOW_FAST_SLEW_N_BIT_21            0

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL6_SLOW_FAST_SLEW_N_BIT_22            0

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL6_SLOW_FAST_SLEW_N_BIT_23            0

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL6_SLOW_FAST_SLEW_N_BIT_24            0

    * Each bit applies to a single IO. Bit 0 for MIO[0].
    *  PSU_IOU_SLCR_BANK0_CTRL6_SLOW_FAST_SLEW_N_BIT_25            0

    * Slew rate control to MIO Bank 0 - control MIO[25:0]
    * (OFFSET, MASK, VALUE)      (0XFF18014C, 0x03FFFFFFU ,0x00000000U)
    */
	PSU_Mask_Write(IOU_SLCR_BANK0_CTRL6_OFFSET,
		0x03FFFFFFU, 0x00000000U);
/*##################################################################### */

    /*
    * Register : bank1_ctrl0 @ 0XFF180154

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL0_DRIVE0_BIT_0                       1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL0_DRIVE0_BIT_1                       1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL0_DRIVE0_BIT_2                       1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL0_DRIVE0_BIT_3                       1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL0_DRIVE0_BIT_4                       1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL0_DRIVE0_BIT_5                       1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL0_DRIVE0_BIT_6                       1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL0_DRIVE0_BIT_7                       1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL0_DRIVE0_BIT_8                       1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL0_DRIVE0_BIT_9                       1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL0_DRIVE0_BIT_10                      1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL0_DRIVE0_BIT_11                      1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL0_DRIVE0_BIT_12                      1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL0_DRIVE0_BIT_13                      1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL0_DRIVE0_BIT_14                      1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL0_DRIVE0_BIT_15                      1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL0_DRIVE0_BIT_16                      1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL0_DRIVE0_BIT_17                      1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL0_DRIVE0_BIT_18                      1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL0_DRIVE0_BIT_19                      1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL0_DRIVE0_BIT_20                      1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL0_DRIVE0_BIT_21                      1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL0_DRIVE0_BIT_22                      1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL0_DRIVE0_BIT_23                      1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL0_DRIVE0_BIT_24                      1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL0_DRIVE0_BIT_25                      1

    * Drive0 control to MIO Bank 1 - control MIO[51:26]
    * (OFFSET, MASK, VALUE)      (0XFF180154, 0x03FFFFFFU ,0x03FFFFFFU)
    */
	PSU_Mask_Write(IOU_SLCR_BANK1_CTRL0_OFFSET,
		0x03FFFFFFU, 0x03FFFFFFU);
/*##################################################################### */

    /*
    * Register : bank1_ctrl1 @ 0XFF180158

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL1_DRIVE1_BIT_0                       1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL1_DRIVE1_BIT_1                       1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL1_DRIVE1_BIT_2                       1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL1_DRIVE1_BIT_3                       1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL1_DRIVE1_BIT_4                       1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL1_DRIVE1_BIT_5                       1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL1_DRIVE1_BIT_6                       1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL1_DRIVE1_BIT_7                       1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL1_DRIVE1_BIT_8                       1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL1_DRIVE1_BIT_9                       1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL1_DRIVE1_BIT_10                      1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL1_DRIVE1_BIT_11                      1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL1_DRIVE1_BIT_12                      1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL1_DRIVE1_BIT_13                      1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL1_DRIVE1_BIT_14                      1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL1_DRIVE1_BIT_15                      1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL1_DRIVE1_BIT_16                      1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL1_DRIVE1_BIT_17                      1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL1_DRIVE1_BIT_18                      1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL1_DRIVE1_BIT_19                      1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL1_DRIVE1_BIT_20                      1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL1_DRIVE1_BIT_21                      1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL1_DRIVE1_BIT_22                      1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL1_DRIVE1_BIT_23                      1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL1_DRIVE1_BIT_24                      1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL1_DRIVE1_BIT_25                      1

    * Drive1 control to MIO Bank 1 - control MIO[51:26]
    * (OFFSET, MASK, VALUE)      (0XFF180158, 0x03FFFFFFU ,0x03FFFFFFU)
    */
	PSU_Mask_Write(IOU_SLCR_BANK1_CTRL1_OFFSET,
		0x03FFFFFFU, 0x03FFFFFFU);
/*##################################################################### */

    /*
    * Register : bank1_ctrl3 @ 0XFF18015C

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL3_SCHMITT_CMOS_N_BIT_0               0

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL3_SCHMITT_CMOS_N_BIT_1               0

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL3_SCHMITT_CMOS_N_BIT_2               0

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL3_SCHMITT_CMOS_N_BIT_3               0

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL3_SCHMITT_CMOS_N_BIT_4               0

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL3_SCHMITT_CMOS_N_BIT_5               0

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL3_SCHMITT_CMOS_N_BIT_6               0

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL3_SCHMITT_CMOS_N_BIT_7               0

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL3_SCHMITT_CMOS_N_BIT_8               0

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL3_SCHMITT_CMOS_N_BIT_9               0

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL3_SCHMITT_CMOS_N_BIT_10              0

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL3_SCHMITT_CMOS_N_BIT_11              0

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL3_SCHMITT_CMOS_N_BIT_12              0

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL3_SCHMITT_CMOS_N_BIT_13              0

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL3_SCHMITT_CMOS_N_BIT_14              0

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL3_SCHMITT_CMOS_N_BIT_15              0

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL3_SCHMITT_CMOS_N_BIT_16              0

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL3_SCHMITT_CMOS_N_BIT_17              0

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL3_SCHMITT_CMOS_N_BIT_18              0

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL3_SCHMITT_CMOS_N_BIT_19              0

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL3_SCHMITT_CMOS_N_BIT_20              0

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL3_SCHMITT_CMOS_N_BIT_21              0

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL3_SCHMITT_CMOS_N_BIT_22              0

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL3_SCHMITT_CMOS_N_BIT_23              0

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL3_SCHMITT_CMOS_N_BIT_24              0

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL3_SCHMITT_CMOS_N_BIT_25              0

    * Selects either Schmitt or CMOS input for MIO Bank 1 - control MIO[51:26]
    * (OFFSET, MASK, VALUE)      (0XFF18015C, 0x03FFFFFFU ,0x00000000U)
    */
	PSU_Mask_Write(IOU_SLCR_BANK1_CTRL3_OFFSET,
		0x03FFFFFFU, 0x00000000U);
/*##################################################################### */

    /*
    * Register : bank1_ctrl4 @ 0XFF180160

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL4_PULL_HIGH_LOW_N_BIT_0              1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL4_PULL_HIGH_LOW_N_BIT_1              1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL4_PULL_HIGH_LOW_N_BIT_2              1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL4_PULL_HIGH_LOW_N_BIT_3              1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL4_PULL_HIGH_LOW_N_BIT_4              1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL4_PULL_HIGH_LOW_N_BIT_5              1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL4_PULL_HIGH_LOW_N_BIT_6              1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL4_PULL_HIGH_LOW_N_BIT_7              1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL4_PULL_HIGH_LOW_N_BIT_8              1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL4_PULL_HIGH_LOW_N_BIT_9              1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL4_PULL_HIGH_LOW_N_BIT_10             1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL4_PULL_HIGH_LOW_N_BIT_11             1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL4_PULL_HIGH_LOW_N_BIT_12             1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL4_PULL_HIGH_LOW_N_BIT_13             1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL4_PULL_HIGH_LOW_N_BIT_14             1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL4_PULL_HIGH_LOW_N_BIT_15             1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL4_PULL_HIGH_LOW_N_BIT_16             1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL4_PULL_HIGH_LOW_N_BIT_17             1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL4_PULL_HIGH_LOW_N_BIT_18             1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL4_PULL_HIGH_LOW_N_BIT_19             1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL4_PULL_HIGH_LOW_N_BIT_20             1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL4_PULL_HIGH_LOW_N_BIT_21             1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL4_PULL_HIGH_LOW_N_BIT_22             1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL4_PULL_HIGH_LOW_N_BIT_23             1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL4_PULL_HIGH_LOW_N_BIT_24             1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL4_PULL_HIGH_LOW_N_BIT_25             1

    * When mio_bank1_pull_enable is set, this selects pull up or pull down for
    *  MIO Bank 1 - control MIO[51:26]
    * (OFFSET, MASK, VALUE)      (0XFF180160, 0x03FFFFFFU ,0x03FFFFFFU)
    */
	PSU_Mask_Write(IOU_SLCR_BANK1_CTRL4_OFFSET,
		0x03FFFFFFU, 0x03FFFFFFU);
/*##################################################################### */

    /*
    * Register : bank1_ctrl5 @ 0XFF180164

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL5_PULL_ENABLE_BIT_0                  1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL5_PULL_ENABLE_BIT_1                  1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL5_PULL_ENABLE_BIT_2                  1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL5_PULL_ENABLE_BIT_3                  1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL5_PULL_ENABLE_BIT_4                  1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL5_PULL_ENABLE_BIT_5                  1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL5_PULL_ENABLE_BIT_6                  1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL5_PULL_ENABLE_BIT_7                  1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL5_PULL_ENABLE_BIT_8                  1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL5_PULL_ENABLE_BIT_9                  1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL5_PULL_ENABLE_BIT_10                 1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL5_PULL_ENABLE_BIT_11                 1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL5_PULL_ENABLE_BIT_12                 1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL5_PULL_ENABLE_BIT_13                 1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL5_PULL_ENABLE_BIT_14                 1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL5_PULL_ENABLE_BIT_15                 1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL5_PULL_ENABLE_BIT_16                 1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL5_PULL_ENABLE_BIT_17                 1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL5_PULL_ENABLE_BIT_18                 1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL5_PULL_ENABLE_BIT_19                 1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL5_PULL_ENABLE_BIT_20                 1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL5_PULL_ENABLE_BIT_21                 1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL5_PULL_ENABLE_BIT_22                 1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL5_PULL_ENABLE_BIT_23                 1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL5_PULL_ENABLE_BIT_24                 1

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL5_PULL_ENABLE_BIT_25                 1

    * When set, this enables mio_bank1_pullupdown to selects pull up or pull d
    * own for MIO Bank 1 - control MIO[51:26]
    * (OFFSET, MASK, VALUE)      (0XFF180164, 0x03FFFFFFU ,0x03FFFFFFU)
    */
	PSU_Mask_Write(IOU_SLCR_BANK1_CTRL5_OFFSET,
		0x03FFFFFFU, 0x03FFFFFFU);
/*##################################################################### */

    /*
    * Register : bank1_ctrl6 @ 0XFF180168

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL6_SLOW_FAST_SLEW_N_BIT_0             0

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL6_SLOW_FAST_SLEW_N_BIT_1             0

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL6_SLOW_FAST_SLEW_N_BIT_2             0

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL6_SLOW_FAST_SLEW_N_BIT_3             0

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL6_SLOW_FAST_SLEW_N_BIT_4             0

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL6_SLOW_FAST_SLEW_N_BIT_5             0

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL6_SLOW_FAST_SLEW_N_BIT_6             0

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL6_SLOW_FAST_SLEW_N_BIT_7             0

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL6_SLOW_FAST_SLEW_N_BIT_8             0

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL6_SLOW_FAST_SLEW_N_BIT_9             0

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL6_SLOW_FAST_SLEW_N_BIT_10            0

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL6_SLOW_FAST_SLEW_N_BIT_11            0

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL6_SLOW_FAST_SLEW_N_BIT_12            0

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL6_SLOW_FAST_SLEW_N_BIT_13            0

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL6_SLOW_FAST_SLEW_N_BIT_14            0

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL6_SLOW_FAST_SLEW_N_BIT_15            0

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL6_SLOW_FAST_SLEW_N_BIT_16            0

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL6_SLOW_FAST_SLEW_N_BIT_17            0

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL6_SLOW_FAST_SLEW_N_BIT_18            0

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL6_SLOW_FAST_SLEW_N_BIT_19            0

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL6_SLOW_FAST_SLEW_N_BIT_20            0

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL6_SLOW_FAST_SLEW_N_BIT_21            0

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL6_SLOW_FAST_SLEW_N_BIT_22            0

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL6_SLOW_FAST_SLEW_N_BIT_23            0

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL6_SLOW_FAST_SLEW_N_BIT_24            0

    * Each bit applies to a single IO. Bit 0 for MIO[26].
    *  PSU_IOU_SLCR_BANK1_CTRL6_SLOW_FAST_SLEW_N_BIT_25            0

    * Slew rate control to MIO Bank 1 - control MIO[51:26]
    * (OFFSET, MASK, VALUE)      (0XFF180168, 0x03FFFFFFU ,0x00000000U)
    */
	PSU_Mask_Write(IOU_SLCR_BANK1_CTRL6_OFFSET,
		0x03FFFFFFU, 0x00000000U);
/*##################################################################### */

    /*
    * Register : bank2_ctrl0 @ 0XFF180170

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL0_DRIVE0_BIT_0                       1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL0_DRIVE0_BIT_1                       1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL0_DRIVE0_BIT_2                       1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL0_DRIVE0_BIT_3                       1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL0_DRIVE0_BIT_4                       1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL0_DRIVE0_BIT_5                       1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL0_DRIVE0_BIT_6                       1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL0_DRIVE0_BIT_7                       1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL0_DRIVE0_BIT_8                       1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL0_DRIVE0_BIT_9                       1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL0_DRIVE0_BIT_10                      1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL0_DRIVE0_BIT_11                      1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL0_DRIVE0_BIT_12                      1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL0_DRIVE0_BIT_13                      1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL0_DRIVE0_BIT_14                      1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL0_DRIVE0_BIT_15                      1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL0_DRIVE0_BIT_16                      1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL0_DRIVE0_BIT_17                      1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL0_DRIVE0_BIT_18                      1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL0_DRIVE0_BIT_19                      1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL0_DRIVE0_BIT_20                      1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL0_DRIVE0_BIT_21                      1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL0_DRIVE0_BIT_22                      1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL0_DRIVE0_BIT_23                      1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL0_DRIVE0_BIT_24                      1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL0_DRIVE0_BIT_25                      1

    * Drive0 control to MIO Bank 2 - control MIO[77:52]
    * (OFFSET, MASK, VALUE)      (0XFF180170, 0x03FFFFFFU ,0x03FFFFFFU)
    */
	PSU_Mask_Write(IOU_SLCR_BANK2_CTRL0_OFFSET,
		0x03FFFFFFU, 0x03FFFFFFU);
/*##################################################################### */

    /*
    * Register : bank2_ctrl1 @ 0XFF180174

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL1_DRIVE1_BIT_0                       1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL1_DRIVE1_BIT_1                       1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL1_DRIVE1_BIT_2                       1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL1_DRIVE1_BIT_3                       1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL1_DRIVE1_BIT_4                       1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL1_DRIVE1_BIT_5                       1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL1_DRIVE1_BIT_6                       1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL1_DRIVE1_BIT_7                       1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL1_DRIVE1_BIT_8                       1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL1_DRIVE1_BIT_9                       1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL1_DRIVE1_BIT_10                      1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL1_DRIVE1_BIT_11                      1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL1_DRIVE1_BIT_12                      1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL1_DRIVE1_BIT_13                      1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL1_DRIVE1_BIT_14                      1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL1_DRIVE1_BIT_15                      1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL1_DRIVE1_BIT_16                      1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL1_DRIVE1_BIT_17                      1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL1_DRIVE1_BIT_18                      1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL1_DRIVE1_BIT_19                      1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL1_DRIVE1_BIT_20                      1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL1_DRIVE1_BIT_21                      1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL1_DRIVE1_BIT_22                      1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL1_DRIVE1_BIT_23                      1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL1_DRIVE1_BIT_24                      1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL1_DRIVE1_BIT_25                      1

    * Drive1 control to MIO Bank 2 - control MIO[77:52]
    * (OFFSET, MASK, VALUE)      (0XFF180174, 0x03FFFFFFU ,0x03FFFFFFU)
    */
	PSU_Mask_Write(IOU_SLCR_BANK2_CTRL1_OFFSET,
		0x03FFFFFFU, 0x03FFFFFFU);
/*##################################################################### */

    /*
    * Register : bank2_ctrl3 @ 0XFF180178

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL3_SCHMITT_CMOS_N_BIT_0               0

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL3_SCHMITT_CMOS_N_BIT_1               0

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL3_SCHMITT_CMOS_N_BIT_2               0

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL3_SCHMITT_CMOS_N_BIT_3               0

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL3_SCHMITT_CMOS_N_BIT_4               0

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL3_SCHMITT_CMOS_N_BIT_5               0

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL3_SCHMITT_CMOS_N_BIT_6               0

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL3_SCHMITT_CMOS_N_BIT_7               0

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL3_SCHMITT_CMOS_N_BIT_8               0

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL3_SCHMITT_CMOS_N_BIT_9               0

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL3_SCHMITT_CMOS_N_BIT_10              0

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL3_SCHMITT_CMOS_N_BIT_11              0

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL3_SCHMITT_CMOS_N_BIT_12              0

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL3_SCHMITT_CMOS_N_BIT_13              0

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL3_SCHMITT_CMOS_N_BIT_14              0

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL3_SCHMITT_CMOS_N_BIT_15              0

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL3_SCHMITT_CMOS_N_BIT_16              0

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL3_SCHMITT_CMOS_N_BIT_17              0

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL3_SCHMITT_CMOS_N_BIT_18              0

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL3_SCHMITT_CMOS_N_BIT_19              0

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL3_SCHMITT_CMOS_N_BIT_20              0

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL3_SCHMITT_CMOS_N_BIT_21              0

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL3_SCHMITT_CMOS_N_BIT_22              0

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL3_SCHMITT_CMOS_N_BIT_23              0

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL3_SCHMITT_CMOS_N_BIT_24              0

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL3_SCHMITT_CMOS_N_BIT_25              0

    * Selects either Schmitt or CMOS input for MIO Bank 2 - control MIO[77:52]
    * (OFFSET, MASK, VALUE)      (0XFF180178, 0x03FFFFFFU ,0x00000000U)
    */
	PSU_Mask_Write(IOU_SLCR_BANK2_CTRL3_OFFSET,
		0x03FFFFFFU, 0x00000000U);
/*##################################################################### */

    /*
    * Register : bank2_ctrl4 @ 0XFF18017C

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL4_PULL_HIGH_LOW_N_BIT_0              1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL4_PULL_HIGH_LOW_N_BIT_1              1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL4_PULL_HIGH_LOW_N_BIT_2              1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL4_PULL_HIGH_LOW_N_BIT_3              1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL4_PULL_HIGH_LOW_N_BIT_4              1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL4_PULL_HIGH_LOW_N_BIT_5              1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL4_PULL_HIGH_LOW_N_BIT_6              1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL4_PULL_HIGH_LOW_N_BIT_7              1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL4_PULL_HIGH_LOW_N_BIT_8              1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL4_PULL_HIGH_LOW_N_BIT_9              1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL4_PULL_HIGH_LOW_N_BIT_10             1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL4_PULL_HIGH_LOW_N_BIT_11             1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL4_PULL_HIGH_LOW_N_BIT_12             1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL4_PULL_HIGH_LOW_N_BIT_13             1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL4_PULL_HIGH_LOW_N_BIT_14             1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL4_PULL_HIGH_LOW_N_BIT_15             1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL4_PULL_HIGH_LOW_N_BIT_16             1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL4_PULL_HIGH_LOW_N_BIT_17             1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL4_PULL_HIGH_LOW_N_BIT_18             1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL4_PULL_HIGH_LOW_N_BIT_19             1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL4_PULL_HIGH_LOW_N_BIT_20             1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL4_PULL_HIGH_LOW_N_BIT_21             1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL4_PULL_HIGH_LOW_N_BIT_22             1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL4_PULL_HIGH_LOW_N_BIT_23             1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL4_PULL_HIGH_LOW_N_BIT_24             1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL4_PULL_HIGH_LOW_N_BIT_25             1

    * When mio_bank2_pull_enable is set, this selects pull up or pull down for
    *  MIO Bank 2 - control MIO[77:52]
    * (OFFSET, MASK, VALUE)      (0XFF18017C, 0x03FFFFFFU ,0x03FFFFFFU)
    */
	PSU_Mask_Write(IOU_SLCR_BANK2_CTRL4_OFFSET,
		0x03FFFFFFU, 0x03FFFFFFU);
/*##################################################################### */

    /*
    * Register : bank2_ctrl5 @ 0XFF180180

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL5_PULL_ENABLE_BIT_0                  1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL5_PULL_ENABLE_BIT_1                  1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL5_PULL_ENABLE_BIT_2                  1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL5_PULL_ENABLE_BIT_3                  1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL5_PULL_ENABLE_BIT_4                  1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL5_PULL_ENABLE_BIT_5                  1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL5_PULL_ENABLE_BIT_6                  1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL5_PULL_ENABLE_BIT_7                  1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL5_PULL_ENABLE_BIT_8                  1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL5_PULL_ENABLE_BIT_9                  1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL5_PULL_ENABLE_BIT_10                 1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL5_PULL_ENABLE_BIT_11                 1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL5_PULL_ENABLE_BIT_12                 1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL5_PULL_ENABLE_BIT_13                 1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL5_PULL_ENABLE_BIT_14                 1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL5_PULL_ENABLE_BIT_15                 1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL5_PULL_ENABLE_BIT_16                 1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL5_PULL_ENABLE_BIT_17                 1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL5_PULL_ENABLE_BIT_18                 1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL5_PULL_ENABLE_BIT_19                 1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL5_PULL_ENABLE_BIT_20                 1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL5_PULL_ENABLE_BIT_21                 1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL5_PULL_ENABLE_BIT_22                 1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL5_PULL_ENABLE_BIT_23                 1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL5_PULL_ENABLE_BIT_24                 1

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL5_PULL_ENABLE_BIT_25                 1

    * When set, this enables mio_bank2_pullupdown to selects pull up or pull d
    * own for MIO Bank 2 - control MIO[77:52]
    * (OFFSET, MASK, VALUE)      (0XFF180180, 0x03FFFFFFU ,0x03FFFFFFU)
    */
	PSU_Mask_Write(IOU_SLCR_BANK2_CTRL5_OFFSET,
		0x03FFFFFFU, 0x03FFFFFFU);
/*##################################################################### */

    /*
    * Register : bank2_ctrl6 @ 0XFF180184

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL6_SLOW_FAST_SLEW_N_BIT_0             0

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL6_SLOW_FAST_SLEW_N_BIT_1             0

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL6_SLOW_FAST_SLEW_N_BIT_2             0

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL6_SLOW_FAST_SLEW_N_BIT_3             0

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL6_SLOW_FAST_SLEW_N_BIT_4             0

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL6_SLOW_FAST_SLEW_N_BIT_5             0

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL6_SLOW_FAST_SLEW_N_BIT_6             0

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL6_SLOW_FAST_SLEW_N_BIT_7             0

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL6_SLOW_FAST_SLEW_N_BIT_8             0

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL6_SLOW_FAST_SLEW_N_BIT_9             0

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL6_SLOW_FAST_SLEW_N_BIT_10            0

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL6_SLOW_FAST_SLEW_N_BIT_11            0

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL6_SLOW_FAST_SLEW_N_BIT_12            0

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL6_SLOW_FAST_SLEW_N_BIT_13            0

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL6_SLOW_FAST_SLEW_N_BIT_14            0

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL6_SLOW_FAST_SLEW_N_BIT_15            0

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL6_SLOW_FAST_SLEW_N_BIT_16            0

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL6_SLOW_FAST_SLEW_N_BIT_17            0

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL6_SLOW_FAST_SLEW_N_BIT_18            0

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL6_SLOW_FAST_SLEW_N_BIT_19            0

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL6_SLOW_FAST_SLEW_N_BIT_20            0

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL6_SLOW_FAST_SLEW_N_BIT_21            0

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL6_SLOW_FAST_SLEW_N_BIT_22            0

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL6_SLOW_FAST_SLEW_N_BIT_23            0

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL6_SLOW_FAST_SLEW_N_BIT_24            0

    * Each bit applies to a single IO. Bit 0 for MIO[52].
    *  PSU_IOU_SLCR_BANK2_CTRL6_SLOW_FAST_SLEW_N_BIT_25            0

    * Slew rate control to MIO Bank 2 - control MIO[77:52]
    * (OFFSET, MASK, VALUE)      (0XFF180184, 0x03FFFFFFU ,0x00000000U)
    */
	PSU_Mask_Write(IOU_SLCR_BANK2_CTRL6_OFFSET,
		0x03FFFFFFU, 0x00000000U);
/*##################################################################### */

    /*
    * LOOPBACK
    */
    /*
    * Register : MIO_LOOPBACK @ 0XFF180200

    * I2C Loopback Control. 0 = Connect I2C inputs according to MIO mapping. 1
    *  = Loop I2C 0 outputs to I2C 1 inputs, and I2C 1 outputs to I2C 0 inputs
    * .
    *  PSU_IOU_SLCR_MIO_LOOPBACK_I2C0_LOOP_I2C1                    0

    * CAN Loopback Control. 0 = Connect CAN inputs according to MIO mapping. 1
    *  = Loop CAN 0 Tx to CAN 1 Rx, and CAN 1 Tx to CAN 0 Rx.
    *  PSU_IOU_SLCR_MIO_LOOPBACK_CAN0_LOOP_CAN1                    0

    * UART Loopback Control. 0 = Connect UART inputs according to MIO mapping.
    *  1 = Loop UART 0 outputs to UART 1 inputs, and UART 1 outputs to UART 0
    * inputs. RXD/TXD cross-connected. RTS/CTS cross-connected. DSR, DTR, DCD
    * and RI not used.
    *  PSU_IOU_SLCR_MIO_LOOPBACK_UA0_LOOP_UA1                      0

    * SPI Loopback Control. 0 = Connect SPI inputs according to MIO mapping. 1
    *  = Loop SPI 0 outputs to SPI 1 inputs, and SPI 1 outputs to SPI 0 inputs
    * . The other SPI core will appear on the LS Slave Select.
    *  PSU_IOU_SLCR_MIO_LOOPBACK_SPI0_LOOP_SPI1                    0

    * Loopback function within MIO
    * (OFFSET, MASK, VALUE)      (0XFF180200, 0x0000000FU ,0x00000000U)
    */
	PSU_Mask_Write(IOU_SLCR_MIO_LOOPBACK_OFFSET,
		0x0000000FU, 0x00000000U);
/*##################################################################### */


	return 1;
}
unsigned long psu_peripherals_init_data(void)
{
    /*
    * COHERENCY
    */
    /*
    * FPD RESET
    */
    /*
    * Register : RST_FPD_TOP @ 0XFD1A0100

    * PCIE config reset
    *  PSU_CRF_APB_RST_FPD_TOP_PCIE_CFG_RESET                      0

    * PCIE control block level reset
    *  PSU_CRF_APB_RST_FPD_TOP_PCIE_CTRL_RESET                     0

    * PCIE bridge block level reset (AXI interface)
    *  PSU_CRF_APB_RST_FPD_TOP_PCIE_BRIDGE_RESET                   0

    * Display Port block level reset (includes DPDMA)
    *  PSU_CRF_APB_RST_FPD_TOP_DP_RESET                            0

    * FPD WDT reset
    *  PSU_CRF_APB_RST_FPD_TOP_SWDT_RESET                          0

    * GDMA block level reset
    *  PSU_CRF_APB_RST_FPD_TOP_GDMA_RESET                          0

    * Pixel Processor (submodule of GPU) block level reset
    *  PSU_CRF_APB_RST_FPD_TOP_GPU_PP0_RESET                       0

    * Pixel Processor (submodule of GPU) block level reset
    *  PSU_CRF_APB_RST_FPD_TOP_GPU_PP1_RESET                       0

    * GPU block level reset
    *  PSU_CRF_APB_RST_FPD_TOP_GPU_RESET                           0

    * GT block level reset
    *  PSU_CRF_APB_RST_FPD_TOP_GT_RESET                            0

    * Sata block level reset
    *  PSU_CRF_APB_RST_FPD_TOP_SATA_RESET                          0

    * FPD Block level software controlled reset
    * (OFFSET, MASK, VALUE)      (0XFD1A0100, 0x000F807EU ,0x00000000U)
    */
	PSU_Mask_Write(CRF_APB_RST_FPD_TOP_OFFSET, 0x000F807EU, 0x00000000U);
/*##################################################################### */

    /*
    * RESET BLOCKS
    */
    /*
    * TIMESTAMP
    */
    /*
    * Register : RST_LPD_IOU2 @ 0XFF5E0238

    * Block level reset
    *  PSU_CRL_APB_RST_LPD_IOU2_TIMESTAMP_RESET                    0

    * Block level reset
    *  PSU_CRL_APB_RST_LPD_IOU2_IOU_CC_RESET                       0

    * Block level reset
    *  PSU_CRL_APB_RST_LPD_IOU2_ADMA_RESET                         0

    * Software control register for the IOU block. Each bit will cause a singl
    * erperipheral or part of the peripheral to be reset.
    * (OFFSET, MASK, VALUE)      (0XFF5E0238, 0x001A0000U ,0x00000000U)
    */
	PSU_Mask_Write(CRL_APB_RST_LPD_IOU2_OFFSET,
		0x001A0000U, 0x00000000U);
/*##################################################################### */

    /*
    * Register : RST_LPD_TOP @ 0XFF5E023C

    * Reset entire full power domain.
    *  PSU_CRL_APB_RST_LPD_TOP_FPD_RESET                           0

    * LPD SWDT
    *  PSU_CRL_APB_RST_LPD_TOP_LPD_SWDT_RESET                      0

    * Sysmonitor reset
    *  PSU_CRL_APB_RST_LPD_TOP_SYSMON_RESET                        0

    * Real Time Clock reset
    *  PSU_CRL_APB_RST_LPD_TOP_RTC_RESET                           0

    * APM reset
    *  PSU_CRL_APB_RST_LPD_TOP_APM_RESET                           0

    * IPI reset
    *  PSU_CRL_APB_RST_LPD_TOP_IPI_RESET                           0

    * reset entire RPU power island
    *  PSU_CRL_APB_RST_LPD_TOP_RPU_PGE_RESET                       0

    * reset ocm
    *  PSU_CRL_APB_RST_LPD_TOP_OCM_RESET                           0

    * Software control register for the LPD block.
    * (OFFSET, MASK, VALUE)      (0XFF5E023C, 0x0093C018U ,0x00000000U)
    */
	PSU_Mask_Write(CRL_APB_RST_LPD_TOP_OFFSET, 0x0093C018U, 0x00000000U);
/*##################################################################### */

    /*
    * ENET
    */
    /*
    * Register : RST_LPD_IOU0 @ 0XFF5E0230

    * GEM 3 reset
    *  PSU_CRL_APB_RST_LPD_IOU0_GEM3_RESET                         0

    * Software controlled reset for the GEMs
    * (OFFSET, MASK, VALUE)      (0XFF5E0230, 0x00000008U ,0x00000000U)
    */
	PSU_Mask_Write(CRL_APB_RST_LPD_IOU0_OFFSET,
		0x00000008U, 0x00000000U);
/*##################################################################### */

    /*
    * QSPI
    */
    /*
    * Register : RST_LPD_IOU2 @ 0XFF5E0238

    * Block level reset
    *  PSU_CRL_APB_RST_LPD_IOU2_QSPI_RESET                         0

    * Software control register for the IOU block. Each bit will cause a singl
    * erperipheral or part of the peripheral to be reset.
    * (OFFSET, MASK, VALUE)      (0XFF5E0238, 0x00000001U ,0x00000000U)
    */
	PSU_Mask_Write(CRL_APB_RST_LPD_IOU2_OFFSET,
		0x00000001U, 0x00000000U);
/*##################################################################### */

    /*
    * QSPI TAP DELAY
    */
    /*
    * Register : IOU_TAPDLY_BYPASS @ 0XFF180390

    * 0: Do not by pass the tap delays on the Rx clock signal of LQSPI 1: Bypa
    * ss the Tap delay on the Rx clock signal of LQSPI
    *  PSU_IOU_SLCR_IOU_TAPDLY_BYPASS_LQSPI_RX                     1

    * IOU tap delay bypass for the LQSPI and NAND controllers
    * (OFFSET, MASK, VALUE)      (0XFF180390, 0x00000004U ,0x00000004U)
    */
	PSU_Mask_Write(IOU_SLCR_IOU_TAPDLY_BYPASS_OFFSET,
		0x00000004U, 0x00000004U);
/*##################################################################### */

    /*
    * NAND
    */
    /*
    * USB
    */
    /*
    * Register : RST_LPD_TOP @ 0XFF5E023C

    * USB 0 reset for control registers
    *  PSU_CRL_APB_RST_LPD_TOP_USB0_APB_RESET                      0

    * USB 0 sleep circuit reset
    *  PSU_CRL_APB_RST_LPD_TOP_USB0_HIBERRESET                     0

    * USB 0 reset
    *  PSU_CRL_APB_RST_LPD_TOP_USB0_CORERESET                      0

    * Software control register for the LPD block.
    * (OFFSET, MASK, VALUE)      (0XFF5E023C, 0x00000540U ,0x00000000U)
    */
	PSU_Mask_Write(CRL_APB_RST_LPD_TOP_OFFSET, 0x00000540U, 0x00000000U);
/*##################################################################### */

    /*
    * USB0 PIPE POWER PRESENT
    */
    /*
    * Register : fpd_power_prsnt @ 0XFF9D0080

    * This bit is used to choose between PIPE power present and 1'b1
    *  PSU_USB3_0_FPD_POWER_PRSNT_OPTION                           0X1

    * fpd_power_prsnt
    * (OFFSET, MASK, VALUE)      (0XFF9D0080, 0x00000001U ,0x00000001U)
    */
	PSU_Mask_Write(USB3_0_FPD_POWER_PRSNT_OFFSET,
		0x00000001U, 0x00000001U);
/*##################################################################### */

    /*
    * Register : fpd_pipe_clk @ 0XFF9D007C

    * This bit is used to choose between PIPE clock coming from SerDes and the
    *  suspend clk
    *  PSU_USB3_0_FPD_PIPE_CLK_OPTION                              0x0

    * fpd_pipe_clk
    * (OFFSET, MASK, VALUE)      (0XFF9D007C, 0x00000001U ,0x00000000U)
    */
	PSU_Mask_Write(USB3_0_FPD_PIPE_CLK_OFFSET, 0x00000001U, 0x00000000U);
/*##################################################################### */

    /*
    * SD
    */
    /*
    * Register : RST_LPD_IOU2 @ 0XFF5E0238

    * Block level reset
    *  PSU_CRL_APB_RST_LPD_IOU2_SDIO1_RESET                        0

    * Software control register for the IOU block. Each bit will cause a singl
    * erperipheral or part of the peripheral to be reset.
    * (OFFSET, MASK, VALUE)      (0XFF5E0238, 0x00000040U ,0x00000000U)
    */
	PSU_Mask_Write(CRL_APB_RST_LPD_IOU2_OFFSET,
		0x00000040U, 0x00000000U);
/*##################################################################### */

    /*
    * Register : CTRL_REG_SD @ 0XFF180310

    * SD or eMMC selection on SDIO1 0: SD enabled 1: eMMC enabled
    *  PSU_IOU_SLCR_CTRL_REG_SD_SD1_EMMC_SEL                       0

    * SD eMMC selection
    * (OFFSET, MASK, VALUE)      (0XFF180310, 0x00008000U ,0x00000000U)
    */
	PSU_Mask_Write(IOU_SLCR_CTRL_REG_SD_OFFSET,
		0x00008000U, 0x00000000U);
/*##################################################################### */

    /*
    * Register : SD_CONFIG_REG2 @ 0XFF180320

    * Should be set based on the final product usage 00 - Removable SCard Slot
    *  01 - Embedded Slot for One Device 10 - Shared Bus Slot 11 - Reserved
    *  PSU_IOU_SLCR_SD_CONFIG_REG2_SD1_SLOTTYPE                    0

    * 1.8V Support 1: 1.8V supported 0: 1.8V not supported support
    *  PSU_IOU_SLCR_SD_CONFIG_REG2_SD1_1P8V                        1

    * 3.0V Support 1: 3.0V supported 0: 3.0V not supported support
    *  PSU_IOU_SLCR_SD_CONFIG_REG2_SD1_3P0V                        0

    * 3.3V Support 1: 3.3V supported 0: 3.3V not supported support
    *  PSU_IOU_SLCR_SD_CONFIG_REG2_SD1_3P3V                        1

    * SD Config Register 2
    * (OFFSET, MASK, VALUE)      (0XFF180320, 0x33800000U ,0x02800000U)
    */
	PSU_Mask_Write(IOU_SLCR_SD_CONFIG_REG2_OFFSET,
		0x33800000U, 0x02800000U);
/*##################################################################### */

    /*
    * SD1 BASE CLOCK
    */
    /*
    * Register : SD_CONFIG_REG1 @ 0XFF18031C

    * Base Clock Frequency for SD Clock. This is the frequency of the xin_clk.
    *  PSU_IOU_SLCR_SD_CONFIG_REG1_SD1_BASECLK                     0xc8

    * Configures the Number of Taps (Phases) of the rxclk_in that is supported
    * .
    *  PSU_IOU_SLCR_SD_CONFIG_REG1_SD1_TUNIGCOUNT                  0x28

    * SD Config Register 1
    * (OFFSET, MASK, VALUE)      (0XFF18031C, 0x7FFE0000U ,0x64500000U)
    */
	PSU_Mask_Write(IOU_SLCR_SD_CONFIG_REG1_OFFSET,
		0x7FFE0000U, 0x64500000U);
/*##################################################################### */

    /*
    * Register : SD_DLL_CTRL @ 0XFF180358

    * Reserved.
    *  PSU_IOU_SLCR_SD_DLL_CTRL_RESERVED                           1

    * SDIO status register
    * (OFFSET, MASK, VALUE)      (0XFF180358, 0x00000008U ,0x00000008U)
    */
	PSU_Mask_Write(IOU_SLCR_SD_DLL_CTRL_OFFSET,
		0x00000008U, 0x00000008U);
/*##################################################################### */

    /*
    * SD1 RETUNER
    */
    /*
    * Register : SD_CONFIG_REG3 @ 0XFF180324

    * This is the Timer Count for Re-Tuning Timer for Re-Tuning Mode 1 to 3. S
    * etting to 4'b0 disables Re-Tuning Timer. 0h - Get information via other
    * source 1h = 1 seconds 2h = 2 seconds 3h = 4 seconds 4h = 8 seconds -- n
    * = 2(n-1) seconds -- Bh = 1024 seconds Fh - Ch = Reserved
    *  PSU_IOU_SLCR_SD_CONFIG_REG3_SD1_RETUNETMR                   0X0

    * SD Config Register 3
    * (OFFSET, MASK, VALUE)      (0XFF180324, 0x03C00000U ,0x00000000U)
    */
	PSU_Mask_Write(IOU_SLCR_SD_CONFIG_REG3_OFFSET,
		0x03C00000U, 0x00000000U);
/*##################################################################### */

    /*
    * CAN
    */
    /*
    * Register : RST_LPD_IOU2 @ 0XFF5E0238

    * Block level reset
    *  PSU_CRL_APB_RST_LPD_IOU2_CAN1_RESET                         0

    * Software control register for the IOU block. Each bit will cause a singl
    * erperipheral or part of the peripheral to be reset.
    * (OFFSET, MASK, VALUE)      (0XFF5E0238, 0x00000100U ,0x00000000U)
    */
	PSU_Mask_Write(CRL_APB_RST_LPD_IOU2_OFFSET,
		0x00000100U, 0x00000000U);
/*##################################################################### */

    /*
    * I2C
    */
    /*
    * Register : RST_LPD_IOU2 @ 0XFF5E0238

    * Block level reset
    *  PSU_CRL_APB_RST_LPD_IOU2_I2C0_RESET                         0

    * Block level reset
    *  PSU_CRL_APB_RST_LPD_IOU2_I2C1_RESET                         0

    * Software control register for the IOU block. Each bit will cause a singl
    * erperipheral or part of the peripheral to be reset.
    * (OFFSET, MASK, VALUE)      (0XFF5E0238, 0x00000600U ,0x00000000U)
    */
	PSU_Mask_Write(CRL_APB_RST_LPD_IOU2_OFFSET,
		0x00000600U, 0x00000000U);
/*##################################################################### */

    /*
    * SWDT
    */
    /*
    * Register : RST_LPD_IOU2 @ 0XFF5E0238

    * Block level reset
    *  PSU_CRL_APB_RST_LPD_IOU2_SWDT_RESET                         0

    * Software control register for the IOU block. Each bit will cause a singl
    * erperipheral or part of the peripheral to be reset.
    * (OFFSET, MASK, VALUE)      (0XFF5E0238, 0x00008000U ,0x00000000U)
    */
	PSU_Mask_Write(CRL_APB_RST_LPD_IOU2_OFFSET,
		0x00008000U, 0x00000000U);
/*##################################################################### */

    /*
    * SPI
    */
    /*
    * TTC
    */
    /*
    * Register : RST_LPD_IOU2 @ 0XFF5E0238

    * Block level reset
    *  PSU_CRL_APB_RST_LPD_IOU2_TTC0_RESET                         0

    * Block level reset
    *  PSU_CRL_APB_RST_LPD_IOU2_TTC1_RESET                         0

    * Block level reset
    *  PSU_CRL_APB_RST_LPD_IOU2_TTC2_RESET                         0

    * Block level reset
    *  PSU_CRL_APB_RST_LPD_IOU2_TTC3_RESET                         0

    * Software control register for the IOU block. Each bit will cause a singl
    * erperipheral or part of the peripheral to be reset.
    * (OFFSET, MASK, VALUE)      (0XFF5E0238, 0x00007800U ,0x00000000U)
    */
	PSU_Mask_Write(CRL_APB_RST_LPD_IOU2_OFFSET,
		0x00007800U, 0x00000000U);
/*##################################################################### */

    /*
    * UART
    */
    /*
    * Register : RST_LPD_IOU2 @ 0XFF5E0238

    * Block level reset
    *  PSU_CRL_APB_RST_LPD_IOU2_UART0_RESET                        0

    * Block level reset
    *  PSU_CRL_APB_RST_LPD_IOU2_UART1_RESET                        0

    * Software control register for the IOU block. Each bit will cause a singl
    * erperipheral or part of the peripheral to be reset.
    * (OFFSET, MASK, VALUE)      (0XFF5E0238, 0x00000006U ,0x00000000U)
    */
	PSU_Mask_Write(CRL_APB_RST_LPD_IOU2_OFFSET,
		0x00000006U, 0x00000000U);
/*##################################################################### */

    /*
    * UART BAUD RATE
    */
    /*
    * Register : Baud_rate_divider_reg0 @ 0XFF000034

    * Baud rate divider value: 0 - 3: ignored 4 - 255: Baud rate
    *  PSU_UART0_BAUD_RATE_DIVIDER_REG0_BDIV                       0x5

    * Baud Rate Divider Register
    * (OFFSET, MASK, VALUE)      (0XFF000034, 0x000000FFU ,0x00000005U)
    */
	PSU_Mask_Write(UART0_BAUD_RATE_DIVIDER_REG0_OFFSET,
		0x000000FFU, 0x00000005U);
/*##################################################################### */

    /*
    * Register : Baud_rate_gen_reg0 @ 0XFF000018

    * Baud Rate Clock Divisor Value: 0: Disables baud_sample 1: Clock divisor
    * bypass (baud_sample = sel_clk) 2 - 65535: baud_sample
    *  PSU_UART0_BAUD_RATE_GEN_REG0_CD                             0x8f

    * Baud Rate Generator Register.
    * (OFFSET, MASK, VALUE)      (0XFF000018, 0x0000FFFFU ,0x0000008FU)
    */
	PSU_Mask_Write(UART0_BAUD_RATE_GEN_REG0_OFFSET,
		0x0000FFFFU, 0x0000008FU);
/*##################################################################### */

    /*
    * Register : Control_reg0 @ 0XFF000000

    * Stop transmitter break: 0: no affect 1: stop transmission of the break a
    * fter a minimum of one character length and transmit a high level during
    * 12 bit periods. It can be set regardless of the value of STTBRK.
    *  PSU_UART0_CONTROL_REG0_STPBRK                               0x0

    * Start transmitter break: 0: no affect 1: start to transmit a break after
    *  the characters currently present in the FIFO and the transmit shift reg
    * ister have been transmitted. It can only be set if STPBRK (Stop transmit
    * ter break) is not high.
    *  PSU_UART0_CONTROL_REG0_STTBRK                               0x0

    * Restart receiver timeout counter: 1: receiver timeout counter is restart
    * ed. This bit is self clearing once the restart has completed.
    *  PSU_UART0_CONTROL_REG0_RSTTO                                0x0

    * Transmit disable: 0: enable transmitter 1: disable transmitter
    *  PSU_UART0_CONTROL_REG0_TXDIS                                0x0

    * Transmit enable: 0: disable transmitter 1: enable transmitter, provided
    * the TXDIS field is set to 0.
    *  PSU_UART0_CONTROL_REG0_TXEN                                 0x1

    * Receive disable: 0: enable 1: disable, regardless of the value of RXEN
    *  PSU_UART0_CONTROL_REG0_RXDIS                                0x0

    * Receive enable: 0: disable 1: enable When set to one, the receiver logic
    *  is enabled, provided the RXDIS field is set to zero.
    *  PSU_UART0_CONTROL_REG0_RXEN                                 0x1

    * Software reset for Tx data path: 0: no affect 1: transmitter logic is re
    * set and all pending transmitter data is discarded This bit is self clear
    * ing once the reset has completed.
    *  PSU_UART0_CONTROL_REG0_TXRES                                0x1

    * Software reset for Rx data path: 0: no affect 1: receiver logic is reset
    *  and all pending receiver data is discarded. This bit is self clearing o
    * nce the reset has completed.
    *  PSU_UART0_CONTROL_REG0_RXRES                                0x1

    * UART Control Register
    * (OFFSET, MASK, VALUE)      (0XFF000000, 0x000001FFU ,0x00000017U)
    */
	PSU_Mask_Write(UART0_CONTROL_REG0_OFFSET, 0x000001FFU, 0x00000017U);
/*##################################################################### */

    /*
    * Register : mode_reg0 @ 0XFF000004

    * Channel mode: Defines the mode of operation of the UART. 00: normal 01:
    * automatic echo 10: local loopback 11: remote loopback
    *  PSU_UART0_MODE_REG0_CHMODE                                  0x0

    * Number of stop bits: Defines the number of stop bits to detect on receiv
    * e and to generate on transmit. 00: 1 stop bit 01: 1.5 stop bits 10: 2 st
    * op bits 11: reserved
    *  PSU_UART0_MODE_REG0_NBSTOP                                  0x0

    * Parity type select: Defines the expected parity to check on receive and
    * the parity to generate on transmit. 000: even parity 001: odd parity 010
    * : forced to 0 parity (space) 011: forced to 1 parity (mark) 1xx: no pari
    * ty
    *  PSU_UART0_MODE_REG0_PAR                                     0x4

    * Character length select: Defines the number of bits in each character. 1
    * 1: 6 bits 10: 7 bits 0x: 8 bits
    *  PSU_UART0_MODE_REG0_CHRL                                    0x0

    * Clock source select: This field defines whether a pre-scalar of 8 is app
    * lied to the baud rate generator input clock. 0: clock source is uart_ref
    * _clk 1: clock source is uart_ref_clk/8
    *  PSU_UART0_MODE_REG0_CLKS                                    0x0

    * UART Mode Register
    * (OFFSET, MASK, VALUE)      (0XFF000004, 0x000003FFU ,0x00000020U)
    */
	PSU_Mask_Write(UART0_MODE_REG0_OFFSET, 0x000003FFU, 0x00000020U);
/*##################################################################### */

    /*
    * Register : Baud_rate_divider_reg0 @ 0XFF010034

    * Baud rate divider value: 0 - 3: ignored 4 - 255: Baud rate
    *  PSU_UART1_BAUD_RATE_DIVIDER_REG0_BDIV                       0x5

    * Baud Rate Divider Register
    * (OFFSET, MASK, VALUE)      (0XFF010034, 0x000000FFU ,0x00000005U)
    */
	PSU_Mask_Write(UART1_BAUD_RATE_DIVIDER_REG0_OFFSET,
		0x000000FFU, 0x00000005U);
/*##################################################################### */

    /*
    * Register : Baud_rate_gen_reg0 @ 0XFF010018

    * Baud Rate Clock Divisor Value: 0: Disables baud_sample 1: Clock divisor
    * bypass (baud_sample = sel_clk) 2 - 65535: baud_sample
    *  PSU_UART1_BAUD_RATE_GEN_REG0_CD                             0x8f

    * Baud Rate Generator Register.
    * (OFFSET, MASK, VALUE)      (0XFF010018, 0x0000FFFFU ,0x0000008FU)
    */
	PSU_Mask_Write(UART1_BAUD_RATE_GEN_REG0_OFFSET,
		0x0000FFFFU, 0x0000008FU);
/*##################################################################### */

    /*
    * Register : Control_reg0 @ 0XFF010000

    * Stop transmitter break: 0: no affect 1: stop transmission of the break a
    * fter a minimum of one character length and transmit a high level during
    * 12 bit periods. It can be set regardless of the value of STTBRK.
    *  PSU_UART1_CONTROL_REG0_STPBRK                               0x0

    * Start transmitter break: 0: no affect 1: start to transmit a break after
    *  the characters currently present in the FIFO and the transmit shift reg
    * ister have been transmitted. It can only be set if STPBRK (Stop transmit
    * ter break) is not high.
    *  PSU_UART1_CONTROL_REG0_STTBRK                               0x0

    * Restart receiver timeout counter: 1: receiver timeout counter is restart
    * ed. This bit is self clearing once the restart has completed.
    *  PSU_UART1_CONTROL_REG0_RSTTO                                0x0

    * Transmit disable: 0: enable transmitter 1: disable transmitter
    *  PSU_UART1_CONTROL_REG0_TXDIS                                0x0

    * Transmit enable: 0: disable transmitter 1: enable transmitter, provided
    * the TXDIS field is set to 0.
    *  PSU_UART1_CONTROL_REG0_TXEN                                 0x1

    * Receive disable: 0: enable 1: disable, regardless of the value of RXEN
    *  PSU_UART1_CONTROL_REG0_RXDIS                                0x0

    * Receive enable: 0: disable 1: enable When set to one, the receiver logic
    *  is enabled, provided the RXDIS field is set to zero.
    *  PSU_UART1_CONTROL_REG0_RXEN                                 0x1

    * Software reset for Tx data path: 0: no affect 1: transmitter logic is re
    * set and all pending transmitter data is discarded This bit is self clear
    * ing once the reset has completed.
    *  PSU_UART1_CONTROL_REG0_TXRES                                0x1

    * Software reset for Rx data path: 0: no affect 1: receiver logic is reset
    *  and all pending receiver data is discarded. This bit is self clearing o
    * nce the reset has completed.
    *  PSU_UART1_CONTROL_REG0_RXRES                                0x1

    * UART Control Register
    * (OFFSET, MASK, VALUE)      (0XFF010000, 0x000001FFU ,0x00000017U)
    */
	PSU_Mask_Write(UART1_CONTROL_REG0_OFFSET, 0x000001FFU, 0x00000017U);
/*##################################################################### */

    /*
    * Register : mode_reg0 @ 0XFF010004

    * Channel mode: Defines the mode of operation of the UART. 00: normal 01:
    * automatic echo 10: local loopback 11: remote loopback
    *  PSU_UART1_MODE_REG0_CHMODE                                  0x0

    * Number of stop bits: Defines the number of stop bits to detect on receiv
    * e and to generate on transmit. 00: 1 stop bit 01: 1.5 stop bits 10: 2 st
    * op bits 11: reserved
    *  PSU_UART1_MODE_REG0_NBSTOP                                  0x0

    * Parity type select: Defines the expected parity to check on receive and
    * the parity to generate on transmit. 000: even parity 001: odd parity 010
    * : forced to 0 parity (space) 011: forced to 1 parity (mark) 1xx: no pari
    * ty
    *  PSU_UART1_MODE_REG0_PAR                                     0x4

    * Character length select: Defines the number of bits in each character. 1
    * 1: 6 bits 10: 7 bits 0x: 8 bits
    *  PSU_UART1_MODE_REG0_CHRL                                    0x0

    * Clock source select: This field defines whether a pre-scalar of 8 is app
    * lied to the baud rate generator input clock. 0: clock source is uart_ref
    * _clk 1: clock source is uart_ref_clk/8
    *  PSU_UART1_MODE_REG0_CLKS                                    0x0

    * UART Mode Register
    * (OFFSET, MASK, VALUE)      (0XFF010004, 0x000003FFU ,0x00000020U)
    */
	PSU_Mask_Write(UART1_MODE_REG0_OFFSET, 0x000003FFU, 0x00000020U);
/*##################################################################### */

    /*
    * GPIO
    */
    /*
    * Register : RST_LPD_IOU2 @ 0XFF5E0238

    * Block level reset
    *  PSU_CRL_APB_RST_LPD_IOU2_GPIO_RESET                         0

    * Software control register for the IOU block. Each bit will cause a singl
    * erperipheral or part of the peripheral to be reset.
    * (OFFSET, MASK, VALUE)      (0XFF5E0238, 0x00040000U ,0x00000000U)
    */
	PSU_Mask_Write(CRL_APB_RST_LPD_IOU2_OFFSET,
		0x00040000U, 0x00000000U);
/*##################################################################### */

    /*
    * ADMA TZ
    */
    /*
    * Register : slcr_adma @ 0XFF4B0024

    * TrustZone Classification for ADMA
    *  PSU_LPD_SLCR_SECURE_SLCR_ADMA_TZ                            0XFF

    * RPU TrustZone settings
    * (OFFSET, MASK, VALUE)      (0XFF4B0024, 0x000000FFU ,0x000000FFU)
    */
	PSU_Mask_Write(LPD_SLCR_SECURE_SLCR_ADMA_OFFSET,
		0x000000FFU, 0x000000FFU);
/*##################################################################### */

    /*
    * CSU TAMPERING
    */
    /*
    * CSU TAMPER STATUS
    */
    /*
    * Register : tamper_status @ 0XFFCA5000

    * CSU regsiter
    *  PSU_CSU_TAMPER_STATUS_TAMPER_0                              0

    * External MIO
    *  PSU_CSU_TAMPER_STATUS_TAMPER_1                              0

    * JTAG toggle detect
    *  PSU_CSU_TAMPER_STATUS_TAMPER_2                              0

    * PL SEU error
    *  PSU_CSU_TAMPER_STATUS_TAMPER_3                              0

    * AMS over temperature alarm for LPD
    *  PSU_CSU_TAMPER_STATUS_TAMPER_4                              0

    * AMS over temperature alarm for APU
    *  PSU_CSU_TAMPER_STATUS_TAMPER_5                              0

    * AMS voltage alarm for VCCPINT_FPD
    *  PSU_CSU_TAMPER_STATUS_TAMPER_6                              0

    * AMS voltage alarm for VCCPINT_LPD
    *  PSU_CSU_TAMPER_STATUS_TAMPER_7                              0

    * AMS voltage alarm for VCCPAUX
    *  PSU_CSU_TAMPER_STATUS_TAMPER_8                              0

    * AMS voltage alarm for DDRPHY
    *  PSU_CSU_TAMPER_STATUS_TAMPER_9                              0

    * AMS voltage alarm for PSIO bank 0/1/2
    *  PSU_CSU_TAMPER_STATUS_TAMPER_10                             0

    * AMS voltage alarm for PSIO bank 3 (dedicated pins)
    *  PSU_CSU_TAMPER_STATUS_TAMPER_11                             0

    * AMS voltaage alarm for GT
    *  PSU_CSU_TAMPER_STATUS_TAMPER_12                             0

    * Tamper Response Status
    * (OFFSET, MASK, VALUE)      (0XFFCA5000, 0x00001FFFU ,0x00000000U)
    */
	PSU_Mask_Write(CSU_TAMPER_STATUS_OFFSET, 0x00001FFFU, 0x00000000U);
/*##################################################################### */

    /*
    * CSU TAMPER RESPONSE
    */
    /*
    * CPU QOS DEFAULT
    */
    /*
    * Register : ACE_CTRL @ 0XFD5C0060

    * Set ACE outgoing AWQOS value
    *  PSU_APU_ACE_CTRL_AWQOS                                      0X0

    * Set ACE outgoing ARQOS value
    *  PSU_APU_ACE_CTRL_ARQOS                                      0X0

    * ACE Control Register
    * (OFFSET, MASK, VALUE)      (0XFD5C0060, 0x000F000FU ,0x00000000U)
    */
	PSU_Mask_Write(APU_ACE_CTRL_OFFSET, 0x000F000FU, 0x00000000U);
/*##################################################################### */

    /*
    * ENABLES RTC SWITCH TO BATTERY WHEN VCC_PSAUX IS NOT AVAILABLE
    */
    /*
    * Register : CONTROL @ 0XFFA60040

    * Enables the RTC. By writing a 0 to this bit, RTC will be powered off and
    *  the only module that potentially draws current from the battery will be
    *  BBRAM. The value read through this bit does not necessarily reflect whe
    * ther RTC is enabled or not. It is expected that RTC is enabled every tim
    * e it is being configured. If RTC is not used in the design, FSBL will di
    * sable it by writing a 0 to this bit.
    *  PSU_RTC_CONTROL_BATTERY_DISABLE                             0X1

    * This register controls various functionalities within the RTC
    * (OFFSET, MASK, VALUE)      (0XFFA60040, 0x80000000U ,0x80000000U)
    */
	PSU_Mask_Write(RTC_CONTROL_OFFSET, 0x80000000U, 0x80000000U);
/*##################################################################### */

    /*
    * TIMESTAMP COUNTER
    */
    /*
    * Register : base_frequency_ID_register @ 0XFF260020

    * Frequency in number of ticks per second. Valid range from 10 MHz to 100
    * MHz.
    *  PSU_IOU_SCNTRS_BASE_FREQUENCY_ID_REGISTER_FREQ              0x5f5b9f0

    * Program this register to match the clock frequency of the timestamp gene
    * rator, in ticks per second. For example, for a 50 MHz clock, program 0x0
    * 2FAF080. This register is not accessible to the read-only programming in
    * terface.
    * (OFFSET, MASK, VALUE)      (0XFF260020, 0xFFFFFFFFU ,0x05F5B9F0U)
    */
	PSU_Mask_Write(IOU_SCNTRS_BASE_FREQUENCY_ID_REGISTER_OFFSET,
		0xFFFFFFFFU, 0x05F5B9F0U);
/*##################################################################### */

    /*
    * Register : counter_control_register @ 0XFF260000

    * Enable 0: The counter is disabled and not incrementing. 1: The counter i
    * s enabled and is incrementing.
    *  PSU_IOU_SCNTRS_COUNTER_CONTROL_REGISTER_EN                  0x1

    * Controls the counter increments. This register is not accessible to the
    * read-only programming interface.
    * (OFFSET, MASK, VALUE)      (0XFF260000, 0x00000001U ,0x00000001U)
    */
	PSU_Mask_Write(IOU_SCNTRS_COUNTER_CONTROL_REGISTER_OFFSET,
		0x00000001U, 0x00000001U);
/*##################################################################### */

    /*
    * TTC SRC SELECT
    */
    /*
    * PCIE GPIO RESET
    */
    /*
    * PCIE RESET
    */
    /*
    * DIR MODE BANK 0
    */
    /*
    * DIR MODE BANK 1
    */
    /*
    * Register : DIRM_1 @ 0XFF0A0244

    * Operation is the same as DIRM_0[DIRECTION_0]
    *  PSU_GPIO_DIRM_1_DIRECTION_1                                 0x20

    * Direction mode (GPIO Bank1, MIO)
    * (OFFSET, MASK, VALUE)      (0XFF0A0244, 0x03FFFFFFU ,0x00000020U)
    */
	PSU_Mask_Write(GPIO_DIRM_1_OFFSET, 0x03FFFFFFU, 0x00000020U);
/*##################################################################### */

    /*
    * DIR MODE BANK 2
    */
    /*
    * OUTPUT ENABLE BANK 0
    */
    /*
    * OUTPUT ENABLE BANK 1
    */
    /*
    * Register : OEN_1 @ 0XFF0A0248

    * Operation is the same as OEN_0[OP_ENABLE_0]
    *  PSU_GPIO_OEN_1_OP_ENABLE_1                                  0x20

    * Output enable (GPIO Bank1, MIO)
    * (OFFSET, MASK, VALUE)      (0XFF0A0248, 0x03FFFFFFU ,0x00000020U)
    */
	PSU_Mask_Write(GPIO_OEN_1_OFFSET, 0x03FFFFFFU, 0x00000020U);
/*##################################################################### */

    /*
    * OUTPUT ENABLE BANK 2
    */
    /*
    * MASK_DATA_0_LSW LOW BANK [15:0]
    */
    /*
    * MASK_DATA_0_MSW LOW BANK [25:16]
    */
    /*
    * MASK_DATA_1_LSW LOW BANK [41:26]
    */
    /*
    * Register : MASK_DATA_1_LSW @ 0XFF0A0008

    * Operation is the same as MASK_DATA_0_LSW[MASK_0_LSW]
    *  PSU_GPIO_MASK_DATA_1_LSW_MASK_1_LSW                         0xffdf

    * Operation is the same as MASK_DATA_0_LSW[DATA_0_LSW]
    *  PSU_GPIO_MASK_DATA_1_LSW_DATA_1_LSW                         0x20

    * Maskable Output Data (GPIO Bank1, MIO, Lower 16bits)
    * (OFFSET, MASK, VALUE)      (0XFF0A0008, 0xFFFFFFFFU ,0xFFDF0020U)
    */
	PSU_Mask_Write(GPIO_MASK_DATA_1_LSW_OFFSET,
		0xFFFFFFFFU, 0xFFDF0020U);
/*##################################################################### */

    /*
    * MASK_DATA_1_MSW HIGH BANK [51:42]
    */
    /*
    * MASK_DATA_1_LSW HIGH BANK [67:52]
    */
    /*
    * MASK_DATA_1_LSW HIGH BANK [77:68]
    */
    /*
    * ADD 1 MS DELAY
    */
		mask_delay(1);

/*##################################################################### */

    /*
    * MASK_DATA_0_LSW LOW BANK [15:0]
    */
    /*
    * MASK_DATA_0_MSW LOW BANK [25:16]
    */
    /*
    * MASK_DATA_1_LSW LOW BANK [41:26]
    */
    /*
    * Register : MASK_DATA_1_LSW @ 0XFF0A0008

    * Operation is the same as MASK_DATA_0_LSW[MASK_0_LSW]
    *  PSU_GPIO_MASK_DATA_1_LSW_MASK_1_LSW                         0xffdf

    * Operation is the same as MASK_DATA_0_LSW[DATA_0_LSW]
    *  PSU_GPIO_MASK_DATA_1_LSW_DATA_1_LSW                         0x0

    * Maskable Output Data (GPIO Bank1, MIO, Lower 16bits)
    * (OFFSET, MASK, VALUE)      (0XFF0A0008, 0xFFFFFFFFU ,0xFFDF0000U)
    */
	PSU_Mask_Write(GPIO_MASK_DATA_1_LSW_OFFSET,
		0xFFFFFFFFU, 0xFFDF0000U);
/*##################################################################### */

    /*
    * MASK_DATA_1_MSW HIGH BANK [51:42]
    */
    /*
    * MASK_DATA_1_LSW HIGH BANK [67:52]
    */
    /*
    * MASK_DATA_1_LSW HIGH BANK [77:68]
    */
    /*
    * ADD 5 MS DELAY
    */
		mask_delay(5);

/*##################################################################### */


	return 1;
}
unsigned long psu_post_config_data(void)
{
    /*
    * POST_CONFIG
    */

	return 1;
}
unsigned long psu_peripherals_powerdwn_data(void)
{
    /*
    * POWER DOWN REQUEST INTERRUPT ENABLE
    */
    /*
    * POWER DOWN TRIGGER
    */

	return 1;
}
unsigned long psu_lpd_xppu_data(void)
{
    /*
    * MASTER ID LIST
    */
    /*
    * APERTURE PERMISIION LIST
    */
    /*
    * APERTURE NAME: UART0, START ADDRESS: FF000000, END ADDRESS: FF00FFFF
    */
    /*
    * APERTURE NAME: UART1, START ADDRESS: FF010000, END ADDRESS: FF01FFFF
    */
    /*
    * APERTURE NAME: I2C0, START ADDRESS: FF020000, END ADDRESS: FF02FFFF
    */
    /*
    * APERTURE NAME: I2C1, START ADDRESS: FF030000, END ADDRESS: FF03FFFF
    */
    /*
    * APERTURE NAME: SPI0, START ADDRESS: FF040000, END ADDRESS: FF04FFFF
    */
    /*
    * APERTURE NAME: SPI1, START ADDRESS: FF050000, END ADDRESS: FF05FFFF
    */
    /*
    * APERTURE NAME: CAN0, START ADDRESS: FF060000, END ADDRESS: FF06FFFF
    */
    /*
    * APERTURE NAME: CAN1, START ADDRESS: FF070000, END ADDRESS: FF07FFFF
    */
    /*
    * APERTURE NAME: RPU_UNUSED_12, START ADDRESS: FF080000, END ADDRESS: FF09
    * FFFF
    */
    /*
    * APERTURE NAME: RPU_UNUSED_12, START ADDRESS: FF080000, END ADDRESS: FF09
    * FFFF
    */
    /*
    * APERTURE NAME: GPIO, START ADDRESS: FF0A0000, END ADDRESS: FF0AFFFF
    */
    /*
    * APERTURE NAME: GEM0, START ADDRESS: FF0B0000, END ADDRESS: FF0BFFFF
    */
    /*
    * APERTURE NAME: GEM1, START ADDRESS: FF0C0000, END ADDRESS: FF0CFFFF
    */
    /*
    * APERTURE NAME: GEM2, START ADDRESS: FF0D0000, END ADDRESS: FF0DFFFF
    */
    /*
    * APERTURE NAME: GEM3, START ADDRESS: FF0E0000, END ADDRESS: FF0EFFFF
    */
    /*
    * APERTURE NAME: QSPI, START ADDRESS: FF0F0000, END ADDRESS: FF0FFFFF
    */
    /*
    * APERTURE NAME: NAND, START ADDRESS: FF100000, END ADDRESS: FF10FFFF
    */
    /*
    * APERTURE NAME: TTC0, START ADDRESS: FF110000, END ADDRESS: FF11FFFF
    */
    /*
    * APERTURE NAME: TTC1, START ADDRESS: FF120000, END ADDRESS: FF12FFFF
    */
    /*
    * APERTURE NAME: TTC2, START ADDRESS: FF130000, END ADDRESS: FF13FFFF
    */
    /*
    * APERTURE NAME: TTC3, START ADDRESS: FF140000, END ADDRESS: FF14FFFF
    */
    /*
    * APERTURE NAME: SWDT, START ADDRESS: FF150000, END ADDRESS: FF15FFFF
    */
    /*
    * APERTURE NAME: SD0, START ADDRESS: FF160000, END ADDRESS: FF16FFFF
    */
    /*
    * APERTURE NAME: SD1, START ADDRESS: FF170000, END ADDRESS: FF17FFFF
    */
    /*
    * APERTURE NAME: IOU_SLCR, START ADDRESS: FF180000, END ADDRESS: FF23FFFF
    */
    /*
    * APERTURE NAME: IOU_SLCR, START ADDRESS: FF180000, END ADDRESS: FF23FFFF
    */
    /*
    * APERTURE NAME: IOU_SLCR, START ADDRESS: FF180000, END ADDRESS: FF23FFFF
    */
    /*
    * APERTURE NAME: IOU_SLCR, START ADDRESS: FF180000, END ADDRESS: FF23FFFF
    */
    /*
    * APERTURE NAME: IOU_SLCR, START ADDRESS: FF180000, END ADDRESS: FF23FFFF
    */
    /*
    * APERTURE NAME: IOU_SLCR, START ADDRESS: FF180000, END ADDRESS: FF23FFFF
    */
    /*
    * APERTURE NAME: IOU_SLCR, START ADDRESS: FF180000, END ADDRESS: FF23FFFF
    */
    /*
    * APERTURE NAME: IOU_SLCR, START ADDRESS: FF180000, END ADDRESS: FF23FFFF
    */
    /*
    * APERTURE NAME: IOU_SLCR, START ADDRESS: FF180000, END ADDRESS: FF23FFFF
    */
    /*
    * APERTURE NAME: IOU_SLCR, START ADDRESS: FF180000, END ADDRESS: FF23FFFF
    */
    /*
    * APERTURE NAME: IOU_SLCR, START ADDRESS: FF180000, END ADDRESS: FF23FFFF
    */
    /*
    * APERTURE NAME: IOU_SLCR, START ADDRESS: FF180000, END ADDRESS: FF23FFFF
    */
    /*
    * APERTURE NAME: IOU_SECURE_SLCR, START ADDRESS: FF240000, END ADDRESS: FF
    * 24FFFF
    */
    /*
    * APERTURE NAME: IOU_SCNTR, START ADDRESS: FF250000, END ADDRESS: FF25FFFF
    */
    /*
    * APERTURE NAME: IOU_SCNTRS, START ADDRESS: FF260000, END ADDRESS: FF26FFF
    * F
    */
    /*
    * APERTURE NAME: RPU_UNUSED_11, START ADDRESS: FF270000, END ADDRESS: FF2A
    * FFFF
    */
    /*
    * APERTURE NAME: RPU_UNUSED_11, START ADDRESS: FF270000, END ADDRESS: FF2A
    * FFFF
    */
    /*
    * APERTURE NAME: RPU_UNUSED_11, START ADDRESS: FF270000, END ADDRESS: FF2A
    * FFFF
    */
    /*
    * APERTURE NAME: RPU_UNUSED_11, START ADDRESS: FF270000, END ADDRESS: FF2A
    * FFFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_14, START ADDRESS: FF2B0000, END ADDRESS: FF2F
    * FFFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_14, START ADDRESS: FF2B0000, END ADDRESS: FF2F
    * FFFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_14, START ADDRESS: FF2B0000, END ADDRESS: FF2F
    * FFFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_14, START ADDRESS: FF2B0000, END ADDRESS: FF2F
    * FFFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_14, START ADDRESS: FF2B0000, END ADDRESS: FF2F
    * FFFF
    */
    /*
    * APERTURE NAME: IPI_0, START ADDRESS: FF300000, END ADDRESS: FF30FFFF
    */
    /*
    * APERTURE NAME: IPI_1, START ADDRESS: FF310000, END ADDRESS: FF31FFFF
    */
    /*
    * APERTURE NAME: IPI_2, START ADDRESS: FF320000, END ADDRESS: FF32FFFF
    */
    /*
    * APERTURE NAME: IPI_PMU, START ADDRESS: FF330000, END ADDRESS: FF33FFFF
    */
    /*
    * APERTURE NAME: IPI_7, START ADDRESS: FF340000, END ADDRESS: FF34FFFF
    */
    /*
    * APERTURE NAME: IPI_8, START ADDRESS: FF350000, END ADDRESS: FF35FFFF
    */
    /*
    * APERTURE NAME: IPI_9, START ADDRESS: FF360000, END ADDRESS: FF36FFFF
    */
    /*
    * APERTURE NAME: IPI_10, START ADDRESS: FF370000, END ADDRESS: FF37FFFF
    */
    /*
    * APERTURE NAME: IPI_CTRL, START ADDRESS: FF380000, END ADDRESS: FF3FFFFF
    */
    /*
    * APERTURE NAME: IPI_CTRL, START ADDRESS: FF380000, END ADDRESS: FF3FFFFF
    */
    /*
    * APERTURE NAME: IPI_CTRL, START ADDRESS: FF380000, END ADDRESS: FF3FFFFF
    */
    /*
    * APERTURE NAME: IPI_CTRL, START ADDRESS: FF380000, END ADDRESS: FF3FFFFF
    */
    /*
    * APERTURE NAME: IPI_CTRL, START ADDRESS: FF380000, END ADDRESS: FF3FFFFF
    */
    /*
    * APERTURE NAME: IPI_CTRL, START ADDRESS: FF380000, END ADDRESS: FF3FFFFF
    */
    /*
    * APERTURE NAME: IPI_CTRL, START ADDRESS: FF380000, END ADDRESS: FF3FFFFF
    */
    /*
    * APERTURE NAME: IPI_CTRL, START ADDRESS: FF380000, END ADDRESS: FF3FFFFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_1, START ADDRESS: FF400000, END ADDRESS: FF40F
    * FFF
    */
    /*
    * APERTURE NAME: LPD_SLCR, START ADDRESS: FF410000, END ADDRESS: FF4AFFFF
    */
    /*
    * APERTURE NAME: LPD_SLCR, START ADDRESS: FF410000, END ADDRESS: FF4AFFFF
    */
    /*
    * APERTURE NAME: LPD_SLCR, START ADDRESS: FF410000, END ADDRESS: FF4AFFFF
    */
    /*
    * APERTURE NAME: LPD_SLCR, START ADDRESS: FF410000, END ADDRESS: FF4AFFFF
    */
    /*
    * APERTURE NAME: LPD_SLCR, START ADDRESS: FF410000, END ADDRESS: FF4AFFFF
    */
    /*
    * APERTURE NAME: LPD_SLCR, START ADDRESS: FF410000, END ADDRESS: FF4AFFFF
    */
    /*
    * APERTURE NAME: LPD_SLCR, START ADDRESS: FF410000, END ADDRESS: FF4AFFFF
    */
    /*
    * APERTURE NAME: LPD_SLCR, START ADDRESS: FF410000, END ADDRESS: FF4AFFFF
    */
    /*
    * APERTURE NAME: LPD_SLCR, START ADDRESS: FF410000, END ADDRESS: FF4AFFFF
    */
    /*
    * APERTURE NAME: LPD_SLCR, START ADDRESS: FF410000, END ADDRESS: FF4AFFFF
    */
    /*
    * APERTURE NAME: LPD_SLCR_SECURE, START ADDRESS: FF4B0000, END ADDRESS: FF
    * 4DFFFF
    */
    /*
    * APERTURE NAME: LPD_SLCR_SECURE, START ADDRESS: FF4B0000, END ADDRESS: FF
    * 4DFFFF
    */
    /*
    * APERTURE NAME: LPD_SLCR_SECURE, START ADDRESS: FF4B0000, END ADDRESS: FF
    * 4DFFFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_2, START ADDRESS: FF4E0000, END ADDRESS: FF5DF
    * FFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_2, START ADDRESS: FF4E0000, END ADDRESS: FF5DF
    * FFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_2, START ADDRESS: FF4E0000, END ADDRESS: FF5DF
    * FFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_2, START ADDRESS: FF4E0000, END ADDRESS: FF5DF
    * FFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_2, START ADDRESS: FF4E0000, END ADDRESS: FF5DF
    * FFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_2, START ADDRESS: FF4E0000, END ADDRESS: FF5DF
    * FFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_2, START ADDRESS: FF4E0000, END ADDRESS: FF5DF
    * FFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_2, START ADDRESS: FF4E0000, END ADDRESS: FF5DF
    * FFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_2, START ADDRESS: FF4E0000, END ADDRESS: FF5DF
    * FFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_2, START ADDRESS: FF4E0000, END ADDRESS: FF5DF
    * FFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_2, START ADDRESS: FF4E0000, END ADDRESS: FF5DF
    * FFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_2, START ADDRESS: FF4E0000, END ADDRESS: FF5DF
    * FFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_2, START ADDRESS: FF4E0000, END ADDRESS: FF5DF
    * FFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_2, START ADDRESS: FF4E0000, END ADDRESS: FF5DF
    * FFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_2, START ADDRESS: FF4E0000, END ADDRESS: FF5DF
    * FFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_2, START ADDRESS: FF4E0000, END ADDRESS: FF5DF
    * FFF
    */
    /*
    * APERTURE NAME: CRL_APB, START ADDRESS: FF5E0000, END ADDRESS: FF85FFFF
    */
    /*
    * APERTURE NAME: CRL_APB, START ADDRESS: FF5E0000, END ADDRESS: FF85FFFF
    */
    /*
    * APERTURE NAME: CRL_APB, START ADDRESS: FF5E0000, END ADDRESS: FF85FFFF
    */
    /*
    * APERTURE NAME: CRL_APB, START ADDRESS: FF5E0000, END ADDRESS: FF85FFFF
    */
    /*
    * APERTURE NAME: CRL_APB, START ADDRESS: FF5E0000, END ADDRESS: FF85FFFF
    */
    /*
    * APERTURE NAME: CRL_APB, START ADDRESS: FF5E0000, END ADDRESS: FF85FFFF
    */
    /*
    * APERTURE NAME: CRL_APB, START ADDRESS: FF5E0000, END ADDRESS: FF85FFFF
    */
    /*
    * APERTURE NAME: CRL_APB, START ADDRESS: FF5E0000, END ADDRESS: FF85FFFF
    */
    /*
    * APERTURE NAME: CRL_APB, START ADDRESS: FF5E0000, END ADDRESS: FF85FFFF
    */
    /*
    * APERTURE NAME: CRL_APB, START ADDRESS: FF5E0000, END ADDRESS: FF85FFFF
    */
    /*
    * APERTURE NAME: CRL_APB, START ADDRESS: FF5E0000, END ADDRESS: FF85FFFF
    */
    /*
    * APERTURE NAME: CRL_APB, START ADDRESS: FF5E0000, END ADDRESS: FF85FFFF
    */
    /*
    * APERTURE NAME: CRL_APB, START ADDRESS: FF5E0000, END ADDRESS: FF85FFFF
    */
    /*
    * APERTURE NAME: CRL_APB, START ADDRESS: FF5E0000, END ADDRESS: FF85FFFF
    */
    /*
    * APERTURE NAME: CRL_APB, START ADDRESS: FF5E0000, END ADDRESS: FF85FFFF
    */
    /*
    * APERTURE NAME: CRL_APB, START ADDRESS: FF5E0000, END ADDRESS: FF85FFFF
    */
    /*
    * APERTURE NAME: CRL_APB, START ADDRESS: FF5E0000, END ADDRESS: FF85FFFF
    */
    /*
    * APERTURE NAME: CRL_APB, START ADDRESS: FF5E0000, END ADDRESS: FF85FFFF
    */
    /*
    * APERTURE NAME: CRL_APB, START ADDRESS: FF5E0000, END ADDRESS: FF85FFFF
    */
    /*
    * APERTURE NAME: CRL_APB, START ADDRESS: FF5E0000, END ADDRESS: FF85FFFF
    */
    /*
    * APERTURE NAME: CRL_APB, START ADDRESS: FF5E0000, END ADDRESS: FF85FFFF
    */
    /*
    * APERTURE NAME: CRL_APB, START ADDRESS: FF5E0000, END ADDRESS: FF85FFFF
    */
    /*
    * APERTURE NAME: CRL_APB, START ADDRESS: FF5E0000, END ADDRESS: FF85FFFF
    */
    /*
    * APERTURE NAME: CRL_APB, START ADDRESS: FF5E0000, END ADDRESS: FF85FFFF
    */
    /*
    * APERTURE NAME: CRL_APB, START ADDRESS: FF5E0000, END ADDRESS: FF85FFFF
    */
    /*
    * APERTURE NAME: CRL_APB, START ADDRESS: FF5E0000, END ADDRESS: FF85FFFF
    */
    /*
    * APERTURE NAME: CRL_APB, START ADDRESS: FF5E0000, END ADDRESS: FF85FFFF
    */
    /*
    * APERTURE NAME: CRL_APB, START ADDRESS: FF5E0000, END ADDRESS: FF85FFFF
    */
    /*
    * APERTURE NAME: CRL_APB, START ADDRESS: FF5E0000, END ADDRESS: FF85FFFF
    */
    /*
    * APERTURE NAME: CRL_APB, START ADDRESS: FF5E0000, END ADDRESS: FF85FFFF
    */
    /*
    * APERTURE NAME: CRL_APB, START ADDRESS: FF5E0000, END ADDRESS: FF85FFFF
    */
    /*
    * APERTURE NAME: CRL_APB, START ADDRESS: FF5E0000, END ADDRESS: FF85FFFF
    */
    /*
    * APERTURE NAME: CRL_APB, START ADDRESS: FF5E0000, END ADDRESS: FF85FFFF
    */
    /*
    * APERTURE NAME: CRL_APB, START ADDRESS: FF5E0000, END ADDRESS: FF85FFFF
    */
    /*
    * APERTURE NAME: CRL_APB, START ADDRESS: FF5E0000, END ADDRESS: FF85FFFF
    */
    /*
    * APERTURE NAME: CRL_APB, START ADDRESS: FF5E0000, END ADDRESS: FF85FFFF
    */
    /*
    * APERTURE NAME: CRL_APB, START ADDRESS: FF5E0000, END ADDRESS: FF85FFFF
    */
    /*
    * APERTURE NAME: CRL_APB, START ADDRESS: FF5E0000, END ADDRESS: FF85FFFF
    */
    /*
    * APERTURE NAME: CRL_APB, START ADDRESS: FF5E0000, END ADDRESS: FF85FFFF
    */
    /*
    * APERTURE NAME: CRL_APB, START ADDRESS: FF5E0000, END ADDRESS: FF85FFFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_3, START ADDRESS: FF860000, END ADDRESS: FF95F
    * FFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_3, START ADDRESS: FF860000, END ADDRESS: FF95F
    * FFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_3, START ADDRESS: FF860000, END ADDRESS: FF95F
    * FFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_3, START ADDRESS: FF860000, END ADDRESS: FF95F
    * FFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_3, START ADDRESS: FF860000, END ADDRESS: FF95F
    * FFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_3, START ADDRESS: FF860000, END ADDRESS: FF95F
    * FFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_3, START ADDRESS: FF860000, END ADDRESS: FF95F
    * FFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_3, START ADDRESS: FF860000, END ADDRESS: FF95F
    * FFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_3, START ADDRESS: FF860000, END ADDRESS: FF95F
    * FFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_3, START ADDRESS: FF860000, END ADDRESS: FF95F
    * FFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_3, START ADDRESS: FF860000, END ADDRESS: FF95F
    * FFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_3, START ADDRESS: FF860000, END ADDRESS: FF95F
    * FFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_3, START ADDRESS: FF860000, END ADDRESS: FF95F
    * FFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_3, START ADDRESS: FF860000, END ADDRESS: FF95F
    * FFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_3, START ADDRESS: FF860000, END ADDRESS: FF95F
    * FFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_3, START ADDRESS: FF860000, END ADDRESS: FF95F
    * FFF
    */
    /*
    * APERTURE NAME: OCM_SLCR, START ADDRESS: FF960000, END ADDRESS: FF96FFFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_4, START ADDRESS: FF970000, END ADDRESS: FF97F
    * FFF
    */
    /*
    * APERTURE NAME: LPD_XPPU, START ADDRESS: FF980000, END ADDRESS: FF99FFFF
    */
    /*
    * APERTURE NAME: RPU, START ADDRESS: FF9A0000, END ADDRESS: FF9AFFFF
    */
    /*
    * APERTURE NAME: AFIFM6, START ADDRESS: FF9B0000, END ADDRESS: FF9BFFFF
    */
    /*
    * APERTURE NAME: LPD_XPPU_SINK, START ADDRESS: FF9C0000, END ADDRESS: FF9C
    * FFFF
    */
    /*
    * APERTURE NAME: USB3_0, START ADDRESS: FF9D0000, END ADDRESS: FF9DFFFF
    */
    /*
    * APERTURE NAME: USB3_1, START ADDRESS: FF9E0000, END ADDRESS: FF9EFFFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_5, START ADDRESS: FF9F0000, END ADDRESS: FF9FF
    * FFF
    */
    /*
    * APERTURE NAME: APM0, START ADDRESS: FFA00000, END ADDRESS: FFA0FFFF
    */
    /*
    * APERTURE NAME: APM1, START ADDRESS: FFA10000, END ADDRESS: FFA1FFFF
    */
    /*
    * APERTURE NAME: APM_INTC_IOU, START ADDRESS: FFA20000, END ADDRESS: FFA2F
    * FFF
    */
    /*
    * APERTURE NAME: APM_FPD_LPD, START ADDRESS: FFA30000, END ADDRESS: FFA3FF
    * FF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_6, START ADDRESS: FFA40000, END ADDRESS: FFA4F
    * FFF
    */
    /*
    * APERTURE NAME: AMS, START ADDRESS: FFA50000, END ADDRESS: FFA5FFFF
    */
    /*
    * APERTURE NAME: RTC, START ADDRESS: FFA60000, END ADDRESS: FFA6FFFF
    */
    /*
    * APERTURE NAME: OCM_XMPU_CFG, START ADDRESS: FFA70000, END ADDRESS: FFA7F
    * FFF
    */
    /*
    * APERTURE NAME: ADMA_0, START ADDRESS: FFA80000, END ADDRESS: FFA8FFFF
    */
    /*
    * APERTURE NAME: ADMA_1, START ADDRESS: FFA90000, END ADDRESS: FFA9FFFF
    */
    /*
    * APERTURE NAME: ADMA_2, START ADDRESS: FFAA0000, END ADDRESS: FFAAFFFF
    */
    /*
    * APERTURE NAME: ADMA_3, START ADDRESS: FFAB0000, END ADDRESS: FFABFFFF
    */
    /*
    * APERTURE NAME: ADMA_4, START ADDRESS: FFAC0000, END ADDRESS: FFACFFFF
    */
    /*
    * APERTURE NAME: ADMA_5, START ADDRESS: FFAD0000, END ADDRESS: FFADFFFF
    */
    /*
    * APERTURE NAME: ADMA_6, START ADDRESS: FFAE0000, END ADDRESS: FFAEFFFF
    */
    /*
    * APERTURE NAME: ADMA_7, START ADDRESS: FFAF0000, END ADDRESS: FFAFFFFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_7, START ADDRESS: FFB00000, END ADDRESS: FFBFF
    * FFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_7, START ADDRESS: FFB00000, END ADDRESS: FFBFF
    * FFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_7, START ADDRESS: FFB00000, END ADDRESS: FFBFF
    * FFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_7, START ADDRESS: FFB00000, END ADDRESS: FFBFF
    * FFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_7, START ADDRESS: FFB00000, END ADDRESS: FFBFF
    * FFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_7, START ADDRESS: FFB00000, END ADDRESS: FFBFF
    * FFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_7, START ADDRESS: FFB00000, END ADDRESS: FFBFF
    * FFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_7, START ADDRESS: FFB00000, END ADDRESS: FFBFF
    * FFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_7, START ADDRESS: FFB00000, END ADDRESS: FFBFF
    * FFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_7, START ADDRESS: FFB00000, END ADDRESS: FFBFF
    * FFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_7, START ADDRESS: FFB00000, END ADDRESS: FFBFF
    * FFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_7, START ADDRESS: FFB00000, END ADDRESS: FFBFF
    * FFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_7, START ADDRESS: FFB00000, END ADDRESS: FFBFF
    * FFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_7, START ADDRESS: FFB00000, END ADDRESS: FFBFF
    * FFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_7, START ADDRESS: FFB00000, END ADDRESS: FFBFF
    * FFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_7, START ADDRESS: FFB00000, END ADDRESS: FFBFF
    * FFF
    */
    /*
    * APERTURE NAME: CSU_ROM, START ADDRESS: FFC00000, END ADDRESS: FFC1FFFF
    */
    /*
    * APERTURE NAME: CSU_ROM, START ADDRESS: FFC00000, END ADDRESS: FFC1FFFF
    */
    /*
    * APERTURE NAME: CSU_LOCAL, START ADDRESS: FFC20000, END ADDRESS: FFC2FFFF
    */
    /*
    * APERTURE NAME: PUF, START ADDRESS: FFC30000, END ADDRESS: FFC3FFFF
    */
    /*
    * APERTURE NAME: CSU_RAM, START ADDRESS: FFC40000, END ADDRESS: FFC5FFFF
    */
    /*
    * APERTURE NAME: CSU_RAM, START ADDRESS: FFC40000, END ADDRESS: FFC5FFFF
    */
    /*
    * APERTURE NAME: CSU_IOMODULE, START ADDRESS: FFC60000, END ADDRESS: FFC7F
    * FFF
    */
    /*
    * APERTURE NAME: CSU_IOMODULE, START ADDRESS: FFC60000, END ADDRESS: FFC7F
    * FFF
    */
    /*
    * APERTURE NAME: CSUDMA, START ADDRESS: FFC80000, END ADDRESS: FFC9FFFF
    */
    /*
    * APERTURE NAME: CSUDMA, START ADDRESS: FFC80000, END ADDRESS: FFC9FFFF
    */
    /*
    * APERTURE NAME: CSU, START ADDRESS: FFCA0000, END ADDRESS: FFCAFFFF
    */
    /*
    * APERTURE NAME: CSU_WDT, START ADDRESS: FFCB0000, END ADDRESS: FFCBFFFF
    */
    /*
    * APERTURE NAME: EFUSE, START ADDRESS: FFCC0000, END ADDRESS: FFCCFFFF
    */
    /*
    * APERTURE NAME: BBRAM, START ADDRESS: FFCD0000, END ADDRESS: FFCDFFFF
    */
    /*
    * APERTURE NAME: RSA_CORE, START ADDRESS: FFCE0000, END ADDRESS: FFCEFFFF
    */
    /*
    * APERTURE NAME: MBISTJTAG, START ADDRESS: FFCF0000, END ADDRESS: FFCFFFFF
    */
    /*
    * APERTURE NAME: PMU_ROM, START ADDRESS: FFD00000, END ADDRESS: FFD3FFFF
    */
    /*
    * APERTURE NAME: PMU_ROM, START ADDRESS: FFD00000, END ADDRESS: FFD3FFFF
    */
    /*
    * APERTURE NAME: PMU_ROM, START ADDRESS: FFD00000, END ADDRESS: FFD3FFFF
    */
    /*
    * APERTURE NAME: PMU_ROM, START ADDRESS: FFD00000, END ADDRESS: FFD3FFFF
    */
    /*
    * APERTURE NAME: PMU_IOMODULE, START ADDRESS: FFD40000, END ADDRESS: FFD5F
    * FFF
    */
    /*
    * APERTURE NAME: PMU_IOMODULE, START ADDRESS: FFD40000, END ADDRESS: FFD5F
    * FFF
    */
    /*
    * APERTURE NAME: PMU_LOCAL, START ADDRESS: FFD60000, END ADDRESS: FFD7FFFF
    */
    /*
    * APERTURE NAME: PMU_LOCAL, START ADDRESS: FFD60000, END ADDRESS: FFD7FFFF
    */
    /*
    * APERTURE NAME: PMU_GLOBAL, START ADDRESS: FFD80000, END ADDRESS: FFDBFFF
    * F
    */
    /*
    * APERTURE NAME: PMU_GLOBAL, START ADDRESS: FFD80000, END ADDRESS: FFDBFFF
    * F
    */
    /*
    * APERTURE NAME: PMU_GLOBAL, START ADDRESS: FFD80000, END ADDRESS: FFDBFFF
    * F
    */
    /*
    * APERTURE NAME: PMU_GLOBAL, START ADDRESS: FFD80000, END ADDRESS: FFDBFFF
    * F
    */
    /*
    * APERTURE NAME: PMU_RAM, START ADDRESS: FFDC0000, END ADDRESS: FFDFFFFF
    */
    /*
    * APERTURE NAME: PMU_RAM, START ADDRESS: FFDC0000, END ADDRESS: FFDFFFFF
    */
    /*
    * APERTURE NAME: PMU_RAM, START ADDRESS: FFDC0000, END ADDRESS: FFDFFFFF
    */
    /*
    * APERTURE NAME: PMU_RAM, START ADDRESS: FFDC0000, END ADDRESS: FFDFFFFF
    */
    /*
    * APERTURE NAME: R5_0_ATCM, START ADDRESS: FFE00000, END ADDRESS: FFE0FFFF
    */
    /*
    * APERTURE NAME: R5_0_ATCM_LOCKSTEP, START ADDRESS: FFE10000, END ADDRESS:
    *  FFE1FFFF
    */
    /*
    * APERTURE NAME: R5_0_BTCM, START ADDRESS: FFE20000, END ADDRESS: FFE2FFFF
    */
    /*
    * APERTURE NAME: R5_0_BTCM_LOCKSTEP, START ADDRESS: FFE30000, END ADDRESS:
    *  FFE3FFFF
    */
    /*
    * APERTURE NAME: R5_0_INSTRUCTION_CACHE, START ADDRESS: FFE40000, END ADDR
    * ESS: FFE4FFFF
    */
    /*
    * APERTURE NAME: R5_0_DATA_CACHE, START ADDRESS: FFE50000, END ADDRESS: FF
    * E5FFFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_8, START ADDRESS: FFE60000, END ADDRESS: FFE8F
    * FFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_8, START ADDRESS: FFE60000, END ADDRESS: FFE8F
    * FFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_8, START ADDRESS: FFE60000, END ADDRESS: FFE8F
    * FFF
    */
    /*
    * APERTURE NAME: R5_1_ATCM_, START ADDRESS: FFE90000, END ADDRESS: FFE9FFF
    * F
    */
    /*
    * APERTURE NAME: RPU_UNUSED_10, START ADDRESS: FFEA0000, END ADDRESS: FFEA
    * FFFF
    */
    /*
    * APERTURE NAME: R5_1_BTCM_, START ADDRESS: FFEB0000, END ADDRESS: FFEBFFF
    * F
    */
    /*
    * APERTURE NAME: R5_1_INSTRUCTION_CACHE, START ADDRESS: FFEC0000, END ADDR
    * ESS: FFECFFFF
    */
    /*
    * APERTURE NAME: R5_1_DATA_CACHE, START ADDRESS: FFED0000, END ADDRESS: FF
    * EDFFFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_9, START ADDRESS: FFEE0000, END ADDRESS: FFFBF
    * FFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_9, START ADDRESS: FFEE0000, END ADDRESS: FFFBF
    * FFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_9, START ADDRESS: FFEE0000, END ADDRESS: FFFBF
    * FFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_9, START ADDRESS: FFEE0000, END ADDRESS: FFFBF
    * FFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_9, START ADDRESS: FFEE0000, END ADDRESS: FFFBF
    * FFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_9, START ADDRESS: FFEE0000, END ADDRESS: FFFBF
    * FFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_9, START ADDRESS: FFEE0000, END ADDRESS: FFFBF
    * FFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_9, START ADDRESS: FFEE0000, END ADDRESS: FFFBF
    * FFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_9, START ADDRESS: FFEE0000, END ADDRESS: FFFBF
    * FFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_9, START ADDRESS: FFEE0000, END ADDRESS: FFFBF
    * FFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_9, START ADDRESS: FFEE0000, END ADDRESS: FFFBF
    * FFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_9, START ADDRESS: FFEE0000, END ADDRESS: FFFBF
    * FFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_9, START ADDRESS: FFEE0000, END ADDRESS: FFFBF
    * FFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_9, START ADDRESS: FFEE0000, END ADDRESS: FFFBF
    * FFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_9, START ADDRESS: FFEE0000, END ADDRESS: FFFBF
    * FFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_15, START ADDRESS: FFFD0000, END ADDRESS: FFFF
    * FFFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_15, START ADDRESS: FFFD0000, END ADDRESS: FFFF
    * FFFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_15, START ADDRESS: FFFD0000, END ADDRESS: FFFF
    * FFFF
    */
    /*
    * APERTURE NAME: IPI_1, START ADDRESS: FF310000, END ADDRESS: FF31FFFF
    */
    /*
    * APERTURE NAME: IPI_1, START ADDRESS: FF310000, END ADDRESS: FF31FFFF
    */
    /*
    * APERTURE NAME: IPI_1, START ADDRESS: FF310000, END ADDRESS: FF31FFFF
    */
    /*
    * APERTURE NAME: IPI_1, START ADDRESS: FF310000, END ADDRESS: FF31FFFF
    */
    /*
    * APERTURE NAME: IPI_1, START ADDRESS: FF310000, END ADDRESS: FF31FFFF
    */
    /*
    * APERTURE NAME: IPI_1, START ADDRESS: FF310000, END ADDRESS: FF31FFFF
    */
    /*
    * APERTURE NAME: IPI_1, START ADDRESS: FF310000, END ADDRESS: FF31FFFF
    */
    /*
    * APERTURE NAME: IPI_1, START ADDRESS: FF310000, END ADDRESS: FF31FFFF
    */
    /*
    * APERTURE NAME: IPI_1, START ADDRESS: FF310000, END ADDRESS: FF31FFFF
    */
    /*
    * APERTURE NAME: IPI_1, START ADDRESS: FF310000, END ADDRESS: FF31FFFF
    */
    /*
    * APERTURE NAME: IPI_1, START ADDRESS: FF310000, END ADDRESS: FF31FFFF
    */
    /*
    * APERTURE NAME: IPI_1, START ADDRESS: FF310000, END ADDRESS: FF31FFFF
    */
    /*
    * APERTURE NAME: IPI_1, START ADDRESS: FF310000, END ADDRESS: FF31FFFF
    */
    /*
    * APERTURE NAME: IPI_1, START ADDRESS: FF310000, END ADDRESS: FF31FFFF
    */
    /*
    * APERTURE NAME: IPI_1, START ADDRESS: FF310000, END ADDRESS: FF31FFFF
    */
    /*
    * APERTURE NAME: IPI_1, START ADDRESS: FF310000, END ADDRESS: FF31FFFF
    */
    /*
    * APERTURE NAME: IPI_2, START ADDRESS: FF320000, END ADDRESS: FF32FFFF
    */
    /*
    * APERTURE NAME: IPI_2, START ADDRESS: FF320000, END ADDRESS: FF32FFFF
    */
    /*
    * APERTURE NAME: IPI_2, START ADDRESS: FF320000, END ADDRESS: FF32FFFF
    */
    /*
    * APERTURE NAME: IPI_2, START ADDRESS: FF320000, END ADDRESS: FF32FFFF
    */
    /*
    * APERTURE NAME: IPI_2, START ADDRESS: FF320000, END ADDRESS: FF32FFFF
    */
    /*
    * APERTURE NAME: IPI_2, START ADDRESS: FF320000, END ADDRESS: FF32FFFF
    */
    /*
    * APERTURE NAME: IPI_2, START ADDRESS: FF320000, END ADDRESS: FF32FFFF
    */
    /*
    * APERTURE NAME: IPI_2, START ADDRESS: FF320000, END ADDRESS: FF32FFFF
    */
    /*
    * APERTURE NAME: IPI_2, START ADDRESS: FF320000, END ADDRESS: FF32FFFF
    */
    /*
    * APERTURE NAME: IPI_2, START ADDRESS: FF320000, END ADDRESS: FF32FFFF
    */
    /*
    * APERTURE NAME: IPI_2, START ADDRESS: FF320000, END ADDRESS: FF32FFFF
    */
    /*
    * APERTURE NAME: IPI_2, START ADDRESS: FF320000, END ADDRESS: FF32FFFF
    */
    /*
    * APERTURE NAME: IPI_2, START ADDRESS: FF320000, END ADDRESS: FF32FFFF
    */
    /*
    * APERTURE NAME: IPI_2, START ADDRESS: FF320000, END ADDRESS: FF32FFFF
    */
    /*
    * APERTURE NAME: IPI_2, START ADDRESS: FF320000, END ADDRESS: FF32FFFF
    */
    /*
    * APERTURE NAME: IPI_2, START ADDRESS: FF320000, END ADDRESS: FF32FFFF
    */
    /*
    * APERTURE NAME: IPI_0, START ADDRESS: FF300000, END ADDRESS: FF30FFFF
    */
    /*
    * APERTURE NAME: IPI_0, START ADDRESS: FF300000, END ADDRESS: FF30FFFF
    */
    /*
    * APERTURE NAME: IPI_0, START ADDRESS: FF300000, END ADDRESS: FF30FFFF
    */
    /*
    * APERTURE NAME: IPI_0, START ADDRESS: FF300000, END ADDRESS: FF30FFFF
    */
    /*
    * APERTURE NAME: IPI_0, START ADDRESS: FF300000, END ADDRESS: FF30FFFF
    */
    /*
    * APERTURE NAME: IPI_0, START ADDRESS: FF300000, END ADDRESS: FF30FFFF
    */
    /*
    * APERTURE NAME: IPI_0, START ADDRESS: FF300000, END ADDRESS: FF30FFFF
    */
    /*
    * APERTURE NAME: IPI_0, START ADDRESS: FF300000, END ADDRESS: FF30FFFF
    */
    /*
    * APERTURE NAME: IPI_0, START ADDRESS: FF300000, END ADDRESS: FF30FFFF
    */
    /*
    * APERTURE NAME: IPI_0, START ADDRESS: FF300000, END ADDRESS: FF30FFFF
    */
    /*
    * APERTURE NAME: IPI_0, START ADDRESS: FF300000, END ADDRESS: FF30FFFF
    */
    /*
    * APERTURE NAME: IPI_0, START ADDRESS: FF300000, END ADDRESS: FF30FFFF
    */
    /*
    * APERTURE NAME: IPI_0, START ADDRESS: FF300000, END ADDRESS: FF30FFFF
    */
    /*
    * APERTURE NAME: IPI_0, START ADDRESS: FF300000, END ADDRESS: FF30FFFF
    */
    /*
    * APERTURE NAME: IPI_0, START ADDRESS: FF300000, END ADDRESS: FF30FFFF
    */
    /*
    * APERTURE NAME: IPI_0, START ADDRESS: FF300000, END ADDRESS: FF30FFFF
    */
    /*
    * APERTURE NAME: IPI_7, START ADDRESS: FF340000, END ADDRESS: FF34FFFF
    */
    /*
    * APERTURE NAME: IPI_7, START ADDRESS: FF340000, END ADDRESS: FF34FFFF
    */
    /*
    * APERTURE NAME: IPI_7, START ADDRESS: FF340000, END ADDRESS: FF34FFFF
    */
    /*
    * APERTURE NAME: IPI_7, START ADDRESS: FF340000, END ADDRESS: FF34FFFF
    */
    /*
    * APERTURE NAME: IPI_7, START ADDRESS: FF340000, END ADDRESS: FF34FFFF
    */
    /*
    * APERTURE NAME: IPI_7, START ADDRESS: FF340000, END ADDRESS: FF34FFFF
    */
    /*
    * APERTURE NAME: IPI_7, START ADDRESS: FF340000, END ADDRESS: FF34FFFF
    */
    /*
    * APERTURE NAME: IPI_7, START ADDRESS: FF340000, END ADDRESS: FF34FFFF
    */
    /*
    * APERTURE NAME: IPI_7, START ADDRESS: FF340000, END ADDRESS: FF34FFFF
    */
    /*
    * APERTURE NAME: IPI_7, START ADDRESS: FF340000, END ADDRESS: FF34FFFF
    */
    /*
    * APERTURE NAME: IPI_7, START ADDRESS: FF340000, END ADDRESS: FF34FFFF
    */
    /*
    * APERTURE NAME: IPI_7, START ADDRESS: FF340000, END ADDRESS: FF34FFFF
    */
    /*
    * APERTURE NAME: IPI_7, START ADDRESS: FF340000, END ADDRESS: FF34FFFF
    */
    /*
    * APERTURE NAME: IPI_7, START ADDRESS: FF340000, END ADDRESS: FF34FFFF
    */
    /*
    * APERTURE NAME: IPI_7, START ADDRESS: FF340000, END ADDRESS: FF34FFFF
    */
    /*
    * APERTURE NAME: IPI_7, START ADDRESS: FF340000, END ADDRESS: FF34FFFF
    */
    /*
    * APERTURE NAME: IPI_8, START ADDRESS: FF350000, END ADDRESS: FF35FFFF
    */
    /*
    * APERTURE NAME: IPI_8, START ADDRESS: FF350000, END ADDRESS: FF35FFFF
    */
    /*
    * APERTURE NAME: IPI_8, START ADDRESS: FF350000, END ADDRESS: FF35FFFF
    */
    /*
    * APERTURE NAME: IPI_8, START ADDRESS: FF350000, END ADDRESS: FF35FFFF
    */
    /*
    * APERTURE NAME: IPI_8, START ADDRESS: FF350000, END ADDRESS: FF35FFFF
    */
    /*
    * APERTURE NAME: IPI_8, START ADDRESS: FF350000, END ADDRESS: FF35FFFF
    */
    /*
    * APERTURE NAME: IPI_8, START ADDRESS: FF350000, END ADDRESS: FF35FFFF
    */
    /*
    * APERTURE NAME: IPI_8, START ADDRESS: FF350000, END ADDRESS: FF35FFFF
    */
    /*
    * APERTURE NAME: IPI_8, START ADDRESS: FF350000, END ADDRESS: FF35FFFF
    */
    /*
    * APERTURE NAME: IPI_8, START ADDRESS: FF350000, END ADDRESS: FF35FFFF
    */
    /*
    * APERTURE NAME: IPI_8, START ADDRESS: FF350000, END ADDRESS: FF35FFFF
    */
    /*
    * APERTURE NAME: IPI_8, START ADDRESS: FF350000, END ADDRESS: FF35FFFF
    */
    /*
    * APERTURE NAME: IPI_8, START ADDRESS: FF350000, END ADDRESS: FF35FFFF
    */
    /*
    * APERTURE NAME: IPI_8, START ADDRESS: FF350000, END ADDRESS: FF35FFFF
    */
    /*
    * APERTURE NAME: IPI_8, START ADDRESS: FF350000, END ADDRESS: FF35FFFF
    */
    /*
    * APERTURE NAME: IPI_8, START ADDRESS: FF350000, END ADDRESS: FF35FFFF
    */
    /*
    * APERTURE NAME: IPI_9, START ADDRESS: FF360000, END ADDRESS: FF36FFFF
    */
    /*
    * APERTURE NAME: IPI_9, START ADDRESS: FF360000, END ADDRESS: FF36FFFF
    */
    /*
    * APERTURE NAME: IPI_9, START ADDRESS: FF360000, END ADDRESS: FF36FFFF
    */
    /*
    * APERTURE NAME: IPI_9, START ADDRESS: FF360000, END ADDRESS: FF36FFFF
    */
    /*
    * APERTURE NAME: IPI_9, START ADDRESS: FF360000, END ADDRESS: FF36FFFF
    */
    /*
    * APERTURE NAME: IPI_9, START ADDRESS: FF360000, END ADDRESS: FF36FFFF
    */
    /*
    * APERTURE NAME: IPI_9, START ADDRESS: FF360000, END ADDRESS: FF36FFFF
    */
    /*
    * APERTURE NAME: IPI_9, START ADDRESS: FF360000, END ADDRESS: FF36FFFF
    */
    /*
    * APERTURE NAME: IPI_9, START ADDRESS: FF360000, END ADDRESS: FF36FFFF
    */
    /*
    * APERTURE NAME: IPI_9, START ADDRESS: FF360000, END ADDRESS: FF36FFFF
    */
    /*
    * APERTURE NAME: IPI_9, START ADDRESS: FF360000, END ADDRESS: FF36FFFF
    */
    /*
    * APERTURE NAME: IPI_9, START ADDRESS: FF360000, END ADDRESS: FF36FFFF
    */
    /*
    * APERTURE NAME: IPI_9, START ADDRESS: FF360000, END ADDRESS: FF36FFFF
    */
    /*
    * APERTURE NAME: IPI_9, START ADDRESS: FF360000, END ADDRESS: FF36FFFF
    */
    /*
    * APERTURE NAME: IPI_9, START ADDRESS: FF360000, END ADDRESS: FF36FFFF
    */
    /*
    * APERTURE NAME: IPI_9, START ADDRESS: FF360000, END ADDRESS: FF36FFFF
    */
    /*
    * APERTURE NAME: IPI_10, START ADDRESS: FF370000, END ADDRESS: FF37FFFF
    */
    /*
    * APERTURE NAME: IPI_10, START ADDRESS: FF370000, END ADDRESS: FF37FFFF
    */
    /*
    * APERTURE NAME: IPI_10, START ADDRESS: FF370000, END ADDRESS: FF37FFFF
    */
    /*
    * APERTURE NAME: IPI_10, START ADDRESS: FF370000, END ADDRESS: FF37FFFF
    */
    /*
    * APERTURE NAME: IPI_10, START ADDRESS: FF370000, END ADDRESS: FF37FFFF
    */
    /*
    * APERTURE NAME: IPI_10, START ADDRESS: FF370000, END ADDRESS: FF37FFFF
    */
    /*
    * APERTURE NAME: IPI_10, START ADDRESS: FF370000, END ADDRESS: FF37FFFF
    */
    /*
    * APERTURE NAME: IPI_10, START ADDRESS: FF370000, END ADDRESS: FF37FFFF
    */
    /*
    * APERTURE NAME: IPI_10, START ADDRESS: FF370000, END ADDRESS: FF37FFFF
    */
    /*
    * APERTURE NAME: IPI_10, START ADDRESS: FF370000, END ADDRESS: FF37FFFF
    */
    /*
    * APERTURE NAME: IPI_10, START ADDRESS: FF370000, END ADDRESS: FF37FFFF
    */
    /*
    * APERTURE NAME: IPI_10, START ADDRESS: FF370000, END ADDRESS: FF37FFFF
    */
    /*
    * APERTURE NAME: IPI_10, START ADDRESS: FF370000, END ADDRESS: FF37FFFF
    */
    /*
    * APERTURE NAME: IPI_10, START ADDRESS: FF370000, END ADDRESS: FF37FFFF
    */
    /*
    * APERTURE NAME: IPI_10, START ADDRESS: FF370000, END ADDRESS: FF37FFFF
    */
    /*
    * APERTURE NAME: IPI_10, START ADDRESS: FF370000, END ADDRESS: FF37FFFF
    */
    /*
    * APERTURE NAME: IPI_PMU, START ADDRESS: FF330000, END ADDRESS: FF33FFFF
    */
    /*
    * APERTURE NAME: IPI_PMU, START ADDRESS: FF330000, END ADDRESS: FF33FFFF
    */
    /*
    * APERTURE NAME: IPI_PMU, START ADDRESS: FF330000, END ADDRESS: FF33FFFF
    */
    /*
    * APERTURE NAME: IPI_PMU, START ADDRESS: FF330000, END ADDRESS: FF33FFFF
    */
    /*
    * APERTURE NAME: IPI_PMU, START ADDRESS: FF330000, END ADDRESS: FF33FFFF
    */
    /*
    * APERTURE NAME: IPI_PMU, START ADDRESS: FF330000, END ADDRESS: FF33FFFF
    */
    /*
    * APERTURE NAME: IPI_PMU, START ADDRESS: FF330000, END ADDRESS: FF33FFFF
    */
    /*
    * APERTURE NAME: IPI_PMU, START ADDRESS: FF330000, END ADDRESS: FF33FFFF
    */
    /*
    * APERTURE NAME: IPI_PMU, START ADDRESS: FF330000, END ADDRESS: FF33FFFF
    */
    /*
    * APERTURE NAME: IPI_PMU, START ADDRESS: FF330000, END ADDRESS: FF33FFFF
    */
    /*
    * APERTURE NAME: IPI_PMU, START ADDRESS: FF330000, END ADDRESS: FF33FFFF
    */
    /*
    * APERTURE NAME: IPI_PMU, START ADDRESS: FF330000, END ADDRESS: FF33FFFF
    */
    /*
    * APERTURE NAME: IPI_PMU, START ADDRESS: FF330000, END ADDRESS: FF33FFFF
    */
    /*
    * APERTURE NAME: IPI_PMU, START ADDRESS: FF330000, END ADDRESS: FF33FFFF
    */
    /*
    * APERTURE NAME: IPI_PMU, START ADDRESS: FF330000, END ADDRESS: FF33FFFF
    */
    /*
    * APERTURE NAME: IPI_PMU, START ADDRESS: FF330000, END ADDRESS: FF33FFFF
    */
    /*
    * APERTURE NAME: IOU_GPV, START ADDRESS: FE000000, END ADDRESS: FE0FFFFF
    */
    /*
    * APERTURE NAME: LPD_GPV, START ADDRESS: FE100000, END ADDRESS: FE1FFFFF
    */
    /*
    * APERTURE NAME: USB3_0_XHCI, START ADDRESS: FE200000, END ADDRESS: FE2FFF
    * FF
    */
    /*
    * APERTURE NAME: USB3_1_XHCI, START ADDRESS: FE300000, END ADDRESS: FE3FFF
    * FF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_13, START ADDRESS: FE400000, END ADDRESS: FE7F
    * FFFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_13, START ADDRESS: FE400000, END ADDRESS: FE7F
    * FFFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_13, START ADDRESS: FE400000, END ADDRESS: FE7F
    * FFFF
    */
    /*
    * APERTURE NAME: LPD_UNUSED_13, START ADDRESS: FE400000, END ADDRESS: FE7F
    * FFFF
    */
    /*
    * APERTURE NAME: CORESIGHT, START ADDRESS: FE800000, END ADDRESS: FEFFFFFF
    */
    /*
    * APERTURE NAME: CORESIGHT, START ADDRESS: FE800000, END ADDRESS: FEFFFFFF
    */
    /*
    * APERTURE NAME: CORESIGHT, START ADDRESS: FE800000, END ADDRESS: FEFFFFFF
    */
    /*
    * APERTURE NAME: CORESIGHT, START ADDRESS: FE800000, END ADDRESS: FEFFFFFF
    */
    /*
    * APERTURE NAME: CORESIGHT, START ADDRESS: FE800000, END ADDRESS: FEFFFFFF
    */
    /*
    * APERTURE NAME: CORESIGHT, START ADDRESS: FE800000, END ADDRESS: FEFFFFFF
    */
    /*
    * APERTURE NAME: CORESIGHT, START ADDRESS: FE800000, END ADDRESS: FEFFFFFF
    */
    /*
    * APERTURE NAME: CORESIGHT, START ADDRESS: FE800000, END ADDRESS: FEFFFFFF
    */
    /*
    * APERTURE NAME: QSPI_LINEAR_ADDRESS, START ADDRESS: C0000000, END ADDRESS
    * : DFFFFFFF
    */
    /*
    * XPPU CONTROL
    */

	return 1;
}
unsigned long psu_ddr_xmpu0_data(void)
{
    /*
    * DDR XMPU0
    */

	return 1;
}
unsigned long psu_ddr_xmpu1_data(void)
{
    /*
    * DDR XMPU1
    */

	return 1;
}
unsigned long psu_ddr_xmpu2_data(void)
{
    /*
    * DDR XMPU2
    */

	return 1;
}
unsigned long psu_ddr_xmpu3_data(void)
{
    /*
    * DDR XMPU3
    */

	return 1;
}
unsigned long psu_ddr_xmpu4_data(void)
{
    /*
    * DDR XMPU4
    */

	return 1;
}
unsigned long psu_ddr_xmpu5_data(void)
{
    /*
    * DDR XMPU5
    */

	return 1;
}
unsigned long psu_ocm_xmpu_data(void)
{
    /*
    * OCM XMPU
    */

	return 1;
}
unsigned long psu_fpd_xmpu_data(void)
{
    /*
    * FPD XMPU
    */

	return 1;
}
unsigned long psu_protection_lock_data(void)
{
    /*
    * LOCKING PROTECTION MODULE
    */
    /*
    * XPPU LOCK
    */
    /*
    * APERTURE NAME: LPD_XPPU, START ADDRESS: FF980000, END ADDRESS: FF99FFFF
    */
    /*
    * XMPU LOCK
    */
    /*
    * LOCK OCM XMPU ONLY IF IT IS NOT PROTECTED BY ANY MASTER
    */
    /*
    * LOCK FPD XMPU ONLY IF IT IS NOT PROTECTED BY ANY MASTER
    */
    /*
    * LOCK DDR XMPU ONLY IF IT IS NOT PROTECTED BY ANY MASTER
    */
    /*
    * LOCK DDR XMPU ONLY IF IT IS NOT PROTECTED BY ANY MASTER
    */
    /*
    * LOCK DDR XMPU ONLY IF IT IS NOT PROTECTED BY ANY MASTER
    */
    /*
    * LOCK DDR XMPU ONLY IF IT IS NOT PROTECTED BY ANY MASTER
    */
    /*
    * LOCK DDR XMPU ONLY IF IT IS NOT PROTECTED BY ANY MASTER
    */
    /*
    * LOCK DDR XMPU ONLY IF IT IS NOT PROTECTED BY ANY MASTER
    */

	return 1;
}
unsigned long psu_apply_master_tz(void)
{
    /*
    * RPU
    */
    /*
    * DP TZ
    */
    /*
    * Register : slcr_dpdma @ 0XFD690040

    * TrustZone classification for DisplayPort DMA
    *  PSU_FPD_SLCR_SECURE_SLCR_DPDMA_TZ                           1

    * DPDMA TrustZone Settings
    * (OFFSET, MASK, VALUE)      (0XFD690040, 0x00000001U ,0x00000001U)
    */
	PSU_Mask_Write(FPD_SLCR_SECURE_SLCR_DPDMA_OFFSET,
		0x00000001U, 0x00000001U);
/*##################################################################### */

    /*
    * SATA TZ
    */
    /*
    * PCIE TZ
    */
    /*
    * Register : slcr_pcie @ 0XFD690030

    * TrustZone classification for DMA Channel 0
    *  PSU_FPD_SLCR_SECURE_SLCR_PCIE_TZ_DMA_0                      1

    * TrustZone classification for DMA Channel 1
    *  PSU_FPD_SLCR_SECURE_SLCR_PCIE_TZ_DMA_1                      1

    * TrustZone classification for DMA Channel 2
    *  PSU_FPD_SLCR_SECURE_SLCR_PCIE_TZ_DMA_2                      1

    * TrustZone classification for DMA Channel 3
    *  PSU_FPD_SLCR_SECURE_SLCR_PCIE_TZ_DMA_3                      1

    * TrustZone classification for Ingress Address Translation 0
    *  PSU_FPD_SLCR_SECURE_SLCR_PCIE_TZ_AT_INGR_0                  1

    * TrustZone classification for Ingress Address Translation 1
    *  PSU_FPD_SLCR_SECURE_SLCR_PCIE_TZ_AT_INGR_1                  1

    * TrustZone classification for Ingress Address Translation 2
    *  PSU_FPD_SLCR_SECURE_SLCR_PCIE_TZ_AT_INGR_2                  1

    * TrustZone classification for Ingress Address Translation 3
    *  PSU_FPD_SLCR_SECURE_SLCR_PCIE_TZ_AT_INGR_3                  1

    * TrustZone classification for Ingress Address Translation 4
    *  PSU_FPD_SLCR_SECURE_SLCR_PCIE_TZ_AT_INGR_4                  1

    * TrustZone classification for Ingress Address Translation 5
    *  PSU_FPD_SLCR_SECURE_SLCR_PCIE_TZ_AT_INGR_5                  1

    * TrustZone classification for Ingress Address Translation 6
    *  PSU_FPD_SLCR_SECURE_SLCR_PCIE_TZ_AT_INGR_6                  1

    * TrustZone classification for Ingress Address Translation 7
    *  PSU_FPD_SLCR_SECURE_SLCR_PCIE_TZ_AT_INGR_7                  1

    * TrustZone classification for Egress Address Translation 0
    *  PSU_FPD_SLCR_SECURE_SLCR_PCIE_TZ_AT_EGR_0                   1

    * TrustZone classification for Egress Address Translation 1
    *  PSU_FPD_SLCR_SECURE_SLCR_PCIE_TZ_AT_EGR_1                   1

    * TrustZone classification for Egress Address Translation 2
    *  PSU_FPD_SLCR_SECURE_SLCR_PCIE_TZ_AT_EGR_2                   1

    * TrustZone classification for Egress Address Translation 3
    *  PSU_FPD_SLCR_SECURE_SLCR_PCIE_TZ_AT_EGR_3                   1

    * TrustZone classification for Egress Address Translation 4
    *  PSU_FPD_SLCR_SECURE_SLCR_PCIE_TZ_AT_EGR_4                   1

    * TrustZone classification for Egress Address Translation 5
    *  PSU_FPD_SLCR_SECURE_SLCR_PCIE_TZ_AT_EGR_5                   1

    * TrustZone classification for Egress Address Translation 6
    *  PSU_FPD_SLCR_SECURE_SLCR_PCIE_TZ_AT_EGR_6                   1

    * TrustZone classification for Egress Address Translation 7
    *  PSU_FPD_SLCR_SECURE_SLCR_PCIE_TZ_AT_EGR_7                   1

    * TrustZone classification for DMA Registers
    *  PSU_FPD_SLCR_SECURE_SLCR_PCIE_TZ_DMA_REGS                   1

    * TrustZone classification for MSIx Table
    *  PSU_FPD_SLCR_SECURE_SLCR_PCIE_TZ_MSIX_TABLE                 1

    * TrustZone classification for MSIx PBA
    *  PSU_FPD_SLCR_SECURE_SLCR_PCIE_TZ_MSIX_PBA                   1

    * TrustZone classification for ECAM
    *  PSU_FPD_SLCR_SECURE_SLCR_PCIE_TZ_ECAM                       1

    * TrustZone classification for Bridge Common Registers
    *  PSU_FPD_SLCR_SECURE_SLCR_PCIE_TZ_BRIDGE_REGS                1

    * PCIe TrustZone settings. This register may only be modified during bootu
    * p (while PCIe block is disabled)
    * (OFFSET, MASK, VALUE)      (0XFD690030, 0x01FFFFFFU ,0x01FFFFFFU)
    */
	PSU_Mask_Write(FPD_SLCR_SECURE_SLCR_PCIE_OFFSET,
		0x01FFFFFFU, 0x01FFFFFFU);
/*##################################################################### */

    /*
    * USB TZ
    */
    /*
    * Register : slcr_usb @ 0XFF4B0034

    * TrustZone Classification for USB3_0
    *  PSU_LPD_SLCR_SECURE_SLCR_USB_TZ_USB3_0                      1

    * TrustZone Classification for USB3_1
    *  PSU_LPD_SLCR_SECURE_SLCR_USB_TZ_USB3_1                      1

    * USB3 TrustZone settings
    * (OFFSET, MASK, VALUE)      (0XFF4B0034, 0x00000003U ,0x00000003U)
    */
	PSU_Mask_Write(LPD_SLCR_SECURE_SLCR_USB_OFFSET,
		0x00000003U, 0x00000003U);
/*##################################################################### */

    /*
    * SD TZ
    */
    /*
    * Register : IOU_AXI_RPRTCN @ 0XFF240004

    * AXI protection [0] = '0' : Normal access [0] = '1' : Previleged access [
    * 1] = '0' : Secure access [1] = '1' : No secure access [2] = '0' : Data a
    * ccess [2] = '1'' : Instruction access
    *  PSU_IOU_SECURE_SLCR_IOU_AXI_RPRTCN_SD0_AXI_ARPROT           2

    * AXI protection [0] = '0' : Normal access [0] = '1' : Previleged access [
    * 1] = '0' : Secure access [1] = '1' : No secure access [2] = '0' : Data a
    * ccess [2] = '1'' : Instruction access
    *  PSU_IOU_SECURE_SLCR_IOU_AXI_RPRTCN_SD1_AXI_ARPROT           2

    * AXI read protection type selection
    * (OFFSET, MASK, VALUE)      (0XFF240004, 0x003F0000U ,0x00120000U)
    */
	PSU_Mask_Write(IOU_SECURE_SLCR_IOU_AXI_RPRTCN_OFFSET,
		0x003F0000U, 0x00120000U);
/*##################################################################### */

    /*
    * Register : IOU_AXI_WPRTCN @ 0XFF240000

    * AXI protection [0] = '0' : Normal access [0] = '1' : Previleged access [
    * 1] = '0' : Secure access [1] = '1' : No secure access [2] = '0' : Data a
    * ccess [2] = '1'' : Instruction access
    *  PSU_IOU_SECURE_SLCR_IOU_AXI_WPRTCN_SD0_AXI_AWPROT           2

    * AXI protection [0] = '0' : Normal access [0] = '1' : Previleged access [
    * 1] = '0' : Secure access [1] = '1' : No secure access [2] = '0' : Data a
    * ccess [2] = '1'' : Instruction access
    *  PSU_IOU_SECURE_SLCR_IOU_AXI_WPRTCN_SD1_AXI_AWPROT           2

    * AXI write protection type selection
    * (OFFSET, MASK, VALUE)      (0XFF240000, 0x003F0000U ,0x00120000U)
    */
	PSU_Mask_Write(IOU_SECURE_SLCR_IOU_AXI_WPRTCN_OFFSET,
		0x003F0000U, 0x00120000U);
/*##################################################################### */

    /*
    * GEM TZ
    */
    /*
    * Register : IOU_AXI_RPRTCN @ 0XFF240004

    * AXI protection [0] = '0' : Normal access [0] = '1' : Previleged access [
    * 1] = '0' : Secure access [1] = '1' : No secure access [2] = '0' : Data a
    * ccess [2] = '1'' : Instruction access
    *  PSU_IOU_SECURE_SLCR_IOU_AXI_RPRTCN_GEM0_AXI_ARPROT          2

    * AXI protection [0] = '0' : Normal access [0] = '1' : Previleged access [
    * 1] = '0' : Secure access [1] = '1' : No secure access [2] = '0' : Data a
    * ccess [2] = '1'' : Instruction access
    *  PSU_IOU_SECURE_SLCR_IOU_AXI_RPRTCN_GEM1_AXI_ARPROT          2

    * AXI protection [0] = '0' : Normal access [0] = '1' : Previleged access [
    * 1] = '0' : Secure access [1] = '1' : No secure access [2] = '0' : Data a
    * ccess [2] = '1'' : Instruction access
    *  PSU_IOU_SECURE_SLCR_IOU_AXI_RPRTCN_GEM2_AXI_ARPROT          2

    * AXI protection [0] = '0' : Normal access [0] = '1' : Previleged access [
    * 1] = '0' : Secure access [1] = '1' : No secure access [2] = '0' : Data a
    * ccess [2] = '1'' : Instruction access
    *  PSU_IOU_SECURE_SLCR_IOU_AXI_RPRTCN_GEM3_AXI_ARPROT          2

    * AXI read protection type selection
    * (OFFSET, MASK, VALUE)      (0XFF240004, 0x00000FFFU ,0x00000492U)
    */
	PSU_Mask_Write(IOU_SECURE_SLCR_IOU_AXI_RPRTCN_OFFSET,
		0x00000FFFU, 0x00000492U);
/*##################################################################### */

    /*
    * Register : IOU_AXI_WPRTCN @ 0XFF240000

    * AXI protection [0] = '0' : Normal access [0] = '1' : Previleged access [
    * 1] = '0' : Secure access [1] = '1' : No secure access [2] = '0' : Data a
    * ccess [2] = '1'' : Instruction access
    *  PSU_IOU_SECURE_SLCR_IOU_AXI_WPRTCN_GEM0_AXI_AWPROT          2

    * AXI protection [0] = '0' : Normal access [0] = '1' : Previleged access [
    * 1] = '0' : Secure access [1] = '1' : No secure access [2] = '0' : Data a
    * ccess [2] = '1'' : Instruction access
    *  PSU_IOU_SECURE_SLCR_IOU_AXI_WPRTCN_GEM1_AXI_AWPROT          2

    * AXI protection [0] = '0' : Normal access [0] = '1' : Previleged access [
    * 1] = '0' : Secure access [1] = '1' : No secure access [2] = '0' : Data a
    * ccess [2] = '1'' : Instruction access
    *  PSU_IOU_SECURE_SLCR_IOU_AXI_WPRTCN_GEM2_AXI_AWPROT          2

    * AXI protection [0] = '0' : Normal access [0] = '1' : Previleged access [
    * 1] = '0' : Secure access [1] = '1' : No secure access [2] = '0' : Data a
    * ccess [2] = '1'' : Instruction access
    *  PSU_IOU_SECURE_SLCR_IOU_AXI_WPRTCN_GEM3_AXI_AWPROT          2

    * AXI write protection type selection
    * (OFFSET, MASK, VALUE)      (0XFF240000, 0x00000FFFU ,0x00000492U)
    */
	PSU_Mask_Write(IOU_SECURE_SLCR_IOU_AXI_WPRTCN_OFFSET,
		0x00000FFFU, 0x00000492U);
/*##################################################################### */

    /*
    * QSPI TZ
    */
    /*
    * Register : IOU_AXI_WPRTCN @ 0XFF240000

    * AXI protection [0] = '0' : Normal access [0] = '1' : Previleged access [
    * 1] = '0' : Secure access [1] = '1' : No secure access [2] = '0' : Data a
    * ccess [2] = '1'' : Instruction access
    *  PSU_IOU_SECURE_SLCR_IOU_AXI_WPRTCN_QSPI_AXI_AWPROT          2

    * AXI write protection type selection
    * (OFFSET, MASK, VALUE)      (0XFF240000, 0x0E000000U ,0x04000000U)
    */
	PSU_Mask_Write(IOU_SECURE_SLCR_IOU_AXI_WPRTCN_OFFSET,
		0x0E000000U, 0x04000000U);
/*##################################################################### */

    /*
    * NAND TZ
    */
    /*
    * Register : IOU_AXI_RPRTCN @ 0XFF240004

    * AXI protection [0] = '0' : Normal access [0] = '1' : Previleged access [
    * 1] = '0' : Secure access [1] = '1' : No secure access [2] = '0' : Data a
    * ccess [2] = '1'' : Instruction access
    *  PSU_IOU_SECURE_SLCR_IOU_AXI_RPRTCN_NAND_AXI_ARPROT          2

    * AXI read protection type selection
    * (OFFSET, MASK, VALUE)      (0XFF240004, 0x01C00000U ,0x00800000U)
    */
	PSU_Mask_Write(IOU_SECURE_SLCR_IOU_AXI_RPRTCN_OFFSET,
		0x01C00000U, 0x00800000U);
/*##################################################################### */

    /*
    * Register : IOU_AXI_WPRTCN @ 0XFF240000

    * AXI protection [0] = '0' : Normal access [0] = '1' : Previleged access [
    * 1] = '0' : Secure access [1] = '1' : No secure access [2] = '0' : Data a
    * ccess [2] = '1'' : Instruction access
    *  PSU_IOU_SECURE_SLCR_IOU_AXI_WPRTCN_NAND_AXI_AWPROT          2

    * AXI write protection type selection
    * (OFFSET, MASK, VALUE)      (0XFF240000, 0x01C00000U ,0x00800000U)
    */
	PSU_Mask_Write(IOU_SECURE_SLCR_IOU_AXI_WPRTCN_OFFSET,
		0x01C00000U, 0x00800000U);
/*##################################################################### */

    /*
    * DMA TZ
    */
    /*
    * Register : slcr_adma @ 0XFF4B0024

    * TrustZone Classification for ADMA
    *  PSU_LPD_SLCR_SECURE_SLCR_ADMA_TZ                            0xFF

    * RPU TrustZone settings
    * (OFFSET, MASK, VALUE)      (0XFF4B0024, 0x000000FFU ,0x000000FFU)
    */
	PSU_Mask_Write(LPD_SLCR_SECURE_SLCR_ADMA_OFFSET,
		0x000000FFU, 0x000000FFU);
/*##################################################################### */

    /*
    * Register : slcr_gdma @ 0XFD690050

    * TrustZone Classification for GDMA
    *  PSU_FPD_SLCR_SECURE_SLCR_GDMA_TZ                            0xFF

    * GDMA Trustzone Settings
    * (OFFSET, MASK, VALUE)      (0XFD690050, 0x000000FFU ,0x000000FFU)
    */
	PSU_Mask_Write(FPD_SLCR_SECURE_SLCR_GDMA_OFFSET,
		0x000000FFU, 0x000000FFU);
/*##################################################################### */


	return 1;
}
unsigned long psu_serdes_init_data(void)
{
    /*
    * SERDES INITIALIZATION
    */
    /*
    * GT REFERENCE CLOCK SOURCE SELECTION
    */
    /*
    * Register : PLL_REF_SEL0 @ 0XFD410000

    * PLL0 Reference Selection. 0x0 - 5MHz, 0x1 - 9.6MHz, 0x2 - 10MHz, 0x3 - 1
    * 2MHz, 0x4 - 13MHz, 0x5 - 19.2MHz, 0x6 - 20MHz, 0x7 - 24MHz, 0x8 - 26MHz,
    *  0x9 - 27MHz, 0xA - 38.4MHz, 0xB - 40MHz, 0xC - 52MHz, 0xD - 100MHz, 0xE
    *  - 108MHz, 0xF - 125MHz, 0x10 - 135MHz, 0x11 - 150 MHz. 0x12 to 0x1F - R
    * eserved
    *  PSU_SERDES_PLL_REF_SEL0_PLLREFSEL0                          0xD

    * PLL0 Reference Selection Register
    * (OFFSET, MASK, VALUE)      (0XFD410000, 0x0000001FU ,0x0000000DU)
    */
	PSU_Mask_Write(SERDES_PLL_REF_SEL0_OFFSET, 0x0000001FU, 0x0000000DU);
/*##################################################################### */

    /*
    * Register : PLL_REF_SEL1 @ 0XFD410004

    * PLL1 Reference Selection. 0x0 - 5MHz, 0x1 - 9.6MHz, 0x2 - 10MHz, 0x3 - 1
    * 2MHz, 0x4 - 13MHz, 0x5 - 19.2MHz, 0x6 - 20MHz, 0x7 - 24MHz, 0x8 - 26MHz,
    *  0x9 - 27MHz, 0xA - 38.4MHz, 0xB - 40MHz, 0xC - 52MHz, 0xD - 100MHz, 0xE
    *  - 108MHz, 0xF - 125MHz, 0x10 - 135MHz, 0x11 - 150 MHz. 0x12 to 0x1F - R
    * eserved
    *  PSU_SERDES_PLL_REF_SEL1_PLLREFSEL1                          0x9

    * PLL1 Reference Selection Register
    * (OFFSET, MASK, VALUE)      (0XFD410004, 0x0000001FU ,0x00000009U)
    */
	PSU_Mask_Write(SERDES_PLL_REF_SEL1_OFFSET, 0x0000001FU, 0x00000009U);
/*##################################################################### */

    /*
    * Register : PLL_REF_SEL2 @ 0XFD410008

    * PLL2 Reference Selection. 0x0 - 5MHz, 0x1 - 9.6MHz, 0x2 - 10MHz, 0x3 - 1
    * 2MHz, 0x4 - 13MHz, 0x5 - 19.2MHz, 0x6 - 20MHz, 0x7 - 24MHz, 0x8 - 26MHz,
    *  0x9 - 27MHz, 0xA - 38.4MHz, 0xB - 40MHz, 0xC - 52MHz, 0xD - 100MHz, 0xE
    *  - 108MHz, 0xF - 125MHz, 0x10 - 135MHz, 0x11 - 150 MHz. 0x12 to 0x1F - R
    * eserved
    *  PSU_SERDES_PLL_REF_SEL2_PLLREFSEL2                          0x8

    * PLL2 Reference Selection Register
    * (OFFSET, MASK, VALUE)      (0XFD410008, 0x0000001FU ,0x00000008U)
    */
	PSU_Mask_Write(SERDES_PLL_REF_SEL2_OFFSET, 0x0000001FU, 0x00000008U);
/*##################################################################### */

    /*
    * Register : PLL_REF_SEL3 @ 0XFD41000C

    * PLL3 Reference Selection. 0x0 - 5MHz, 0x1 - 9.6MHz, 0x2 - 10MHz, 0x3 - 1
    * 2MHz, 0x4 - 13MHz, 0x5 - 19.2MHz, 0x6 - 20MHz, 0x7 - 24MHz, 0x8 - 26MHz,
    *  0x9 - 27MHz, 0xA - 38.4MHz, 0xB - 40MHz, 0xC - 52MHz, 0xD - 100MHz, 0xE
    *  - 108MHz, 0xF - 125MHz, 0x10 - 135MHz, 0x11 - 150 MHz. 0x12 to 0x1F - R
    * eserved
    *  PSU_SERDES_PLL_REF_SEL3_PLLREFSEL3                          0xF

    * PLL3 Reference Selection Register
    * (OFFSET, MASK, VALUE)      (0XFD41000C, 0x0000001FU ,0x0000000FU)
    */
	PSU_Mask_Write(SERDES_PLL_REF_SEL3_OFFSET, 0x0000001FU, 0x0000000FU);
/*##################################################################### */

    /*
    * GT REFERENCE CLOCK FREQUENCY SELECTION
    */
    /*
    * Register : L0_L0_REF_CLK_SEL @ 0XFD402860

    * Sel of lane 0 ref clock local mux. Set to 1 to select lane 0 slicer outp
    * ut. Set to 0 to select lane0 ref clock mux output.
    *  PSU_SERDES_L0_L0_REF_CLK_SEL_L0_REF_CLK_LCL_SEL             0x1

    * Lane0 Ref Clock Selection Register
    * (OFFSET, MASK, VALUE)      (0XFD402860, 0x00000080U ,0x00000080U)
    */
	PSU_Mask_Write(SERDES_L0_L0_REF_CLK_SEL_OFFSET,
		0x00000080U, 0x00000080U);
/*##################################################################### */

    /*
    * Register : L0_L1_REF_CLK_SEL @ 0XFD402864

    * Sel of lane 1 ref clock local mux. Set to 1 to select lane 1 slicer outp
    * ut. Set to 0 to select lane1 ref clock mux output.
    *  PSU_SERDES_L0_L1_REF_CLK_SEL_L1_REF_CLK_LCL_SEL             0x0

    * Bit 3 of lane 1 ref clock mux one hot sel. Set to 1 to select lane 3 sli
    * cer output from ref clock network
    *  PSU_SERDES_L0_L1_REF_CLK_SEL_L1_REF_CLK_SEL_3               0x1

    * Lane1 Ref Clock Selection Register
    * (OFFSET, MASK, VALUE)      (0XFD402864, 0x00000088U ,0x00000008U)
    */
	PSU_Mask_Write(SERDES_L0_L1_REF_CLK_SEL_OFFSET,
		0x00000088U, 0x00000008U);
/*##################################################################### */

    /*
    * Register : L0_L2_REF_CLK_SEL @ 0XFD402868

    * Sel of lane 2 ref clock local mux. Set to 1 to select lane 1 slicer outp
    * ut. Set to 0 to select lane2 ref clock mux output.
    *  PSU_SERDES_L0_L2_REF_CLK_SEL_L2_REF_CLK_LCL_SEL             0x1

    * Lane2 Ref Clock Selection Register
    * (OFFSET, MASK, VALUE)      (0XFD402868, 0x00000080U ,0x00000080U)
    */
	PSU_Mask_Write(SERDES_L0_L2_REF_CLK_SEL_OFFSET,
		0x00000080U, 0x00000080U);
/*##################################################################### */

    /*
    * Register : L0_L3_REF_CLK_SEL @ 0XFD40286C

    * Sel of lane 3 ref clock local mux. Set to 1 to select lane 3 slicer outp
    * ut. Set to 0 to select lane3 ref clock mux output.
    *  PSU_SERDES_L0_L3_REF_CLK_SEL_L3_REF_CLK_LCL_SEL             0x0

    * Bit 1 of lane 3 ref clock mux one hot sel. Set to 1 to select lane 1 sli
    * cer output from ref clock network
    *  PSU_SERDES_L0_L3_REF_CLK_SEL_L3_REF_CLK_SEL_1               0x1

    * Lane3 Ref Clock Selection Register
    * (OFFSET, MASK, VALUE)      (0XFD40286C, 0x00000082U ,0x00000002U)
    */
	PSU_Mask_Write(SERDES_L0_L3_REF_CLK_SEL_OFFSET,
		0x00000082U, 0x00000002U);
/*##################################################################### */

    /*
    * ENABLE SPREAD SPECTRUM
    */
    /*
    * Register : L2_TM_PLL_DIG_37 @ 0XFD40A094

    * Enable/Disable coarse code satureation limiting logic
    *  PSU_SERDES_L2_TM_PLL_DIG_37_TM_ENABLE_COARSE_SATURATION     0x1

    * Test mode register 37
    * (OFFSET, MASK, VALUE)      (0XFD40A094, 0x00000010U ,0x00000010U)
    */
	PSU_Mask_Write(SERDES_L2_TM_PLL_DIG_37_OFFSET,
		0x00000010U, 0x00000010U);
/*##################################################################### */

    /*
    * Register : L2_PLL_SS_STEPS_0_LSB @ 0XFD40A368

    * Spread Spectrum No of Steps [7:0]
    *  PSU_SERDES_L2_PLL_SS_STEPS_0_LSB_SS_NUM_OF_STEPS_0_LSB      0x38

    * Spread Spectrum No of Steps bits 7:0
    * (OFFSET, MASK, VALUE)      (0XFD40A368, 0x000000FFU ,0x00000038U)
    */
	PSU_Mask_Write(SERDES_L2_PLL_SS_STEPS_0_LSB_OFFSET,
		0x000000FFU, 0x00000038U);
/*##################################################################### */

    /*
    * Register : L2_PLL_SS_STEPS_1_MSB @ 0XFD40A36C

    * Spread Spectrum No of Steps [10:8]
    *  PSU_SERDES_L2_PLL_SS_STEPS_1_MSB_SS_NUM_OF_STEPS_1_MSB      0x03

    * Spread Spectrum No of Steps bits 10:8
    * (OFFSET, MASK, VALUE)      (0XFD40A36C, 0x00000007U ,0x00000003U)
    */
	PSU_Mask_Write(SERDES_L2_PLL_SS_STEPS_1_MSB_OFFSET,
		0x00000007U, 0x00000003U);
/*##################################################################### */

    /*
    * Register : L3_PLL_SS_STEPS_0_LSB @ 0XFD40E368

    * Spread Spectrum No of Steps [7:0]
    *  PSU_SERDES_L3_PLL_SS_STEPS_0_LSB_SS_NUM_OF_STEPS_0_LSB      0xE0

    * Spread Spectrum No of Steps bits 7:0
    * (OFFSET, MASK, VALUE)      (0XFD40E368, 0x000000FFU ,0x000000E0U)
    */
	PSU_Mask_Write(SERDES_L3_PLL_SS_STEPS_0_LSB_OFFSET,
		0x000000FFU, 0x000000E0U);
/*##################################################################### */

    /*
    * Register : L3_PLL_SS_STEPS_1_MSB @ 0XFD40E36C

    * Spread Spectrum No of Steps [10:8]
    *  PSU_SERDES_L3_PLL_SS_STEPS_1_MSB_SS_NUM_OF_STEPS_1_MSB      0x3

    * Spread Spectrum No of Steps bits 10:8
    * (OFFSET, MASK, VALUE)      (0XFD40E36C, 0x00000007U ,0x00000003U)
    */
	PSU_Mask_Write(SERDES_L3_PLL_SS_STEPS_1_MSB_OFFSET,
		0x00000007U, 0x00000003U);
/*##################################################################### */

    /*
    * Register : L1_PLL_SS_STEPS_0_LSB @ 0XFD406368

    * Spread Spectrum No of Steps [7:0]
    *  PSU_SERDES_L1_PLL_SS_STEPS_0_LSB_SS_NUM_OF_STEPS_0_LSB      0x58

    * Spread Spectrum No of Steps bits 7:0
    * (OFFSET, MASK, VALUE)      (0XFD406368, 0x000000FFU ,0x00000058U)
    */
	PSU_Mask_Write(SERDES_L1_PLL_SS_STEPS_0_LSB_OFFSET,
		0x000000FFU, 0x00000058U);
/*##################################################################### */

    /*
    * Register : L1_PLL_SS_STEPS_1_MSB @ 0XFD40636C

    * Spread Spectrum No of Steps [10:8]
    *  PSU_SERDES_L1_PLL_SS_STEPS_1_MSB_SS_NUM_OF_STEPS_1_MSB      0x3

    * Spread Spectrum No of Steps bits 10:8
    * (OFFSET, MASK, VALUE)      (0XFD40636C, 0x00000007U ,0x00000003U)
    */
	PSU_Mask_Write(SERDES_L1_PLL_SS_STEPS_1_MSB_OFFSET,
		0x00000007U, 0x00000003U);
/*##################################################################### */

    /*
    * Register : L1_PLL_SS_STEP_SIZE_0_LSB @ 0XFD406370

    * Step Size for Spread Spectrum [7:0]
    *  PSU_SERDES_L1_PLL_SS_STEP_SIZE_0_LSB_SS_STEP_SIZE_0_LSB     0x7C

    * Step Size for Spread Spectrum LSB
    * (OFFSET, MASK, VALUE)      (0XFD406370, 0x000000FFU ,0x0000007CU)
    */
	PSU_Mask_Write(SERDES_L1_PLL_SS_STEP_SIZE_0_LSB_OFFSET,
		0x000000FFU, 0x0000007CU);
/*##################################################################### */

    /*
    * Register : L1_PLL_SS_STEP_SIZE_1 @ 0XFD406374

    * Step Size for Spread Spectrum [15:8]
    *  PSU_SERDES_L1_PLL_SS_STEP_SIZE_1_SS_STEP_SIZE_1             0x33

    * Step Size for Spread Spectrum 1
    * (OFFSET, MASK, VALUE)      (0XFD406374, 0x000000FFU ,0x00000033U)
    */
	PSU_Mask_Write(SERDES_L1_PLL_SS_STEP_SIZE_1_OFFSET,
		0x000000FFU, 0x00000033U);
/*##################################################################### */

    /*
    * Register : L1_PLL_SS_STEP_SIZE_2 @ 0XFD406378

    * Step Size for Spread Spectrum [23:16]
    *  PSU_SERDES_L1_PLL_SS_STEP_SIZE_2_SS_STEP_SIZE_2             0x2

    * Step Size for Spread Spectrum 2
    * (OFFSET, MASK, VALUE)      (0XFD406378, 0x000000FFU ,0x00000002U)
    */
	PSU_Mask_Write(SERDES_L1_PLL_SS_STEP_SIZE_2_OFFSET,
		0x000000FFU, 0x00000002U);
/*##################################################################### */

    /*
    * Register : L1_PLL_SS_STEP_SIZE_3_MSB @ 0XFD40637C

    * Step Size for Spread Spectrum [25:24]
    *  PSU_SERDES_L1_PLL_SS_STEP_SIZE_3_MSB_SS_STEP_SIZE_3_MSB     0x0

    * Enable/Disable test mode force on SS step size
    *  PSU_SERDES_L1_PLL_SS_STEP_SIZE_3_MSB_FORCE_SS_STEP_SIZE     0x1

    * Enable/Disable test mode force on SS no of steps
    *  PSU_SERDES_L1_PLL_SS_STEP_SIZE_3_MSB_FORCE_SS_NUM_OF_STEPS  0x1

    * Enable force on enable Spread Spectrum
    * (OFFSET, MASK, VALUE)      (0XFD40637C, 0x00000033U ,0x00000030U)
    */
	PSU_Mask_Write(SERDES_L1_PLL_SS_STEP_SIZE_3_MSB_OFFSET,
		0x00000033U, 0x00000030U);
/*##################################################################### */

    /*
    * Register : L2_PLL_SS_STEP_SIZE_0_LSB @ 0XFD40A370

    * Step Size for Spread Spectrum [7:0]
    *  PSU_SERDES_L2_PLL_SS_STEP_SIZE_0_LSB_SS_STEP_SIZE_0_LSB     0xF4

    * Step Size for Spread Spectrum LSB
    * (OFFSET, MASK, VALUE)      (0XFD40A370, 0x000000FFU ,0x000000F4U)
    */
	PSU_Mask_Write(SERDES_L2_PLL_SS_STEP_SIZE_0_LSB_OFFSET,
		0x000000FFU, 0x000000F4U);
/*##################################################################### */

    /*
    * Register : L2_PLL_SS_STEP_SIZE_1 @ 0XFD40A374

    * Step Size for Spread Spectrum [15:8]
    *  PSU_SERDES_L2_PLL_SS_STEP_SIZE_1_SS_STEP_SIZE_1             0x31

    * Step Size for Spread Spectrum 1
    * (OFFSET, MASK, VALUE)      (0XFD40A374, 0x000000FFU ,0x00000031U)
    */
	PSU_Mask_Write(SERDES_L2_PLL_SS_STEP_SIZE_1_OFFSET,
		0x000000FFU, 0x00000031U);
/*##################################################################### */

    /*
    * Register : L2_PLL_SS_STEP_SIZE_2 @ 0XFD40A378

    * Step Size for Spread Spectrum [23:16]
    *  PSU_SERDES_L2_PLL_SS_STEP_SIZE_2_SS_STEP_SIZE_2             0x2

    * Step Size for Spread Spectrum 2
    * (OFFSET, MASK, VALUE)      (0XFD40A378, 0x000000FFU ,0x00000002U)
    */
	PSU_Mask_Write(SERDES_L2_PLL_SS_STEP_SIZE_2_OFFSET,
		0x000000FFU, 0x00000002U);
/*##################################################################### */

    /*
    * Register : L2_PLL_SS_STEP_SIZE_3_MSB @ 0XFD40A37C

    * Step Size for Spread Spectrum [25:24]
    *  PSU_SERDES_L2_PLL_SS_STEP_SIZE_3_MSB_SS_STEP_SIZE_3_MSB     0x0

    * Enable/Disable test mode force on SS step size
    *  PSU_SERDES_L2_PLL_SS_STEP_SIZE_3_MSB_FORCE_SS_STEP_SIZE     0x1

    * Enable/Disable test mode force on SS no of steps
    *  PSU_SERDES_L2_PLL_SS_STEP_SIZE_3_MSB_FORCE_SS_NUM_OF_STEPS  0x1

    * Enable force on enable Spread Spectrum
    * (OFFSET, MASK, VALUE)      (0XFD40A37C, 0x00000033U ,0x00000030U)
    */
	PSU_Mask_Write(SERDES_L2_PLL_SS_STEP_SIZE_3_MSB_OFFSET,
		0x00000033U, 0x00000030U);
/*##################################################################### */

    /*
    * Register : L3_PLL_SS_STEP_SIZE_0_LSB @ 0XFD40E370

    * Step Size for Spread Spectrum [7:0]
    *  PSU_SERDES_L3_PLL_SS_STEP_SIZE_0_LSB_SS_STEP_SIZE_0_LSB     0xC9

    * Step Size for Spread Spectrum LSB
    * (OFFSET, MASK, VALUE)      (0XFD40E370, 0x000000FFU ,0x000000C9U)
    */
	PSU_Mask_Write(SERDES_L3_PLL_SS_STEP_SIZE_0_LSB_OFFSET,
		0x000000FFU, 0x000000C9U);
/*##################################################################### */

    /*
    * Register : L3_PLL_SS_STEP_SIZE_1 @ 0XFD40E374

    * Step Size for Spread Spectrum [15:8]
    *  PSU_SERDES_L3_PLL_SS_STEP_SIZE_1_SS_STEP_SIZE_1             0xD2

    * Step Size for Spread Spectrum 1
    * (OFFSET, MASK, VALUE)      (0XFD40E374, 0x000000FFU ,0x000000D2U)
    */
	PSU_Mask_Write(SERDES_L3_PLL_SS_STEP_SIZE_1_OFFSET,
		0x000000FFU, 0x000000D2U);
/*##################################################################### */

    /*
    * Register : L3_PLL_SS_STEP_SIZE_2 @ 0XFD40E378

    * Step Size for Spread Spectrum [23:16]
    *  PSU_SERDES_L3_PLL_SS_STEP_SIZE_2_SS_STEP_SIZE_2             0x1

    * Step Size for Spread Spectrum 2
    * (OFFSET, MASK, VALUE)      (0XFD40E378, 0x000000FFU ,0x00000001U)
    */
	PSU_Mask_Write(SERDES_L3_PLL_SS_STEP_SIZE_2_OFFSET,
		0x000000FFU, 0x00000001U);
/*##################################################################### */

    /*
    * Register : L3_PLL_SS_STEP_SIZE_3_MSB @ 0XFD40E37C

    * Step Size for Spread Spectrum [25:24]
    *  PSU_SERDES_L3_PLL_SS_STEP_SIZE_3_MSB_SS_STEP_SIZE_3_MSB     0x0

    * Enable/Disable test mode force on SS step size
    *  PSU_SERDES_L3_PLL_SS_STEP_SIZE_3_MSB_FORCE_SS_STEP_SIZE     0x1

    * Enable/Disable test mode force on SS no of steps
    *  PSU_SERDES_L3_PLL_SS_STEP_SIZE_3_MSB_FORCE_SS_NUM_OF_STEPS  0x1

    * Enable test mode forcing on enable Spread Spectrum
    *  PSU_SERDES_L3_PLL_SS_STEP_SIZE_3_MSB_TM_FORCE_EN_SS         0x1

    * Enable force on enable Spread Spectrum
    * (OFFSET, MASK, VALUE)      (0XFD40E37C, 0x000000B3U ,0x000000B0U)
    */
	PSU_Mask_Write(SERDES_L3_PLL_SS_STEP_SIZE_3_MSB_OFFSET,
		0x000000B3U, 0x000000B0U);
/*##################################################################### */

    /*
    * Register : L2_TM_DIG_6 @ 0XFD40906C

    * Bypass Descrambler
    *  PSU_SERDES_L2_TM_DIG_6_BYPASS_DESCRAM                       0x1

    * Enable Bypass for <1> TM_DIG_CTRL_6
    *  PSU_SERDES_L2_TM_DIG_6_FORCE_BYPASS_DESCRAM                 0x1

    * Data path test modes in decoder and descram
    * (OFFSET, MASK, VALUE)      (0XFD40906C, 0x00000003U ,0x00000003U)
    */
	PSU_Mask_Write(SERDES_L2_TM_DIG_6_OFFSET, 0x00000003U, 0x00000003U);
/*##################################################################### */

    /*
    * Register : L2_TX_DIG_TM_61 @ 0XFD4080F4

    * Bypass scrambler signal
    *  PSU_SERDES_L2_TX_DIG_TM_61_BYPASS_SCRAM                     0x1

    * Enable/disable scrambler bypass signal
    *  PSU_SERDES_L2_TX_DIG_TM_61_FORCE_BYPASS_SCRAM               0x1

    * MPHY PLL Gear and bypass scrambler
    * (OFFSET, MASK, VALUE)      (0XFD4080F4, 0x00000003U ,0x00000003U)
    */
	PSU_Mask_Write(SERDES_L2_TX_DIG_TM_61_OFFSET,
		0x00000003U, 0x00000003U);
/*##################################################################### */

    /*
    * Register : L3_PLL_FBDIV_FRAC_3_MSB @ 0XFD40E360

    * Enable test mode force on fractional mode enable
    *  PSU_SERDES_L3_PLL_FBDIV_FRAC_3_MSB_TM_FORCE_EN_FRAC         0x1

    * Fractional feedback division control and fractional value for feedback d
    * ivision bits 26:24
    * (OFFSET, MASK, VALUE)      (0XFD40E360, 0x00000040U ,0x00000040U)
    */
	PSU_Mask_Write(SERDES_L3_PLL_FBDIV_FRAC_3_MSB_OFFSET,
		0x00000040U, 0x00000040U);
/*##################################################################### */

    /*
    * Register : L3_TM_DIG_6 @ 0XFD40D06C

    * Bypass 8b10b decoder
    *  PSU_SERDES_L3_TM_DIG_6_BYPASS_DECODER                       0x1

    * Enable Bypass for <3> TM_DIG_CTRL_6
    *  PSU_SERDES_L3_TM_DIG_6_FORCE_BYPASS_DEC                     0x1

    * Bypass Descrambler
    *  PSU_SERDES_L3_TM_DIG_6_BYPASS_DESCRAM                       0x1

    * Enable Bypass for <1> TM_DIG_CTRL_6
    *  PSU_SERDES_L3_TM_DIG_6_FORCE_BYPASS_DESCRAM                 0x1

    * Data path test modes in decoder and descram
    * (OFFSET, MASK, VALUE)      (0XFD40D06C, 0x0000000FU ,0x0000000FU)
    */
	PSU_Mask_Write(SERDES_L3_TM_DIG_6_OFFSET, 0x0000000FU, 0x0000000FU);
/*##################################################################### */

    /*
    * Register : L3_TX_DIG_TM_61 @ 0XFD40C0F4

    * Enable/disable encoder bypass signal
    *  PSU_SERDES_L3_TX_DIG_TM_61_BYPASS_ENC                       0x1

    * Bypass scrambler signal
    *  PSU_SERDES_L3_TX_DIG_TM_61_BYPASS_SCRAM                     0x1

    * Enable/disable scrambler bypass signal
    *  PSU_SERDES_L3_TX_DIG_TM_61_FORCE_BYPASS_SCRAM               0x1

    * MPHY PLL Gear and bypass scrambler
    * (OFFSET, MASK, VALUE)      (0XFD40C0F4, 0x0000000BU ,0x0000000BU)
    */
	PSU_Mask_Write(SERDES_L3_TX_DIG_TM_61_OFFSET,
		0x0000000BU, 0x0000000BU);
/*##################################################################### */

    /*
    * ENABLE CHICKEN BIT FOR PCIE AND USB
    */
    /*
    * Register : L0_TM_AUX_0 @ 0XFD4010CC

    * Spare- not used
    *  PSU_SERDES_L0_TM_AUX_0_BIT_2                                1

    * Spare registers
    * (OFFSET, MASK, VALUE)      (0XFD4010CC, 0x00000020U ,0x00000020U)
    */
	PSU_Mask_Write(SERDES_L0_TM_AUX_0_OFFSET, 0x00000020U, 0x00000020U);
/*##################################################################### */

    /*
    * Register : L2_TM_AUX_0 @ 0XFD4090CC

    * Spare- not used
    *  PSU_SERDES_L2_TM_AUX_0_BIT_2                                1

    * Spare registers
    * (OFFSET, MASK, VALUE)      (0XFD4090CC, 0x00000020U ,0x00000020U)
    */
	PSU_Mask_Write(SERDES_L2_TM_AUX_0_OFFSET, 0x00000020U, 0x00000020U);
/*##################################################################### */

    /*
    * ENABLING EYE SURF
    */
    /*
    * Register : L0_TM_DIG_8 @ 0XFD401074

    * Enable Eye Surf
    *  PSU_SERDES_L0_TM_DIG_8_EYESURF_ENABLE                       0x1

    * Test modes for Elastic buffer and enabling Eye Surf
    * (OFFSET, MASK, VALUE)      (0XFD401074, 0x00000010U ,0x00000010U)
    */
	PSU_Mask_Write(SERDES_L0_TM_DIG_8_OFFSET, 0x00000010U, 0x00000010U);
/*##################################################################### */

    /*
    * Register : L1_TM_DIG_8 @ 0XFD405074

    * Enable Eye Surf
    *  PSU_SERDES_L1_TM_DIG_8_EYESURF_ENABLE                       0x1

    * Test modes for Elastic buffer and enabling Eye Surf
    * (OFFSET, MASK, VALUE)      (0XFD405074, 0x00000010U ,0x00000010U)
    */
	PSU_Mask_Write(SERDES_L1_TM_DIG_8_OFFSET, 0x00000010U, 0x00000010U);
/*##################################################################### */

    /*
    * Register : L2_TM_DIG_8 @ 0XFD409074

    * Enable Eye Surf
    *  PSU_SERDES_L2_TM_DIG_8_EYESURF_ENABLE                       0x1

    * Test modes for Elastic buffer and enabling Eye Surf
    * (OFFSET, MASK, VALUE)      (0XFD409074, 0x00000010U ,0x00000010U)
    */
	PSU_Mask_Write(SERDES_L2_TM_DIG_8_OFFSET, 0x00000010U, 0x00000010U);
/*##################################################################### */

    /*
    * Register : L3_TM_DIG_8 @ 0XFD40D074

    * Enable Eye Surf
    *  PSU_SERDES_L3_TM_DIG_8_EYESURF_ENABLE                       0x1

    * Test modes for Elastic buffer and enabling Eye Surf
    * (OFFSET, MASK, VALUE)      (0XFD40D074, 0x00000010U ,0x00000010U)
    */
	PSU_Mask_Write(SERDES_L3_TM_DIG_8_OFFSET, 0x00000010U, 0x00000010U);
/*##################################################################### */

    /*
    * ILL SETTINGS FOR GAIN AND LOCK SETTINGS
    */
    /*
    * Register : L0_TM_MISC2 @ 0XFD40189C

    * ILL calib counts BYPASSED with calcode bits
    *  PSU_SERDES_L0_TM_MISC2_ILL_CAL_BYPASS_COUNTS                0x1

    * sampler cal
    * (OFFSET, MASK, VALUE)      (0XFD40189C, 0x00000080U ,0x00000080U)
    */
	PSU_Mask_Write(SERDES_L0_TM_MISC2_OFFSET, 0x00000080U, 0x00000080U);
/*##################################################################### */

    /*
    * Register : L0_TM_IQ_ILL1 @ 0XFD4018F8

    * IQ ILL F0 CALCODE bypass value. MPHY : G1a, PCIE : Gen 1, SATA : Gen1 ,
    * USB3 : SS
    *  PSU_SERDES_L0_TM_IQ_ILL1_ILL_BYPASS_IQ_CALCODE_F0           0x64

    * iqpi cal code
    * (OFFSET, MASK, VALUE)      (0XFD4018F8, 0x000000FFU ,0x00000064U)
    */
	PSU_Mask_Write(SERDES_L0_TM_IQ_ILL1_OFFSET,
		0x000000FFU, 0x00000064U);
/*##################################################################### */

    /*
    * Register : L0_TM_IQ_ILL2 @ 0XFD4018FC

    * IQ ILL F1 CALCODE bypass value. MPHY : G1b, PCIE : Gen2, SATA: Gen2
    *  PSU_SERDES_L0_TM_IQ_ILL2_ILL_BYPASS_IQ_CALCODE_F1           0x64

    * iqpi cal code
    * (OFFSET, MASK, VALUE)      (0XFD4018FC, 0x000000FFU ,0x00000064U)
    */
	PSU_Mask_Write(SERDES_L0_TM_IQ_ILL2_OFFSET,
		0x000000FFU, 0x00000064U);
/*##################################################################### */

    /*
    * Register : L0_TM_ILL12 @ 0XFD401990

    * G1A pll ctr bypass value
    *  PSU_SERDES_L0_TM_ILL12_G1A_PLL_CTR_BYP_VAL                  0x11

    * ill pll counter values
    * (OFFSET, MASK, VALUE)      (0XFD401990, 0x000000FFU ,0x00000011U)
    */
	PSU_Mask_Write(SERDES_L0_TM_ILL12_OFFSET, 0x000000FFU, 0x00000011U);
/*##################################################################### */

    /*
    * Register : L0_TM_E_ILL1 @ 0XFD401924

    * E ILL F0 CALCODE bypass value. MPHY : G1a, PCIE : Gen 1, SATA : Gen1 , U
    * SB3 : SS
    *  PSU_SERDES_L0_TM_E_ILL1_ILL_BYPASS_E_CALCODE_F0             0x4

    * epi cal code
    * (OFFSET, MASK, VALUE)      (0XFD401924, 0x000000FFU ,0x00000004U)
    */
	PSU_Mask_Write(SERDES_L0_TM_E_ILL1_OFFSET, 0x000000FFU, 0x00000004U);
/*##################################################################### */

    /*
    * Register : L0_TM_E_ILL2 @ 0XFD401928

    * E ILL F1 CALCODE bypass value. MPHY : G1b, PCIE : Gen2, SATA: Gen2
    *  PSU_SERDES_L0_TM_E_ILL2_ILL_BYPASS_E_CALCODE_F1             0xFE

    * epi cal code
    * (OFFSET, MASK, VALUE)      (0XFD401928, 0x000000FFU ,0x000000FEU)
    */
	PSU_Mask_Write(SERDES_L0_TM_E_ILL2_OFFSET, 0x000000FFU, 0x000000FEU);
/*##################################################################### */

    /*
    * Register : L0_TM_IQ_ILL3 @ 0XFD401900

    * IQ ILL F2CALCODE bypass value. MPHY : G2a, SATA : Gen3
    *  PSU_SERDES_L0_TM_IQ_ILL3_ILL_BYPASS_IQ_CALCODE_F2           0x64

    * iqpi cal code
    * (OFFSET, MASK, VALUE)      (0XFD401900, 0x000000FFU ,0x00000064U)
    */
	PSU_Mask_Write(SERDES_L0_TM_IQ_ILL3_OFFSET,
		0x000000FFU, 0x00000064U);
/*##################################################################### */

    /*
    * Register : L0_TM_E_ILL3 @ 0XFD40192C

    * E ILL F2CALCODE bypass value. MPHY : G2a, SATA : Gen3
    *  PSU_SERDES_L0_TM_E_ILL3_ILL_BYPASS_E_CALCODE_F2             0x0

    * epi cal code
    * (OFFSET, MASK, VALUE)      (0XFD40192C, 0x000000FFU ,0x00000000U)
    */
	PSU_Mask_Write(SERDES_L0_TM_E_ILL3_OFFSET, 0x000000FFU, 0x00000000U);
/*##################################################################### */

    /*
    * Register : L0_TM_ILL8 @ 0XFD401980

    * ILL calibration code change wait time
    *  PSU_SERDES_L0_TM_ILL8_ILL_CAL_ITER_WAIT                     0xFF

    * ILL cal routine control
    * (OFFSET, MASK, VALUE)      (0XFD401980, 0x000000FFU ,0x000000FFU)
    */
	PSU_Mask_Write(SERDES_L0_TM_ILL8_OFFSET, 0x000000FFU, 0x000000FFU);
/*##################################################################### */

    /*
    * Register : L0_TM_IQ_ILL8 @ 0XFD401914

    * IQ ILL polytrim bypass value
    *  PSU_SERDES_L0_TM_IQ_ILL8_ILL_BYPASS_IQ_POLYTRIM_VAL         0xF7

    * iqpi polytrim
    * (OFFSET, MASK, VALUE)      (0XFD401914, 0x000000FFU ,0x000000F7U)
    */
	PSU_Mask_Write(SERDES_L0_TM_IQ_ILL8_OFFSET,
		0x000000FFU, 0x000000F7U);
/*##################################################################### */

    /*
    * Register : L0_TM_IQ_ILL9 @ 0XFD401918

    * bypass IQ polytrim
    *  PSU_SERDES_L0_TM_IQ_ILL9_ILL_BYPASS_IQ_POLYTIM              0x1

    * enables for lf,constant gm trim and polytirm
    * (OFFSET, MASK, VALUE)      (0XFD401918, 0x00000001U ,0x00000001U)
    */
	PSU_Mask_Write(SERDES_L0_TM_IQ_ILL9_OFFSET,
		0x00000001U, 0x00000001U);
/*##################################################################### */

    /*
    * Register : L0_TM_E_ILL8 @ 0XFD401940

    * E ILL polytrim bypass value
    *  PSU_SERDES_L0_TM_E_ILL8_ILL_BYPASS_E_POLYTRIM_VAL           0xF7

    * epi polytrim
    * (OFFSET, MASK, VALUE)      (0XFD401940, 0x000000FFU ,0x000000F7U)
    */
	PSU_Mask_Write(SERDES_L0_TM_E_ILL8_OFFSET, 0x000000FFU, 0x000000F7U);
/*##################################################################### */

    /*
    * Register : L0_TM_E_ILL9 @ 0XFD401944

    * bypass E polytrim
    *  PSU_SERDES_L0_TM_E_ILL9_ILL_BYPASS_E_POLYTIM                0x1

    * enables for lf,constant gm trim and polytirm
    * (OFFSET, MASK, VALUE)      (0XFD401944, 0x00000001U ,0x00000001U)
    */
	PSU_Mask_Write(SERDES_L0_TM_E_ILL9_OFFSET, 0x00000001U, 0x00000001U);
/*##################################################################### */

    /*
    * Register : L0_TM_ILL13 @ 0XFD401994

    * ILL cal idle val refcnt
    *  PSU_SERDES_L0_TM_ILL13_ILL_CAL_IDLE_VAL_REFCNT              0x7

    * ill cal idle value count
    * (OFFSET, MASK, VALUE)      (0XFD401994, 0x00000007U ,0x00000007U)
    */
	PSU_Mask_Write(SERDES_L0_TM_ILL13_OFFSET, 0x00000007U, 0x00000007U);
/*##################################################################### */

    /*
    * Register : L1_TM_ILL13 @ 0XFD405994

    * ILL cal idle val refcnt
    *  PSU_SERDES_L1_TM_ILL13_ILL_CAL_IDLE_VAL_REFCNT              0x7

    * ill cal idle value count
    * (OFFSET, MASK, VALUE)      (0XFD405994, 0x00000007U ,0x00000007U)
    */
	PSU_Mask_Write(SERDES_L1_TM_ILL13_OFFSET, 0x00000007U, 0x00000007U);
/*##################################################################### */

    /*
    * Register : L2_TM_MISC2 @ 0XFD40989C

    * ILL calib counts BYPASSED with calcode bits
    *  PSU_SERDES_L2_TM_MISC2_ILL_CAL_BYPASS_COUNTS                0x1

    * sampler cal
    * (OFFSET, MASK, VALUE)      (0XFD40989C, 0x00000080U ,0x00000080U)
    */
	PSU_Mask_Write(SERDES_L2_TM_MISC2_OFFSET, 0x00000080U, 0x00000080U);
/*##################################################################### */

    /*
    * Register : L2_TM_IQ_ILL1 @ 0XFD4098F8

    * IQ ILL F0 CALCODE bypass value. MPHY : G1a, PCIE : Gen 1, SATA : Gen1 ,
    * USB3 : SS
    *  PSU_SERDES_L2_TM_IQ_ILL1_ILL_BYPASS_IQ_CALCODE_F0           0x1A

    * iqpi cal code
    * (OFFSET, MASK, VALUE)      (0XFD4098F8, 0x000000FFU ,0x0000001AU)
    */
	PSU_Mask_Write(SERDES_L2_TM_IQ_ILL1_OFFSET,
		0x000000FFU, 0x0000001AU);
/*##################################################################### */

    /*
    * Register : L2_TM_IQ_ILL2 @ 0XFD4098FC

    * IQ ILL F1 CALCODE bypass value. MPHY : G1b, PCIE : Gen2, SATA: Gen2
    *  PSU_SERDES_L2_TM_IQ_ILL2_ILL_BYPASS_IQ_CALCODE_F1           0x1A

    * iqpi cal code
    * (OFFSET, MASK, VALUE)      (0XFD4098FC, 0x000000FFU ,0x0000001AU)
    */
	PSU_Mask_Write(SERDES_L2_TM_IQ_ILL2_OFFSET,
		0x000000FFU, 0x0000001AU);
/*##################################################################### */

    /*
    * Register : L2_TM_ILL12 @ 0XFD409990

    * G1A pll ctr bypass value
    *  PSU_SERDES_L2_TM_ILL12_G1A_PLL_CTR_BYP_VAL                  0x10

    * ill pll counter values
    * (OFFSET, MASK, VALUE)      (0XFD409990, 0x000000FFU ,0x00000010U)
    */
	PSU_Mask_Write(SERDES_L2_TM_ILL12_OFFSET, 0x000000FFU, 0x00000010U);
/*##################################################################### */

    /*
    * Register : L2_TM_E_ILL1 @ 0XFD409924

    * E ILL F0 CALCODE bypass value. MPHY : G1a, PCIE : Gen 1, SATA : Gen1 , U
    * SB3 : SS
    *  PSU_SERDES_L2_TM_E_ILL1_ILL_BYPASS_E_CALCODE_F0             0xFE

    * epi cal code
    * (OFFSET, MASK, VALUE)      (0XFD409924, 0x000000FFU ,0x000000FEU)
    */
	PSU_Mask_Write(SERDES_L2_TM_E_ILL1_OFFSET, 0x000000FFU, 0x000000FEU);
/*##################################################################### */

    /*
    * Register : L2_TM_E_ILL2 @ 0XFD409928

    * E ILL F1 CALCODE bypass value. MPHY : G1b, PCIE : Gen2, SATA: Gen2
    *  PSU_SERDES_L2_TM_E_ILL2_ILL_BYPASS_E_CALCODE_F1             0x0

    * epi cal code
    * (OFFSET, MASK, VALUE)      (0XFD409928, 0x000000FFU ,0x00000000U)
    */
	PSU_Mask_Write(SERDES_L2_TM_E_ILL2_OFFSET, 0x000000FFU, 0x00000000U);
/*##################################################################### */

    /*
    * Register : L2_TM_IQ_ILL3 @ 0XFD409900

    * IQ ILL F2CALCODE bypass value. MPHY : G2a, SATA : Gen3
    *  PSU_SERDES_L2_TM_IQ_ILL3_ILL_BYPASS_IQ_CALCODE_F2           0x1A

    * iqpi cal code
    * (OFFSET, MASK, VALUE)      (0XFD409900, 0x000000FFU ,0x0000001AU)
    */
	PSU_Mask_Write(SERDES_L2_TM_IQ_ILL3_OFFSET,
		0x000000FFU, 0x0000001AU);
/*##################################################################### */

    /*
    * Register : L2_TM_E_ILL3 @ 0XFD40992C

    * E ILL F2CALCODE bypass value. MPHY : G2a, SATA : Gen3
    *  PSU_SERDES_L2_TM_E_ILL3_ILL_BYPASS_E_CALCODE_F2             0x0

    * epi cal code
    * (OFFSET, MASK, VALUE)      (0XFD40992C, 0x000000FFU ,0x00000000U)
    */
	PSU_Mask_Write(SERDES_L2_TM_E_ILL3_OFFSET, 0x000000FFU, 0x00000000U);
/*##################################################################### */

    /*
    * Register : L2_TM_ILL8 @ 0XFD409980

    * ILL calibration code change wait time
    *  PSU_SERDES_L2_TM_ILL8_ILL_CAL_ITER_WAIT                     0xFF

    * ILL cal routine control
    * (OFFSET, MASK, VALUE)      (0XFD409980, 0x000000FFU ,0x000000FFU)
    */
	PSU_Mask_Write(SERDES_L2_TM_ILL8_OFFSET, 0x000000FFU, 0x000000FFU);
/*##################################################################### */

    /*
    * Register : L2_TM_IQ_ILL8 @ 0XFD409914

    * IQ ILL polytrim bypass value
    *  PSU_SERDES_L2_TM_IQ_ILL8_ILL_BYPASS_IQ_POLYTRIM_VAL         0xF7

    * iqpi polytrim
    * (OFFSET, MASK, VALUE)      (0XFD409914, 0x000000FFU ,0x000000F7U)
    */
	PSU_Mask_Write(SERDES_L2_TM_IQ_ILL8_OFFSET,
		0x000000FFU, 0x000000F7U);
/*##################################################################### */

    /*
    * Register : L2_TM_IQ_ILL9 @ 0XFD409918

    * bypass IQ polytrim
    *  PSU_SERDES_L2_TM_IQ_ILL9_ILL_BYPASS_IQ_POLYTIM              0x1

    * enables for lf,constant gm trim and polytirm
    * (OFFSET, MASK, VALUE)      (0XFD409918, 0x00000001U ,0x00000001U)
    */
	PSU_Mask_Write(SERDES_L2_TM_IQ_ILL9_OFFSET,
		0x00000001U, 0x00000001U);
/*##################################################################### */

    /*
    * Register : L2_TM_E_ILL8 @ 0XFD409940

    * E ILL polytrim bypass value
    *  PSU_SERDES_L2_TM_E_ILL8_ILL_BYPASS_E_POLYTRIM_VAL           0xF7

    * epi polytrim
    * (OFFSET, MASK, VALUE)      (0XFD409940, 0x000000FFU ,0x000000F7U)
    */
	PSU_Mask_Write(SERDES_L2_TM_E_ILL8_OFFSET, 0x000000FFU, 0x000000F7U);
/*##################################################################### */

    /*
    * Register : L2_TM_E_ILL9 @ 0XFD409944

    * bypass E polytrim
    *  PSU_SERDES_L2_TM_E_ILL9_ILL_BYPASS_E_POLYTIM                0x1

    * enables for lf,constant gm trim and polytirm
    * (OFFSET, MASK, VALUE)      (0XFD409944, 0x00000001U ,0x00000001U)
    */
	PSU_Mask_Write(SERDES_L2_TM_E_ILL9_OFFSET, 0x00000001U, 0x00000001U);
/*##################################################################### */

    /*
    * Register : L2_TM_ILL13 @ 0XFD409994

    * ILL cal idle val refcnt
    *  PSU_SERDES_L2_TM_ILL13_ILL_CAL_IDLE_VAL_REFCNT              0x7

    * ill cal idle value count
    * (OFFSET, MASK, VALUE)      (0XFD409994, 0x00000007U ,0x00000007U)
    */
	PSU_Mask_Write(SERDES_L2_TM_ILL13_OFFSET, 0x00000007U, 0x00000007U);
/*##################################################################### */

    /*
    * Register : L3_TM_MISC2 @ 0XFD40D89C

    * ILL calib counts BYPASSED with calcode bits
    *  PSU_SERDES_L3_TM_MISC2_ILL_CAL_BYPASS_COUNTS                0x1

    * sampler cal
    * (OFFSET, MASK, VALUE)      (0XFD40D89C, 0x00000080U ,0x00000080U)
    */
	PSU_Mask_Write(SERDES_L3_TM_MISC2_OFFSET, 0x00000080U, 0x00000080U);
/*##################################################################### */

    /*
    * Register : L3_TM_IQ_ILL1 @ 0XFD40D8F8

    * IQ ILL F0 CALCODE bypass value. MPHY : G1a, PCIE : Gen 1, SATA : Gen1 ,
    * USB3 : SS
    *  PSU_SERDES_L3_TM_IQ_ILL1_ILL_BYPASS_IQ_CALCODE_F0           0x7D

    * iqpi cal code
    * (OFFSET, MASK, VALUE)      (0XFD40D8F8, 0x000000FFU ,0x0000007DU)
    */
	PSU_Mask_Write(SERDES_L3_TM_IQ_ILL1_OFFSET,
		0x000000FFU, 0x0000007DU);
/*##################################################################### */

    /*
    * Register : L3_TM_IQ_ILL2 @ 0XFD40D8FC

    * IQ ILL F1 CALCODE bypass value. MPHY : G1b, PCIE : Gen2, SATA: Gen2
    *  PSU_SERDES_L3_TM_IQ_ILL2_ILL_BYPASS_IQ_CALCODE_F1           0x7D

    * iqpi cal code
    * (OFFSET, MASK, VALUE)      (0XFD40D8FC, 0x000000FFU ,0x0000007DU)
    */
	PSU_Mask_Write(SERDES_L3_TM_IQ_ILL2_OFFSET,
		0x000000FFU, 0x0000007DU);
/*##################################################################### */

    /*
    * Register : L3_TM_ILL12 @ 0XFD40D990

    * G1A pll ctr bypass value
    *  PSU_SERDES_L3_TM_ILL12_G1A_PLL_CTR_BYP_VAL                  0x1

    * ill pll counter values
    * (OFFSET, MASK, VALUE)      (0XFD40D990, 0x000000FFU ,0x00000001U)
    */
	PSU_Mask_Write(SERDES_L3_TM_ILL12_OFFSET, 0x000000FFU, 0x00000001U);
/*##################################################################### */

    /*
    * Register : L3_TM_E_ILL1 @ 0XFD40D924

    * E ILL F0 CALCODE bypass value. MPHY : G1a, PCIE : Gen 1, SATA : Gen1 , U
    * SB3 : SS
    *  PSU_SERDES_L3_TM_E_ILL1_ILL_BYPASS_E_CALCODE_F0             0x9C

    * epi cal code
    * (OFFSET, MASK, VALUE)      (0XFD40D924, 0x000000FFU ,0x0000009CU)
    */
	PSU_Mask_Write(SERDES_L3_TM_E_ILL1_OFFSET, 0x000000FFU, 0x0000009CU);
/*##################################################################### */

    /*
    * Register : L3_TM_E_ILL2 @ 0XFD40D928

    * E ILL F1 CALCODE bypass value. MPHY : G1b, PCIE : Gen2, SATA: Gen2
    *  PSU_SERDES_L3_TM_E_ILL2_ILL_BYPASS_E_CALCODE_F1             0x39

    * epi cal code
    * (OFFSET, MASK, VALUE)      (0XFD40D928, 0x000000FFU ,0x00000039U)
    */
	PSU_Mask_Write(SERDES_L3_TM_E_ILL2_OFFSET, 0x000000FFU, 0x00000039U);
/*##################################################################### */

    /*
    * Register : L3_TM_ILL11 @ 0XFD40D98C

    * G2A_PCIe1 PLL ctr bypass value
    *  PSU_SERDES_L3_TM_ILL11_G2A_PCIEG1_PLL_CTR_11_8_BYP_VAL      0x2

    * ill pll counter values
    * (OFFSET, MASK, VALUE)      (0XFD40D98C, 0x000000F0U ,0x00000020U)
    */
	PSU_Mask_Write(SERDES_L3_TM_ILL11_OFFSET, 0x000000F0U, 0x00000020U);
/*##################################################################### */

    /*
    * Register : L3_TM_IQ_ILL3 @ 0XFD40D900

    * IQ ILL F2CALCODE bypass value. MPHY : G2a, SATA : Gen3
    *  PSU_SERDES_L3_TM_IQ_ILL3_ILL_BYPASS_IQ_CALCODE_F2           0x7D

    * iqpi cal code
    * (OFFSET, MASK, VALUE)      (0XFD40D900, 0x000000FFU ,0x0000007DU)
    */
	PSU_Mask_Write(SERDES_L3_TM_IQ_ILL3_OFFSET,
		0x000000FFU, 0x0000007DU);
/*##################################################################### */

    /*
    * Register : L3_TM_E_ILL3 @ 0XFD40D92C

    * E ILL F2CALCODE bypass value. MPHY : G2a, SATA : Gen3
    *  PSU_SERDES_L3_TM_E_ILL3_ILL_BYPASS_E_CALCODE_F2             0x64

    * epi cal code
    * (OFFSET, MASK, VALUE)      (0XFD40D92C, 0x000000FFU ,0x00000064U)
    */
	PSU_Mask_Write(SERDES_L3_TM_E_ILL3_OFFSET, 0x000000FFU, 0x00000064U);
/*##################################################################### */

    /*
    * Register : L3_TM_ILL8 @ 0XFD40D980

    * ILL calibration code change wait time
    *  PSU_SERDES_L3_TM_ILL8_ILL_CAL_ITER_WAIT                     0xFF

    * ILL cal routine control
    * (OFFSET, MASK, VALUE)      (0XFD40D980, 0x000000FFU ,0x000000FFU)
    */
	PSU_Mask_Write(SERDES_L3_TM_ILL8_OFFSET, 0x000000FFU, 0x000000FFU);
/*##################################################################### */

    /*
    * Register : L3_TM_IQ_ILL8 @ 0XFD40D914

    * IQ ILL polytrim bypass value
    *  PSU_SERDES_L3_TM_IQ_ILL8_ILL_BYPASS_IQ_POLYTRIM_VAL         0xF7

    * iqpi polytrim
    * (OFFSET, MASK, VALUE)      (0XFD40D914, 0x000000FFU ,0x000000F7U)
    */
	PSU_Mask_Write(SERDES_L3_TM_IQ_ILL8_OFFSET,
		0x000000FFU, 0x000000F7U);
/*##################################################################### */

    /*
    * Register : L3_TM_IQ_ILL9 @ 0XFD40D918

    * bypass IQ polytrim
    *  PSU_SERDES_L3_TM_IQ_ILL9_ILL_BYPASS_IQ_POLYTIM              0x1

    * enables for lf,constant gm trim and polytirm
    * (OFFSET, MASK, VALUE)      (0XFD40D918, 0x00000001U ,0x00000001U)
    */
	PSU_Mask_Write(SERDES_L3_TM_IQ_ILL9_OFFSET,
		0x00000001U, 0x00000001U);
/*##################################################################### */

    /*
    * Register : L3_TM_E_ILL8 @ 0XFD40D940

    * E ILL polytrim bypass value
    *  PSU_SERDES_L3_TM_E_ILL8_ILL_BYPASS_E_POLYTRIM_VAL           0xF7

    * epi polytrim
    * (OFFSET, MASK, VALUE)      (0XFD40D940, 0x000000FFU ,0x000000F7U)
    */
	PSU_Mask_Write(SERDES_L3_TM_E_ILL8_OFFSET, 0x000000FFU, 0x000000F7U);
/*##################################################################### */

    /*
    * Register : L3_TM_E_ILL9 @ 0XFD40D944

    * bypass E polytrim
    *  PSU_SERDES_L3_TM_E_ILL9_ILL_BYPASS_E_POLYTIM                0x1

    * enables for lf,constant gm trim and polytirm
    * (OFFSET, MASK, VALUE)      (0XFD40D944, 0x00000001U ,0x00000001U)
    */
	PSU_Mask_Write(SERDES_L3_TM_E_ILL9_OFFSET, 0x00000001U, 0x00000001U);
/*##################################################################### */

    /*
    * Register : L3_TM_ILL13 @ 0XFD40D994

    * ILL cal idle val refcnt
    *  PSU_SERDES_L3_TM_ILL13_ILL_CAL_IDLE_VAL_REFCNT              0x7

    * ill cal idle value count
    * (OFFSET, MASK, VALUE)      (0XFD40D994, 0x00000007U ,0x00000007U)
    */
	PSU_Mask_Write(SERDES_L3_TM_ILL13_OFFSET, 0x00000007U, 0x00000007U);
/*##################################################################### */

    /*
    * SYMBOL LOCK AND WAIT
    */
    /*
    * Register : L0_TM_DIG_10 @ 0XFD40107C

    * CDR lock wait time. (1-16 us). cdr_lock_wait_time = 4'b xxxx + 4'b 0001
    *  PSU_SERDES_L0_TM_DIG_10_CDR_BIT_LOCK_TIME                   0x1

    * test control for changing cdr lock wait time
    * (OFFSET, MASK, VALUE)      (0XFD40107C, 0x0000000FU ,0x00000001U)
    */
	PSU_Mask_Write(SERDES_L0_TM_DIG_10_OFFSET, 0x0000000FU, 0x00000001U);
/*##################################################################### */

    /*
    * Register : L1_TM_DIG_10 @ 0XFD40507C

    * CDR lock wait time. (1-16 us). cdr_lock_wait_time = 4'b xxxx + 4'b 0001
    *  PSU_SERDES_L1_TM_DIG_10_CDR_BIT_LOCK_TIME                   0x1

    * test control for changing cdr lock wait time
    * (OFFSET, MASK, VALUE)      (0XFD40507C, 0x0000000FU ,0x00000001U)
    */
	PSU_Mask_Write(SERDES_L1_TM_DIG_10_OFFSET, 0x0000000FU, 0x00000001U);
/*##################################################################### */

    /*
    * Register : L2_TM_DIG_10 @ 0XFD40907C

    * CDR lock wait time. (1-16 us). cdr_lock_wait_time = 4'b xxxx + 4'b 0001
    *  PSU_SERDES_L2_TM_DIG_10_CDR_BIT_LOCK_TIME                   0x1

    * test control for changing cdr lock wait time
    * (OFFSET, MASK, VALUE)      (0XFD40907C, 0x0000000FU ,0x00000001U)
    */
	PSU_Mask_Write(SERDES_L2_TM_DIG_10_OFFSET, 0x0000000FU, 0x00000001U);
/*##################################################################### */

    /*
    * Register : L3_TM_DIG_10 @ 0XFD40D07C

    * CDR lock wait time. (1-16 us). cdr_lock_wait_time = 4'b xxxx + 4'b 0001
    *  PSU_SERDES_L3_TM_DIG_10_CDR_BIT_LOCK_TIME                   0x1

    * test control for changing cdr lock wait time
    * (OFFSET, MASK, VALUE)      (0XFD40D07C, 0x0000000FU ,0x00000001U)
    */
	PSU_Mask_Write(SERDES_L3_TM_DIG_10_OFFSET, 0x0000000FU, 0x00000001U);
/*##################################################################### */

    /*
    * SIOU SETTINGS FOR BYPASS CONTROL,HSRX-DIG
    */
    /*
    * Register : L0_TM_RST_DLY @ 0XFD4019A4

    * Delay apb reset by specified amount
    *  PSU_SERDES_L0_TM_RST_DLY_APB_RST_DLY                        0xFF

    * reset delay for apb reset w.r.t pso of hsrx
    * (OFFSET, MASK, VALUE)      (0XFD4019A4, 0x000000FFU ,0x000000FFU)
    */
	PSU_Mask_Write(SERDES_L0_TM_RST_DLY_OFFSET,
		0x000000FFU, 0x000000FFU);
/*##################################################################### */

    /*
    * Register : L0_TM_ANA_BYP_15 @ 0XFD401038

    * Enable Bypass for <7> of TM_ANA_BYPS_15
    *  PSU_SERDES_L0_TM_ANA_BYP_15_FORCE_UPHY_ENABLE_LOW_LEAKAGE   0x1

    * Bypass control for pcs-pma interface. EQ supplies, main master supply an
    * d ps for samp c2c
    * (OFFSET, MASK, VALUE)      (0XFD401038, 0x00000040U ,0x00000040U)
    */
	PSU_Mask_Write(SERDES_L0_TM_ANA_BYP_15_OFFSET,
		0x00000040U, 0x00000040U);
/*##################################################################### */

    /*
    * Register : L0_TM_ANA_BYP_12 @ 0XFD40102C

    * Enable Bypass for <7> of TM_ANA_BYPS_12
    *  PSU_SERDES_L0_TM_ANA_BYP_12_FORCE_UPHY_PSO_HSRXDIG          0x1

    * Bypass control for pcs-pma interface. Hsrx supply, hsrx des, and cdr ena
    * ble controls
    * (OFFSET, MASK, VALUE)      (0XFD40102C, 0x00000040U ,0x00000040U)
    */
	PSU_Mask_Write(SERDES_L0_TM_ANA_BYP_12_OFFSET,
		0x00000040U, 0x00000040U);
/*##################################################################### */

    /*
    * Register : L1_TM_RST_DLY @ 0XFD4059A4

    * Delay apb reset by specified amount
    *  PSU_SERDES_L1_TM_RST_DLY_APB_RST_DLY                        0xFF

    * reset delay for apb reset w.r.t pso of hsrx
    * (OFFSET, MASK, VALUE)      (0XFD4059A4, 0x000000FFU ,0x000000FFU)
    */
	PSU_Mask_Write(SERDES_L1_TM_RST_DLY_OFFSET,
		0x000000FFU, 0x000000FFU);
/*##################################################################### */

    /*
    * Register : L1_TM_ANA_BYP_15 @ 0XFD405038

    * Enable Bypass for <7> of TM_ANA_BYPS_15
    *  PSU_SERDES_L1_TM_ANA_BYP_15_FORCE_UPHY_ENABLE_LOW_LEAKAGE   0x1

    * Bypass control for pcs-pma interface. EQ supplies, main master supply an
    * d ps for samp c2c
    * (OFFSET, MASK, VALUE)      (0XFD405038, 0x00000040U ,0x00000040U)
    */
	PSU_Mask_Write(SERDES_L1_TM_ANA_BYP_15_OFFSET,
		0x00000040U, 0x00000040U);
/*##################################################################### */

    /*
    * Register : L1_TM_ANA_BYP_12 @ 0XFD40502C

    * Enable Bypass for <7> of TM_ANA_BYPS_12
    *  PSU_SERDES_L1_TM_ANA_BYP_12_FORCE_UPHY_PSO_HSRXDIG          0x1

    * Bypass control for pcs-pma interface. Hsrx supply, hsrx des, and cdr ena
    * ble controls
    * (OFFSET, MASK, VALUE)      (0XFD40502C, 0x00000040U ,0x00000040U)
    */
	PSU_Mask_Write(SERDES_L1_TM_ANA_BYP_12_OFFSET,
		0x00000040U, 0x00000040U);
/*##################################################################### */

    /*
    * Register : L2_TM_RST_DLY @ 0XFD4099A4

    * Delay apb reset by specified amount
    *  PSU_SERDES_L2_TM_RST_DLY_APB_RST_DLY                        0xFF

    * reset delay for apb reset w.r.t pso of hsrx
    * (OFFSET, MASK, VALUE)      (0XFD4099A4, 0x000000FFU ,0x000000FFU)
    */
	PSU_Mask_Write(SERDES_L2_TM_RST_DLY_OFFSET,
		0x000000FFU, 0x000000FFU);
/*##################################################################### */

    /*
    * Register : L2_TM_ANA_BYP_15 @ 0XFD409038

    * Enable Bypass for <7> of TM_ANA_BYPS_15
    *  PSU_SERDES_L2_TM_ANA_BYP_15_FORCE_UPHY_ENABLE_LOW_LEAKAGE   0x1

    * Bypass control for pcs-pma interface. EQ supplies, main master supply an
    * d ps for samp c2c
    * (OFFSET, MASK, VALUE)      (0XFD409038, 0x00000040U ,0x00000040U)
    */
	PSU_Mask_Write(SERDES_L2_TM_ANA_BYP_15_OFFSET,
		0x00000040U, 0x00000040U);
/*##################################################################### */

    /*
    * Register : L2_TM_ANA_BYP_12 @ 0XFD40902C

    * Enable Bypass for <7> of TM_ANA_BYPS_12
    *  PSU_SERDES_L2_TM_ANA_BYP_12_FORCE_UPHY_PSO_HSRXDIG          0x1

    * Bypass control for pcs-pma interface. Hsrx supply, hsrx des, and cdr ena
    * ble controls
    * (OFFSET, MASK, VALUE)      (0XFD40902C, 0x00000040U ,0x00000040U)
    */
	PSU_Mask_Write(SERDES_L2_TM_ANA_BYP_12_OFFSET,
		0x00000040U, 0x00000040U);
/*##################################################################### */

    /*
    * Register : L3_TM_RST_DLY @ 0XFD40D9A4

    * Delay apb reset by specified amount
    *  PSU_SERDES_L3_TM_RST_DLY_APB_RST_DLY                        0xFF

    * reset delay for apb reset w.r.t pso of hsrx
    * (OFFSET, MASK, VALUE)      (0XFD40D9A4, 0x000000FFU ,0x000000FFU)
    */
	PSU_Mask_Write(SERDES_L3_TM_RST_DLY_OFFSET,
		0x000000FFU, 0x000000FFU);
/*##################################################################### */

    /*
    * Register : L3_TM_ANA_BYP_15 @ 0XFD40D038

    * Enable Bypass for <7> of TM_ANA_BYPS_15
    *  PSU_SERDES_L3_TM_ANA_BYP_15_FORCE_UPHY_ENABLE_LOW_LEAKAGE   0x1

    * Bypass control for pcs-pma interface. EQ supplies, main master supply an
    * d ps for samp c2c
    * (OFFSET, MASK, VALUE)      (0XFD40D038, 0x00000040U ,0x00000040U)
    */
	PSU_Mask_Write(SERDES_L3_TM_ANA_BYP_15_OFFSET,
		0x00000040U, 0x00000040U);
/*##################################################################### */

    /*
    * Register : L3_TM_ANA_BYP_12 @ 0XFD40D02C

    * Enable Bypass for <7> of TM_ANA_BYPS_12
    *  PSU_SERDES_L3_TM_ANA_BYP_12_FORCE_UPHY_PSO_HSRXDIG          0x1

    * Bypass control for pcs-pma interface. Hsrx supply, hsrx des, and cdr ena
    * ble controls
    * (OFFSET, MASK, VALUE)      (0XFD40D02C, 0x00000040U ,0x00000040U)
    */
	PSU_Mask_Write(SERDES_L3_TM_ANA_BYP_12_OFFSET,
		0x00000040U, 0x00000040U);
/*##################################################################### */

    /*
    * DISABLE FPL/FFL
    */
    /*
    * Register : L0_TM_MISC3 @ 0XFD4019AC

    * CDR fast phase lock control
    *  PSU_SERDES_L0_TM_MISC3_CDR_EN_FPL                           0x0

    * CDR fast frequency lock control
    *  PSU_SERDES_L0_TM_MISC3_CDR_EN_FFL                           0x0

    * debug bus selection bit, cdr fast phase and freq controls
    * (OFFSET, MASK, VALUE)      (0XFD4019AC, 0x00000003U ,0x00000000U)
    */
	PSU_Mask_Write(SERDES_L0_TM_MISC3_OFFSET, 0x00000003U, 0x00000000U);
/*##################################################################### */

    /*
    * Register : L1_TM_MISC3 @ 0XFD4059AC

    * CDR fast phase lock control
    *  PSU_SERDES_L1_TM_MISC3_CDR_EN_FPL                           0x0

    * CDR fast frequency lock control
    *  PSU_SERDES_L1_TM_MISC3_CDR_EN_FFL                           0x0

    * debug bus selection bit, cdr fast phase and freq controls
    * (OFFSET, MASK, VALUE)      (0XFD4059AC, 0x00000003U ,0x00000000U)
    */
	PSU_Mask_Write(SERDES_L1_TM_MISC3_OFFSET, 0x00000003U, 0x00000000U);
/*##################################################################### */

    /*
    * Register : L2_TM_MISC3 @ 0XFD4099AC

    * CDR fast phase lock control
    *  PSU_SERDES_L2_TM_MISC3_CDR_EN_FPL                           0x0

    * CDR fast frequency lock control
    *  PSU_SERDES_L2_TM_MISC3_CDR_EN_FFL                           0x0

    * debug bus selection bit, cdr fast phase and freq controls
    * (OFFSET, MASK, VALUE)      (0XFD4099AC, 0x00000003U ,0x00000000U)
    */
	PSU_Mask_Write(SERDES_L2_TM_MISC3_OFFSET, 0x00000003U, 0x00000000U);
/*##################################################################### */

    /*
    * Register : L3_TM_MISC3 @ 0XFD40D9AC

    * CDR fast phase lock control
    *  PSU_SERDES_L3_TM_MISC3_CDR_EN_FPL                           0x0

    * CDR fast frequency lock control
    *  PSU_SERDES_L3_TM_MISC3_CDR_EN_FFL                           0x0

    * debug bus selection bit, cdr fast phase and freq controls
    * (OFFSET, MASK, VALUE)      (0XFD40D9AC, 0x00000003U ,0x00000000U)
    */
	PSU_Mask_Write(SERDES_L3_TM_MISC3_OFFSET, 0x00000003U, 0x00000000U);
/*##################################################################### */

    /*
    * DISABLE DYNAMIC OFFSET CALIBRATION
    */
    /*
    * Register : L0_TM_EQ11 @ 0XFD401978

    * Force EQ offset correction algo off if not forced on
    *  PSU_SERDES_L0_TM_EQ11_FORCE_EQ_OFFS_OFF                     0x1

    * eq dynamic offset correction
    * (OFFSET, MASK, VALUE)      (0XFD401978, 0x00000010U ,0x00000010U)
    */
	PSU_Mask_Write(SERDES_L0_TM_EQ11_OFFSET, 0x00000010U, 0x00000010U);
/*##################################################################### */

    /*
    * Register : L1_TM_EQ11 @ 0XFD405978

    * Force EQ offset correction algo off if not forced on
    *  PSU_SERDES_L1_TM_EQ11_FORCE_EQ_OFFS_OFF                     0x1

    * eq dynamic offset correction
    * (OFFSET, MASK, VALUE)      (0XFD405978, 0x00000010U ,0x00000010U)
    */
	PSU_Mask_Write(SERDES_L1_TM_EQ11_OFFSET, 0x00000010U, 0x00000010U);
/*##################################################################### */

    /*
    * Register : L2_TM_EQ11 @ 0XFD409978

    * Force EQ offset correction algo off if not forced on
    *  PSU_SERDES_L2_TM_EQ11_FORCE_EQ_OFFS_OFF                     0x1

    * eq dynamic offset correction
    * (OFFSET, MASK, VALUE)      (0XFD409978, 0x00000010U ,0x00000010U)
    */
	PSU_Mask_Write(SERDES_L2_TM_EQ11_OFFSET, 0x00000010U, 0x00000010U);
/*##################################################################### */

    /*
    * Register : L3_TM_EQ11 @ 0XFD40D978

    * Force EQ offset correction algo off if not forced on
    *  PSU_SERDES_L3_TM_EQ11_FORCE_EQ_OFFS_OFF                     0x1

    * eq dynamic offset correction
    * (OFFSET, MASK, VALUE)      (0XFD40D978, 0x00000010U ,0x00000010U)
    */
	PSU_Mask_Write(SERDES_L3_TM_EQ11_OFFSET, 0x00000010U, 0x00000010U);
/*##################################################################### */

    /*
    * DISABLE ECO FOR PCIE
    */
    /*
    * Register : eco_0 @ 0XFD3D001C

    * For future use
    *  PSU_SIOU_ECO_0_FIELD                                        0x1

    * ECO Register for future use
    * (OFFSET, MASK, VALUE)      (0XFD3D001C, 0xFFFFFFFFU ,0x00000001U)
    */
	PSU_Mask_Write(SIOU_ECO_0_OFFSET, 0xFFFFFFFFU, 0x00000001U);
/*##################################################################### */

    /*
    * GT LANE SETTINGS
    */
    /*
    * Register : ICM_CFG0 @ 0XFD410010

    * Controls UPHY Lane 0 protocol configuration. 0 - PowerDown, 1 - PCIe .0,
    *  2 - Sata0, 3 - USB0, 4 - DP.1, 5 - SGMII0, 6 - Unused, 7 - Unused
    *  PSU_SERDES_ICM_CFG0_L0_ICM_CFG                              1

    * Controls UPHY Lane 1 protocol configuration. 0 - PowerDown, 1 - PCIe.1,
    * 2 - Sata1, 3 - USB0, 4 - DP.0, 5 - SGMII1, 6 - Unused, 7 - Unused
    *  PSU_SERDES_ICM_CFG0_L1_ICM_CFG                              4

    * ICM Configuration Register 0
    * (OFFSET, MASK, VALUE)      (0XFD410010, 0x00000077U ,0x00000041U)
    */
	PSU_Mask_Write(SERDES_ICM_CFG0_OFFSET, 0x00000077U, 0x00000041U);
/*##################################################################### */

    /*
    * Register : ICM_CFG1 @ 0XFD410014

    * Controls UPHY Lane 2 protocol configuration. 0 - PowerDown, 1 - PCIe.1,
    * 2 - Sata0, 3 - USB0, 4 - DP.1, 5 - SGMII2, 6 - Unused, 7 - Unused
    *  PSU_SERDES_ICM_CFG1_L2_ICM_CFG                              3

    * Controls UPHY Lane 3 protocol configuration. 0 - PowerDown, 1 - PCIe.3,
    * 2 - Sata1, 3 - USB1, 4 - DP.0, 5 - SGMII3, 6 - Unused, 7 - Unused
    *  PSU_SERDES_ICM_CFG1_L3_ICM_CFG                              2

    * ICM Configuration Register 1
    * (OFFSET, MASK, VALUE)      (0XFD410014, 0x00000077U ,0x00000023U)
    */
	PSU_Mask_Write(SERDES_ICM_CFG1_OFFSET, 0x00000077U, 0x00000023U);
/*##################################################################### */

    /*
    * CHECKING PLL LOCK
    */
    /*
    * ENABLE SERIAL DATA MUX DEEMPH
    */
    /*
    * Register : L1_TXPMD_TM_45 @ 0XFD404CB4

    * Enable/disable DP post2 path
    *  PSU_SERDES_L1_TXPMD_TM_45_DP_TM_TX_DP_ENABLE_POST2_PATH     0x1

    * Override enable/disable of DP post2 path
    *  PSU_SERDES_L1_TXPMD_TM_45_DP_TM_TX_OVRD_DP_ENABLE_POST2_PATH 0x1

    * Override enable/disable of DP post1 path
    *  PSU_SERDES_L1_TXPMD_TM_45_DP_TM_TX_OVRD_DP_ENABLE_POST1_PATH 0x1

    * Enable/disable DP main path
    *  PSU_SERDES_L1_TXPMD_TM_45_DP_TM_TX_DP_ENABLE_MAIN_PATH      0x1

    * Override enable/disable of DP main path
    *  PSU_SERDES_L1_TXPMD_TM_45_DP_TM_TX_OVRD_DP_ENABLE_MAIN_PATH 0x1

    * Post or pre or main DP path selection
    * (OFFSET, MASK, VALUE)      (0XFD404CB4, 0x00000037U ,0x00000037U)
    */
	PSU_Mask_Write(SERDES_L1_TXPMD_TM_45_OFFSET,
		0x00000037U, 0x00000037U);
/*##################################################################### */

    /*
    * Register : L1_TX_ANA_TM_118 @ 0XFD4041D8

    * Test register force for enabling/disablign TX deemphasis bits <17:0>
    *  PSU_SERDES_L1_TX_ANA_TM_118_FORCE_TX_DEEMPH_17_0            0x1

    * Enable Override of TX deemphasis
    * (OFFSET, MASK, VALUE)      (0XFD4041D8, 0x00000001U ,0x00000001U)
    */
	PSU_Mask_Write(SERDES_L1_TX_ANA_TM_118_OFFSET,
		0x00000001U, 0x00000001U);
/*##################################################################### */

    /*
    * Register : L3_TX_ANA_TM_118 @ 0XFD40C1D8

    * Test register force for enabling/disablign TX deemphasis bits <17:0>
    *  PSU_SERDES_L3_TX_ANA_TM_118_FORCE_TX_DEEMPH_17_0            0x1

    * Enable Override of TX deemphasis
    * (OFFSET, MASK, VALUE)      (0XFD40C1D8, 0x00000001U ,0x00000001U)
    */
	PSU_Mask_Write(SERDES_L3_TX_ANA_TM_118_OFFSET,
		0x00000001U, 0x00000001U);
/*##################################################################### */

    /*
    * CDR AND RX EQUALIZATION SETTINGS
    */
    /*
    * Register : L3_TM_CDR5 @ 0XFD40DC14

    * FPHL FSM accumulate cycles
    *  PSU_SERDES_L3_TM_CDR5_FPHL_FSM_ACC_CYCLES                   0x7

    * FFL Phase0 int gain aka 2ol SD update rate
    *  PSU_SERDES_L3_TM_CDR5_FFL_PH0_INT_GAIN                      0x6

    * Fast phase lock controls -- FSM accumulator cycle control and phase 0 in
    * t gain control.
    * (OFFSET, MASK, VALUE)      (0XFD40DC14, 0x000000FFU ,0x000000E6U)
    */
	PSU_Mask_Write(SERDES_L3_TM_CDR5_OFFSET, 0x000000FFU, 0x000000E6U);
/*##################################################################### */

    /*
    * Register : L3_TM_CDR16 @ 0XFD40DC40

    * FFL Phase0 prop gain aka 1ol SD update rate
    *  PSU_SERDES_L3_TM_CDR16_FFL_PH0_PROP_GAIN                    0xC

    * Fast phase lock controls -- phase 0 prop gain
    * (OFFSET, MASK, VALUE)      (0XFD40DC40, 0x0000001FU ,0x0000000CU)
    */
	PSU_Mask_Write(SERDES_L3_TM_CDR16_OFFSET, 0x0000001FU, 0x0000000CU);
/*##################################################################### */

    /*
    * Register : L3_TM_EQ0 @ 0XFD40D94C

    * EQ stg 2 controls BYPASSED
    *  PSU_SERDES_L3_TM_EQ0_EQ_STG2_CTRL_BYP                       1

    * eq stg1 and stg2 controls
    * (OFFSET, MASK, VALUE)      (0XFD40D94C, 0x00000020U ,0x00000020U)
    */
	PSU_Mask_Write(SERDES_L3_TM_EQ0_OFFSET, 0x00000020U, 0x00000020U);
/*##################################################################### */

    /*
    * Register : L3_TM_EQ1 @ 0XFD40D950

    * EQ STG2 RL PROG
    *  PSU_SERDES_L3_TM_EQ1_EQ_STG2_RL_PROG                        0x2

    * EQ stg 2 preamp mode val
    *  PSU_SERDES_L3_TM_EQ1_EQ_STG2_PREAMP_MODE_VAL                0x1

    * eq stg1 and stg2 controls
    * (OFFSET, MASK, VALUE)      (0XFD40D950, 0x00000007U ,0x00000006U)
    */
	PSU_Mask_Write(SERDES_L3_TM_EQ1_OFFSET, 0x00000007U, 0x00000006U);
/*##################################################################### */

    /*
    * GEM SERDES SETTINGS
    */
    /*
    * ENABLE PRE EMPHAIS AND VOLTAGE SWING
    */
    /*
    * Register : L1_TXPMD_TM_48 @ 0XFD404CC0

    * Margining factor value
    *  PSU_SERDES_L1_TXPMD_TM_48_TM_RESULTANT_MARGINING_FACTOR     0

    * Margining factor
    * (OFFSET, MASK, VALUE)      (0XFD404CC0, 0x0000001FU ,0x00000000U)
    */
	PSU_Mask_Write(SERDES_L1_TXPMD_TM_48_OFFSET,
		0x0000001FU, 0x00000000U);
/*##################################################################### */

    /*
    * Register : L1_TX_ANA_TM_18 @ 0XFD404048

    * pipe_TX_Deemph. 0: -6dB de-emphasis, 1: -3.5dB de-emphasis, 2 : No de-em
    * phasis, Others: reserved
    *  PSU_SERDES_L1_TX_ANA_TM_18_PIPE_TX_DEEMPH_7_0               0

    * Override for PIPE TX de-emphasis
    * (OFFSET, MASK, VALUE)      (0XFD404048, 0x000000FFU ,0x00000000U)
    */
	PSU_Mask_Write(SERDES_L1_TX_ANA_TM_18_OFFSET,
		0x000000FFU, 0x00000000U);
/*##################################################################### */

    /*
    * Register : L3_TX_ANA_TM_18 @ 0XFD40C048

    * pipe_TX_Deemph. 0: -6dB de-emphasis, 1: -3.5dB de-emphasis, 2 : No de-em
    * phasis, Others: reserved
    *  PSU_SERDES_L3_TX_ANA_TM_18_PIPE_TX_DEEMPH_7_0               0x1

    * Override for PIPE TX de-emphasis
    * (OFFSET, MASK, VALUE)      (0XFD40C048, 0x000000FFU ,0x00000001U)
    */
	PSU_Mask_Write(SERDES_L3_TX_ANA_TM_18_OFFSET,
		0x000000FFU, 0x00000001U);
/*##################################################################### */


	return 1;
}
unsigned long psu_resetout_init_data(void)
{
    /*
    * TAKING SERDES PERIPHERAL OUT OF RESET RESET
    */
    /*
    * PUTTING USB0 IN RESET
    */
    /*
    * Register : RST_LPD_TOP @ 0XFF5E023C

    * USB 0 reset for control registers
    *  PSU_CRL_APB_RST_LPD_TOP_USB0_APB_RESET                      0X0

    * Software control register for the LPD block.
    * (OFFSET, MASK, VALUE)      (0XFF5E023C, 0x00000400U ,0x00000000U)
    */
	PSU_Mask_Write(CRL_APB_RST_LPD_TOP_OFFSET, 0x00000400U, 0x00000000U);
/*##################################################################### */

    /*
    * HIBERREST
    */
    /*
    * Register : RST_LPD_TOP @ 0XFF5E023C

    * USB 0 sleep circuit reset
    *  PSU_CRL_APB_RST_LPD_TOP_USB0_HIBERRESET                     0X0

    * USB 0 reset
    *  PSU_CRL_APB_RST_LPD_TOP_USB0_CORERESET                      0X0

    * Software control register for the LPD block.
    * (OFFSET, MASK, VALUE)      (0XFF5E023C, 0x00000140U ,0x00000000U)
    */
	PSU_Mask_Write(CRL_APB_RST_LPD_TOP_OFFSET, 0x00000140U, 0x00000000U);
/*##################################################################### */

    /*
    * PUTTING GEM0 IN RESET
    */
    /*
    * Register : RST_LPD_IOU0 @ 0XFF5E0230

    * GEM 3 reset
    *  PSU_CRL_APB_RST_LPD_IOU0_GEM3_RESET                         0X0

    * Software controlled reset for the GEMs
    * (OFFSET, MASK, VALUE)      (0XFF5E0230, 0x00000008U ,0x00000000U)
    */
	PSU_Mask_Write(CRL_APB_RST_LPD_IOU0_OFFSET,
		0x00000008U, 0x00000000U);
/*##################################################################### */

    /*
    * PUTTING SATA IN RESET
    */
    /*
    * Register : sata_misc_ctrl @ 0XFD3D0100

    * Sata PM clock control select
    *  PSU_SIOU_SATA_MISC_CTRL_SATA_PM_CLK_SEL                     0x3

    * Misc Contorls for SATA.This register may only be modified during bootup
    * (while SATA block is disabled)
    * (OFFSET, MASK, VALUE)      (0XFD3D0100, 0x00000003U ,0x00000003U)
    */
	PSU_Mask_Write(SIOU_SATA_MISC_CTRL_OFFSET, 0x00000003U, 0x00000003U);
/*##################################################################### */

    /*
    * Register : RST_FPD_TOP @ 0XFD1A0100

    * Sata block level reset
    *  PSU_CRF_APB_RST_FPD_TOP_SATA_RESET                          0X0

    * FPD Block level software controlled reset
    * (OFFSET, MASK, VALUE)      (0XFD1A0100, 0x00000002U ,0x00000000U)
    */
	PSU_Mask_Write(CRF_APB_RST_FPD_TOP_OFFSET, 0x00000002U, 0x00000000U);
/*##################################################################### */

    /*
    * PUTTING PCIE CFG AND BRIDGE IN RESET
    */
    /*
    * Register : RST_FPD_TOP @ 0XFD1A0100

    * PCIE config reset
    *  PSU_CRF_APB_RST_FPD_TOP_PCIE_CFG_RESET                      0X0

    * PCIE bridge block level reset (AXI interface)
    *  PSU_CRF_APB_RST_FPD_TOP_PCIE_BRIDGE_RESET                   0X0

    * FPD Block level software controlled reset
    * (OFFSET, MASK, VALUE)      (0XFD1A0100, 0x000C0000U ,0x00000000U)
    */
	PSU_Mask_Write(CRF_APB_RST_FPD_TOP_OFFSET, 0x000C0000U, 0x00000000U);
/*##################################################################### */

    /*
    * PUTTING DP IN RESET
    */
    /*
    * Register : RST_FPD_TOP @ 0XFD1A0100

    * Display Port block level reset (includes DPDMA)
    *  PSU_CRF_APB_RST_FPD_TOP_DP_RESET                            0X0

    * FPD Block level software controlled reset
    * (OFFSET, MASK, VALUE)      (0XFD1A0100, 0x00010000U ,0x00000000U)
    */
	PSU_Mask_Write(CRF_APB_RST_FPD_TOP_OFFSET, 0x00010000U, 0x00000000U);
/*##################################################################### */

    /*
    * Register : DP_PHY_RESET @ 0XFD4A0200

    * Set to '1' to hold the GT in reset. Clear to release.
    *  PSU_DP_DP_PHY_RESET_GT_RESET                                0X0

    * Reset the transmitter PHY.
    * (OFFSET, MASK, VALUE)      (0XFD4A0200, 0x00000002U ,0x00000000U)
    */
	PSU_Mask_Write(DP_DP_PHY_RESET_OFFSET, 0x00000002U, 0x00000000U);
/*##################################################################### */

    /*
    * Register : DP_TX_PHY_POWER_DOWN @ 0XFD4A0238

    * Two bits per lane. When set to 11, moves the GT to power down mode. When
    *  set to 00, GT will be in active state. bits [1:0] - lane0 Bits [3:2] -
    * lane 1
    *  PSU_DP_DP_TX_PHY_POWER_DOWN_POWER_DWN                       0X0

    * Control PHY Power down
    * (OFFSET, MASK, VALUE)      (0XFD4A0238, 0x0000000FU ,0x00000000U)
    */
	PSU_Mask_Write(DP_DP_TX_PHY_POWER_DOWN_OFFSET,
		0x0000000FU, 0x00000000U);
/*##################################################################### */

    /*
    * USB0 GFLADJ
    */
    /*
    * Register : GUSB2PHYCFG @ 0XFE20C200

    * USB 2.0 Turnaround Time (USBTrdTim) Sets the turnaround time in PHY cloc
    * ks. Specifies the response time for a MAC request to the Packet FIFO Con
    * troller (PFC) to fetch data from the DFIFO (SPRAM). The following are th
    * e required values for the minimum SoC bus frequency of 60 MHz. USB turna
    * round time is a critical certification criteria when using long cables a
    * nd five hub levels. The required values for this field: - 4'h5: When the
    *  MAC interface is 16-bit UTMI+. - 4'h9: When the MAC interface is 8-bit
    * UTMI+/ULPI. If SoC bus clock is less than 60 MHz, and USB turnaround tim
    * e is not critical, this field can be set to a larger value. Note: This f
    * ield is valid only in device mode.
    *  PSU_USB3_0_XHCI_GUSB2PHYCFG_USBTRDTIM                       0x9

    * Transceiver Delay: Enables a delay between the assertion of the UTMI/ULP
    * I Transceiver Select signal (for HS) and the assertion of the TxValid si
    * gnal during a HS Chirp. When this bit is set to 1, a delay (of approxima
    * tely 2.5 us) is introduced from the time when the Transceiver Select is
    * set to 2'b00 (HS) to the time the TxValid is driven to 0 for sending the
    *  chirp-K. This delay is required for some UTMI/ULPI PHYs. Note: - If you
    *  enable the hibernation feature when the device core comes out of power-
    * off, you must re-initialize this bit with the appropriate value because
    * the core does not save and restore this bit value during hibernation. -
    * This bit is valid only in device mode.
    *  PSU_USB3_0_XHCI_GUSB2PHYCFG_XCVRDLY                         0x0

    * Enable utmi_sleep_n and utmi_l1_suspend_n (EnblSlpM) The application use
    * s this bit to control utmi_sleep_n and utmi_l1_suspend_n assertion to th
    * e PHY in the L1 state. - 1'b0: utmi_sleep_n and utmi_l1_suspend_n assert
    * ion from the core is not transferred to the external PHY. - 1'b1: utmi_s
    * leep_n and utmi_l1_suspend_n assertion from the core is transferred to t
    * he external PHY. Note: This bit must be set high for Port0 if PHY is use
    * d. Note: In Device mode - Before issuing any device endpoint command whe
    * n operating in 2.0 speeds, disable this bit and enable it after the comm
    * and completes. Without disabling this bit, if a command is issued when t
    * he device is in L1 state and if mac2_clk (utmi_clk/ulpi_clk) is gated of
    * f, the command will not get completed.
    *  PSU_USB3_0_XHCI_GUSB2PHYCFG_ENBLSLPM                        0x0

    * USB 2.0 High-Speed PHY or USB 1.1 Full-Speed Serial Transceiver Select T
    * he application uses this bit to select a high-speed PHY or a full-speed
    * transceiver. - 1'b0: USB 2.0 high-speed UTMI+ or ULPI PHY. This bit is a
    * lways 0, with Write Only access. - 1'b1: USB 1.1 full-speed serial trans
    * ceiver. This bit is always 1, with Write Only access. If both interface
    * types are selected in coreConsultant (that is, parameters' values are no
    * t zero), the application uses this bit to select the active interface is
    *  active, with Read-Write bit access. Note: USB 1.1 full-serial transceiv
    * er is not supported. This bit always reads as 1'b0.
    *  PSU_USB3_0_XHCI_GUSB2PHYCFG_PHYSEL                          0x0

    * Suspend USB2.0 HS/FS/LS PHY (SusPHY) When set, USB2.0 PHY enters Suspend
    *  mode if Suspend conditions are valid. For DRD/OTG configurations, it is
    *  recommended that this bit is set to 0 during coreConsultant configurati
    * on. If it is set to 1, then the application must clear this bit after po
    * wer-on reset. Application needs to set it to 1 after the core initializa
    * tion completes. For all other configurations, this bit can be set to 1 d
    * uring core configuration. Note: - In host mode, on reset, this bit is se
    * t to 1. Software can override this bit after reset. - In device mode, be
    * fore issuing any device endpoint command when operating in 2.0 speeds, d
    * isable this bit and enable it after the command completes. If you issue
    * a command without disabling this bit when the device is in L2 state and
    * if mac2_clk (utmi_clk/ulpi_clk) is gated off, the command will not get c
    * ompleted.
    *  PSU_USB3_0_XHCI_GUSB2PHYCFG_SUSPENDUSB20                    0x1

    * Full-Speed Serial Interface Select (FSIntf) The application uses this bi
    * t to select a unidirectional or bidirectional USB 1.1 full-speed serial
    * transceiver interface. - 1'b0: 6-pin unidirectional full-speed serial in
    * terface. This bit is set to 0 with Read Only access. - 1'b1: 3-pin bidir
    * ectional full-speed serial interface. This bit is set to 0 with Read Onl
    * y access. Note: USB 1.1 full-speed serial interface is not supported. Th
    * is bit always reads as 1'b0.
    *  PSU_USB3_0_XHCI_GUSB2PHYCFG_FSINTF                          0x0

    * ULPI or UTMI+ Select (ULPI_UTMI_Sel) The application uses this bit to se
    * lect a UTMI+ or ULPI Interface. - 1'b0: UTMI+ Interface - 1'b1: ULPI Int
    * erface This bit is writable only if UTMI+ and ULPI is specified for High
    * -Speed PHY Interface(s) in coreConsultant configuration (DWC_USB3_HSPHY_
    * INTERFACE = 3). Otherwise, this bit is read-only and the value depends o
    * n the interface selected through DWC_USB3_HSPHY_INTERFACE.
    *  PSU_USB3_0_XHCI_GUSB2PHYCFG_ULPI_UTMI_SEL                   0x1

    * PHY Interface (PHYIf) If UTMI+ is selected, the application uses this bi
    * t to configure the core to support a UTMI+ PHY with an 8- or 16-bit inte
    * rface. - 1'b0: 8 bits - 1'b1: 16 bits ULPI Mode: 1'b0 Note: - All the en
    * abled 2.0 ports must have the same clock frequency as Port0 clock freque
    * ncy (utmi_clk[0]). - The UTMI 8-bit and 16-bit modes cannot be used toge
    * ther for different ports at the same time (that is, all the ports must b
    * e in 8-bit mode, or all of them must be in 16-bit mode, at a time). - If
    *  any of the USB 2.0 ports is selected as ULPI port for operation, then a
    * ll the USB 2.0 ports must be operating at 60 MHz.
    *  PSU_USB3_0_XHCI_GUSB2PHYCFG_PHYIF                           0x0

    * HS/FS Timeout Calibration (TOutCal) The number of PHY clocks, as indicat
    * ed by the application in this field, is multiplied by a bit-time factor;
    *  this factor is added to the high-speed/full-speed interpacket timeout d
    * uration in the core to account for additional delays introduced by the P
    * HY. This may be required, since the delay introduced by the PHY in gener
    * ating the linestate condition may vary among PHYs. The USB standard time
    * out value for high-speed operation is 736 to 816 (inclusive) bit times.
    * The USB standard timeout value for full-speed operation is 16 to 18 (inc
    * lusive) bit times. The application must program this field based on the
    * speed of connection. The number of bit times added per PHY clock are: Hi
    * gh-speed operation: - One 30-MHz PHY clock = 16 bit times - One 60-MHz P
    * HY clock = 8 bit times Full-speed operation: - One 30-MHz PHY clock = 0.
    * 4 bit times - One 60-MHz PHY clock = 0.2 bit times - One 48-MHz PHY cloc
    * k = 0.25 bit times
    *  PSU_USB3_0_XHCI_GUSB2PHYCFG_TOUTCAL                         0x7

    * ULPI External VBUS Drive (ULPIExtVbusDrv) Selects supply source to drive
    *  5V on VBUS, in the ULPI PHY. - 1'b0: PHY drives VBUS with internal char
    * ge pump (default). - 1'b1: PHY drives VBUS with an external supply. (Onl
    * y when RTL parameter DWC_USB3_HSPHY_INTERFACE = 2 or 3)
    *  PSU_USB3_0_XHCI_GUSB2PHYCFG_ULPIEXTVBUSDRV                  0x1

    * Global USB2 PHY Configuration Register The application must program this
    *  register before starting any transactions on either the SoC bus or the
    * USB. In Device-only configurations, only one register is needed. In Host
    *  mode, per-port registers are implemented.
    * (OFFSET, MASK, VALUE)      (0XFE20C200, 0x00023FFFU ,0x00022457U)
    */
	PSU_Mask_Write(USB3_0_XHCI_GUSB2PHYCFG_OFFSET,
		0x00023FFFU, 0x00022457U);
/*##################################################################### */

    /*
    * Register : GFLADJ @ 0XFE20C630

    * This field indicates the frame length adjustment to be applied when SOF/
    * ITP counter is running on the ref_clk. This register value is used to ad
    * just the ITP interval when GCTL[SOFITPSYNC] is set to '1'; SOF and ITP i
    * nterval when GLADJ.GFLADJ_REFCLK_LPM_SEL is set to '1'. This field must
    * be programmed to a non-zero value only if GFLADJ_REFCLK_LPM_SEL is set t
    * o '1' or GCTL.SOFITPSYNC is set to '1'. The value is derived as follows:
    *  FLADJ_REF_CLK_FLADJ=((125000/ref_clk_period_integer)-(125000/ref_clk_pe
    * riod)) * ref_clk_period where - the ref_clk_period_integer is the intege
    * r value of the ref_clk period got by truncating the decimal (fractional)
    *  value that is programmed in the GUCTL.REF_CLK_PERIOD field. - the ref_c
    * lk_period is the ref_clk period including the fractional value. Examples
    * : If the ref_clk is 24 MHz then - GUCTL.REF_CLK_PERIOD = 41 - GFLADJ.GLA
    * DJ_REFCLK_FLADJ = ((125000/41)-(125000/41.6666))*41.6666 = 2032 (ignorin
    * g the fractional value) If the ref_clk is 48 MHz then - GUCTL.REF_CLK_PE
    * RIOD = 20 - GFLADJ.GLADJ_REFCLK_FLADJ = ((125000/20)-(125000/20.8333))*2
    * 0.8333 = 5208 (ignoring the fractional value)
    *  PSU_USB3_0_XHCI_GFLADJ_GFLADJ_REFCLK_FLADJ                  0x0

    * Global Frame Length Adjustment Register This register provides options f
    * or the software to control the core behavior with respect to SOF (Start
    * of Frame) and ITP (Isochronous Timestamp Packet) timers and frame timer
    * functionality. It provides an option to override the fladj_30mhz_reg sid
    * eband signal. In addition, it enables running SOF or ITP frame timer cou
    * nters completely from the ref_clk. This facilitates hardware LPM in host
    *  mode with the SOF or ITP counters being run from the ref_clk signal.
    * (OFFSET, MASK, VALUE)      (0XFE20C630, 0x003FFF00U ,0x00000000U)
    */
	PSU_Mask_Write(USB3_0_XHCI_GFLADJ_OFFSET, 0x003FFF00U, 0x00000000U);
/*##################################################################### */

    /*
    * Register : GUCTL1 @ 0XFE20C11C

    * When this bit is set to '0', termsel, xcvrsel will become 0 during end o
    * f resume while the opmode will become 0 once controller completes end of
    *  resume and enters U0 state (2 separate commandswill be issued). When th
    * is bit is set to '1', all the termsel, xcvrsel, opmode becomes 0 during
    * end of resume itself (only 1 command will be issued)
    *  PSU_USB3_0_XHCI_GUCTL1_RESUME_TERMSEL_XCVRSEL_UNIFY         0x1

    * Reserved
    *  PSU_USB3_0_XHCI_GUCTL1_RESERVED_9                           0x1

    * Global User Control Register 1
    * (OFFSET, MASK, VALUE)      (0XFE20C11C, 0x00000600U ,0x00000600U)
    */
	PSU_Mask_Write(USB3_0_XHCI_GUCTL1_OFFSET, 0x00000600U, 0x00000600U);
/*##################################################################### */

    /*
    * Register : GUCTL @ 0XFE20C12C

    * Host IN Auto Retry (USBHstInAutoRetryEn) When set, this field enables th
    * e Auto Retry feature. For IN transfers (non-isochronous) that encounter
    * data packets with CRC errors or internal overrun scenarios, the auto ret
    * ry feature causes the Host core to reply to the device with a non-termin
    * ating retry ACK (that is, an ACK transaction packet with Retry = 1 and N
    * umP != 0). If the Auto Retry feature is disabled (default), the core wil
    * l respond with a terminating retry ACK (that is, an ACK transaction pack
    * et with Retry = 1 and NumP = 0). - 1'b0: Auto Retry Disabled - 1'b1: Aut
    * o Retry Enabled Note: This bit is also applicable to the device mode.
    *  PSU_USB3_0_XHCI_GUCTL_USBHSTINAUTORETRYEN                   0x1

    * Global User Control Register: This register provides a few options for t
    * he software to control the core behavior in the Host mode. Most of the o
    * ptions are used to improve host inter-operability with different devices
    * .
    * (OFFSET, MASK, VALUE)      (0XFE20C12C, 0x00004000U ,0x00004000U)
    */
	PSU_Mask_Write(USB3_0_XHCI_GUCTL_OFFSET, 0x00004000U, 0x00004000U);
/*##################################################################### */

    /*
    * UPDATING TWO PCIE REGISTERS DEFAULT VALUES, AS THESE REGISTERS HAVE INCO
    * RRECT RESET VALUES IN SILICON.
    */
    /*
    * Register : ATTR_25 @ 0XFD480064

    * If TRUE Completion Timeout Disable is supported. This is required to be
    * TRUE for Endpoint and either setting allowed for Root ports. Drives Devi
    * ce Capability 2 [4]; EP=0x0001; RP=0x0001
    *  PSU_PCIE_ATTRIB_ATTR_25_ATTR_CPL_TIMEOUT_DISABLE_SUPPORTED  0X1

    * ATTR_25
    * (OFFSET, MASK, VALUE)      (0XFD480064, 0x00000200U ,0x00000200U)
    */
	PSU_Mask_Write(PCIE_ATTRIB_ATTR_25_OFFSET, 0x00000200U, 0x00000200U);
/*##################################################################### */

    /*
    * PCIE SETTINGS
    */
    /*
    * Register : ATTR_7 @ 0XFD48001C

    * Specifies mask/settings for Base Address Register (BAR) 0. If BAR is not
    *  to be implemented, set to 32'h00000000. Bits are defined as follows: Me
    * mory Space BAR [0] = Mem Space Indicator (set to 0) [2:1] = Type field (
    * 10 for 64-bit, 00 for 32-bit) [3] = Prefetchable (0 or 1) [31:4] = Mask
    * for writable bits of BAR; if 32-bit BAR, set uppermost 31:n bits to 1, w
    * here 2^n=memory aperture size in bytes. If 64-bit BAR, set uppermost 63:
    * n bits of \'7bBAR1,BAR0\'7d to 1. IO Space BAR 0] = IO Space Indicator (
    * set to 1) [1] = Reserved (set to 0) [31:2] = Mask for writable bits of B
    * AR; set uppermost 31:n bits to 1, where 2^n=i/o aperture size in bytes.;
    *  EP=0x0004; RP=0x0000
    *  PSU_PCIE_ATTRIB_ATTR_7_ATTR_BAR0                            0x0

    * ATTR_7
    * (OFFSET, MASK, VALUE)      (0XFD48001C, 0x0000FFFFU ,0x00000000U)
    */
	PSU_Mask_Write(PCIE_ATTRIB_ATTR_7_OFFSET, 0x0000FFFFU, 0x00000000U);
/*##################################################################### */

    /*
    * Register : ATTR_8 @ 0XFD480020

    * Specifies mask/settings for Base Address Register (BAR) 0. If BAR is not
    *  to be implemented, set to 32'h00000000. Bits are defined as follows: Me
    * mory Space BAR [0] = Mem Space Indicator (set to 0) [2:1] = Type field (
    * 10 for 64-bit, 00 for 32-bit) [3] = Prefetchable (0 or 1) [31:4] = Mask
    * for writable bits of BAR; if 32-bit BAR, set uppermost 31:n bits to 1, w
    * here 2^n=memory aperture size in bytes. If 64-bit BAR, set uppermost 63:
    * n bits of \'7bBAR1,BAR0\'7d to 1. IO Space BAR 0] = IO Space Indicator (
    * set to 1) [1] = Reserved (set to 0) [31:2] = Mask for writable bits of B
    * AR; set uppermost 31:n bits to 1, where 2^n=i/o aperture size in bytes.;
    *  EP=0xFFF0; RP=0x0000
    *  PSU_PCIE_ATTRIB_ATTR_8_ATTR_BAR0                            0x0

    * ATTR_8
    * (OFFSET, MASK, VALUE)      (0XFD480020, 0x0000FFFFU ,0x00000000U)
    */
	PSU_Mask_Write(PCIE_ATTRIB_ATTR_8_OFFSET, 0x0000FFFFU, 0x00000000U);
/*##################################################################### */

    /*
    * Register : ATTR_9 @ 0XFD480024

    * Specifies mask/settings for Base Address Register (BAR) 1 if BAR0 is a 3
    * 2-bit BAR, or the upper bits of \'7bBAR1,BAR0\'7d if BAR0 is a 64-bit BA
    * R. If BAR is not to be implemented, set to 32'h00000000. See BAR0 descri
    * ption if this functions as the upper bits of a 64-bit BAR. Bits are defi
    * ned as follows: Memory Space BAR (not upper bits of BAR0) [0] = Mem Spac
    * e Indicator (set to 0) [2:1] = Type field (10 for 64-bit, 00 for 32-bit)
    *  [3] = Prefetchable (0 or 1) [31:4] = Mask for writable bits of BAR; if
    * 32-bit BAR, set uppermost 31:n bits to 1, where 2^n=memory aperture size
    *  in bytes. If 64-bit BAR, set uppermost 63:n bits of \'7bBAR2,BAR1\'7d t
    * o 1. IO Space BAR 0] = IO Space Indicator (set to 1) [1] = Reserved (set
    *  to 0) [31:2] = Mask for writable bits of BAR; set uppermost 31:n bits t
    * o 1, where 2^n=i/o aperture size in bytes.; EP=0xFFFF; RP=0x0000
    *  PSU_PCIE_ATTRIB_ATTR_9_ATTR_BAR1                            0x0

    * ATTR_9
    * (OFFSET, MASK, VALUE)      (0XFD480024, 0x0000FFFFU ,0x00000000U)
    */
	PSU_Mask_Write(PCIE_ATTRIB_ATTR_9_OFFSET, 0x0000FFFFU, 0x00000000U);
/*##################################################################### */

    /*
    * Register : ATTR_10 @ 0XFD480028

    * Specifies mask/settings for Base Address Register (BAR) 1 if BAR0 is a 3
    * 2-bit BAR, or the upper bits of \'7bBAR1,BAR0\'7d if BAR0 is a 64-bit BA
    * R. If BAR is not to be implemented, set to 32'h00000000. See BAR0 descri
    * ption if this functions as the upper bits of a 64-bit BAR. Bits are defi
    * ned as follows: Memory Space BAR (not upper bits of BAR0) [0] = Mem Spac
    * e Indicator (set to 0) [2:1] = Type field (10 for 64-bit, 00 for 32-bit)
    *  [3] = Prefetchable (0 or 1) [31:4] = Mask for writable bits of BAR; if
    * 32-bit BAR, set uppermost 31:n bits to 1, where 2^n=memory aperture size
    *  in bytes. If 64-bit BAR, set uppermost 63:n bits of \'7bBAR2,BAR1\'7d t
    * o 1. IO Space BAR 0] = IO Space Indicator (set to 1) [1] = Reserved (set
    *  to 0) [31:2] = Mask for writable bits of BAR; set uppermost 31:n bits t
    * o 1, where 2^n=i/o aperture size in bytes.; EP=0xFFFF; RP=0x0000
    *  PSU_PCIE_ATTRIB_ATTR_10_ATTR_BAR1                           0x0

    * ATTR_10
    * (OFFSET, MASK, VALUE)      (0XFD480028, 0x0000FFFFU ,0x00000000U)
    */
	PSU_Mask_Write(PCIE_ATTRIB_ATTR_10_OFFSET, 0x0000FFFFU, 0x00000000U);
/*##################################################################### */

    /*
    * Register : ATTR_11 @ 0XFD48002C

    * For an endpoint, specifies mask/settings for Base Address Register (BAR)
    *  2 if BAR1 is a 32-bit BAR, or the upper bits of \'7bBAR2,BAR1\'7d if BA
    * R1 is the lower part of a 64-bit BAR. If BAR is not to be implemented, s
    * et to 32'h00000000. See BAR1 description if this functions as the upper
    * bits of a 64-bit BAR. For a switch or root: This must be set to 00FF_FFF
    * F. For an endpoint, bits are defined as follows: Memory Space BAR (not u
    * pper bits of BAR1) [0] = Mem Space Indicator (set to 0) [2:1] = Type fie
    * ld (10 for 64-bit, 00 for 32-bit) [3] = Prefetchable (0 or 1) [31:4] = M
    * ask for writable bits of BAR; if 32-bit BAR, set uppermost 31:n bits to
    * 1, where 2^n=memory aperture size in bytes. If 64-bit BAR, set uppermost
    *  63:n bits of \'7bBAR3,BAR2\'7d to 1. IO Space BAR 0] = IO Space Indicat
    * or (set to 1) [1] = Reserved (set to 0) [31:2] = Mask for writable bits
    * of BAR; set uppermost 31:n bits to 1, where 2^n=i/o aperture size in byt
    * es.; EP=0x0004; RP=0xFFFF
    *  PSU_PCIE_ATTRIB_ATTR_11_ATTR_BAR2                           0xFFFF

    * ATTR_11
    * (OFFSET, MASK, VALUE)      (0XFD48002C, 0x0000FFFFU ,0x0000FFFFU)
    */
	PSU_Mask_Write(PCIE_ATTRIB_ATTR_11_OFFSET, 0x0000FFFFU, 0x0000FFFFU);
/*##################################################################### */

    /*
    * Register : ATTR_12 @ 0XFD480030

    * For an endpoint, specifies mask/settings for Base Address Register (BAR)
    *  2 if BAR1 is a 32-bit BAR, or the upper bits of \'7bBAR2,BAR1\'7d if BA
    * R1 is the lower part of a 64-bit BAR. If BAR is not to be implemented, s
    * et to 32'h00000000. See BAR1 description if this functions as the upper
    * bits of a 64-bit BAR. For a switch or root: This must be set to 00FF_FFF
    * F. For an endpoint, bits are defined as follows: Memory Space BAR (not u
    * pper bits of BAR1) [0] = Mem Space Indicator (set to 0) [2:1] = Type fie
    * ld (10 for 64-bit, 00 for 32-bit) [3] = Prefetchable (0 or 1) [31:4] = M
    * ask for writable bits of BAR; if 32-bit BAR, set uppermost 31:n bits to
    * 1, where 2^n=memory aperture size in bytes. If 64-bit BAR, set uppermost
    *  63:n bits of \'7bBAR3,BAR2\'7d to 1. IO Space BAR 0] = IO Space Indicat
    * or (set to 1) [1] = Reserved (set to 0) [31:2] = Mask for writable bits
    * of BAR; set uppermost 31:n bits to 1, where 2^n=i/o aperture size in byt
    * es.; EP=0xFFF0; RP=0x00FF
    *  PSU_PCIE_ATTRIB_ATTR_12_ATTR_BAR2                           0xFF

    * ATTR_12
    * (OFFSET, MASK, VALUE)      (0XFD480030, 0x0000FFFFU ,0x000000FFU)
    */
	PSU_Mask_Write(PCIE_ATTRIB_ATTR_12_OFFSET, 0x0000FFFFU, 0x000000FFU);
/*##################################################################### */

    /*
    * Register : ATTR_13 @ 0XFD480034

    * For an endpoint, specifies mask/settings for Base Address Register (BAR)
    *  3 if BAR2 is a 32-bit BAR, or the upper bits of \'7bBAR3,BAR2\'7d if BA
    * R2 is the lower part of a 64-bit BAR. If BAR is not to be implemented, s
    * et to 32'h00000000. See BAR2 description if this functions as the upper
    * bits of a 64-bit BAR. For a switch or root, this must be set to: FFFF_00
    * 00 = IO Limit/Base Registers not implemented FFFF_F0F0 = IO Limit/Base R
    * egisters use 16-bit decode FFFF_F1F1 = IO Limit/Base Registers use 32-bi
    * t decode For an endpoint, bits are defined as follows: Memory Space BAR
    * (not upper bits of BAR2) [0] = Mem Space Indicator (set to 0) [2:1] = Ty
    * pe field (10 for 64-bit, 00 for 32-bit) [3] = Prefetchable (0 or 1) [31:
    * 4] = Mask for writable bits of BAR; if 32-bit BAR, set uppermost 31:n bi
    * ts to 1, where 2^n=memory aperture size in bytes. If 64-bit BAR, set upp
    * ermost 63:n bits of \'7bBAR4,BAR3\'7d to 1. IO Space BAR 0] = IO Space I
    * ndicator (set to 1) [1] = Reserved (set to 0) [31:2] = Mask for writable
    *  bits of BAR; set uppermost 31:n bits to 1, where 2^n=i/o aperture size
    * in bytes.; EP=0xFFFF; RP=0x0000
    *  PSU_PCIE_ATTRIB_ATTR_13_ATTR_BAR3                           0x0

    * ATTR_13
    * (OFFSET, MASK, VALUE)      (0XFD480034, 0x0000FFFFU ,0x00000000U)
    */
	PSU_Mask_Write(PCIE_ATTRIB_ATTR_13_OFFSET, 0x0000FFFFU, 0x00000000U);
/*##################################################################### */

    /*
    * Register : ATTR_14 @ 0XFD480038

    * For an endpoint, specifies mask/settings for Base Address Register (BAR)
    *  3 if BAR2 is a 32-bit BAR, or the upper bits of \'7bBAR3,BAR2\'7d if BA
    * R2 is the lower part of a 64-bit BAR. If BAR is not to be implemented, s
    * et to 32'h00000000. See BAR2 description if this functions as the upper
    * bits of a 64-bit BAR. For a switch or root, this must be set to: FFFF_00
    * 00 = IO Limit/Base Registers not implemented FFFF_F0F0 = IO Limit/Base R
    * egisters use 16-bit decode FFFF_F1F1 = IO Limit/Base Registers use 32-bi
    * t decode For an endpoint, bits are defined as follows: Memory Space BAR
    * (not upper bits of BAR2) [0] = Mem Space Indicator (set to 0) [2:1] = Ty
    * pe field (10 for 64-bit, 00 for 32-bit) [3] = Prefetchable (0 or 1) [31:
    * 4] = Mask for writable bits of BAR; if 32-bit BAR, set uppermost 31:n bi
    * ts to 1, where 2^n=memory aperture size in bytes. If 64-bit BAR, set upp
    * ermost 63:n bits of \'7bBAR4,BAR3\'7d to 1. IO Space BAR 0] = IO Space I
    * ndicator (set to 1) [1] = Reserved (set to 0) [31:2] = Mask for writable
    *  bits of BAR; set uppermost 31:n bits to 1, where 2^n=i/o aperture size
    * in bytes.; EP=0xFFFF; RP=0xFFFF
    *  PSU_PCIE_ATTRIB_ATTR_14_ATTR_BAR3                           0xFFFF

    * ATTR_14
    * (OFFSET, MASK, VALUE)      (0XFD480038, 0x0000FFFFU ,0x0000FFFFU)
    */
	PSU_Mask_Write(PCIE_ATTRIB_ATTR_14_OFFSET, 0x0000FFFFU, 0x0000FFFFU);
/*##################################################################### */

    /*
    * Register : ATTR_15 @ 0XFD48003C

    * For an endpoint, specifies mask/settings for Base Address Register (BAR)
    *  4 if BAR3 is a 32-bit BAR, or the upper bits of \'7bBAR4,BAR3\'7d if BA
    * R3 is the lower part of a 64-bit BAR. If BAR is not to be implemented, s
    * et to 32'h00000000. See BAR3 description if this functions as the upper
    * bits of a 64-bit BAR. For a switch or root: This must be set to FFF0_FFF
    * 0. For an endpoint, bits are defined as follows: Memory Space BAR (not u
    * pper bits of BAR3) [0] = Mem Space Indicator (set to 0) [2:1] = Type fie
    * ld (10 for 64-bit, 00 for 32-bit) [3] = Prefetchable (0 or 1) [31:4] = M
    * ask for writable bits of BAR; if 32-bit BAR, set uppermost 31:n bits to
    * 1, where 2^n=memory aperture size in bytes. If 64-bit BAR, set uppermost
    *  63:n bits of \'7bBAR5,BAR4\'7d to 1. IO Space BAR 0] = IO Space Indicat
    * or (set to 1) [1] = Reserved (set to 0) [31:2] = Mask for writable bits
    * of BAR; set uppermost 31:n bits to 1, where 2^n=i/o aperture size in byt
    * es.; EP=0x0004; RP=0xFFF0
    *  PSU_PCIE_ATTRIB_ATTR_15_ATTR_BAR4                           0xFFF0

    * ATTR_15
    * (OFFSET, MASK, VALUE)      (0XFD48003C, 0x0000FFFFU ,0x0000FFF0U)
    */
	PSU_Mask_Write(PCIE_ATTRIB_ATTR_15_OFFSET, 0x0000FFFFU, 0x0000FFF0U);
/*##################################################################### */

    /*
    * Register : ATTR_16 @ 0XFD480040

    * For an endpoint, specifies mask/settings for Base Address Register (BAR)
    *  4 if BAR3 is a 32-bit BAR, or the upper bits of \'7bBAR4,BAR3\'7d if BA
    * R3 is the lower part of a 64-bit BAR. If BAR is not to be implemented, s
    * et to 32'h00000000. See BAR3 description if this functions as the upper
    * bits of a 64-bit BAR. For a switch or root: This must be set to FFF0_FFF
    * 0. For an endpoint, bits are defined as follows: Memory Space BAR (not u
    * pper bits of BAR3) [0] = Mem Space Indicator (set to 0) [2:1] = Type fie
    * ld (10 for 64-bit, 00 for 32-bit) [3] = Prefetchable (0 or 1) [31:4] = M
    * ask for writable bits of BAR; if 32-bit BAR, set uppermost 31:n bits to
    * 1, where 2^n=memory aperture size in bytes. If 64-bit BAR, set uppermost
    *  63:n bits of \'7bBAR5,BAR4\'7d to 1. IO Space BAR 0] = IO Space Indicat
    * or (set to 1) [1] = Reserved (set to 0) [31:2] = Mask for writable bits
    * of BAR; set uppermost 31:n bits to 1, where 2^n=i/o aperture size in byt
    * es.; EP=0xFFF0; RP=0xFFF0
    *  PSU_PCIE_ATTRIB_ATTR_16_ATTR_BAR4                           0xFFF0

    * ATTR_16
    * (OFFSET, MASK, VALUE)      (0XFD480040, 0x0000FFFFU ,0x0000FFF0U)
    */
	PSU_Mask_Write(PCIE_ATTRIB_ATTR_16_OFFSET, 0x0000FFFFU, 0x0000FFF0U);
/*##################################################################### */

    /*
    * Register : ATTR_17 @ 0XFD480044

    * For an endpoint, specifies mask/settings for Base Address Register (BAR)
    *  5 if BAR4 is a 32-bit BAR, or the upper bits of \'7bBAR5,BAR4\'7d if BA
    * R4 is the lower part of a 64-bit BAR. If BAR is not to be implemented, s
    * et to 32'h00000000. See BAR4 description if this functions as the upper
    * bits of a 64-bit BAR. For a switch or root, this must be set to: 0000_00
    * 00 = Prefetchable Memory Limit/Base Registers not implemented FFF0_FFF0
    * = 32-bit Prefetchable Memory Limit/Base implemented FFF1_FFF1 = 64-bit P
    * refetchable Memory Limit/Base implemented For an endpoint, bits are defi
    * ned as follows: Memory Space BAR (not upper bits of BAR4) [0] = Mem Spac
    * e Indicator (set to 0) [2:1] = Type field (00 for 32-bit; BAR5 cannot be
    *  lower part of a 64-bit BAR) [3] = Prefetchable (0 or 1) [31:4] = Mask f
    * or writable bits of BAR; set uppermost 31:n bits to 1, where 2^n=memory
    * aperture size in bytes. IO Space BAR 0] = IO Space Indicator (set to 1)
    * [1] = Reserved (set to 0) [31:2] = Mask for writable bits of BAR; set up
    * permost 31:n bits to 1, where 2^n=i/o aperture size in bytes.; EP=0xFFFF
    * ; RP=0xFFF1
    *  PSU_PCIE_ATTRIB_ATTR_17_ATTR_BAR5                           0xFFF1

    * ATTR_17
    * (OFFSET, MASK, VALUE)      (0XFD480044, 0x0000FFFFU ,0x0000FFF1U)
    */
	PSU_Mask_Write(PCIE_ATTRIB_ATTR_17_OFFSET, 0x0000FFFFU, 0x0000FFF1U);
/*##################################################################### */

    /*
    * Register : ATTR_18 @ 0XFD480048

    * For an endpoint, specifies mask/settings for Base Address Register (BAR)
    *  5 if BAR4 is a 32-bit BAR, or the upper bits of \'7bBAR5,BAR4\'7d if BA
    * R4 is the lower part of a 64-bit BAR. If BAR is not to be implemented, s
    * et to 32'h00000000. See BAR4 description if this functions as the upper
    * bits of a 64-bit BAR. For a switch or root, this must be set to: 0000_00
    * 00 = Prefetchable Memory Limit/Base Registers not implemented FFF0_FFF0
    * = 32-bit Prefetchable Memory Limit/Base implemented FFF1_FFF1 = 64-bit P
    * refetchable Memory Limit/Base implemented For an endpoint, bits are defi
    * ned as follows: Memory Space BAR (not upper bits of BAR4) [0] = Mem Spac
    * e Indicator (set to 0) [2:1] = Type field (00 for 32-bit; BAR5 cannot be
    *  lower part of a 64-bit BAR) [3] = Prefetchable (0 or 1) [31:4] = Mask f
    * or writable bits of BAR; set uppermost 31:n bits to 1, where 2^n=memory
    * aperture size in bytes. IO Space BAR 0] = IO Space Indicator (set to 1)
    * [1] = Reserved (set to 0) [31:2] = Mask for writable bits of BAR; set up
    * permost 31:n bits to 1, where 2^n=i/o aperture size in bytes.; EP=0xFFFF
    * ; RP=0xFFF1
    *  PSU_PCIE_ATTRIB_ATTR_18_ATTR_BAR5                           0xFFF1

    * ATTR_18
    * (OFFSET, MASK, VALUE)      (0XFD480048, 0x0000FFFFU ,0x0000FFF1U)
    */
	PSU_Mask_Write(PCIE_ATTRIB_ATTR_18_OFFSET, 0x0000FFFFU, 0x0000FFF1U);
/*##################################################################### */

    /*
    * Register : ATTR_27 @ 0XFD48006C

    * Specifies maximum payload supported. Valid settings are: 0- 128 bytes, 1
    * - 256 bytes, 2- 512 bytes, 3- 1024 bytes. Transferred to the Device Capa
    * bilities register. The values: 4-2048 bytes, 5- 4096 bytes are not suppo
    * rted; EP=0x0001; RP=0x0001
    *  PSU_PCIE_ATTRIB_ATTR_27_ATTR_DEV_CAP_MAX_PAYLOAD_SUPPORTED  1

    * Endpoint L1 Acceptable Latency. Records the latency that the endpoint ca
    * n withstand on transitions from L1 state to L0 (if L1 state supported).
    * Valid settings are: 0h less than 1us, 1h 1 to 2us, 2h 2 to 4us, 3h 4 to
    * 8us, 4h 8 to 16us, 5h 16 to 32us, 6h 32 to 64us, 7h more than 64us. For
    * Endpoints only. Must be 0h for other devices.; EP=0x0007; RP=0x0000
    *  PSU_PCIE_ATTRIB_ATTR_27_ATTR_DEV_CAP_ENDPOINT_L1_LATENCY    0x0

    * ATTR_27
    * (OFFSET, MASK, VALUE)      (0XFD48006C, 0x00000738U ,0x00000100U)
    */
	PSU_Mask_Write(PCIE_ATTRIB_ATTR_27_OFFSET, 0x00000738U, 0x00000100U);
/*##################################################################### */

    /*
    * Register : ATTR_50 @ 0XFD4800C8

    * Identifies the type of device/port as follows: 0000b PCI Express Endpoin
    * t device, 0001b Legacy PCI Express Endpoint device, 0100b Root Port of P
    * CI Express Root Complex, 0101b Upstream Port of PCI Express Switch, 0110
    * b Downstream Port of PCI Express Switch, 0111b PCIE Express to PCI/PCI-X
    *  Bridge, 1000b PCI/PCI-X to PCI Express Bridge. Transferred to PCI Expre
    * ss Capabilities register. Must be consistent with IS_SWITCH and UPSTREAM
    * _FACING settings.; EP=0x0000; RP=0x0004
    *  PSU_PCIE_ATTRIB_ATTR_50_ATTR_PCIE_CAP_DEVICE_PORT_TYPE      4

    * PCIe Capability's Next Capability Offset pointer to the next item in the
    *  capabilities list, or 00h if this is the final capability.; EP=0x009C;
    * RP=0x0000
    *  PSU_PCIE_ATTRIB_ATTR_50_ATTR_PCIE_CAP_NEXTPTR               0

    * ATTR_50
    * (OFFSET, MASK, VALUE)      (0XFD4800C8, 0x0000FFF0U ,0x00000040U)
    */
	PSU_Mask_Write(PCIE_ATTRIB_ATTR_50_OFFSET, 0x0000FFF0U, 0x00000040U);
/*##################################################################### */

    /*
    * Register : ATTR_105 @ 0XFD4801A4

    * Number of credits that should be advertised for Completion data received
    *  on Virtual Channel 0. The bytes advertised must be less than or equal t
    * o the bram bytes available. See VC0_RX_RAM_LIMIT; EP=0x0172; RP=0x00CD
    *  PSU_PCIE_ATTRIB_ATTR_105_ATTR_VC0_TOTAL_CREDITS_CD          0xCD

    * ATTR_105
    * (OFFSET, MASK, VALUE)      (0XFD4801A4, 0x000007FFU ,0x000000CDU)
    */
	PSU_Mask_Write(PCIE_ATTRIB_ATTR_105_OFFSET,
		0x000007FFU, 0x000000CDU);
/*##################################################################### */

    /*
    * Register : ATTR_106 @ 0XFD4801A8

    * Number of credits that should be advertised for Completion headers recei
    * ved on Virtual Channel 0. The sum of the posted, non posted, and complet
    * ion header credits must be <= 80; EP=0x0048; RP=0x0024
    *  PSU_PCIE_ATTRIB_ATTR_106_ATTR_VC0_TOTAL_CREDITS_CH          0x24

    * Number of credits that should be advertised for Non-Posted headers recei
    * ved on Virtual Channel 0. The number of non posted data credits advertis
    * ed by the block is equal to the number of non posted header credits. The
    *  sum of the posted, non posted, and completion header credits must be <=
    *  80; EP=0x0004; RP=0x000C
    *  PSU_PCIE_ATTRIB_ATTR_106_ATTR_VC0_TOTAL_CREDITS_NPH         0xC

    * ATTR_106
    * (OFFSET, MASK, VALUE)      (0XFD4801A8, 0x00003FFFU ,0x00000624U)
    */
	PSU_Mask_Write(PCIE_ATTRIB_ATTR_106_OFFSET,
		0x00003FFFU, 0x00000624U);
/*##################################################################### */

    /*
    * Register : ATTR_107 @ 0XFD4801AC

    * Number of credits that should be advertised for Non-Posted data received
    *  on Virtual Channel 0. The number of non posted data credits advertised
    * by the block is equal to two times the number of non posted header credi
    * ts if atomic operations are supported or is equal to the number of non p
    * osted header credits if atomic operations are not supported. The bytes a
    * dvertised must be less than or equal to the bram bytes available. See VC
    * 0_RX_RAM_LIMIT; EP=0x0008; RP=0x0018
    *  PSU_PCIE_ATTRIB_ATTR_107_ATTR_VC0_TOTAL_CREDITS_NPD         0x18

    * ATTR_107
    * (OFFSET, MASK, VALUE)      (0XFD4801AC, 0x000007FFU ,0x00000018U)
    */
	PSU_Mask_Write(PCIE_ATTRIB_ATTR_107_OFFSET,
		0x000007FFU, 0x00000018U);
/*##################################################################### */

    /*
    * Register : ATTR_108 @ 0XFD4801B0

    * Number of credits that should be advertised for Posted data received on
    * Virtual Channel 0. The bytes advertised must be less than or equal to th
    * e bram bytes available. See VC0_RX_RAM_LIMIT; EP=0x0020; RP=0x00B5
    *  PSU_PCIE_ATTRIB_ATTR_108_ATTR_VC0_TOTAL_CREDITS_PD          0xB5

    * ATTR_108
    * (OFFSET, MASK, VALUE)      (0XFD4801B0, 0x000007FFU ,0x000000B5U)
    */
	PSU_Mask_Write(PCIE_ATTRIB_ATTR_108_OFFSET,
		0x000007FFU, 0x000000B5U);
/*##################################################################### */

    /*
    * Register : ATTR_109 @ 0XFD4801B4

    * Not currently in use. Invert ECRC generated by block when trn_tecrc_gen_
    * n and trn_terrfwd_n are asserted.; EP=0x0000; RP=0x0000
    *  PSU_PCIE_ATTRIB_ATTR_109_ATTR_TECRC_EP_INV                  0x0

    * Enables td bit clear and ECRC trim on received TLP's FALSE == don't trim
    *  TRUE == trim.; EP=0x0001; RP=0x0001
    *  PSU_PCIE_ATTRIB_ATTR_109_ATTR_RECRC_CHK_TRIM                0x1

    * Enables ECRC check on received TLP's 0 == don't check 1 == always check
    * 3 == check if enabled by ECRC check enable bit of AER cap structure; EP=
    * 0x0003; RP=0x0003
    *  PSU_PCIE_ATTRIB_ATTR_109_ATTR_RECRC_CHK                     0x3

    * Index of last packet buffer used by TX TLM (i.e. number of buffers - 1).
    *  Calculated from max payload size supported and the number of brams conf
    * igured for transmit; EP=0x001C; RP=0x001C
    *  PSU_PCIE_ATTRIB_ATTR_109_ATTR_VC0_TX_LASTPACKET             0x1c

    * Number of credits that should be advertised for Posted headers received
    * on Virtual Channel 0. The sum of the posted, non posted, and completion
    * header credits must be <= 80; EP=0x0004; RP=0x0020
    *  PSU_PCIE_ATTRIB_ATTR_109_ATTR_VC0_TOTAL_CREDITS_PH          0x20

    * ATTR_109
    * (OFFSET, MASK, VALUE)      (0XFD4801B4, 0x0000FFFFU ,0x00007E20U)
    */
	PSU_Mask_Write(PCIE_ATTRIB_ATTR_109_OFFSET,
		0x0000FFFFU, 0x00007E20U);
/*##################################################################### */

    /*
    * Register : ATTR_34 @ 0XFD480088

    * Specifies values to be transferred to Header Type register. Bit 7 should
    *  be set to '0' indicating single-function device. Bit 0 identifies heade
    * r as Type 0 or Type 1, with '0' indicating a Type 0 header.; EP=0x0000;
    * RP=0x0001
    *  PSU_PCIE_ATTRIB_ATTR_34_ATTR_HEADER_TYPE                    0x1

    * ATTR_34
    * (OFFSET, MASK, VALUE)      (0XFD480088, 0x000000FFU ,0x00000001U)
    */
	PSU_Mask_Write(PCIE_ATTRIB_ATTR_34_OFFSET, 0x000000FFU, 0x00000001U);
/*##################################################################### */

    /*
    * Register : ATTR_53 @ 0XFD4800D4

    * PM Capability's Next Capability Offset pointer to the next item in the c
    * apabilities list, or 00h if this is the final capability.; EP=0x0048; RP
    * =0x0060
    *  PSU_PCIE_ATTRIB_ATTR_53_ATTR_PM_CAP_NEXTPTR                 0x60

    * ATTR_53
    * (OFFSET, MASK, VALUE)      (0XFD4800D4, 0x000000FFU ,0x00000060U)
    */
	PSU_Mask_Write(PCIE_ATTRIB_ATTR_53_OFFSET, 0x000000FFU, 0x00000060U);
/*##################################################################### */

    /*
    * Register : ATTR_41 @ 0XFD4800A4

    * MSI Per-Vector Masking Capable. The value is transferred to the MSI Cont
    * rol Register[8]. When set, adds Mask and Pending Dword to Cap structure;
    *  EP=0x0000; RP=0x0000
    *  PSU_PCIE_ATTRIB_ATTR_41_ATTR_MSI_CAP_PER_VECTOR_MASKING_CAPABLE 0x0

    * Indicates that the MSI structures exists. If this is FALSE, then the MSI
    *  structure cannot be accessed via either the link or the management port
    * .; EP=0x0001; RP=0x0000
    *  PSU_PCIE_ATTRIB_ATTR_41_ATTR_MSI_CAP_ON                     0

    * MSI Capability's Next Capability Offset pointer to the next item in the
    * capabilities list, or 00h if this is the final capability.; EP=0x0060; R
    * P=0x0000
    *  PSU_PCIE_ATTRIB_ATTR_41_ATTR_MSI_CAP_NEXTPTR                0x0

    * Indicates that the MSI structures exists. If this is FALSE, then the MSI
    *  structure cannot be accessed via either the link or the management port
    * .; EP=0x0001; RP=0x0000
    *  PSU_PCIE_ATTRIB_ATTR_41_ATTR_MSI_CAP_ON                     0

    * ATTR_41
    * (OFFSET, MASK, VALUE)      (0XFD4800A4, 0x000003FFU ,0x00000000U)
    */
	PSU_Mask_Write(PCIE_ATTRIB_ATTR_41_OFFSET, 0x000003FFU, 0x00000000U);
/*##################################################################### */

    /*
    * Register : ATTR_97 @ 0XFD480184

    * Maximum Link Width. Valid settings are: 000001b x1, 000010b x2, 000100b
    * x4, 001000b x8.; EP=0x0004; RP=0x0004
    *  PSU_PCIE_ATTRIB_ATTR_97_ATTR_LINK_CAP_MAX_LINK_WIDTH        0x1

    * Used by LTSSM to set Maximum Link Width. Valid settings are: 000001b [x1
    * ], 000010b [x2], 000100b [x4], 001000b [x8].; EP=0x0004; RP=0x0004
    *  PSU_PCIE_ATTRIB_ATTR_97_ATTR_LTSSM_MAX_LINK_WIDTH           0x1

    * ATTR_97
    * (OFFSET, MASK, VALUE)      (0XFD480184, 0x00000FFFU ,0x00000041U)
    */
	PSU_Mask_Write(PCIE_ATTRIB_ATTR_97_OFFSET, 0x00000FFFU, 0x00000041U);
/*##################################################################### */

    /*
    * Register : ATTR_100 @ 0XFD480190

    * TRUE specifies upstream-facing port. FALSE specifies downstream-facing p
    * ort.; EP=0x0001; RP=0x0000
    *  PSU_PCIE_ATTRIB_ATTR_100_ATTR_UPSTREAM_FACING               0x0

    * ATTR_100
    * (OFFSET, MASK, VALUE)      (0XFD480190, 0x00000040U ,0x00000000U)
    */
	PSU_Mask_Write(PCIE_ATTRIB_ATTR_100_OFFSET,
		0x00000040U, 0x00000000U);
/*##################################################################### */

    /*
    * Register : ATTR_101 @ 0XFD480194

    * Enable the routing of message TLPs to the user through the TRN RX interf
    * ace. A bit value of 1 enables routing of the message TLP to the user. Me
    * ssages are always decoded by the message decoder. Bit 0 - ERR COR, Bit 1
    *  - ERR NONFATAL, Bit 2 - ERR FATAL, Bit 3 - INTA Bit 4 - INTB, Bit 5 - I
    * NTC, Bit 6 - INTD, Bit 7 PM_PME, Bit 8 - PME_TO_ACK, Bit 9 - unlock, Bit
    *  10 PME_Turn_Off; EP=0x0000; RP=0x07FF
    *  PSU_PCIE_ATTRIB_ATTR_101_ATTR_ENABLE_MSG_ROUTE              0x7FF

    * Disable BAR filtering. Does not change the behavior of the bar hit outpu
    * ts; EP=0x0000; RP=0x0001
    *  PSU_PCIE_ATTRIB_ATTR_101_ATTR_DISABLE_BAR_FILTERING         0x1

    * ATTR_101
    * (OFFSET, MASK, VALUE)      (0XFD480194, 0x0000FFE2U ,0x0000FFE2U)
    */
	PSU_Mask_Write(PCIE_ATTRIB_ATTR_101_OFFSET,
		0x0000FFE2U, 0x0000FFE2U);
/*##################################################################### */

    /*
    * Register : ATTR_37 @ 0XFD480094

    * Link Bandwidth notification capability. Indicates support for the link b
    * andwidth notification status and interrupt mechanism. Required for Root.
    * ; EP=0x0000; RP=0x0001
    *  PSU_PCIE_ATTRIB_ATTR_37_ATTR_LINK_CAP_LINK_BANDWIDTH_NOTIFICATION_CAP 0x1

    * Sets the ASPM Optionality Compliance bit, to comply with the 2.1 ASPM Op
    * tionality ECN. Transferred to the Link Capabilities register.; EP=0x0001
    * ; RP=0x0001
    *  PSU_PCIE_ATTRIB_ATTR_37_ATTR_LINK_CAP_ASPM_OPTIONALITY      0x1

    * ATTR_37
    * (OFFSET, MASK, VALUE)      (0XFD480094, 0x00004200U ,0x00004200U)
    */
	PSU_Mask_Write(PCIE_ATTRIB_ATTR_37_OFFSET, 0x00004200U, 0x00004200U);
/*##################################################################### */

    /*
    * Register : ATTR_93 @ 0XFD480174

    * Enables the Replay Timer to use the user-defined LL_REPLAY_TIMEOUT value
    *  (or combined with the built-in value, depending on LL_REPLAY_TIMEOUT_FU
    * NC). If FALSE, the built-in value is used.; EP=0x0000; RP=0x0000
    *  PSU_PCIE_ATTRIB_ATTR_93_ATTR_LL_REPLAY_TIMEOUT_EN           0x1

    * Sets a user-defined timeout for the Replay Timer to force cause the retr
    * ansmission of unacknowledged TLPs; refer to LL_REPLAY_TIMEOUT_EN and LL_
    * REPLAY_TIMEOUT_FUNC to see how this value is used. The unit for this att
    * ribute is in symbol times, which is 4ns at GEN1 speeds and 2ns at GEN2.;
    *  EP=0x0000; RP=0x0000
    *  PSU_PCIE_ATTRIB_ATTR_93_ATTR_LL_REPLAY_TIMEOUT              0x1000

    * ATTR_93
    * (OFFSET, MASK, VALUE)      (0XFD480174, 0x0000FFFFU ,0x00009000U)
    */
	PSU_Mask_Write(PCIE_ATTRIB_ATTR_93_OFFSET, 0x0000FFFFU, 0x00009000U);
/*##################################################################### */

    /*
    * Register : ID @ 0XFD480200

    * Device ID for the the PCIe Cap Structure Device ID field
    *  PSU_PCIE_ATTRIB_ID_CFG_DEV_ID                               0xd021

    * Vendor ID for the PCIe Cap Structure Vendor ID field
    *  PSU_PCIE_ATTRIB_ID_CFG_VEND_ID                              0x10ee

    * ID
    * (OFFSET, MASK, VALUE)      (0XFD480200, 0xFFFFFFFFU ,0x10EED021U)
    */
	PSU_Mask_Write(PCIE_ATTRIB_ID_OFFSET, 0xFFFFFFFFU, 0x10EED021U);
/*##################################################################### */

    /*
    * Register : SUBSYS_ID @ 0XFD480204

    * Subsystem ID for the the PCIe Cap Structure Subsystem ID field
    *  PSU_PCIE_ATTRIB_SUBSYS_ID_CFG_SUBSYS_ID                     0x7

    * Subsystem Vendor ID for the PCIe Cap Structure Subsystem Vendor ID field
    *  PSU_PCIE_ATTRIB_SUBSYS_ID_CFG_SUBSYS_VEND_ID                0x10ee

    * SUBSYS_ID
    * (OFFSET, MASK, VALUE)      (0XFD480204, 0xFFFFFFFFU ,0x10EE0007U)
    */
	PSU_Mask_Write(PCIE_ATTRIB_SUBSYS_ID_OFFSET,
		0xFFFFFFFFU, 0x10EE0007U);
/*##################################################################### */

    /*
    * Register : REV_ID @ 0XFD480208

    * Revision ID for the the PCIe Cap Structure
    *  PSU_PCIE_ATTRIB_REV_ID_CFG_REV_ID                           0x0

    * REV_ID
    * (OFFSET, MASK, VALUE)      (0XFD480208, 0x000000FFU ,0x00000000U)
    */
	PSU_Mask_Write(PCIE_ATTRIB_REV_ID_OFFSET, 0x000000FFU, 0x00000000U);
/*##################################################################### */

    /*
    * Register : ATTR_24 @ 0XFD480060

    * Code identifying basic function, subclass and applicable programming int
    * erface. Transferred to the Class Code register.; EP=0x8000; RP=0x8000
    *  PSU_PCIE_ATTRIB_ATTR_24_ATTR_CLASS_CODE                     0x400

    * ATTR_24
    * (OFFSET, MASK, VALUE)      (0XFD480060, 0x0000FFFFU ,0x00000400U)
    */
	PSU_Mask_Write(PCIE_ATTRIB_ATTR_24_OFFSET, 0x0000FFFFU, 0x00000400U);
/*##################################################################### */

    /*
    * Register : ATTR_25 @ 0XFD480064

    * Code identifying basic function, subclass and applicable programming int
    * erface. Transferred to the Class Code register.; EP=0x0005; RP=0x0006
    *  PSU_PCIE_ATTRIB_ATTR_25_ATTR_CLASS_CODE                     0x6

    * INTX Interrupt Generation Capable. If FALSE, this will cause Command[10]
    *  to be hardwired to 0.; EP=0x0001; RP=0x0001
    *  PSU_PCIE_ATTRIB_ATTR_25_ATTR_CMD_INTX_IMPLEMENTED           0

    * ATTR_25
    * (OFFSET, MASK, VALUE)      (0XFD480064, 0x000001FFU ,0x00000006U)
    */
	PSU_Mask_Write(PCIE_ATTRIB_ATTR_25_OFFSET, 0x000001FFU, 0x00000006U);
/*##################################################################### */

    /*
    * Register : ATTR_4 @ 0XFD480010

    * Indicates that the AER structures exists. If this is FALSE, then the AER
    *  structure cannot be accessed via either the link or the management port
    * , and AER will be considered to not be present for error management task
    * s (such as what types of error messages are sent if an error is detected
    * ).; EP=0x0001; RP=0x0001
    *  PSU_PCIE_ATTRIB_ATTR_4_ATTR_AER_CAP_ON                      0

    * Indicates that the AER structures exists. If this is FALSE, then the AER
    *  structure cannot be accessed via either the link or the management port
    * , and AER will be considered to not be present for error management task
    * s (such as what types of error messages are sent if an error is detected
    * ).; EP=0x0001; RP=0x0001
    *  PSU_PCIE_ATTRIB_ATTR_4_ATTR_AER_CAP_ON                      0

    * ATTR_4
    * (OFFSET, MASK, VALUE)      (0XFD480010, 0x00001000U ,0x00000000U)
    */
	PSU_Mask_Write(PCIE_ATTRIB_ATTR_4_OFFSET, 0x00001000U, 0x00000000U);
/*##################################################################### */

    /*
    * Register : ATTR_89 @ 0XFD480164

    * VSEC's Next Capability Offset pointer to the next item in the capabiliti
    * es list, or 000h if this is the final capability.; EP=0x0140; RP=0x0140
    *  PSU_PCIE_ATTRIB_ATTR_89_ATTR_VSEC_CAP_NEXTPTR               0

    * ATTR_89
    * (OFFSET, MASK, VALUE)      (0XFD480164, 0x00001FFEU ,0x00000000U)
    */
	PSU_Mask_Write(PCIE_ATTRIB_ATTR_89_OFFSET, 0x00001FFEU, 0x00000000U);
/*##################################################################### */

    /*
    * Register : ATTR_79 @ 0XFD48013C

    * CRS SW Visibility. Indicates RC can return CRS to SW. Transferred to the
    *  Root Capabilities register.; EP=0x0000; RP=0x0000
    *  PSU_PCIE_ATTRIB_ATTR_79_ATTR_ROOT_CAP_CRS_SW_VISIBILITY     1

    * ATTR_79
    * (OFFSET, MASK, VALUE)      (0XFD48013C, 0x00000020U ,0x00000020U)
    */
	PSU_Mask_Write(PCIE_ATTRIB_ATTR_79_OFFSET, 0x00000020U, 0x00000020U);
/*##################################################################### */

    /*
    * Register : ATTR_43 @ 0XFD4800AC

    * Indicates that the MSIX structures exists. If this is FALSE, then the MS
    * IX structure cannot be accessed via either the link or the management po
    * rt.; EP=0x0001; RP=0x0000
    *  PSU_PCIE_ATTRIB_ATTR_43_ATTR_MSIX_CAP_ON                    0

    * ATTR_43
    * (OFFSET, MASK, VALUE)      (0XFD4800AC, 0x00000100U ,0x00000000U)
    */
	PSU_Mask_Write(PCIE_ATTRIB_ATTR_43_OFFSET, 0x00000100U, 0x00000000U);
/*##################################################################### */

    /*
    * Register : ATTR_48 @ 0XFD4800C0

    * MSI-X Table Size. This value is transferred to the MSI-X Message Control
    * [10:0] field. Set to 0 if MSI-X is not enabled. Note that the core does
    * not implement the table; that must be implemented in user logic.; EP=0x0
    * 003; RP=0x0000
    *  PSU_PCIE_ATTRIB_ATTR_48_ATTR_MSIX_CAP_TABLE_SIZE            0

    * ATTR_48
    * (OFFSET, MASK, VALUE)      (0XFD4800C0, 0x000007FFU ,0x00000000U)
    */
	PSU_Mask_Write(PCIE_ATTRIB_ATTR_48_OFFSET, 0x000007FFU, 0x00000000U);
/*##################################################################### */

    /*
    * Register : ATTR_46 @ 0XFD4800B8

    * MSI-X Table Offset. This value is transferred to the MSI-X Table Offset
    * field. Set to 0 if MSI-X is not enabled.; EP=0x0001; RP=0x0000
    *  PSU_PCIE_ATTRIB_ATTR_46_ATTR_MSIX_CAP_TABLE_OFFSET          0

    * ATTR_46
    * (OFFSET, MASK, VALUE)      (0XFD4800B8, 0x0000FFFFU ,0x00000000U)
    */
	PSU_Mask_Write(PCIE_ATTRIB_ATTR_46_OFFSET, 0x0000FFFFU, 0x00000000U);
/*##################################################################### */

    /*
    * Register : ATTR_47 @ 0XFD4800BC

    * MSI-X Table Offset. This value is transferred to the MSI-X Table Offset
    * field. Set to 0 if MSI-X is not enabled.; EP=0x0000; RP=0x0000
    *  PSU_PCIE_ATTRIB_ATTR_47_ATTR_MSIX_CAP_TABLE_OFFSET          0

    * ATTR_47
    * (OFFSET, MASK, VALUE)      (0XFD4800BC, 0x00001FFFU ,0x00000000U)
    */
	PSU_Mask_Write(PCIE_ATTRIB_ATTR_47_OFFSET, 0x00001FFFU, 0x00000000U);
/*##################################################################### */

    /*
    * Register : ATTR_44 @ 0XFD4800B0

    * MSI-X Pending Bit Array Offset This value is transferred to the MSI-X PB
    * A Offset field. Set to 0 if MSI-X is not enabled.; EP=0x0001; RP=0x0000
    *  PSU_PCIE_ATTRIB_ATTR_44_ATTR_MSIX_CAP_PBA_OFFSET            0

    * ATTR_44
    * (OFFSET, MASK, VALUE)      (0XFD4800B0, 0x0000FFFFU ,0x00000000U)
    */
	PSU_Mask_Write(PCIE_ATTRIB_ATTR_44_OFFSET, 0x0000FFFFU, 0x00000000U);
/*##################################################################### */

    /*
    * Register : ATTR_45 @ 0XFD4800B4

    * MSI-X Pending Bit Array Offset This value is transferred to the MSI-X PB
    * A Offset field. Set to 0 if MSI-X is not enabled.; EP=0x1000; RP=0x0000
    *  PSU_PCIE_ATTRIB_ATTR_45_ATTR_MSIX_CAP_PBA_OFFSET            0

    * ATTR_45
    * (OFFSET, MASK, VALUE)      (0XFD4800B4, 0x0000FFF8U ,0x00000000U)
    */
	PSU_Mask_Write(PCIE_ATTRIB_ATTR_45_OFFSET, 0x0000FFF8U, 0x00000000U);
/*##################################################################### */

    /*
    * Register : CB @ 0XFD48031C

    * DT837748 Enable
    *  PSU_PCIE_ATTRIB_CB_CB1                                      0x0

    * ECO Register 1
    * (OFFSET, MASK, VALUE)      (0XFD48031C, 0x00000002U ,0x00000000U)
    */
	PSU_Mask_Write(PCIE_ATTRIB_CB_OFFSET, 0x00000002U, 0x00000000U);
/*##################################################################### */

    /*
    * Register : ATTR_35 @ 0XFD48008C

    * Active State PM Support. Indicates the level of active state power manag
    * ement supported by the selected PCI Express Link, encoded as follows: 0
    * Reserved, 1 L0s entry supported, 2 Reserved, 3 L0s and L1 entry supporte
    * d.; EP=0x0001; RP=0x0001
    *  PSU_PCIE_ATTRIB_ATTR_35_ATTR_LINK_CAP_ASPM_SUPPORT          0x0

    * ATTR_35
    * (OFFSET, MASK, VALUE)      (0XFD48008C, 0x00003000U ,0x00000000U)
    */
	PSU_Mask_Write(PCIE_ATTRIB_ATTR_35_OFFSET, 0x00003000U, 0x00000000U);
/*##################################################################### */

    /*
    * PUTTING PCIE CONTROL IN RESET
    */
    /*
    * Register : RST_FPD_TOP @ 0XFD1A0100

    * PCIE control block level reset
    *  PSU_CRF_APB_RST_FPD_TOP_PCIE_CTRL_RESET                     0X0

    * FPD Block level software controlled reset
    * (OFFSET, MASK, VALUE)      (0XFD1A0100, 0x00020000U ,0x00000000U)
    */
	PSU_Mask_Write(CRF_APB_RST_FPD_TOP_OFFSET, 0x00020000U, 0x00000000U);
/*##################################################################### */

    /*
    * PCIE GPIO RESET
    */
    /*
    * MASK_DATA_0_LSW LOW BANK [15:0]
    */
    /*
    * MASK_DATA_0_MSW LOW BANK [25:16]
    */
    /*
    * MASK_DATA_1_LSW LOW BANK [41:26]
    */
    /*
    * Register : MASK_DATA_1_LSW @ 0XFF0A0008

    * Operation is the same as MASK_DATA_0_LSW[MASK_0_LSW]
    *  PSU_GPIO_MASK_DATA_1_LSW_MASK_1_LSW                         0xffdf

    * Operation is the same as MASK_DATA_0_LSW[DATA_0_LSW]
    *  PSU_GPIO_MASK_DATA_1_LSW_DATA_1_LSW                         0x20

    * Maskable Output Data (GPIO Bank1, MIO, Lower 16bits)
    * (OFFSET, MASK, VALUE)      (0XFF0A0008, 0xFFFFFFFFU ,0xFFDF0020U)
    */
	PSU_Mask_Write(GPIO_MASK_DATA_1_LSW_OFFSET,
		0xFFFFFFFFU, 0xFFDF0020U);
/*##################################################################### */

    /*
    * MASK_DATA_1_MSW HIGH BANK [51:42]
    */
    /*
    * MASK_DATA_1_LSW HIGH BANK [67:52]
    */
    /*
    * MASK_DATA_1_LSW HIGH BANK [77:68]
    */
    /*
    * CHECK PLL LOCK FOR LANE0
    */
    /*
    * Register : L0_PLL_STATUS_READ_1 @ 0XFD4023E4

    * Status Read value of PLL Lock
    *  PSU_SERDES_L0_PLL_STATUS_READ_1_PLL_LOCK_STATUS_READ        1
    * (OFFSET, MASK, VALUE)      (0XFD4023E4, 0x00000010U ,0x00000010U)
		*/
	mask_poll(SERDES_L0_PLL_STATUS_READ_1_OFFSET, 0x00000010U);

/*##################################################################### */

    /*
    * CHECK PLL LOCK FOR LANE1
    */
    /*
    * Register : L1_PLL_STATUS_READ_1 @ 0XFD4063E4

    * Status Read value of PLL Lock
    *  PSU_SERDES_L1_PLL_STATUS_READ_1_PLL_LOCK_STATUS_READ        1
    * (OFFSET, MASK, VALUE)      (0XFD4063E4, 0x00000010U ,0x00000010U)
		*/
	mask_poll(SERDES_L1_PLL_STATUS_READ_1_OFFSET, 0x00000010U);

/*##################################################################### */

    /*
    * CHECK PLL LOCK FOR LANE2
    */
    /*
    * Register : L2_PLL_STATUS_READ_1 @ 0XFD40A3E4

    * Status Read value of PLL Lock
    *  PSU_SERDES_L2_PLL_STATUS_READ_1_PLL_LOCK_STATUS_READ        1
    * (OFFSET, MASK, VALUE)      (0XFD40A3E4, 0x00000010U ,0x00000010U)
		*/
	mask_poll(SERDES_L2_PLL_STATUS_READ_1_OFFSET, 0x00000010U);

/*##################################################################### */

    /*
    * CHECK PLL LOCK FOR LANE3
    */
    /*
    * Register : L3_PLL_STATUS_READ_1 @ 0XFD40E3E4

    * Status Read value of PLL Lock
    *  PSU_SERDES_L3_PLL_STATUS_READ_1_PLL_LOCK_STATUS_READ        1
    * (OFFSET, MASK, VALUE)      (0XFD40E3E4, 0x00000010U ,0x00000010U)
		*/
	mask_poll(SERDES_L3_PLL_STATUS_READ_1_OFFSET, 0x00000010U);

/*##################################################################### */

    /*
    * SATA AHCI VENDOR SETTING
    */
    /*
    * Register : PP2C @ 0XFD0C00AC

    * CIBGMN: COMINIT Burst Gap Minimum.
    *  PSU_SATA_AHCI_VENDOR_PP2C_CIBGMN                            0x18

    * CIBGMX: COMINIT Burst Gap Maximum.
    *  PSU_SATA_AHCI_VENDOR_PP2C_CIBGMX                            0x40

    * CIBGN: COMINIT Burst Gap Nominal.
    *  PSU_SATA_AHCI_VENDOR_PP2C_CIBGN                             0x18

    * CINMP: COMINIT Negate Minimum Period.
    *  PSU_SATA_AHCI_VENDOR_PP2C_CINMP                             0x28

    * PP2C - Port Phy2Cfg Register. This register controls the configuration o
    * f the Phy Control OOB timing for the COMINIT parameters for either Port
    * 0 or Port 1. The Port configured is controlled by the value programmed i
    * nto the Port Config Register.
    * (OFFSET, MASK, VALUE)      (0XFD0C00AC, 0xFFFFFFFFU ,0x28184018U)
    */
	PSU_Mask_Write(SATA_AHCI_VENDOR_PP2C_OFFSET,
		0xFFFFFFFFU, 0x28184018U);
/*##################################################################### */

    /*
    * Register : PP3C @ 0XFD0C00B0

    * CWBGMN: COMWAKE Burst Gap Minimum.
    *  PSU_SATA_AHCI_VENDOR_PP3C_CWBGMN                            0x06

    * CWBGMX: COMWAKE Burst Gap Maximum.
    *  PSU_SATA_AHCI_VENDOR_PP3C_CWBGMX                            0x14

    * CWBGN: COMWAKE Burst Gap Nominal.
    *  PSU_SATA_AHCI_VENDOR_PP3C_CWBGN                             0x08

    * CWNMP: COMWAKE Negate Minimum Period.
    *  PSU_SATA_AHCI_VENDOR_PP3C_CWNMP                             0x0E

    * PP3C - Port Phy3CfgRegister. This register controls the configuration of
    *  the Phy Control OOB timing for the COMWAKE parameters for either Port 0
    *  or Port 1. The Port configured is controlled by the value programmed in
    * to the Port Config Register.
    * (OFFSET, MASK, VALUE)      (0XFD0C00B0, 0xFFFFFFFFU ,0x0E081406U)
    */
	PSU_Mask_Write(SATA_AHCI_VENDOR_PP3C_OFFSET,
		0xFFFFFFFFU, 0x0E081406U);
/*##################################################################### */

    /*
    * Register : PP4C @ 0XFD0C00B4

    * BMX: COM Burst Maximum.
    *  PSU_SATA_AHCI_VENDOR_PP4C_BMX                               0x13

    * BNM: COM Burst Nominal.
    *  PSU_SATA_AHCI_VENDOR_PP4C_BNM                               0x08

    * SFD: Signal Failure Detection, if the signal detection de-asserts for a
    * time greater than this then the OOB detector will determine this is a li
    * ne idle and cause the PhyInit state machine to exit the Phy Ready State.
    *  A value of zero disables the Signal Failure Detector. The value is base
    * d on the OOB Detector Clock typically (PMCLK Clock Period) * SFD giving
    * a nominal time of 500ns based on a 150MHz PMCLK.
    *  PSU_SATA_AHCI_VENDOR_PP4C_SFD                               0x4A

    * PTST: Partial to Slumber timer value, specific delay the controller shou
    * ld apply while in partial before entering slumber. The value is bases on
    *  the system clock divided by 128, total delay = (Sys Clock Period) * PTS
    * T * 128
    *  PSU_SATA_AHCI_VENDOR_PP4C_PTST                              0x06

    * PP4C - Port Phy4Cfg Register. This register controls the configuration o
    * f the Phy Control Burst timing for the COM parameters for either Port 0
    * or Port 1. The Port configured is controlled by the value programmed int
    * o the Port Config Register.
    * (OFFSET, MASK, VALUE)      (0XFD0C00B4, 0xFFFFFFFFU ,0x064A0813U)
    */
	PSU_Mask_Write(SATA_AHCI_VENDOR_PP4C_OFFSET,
		0xFFFFFFFFU, 0x064A0813U);
/*##################################################################### */

    /*
    * Register : PP5C @ 0XFD0C00B8

    * RIT: Retry Interval Timer. The calculated value divided by two, the lowe
    * r digit of precision is not needed.
    *  PSU_SATA_AHCI_VENDOR_PP5C_RIT                               0xC96A4

    * RCT: Rate Change Timer, a value based on the 54.2us for which a SATA dev
    * ice will transmit at a fixed rate ALIGNp after OOB has completed, for a
    * fast SERDES it is suggested that this value be 54.2us / 4
    *  PSU_SATA_AHCI_VENDOR_PP5C_RCT                               0x3FF

    * PP5C - Port Phy5Cfg Register. This register controls the configuration o
    * f the Phy Control Retry Interval timing for either Port 0 or Port 1. The
    *  Port configured is controlled by the value programmed into the Port Con
    * fig Register.
    * (OFFSET, MASK, VALUE)      (0XFD0C00B8, 0xFFFFFFFFU ,0x3FFC96A4U)
    */
	PSU_Mask_Write(SATA_AHCI_VENDOR_PP5C_OFFSET,
		0xFFFFFFFFU, 0x3FFC96A4U);
/*##################################################################### */


	return 1;
}
unsigned long psu_resetin_init_data(void)
{
    /*
    * PUTTING SERDES PERIPHERAL IN RESET
    */
    /*
    * PUTTING USB0 IN RESET
    */
    /*
    * Register : RST_LPD_TOP @ 0XFF5E023C

    * USB 0 reset for control registers
    *  PSU_CRL_APB_RST_LPD_TOP_USB0_APB_RESET                      0X1

    * USB 0 sleep circuit reset
    *  PSU_CRL_APB_RST_LPD_TOP_USB0_HIBERRESET                     0X1

    * USB 0 reset
    *  PSU_CRL_APB_RST_LPD_TOP_USB0_CORERESET                      0X1

    * Software control register for the LPD block.
    * (OFFSET, MASK, VALUE)      (0XFF5E023C, 0x00000540U ,0x00000540U)
    */
	PSU_Mask_Write(CRL_APB_RST_LPD_TOP_OFFSET, 0x00000540U, 0x00000540U);
/*##################################################################### */

    /*
    * PUTTING GEM0 IN RESET
    */
    /*
    * Register : RST_LPD_IOU0 @ 0XFF5E0230

    * GEM 3 reset
    *  PSU_CRL_APB_RST_LPD_IOU0_GEM3_RESET                         0X1

    * Software controlled reset for the GEMs
    * (OFFSET, MASK, VALUE)      (0XFF5E0230, 0x00000008U ,0x00000008U)
    */
	PSU_Mask_Write(CRL_APB_RST_LPD_IOU0_OFFSET,
		0x00000008U, 0x00000008U);
/*##################################################################### */

    /*
    * PUTTING SATA IN RESET
    */
    /*
    * Register : RST_FPD_TOP @ 0XFD1A0100

    * Sata block level reset
    *  PSU_CRF_APB_RST_FPD_TOP_SATA_RESET                          0X1

    * FPD Block level software controlled reset
    * (OFFSET, MASK, VALUE)      (0XFD1A0100, 0x00000002U ,0x00000002U)
    */
	PSU_Mask_Write(CRF_APB_RST_FPD_TOP_OFFSET, 0x00000002U, 0x00000002U);
/*##################################################################### */

    /*
    * PUTTING PCIE IN RESET
    */
    /*
    * Register : RST_FPD_TOP @ 0XFD1A0100

    * PCIE config reset
    *  PSU_CRF_APB_RST_FPD_TOP_PCIE_CFG_RESET                      0X1

    * PCIE control block level reset
    *  PSU_CRF_APB_RST_FPD_TOP_PCIE_CTRL_RESET                     0X1

    * PCIE bridge block level reset (AXI interface)
    *  PSU_CRF_APB_RST_FPD_TOP_PCIE_BRIDGE_RESET                   0X1

    * FPD Block level software controlled reset
    * (OFFSET, MASK, VALUE)      (0XFD1A0100, 0x000E0000U ,0x000E0000U)
    */
	PSU_Mask_Write(CRF_APB_RST_FPD_TOP_OFFSET, 0x000E0000U, 0x000E0000U);
/*##################################################################### */

    /*
    * PUTTING DP IN RESET
    */
    /*
    * Register : DP_TX_PHY_POWER_DOWN @ 0XFD4A0238

    * Two bits per lane. When set to 11, moves the GT to power down mode. When
    *  set to 00, GT will be in active state. bits [1:0] - lane0 Bits [3:2] -
    * lane 1
    *  PSU_DP_DP_TX_PHY_POWER_DOWN_POWER_DWN                       0XA

    * Control PHY Power down
    * (OFFSET, MASK, VALUE)      (0XFD4A0238, 0x0000000FU ,0x0000000AU)
    */
	PSU_Mask_Write(DP_DP_TX_PHY_POWER_DOWN_OFFSET,
		0x0000000FU, 0x0000000AU);
/*##################################################################### */

    /*
    * Register : DP_PHY_RESET @ 0XFD4A0200

    * Set to '1' to hold the GT in reset. Clear to release.
    *  PSU_DP_DP_PHY_RESET_GT_RESET                                0X1

    * Reset the transmitter PHY.
    * (OFFSET, MASK, VALUE)      (0XFD4A0200, 0x00000002U ,0x00000002U)
    */
	PSU_Mask_Write(DP_DP_PHY_RESET_OFFSET, 0x00000002U, 0x00000002U);
/*##################################################################### */

    /*
    * Register : RST_FPD_TOP @ 0XFD1A0100

    * Display Port block level reset (includes DPDMA)
    *  PSU_CRF_APB_RST_FPD_TOP_DP_RESET                            0X1

    * FPD Block level software controlled reset
    * (OFFSET, MASK, VALUE)      (0XFD1A0100, 0x00010000U ,0x00010000U)
    */
	PSU_Mask_Write(CRF_APB_RST_FPD_TOP_OFFSET, 0x00010000U, 0x00010000U);
/*##################################################################### */


	return 1;
}
unsigned long psu_ps_pl_isolation_removal_data(void)
{
    /*
    * PS-PL POWER UP REQUEST
    */
    /*
    * Register : REQ_PWRUP_INT_EN @ 0XFFD80118

    * Power-up Request Interrupt Enable for PL
    *  PSU_PMU_GLOBAL_REQ_PWRUP_INT_EN_PL                          1

    * Power-up Request Interrupt Enable Register. Writing a 1 to this location
    *  will unmask the interrupt.
    * (OFFSET, MASK, VALUE)      (0XFFD80118, 0x00800000U ,0x00800000U)
    */
	PSU_Mask_Write(PMU_GLOBAL_REQ_PWRUP_INT_EN_OFFSET,
		0x00800000U, 0x00800000U);
/*##################################################################### */

    /*
    * Register : REQ_PWRUP_TRIG @ 0XFFD80120

    * Power-up Request Trigger for PL
    *  PSU_PMU_GLOBAL_REQ_PWRUP_TRIG_PL                            1

    * Power-up Request Trigger Register. A write of one to this location will
    * generate a power-up request to the PMU.
    * (OFFSET, MASK, VALUE)      (0XFFD80120, 0x00800000U ,0x00800000U)
    */
	PSU_Mask_Write(PMU_GLOBAL_REQ_PWRUP_TRIG_OFFSET,
		0x00800000U, 0x00800000U);
/*##################################################################### */

    /*
    * POLL ON PL POWER STATUS
    */
    /*
    * Register : REQ_PWRUP_STATUS @ 0XFFD80110

    * Power-up Request Status for PL
    *  PSU_PMU_GLOBAL_REQ_PWRUP_STATUS_PL                          1
    * (OFFSET, MASK, VALUE)      (0XFFD80110, 0x00800000U ,0x00000000U)
		*/
	mask_pollOnValue(PMU_GLOBAL_REQ_PWRUP_STATUS_OFFSET,
		0x00800000U, 0x00000000U);

/*##################################################################### */


	return 1;
}
unsigned long psu_afi_config(void)
{
    /*
    * AFI RESET
    */
    /*
    * Register : RST_FPD_TOP @ 0XFD1A0100

    * AF_FM0 block level reset
    *  PSU_CRF_APB_RST_FPD_TOP_AFI_FM0_RESET                       0

    * AF_FM1 block level reset
    *  PSU_CRF_APB_RST_FPD_TOP_AFI_FM1_RESET                       0

    * AF_FM2 block level reset
    *  PSU_CRF_APB_RST_FPD_TOP_AFI_FM2_RESET                       0

    * AF_FM3 block level reset
    *  PSU_CRF_APB_RST_FPD_TOP_AFI_FM3_RESET                       0

    * AF_FM4 block level reset
    *  PSU_CRF_APB_RST_FPD_TOP_AFI_FM4_RESET                       0

    * AF_FM5 block level reset
    *  PSU_CRF_APB_RST_FPD_TOP_AFI_FM5_RESET                       0

    * FPD Block level software controlled reset
    * (OFFSET, MASK, VALUE)      (0XFD1A0100, 0x00001F80U ,0x00000000U)
    */
	PSU_Mask_Write(CRF_APB_RST_FPD_TOP_OFFSET, 0x00001F80U, 0x00000000U);
/*##################################################################### */

    /*
    * Register : RST_LPD_TOP @ 0XFF5E023C

    * AFI FM 6
    *  PSU_CRL_APB_RST_LPD_TOP_AFI_FM6_RESET                       0

    * Software control register for the LPD block.
    * (OFFSET, MASK, VALUE)      (0XFF5E023C, 0x00080000U ,0x00000000U)
    */
	PSU_Mask_Write(CRL_APB_RST_LPD_TOP_OFFSET, 0x00080000U, 0x00000000U);
/*##################################################################### */

    /*
    * AFIFM INTERFACE WIDTH
    */
    /*
    * Register : afi_fs @ 0XFD615000

    * Select the 32/64/128-bit data width selection for the Slave 0 00: 32-bit
    *  AXI data width (default) 01: 64-bit AXI data width 10: 128-bit AXI data
    *  width 11: reserved
    *  PSU_FPD_SLCR_AFI_FS_DW_SS0_SEL                              0x2

    * Select the 32/64/128-bit data width selection for the Slave 1 00: 32-bit
    *  AXI data width (default) 01: 64-bit AXI data width 10: 128-bit AXI data
    *  width 11: reserved
    *  PSU_FPD_SLCR_AFI_FS_DW_SS1_SEL                              0x2

    * afi fs SLCR control register. This register is static and should not be
    * modified during operation.
    * (OFFSET, MASK, VALUE)      (0XFD615000, 0x00000F00U ,0x00000A00U)
    */
	PSU_Mask_Write(FPD_SLCR_AFI_FS_OFFSET, 0x00000F00U, 0x00000A00U);
/*##################################################################### */


	return 1;
}
unsigned long psu_ps_pl_reset_config_data(void)
{
    /*
    * PS PL RESET SEQUENCE
    */
    /*
    * FABRIC RESET USING EMIO
    */
    /*
    * Register : MASK_DATA_5_MSW @ 0XFF0A002C

    * Operation is the same as MASK_DATA_0_LSW[MASK_0_LSW]
    *  PSU_GPIO_MASK_DATA_5_MSW_MASK_5_MSW                         0x8000

    * Maskable Output Data (GPIO Bank5, EMIO, Upper 16bits)
    * (OFFSET, MASK, VALUE)      (0XFF0A002C, 0xFFFF0000U ,0x80000000U)
    */
	PSU_Mask_Write(GPIO_MASK_DATA_5_MSW_OFFSET,
		0xFFFF0000U, 0x80000000U);
/*##################################################################### */

    /*
    * Register : DIRM_5 @ 0XFF0A0344

    * Operation is the same as DIRM_0[DIRECTION_0]
    *  PSU_GPIO_DIRM_5_DIRECTION_5                                 0x80000000

    * Direction mode (GPIO Bank5, EMIO)
    * (OFFSET, MASK, VALUE)      (0XFF0A0344, 0xFFFFFFFFU ,0x80000000U)
    */
	PSU_Mask_Write(GPIO_DIRM_5_OFFSET, 0xFFFFFFFFU, 0x80000000U);
/*##################################################################### */

    /*
    * Register : OEN_5 @ 0XFF0A0348

    * Operation is the same as OEN_0[OP_ENABLE_0]
    *  PSU_GPIO_OEN_5_OP_ENABLE_5                                  0x80000000

    * Output enable (GPIO Bank5, EMIO)
    * (OFFSET, MASK, VALUE)      (0XFF0A0348, 0xFFFFFFFFU ,0x80000000U)
    */
	PSU_Mask_Write(GPIO_OEN_5_OFFSET, 0xFFFFFFFFU, 0x80000000U);
/*##################################################################### */

    /*
    * Register : DATA_5 @ 0XFF0A0054

    * Output Data
    *  PSU_GPIO_DATA_5_DATA_5                                      0x80000000

    * Output Data (GPIO Bank5, EMIO)
    * (OFFSET, MASK, VALUE)      (0XFF0A0054, 0xFFFFFFFFU ,0x80000000U)
    */
	PSU_Mask_Write(GPIO_DATA_5_OFFSET, 0xFFFFFFFFU, 0x80000000U);
/*##################################################################### */

		mask_delay(1);

/*##################################################################### */

    /*
    * FABRIC RESET USING DATA_5 TOGGLE
    */
    /*
    * Register : DATA_5 @ 0XFF0A0054

    * Output Data
    *  PSU_GPIO_DATA_5_DATA_5                                      0X00000000

    * Output Data (GPIO Bank5, EMIO)
    * (OFFSET, MASK, VALUE)      (0XFF0A0054, 0xFFFFFFFFU ,0x00000000U)
    */
	PSU_Mask_Write(GPIO_DATA_5_OFFSET, 0xFFFFFFFFU, 0x00000000U);
/*##################################################################### */

		mask_delay(1);

/*##################################################################### */

    /*
    * FABRIC RESET USING DATA_5 TOGGLE
    */
    /*
    * Register : DATA_5 @ 0XFF0A0054

    * Output Data
    *  PSU_GPIO_DATA_5_DATA_5                                      0x80000000

    * Output Data (GPIO Bank5, EMIO)
    * (OFFSET, MASK, VALUE)      (0XFF0A0054, 0xFFFFFFFFU ,0x80000000U)
    */
	PSU_Mask_Write(GPIO_DATA_5_OFFSET, 0xFFFFFFFFU, 0x80000000U);
/*##################################################################### */


	return 1;
}

unsigned long psu_ddr_phybringup_data(void)
{


	unsigned int regval = 0;

	unsigned int pll_retry = 10;

	unsigned int pll_locked = 0;


	while ((pll_retry > 0) && (!pll_locked)) {

		Xil_Out32(0xFD080004, 0x00040010);/*PIR*/
		Xil_Out32(0xFD080004, 0x00040011);/*PIR*/

	while ((Xil_In32(0xFD080030) & 0x1) != 1) {
	/*****TODO*****/

	/*TIMEOUT poll mechanism need to be inserted in this block*/

	}


		pll_locked = (Xil_In32(0xFD080030) & 0x80000000)
		>> 31;/*PGSR0*/
		pll_locked &= (Xil_In32(0xFD0807E0) & 0x10000)
		>> 16;/*DX0GSR0*/
		pll_locked &= (Xil_In32(0xFD0809E0) & 0x10000)
		>> 16;/*DX2GSR0*/
		pll_locked &= (Xil_In32(0xFD080BE0) & 0x10000)
		>> 16;/*DX4GSR0*/
		pll_locked &= (Xil_In32(0xFD080DE0) & 0x10000)
		>> 16;/*DX6GSR0*/
		pll_retry--;
	}
	Xil_Out32(0xFD0800C0, Xil_In32(0xFD0800C0) |
		(pll_retry << 16));/*GPR0*/
	Xil_Out32(0xFD080004U, 0x00040063U);
	/* PHY BRINGUP SEQ */
	while ((Xil_In32(0xFD080030U) & 0x0000000FU) != 0x0000000FU) {
	/*****TODO*****/

	/*TIMEOUT poll mechanism need to be inserted in this block*/

	}

	prog_reg(0xFD080004U, 0x00000001U, 0x00000000U, 0x00000001U);
	/* poll for PHY initialization to complete */
	while ((Xil_In32(0xFD080030U) & 0x000000FFU) != 0x0000001FU) {
	/*****TODO*****/

	/*TIMEOUT poll mechanism need to be inserted in this block*/

	}


	Xil_Out32(0xFD0701B0U, 0x00000001U);
	Xil_Out32(0xFD070320U, 0x00000001U);
	while ((Xil_In32(0xFD070004U) & 0x0000000FU) != 0x00000001U) {
	/*****TODO*****/

	/*TIMEOUT poll mechanism need to be inserted in this block*/

	}

	prog_reg(0xFD080014U, 0x00000040U, 0x00000006U, 0x00000001U);
	Xil_Out32(0xFD080004, 0x0004FE01); /*PUB_PIR*/
	regval = Xil_In32(0xFD080030); /*PUB_PGSR0*/
	while (regval != 0x80000FFF)
		regval = Xil_In32(0xFD080030); /*PUB_PGSR0*/

/* Run Vref training in static read mode*/
	Xil_Out32(0xFD080200U, 0x100091C7U);
	Xil_Out32(0xFD080018U, 0x00F01EEFU);
	prog_reg(0xFD08001CU, 0x00000018U, 0x00000003U, 0x00000003U);
	prog_reg(0xFD08142CU, 0x00000030U, 0x00000004U, 0x00000003U);
	prog_reg(0xFD08146CU, 0x00000030U, 0x00000004U, 0x00000003U);
	prog_reg(0xFD0814ACU, 0x00000030U, 0x00000004U, 0x00000003U);
	prog_reg(0xFD0814ECU, 0x00000030U, 0x00000004U, 0x00000003U);
	prog_reg(0xFD08152CU, 0x00000030U, 0x00000004U, 0x00000003U);


	Xil_Out32(0xFD080004, 0x00060001); /*PUB_PIR*/
	regval = Xil_In32(0xFD080030); /*PUB_PGSR0*/
	while ((regval & 0x80004001) != 0x80004001) {
	/*PUB_PGSR0*/
		regval = Xil_In32(0xFD080030);
	}

	prog_reg(0xFD08001CU, 0x00000018U, 0x00000003U, 0x00000000U);
	prog_reg(0xFD08142CU, 0x00000030U, 0x00000004U, 0x00000000U);
	prog_reg(0xFD08146CU, 0x00000030U, 0x00000004U, 0x00000000U);
	prog_reg(0xFD0814ACU, 0x00000030U, 0x00000004U, 0x00000000U);
	prog_reg(0xFD0814ECU, 0x00000030U, 0x00000004U, 0x00000000U);
	prog_reg(0xFD08152CU, 0x00000030U, 0x00000004U, 0x00000000U);
/*Vref training is complete, disabling static read mode*/
	Xil_Out32(0xFD080200U, 0x800091C7U);
	Xil_Out32(0xFD080018U, 0x00F122E7U);


	Xil_Out32(0xFD080004, 0x0000C001); /*PUB_PIR*/
	regval = Xil_In32(0xFD080030); /*PUB_PGSR0*/
	while ((regval & 0x80000C01) != 0x80000C01) {
	/*PUB_PGSR0*/
		regval = Xil_In32(0xFD080030);
	}

	Xil_Out32(0xFD070180U, 0x01000040U);
	Xil_Out32(0xFD070060U, 0x00000000U);
	prog_reg(0xFD080014U, 0x00000040U, 0x00000006U, 0x00000000U);

return 1;
}

/**
 * CRL_APB Base Address
 */
#define CRL_APB_BASEADDR      0XFF5E0000U
#define CRL_APB_RST_LPD_IOU0    ((CRL_APB_BASEADDR) + 0X00000230U)
#define CRL_APB_RST_LPD_IOU1    ((CRL_APB_BASEADDR) + 0X00000234U)
#define CRL_APB_RST_LPD_IOU2    ((CRL_APB_BASEADDR) + 0X00000238U)
#define CRL_APB_RST_LPD_TOP    ((CRL_APB_BASEADDR) + 0X0000023CU)
#define CRL_APB_IOU_SWITCH_CTRL    ((CRL_APB_BASEADDR) + 0X0000009CU)

/**
 * CRF_APB Base Address
 */
#define CRF_APB_BASEADDR      0XFD1A0000U

#define CRF_APB_RST_FPD_TOP    ((CRF_APB_BASEADDR) + 0X00000100U)
#define CRF_APB_GPU_REF_CTRL    ((CRF_APB_BASEADDR) + 0X00000084U)
#define CRF_APB_RST_DDR_SS    ((CRF_APB_BASEADDR) + 0X00000108U)
#define PSU_MASK_POLL_TIME 1100000

/**
 *  * Register: CRF_APB_DPLL_CTRL
 */
#define CRF_APB_DPLL_CTRL    ((CRF_APB_BASEADDR) + 0X0000002C)


#define CRF_APB_DPLL_CTRL_DIV2_SHIFT   16
#define CRF_APB_DPLL_CTRL_DIV2_WIDTH   1

#define CRF_APB_DPLL_CTRL_FBDIV_SHIFT   8
#define CRF_APB_DPLL_CTRL_FBDIV_WIDTH   7

#define CRF_APB_DPLL_CTRL_BYPASS_SHIFT   3
#define CRF_APB_DPLL_CTRL_BYPASS_WIDTH   1

#define CRF_APB_DPLL_CTRL_RESET_SHIFT   0
#define CRF_APB_DPLL_CTRL_RESET_WIDTH   1

/**
 *  * Register: CRF_APB_DPLL_CFG
 */
#define CRF_APB_DPLL_CFG    ((CRF_APB_BASEADDR) + 0X00000030)

#define CRF_APB_DPLL_CFG_LOCK_DLY_SHIFT   25
#define CRF_APB_DPLL_CFG_LOCK_DLY_WIDTH   7

#define CRF_APB_DPLL_CFG_LOCK_CNT_SHIFT   13
#define CRF_APB_DPLL_CFG_LOCK_CNT_WIDTH   10

#define CRF_APB_DPLL_CFG_LFHF_SHIFT   10
#define CRF_APB_DPLL_CFG_LFHF_WIDTH   2

#define CRF_APB_DPLL_CFG_CP_SHIFT   5
#define CRF_APB_DPLL_CFG_CP_WIDTH   4

#define CRF_APB_DPLL_CFG_RES_SHIFT   0
#define CRF_APB_DPLL_CFG_RES_WIDTH   4

/**
 * Register: CRF_APB_PLL_STATUS
 */
#define CRF_APB_PLL_STATUS    ((CRF_APB_BASEADDR) + 0X00000044)


static int mask_pollOnValue(u32 add, u32 mask, u32 value)
{
	volatile u32 *addr = (volatile u32 *)(unsigned long) add;
	int i = 0;

	while ((*addr & mask) != value) {
		if (i == PSU_MASK_POLL_TIME)
			return 0;
		i++;
	}
	return 1;
}

static int mask_poll(u32 add, u32 mask)
{
	volatile u32 *addr = (volatile u32 *)(unsigned long) add;
	int i = 0;

	while (!(*addr & mask)) {
		if (i == PSU_MASK_POLL_TIME)
			return 0;
		i++;
	}
	return 1;
}

static void mask_delay(u32 delay)
{
	usleep(delay);
}

static u32 mask_read(u32 add, u32 mask)
{
	volatile u32 *addr = (volatile u32 *)(unsigned long) add;
	u32 val = (*addr & mask);
	return val;
}

static void dpll_prog(int ddr_pll_fbdiv, int d_lock_dly, int d_lock_cnt,
	int d_lfhf, int d_cp, int d_res) {

	unsigned int pll_ctrl_regval;
	unsigned int pll_status_regval;

	pll_ctrl_regval = Xil_In32(CRF_APB_DPLL_CTRL);
	pll_ctrl_regval = pll_ctrl_regval & (~CRF_APB_DPLL_CTRL_DIV2_MASK);
	pll_ctrl_regval = pll_ctrl_regval | (1 << CRF_APB_DPLL_CTRL_DIV2_SHIFT);
	Xil_Out32(CRF_APB_DPLL_CTRL, pll_ctrl_regval);

	pll_ctrl_regval = Xil_In32(CRF_APB_DPLL_CFG);
	pll_ctrl_regval = pll_ctrl_regval & (~CRF_APB_DPLL_CFG_LOCK_DLY_MASK);
	pll_ctrl_regval = pll_ctrl_regval |
		(d_lock_dly << CRF_APB_DPLL_CFG_LOCK_DLY_SHIFT);
	Xil_Out32(CRF_APB_DPLL_CFG, pll_ctrl_regval);

	pll_ctrl_regval = Xil_In32(CRF_APB_DPLL_CFG);
	pll_ctrl_regval = pll_ctrl_regval & (~CRF_APB_DPLL_CFG_LOCK_CNT_MASK);
	pll_ctrl_regval = pll_ctrl_regval |
		(d_lock_cnt << CRF_APB_DPLL_CFG_LOCK_CNT_SHIFT);
	Xil_Out32(CRF_APB_DPLL_CFG, pll_ctrl_regval);

	pll_ctrl_regval = Xil_In32(CRF_APB_DPLL_CFG);
	pll_ctrl_regval = pll_ctrl_regval & (~CRF_APB_DPLL_CFG_LFHF_MASK);
	pll_ctrl_regval = pll_ctrl_regval |
		(d_lfhf << CRF_APB_DPLL_CFG_LFHF_SHIFT);
	Xil_Out32(CRF_APB_DPLL_CFG, pll_ctrl_regval);

	pll_ctrl_regval = Xil_In32(CRF_APB_DPLL_CFG);
	pll_ctrl_regval = pll_ctrl_regval & (~CRF_APB_DPLL_CFG_CP_MASK);
	pll_ctrl_regval = pll_ctrl_regval |
		(d_cp << CRF_APB_DPLL_CFG_CP_SHIFT);
	Xil_Out32(CRF_APB_DPLL_CFG, pll_ctrl_regval);

	pll_ctrl_regval = Xil_In32(CRF_APB_DPLL_CFG);
	pll_ctrl_regval = pll_ctrl_regval & (~CRF_APB_DPLL_CFG_RES_MASK);
	pll_ctrl_regval = pll_ctrl_regval |
		(d_res << CRF_APB_DPLL_CFG_RES_SHIFT);
	Xil_Out32(CRF_APB_DPLL_CFG, pll_ctrl_regval);

	pll_ctrl_regval = Xil_In32(CRF_APB_DPLL_CTRL);
	pll_ctrl_regval = pll_ctrl_regval & (~CRF_APB_DPLL_CTRL_FBDIV_MASK);
	pll_ctrl_regval = pll_ctrl_regval |
		(ddr_pll_fbdiv << CRF_APB_DPLL_CTRL_FBDIV_SHIFT);
	Xil_Out32(CRF_APB_DPLL_CTRL, pll_ctrl_regval);

	/*Setting PLL BYPASS*/
	pll_ctrl_regval = Xil_In32(CRF_APB_DPLL_CTRL);
	pll_ctrl_regval = pll_ctrl_regval & (~CRF_APB_DPLL_CTRL_BYPASS_MASK);
	pll_ctrl_regval = pll_ctrl_regval |
		(1 << CRF_APB_DPLL_CTRL_BYPASS_SHIFT);
	Xil_Out32(CRF_APB_DPLL_CTRL, pll_ctrl_regval);

	/*Setting PLL RESET*/
	pll_ctrl_regval = Xil_In32(CRF_APB_DPLL_CTRL);
	pll_ctrl_regval = pll_ctrl_regval & (~CRF_APB_DPLL_CTRL_RESET_MASK);
	pll_ctrl_regval = pll_ctrl_regval |
		(1 << CRF_APB_DPLL_CTRL_RESET_SHIFT);
	Xil_Out32(CRF_APB_DPLL_CTRL, pll_ctrl_regval);

	/*Clearing PLL RESET*/
	pll_ctrl_regval = Xil_In32(CRF_APB_DPLL_CTRL);
	pll_ctrl_regval = pll_ctrl_regval & (~CRF_APB_DPLL_CTRL_RESET_MASK);
	pll_ctrl_regval = pll_ctrl_regval |
		(0 << CRF_APB_DPLL_CTRL_RESET_SHIFT);
	Xil_Out32(CRF_APB_DPLL_CTRL, pll_ctrl_regval);

	/*Checking PLL lock*/
	pll_status_regval = 0x00000000;
	while ((pll_status_regval & CRF_APB_PLL_STATUS_DPLL_LOCK_MASK) !=
		CRF_APB_PLL_STATUS_DPLL_LOCK_MASK)
		pll_status_regval = Xil_In32(CRF_APB_PLL_STATUS);




	/*Clearing PLL BYPASS*/
	pll_ctrl_regval = Xil_In32(CRF_APB_DPLL_CTRL);
	pll_ctrl_regval = pll_ctrl_regval & (~CRF_APB_DPLL_CTRL_BYPASS_MASK);
	pll_ctrl_regval = pll_ctrl_regval |
		(0 << CRF_APB_DPLL_CTRL_BYPASS_SHIFT);
	Xil_Out32(CRF_APB_DPLL_CTRL, pll_ctrl_regval);

}

/*Following SERDES programming sequences that a user need to follow to work
 * around the known limitation with SERDES. These sequences should done
 * before STEP 1 and STEP 2 as described in previous section. These
 * programming steps are *required for current silicon version and are
 * likely to undergo further changes with subsequent silicon versions.
 */


static int serdes_enb_coarse_saturation(void)
{
  /*Enable PLL Coarse Code saturation Logic*/
	Xil_Out32(0xFD402094, 0x00000010);
	Xil_Out32(0xFD406094, 0x00000010);
	Xil_Out32(0xFD40A094, 0x00000010);
	Xil_Out32(0xFD40E094, 0x00000010);
		return 1;
}

int serdes_fixcal_code(void)
{
	int MaskStatus = 1;

  unsigned int rdata = 0;

	/*The valid codes are from 0x26 to 0x3C.
	*There are 23 valid codes in total.
	*/
 /*Each element of array stands for count of occurence of valid code.*/
	unsigned int match_pmos_code[23];
	/*Each element of array stands for count of occurence of valid code.*/
	/*The valid codes are from 0xC to 0x12.
	*There are 7 valid codes in total.
	*/
	unsigned int match_nmos_code[23];
	/*Each element of array stands for count of occurence of valid code.*/
	/*The valid codes are from 0x6 to 0xC.
	* There are 7 valid codes in total.
	*/
	unsigned int match_ical_code[7];
	/*Each element of array stands for count of occurence of valid code.*/
	unsigned int match_rcal_code[7];

	unsigned int p_code = 0;
	unsigned int n_code = 0;
	unsigned int i_code = 0;
	unsigned int r_code = 0;
	unsigned int repeat_count = 0;
	unsigned int L3_TM_CALIB_DIG20 = 0;
	unsigned int L3_TM_CALIB_DIG19 = 0;
	unsigned int L3_TM_CALIB_DIG18 = 0;
	unsigned int L3_TM_CALIB_DIG16 = 0;
	unsigned int L3_TM_CALIB_DIG15 = 0;
	unsigned int L3_TM_CALIB_DIG14 = 0;

	int i = 0;

  rdata = Xil_In32(0XFD40289C);
  rdata = rdata & ~0x03;
  rdata = rdata | 0x1;
  Xil_Out32(0XFD40289C, rdata);
  // check supply good status before starting AFE sequencing
  int count = 0;
  do
  {
    if (count == PSU_MASK_POLL_TIME)
      break;
    rdata = Xil_In32(0xFD402B1C);
    count++;
  }while((rdata&0x0000000E) !=0x0000000E);

	for (i = 0; i < 23; i++) {
		match_pmos_code[i] = 0;
		match_nmos_code[i] = 0;
	}
	for (i = 0; i < 7; i++) {
		match_ical_code[i] = 0;
		match_rcal_code[i] = 0;
	}


	do {
	/*Clear ICM_CFG value*/
		Xil_Out32(0xFD410010, 0x00000000);
		Xil_Out32(0xFD410014, 0x00000000);

	/*Set ICM_CFG value*/
	/*This will trigger recalibration of all stages*/
	Xil_Out32(0xFD410010, 0x00000001);
	Xil_Out32(0xFD410014, 0x00000000);

	/*is calibration done? polling on L3_CALIB_DONE_STATUS*/
	MaskStatus = mask_poll(0xFD40EF14, 0x2);
	if (MaskStatus == 0) {
		/*failure here is because of calibration done timeout*/
		xil_printf("#SERDES initialization timed out\n\r");
		return MaskStatus;
	}

	p_code = mask_read(0xFD40EF18, 0xFFFFFFFF);/*PMOS code*/
	n_code = mask_read(0xFD40EF1C, 0xFFFFFFFF);/*NMOS code*/
	/*m_code = mask_read(0xFD40EF20, 0xFFFFFFFF)*/;/*MPHY code*/
	i_code = mask_read(0xFD40EF24, 0xFFFFFFFF);/*ICAL code*/
	r_code = mask_read(0xFD40EF28, 0xFFFFFFFF);/*RX code*/
	/*u_code = mask_read(0xFD40EF2C, 0xFFFFFFFF)*/;/*USB2 code*/

	/*PMOS code in acceptable range*/
	if ((p_code >= 0x26) && (p_code <= 0x3C))
		match_pmos_code[p_code - 0x26] += 1;

	/*NMOS code in acceptable range*/
	if ((n_code >= 0x26) && (n_code <= 0x3C))
		match_nmos_code[n_code - 0x26] += 1;

	/*PMOS code in acceptable range*/
	if ((i_code >= 0xC) && (i_code <= 0x12))
		match_ical_code[i_code - 0xC] += 1;

	/*NMOS code in acceptable range*/
	if ((r_code >= 0x6) && (r_code <= 0xC))
		match_rcal_code[r_code - 0x6] += 1;


	} while (repeat_count++ < 10);

	/*find the valid code which resulted in maximum times in 10 iterations*/
	for (i = 0; i < 23; i++) {
		if (match_pmos_code[i] >= match_pmos_code[0]) {
			match_pmos_code[0] = match_pmos_code[i];
			p_code = 0x26 + i;
		}
	if (match_nmos_code[i] >= match_nmos_code[0]) {
		match_nmos_code[0] = match_nmos_code[i];
		n_code = 0x26 + i;
		}
	}

	for (i = 0; i < 7; i++) {
		if (match_ical_code[i] >= match_ical_code[0]) {
			match_ical_code[0] = match_ical_code[i];
			i_code = 0xC + i;
		}
		if (match_rcal_code[i] >= match_rcal_code[0]) {
			match_rcal_code[0] = match_rcal_code[i];
			r_code = 0x6 + i;
		}
	}
	/*L3_TM_CALIB_DIG20[3] PSW MSB Override*/
	/*L3_TM_CALIB_DIG20[2:0]	PSW Code [4:2]*/
	L3_TM_CALIB_DIG20 = mask_read(0xFD40EC50, 0xFFFFFFF0);/*read DIG20*/
	L3_TM_CALIB_DIG20 = L3_TM_CALIB_DIG20 | 0x8 | ((p_code >> 2) & 0x7);


	/*L3_TM_CALIB_DIG19[7:6]	PSW Code [1:0]*/
	/*L3_TM_CALIB_DIG19[5]	PSW Override*/
	/*L3_TM_CALIB_DIG19[2]	NSW MSB Override*/
	/*L3_TM_CALIB_DIG19[1:0]	NSW Code [4:3]*/
	L3_TM_CALIB_DIG19 = mask_read(0xFD40EC4C, 0xFFFFFF18);/*read DIG19*/
	L3_TM_CALIB_DIG19 = L3_TM_CALIB_DIG19 | ((p_code & 0x3) << 6)
		| 0x20 | 0x4 | ((n_code >> 3) & 0x3);

	/*L3_TM_CALIB_DIG18[7:5]	NSW Code [2:0]*/
	/*L3_TM_CALIB_DIG18[4]	NSW Override*/
	L3_TM_CALIB_DIG18 = mask_read(0xFD40EC48, 0xFFFFFF0F);/*read DIG18*/
	L3_TM_CALIB_DIG18 = L3_TM_CALIB_DIG18 | ((n_code & 0x7) << 5) | 0x10;


	/*L3_TM_CALIB_DIG16[2:0]	RX Code [3:1]*/
	L3_TM_CALIB_DIG16 = mask_read(0xFD40EC40, 0xFFFFFFF8);/*read DIG16*/
	L3_TM_CALIB_DIG16 = L3_TM_CALIB_DIG16 | ((r_code >> 1) & 0x7);

	/*L3_TM_CALIB_DIG15[7]	RX Code [0]*/
	/*L3_TM_CALIB_DIG15[6]	RX CODE Override*/
	/*L3_TM_CALIB_DIG15[3]	ICAL MSB Override*/
	/*L3_TM_CALIB_DIG15[2:0]	ICAL Code [3:1]*/
	L3_TM_CALIB_DIG15 = mask_read(0xFD40EC3C, 0xFFFFFF30);/*read DIG15*/
	L3_TM_CALIB_DIG15 = L3_TM_CALIB_DIG15 | ((r_code & 0x1) << 7)
	| 0x40 | 0x8 | ((i_code >> 1) & 0x7);

	/*L3_TM_CALIB_DIG14[7]	ICAL Code [0]*/
	/*L3_TM_CALIB_DIG14[6]	ICAL Override*/
	L3_TM_CALIB_DIG14 = mask_read(0xFD40EC38, 0xFFFFFF3F);/*read DIG14*/
	L3_TM_CALIB_DIG14 = L3_TM_CALIB_DIG14 | ((i_code & 0x1) << 7) | 0x40;

	/*Forces the calibration values*/
	Xil_Out32(0xFD40EC50, L3_TM_CALIB_DIG20);
	Xil_Out32(0xFD40EC4C, L3_TM_CALIB_DIG19);
	Xil_Out32(0xFD40EC48, L3_TM_CALIB_DIG18);
	Xil_Out32(0xFD40EC40, L3_TM_CALIB_DIG16);
	Xil_Out32(0xFD40EC3C, L3_TM_CALIB_DIG15);
	Xil_Out32(0xFD40EC38, L3_TM_CALIB_DIG14);
	return MaskStatus;

}
static int init_serdes(void)
{
	int status = 1;

	status &=  psu_resetin_init_data();

	status &= serdes_fixcal_code();
	status &= serdes_enb_coarse_saturation();

	status &=  psu_serdes_init_data();
	status &=  psu_resetout_init_data();

	return status;
}


static void init_peripheral(void)
{
/*SMMU_REG Interrrupt Enable: Followig register need to be written all the time to properly catch SMMU messages.*/
	PSU_Mask_Write(0xFD5F0018, 0x8000001FU, 0x8000001FU);
}

static int psu_init_xppu_aper_ram(void)
{

	return 0;
}

int psu_lpd_protection(void)
{
	psu_init_xppu_aper_ram();
	return 0;
}

int psu_ddr_protection(void)
{
	psu_ddr_xmpu0_data();
	psu_ddr_xmpu1_data();
	psu_ddr_xmpu2_data();
	psu_ddr_xmpu3_data();
	psu_ddr_xmpu4_data();
	psu_ddr_xmpu5_data();
	return 0;
}
int psu_ocm_protection(void)
{
	psu_ocm_xmpu_data();
	return 0;
}

int psu_fpd_protection(void)
{
	psu_fpd_xmpu_data();
	return 0;
}

int psu_protection_lock(void)
{
	psu_protection_lock_data();
	return 0;
}

int psu_protection(void)
{
	psu_apply_master_tz();
	psu_ddr_protection();
	psu_ocm_protection();
	psu_fpd_protection();
	psu_lpd_protection();
	return 0;
}

int
psu_init(void)
{
	int status = 1;

	status &= psu_mio_init_data();
	status &=   psu_pll_init_data();
	status &=   psu_clock_init_data();
	status &=  psu_ddr_init_data();
	status &=  psu_ddr_phybringup_data();
	status &=  psu_peripherals_init_data();
	status &=  init_serdes();
	init_peripheral();

	status &=  psu_peripherals_powerdwn_data();
	status &=    psu_afi_config();
	psu_ddr_qos_init_data();

	if (status == 0)
		return 1;
	return 0;
}
