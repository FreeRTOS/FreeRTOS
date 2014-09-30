/*******************************************************************************
*                                                                              *
* Copyright 2013 Altera Corporation. All Rights Reserved.                      *
*                                                                              *
* Redistribution and use in source and binary forms, with or without           *
* modification, are permitted provided that the following conditions are met:  *
*                                                                              *
* 1. Redistributions of source code must retain the above copyright notice,    *
*    this list of conditions and the following disclaimer.                     *
*                                                                              *
* 2. Redistributions in binary form must reproduce the above copyright notice, *
*    this list of conditions and the following disclaimer in the documentation *
*    and/or other materials provided with the distribution.                    *
*                                                                              *
* 3. The name of the author may not be used to endorse or promote products     *
*    derived from this software without specific prior written permission.     *
*                                                                              *
* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDER "AS IS" AND ANY EXPRESS OR *
* IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF *
* MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE, ARE DISCLAIMED. IN NO  *
* EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,       *
* SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, *
* PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS;  *
* OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,     *
* WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR      *
* OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF       *
* ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.                                   *
*                                                                              *
*******************************************************************************/

/* Altera - hps */

#ifndef __ALTERA_HPS_H__
#define __ALTERA_HPS_H__

#ifdef __cplusplus
extern "C"
{
#endif  /* __cplusplus */

#define ALT_HPS_ADDR        0
/*
 * Address Space : ALT_HPS
 * 
 */
/*
 * Component Instance : stm
 * 
 * Instance stm of component ALT_STM.
 * 
 * 
 */
/* The address of the ALT_STM_REG register for the ALT_STM instance. */
#define ALT_STM_REG_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_STM_ADDR) + ALT_STM_REG_OFST))
/* The base address byte offset for the start of the ALT_STM component. */
#define ALT_STM_OFST        0xfc000000
/* The start address of the ALT_STM component. */
#define ALT_STM_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_HPS_ADDR) + ALT_STM_OFST))
/* The lower bound address range of the ALT_STM component. */
#define ALT_STM_LB_ADDR     ALT_STM_ADDR
/* The upper bound address range of the ALT_STM component. */
#define ALT_STM_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_STM_ADDR) + 0x4) - 1))


/*
 * Component Instance : dap
 * 
 * Instance dap of component ALT_DAP.
 * 
 * 
 */
/* The address of the ALT_DAP_REG register for the ALT_DAP instance. */
#define ALT_DAP_REG_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_DAP_ADDR) + ALT_DAP_REG_OFST))
/* The base address byte offset for the start of the ALT_DAP component. */
#define ALT_DAP_OFST        0xff000000
/* The start address of the ALT_DAP component. */
#define ALT_DAP_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_HPS_ADDR) + ALT_DAP_OFST))
/* The lower bound address range of the ALT_DAP component. */
#define ALT_DAP_LB_ADDR     ALT_DAP_ADDR
/* The upper bound address range of the ALT_DAP component. */
#define ALT_DAP_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_DAP_ADDR) + 0x4) - 1))


/*
 * Component Instance : lwfpgaslaves
 * 
 * Instance lwfpgaslaves of component ALT_LWFPGASLVS.
 * 
 * 
 */
/* The base address byte offset for the start of the ALT_LWFPGASLVS component. */
#define ALT_LWFPGASLVS_OFST        0xff200000
/* The start address of the ALT_LWFPGASLVS component. */
#define ALT_LWFPGASLVS_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_HPS_ADDR) + ALT_LWFPGASLVS_OFST))
/* The lower bound address range of the ALT_LWFPGASLVS component. */
#define ALT_LWFPGASLVS_LB_ADDR     ALT_LWFPGASLVS_ADDR
/* The upper bound address range of the ALT_LWFPGASLVS component. */
#define ALT_LWFPGASLVS_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_LWFPGASLVS_ADDR) + 0x200000) - 1))


/*
 * Component Instance : lwhps2fpgaregs
 * 
 * Instance lwhps2fpgaregs of component ALT_LWH2F.
 * 
 * 
 */
/*
 * Register Group Instance : idgrp
 * 
 * Instance idgrp of register group ALT_LWH2F_ID.
 * 
 * 
 */
/* The address of the ALT_LWH2F_ID_PERIPH_ID_4 register for the ALT_LWH2F_ID instance. */
#define ALT_LWH2F_ID_PERIPH_ID_4_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_LWH2F_ID_ADDR) + ALT_LWH2F_ID_PERIPH_ID_4_OFST))
/* The address of the ALT_LWH2F_ID_PERIPH_ID_0 register for the ALT_LWH2F_ID instance. */
#define ALT_LWH2F_ID_PERIPH_ID_0_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_LWH2F_ID_ADDR) + ALT_LWH2F_ID_PERIPH_ID_0_OFST))
/* The address of the ALT_LWH2F_ID_PERIPH_ID_1 register for the ALT_LWH2F_ID instance. */
#define ALT_LWH2F_ID_PERIPH_ID_1_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_LWH2F_ID_ADDR) + ALT_LWH2F_ID_PERIPH_ID_1_OFST))
/* The address of the ALT_LWH2F_ID_PERIPH_ID_2 register for the ALT_LWH2F_ID instance. */
#define ALT_LWH2F_ID_PERIPH_ID_2_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_LWH2F_ID_ADDR) + ALT_LWH2F_ID_PERIPH_ID_2_OFST))
/* The address of the ALT_LWH2F_ID_PERIPH_ID_3 register for the ALT_LWH2F_ID instance. */
#define ALT_LWH2F_ID_PERIPH_ID_3_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_LWH2F_ID_ADDR) + ALT_LWH2F_ID_PERIPH_ID_3_OFST))
/* The address of the ALT_LWH2F_ID_COMP_ID_0 register for the ALT_LWH2F_ID instance. */
#define ALT_LWH2F_ID_COMP_ID_0_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_LWH2F_ID_ADDR) + ALT_LWH2F_ID_COMP_ID_0_OFST))
/* The address of the ALT_LWH2F_ID_COMP_ID_1 register for the ALT_LWH2F_ID instance. */
#define ALT_LWH2F_ID_COMP_ID_1_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_LWH2F_ID_ADDR) + ALT_LWH2F_ID_COMP_ID_1_OFST))
/* The address of the ALT_LWH2F_ID_COMP_ID_2 register for the ALT_LWH2F_ID instance. */
#define ALT_LWH2F_ID_COMP_ID_2_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_LWH2F_ID_ADDR) + ALT_LWH2F_ID_COMP_ID_2_OFST))
/* The address of the ALT_LWH2F_ID_COMP_ID_3 register for the ALT_LWH2F_ID instance. */
#define ALT_LWH2F_ID_COMP_ID_3_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_LWH2F_ID_ADDR) + ALT_LWH2F_ID_COMP_ID_3_OFST))
/* The base address byte offset for the start of the ALT_LWH2F_ID component. */
#define ALT_LWH2F_ID_OFST        0x1000
/* The start address of the ALT_LWH2F_ID component. */
#define ALT_LWH2F_ID_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_LWH2F_ADDR) + ALT_LWH2F_ID_OFST))
/* The lower bound address range of the ALT_LWH2F_ID component. */
#define ALT_LWH2F_ID_LB_ADDR     ALT_LWH2F_ID_ADDR
/* The upper bound address range of the ALT_LWH2F_ID component. */
#define ALT_LWH2F_ID_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_LWH2F_ID_ADDR) + 0x1000) - 1))


/*
 * Register Group Instance : mastergrp
 * 
 * Instance mastergrp of register group ALT_LWH2F_MST.
 * 
 * 
 */
/*
 * Register Group Instance : mastergrp_fpga2hpsregs
 * 
 * Instance mastergrp_fpga2hpsregs of register group ALT_LWH2F_MST_F2H.
 * 
 * 
 */
/* The address of the ALT_LWH2F_FN_MOD_BM_ISS register for the ALT_LWH2F_MST_MST_F2H instance. */
#define ALT_LWH2F_MST_MST_F2H_FN_MOD_BM_ISS_ADDR  ALT_LWH2F_FN_MOD_BM_ISS_ADDR(ALT_LWH2F_MST_MST_F2H_ADDR)
/* The address of the ALT_LWH2F_AHB_CNTL register for the ALT_LWH2F_MST_MST_F2H instance. */
#define ALT_LWH2F_MST_MST_F2H_AHB_CNTL_ADDR  ALT_LWH2F_AHB_CNTL_ADDR(ALT_LWH2F_MST_MST_F2H_ADDR)
/* The base address byte offset for the start of the ALT_LWH2F_MST_MST_F2H component. */
#define ALT_LWH2F_MST_MST_F2H_OFST        0x0
/* The start address of the ALT_LWH2F_MST_MST_F2H component. */
#define ALT_LWH2F_MST_MST_F2H_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_LWH2F_MST_ADDR) + ALT_LWH2F_MST_MST_F2H_OFST))
/* The lower bound address range of the ALT_LWH2F_MST_MST_F2H component. */
#define ALT_LWH2F_MST_MST_F2H_LB_ADDR     ALT_LWH2F_MST_MST_F2H_ADDR
/* The upper bound address range of the ALT_LWH2F_MST_MST_F2H component. */
#define ALT_LWH2F_MST_MST_F2H_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_LWH2F_MST_MST_F2H_ADDR) + 0x48) - 1))


/*
 * Register Group Instance : mastergrp_hps2fpgaregs
 * 
 * Instance mastergrp_hps2fpgaregs of register group ALT_LWH2F_MST_H2F.
 * 
 * 
 */
/* The address of the ALT_LWH2F_FN_MOD_BM_ISS register for the ALT_LWH2F_MST_MST_H2F instance. */
#define ALT_LWH2F_MST_MST_H2F_FN_MOD_BM_ISS_ADDR  ALT_LWH2F_FN_MOD_BM_ISS_ADDR(ALT_LWH2F_MST_MST_H2F_ADDR)
/* The address of the ALT_LWH2F_AHB_CNTL register for the ALT_LWH2F_MST_MST_H2F instance. */
#define ALT_LWH2F_MST_MST_H2F_AHB_CNTL_ADDR  ALT_LWH2F_AHB_CNTL_ADDR(ALT_LWH2F_MST_MST_H2F_ADDR)
/* The base address byte offset for the start of the ALT_LWH2F_MST_MST_H2F component. */
#define ALT_LWH2F_MST_MST_H2F_OFST        0x1000
/* The start address of the ALT_LWH2F_MST_MST_H2F component. */
#define ALT_LWH2F_MST_MST_H2F_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_LWH2F_MST_ADDR) + ALT_LWH2F_MST_MST_H2F_OFST))
/* The lower bound address range of the ALT_LWH2F_MST_MST_H2F component. */
#define ALT_LWH2F_MST_MST_H2F_LB_ADDR     ALT_LWH2F_MST_MST_H2F_ADDR
/* The upper bound address range of the ALT_LWH2F_MST_MST_H2F component. */
#define ALT_LWH2F_MST_MST_H2F_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_LWH2F_MST_MST_H2F_ADDR) + 0x48) - 1))


/*
 * Register Group Instance : mastergrp_b32
 * 
 * Instance mastergrp_b32 of register group ALT_LWH2F_MST_B32.
 * 
 * 
 */
/* The address of the ALT_LWH2F_FN_MOD_BM_ISS register for the ALT_LWH2F_MST_MST_B32 instance. */
#define ALT_LWH2F_MST_MST_B32_FN_MOD_BM_ISS_ADDR  ALT_LWH2F_FN_MOD_BM_ISS_ADDR(ALT_LWH2F_MST_MST_B32_ADDR)
/* The address of the ALT_LWH2F_WR_TIDEMARK register for the ALT_LWH2F_MST_MST_B32 instance. */
#define ALT_LWH2F_MST_MST_B32_WR_TIDEMARK_ADDR  ALT_LWH2F_WR_TIDEMARK_ADDR(ALT_LWH2F_MST_MST_B32_ADDR)
/* The address of the ALT_LWH2F_FN_MOD register for the ALT_LWH2F_MST_MST_B32 instance. */
#define ALT_LWH2F_MST_MST_B32_FN_MOD_ADDR  ALT_LWH2F_FN_MOD_ADDR(ALT_LWH2F_MST_MST_B32_ADDR)
/* The base address byte offset for the start of the ALT_LWH2F_MST_MST_B32 component. */
#define ALT_LWH2F_MST_MST_B32_OFST        0x3000
/* The start address of the ALT_LWH2F_MST_MST_B32 component. */
#define ALT_LWH2F_MST_MST_B32_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_LWH2F_MST_ADDR) + ALT_LWH2F_MST_MST_B32_OFST))
/* The lower bound address range of the ALT_LWH2F_MST_MST_B32 component. */
#define ALT_LWH2F_MST_MST_B32_LB_ADDR     ALT_LWH2F_MST_MST_B32_ADDR
/* The upper bound address range of the ALT_LWH2F_MST_MST_B32 component. */
#define ALT_LWH2F_MST_MST_B32_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_LWH2F_MST_MST_B32_ADDR) + 0x10c) - 1))


/* The base address byte offset for the start of the ALT_LWH2F_MST component. */
#define ALT_LWH2F_MST_OFST        0x2000
/* The start address of the ALT_LWH2F_MST component. */
#define ALT_LWH2F_MST_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_LWH2F_ADDR) + ALT_LWH2F_MST_OFST))
/* The lower bound address range of the ALT_LWH2F_MST component. */
#define ALT_LWH2F_MST_LB_ADDR     ALT_LWH2F_MST_ADDR
/* The upper bound address range of the ALT_LWH2F_MST component. */
#define ALT_LWH2F_MST_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_LWH2F_MST_ADDR) + 0x310c) - 1))


/*
 * Register Group Instance : slavegrp
 * 
 * Instance slavegrp of register group ALT_LWH2F_SLV.
 * 
 * 
 */
/*
 * Register Group Instance : slavegrp_b32
 * 
 * Instance slavegrp_b32 of register group ALT_LWH2F_SLV_B32.
 * 
 * 
 */
/* The address of the ALT_LWH2F_FN_MOD register for the ALT_LWH2F_SLV_SLV_B32 instance. */
#define ALT_LWH2F_SLV_SLV_B32_FN_MOD_ADDR  ALT_LWH2F_FN_MOD_ADDR(ALT_LWH2F_SLV_SLV_B32_ADDR)
/* The base address byte offset for the start of the ALT_LWH2F_SLV_SLV_B32 component. */
#define ALT_LWH2F_SLV_SLV_B32_OFST        0x3000
/* The start address of the ALT_LWH2F_SLV_SLV_B32 component. */
#define ALT_LWH2F_SLV_SLV_B32_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_LWH2F_SLV_ADDR) + ALT_LWH2F_SLV_SLV_B32_OFST))
/* The lower bound address range of the ALT_LWH2F_SLV_SLV_B32 component. */
#define ALT_LWH2F_SLV_SLV_B32_LB_ADDR     ALT_LWH2F_SLV_SLV_B32_ADDR
/* The upper bound address range of the ALT_LWH2F_SLV_SLV_B32 component. */
#define ALT_LWH2F_SLV_SLV_B32_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_LWH2F_SLV_SLV_B32_ADDR) + 0x10c) - 1))


/* The base address byte offset for the start of the ALT_LWH2F_SLV component. */
#define ALT_LWH2F_SLV_OFST        0x42000
/* The start address of the ALT_LWH2F_SLV component. */
#define ALT_LWH2F_SLV_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_LWH2F_ADDR) + ALT_LWH2F_SLV_OFST))
/* The lower bound address range of the ALT_LWH2F_SLV component. */
#define ALT_LWH2F_SLV_LB_ADDR     ALT_LWH2F_SLV_ADDR
/* The upper bound address range of the ALT_LWH2F_SLV component. */
#define ALT_LWH2F_SLV_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_LWH2F_SLV_ADDR) + 0x310c) - 1))


/* The base address byte offset for the start of the ALT_LWH2F component. */
#define ALT_LWH2F_OFST        0xff400000
/* The start address of the ALT_LWH2F component. */
#define ALT_LWH2F_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_HPS_ADDR) + ALT_LWH2F_OFST))
/* The lower bound address range of the ALT_LWH2F component. */
#define ALT_LWH2F_LB_ADDR     ALT_LWH2F_ADDR
/* The upper bound address range of the ALT_LWH2F component. */
#define ALT_LWH2F_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_LWH2F_ADDR) + 0x80000) - 1))


/*
 * Component Instance : hps2fpgaregs
 * 
 * Instance hps2fpgaregs of component ALT_H2F.
 * 
 * 
 */
/*
 * Register Group Instance : idgrp
 * 
 * Instance idgrp of register group ALT_H2F_IDGRP.
 * 
 * 
 */
/* The address of the ALT_H2F_ID_PERIPH_ID_4 register for the ALT_H2F_IDGRP instance. */
#define ALT_H2F_ID_PERIPH_ID_4_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_H2F_IDGRP_ADDR) + ALT_H2F_ID_PERIPH_ID_4_OFST))
/* The address of the ALT_H2F_ID_PERIPH_ID_0 register for the ALT_H2F_IDGRP instance. */
#define ALT_H2F_ID_PERIPH_ID_0_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_H2F_IDGRP_ADDR) + ALT_H2F_ID_PERIPH_ID_0_OFST))
/* The address of the ALT_H2F_ID_PERIPH_ID_1 register for the ALT_H2F_IDGRP instance. */
#define ALT_H2F_ID_PERIPH_ID_1_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_H2F_IDGRP_ADDR) + ALT_H2F_ID_PERIPH_ID_1_OFST))
/* The address of the ALT_H2F_ID_PERIPH_ID_2 register for the ALT_H2F_IDGRP instance. */
#define ALT_H2F_ID_PERIPH_ID_2_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_H2F_IDGRP_ADDR) + ALT_H2F_ID_PERIPH_ID_2_OFST))
/* The address of the ALT_H2F_ID_PERIPH_ID_3 register for the ALT_H2F_IDGRP instance. */
#define ALT_H2F_ID_PERIPH_ID_3_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_H2F_IDGRP_ADDR) + ALT_H2F_ID_PERIPH_ID_3_OFST))
/* The address of the ALT_H2F_ID_COMP_ID_0 register for the ALT_H2F_IDGRP instance. */
#define ALT_H2F_ID_COMP_ID_0_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_H2F_IDGRP_ADDR) + ALT_H2F_ID_COMP_ID_0_OFST))
/* The address of the ALT_H2F_ID_COMP_ID_1 register for the ALT_H2F_IDGRP instance. */
#define ALT_H2F_ID_COMP_ID_1_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_H2F_IDGRP_ADDR) + ALT_H2F_ID_COMP_ID_1_OFST))
/* The address of the ALT_H2F_ID_COMP_ID_2 register for the ALT_H2F_IDGRP instance. */
#define ALT_H2F_ID_COMP_ID_2_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_H2F_IDGRP_ADDR) + ALT_H2F_ID_COMP_ID_2_OFST))
/* The address of the ALT_H2F_ID_COMP_ID_3 register for the ALT_H2F_IDGRP instance. */
#define ALT_H2F_ID_COMP_ID_3_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_H2F_IDGRP_ADDR) + ALT_H2F_ID_COMP_ID_3_OFST))
/* The base address byte offset for the start of the ALT_H2F_IDGRP component. */
#define ALT_H2F_IDGRP_OFST        0x1000
/* The start address of the ALT_H2F_IDGRP component. */
#define ALT_H2F_IDGRP_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_H2F_ADDR) + ALT_H2F_IDGRP_OFST))
/* The lower bound address range of the ALT_H2F_IDGRP component. */
#define ALT_H2F_IDGRP_LB_ADDR     ALT_H2F_IDGRP_ADDR
/* The upper bound address range of the ALT_H2F_IDGRP component. */
#define ALT_H2F_IDGRP_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_H2F_IDGRP_ADDR) + 0x1000) - 1))


/*
 * Register Group Instance : mastergrp
 * 
 * Instance mastergrp of register group ALT_H2F_MSTGRP.
 * 
 * 
 */
/*
 * Register Group Instance : mastergrp_b32
 * 
 * Instance mastergrp_b32 of register group ALT_H2F_MST_B32.
 * 
 * 
 */
/* The address of the ALT_H2F_FN_MOD2 register for the ALT_H2F_MST_MST_B32 instance. */
#define ALT_H2F_MST_MST_B32_FN_MOD2_ADDR  ALT_H2F_FN_MOD2_ADDR(ALT_H2F_MST_MST_B32_ADDR)
/* The address of the ALT_H2F_FN_MOD register for the ALT_H2F_MST_MST_B32 instance. */
#define ALT_H2F_MST_MST_B32_FN_MOD_ADDR  ALT_H2F_FN_MOD_ADDR(ALT_H2F_MST_MST_B32_ADDR)
/* The base address byte offset for the start of the ALT_H2F_MST_MST_B32 component. */
#define ALT_H2F_MST_MST_B32_OFST        0x0
/* The start address of the ALT_H2F_MST_MST_B32 component. */
#define ALT_H2F_MST_MST_B32_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_H2F_MSTGRP_ADDR) + ALT_H2F_MST_MST_B32_OFST))
/* The lower bound address range of the ALT_H2F_MST_MST_B32 component. */
#define ALT_H2F_MST_MST_B32_LB_ADDR     ALT_H2F_MST_MST_B32_ADDR
/* The upper bound address range of the ALT_H2F_MST_MST_B32 component. */
#define ALT_H2F_MST_MST_B32_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_H2F_MST_MST_B32_ADDR) + 0x10c) - 1))


/*
 * Register Group Instance : mastergrp_b128
 * 
 * Instance mastergrp_b128 of register group ALT_H2F_MST_B128.
 * 
 * 
 */
/* The address of the ALT_H2F_FN_MOD2 register for the ALT_H2F_MST_MST_B128 instance. */
#define ALT_H2F_MST_MST_B128_FN_MOD2_ADDR  ALT_H2F_FN_MOD2_ADDR(ALT_H2F_MST_MST_B128_ADDR)
/* The address of the ALT_H2F_FN_MOD register for the ALT_H2F_MST_MST_B128 instance. */
#define ALT_H2F_MST_MST_B128_FN_MOD_ADDR  ALT_H2F_FN_MOD_ADDR(ALT_H2F_MST_MST_B128_ADDR)
/* The base address byte offset for the start of the ALT_H2F_MST_MST_B128 component. */
#define ALT_H2F_MST_MST_B128_OFST        0x2000
/* The start address of the ALT_H2F_MST_MST_B128 component. */
#define ALT_H2F_MST_MST_B128_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_H2F_MSTGRP_ADDR) + ALT_H2F_MST_MST_B128_OFST))
/* The lower bound address range of the ALT_H2F_MST_MST_B128 component. */
#define ALT_H2F_MST_MST_B128_LB_ADDR     ALT_H2F_MST_MST_B128_ADDR
/* The upper bound address range of the ALT_H2F_MST_MST_B128 component. */
#define ALT_H2F_MST_MST_B128_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_H2F_MST_MST_B128_ADDR) + 0x10c) - 1))


/* The base address byte offset for the start of the ALT_H2F_MSTGRP component. */
#define ALT_H2F_MSTGRP_OFST        0x2000
/* The start address of the ALT_H2F_MSTGRP component. */
#define ALT_H2F_MSTGRP_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_H2F_ADDR) + ALT_H2F_MSTGRP_OFST))
/* The lower bound address range of the ALT_H2F_MSTGRP component. */
#define ALT_H2F_MSTGRP_LB_ADDR     ALT_H2F_MSTGRP_ADDR
/* The upper bound address range of the ALT_H2F_MSTGRP component. */
#define ALT_H2F_MSTGRP_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_H2F_MSTGRP_ADDR) + 0x210c) - 1))


/* The base address byte offset for the start of the ALT_H2F component. */
#define ALT_H2F_OFST        0xff500000
/* The start address of the ALT_H2F component. */
#define ALT_H2F_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_HPS_ADDR) + ALT_H2F_OFST))
/* The lower bound address range of the ALT_H2F component. */
#define ALT_H2F_LB_ADDR     ALT_H2F_ADDR
/* The upper bound address range of the ALT_H2F component. */
#define ALT_H2F_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_H2F_ADDR) + 0x8000) - 1))


/*
 * Component Instance : fpga2hpsregs
 * 
 * Instance fpga2hpsregs of component ALT_F2H.
 * 
 * 
 */
/*
 * Register Group Instance : idgrp
 * 
 * Instance idgrp of register group ALT_F2H_IDGRP.
 * 
 * 
 */
/* The address of the ALT_F2H_ID_PERIPH_ID_4 register for the ALT_F2H_IDGRP instance. */
#define ALT_F2H_ID_PERIPH_ID_4_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_F2H_IDGRP_ADDR) + ALT_F2H_ID_PERIPH_ID_4_OFST))
/* The address of the ALT_F2H_ID_PERIPH_ID_0 register for the ALT_F2H_IDGRP instance. */
#define ALT_F2H_ID_PERIPH_ID_0_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_F2H_IDGRP_ADDR) + ALT_F2H_ID_PERIPH_ID_0_OFST))
/* The address of the ALT_F2H_ID_PERIPH_ID_1 register for the ALT_F2H_IDGRP instance. */
#define ALT_F2H_ID_PERIPH_ID_1_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_F2H_IDGRP_ADDR) + ALT_F2H_ID_PERIPH_ID_1_OFST))
/* The address of the ALT_F2H_ID_PERIPH_ID_2 register for the ALT_F2H_IDGRP instance. */
#define ALT_F2H_ID_PERIPH_ID_2_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_F2H_IDGRP_ADDR) + ALT_F2H_ID_PERIPH_ID_2_OFST))
/* The address of the ALT_F2H_ID_PERIPH_ID_3 register for the ALT_F2H_IDGRP instance. */
#define ALT_F2H_ID_PERIPH_ID_3_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_F2H_IDGRP_ADDR) + ALT_F2H_ID_PERIPH_ID_3_OFST))
/* The address of the ALT_F2H_ID_COMP_ID_0 register for the ALT_F2H_IDGRP instance. */
#define ALT_F2H_ID_COMP_ID_0_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_F2H_IDGRP_ADDR) + ALT_F2H_ID_COMP_ID_0_OFST))
/* The address of the ALT_F2H_ID_COMP_ID_1 register for the ALT_F2H_IDGRP instance. */
#define ALT_F2H_ID_COMP_ID_1_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_F2H_IDGRP_ADDR) + ALT_F2H_ID_COMP_ID_1_OFST))
/* The address of the ALT_F2H_ID_COMP_ID_2 register for the ALT_F2H_IDGRP instance. */
#define ALT_F2H_ID_COMP_ID_2_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_F2H_IDGRP_ADDR) + ALT_F2H_ID_COMP_ID_2_OFST))
/* The address of the ALT_F2H_ID_COMP_ID_3 register for the ALT_F2H_IDGRP instance. */
#define ALT_F2H_ID_COMP_ID_3_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_F2H_IDGRP_ADDR) + ALT_F2H_ID_COMP_ID_3_OFST))
/* The base address byte offset for the start of the ALT_F2H_IDGRP component. */
#define ALT_F2H_IDGRP_OFST        0x1000
/* The start address of the ALT_F2H_IDGRP component. */
#define ALT_F2H_IDGRP_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_F2H_ADDR) + ALT_F2H_IDGRP_OFST))
/* The lower bound address range of the ALT_F2H_IDGRP component. */
#define ALT_F2H_IDGRP_LB_ADDR     ALT_F2H_IDGRP_ADDR
/* The upper bound address range of the ALT_F2H_IDGRP component. */
#define ALT_F2H_IDGRP_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_F2H_IDGRP_ADDR) + 0x1000) - 1))


/*
 * Register Group Instance : slavegrp
 * 
 * Instance slavegrp of register group ALT_F2H_SLVGRP.
 * 
 * 
 */
/*
 * Register Group Instance : slavegrp_b32
 * 
 * Instance slavegrp_b32 of register group ALT_F2H_SLV_B32.
 * 
 * 
 */
/* The address of the ALT_F2H_FN_MOD2 register for the ALT_F2H_SLV_SLV_B32 instance. */
#define ALT_F2H_SLV_SLV_B32_FN_MOD2_ADDR  ALT_F2H_FN_MOD2_ADDR(ALT_F2H_SLV_SLV_B32_ADDR)
/* The address of the ALT_F2H_FN_MOD register for the ALT_F2H_SLV_SLV_B32 instance. */
#define ALT_F2H_SLV_SLV_B32_FN_MOD_ADDR  ALT_F2H_FN_MOD_ADDR(ALT_F2H_SLV_SLV_B32_ADDR)
/* The base address byte offset for the start of the ALT_F2H_SLV_SLV_B32 component. */
#define ALT_F2H_SLV_SLV_B32_OFST        0x0
/* The start address of the ALT_F2H_SLV_SLV_B32 component. */
#define ALT_F2H_SLV_SLV_B32_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_F2H_SLVGRP_ADDR) + ALT_F2H_SLV_SLV_B32_OFST))
/* The lower bound address range of the ALT_F2H_SLV_SLV_B32 component. */
#define ALT_F2H_SLV_SLV_B32_LB_ADDR     ALT_F2H_SLV_SLV_B32_ADDR
/* The upper bound address range of the ALT_F2H_SLV_SLV_B32 component. */
#define ALT_F2H_SLV_SLV_B32_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_F2H_SLV_SLV_B32_ADDR) + 0x10c) - 1))


/*
 * Register Group Instance : slavegrp_b128
 * 
 * Instance slavegrp_b128 of register group ALT_F2H_SLV_B128.
 * 
 * 
 */
/* The address of the ALT_F2H_FN_MOD2 register for the ALT_F2H_SLV_SLV_B128 instance. */
#define ALT_F2H_SLV_SLV_B128_FN_MOD2_ADDR  ALT_F2H_FN_MOD2_ADDR(ALT_F2H_SLV_SLV_B128_ADDR)
/* The address of the ALT_F2H_FN_MOD register for the ALT_F2H_SLV_SLV_B128 instance. */
#define ALT_F2H_SLV_SLV_B128_FN_MOD_ADDR  ALT_F2H_FN_MOD_ADDR(ALT_F2H_SLV_SLV_B128_ADDR)
/* The base address byte offset for the start of the ALT_F2H_SLV_SLV_B128 component. */
#define ALT_F2H_SLV_SLV_B128_OFST        0x2000
/* The start address of the ALT_F2H_SLV_SLV_B128 component. */
#define ALT_F2H_SLV_SLV_B128_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_F2H_SLVGRP_ADDR) + ALT_F2H_SLV_SLV_B128_OFST))
/* The lower bound address range of the ALT_F2H_SLV_SLV_B128 component. */
#define ALT_F2H_SLV_SLV_B128_LB_ADDR     ALT_F2H_SLV_SLV_B128_ADDR
/* The upper bound address range of the ALT_F2H_SLV_SLV_B128 component. */
#define ALT_F2H_SLV_SLV_B128_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_F2H_SLV_SLV_B128_ADDR) + 0x10c) - 1))


/* The base address byte offset for the start of the ALT_F2H_SLVGRP component. */
#define ALT_F2H_SLVGRP_OFST        0x42000
/* The start address of the ALT_F2H_SLVGRP component. */
#define ALT_F2H_SLVGRP_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_F2H_ADDR) + ALT_F2H_SLVGRP_OFST))
/* The lower bound address range of the ALT_F2H_SLVGRP component. */
#define ALT_F2H_SLVGRP_LB_ADDR     ALT_F2H_SLVGRP_ADDR
/* The upper bound address range of the ALT_F2H_SLVGRP component. */
#define ALT_F2H_SLVGRP_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_F2H_SLVGRP_ADDR) + 0x210c) - 1))


/* The base address byte offset for the start of the ALT_F2H component. */
#define ALT_F2H_OFST        0xff600000
/* The start address of the ALT_F2H component. */
#define ALT_F2H_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_HPS_ADDR) + ALT_F2H_OFST))
/* The lower bound address range of the ALT_F2H component. */
#define ALT_F2H_LB_ADDR     ALT_F2H_ADDR
/* The upper bound address range of the ALT_F2H component. */
#define ALT_F2H_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_F2H_ADDR) + 0x80000) - 1))


/*
 * Component Instance : emac0
 * 
 * Instance emac0 of component ALT_EMAC.
 * 
 * 
 */
/*
 * Register Group Instance : gmacgrp
 * 
 * Instance gmacgrp of register group ALT_EMAC_GMAC.
 * 
 * 
 */
/* The address of the ALT_EMAC_GMAC_MAC_CFG register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_CFG_ADDR  ALT_EMAC_GMAC_MAC_CFG_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_FRM_FLT register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_FRM_FLT_ADDR  ALT_EMAC_GMAC_MAC_FRM_FLT_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_GMII_ADDR register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_GMII_ADDR_ADDR  ALT_EMAC_GMAC_GMII_ADDR_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_GMII_DATA register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_GMII_DATA_ADDR  ALT_EMAC_GMAC_GMII_DATA_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_FLOW_CTL register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_FLOW_CTL_ADDR  ALT_EMAC_GMAC_FLOW_CTL_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_VLAN_TAG register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_VLAN_TAG_ADDR  ALT_EMAC_GMAC_VLAN_TAG_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_VER register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_VER_ADDR  ALT_EMAC_GMAC_VER_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_DBG register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_DBG_ADDR  ALT_EMAC_GMAC_DBG_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_LPI_CTL_STAT register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_LPI_CTL_STAT_ADDR  ALT_EMAC_GMAC_LPI_CTL_STAT_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_LPI_TMRS_CTL register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_LPI_TMRS_CTL_ADDR  ALT_EMAC_GMAC_LPI_TMRS_CTL_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_INT_STAT register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_INT_STAT_ADDR  ALT_EMAC_GMAC_INT_STAT_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_INT_MSK register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_INT_MSK_ADDR  ALT_EMAC_GMAC_INT_MSK_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR0_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR0_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR0_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR0_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR0_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR0_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR1_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR1_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR1_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR1_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR1_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR1_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR2_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR2_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR2_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR2_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR2_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR2_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR3_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR3_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR3_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR3_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR3_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR3_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR4_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR4_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR4_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR4_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR4_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR4_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR5_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR5_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR5_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR5_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR5_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR5_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR6_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR6_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR6_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR6_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR6_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR6_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR7_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR7_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR7_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR7_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR7_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR7_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR8_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR8_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR8_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR8_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR8_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR8_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR9_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR9_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR9_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR9_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR9_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR9_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR10_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR10_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR10_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR10_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR10_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR10_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR11_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR11_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR11_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR11_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR11_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR11_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR12_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR12_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR12_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR12_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR12_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR12_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR13_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR13_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR13_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR13_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR13_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR13_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR14_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR14_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR14_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR14_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR14_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR14_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR15_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR15_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR15_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR15_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR15_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR15_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MII_CTL_STAT register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_SGMII_RGMII_SMII_CTL_STAT_ADDR  ALT_EMAC_GMAC_MII_CTL_STAT_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MMC_CTL register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MMC_CTL_ADDR  ALT_EMAC_GMAC_MMC_CTL_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MMC_RX_INT register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MMC_RX_INT_ADDR  ALT_EMAC_GMAC_MMC_RX_INT_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MMC_TX_INT register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MMC_TX_INT_ADDR  ALT_EMAC_GMAC_MMC_TX_INT_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MMC_RX_INT_MSK register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MMC_RX_INT_MSK_ADDR  ALT_EMAC_GMAC_MMC_RX_INT_MSK_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MMC_TX_INT_MSK register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MMC_TX_INT_MSK_ADDR  ALT_EMAC_GMAC_MMC_TX_INT_MSK_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_TXOCTETCOUNT_GB register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_TXOCTETCOUNT_GB_ADDR  ALT_EMAC_GMAC_TXOCTETCOUNT_GB_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_TXFRMCOUNT_GB register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_TXFRMCOUNT_GB_ADDR  ALT_EMAC_GMAC_TXFRMCOUNT_GB_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_TXBCASTFRMS_G register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_TXBCASTFRMS_G_ADDR  ALT_EMAC_GMAC_TXBCASTFRMS_G_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_TXMCASTFRMS_G register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_TXMCASTFRMS_G_ADDR  ALT_EMAC_GMAC_TXMCASTFRMS_G_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_TX64OCTETS_GB register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_TX64OCTETS_GB_ADDR  ALT_EMAC_GMAC_TX64OCTETS_GB_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_TX65TO127OCTETS_GB register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_TX65TO127OCTETS_GB_ADDR  ALT_EMAC_GMAC_TX65TO127OCTETS_GB_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_TX128TO255OCTETS_GB register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_TX128TO255OCTETS_GB_ADDR  ALT_EMAC_GMAC_TX128TO255OCTETS_GB_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_TX256TO511OCTETS_GB register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_TX256TO511OCTETS_GB_ADDR  ALT_EMAC_GMAC_TX256TO511OCTETS_GB_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_TX512TO1023OCTETS_GB register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_TX512TO1023OCTETS_GB_ADDR  ALT_EMAC_GMAC_TX512TO1023OCTETS_GB_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_TX1024TOMAXOCTETS_GB register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_TX1024TOMAXOCTETS_GB_ADDR  ALT_EMAC_GMAC_TX1024TOMAXOCTETS_GB_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_TXUNICASTFRMS_GB register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_TXUNICASTFRMS_GB_ADDR  ALT_EMAC_GMAC_TXUNICASTFRMS_GB_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_TXMCASTFRMS_GB register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_TXMCASTFRMS_GB_ADDR  ALT_EMAC_GMAC_TXMCASTFRMS_GB_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_TXBCASTFRMS_GB register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_TXBCASTFRMS_GB_ADDR  ALT_EMAC_GMAC_TXBCASTFRMS_GB_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_TXUNDERFLOWERROR register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_TXUNDERFLOWERROR_ADDR  ALT_EMAC_GMAC_TXUNDERFLOWERROR_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_TXSINGLECOL_G register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_TXSINGLECOL_G_ADDR  ALT_EMAC_GMAC_TXSINGLECOL_G_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_TXMULTICOL_G register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_TXMULTICOL_G_ADDR  ALT_EMAC_GMAC_TXMULTICOL_G_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_TXDEFERRED register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_TXDEFERRED_ADDR  ALT_EMAC_GMAC_TXDEFERRED_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_TXLATECOL register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_TXLATECOL_ADDR  ALT_EMAC_GMAC_TXLATECOL_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_TXEXESSCOL register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_TXEXESSCOL_ADDR  ALT_EMAC_GMAC_TXEXESSCOL_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_TXCARRIERERR register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_TXCARRIERERR_ADDR  ALT_EMAC_GMAC_TXCARRIERERR_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_TXOCTETCNT register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_TXOCTETCNT_ADDR  ALT_EMAC_GMAC_TXOCTETCNT_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_TXFRMCOUNT_G register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_TXFRMCOUNT_G_ADDR  ALT_EMAC_GMAC_TXFRMCOUNT_G_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_TXEXCESSDEF register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_TXEXCESSDEF_ADDR  ALT_EMAC_GMAC_TXEXCESSDEF_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_TXPAUSEFRMS register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_TXPAUSEFRMS_ADDR  ALT_EMAC_GMAC_TXPAUSEFRMS_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_TXVLANFRMS_G register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_TXVLANFRMS_G_ADDR  ALT_EMAC_GMAC_TXVLANFRMS_G_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_TXOVERSIZE_G register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_TXOVERSIZE_G_ADDR  ALT_EMAC_GMAC_TXOVERSIZE_G_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXFRMCOUNT_GB register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_RXFRMCOUNT_GB_ADDR  ALT_EMAC_GMAC_RXFRMCOUNT_GB_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXOCTETCOUNT_GB register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_RXOCTETCOUNT_GB_ADDR  ALT_EMAC_GMAC_RXOCTETCOUNT_GB_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXOCTETCOUNT_G register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_RXOCTETCOUNT_G_ADDR  ALT_EMAC_GMAC_RXOCTETCOUNT_G_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXBCASTFRMS_G register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_RXBCASTFRMS_G_ADDR  ALT_EMAC_GMAC_RXBCASTFRMS_G_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXMCASTFRMS_G register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_RXMCASTFRMS_G_ADDR  ALT_EMAC_GMAC_RXMCASTFRMS_G_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXCRCERROR register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_RXCRCERROR_ADDR  ALT_EMAC_GMAC_RXCRCERROR_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXALIGNMENTERROR register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_RXALIGNMENTERROR_ADDR  ALT_EMAC_GMAC_RXALIGNMENTERROR_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXRUNTERROR register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_RXRUNTERROR_ADDR  ALT_EMAC_GMAC_RXRUNTERROR_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXJABBERERROR register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_RXJABBERERROR_ADDR  ALT_EMAC_GMAC_RXJABBERERROR_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXUNDERSIZE_G register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_RXUNDERSIZE_G_ADDR  ALT_EMAC_GMAC_RXUNDERSIZE_G_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXOVERSIZE_G register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_RXOVERSIZE_G_ADDR  ALT_EMAC_GMAC_RXOVERSIZE_G_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RX64OCTETS_GB register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_RX64OCTETS_GB_ADDR  ALT_EMAC_GMAC_RX64OCTETS_GB_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RX65TO127OCTETS_GB register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_RX65TO127OCTETS_GB_ADDR  ALT_EMAC_GMAC_RX65TO127OCTETS_GB_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RX128TO255OCTETS_GB register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_RX128TO255OCTETS_GB_ADDR  ALT_EMAC_GMAC_RX128TO255OCTETS_GB_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RX256TO511OCTETS_GB register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_RX256TO511OCTETS_GB_ADDR  ALT_EMAC_GMAC_RX256TO511OCTETS_GB_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RX512TO1023OCTETS_GB register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_RX512TO1023OCTETS_GB_ADDR  ALT_EMAC_GMAC_RX512TO1023OCTETS_GB_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RX1024TOMAXOCTETS_GB register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_RX1024TOMAXOCTETS_GB_ADDR  ALT_EMAC_GMAC_RX1024TOMAXOCTETS_GB_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXUNICASTFRMS_G register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_RXUNICASTFRMS_G_ADDR  ALT_EMAC_GMAC_RXUNICASTFRMS_G_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXLENERROR register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_RXLENERROR_ADDR  ALT_EMAC_GMAC_RXLENERROR_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXOUTOFRANGETYPE register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_RXOUTOFRANGETYPE_ADDR  ALT_EMAC_GMAC_RXOUTOFRANGETYPE_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXPAUSEFRMS register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_RXPAUSEFRMS_ADDR  ALT_EMAC_GMAC_RXPAUSEFRMS_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXFIFOOVF register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_RXFIFOOVF_ADDR  ALT_EMAC_GMAC_RXFIFOOVF_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXVLANFRMS_GB register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_RXVLANFRMS_GB_ADDR  ALT_EMAC_GMAC_RXVLANFRMS_GB_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXWDERROR register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_RXWDERROR_ADDR  ALT_EMAC_GMAC_RXWDERROR_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXRCVERROR register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_RXRCVERROR_ADDR  ALT_EMAC_GMAC_RXRCVERROR_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXCTLFRMS_G register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_RXCTLFRMS_G_ADDR  ALT_EMAC_GMAC_RXCTLFRMS_G_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MMC_IPC_RX_INT_MSK register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MMC_IPC_RX_INT_MSK_ADDR  ALT_EMAC_GMAC_MMC_IPC_RX_INT_MSK_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MMC_IPC_RX_INT register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MMC_IPC_RX_INT_ADDR  ALT_EMAC_GMAC_MMC_IPC_RX_INT_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXIPV4_GD_FRMS register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_RXIPV4_GD_FRMS_ADDR  ALT_EMAC_GMAC_RXIPV4_GD_FRMS_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXIPV4_HDRERR_FRMS register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_RXIPV4_HDRERR_FRMS_ADDR  ALT_EMAC_GMAC_RXIPV4_HDRERR_FRMS_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXIPV4_NOPAY_FRMS register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_RXIPV4_NOPAY_FRMS_ADDR  ALT_EMAC_GMAC_RXIPV4_NOPAY_FRMS_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXIPV4_FRAG_FRMS register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_RXIPV4_FRAG_FRMS_ADDR  ALT_EMAC_GMAC_RXIPV4_FRAG_FRMS_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXIPV4_UDSBL_FRMS register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_RXIPV4_UDSBL_FRMS_ADDR  ALT_EMAC_GMAC_RXIPV4_UDSBL_FRMS_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXIPV6_GD_FRMS register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_RXIPV6_GD_FRMS_ADDR  ALT_EMAC_GMAC_RXIPV6_GD_FRMS_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXIPV6_HDRERR_FRMS register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_RXIPV6_HDRERR_FRMS_ADDR  ALT_EMAC_GMAC_RXIPV6_HDRERR_FRMS_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXIPV6_NOPAY_FRMS register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_RXIPV6_NOPAY_FRMS_ADDR  ALT_EMAC_GMAC_RXIPV6_NOPAY_FRMS_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXUDP_GD_FRMS register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_RXUDP_GD_FRMS_ADDR  ALT_EMAC_GMAC_RXUDP_GD_FRMS_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXUDP_ERR_FRMS register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_RXUDP_ERR_FRMS_ADDR  ALT_EMAC_GMAC_RXUDP_ERR_FRMS_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXTCP_GD_FRMS register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_RXTCP_GD_FRMS_ADDR  ALT_EMAC_GMAC_RXTCP_GD_FRMS_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXTCP_ERR_FRMS register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_RXTCP_ERR_FRMS_ADDR  ALT_EMAC_GMAC_RXTCP_ERR_FRMS_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXICMP_GD_FRMS register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_RXICMP_GD_FRMS_ADDR  ALT_EMAC_GMAC_RXICMP_GD_FRMS_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXICMP_ERR_FRMS register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_RXICMP_ERR_FRMS_ADDR  ALT_EMAC_GMAC_RXICMP_ERR_FRMS_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXIPV4_GD_OCTETS register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_RXIPV4_GD_OCTETS_ADDR  ALT_EMAC_GMAC_RXIPV4_GD_OCTETS_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXIPV4_HDRERR_OCTETS register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_RXIPV4_HDRERR_OCTETS_ADDR  ALT_EMAC_GMAC_RXIPV4_HDRERR_OCTETS_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXIPV4_NOPAY_OCTETS register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_RXIPV4_NOPAY_OCTETS_ADDR  ALT_EMAC_GMAC_RXIPV4_NOPAY_OCTETS_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXIPV4_FRAG_OCTETS register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_RXIPV4_FRAG_OCTETS_ADDR  ALT_EMAC_GMAC_RXIPV4_FRAG_OCTETS_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXIPV4_UDSBL_OCTETS register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_RXIPV4_UDSBL_OCTETS_ADDR  ALT_EMAC_GMAC_RXIPV4_UDSBL_OCTETS_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXIPV6_GD_OCTETS register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_RXIPV6_GD_OCTETS_ADDR  ALT_EMAC_GMAC_RXIPV6_GD_OCTETS_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXIPV6_HDRERR_OCTETS register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_RXIPV6_HDRERR_OCTETS_ADDR  ALT_EMAC_GMAC_RXIPV6_HDRERR_OCTETS_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXIPV6_NOPAY_OCTETS register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_RXIPV6_NOPAY_OCTETS_ADDR  ALT_EMAC_GMAC_RXIPV6_NOPAY_OCTETS_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXUDP_GD_OCTETS register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_RXUDP_GD_OCTETS_ADDR  ALT_EMAC_GMAC_RXUDP_GD_OCTETS_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXUDP_ERR_OCTETS register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_RXUDP_ERR_OCTETS_ADDR  ALT_EMAC_GMAC_RXUDP_ERR_OCTETS_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXTCP_GD_OCTETS register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_RXTCP_GD_OCTETS_ADDR  ALT_EMAC_GMAC_RXTCP_GD_OCTETS_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXTCPERROCTETS register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_RXTCPERROCTETS_ADDR  ALT_EMAC_GMAC_RXTCPERROCTETS_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXICMP_GD_OCTETS register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_RXICMP_GD_OCTETS_ADDR  ALT_EMAC_GMAC_RXICMP_GD_OCTETS_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXICMP_ERR_OCTETS register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_RXICMP_ERR_OCTETS_ADDR  ALT_EMAC_GMAC_RXICMP_ERR_OCTETS_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_L3_L4_CTL0 register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_L3_L4_CTL0_ADDR  ALT_EMAC_GMAC_L3_L4_CTL0_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_LYR4_ADDR0 register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_LYR4_ADDR0_ADDR  ALT_EMAC_GMAC_LYR4_ADDR0_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_LYR3_ADDR0_REG0 register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_LYR3_ADDR0_REG0_ADDR  ALT_EMAC_GMAC_LYR3_ADDR0_REG0_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_LYR3_ADDR1_REG0 register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_LYR3_ADDR1_REG0_ADDR  ALT_EMAC_GMAC_LYR3_ADDR1_REG0_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_LYR3_ADDR2_REG0 register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_LYR3_ADDR2_REG0_ADDR  ALT_EMAC_GMAC_LYR3_ADDR2_REG0_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_LYR3_ADDR3_REG0 register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_LYR3_ADDR3_REG0_ADDR  ALT_EMAC_GMAC_LYR3_ADDR3_REG0_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_L3_L4_CTL1 register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_L3_L4_CTL1_ADDR  ALT_EMAC_GMAC_L3_L4_CTL1_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_LYR4_ADDR1 register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_LYR4_ADDR1_ADDR  ALT_EMAC_GMAC_LYR4_ADDR1_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_LYR3_ADDR0_REG1 register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_LYR3_ADDR0_REG1_ADDR  ALT_EMAC_GMAC_LYR3_ADDR0_REG1_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_LYR3_ADDR1_REG1 register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_LYR3_ADDR1_REG1_ADDR  ALT_EMAC_GMAC_LYR3_ADDR1_REG1_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_LYR3_ADDR2_REG1 register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_LYR3_ADDR2_REG1_ADDR  ALT_EMAC_GMAC_LYR3_ADDR2_REG1_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_LYR3_ADDR3_REG1 register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_LYR3_ADDR3_REG1_ADDR  ALT_EMAC_GMAC_LYR3_ADDR3_REG1_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_L3_L4_CTL2 register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_L3_L4_CTL2_ADDR  ALT_EMAC_GMAC_L3_L4_CTL2_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_LYR4_ADDR2 register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_LYR4_ADDR2_ADDR  ALT_EMAC_GMAC_LYR4_ADDR2_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_LYR3_ADDR0_REG2 register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_LYR3_ADDR0_REG2_ADDR  ALT_EMAC_GMAC_LYR3_ADDR0_REG2_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_LYR3_ADDR1_REG2 register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_LYR3_ADDR1_REG2_ADDR  ALT_EMAC_GMAC_LYR3_ADDR1_REG2_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_LYR3_ADDR2_REG2 register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_LYR3_ADDR2_REG2_ADDR  ALT_EMAC_GMAC_LYR3_ADDR2_REG2_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_LYR3_ADDR3_REG2 register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_LYR3_ADDR3_REG2_ADDR  ALT_EMAC_GMAC_LYR3_ADDR3_REG2_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_L3_L4_CTL3 register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_L3_L4_CTL3_ADDR  ALT_EMAC_GMAC_L3_L4_CTL3_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_LYR4_ADDR3 register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_LYR4_ADDR3_ADDR  ALT_EMAC_GMAC_LYR4_ADDR3_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_LYR3_ADDR0_REG3 register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_LYR3_ADDR0_REG3_ADDR  ALT_EMAC_GMAC_LYR3_ADDR0_REG3_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_LYR3_ADDR1_REG3 register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_LYR3_ADDR1_REG3_ADDR  ALT_EMAC_GMAC_LYR3_ADDR1_REG3_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_LYR3_ADDR2_REG3 register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_LYR3_ADDR2_REG3_ADDR  ALT_EMAC_GMAC_LYR3_ADDR2_REG3_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_LYR3_ADDR3_REG3 register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_LYR3_ADDR3_REG3_ADDR  ALT_EMAC_GMAC_LYR3_ADDR3_REG3_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_HASH_TABLE_REG0 register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_HASH_TABLE_REG0_ADDR  ALT_EMAC_GMAC_HASH_TABLE_REG0_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_HASH_TABLE_REG1 register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_HASH_TABLE_REG1_ADDR  ALT_EMAC_GMAC_HASH_TABLE_REG1_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_HASH_TABLE_REG2 register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_HASH_TABLE_REG2_ADDR  ALT_EMAC_GMAC_HASH_TABLE_REG2_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_HASH_TABLE_REG3 register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_HASH_TABLE_REG3_ADDR  ALT_EMAC_GMAC_HASH_TABLE_REG3_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_HASH_TABLE_REG4 register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_HASH_TABLE_REG4_ADDR  ALT_EMAC_GMAC_HASH_TABLE_REG4_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_HASH_TABLE_REG5 register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_HASH_TABLE_REG5_ADDR  ALT_EMAC_GMAC_HASH_TABLE_REG5_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_HASH_TABLE_REG6 register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_HASH_TABLE_REG6_ADDR  ALT_EMAC_GMAC_HASH_TABLE_REG6_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_HASH_TABLE_REG7 register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_HASH_TABLE_REG7_ADDR  ALT_EMAC_GMAC_HASH_TABLE_REG7_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_VLAN_INCL_REG register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_VLAN_INCL_REG_ADDR  ALT_EMAC_GMAC_VLAN_INCL_REG_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_VLAN_HASH_TABLE_REG register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_VLAN_HASH_TABLE_REG_ADDR  ALT_EMAC_GMAC_VLAN_HASH_TABLE_REG_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_TS_CTL register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_TS_CTL_ADDR  ALT_EMAC_GMAC_TS_CTL_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_SUB_SEC_INCREMENT register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_SUB_SEC_INCREMENT_ADDR  ALT_EMAC_GMAC_SUB_SEC_INCREMENT_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_SYS_TIME_SECS register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_SYS_TIME_SECS_ADDR  ALT_EMAC_GMAC_SYS_TIME_SECS_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_SYS_TIME_NANOSECS register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_SYS_TIME_NANOSECS_ADDR  ALT_EMAC_GMAC_SYS_TIME_NANOSECS_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_SYS_TIME_SECS_UPDATE register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_SYS_TIME_SECS_UPDATE_ADDR  ALT_EMAC_GMAC_SYS_TIME_SECS_UPDATE_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_SYS_TIME_NANOSECS_UPDATE register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_SYS_TIME_NANOSECS_UPDATE_ADDR  ALT_EMAC_GMAC_SYS_TIME_NANOSECS_UPDATE_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_TS_ADDEND register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_TS_ADDEND_ADDR  ALT_EMAC_GMAC_TS_ADDEND_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_TGT_TIME_SECS register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_TGT_TIME_SECS_ADDR  ALT_EMAC_GMAC_TGT_TIME_SECS_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_TGT_TIME_NANOSECS register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_TGT_TIME_NANOSECS_ADDR  ALT_EMAC_GMAC_TGT_TIME_NANOSECS_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_SYS_TIME_HIGHER_WORD_SECS register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_SYS_TIME_HIGHER_WORD_SECS_ADDR  ALT_EMAC_GMAC_SYS_TIME_HIGHER_WORD_SECS_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_TS_STAT register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_TS_STAT_ADDR  ALT_EMAC_GMAC_TS_STAT_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_PPS_CTL register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_PPS_CTL_ADDR  ALT_EMAC_GMAC_PPS_CTL_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_AUX_TS_NANOSECS register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_AUX_TS_NANOSECS_ADDR  ALT_EMAC_GMAC_AUX_TS_NANOSECS_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_AUX_TS_SECS register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_AUX_TS_SECS_ADDR  ALT_EMAC_GMAC_AUX_TS_SECS_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_PPS0_INTERVAL register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_PPS0_INTERVAL_ADDR  ALT_EMAC_GMAC_PPS0_INTERVAL_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_PPS0_WIDTH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_PPS0_WIDTH_ADDR  ALT_EMAC_GMAC_PPS0_WIDTH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR16_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR16_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR16_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR16_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR16_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR16_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR17_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR17_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR17_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR17_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR17_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR17_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR18_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR18_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR18_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR18_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR18_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR18_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR19_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR19_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR19_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR19_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR19_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR19_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR20_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR20_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR20_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR20_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR20_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR20_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR21_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR21_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR21_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR21_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR21_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR21_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR22_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR22_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR22_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR22_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR22_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR22_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR23_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR23_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR23_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR23_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR23_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR23_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR24_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR24_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR24_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR24_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR24_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR24_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR25_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR25_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR25_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR25_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR25_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR25_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR26_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR26_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR26_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR26_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR26_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR26_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR27_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR27_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR27_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR27_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR27_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR27_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR28_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR28_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR28_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR28_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR28_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR28_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR29_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR29_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR29_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR29_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR29_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR29_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR30_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR30_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR30_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR30_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR30_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR30_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR31_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR31_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR31_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR31_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR31_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR31_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR32_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR32_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR32_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR32_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR32_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR32_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR33_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR33_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR33_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR33_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR33_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR33_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR34_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR34_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR34_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR34_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR34_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR34_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR35_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR35_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR35_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR35_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR35_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR35_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR36_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR36_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR36_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR36_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR36_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR36_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR37_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR37_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR37_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR37_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR37_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR37_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR38_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR38_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR38_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR38_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR38_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR38_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR39_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR39_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR39_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR39_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR39_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR39_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR40_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR40_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR40_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR40_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR40_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR40_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR41_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR41_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR41_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR41_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR41_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR41_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR42_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR42_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR42_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR42_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR42_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR42_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR43_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR43_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR43_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR43_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR43_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR43_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR44_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR44_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR44_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR44_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR44_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR44_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR45_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR45_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR45_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR45_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR45_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR45_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR46_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR46_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR46_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR46_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR46_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR46_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR47_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR47_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR47_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR47_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR47_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR47_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR48_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR48_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR48_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR48_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR48_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR48_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR49_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR49_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR49_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR49_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR49_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR49_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR50_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR50_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR50_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR50_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR50_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR50_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR51_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR51_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR51_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR51_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR51_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR51_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR52_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR52_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR52_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR52_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR52_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR52_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR53_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR53_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR53_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR53_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR53_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR53_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR54_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR54_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR54_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR54_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR54_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR54_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR55_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR55_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR55_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR55_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR55_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR55_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR56_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR56_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR56_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR56_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR56_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR56_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR57_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR57_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR57_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR57_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR57_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR57_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR58_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR58_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR58_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR58_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR58_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR58_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR59_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR59_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR59_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR59_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR59_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR59_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR60_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR60_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR60_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR60_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR60_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR60_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR61_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR61_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR61_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR61_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR61_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR61_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR62_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR62_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR62_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR62_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR62_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR62_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR63_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR63_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR63_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR63_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR63_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR63_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR64_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR64_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR64_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR64_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR64_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR64_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR65_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR65_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR65_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR65_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR65_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR65_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR66_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR66_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR66_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR66_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR66_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR66_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR67_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR67_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR67_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR67_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR67_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR67_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR68_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR68_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR68_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR68_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR68_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR68_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR69_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR69_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR69_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR69_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR69_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR69_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR70_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR70_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR70_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR70_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR70_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR70_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR71_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR71_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR71_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR71_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR71_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR71_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR72_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR72_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR72_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR72_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR72_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR72_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR73_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR73_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR73_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR73_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR73_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR73_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR74_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR74_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR74_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR74_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR74_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR74_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR75_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR75_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR75_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR75_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR75_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR75_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR76_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR76_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR76_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR76_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR76_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR76_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR77_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR77_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR77_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR77_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR77_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR77_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR78_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR78_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR78_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR78_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR78_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR78_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR79_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR79_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR79_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR79_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR79_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR79_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR80_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR80_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR80_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR80_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR80_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR80_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR81_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR81_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR81_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR81_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR81_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR81_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR82_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR82_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR82_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR82_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR82_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR82_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR83_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR83_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR83_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR83_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR83_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR83_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR84_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR84_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR84_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR84_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR84_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR84_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR85_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR85_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR85_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR85_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR85_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR85_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR86_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR86_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR86_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR86_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR86_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR86_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR87_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR87_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR87_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR87_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR87_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR87_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR88_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR88_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR88_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR88_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR88_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR88_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR89_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR89_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR89_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR89_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR89_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR89_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR90_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR90_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR90_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR90_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR90_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR90_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR91_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR91_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR91_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR91_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR91_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR91_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR92_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR92_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR92_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR92_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR92_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR92_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR93_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR93_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR93_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR93_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR93_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR93_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR94_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR94_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR94_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR94_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR94_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR94_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR95_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR95_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR95_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR95_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR95_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR95_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR96_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR96_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR96_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR96_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR96_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR96_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR97_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR97_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR97_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR97_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR97_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR97_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR98_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR98_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR98_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR98_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR98_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR98_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR99_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR99_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR99_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR99_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR99_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR99_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR100_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR100_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR100_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR100_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR100_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR100_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR101_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR101_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR101_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR101_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR101_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR101_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR102_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR102_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR102_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR102_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR102_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR102_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR103_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR103_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR103_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR103_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR103_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR103_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR104_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR104_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR104_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR104_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR104_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR104_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR105_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR105_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR105_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR105_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR105_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR105_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR106_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR106_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR106_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR106_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR106_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR106_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR107_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR107_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR107_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR107_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR107_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR107_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR108_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR108_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR108_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR108_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR108_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR108_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR109_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR109_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR109_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR109_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR109_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR109_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR110_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR110_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR110_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR110_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR110_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR110_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR111_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR111_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR111_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR111_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR111_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR111_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR112_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR112_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR112_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR112_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR112_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR112_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR113_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR113_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR113_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR113_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR113_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR113_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR114_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR114_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR114_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR114_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR114_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR114_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR115_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR115_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR115_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR115_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR115_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR115_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR116_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR116_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR116_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR116_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR116_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR116_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR117_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR117_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR117_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR117_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR117_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR117_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR118_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR118_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR118_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR118_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR118_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR118_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR119_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR119_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR119_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR119_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR119_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR119_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR120_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR120_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR120_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR120_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR120_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR120_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR121_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR121_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR121_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR121_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR121_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR121_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR122_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR122_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR122_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR122_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR122_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR122_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR123_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR123_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR123_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR123_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR123_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR123_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR124_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR124_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR124_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR124_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR124_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR124_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR125_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR125_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR125_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR125_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR125_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR125_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR126_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR126_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR126_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR126_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR126_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR126_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR127_HIGH register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR127_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR127_HIGH_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR127_LOW register for the ALT_EMAC0_GMACGRP instance. */
#define ALT_EMAC0_GMAC_MAC_ADDR127_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR127_LOW_ADDR(ALT_EMAC0_GMACGRP_ADDR)
/* The base address byte offset for the start of the ALT_EMAC0_GMACGRP component. */
#define ALT_EMAC0_GMACGRP_OFST        0x0
/* The start address of the ALT_EMAC0_GMACGRP component. */
#define ALT_EMAC0_GMACGRP_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_EMAC0_ADDR) + ALT_EMAC0_GMACGRP_OFST))
/* The lower bound address range of the ALT_EMAC0_GMACGRP component. */
#define ALT_EMAC0_GMACGRP_LB_ADDR     ALT_EMAC0_GMACGRP_ADDR
/* The upper bound address range of the ALT_EMAC0_GMACGRP component. */
#define ALT_EMAC0_GMACGRP_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_EMAC0_GMACGRP_ADDR) + 0xb80) - 1))


/*
 * Register Group Instance : dmagrp
 * 
 * Instance dmagrp of register group ALT_EMAC_DMA.
 * 
 * 
 */
/* The address of the ALT_EMAC_DMA_BUS_MOD register for the ALT_EMAC0_DMAGRP instance. */
#define ALT_EMAC0_DMA_BUS_MOD_ADDR  ALT_EMAC_DMA_BUS_MOD_ADDR(ALT_EMAC0_DMAGRP_ADDR)
/* The address of the ALT_EMAC_DMA_TX_POLL_DEMAND register for the ALT_EMAC0_DMAGRP instance. */
#define ALT_EMAC0_DMA_TX_POLL_DEMAND_ADDR  ALT_EMAC_DMA_TX_POLL_DEMAND_ADDR(ALT_EMAC0_DMAGRP_ADDR)
/* The address of the ALT_EMAC_DMA_RX_POLL_DEMAND register for the ALT_EMAC0_DMAGRP instance. */
#define ALT_EMAC0_DMA_RX_POLL_DEMAND_ADDR  ALT_EMAC_DMA_RX_POLL_DEMAND_ADDR(ALT_EMAC0_DMAGRP_ADDR)
/* The address of the ALT_EMAC_DMA_RX_DESC_LIST_ADDR register for the ALT_EMAC0_DMAGRP instance. */
#define ALT_EMAC0_DMA_RX_DESC_LIST_ADDR_ADDR  ALT_EMAC_DMA_RX_DESC_LIST_ADDR_ADDR(ALT_EMAC0_DMAGRP_ADDR)
/* The address of the ALT_EMAC_DMA_TX_DESC_LIST_ADDR register for the ALT_EMAC0_DMAGRP instance. */
#define ALT_EMAC0_DMA_TX_DESC_LIST_ADDR_ADDR  ALT_EMAC_DMA_TX_DESC_LIST_ADDR_ADDR(ALT_EMAC0_DMAGRP_ADDR)
/* The address of the ALT_EMAC_DMA_STAT register for the ALT_EMAC0_DMAGRP instance. */
#define ALT_EMAC0_DMA_STAT_ADDR  ALT_EMAC_DMA_STAT_ADDR(ALT_EMAC0_DMAGRP_ADDR)
/* The address of the ALT_EMAC_DMA_OP_MOD register for the ALT_EMAC0_DMAGRP instance. */
#define ALT_EMAC0_DMA_OP_MOD_ADDR  ALT_EMAC_DMA_OP_MOD_ADDR(ALT_EMAC0_DMAGRP_ADDR)
/* The address of the ALT_EMAC_DMA_INT_EN register for the ALT_EMAC0_DMAGRP instance. */
#define ALT_EMAC0_DMA_INT_EN_ADDR  ALT_EMAC_DMA_INT_EN_ADDR(ALT_EMAC0_DMAGRP_ADDR)
/* The address of the ALT_EMAC_DMA_MFRM_BUF_OVF_CNTR register for the ALT_EMAC0_DMAGRP instance. */
#define ALT_EMAC0_DMA_MISSED_FRM_AND_BUF_OVF_CNTR_ADDR  ALT_EMAC_DMA_MFRM_BUF_OVF_CNTR_ADDR(ALT_EMAC0_DMAGRP_ADDR)
/* The address of the ALT_EMAC_DMA_RX_INT_WDT register for the ALT_EMAC0_DMAGRP instance. */
#define ALT_EMAC0_DMA_RX_INT_WDT_ADDR  ALT_EMAC_DMA_RX_INT_WDT_ADDR(ALT_EMAC0_DMAGRP_ADDR)
/* The address of the ALT_EMAC_DMA_AXI_BUS_MOD register for the ALT_EMAC0_DMAGRP instance. */
#define ALT_EMAC0_DMA_AXI_BUS_MOD_ADDR  ALT_EMAC_DMA_AXI_BUS_MOD_ADDR(ALT_EMAC0_DMAGRP_ADDR)
/* The address of the ALT_EMAC_DMA_AHB_OR_AXI_STAT register for the ALT_EMAC0_DMAGRP instance. */
#define ALT_EMAC0_DMA_AHB_OR_AXI_STAT_ADDR  ALT_EMAC_DMA_AHB_OR_AXI_STAT_ADDR(ALT_EMAC0_DMAGRP_ADDR)
/* The address of the ALT_EMAC_DMA_CUR_HOST_TX_DESC register for the ALT_EMAC0_DMAGRP instance. */
#define ALT_EMAC0_DMA_CUR_HOST_TX_DESC_ADDR  ALT_EMAC_DMA_CUR_HOST_TX_DESC_ADDR(ALT_EMAC0_DMAGRP_ADDR)
/* The address of the ALT_EMAC_DMA_CUR_HOST_RX_DESC register for the ALT_EMAC0_DMAGRP instance. */
#define ALT_EMAC0_DMA_CUR_HOST_RX_DESC_ADDR  ALT_EMAC_DMA_CUR_HOST_RX_DESC_ADDR(ALT_EMAC0_DMAGRP_ADDR)
/* The address of the ALT_EMAC_DMA_CUR_HOST_TX_BUF_ADDR register for the ALT_EMAC0_DMAGRP instance. */
#define ALT_EMAC0_DMA_CUR_HOST_TX_BUF_ADDR_ADDR  ALT_EMAC_DMA_CUR_HOST_TX_BUF_ADDR_ADDR(ALT_EMAC0_DMAGRP_ADDR)
/* The address of the ALT_EMAC_DMA_CUR_HOST_RX_BUF_ADDR register for the ALT_EMAC0_DMAGRP instance. */
#define ALT_EMAC0_DMA_CUR_HOST_RX_BUF_ADDR_ADDR  ALT_EMAC_DMA_CUR_HOST_RX_BUF_ADDR_ADDR(ALT_EMAC0_DMAGRP_ADDR)
/* The address of the ALT_EMAC_DMA_HW_FEATURE register for the ALT_EMAC0_DMAGRP instance. */
#define ALT_EMAC0_DMA_HW_FEATURE_ADDR  ALT_EMAC_DMA_HW_FEATURE_ADDR(ALT_EMAC0_DMAGRP_ADDR)
/* The base address byte offset for the start of the ALT_EMAC0_DMAGRP component. */
#define ALT_EMAC0_DMAGRP_OFST        0x1000
/* The start address of the ALT_EMAC0_DMAGRP component. */
#define ALT_EMAC0_DMAGRP_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_EMAC0_ADDR) + ALT_EMAC0_DMAGRP_OFST))
/* The lower bound address range of the ALT_EMAC0_DMAGRP component. */
#define ALT_EMAC0_DMAGRP_LB_ADDR     ALT_EMAC0_DMAGRP_ADDR
/* The upper bound address range of the ALT_EMAC0_DMAGRP component. */
#define ALT_EMAC0_DMAGRP_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_EMAC0_DMAGRP_ADDR) + 0x5c) - 1))


/* The base address byte offset for the start of the ALT_EMAC0 component. */
#define ALT_EMAC0_OFST        0xff700000
/* The start address of the ALT_EMAC0 component. */
#define ALT_EMAC0_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_HPS_ADDR) + ALT_EMAC0_OFST))
/* The lower bound address range of the ALT_EMAC0 component. */
#define ALT_EMAC0_LB_ADDR     ALT_EMAC0_ADDR
/* The upper bound address range of the ALT_EMAC0 component. */
#define ALT_EMAC0_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_EMAC0_ADDR) + 0x2000) - 1))


/*
 * Component Instance : emac1
 * 
 * Instance emac1 of component ALT_EMAC.
 * 
 * 
 */
/*
 * Register Group Instance : gmacgrp
 * 
 * Instance gmacgrp of register group ALT_EMAC_GMAC.
 * 
 * 
 */
/* The address of the ALT_EMAC_GMAC_MAC_CFG register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_CFG_ADDR  ALT_EMAC_GMAC_MAC_CFG_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_FRM_FLT register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_FRM_FLT_ADDR  ALT_EMAC_GMAC_MAC_FRM_FLT_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_GMII_ADDR register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_GMII_ADDR_ADDR  ALT_EMAC_GMAC_GMII_ADDR_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_GMII_DATA register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_GMII_DATA_ADDR  ALT_EMAC_GMAC_GMII_DATA_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_FLOW_CTL register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_FLOW_CTL_ADDR  ALT_EMAC_GMAC_FLOW_CTL_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_VLAN_TAG register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_VLAN_TAG_ADDR  ALT_EMAC_GMAC_VLAN_TAG_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_VER register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_VER_ADDR  ALT_EMAC_GMAC_VER_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_DBG register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_DBG_ADDR  ALT_EMAC_GMAC_DBG_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_LPI_CTL_STAT register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_LPI_CTL_STAT_ADDR  ALT_EMAC_GMAC_LPI_CTL_STAT_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_LPI_TMRS_CTL register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_LPI_TMRS_CTL_ADDR  ALT_EMAC_GMAC_LPI_TMRS_CTL_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_INT_STAT register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_INT_STAT_ADDR  ALT_EMAC_GMAC_INT_STAT_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_INT_MSK register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_INT_MSK_ADDR  ALT_EMAC_GMAC_INT_MSK_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR0_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR0_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR0_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR0_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR0_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR0_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR1_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR1_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR1_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR1_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR1_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR1_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR2_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR2_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR2_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR2_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR2_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR2_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR3_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR3_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR3_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR3_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR3_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR3_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR4_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR4_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR4_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR4_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR4_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR4_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR5_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR5_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR5_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR5_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR5_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR5_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR6_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR6_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR6_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR6_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR6_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR6_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR7_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR7_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR7_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR7_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR7_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR7_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR8_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR8_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR8_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR8_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR8_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR8_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR9_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR9_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR9_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR9_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR9_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR9_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR10_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR10_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR10_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR10_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR10_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR10_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR11_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR11_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR11_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR11_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR11_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR11_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR12_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR12_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR12_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR12_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR12_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR12_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR13_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR13_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR13_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR13_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR13_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR13_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR14_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR14_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR14_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR14_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR14_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR14_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR15_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR15_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR15_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR15_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR15_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR15_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MII_CTL_STAT register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_SGMII_RGMII_SMII_CTL_STAT_ADDR  ALT_EMAC_GMAC_MII_CTL_STAT_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MMC_CTL register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MMC_CTL_ADDR  ALT_EMAC_GMAC_MMC_CTL_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MMC_RX_INT register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MMC_RX_INT_ADDR  ALT_EMAC_GMAC_MMC_RX_INT_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MMC_TX_INT register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MMC_TX_INT_ADDR  ALT_EMAC_GMAC_MMC_TX_INT_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MMC_RX_INT_MSK register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MMC_RX_INT_MSK_ADDR  ALT_EMAC_GMAC_MMC_RX_INT_MSK_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MMC_TX_INT_MSK register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MMC_TX_INT_MSK_ADDR  ALT_EMAC_GMAC_MMC_TX_INT_MSK_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_TXOCTETCOUNT_GB register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_TXOCTETCOUNT_GB_ADDR  ALT_EMAC_GMAC_TXOCTETCOUNT_GB_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_TXFRMCOUNT_GB register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_TXFRMCOUNT_GB_ADDR  ALT_EMAC_GMAC_TXFRMCOUNT_GB_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_TXBCASTFRMS_G register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_TXBCASTFRMS_G_ADDR  ALT_EMAC_GMAC_TXBCASTFRMS_G_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_TXMCASTFRMS_G register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_TXMCASTFRMS_G_ADDR  ALT_EMAC_GMAC_TXMCASTFRMS_G_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_TX64OCTETS_GB register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_TX64OCTETS_GB_ADDR  ALT_EMAC_GMAC_TX64OCTETS_GB_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_TX65TO127OCTETS_GB register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_TX65TO127OCTETS_GB_ADDR  ALT_EMAC_GMAC_TX65TO127OCTETS_GB_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_TX128TO255OCTETS_GB register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_TX128TO255OCTETS_GB_ADDR  ALT_EMAC_GMAC_TX128TO255OCTETS_GB_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_TX256TO511OCTETS_GB register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_TX256TO511OCTETS_GB_ADDR  ALT_EMAC_GMAC_TX256TO511OCTETS_GB_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_TX512TO1023OCTETS_GB register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_TX512TO1023OCTETS_GB_ADDR  ALT_EMAC_GMAC_TX512TO1023OCTETS_GB_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_TX1024TOMAXOCTETS_GB register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_TX1024TOMAXOCTETS_GB_ADDR  ALT_EMAC_GMAC_TX1024TOMAXOCTETS_GB_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_TXUNICASTFRMS_GB register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_TXUNICASTFRMS_GB_ADDR  ALT_EMAC_GMAC_TXUNICASTFRMS_GB_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_TXMCASTFRMS_GB register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_TXMCASTFRMS_GB_ADDR  ALT_EMAC_GMAC_TXMCASTFRMS_GB_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_TXBCASTFRMS_GB register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_TXBCASTFRMS_GB_ADDR  ALT_EMAC_GMAC_TXBCASTFRMS_GB_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_TXUNDERFLOWERROR register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_TXUNDERFLOWERROR_ADDR  ALT_EMAC_GMAC_TXUNDERFLOWERROR_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_TXSINGLECOL_G register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_TXSINGLECOL_G_ADDR  ALT_EMAC_GMAC_TXSINGLECOL_G_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_TXMULTICOL_G register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_TXMULTICOL_G_ADDR  ALT_EMAC_GMAC_TXMULTICOL_G_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_TXDEFERRED register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_TXDEFERRED_ADDR  ALT_EMAC_GMAC_TXDEFERRED_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_TXLATECOL register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_TXLATECOL_ADDR  ALT_EMAC_GMAC_TXLATECOL_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_TXEXESSCOL register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_TXEXESSCOL_ADDR  ALT_EMAC_GMAC_TXEXESSCOL_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_TXCARRIERERR register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_TXCARRIERERR_ADDR  ALT_EMAC_GMAC_TXCARRIERERR_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_TXOCTETCNT register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_TXOCTETCNT_ADDR  ALT_EMAC_GMAC_TXOCTETCNT_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_TXFRMCOUNT_G register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_TXFRMCOUNT_G_ADDR  ALT_EMAC_GMAC_TXFRMCOUNT_G_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_TXEXCESSDEF register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_TXEXCESSDEF_ADDR  ALT_EMAC_GMAC_TXEXCESSDEF_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_TXPAUSEFRMS register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_TXPAUSEFRMS_ADDR  ALT_EMAC_GMAC_TXPAUSEFRMS_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_TXVLANFRMS_G register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_TXVLANFRMS_G_ADDR  ALT_EMAC_GMAC_TXVLANFRMS_G_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_TXOVERSIZE_G register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_TXOVERSIZE_G_ADDR  ALT_EMAC_GMAC_TXOVERSIZE_G_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXFRMCOUNT_GB register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_RXFRMCOUNT_GB_ADDR  ALT_EMAC_GMAC_RXFRMCOUNT_GB_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXOCTETCOUNT_GB register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_RXOCTETCOUNT_GB_ADDR  ALT_EMAC_GMAC_RXOCTETCOUNT_GB_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXOCTETCOUNT_G register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_RXOCTETCOUNT_G_ADDR  ALT_EMAC_GMAC_RXOCTETCOUNT_G_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXBCASTFRMS_G register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_RXBCASTFRMS_G_ADDR  ALT_EMAC_GMAC_RXBCASTFRMS_G_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXMCASTFRMS_G register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_RXMCASTFRMS_G_ADDR  ALT_EMAC_GMAC_RXMCASTFRMS_G_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXCRCERROR register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_RXCRCERROR_ADDR  ALT_EMAC_GMAC_RXCRCERROR_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXALIGNMENTERROR register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_RXALIGNMENTERROR_ADDR  ALT_EMAC_GMAC_RXALIGNMENTERROR_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXRUNTERROR register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_RXRUNTERROR_ADDR  ALT_EMAC_GMAC_RXRUNTERROR_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXJABBERERROR register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_RXJABBERERROR_ADDR  ALT_EMAC_GMAC_RXJABBERERROR_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXUNDERSIZE_G register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_RXUNDERSIZE_G_ADDR  ALT_EMAC_GMAC_RXUNDERSIZE_G_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXOVERSIZE_G register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_RXOVERSIZE_G_ADDR  ALT_EMAC_GMAC_RXOVERSIZE_G_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RX64OCTETS_GB register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_RX64OCTETS_GB_ADDR  ALT_EMAC_GMAC_RX64OCTETS_GB_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RX65TO127OCTETS_GB register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_RX65TO127OCTETS_GB_ADDR  ALT_EMAC_GMAC_RX65TO127OCTETS_GB_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RX128TO255OCTETS_GB register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_RX128TO255OCTETS_GB_ADDR  ALT_EMAC_GMAC_RX128TO255OCTETS_GB_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RX256TO511OCTETS_GB register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_RX256TO511OCTETS_GB_ADDR  ALT_EMAC_GMAC_RX256TO511OCTETS_GB_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RX512TO1023OCTETS_GB register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_RX512TO1023OCTETS_GB_ADDR  ALT_EMAC_GMAC_RX512TO1023OCTETS_GB_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RX1024TOMAXOCTETS_GB register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_RX1024TOMAXOCTETS_GB_ADDR  ALT_EMAC_GMAC_RX1024TOMAXOCTETS_GB_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXUNICASTFRMS_G register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_RXUNICASTFRMS_G_ADDR  ALT_EMAC_GMAC_RXUNICASTFRMS_G_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXLENERROR register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_RXLENERROR_ADDR  ALT_EMAC_GMAC_RXLENERROR_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXOUTOFRANGETYPE register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_RXOUTOFRANGETYPE_ADDR  ALT_EMAC_GMAC_RXOUTOFRANGETYPE_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXPAUSEFRMS register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_RXPAUSEFRMS_ADDR  ALT_EMAC_GMAC_RXPAUSEFRMS_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXFIFOOVF register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_RXFIFOOVF_ADDR  ALT_EMAC_GMAC_RXFIFOOVF_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXVLANFRMS_GB register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_RXVLANFRMS_GB_ADDR  ALT_EMAC_GMAC_RXVLANFRMS_GB_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXWDERROR register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_RXWDERROR_ADDR  ALT_EMAC_GMAC_RXWDERROR_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXRCVERROR register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_RXRCVERROR_ADDR  ALT_EMAC_GMAC_RXRCVERROR_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXCTLFRMS_G register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_RXCTLFRMS_G_ADDR  ALT_EMAC_GMAC_RXCTLFRMS_G_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MMC_IPC_RX_INT_MSK register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MMC_IPC_RX_INT_MSK_ADDR  ALT_EMAC_GMAC_MMC_IPC_RX_INT_MSK_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MMC_IPC_RX_INT register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MMC_IPC_RX_INT_ADDR  ALT_EMAC_GMAC_MMC_IPC_RX_INT_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXIPV4_GD_FRMS register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_RXIPV4_GD_FRMS_ADDR  ALT_EMAC_GMAC_RXIPV4_GD_FRMS_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXIPV4_HDRERR_FRMS register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_RXIPV4_HDRERR_FRMS_ADDR  ALT_EMAC_GMAC_RXIPV4_HDRERR_FRMS_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXIPV4_NOPAY_FRMS register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_RXIPV4_NOPAY_FRMS_ADDR  ALT_EMAC_GMAC_RXIPV4_NOPAY_FRMS_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXIPV4_FRAG_FRMS register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_RXIPV4_FRAG_FRMS_ADDR  ALT_EMAC_GMAC_RXIPV4_FRAG_FRMS_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXIPV4_UDSBL_FRMS register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_RXIPV4_UDSBL_FRMS_ADDR  ALT_EMAC_GMAC_RXIPV4_UDSBL_FRMS_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXIPV6_GD_FRMS register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_RXIPV6_GD_FRMS_ADDR  ALT_EMAC_GMAC_RXIPV6_GD_FRMS_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXIPV6_HDRERR_FRMS register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_RXIPV6_HDRERR_FRMS_ADDR  ALT_EMAC_GMAC_RXIPV6_HDRERR_FRMS_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXIPV6_NOPAY_FRMS register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_RXIPV6_NOPAY_FRMS_ADDR  ALT_EMAC_GMAC_RXIPV6_NOPAY_FRMS_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXUDP_GD_FRMS register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_RXUDP_GD_FRMS_ADDR  ALT_EMAC_GMAC_RXUDP_GD_FRMS_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXUDP_ERR_FRMS register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_RXUDP_ERR_FRMS_ADDR  ALT_EMAC_GMAC_RXUDP_ERR_FRMS_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXTCP_GD_FRMS register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_RXTCP_GD_FRMS_ADDR  ALT_EMAC_GMAC_RXTCP_GD_FRMS_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXTCP_ERR_FRMS register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_RXTCP_ERR_FRMS_ADDR  ALT_EMAC_GMAC_RXTCP_ERR_FRMS_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXICMP_GD_FRMS register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_RXICMP_GD_FRMS_ADDR  ALT_EMAC_GMAC_RXICMP_GD_FRMS_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXICMP_ERR_FRMS register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_RXICMP_ERR_FRMS_ADDR  ALT_EMAC_GMAC_RXICMP_ERR_FRMS_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXIPV4_GD_OCTETS register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_RXIPV4_GD_OCTETS_ADDR  ALT_EMAC_GMAC_RXIPV4_GD_OCTETS_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXIPV4_HDRERR_OCTETS register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_RXIPV4_HDRERR_OCTETS_ADDR  ALT_EMAC_GMAC_RXIPV4_HDRERR_OCTETS_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXIPV4_NOPAY_OCTETS register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_RXIPV4_NOPAY_OCTETS_ADDR  ALT_EMAC_GMAC_RXIPV4_NOPAY_OCTETS_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXIPV4_FRAG_OCTETS register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_RXIPV4_FRAG_OCTETS_ADDR  ALT_EMAC_GMAC_RXIPV4_FRAG_OCTETS_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXIPV4_UDSBL_OCTETS register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_RXIPV4_UDSBL_OCTETS_ADDR  ALT_EMAC_GMAC_RXIPV4_UDSBL_OCTETS_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXIPV6_GD_OCTETS register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_RXIPV6_GD_OCTETS_ADDR  ALT_EMAC_GMAC_RXIPV6_GD_OCTETS_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXIPV6_HDRERR_OCTETS register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_RXIPV6_HDRERR_OCTETS_ADDR  ALT_EMAC_GMAC_RXIPV6_HDRERR_OCTETS_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXIPV6_NOPAY_OCTETS register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_RXIPV6_NOPAY_OCTETS_ADDR  ALT_EMAC_GMAC_RXIPV6_NOPAY_OCTETS_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXUDP_GD_OCTETS register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_RXUDP_GD_OCTETS_ADDR  ALT_EMAC_GMAC_RXUDP_GD_OCTETS_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXUDP_ERR_OCTETS register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_RXUDP_ERR_OCTETS_ADDR  ALT_EMAC_GMAC_RXUDP_ERR_OCTETS_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXTCP_GD_OCTETS register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_RXTCP_GD_OCTETS_ADDR  ALT_EMAC_GMAC_RXTCP_GD_OCTETS_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXTCPERROCTETS register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_RXTCPERROCTETS_ADDR  ALT_EMAC_GMAC_RXTCPERROCTETS_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXICMP_GD_OCTETS register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_RXICMP_GD_OCTETS_ADDR  ALT_EMAC_GMAC_RXICMP_GD_OCTETS_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_RXICMP_ERR_OCTETS register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_RXICMP_ERR_OCTETS_ADDR  ALT_EMAC_GMAC_RXICMP_ERR_OCTETS_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_L3_L4_CTL0 register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_L3_L4_CTL0_ADDR  ALT_EMAC_GMAC_L3_L4_CTL0_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_LYR4_ADDR0 register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_LYR4_ADDR0_ADDR  ALT_EMAC_GMAC_LYR4_ADDR0_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_LYR3_ADDR0_REG0 register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_LYR3_ADDR0_REG0_ADDR  ALT_EMAC_GMAC_LYR3_ADDR0_REG0_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_LYR3_ADDR1_REG0 register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_LYR3_ADDR1_REG0_ADDR  ALT_EMAC_GMAC_LYR3_ADDR1_REG0_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_LYR3_ADDR2_REG0 register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_LYR3_ADDR2_REG0_ADDR  ALT_EMAC_GMAC_LYR3_ADDR2_REG0_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_LYR3_ADDR3_REG0 register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_LYR3_ADDR3_REG0_ADDR  ALT_EMAC_GMAC_LYR3_ADDR3_REG0_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_L3_L4_CTL1 register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_L3_L4_CTL1_ADDR  ALT_EMAC_GMAC_L3_L4_CTL1_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_LYR4_ADDR1 register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_LYR4_ADDR1_ADDR  ALT_EMAC_GMAC_LYR4_ADDR1_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_LYR3_ADDR0_REG1 register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_LYR3_ADDR0_REG1_ADDR  ALT_EMAC_GMAC_LYR3_ADDR0_REG1_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_LYR3_ADDR1_REG1 register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_LYR3_ADDR1_REG1_ADDR  ALT_EMAC_GMAC_LYR3_ADDR1_REG1_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_LYR3_ADDR2_REG1 register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_LYR3_ADDR2_REG1_ADDR  ALT_EMAC_GMAC_LYR3_ADDR2_REG1_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_LYR3_ADDR3_REG1 register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_LYR3_ADDR3_REG1_ADDR  ALT_EMAC_GMAC_LYR3_ADDR3_REG1_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_L3_L4_CTL2 register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_L3_L4_CTL2_ADDR  ALT_EMAC_GMAC_L3_L4_CTL2_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_LYR4_ADDR2 register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_LYR4_ADDR2_ADDR  ALT_EMAC_GMAC_LYR4_ADDR2_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_LYR3_ADDR0_REG2 register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_LYR3_ADDR0_REG2_ADDR  ALT_EMAC_GMAC_LYR3_ADDR0_REG2_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_LYR3_ADDR1_REG2 register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_LYR3_ADDR1_REG2_ADDR  ALT_EMAC_GMAC_LYR3_ADDR1_REG2_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_LYR3_ADDR2_REG2 register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_LYR3_ADDR2_REG2_ADDR  ALT_EMAC_GMAC_LYR3_ADDR2_REG2_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_LYR3_ADDR3_REG2 register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_LYR3_ADDR3_REG2_ADDR  ALT_EMAC_GMAC_LYR3_ADDR3_REG2_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_L3_L4_CTL3 register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_L3_L4_CTL3_ADDR  ALT_EMAC_GMAC_L3_L4_CTL3_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_LYR4_ADDR3 register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_LYR4_ADDR3_ADDR  ALT_EMAC_GMAC_LYR4_ADDR3_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_LYR3_ADDR0_REG3 register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_LYR3_ADDR0_REG3_ADDR  ALT_EMAC_GMAC_LYR3_ADDR0_REG3_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_LYR3_ADDR1_REG3 register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_LYR3_ADDR1_REG3_ADDR  ALT_EMAC_GMAC_LYR3_ADDR1_REG3_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_LYR3_ADDR2_REG3 register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_LYR3_ADDR2_REG3_ADDR  ALT_EMAC_GMAC_LYR3_ADDR2_REG3_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_LYR3_ADDR3_REG3 register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_LYR3_ADDR3_REG3_ADDR  ALT_EMAC_GMAC_LYR3_ADDR3_REG3_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_HASH_TABLE_REG0 register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_HASH_TABLE_REG0_ADDR  ALT_EMAC_GMAC_HASH_TABLE_REG0_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_HASH_TABLE_REG1 register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_HASH_TABLE_REG1_ADDR  ALT_EMAC_GMAC_HASH_TABLE_REG1_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_HASH_TABLE_REG2 register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_HASH_TABLE_REG2_ADDR  ALT_EMAC_GMAC_HASH_TABLE_REG2_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_HASH_TABLE_REG3 register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_HASH_TABLE_REG3_ADDR  ALT_EMAC_GMAC_HASH_TABLE_REG3_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_HASH_TABLE_REG4 register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_HASH_TABLE_REG4_ADDR  ALT_EMAC_GMAC_HASH_TABLE_REG4_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_HASH_TABLE_REG5 register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_HASH_TABLE_REG5_ADDR  ALT_EMAC_GMAC_HASH_TABLE_REG5_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_HASH_TABLE_REG6 register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_HASH_TABLE_REG6_ADDR  ALT_EMAC_GMAC_HASH_TABLE_REG6_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_HASH_TABLE_REG7 register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_HASH_TABLE_REG7_ADDR  ALT_EMAC_GMAC_HASH_TABLE_REG7_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_VLAN_INCL_REG register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_VLAN_INCL_REG_ADDR  ALT_EMAC_GMAC_VLAN_INCL_REG_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_VLAN_HASH_TABLE_REG register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_VLAN_HASH_TABLE_REG_ADDR  ALT_EMAC_GMAC_VLAN_HASH_TABLE_REG_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_TS_CTL register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_TS_CTL_ADDR  ALT_EMAC_GMAC_TS_CTL_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_SUB_SEC_INCREMENT register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_SUB_SEC_INCREMENT_ADDR  ALT_EMAC_GMAC_SUB_SEC_INCREMENT_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_SYS_TIME_SECS register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_SYS_TIME_SECS_ADDR  ALT_EMAC_GMAC_SYS_TIME_SECS_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_SYS_TIME_NANOSECS register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_SYS_TIME_NANOSECS_ADDR  ALT_EMAC_GMAC_SYS_TIME_NANOSECS_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_SYS_TIME_SECS_UPDATE register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_SYS_TIME_SECS_UPDATE_ADDR  ALT_EMAC_GMAC_SYS_TIME_SECS_UPDATE_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_SYS_TIME_NANOSECS_UPDATE register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_SYS_TIME_NANOSECS_UPDATE_ADDR  ALT_EMAC_GMAC_SYS_TIME_NANOSECS_UPDATE_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_TS_ADDEND register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_TS_ADDEND_ADDR  ALT_EMAC_GMAC_TS_ADDEND_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_TGT_TIME_SECS register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_TGT_TIME_SECS_ADDR  ALT_EMAC_GMAC_TGT_TIME_SECS_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_TGT_TIME_NANOSECS register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_TGT_TIME_NANOSECS_ADDR  ALT_EMAC_GMAC_TGT_TIME_NANOSECS_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_SYS_TIME_HIGHER_WORD_SECS register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_SYS_TIME_HIGHER_WORD_SECS_ADDR  ALT_EMAC_GMAC_SYS_TIME_HIGHER_WORD_SECS_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_TS_STAT register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_TS_STAT_ADDR  ALT_EMAC_GMAC_TS_STAT_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_PPS_CTL register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_PPS_CTL_ADDR  ALT_EMAC_GMAC_PPS_CTL_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_AUX_TS_NANOSECS register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_AUX_TS_NANOSECS_ADDR  ALT_EMAC_GMAC_AUX_TS_NANOSECS_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_AUX_TS_SECS register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_AUX_TS_SECS_ADDR  ALT_EMAC_GMAC_AUX_TS_SECS_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_PPS0_INTERVAL register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_PPS0_INTERVAL_ADDR  ALT_EMAC_GMAC_PPS0_INTERVAL_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_PPS0_WIDTH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_PPS0_WIDTH_ADDR  ALT_EMAC_GMAC_PPS0_WIDTH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR16_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR16_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR16_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR16_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR16_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR16_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR17_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR17_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR17_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR17_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR17_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR17_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR18_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR18_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR18_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR18_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR18_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR18_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR19_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR19_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR19_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR19_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR19_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR19_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR20_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR20_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR20_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR20_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR20_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR20_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR21_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR21_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR21_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR21_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR21_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR21_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR22_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR22_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR22_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR22_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR22_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR22_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR23_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR23_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR23_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR23_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR23_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR23_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR24_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR24_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR24_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR24_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR24_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR24_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR25_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR25_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR25_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR25_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR25_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR25_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR26_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR26_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR26_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR26_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR26_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR26_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR27_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR27_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR27_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR27_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR27_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR27_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR28_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR28_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR28_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR28_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR28_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR28_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR29_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR29_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR29_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR29_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR29_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR29_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR30_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR30_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR30_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR30_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR30_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR30_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR31_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR31_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR31_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR31_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR31_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR31_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR32_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR32_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR32_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR32_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR32_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR32_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR33_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR33_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR33_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR33_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR33_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR33_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR34_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR34_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR34_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR34_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR34_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR34_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR35_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR35_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR35_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR35_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR35_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR35_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR36_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR36_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR36_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR36_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR36_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR36_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR37_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR37_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR37_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR37_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR37_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR37_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR38_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR38_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR38_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR38_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR38_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR38_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR39_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR39_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR39_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR39_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR39_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR39_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR40_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR40_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR40_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR40_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR40_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR40_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR41_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR41_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR41_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR41_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR41_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR41_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR42_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR42_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR42_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR42_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR42_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR42_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR43_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR43_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR43_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR43_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR43_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR43_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR44_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR44_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR44_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR44_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR44_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR44_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR45_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR45_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR45_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR45_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR45_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR45_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR46_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR46_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR46_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR46_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR46_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR46_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR47_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR47_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR47_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR47_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR47_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR47_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR48_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR48_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR48_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR48_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR48_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR48_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR49_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR49_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR49_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR49_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR49_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR49_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR50_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR50_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR50_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR50_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR50_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR50_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR51_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR51_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR51_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR51_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR51_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR51_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR52_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR52_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR52_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR52_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR52_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR52_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR53_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR53_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR53_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR53_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR53_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR53_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR54_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR54_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR54_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR54_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR54_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR54_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR55_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR55_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR55_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR55_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR55_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR55_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR56_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR56_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR56_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR56_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR56_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR56_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR57_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR57_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR57_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR57_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR57_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR57_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR58_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR58_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR58_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR58_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR58_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR58_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR59_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR59_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR59_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR59_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR59_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR59_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR60_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR60_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR60_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR60_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR60_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR60_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR61_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR61_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR61_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR61_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR61_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR61_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR62_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR62_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR62_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR62_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR62_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR62_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR63_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR63_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR63_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR63_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR63_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR63_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR64_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR64_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR64_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR64_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR64_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR64_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR65_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR65_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR65_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR65_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR65_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR65_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR66_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR66_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR66_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR66_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR66_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR66_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR67_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR67_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR67_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR67_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR67_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR67_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR68_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR68_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR68_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR68_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR68_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR68_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR69_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR69_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR69_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR69_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR69_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR69_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR70_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR70_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR70_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR70_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR70_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR70_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR71_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR71_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR71_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR71_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR71_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR71_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR72_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR72_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR72_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR72_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR72_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR72_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR73_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR73_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR73_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR73_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR73_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR73_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR74_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR74_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR74_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR74_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR74_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR74_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR75_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR75_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR75_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR75_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR75_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR75_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR76_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR76_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR76_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR76_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR76_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR76_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR77_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR77_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR77_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR77_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR77_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR77_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR78_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR78_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR78_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR78_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR78_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR78_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR79_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR79_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR79_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR79_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR79_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR79_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR80_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR80_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR80_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR80_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR80_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR80_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR81_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR81_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR81_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR81_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR81_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR81_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR82_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR82_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR82_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR82_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR82_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR82_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR83_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR83_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR83_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR83_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR83_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR83_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR84_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR84_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR84_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR84_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR84_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR84_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR85_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR85_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR85_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR85_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR85_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR85_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR86_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR86_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR86_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR86_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR86_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR86_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR87_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR87_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR87_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR87_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR87_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR87_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR88_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR88_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR88_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR88_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR88_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR88_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR89_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR89_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR89_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR89_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR89_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR89_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR90_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR90_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR90_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR90_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR90_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR90_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR91_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR91_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR91_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR91_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR91_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR91_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR92_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR92_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR92_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR92_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR92_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR92_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR93_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR93_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR93_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR93_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR93_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR93_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR94_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR94_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR94_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR94_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR94_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR94_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR95_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR95_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR95_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR95_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR95_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR95_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR96_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR96_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR96_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR96_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR96_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR96_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR97_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR97_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR97_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR97_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR97_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR97_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR98_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR98_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR98_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR98_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR98_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR98_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR99_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR99_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR99_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR99_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR99_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR99_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR100_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR100_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR100_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR100_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR100_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR100_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR101_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR101_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR101_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR101_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR101_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR101_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR102_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR102_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR102_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR102_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR102_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR102_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR103_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR103_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR103_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR103_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR103_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR103_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR104_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR104_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR104_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR104_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR104_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR104_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR105_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR105_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR105_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR105_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR105_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR105_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR106_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR106_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR106_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR106_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR106_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR106_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR107_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR107_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR107_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR107_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR107_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR107_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR108_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR108_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR108_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR108_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR108_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR108_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR109_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR109_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR109_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR109_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR109_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR109_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR110_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR110_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR110_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR110_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR110_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR110_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR111_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR111_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR111_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR111_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR111_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR111_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR112_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR112_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR112_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR112_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR112_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR112_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR113_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR113_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR113_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR113_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR113_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR113_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR114_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR114_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR114_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR114_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR114_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR114_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR115_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR115_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR115_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR115_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR115_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR115_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR116_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR116_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR116_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR116_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR116_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR116_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR117_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR117_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR117_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR117_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR117_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR117_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR118_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR118_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR118_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR118_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR118_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR118_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR119_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR119_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR119_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR119_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR119_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR119_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR120_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR120_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR120_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR120_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR120_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR120_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR121_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR121_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR121_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR121_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR121_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR121_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR122_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR122_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR122_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR122_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR122_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR122_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR123_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR123_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR123_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR123_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR123_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR123_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR124_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR124_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR124_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR124_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR124_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR124_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR125_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR125_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR125_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR125_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR125_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR125_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR126_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR126_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR126_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR126_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR126_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR126_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR127_HIGH register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR127_HIGH_ADDR  ALT_EMAC_GMAC_MAC_ADDR127_HIGH_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The address of the ALT_EMAC_GMAC_MAC_ADDR127_LOW register for the ALT_EMAC1_GMACGRP instance. */
#define ALT_EMAC1_GMAC_MAC_ADDR127_LOW_ADDR  ALT_EMAC_GMAC_MAC_ADDR127_LOW_ADDR(ALT_EMAC1_GMACGRP_ADDR)
/* The base address byte offset for the start of the ALT_EMAC1_GMACGRP component. */
#define ALT_EMAC1_GMACGRP_OFST        0x0
/* The start address of the ALT_EMAC1_GMACGRP component. */
#define ALT_EMAC1_GMACGRP_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_EMAC1_ADDR) + ALT_EMAC1_GMACGRP_OFST))
/* The lower bound address range of the ALT_EMAC1_GMACGRP component. */
#define ALT_EMAC1_GMACGRP_LB_ADDR     ALT_EMAC1_GMACGRP_ADDR
/* The upper bound address range of the ALT_EMAC1_GMACGRP component. */
#define ALT_EMAC1_GMACGRP_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_EMAC1_GMACGRP_ADDR) + 0xb80) - 1))


/*
 * Register Group Instance : dmagrp
 * 
 * Instance dmagrp of register group ALT_EMAC_DMA.
 * 
 * 
 */
/* The address of the ALT_EMAC_DMA_BUS_MOD register for the ALT_EMAC1_DMAGRP instance. */
#define ALT_EMAC1_DMA_BUS_MOD_ADDR  ALT_EMAC_DMA_BUS_MOD_ADDR(ALT_EMAC1_DMAGRP_ADDR)
/* The address of the ALT_EMAC_DMA_TX_POLL_DEMAND register for the ALT_EMAC1_DMAGRP instance. */
#define ALT_EMAC1_DMA_TX_POLL_DEMAND_ADDR  ALT_EMAC_DMA_TX_POLL_DEMAND_ADDR(ALT_EMAC1_DMAGRP_ADDR)
/* The address of the ALT_EMAC_DMA_RX_POLL_DEMAND register for the ALT_EMAC1_DMAGRP instance. */
#define ALT_EMAC1_DMA_RX_POLL_DEMAND_ADDR  ALT_EMAC_DMA_RX_POLL_DEMAND_ADDR(ALT_EMAC1_DMAGRP_ADDR)
/* The address of the ALT_EMAC_DMA_RX_DESC_LIST_ADDR register for the ALT_EMAC1_DMAGRP instance. */
#define ALT_EMAC1_DMA_RX_DESC_LIST_ADDR_ADDR  ALT_EMAC_DMA_RX_DESC_LIST_ADDR_ADDR(ALT_EMAC1_DMAGRP_ADDR)
/* The address of the ALT_EMAC_DMA_TX_DESC_LIST_ADDR register for the ALT_EMAC1_DMAGRP instance. */
#define ALT_EMAC1_DMA_TX_DESC_LIST_ADDR_ADDR  ALT_EMAC_DMA_TX_DESC_LIST_ADDR_ADDR(ALT_EMAC1_DMAGRP_ADDR)
/* The address of the ALT_EMAC_DMA_STAT register for the ALT_EMAC1_DMAGRP instance. */
#define ALT_EMAC1_DMA_STAT_ADDR  ALT_EMAC_DMA_STAT_ADDR(ALT_EMAC1_DMAGRP_ADDR)
/* The address of the ALT_EMAC_DMA_OP_MOD register for the ALT_EMAC1_DMAGRP instance. */
#define ALT_EMAC1_DMA_OP_MOD_ADDR  ALT_EMAC_DMA_OP_MOD_ADDR(ALT_EMAC1_DMAGRP_ADDR)
/* The address of the ALT_EMAC_DMA_INT_EN register for the ALT_EMAC1_DMAGRP instance. */
#define ALT_EMAC1_DMA_INT_EN_ADDR  ALT_EMAC_DMA_INT_EN_ADDR(ALT_EMAC1_DMAGRP_ADDR)
/* The address of the ALT_EMAC_DMA_MFRM_BUF_OVF_CNTR register for the ALT_EMAC1_DMAGRP instance. */
#define ALT_EMAC1_DMA_MISSED_FRM_AND_BUF_OVF_CNTR_ADDR  ALT_EMAC_DMA_MFRM_BUF_OVF_CNTR_ADDR(ALT_EMAC1_DMAGRP_ADDR)
/* The address of the ALT_EMAC_DMA_RX_INT_WDT register for the ALT_EMAC1_DMAGRP instance. */
#define ALT_EMAC1_DMA_RX_INT_WDT_ADDR  ALT_EMAC_DMA_RX_INT_WDT_ADDR(ALT_EMAC1_DMAGRP_ADDR)
/* The address of the ALT_EMAC_DMA_AXI_BUS_MOD register for the ALT_EMAC1_DMAGRP instance. */
#define ALT_EMAC1_DMA_AXI_BUS_MOD_ADDR  ALT_EMAC_DMA_AXI_BUS_MOD_ADDR(ALT_EMAC1_DMAGRP_ADDR)
/* The address of the ALT_EMAC_DMA_AHB_OR_AXI_STAT register for the ALT_EMAC1_DMAGRP instance. */
#define ALT_EMAC1_DMA_AHB_OR_AXI_STAT_ADDR  ALT_EMAC_DMA_AHB_OR_AXI_STAT_ADDR(ALT_EMAC1_DMAGRP_ADDR)
/* The address of the ALT_EMAC_DMA_CUR_HOST_TX_DESC register for the ALT_EMAC1_DMAGRP instance. */
#define ALT_EMAC1_DMA_CUR_HOST_TX_DESC_ADDR  ALT_EMAC_DMA_CUR_HOST_TX_DESC_ADDR(ALT_EMAC1_DMAGRP_ADDR)
/* The address of the ALT_EMAC_DMA_CUR_HOST_RX_DESC register for the ALT_EMAC1_DMAGRP instance. */
#define ALT_EMAC1_DMA_CUR_HOST_RX_DESC_ADDR  ALT_EMAC_DMA_CUR_HOST_RX_DESC_ADDR(ALT_EMAC1_DMAGRP_ADDR)
/* The address of the ALT_EMAC_DMA_CUR_HOST_TX_BUF_ADDR register for the ALT_EMAC1_DMAGRP instance. */
#define ALT_EMAC1_DMA_CUR_HOST_TX_BUF_ADDR_ADDR  ALT_EMAC_DMA_CUR_HOST_TX_BUF_ADDR_ADDR(ALT_EMAC1_DMAGRP_ADDR)
/* The address of the ALT_EMAC_DMA_CUR_HOST_RX_BUF_ADDR register for the ALT_EMAC1_DMAGRP instance. */
#define ALT_EMAC1_DMA_CUR_HOST_RX_BUF_ADDR_ADDR  ALT_EMAC_DMA_CUR_HOST_RX_BUF_ADDR_ADDR(ALT_EMAC1_DMAGRP_ADDR)
/* The address of the ALT_EMAC_DMA_HW_FEATURE register for the ALT_EMAC1_DMAGRP instance. */
#define ALT_EMAC1_DMA_HW_FEATURE_ADDR  ALT_EMAC_DMA_HW_FEATURE_ADDR(ALT_EMAC1_DMAGRP_ADDR)
/* The base address byte offset for the start of the ALT_EMAC1_DMAGRP component. */
#define ALT_EMAC1_DMAGRP_OFST        0x1000
/* The start address of the ALT_EMAC1_DMAGRP component. */
#define ALT_EMAC1_DMAGRP_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_EMAC1_ADDR) + ALT_EMAC1_DMAGRP_OFST))
/* The lower bound address range of the ALT_EMAC1_DMAGRP component. */
#define ALT_EMAC1_DMAGRP_LB_ADDR     ALT_EMAC1_DMAGRP_ADDR
/* The upper bound address range of the ALT_EMAC1_DMAGRP component. */
#define ALT_EMAC1_DMAGRP_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_EMAC1_DMAGRP_ADDR) + 0x5c) - 1))


/* The base address byte offset for the start of the ALT_EMAC1 component. */
#define ALT_EMAC1_OFST        0xff702000
/* The start address of the ALT_EMAC1 component. */
#define ALT_EMAC1_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_HPS_ADDR) + ALT_EMAC1_OFST))
/* The lower bound address range of the ALT_EMAC1 component. */
#define ALT_EMAC1_LB_ADDR     ALT_EMAC1_ADDR
/* The upper bound address range of the ALT_EMAC1 component. */
#define ALT_EMAC1_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_EMAC1_ADDR) + 0x2000) - 1))


/*
 * Component Instance : sdmmc
 * 
 * Instance sdmmc of component ALT_SDMMC.
 * 
 * 
 */
/* The address of the ALT_SDMMC_CTL register for the ALT_SDMMC instance. */
#define ALT_SDMMC_CTL_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDMMC_ADDR) + ALT_SDMMC_CTL_OFST))
/* The address of the ALT_SDMMC_PWREN register for the ALT_SDMMC instance. */
#define ALT_SDMMC_PWREN_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDMMC_ADDR) + ALT_SDMMC_PWREN_OFST))
/* The address of the ALT_SDMMC_CLKDIV register for the ALT_SDMMC instance. */
#define ALT_SDMMC_CLKDIV_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDMMC_ADDR) + ALT_SDMMC_CLKDIV_OFST))
/* The address of the ALT_SDMMC_CLKSRC register for the ALT_SDMMC instance. */
#define ALT_SDMMC_CLKSRC_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDMMC_ADDR) + ALT_SDMMC_CLKSRC_OFST))
/* The address of the ALT_SDMMC_CLKENA register for the ALT_SDMMC instance. */
#define ALT_SDMMC_CLKENA_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDMMC_ADDR) + ALT_SDMMC_CLKENA_OFST))
/* The address of the ALT_SDMMC_TMOUT register for the ALT_SDMMC instance. */
#define ALT_SDMMC_TMOUT_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDMMC_ADDR) + ALT_SDMMC_TMOUT_OFST))
/* The address of the ALT_SDMMC_CTYPE register for the ALT_SDMMC instance. */
#define ALT_SDMMC_CTYPE_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDMMC_ADDR) + ALT_SDMMC_CTYPE_OFST))
/* The address of the ALT_SDMMC_BLKSIZ register for the ALT_SDMMC instance. */
#define ALT_SDMMC_BLKSIZ_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDMMC_ADDR) + ALT_SDMMC_BLKSIZ_OFST))
/* The address of the ALT_SDMMC_BYTCNT register for the ALT_SDMMC instance. */
#define ALT_SDMMC_BYTCNT_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDMMC_ADDR) + ALT_SDMMC_BYTCNT_OFST))
/* The address of the ALT_SDMMC_INTMSK register for the ALT_SDMMC instance. */
#define ALT_SDMMC_INTMSK_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDMMC_ADDR) + ALT_SDMMC_INTMSK_OFST))
/* The address of the ALT_SDMMC_CMDARG register for the ALT_SDMMC instance. */
#define ALT_SDMMC_CMDARG_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDMMC_ADDR) + ALT_SDMMC_CMDARG_OFST))
/* The address of the ALT_SDMMC_CMD register for the ALT_SDMMC instance. */
#define ALT_SDMMC_CMD_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDMMC_ADDR) + ALT_SDMMC_CMD_OFST))
/* The address of the ALT_SDMMC_RESP0 register for the ALT_SDMMC instance. */
#define ALT_SDMMC_RESP0_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDMMC_ADDR) + ALT_SDMMC_RESP0_OFST))
/* The address of the ALT_SDMMC_RESP1 register for the ALT_SDMMC instance. */
#define ALT_SDMMC_RESP1_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDMMC_ADDR) + ALT_SDMMC_RESP1_OFST))
/* The address of the ALT_SDMMC_RESP2 register for the ALT_SDMMC instance. */
#define ALT_SDMMC_RESP2_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDMMC_ADDR) + ALT_SDMMC_RESP2_OFST))
/* The address of the ALT_SDMMC_RESP3 register for the ALT_SDMMC instance. */
#define ALT_SDMMC_RESP3_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDMMC_ADDR) + ALT_SDMMC_RESP3_OFST))
/* The address of the ALT_SDMMC_MINTSTS register for the ALT_SDMMC instance. */
#define ALT_SDMMC_MINTSTS_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDMMC_ADDR) + ALT_SDMMC_MINTSTS_OFST))
/* The address of the ALT_SDMMC_RINTSTS register for the ALT_SDMMC instance. */
#define ALT_SDMMC_RINTSTS_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDMMC_ADDR) + ALT_SDMMC_RINTSTS_OFST))
/* The address of the ALT_SDMMC_STAT register for the ALT_SDMMC instance. */
#define ALT_SDMMC_STAT_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDMMC_ADDR) + ALT_SDMMC_STAT_OFST))
/* The address of the ALT_SDMMC_FIFOTH register for the ALT_SDMMC instance. */
#define ALT_SDMMC_FIFOTH_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDMMC_ADDR) + ALT_SDMMC_FIFOTH_OFST))
/* The address of the ALT_SDMMC_CDETECT register for the ALT_SDMMC instance. */
#define ALT_SDMMC_CDETECT_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDMMC_ADDR) + ALT_SDMMC_CDETECT_OFST))
/* The address of the ALT_SDMMC_WRTPRT register for the ALT_SDMMC instance. */
#define ALT_SDMMC_WRTPRT_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDMMC_ADDR) + ALT_SDMMC_WRTPRT_OFST))
/* The address of the ALT_SDMMC_TCBCNT register for the ALT_SDMMC instance. */
#define ALT_SDMMC_TCBCNT_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDMMC_ADDR) + ALT_SDMMC_TCBCNT_OFST))
/* The address of the ALT_SDMMC_TBBCNT register for the ALT_SDMMC instance. */
#define ALT_SDMMC_TBBCNT_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDMMC_ADDR) + ALT_SDMMC_TBBCNT_OFST))
/* The address of the ALT_SDMMC_DEBNCE register for the ALT_SDMMC instance. */
#define ALT_SDMMC_DEBNCE_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDMMC_ADDR) + ALT_SDMMC_DEBNCE_OFST))
/* The address of the ALT_SDMMC_USRID register for the ALT_SDMMC instance. */
#define ALT_SDMMC_USRID_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDMMC_ADDR) + ALT_SDMMC_USRID_OFST))
/* The address of the ALT_SDMMC_VERID register for the ALT_SDMMC instance. */
#define ALT_SDMMC_VERID_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDMMC_ADDR) + ALT_SDMMC_VERID_OFST))
/* The address of the ALT_SDMMC_HCON register for the ALT_SDMMC instance. */
#define ALT_SDMMC_HCON_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDMMC_ADDR) + ALT_SDMMC_HCON_OFST))
/* The address of the ALT_SDMMC_UHS_REG register for the ALT_SDMMC instance. */
#define ALT_SDMMC_UHS_REG_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDMMC_ADDR) + ALT_SDMMC_UHS_REG_OFST))
/* The address of the ALT_SDMMC_RST_N register for the ALT_SDMMC instance. */
#define ALT_SDMMC_RST_N_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDMMC_ADDR) + ALT_SDMMC_RST_N_OFST))
/* The address of the ALT_SDMMC_BMOD register for the ALT_SDMMC instance. */
#define ALT_SDMMC_BMOD_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDMMC_ADDR) + ALT_SDMMC_BMOD_OFST))
/* The address of the ALT_SDMMC_PLDMND register for the ALT_SDMMC instance. */
#define ALT_SDMMC_PLDMND_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDMMC_ADDR) + ALT_SDMMC_PLDMND_OFST))
/* The address of the ALT_SDMMC_DBADDR register for the ALT_SDMMC instance. */
#define ALT_SDMMC_DBADDR_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDMMC_ADDR) + ALT_SDMMC_DBADDR_OFST))
/* The address of the ALT_SDMMC_IDSTS register for the ALT_SDMMC instance. */
#define ALT_SDMMC_IDSTS_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDMMC_ADDR) + ALT_SDMMC_IDSTS_OFST))
/* The address of the ALT_SDMMC_IDINTEN register for the ALT_SDMMC instance. */
#define ALT_SDMMC_IDINTEN_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDMMC_ADDR) + ALT_SDMMC_IDINTEN_OFST))
/* The address of the ALT_SDMMC_DSCADDR register for the ALT_SDMMC instance. */
#define ALT_SDMMC_DSCADDR_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDMMC_ADDR) + ALT_SDMMC_DSCADDR_OFST))
/* The address of the ALT_SDMMC_BUFADDR register for the ALT_SDMMC instance. */
#define ALT_SDMMC_BUFADDR_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDMMC_ADDR) + ALT_SDMMC_BUFADDR_OFST))
/* The address of the ALT_SDMMC_CARDTHRCTL register for the ALT_SDMMC instance. */
#define ALT_SDMMC_CARDTHRCTL_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDMMC_ADDR) + ALT_SDMMC_CARDTHRCTL_OFST))
/* The address of the ALT_SDMMC_BACK_END_POWER_R register for the ALT_SDMMC instance. */
#define ALT_SDMMC_BACK_END_POWER_R_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDMMC_ADDR) + ALT_SDMMC_BACK_END_POWER_R_OFST))
/* The address of the ALT_SDMMC_DATA register for the ALT_SDMMC instance. */
#define ALT_SDMMC_DATA_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDMMC_ADDR) + ALT_SDMMC_DATA_OFST))
/* The base address byte offset for the start of the ALT_SDMMC component. */
#define ALT_SDMMC_OFST        0xff704000
/* The start address of the ALT_SDMMC component. */
#define ALT_SDMMC_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_HPS_ADDR) + ALT_SDMMC_OFST))
/* The lower bound address range of the ALT_SDMMC component. */
#define ALT_SDMMC_LB_ADDR     ALT_SDMMC_ADDR
/* The upper bound address range of the ALT_SDMMC component. */
#define ALT_SDMMC_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_SDMMC_ADDR) + 0x400) - 1))


/*
 * Component Instance : qspiregs
 * 
 * Instance qspiregs of component ALT_QSPI.
 * 
 * 
 */
/* The address of the ALT_QSPI_CFG register for the ALT_QSPI instance. */
#define ALT_QSPI_CFG_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_QSPI_ADDR) + ALT_QSPI_CFG_OFST))
/* The address of the ALT_QSPI_DEVRD register for the ALT_QSPI instance. */
#define ALT_QSPI_DEVRD_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_QSPI_ADDR) + ALT_QSPI_DEVRD_OFST))
/* The address of the ALT_QSPI_DEVWR register for the ALT_QSPI instance. */
#define ALT_QSPI_DEVWR_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_QSPI_ADDR) + ALT_QSPI_DEVWR_OFST))
/* The address of the ALT_QSPI_DELAY register for the ALT_QSPI instance. */
#define ALT_QSPI_DELAY_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_QSPI_ADDR) + ALT_QSPI_DELAY_OFST))
/* The address of the ALT_QSPI_RDDATACAP register for the ALT_QSPI instance. */
#define ALT_QSPI_RDDATACAP_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_QSPI_ADDR) + ALT_QSPI_RDDATACAP_OFST))
/* The address of the ALT_QSPI_DEVSZ register for the ALT_QSPI instance. */
#define ALT_QSPI_DEVSZ_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_QSPI_ADDR) + ALT_QSPI_DEVSZ_OFST))
/* The address of the ALT_QSPI_SRAMPART register for the ALT_QSPI instance. */
#define ALT_QSPI_SRAMPART_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_QSPI_ADDR) + ALT_QSPI_SRAMPART_OFST))
/* The address of the ALT_QSPI_INDADDRTRIG register for the ALT_QSPI instance. */
#define ALT_QSPI_INDADDRTRIG_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_QSPI_ADDR) + ALT_QSPI_INDADDRTRIG_OFST))
/* The address of the ALT_QSPI_DMAPER register for the ALT_QSPI instance. */
#define ALT_QSPI_DMAPER_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_QSPI_ADDR) + ALT_QSPI_DMAPER_OFST))
/* The address of the ALT_QSPI_REMAPADDR register for the ALT_QSPI instance. */
#define ALT_QSPI_REMAPADDR_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_QSPI_ADDR) + ALT_QSPI_REMAPADDR_OFST))
/* The address of the ALT_QSPI_MODBIT register for the ALT_QSPI instance. */
#define ALT_QSPI_MODBIT_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_QSPI_ADDR) + ALT_QSPI_MODBIT_OFST))
/* The address of the ALT_QSPI_SRAMFILL register for the ALT_QSPI instance. */
#define ALT_QSPI_SRAMFILL_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_QSPI_ADDR) + ALT_QSPI_SRAMFILL_OFST))
/* The address of the ALT_QSPI_TXTHRESH register for the ALT_QSPI instance. */
#define ALT_QSPI_TXTHRESH_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_QSPI_ADDR) + ALT_QSPI_TXTHRESH_OFST))
/* The address of the ALT_QSPI_RXTHRESH register for the ALT_QSPI instance. */
#define ALT_QSPI_RXTHRESH_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_QSPI_ADDR) + ALT_QSPI_RXTHRESH_OFST))
/* The address of the ALT_QSPI_IRQSTAT register for the ALT_QSPI instance. */
#define ALT_QSPI_IRQSTAT_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_QSPI_ADDR) + ALT_QSPI_IRQSTAT_OFST))
/* The address of the ALT_QSPI_IRQMSK register for the ALT_QSPI instance. */
#define ALT_QSPI_IRQMSK_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_QSPI_ADDR) + ALT_QSPI_IRQMSK_OFST))
/* The address of the ALT_QSPI_LOWWRPROT register for the ALT_QSPI instance. */
#define ALT_QSPI_LOWWRPROT_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_QSPI_ADDR) + ALT_QSPI_LOWWRPROT_OFST))
/* The address of the ALT_QSPI_UPPWRPROT register for the ALT_QSPI instance. */
#define ALT_QSPI_UPPWRPROT_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_QSPI_ADDR) + ALT_QSPI_UPPWRPROT_OFST))
/* The address of the ALT_QSPI_WRPROT register for the ALT_QSPI instance. */
#define ALT_QSPI_WRPROT_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_QSPI_ADDR) + ALT_QSPI_WRPROT_OFST))
/* The address of the ALT_QSPI_INDRD register for the ALT_QSPI instance. */
#define ALT_QSPI_INDRD_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_QSPI_ADDR) + ALT_QSPI_INDRD_OFST))
/* The address of the ALT_QSPI_INDRDWATER register for the ALT_QSPI instance. */
#define ALT_QSPI_INDRDWATER_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_QSPI_ADDR) + ALT_QSPI_INDRDWATER_OFST))
/* The address of the ALT_QSPI_INDRDSTADDR register for the ALT_QSPI instance. */
#define ALT_QSPI_INDRDSTADDR_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_QSPI_ADDR) + ALT_QSPI_INDRDSTADDR_OFST))
/* The address of the ALT_QSPI_INDRDCNT register for the ALT_QSPI instance. */
#define ALT_QSPI_INDRDCNT_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_QSPI_ADDR) + ALT_QSPI_INDRDCNT_OFST))
/* The address of the ALT_QSPI_INDWR register for the ALT_QSPI instance. */
#define ALT_QSPI_INDWR_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_QSPI_ADDR) + ALT_QSPI_INDWR_OFST))
/* The address of the ALT_QSPI_INDWRWATER register for the ALT_QSPI instance. */
#define ALT_QSPI_INDWRWATER_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_QSPI_ADDR) + ALT_QSPI_INDWRWATER_OFST))
/* The address of the ALT_QSPI_INDWRSTADDR register for the ALT_QSPI instance. */
#define ALT_QSPI_INDWRSTADDR_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_QSPI_ADDR) + ALT_QSPI_INDWRSTADDR_OFST))
/* The address of the ALT_QSPI_INDWRCNT register for the ALT_QSPI instance. */
#define ALT_QSPI_INDWRCNT_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_QSPI_ADDR) + ALT_QSPI_INDWRCNT_OFST))
/* The address of the ALT_QSPI_FLSHCMD register for the ALT_QSPI instance. */
#define ALT_QSPI_FLSHCMD_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_QSPI_ADDR) + ALT_QSPI_FLSHCMD_OFST))
/* The address of the ALT_QSPI_FLSHCMDADDR register for the ALT_QSPI instance. */
#define ALT_QSPI_FLSHCMDADDR_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_QSPI_ADDR) + ALT_QSPI_FLSHCMDADDR_OFST))
/* The address of the ALT_QSPI_FLSHCMDRDDATALO register for the ALT_QSPI instance. */
#define ALT_QSPI_FLSHCMDRDDATALO_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_QSPI_ADDR) + ALT_QSPI_FLSHCMDRDDATALO_OFST))
/* The address of the ALT_QSPI_FLSHCMDRDDATAUP register for the ALT_QSPI instance. */
#define ALT_QSPI_FLSHCMDRDDATAUP_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_QSPI_ADDR) + ALT_QSPI_FLSHCMDRDDATAUP_OFST))
/* The address of the ALT_QSPI_FLSHCMDWRDATALO register for the ALT_QSPI instance. */
#define ALT_QSPI_FLSHCMDWRDATALO_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_QSPI_ADDR) + ALT_QSPI_FLSHCMDWRDATALO_OFST))
/* The address of the ALT_QSPI_FLSHCMDWRDATAUP register for the ALT_QSPI instance. */
#define ALT_QSPI_FLSHCMDWRDATAUP_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_QSPI_ADDR) + ALT_QSPI_FLSHCMDWRDATAUP_OFST))
/* The address of the ALT_QSPI_MODULEID register for the ALT_QSPI instance. */
#define ALT_QSPI_MODULEID_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_QSPI_ADDR) + ALT_QSPI_MODULEID_OFST))
/* The base address byte offset for the start of the ALT_QSPI component. */
#define ALT_QSPI_OFST        0xff705000
/* The start address of the ALT_QSPI component. */
#define ALT_QSPI_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_HPS_ADDR) + ALT_QSPI_OFST))
/* The lower bound address range of the ALT_QSPI component. */
#define ALT_QSPI_LB_ADDR     ALT_QSPI_ADDR
/* The upper bound address range of the ALT_QSPI component. */
#define ALT_QSPI_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_QSPI_ADDR) + 0x100) - 1))


/*
 * Component Instance : fpgamgrregs
 * 
 * Instance fpgamgrregs of component ALT_FPGAMGR.
 * 
 * 
 */
/* The address of the ALT_FPGAMGR_STAT register for the ALT_FPGAMGR instance. */
#define ALT_FPGAMGR_STAT_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_FPGAMGR_ADDR) + ALT_FPGAMGR_STAT_OFST))
/* The address of the ALT_FPGAMGR_CTL register for the ALT_FPGAMGR instance. */
#define ALT_FPGAMGR_CTL_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_FPGAMGR_ADDR) + ALT_FPGAMGR_CTL_OFST))
/* The address of the ALT_FPGAMGR_DCLKCNT register for the ALT_FPGAMGR instance. */
#define ALT_FPGAMGR_DCLKCNT_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_FPGAMGR_ADDR) + ALT_FPGAMGR_DCLKCNT_OFST))
/* The address of the ALT_FPGAMGR_DCLKSTAT register for the ALT_FPGAMGR instance. */
#define ALT_FPGAMGR_DCLKSTAT_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_FPGAMGR_ADDR) + ALT_FPGAMGR_DCLKSTAT_OFST))
/* The address of the ALT_FPGAMGR_GPO register for the ALT_FPGAMGR instance. */
#define ALT_FPGAMGR_GPO_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_FPGAMGR_ADDR) + ALT_FPGAMGR_GPO_OFST))
/* The address of the ALT_FPGAMGR_GPI register for the ALT_FPGAMGR instance. */
#define ALT_FPGAMGR_GPI_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_FPGAMGR_ADDR) + ALT_FPGAMGR_GPI_OFST))
/* The address of the ALT_FPGAMGR_MISCI register for the ALT_FPGAMGR instance. */
#define ALT_FPGAMGR_MISCI_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_FPGAMGR_ADDR) + ALT_FPGAMGR_MISCI_OFST))
/*
 * Register Group Instance : mon
 * 
 * Instance mon of register group ALT_MON.
 * 
 * 
 */
/* The address of the ALT_MON_GPIO_INTEN register for the ALT_FPGAMGR_MON instance. */
#define ALT_FPGAMGR_MON_GPIO_INTEN_ADDR  ALT_MON_GPIO_INTEN_ADDR(ALT_FPGAMGR_MON_ADDR)
/* The address of the ALT_MON_GPIO_INTMSK register for the ALT_FPGAMGR_MON instance. */
#define ALT_FPGAMGR_MON_GPIO_INTMSK_ADDR  ALT_MON_GPIO_INTMSK_ADDR(ALT_FPGAMGR_MON_ADDR)
/* The address of the ALT_MON_GPIO_INTTYPE_LEVEL register for the ALT_FPGAMGR_MON instance. */
#define ALT_FPGAMGR_MON_GPIO_INTTYPE_LEVEL_ADDR  ALT_MON_GPIO_INTTYPE_LEVEL_ADDR(ALT_FPGAMGR_MON_ADDR)
/* The address of the ALT_MON_GPIO_INT_POL register for the ALT_FPGAMGR_MON instance. */
#define ALT_FPGAMGR_MON_GPIO_INT_POL_ADDR  ALT_MON_GPIO_INT_POL_ADDR(ALT_FPGAMGR_MON_ADDR)
/* The address of the ALT_MON_GPIO_INTSTAT register for the ALT_FPGAMGR_MON instance. */
#define ALT_FPGAMGR_MON_GPIO_INTSTAT_ADDR  ALT_MON_GPIO_INTSTAT_ADDR(ALT_FPGAMGR_MON_ADDR)
/* The address of the ALT_MON_GPIO_RAW_INTSTAT register for the ALT_FPGAMGR_MON instance. */
#define ALT_FPGAMGR_MON_GPIO_RAW_INTSTAT_ADDR  ALT_MON_GPIO_RAW_INTSTAT_ADDR(ALT_FPGAMGR_MON_ADDR)
/* The address of the ALT_MON_GPIO_PORTA_EOI register for the ALT_FPGAMGR_MON instance. */
#define ALT_FPGAMGR_MON_GPIO_PORTA_EOI_ADDR  ALT_MON_GPIO_PORTA_EOI_ADDR(ALT_FPGAMGR_MON_ADDR)
/* The address of the ALT_MON_GPIO_EXT_PORTA register for the ALT_FPGAMGR_MON instance. */
#define ALT_FPGAMGR_MON_GPIO_EXT_PORTA_ADDR  ALT_MON_GPIO_EXT_PORTA_ADDR(ALT_FPGAMGR_MON_ADDR)
/* The address of the ALT_MON_GPIO_LS_SYNC register for the ALT_FPGAMGR_MON instance. */
#define ALT_FPGAMGR_MON_GPIO_LS_SYNC_ADDR  ALT_MON_GPIO_LS_SYNC_ADDR(ALT_FPGAMGR_MON_ADDR)
/* The address of the ALT_MON_GPIO_VER_ID_CODE register for the ALT_FPGAMGR_MON instance. */
#define ALT_FPGAMGR_MON_GPIO_VER_ID_CODE_ADDR  ALT_MON_GPIO_VER_ID_CODE_ADDR(ALT_FPGAMGR_MON_ADDR)
/* The address of the ALT_MON_GPIO_CFG_REG2 register for the ALT_FPGAMGR_MON instance. */
#define ALT_FPGAMGR_MON_GPIO_CFG_REG2_ADDR  ALT_MON_GPIO_CFG_REG2_ADDR(ALT_FPGAMGR_MON_ADDR)
/* The address of the ALT_MON_GPIO_CFG_REG1 register for the ALT_FPGAMGR_MON instance. */
#define ALT_FPGAMGR_MON_GPIO_CFG_REG1_ADDR  ALT_MON_GPIO_CFG_REG1_ADDR(ALT_FPGAMGR_MON_ADDR)
/* The base address byte offset for the start of the ALT_FPGAMGR_MON component. */
#define ALT_FPGAMGR_MON_OFST        0x800
/* The start address of the ALT_FPGAMGR_MON component. */
#define ALT_FPGAMGR_MON_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_FPGAMGR_ADDR) + ALT_FPGAMGR_MON_OFST))
/* The lower bound address range of the ALT_FPGAMGR_MON component. */
#define ALT_FPGAMGR_MON_LB_ADDR     ALT_FPGAMGR_MON_ADDR
/* The upper bound address range of the ALT_FPGAMGR_MON component. */
#define ALT_FPGAMGR_MON_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_FPGAMGR_MON_ADDR) + 0x80) - 1))


/* The base address byte offset for the start of the ALT_FPGAMGR component. */
#define ALT_FPGAMGR_OFST        0xff706000
/* The start address of the ALT_FPGAMGR component. */
#define ALT_FPGAMGR_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_HPS_ADDR) + ALT_FPGAMGR_OFST))
/* The lower bound address range of the ALT_FPGAMGR component. */
#define ALT_FPGAMGR_LB_ADDR     ALT_FPGAMGR_ADDR
/* The upper bound address range of the ALT_FPGAMGR component. */
#define ALT_FPGAMGR_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_FPGAMGR_ADDR) + 0x1000) - 1))


/*
 * Component Instance : acpidmap
 * 
 * Instance acpidmap of component ALT_ACPIDMAP.
 * 
 * 
 */
/* The address of the ALT_ACPIDMAP_VID2RD register for the ALT_ACPIDMAP instance. */
#define ALT_ACPIDMAP_VID2RD_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_ACPIDMAP_ADDR) + ALT_ACPIDMAP_VID2RD_OFST))
/* The address of the ALT_ACPIDMAP_VID2WR register for the ALT_ACPIDMAP instance. */
#define ALT_ACPIDMAP_VID2WR_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_ACPIDMAP_ADDR) + ALT_ACPIDMAP_VID2WR_OFST))
/* The address of the ALT_ACPIDMAP_VID3RD register for the ALT_ACPIDMAP instance. */
#define ALT_ACPIDMAP_VID3RD_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_ACPIDMAP_ADDR) + ALT_ACPIDMAP_VID3RD_OFST))
/* The address of the ALT_ACPIDMAP_VID3WR register for the ALT_ACPIDMAP instance. */
#define ALT_ACPIDMAP_VID3WR_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_ACPIDMAP_ADDR) + ALT_ACPIDMAP_VID3WR_OFST))
/* The address of the ALT_ACPIDMAP_VID4RD register for the ALT_ACPIDMAP instance. */
#define ALT_ACPIDMAP_VID4RD_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_ACPIDMAP_ADDR) + ALT_ACPIDMAP_VID4RD_OFST))
/* The address of the ALT_ACPIDMAP_VID4WR register for the ALT_ACPIDMAP instance. */
#define ALT_ACPIDMAP_VID4WR_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_ACPIDMAP_ADDR) + ALT_ACPIDMAP_VID4WR_OFST))
/* The address of the ALT_ACPIDMAP_VID5RD register for the ALT_ACPIDMAP instance. */
#define ALT_ACPIDMAP_VID5RD_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_ACPIDMAP_ADDR) + ALT_ACPIDMAP_VID5RD_OFST))
/* The address of the ALT_ACPIDMAP_VID5WR register for the ALT_ACPIDMAP instance. */
#define ALT_ACPIDMAP_VID5WR_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_ACPIDMAP_ADDR) + ALT_ACPIDMAP_VID5WR_OFST))
/* The address of the ALT_ACPIDMAP_VID6RD register for the ALT_ACPIDMAP instance. */
#define ALT_ACPIDMAP_VID6RD_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_ACPIDMAP_ADDR) + ALT_ACPIDMAP_VID6RD_OFST))
/* The address of the ALT_ACPIDMAP_VID6WR register for the ALT_ACPIDMAP instance. */
#define ALT_ACPIDMAP_VID6WR_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_ACPIDMAP_ADDR) + ALT_ACPIDMAP_VID6WR_OFST))
/* The address of the ALT_ACPIDMAP_DYNRD register for the ALT_ACPIDMAP instance. */
#define ALT_ACPIDMAP_DYNRD_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_ACPIDMAP_ADDR) + ALT_ACPIDMAP_DYNRD_OFST))
/* The address of the ALT_ACPIDMAP_DYNWR register for the ALT_ACPIDMAP instance. */
#define ALT_ACPIDMAP_DYNWR_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_ACPIDMAP_ADDR) + ALT_ACPIDMAP_DYNWR_OFST))
/* The address of the ALT_ACPIDMAP_VID2RD_S register for the ALT_ACPIDMAP instance. */
#define ALT_ACPIDMAP_VID2RD_S_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_ACPIDMAP_ADDR) + ALT_ACPIDMAP_VID2RD_S_OFST))
/* The address of the ALT_ACPIDMAP_VID2WR_S register for the ALT_ACPIDMAP instance. */
#define ALT_ACPIDMAP_VID2WR_S_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_ACPIDMAP_ADDR) + ALT_ACPIDMAP_VID2WR_S_OFST))
/* The address of the ALT_ACPIDMAP_VID3RD_S register for the ALT_ACPIDMAP instance. */
#define ALT_ACPIDMAP_VID3RD_S_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_ACPIDMAP_ADDR) + ALT_ACPIDMAP_VID3RD_S_OFST))
/* The address of the ALT_ACPIDMAP_VID3WR_S register for the ALT_ACPIDMAP instance. */
#define ALT_ACPIDMAP_VID3WR_S_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_ACPIDMAP_ADDR) + ALT_ACPIDMAP_VID3WR_S_OFST))
/* The address of the ALT_ACPIDMAP_VID4RD_S register for the ALT_ACPIDMAP instance. */
#define ALT_ACPIDMAP_VID4RD_S_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_ACPIDMAP_ADDR) + ALT_ACPIDMAP_VID4RD_S_OFST))
/* The address of the ALT_ACPIDMAP_VID4WR_S register for the ALT_ACPIDMAP instance. */
#define ALT_ACPIDMAP_VID4WR_S_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_ACPIDMAP_ADDR) + ALT_ACPIDMAP_VID4WR_S_OFST))
/* The address of the ALT_ACPIDMAP_VID5RD_S register for the ALT_ACPIDMAP instance. */
#define ALT_ACPIDMAP_VID5RD_S_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_ACPIDMAP_ADDR) + ALT_ACPIDMAP_VID5RD_S_OFST))
/* The address of the ALT_ACPIDMAP_VID5WR_S register for the ALT_ACPIDMAP instance. */
#define ALT_ACPIDMAP_VID5WR_S_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_ACPIDMAP_ADDR) + ALT_ACPIDMAP_VID5WR_S_OFST))
/* The address of the ALT_ACPIDMAP_VID6RD_S register for the ALT_ACPIDMAP instance. */
#define ALT_ACPIDMAP_VID6RD_S_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_ACPIDMAP_ADDR) + ALT_ACPIDMAP_VID6RD_S_OFST))
/* The address of the ALT_ACPIDMAP_VID6WR_S register for the ALT_ACPIDMAP instance. */
#define ALT_ACPIDMAP_VID6WR_S_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_ACPIDMAP_ADDR) + ALT_ACPIDMAP_VID6WR_S_OFST))
/* The address of the ALT_ACPIDMAP_DYNRD_S register for the ALT_ACPIDMAP instance. */
#define ALT_ACPIDMAP_DYNRD_S_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_ACPIDMAP_ADDR) + ALT_ACPIDMAP_DYNRD_S_OFST))
/* The address of the ALT_ACPIDMAP_DYNWR_S register for the ALT_ACPIDMAP instance. */
#define ALT_ACPIDMAP_DYNWR_S_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_ACPIDMAP_ADDR) + ALT_ACPIDMAP_DYNWR_S_OFST))
/* The base address byte offset for the start of the ALT_ACPIDMAP component. */
#define ALT_ACPIDMAP_OFST        0xff707000
/* The start address of the ALT_ACPIDMAP component. */
#define ALT_ACPIDMAP_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_HPS_ADDR) + ALT_ACPIDMAP_OFST))
/* The lower bound address range of the ALT_ACPIDMAP component. */
#define ALT_ACPIDMAP_LB_ADDR     ALT_ACPIDMAP_ADDR
/* The upper bound address range of the ALT_ACPIDMAP component. */
#define ALT_ACPIDMAP_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_ACPIDMAP_ADDR) + 0x1000) - 1))


/*
 * Component Instance : gpio0
 * 
 * Instance gpio0 of component ALT_GPIO.
 * 
 * 
 */
/* The address of the ALT_GPIO_SWPORTA_DR register for the ALT_GPIO0 instance. */
#define ALT_GPIO0_SWPORTA_DR_ADDR  ALT_GPIO_SWPORTA_DR_ADDR(ALT_GPIO0_ADDR)
/* The address of the ALT_GPIO_SWPORTA_DDR register for the ALT_GPIO0 instance. */
#define ALT_GPIO0_SWPORTA_DDR_ADDR  ALT_GPIO_SWPORTA_DDR_ADDR(ALT_GPIO0_ADDR)
/* The address of the ALT_GPIO_INTEN register for the ALT_GPIO0 instance. */
#define ALT_GPIO0_INTEN_ADDR  ALT_GPIO_INTEN_ADDR(ALT_GPIO0_ADDR)
/* The address of the ALT_GPIO_INTMSK register for the ALT_GPIO0 instance. */
#define ALT_GPIO0_INTMSK_ADDR  ALT_GPIO_INTMSK_ADDR(ALT_GPIO0_ADDR)
/* The address of the ALT_GPIO_INTTYPE_LEVEL register for the ALT_GPIO0 instance. */
#define ALT_GPIO0_INTTYPE_LEVEL_ADDR  ALT_GPIO_INTTYPE_LEVEL_ADDR(ALT_GPIO0_ADDR)
/* The address of the ALT_GPIO_INT_POL register for the ALT_GPIO0 instance. */
#define ALT_GPIO0_INT_POL_ADDR  ALT_GPIO_INT_POL_ADDR(ALT_GPIO0_ADDR)
/* The address of the ALT_GPIO_INTSTAT register for the ALT_GPIO0 instance. */
#define ALT_GPIO0_INTSTAT_ADDR  ALT_GPIO_INTSTAT_ADDR(ALT_GPIO0_ADDR)
/* The address of the ALT_GPIO_RAW_INTSTAT register for the ALT_GPIO0 instance. */
#define ALT_GPIO0_RAW_INTSTAT_ADDR  ALT_GPIO_RAW_INTSTAT_ADDR(ALT_GPIO0_ADDR)
/* The address of the ALT_GPIO_DEBOUNCE register for the ALT_GPIO0 instance. */
#define ALT_GPIO0_DEBOUNCE_ADDR  ALT_GPIO_DEBOUNCE_ADDR(ALT_GPIO0_ADDR)
/* The address of the ALT_GPIO_PORTA_EOI register for the ALT_GPIO0 instance. */
#define ALT_GPIO0_PORTA_EOI_ADDR  ALT_GPIO_PORTA_EOI_ADDR(ALT_GPIO0_ADDR)
/* The address of the ALT_GPIO_EXT_PORTA register for the ALT_GPIO0 instance. */
#define ALT_GPIO0_EXT_PORTA_ADDR  ALT_GPIO_EXT_PORTA_ADDR(ALT_GPIO0_ADDR)
/* The address of the ALT_GPIO_LS_SYNC register for the ALT_GPIO0 instance. */
#define ALT_GPIO0_LS_SYNC_ADDR  ALT_GPIO_LS_SYNC_ADDR(ALT_GPIO0_ADDR)
/* The address of the ALT_GPIO_ID_CODE register for the ALT_GPIO0 instance. */
#define ALT_GPIO0_ID_CODE_ADDR  ALT_GPIO_ID_CODE_ADDR(ALT_GPIO0_ADDR)
/* The address of the ALT_GPIO_VER_ID_CODE register for the ALT_GPIO0 instance. */
#define ALT_GPIO0_VER_ID_CODE_ADDR  ALT_GPIO_VER_ID_CODE_ADDR(ALT_GPIO0_ADDR)
/* The address of the ALT_GPIO_CFG_REG2 register for the ALT_GPIO0 instance. */
#define ALT_GPIO0_CFG_REG2_ADDR  ALT_GPIO_CFG_REG2_ADDR(ALT_GPIO0_ADDR)
/* The address of the ALT_GPIO_CFG_REG1 register for the ALT_GPIO0 instance. */
#define ALT_GPIO0_CFG_REG1_ADDR  ALT_GPIO_CFG_REG1_ADDR(ALT_GPIO0_ADDR)
/* The base address byte offset for the start of the ALT_GPIO0 component. */
#define ALT_GPIO0_OFST        0xff708000
/* The start address of the ALT_GPIO0 component. */
#define ALT_GPIO0_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_HPS_ADDR) + ALT_GPIO0_OFST))
/* The lower bound address range of the ALT_GPIO0 component. */
#define ALT_GPIO0_LB_ADDR     ALT_GPIO0_ADDR
/* The upper bound address range of the ALT_GPIO0 component. */
#define ALT_GPIO0_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_GPIO0_ADDR) + 0x80) - 1))


/*
 * Component Instance : gpio1
 * 
 * Instance gpio1 of component ALT_GPIO.
 * 
 * 
 */
/* The address of the ALT_GPIO_SWPORTA_DR register for the ALT_GPIO1 instance. */
#define ALT_GPIO1_SWPORTA_DR_ADDR  ALT_GPIO_SWPORTA_DR_ADDR(ALT_GPIO1_ADDR)
/* The address of the ALT_GPIO_SWPORTA_DDR register for the ALT_GPIO1 instance. */
#define ALT_GPIO1_SWPORTA_DDR_ADDR  ALT_GPIO_SWPORTA_DDR_ADDR(ALT_GPIO1_ADDR)
/* The address of the ALT_GPIO_INTEN register for the ALT_GPIO1 instance. */
#define ALT_GPIO1_INTEN_ADDR  ALT_GPIO_INTEN_ADDR(ALT_GPIO1_ADDR)
/* The address of the ALT_GPIO_INTMSK register for the ALT_GPIO1 instance. */
#define ALT_GPIO1_INTMSK_ADDR  ALT_GPIO_INTMSK_ADDR(ALT_GPIO1_ADDR)
/* The address of the ALT_GPIO_INTTYPE_LEVEL register for the ALT_GPIO1 instance. */
#define ALT_GPIO1_INTTYPE_LEVEL_ADDR  ALT_GPIO_INTTYPE_LEVEL_ADDR(ALT_GPIO1_ADDR)
/* The address of the ALT_GPIO_INT_POL register for the ALT_GPIO1 instance. */
#define ALT_GPIO1_INT_POL_ADDR  ALT_GPIO_INT_POL_ADDR(ALT_GPIO1_ADDR)
/* The address of the ALT_GPIO_INTSTAT register for the ALT_GPIO1 instance. */
#define ALT_GPIO1_INTSTAT_ADDR  ALT_GPIO_INTSTAT_ADDR(ALT_GPIO1_ADDR)
/* The address of the ALT_GPIO_RAW_INTSTAT register for the ALT_GPIO1 instance. */
#define ALT_GPIO1_RAW_INTSTAT_ADDR  ALT_GPIO_RAW_INTSTAT_ADDR(ALT_GPIO1_ADDR)
/* The address of the ALT_GPIO_DEBOUNCE register for the ALT_GPIO1 instance. */
#define ALT_GPIO1_DEBOUNCE_ADDR  ALT_GPIO_DEBOUNCE_ADDR(ALT_GPIO1_ADDR)
/* The address of the ALT_GPIO_PORTA_EOI register for the ALT_GPIO1 instance. */
#define ALT_GPIO1_PORTA_EOI_ADDR  ALT_GPIO_PORTA_EOI_ADDR(ALT_GPIO1_ADDR)
/* The address of the ALT_GPIO_EXT_PORTA register for the ALT_GPIO1 instance. */
#define ALT_GPIO1_EXT_PORTA_ADDR  ALT_GPIO_EXT_PORTA_ADDR(ALT_GPIO1_ADDR)
/* The address of the ALT_GPIO_LS_SYNC register for the ALT_GPIO1 instance. */
#define ALT_GPIO1_LS_SYNC_ADDR  ALT_GPIO_LS_SYNC_ADDR(ALT_GPIO1_ADDR)
/* The address of the ALT_GPIO_ID_CODE register for the ALT_GPIO1 instance. */
#define ALT_GPIO1_ID_CODE_ADDR  ALT_GPIO_ID_CODE_ADDR(ALT_GPIO1_ADDR)
/* The address of the ALT_GPIO_VER_ID_CODE register for the ALT_GPIO1 instance. */
#define ALT_GPIO1_VER_ID_CODE_ADDR  ALT_GPIO_VER_ID_CODE_ADDR(ALT_GPIO1_ADDR)
/* The address of the ALT_GPIO_CFG_REG2 register for the ALT_GPIO1 instance. */
#define ALT_GPIO1_CFG_REG2_ADDR  ALT_GPIO_CFG_REG2_ADDR(ALT_GPIO1_ADDR)
/* The address of the ALT_GPIO_CFG_REG1 register for the ALT_GPIO1 instance. */
#define ALT_GPIO1_CFG_REG1_ADDR  ALT_GPIO_CFG_REG1_ADDR(ALT_GPIO1_ADDR)
/* The base address byte offset for the start of the ALT_GPIO1 component. */
#define ALT_GPIO1_OFST        0xff709000
/* The start address of the ALT_GPIO1 component. */
#define ALT_GPIO1_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_HPS_ADDR) + ALT_GPIO1_OFST))
/* The lower bound address range of the ALT_GPIO1 component. */
#define ALT_GPIO1_LB_ADDR     ALT_GPIO1_ADDR
/* The upper bound address range of the ALT_GPIO1 component. */
#define ALT_GPIO1_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_GPIO1_ADDR) + 0x80) - 1))


/*
 * Component Instance : gpio2
 * 
 * Instance gpio2 of component ALT_GPIO.
 * 
 * 
 */
/* The address of the ALT_GPIO_SWPORTA_DR register for the ALT_GPIO2 instance. */
#define ALT_GPIO2_SWPORTA_DR_ADDR  ALT_GPIO_SWPORTA_DR_ADDR(ALT_GPIO2_ADDR)
/* The address of the ALT_GPIO_SWPORTA_DDR register for the ALT_GPIO2 instance. */
#define ALT_GPIO2_SWPORTA_DDR_ADDR  ALT_GPIO_SWPORTA_DDR_ADDR(ALT_GPIO2_ADDR)
/* The address of the ALT_GPIO_INTEN register for the ALT_GPIO2 instance. */
#define ALT_GPIO2_INTEN_ADDR  ALT_GPIO_INTEN_ADDR(ALT_GPIO2_ADDR)
/* The address of the ALT_GPIO_INTMSK register for the ALT_GPIO2 instance. */
#define ALT_GPIO2_INTMSK_ADDR  ALT_GPIO_INTMSK_ADDR(ALT_GPIO2_ADDR)
/* The address of the ALT_GPIO_INTTYPE_LEVEL register for the ALT_GPIO2 instance. */
#define ALT_GPIO2_INTTYPE_LEVEL_ADDR  ALT_GPIO_INTTYPE_LEVEL_ADDR(ALT_GPIO2_ADDR)
/* The address of the ALT_GPIO_INT_POL register for the ALT_GPIO2 instance. */
#define ALT_GPIO2_INT_POL_ADDR  ALT_GPIO_INT_POL_ADDR(ALT_GPIO2_ADDR)
/* The address of the ALT_GPIO_INTSTAT register for the ALT_GPIO2 instance. */
#define ALT_GPIO2_INTSTAT_ADDR  ALT_GPIO_INTSTAT_ADDR(ALT_GPIO2_ADDR)
/* The address of the ALT_GPIO_RAW_INTSTAT register for the ALT_GPIO2 instance. */
#define ALT_GPIO2_RAW_INTSTAT_ADDR  ALT_GPIO_RAW_INTSTAT_ADDR(ALT_GPIO2_ADDR)
/* The address of the ALT_GPIO_DEBOUNCE register for the ALT_GPIO2 instance. */
#define ALT_GPIO2_DEBOUNCE_ADDR  ALT_GPIO_DEBOUNCE_ADDR(ALT_GPIO2_ADDR)
/* The address of the ALT_GPIO_PORTA_EOI register for the ALT_GPIO2 instance. */
#define ALT_GPIO2_PORTA_EOI_ADDR  ALT_GPIO_PORTA_EOI_ADDR(ALT_GPIO2_ADDR)
/* The address of the ALT_GPIO_EXT_PORTA register for the ALT_GPIO2 instance. */
#define ALT_GPIO2_EXT_PORTA_ADDR  ALT_GPIO_EXT_PORTA_ADDR(ALT_GPIO2_ADDR)
/* The address of the ALT_GPIO_LS_SYNC register for the ALT_GPIO2 instance. */
#define ALT_GPIO2_LS_SYNC_ADDR  ALT_GPIO_LS_SYNC_ADDR(ALT_GPIO2_ADDR)
/* The address of the ALT_GPIO_ID_CODE register for the ALT_GPIO2 instance. */
#define ALT_GPIO2_ID_CODE_ADDR  ALT_GPIO_ID_CODE_ADDR(ALT_GPIO2_ADDR)
/* The address of the ALT_GPIO_VER_ID_CODE register for the ALT_GPIO2 instance. */
#define ALT_GPIO2_VER_ID_CODE_ADDR  ALT_GPIO_VER_ID_CODE_ADDR(ALT_GPIO2_ADDR)
/* The address of the ALT_GPIO_CFG_REG2 register for the ALT_GPIO2 instance. */
#define ALT_GPIO2_CFG_REG2_ADDR  ALT_GPIO_CFG_REG2_ADDR(ALT_GPIO2_ADDR)
/* The address of the ALT_GPIO_CFG_REG1 register for the ALT_GPIO2 instance. */
#define ALT_GPIO2_CFG_REG1_ADDR  ALT_GPIO_CFG_REG1_ADDR(ALT_GPIO2_ADDR)
/* The base address byte offset for the start of the ALT_GPIO2 component. */
#define ALT_GPIO2_OFST        0xff70a000
/* The start address of the ALT_GPIO2 component. */
#define ALT_GPIO2_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_HPS_ADDR) + ALT_GPIO2_OFST))
/* The lower bound address range of the ALT_GPIO2 component. */
#define ALT_GPIO2_LB_ADDR     ALT_GPIO2_ADDR
/* The upper bound address range of the ALT_GPIO2 component. */
#define ALT_GPIO2_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_GPIO2_ADDR) + 0x80) - 1))


/*
 * Component Instance : l3regs
 * 
 * Instance l3regs of component ALT_L3.
 * 
 * 
 */
/* The address of the ALT_L3_REMAP register for the ALT_L3 instance. */
#define ALT_L3_REMAP_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_L3_ADDR) + ALT_L3_REMAP_OFST))
/*
 * Register Group Instance : secgrp
 * 
 * Instance secgrp of register group ALT_L3_SECGRP.
 * 
 * 
 */
/* The address of the ALT_L3_SEC_L4MAIN register for the ALT_L3_SECGRP instance. */
#define ALT_L3_SEC_L4MAIN_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_L3_SECGRP_ADDR) + ALT_L3_SEC_L4MAIN_OFST))
/* The address of the ALT_L3_SEC_L4SP register for the ALT_L3_SECGRP instance. */
#define ALT_L3_SEC_L4SP_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_L3_SECGRP_ADDR) + ALT_L3_SEC_L4SP_OFST))
/* The address of the ALT_L3_SEC_L4MP register for the ALT_L3_SECGRP instance. */
#define ALT_L3_SEC_L4MP_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_L3_SECGRP_ADDR) + ALT_L3_SEC_L4MP_OFST))
/* The address of the ALT_L3_SEC_L4OSC1 register for the ALT_L3_SECGRP instance. */
#define ALT_L3_SEC_L4OSC1_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_L3_SECGRP_ADDR) + ALT_L3_SEC_L4OSC1_OFST))
/* The address of the ALT_L3_SEC_L4SPIM register for the ALT_L3_SECGRP instance. */
#define ALT_L3_SEC_L4SPIM_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_L3_SECGRP_ADDR) + ALT_L3_SEC_L4SPIM_OFST))
/* The address of the ALT_L3_SEC_STM register for the ALT_L3_SECGRP instance. */
#define ALT_L3_SEC_STM_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_L3_SECGRP_ADDR) + ALT_L3_SEC_STM_OFST))
/* The address of the ALT_L3_SEC_LWH2F register for the ALT_L3_SECGRP instance. */
#define ALT_L3_SEC_LWH2F_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_L3_SECGRP_ADDR) + ALT_L3_SEC_LWH2F_OFST))
/* The address of the ALT_L3_SEC_USB1 register for the ALT_L3_SECGRP instance. */
#define ALT_L3_SEC_USB1_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_L3_SECGRP_ADDR) + ALT_L3_SEC_USB1_OFST))
/* The address of the ALT_L3_SEC_NANDDATA register for the ALT_L3_SECGRP instance. */
#define ALT_L3_SEC_NANDDATA_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_L3_SECGRP_ADDR) + ALT_L3_SEC_NANDDATA_OFST))
/* The address of the ALT_L3_SEC_USB0 register for the ALT_L3_SECGRP instance. */
#define ALT_L3_SEC_USB0_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_L3_SECGRP_ADDR) + ALT_L3_SEC_USB0_OFST))
/* The address of the ALT_L3_SEC_NAND register for the ALT_L3_SECGRP instance. */
#define ALT_L3_SEC_NAND_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_L3_SECGRP_ADDR) + ALT_L3_SEC_NAND_OFST))
/* The address of the ALT_L3_SEC_QSPIDATA register for the ALT_L3_SECGRP instance. */
#define ALT_L3_SEC_QSPIDATA_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_L3_SECGRP_ADDR) + ALT_L3_SEC_QSPIDATA_OFST))
/* The address of the ALT_L3_SEC_FPGAMGRDATA register for the ALT_L3_SECGRP instance. */
#define ALT_L3_SEC_FPGAMGRDATA_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_L3_SECGRP_ADDR) + ALT_L3_SEC_FPGAMGRDATA_OFST))
/* The address of the ALT_L3_SEC_H2F register for the ALT_L3_SECGRP instance. */
#define ALT_L3_SEC_H2F_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_L3_SECGRP_ADDR) + ALT_L3_SEC_H2F_OFST))
/* The address of the ALT_L3_SEC_ACP register for the ALT_L3_SECGRP instance. */
#define ALT_L3_SEC_ACP_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_L3_SECGRP_ADDR) + ALT_L3_SEC_ACP_OFST))
/* The address of the ALT_L3_SEC_ROM register for the ALT_L3_SECGRP instance. */
#define ALT_L3_SEC_ROM_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_L3_SECGRP_ADDR) + ALT_L3_SEC_ROM_OFST))
/* The address of the ALT_L3_SEC_OCRAM register for the ALT_L3_SECGRP instance. */
#define ALT_L3_SEC_OCRAM_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_L3_SECGRP_ADDR) + ALT_L3_SEC_OCRAM_OFST))
/* The address of the ALT_L3_SEC_SDRDATA register for the ALT_L3_SECGRP instance. */
#define ALT_L3_SEC_SDRDATA_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_L3_SECGRP_ADDR) + ALT_L3_SEC_SDRDATA_OFST))
/* The base address byte offset for the start of the ALT_L3_SECGRP component. */
#define ALT_L3_SECGRP_OFST        0x8
/* The start address of the ALT_L3_SECGRP component. */
#define ALT_L3_SECGRP_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_L3_ADDR) + ALT_L3_SECGRP_OFST))
/* The lower bound address range of the ALT_L3_SECGRP component. */
#define ALT_L3_SECGRP_LB_ADDR     ALT_L3_SECGRP_ADDR
/* The upper bound address range of the ALT_L3_SECGRP component. */
#define ALT_L3_SECGRP_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_L3_SECGRP_ADDR) + 0x9c) - 1))


/*
 * Register Group Instance : idgrp
 * 
 * Instance idgrp of register group ALT_L3_IDGRP.
 * 
 * 
 */
/* The address of the ALT_L3_ID_PERIPH_ID_4 register for the ALT_L3_IDGRP instance. */
#define ALT_L3_ID_PERIPH_ID_4_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_L3_IDGRP_ADDR) + ALT_L3_ID_PERIPH_ID_4_OFST))
/* The address of the ALT_L3_ID_PERIPH_ID_0 register for the ALT_L3_IDGRP instance. */
#define ALT_L3_ID_PERIPH_ID_0_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_L3_IDGRP_ADDR) + ALT_L3_ID_PERIPH_ID_0_OFST))
/* The address of the ALT_L3_ID_PERIPH_ID_1 register for the ALT_L3_IDGRP instance. */
#define ALT_L3_ID_PERIPH_ID_1_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_L3_IDGRP_ADDR) + ALT_L3_ID_PERIPH_ID_1_OFST))
/* The address of the ALT_L3_ID_PERIPH_ID_2 register for the ALT_L3_IDGRP instance. */
#define ALT_L3_ID_PERIPH_ID_2_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_L3_IDGRP_ADDR) + ALT_L3_ID_PERIPH_ID_2_OFST))
/* The address of the ALT_L3_ID_PERIPH_ID_3 register for the ALT_L3_IDGRP instance. */
#define ALT_L3_ID_PERIPH_ID_3_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_L3_IDGRP_ADDR) + ALT_L3_ID_PERIPH_ID_3_OFST))
/* The address of the ALT_L3_ID_COMP_ID_0 register for the ALT_L3_IDGRP instance. */
#define ALT_L3_ID_COMP_ID_0_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_L3_IDGRP_ADDR) + ALT_L3_ID_COMP_ID_0_OFST))
/* The address of the ALT_L3_ID_COMP_ID_1 register for the ALT_L3_IDGRP instance. */
#define ALT_L3_ID_COMP_ID_1_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_L3_IDGRP_ADDR) + ALT_L3_ID_COMP_ID_1_OFST))
/* The address of the ALT_L3_ID_COMP_ID_2 register for the ALT_L3_IDGRP instance. */
#define ALT_L3_ID_COMP_ID_2_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_L3_IDGRP_ADDR) + ALT_L3_ID_COMP_ID_2_OFST))
/* The address of the ALT_L3_ID_COMP_ID_3 register for the ALT_L3_IDGRP instance. */
#define ALT_L3_ID_COMP_ID_3_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_L3_IDGRP_ADDR) + ALT_L3_ID_COMP_ID_3_OFST))
/* The base address byte offset for the start of the ALT_L3_IDGRP component. */
#define ALT_L3_IDGRP_OFST        0x1000
/* The start address of the ALT_L3_IDGRP component. */
#define ALT_L3_IDGRP_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_L3_ADDR) + ALT_L3_IDGRP_OFST))
/* The lower bound address range of the ALT_L3_IDGRP component. */
#define ALT_L3_IDGRP_LB_ADDR     ALT_L3_IDGRP_ADDR
/* The upper bound address range of the ALT_L3_IDGRP component. */
#define ALT_L3_IDGRP_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_L3_IDGRP_ADDR) + 0x1000) - 1))


/*
 * Register Group Instance : mastergrp
 * 
 * Instance mastergrp of register group ALT_L3_MSTGRP.
 * 
 * 
 */
/*
 * Register Group Instance : mastergrp_l4main
 * 
 * Instance mastergrp_l4main of register group ALT_L3_MST_L4MAIN.
 * 
 * 
 */
/* The address of the ALT_L3_FN_MOD_BM_ISS register for the ALT_L3_MST_MST_L4MAIN instance. */
#define ALT_L3_MST_MST_L4MAIN_FN_MOD_BM_ISS_ADDR  ALT_L3_FN_MOD_BM_ISS_ADDR(ALT_L3_MST_MST_L4MAIN_ADDR)
/* The base address byte offset for the start of the ALT_L3_MST_MST_L4MAIN component. */
#define ALT_L3_MST_MST_L4MAIN_OFST        0x0
/* The start address of the ALT_L3_MST_MST_L4MAIN component. */
#define ALT_L3_MST_MST_L4MAIN_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_L3_MSTGRP_ADDR) + ALT_L3_MST_MST_L4MAIN_OFST))
/* The lower bound address range of the ALT_L3_MST_MST_L4MAIN component. */
#define ALT_L3_MST_MST_L4MAIN_LB_ADDR     ALT_L3_MST_MST_L4MAIN_ADDR
/* The upper bound address range of the ALT_L3_MST_MST_L4MAIN component. */
#define ALT_L3_MST_MST_L4MAIN_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_L3_MST_MST_L4MAIN_ADDR) + 0xc) - 1))


/*
 * Register Group Instance : mastergrp_l4sp
 * 
 * Instance mastergrp_l4sp of register group ALT_L3_MST_L4SP.
 * 
 * 
 */
/* The address of the ALT_L3_FN_MOD_BM_ISS register for the ALT_L3_MST_MST_L4SP instance. */
#define ALT_L3_MST_MST_L4SP_FN_MOD_BM_ISS_ADDR  ALT_L3_FN_MOD_BM_ISS_ADDR(ALT_L3_MST_MST_L4SP_ADDR)
/* The base address byte offset for the start of the ALT_L3_MST_MST_L4SP component. */
#define ALT_L3_MST_MST_L4SP_OFST        0x1000
/* The start address of the ALT_L3_MST_MST_L4SP component. */
#define ALT_L3_MST_MST_L4SP_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_L3_MSTGRP_ADDR) + ALT_L3_MST_MST_L4SP_OFST))
/* The lower bound address range of the ALT_L3_MST_MST_L4SP component. */
#define ALT_L3_MST_MST_L4SP_LB_ADDR     ALT_L3_MST_MST_L4SP_ADDR
/* The upper bound address range of the ALT_L3_MST_MST_L4SP component. */
#define ALT_L3_MST_MST_L4SP_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_L3_MST_MST_L4SP_ADDR) + 0xc) - 1))


/*
 * Register Group Instance : mastergrp_l4mp
 * 
 * Instance mastergrp_l4mp of register group ALT_L3_MST_L4MP.
 * 
 * 
 */
/* The address of the ALT_L3_FN_MOD_BM_ISS register for the ALT_L3_MST_MST_L4MP instance. */
#define ALT_L3_MST_MST_L4MP_FN_MOD_BM_ISS_ADDR  ALT_L3_FN_MOD_BM_ISS_ADDR(ALT_L3_MST_MST_L4MP_ADDR)
/* The base address byte offset for the start of the ALT_L3_MST_MST_L4MP component. */
#define ALT_L3_MST_MST_L4MP_OFST        0x2000
/* The start address of the ALT_L3_MST_MST_L4MP component. */
#define ALT_L3_MST_MST_L4MP_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_L3_MSTGRP_ADDR) + ALT_L3_MST_MST_L4MP_OFST))
/* The lower bound address range of the ALT_L3_MST_MST_L4MP component. */
#define ALT_L3_MST_MST_L4MP_LB_ADDR     ALT_L3_MST_MST_L4MP_ADDR
/* The upper bound address range of the ALT_L3_MST_MST_L4MP component. */
#define ALT_L3_MST_MST_L4MP_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_L3_MST_MST_L4MP_ADDR) + 0xc) - 1))


/*
 * Register Group Instance : mastergrp_l4osc1
 * 
 * Instance mastergrp_l4osc1 of register group ALT_L3_MST_L4OSC1.
 * 
 * 
 */
/* The address of the ALT_L3_FN_MOD_BM_ISS register for the ALT_L3_MST_MST_L4OSC1 instance. */
#define ALT_L3_MST_MST_L4OSC1_FN_MOD_BM_ISS_ADDR  ALT_L3_FN_MOD_BM_ISS_ADDR(ALT_L3_MST_MST_L4OSC1_ADDR)
/* The base address byte offset for the start of the ALT_L3_MST_MST_L4OSC1 component. */
#define ALT_L3_MST_MST_L4OSC1_OFST        0x3000
/* The start address of the ALT_L3_MST_MST_L4OSC1 component. */
#define ALT_L3_MST_MST_L4OSC1_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_L3_MSTGRP_ADDR) + ALT_L3_MST_MST_L4OSC1_OFST))
/* The lower bound address range of the ALT_L3_MST_MST_L4OSC1 component. */
#define ALT_L3_MST_MST_L4OSC1_LB_ADDR     ALT_L3_MST_MST_L4OSC1_ADDR
/* The upper bound address range of the ALT_L3_MST_MST_L4OSC1 component. */
#define ALT_L3_MST_MST_L4OSC1_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_L3_MST_MST_L4OSC1_ADDR) + 0xc) - 1))


/*
 * Register Group Instance : mastergrp_l4spim
 * 
 * Instance mastergrp_l4spim of register group ALT_L3_MST_L4SPIM.
 * 
 * 
 */
/* The address of the ALT_L3_FN_MOD_BM_ISS register for the ALT_L3_MST_MST_L4SPIM instance. */
#define ALT_L3_MST_MST_L4SPIM_FN_MOD_BM_ISS_ADDR  ALT_L3_FN_MOD_BM_ISS_ADDR(ALT_L3_MST_MST_L4SPIM_ADDR)
/* The base address byte offset for the start of the ALT_L3_MST_MST_L4SPIM component. */
#define ALT_L3_MST_MST_L4SPIM_OFST        0x4000
/* The start address of the ALT_L3_MST_MST_L4SPIM component. */
#define ALT_L3_MST_MST_L4SPIM_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_L3_MSTGRP_ADDR) + ALT_L3_MST_MST_L4SPIM_OFST))
/* The lower bound address range of the ALT_L3_MST_MST_L4SPIM component. */
#define ALT_L3_MST_MST_L4SPIM_LB_ADDR     ALT_L3_MST_MST_L4SPIM_ADDR
/* The upper bound address range of the ALT_L3_MST_MST_L4SPIM component. */
#define ALT_L3_MST_MST_L4SPIM_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_L3_MST_MST_L4SPIM_ADDR) + 0xc) - 1))


/*
 * Register Group Instance : mastergrp_stm
 * 
 * Instance mastergrp_stm of register group ALT_L3_MST_STM.
 * 
 * 
 */
/* The address of the ALT_L3_FN_MOD_BM_ISS register for the ALT_L3_MST_MST_STM instance. */
#define ALT_L3_MST_MST_STM_FN_MOD_BM_ISS_ADDR  ALT_L3_FN_MOD_BM_ISS_ADDR(ALT_L3_MST_MST_STM_ADDR)
/* The address of the ALT_L3_FN_MOD register for the ALT_L3_MST_MST_STM instance. */
#define ALT_L3_MST_MST_STM_FN_MOD_ADDR  ALT_L3_FN_MOD_ADDR(ALT_L3_MST_MST_STM_ADDR)
/* The base address byte offset for the start of the ALT_L3_MST_MST_STM component. */
#define ALT_L3_MST_MST_STM_OFST        0x5000
/* The start address of the ALT_L3_MST_MST_STM component. */
#define ALT_L3_MST_MST_STM_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_L3_MSTGRP_ADDR) + ALT_L3_MST_MST_STM_OFST))
/* The lower bound address range of the ALT_L3_MST_MST_STM component. */
#define ALT_L3_MST_MST_STM_LB_ADDR     ALT_L3_MST_MST_STM_ADDR
/* The upper bound address range of the ALT_L3_MST_MST_STM component. */
#define ALT_L3_MST_MST_STM_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_L3_MST_MST_STM_ADDR) + 0x10c) - 1))


/*
 * Register Group Instance : mastergrp_lwhps2fpga
 * 
 * Instance mastergrp_lwhps2fpga of register group ALT_L3_MST_LWH2F.
 * 
 * 
 */
/* The address of the ALT_L3_FN_MOD_BM_ISS register for the ALT_L3_MST_MST_LWH2F instance. */
#define ALT_L3_MST_MST_LWH2F_FN_MOD_BM_ISS_ADDR  ALT_L3_FN_MOD_BM_ISS_ADDR(ALT_L3_MST_MST_LWH2F_ADDR)
/* The address of the ALT_L3_FN_MOD register for the ALT_L3_MST_MST_LWH2F instance. */
#define ALT_L3_MST_MST_LWH2F_FN_MOD_ADDR  ALT_L3_FN_MOD_ADDR(ALT_L3_MST_MST_LWH2F_ADDR)
/* The base address byte offset for the start of the ALT_L3_MST_MST_LWH2F component. */
#define ALT_L3_MST_MST_LWH2F_OFST        0x6000
/* The start address of the ALT_L3_MST_MST_LWH2F component. */
#define ALT_L3_MST_MST_LWH2F_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_L3_MSTGRP_ADDR) + ALT_L3_MST_MST_LWH2F_OFST))
/* The lower bound address range of the ALT_L3_MST_MST_LWH2F component. */
#define ALT_L3_MST_MST_LWH2F_LB_ADDR     ALT_L3_MST_MST_LWH2F_ADDR
/* The upper bound address range of the ALT_L3_MST_MST_LWH2F component. */
#define ALT_L3_MST_MST_LWH2F_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_L3_MST_MST_LWH2F_ADDR) + 0x10c) - 1))


/*
 * Register Group Instance : mastergrp_usb1
 * 
 * Instance mastergrp_usb1 of register group ALT_L3_MST_USB1.
 * 
 * 
 */
/* The address of the ALT_L3_FN_MOD_BM_ISS register for the ALT_L3_MST_MST_USB1 instance. */
#define ALT_L3_MST_MST_USB1_FN_MOD_BM_ISS_ADDR  ALT_L3_FN_MOD_BM_ISS_ADDR(ALT_L3_MST_MST_USB1_ADDR)
/* The address of the ALT_L3_AHB_CNTL register for the ALT_L3_MST_MST_USB1 instance. */
#define ALT_L3_MST_MST_USB1_AHB_CNTL_ADDR  ALT_L3_AHB_CNTL_ADDR(ALT_L3_MST_MST_USB1_ADDR)
/* The base address byte offset for the start of the ALT_L3_MST_MST_USB1 component. */
#define ALT_L3_MST_MST_USB1_OFST        0x8000
/* The start address of the ALT_L3_MST_MST_USB1 component. */
#define ALT_L3_MST_MST_USB1_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_L3_MSTGRP_ADDR) + ALT_L3_MST_MST_USB1_OFST))
/* The lower bound address range of the ALT_L3_MST_MST_USB1 component. */
#define ALT_L3_MST_MST_USB1_LB_ADDR     ALT_L3_MST_MST_USB1_ADDR
/* The upper bound address range of the ALT_L3_MST_MST_USB1 component. */
#define ALT_L3_MST_MST_USB1_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_L3_MST_MST_USB1_ADDR) + 0x48) - 1))


/*
 * Register Group Instance : mastergrp_nanddata
 * 
 * Instance mastergrp_nanddata of register group ALT_L3_MST_NANDDATA.
 * 
 * 
 */
/* The address of the ALT_L3_FN_MOD_BM_ISS register for the ALT_L3_MST_MST_NANDDATA instance. */
#define ALT_L3_MST_MST_NANDDATA_FN_MOD_BM_ISS_ADDR  ALT_L3_FN_MOD_BM_ISS_ADDR(ALT_L3_MST_MST_NANDDATA_ADDR)
/* The address of the ALT_L3_FN_MOD register for the ALT_L3_MST_MST_NANDDATA instance. */
#define ALT_L3_MST_MST_NANDDATA_FN_MOD_ADDR  ALT_L3_FN_MOD_ADDR(ALT_L3_MST_MST_NANDDATA_ADDR)
/* The base address byte offset for the start of the ALT_L3_MST_MST_NANDDATA component. */
#define ALT_L3_MST_MST_NANDDATA_OFST        0x9000
/* The start address of the ALT_L3_MST_MST_NANDDATA component. */
#define ALT_L3_MST_MST_NANDDATA_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_L3_MSTGRP_ADDR) + ALT_L3_MST_MST_NANDDATA_OFST))
/* The lower bound address range of the ALT_L3_MST_MST_NANDDATA component. */
#define ALT_L3_MST_MST_NANDDATA_LB_ADDR     ALT_L3_MST_MST_NANDDATA_ADDR
/* The upper bound address range of the ALT_L3_MST_MST_NANDDATA component. */
#define ALT_L3_MST_MST_NANDDATA_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_L3_MST_MST_NANDDATA_ADDR) + 0x10c) - 1))


/*
 * Register Group Instance : mastergrp_usb0
 * 
 * Instance mastergrp_usb0 of register group ALT_L3_MST_USB0.
 * 
 * 
 */
/* The address of the ALT_L3_FN_MOD_BM_ISS register for the ALT_L3_MST_MST_USB0 instance. */
#define ALT_L3_MST_MST_USB0_FN_MOD_BM_ISS_ADDR  ALT_L3_FN_MOD_BM_ISS_ADDR(ALT_L3_MST_MST_USB0_ADDR)
/* The address of the ALT_L3_AHB_CNTL register for the ALT_L3_MST_MST_USB0 instance. */
#define ALT_L3_MST_MST_USB0_AHB_CNTL_ADDR  ALT_L3_AHB_CNTL_ADDR(ALT_L3_MST_MST_USB0_ADDR)
/* The base address byte offset for the start of the ALT_L3_MST_MST_USB0 component. */
#define ALT_L3_MST_MST_USB0_OFST        0x1e000
/* The start address of the ALT_L3_MST_MST_USB0 component. */
#define ALT_L3_MST_MST_USB0_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_L3_MSTGRP_ADDR) + ALT_L3_MST_MST_USB0_OFST))
/* The lower bound address range of the ALT_L3_MST_MST_USB0 component. */
#define ALT_L3_MST_MST_USB0_LB_ADDR     ALT_L3_MST_MST_USB0_ADDR
/* The upper bound address range of the ALT_L3_MST_MST_USB0 component. */
#define ALT_L3_MST_MST_USB0_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_L3_MST_MST_USB0_ADDR) + 0x48) - 1))


/*
 * Register Group Instance : mastergrp_nandregs
 * 
 * Instance mastergrp_nandregs of register group ALT_L3_MST_NAND.
 * 
 * 
 */
/* The address of the ALT_L3_FN_MOD_BM_ISS register for the ALT_L3_MST_MST_NAND instance. */
#define ALT_L3_MST_MST_NAND_FN_MOD_BM_ISS_ADDR  ALT_L3_FN_MOD_BM_ISS_ADDR(ALT_L3_MST_MST_NAND_ADDR)
/* The address of the ALT_L3_FN_MOD register for the ALT_L3_MST_MST_NAND instance. */
#define ALT_L3_MST_MST_NAND_FN_MOD_ADDR  ALT_L3_FN_MOD_ADDR(ALT_L3_MST_MST_NAND_ADDR)
/* The base address byte offset for the start of the ALT_L3_MST_MST_NAND component. */
#define ALT_L3_MST_MST_NAND_OFST        0x1f000
/* The start address of the ALT_L3_MST_MST_NAND component. */
#define ALT_L3_MST_MST_NAND_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_L3_MSTGRP_ADDR) + ALT_L3_MST_MST_NAND_OFST))
/* The lower bound address range of the ALT_L3_MST_MST_NAND component. */
#define ALT_L3_MST_MST_NAND_LB_ADDR     ALT_L3_MST_MST_NAND_ADDR
/* The upper bound address range of the ALT_L3_MST_MST_NAND component. */
#define ALT_L3_MST_MST_NAND_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_L3_MST_MST_NAND_ADDR) + 0x10c) - 1))


/*
 * Register Group Instance : mastergrp_qspidata
 * 
 * Instance mastergrp_qspidata of register group ALT_L3_MST_QSPIDATA.
 * 
 * 
 */
/* The address of the ALT_L3_FN_MOD_BM_ISS register for the ALT_L3_MST_MST_QSPIDATA instance. */
#define ALT_L3_MST_MST_QSPIDATA_FN_MOD_BM_ISS_ADDR  ALT_L3_FN_MOD_BM_ISS_ADDR(ALT_L3_MST_MST_QSPIDATA_ADDR)
/* The address of the ALT_L3_AHB_CNTL register for the ALT_L3_MST_MST_QSPIDATA instance. */
#define ALT_L3_MST_MST_QSPIDATA_AHB_CNTL_ADDR  ALT_L3_AHB_CNTL_ADDR(ALT_L3_MST_MST_QSPIDATA_ADDR)
/* The base address byte offset for the start of the ALT_L3_MST_MST_QSPIDATA component. */
#define ALT_L3_MST_MST_QSPIDATA_OFST        0x20000
/* The start address of the ALT_L3_MST_MST_QSPIDATA component. */
#define ALT_L3_MST_MST_QSPIDATA_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_L3_MSTGRP_ADDR) + ALT_L3_MST_MST_QSPIDATA_OFST))
/* The lower bound address range of the ALT_L3_MST_MST_QSPIDATA component. */
#define ALT_L3_MST_MST_QSPIDATA_LB_ADDR     ALT_L3_MST_MST_QSPIDATA_ADDR
/* The upper bound address range of the ALT_L3_MST_MST_QSPIDATA component. */
#define ALT_L3_MST_MST_QSPIDATA_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_L3_MST_MST_QSPIDATA_ADDR) + 0x48) - 1))


/*
 * Register Group Instance : mastergrp_fpgamgrdata
 * 
 * Instance mastergrp_fpgamgrdata of register group ALT_L3_MST_FPGAMGRDATA.
 * 
 * 
 */
/* The address of the ALT_L3_FN_MOD_BM_ISS register for the ALT_L3_MST_MST_FPGAMGRDATA instance. */
#define ALT_L3_MST_MST_FPGAMGRDATA_FN_MOD_BM_ISS_ADDR  ALT_L3_FN_MOD_BM_ISS_ADDR(ALT_L3_MST_MST_FPGAMGRDATA_ADDR)
/* The address of the ALT_L3_WR_TIDEMARK register for the ALT_L3_MST_MST_FPGAMGRDATA instance. */
#define ALT_L3_MST_MST_FPGAMGRDATA_WR_TIDEMARK_ADDR  ALT_L3_WR_TIDEMARK_ADDR(ALT_L3_MST_MST_FPGAMGRDATA_ADDR)
/* The address of the ALT_L3_FN_MOD register for the ALT_L3_MST_MST_FPGAMGRDATA instance. */
#define ALT_L3_MST_MST_FPGAMGRDATA_FN_MOD_ADDR  ALT_L3_FN_MOD_ADDR(ALT_L3_MST_MST_FPGAMGRDATA_ADDR)
/* The base address byte offset for the start of the ALT_L3_MST_MST_FPGAMGRDATA component. */
#define ALT_L3_MST_MST_FPGAMGRDATA_OFST        0x21000
/* The start address of the ALT_L3_MST_MST_FPGAMGRDATA component. */
#define ALT_L3_MST_MST_FPGAMGRDATA_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_L3_MSTGRP_ADDR) + ALT_L3_MST_MST_FPGAMGRDATA_OFST))
/* The lower bound address range of the ALT_L3_MST_MST_FPGAMGRDATA component. */
#define ALT_L3_MST_MST_FPGAMGRDATA_LB_ADDR     ALT_L3_MST_MST_FPGAMGRDATA_ADDR
/* The upper bound address range of the ALT_L3_MST_MST_FPGAMGRDATA component. */
#define ALT_L3_MST_MST_FPGAMGRDATA_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_L3_MST_MST_FPGAMGRDATA_ADDR) + 0x10c) - 1))


/*
 * Register Group Instance : mastergrp_hps2fpga
 * 
 * Instance mastergrp_hps2fpga of register group ALT_L3_MST_H2F.
 * 
 * 
 */
/* The address of the ALT_L3_FN_MOD_BM_ISS register for the ALT_L3_MST_MST_H2F instance. */
#define ALT_L3_MST_MST_H2F_FN_MOD_BM_ISS_ADDR  ALT_L3_FN_MOD_BM_ISS_ADDR(ALT_L3_MST_MST_H2F_ADDR)
/* The address of the ALT_L3_WR_TIDEMARK register for the ALT_L3_MST_MST_H2F instance. */
#define ALT_L3_MST_MST_H2F_WR_TIDEMARK_ADDR  ALT_L3_WR_TIDEMARK_ADDR(ALT_L3_MST_MST_H2F_ADDR)
/* The address of the ALT_L3_FN_MOD register for the ALT_L3_MST_MST_H2F instance. */
#define ALT_L3_MST_MST_H2F_FN_MOD_ADDR  ALT_L3_FN_MOD_ADDR(ALT_L3_MST_MST_H2F_ADDR)
/* The base address byte offset for the start of the ALT_L3_MST_MST_H2F component. */
#define ALT_L3_MST_MST_H2F_OFST        0x22000
/* The start address of the ALT_L3_MST_MST_H2F component. */
#define ALT_L3_MST_MST_H2F_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_L3_MSTGRP_ADDR) + ALT_L3_MST_MST_H2F_OFST))
/* The lower bound address range of the ALT_L3_MST_MST_H2F component. */
#define ALT_L3_MST_MST_H2F_LB_ADDR     ALT_L3_MST_MST_H2F_ADDR
/* The upper bound address range of the ALT_L3_MST_MST_H2F component. */
#define ALT_L3_MST_MST_H2F_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_L3_MST_MST_H2F_ADDR) + 0x10c) - 1))


/*
 * Register Group Instance : mastergrp_acp
 * 
 * Instance mastergrp_acp of register group ALT_L3_MST_ACP.
 * 
 * 
 */
/* The address of the ALT_L3_FN_MOD_BM_ISS register for the ALT_L3_MST_MST_ACP instance. */
#define ALT_L3_MST_MST_ACP_FN_MOD_BM_ISS_ADDR  ALT_L3_FN_MOD_BM_ISS_ADDR(ALT_L3_MST_MST_ACP_ADDR)
/* The address of the ALT_L3_FN_MOD register for the ALT_L3_MST_MST_ACP instance. */
#define ALT_L3_MST_MST_ACP_FN_MOD_ADDR  ALT_L3_FN_MOD_ADDR(ALT_L3_MST_MST_ACP_ADDR)
/* The base address byte offset for the start of the ALT_L3_MST_MST_ACP component. */
#define ALT_L3_MST_MST_ACP_OFST        0x23000
/* The start address of the ALT_L3_MST_MST_ACP component. */
#define ALT_L3_MST_MST_ACP_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_L3_MSTGRP_ADDR) + ALT_L3_MST_MST_ACP_OFST))
/* The lower bound address range of the ALT_L3_MST_MST_ACP component. */
#define ALT_L3_MST_MST_ACP_LB_ADDR     ALT_L3_MST_MST_ACP_ADDR
/* The upper bound address range of the ALT_L3_MST_MST_ACP component. */
#define ALT_L3_MST_MST_ACP_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_L3_MST_MST_ACP_ADDR) + 0x10c) - 1))


/*
 * Register Group Instance : mastergrp_rom
 * 
 * Instance mastergrp_rom of register group ALT_L3_MST_ROM.
 * 
 * 
 */
/* The address of the ALT_L3_FN_MOD_BM_ISS register for the ALT_L3_MST_MST_ROM instance. */
#define ALT_L3_MST_MST_ROM_FN_MOD_BM_ISS_ADDR  ALT_L3_FN_MOD_BM_ISS_ADDR(ALT_L3_MST_MST_ROM_ADDR)
/* The address of the ALT_L3_FN_MOD register for the ALT_L3_MST_MST_ROM instance. */
#define ALT_L3_MST_MST_ROM_FN_MOD_ADDR  ALT_L3_FN_MOD_ADDR(ALT_L3_MST_MST_ROM_ADDR)
/* The base address byte offset for the start of the ALT_L3_MST_MST_ROM component. */
#define ALT_L3_MST_MST_ROM_OFST        0x24000
/* The start address of the ALT_L3_MST_MST_ROM component. */
#define ALT_L3_MST_MST_ROM_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_L3_MSTGRP_ADDR) + ALT_L3_MST_MST_ROM_OFST))
/* The lower bound address range of the ALT_L3_MST_MST_ROM component. */
#define ALT_L3_MST_MST_ROM_LB_ADDR     ALT_L3_MST_MST_ROM_ADDR
/* The upper bound address range of the ALT_L3_MST_MST_ROM component. */
#define ALT_L3_MST_MST_ROM_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_L3_MST_MST_ROM_ADDR) + 0x10c) - 1))


/*
 * Register Group Instance : mastergrp_ocram
 * 
 * Instance mastergrp_ocram of register group ALT_L3_MST_OCRAM.
 * 
 * 
 */
/* The address of the ALT_L3_FN_MOD_BM_ISS register for the ALT_L3_MST_MST_OCRAM instance. */
#define ALT_L3_MST_MST_OCRAM_FN_MOD_BM_ISS_ADDR  ALT_L3_FN_MOD_BM_ISS_ADDR(ALT_L3_MST_MST_OCRAM_ADDR)
/* The address of the ALT_L3_WR_TIDEMARK register for the ALT_L3_MST_MST_OCRAM instance. */
#define ALT_L3_MST_MST_OCRAM_WR_TIDEMARK_ADDR  ALT_L3_WR_TIDEMARK_ADDR(ALT_L3_MST_MST_OCRAM_ADDR)
/* The address of the ALT_L3_FN_MOD register for the ALT_L3_MST_MST_OCRAM instance. */
#define ALT_L3_MST_MST_OCRAM_FN_MOD_ADDR  ALT_L3_FN_MOD_ADDR(ALT_L3_MST_MST_OCRAM_ADDR)
/* The base address byte offset for the start of the ALT_L3_MST_MST_OCRAM component. */
#define ALT_L3_MST_MST_OCRAM_OFST        0x25000
/* The start address of the ALT_L3_MST_MST_OCRAM component. */
#define ALT_L3_MST_MST_OCRAM_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_L3_MSTGRP_ADDR) + ALT_L3_MST_MST_OCRAM_OFST))
/* The lower bound address range of the ALT_L3_MST_MST_OCRAM component. */
#define ALT_L3_MST_MST_OCRAM_LB_ADDR     ALT_L3_MST_MST_OCRAM_ADDR
/* The upper bound address range of the ALT_L3_MST_MST_OCRAM component. */
#define ALT_L3_MST_MST_OCRAM_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_L3_MST_MST_OCRAM_ADDR) + 0x10c) - 1))


/* The base address byte offset for the start of the ALT_L3_MSTGRP component. */
#define ALT_L3_MSTGRP_OFST        0x2000
/* The start address of the ALT_L3_MSTGRP component. */
#define ALT_L3_MSTGRP_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_L3_ADDR) + ALT_L3_MSTGRP_OFST))
/* The lower bound address range of the ALT_L3_MSTGRP component. */
#define ALT_L3_MSTGRP_LB_ADDR     ALT_L3_MSTGRP_ADDR
/* The upper bound address range of the ALT_L3_MSTGRP component. */
#define ALT_L3_MSTGRP_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_L3_MSTGRP_ADDR) + 0x2510c) - 1))


/*
 * Register Group Instance : slavegrp
 * 
 * Instance slavegrp of register group ALT_L3_SLVGRP.
 * 
 * 
 */
/*
 * Register Group Instance : slavegrp_dap
 * 
 * Instance slavegrp_dap of register group ALT_L3_SLV_DAP.
 * 
 * 
 */
/* The address of the ALT_L3_FN_MOD2 register for the ALT_L3_SLV_SLV_DAP instance. */
#define ALT_L3_SLV_SLV_DAP_FN_MOD2_ADDR  ALT_L3_FN_MOD2_ADDR(ALT_L3_SLV_SLV_DAP_ADDR)
/* The address of the ALT_L3_FN_MOD_AHB register for the ALT_L3_SLV_SLV_DAP instance. */
#define ALT_L3_SLV_SLV_DAP_FN_MOD_AHB_ADDR  ALT_L3_FN_MOD_AHB_ADDR(ALT_L3_SLV_SLV_DAP_ADDR)
/* The address of the ALT_L3_RD_QOS register for the ALT_L3_SLV_SLV_DAP instance. */
#define ALT_L3_SLV_SLV_DAP_RD_QOS_ADDR  ALT_L3_RD_QOS_ADDR(ALT_L3_SLV_SLV_DAP_ADDR)
/* The address of the ALT_L3_WR_QOS register for the ALT_L3_SLV_SLV_DAP instance. */
#define ALT_L3_SLV_SLV_DAP_WR_QOS_ADDR  ALT_L3_WR_QOS_ADDR(ALT_L3_SLV_SLV_DAP_ADDR)
/* The address of the ALT_L3_FN_MOD register for the ALT_L3_SLV_SLV_DAP instance. */
#define ALT_L3_SLV_SLV_DAP_FN_MOD_ADDR  ALT_L3_FN_MOD_ADDR(ALT_L3_SLV_SLV_DAP_ADDR)
/* The base address byte offset for the start of the ALT_L3_SLV_SLV_DAP component. */
#define ALT_L3_SLV_SLV_DAP_OFST        0x0
/* The start address of the ALT_L3_SLV_SLV_DAP component. */
#define ALT_L3_SLV_SLV_DAP_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_L3_SLVGRP_ADDR) + ALT_L3_SLV_SLV_DAP_OFST))
/* The lower bound address range of the ALT_L3_SLV_SLV_DAP component. */
#define ALT_L3_SLV_SLV_DAP_LB_ADDR     ALT_L3_SLV_SLV_DAP_ADDR
/* The upper bound address range of the ALT_L3_SLV_SLV_DAP component. */
#define ALT_L3_SLV_SLV_DAP_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_L3_SLV_SLV_DAP_ADDR) + 0x10c) - 1))


/*
 * Register Group Instance : slavegrp_mpu
 * 
 * Instance slavegrp_mpu of register group ALT_L3_SLV_MPU.
 * 
 * 
 */
/* The address of the ALT_L3_RD_QOS register for the ALT_L3_SLV_SLV_MPU instance. */
#define ALT_L3_SLV_SLV_MPU_RD_QOS_ADDR  ALT_L3_RD_QOS_ADDR(ALT_L3_SLV_SLV_MPU_ADDR)
/* The address of the ALT_L3_WR_QOS register for the ALT_L3_SLV_SLV_MPU instance. */
#define ALT_L3_SLV_SLV_MPU_WR_QOS_ADDR  ALT_L3_WR_QOS_ADDR(ALT_L3_SLV_SLV_MPU_ADDR)
/* The address of the ALT_L3_FN_MOD register for the ALT_L3_SLV_SLV_MPU instance. */
#define ALT_L3_SLV_SLV_MPU_FN_MOD_ADDR  ALT_L3_FN_MOD_ADDR(ALT_L3_SLV_SLV_MPU_ADDR)
/* The base address byte offset for the start of the ALT_L3_SLV_SLV_MPU component. */
#define ALT_L3_SLV_SLV_MPU_OFST        0x1000
/* The start address of the ALT_L3_SLV_SLV_MPU component. */
#define ALT_L3_SLV_SLV_MPU_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_L3_SLVGRP_ADDR) + ALT_L3_SLV_SLV_MPU_OFST))
/* The lower bound address range of the ALT_L3_SLV_SLV_MPU component. */
#define ALT_L3_SLV_SLV_MPU_LB_ADDR     ALT_L3_SLV_SLV_MPU_ADDR
/* The upper bound address range of the ALT_L3_SLV_SLV_MPU component. */
#define ALT_L3_SLV_SLV_MPU_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_L3_SLV_SLV_MPU_ADDR) + 0x10c) - 1))


/*
 * Register Group Instance : slavegrp_sdmmc
 * 
 * Instance slavegrp_sdmmc of register group ALT_L3_SLV_SDMMC.
 * 
 * 
 */
/* The address of the ALT_L3_FN_MOD_AHB register for the ALT_L3_SLV_SLV_SDMMC instance. */
#define ALT_L3_SLV_SLV_SDMMC_FN_MOD_AHB_ADDR  ALT_L3_FN_MOD_AHB_ADDR(ALT_L3_SLV_SLV_SDMMC_ADDR)
/* The address of the ALT_L3_RD_QOS register for the ALT_L3_SLV_SLV_SDMMC instance. */
#define ALT_L3_SLV_SLV_SDMMC_RD_QOS_ADDR  ALT_L3_RD_QOS_ADDR(ALT_L3_SLV_SLV_SDMMC_ADDR)
/* The address of the ALT_L3_WR_QOS register for the ALT_L3_SLV_SLV_SDMMC instance. */
#define ALT_L3_SLV_SLV_SDMMC_WR_QOS_ADDR  ALT_L3_WR_QOS_ADDR(ALT_L3_SLV_SLV_SDMMC_ADDR)
/* The address of the ALT_L3_FN_MOD register for the ALT_L3_SLV_SLV_SDMMC instance. */
#define ALT_L3_SLV_SLV_SDMMC_FN_MOD_ADDR  ALT_L3_FN_MOD_ADDR(ALT_L3_SLV_SLV_SDMMC_ADDR)
/* The base address byte offset for the start of the ALT_L3_SLV_SLV_SDMMC component. */
#define ALT_L3_SLV_SLV_SDMMC_OFST        0x2000
/* The start address of the ALT_L3_SLV_SLV_SDMMC component. */
#define ALT_L3_SLV_SLV_SDMMC_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_L3_SLVGRP_ADDR) + ALT_L3_SLV_SLV_SDMMC_OFST))
/* The lower bound address range of the ALT_L3_SLV_SLV_SDMMC component. */
#define ALT_L3_SLV_SLV_SDMMC_LB_ADDR     ALT_L3_SLV_SLV_SDMMC_ADDR
/* The upper bound address range of the ALT_L3_SLV_SLV_SDMMC component. */
#define ALT_L3_SLV_SLV_SDMMC_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_L3_SLV_SLV_SDMMC_ADDR) + 0x10c) - 1))


/*
 * Register Group Instance : slavegrp_dma
 * 
 * Instance slavegrp_dma of register group ALT_L3_SLV_DMA.
 * 
 * 
 */
/* The address of the ALT_L3_RD_QOS register for the ALT_L3_SLV_SLV_DMA instance. */
#define ALT_L3_SLV_SLV_DMA_RD_QOS_ADDR  ALT_L3_RD_QOS_ADDR(ALT_L3_SLV_SLV_DMA_ADDR)
/* The address of the ALT_L3_WR_QOS register for the ALT_L3_SLV_SLV_DMA instance. */
#define ALT_L3_SLV_SLV_DMA_WR_QOS_ADDR  ALT_L3_WR_QOS_ADDR(ALT_L3_SLV_SLV_DMA_ADDR)
/* The address of the ALT_L3_FN_MOD register for the ALT_L3_SLV_SLV_DMA instance. */
#define ALT_L3_SLV_SLV_DMA_FN_MOD_ADDR  ALT_L3_FN_MOD_ADDR(ALT_L3_SLV_SLV_DMA_ADDR)
/* The base address byte offset for the start of the ALT_L3_SLV_SLV_DMA component. */
#define ALT_L3_SLV_SLV_DMA_OFST        0x3000
/* The start address of the ALT_L3_SLV_SLV_DMA component. */
#define ALT_L3_SLV_SLV_DMA_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_L3_SLVGRP_ADDR) + ALT_L3_SLV_SLV_DMA_OFST))
/* The lower bound address range of the ALT_L3_SLV_SLV_DMA component. */
#define ALT_L3_SLV_SLV_DMA_LB_ADDR     ALT_L3_SLV_SLV_DMA_ADDR
/* The upper bound address range of the ALT_L3_SLV_SLV_DMA component. */
#define ALT_L3_SLV_SLV_DMA_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_L3_SLV_SLV_DMA_ADDR) + 0x10c) - 1))


/*
 * Register Group Instance : slavegrp_fpga2hps
 * 
 * Instance slavegrp_fpga2hps of register group ALT_L3_SLV_F2H.
 * 
 * 
 */
/* The address of the ALT_L3_WR_TIDEMARK register for the ALT_L3_SLV_SLV_F2H instance. */
#define ALT_L3_SLV_SLV_FPGA2WR_TIDEMARK_ADDR  ALT_L3_WR_TIDEMARK_ADDR(ALT_L3_SLV_SLV_F2H_ADDR)
/* The address of the ALT_L3_RD_QOS register for the ALT_L3_SLV_SLV_F2H instance. */
#define ALT_L3_SLV_SLV_FPGA2RD_QOS_ADDR  ALT_L3_RD_QOS_ADDR(ALT_L3_SLV_SLV_F2H_ADDR)
/* The address of the ALT_L3_WR_QOS register for the ALT_L3_SLV_SLV_F2H instance. */
#define ALT_L3_SLV_SLV_FPGA2WR_QOS_ADDR  ALT_L3_WR_QOS_ADDR(ALT_L3_SLV_SLV_F2H_ADDR)
/* The address of the ALT_L3_FN_MOD register for the ALT_L3_SLV_SLV_F2H instance. */
#define ALT_L3_SLV_SLV_FPGA2FN_MOD_ADDR  ALT_L3_FN_MOD_ADDR(ALT_L3_SLV_SLV_F2H_ADDR)
/* The base address byte offset for the start of the ALT_L3_SLV_SLV_F2H component. */
#define ALT_L3_SLV_SLV_F2H_OFST        0x4000
/* The start address of the ALT_L3_SLV_SLV_F2H component. */
#define ALT_L3_SLV_SLV_F2H_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_L3_SLVGRP_ADDR) + ALT_L3_SLV_SLV_F2H_OFST))
/* The lower bound address range of the ALT_L3_SLV_SLV_F2H component. */
#define ALT_L3_SLV_SLV_F2H_LB_ADDR     ALT_L3_SLV_SLV_F2H_ADDR
/* The upper bound address range of the ALT_L3_SLV_SLV_F2H component. */
#define ALT_L3_SLV_SLV_F2H_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_L3_SLV_SLV_F2H_ADDR) + 0x10c) - 1))


/*
 * Register Group Instance : slavegrp_etr
 * 
 * Instance slavegrp_etr of register group ALT_L3_SLV_ETR.
 * 
 * 
 */
/* The address of the ALT_L3_RD_QOS register for the ALT_L3_SLV_SLV_ETR instance. */
#define ALT_L3_SLV_SLV_ETR_RD_QOS_ADDR  ALT_L3_RD_QOS_ADDR(ALT_L3_SLV_SLV_ETR_ADDR)
/* The address of the ALT_L3_WR_QOS register for the ALT_L3_SLV_SLV_ETR instance. */
#define ALT_L3_SLV_SLV_ETR_WR_QOS_ADDR  ALT_L3_WR_QOS_ADDR(ALT_L3_SLV_SLV_ETR_ADDR)
/* The address of the ALT_L3_FN_MOD register for the ALT_L3_SLV_SLV_ETR instance. */
#define ALT_L3_SLV_SLV_ETR_FN_MOD_ADDR  ALT_L3_FN_MOD_ADDR(ALT_L3_SLV_SLV_ETR_ADDR)
/* The base address byte offset for the start of the ALT_L3_SLV_SLV_ETR component. */
#define ALT_L3_SLV_SLV_ETR_OFST        0x5000
/* The start address of the ALT_L3_SLV_SLV_ETR component. */
#define ALT_L3_SLV_SLV_ETR_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_L3_SLVGRP_ADDR) + ALT_L3_SLV_SLV_ETR_OFST))
/* The lower bound address range of the ALT_L3_SLV_SLV_ETR component. */
#define ALT_L3_SLV_SLV_ETR_LB_ADDR     ALT_L3_SLV_SLV_ETR_ADDR
/* The upper bound address range of the ALT_L3_SLV_SLV_ETR component. */
#define ALT_L3_SLV_SLV_ETR_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_L3_SLV_SLV_ETR_ADDR) + 0x10c) - 1))


/*
 * Register Group Instance : slavegrp_emac0
 * 
 * Instance slavegrp_emac0 of register group ALT_L3_SLV_EMAC0.
 * 
 * 
 */
/* The address of the ALT_L3_RD_QOS register for the ALT_L3_SLV_SLV_EMAC0 instance. */
#define ALT_L3_SLV_SLV_EMAC0_RD_QOS_ADDR  ALT_L3_RD_QOS_ADDR(ALT_L3_SLV_SLV_EMAC0_ADDR)
/* The address of the ALT_L3_WR_QOS register for the ALT_L3_SLV_SLV_EMAC0 instance. */
#define ALT_L3_SLV_SLV_EMAC0_WR_QOS_ADDR  ALT_L3_WR_QOS_ADDR(ALT_L3_SLV_SLV_EMAC0_ADDR)
/* The address of the ALT_L3_FN_MOD register for the ALT_L3_SLV_SLV_EMAC0 instance. */
#define ALT_L3_SLV_SLV_EMAC0_FN_MOD_ADDR  ALT_L3_FN_MOD_ADDR(ALT_L3_SLV_SLV_EMAC0_ADDR)
/* The base address byte offset for the start of the ALT_L3_SLV_SLV_EMAC0 component. */
#define ALT_L3_SLV_SLV_EMAC0_OFST        0x6000
/* The start address of the ALT_L3_SLV_SLV_EMAC0 component. */
#define ALT_L3_SLV_SLV_EMAC0_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_L3_SLVGRP_ADDR) + ALT_L3_SLV_SLV_EMAC0_OFST))
/* The lower bound address range of the ALT_L3_SLV_SLV_EMAC0 component. */
#define ALT_L3_SLV_SLV_EMAC0_LB_ADDR     ALT_L3_SLV_SLV_EMAC0_ADDR
/* The upper bound address range of the ALT_L3_SLV_SLV_EMAC0 component. */
#define ALT_L3_SLV_SLV_EMAC0_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_L3_SLV_SLV_EMAC0_ADDR) + 0x10c) - 1))


/*
 * Register Group Instance : slavegrp_emac1
 * 
 * Instance slavegrp_emac1 of register group ALT_L3_SLV_EMAC1.
 * 
 * 
 */
/* The address of the ALT_L3_RD_QOS register for the ALT_L3_SLV_SLV_EMAC1 instance. */
#define ALT_L3_SLV_SLV_EMAC1_RD_QOS_ADDR  ALT_L3_RD_QOS_ADDR(ALT_L3_SLV_SLV_EMAC1_ADDR)
/* The address of the ALT_L3_WR_QOS register for the ALT_L3_SLV_SLV_EMAC1 instance. */
#define ALT_L3_SLV_SLV_EMAC1_WR_QOS_ADDR  ALT_L3_WR_QOS_ADDR(ALT_L3_SLV_SLV_EMAC1_ADDR)
/* The address of the ALT_L3_FN_MOD register for the ALT_L3_SLV_SLV_EMAC1 instance. */
#define ALT_L3_SLV_SLV_EMAC1_FN_MOD_ADDR  ALT_L3_FN_MOD_ADDR(ALT_L3_SLV_SLV_EMAC1_ADDR)
/* The base address byte offset for the start of the ALT_L3_SLV_SLV_EMAC1 component. */
#define ALT_L3_SLV_SLV_EMAC1_OFST        0x7000
/* The start address of the ALT_L3_SLV_SLV_EMAC1 component. */
#define ALT_L3_SLV_SLV_EMAC1_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_L3_SLVGRP_ADDR) + ALT_L3_SLV_SLV_EMAC1_OFST))
/* The lower bound address range of the ALT_L3_SLV_SLV_EMAC1 component. */
#define ALT_L3_SLV_SLV_EMAC1_LB_ADDR     ALT_L3_SLV_SLV_EMAC1_ADDR
/* The upper bound address range of the ALT_L3_SLV_SLV_EMAC1 component. */
#define ALT_L3_SLV_SLV_EMAC1_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_L3_SLV_SLV_EMAC1_ADDR) + 0x10c) - 1))


/*
 * Register Group Instance : slavegrp_usb0
 * 
 * Instance slavegrp_usb0 of register group ALT_L3_SLV_USB0.
 * 
 * 
 */
/* The address of the ALT_L3_FN_MOD_AHB register for the ALT_L3_SLV_SLV_USB0 instance. */
#define ALT_L3_SLV_SLV_USB0_FN_MOD_AHB_ADDR  ALT_L3_FN_MOD_AHB_ADDR(ALT_L3_SLV_SLV_USB0_ADDR)
/* The address of the ALT_L3_RD_QOS register for the ALT_L3_SLV_SLV_USB0 instance. */
#define ALT_L3_SLV_SLV_USB0_RD_QOS_ADDR  ALT_L3_RD_QOS_ADDR(ALT_L3_SLV_SLV_USB0_ADDR)
/* The address of the ALT_L3_WR_QOS register for the ALT_L3_SLV_SLV_USB0 instance. */
#define ALT_L3_SLV_SLV_USB0_WR_QOS_ADDR  ALT_L3_WR_QOS_ADDR(ALT_L3_SLV_SLV_USB0_ADDR)
/* The address of the ALT_L3_FN_MOD register for the ALT_L3_SLV_SLV_USB0 instance. */
#define ALT_L3_SLV_SLV_USB0_FN_MOD_ADDR  ALT_L3_FN_MOD_ADDR(ALT_L3_SLV_SLV_USB0_ADDR)
/* The base address byte offset for the start of the ALT_L3_SLV_SLV_USB0 component. */
#define ALT_L3_SLV_SLV_USB0_OFST        0x8000
/* The start address of the ALT_L3_SLV_SLV_USB0 component. */
#define ALT_L3_SLV_SLV_USB0_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_L3_SLVGRP_ADDR) + ALT_L3_SLV_SLV_USB0_OFST))
/* The lower bound address range of the ALT_L3_SLV_SLV_USB0 component. */
#define ALT_L3_SLV_SLV_USB0_LB_ADDR     ALT_L3_SLV_SLV_USB0_ADDR
/* The upper bound address range of the ALT_L3_SLV_SLV_USB0 component. */
#define ALT_L3_SLV_SLV_USB0_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_L3_SLV_SLV_USB0_ADDR) + 0x10c) - 1))


/*
 * Register Group Instance : slavegrp_nand
 * 
 * Instance slavegrp_nand of register group ALT_L3_SLV_NAND.
 * 
 * 
 */
/* The address of the ALT_L3_RD_QOS register for the ALT_L3_SLV_SLV_NAND instance. */
#define ALT_L3_SLV_SLV_NAND_RD_QOS_ADDR  ALT_L3_RD_QOS_ADDR(ALT_L3_SLV_SLV_NAND_ADDR)
/* The address of the ALT_L3_WR_QOS register for the ALT_L3_SLV_SLV_NAND instance. */
#define ALT_L3_SLV_SLV_NAND_WR_QOS_ADDR  ALT_L3_WR_QOS_ADDR(ALT_L3_SLV_SLV_NAND_ADDR)
/* The address of the ALT_L3_FN_MOD register for the ALT_L3_SLV_SLV_NAND instance. */
#define ALT_L3_SLV_SLV_NAND_FN_MOD_ADDR  ALT_L3_FN_MOD_ADDR(ALT_L3_SLV_SLV_NAND_ADDR)
/* The base address byte offset for the start of the ALT_L3_SLV_SLV_NAND component. */
#define ALT_L3_SLV_SLV_NAND_OFST        0x9000
/* The start address of the ALT_L3_SLV_SLV_NAND component. */
#define ALT_L3_SLV_SLV_NAND_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_L3_SLVGRP_ADDR) + ALT_L3_SLV_SLV_NAND_OFST))
/* The lower bound address range of the ALT_L3_SLV_SLV_NAND component. */
#define ALT_L3_SLV_SLV_NAND_LB_ADDR     ALT_L3_SLV_SLV_NAND_ADDR
/* The upper bound address range of the ALT_L3_SLV_SLV_NAND component. */
#define ALT_L3_SLV_SLV_NAND_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_L3_SLV_SLV_NAND_ADDR) + 0x10c) - 1))


/*
 * Register Group Instance : slavegrp_usb1
 * 
 * Instance slavegrp_usb1 of register group ALT_L3_SLV_USB1.
 * 
 * 
 */
/* The address of the ALT_L3_FN_MOD_AHB register for the ALT_L3_SLV_SLV_USB1 instance. */
#define ALT_L3_SLV_SLV_USB1_FN_MOD_AHB_ADDR  ALT_L3_FN_MOD_AHB_ADDR(ALT_L3_SLV_SLV_USB1_ADDR)
/* The address of the ALT_L3_RD_QOS register for the ALT_L3_SLV_SLV_USB1 instance. */
#define ALT_L3_SLV_SLV_USB1_RD_QOS_ADDR  ALT_L3_RD_QOS_ADDR(ALT_L3_SLV_SLV_USB1_ADDR)
/* The address of the ALT_L3_WR_QOS register for the ALT_L3_SLV_SLV_USB1 instance. */
#define ALT_L3_SLV_SLV_USB1_WR_QOS_ADDR  ALT_L3_WR_QOS_ADDR(ALT_L3_SLV_SLV_USB1_ADDR)
/* The address of the ALT_L3_FN_MOD register for the ALT_L3_SLV_SLV_USB1 instance. */
#define ALT_L3_SLV_SLV_USB1_FN_MOD_ADDR  ALT_L3_FN_MOD_ADDR(ALT_L3_SLV_SLV_USB1_ADDR)
/* The base address byte offset for the start of the ALT_L3_SLV_SLV_USB1 component. */
#define ALT_L3_SLV_SLV_USB1_OFST        0xa000
/* The start address of the ALT_L3_SLV_SLV_USB1 component. */
#define ALT_L3_SLV_SLV_USB1_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_L3_SLVGRP_ADDR) + ALT_L3_SLV_SLV_USB1_OFST))
/* The lower bound address range of the ALT_L3_SLV_SLV_USB1 component. */
#define ALT_L3_SLV_SLV_USB1_LB_ADDR     ALT_L3_SLV_SLV_USB1_ADDR
/* The upper bound address range of the ALT_L3_SLV_SLV_USB1 component. */
#define ALT_L3_SLV_SLV_USB1_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_L3_SLV_SLV_USB1_ADDR) + 0x10c) - 1))


/* The base address byte offset for the start of the ALT_L3_SLVGRP component. */
#define ALT_L3_SLVGRP_OFST        0x42000
/* The start address of the ALT_L3_SLVGRP component. */
#define ALT_L3_SLVGRP_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_L3_ADDR) + ALT_L3_SLVGRP_OFST))
/* The lower bound address range of the ALT_L3_SLVGRP component. */
#define ALT_L3_SLVGRP_LB_ADDR     ALT_L3_SLVGRP_ADDR
/* The upper bound address range of the ALT_L3_SLVGRP component. */
#define ALT_L3_SLVGRP_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_L3_SLVGRP_ADDR) + 0xa10c) - 1))


/* The base address byte offset for the start of the ALT_L3 component. */
#define ALT_L3_OFST        0xff800000
/* The start address of the ALT_L3 component. */
#define ALT_L3_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_HPS_ADDR) + ALT_L3_OFST))
/* The lower bound address range of the ALT_L3 component. */
#define ALT_L3_LB_ADDR     ALT_L3_ADDR
/* The upper bound address range of the ALT_L3 component. */
#define ALT_L3_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_L3_ADDR) + 0x80000) - 1))


/*
 * Component Instance : nanddata
 * 
 * Instance nanddata of component ALT_NANDDATA.
 * 
 * 
 */
/* The base address byte offset for the start of the ALT_NANDDATA component. */
#define ALT_NANDDATA_OFST        0xff900000
/* The start address of the ALT_NANDDATA component. */
#define ALT_NANDDATA_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_HPS_ADDR) + ALT_NANDDATA_OFST))
/* The lower bound address range of the ALT_NANDDATA component. */
#define ALT_NANDDATA_LB_ADDR     ALT_NANDDATA_ADDR
/* The upper bound address range of the ALT_NANDDATA component. */
#define ALT_NANDDATA_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_NANDDATA_ADDR) + 0x100000) - 1))


/*
 * Component Instance : qspidata
 * 
 * Instance qspidata of component ALT_QSPIDATA.
 * 
 * 
 */
/* The base address byte offset for the start of the ALT_QSPIDATA component. */
#define ALT_QSPIDATA_OFST        0xffa00000
/* The start address of the ALT_QSPIDATA component. */
#define ALT_QSPIDATA_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_HPS_ADDR) + ALT_QSPIDATA_OFST))
/* The lower bound address range of the ALT_QSPIDATA component. */
#define ALT_QSPIDATA_LB_ADDR     ALT_QSPIDATA_ADDR
/* The upper bound address range of the ALT_QSPIDATA component. */
#define ALT_QSPIDATA_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_QSPIDATA_ADDR) + 0x100000) - 1))


/*
 * Component Instance : usb0
 * 
 * Instance usb0 of component ALT_USB.
 * 
 * 
 */
/*
 * Register Group Instance : globgrp
 * 
 * Instance globgrp of register group ALT_USB_GLOB.
 * 
 * 
 */
/* The address of the ALT_USB_GLOB_GOTGCTL register for the ALT_USB0_GLOBGRP instance. */
#define ALT_USB0_GLOB_GOTGCTL_ADDR  ALT_USB_GLOB_GOTGCTL_ADDR(ALT_USB0_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_GOTGINT register for the ALT_USB0_GLOBGRP instance. */
#define ALT_USB0_GLOB_GOTGINT_ADDR  ALT_USB_GLOB_GOTGINT_ADDR(ALT_USB0_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_GAHBCFG register for the ALT_USB0_GLOBGRP instance. */
#define ALT_USB0_GLOB_GAHBCFG_ADDR  ALT_USB_GLOB_GAHBCFG_ADDR(ALT_USB0_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_GUSBCFG register for the ALT_USB0_GLOBGRP instance. */
#define ALT_USB0_GLOB_GUSBCFG_ADDR  ALT_USB_GLOB_GUSBCFG_ADDR(ALT_USB0_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_GRSTCTL register for the ALT_USB0_GLOBGRP instance. */
#define ALT_USB0_GLOB_GRSTCTL_ADDR  ALT_USB_GLOB_GRSTCTL_ADDR(ALT_USB0_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_GINTSTS register for the ALT_USB0_GLOBGRP instance. */
#define ALT_USB0_GLOB_GINTSTS_ADDR  ALT_USB_GLOB_GINTSTS_ADDR(ALT_USB0_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_GINTMSK register for the ALT_USB0_GLOBGRP instance. */
#define ALT_USB0_GLOB_GINTMSK_ADDR  ALT_USB_GLOB_GINTMSK_ADDR(ALT_USB0_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_GRXSTSR register for the ALT_USB0_GLOBGRP instance. */
#define ALT_USB0_GLOB_GRXSTSR_ADDR  ALT_USB_GLOB_GRXSTSR_ADDR(ALT_USB0_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_GRXSTSP register for the ALT_USB0_GLOBGRP instance. */
#define ALT_USB0_GLOB_GRXSTSP_ADDR  ALT_USB_GLOB_GRXSTSP_ADDR(ALT_USB0_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_GRXFSIZ register for the ALT_USB0_GLOBGRP instance. */
#define ALT_USB0_GLOB_GRXFSIZ_ADDR  ALT_USB_GLOB_GRXFSIZ_ADDR(ALT_USB0_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_GNPTXFSIZ register for the ALT_USB0_GLOBGRP instance. */
#define ALT_USB0_GLOB_GNPTXFSIZ_ADDR  ALT_USB_GLOB_GNPTXFSIZ_ADDR(ALT_USB0_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_GNPTXSTS register for the ALT_USB0_GLOBGRP instance. */
#define ALT_USB0_GLOB_GNPTXSTS_ADDR  ALT_USB_GLOB_GNPTXSTS_ADDR(ALT_USB0_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_GPVNDCTL register for the ALT_USB0_GLOBGRP instance. */
#define ALT_USB0_GLOB_GPVNDCTL_ADDR  ALT_USB_GLOB_GPVNDCTL_ADDR(ALT_USB0_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_GGPIO register for the ALT_USB0_GLOBGRP instance. */
#define ALT_USB0_GLOB_GGPIO_ADDR  ALT_USB_GLOB_GGPIO_ADDR(ALT_USB0_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_GUID register for the ALT_USB0_GLOBGRP instance. */
#define ALT_USB0_GLOB_GUID_ADDR  ALT_USB_GLOB_GUID_ADDR(ALT_USB0_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_GSNPSID register for the ALT_USB0_GLOBGRP instance. */
#define ALT_USB0_GLOB_GSNPSID_ADDR  ALT_USB_GLOB_GSNPSID_ADDR(ALT_USB0_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_GHWCFG1 register for the ALT_USB0_GLOBGRP instance. */
#define ALT_USB0_GLOB_GHWCFG1_ADDR  ALT_USB_GLOB_GHWCFG1_ADDR(ALT_USB0_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_GHWCFG2 register for the ALT_USB0_GLOBGRP instance. */
#define ALT_USB0_GLOB_GHWCFG2_ADDR  ALT_USB_GLOB_GHWCFG2_ADDR(ALT_USB0_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_GHWCFG3 register for the ALT_USB0_GLOBGRP instance. */
#define ALT_USB0_GLOB_GHWCFG3_ADDR  ALT_USB_GLOB_GHWCFG3_ADDR(ALT_USB0_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_GHWCFG4 register for the ALT_USB0_GLOBGRP instance. */
#define ALT_USB0_GLOB_GHWCFG4_ADDR  ALT_USB_GLOB_GHWCFG4_ADDR(ALT_USB0_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_GDFIFOCFG register for the ALT_USB0_GLOBGRP instance. */
#define ALT_USB0_GLOB_GDFIFOCFG_ADDR  ALT_USB_GLOB_GDFIFOCFG_ADDR(ALT_USB0_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_HPTXFSIZ register for the ALT_USB0_GLOBGRP instance. */
#define ALT_USB0_GLOB_HPTXFSIZ_ADDR  ALT_USB_GLOB_HPTXFSIZ_ADDR(ALT_USB0_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_DIEPTXF1 register for the ALT_USB0_GLOBGRP instance. */
#define ALT_USB0_GLOB_DIEPTXF1_ADDR  ALT_USB_GLOB_DIEPTXF1_ADDR(ALT_USB0_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_DIEPTXF2 register for the ALT_USB0_GLOBGRP instance. */
#define ALT_USB0_GLOB_DIEPTXF2_ADDR  ALT_USB_GLOB_DIEPTXF2_ADDR(ALT_USB0_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_DIEPTXF3 register for the ALT_USB0_GLOBGRP instance. */
#define ALT_USB0_GLOB_DIEPTXF3_ADDR  ALT_USB_GLOB_DIEPTXF3_ADDR(ALT_USB0_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_DIEPTXF4 register for the ALT_USB0_GLOBGRP instance. */
#define ALT_USB0_GLOB_DIEPTXF4_ADDR  ALT_USB_GLOB_DIEPTXF4_ADDR(ALT_USB0_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_DIEPTXF5 register for the ALT_USB0_GLOBGRP instance. */
#define ALT_USB0_GLOB_DIEPTXF5_ADDR  ALT_USB_GLOB_DIEPTXF5_ADDR(ALT_USB0_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_DIEPTXF6 register for the ALT_USB0_GLOBGRP instance. */
#define ALT_USB0_GLOB_DIEPTXF6_ADDR  ALT_USB_GLOB_DIEPTXF6_ADDR(ALT_USB0_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_DIEPTXF7 register for the ALT_USB0_GLOBGRP instance. */
#define ALT_USB0_GLOB_DIEPTXF7_ADDR  ALT_USB_GLOB_DIEPTXF7_ADDR(ALT_USB0_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_DIEPTXF8 register for the ALT_USB0_GLOBGRP instance. */
#define ALT_USB0_GLOB_DIEPTXF8_ADDR  ALT_USB_GLOB_DIEPTXF8_ADDR(ALT_USB0_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_DIEPTXF9 register for the ALT_USB0_GLOBGRP instance. */
#define ALT_USB0_GLOB_DIEPTXF9_ADDR  ALT_USB_GLOB_DIEPTXF9_ADDR(ALT_USB0_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_DIEPTXF10 register for the ALT_USB0_GLOBGRP instance. */
#define ALT_USB0_GLOB_DIEPTXF10_ADDR  ALT_USB_GLOB_DIEPTXF10_ADDR(ALT_USB0_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_DIEPTXF11 register for the ALT_USB0_GLOBGRP instance. */
#define ALT_USB0_GLOB_DIEPTXF11_ADDR  ALT_USB_GLOB_DIEPTXF11_ADDR(ALT_USB0_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_DIEPTXF12 register for the ALT_USB0_GLOBGRP instance. */
#define ALT_USB0_GLOB_DIEPTXF12_ADDR  ALT_USB_GLOB_DIEPTXF12_ADDR(ALT_USB0_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_DIEPTXF13 register for the ALT_USB0_GLOBGRP instance. */
#define ALT_USB0_GLOB_DIEPTXF13_ADDR  ALT_USB_GLOB_DIEPTXF13_ADDR(ALT_USB0_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_DIEPTXF14 register for the ALT_USB0_GLOBGRP instance. */
#define ALT_USB0_GLOB_DIEPTXF14_ADDR  ALT_USB_GLOB_DIEPTXF14_ADDR(ALT_USB0_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_DIEPTXF15 register for the ALT_USB0_GLOBGRP instance. */
#define ALT_USB0_GLOB_DIEPTXF15_ADDR  ALT_USB_GLOB_DIEPTXF15_ADDR(ALT_USB0_GLOBGRP_ADDR)
/* The base address byte offset for the start of the ALT_USB0_GLOBGRP component. */
#define ALT_USB0_GLOBGRP_OFST        0x0
/* The start address of the ALT_USB0_GLOBGRP component. */
#define ALT_USB0_GLOBGRP_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_USB0_ADDR) + ALT_USB0_GLOBGRP_OFST))
/* The lower bound address range of the ALT_USB0_GLOBGRP component. */
#define ALT_USB0_GLOBGRP_LB_ADDR     ALT_USB0_GLOBGRP_ADDR
/* The upper bound address range of the ALT_USB0_GLOBGRP component. */
#define ALT_USB0_GLOBGRP_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_USB0_GLOBGRP_ADDR) + 0x140) - 1))


/*
 * Register Group Instance : hostgrp
 * 
 * Instance hostgrp of register group ALT_USB_HOST.
 * 
 * 
 */
/* The address of the ALT_USB_HOST_HCFG register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCFG_ADDR  ALT_USB_HOST_HCFG_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HFIR register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HFIR_ADDR  ALT_USB_HOST_HFIR_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HFNUM register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HFNUM_ADDR  ALT_USB_HOST_HFNUM_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HPTXSTS register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HPTXSTS_ADDR  ALT_USB_HOST_HPTXSTS_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HAINT register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HAINT_ADDR  ALT_USB_HOST_HAINT_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HAINTMSK register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HAINTMSK_ADDR  ALT_USB_HOST_HAINTMSK_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HFLBADDR register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HFLBADDR_ADDR  ALT_USB_HOST_HFLBADDR_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HPRT register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HPRT_ADDR  ALT_USB_HOST_HPRT_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCCHAR0 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCCHAR0_ADDR  ALT_USB_HOST_HCCHAR0_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCSPLT0 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCSPLT0_ADDR  ALT_USB_HOST_HCSPLT0_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCINT0 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCINT0_ADDR  ALT_USB_HOST_HCINT0_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCINTMSK0 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCINTMSK0_ADDR  ALT_USB_HOST_HCINTMSK0_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCTSIZ0 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCTSIZ0_ADDR  ALT_USB_HOST_HCTSIZ0_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCDMA0 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCDMA0_ADDR  ALT_USB_HOST_HCDMA0_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCDMAB0 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCDMAB0_ADDR  ALT_USB_HOST_HCDMAB0_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCCHAR1 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCCHAR1_ADDR  ALT_USB_HOST_HCCHAR1_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCSPLT1 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCSPLT1_ADDR  ALT_USB_HOST_HCSPLT1_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCINT1 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCINT1_ADDR  ALT_USB_HOST_HCINT1_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCINTMSK1 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCINTMSK1_ADDR  ALT_USB_HOST_HCINTMSK1_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCTSIZ1 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCTSIZ1_ADDR  ALT_USB_HOST_HCTSIZ1_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCDMA1 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCDMA1_ADDR  ALT_USB_HOST_HCDMA1_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCDMAB1 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCDMAB1_ADDR  ALT_USB_HOST_HCDMAB1_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCCHAR2 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCCHAR2_ADDR  ALT_USB_HOST_HCCHAR2_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCSPLT2 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCSPLT2_ADDR  ALT_USB_HOST_HCSPLT2_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCINT2 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCINT2_ADDR  ALT_USB_HOST_HCINT2_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCINTMSK2 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCINTMSK2_ADDR  ALT_USB_HOST_HCINTMSK2_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCTSIZ2 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCTSIZ2_ADDR  ALT_USB_HOST_HCTSIZ2_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCDMA2 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCDMA2_ADDR  ALT_USB_HOST_HCDMA2_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCDMAB2 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCDMAB2_ADDR  ALT_USB_HOST_HCDMAB2_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCCHAR3 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCCHAR3_ADDR  ALT_USB_HOST_HCCHAR3_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCSPLT3 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCSPLT3_ADDR  ALT_USB_HOST_HCSPLT3_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCINT3 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCINT3_ADDR  ALT_USB_HOST_HCINT3_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCINTMSK3 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCINTMSK3_ADDR  ALT_USB_HOST_HCINTMSK3_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCTSIZ3 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCTSIZ3_ADDR  ALT_USB_HOST_HCTSIZ3_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCDMA3 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCDMA3_ADDR  ALT_USB_HOST_HCDMA3_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCDMAB3 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCDMAB3_ADDR  ALT_USB_HOST_HCDMAB3_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCCHAR4 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCCHAR4_ADDR  ALT_USB_HOST_HCCHAR4_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCSPLT4 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCSPLT4_ADDR  ALT_USB_HOST_HCSPLT4_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCINT4 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCINT4_ADDR  ALT_USB_HOST_HCINT4_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCINTMSK4 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCINTMSK4_ADDR  ALT_USB_HOST_HCINTMSK4_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCTSIZ4 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCTSIZ4_ADDR  ALT_USB_HOST_HCTSIZ4_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCDMA4 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCDMA4_ADDR  ALT_USB_HOST_HCDMA4_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCDMAB4 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCDMAB4_ADDR  ALT_USB_HOST_HCDMAB4_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCCHAR5 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCCHAR5_ADDR  ALT_USB_HOST_HCCHAR5_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCSPLT5 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCSPLT5_ADDR  ALT_USB_HOST_HCSPLT5_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCINT5 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCINT5_ADDR  ALT_USB_HOST_HCINT5_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCINTMSK5 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCINTMSK5_ADDR  ALT_USB_HOST_HCINTMSK5_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCTSIZ5 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCTSIZ5_ADDR  ALT_USB_HOST_HCTSIZ5_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCDMA5 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCDMA5_ADDR  ALT_USB_HOST_HCDMA5_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCDMAB5 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCDMAB5_ADDR  ALT_USB_HOST_HCDMAB5_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCCHAR6 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCCHAR6_ADDR  ALT_USB_HOST_HCCHAR6_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCSPLT6 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCSPLT6_ADDR  ALT_USB_HOST_HCSPLT6_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCINT6 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCINT6_ADDR  ALT_USB_HOST_HCINT6_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCINTMSK6 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCINTMSK6_ADDR  ALT_USB_HOST_HCINTMSK6_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCTSIZ6 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCTSIZ6_ADDR  ALT_USB_HOST_HCTSIZ6_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCDMA6 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCDMA6_ADDR  ALT_USB_HOST_HCDMA6_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCDMAB6 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCDMAB6_ADDR  ALT_USB_HOST_HCDMAB6_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCCHAR7 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCCHAR7_ADDR  ALT_USB_HOST_HCCHAR7_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCSPLT7 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCSPLT7_ADDR  ALT_USB_HOST_HCSPLT7_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCINT7 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCINT7_ADDR  ALT_USB_HOST_HCINT7_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCINTMSK7 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCINTMSK7_ADDR  ALT_USB_HOST_HCINTMSK7_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCTSIZ7 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCTSIZ7_ADDR  ALT_USB_HOST_HCTSIZ7_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCDMA7 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCDMA7_ADDR  ALT_USB_HOST_HCDMA7_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCDMAB7 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCDMAB7_ADDR  ALT_USB_HOST_HCDMAB7_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCCHAR8 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCCHAR8_ADDR  ALT_USB_HOST_HCCHAR8_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCSPLT8 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCSPLT8_ADDR  ALT_USB_HOST_HCSPLT8_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCINT8 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCINT8_ADDR  ALT_USB_HOST_HCINT8_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCINTMSK8 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCINTMSK8_ADDR  ALT_USB_HOST_HCINTMSK8_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCTSIZ8 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCTSIZ8_ADDR  ALT_USB_HOST_HCTSIZ8_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCDMA8 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCDMA8_ADDR  ALT_USB_HOST_HCDMA8_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCDMAB8 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCDMAB8_ADDR  ALT_USB_HOST_HCDMAB8_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCCHAR9 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCCHAR9_ADDR  ALT_USB_HOST_HCCHAR9_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCSPLT9 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCSPLT9_ADDR  ALT_USB_HOST_HCSPLT9_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCINT9 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCINT9_ADDR  ALT_USB_HOST_HCINT9_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCINTMSK9 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCINTMSK9_ADDR  ALT_USB_HOST_HCINTMSK9_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCTSIZ9 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCTSIZ9_ADDR  ALT_USB_HOST_HCTSIZ9_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCDMA9 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCDMA9_ADDR  ALT_USB_HOST_HCDMA9_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCDMAB9 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCDMAB9_ADDR  ALT_USB_HOST_HCDMAB9_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCCHAR10 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCCHAR10_ADDR  ALT_USB_HOST_HCCHAR10_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCSPLT10 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCSPLT10_ADDR  ALT_USB_HOST_HCSPLT10_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCINT10 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCINT10_ADDR  ALT_USB_HOST_HCINT10_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCINTMSK10 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCINTMSK10_ADDR  ALT_USB_HOST_HCINTMSK10_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCTSIZ10 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCTSIZ10_ADDR  ALT_USB_HOST_HCTSIZ10_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCDMA10 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCDMA10_ADDR  ALT_USB_HOST_HCDMA10_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCDMAB10 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCDMAB10_ADDR  ALT_USB_HOST_HCDMAB10_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCCHAR11 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCCHAR11_ADDR  ALT_USB_HOST_HCCHAR11_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCSPLT11 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCSPLT11_ADDR  ALT_USB_HOST_HCSPLT11_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCINT11 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCINT11_ADDR  ALT_USB_HOST_HCINT11_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCINTMSK11 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCINTMSK11_ADDR  ALT_USB_HOST_HCINTMSK11_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCTSIZ11 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCTSIZ11_ADDR  ALT_USB_HOST_HCTSIZ11_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCDMA11 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCDMA11_ADDR  ALT_USB_HOST_HCDMA11_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCDMAB11 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCDMAB11_ADDR  ALT_USB_HOST_HCDMAB11_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCCHAR12 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCCHAR12_ADDR  ALT_USB_HOST_HCCHAR12_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCSPLT12 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCSPLT12_ADDR  ALT_USB_HOST_HCSPLT12_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCINT12 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCINT12_ADDR  ALT_USB_HOST_HCINT12_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCINTMSK12 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCINTMSK12_ADDR  ALT_USB_HOST_HCINTMSK12_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCTSIZ12 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCTSIZ12_ADDR  ALT_USB_HOST_HCTSIZ12_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCDMA12 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCDMA12_ADDR  ALT_USB_HOST_HCDMA12_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCDMAB12 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCDMAB12_ADDR  ALT_USB_HOST_HCDMAB12_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCCHAR13 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCCHAR13_ADDR  ALT_USB_HOST_HCCHAR13_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCSPLT13 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCSPLT13_ADDR  ALT_USB_HOST_HCSPLT13_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCINT13 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCINT13_ADDR  ALT_USB_HOST_HCINT13_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCINTMSK13 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCINTMSK13_ADDR  ALT_USB_HOST_HCINTMSK13_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCTSIZ13 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCTSIZ13_ADDR  ALT_USB_HOST_HCTSIZ13_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCDMA13 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCDMA13_ADDR  ALT_USB_HOST_HCDMA13_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCDMAB13 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCDMAB13_ADDR  ALT_USB_HOST_HCDMAB13_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCCHAR14 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCCHAR14_ADDR  ALT_USB_HOST_HCCHAR14_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCSPLT14 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCSPLT14_ADDR  ALT_USB_HOST_HCSPLT14_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCINT14 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCINT14_ADDR  ALT_USB_HOST_HCINT14_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCINTMSK14 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCINTMSK14_ADDR  ALT_USB_HOST_HCINTMSK14_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCTSIZ14 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCTSIZ14_ADDR  ALT_USB_HOST_HCTSIZ14_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCDMA14 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCDMA14_ADDR  ALT_USB_HOST_HCDMA14_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCDMAB14 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCDMAB14_ADDR  ALT_USB_HOST_HCDMAB14_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCCHAR15 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCCHAR15_ADDR  ALT_USB_HOST_HCCHAR15_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCSPLT15 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCSPLT15_ADDR  ALT_USB_HOST_HCSPLT15_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCINT15 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCINT15_ADDR  ALT_USB_HOST_HCINT15_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCINTMSK15 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCINTMSK15_ADDR  ALT_USB_HOST_HCINTMSK15_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCTSIZ15 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCTSIZ15_ADDR  ALT_USB_HOST_HCTSIZ15_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCDMA15 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCDMA15_ADDR  ALT_USB_HOST_HCDMA15_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCDMAB15 register for the ALT_USB0_HOSTGRP instance. */
#define ALT_USB0_HOST_HCDMAB15_ADDR  ALT_USB_HOST_HCDMAB15_ADDR(ALT_USB0_HOSTGRP_ADDR)
/* The base address byte offset for the start of the ALT_USB0_HOSTGRP component. */
#define ALT_USB0_HOSTGRP_OFST        0x400
/* The start address of the ALT_USB0_HOSTGRP component. */
#define ALT_USB0_HOSTGRP_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_USB0_ADDR) + ALT_USB0_HOSTGRP_OFST))
/* The lower bound address range of the ALT_USB0_HOSTGRP component. */
#define ALT_USB0_HOSTGRP_LB_ADDR     ALT_USB0_HOSTGRP_ADDR
/* The upper bound address range of the ALT_USB0_HOSTGRP component. */
#define ALT_USB0_HOSTGRP_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_USB0_HOSTGRP_ADDR) + 0x2fc) - 1))


/*
 * Register Group Instance : devgrp
 * 
 * Instance devgrp of register group ALT_USB_DEV.
 * 
 * 
 */
/* The address of the ALT_USB_DEV_DCFG register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DCFG_ADDR  ALT_USB_DEV_DCFG_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DCTL register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DCTL_ADDR  ALT_USB_DEV_DCTL_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DSTS register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DSTS_ADDR  ALT_USB_DEV_DSTS_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPMSK register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPMSK_ADDR  ALT_USB_DEV_DIEPMSK_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPMSK register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPMSK_ADDR  ALT_USB_DEV_DOEPMSK_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DAINT register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DAINT_ADDR  ALT_USB_DEV_DAINT_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DAINTMSK register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DAINTMSK_ADDR  ALT_USB_DEV_DAINTMSK_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DVBUSDIS register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DVBUSDIS_ADDR  ALT_USB_DEV_DVBUSDIS_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DVBUSPULSE register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DVBUSPULSE_ADDR  ALT_USB_DEV_DVBUSPULSE_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DTHRCTL register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DTHRCTL_ADDR  ALT_USB_DEV_DTHRCTL_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPEMPMSK register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPEMPMSK_ADDR  ALT_USB_DEV_DIEPEMPMSK_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPCTL0 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPCTL0_ADDR  ALT_USB_DEV_DIEPCTL0_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPINT0 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPINT0_ADDR  ALT_USB_DEV_DIEPINT0_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPTSIZ0 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPTSIZ0_ADDR  ALT_USB_DEV_DIEPTSIZ0_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPDMA0 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPDMA0_ADDR  ALT_USB_DEV_DIEPDMA0_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DTXFSTS0 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DTXFSTS0_ADDR  ALT_USB_DEV_DTXFSTS0_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPDMAB0 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPDMAB0_ADDR  ALT_USB_DEV_DIEPDMAB0_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPCTL1 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPCTL1_ADDR  ALT_USB_DEV_DIEPCTL1_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPINT1 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPINT1_ADDR  ALT_USB_DEV_DIEPINT1_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPTSIZ1 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPTSIZ1_ADDR  ALT_USB_DEV_DIEPTSIZ1_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPDMA1 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPDMA1_ADDR  ALT_USB_DEV_DIEPDMA1_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DTXFSTS1 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DTXFSTS1_ADDR  ALT_USB_DEV_DTXFSTS1_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPDMAB1 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPDMAB1_ADDR  ALT_USB_DEV_DIEPDMAB1_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPCTL2 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPCTL2_ADDR  ALT_USB_DEV_DIEPCTL2_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPINT2 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPINT2_ADDR  ALT_USB_DEV_DIEPINT2_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPTSIZ2 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPTSIZ2_ADDR  ALT_USB_DEV_DIEPTSIZ2_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPDMA2 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPDMA2_ADDR  ALT_USB_DEV_DIEPDMA2_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DTXFSTS2 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DTXFSTS2_ADDR  ALT_USB_DEV_DTXFSTS2_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPDMAB2 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPDMAB2_ADDR  ALT_USB_DEV_DIEPDMAB2_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPCTL3 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPCTL3_ADDR  ALT_USB_DEV_DIEPCTL3_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPINT3 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPINT3_ADDR  ALT_USB_DEV_DIEPINT3_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPTSIZ3 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPTSIZ3_ADDR  ALT_USB_DEV_DIEPTSIZ3_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPDMA3 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPDMA3_ADDR  ALT_USB_DEV_DIEPDMA3_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DTXFSTS3 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DTXFSTS3_ADDR  ALT_USB_DEV_DTXFSTS3_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPDMAB3 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPDMAB3_ADDR  ALT_USB_DEV_DIEPDMAB3_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPCTL4 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPCTL4_ADDR  ALT_USB_DEV_DIEPCTL4_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPINT4 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPINT4_ADDR  ALT_USB_DEV_DIEPINT4_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPTSIZ4 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPTSIZ4_ADDR  ALT_USB_DEV_DIEPTSIZ4_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPDMA4 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPDMA4_ADDR  ALT_USB_DEV_DIEPDMA4_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DTXFSTS4 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DTXFSTS4_ADDR  ALT_USB_DEV_DTXFSTS4_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPDMAB4 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPDMAB4_ADDR  ALT_USB_DEV_DIEPDMAB4_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPCTL5 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPCTL5_ADDR  ALT_USB_DEV_DIEPCTL5_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPINT5 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPINT5_ADDR  ALT_USB_DEV_DIEPINT5_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPTSIZ5 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPTSIZ5_ADDR  ALT_USB_DEV_DIEPTSIZ5_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPDMA5 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPDMA5_ADDR  ALT_USB_DEV_DIEPDMA5_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DTXFSTS5 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DTXFSTS5_ADDR  ALT_USB_DEV_DTXFSTS5_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPDMAB5 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPDMAB5_ADDR  ALT_USB_DEV_DIEPDMAB5_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPCTL6 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPCTL6_ADDR  ALT_USB_DEV_DIEPCTL6_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPINT6 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPINT6_ADDR  ALT_USB_DEV_DIEPINT6_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPTSIZ6 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPTSIZ6_ADDR  ALT_USB_DEV_DIEPTSIZ6_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPDMA6 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPDMA6_ADDR  ALT_USB_DEV_DIEPDMA6_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DTXFSTS6 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DTXFSTS6_ADDR  ALT_USB_DEV_DTXFSTS6_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPDMAB6 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPDMAB6_ADDR  ALT_USB_DEV_DIEPDMAB6_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPCTL7 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPCTL7_ADDR  ALT_USB_DEV_DIEPCTL7_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPINT7 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPINT7_ADDR  ALT_USB_DEV_DIEPINT7_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPTSIZ7 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPTSIZ7_ADDR  ALT_USB_DEV_DIEPTSIZ7_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPDMA7 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPDMA7_ADDR  ALT_USB_DEV_DIEPDMA7_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DTXFSTS7 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DTXFSTS7_ADDR  ALT_USB_DEV_DTXFSTS7_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPDMAB7 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPDMAB7_ADDR  ALT_USB_DEV_DIEPDMAB7_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPCTL8 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPCTL8_ADDR  ALT_USB_DEV_DIEPCTL8_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPINT8 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPINT8_ADDR  ALT_USB_DEV_DIEPINT8_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPTSIZ8 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPTSIZ8_ADDR  ALT_USB_DEV_DIEPTSIZ8_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPDMA8 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPDMA8_ADDR  ALT_USB_DEV_DIEPDMA8_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DTXFSTS8 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DTXFSTS8_ADDR  ALT_USB_DEV_DTXFSTS8_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPDMAB8 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPDMAB8_ADDR  ALT_USB_DEV_DIEPDMAB8_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPCTL9 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPCTL9_ADDR  ALT_USB_DEV_DIEPCTL9_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPINT9 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPINT9_ADDR  ALT_USB_DEV_DIEPINT9_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPTSIZ9 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPTSIZ9_ADDR  ALT_USB_DEV_DIEPTSIZ9_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPDMA9 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPDMA9_ADDR  ALT_USB_DEV_DIEPDMA9_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DTXFSTS9 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DTXFSTS9_ADDR  ALT_USB_DEV_DTXFSTS9_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPDMAB9 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPDMAB9_ADDR  ALT_USB_DEV_DIEPDMAB9_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPCTL10 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPCTL10_ADDR  ALT_USB_DEV_DIEPCTL10_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPINT10 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPINT10_ADDR  ALT_USB_DEV_DIEPINT10_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPTSIZ10 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPTSIZ10_ADDR  ALT_USB_DEV_DIEPTSIZ10_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPDMA10 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPDMA10_ADDR  ALT_USB_DEV_DIEPDMA10_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DTXFSTS10 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DTXFSTS10_ADDR  ALT_USB_DEV_DTXFSTS10_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPDMAB10 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPDMAB10_ADDR  ALT_USB_DEV_DIEPDMAB10_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPCTL11 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPCTL11_ADDR  ALT_USB_DEV_DIEPCTL11_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPINT11 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPINT11_ADDR  ALT_USB_DEV_DIEPINT11_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPTSIZ11 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPTSIZ11_ADDR  ALT_USB_DEV_DIEPTSIZ11_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPDMA11 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPDMA11_ADDR  ALT_USB_DEV_DIEPDMA11_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DTXFSTS11 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DTXFSTS11_ADDR  ALT_USB_DEV_DTXFSTS11_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPDMAB11 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPDMAB11_ADDR  ALT_USB_DEV_DIEPDMAB11_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPCTL12 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPCTL12_ADDR  ALT_USB_DEV_DIEPCTL12_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPINT12 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPINT12_ADDR  ALT_USB_DEV_DIEPINT12_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPTSIZ12 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPTSIZ12_ADDR  ALT_USB_DEV_DIEPTSIZ12_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPDMA12 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPDMA12_ADDR  ALT_USB_DEV_DIEPDMA12_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DTXFSTS12 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DTXFSTS12_ADDR  ALT_USB_DEV_DTXFSTS12_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPDMAB12 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPDMAB12_ADDR  ALT_USB_DEV_DIEPDMAB12_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPCTL13 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPCTL13_ADDR  ALT_USB_DEV_DIEPCTL13_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPINT13 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPINT13_ADDR  ALT_USB_DEV_DIEPINT13_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPTSIZ13 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPTSIZ13_ADDR  ALT_USB_DEV_DIEPTSIZ13_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPDMA13 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPDMA13_ADDR  ALT_USB_DEV_DIEPDMA13_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DTXFSTS13 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DTXFSTS13_ADDR  ALT_USB_DEV_DTXFSTS13_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPDMAB13 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPDMAB13_ADDR  ALT_USB_DEV_DIEPDMAB13_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPCTL14 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPCTL14_ADDR  ALT_USB_DEV_DIEPCTL14_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPINT14 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPINT14_ADDR  ALT_USB_DEV_DIEPINT14_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPTSIZ14 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPTSIZ14_ADDR  ALT_USB_DEV_DIEPTSIZ14_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPDMA14 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPDMA14_ADDR  ALT_USB_DEV_DIEPDMA14_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DTXFSTS14 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DTXFSTS14_ADDR  ALT_USB_DEV_DTXFSTS14_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPDMAB14 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPDMAB14_ADDR  ALT_USB_DEV_DIEPDMAB14_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPCTL15 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPCTL15_ADDR  ALT_USB_DEV_DIEPCTL15_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPINT15 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPINT15_ADDR  ALT_USB_DEV_DIEPINT15_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPTSIZ15 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPTSIZ15_ADDR  ALT_USB_DEV_DIEPTSIZ15_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPDMA15 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPDMA15_ADDR  ALT_USB_DEV_DIEPDMA15_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DTXFSTS15 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DTXFSTS15_ADDR  ALT_USB_DEV_DTXFSTS15_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPDMAB15 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DIEPDMAB15_ADDR  ALT_USB_DEV_DIEPDMAB15_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPCTL0 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPCTL0_ADDR  ALT_USB_DEV_DOEPCTL0_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPINT0 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPINT0_ADDR  ALT_USB_DEV_DOEPINT0_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPTSIZ0 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPTSIZ0_ADDR  ALT_USB_DEV_DOEPTSIZ0_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPDMA0 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPDMA0_ADDR  ALT_USB_DEV_DOEPDMA0_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPDMAB0 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPDMAB0_ADDR  ALT_USB_DEV_DOEPDMAB0_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPCTL1 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPCTL1_ADDR  ALT_USB_DEV_DOEPCTL1_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPINT1 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPINT1_ADDR  ALT_USB_DEV_DOEPINT1_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPTSIZ1 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPTSIZ1_ADDR  ALT_USB_DEV_DOEPTSIZ1_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPDMA1 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPDMA1_ADDR  ALT_USB_DEV_DOEPDMA1_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPDMAB1 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPDMAB1_ADDR  ALT_USB_DEV_DOEPDMAB1_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPCTL2 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPCTL2_ADDR  ALT_USB_DEV_DOEPCTL2_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPINT2 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPINT2_ADDR  ALT_USB_DEV_DOEPINT2_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPTSIZ2 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPTSIZ2_ADDR  ALT_USB_DEV_DOEPTSIZ2_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPDMA2 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPDMA2_ADDR  ALT_USB_DEV_DOEPDMA2_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPDMAB2 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPDMAB2_ADDR  ALT_USB_DEV_DOEPDMAB2_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPCTL3 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPCTL3_ADDR  ALT_USB_DEV_DOEPCTL3_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPINT3 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPINT3_ADDR  ALT_USB_DEV_DOEPINT3_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPTSIZ3 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPTSIZ3_ADDR  ALT_USB_DEV_DOEPTSIZ3_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPDMA3 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPDMA3_ADDR  ALT_USB_DEV_DOEPDMA3_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPDMAB3 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPDMAB3_ADDR  ALT_USB_DEV_DOEPDMAB3_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPCTL4 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPCTL4_ADDR  ALT_USB_DEV_DOEPCTL4_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPINT4 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPINT4_ADDR  ALT_USB_DEV_DOEPINT4_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPTSIZ4 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPTSIZ4_ADDR  ALT_USB_DEV_DOEPTSIZ4_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPDMA4 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPDMA4_ADDR  ALT_USB_DEV_DOEPDMA4_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPDMAB4 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPDMAB4_ADDR  ALT_USB_DEV_DOEPDMAB4_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPCTL5 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPCTL5_ADDR  ALT_USB_DEV_DOEPCTL5_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPINT5 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPINT5_ADDR  ALT_USB_DEV_DOEPINT5_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPTSIZ5 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPTSIZ5_ADDR  ALT_USB_DEV_DOEPTSIZ5_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPDMA5 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPDMA5_ADDR  ALT_USB_DEV_DOEPDMA5_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPDMAB5 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPDMAB5_ADDR  ALT_USB_DEV_DOEPDMAB5_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPCTL6 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPCTL6_ADDR  ALT_USB_DEV_DOEPCTL6_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPINT6 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPINT6_ADDR  ALT_USB_DEV_DOEPINT6_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPTSIZ6 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPTSIZ6_ADDR  ALT_USB_DEV_DOEPTSIZ6_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPDMA6 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPDMA6_ADDR  ALT_USB_DEV_DOEPDMA6_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPDMAB6 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPDMAB6_ADDR  ALT_USB_DEV_DOEPDMAB6_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPCTL7 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPCTL7_ADDR  ALT_USB_DEV_DOEPCTL7_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPINT7 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPINT7_ADDR  ALT_USB_DEV_DOEPINT7_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPTSIZ7 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPTSIZ7_ADDR  ALT_USB_DEV_DOEPTSIZ7_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPDMA7 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPDMA7_ADDR  ALT_USB_DEV_DOEPDMA7_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPDMAB7 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPDMAB7_ADDR  ALT_USB_DEV_DOEPDMAB7_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPCTL8 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPCTL8_ADDR  ALT_USB_DEV_DOEPCTL8_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPINT8 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPINT8_ADDR  ALT_USB_DEV_DOEPINT8_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPTSIZ8 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPTSIZ8_ADDR  ALT_USB_DEV_DOEPTSIZ8_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPDMA8 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPDMA8_ADDR  ALT_USB_DEV_DOEPDMA8_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPDMAB8 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPDMAB8_ADDR  ALT_USB_DEV_DOEPDMAB8_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPCTL9 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPCTL9_ADDR  ALT_USB_DEV_DOEPCTL9_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPINT9 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPINT9_ADDR  ALT_USB_DEV_DOEPINT9_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPTSIZ9 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPTSIZ9_ADDR  ALT_USB_DEV_DOEPTSIZ9_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPDMA9 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPDMA9_ADDR  ALT_USB_DEV_DOEPDMA9_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPDMAB9 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPDMAB9_ADDR  ALT_USB_DEV_DOEPDMAB9_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPCTL10 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPCTL10_ADDR  ALT_USB_DEV_DOEPCTL10_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPINT10 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPINT10_ADDR  ALT_USB_DEV_DOEPINT10_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPTSIZ10 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPTSIZ10_ADDR  ALT_USB_DEV_DOEPTSIZ10_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPDMA10 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPDMA10_ADDR  ALT_USB_DEV_DOEPDMA10_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPDMAB10 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPDMAB10_ADDR  ALT_USB_DEV_DOEPDMAB10_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPCTL11 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPCTL11_ADDR  ALT_USB_DEV_DOEPCTL11_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPINT11 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPINT11_ADDR  ALT_USB_DEV_DOEPINT11_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPTSIZ11 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPTSIZ11_ADDR  ALT_USB_DEV_DOEPTSIZ11_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPDMA11 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPDMA11_ADDR  ALT_USB_DEV_DOEPDMA11_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPDMAB11 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPDMAB11_ADDR  ALT_USB_DEV_DOEPDMAB11_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPCTL12 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPCTL12_ADDR  ALT_USB_DEV_DOEPCTL12_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPINT12 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPINT12_ADDR  ALT_USB_DEV_DOEPINT12_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPTSIZ12 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPTSIZ12_ADDR  ALT_USB_DEV_DOEPTSIZ12_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPDMA12 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPDMA12_ADDR  ALT_USB_DEV_DOEPDMA12_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPDMAB12 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPDMAB12_ADDR  ALT_USB_DEV_DOEPDMAB12_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPCTL13 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPCTL13_ADDR  ALT_USB_DEV_DOEPCTL13_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPINT13 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPINT13_ADDR  ALT_USB_DEV_DOEPINT13_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPTSIZ13 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPTSIZ13_ADDR  ALT_USB_DEV_DOEPTSIZ13_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPDMA13 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPDMA13_ADDR  ALT_USB_DEV_DOEPDMA13_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPDMAB13 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPDMAB13_ADDR  ALT_USB_DEV_DOEPDMAB13_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPCTL14 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPCTL14_ADDR  ALT_USB_DEV_DOEPCTL14_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPINT14 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPINT14_ADDR  ALT_USB_DEV_DOEPINT14_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPTSIZ14 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPTSIZ14_ADDR  ALT_USB_DEV_DOEPTSIZ14_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPDMA14 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPDMA14_ADDR  ALT_USB_DEV_DOEPDMA14_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPDMAB14 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPDMAB14_ADDR  ALT_USB_DEV_DOEPDMAB14_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPCTL15 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPCTL15_ADDR  ALT_USB_DEV_DOEPCTL15_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPINT15 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPINT15_ADDR  ALT_USB_DEV_DOEPINT15_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPTSIZ15 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPTSIZ15_ADDR  ALT_USB_DEV_DOEPTSIZ15_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPDMA15 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPDMA15_ADDR  ALT_USB_DEV_DOEPDMA15_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPDMAB15 register for the ALT_USB0_DEVGRP instance. */
#define ALT_USB0_DEV_DOEPDMAB15_ADDR  ALT_USB_DEV_DOEPDMAB15_ADDR(ALT_USB0_DEVGRP_ADDR)
/* The base address byte offset for the start of the ALT_USB0_DEVGRP component. */
#define ALT_USB0_DEVGRP_OFST        0x800
/* The start address of the ALT_USB0_DEVGRP component. */
#define ALT_USB0_DEVGRP_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_USB0_ADDR) + ALT_USB0_DEVGRP_OFST))
/* The lower bound address range of the ALT_USB0_DEVGRP component. */
#define ALT_USB0_DEVGRP_LB_ADDR     ALT_USB0_DEVGRP_ADDR
/* The upper bound address range of the ALT_USB0_DEVGRP component. */
#define ALT_USB0_DEVGRP_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_USB0_DEVGRP_ADDR) + 0x500) - 1))


/*
 * Register Group Instance : pwrclkgrp
 * 
 * Instance pwrclkgrp of register group ALT_USB_PWRCLK.
 * 
 * 
 */
/* The address of the ALT_USB_PWRCLK_PCGCCTL register for the ALT_USB0_PWRCLKGRP instance. */
#define ALT_USB0_PWRCLK_PCGCCTL_ADDR  ALT_USB_PWRCLK_PCGCCTL_ADDR(ALT_USB0_PWRCLKGRP_ADDR)
/* The base address byte offset for the start of the ALT_USB0_PWRCLKGRP component. */
#define ALT_USB0_PWRCLKGRP_OFST        0xe00
/* The start address of the ALT_USB0_PWRCLKGRP component. */
#define ALT_USB0_PWRCLKGRP_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_USB0_ADDR) + ALT_USB0_PWRCLKGRP_OFST))
/* The lower bound address range of the ALT_USB0_PWRCLKGRP component. */
#define ALT_USB0_PWRCLKGRP_LB_ADDR     ALT_USB0_PWRCLKGRP_ADDR
/* The upper bound address range of the ALT_USB0_PWRCLKGRP component. */
#define ALT_USB0_PWRCLKGRP_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_USB0_PWRCLKGRP_ADDR) + 0x4) - 1))


/* The base address byte offset for the start of the ALT_USB0 component. */
#define ALT_USB0_OFST        0xffb00000
/* The start address of the ALT_USB0 component. */
#define ALT_USB0_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_HPS_ADDR) + ALT_USB0_OFST))
/* The lower bound address range of the ALT_USB0 component. */
#define ALT_USB0_LB_ADDR     ALT_USB0_ADDR
/* The upper bound address range of the ALT_USB0 component. */
#define ALT_USB0_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_USB0_ADDR) + 0x40000) - 1))


/*
 * Component Instance : usb1
 * 
 * Instance usb1 of component ALT_USB.
 * 
 * 
 */
/*
 * Register Group Instance : globgrp
 * 
 * Instance globgrp of register group ALT_USB_GLOB.
 * 
 * 
 */
/* The address of the ALT_USB_GLOB_GOTGCTL register for the ALT_USB1_GLOBGRP instance. */
#define ALT_USB1_GLOB_GOTGCTL_ADDR  ALT_USB_GLOB_GOTGCTL_ADDR(ALT_USB1_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_GOTGINT register for the ALT_USB1_GLOBGRP instance. */
#define ALT_USB1_GLOB_GOTGINT_ADDR  ALT_USB_GLOB_GOTGINT_ADDR(ALT_USB1_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_GAHBCFG register for the ALT_USB1_GLOBGRP instance. */
#define ALT_USB1_GLOB_GAHBCFG_ADDR  ALT_USB_GLOB_GAHBCFG_ADDR(ALT_USB1_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_GUSBCFG register for the ALT_USB1_GLOBGRP instance. */
#define ALT_USB1_GLOB_GUSBCFG_ADDR  ALT_USB_GLOB_GUSBCFG_ADDR(ALT_USB1_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_GRSTCTL register for the ALT_USB1_GLOBGRP instance. */
#define ALT_USB1_GLOB_GRSTCTL_ADDR  ALT_USB_GLOB_GRSTCTL_ADDR(ALT_USB1_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_GINTSTS register for the ALT_USB1_GLOBGRP instance. */
#define ALT_USB1_GLOB_GINTSTS_ADDR  ALT_USB_GLOB_GINTSTS_ADDR(ALT_USB1_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_GINTMSK register for the ALT_USB1_GLOBGRP instance. */
#define ALT_USB1_GLOB_GINTMSK_ADDR  ALT_USB_GLOB_GINTMSK_ADDR(ALT_USB1_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_GRXSTSR register for the ALT_USB1_GLOBGRP instance. */
#define ALT_USB1_GLOB_GRXSTSR_ADDR  ALT_USB_GLOB_GRXSTSR_ADDR(ALT_USB1_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_GRXSTSP register for the ALT_USB1_GLOBGRP instance. */
#define ALT_USB1_GLOB_GRXSTSP_ADDR  ALT_USB_GLOB_GRXSTSP_ADDR(ALT_USB1_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_GRXFSIZ register for the ALT_USB1_GLOBGRP instance. */
#define ALT_USB1_GLOB_GRXFSIZ_ADDR  ALT_USB_GLOB_GRXFSIZ_ADDR(ALT_USB1_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_GNPTXFSIZ register for the ALT_USB1_GLOBGRP instance. */
#define ALT_USB1_GLOB_GNPTXFSIZ_ADDR  ALT_USB_GLOB_GNPTXFSIZ_ADDR(ALT_USB1_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_GNPTXSTS register for the ALT_USB1_GLOBGRP instance. */
#define ALT_USB1_GLOB_GNPTXSTS_ADDR  ALT_USB_GLOB_GNPTXSTS_ADDR(ALT_USB1_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_GPVNDCTL register for the ALT_USB1_GLOBGRP instance. */
#define ALT_USB1_GLOB_GPVNDCTL_ADDR  ALT_USB_GLOB_GPVNDCTL_ADDR(ALT_USB1_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_GGPIO register for the ALT_USB1_GLOBGRP instance. */
#define ALT_USB1_GLOB_GGPIO_ADDR  ALT_USB_GLOB_GGPIO_ADDR(ALT_USB1_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_GUID register for the ALT_USB1_GLOBGRP instance. */
#define ALT_USB1_GLOB_GUID_ADDR  ALT_USB_GLOB_GUID_ADDR(ALT_USB1_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_GSNPSID register for the ALT_USB1_GLOBGRP instance. */
#define ALT_USB1_GLOB_GSNPSID_ADDR  ALT_USB_GLOB_GSNPSID_ADDR(ALT_USB1_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_GHWCFG1 register for the ALT_USB1_GLOBGRP instance. */
#define ALT_USB1_GLOB_GHWCFG1_ADDR  ALT_USB_GLOB_GHWCFG1_ADDR(ALT_USB1_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_GHWCFG2 register for the ALT_USB1_GLOBGRP instance. */
#define ALT_USB1_GLOB_GHWCFG2_ADDR  ALT_USB_GLOB_GHWCFG2_ADDR(ALT_USB1_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_GHWCFG3 register for the ALT_USB1_GLOBGRP instance. */
#define ALT_USB1_GLOB_GHWCFG3_ADDR  ALT_USB_GLOB_GHWCFG3_ADDR(ALT_USB1_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_GHWCFG4 register for the ALT_USB1_GLOBGRP instance. */
#define ALT_USB1_GLOB_GHWCFG4_ADDR  ALT_USB_GLOB_GHWCFG4_ADDR(ALT_USB1_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_GDFIFOCFG register for the ALT_USB1_GLOBGRP instance. */
#define ALT_USB1_GLOB_GDFIFOCFG_ADDR  ALT_USB_GLOB_GDFIFOCFG_ADDR(ALT_USB1_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_HPTXFSIZ register for the ALT_USB1_GLOBGRP instance. */
#define ALT_USB1_GLOB_HPTXFSIZ_ADDR  ALT_USB_GLOB_HPTXFSIZ_ADDR(ALT_USB1_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_DIEPTXF1 register for the ALT_USB1_GLOBGRP instance. */
#define ALT_USB1_GLOB_DIEPTXF1_ADDR  ALT_USB_GLOB_DIEPTXF1_ADDR(ALT_USB1_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_DIEPTXF2 register for the ALT_USB1_GLOBGRP instance. */
#define ALT_USB1_GLOB_DIEPTXF2_ADDR  ALT_USB_GLOB_DIEPTXF2_ADDR(ALT_USB1_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_DIEPTXF3 register for the ALT_USB1_GLOBGRP instance. */
#define ALT_USB1_GLOB_DIEPTXF3_ADDR  ALT_USB_GLOB_DIEPTXF3_ADDR(ALT_USB1_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_DIEPTXF4 register for the ALT_USB1_GLOBGRP instance. */
#define ALT_USB1_GLOB_DIEPTXF4_ADDR  ALT_USB_GLOB_DIEPTXF4_ADDR(ALT_USB1_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_DIEPTXF5 register for the ALT_USB1_GLOBGRP instance. */
#define ALT_USB1_GLOB_DIEPTXF5_ADDR  ALT_USB_GLOB_DIEPTXF5_ADDR(ALT_USB1_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_DIEPTXF6 register for the ALT_USB1_GLOBGRP instance. */
#define ALT_USB1_GLOB_DIEPTXF6_ADDR  ALT_USB_GLOB_DIEPTXF6_ADDR(ALT_USB1_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_DIEPTXF7 register for the ALT_USB1_GLOBGRP instance. */
#define ALT_USB1_GLOB_DIEPTXF7_ADDR  ALT_USB_GLOB_DIEPTXF7_ADDR(ALT_USB1_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_DIEPTXF8 register for the ALT_USB1_GLOBGRP instance. */
#define ALT_USB1_GLOB_DIEPTXF8_ADDR  ALT_USB_GLOB_DIEPTXF8_ADDR(ALT_USB1_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_DIEPTXF9 register for the ALT_USB1_GLOBGRP instance. */
#define ALT_USB1_GLOB_DIEPTXF9_ADDR  ALT_USB_GLOB_DIEPTXF9_ADDR(ALT_USB1_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_DIEPTXF10 register for the ALT_USB1_GLOBGRP instance. */
#define ALT_USB1_GLOB_DIEPTXF10_ADDR  ALT_USB_GLOB_DIEPTXF10_ADDR(ALT_USB1_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_DIEPTXF11 register for the ALT_USB1_GLOBGRP instance. */
#define ALT_USB1_GLOB_DIEPTXF11_ADDR  ALT_USB_GLOB_DIEPTXF11_ADDR(ALT_USB1_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_DIEPTXF12 register for the ALT_USB1_GLOBGRP instance. */
#define ALT_USB1_GLOB_DIEPTXF12_ADDR  ALT_USB_GLOB_DIEPTXF12_ADDR(ALT_USB1_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_DIEPTXF13 register for the ALT_USB1_GLOBGRP instance. */
#define ALT_USB1_GLOB_DIEPTXF13_ADDR  ALT_USB_GLOB_DIEPTXF13_ADDR(ALT_USB1_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_DIEPTXF14 register for the ALT_USB1_GLOBGRP instance. */
#define ALT_USB1_GLOB_DIEPTXF14_ADDR  ALT_USB_GLOB_DIEPTXF14_ADDR(ALT_USB1_GLOBGRP_ADDR)
/* The address of the ALT_USB_GLOB_DIEPTXF15 register for the ALT_USB1_GLOBGRP instance. */
#define ALT_USB1_GLOB_DIEPTXF15_ADDR  ALT_USB_GLOB_DIEPTXF15_ADDR(ALT_USB1_GLOBGRP_ADDR)
/* The base address byte offset for the start of the ALT_USB1_GLOBGRP component. */
#define ALT_USB1_GLOBGRP_OFST        0x0
/* The start address of the ALT_USB1_GLOBGRP component. */
#define ALT_USB1_GLOBGRP_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_USB1_ADDR) + ALT_USB1_GLOBGRP_OFST))
/* The lower bound address range of the ALT_USB1_GLOBGRP component. */
#define ALT_USB1_GLOBGRP_LB_ADDR     ALT_USB1_GLOBGRP_ADDR
/* The upper bound address range of the ALT_USB1_GLOBGRP component. */
#define ALT_USB1_GLOBGRP_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_USB1_GLOBGRP_ADDR) + 0x140) - 1))


/*
 * Register Group Instance : hostgrp
 * 
 * Instance hostgrp of register group ALT_USB_HOST.
 * 
 * 
 */
/* The address of the ALT_USB_HOST_HCFG register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCFG_ADDR  ALT_USB_HOST_HCFG_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HFIR register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HFIR_ADDR  ALT_USB_HOST_HFIR_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HFNUM register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HFNUM_ADDR  ALT_USB_HOST_HFNUM_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HPTXSTS register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HPTXSTS_ADDR  ALT_USB_HOST_HPTXSTS_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HAINT register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HAINT_ADDR  ALT_USB_HOST_HAINT_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HAINTMSK register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HAINTMSK_ADDR  ALT_USB_HOST_HAINTMSK_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HFLBADDR register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HFLBADDR_ADDR  ALT_USB_HOST_HFLBADDR_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HPRT register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HPRT_ADDR  ALT_USB_HOST_HPRT_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCCHAR0 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCCHAR0_ADDR  ALT_USB_HOST_HCCHAR0_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCSPLT0 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCSPLT0_ADDR  ALT_USB_HOST_HCSPLT0_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCINT0 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCINT0_ADDR  ALT_USB_HOST_HCINT0_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCINTMSK0 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCINTMSK0_ADDR  ALT_USB_HOST_HCINTMSK0_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCTSIZ0 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCTSIZ0_ADDR  ALT_USB_HOST_HCTSIZ0_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCDMA0 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCDMA0_ADDR  ALT_USB_HOST_HCDMA0_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCDMAB0 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCDMAB0_ADDR  ALT_USB_HOST_HCDMAB0_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCCHAR1 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCCHAR1_ADDR  ALT_USB_HOST_HCCHAR1_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCSPLT1 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCSPLT1_ADDR  ALT_USB_HOST_HCSPLT1_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCINT1 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCINT1_ADDR  ALT_USB_HOST_HCINT1_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCINTMSK1 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCINTMSK1_ADDR  ALT_USB_HOST_HCINTMSK1_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCTSIZ1 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCTSIZ1_ADDR  ALT_USB_HOST_HCTSIZ1_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCDMA1 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCDMA1_ADDR  ALT_USB_HOST_HCDMA1_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCDMAB1 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCDMAB1_ADDR  ALT_USB_HOST_HCDMAB1_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCCHAR2 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCCHAR2_ADDR  ALT_USB_HOST_HCCHAR2_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCSPLT2 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCSPLT2_ADDR  ALT_USB_HOST_HCSPLT2_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCINT2 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCINT2_ADDR  ALT_USB_HOST_HCINT2_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCINTMSK2 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCINTMSK2_ADDR  ALT_USB_HOST_HCINTMSK2_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCTSIZ2 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCTSIZ2_ADDR  ALT_USB_HOST_HCTSIZ2_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCDMA2 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCDMA2_ADDR  ALT_USB_HOST_HCDMA2_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCDMAB2 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCDMAB2_ADDR  ALT_USB_HOST_HCDMAB2_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCCHAR3 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCCHAR3_ADDR  ALT_USB_HOST_HCCHAR3_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCSPLT3 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCSPLT3_ADDR  ALT_USB_HOST_HCSPLT3_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCINT3 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCINT3_ADDR  ALT_USB_HOST_HCINT3_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCINTMSK3 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCINTMSK3_ADDR  ALT_USB_HOST_HCINTMSK3_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCTSIZ3 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCTSIZ3_ADDR  ALT_USB_HOST_HCTSIZ3_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCDMA3 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCDMA3_ADDR  ALT_USB_HOST_HCDMA3_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCDMAB3 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCDMAB3_ADDR  ALT_USB_HOST_HCDMAB3_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCCHAR4 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCCHAR4_ADDR  ALT_USB_HOST_HCCHAR4_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCSPLT4 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCSPLT4_ADDR  ALT_USB_HOST_HCSPLT4_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCINT4 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCINT4_ADDR  ALT_USB_HOST_HCINT4_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCINTMSK4 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCINTMSK4_ADDR  ALT_USB_HOST_HCINTMSK4_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCTSIZ4 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCTSIZ4_ADDR  ALT_USB_HOST_HCTSIZ4_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCDMA4 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCDMA4_ADDR  ALT_USB_HOST_HCDMA4_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCDMAB4 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCDMAB4_ADDR  ALT_USB_HOST_HCDMAB4_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCCHAR5 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCCHAR5_ADDR  ALT_USB_HOST_HCCHAR5_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCSPLT5 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCSPLT5_ADDR  ALT_USB_HOST_HCSPLT5_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCINT5 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCINT5_ADDR  ALT_USB_HOST_HCINT5_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCINTMSK5 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCINTMSK5_ADDR  ALT_USB_HOST_HCINTMSK5_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCTSIZ5 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCTSIZ5_ADDR  ALT_USB_HOST_HCTSIZ5_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCDMA5 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCDMA5_ADDR  ALT_USB_HOST_HCDMA5_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCDMAB5 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCDMAB5_ADDR  ALT_USB_HOST_HCDMAB5_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCCHAR6 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCCHAR6_ADDR  ALT_USB_HOST_HCCHAR6_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCSPLT6 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCSPLT6_ADDR  ALT_USB_HOST_HCSPLT6_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCINT6 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCINT6_ADDR  ALT_USB_HOST_HCINT6_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCINTMSK6 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCINTMSK6_ADDR  ALT_USB_HOST_HCINTMSK6_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCTSIZ6 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCTSIZ6_ADDR  ALT_USB_HOST_HCTSIZ6_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCDMA6 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCDMA6_ADDR  ALT_USB_HOST_HCDMA6_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCDMAB6 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCDMAB6_ADDR  ALT_USB_HOST_HCDMAB6_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCCHAR7 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCCHAR7_ADDR  ALT_USB_HOST_HCCHAR7_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCSPLT7 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCSPLT7_ADDR  ALT_USB_HOST_HCSPLT7_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCINT7 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCINT7_ADDR  ALT_USB_HOST_HCINT7_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCINTMSK7 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCINTMSK7_ADDR  ALT_USB_HOST_HCINTMSK7_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCTSIZ7 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCTSIZ7_ADDR  ALT_USB_HOST_HCTSIZ7_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCDMA7 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCDMA7_ADDR  ALT_USB_HOST_HCDMA7_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCDMAB7 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCDMAB7_ADDR  ALT_USB_HOST_HCDMAB7_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCCHAR8 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCCHAR8_ADDR  ALT_USB_HOST_HCCHAR8_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCSPLT8 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCSPLT8_ADDR  ALT_USB_HOST_HCSPLT8_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCINT8 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCINT8_ADDR  ALT_USB_HOST_HCINT8_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCINTMSK8 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCINTMSK8_ADDR  ALT_USB_HOST_HCINTMSK8_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCTSIZ8 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCTSIZ8_ADDR  ALT_USB_HOST_HCTSIZ8_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCDMA8 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCDMA8_ADDR  ALT_USB_HOST_HCDMA8_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCDMAB8 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCDMAB8_ADDR  ALT_USB_HOST_HCDMAB8_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCCHAR9 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCCHAR9_ADDR  ALT_USB_HOST_HCCHAR9_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCSPLT9 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCSPLT9_ADDR  ALT_USB_HOST_HCSPLT9_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCINT9 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCINT9_ADDR  ALT_USB_HOST_HCINT9_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCINTMSK9 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCINTMSK9_ADDR  ALT_USB_HOST_HCINTMSK9_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCTSIZ9 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCTSIZ9_ADDR  ALT_USB_HOST_HCTSIZ9_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCDMA9 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCDMA9_ADDR  ALT_USB_HOST_HCDMA9_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCDMAB9 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCDMAB9_ADDR  ALT_USB_HOST_HCDMAB9_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCCHAR10 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCCHAR10_ADDR  ALT_USB_HOST_HCCHAR10_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCSPLT10 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCSPLT10_ADDR  ALT_USB_HOST_HCSPLT10_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCINT10 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCINT10_ADDR  ALT_USB_HOST_HCINT10_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCINTMSK10 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCINTMSK10_ADDR  ALT_USB_HOST_HCINTMSK10_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCTSIZ10 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCTSIZ10_ADDR  ALT_USB_HOST_HCTSIZ10_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCDMA10 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCDMA10_ADDR  ALT_USB_HOST_HCDMA10_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCDMAB10 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCDMAB10_ADDR  ALT_USB_HOST_HCDMAB10_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCCHAR11 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCCHAR11_ADDR  ALT_USB_HOST_HCCHAR11_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCSPLT11 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCSPLT11_ADDR  ALT_USB_HOST_HCSPLT11_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCINT11 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCINT11_ADDR  ALT_USB_HOST_HCINT11_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCINTMSK11 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCINTMSK11_ADDR  ALT_USB_HOST_HCINTMSK11_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCTSIZ11 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCTSIZ11_ADDR  ALT_USB_HOST_HCTSIZ11_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCDMA11 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCDMA11_ADDR  ALT_USB_HOST_HCDMA11_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCDMAB11 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCDMAB11_ADDR  ALT_USB_HOST_HCDMAB11_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCCHAR12 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCCHAR12_ADDR  ALT_USB_HOST_HCCHAR12_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCSPLT12 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCSPLT12_ADDR  ALT_USB_HOST_HCSPLT12_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCINT12 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCINT12_ADDR  ALT_USB_HOST_HCINT12_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCINTMSK12 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCINTMSK12_ADDR  ALT_USB_HOST_HCINTMSK12_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCTSIZ12 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCTSIZ12_ADDR  ALT_USB_HOST_HCTSIZ12_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCDMA12 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCDMA12_ADDR  ALT_USB_HOST_HCDMA12_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCDMAB12 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCDMAB12_ADDR  ALT_USB_HOST_HCDMAB12_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCCHAR13 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCCHAR13_ADDR  ALT_USB_HOST_HCCHAR13_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCSPLT13 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCSPLT13_ADDR  ALT_USB_HOST_HCSPLT13_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCINT13 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCINT13_ADDR  ALT_USB_HOST_HCINT13_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCINTMSK13 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCINTMSK13_ADDR  ALT_USB_HOST_HCINTMSK13_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCTSIZ13 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCTSIZ13_ADDR  ALT_USB_HOST_HCTSIZ13_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCDMA13 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCDMA13_ADDR  ALT_USB_HOST_HCDMA13_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCDMAB13 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCDMAB13_ADDR  ALT_USB_HOST_HCDMAB13_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCCHAR14 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCCHAR14_ADDR  ALT_USB_HOST_HCCHAR14_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCSPLT14 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCSPLT14_ADDR  ALT_USB_HOST_HCSPLT14_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCINT14 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCINT14_ADDR  ALT_USB_HOST_HCINT14_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCINTMSK14 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCINTMSK14_ADDR  ALT_USB_HOST_HCINTMSK14_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCTSIZ14 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCTSIZ14_ADDR  ALT_USB_HOST_HCTSIZ14_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCDMA14 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCDMA14_ADDR  ALT_USB_HOST_HCDMA14_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCDMAB14 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCDMAB14_ADDR  ALT_USB_HOST_HCDMAB14_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCCHAR15 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCCHAR15_ADDR  ALT_USB_HOST_HCCHAR15_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCSPLT15 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCSPLT15_ADDR  ALT_USB_HOST_HCSPLT15_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCINT15 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCINT15_ADDR  ALT_USB_HOST_HCINT15_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCINTMSK15 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCINTMSK15_ADDR  ALT_USB_HOST_HCINTMSK15_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCTSIZ15 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCTSIZ15_ADDR  ALT_USB_HOST_HCTSIZ15_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCDMA15 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCDMA15_ADDR  ALT_USB_HOST_HCDMA15_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The address of the ALT_USB_HOST_HCDMAB15 register for the ALT_USB1_HOSTGRP instance. */
#define ALT_USB1_HOST_HCDMAB15_ADDR  ALT_USB_HOST_HCDMAB15_ADDR(ALT_USB1_HOSTGRP_ADDR)
/* The base address byte offset for the start of the ALT_USB1_HOSTGRP component. */
#define ALT_USB1_HOSTGRP_OFST        0x400
/* The start address of the ALT_USB1_HOSTGRP component. */
#define ALT_USB1_HOSTGRP_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_USB1_ADDR) + ALT_USB1_HOSTGRP_OFST))
/* The lower bound address range of the ALT_USB1_HOSTGRP component. */
#define ALT_USB1_HOSTGRP_LB_ADDR     ALT_USB1_HOSTGRP_ADDR
/* The upper bound address range of the ALT_USB1_HOSTGRP component. */
#define ALT_USB1_HOSTGRP_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_USB1_HOSTGRP_ADDR) + 0x2fc) - 1))


/*
 * Register Group Instance : devgrp
 * 
 * Instance devgrp of register group ALT_USB_DEV.
 * 
 * 
 */
/* The address of the ALT_USB_DEV_DCFG register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DCFG_ADDR  ALT_USB_DEV_DCFG_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DCTL register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DCTL_ADDR  ALT_USB_DEV_DCTL_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DSTS register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DSTS_ADDR  ALT_USB_DEV_DSTS_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPMSK register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPMSK_ADDR  ALT_USB_DEV_DIEPMSK_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPMSK register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPMSK_ADDR  ALT_USB_DEV_DOEPMSK_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DAINT register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DAINT_ADDR  ALT_USB_DEV_DAINT_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DAINTMSK register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DAINTMSK_ADDR  ALT_USB_DEV_DAINTMSK_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DVBUSDIS register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DVBUSDIS_ADDR  ALT_USB_DEV_DVBUSDIS_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DVBUSPULSE register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DVBUSPULSE_ADDR  ALT_USB_DEV_DVBUSPULSE_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DTHRCTL register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DTHRCTL_ADDR  ALT_USB_DEV_DTHRCTL_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPEMPMSK register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPEMPMSK_ADDR  ALT_USB_DEV_DIEPEMPMSK_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPCTL0 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPCTL0_ADDR  ALT_USB_DEV_DIEPCTL0_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPINT0 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPINT0_ADDR  ALT_USB_DEV_DIEPINT0_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPTSIZ0 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPTSIZ0_ADDR  ALT_USB_DEV_DIEPTSIZ0_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPDMA0 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPDMA0_ADDR  ALT_USB_DEV_DIEPDMA0_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DTXFSTS0 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DTXFSTS0_ADDR  ALT_USB_DEV_DTXFSTS0_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPDMAB0 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPDMAB0_ADDR  ALT_USB_DEV_DIEPDMAB0_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPCTL1 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPCTL1_ADDR  ALT_USB_DEV_DIEPCTL1_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPINT1 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPINT1_ADDR  ALT_USB_DEV_DIEPINT1_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPTSIZ1 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPTSIZ1_ADDR  ALT_USB_DEV_DIEPTSIZ1_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPDMA1 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPDMA1_ADDR  ALT_USB_DEV_DIEPDMA1_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DTXFSTS1 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DTXFSTS1_ADDR  ALT_USB_DEV_DTXFSTS1_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPDMAB1 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPDMAB1_ADDR  ALT_USB_DEV_DIEPDMAB1_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPCTL2 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPCTL2_ADDR  ALT_USB_DEV_DIEPCTL2_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPINT2 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPINT2_ADDR  ALT_USB_DEV_DIEPINT2_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPTSIZ2 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPTSIZ2_ADDR  ALT_USB_DEV_DIEPTSIZ2_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPDMA2 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPDMA2_ADDR  ALT_USB_DEV_DIEPDMA2_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DTXFSTS2 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DTXFSTS2_ADDR  ALT_USB_DEV_DTXFSTS2_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPDMAB2 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPDMAB2_ADDR  ALT_USB_DEV_DIEPDMAB2_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPCTL3 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPCTL3_ADDR  ALT_USB_DEV_DIEPCTL3_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPINT3 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPINT3_ADDR  ALT_USB_DEV_DIEPINT3_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPTSIZ3 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPTSIZ3_ADDR  ALT_USB_DEV_DIEPTSIZ3_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPDMA3 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPDMA3_ADDR  ALT_USB_DEV_DIEPDMA3_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DTXFSTS3 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DTXFSTS3_ADDR  ALT_USB_DEV_DTXFSTS3_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPDMAB3 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPDMAB3_ADDR  ALT_USB_DEV_DIEPDMAB3_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPCTL4 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPCTL4_ADDR  ALT_USB_DEV_DIEPCTL4_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPINT4 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPINT4_ADDR  ALT_USB_DEV_DIEPINT4_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPTSIZ4 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPTSIZ4_ADDR  ALT_USB_DEV_DIEPTSIZ4_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPDMA4 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPDMA4_ADDR  ALT_USB_DEV_DIEPDMA4_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DTXFSTS4 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DTXFSTS4_ADDR  ALT_USB_DEV_DTXFSTS4_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPDMAB4 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPDMAB4_ADDR  ALT_USB_DEV_DIEPDMAB4_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPCTL5 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPCTL5_ADDR  ALT_USB_DEV_DIEPCTL5_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPINT5 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPINT5_ADDR  ALT_USB_DEV_DIEPINT5_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPTSIZ5 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPTSIZ5_ADDR  ALT_USB_DEV_DIEPTSIZ5_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPDMA5 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPDMA5_ADDR  ALT_USB_DEV_DIEPDMA5_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DTXFSTS5 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DTXFSTS5_ADDR  ALT_USB_DEV_DTXFSTS5_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPDMAB5 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPDMAB5_ADDR  ALT_USB_DEV_DIEPDMAB5_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPCTL6 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPCTL6_ADDR  ALT_USB_DEV_DIEPCTL6_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPINT6 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPINT6_ADDR  ALT_USB_DEV_DIEPINT6_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPTSIZ6 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPTSIZ6_ADDR  ALT_USB_DEV_DIEPTSIZ6_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPDMA6 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPDMA6_ADDR  ALT_USB_DEV_DIEPDMA6_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DTXFSTS6 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DTXFSTS6_ADDR  ALT_USB_DEV_DTXFSTS6_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPDMAB6 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPDMAB6_ADDR  ALT_USB_DEV_DIEPDMAB6_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPCTL7 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPCTL7_ADDR  ALT_USB_DEV_DIEPCTL7_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPINT7 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPINT7_ADDR  ALT_USB_DEV_DIEPINT7_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPTSIZ7 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPTSIZ7_ADDR  ALT_USB_DEV_DIEPTSIZ7_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPDMA7 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPDMA7_ADDR  ALT_USB_DEV_DIEPDMA7_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DTXFSTS7 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DTXFSTS7_ADDR  ALT_USB_DEV_DTXFSTS7_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPDMAB7 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPDMAB7_ADDR  ALT_USB_DEV_DIEPDMAB7_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPCTL8 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPCTL8_ADDR  ALT_USB_DEV_DIEPCTL8_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPINT8 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPINT8_ADDR  ALT_USB_DEV_DIEPINT8_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPTSIZ8 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPTSIZ8_ADDR  ALT_USB_DEV_DIEPTSIZ8_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPDMA8 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPDMA8_ADDR  ALT_USB_DEV_DIEPDMA8_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DTXFSTS8 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DTXFSTS8_ADDR  ALT_USB_DEV_DTXFSTS8_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPDMAB8 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPDMAB8_ADDR  ALT_USB_DEV_DIEPDMAB8_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPCTL9 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPCTL9_ADDR  ALT_USB_DEV_DIEPCTL9_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPINT9 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPINT9_ADDR  ALT_USB_DEV_DIEPINT9_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPTSIZ9 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPTSIZ9_ADDR  ALT_USB_DEV_DIEPTSIZ9_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPDMA9 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPDMA9_ADDR  ALT_USB_DEV_DIEPDMA9_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DTXFSTS9 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DTXFSTS9_ADDR  ALT_USB_DEV_DTXFSTS9_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPDMAB9 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPDMAB9_ADDR  ALT_USB_DEV_DIEPDMAB9_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPCTL10 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPCTL10_ADDR  ALT_USB_DEV_DIEPCTL10_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPINT10 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPINT10_ADDR  ALT_USB_DEV_DIEPINT10_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPTSIZ10 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPTSIZ10_ADDR  ALT_USB_DEV_DIEPTSIZ10_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPDMA10 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPDMA10_ADDR  ALT_USB_DEV_DIEPDMA10_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DTXFSTS10 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DTXFSTS10_ADDR  ALT_USB_DEV_DTXFSTS10_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPDMAB10 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPDMAB10_ADDR  ALT_USB_DEV_DIEPDMAB10_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPCTL11 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPCTL11_ADDR  ALT_USB_DEV_DIEPCTL11_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPINT11 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPINT11_ADDR  ALT_USB_DEV_DIEPINT11_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPTSIZ11 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPTSIZ11_ADDR  ALT_USB_DEV_DIEPTSIZ11_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPDMA11 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPDMA11_ADDR  ALT_USB_DEV_DIEPDMA11_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DTXFSTS11 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DTXFSTS11_ADDR  ALT_USB_DEV_DTXFSTS11_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPDMAB11 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPDMAB11_ADDR  ALT_USB_DEV_DIEPDMAB11_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPCTL12 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPCTL12_ADDR  ALT_USB_DEV_DIEPCTL12_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPINT12 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPINT12_ADDR  ALT_USB_DEV_DIEPINT12_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPTSIZ12 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPTSIZ12_ADDR  ALT_USB_DEV_DIEPTSIZ12_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPDMA12 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPDMA12_ADDR  ALT_USB_DEV_DIEPDMA12_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DTXFSTS12 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DTXFSTS12_ADDR  ALT_USB_DEV_DTXFSTS12_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPDMAB12 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPDMAB12_ADDR  ALT_USB_DEV_DIEPDMAB12_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPCTL13 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPCTL13_ADDR  ALT_USB_DEV_DIEPCTL13_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPINT13 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPINT13_ADDR  ALT_USB_DEV_DIEPINT13_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPTSIZ13 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPTSIZ13_ADDR  ALT_USB_DEV_DIEPTSIZ13_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPDMA13 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPDMA13_ADDR  ALT_USB_DEV_DIEPDMA13_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DTXFSTS13 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DTXFSTS13_ADDR  ALT_USB_DEV_DTXFSTS13_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPDMAB13 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPDMAB13_ADDR  ALT_USB_DEV_DIEPDMAB13_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPCTL14 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPCTL14_ADDR  ALT_USB_DEV_DIEPCTL14_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPINT14 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPINT14_ADDR  ALT_USB_DEV_DIEPINT14_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPTSIZ14 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPTSIZ14_ADDR  ALT_USB_DEV_DIEPTSIZ14_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPDMA14 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPDMA14_ADDR  ALT_USB_DEV_DIEPDMA14_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DTXFSTS14 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DTXFSTS14_ADDR  ALT_USB_DEV_DTXFSTS14_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPDMAB14 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPDMAB14_ADDR  ALT_USB_DEV_DIEPDMAB14_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPCTL15 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPCTL15_ADDR  ALT_USB_DEV_DIEPCTL15_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPINT15 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPINT15_ADDR  ALT_USB_DEV_DIEPINT15_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPTSIZ15 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPTSIZ15_ADDR  ALT_USB_DEV_DIEPTSIZ15_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPDMA15 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPDMA15_ADDR  ALT_USB_DEV_DIEPDMA15_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DTXFSTS15 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DTXFSTS15_ADDR  ALT_USB_DEV_DTXFSTS15_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DIEPDMAB15 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DIEPDMAB15_ADDR  ALT_USB_DEV_DIEPDMAB15_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPCTL0 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPCTL0_ADDR  ALT_USB_DEV_DOEPCTL0_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPINT0 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPINT0_ADDR  ALT_USB_DEV_DOEPINT0_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPTSIZ0 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPTSIZ0_ADDR  ALT_USB_DEV_DOEPTSIZ0_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPDMA0 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPDMA0_ADDR  ALT_USB_DEV_DOEPDMA0_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPDMAB0 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPDMAB0_ADDR  ALT_USB_DEV_DOEPDMAB0_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPCTL1 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPCTL1_ADDR  ALT_USB_DEV_DOEPCTL1_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPINT1 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPINT1_ADDR  ALT_USB_DEV_DOEPINT1_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPTSIZ1 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPTSIZ1_ADDR  ALT_USB_DEV_DOEPTSIZ1_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPDMA1 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPDMA1_ADDR  ALT_USB_DEV_DOEPDMA1_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPDMAB1 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPDMAB1_ADDR  ALT_USB_DEV_DOEPDMAB1_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPCTL2 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPCTL2_ADDR  ALT_USB_DEV_DOEPCTL2_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPINT2 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPINT2_ADDR  ALT_USB_DEV_DOEPINT2_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPTSIZ2 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPTSIZ2_ADDR  ALT_USB_DEV_DOEPTSIZ2_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPDMA2 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPDMA2_ADDR  ALT_USB_DEV_DOEPDMA2_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPDMAB2 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPDMAB2_ADDR  ALT_USB_DEV_DOEPDMAB2_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPCTL3 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPCTL3_ADDR  ALT_USB_DEV_DOEPCTL3_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPINT3 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPINT3_ADDR  ALT_USB_DEV_DOEPINT3_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPTSIZ3 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPTSIZ3_ADDR  ALT_USB_DEV_DOEPTSIZ3_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPDMA3 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPDMA3_ADDR  ALT_USB_DEV_DOEPDMA3_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPDMAB3 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPDMAB3_ADDR  ALT_USB_DEV_DOEPDMAB3_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPCTL4 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPCTL4_ADDR  ALT_USB_DEV_DOEPCTL4_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPINT4 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPINT4_ADDR  ALT_USB_DEV_DOEPINT4_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPTSIZ4 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPTSIZ4_ADDR  ALT_USB_DEV_DOEPTSIZ4_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPDMA4 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPDMA4_ADDR  ALT_USB_DEV_DOEPDMA4_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPDMAB4 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPDMAB4_ADDR  ALT_USB_DEV_DOEPDMAB4_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPCTL5 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPCTL5_ADDR  ALT_USB_DEV_DOEPCTL5_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPINT5 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPINT5_ADDR  ALT_USB_DEV_DOEPINT5_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPTSIZ5 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPTSIZ5_ADDR  ALT_USB_DEV_DOEPTSIZ5_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPDMA5 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPDMA5_ADDR  ALT_USB_DEV_DOEPDMA5_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPDMAB5 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPDMAB5_ADDR  ALT_USB_DEV_DOEPDMAB5_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPCTL6 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPCTL6_ADDR  ALT_USB_DEV_DOEPCTL6_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPINT6 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPINT6_ADDR  ALT_USB_DEV_DOEPINT6_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPTSIZ6 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPTSIZ6_ADDR  ALT_USB_DEV_DOEPTSIZ6_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPDMA6 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPDMA6_ADDR  ALT_USB_DEV_DOEPDMA6_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPDMAB6 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPDMAB6_ADDR  ALT_USB_DEV_DOEPDMAB6_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPCTL7 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPCTL7_ADDR  ALT_USB_DEV_DOEPCTL7_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPINT7 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPINT7_ADDR  ALT_USB_DEV_DOEPINT7_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPTSIZ7 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPTSIZ7_ADDR  ALT_USB_DEV_DOEPTSIZ7_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPDMA7 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPDMA7_ADDR  ALT_USB_DEV_DOEPDMA7_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPDMAB7 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPDMAB7_ADDR  ALT_USB_DEV_DOEPDMAB7_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPCTL8 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPCTL8_ADDR  ALT_USB_DEV_DOEPCTL8_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPINT8 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPINT8_ADDR  ALT_USB_DEV_DOEPINT8_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPTSIZ8 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPTSIZ8_ADDR  ALT_USB_DEV_DOEPTSIZ8_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPDMA8 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPDMA8_ADDR  ALT_USB_DEV_DOEPDMA8_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPDMAB8 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPDMAB8_ADDR  ALT_USB_DEV_DOEPDMAB8_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPCTL9 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPCTL9_ADDR  ALT_USB_DEV_DOEPCTL9_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPINT9 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPINT9_ADDR  ALT_USB_DEV_DOEPINT9_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPTSIZ9 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPTSIZ9_ADDR  ALT_USB_DEV_DOEPTSIZ9_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPDMA9 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPDMA9_ADDR  ALT_USB_DEV_DOEPDMA9_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPDMAB9 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPDMAB9_ADDR  ALT_USB_DEV_DOEPDMAB9_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPCTL10 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPCTL10_ADDR  ALT_USB_DEV_DOEPCTL10_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPINT10 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPINT10_ADDR  ALT_USB_DEV_DOEPINT10_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPTSIZ10 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPTSIZ10_ADDR  ALT_USB_DEV_DOEPTSIZ10_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPDMA10 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPDMA10_ADDR  ALT_USB_DEV_DOEPDMA10_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPDMAB10 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPDMAB10_ADDR  ALT_USB_DEV_DOEPDMAB10_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPCTL11 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPCTL11_ADDR  ALT_USB_DEV_DOEPCTL11_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPINT11 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPINT11_ADDR  ALT_USB_DEV_DOEPINT11_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPTSIZ11 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPTSIZ11_ADDR  ALT_USB_DEV_DOEPTSIZ11_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPDMA11 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPDMA11_ADDR  ALT_USB_DEV_DOEPDMA11_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPDMAB11 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPDMAB11_ADDR  ALT_USB_DEV_DOEPDMAB11_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPCTL12 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPCTL12_ADDR  ALT_USB_DEV_DOEPCTL12_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPINT12 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPINT12_ADDR  ALT_USB_DEV_DOEPINT12_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPTSIZ12 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPTSIZ12_ADDR  ALT_USB_DEV_DOEPTSIZ12_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPDMA12 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPDMA12_ADDR  ALT_USB_DEV_DOEPDMA12_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPDMAB12 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPDMAB12_ADDR  ALT_USB_DEV_DOEPDMAB12_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPCTL13 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPCTL13_ADDR  ALT_USB_DEV_DOEPCTL13_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPINT13 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPINT13_ADDR  ALT_USB_DEV_DOEPINT13_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPTSIZ13 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPTSIZ13_ADDR  ALT_USB_DEV_DOEPTSIZ13_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPDMA13 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPDMA13_ADDR  ALT_USB_DEV_DOEPDMA13_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPDMAB13 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPDMAB13_ADDR  ALT_USB_DEV_DOEPDMAB13_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPCTL14 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPCTL14_ADDR  ALT_USB_DEV_DOEPCTL14_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPINT14 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPINT14_ADDR  ALT_USB_DEV_DOEPINT14_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPTSIZ14 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPTSIZ14_ADDR  ALT_USB_DEV_DOEPTSIZ14_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPDMA14 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPDMA14_ADDR  ALT_USB_DEV_DOEPDMA14_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPDMAB14 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPDMAB14_ADDR  ALT_USB_DEV_DOEPDMAB14_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPCTL15 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPCTL15_ADDR  ALT_USB_DEV_DOEPCTL15_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPINT15 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPINT15_ADDR  ALT_USB_DEV_DOEPINT15_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPTSIZ15 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPTSIZ15_ADDR  ALT_USB_DEV_DOEPTSIZ15_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPDMA15 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPDMA15_ADDR  ALT_USB_DEV_DOEPDMA15_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The address of the ALT_USB_DEV_DOEPDMAB15 register for the ALT_USB1_DEVGRP instance. */
#define ALT_USB1_DEV_DOEPDMAB15_ADDR  ALT_USB_DEV_DOEPDMAB15_ADDR(ALT_USB1_DEVGRP_ADDR)
/* The base address byte offset for the start of the ALT_USB1_DEVGRP component. */
#define ALT_USB1_DEVGRP_OFST        0x800
/* The start address of the ALT_USB1_DEVGRP component. */
#define ALT_USB1_DEVGRP_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_USB1_ADDR) + ALT_USB1_DEVGRP_OFST))
/* The lower bound address range of the ALT_USB1_DEVGRP component. */
#define ALT_USB1_DEVGRP_LB_ADDR     ALT_USB1_DEVGRP_ADDR
/* The upper bound address range of the ALT_USB1_DEVGRP component. */
#define ALT_USB1_DEVGRP_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_USB1_DEVGRP_ADDR) + 0x500) - 1))


/*
 * Register Group Instance : pwrclkgrp
 * 
 * Instance pwrclkgrp of register group ALT_USB_PWRCLK.
 * 
 * 
 */
/* The address of the ALT_USB_PWRCLK_PCGCCTL register for the ALT_USB1_PWRCLKGRP instance. */
#define ALT_USB1_PWRCLK_PCGCCTL_ADDR  ALT_USB_PWRCLK_PCGCCTL_ADDR(ALT_USB1_PWRCLKGRP_ADDR)
/* The base address byte offset for the start of the ALT_USB1_PWRCLKGRP component. */
#define ALT_USB1_PWRCLKGRP_OFST        0xe00
/* The start address of the ALT_USB1_PWRCLKGRP component. */
#define ALT_USB1_PWRCLKGRP_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_USB1_ADDR) + ALT_USB1_PWRCLKGRP_OFST))
/* The lower bound address range of the ALT_USB1_PWRCLKGRP component. */
#define ALT_USB1_PWRCLKGRP_LB_ADDR     ALT_USB1_PWRCLKGRP_ADDR
/* The upper bound address range of the ALT_USB1_PWRCLKGRP component. */
#define ALT_USB1_PWRCLKGRP_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_USB1_PWRCLKGRP_ADDR) + 0x4) - 1))


/* The base address byte offset for the start of the ALT_USB1 component. */
#define ALT_USB1_OFST        0xffb40000
/* The start address of the ALT_USB1 component. */
#define ALT_USB1_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_HPS_ADDR) + ALT_USB1_OFST))
/* The lower bound address range of the ALT_USB1 component. */
#define ALT_USB1_LB_ADDR     ALT_USB1_ADDR
/* The upper bound address range of the ALT_USB1 component. */
#define ALT_USB1_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_USB1_ADDR) + 0x40000) - 1))


/*
 * Component Instance : nandregs
 * 
 * Instance nandregs of component ALT_NAND.
 * 
 * 
 */
/*
 * Register Group Instance : config
 * 
 * Instance config of register group ALT_NAND_CFG.
 * 
 * 
 */
/* The address of the ALT_NAND_CFG_DEVICE_RST register for the ALT_NAND_CFG instance. */
#define ALT_NAND_CFG_DEVICE_RST_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_CFG_ADDR) + ALT_NAND_CFG_DEVICE_RST_OFST))
/* The address of the ALT_NAND_CFG_TFR_SPARE_REG register for the ALT_NAND_CFG instance. */
#define ALT_NAND_CFG_TFR_SPARE_REG_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_CFG_ADDR) + ALT_NAND_CFG_TFR_SPARE_REG_OFST))
/* The address of the ALT_NAND_CFG_LD_WAIT_CNT register for the ALT_NAND_CFG instance. */
#define ALT_NAND_CFG_LD_WAIT_CNT_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_CFG_ADDR) + ALT_NAND_CFG_LD_WAIT_CNT_OFST))
/* The address of the ALT_NAND_CFG_PROGRAM_WAIT_CNT register for the ALT_NAND_CFG instance. */
#define ALT_NAND_CFG_PROGRAM_WAIT_CNT_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_CFG_ADDR) + ALT_NAND_CFG_PROGRAM_WAIT_CNT_OFST))
/* The address of the ALT_NAND_CFG_ERASE_WAIT_CNT register for the ALT_NAND_CFG instance. */
#define ALT_NAND_CFG_ERASE_WAIT_CNT_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_CFG_ADDR) + ALT_NAND_CFG_ERASE_WAIT_CNT_OFST))
/* The address of the ALT_NAND_CFG_INT_MON_CYCCNT register for the ALT_NAND_CFG instance. */
#define ALT_NAND_CFG_INT_MON_CYCCNT_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_CFG_ADDR) + ALT_NAND_CFG_INT_MON_CYCCNT_OFST))
/* The address of the ALT_NAND_CFG_RB_PIN_END register for the ALT_NAND_CFG instance. */
#define ALT_NAND_CFG_RB_PIN_END_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_CFG_ADDR) + ALT_NAND_CFG_RB_PIN_END_OFST))
/* The address of the ALT_NAND_CFG_MULTIPLANE_OP register for the ALT_NAND_CFG instance. */
#define ALT_NAND_CFG_MULTIPLANE_OP_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_CFG_ADDR) + ALT_NAND_CFG_MULTIPLANE_OP_OFST))
/* The address of the ALT_NAND_CFG_MULTIPLANE_RD_EN register for the ALT_NAND_CFG instance. */
#define ALT_NAND_CFG_MULTIPLANE_RD_EN_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_CFG_ADDR) + ALT_NAND_CFG_MULTIPLANE_RD_EN_OFST))
/* The address of the ALT_NAND_CFG_COPYBACK_DIS register for the ALT_NAND_CFG instance. */
#define ALT_NAND_CFG_COPYBACK_DIS_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_CFG_ADDR) + ALT_NAND_CFG_COPYBACK_DIS_OFST))
/* The address of the ALT_NAND_CFG_CACHE_WR_EN register for the ALT_NAND_CFG instance. */
#define ALT_NAND_CFG_CACHE_WR_EN_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_CFG_ADDR) + ALT_NAND_CFG_CACHE_WR_EN_OFST))
/* The address of the ALT_NAND_CFG_CACHE_RD_EN register for the ALT_NAND_CFG instance. */
#define ALT_NAND_CFG_CACHE_RD_EN_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_CFG_ADDR) + ALT_NAND_CFG_CACHE_RD_EN_OFST))
/* The address of the ALT_NAND_CFG_PREFETCH_MOD register for the ALT_NAND_CFG instance. */
#define ALT_NAND_CFG_PREFETCH_MOD_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_CFG_ADDR) + ALT_NAND_CFG_PREFETCH_MOD_OFST))
/* The address of the ALT_NAND_CFG_CHIP_EN_DONT_CARE register for the ALT_NAND_CFG instance. */
#define ALT_NAND_CFG_CHIP_EN_DONT_CARE_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_CFG_ADDR) + ALT_NAND_CFG_CHIP_EN_DONT_CARE_OFST))
/* The address of the ALT_NAND_CFG_ECC_EN register for the ALT_NAND_CFG instance. */
#define ALT_NAND_CFG_ECC_EN_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_CFG_ADDR) + ALT_NAND_CFG_ECC_EN_OFST))
/* The address of the ALT_NAND_CFG_GLOB_INT_EN register for the ALT_NAND_CFG instance. */
#define ALT_NAND_CFG_GLOB_INT_EN_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_CFG_ADDR) + ALT_NAND_CFG_GLOB_INT_EN_OFST))
/* The address of the ALT_NAND_CFG_TWHR2_AND_WE_2_RE register for the ALT_NAND_CFG instance. */
#define ALT_NAND_CFG_TWHR2_AND_WE_2_RE_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_CFG_ADDR) + ALT_NAND_CFG_TWHR2_AND_WE_2_RE_OFST))
/* The address of the ALT_NAND_CFG_TCWAW_AND_ADDR_2_DATA register for the ALT_NAND_CFG instance. */
#define ALT_NAND_CFG_TCWAW_AND_ADDR_2_DATA_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_CFG_ADDR) + ALT_NAND_CFG_TCWAW_AND_ADDR_2_DATA_OFST))
/* The address of the ALT_NAND_CFG_RE_2_WE register for the ALT_NAND_CFG instance. */
#define ALT_NAND_CFG_RE_2_WE_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_CFG_ADDR) + ALT_NAND_CFG_RE_2_WE_OFST))
/* The address of the ALT_NAND_CFG_ACC_CLKS register for the ALT_NAND_CFG instance. */
#define ALT_NAND_CFG_ACC_CLKS_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_CFG_ADDR) + ALT_NAND_CFG_ACC_CLKS_OFST))
/* The address of the ALT_NAND_CFG_NUMBER_OF_PLANES register for the ALT_NAND_CFG instance. */
#define ALT_NAND_CFG_NUMBER_OF_PLANES_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_CFG_ADDR) + ALT_NAND_CFG_NUMBER_OF_PLANES_OFST))
/* The address of the ALT_NAND_CFG_PAGES_PER_BLOCK register for the ALT_NAND_CFG instance. */
#define ALT_NAND_CFG_PAGES_PER_BLOCK_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_CFG_ADDR) + ALT_NAND_CFG_PAGES_PER_BLOCK_OFST))
/* The address of the ALT_NAND_CFG_DEVICE_WIDTH register for the ALT_NAND_CFG instance. */
#define ALT_NAND_CFG_DEVICE_WIDTH_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_CFG_ADDR) + ALT_NAND_CFG_DEVICE_WIDTH_OFST))
/* The address of the ALT_NAND_CFG_DEVICE_MAIN_AREA_SIZE register for the ALT_NAND_CFG instance. */
#define ALT_NAND_CFG_DEVICE_MAIN_AREA_SIZE_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_CFG_ADDR) + ALT_NAND_CFG_DEVICE_MAIN_AREA_SIZE_OFST))
/* The address of the ALT_NAND_CFG_DEVICE_SPARE_AREA_SIZE register for the ALT_NAND_CFG instance. */
#define ALT_NAND_CFG_DEVICE_SPARE_AREA_SIZE_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_CFG_ADDR) + ALT_NAND_CFG_DEVICE_SPARE_AREA_SIZE_OFST))
/* The address of the ALT_NAND_CFG_TWO_ROW_ADDR_CYCLES register for the ALT_NAND_CFG instance. */
#define ALT_NAND_CFG_TWO_ROW_ADDR_CYCLES_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_CFG_ADDR) + ALT_NAND_CFG_TWO_ROW_ADDR_CYCLES_OFST))
/* The address of the ALT_NAND_CFG_MULTIPLANE_ADDR_RESTRICT register for the ALT_NAND_CFG instance. */
#define ALT_NAND_CFG_MULTIPLANE_ADDR_RESTRICT_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_CFG_ADDR) + ALT_NAND_CFG_MULTIPLANE_ADDR_RESTRICT_OFST))
/* The address of the ALT_NAND_CFG_ECC_CORRECTION register for the ALT_NAND_CFG instance. */
#define ALT_NAND_CFG_ECC_CORRECTION_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_CFG_ADDR) + ALT_NAND_CFG_ECC_CORRECTION_OFST))
/* The address of the ALT_NAND_CFG_RD_MOD register for the ALT_NAND_CFG instance. */
#define ALT_NAND_CFG_RD_MOD_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_CFG_ADDR) + ALT_NAND_CFG_RD_MOD_OFST))
/* The address of the ALT_NAND_CFG_WR_MOD register for the ALT_NAND_CFG instance. */
#define ALT_NAND_CFG_WR_MOD_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_CFG_ADDR) + ALT_NAND_CFG_WR_MOD_OFST))
/* The address of the ALT_NAND_CFG_COPYBACK_MOD register for the ALT_NAND_CFG instance. */
#define ALT_NAND_CFG_COPYBACK_MOD_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_CFG_ADDR) + ALT_NAND_CFG_COPYBACK_MOD_OFST))
/* The address of the ALT_NAND_CFG_RDWR_EN_LO_CNT register for the ALT_NAND_CFG instance. */
#define ALT_NAND_CFG_RDWR_EN_LO_CNT_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_CFG_ADDR) + ALT_NAND_CFG_RDWR_EN_LO_CNT_OFST))
/* The address of the ALT_NAND_CFG_RDWR_EN_HI_CNT register for the ALT_NAND_CFG instance. */
#define ALT_NAND_CFG_RDWR_EN_HI_CNT_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_CFG_ADDR) + ALT_NAND_CFG_RDWR_EN_HI_CNT_OFST))
/* The address of the ALT_NAND_CFG_MAX_RD_DELAY register for the ALT_NAND_CFG instance. */
#define ALT_NAND_CFG_MAX_RD_DELAY_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_CFG_ADDR) + ALT_NAND_CFG_MAX_RD_DELAY_OFST))
/* The address of the ALT_NAND_CFG_CS_SETUP_CNT register for the ALT_NAND_CFG instance. */
#define ALT_NAND_CFG_CS_SETUP_CNT_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_CFG_ADDR) + ALT_NAND_CFG_CS_SETUP_CNT_OFST))
/* The address of the ALT_NAND_CFG_SPARE_AREA_SKIP_BYTES register for the ALT_NAND_CFG instance. */
#define ALT_NAND_CFG_SPARE_AREA_SKIP_BYTES_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_CFG_ADDR) + ALT_NAND_CFG_SPARE_AREA_SKIP_BYTES_OFST))
/* The address of the ALT_NAND_CFG_SPARE_AREA_MARKER register for the ALT_NAND_CFG instance. */
#define ALT_NAND_CFG_SPARE_AREA_MARKER_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_CFG_ADDR) + ALT_NAND_CFG_SPARE_AREA_MARKER_OFST))
/* The address of the ALT_NAND_CFG_DEVICES_CONNECTED register for the ALT_NAND_CFG instance. */
#define ALT_NAND_CFG_DEVICES_CONNECTED_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_CFG_ADDR) + ALT_NAND_CFG_DEVICES_CONNECTED_OFST))
/* The address of the ALT_NAND_CFG_DIE_MSK register for the ALT_NAND_CFG instance. */
#define ALT_NAND_CFG_DIE_MSK_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_CFG_ADDR) + ALT_NAND_CFG_DIE_MSK_OFST))
/* The address of the ALT_NAND_CFG_FIRST_BLOCK_OF_NEXT_PLANE register for the ALT_NAND_CFG instance. */
#define ALT_NAND_CFG_FIRST_BLOCK_OF_NEXT_PLANE_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_CFG_ADDR) + ALT_NAND_CFG_FIRST_BLOCK_OF_NEXT_PLANE_OFST))
/* The address of the ALT_NAND_CFG_WR_PROTECT register for the ALT_NAND_CFG instance. */
#define ALT_NAND_CFG_WR_PROTECT_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_CFG_ADDR) + ALT_NAND_CFG_WR_PROTECT_OFST))
/* The address of the ALT_NAND_CFG_RE_2_RE register for the ALT_NAND_CFG instance. */
#define ALT_NAND_CFG_RE_2_RE_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_CFG_ADDR) + ALT_NAND_CFG_RE_2_RE_OFST))
/* The address of the ALT_NAND_CFG_POR_RST_COUNT register for the ALT_NAND_CFG instance. */
#define ALT_NAND_CFG_POR_RST_COUNT_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_CFG_ADDR) + ALT_NAND_CFG_POR_RST_COUNT_OFST))
/* The address of the ALT_NAND_CFG_WD_RST_COUNT register for the ALT_NAND_CFG instance. */
#define ALT_NAND_CFG_WD_RST_COUNT_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_CFG_ADDR) + ALT_NAND_CFG_WD_RST_COUNT_OFST))
/* The base address byte offset for the start of the ALT_NAND_CFG component. */
#define ALT_NAND_CFG_OFST        0x0
/* The start address of the ALT_NAND_CFG component. */
#define ALT_NAND_CFG_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_ADDR) + ALT_NAND_CFG_OFST))
/* The lower bound address range of the ALT_NAND_CFG component. */
#define ALT_NAND_CFG_LB_ADDR     ALT_NAND_CFG_ADDR
/* The upper bound address range of the ALT_NAND_CFG component. */
#define ALT_NAND_CFG_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_NAND_CFG_ADDR) + 0x2b4) - 1))


/*
 * Register Group Instance : param
 * 
 * Instance param of register group ALT_NAND_PARAM.
 * 
 * 
 */
/* The address of the ALT_NAND_PARAM_MANUFACTURER_ID register for the ALT_NAND_PARAM instance. */
#define ALT_NAND_PARAM_MANUFACTURER_ID_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_PARAM_ADDR) + ALT_NAND_PARAM_MANUFACTURER_ID_OFST))
/* The address of the ALT_NAND_PARAM_DEVICE_ID register for the ALT_NAND_PARAM instance. */
#define ALT_NAND_PARAM_DEVICE_ID_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_PARAM_ADDR) + ALT_NAND_PARAM_DEVICE_ID_OFST))
/* The address of the ALT_NAND_PARAM_DEVICE_PARAM_0 register for the ALT_NAND_PARAM instance. */
#define ALT_NAND_PARAM_DEVICE_PARAM_0_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_PARAM_ADDR) + ALT_NAND_PARAM_DEVICE_PARAM_0_OFST))
/* The address of the ALT_NAND_PARAM_DEVICE_PARAM_1 register for the ALT_NAND_PARAM instance. */
#define ALT_NAND_PARAM_DEVICE_PARAM_1_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_PARAM_ADDR) + ALT_NAND_PARAM_DEVICE_PARAM_1_OFST))
/* The address of the ALT_NAND_PARAM_DEVICE_PARAM_2 register for the ALT_NAND_PARAM instance. */
#define ALT_NAND_PARAM_DEVICE_PARAM_2_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_PARAM_ADDR) + ALT_NAND_PARAM_DEVICE_PARAM_2_OFST))
/* The address of the ALT_NAND_PARAM_LOGICAL_PAGE_DATA_SIZE register for the ALT_NAND_PARAM instance. */
#define ALT_NAND_PARAM_LOGICAL_PAGE_DATA_SIZE_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_PARAM_ADDR) + ALT_NAND_PARAM_LOGICAL_PAGE_DATA_SIZE_OFST))
/* The address of the ALT_NAND_PARAM_LOGICAL_PAGE_SPARE_SIZE register for the ALT_NAND_PARAM instance. */
#define ALT_NAND_PARAM_LOGICAL_PAGE_SPARE_SIZE_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_PARAM_ADDR) + ALT_NAND_PARAM_LOGICAL_PAGE_SPARE_SIZE_OFST))
/* The address of the ALT_NAND_PARAM_REVISION register for the ALT_NAND_PARAM instance. */
#define ALT_NAND_PARAM_REVISION_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_PARAM_ADDR) + ALT_NAND_PARAM_REVISION_OFST))
/* The address of the ALT_NAND_PARAM_ONFI_DEV_FEATURES register for the ALT_NAND_PARAM instance. */
#define ALT_NAND_PARAM_ONFI_DEV_FEATURES_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_PARAM_ADDR) + ALT_NAND_PARAM_ONFI_DEV_FEATURES_OFST))
/* The address of the ALT_NAND_PARAM_ONFI_OPTIONAL_CMDS register for the ALT_NAND_PARAM instance. */
#define ALT_NAND_PARAM_ONFI_OPTIONAL_CMDS_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_PARAM_ADDR) + ALT_NAND_PARAM_ONFI_OPTIONAL_CMDS_OFST))
/* The address of the ALT_NAND_PARAM_ONFI_TIMING_MOD register for the ALT_NAND_PARAM instance. */
#define ALT_NAND_PARAM_ONFI_TIMING_MOD_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_PARAM_ADDR) + ALT_NAND_PARAM_ONFI_TIMING_MOD_OFST))
/* The address of the ALT_NAND_PARAM_ONFI_PGM_CACHE_TIMING_MOD register for the ALT_NAND_PARAM instance. */
#define ALT_NAND_PARAM_ONFI_PGM_CACHE_TIMING_MOD_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_PARAM_ADDR) + ALT_NAND_PARAM_ONFI_PGM_CACHE_TIMING_MOD_OFST))
/* The address of the ALT_NAND_PARAM_ONFI_DEV_NO_OF_LUNS register for the ALT_NAND_PARAM instance. */
#define ALT_NAND_PARAM_ONFI_DEV_NO_OF_LUNS_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_PARAM_ADDR) + ALT_NAND_PARAM_ONFI_DEV_NO_OF_LUNS_OFST))
/* The address of the ALT_NAND_PARAM_ONFI_DEV_BLKS_PER_LUN_L register for the ALT_NAND_PARAM instance. */
#define ALT_NAND_PARAM_ONFI_DEV_BLKS_PER_LUN_L_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_PARAM_ADDR) + ALT_NAND_PARAM_ONFI_DEV_BLKS_PER_LUN_L_OFST))
/* The address of the ALT_NAND_PARAM_ONFI_DEV_BLKS_PER_LUN_U register for the ALT_NAND_PARAM instance. */
#define ALT_NAND_PARAM_ONFI_DEV_BLKS_PER_LUN_U_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_PARAM_ADDR) + ALT_NAND_PARAM_ONFI_DEV_BLKS_PER_LUN_U_OFST))
/* The address of the ALT_NAND_PARAM_FEATURES register for the ALT_NAND_PARAM instance. */
#define ALT_NAND_PARAM_FEATURES_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_PARAM_ADDR) + ALT_NAND_PARAM_FEATURES_OFST))
/* The base address byte offset for the start of the ALT_NAND_PARAM component. */
#define ALT_NAND_PARAM_OFST        0x300
/* The start address of the ALT_NAND_PARAM component. */
#define ALT_NAND_PARAM_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_ADDR) + ALT_NAND_PARAM_OFST))
/* The lower bound address range of the ALT_NAND_PARAM component. */
#define ALT_NAND_PARAM_LB_ADDR     ALT_NAND_PARAM_ADDR
/* The upper bound address range of the ALT_NAND_PARAM component. */
#define ALT_NAND_PARAM_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_NAND_PARAM_ADDR) + 0xf4) - 1))


/*
 * Register Group Instance : status
 * 
 * Instance status of register group ALT_NAND_STAT.
 * 
 * 
 */
/* The address of the ALT_NAND_STAT_TFR_MOD register for the ALT_NAND_STAT instance. */
#define ALT_NAND_STAT_TFR_MOD_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_STAT_ADDR) + ALT_NAND_STAT_TFR_MOD_OFST))
/* The address of the ALT_NAND_STAT_INTR_STAT0 register for the ALT_NAND_STAT instance. */
#define ALT_NAND_STAT_INTR_STAT0_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_STAT_ADDR) + ALT_NAND_STAT_INTR_STAT0_OFST))
/* The address of the ALT_NAND_STAT_INTR_EN0 register for the ALT_NAND_STAT instance. */
#define ALT_NAND_STAT_INTR_EN0_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_STAT_ADDR) + ALT_NAND_STAT_INTR_EN0_OFST))
/* The address of the ALT_NAND_STAT_PAGE_CNT0 register for the ALT_NAND_STAT instance. */
#define ALT_NAND_STAT_PAGE_CNT0_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_STAT_ADDR) + ALT_NAND_STAT_PAGE_CNT0_OFST))
/* The address of the ALT_NAND_STAT_ERR_PAGE_ADDR0 register for the ALT_NAND_STAT instance. */
#define ALT_NAND_STAT_ERR_PAGE_ADDR0_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_STAT_ADDR) + ALT_NAND_STAT_ERR_PAGE_ADDR0_OFST))
/* The address of the ALT_NAND_STAT_ERR_BLOCK_ADDR0 register for the ALT_NAND_STAT instance. */
#define ALT_NAND_STAT_ERR_BLOCK_ADDR0_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_STAT_ADDR) + ALT_NAND_STAT_ERR_BLOCK_ADDR0_OFST))
/* The address of the ALT_NAND_STAT_INTR_STAT1 register for the ALT_NAND_STAT instance. */
#define ALT_NAND_STAT_INTR_STAT1_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_STAT_ADDR) + ALT_NAND_STAT_INTR_STAT1_OFST))
/* The address of the ALT_NAND_STAT_INTR_EN1 register for the ALT_NAND_STAT instance. */
#define ALT_NAND_STAT_INTR_EN1_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_STAT_ADDR) + ALT_NAND_STAT_INTR_EN1_OFST))
/* The address of the ALT_NAND_STAT_PAGE_CNT1 register for the ALT_NAND_STAT instance. */
#define ALT_NAND_STAT_PAGE_CNT1_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_STAT_ADDR) + ALT_NAND_STAT_PAGE_CNT1_OFST))
/* The address of the ALT_NAND_STAT_ERR_PAGE_ADDR1 register for the ALT_NAND_STAT instance. */
#define ALT_NAND_STAT_ERR_PAGE_ADDR1_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_STAT_ADDR) + ALT_NAND_STAT_ERR_PAGE_ADDR1_OFST))
/* The address of the ALT_NAND_STAT_ERR_BLOCK_ADDR1 register for the ALT_NAND_STAT instance. */
#define ALT_NAND_STAT_ERR_BLOCK_ADDR1_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_STAT_ADDR) + ALT_NAND_STAT_ERR_BLOCK_ADDR1_OFST))
/* The address of the ALT_NAND_STAT_INTR_STAT2 register for the ALT_NAND_STAT instance. */
#define ALT_NAND_STAT_INTR_STAT2_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_STAT_ADDR) + ALT_NAND_STAT_INTR_STAT2_OFST))
/* The address of the ALT_NAND_STAT_INTR_EN2 register for the ALT_NAND_STAT instance. */
#define ALT_NAND_STAT_INTR_EN2_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_STAT_ADDR) + ALT_NAND_STAT_INTR_EN2_OFST))
/* The address of the ALT_NAND_STAT_PAGE_CNT2 register for the ALT_NAND_STAT instance. */
#define ALT_NAND_STAT_PAGE_CNT2_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_STAT_ADDR) + ALT_NAND_STAT_PAGE_CNT2_OFST))
/* The address of the ALT_NAND_STAT_ERR_PAGE_ADDR2 register for the ALT_NAND_STAT instance. */
#define ALT_NAND_STAT_ERR_PAGE_ADDR2_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_STAT_ADDR) + ALT_NAND_STAT_ERR_PAGE_ADDR2_OFST))
/* The address of the ALT_NAND_STAT_ERR_BLOCK_ADDR2 register for the ALT_NAND_STAT instance. */
#define ALT_NAND_STAT_ERR_BLOCK_ADDR2_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_STAT_ADDR) + ALT_NAND_STAT_ERR_BLOCK_ADDR2_OFST))
/* The address of the ALT_NAND_STAT_INTR_STAT3 register for the ALT_NAND_STAT instance. */
#define ALT_NAND_STAT_INTR_STAT3_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_STAT_ADDR) + ALT_NAND_STAT_INTR_STAT3_OFST))
/* The address of the ALT_NAND_STAT_INTR_EN3 register for the ALT_NAND_STAT instance. */
#define ALT_NAND_STAT_INTR_EN3_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_STAT_ADDR) + ALT_NAND_STAT_INTR_EN3_OFST))
/* The address of the ALT_NAND_STAT_PAGE_CNT3 register for the ALT_NAND_STAT instance. */
#define ALT_NAND_STAT_PAGE_CNT3_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_STAT_ADDR) + ALT_NAND_STAT_PAGE_CNT3_OFST))
/* The address of the ALT_NAND_STAT_ERR_PAGE_ADDR3 register for the ALT_NAND_STAT instance. */
#define ALT_NAND_STAT_ERR_PAGE_ADDR3_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_STAT_ADDR) + ALT_NAND_STAT_ERR_PAGE_ADDR3_OFST))
/* The address of the ALT_NAND_STAT_ERR_BLOCK_ADDR3 register for the ALT_NAND_STAT instance. */
#define ALT_NAND_STAT_ERR_BLOCK_ADDR3_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_STAT_ADDR) + ALT_NAND_STAT_ERR_BLOCK_ADDR3_OFST))
/* The base address byte offset for the start of the ALT_NAND_STAT component. */
#define ALT_NAND_STAT_OFST        0x400
/* The start address of the ALT_NAND_STAT component. */
#define ALT_NAND_STAT_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_ADDR) + ALT_NAND_STAT_OFST))
/* The lower bound address range of the ALT_NAND_STAT component. */
#define ALT_NAND_STAT_LB_ADDR     ALT_NAND_STAT_ADDR
/* The upper bound address range of the ALT_NAND_STAT component. */
#define ALT_NAND_STAT_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_NAND_STAT_ADDR) + 0x144) - 1))


/*
 * Register Group Instance : ecc
 * 
 * Instance ecc of register group ALT_NAND_ECC.
 * 
 * 
 */
/* The address of the ALT_NAND_ECC_ECCCORINFO_B01 register for the ALT_NAND_ECC instance. */
#define ALT_NAND_ECC_ECCCORINFO_B01_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_ECC_ADDR) + ALT_NAND_ECC_ECCCORINFO_B01_OFST))
/* The address of the ALT_NAND_ECC_ECCCORINFO_B23 register for the ALT_NAND_ECC instance. */
#define ALT_NAND_ECC_ECCCORINFO_B23_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_ECC_ADDR) + ALT_NAND_ECC_ECCCORINFO_B23_OFST))
/* The base address byte offset for the start of the ALT_NAND_ECC component. */
#define ALT_NAND_ECC_OFST        0x650
/* The start address of the ALT_NAND_ECC component. */
#define ALT_NAND_ECC_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_ADDR) + ALT_NAND_ECC_OFST))
/* The lower bound address range of the ALT_NAND_ECC component. */
#define ALT_NAND_ECC_LB_ADDR     ALT_NAND_ECC_ADDR
/* The upper bound address range of the ALT_NAND_ECC component. */
#define ALT_NAND_ECC_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_NAND_ECC_ADDR) + 0x14) - 1))


/*
 * Register Group Instance : dma
 * 
 * Instance dma of register group ALT_NAND_DMA.
 * 
 * 
 */
/* The address of the ALT_NAND_DMA_DMA_EN register for the ALT_NAND_DMA instance. */
#define ALT_NAND_DMA_DMA_EN_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_DMA_ADDR) + ALT_NAND_DMA_DMA_EN_OFST))
/* The address of the ALT_NAND_DMA_DMA_INTR register for the ALT_NAND_DMA instance. */
#define ALT_NAND_DMA_DMA_INTR_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_DMA_ADDR) + ALT_NAND_DMA_DMA_INTR_OFST))
/* The address of the ALT_NAND_DMA_DMA_INTR_EN register for the ALT_NAND_DMA instance. */
#define ALT_NAND_DMA_DMA_INTR_EN_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_DMA_ADDR) + ALT_NAND_DMA_DMA_INTR_EN_OFST))
/* The address of the ALT_NAND_DMA_TGT_ERR_ADDR_LO register for the ALT_NAND_DMA instance. */
#define ALT_NAND_DMA_TGT_ERR_ADDR_LO_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_DMA_ADDR) + ALT_NAND_DMA_TGT_ERR_ADDR_LO_OFST))
/* The address of the ALT_NAND_DMA_TGT_ERR_ADDR_HI register for the ALT_NAND_DMA instance. */
#define ALT_NAND_DMA_TGT_ERR_ADDR_HI_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_DMA_ADDR) + ALT_NAND_DMA_TGT_ERR_ADDR_HI_OFST))
/* The address of the ALT_NAND_DMA_FLSH_BURST_LEN register for the ALT_NAND_DMA instance. */
#define ALT_NAND_DMA_FLSH_BURST_LEN_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_DMA_ADDR) + ALT_NAND_DMA_FLSH_BURST_LEN_OFST))
/* The address of the ALT_NAND_DMA_INTRLV register for the ALT_NAND_DMA instance. */
#define ALT_NAND_DMA_INTRLV_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_DMA_ADDR) + ALT_NAND_DMA_INTRLV_OFST))
/* The address of the ALT_NAND_DMA_NO_OF_BLOCKS_PER_LUN register for the ALT_NAND_DMA instance. */
#define ALT_NAND_DMA_NO_OF_BLOCKS_PER_LUN_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_DMA_ADDR) + ALT_NAND_DMA_NO_OF_BLOCKS_PER_LUN_OFST))
/* The address of the ALT_NAND_DMA_LUN_STAT_CMD register for the ALT_NAND_DMA instance. */
#define ALT_NAND_DMA_LUN_STAT_CMD_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_DMA_ADDR) + ALT_NAND_DMA_LUN_STAT_CMD_OFST))
/* The base address byte offset for the start of the ALT_NAND_DMA component. */
#define ALT_NAND_DMA_OFST        0x700
/* The start address of the ALT_NAND_DMA component. */
#define ALT_NAND_DMA_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_NAND_ADDR) + ALT_NAND_DMA_OFST))
/* The lower bound address range of the ALT_NAND_DMA component. */
#define ALT_NAND_DMA_LB_ADDR     ALT_NAND_DMA_ADDR
/* The upper bound address range of the ALT_NAND_DMA component. */
#define ALT_NAND_DMA_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_NAND_DMA_ADDR) + 0xa4) - 1))


/* The base address byte offset for the start of the ALT_NAND component. */
#define ALT_NAND_OFST        0xffb80000
/* The start address of the ALT_NAND component. */
#define ALT_NAND_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_HPS_ADDR) + ALT_NAND_OFST))
/* The lower bound address range of the ALT_NAND component. */
#define ALT_NAND_LB_ADDR     ALT_NAND_ADDR
/* The upper bound address range of the ALT_NAND component. */
#define ALT_NAND_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_NAND_ADDR) + 0x800) - 1))


/*
 * Component Instance : fpgamgrdata
 * 
 * Instance fpgamgrdata of component ALT_FPGAMGRDATA.
 * 
 * 
 */
/* The address of the ALT_FPGAMGRDATA_DATA register for the ALT_FPGAMGRDATA instance. */
#define ALT_FPGAMGRDATA_DATA_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_FPGAMGRDATA_ADDR) + ALT_FPGAMGRDATA_DATA_OFST))
/* The base address byte offset for the start of the ALT_FPGAMGRDATA component. */
#define ALT_FPGAMGRDATA_OFST        0xffb90000
/* The start address of the ALT_FPGAMGRDATA component. */
#define ALT_FPGAMGRDATA_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_HPS_ADDR) + ALT_FPGAMGRDATA_OFST))
/* The lower bound address range of the ALT_FPGAMGRDATA component. */
#define ALT_FPGAMGRDATA_LB_ADDR     ALT_FPGAMGRDATA_ADDR
/* The upper bound address range of the ALT_FPGAMGRDATA component. */
#define ALT_FPGAMGRDATA_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_FPGAMGRDATA_ADDR) + 0x4) - 1))


/*
 * Component Instance : can0
 * 
 * Instance can0 of component ALT_CAN.
 * 
 * 
 */
/*
 * Register Group Instance : protogrp
 * 
 * Instance protogrp of register group ALT_CAN_PROTO.
 * 
 * 
 */
/* The address of the ALT_CAN_PROTO_CCTL register for the ALT_CAN0_PROTOGRP instance. */
#define ALT_CAN0_PROTO_CCTL_ADDR  ALT_CAN_PROTO_CCTL_ADDR(ALT_CAN0_PROTOGRP_ADDR)
/* The address of the ALT_CAN_PROTO_CSTS register for the ALT_CAN0_PROTOGRP instance. */
#define ALT_CAN0_PROTO_CSTS_ADDR  ALT_CAN_PROTO_CSTS_ADDR(ALT_CAN0_PROTOGRP_ADDR)
/* The address of the ALT_CAN_PROTO_CERC register for the ALT_CAN0_PROTOGRP instance. */
#define ALT_CAN0_PROTO_CERC_ADDR  ALT_CAN_PROTO_CERC_ADDR(ALT_CAN0_PROTOGRP_ADDR)
/* The address of the ALT_CAN_PROTO_CBT register for the ALT_CAN0_PROTOGRP instance. */
#define ALT_CAN0_PROTO_CBT_ADDR  ALT_CAN_PROTO_CBT_ADDR(ALT_CAN0_PROTOGRP_ADDR)
/* The address of the ALT_CAN_PROTO_CIR register for the ALT_CAN0_PROTOGRP instance. */
#define ALT_CAN0_PROTO_CIR_ADDR  ALT_CAN_PROTO_CIR_ADDR(ALT_CAN0_PROTOGRP_ADDR)
/* The address of the ALT_CAN_PROTO_CTR register for the ALT_CAN0_PROTOGRP instance. */
#define ALT_CAN0_PROTO_CTR_ADDR  ALT_CAN_PROTO_CTR_ADDR(ALT_CAN0_PROTOGRP_ADDR)
/* The address of the ALT_CAN_PROTO_CFR register for the ALT_CAN0_PROTOGRP instance. */
#define ALT_CAN0_PROTO_CFR_ADDR  ALT_CAN_PROTO_CFR_ADDR(ALT_CAN0_PROTOGRP_ADDR)
/* The address of the ALT_CAN_PROTO_CRR register for the ALT_CAN0_PROTOGRP instance. */
#define ALT_CAN0_PROTO_CRR_ADDR  ALT_CAN_PROTO_CRR_ADDR(ALT_CAN0_PROTOGRP_ADDR)
/* The address of the ALT_CAN_PROTO_HWS register for the ALT_CAN0_PROTOGRP instance. */
#define ALT_CAN0_PROTO_HWS_ADDR  ALT_CAN_PROTO_HWS_ADDR(ALT_CAN0_PROTOGRP_ADDR)
/* The base address byte offset for the start of the ALT_CAN0_PROTOGRP component. */
#define ALT_CAN0_PROTOGRP_OFST        0x0
/* The start address of the ALT_CAN0_PROTOGRP component. */
#define ALT_CAN0_PROTOGRP_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_CAN0_ADDR) + ALT_CAN0_PROTOGRP_OFST))
/* The lower bound address range of the ALT_CAN0_PROTOGRP component. */
#define ALT_CAN0_PROTOGRP_LB_ADDR     ALT_CAN0_PROTOGRP_ADDR
/* The upper bound address range of the ALT_CAN0_PROTOGRP component. */
#define ALT_CAN0_PROTOGRP_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_CAN0_PROTOGRP_ADDR) + 0x28) - 1))


/*
 * Register Group Instance : msghandgrp
 * 
 * Instance msghandgrp of register group ALT_CAN_MSGHAND.
 * 
 * 
 */
/* The address of the ALT_CAN_MSGHAND_MOTRX register for the ALT_CAN0_MSGHANDGRP instance. */
#define ALT_CAN0_MSGHAND_MOTRX_ADDR  ALT_CAN_MSGHAND_MOTRX_ADDR(ALT_CAN0_MSGHANDGRP_ADDR)
/* The address of the ALT_CAN_MSGHAND_MOTRA register for the ALT_CAN0_MSGHANDGRP instance. */
#define ALT_CAN0_MSGHAND_MOTRA_ADDR  ALT_CAN_MSGHAND_MOTRA_ADDR(ALT_CAN0_MSGHANDGRP_ADDR)
/* The address of the ALT_CAN_MSGHAND_MOTRB register for the ALT_CAN0_MSGHANDGRP instance. */
#define ALT_CAN0_MSGHAND_MOTRB_ADDR  ALT_CAN_MSGHAND_MOTRB_ADDR(ALT_CAN0_MSGHANDGRP_ADDR)
/* The address of the ALT_CAN_MSGHAND_MOTRC register for the ALT_CAN0_MSGHANDGRP instance. */
#define ALT_CAN0_MSGHAND_MOTRC_ADDR  ALT_CAN_MSGHAND_MOTRC_ADDR(ALT_CAN0_MSGHANDGRP_ADDR)
/* The address of the ALT_CAN_MSGHAND_MOTRD register for the ALT_CAN0_MSGHANDGRP instance. */
#define ALT_CAN0_MSGHAND_MOTRD_ADDR  ALT_CAN_MSGHAND_MOTRD_ADDR(ALT_CAN0_MSGHANDGRP_ADDR)
/* The address of the ALT_CAN_MSGHAND_MONDX register for the ALT_CAN0_MSGHANDGRP instance. */
#define ALT_CAN0_MSGHAND_MONDX_ADDR  ALT_CAN_MSGHAND_MONDX_ADDR(ALT_CAN0_MSGHANDGRP_ADDR)
/* The address of the ALT_CAN_MSGHAND_MONDA register for the ALT_CAN0_MSGHANDGRP instance. */
#define ALT_CAN0_MSGHAND_MONDA_ADDR  ALT_CAN_MSGHAND_MONDA_ADDR(ALT_CAN0_MSGHANDGRP_ADDR)
/* The address of the ALT_CAN_MSGHAND_MONDB register for the ALT_CAN0_MSGHANDGRP instance. */
#define ALT_CAN0_MSGHAND_MONDB_ADDR  ALT_CAN_MSGHAND_MONDB_ADDR(ALT_CAN0_MSGHANDGRP_ADDR)
/* The address of the ALT_CAN_MSGHAND_MONDC register for the ALT_CAN0_MSGHANDGRP instance. */
#define ALT_CAN0_MSGHAND_MONDC_ADDR  ALT_CAN_MSGHAND_MONDC_ADDR(ALT_CAN0_MSGHANDGRP_ADDR)
/* The address of the ALT_CAN_MSGHAND_MONDD register for the ALT_CAN0_MSGHANDGRP instance. */
#define ALT_CAN0_MSGHAND_MONDD_ADDR  ALT_CAN_MSGHAND_MONDD_ADDR(ALT_CAN0_MSGHANDGRP_ADDR)
/* The address of the ALT_CAN_MSGHAND_MOIPX register for the ALT_CAN0_MSGHANDGRP instance. */
#define ALT_CAN0_MSGHAND_MOIPX_ADDR  ALT_CAN_MSGHAND_MOIPX_ADDR(ALT_CAN0_MSGHANDGRP_ADDR)
/* The address of the ALT_CAN_MSGHAND_MOIPA register for the ALT_CAN0_MSGHANDGRP instance. */
#define ALT_CAN0_MSGHAND_MOIPA_ADDR  ALT_CAN_MSGHAND_MOIPA_ADDR(ALT_CAN0_MSGHANDGRP_ADDR)
/* The address of the ALT_CAN_MSGHAND_MOIPB register for the ALT_CAN0_MSGHANDGRP instance. */
#define ALT_CAN0_MSGHAND_MOIPB_ADDR  ALT_CAN_MSGHAND_MOIPB_ADDR(ALT_CAN0_MSGHANDGRP_ADDR)
/* The address of the ALT_CAN_MSGHAND_MOIPC register for the ALT_CAN0_MSGHANDGRP instance. */
#define ALT_CAN0_MSGHAND_MOIPC_ADDR  ALT_CAN_MSGHAND_MOIPC_ADDR(ALT_CAN0_MSGHANDGRP_ADDR)
/* The address of the ALT_CAN_MSGHAND_MOIPD register for the ALT_CAN0_MSGHANDGRP instance. */
#define ALT_CAN0_MSGHAND_MOIPD_ADDR  ALT_CAN_MSGHAND_MOIPD_ADDR(ALT_CAN0_MSGHANDGRP_ADDR)
/* The address of the ALT_CAN_MSGHAND_MOVALX register for the ALT_CAN0_MSGHANDGRP instance. */
#define ALT_CAN0_MSGHAND_MOVALX_ADDR  ALT_CAN_MSGHAND_MOVALX_ADDR(ALT_CAN0_MSGHANDGRP_ADDR)
/* The address of the ALT_CAN_MSGHAND_MOVALA register for the ALT_CAN0_MSGHANDGRP instance. */
#define ALT_CAN0_MSGHAND_MOVALA_ADDR  ALT_CAN_MSGHAND_MOVALA_ADDR(ALT_CAN0_MSGHANDGRP_ADDR)
/* The address of the ALT_CAN_MSGHAND_MOVALB register for the ALT_CAN0_MSGHANDGRP instance. */
#define ALT_CAN0_MSGHAND_MOVALB_ADDR  ALT_CAN_MSGHAND_MOVALB_ADDR(ALT_CAN0_MSGHANDGRP_ADDR)
/* The address of the ALT_CAN_MSGHAND_MOVALC register for the ALT_CAN0_MSGHANDGRP instance. */
#define ALT_CAN0_MSGHAND_MOVALC_ADDR  ALT_CAN_MSGHAND_MOVALC_ADDR(ALT_CAN0_MSGHANDGRP_ADDR)
/* The address of the ALT_CAN_MSGHAND_MOVALD register for the ALT_CAN0_MSGHANDGRP instance. */
#define ALT_CAN0_MSGHAND_MOVALD_ADDR  ALT_CAN_MSGHAND_MOVALD_ADDR(ALT_CAN0_MSGHANDGRP_ADDR)
/* The base address byte offset for the start of the ALT_CAN0_MSGHANDGRP component. */
#define ALT_CAN0_MSGHANDGRP_OFST        0x84
/* The start address of the ALT_CAN0_MSGHANDGRP component. */
#define ALT_CAN0_MSGHANDGRP_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_CAN0_ADDR) + ALT_CAN0_MSGHANDGRP_OFST))
/* The lower bound address range of the ALT_CAN0_MSGHANDGRP component. */
#define ALT_CAN0_MSGHANDGRP_LB_ADDR     ALT_CAN0_MSGHANDGRP_ADDR
/* The upper bound address range of the ALT_CAN0_MSGHANDGRP component. */
#define ALT_CAN0_MSGHANDGRP_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_CAN0_MSGHANDGRP_ADDR) + 0x50) - 1))


/*
 * Register Group Instance : msgifgrp
 * 
 * Instance msgifgrp of register group ALT_CAN_MSGIF.
 * 
 * 
 */
/* The address of the ALT_CAN_MSGIF_IF1CMR register for the ALT_CAN0_MSGIFGRP instance. */
#define ALT_CAN0_MSGIF_IF1CMR_ADDR  ALT_CAN_MSGIF_IF1CMR_ADDR(ALT_CAN0_MSGIFGRP_ADDR)
/* The address of the ALT_CAN_MSGIF_IF1MSK register for the ALT_CAN0_MSGIFGRP instance. */
#define ALT_CAN0_MSGIF_IF1MSK_ADDR  ALT_CAN_MSGIF_IF1MSK_ADDR(ALT_CAN0_MSGIFGRP_ADDR)
/* The address of the ALT_CAN_MSGIF_IF1ARB register for the ALT_CAN0_MSGIFGRP instance. */
#define ALT_CAN0_MSGIF_IF1ARB_ADDR  ALT_CAN_MSGIF_IF1ARB_ADDR(ALT_CAN0_MSGIFGRP_ADDR)
/* The address of the ALT_CAN_MSGIF_IF1MCTR register for the ALT_CAN0_MSGIFGRP instance. */
#define ALT_CAN0_MSGIF_IF1MCTR_ADDR  ALT_CAN_MSGIF_IF1MCTR_ADDR(ALT_CAN0_MSGIFGRP_ADDR)
/* The address of the ALT_CAN_MSGIF_IF1DA register for the ALT_CAN0_MSGIFGRP instance. */
#define ALT_CAN0_MSGIF_IF1DA_ADDR  ALT_CAN_MSGIF_IF1DA_ADDR(ALT_CAN0_MSGIFGRP_ADDR)
/* The address of the ALT_CAN_MSGIF_IF1DB register for the ALT_CAN0_MSGIFGRP instance. */
#define ALT_CAN0_MSGIF_IF1DB_ADDR  ALT_CAN_MSGIF_IF1DB_ADDR(ALT_CAN0_MSGIFGRP_ADDR)
/* The address of the ALT_CAN_MSGIF_IF2CMR register for the ALT_CAN0_MSGIFGRP instance. */
#define ALT_CAN0_MSGIF_IF2CMR_ADDR  ALT_CAN_MSGIF_IF2CMR_ADDR(ALT_CAN0_MSGIFGRP_ADDR)
/* The address of the ALT_CAN_MSGIF_IF2MSK register for the ALT_CAN0_MSGIFGRP instance. */
#define ALT_CAN0_MSGIF_IF2MSK_ADDR  ALT_CAN_MSGIF_IF2MSK_ADDR(ALT_CAN0_MSGIFGRP_ADDR)
/* The address of the ALT_CAN_MSGIF_IF2ARB register for the ALT_CAN0_MSGIFGRP instance. */
#define ALT_CAN0_MSGIF_IF2ARB_ADDR  ALT_CAN_MSGIF_IF2ARB_ADDR(ALT_CAN0_MSGIFGRP_ADDR)
/* The address of the ALT_CAN_MSGIF_IF2MCTR register for the ALT_CAN0_MSGIFGRP instance. */
#define ALT_CAN0_MSGIF_IF2MCTR_ADDR  ALT_CAN_MSGIF_IF2MCTR_ADDR(ALT_CAN0_MSGIFGRP_ADDR)
/* The address of the ALT_CAN_MSGIF_IF2DA register for the ALT_CAN0_MSGIFGRP instance. */
#define ALT_CAN0_MSGIF_IF2DA_ADDR  ALT_CAN_MSGIF_IF2DA_ADDR(ALT_CAN0_MSGIFGRP_ADDR)
/* The address of the ALT_CAN_MSGIF_IF2DB register for the ALT_CAN0_MSGIFGRP instance. */
#define ALT_CAN0_MSGIF_IF2DB_ADDR  ALT_CAN_MSGIF_IF2DB_ADDR(ALT_CAN0_MSGIFGRP_ADDR)
/* The base address byte offset for the start of the ALT_CAN0_MSGIFGRP component. */
#define ALT_CAN0_MSGIFGRP_OFST        0x100
/* The start address of the ALT_CAN0_MSGIFGRP component. */
#define ALT_CAN0_MSGIFGRP_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_CAN0_ADDR) + ALT_CAN0_MSGIFGRP_OFST))
/* The lower bound address range of the ALT_CAN0_MSGIFGRP component. */
#define ALT_CAN0_MSGIFGRP_LB_ADDR     ALT_CAN0_MSGIFGRP_ADDR
/* The upper bound address range of the ALT_CAN0_MSGIFGRP component. */
#define ALT_CAN0_MSGIFGRP_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_CAN0_MSGIFGRP_ADDR) + 0x38) - 1))


/* The base address byte offset for the start of the ALT_CAN0 component. */
#define ALT_CAN0_OFST        0xffc00000
/* The start address of the ALT_CAN0 component. */
#define ALT_CAN0_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_HPS_ADDR) + ALT_CAN0_OFST))
/* The lower bound address range of the ALT_CAN0 component. */
#define ALT_CAN0_LB_ADDR     ALT_CAN0_ADDR
/* The upper bound address range of the ALT_CAN0 component. */
#define ALT_CAN0_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_CAN0_ADDR) + 0x200) - 1))


/*
 * Component Instance : can1
 * 
 * Instance can1 of component ALT_CAN.
 * 
 * 
 */
/*
 * Register Group Instance : protogrp
 * 
 * Instance protogrp of register group ALT_CAN_PROTO.
 * 
 * 
 */
/* The address of the ALT_CAN_PROTO_CCTL register for the ALT_CAN1_PROTOGRP instance. */
#define ALT_CAN1_PROTO_CCTL_ADDR  ALT_CAN_PROTO_CCTL_ADDR(ALT_CAN1_PROTOGRP_ADDR)
/* The address of the ALT_CAN_PROTO_CSTS register for the ALT_CAN1_PROTOGRP instance. */
#define ALT_CAN1_PROTO_CSTS_ADDR  ALT_CAN_PROTO_CSTS_ADDR(ALT_CAN1_PROTOGRP_ADDR)
/* The address of the ALT_CAN_PROTO_CERC register for the ALT_CAN1_PROTOGRP instance. */
#define ALT_CAN1_PROTO_CERC_ADDR  ALT_CAN_PROTO_CERC_ADDR(ALT_CAN1_PROTOGRP_ADDR)
/* The address of the ALT_CAN_PROTO_CBT register for the ALT_CAN1_PROTOGRP instance. */
#define ALT_CAN1_PROTO_CBT_ADDR  ALT_CAN_PROTO_CBT_ADDR(ALT_CAN1_PROTOGRP_ADDR)
/* The address of the ALT_CAN_PROTO_CIR register for the ALT_CAN1_PROTOGRP instance. */
#define ALT_CAN1_PROTO_CIR_ADDR  ALT_CAN_PROTO_CIR_ADDR(ALT_CAN1_PROTOGRP_ADDR)
/* The address of the ALT_CAN_PROTO_CTR register for the ALT_CAN1_PROTOGRP instance. */
#define ALT_CAN1_PROTO_CTR_ADDR  ALT_CAN_PROTO_CTR_ADDR(ALT_CAN1_PROTOGRP_ADDR)
/* The address of the ALT_CAN_PROTO_CFR register for the ALT_CAN1_PROTOGRP instance. */
#define ALT_CAN1_PROTO_CFR_ADDR  ALT_CAN_PROTO_CFR_ADDR(ALT_CAN1_PROTOGRP_ADDR)
/* The address of the ALT_CAN_PROTO_CRR register for the ALT_CAN1_PROTOGRP instance. */
#define ALT_CAN1_PROTO_CRR_ADDR  ALT_CAN_PROTO_CRR_ADDR(ALT_CAN1_PROTOGRP_ADDR)
/* The address of the ALT_CAN_PROTO_HWS register for the ALT_CAN1_PROTOGRP instance. */
#define ALT_CAN1_PROTO_HWS_ADDR  ALT_CAN_PROTO_HWS_ADDR(ALT_CAN1_PROTOGRP_ADDR)
/* The base address byte offset for the start of the ALT_CAN1_PROTOGRP component. */
#define ALT_CAN1_PROTOGRP_OFST        0x0
/* The start address of the ALT_CAN1_PROTOGRP component. */
#define ALT_CAN1_PROTOGRP_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_CAN1_ADDR) + ALT_CAN1_PROTOGRP_OFST))
/* The lower bound address range of the ALT_CAN1_PROTOGRP component. */
#define ALT_CAN1_PROTOGRP_LB_ADDR     ALT_CAN1_PROTOGRP_ADDR
/* The upper bound address range of the ALT_CAN1_PROTOGRP component. */
#define ALT_CAN1_PROTOGRP_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_CAN1_PROTOGRP_ADDR) + 0x28) - 1))


/*
 * Register Group Instance : msghandgrp
 * 
 * Instance msghandgrp of register group ALT_CAN_MSGHAND.
 * 
 * 
 */
/* The address of the ALT_CAN_MSGHAND_MOTRX register for the ALT_CAN1_MSGHANDGRP instance. */
#define ALT_CAN1_MSGHAND_MOTRX_ADDR  ALT_CAN_MSGHAND_MOTRX_ADDR(ALT_CAN1_MSGHANDGRP_ADDR)
/* The address of the ALT_CAN_MSGHAND_MOTRA register for the ALT_CAN1_MSGHANDGRP instance. */
#define ALT_CAN1_MSGHAND_MOTRA_ADDR  ALT_CAN_MSGHAND_MOTRA_ADDR(ALT_CAN1_MSGHANDGRP_ADDR)
/* The address of the ALT_CAN_MSGHAND_MOTRB register for the ALT_CAN1_MSGHANDGRP instance. */
#define ALT_CAN1_MSGHAND_MOTRB_ADDR  ALT_CAN_MSGHAND_MOTRB_ADDR(ALT_CAN1_MSGHANDGRP_ADDR)
/* The address of the ALT_CAN_MSGHAND_MOTRC register for the ALT_CAN1_MSGHANDGRP instance. */
#define ALT_CAN1_MSGHAND_MOTRC_ADDR  ALT_CAN_MSGHAND_MOTRC_ADDR(ALT_CAN1_MSGHANDGRP_ADDR)
/* The address of the ALT_CAN_MSGHAND_MOTRD register for the ALT_CAN1_MSGHANDGRP instance. */
#define ALT_CAN1_MSGHAND_MOTRD_ADDR  ALT_CAN_MSGHAND_MOTRD_ADDR(ALT_CAN1_MSGHANDGRP_ADDR)
/* The address of the ALT_CAN_MSGHAND_MONDX register for the ALT_CAN1_MSGHANDGRP instance. */
#define ALT_CAN1_MSGHAND_MONDX_ADDR  ALT_CAN_MSGHAND_MONDX_ADDR(ALT_CAN1_MSGHANDGRP_ADDR)
/* The address of the ALT_CAN_MSGHAND_MONDA register for the ALT_CAN1_MSGHANDGRP instance. */
#define ALT_CAN1_MSGHAND_MONDA_ADDR  ALT_CAN_MSGHAND_MONDA_ADDR(ALT_CAN1_MSGHANDGRP_ADDR)
/* The address of the ALT_CAN_MSGHAND_MONDB register for the ALT_CAN1_MSGHANDGRP instance. */
#define ALT_CAN1_MSGHAND_MONDB_ADDR  ALT_CAN_MSGHAND_MONDB_ADDR(ALT_CAN1_MSGHANDGRP_ADDR)
/* The address of the ALT_CAN_MSGHAND_MONDC register for the ALT_CAN1_MSGHANDGRP instance. */
#define ALT_CAN1_MSGHAND_MONDC_ADDR  ALT_CAN_MSGHAND_MONDC_ADDR(ALT_CAN1_MSGHANDGRP_ADDR)
/* The address of the ALT_CAN_MSGHAND_MONDD register for the ALT_CAN1_MSGHANDGRP instance. */
#define ALT_CAN1_MSGHAND_MONDD_ADDR  ALT_CAN_MSGHAND_MONDD_ADDR(ALT_CAN1_MSGHANDGRP_ADDR)
/* The address of the ALT_CAN_MSGHAND_MOIPX register for the ALT_CAN1_MSGHANDGRP instance. */
#define ALT_CAN1_MSGHAND_MOIPX_ADDR  ALT_CAN_MSGHAND_MOIPX_ADDR(ALT_CAN1_MSGHANDGRP_ADDR)
/* The address of the ALT_CAN_MSGHAND_MOIPA register for the ALT_CAN1_MSGHANDGRP instance. */
#define ALT_CAN1_MSGHAND_MOIPA_ADDR  ALT_CAN_MSGHAND_MOIPA_ADDR(ALT_CAN1_MSGHANDGRP_ADDR)
/* The address of the ALT_CAN_MSGHAND_MOIPB register for the ALT_CAN1_MSGHANDGRP instance. */
#define ALT_CAN1_MSGHAND_MOIPB_ADDR  ALT_CAN_MSGHAND_MOIPB_ADDR(ALT_CAN1_MSGHANDGRP_ADDR)
/* The address of the ALT_CAN_MSGHAND_MOIPC register for the ALT_CAN1_MSGHANDGRP instance. */
#define ALT_CAN1_MSGHAND_MOIPC_ADDR  ALT_CAN_MSGHAND_MOIPC_ADDR(ALT_CAN1_MSGHANDGRP_ADDR)
/* The address of the ALT_CAN_MSGHAND_MOIPD register for the ALT_CAN1_MSGHANDGRP instance. */
#define ALT_CAN1_MSGHAND_MOIPD_ADDR  ALT_CAN_MSGHAND_MOIPD_ADDR(ALT_CAN1_MSGHANDGRP_ADDR)
/* The address of the ALT_CAN_MSGHAND_MOVALX register for the ALT_CAN1_MSGHANDGRP instance. */
#define ALT_CAN1_MSGHAND_MOVALX_ADDR  ALT_CAN_MSGHAND_MOVALX_ADDR(ALT_CAN1_MSGHANDGRP_ADDR)
/* The address of the ALT_CAN_MSGHAND_MOVALA register for the ALT_CAN1_MSGHANDGRP instance. */
#define ALT_CAN1_MSGHAND_MOVALA_ADDR  ALT_CAN_MSGHAND_MOVALA_ADDR(ALT_CAN1_MSGHANDGRP_ADDR)
/* The address of the ALT_CAN_MSGHAND_MOVALB register for the ALT_CAN1_MSGHANDGRP instance. */
#define ALT_CAN1_MSGHAND_MOVALB_ADDR  ALT_CAN_MSGHAND_MOVALB_ADDR(ALT_CAN1_MSGHANDGRP_ADDR)
/* The address of the ALT_CAN_MSGHAND_MOVALC register for the ALT_CAN1_MSGHANDGRP instance. */
#define ALT_CAN1_MSGHAND_MOVALC_ADDR  ALT_CAN_MSGHAND_MOVALC_ADDR(ALT_CAN1_MSGHANDGRP_ADDR)
/* The address of the ALT_CAN_MSGHAND_MOVALD register for the ALT_CAN1_MSGHANDGRP instance. */
#define ALT_CAN1_MSGHAND_MOVALD_ADDR  ALT_CAN_MSGHAND_MOVALD_ADDR(ALT_CAN1_MSGHANDGRP_ADDR)
/* The base address byte offset for the start of the ALT_CAN1_MSGHANDGRP component. */
#define ALT_CAN1_MSGHANDGRP_OFST        0x84
/* The start address of the ALT_CAN1_MSGHANDGRP component. */
#define ALT_CAN1_MSGHANDGRP_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_CAN1_ADDR) + ALT_CAN1_MSGHANDGRP_OFST))
/* The lower bound address range of the ALT_CAN1_MSGHANDGRP component. */
#define ALT_CAN1_MSGHANDGRP_LB_ADDR     ALT_CAN1_MSGHANDGRP_ADDR
/* The upper bound address range of the ALT_CAN1_MSGHANDGRP component. */
#define ALT_CAN1_MSGHANDGRP_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_CAN1_MSGHANDGRP_ADDR) + 0x50) - 1))


/*
 * Register Group Instance : msgifgrp
 * 
 * Instance msgifgrp of register group ALT_CAN_MSGIF.
 * 
 * 
 */
/* The address of the ALT_CAN_MSGIF_IF1CMR register for the ALT_CAN1_MSGIFGRP instance. */
#define ALT_CAN1_MSGIF_IF1CMR_ADDR  ALT_CAN_MSGIF_IF1CMR_ADDR(ALT_CAN1_MSGIFGRP_ADDR)
/* The address of the ALT_CAN_MSGIF_IF1MSK register for the ALT_CAN1_MSGIFGRP instance. */
#define ALT_CAN1_MSGIF_IF1MSK_ADDR  ALT_CAN_MSGIF_IF1MSK_ADDR(ALT_CAN1_MSGIFGRP_ADDR)
/* The address of the ALT_CAN_MSGIF_IF1ARB register for the ALT_CAN1_MSGIFGRP instance. */
#define ALT_CAN1_MSGIF_IF1ARB_ADDR  ALT_CAN_MSGIF_IF1ARB_ADDR(ALT_CAN1_MSGIFGRP_ADDR)
/* The address of the ALT_CAN_MSGIF_IF1MCTR register for the ALT_CAN1_MSGIFGRP instance. */
#define ALT_CAN1_MSGIF_IF1MCTR_ADDR  ALT_CAN_MSGIF_IF1MCTR_ADDR(ALT_CAN1_MSGIFGRP_ADDR)
/* The address of the ALT_CAN_MSGIF_IF1DA register for the ALT_CAN1_MSGIFGRP instance. */
#define ALT_CAN1_MSGIF_IF1DA_ADDR  ALT_CAN_MSGIF_IF1DA_ADDR(ALT_CAN1_MSGIFGRP_ADDR)
/* The address of the ALT_CAN_MSGIF_IF1DB register for the ALT_CAN1_MSGIFGRP instance. */
#define ALT_CAN1_MSGIF_IF1DB_ADDR  ALT_CAN_MSGIF_IF1DB_ADDR(ALT_CAN1_MSGIFGRP_ADDR)
/* The address of the ALT_CAN_MSGIF_IF2CMR register for the ALT_CAN1_MSGIFGRP instance. */
#define ALT_CAN1_MSGIF_IF2CMR_ADDR  ALT_CAN_MSGIF_IF2CMR_ADDR(ALT_CAN1_MSGIFGRP_ADDR)
/* The address of the ALT_CAN_MSGIF_IF2MSK register for the ALT_CAN1_MSGIFGRP instance. */
#define ALT_CAN1_MSGIF_IF2MSK_ADDR  ALT_CAN_MSGIF_IF2MSK_ADDR(ALT_CAN1_MSGIFGRP_ADDR)
/* The address of the ALT_CAN_MSGIF_IF2ARB register for the ALT_CAN1_MSGIFGRP instance. */
#define ALT_CAN1_MSGIF_IF2ARB_ADDR  ALT_CAN_MSGIF_IF2ARB_ADDR(ALT_CAN1_MSGIFGRP_ADDR)
/* The address of the ALT_CAN_MSGIF_IF2MCTR register for the ALT_CAN1_MSGIFGRP instance. */
#define ALT_CAN1_MSGIF_IF2MCTR_ADDR  ALT_CAN_MSGIF_IF2MCTR_ADDR(ALT_CAN1_MSGIFGRP_ADDR)
/* The address of the ALT_CAN_MSGIF_IF2DA register for the ALT_CAN1_MSGIFGRP instance. */
#define ALT_CAN1_MSGIF_IF2DA_ADDR  ALT_CAN_MSGIF_IF2DA_ADDR(ALT_CAN1_MSGIFGRP_ADDR)
/* The address of the ALT_CAN_MSGIF_IF2DB register for the ALT_CAN1_MSGIFGRP instance. */
#define ALT_CAN1_MSGIF_IF2DB_ADDR  ALT_CAN_MSGIF_IF2DB_ADDR(ALT_CAN1_MSGIFGRP_ADDR)
/* The base address byte offset for the start of the ALT_CAN1_MSGIFGRP component. */
#define ALT_CAN1_MSGIFGRP_OFST        0x100
/* The start address of the ALT_CAN1_MSGIFGRP component. */
#define ALT_CAN1_MSGIFGRP_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_CAN1_ADDR) + ALT_CAN1_MSGIFGRP_OFST))
/* The lower bound address range of the ALT_CAN1_MSGIFGRP component. */
#define ALT_CAN1_MSGIFGRP_LB_ADDR     ALT_CAN1_MSGIFGRP_ADDR
/* The upper bound address range of the ALT_CAN1_MSGIFGRP component. */
#define ALT_CAN1_MSGIFGRP_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_CAN1_MSGIFGRP_ADDR) + 0x38) - 1))


/* The base address byte offset for the start of the ALT_CAN1 component. */
#define ALT_CAN1_OFST        0xffc01000
/* The start address of the ALT_CAN1 component. */
#define ALT_CAN1_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_HPS_ADDR) + ALT_CAN1_OFST))
/* The lower bound address range of the ALT_CAN1 component. */
#define ALT_CAN1_LB_ADDR     ALT_CAN1_ADDR
/* The upper bound address range of the ALT_CAN1 component. */
#define ALT_CAN1_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_CAN1_ADDR) + 0x200) - 1))


/*
 * Component Instance : uart0
 * 
 * Instance uart0 of component ALT_UART.
 * 
 * 
 */
/* The address of the ALT_UART_RBR_THR_DLL register for the ALT_UART0 instance. */
#define ALT_UART0_RBR_THR_DLL_ADDR  ALT_UART_RBR_THR_DLL_ADDR(ALT_UART0_ADDR)
/* The address of the ALT_UART_IER_DLH register for the ALT_UART0 instance. */
#define ALT_UART0_IER_DLH_ADDR  ALT_UART_IER_DLH_ADDR(ALT_UART0_ADDR)
/* The address of the ALT_UART_IIR register for the ALT_UART0 instance. */
#define ALT_UART0_IIR_ADDR  ALT_UART_IIR_ADDR(ALT_UART0_ADDR)
/* The address of the ALT_UART_FCR register for the ALT_UART0 instance. */
#define ALT_UART0_FCR_ADDR  ALT_UART_FCR_ADDR(ALT_UART0_ADDR)
/* The address of the ALT_UART_LCR register for the ALT_UART0 instance. */
#define ALT_UART0_LCR_ADDR  ALT_UART_LCR_ADDR(ALT_UART0_ADDR)
/* The address of the ALT_UART_MCR register for the ALT_UART0 instance. */
#define ALT_UART0_MCR_ADDR  ALT_UART_MCR_ADDR(ALT_UART0_ADDR)
/* The address of the ALT_UART_LSR register for the ALT_UART0 instance. */
#define ALT_UART0_LSR_ADDR  ALT_UART_LSR_ADDR(ALT_UART0_ADDR)
/* The address of the ALT_UART_MSR register for the ALT_UART0 instance. */
#define ALT_UART0_MSR_ADDR  ALT_UART_MSR_ADDR(ALT_UART0_ADDR)
/* The address of the ALT_UART_SCR register for the ALT_UART0 instance. */
#define ALT_UART0_SCR_ADDR  ALT_UART_SCR_ADDR(ALT_UART0_ADDR)
/* The address of the ALT_UART_SRBR register for the ALT_UART0 instance. */
#define ALT_UART0_SRBR_ADDR  ALT_UART_SRBR_ADDR(ALT_UART0_ADDR)
/* The address of the ALT_UART_STHR register for the ALT_UART0 instance. */
#define ALT_UART0_STHR_ADDR  ALT_UART_STHR_ADDR(ALT_UART0_ADDR)
/* The address of the ALT_UART_FAR register for the ALT_UART0 instance. */
#define ALT_UART0_FAR_ADDR  ALT_UART_FAR_ADDR(ALT_UART0_ADDR)
/* The address of the ALT_UART_TFR register for the ALT_UART0 instance. */
#define ALT_UART0_TFR_ADDR  ALT_UART_TFR_ADDR(ALT_UART0_ADDR)
/* The address of the ALT_UART_RFW register for the ALT_UART0 instance. */
#define ALT_UART0_RFW_ADDR  ALT_UART_RFW_ADDR(ALT_UART0_ADDR)
/* The address of the ALT_UART_USR register for the ALT_UART0 instance. */
#define ALT_UART0_USR_ADDR  ALT_UART_USR_ADDR(ALT_UART0_ADDR)
/* The address of the ALT_UART_TFL register for the ALT_UART0 instance. */
#define ALT_UART0_TFL_ADDR  ALT_UART_TFL_ADDR(ALT_UART0_ADDR)
/* The address of the ALT_UART_RFL register for the ALT_UART0 instance. */
#define ALT_UART0_RFL_ADDR  ALT_UART_RFL_ADDR(ALT_UART0_ADDR)
/* The address of the ALT_UART_SRR register for the ALT_UART0 instance. */
#define ALT_UART0_SRR_ADDR  ALT_UART_SRR_ADDR(ALT_UART0_ADDR)
/* The address of the ALT_UART_SRTS register for the ALT_UART0 instance. */
#define ALT_UART0_SRTS_ADDR  ALT_UART_SRTS_ADDR(ALT_UART0_ADDR)
/* The address of the ALT_UART_SBCR register for the ALT_UART0 instance. */
#define ALT_UART0_SBCR_ADDR  ALT_UART_SBCR_ADDR(ALT_UART0_ADDR)
/* The address of the ALT_UART_SDMAM register for the ALT_UART0 instance. */
#define ALT_UART0_SDMAM_ADDR  ALT_UART_SDMAM_ADDR(ALT_UART0_ADDR)
/* The address of the ALT_UART_SFE register for the ALT_UART0 instance. */
#define ALT_UART0_SFE_ADDR  ALT_UART_SFE_ADDR(ALT_UART0_ADDR)
/* The address of the ALT_UART_SRT register for the ALT_UART0 instance. */
#define ALT_UART0_SRT_ADDR  ALT_UART_SRT_ADDR(ALT_UART0_ADDR)
/* The address of the ALT_UART_STET register for the ALT_UART0 instance. */
#define ALT_UART0_STET_ADDR  ALT_UART_STET_ADDR(ALT_UART0_ADDR)
/* The address of the ALT_UART_HTX register for the ALT_UART0 instance. */
#define ALT_UART0_HTX_ADDR  ALT_UART_HTX_ADDR(ALT_UART0_ADDR)
/* The address of the ALT_UART_DMASA register for the ALT_UART0 instance. */
#define ALT_UART0_DMASA_ADDR  ALT_UART_DMASA_ADDR(ALT_UART0_ADDR)
/* The address of the ALT_UART_CPR register for the ALT_UART0 instance. */
#define ALT_UART0_CPR_ADDR  ALT_UART_CPR_ADDR(ALT_UART0_ADDR)
/* The address of the ALT_UART_UCV register for the ALT_UART0 instance. */
#define ALT_UART0_UCV_ADDR  ALT_UART_UCV_ADDR(ALT_UART0_ADDR)
/* The address of the ALT_UART_CTR register for the ALT_UART0 instance. */
#define ALT_UART0_CTR_ADDR  ALT_UART_CTR_ADDR(ALT_UART0_ADDR)
/* The base address byte offset for the start of the ALT_UART0 component. */
#define ALT_UART0_OFST        0xffc02000
/* The start address of the ALT_UART0 component. */
#define ALT_UART0_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_HPS_ADDR) + ALT_UART0_OFST))
/* The lower bound address range of the ALT_UART0 component. */
#define ALT_UART0_LB_ADDR     ALT_UART0_ADDR
/* The upper bound address range of the ALT_UART0 component. */
#define ALT_UART0_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_UART0_ADDR) + 0x100) - 1))


/*
 * Component Instance : uart1
 * 
 * Instance uart1 of component ALT_UART.
 * 
 * 
 */
/* The address of the ALT_UART_RBR_THR_DLL register for the ALT_UART1 instance. */
#define ALT_UART1_RBR_THR_DLL_ADDR  ALT_UART_RBR_THR_DLL_ADDR(ALT_UART1_ADDR)
/* The address of the ALT_UART_IER_DLH register for the ALT_UART1 instance. */
#define ALT_UART1_IER_DLH_ADDR  ALT_UART_IER_DLH_ADDR(ALT_UART1_ADDR)
/* The address of the ALT_UART_IIR register for the ALT_UART1 instance. */
#define ALT_UART1_IIR_ADDR  ALT_UART_IIR_ADDR(ALT_UART1_ADDR)
/* The address of the ALT_UART_FCR register for the ALT_UART1 instance. */
#define ALT_UART1_FCR_ADDR  ALT_UART_FCR_ADDR(ALT_UART1_ADDR)
/* The address of the ALT_UART_LCR register for the ALT_UART1 instance. */
#define ALT_UART1_LCR_ADDR  ALT_UART_LCR_ADDR(ALT_UART1_ADDR)
/* The address of the ALT_UART_MCR register for the ALT_UART1 instance. */
#define ALT_UART1_MCR_ADDR  ALT_UART_MCR_ADDR(ALT_UART1_ADDR)
/* The address of the ALT_UART_LSR register for the ALT_UART1 instance. */
#define ALT_UART1_LSR_ADDR  ALT_UART_LSR_ADDR(ALT_UART1_ADDR)
/* The address of the ALT_UART_MSR register for the ALT_UART1 instance. */
#define ALT_UART1_MSR_ADDR  ALT_UART_MSR_ADDR(ALT_UART1_ADDR)
/* The address of the ALT_UART_SCR register for the ALT_UART1 instance. */
#define ALT_UART1_SCR_ADDR  ALT_UART_SCR_ADDR(ALT_UART1_ADDR)
/* The address of the ALT_UART_SRBR register for the ALT_UART1 instance. */
#define ALT_UART1_SRBR_ADDR  ALT_UART_SRBR_ADDR(ALT_UART1_ADDR)
/* The address of the ALT_UART_STHR register for the ALT_UART1 instance. */
#define ALT_UART1_STHR_ADDR  ALT_UART_STHR_ADDR(ALT_UART1_ADDR)
/* The address of the ALT_UART_FAR register for the ALT_UART1 instance. */
#define ALT_UART1_FAR_ADDR  ALT_UART_FAR_ADDR(ALT_UART1_ADDR)
/* The address of the ALT_UART_TFR register for the ALT_UART1 instance. */
#define ALT_UART1_TFR_ADDR  ALT_UART_TFR_ADDR(ALT_UART1_ADDR)
/* The address of the ALT_UART_RFW register for the ALT_UART1 instance. */
#define ALT_UART1_RFW_ADDR  ALT_UART_RFW_ADDR(ALT_UART1_ADDR)
/* The address of the ALT_UART_USR register for the ALT_UART1 instance. */
#define ALT_UART1_USR_ADDR  ALT_UART_USR_ADDR(ALT_UART1_ADDR)
/* The address of the ALT_UART_TFL register for the ALT_UART1 instance. */
#define ALT_UART1_TFL_ADDR  ALT_UART_TFL_ADDR(ALT_UART1_ADDR)
/* The address of the ALT_UART_RFL register for the ALT_UART1 instance. */
#define ALT_UART1_RFL_ADDR  ALT_UART_RFL_ADDR(ALT_UART1_ADDR)
/* The address of the ALT_UART_SRR register for the ALT_UART1 instance. */
#define ALT_UART1_SRR_ADDR  ALT_UART_SRR_ADDR(ALT_UART1_ADDR)
/* The address of the ALT_UART_SRTS register for the ALT_UART1 instance. */
#define ALT_UART1_SRTS_ADDR  ALT_UART_SRTS_ADDR(ALT_UART1_ADDR)
/* The address of the ALT_UART_SBCR register for the ALT_UART1 instance. */
#define ALT_UART1_SBCR_ADDR  ALT_UART_SBCR_ADDR(ALT_UART1_ADDR)
/* The address of the ALT_UART_SDMAM register for the ALT_UART1 instance. */
#define ALT_UART1_SDMAM_ADDR  ALT_UART_SDMAM_ADDR(ALT_UART1_ADDR)
/* The address of the ALT_UART_SFE register for the ALT_UART1 instance. */
#define ALT_UART1_SFE_ADDR  ALT_UART_SFE_ADDR(ALT_UART1_ADDR)
/* The address of the ALT_UART_SRT register for the ALT_UART1 instance. */
#define ALT_UART1_SRT_ADDR  ALT_UART_SRT_ADDR(ALT_UART1_ADDR)
/* The address of the ALT_UART_STET register for the ALT_UART1 instance. */
#define ALT_UART1_STET_ADDR  ALT_UART_STET_ADDR(ALT_UART1_ADDR)
/* The address of the ALT_UART_HTX register for the ALT_UART1 instance. */
#define ALT_UART1_HTX_ADDR  ALT_UART_HTX_ADDR(ALT_UART1_ADDR)
/* The address of the ALT_UART_DMASA register for the ALT_UART1 instance. */
#define ALT_UART1_DMASA_ADDR  ALT_UART_DMASA_ADDR(ALT_UART1_ADDR)
/* The address of the ALT_UART_CPR register for the ALT_UART1 instance. */
#define ALT_UART1_CPR_ADDR  ALT_UART_CPR_ADDR(ALT_UART1_ADDR)
/* The address of the ALT_UART_UCV register for the ALT_UART1 instance. */
#define ALT_UART1_UCV_ADDR  ALT_UART_UCV_ADDR(ALT_UART1_ADDR)
/* The address of the ALT_UART_CTR register for the ALT_UART1 instance. */
#define ALT_UART1_CTR_ADDR  ALT_UART_CTR_ADDR(ALT_UART1_ADDR)
/* The base address byte offset for the start of the ALT_UART1 component. */
#define ALT_UART1_OFST        0xffc03000
/* The start address of the ALT_UART1 component. */
#define ALT_UART1_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_HPS_ADDR) + ALT_UART1_OFST))
/* The lower bound address range of the ALT_UART1 component. */
#define ALT_UART1_LB_ADDR     ALT_UART1_ADDR
/* The upper bound address range of the ALT_UART1 component. */
#define ALT_UART1_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_UART1_ADDR) + 0x100) - 1))


/*
 * Component Instance : i2c0
 * 
 * Instance i2c0 of component ALT_I2C.
 * 
 * 
 */
/* The address of the ALT_I2C_CON register for the ALT_I2C0 instance. */
#define ALT_I2C0_IC_CON_ADDR  ALT_I2C_CON_ADDR(ALT_I2C0_ADDR)
/* The address of the ALT_I2C_TAR register for the ALT_I2C0 instance. */
#define ALT_I2C0_IC_TAR_ADDR  ALT_I2C_TAR_ADDR(ALT_I2C0_ADDR)
/* The address of the ALT_I2C_SAR register for the ALT_I2C0 instance. */
#define ALT_I2C0_IC_SAR_ADDR  ALT_I2C_SAR_ADDR(ALT_I2C0_ADDR)
/* The address of the ALT_I2C_DATA_CMD register for the ALT_I2C0 instance. */
#define ALT_I2C0_IC_DATA_CMD_ADDR  ALT_I2C_DATA_CMD_ADDR(ALT_I2C0_ADDR)
/* The address of the ALT_I2C_SS_SCL_HCNT register for the ALT_I2C0 instance. */
#define ALT_I2C0_IC_SS_SCL_HCNT_ADDR  ALT_I2C_SS_SCL_HCNT_ADDR(ALT_I2C0_ADDR)
/* The address of the ALT_I2C_SS_SCL_LCNT register for the ALT_I2C0 instance. */
#define ALT_I2C0_IC_SS_SCL_LCNT_ADDR  ALT_I2C_SS_SCL_LCNT_ADDR(ALT_I2C0_ADDR)
/* The address of the ALT_I2C_FS_SCL_HCNT register for the ALT_I2C0 instance. */
#define ALT_I2C0_IC_FS_SCL_HCNT_ADDR  ALT_I2C_FS_SCL_HCNT_ADDR(ALT_I2C0_ADDR)
/* The address of the ALT_I2C_FS_SCL_LCNT register for the ALT_I2C0 instance. */
#define ALT_I2C0_IC_FS_SCL_LCNT_ADDR  ALT_I2C_FS_SCL_LCNT_ADDR(ALT_I2C0_ADDR)
/* The address of the ALT_I2C_INTR_STAT register for the ALT_I2C0 instance. */
#define ALT_I2C0_IC_INTR_STAT_ADDR  ALT_I2C_INTR_STAT_ADDR(ALT_I2C0_ADDR)
/* The address of the ALT_I2C_INTR_MSK register for the ALT_I2C0 instance. */
#define ALT_I2C0_IC_INTR_MSK_ADDR  ALT_I2C_INTR_MSK_ADDR(ALT_I2C0_ADDR)
/* The address of the ALT_I2C_RAW_INTR_STAT register for the ALT_I2C0 instance. */
#define ALT_I2C0_IC_RAW_INTR_STAT_ADDR  ALT_I2C_RAW_INTR_STAT_ADDR(ALT_I2C0_ADDR)
/* The address of the ALT_I2C_RX_TL register for the ALT_I2C0 instance. */
#define ALT_I2C0_IC_RX_TL_ADDR  ALT_I2C_RX_TL_ADDR(ALT_I2C0_ADDR)
/* The address of the ALT_I2C_TX_TL register for the ALT_I2C0 instance. */
#define ALT_I2C0_IC_TX_TL_ADDR  ALT_I2C_TX_TL_ADDR(ALT_I2C0_ADDR)
/* The address of the ALT_I2C_CLR_INTR register for the ALT_I2C0 instance. */
#define ALT_I2C0_IC_CLR_INTR_ADDR  ALT_I2C_CLR_INTR_ADDR(ALT_I2C0_ADDR)
/* The address of the ALT_I2C_CLR_RX_UNDER register for the ALT_I2C0 instance. */
#define ALT_I2C0_IC_CLR_RX_UNDER_ADDR  ALT_I2C_CLR_RX_UNDER_ADDR(ALT_I2C0_ADDR)
/* The address of the ALT_I2C_CLR_RX_OVER register for the ALT_I2C0 instance. */
#define ALT_I2C0_IC_CLR_RX_OVER_ADDR  ALT_I2C_CLR_RX_OVER_ADDR(ALT_I2C0_ADDR)
/* The address of the ALT_I2C_CLR_TX_OVER register for the ALT_I2C0 instance. */
#define ALT_I2C0_IC_CLR_TX_OVER_ADDR  ALT_I2C_CLR_TX_OVER_ADDR(ALT_I2C0_ADDR)
/* The address of the ALT_I2C_CLR_RD_REQ register for the ALT_I2C0 instance. */
#define ALT_I2C0_IC_CLR_RD_REQ_ADDR  ALT_I2C_CLR_RD_REQ_ADDR(ALT_I2C0_ADDR)
/* The address of the ALT_I2C_CLR_TX_ABRT register for the ALT_I2C0 instance. */
#define ALT_I2C0_IC_CLR_TX_ABRT_ADDR  ALT_I2C_CLR_TX_ABRT_ADDR(ALT_I2C0_ADDR)
/* The address of the ALT_I2C_CLR_RX_DONE register for the ALT_I2C0 instance. */
#define ALT_I2C0_IC_CLR_RX_DONE_ADDR  ALT_I2C_CLR_RX_DONE_ADDR(ALT_I2C0_ADDR)
/* The address of the ALT_I2C_CLR_ACTIVITY register for the ALT_I2C0 instance. */
#define ALT_I2C0_IC_CLR_ACTIVITY_ADDR  ALT_I2C_CLR_ACTIVITY_ADDR(ALT_I2C0_ADDR)
/* The address of the ALT_I2C_CLR_STOP_DET register for the ALT_I2C0 instance. */
#define ALT_I2C0_IC_CLR_STOP_DET_ADDR  ALT_I2C_CLR_STOP_DET_ADDR(ALT_I2C0_ADDR)
/* The address of the ALT_I2C_CLR_START_DET register for the ALT_I2C0 instance. */
#define ALT_I2C0_IC_CLR_START_DET_ADDR  ALT_I2C_CLR_START_DET_ADDR(ALT_I2C0_ADDR)
/* The address of the ALT_I2C_CLR_GEN_CALL register for the ALT_I2C0 instance. */
#define ALT_I2C0_IC_CLR_GEN_CALL_ADDR  ALT_I2C_CLR_GEN_CALL_ADDR(ALT_I2C0_ADDR)
/* The address of the ALT_I2C_EN register for the ALT_I2C0 instance. */
#define ALT_I2C0_IC_EN_ADDR  ALT_I2C_EN_ADDR(ALT_I2C0_ADDR)
/* The address of the ALT_I2C_STAT register for the ALT_I2C0 instance. */
#define ALT_I2C0_IC_STAT_ADDR  ALT_I2C_STAT_ADDR(ALT_I2C0_ADDR)
/* The address of the ALT_I2C_TXFLR register for the ALT_I2C0 instance. */
#define ALT_I2C0_IC_TXFLR_ADDR  ALT_I2C_TXFLR_ADDR(ALT_I2C0_ADDR)
/* The address of the ALT_I2C_RXFLR register for the ALT_I2C0 instance. */
#define ALT_I2C0_IC_RXFLR_ADDR  ALT_I2C_RXFLR_ADDR(ALT_I2C0_ADDR)
/* The address of the ALT_I2C_SDA_HOLD register for the ALT_I2C0 instance. */
#define ALT_I2C0_IC_SDA_HOLD_ADDR  ALT_I2C_SDA_HOLD_ADDR(ALT_I2C0_ADDR)
/* The address of the ALT_I2C_TX_ABRT_SRC register for the ALT_I2C0 instance. */
#define ALT_I2C0_IC_TX_ABRT_SRC_ADDR  ALT_I2C_TX_ABRT_SRC_ADDR(ALT_I2C0_ADDR)
/* The address of the ALT_I2C_SLV_DATA_NACK_ONLY register for the ALT_I2C0 instance. */
#define ALT_I2C0_IC_SLV_DATA_NACK_ONLY_ADDR  ALT_I2C_SLV_DATA_NACK_ONLY_ADDR(ALT_I2C0_ADDR)
/* The address of the ALT_I2C_DMA_CR register for the ALT_I2C0 instance. */
#define ALT_I2C0_IC_DMA_CR_ADDR  ALT_I2C_DMA_CR_ADDR(ALT_I2C0_ADDR)
/* The address of the ALT_I2C_DMA_TDLR register for the ALT_I2C0 instance. */
#define ALT_I2C0_IC_DMA_TDLR_ADDR  ALT_I2C_DMA_TDLR_ADDR(ALT_I2C0_ADDR)
/* The address of the ALT_I2C_DMA_RDLR register for the ALT_I2C0 instance. */
#define ALT_I2C0_IC_DMA_RDLR_ADDR  ALT_I2C_DMA_RDLR_ADDR(ALT_I2C0_ADDR)
/* The address of the ALT_I2C_SDA_SETUP register for the ALT_I2C0 instance. */
#define ALT_I2C0_IC_SDA_SETUP_ADDR  ALT_I2C_SDA_SETUP_ADDR(ALT_I2C0_ADDR)
/* The address of the ALT_I2C_ACK_GENERAL_CALL register for the ALT_I2C0 instance. */
#define ALT_I2C0_IC_ACK_GENERAL_CALL_ADDR  ALT_I2C_ACK_GENERAL_CALL_ADDR(ALT_I2C0_ADDR)
/* The address of the ALT_I2C_EN_STAT register for the ALT_I2C0 instance. */
#define ALT_I2C0_IC_EN_STAT_ADDR  ALT_I2C_EN_STAT_ADDR(ALT_I2C0_ADDR)
/* The address of the ALT_I2C_FS_SPKLEN register for the ALT_I2C0 instance. */
#define ALT_I2C0_IC_FS_SPKLEN_ADDR  ALT_I2C_FS_SPKLEN_ADDR(ALT_I2C0_ADDR)
/* The address of the ALT_I2C_COMP_PARAM_1 register for the ALT_I2C0 instance. */
#define ALT_I2C0_IC_COMP_PARAM_1_ADDR  ALT_I2C_COMP_PARAM_1_ADDR(ALT_I2C0_ADDR)
/* The address of the ALT_I2C_COMP_VER register for the ALT_I2C0 instance. */
#define ALT_I2C0_IC_COMP_VER_ADDR  ALT_I2C_COMP_VER_ADDR(ALT_I2C0_ADDR)
/* The address of the ALT_I2C_COMP_TYPE register for the ALT_I2C0 instance. */
#define ALT_I2C0_IC_COMP_TYPE_ADDR  ALT_I2C_COMP_TYPE_ADDR(ALT_I2C0_ADDR)
/* The base address byte offset for the start of the ALT_I2C0 component. */
#define ALT_I2C0_OFST        0xffc04000
/* The start address of the ALT_I2C0 component. */
#define ALT_I2C0_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_HPS_ADDR) + ALT_I2C0_OFST))
/* The lower bound address range of the ALT_I2C0 component. */
#define ALT_I2C0_LB_ADDR     ALT_I2C0_ADDR
/* The upper bound address range of the ALT_I2C0 component. */
#define ALT_I2C0_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_I2C0_ADDR) + 0x100) - 1))


/*
 * Component Instance : i2c1
 * 
 * Instance i2c1 of component ALT_I2C.
 * 
 * 
 */
/* The address of the ALT_I2C_CON register for the ALT_I2C1 instance. */
#define ALT_I2C1_IC_CON_ADDR  ALT_I2C_CON_ADDR(ALT_I2C1_ADDR)
/* The address of the ALT_I2C_TAR register for the ALT_I2C1 instance. */
#define ALT_I2C1_IC_TAR_ADDR  ALT_I2C_TAR_ADDR(ALT_I2C1_ADDR)
/* The address of the ALT_I2C_SAR register for the ALT_I2C1 instance. */
#define ALT_I2C1_IC_SAR_ADDR  ALT_I2C_SAR_ADDR(ALT_I2C1_ADDR)
/* The address of the ALT_I2C_DATA_CMD register for the ALT_I2C1 instance. */
#define ALT_I2C1_IC_DATA_CMD_ADDR  ALT_I2C_DATA_CMD_ADDR(ALT_I2C1_ADDR)
/* The address of the ALT_I2C_SS_SCL_HCNT register for the ALT_I2C1 instance. */
#define ALT_I2C1_IC_SS_SCL_HCNT_ADDR  ALT_I2C_SS_SCL_HCNT_ADDR(ALT_I2C1_ADDR)
/* The address of the ALT_I2C_SS_SCL_LCNT register for the ALT_I2C1 instance. */
#define ALT_I2C1_IC_SS_SCL_LCNT_ADDR  ALT_I2C_SS_SCL_LCNT_ADDR(ALT_I2C1_ADDR)
/* The address of the ALT_I2C_FS_SCL_HCNT register for the ALT_I2C1 instance. */
#define ALT_I2C1_IC_FS_SCL_HCNT_ADDR  ALT_I2C_FS_SCL_HCNT_ADDR(ALT_I2C1_ADDR)
/* The address of the ALT_I2C_FS_SCL_LCNT register for the ALT_I2C1 instance. */
#define ALT_I2C1_IC_FS_SCL_LCNT_ADDR  ALT_I2C_FS_SCL_LCNT_ADDR(ALT_I2C1_ADDR)
/* The address of the ALT_I2C_INTR_STAT register for the ALT_I2C1 instance. */
#define ALT_I2C1_IC_INTR_STAT_ADDR  ALT_I2C_INTR_STAT_ADDR(ALT_I2C1_ADDR)
/* The address of the ALT_I2C_INTR_MSK register for the ALT_I2C1 instance. */
#define ALT_I2C1_IC_INTR_MSK_ADDR  ALT_I2C_INTR_MSK_ADDR(ALT_I2C1_ADDR)
/* The address of the ALT_I2C_RAW_INTR_STAT register for the ALT_I2C1 instance. */
#define ALT_I2C1_IC_RAW_INTR_STAT_ADDR  ALT_I2C_RAW_INTR_STAT_ADDR(ALT_I2C1_ADDR)
/* The address of the ALT_I2C_RX_TL register for the ALT_I2C1 instance. */
#define ALT_I2C1_IC_RX_TL_ADDR  ALT_I2C_RX_TL_ADDR(ALT_I2C1_ADDR)
/* The address of the ALT_I2C_TX_TL register for the ALT_I2C1 instance. */
#define ALT_I2C1_IC_TX_TL_ADDR  ALT_I2C_TX_TL_ADDR(ALT_I2C1_ADDR)
/* The address of the ALT_I2C_CLR_INTR register for the ALT_I2C1 instance. */
#define ALT_I2C1_IC_CLR_INTR_ADDR  ALT_I2C_CLR_INTR_ADDR(ALT_I2C1_ADDR)
/* The address of the ALT_I2C_CLR_RX_UNDER register for the ALT_I2C1 instance. */
#define ALT_I2C1_IC_CLR_RX_UNDER_ADDR  ALT_I2C_CLR_RX_UNDER_ADDR(ALT_I2C1_ADDR)
/* The address of the ALT_I2C_CLR_RX_OVER register for the ALT_I2C1 instance. */
#define ALT_I2C1_IC_CLR_RX_OVER_ADDR  ALT_I2C_CLR_RX_OVER_ADDR(ALT_I2C1_ADDR)
/* The address of the ALT_I2C_CLR_TX_OVER register for the ALT_I2C1 instance. */
#define ALT_I2C1_IC_CLR_TX_OVER_ADDR  ALT_I2C_CLR_TX_OVER_ADDR(ALT_I2C1_ADDR)
/* The address of the ALT_I2C_CLR_RD_REQ register for the ALT_I2C1 instance. */
#define ALT_I2C1_IC_CLR_RD_REQ_ADDR  ALT_I2C_CLR_RD_REQ_ADDR(ALT_I2C1_ADDR)
/* The address of the ALT_I2C_CLR_TX_ABRT register for the ALT_I2C1 instance. */
#define ALT_I2C1_IC_CLR_TX_ABRT_ADDR  ALT_I2C_CLR_TX_ABRT_ADDR(ALT_I2C1_ADDR)
/* The address of the ALT_I2C_CLR_RX_DONE register for the ALT_I2C1 instance. */
#define ALT_I2C1_IC_CLR_RX_DONE_ADDR  ALT_I2C_CLR_RX_DONE_ADDR(ALT_I2C1_ADDR)
/* The address of the ALT_I2C_CLR_ACTIVITY register for the ALT_I2C1 instance. */
#define ALT_I2C1_IC_CLR_ACTIVITY_ADDR  ALT_I2C_CLR_ACTIVITY_ADDR(ALT_I2C1_ADDR)
/* The address of the ALT_I2C_CLR_STOP_DET register for the ALT_I2C1 instance. */
#define ALT_I2C1_IC_CLR_STOP_DET_ADDR  ALT_I2C_CLR_STOP_DET_ADDR(ALT_I2C1_ADDR)
/* The address of the ALT_I2C_CLR_START_DET register for the ALT_I2C1 instance. */
#define ALT_I2C1_IC_CLR_START_DET_ADDR  ALT_I2C_CLR_START_DET_ADDR(ALT_I2C1_ADDR)
/* The address of the ALT_I2C_CLR_GEN_CALL register for the ALT_I2C1 instance. */
#define ALT_I2C1_IC_CLR_GEN_CALL_ADDR  ALT_I2C_CLR_GEN_CALL_ADDR(ALT_I2C1_ADDR)
/* The address of the ALT_I2C_EN register for the ALT_I2C1 instance. */
#define ALT_I2C1_IC_EN_ADDR  ALT_I2C_EN_ADDR(ALT_I2C1_ADDR)
/* The address of the ALT_I2C_STAT register for the ALT_I2C1 instance. */
#define ALT_I2C1_IC_STAT_ADDR  ALT_I2C_STAT_ADDR(ALT_I2C1_ADDR)
/* The address of the ALT_I2C_TXFLR register for the ALT_I2C1 instance. */
#define ALT_I2C1_IC_TXFLR_ADDR  ALT_I2C_TXFLR_ADDR(ALT_I2C1_ADDR)
/* The address of the ALT_I2C_RXFLR register for the ALT_I2C1 instance. */
#define ALT_I2C1_IC_RXFLR_ADDR  ALT_I2C_RXFLR_ADDR(ALT_I2C1_ADDR)
/* The address of the ALT_I2C_SDA_HOLD register for the ALT_I2C1 instance. */
#define ALT_I2C1_IC_SDA_HOLD_ADDR  ALT_I2C_SDA_HOLD_ADDR(ALT_I2C1_ADDR)
/* The address of the ALT_I2C_TX_ABRT_SRC register for the ALT_I2C1 instance. */
#define ALT_I2C1_IC_TX_ABRT_SRC_ADDR  ALT_I2C_TX_ABRT_SRC_ADDR(ALT_I2C1_ADDR)
/* The address of the ALT_I2C_SLV_DATA_NACK_ONLY register for the ALT_I2C1 instance. */
#define ALT_I2C1_IC_SLV_DATA_NACK_ONLY_ADDR  ALT_I2C_SLV_DATA_NACK_ONLY_ADDR(ALT_I2C1_ADDR)
/* The address of the ALT_I2C_DMA_CR register for the ALT_I2C1 instance. */
#define ALT_I2C1_IC_DMA_CR_ADDR  ALT_I2C_DMA_CR_ADDR(ALT_I2C1_ADDR)
/* The address of the ALT_I2C_DMA_TDLR register for the ALT_I2C1 instance. */
#define ALT_I2C1_IC_DMA_TDLR_ADDR  ALT_I2C_DMA_TDLR_ADDR(ALT_I2C1_ADDR)
/* The address of the ALT_I2C_DMA_RDLR register for the ALT_I2C1 instance. */
#define ALT_I2C1_IC_DMA_RDLR_ADDR  ALT_I2C_DMA_RDLR_ADDR(ALT_I2C1_ADDR)
/* The address of the ALT_I2C_SDA_SETUP register for the ALT_I2C1 instance. */
#define ALT_I2C1_IC_SDA_SETUP_ADDR  ALT_I2C_SDA_SETUP_ADDR(ALT_I2C1_ADDR)
/* The address of the ALT_I2C_ACK_GENERAL_CALL register for the ALT_I2C1 instance. */
#define ALT_I2C1_IC_ACK_GENERAL_CALL_ADDR  ALT_I2C_ACK_GENERAL_CALL_ADDR(ALT_I2C1_ADDR)
/* The address of the ALT_I2C_EN_STAT register for the ALT_I2C1 instance. */
#define ALT_I2C1_IC_EN_STAT_ADDR  ALT_I2C_EN_STAT_ADDR(ALT_I2C1_ADDR)
/* The address of the ALT_I2C_FS_SPKLEN register for the ALT_I2C1 instance. */
#define ALT_I2C1_IC_FS_SPKLEN_ADDR  ALT_I2C_FS_SPKLEN_ADDR(ALT_I2C1_ADDR)
/* The address of the ALT_I2C_COMP_PARAM_1 register for the ALT_I2C1 instance. */
#define ALT_I2C1_IC_COMP_PARAM_1_ADDR  ALT_I2C_COMP_PARAM_1_ADDR(ALT_I2C1_ADDR)
/* The address of the ALT_I2C_COMP_VER register for the ALT_I2C1 instance. */
#define ALT_I2C1_IC_COMP_VER_ADDR  ALT_I2C_COMP_VER_ADDR(ALT_I2C1_ADDR)
/* The address of the ALT_I2C_COMP_TYPE register for the ALT_I2C1 instance. */
#define ALT_I2C1_IC_COMP_TYPE_ADDR  ALT_I2C_COMP_TYPE_ADDR(ALT_I2C1_ADDR)
/* The base address byte offset for the start of the ALT_I2C1 component. */
#define ALT_I2C1_OFST        0xffc05000
/* The start address of the ALT_I2C1 component. */
#define ALT_I2C1_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_HPS_ADDR) + ALT_I2C1_OFST))
/* The lower bound address range of the ALT_I2C1 component. */
#define ALT_I2C1_LB_ADDR     ALT_I2C1_ADDR
/* The upper bound address range of the ALT_I2C1 component. */
#define ALT_I2C1_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_I2C1_ADDR) + 0x100) - 1))


/*
 * Component Instance : i2c2
 * 
 * Instance i2c2 of component ALT_I2C.
 * 
 * 
 */
/* The address of the ALT_I2C_CON register for the ALT_I2C2 instance. */
#define ALT_I2C2_IC_CON_ADDR  ALT_I2C_CON_ADDR(ALT_I2C2_ADDR)
/* The address of the ALT_I2C_TAR register for the ALT_I2C2 instance. */
#define ALT_I2C2_IC_TAR_ADDR  ALT_I2C_TAR_ADDR(ALT_I2C2_ADDR)
/* The address of the ALT_I2C_SAR register for the ALT_I2C2 instance. */
#define ALT_I2C2_IC_SAR_ADDR  ALT_I2C_SAR_ADDR(ALT_I2C2_ADDR)
/* The address of the ALT_I2C_DATA_CMD register for the ALT_I2C2 instance. */
#define ALT_I2C2_IC_DATA_CMD_ADDR  ALT_I2C_DATA_CMD_ADDR(ALT_I2C2_ADDR)
/* The address of the ALT_I2C_SS_SCL_HCNT register for the ALT_I2C2 instance. */
#define ALT_I2C2_IC_SS_SCL_HCNT_ADDR  ALT_I2C_SS_SCL_HCNT_ADDR(ALT_I2C2_ADDR)
/* The address of the ALT_I2C_SS_SCL_LCNT register for the ALT_I2C2 instance. */
#define ALT_I2C2_IC_SS_SCL_LCNT_ADDR  ALT_I2C_SS_SCL_LCNT_ADDR(ALT_I2C2_ADDR)
/* The address of the ALT_I2C_FS_SCL_HCNT register for the ALT_I2C2 instance. */
#define ALT_I2C2_IC_FS_SCL_HCNT_ADDR  ALT_I2C_FS_SCL_HCNT_ADDR(ALT_I2C2_ADDR)
/* The address of the ALT_I2C_FS_SCL_LCNT register for the ALT_I2C2 instance. */
#define ALT_I2C2_IC_FS_SCL_LCNT_ADDR  ALT_I2C_FS_SCL_LCNT_ADDR(ALT_I2C2_ADDR)
/* The address of the ALT_I2C_INTR_STAT register for the ALT_I2C2 instance. */
#define ALT_I2C2_IC_INTR_STAT_ADDR  ALT_I2C_INTR_STAT_ADDR(ALT_I2C2_ADDR)
/* The address of the ALT_I2C_INTR_MSK register for the ALT_I2C2 instance. */
#define ALT_I2C2_IC_INTR_MSK_ADDR  ALT_I2C_INTR_MSK_ADDR(ALT_I2C2_ADDR)
/* The address of the ALT_I2C_RAW_INTR_STAT register for the ALT_I2C2 instance. */
#define ALT_I2C2_IC_RAW_INTR_STAT_ADDR  ALT_I2C_RAW_INTR_STAT_ADDR(ALT_I2C2_ADDR)
/* The address of the ALT_I2C_RX_TL register for the ALT_I2C2 instance. */
#define ALT_I2C2_IC_RX_TL_ADDR  ALT_I2C_RX_TL_ADDR(ALT_I2C2_ADDR)
/* The address of the ALT_I2C_TX_TL register for the ALT_I2C2 instance. */
#define ALT_I2C2_IC_TX_TL_ADDR  ALT_I2C_TX_TL_ADDR(ALT_I2C2_ADDR)
/* The address of the ALT_I2C_CLR_INTR register for the ALT_I2C2 instance. */
#define ALT_I2C2_IC_CLR_INTR_ADDR  ALT_I2C_CLR_INTR_ADDR(ALT_I2C2_ADDR)
/* The address of the ALT_I2C_CLR_RX_UNDER register for the ALT_I2C2 instance. */
#define ALT_I2C2_IC_CLR_RX_UNDER_ADDR  ALT_I2C_CLR_RX_UNDER_ADDR(ALT_I2C2_ADDR)
/* The address of the ALT_I2C_CLR_RX_OVER register for the ALT_I2C2 instance. */
#define ALT_I2C2_IC_CLR_RX_OVER_ADDR  ALT_I2C_CLR_RX_OVER_ADDR(ALT_I2C2_ADDR)
/* The address of the ALT_I2C_CLR_TX_OVER register for the ALT_I2C2 instance. */
#define ALT_I2C2_IC_CLR_TX_OVER_ADDR  ALT_I2C_CLR_TX_OVER_ADDR(ALT_I2C2_ADDR)
/* The address of the ALT_I2C_CLR_RD_REQ register for the ALT_I2C2 instance. */
#define ALT_I2C2_IC_CLR_RD_REQ_ADDR  ALT_I2C_CLR_RD_REQ_ADDR(ALT_I2C2_ADDR)
/* The address of the ALT_I2C_CLR_TX_ABRT register for the ALT_I2C2 instance. */
#define ALT_I2C2_IC_CLR_TX_ABRT_ADDR  ALT_I2C_CLR_TX_ABRT_ADDR(ALT_I2C2_ADDR)
/* The address of the ALT_I2C_CLR_RX_DONE register for the ALT_I2C2 instance. */
#define ALT_I2C2_IC_CLR_RX_DONE_ADDR  ALT_I2C_CLR_RX_DONE_ADDR(ALT_I2C2_ADDR)
/* The address of the ALT_I2C_CLR_ACTIVITY register for the ALT_I2C2 instance. */
#define ALT_I2C2_IC_CLR_ACTIVITY_ADDR  ALT_I2C_CLR_ACTIVITY_ADDR(ALT_I2C2_ADDR)
/* The address of the ALT_I2C_CLR_STOP_DET register for the ALT_I2C2 instance. */
#define ALT_I2C2_IC_CLR_STOP_DET_ADDR  ALT_I2C_CLR_STOP_DET_ADDR(ALT_I2C2_ADDR)
/* The address of the ALT_I2C_CLR_START_DET register for the ALT_I2C2 instance. */
#define ALT_I2C2_IC_CLR_START_DET_ADDR  ALT_I2C_CLR_START_DET_ADDR(ALT_I2C2_ADDR)
/* The address of the ALT_I2C_CLR_GEN_CALL register for the ALT_I2C2 instance. */
#define ALT_I2C2_IC_CLR_GEN_CALL_ADDR  ALT_I2C_CLR_GEN_CALL_ADDR(ALT_I2C2_ADDR)
/* The address of the ALT_I2C_EN register for the ALT_I2C2 instance. */
#define ALT_I2C2_IC_EN_ADDR  ALT_I2C_EN_ADDR(ALT_I2C2_ADDR)
/* The address of the ALT_I2C_STAT register for the ALT_I2C2 instance. */
#define ALT_I2C2_IC_STAT_ADDR  ALT_I2C_STAT_ADDR(ALT_I2C2_ADDR)
/* The address of the ALT_I2C_TXFLR register for the ALT_I2C2 instance. */
#define ALT_I2C2_IC_TXFLR_ADDR  ALT_I2C_TXFLR_ADDR(ALT_I2C2_ADDR)
/* The address of the ALT_I2C_RXFLR register for the ALT_I2C2 instance. */
#define ALT_I2C2_IC_RXFLR_ADDR  ALT_I2C_RXFLR_ADDR(ALT_I2C2_ADDR)
/* The address of the ALT_I2C_SDA_HOLD register for the ALT_I2C2 instance. */
#define ALT_I2C2_IC_SDA_HOLD_ADDR  ALT_I2C_SDA_HOLD_ADDR(ALT_I2C2_ADDR)
/* The address of the ALT_I2C_TX_ABRT_SRC register for the ALT_I2C2 instance. */
#define ALT_I2C2_IC_TX_ABRT_SRC_ADDR  ALT_I2C_TX_ABRT_SRC_ADDR(ALT_I2C2_ADDR)
/* The address of the ALT_I2C_SLV_DATA_NACK_ONLY register for the ALT_I2C2 instance. */
#define ALT_I2C2_IC_SLV_DATA_NACK_ONLY_ADDR  ALT_I2C_SLV_DATA_NACK_ONLY_ADDR(ALT_I2C2_ADDR)
/* The address of the ALT_I2C_DMA_CR register for the ALT_I2C2 instance. */
#define ALT_I2C2_IC_DMA_CR_ADDR  ALT_I2C_DMA_CR_ADDR(ALT_I2C2_ADDR)
/* The address of the ALT_I2C_DMA_TDLR register for the ALT_I2C2 instance. */
#define ALT_I2C2_IC_DMA_TDLR_ADDR  ALT_I2C_DMA_TDLR_ADDR(ALT_I2C2_ADDR)
/* The address of the ALT_I2C_DMA_RDLR register for the ALT_I2C2 instance. */
#define ALT_I2C2_IC_DMA_RDLR_ADDR  ALT_I2C_DMA_RDLR_ADDR(ALT_I2C2_ADDR)
/* The address of the ALT_I2C_SDA_SETUP register for the ALT_I2C2 instance. */
#define ALT_I2C2_IC_SDA_SETUP_ADDR  ALT_I2C_SDA_SETUP_ADDR(ALT_I2C2_ADDR)
/* The address of the ALT_I2C_ACK_GENERAL_CALL register for the ALT_I2C2 instance. */
#define ALT_I2C2_IC_ACK_GENERAL_CALL_ADDR  ALT_I2C_ACK_GENERAL_CALL_ADDR(ALT_I2C2_ADDR)
/* The address of the ALT_I2C_EN_STAT register for the ALT_I2C2 instance. */
#define ALT_I2C2_IC_EN_STAT_ADDR  ALT_I2C_EN_STAT_ADDR(ALT_I2C2_ADDR)
/* The address of the ALT_I2C_FS_SPKLEN register for the ALT_I2C2 instance. */
#define ALT_I2C2_IC_FS_SPKLEN_ADDR  ALT_I2C_FS_SPKLEN_ADDR(ALT_I2C2_ADDR)
/* The address of the ALT_I2C_COMP_PARAM_1 register for the ALT_I2C2 instance. */
#define ALT_I2C2_IC_COMP_PARAM_1_ADDR  ALT_I2C_COMP_PARAM_1_ADDR(ALT_I2C2_ADDR)
/* The address of the ALT_I2C_COMP_VER register for the ALT_I2C2 instance. */
#define ALT_I2C2_IC_COMP_VER_ADDR  ALT_I2C_COMP_VER_ADDR(ALT_I2C2_ADDR)
/* The address of the ALT_I2C_COMP_TYPE register for the ALT_I2C2 instance. */
#define ALT_I2C2_IC_COMP_TYPE_ADDR  ALT_I2C_COMP_TYPE_ADDR(ALT_I2C2_ADDR)
/* The base address byte offset for the start of the ALT_I2C2 component. */
#define ALT_I2C2_OFST        0xffc06000
/* The start address of the ALT_I2C2 component. */
#define ALT_I2C2_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_HPS_ADDR) + ALT_I2C2_OFST))
/* The lower bound address range of the ALT_I2C2 component. */
#define ALT_I2C2_LB_ADDR     ALT_I2C2_ADDR
/* The upper bound address range of the ALT_I2C2 component. */
#define ALT_I2C2_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_I2C2_ADDR) + 0x100) - 1))


/*
 * Component Instance : i2c3
 * 
 * Instance i2c3 of component ALT_I2C.
 * 
 * 
 */
/* The address of the ALT_I2C_CON register for the ALT_I2C3 instance. */
#define ALT_I2C3_IC_CON_ADDR  ALT_I2C_CON_ADDR(ALT_I2C3_ADDR)
/* The address of the ALT_I2C_TAR register for the ALT_I2C3 instance. */
#define ALT_I2C3_IC_TAR_ADDR  ALT_I2C_TAR_ADDR(ALT_I2C3_ADDR)
/* The address of the ALT_I2C_SAR register for the ALT_I2C3 instance. */
#define ALT_I2C3_IC_SAR_ADDR  ALT_I2C_SAR_ADDR(ALT_I2C3_ADDR)
/* The address of the ALT_I2C_DATA_CMD register for the ALT_I2C3 instance. */
#define ALT_I2C3_IC_DATA_CMD_ADDR  ALT_I2C_DATA_CMD_ADDR(ALT_I2C3_ADDR)
/* The address of the ALT_I2C_SS_SCL_HCNT register for the ALT_I2C3 instance. */
#define ALT_I2C3_IC_SS_SCL_HCNT_ADDR  ALT_I2C_SS_SCL_HCNT_ADDR(ALT_I2C3_ADDR)
/* The address of the ALT_I2C_SS_SCL_LCNT register for the ALT_I2C3 instance. */
#define ALT_I2C3_IC_SS_SCL_LCNT_ADDR  ALT_I2C_SS_SCL_LCNT_ADDR(ALT_I2C3_ADDR)
/* The address of the ALT_I2C_FS_SCL_HCNT register for the ALT_I2C3 instance. */
#define ALT_I2C3_IC_FS_SCL_HCNT_ADDR  ALT_I2C_FS_SCL_HCNT_ADDR(ALT_I2C3_ADDR)
/* The address of the ALT_I2C_FS_SCL_LCNT register for the ALT_I2C3 instance. */
#define ALT_I2C3_IC_FS_SCL_LCNT_ADDR  ALT_I2C_FS_SCL_LCNT_ADDR(ALT_I2C3_ADDR)
/* The address of the ALT_I2C_INTR_STAT register for the ALT_I2C3 instance. */
#define ALT_I2C3_IC_INTR_STAT_ADDR  ALT_I2C_INTR_STAT_ADDR(ALT_I2C3_ADDR)
/* The address of the ALT_I2C_INTR_MSK register for the ALT_I2C3 instance. */
#define ALT_I2C3_IC_INTR_MSK_ADDR  ALT_I2C_INTR_MSK_ADDR(ALT_I2C3_ADDR)
/* The address of the ALT_I2C_RAW_INTR_STAT register for the ALT_I2C3 instance. */
#define ALT_I2C3_IC_RAW_INTR_STAT_ADDR  ALT_I2C_RAW_INTR_STAT_ADDR(ALT_I2C3_ADDR)
/* The address of the ALT_I2C_RX_TL register for the ALT_I2C3 instance. */
#define ALT_I2C3_IC_RX_TL_ADDR  ALT_I2C_RX_TL_ADDR(ALT_I2C3_ADDR)
/* The address of the ALT_I2C_TX_TL register for the ALT_I2C3 instance. */
#define ALT_I2C3_IC_TX_TL_ADDR  ALT_I2C_TX_TL_ADDR(ALT_I2C3_ADDR)
/* The address of the ALT_I2C_CLR_INTR register for the ALT_I2C3 instance. */
#define ALT_I2C3_IC_CLR_INTR_ADDR  ALT_I2C_CLR_INTR_ADDR(ALT_I2C3_ADDR)
/* The address of the ALT_I2C_CLR_RX_UNDER register for the ALT_I2C3 instance. */
#define ALT_I2C3_IC_CLR_RX_UNDER_ADDR  ALT_I2C_CLR_RX_UNDER_ADDR(ALT_I2C3_ADDR)
/* The address of the ALT_I2C_CLR_RX_OVER register for the ALT_I2C3 instance. */
#define ALT_I2C3_IC_CLR_RX_OVER_ADDR  ALT_I2C_CLR_RX_OVER_ADDR(ALT_I2C3_ADDR)
/* The address of the ALT_I2C_CLR_TX_OVER register for the ALT_I2C3 instance. */
#define ALT_I2C3_IC_CLR_TX_OVER_ADDR  ALT_I2C_CLR_TX_OVER_ADDR(ALT_I2C3_ADDR)
/* The address of the ALT_I2C_CLR_RD_REQ register for the ALT_I2C3 instance. */
#define ALT_I2C3_IC_CLR_RD_REQ_ADDR  ALT_I2C_CLR_RD_REQ_ADDR(ALT_I2C3_ADDR)
/* The address of the ALT_I2C_CLR_TX_ABRT register for the ALT_I2C3 instance. */
#define ALT_I2C3_IC_CLR_TX_ABRT_ADDR  ALT_I2C_CLR_TX_ABRT_ADDR(ALT_I2C3_ADDR)
/* The address of the ALT_I2C_CLR_RX_DONE register for the ALT_I2C3 instance. */
#define ALT_I2C3_IC_CLR_RX_DONE_ADDR  ALT_I2C_CLR_RX_DONE_ADDR(ALT_I2C3_ADDR)
/* The address of the ALT_I2C_CLR_ACTIVITY register for the ALT_I2C3 instance. */
#define ALT_I2C3_IC_CLR_ACTIVITY_ADDR  ALT_I2C_CLR_ACTIVITY_ADDR(ALT_I2C3_ADDR)
/* The address of the ALT_I2C_CLR_STOP_DET register for the ALT_I2C3 instance. */
#define ALT_I2C3_IC_CLR_STOP_DET_ADDR  ALT_I2C_CLR_STOP_DET_ADDR(ALT_I2C3_ADDR)
/* The address of the ALT_I2C_CLR_START_DET register for the ALT_I2C3 instance. */
#define ALT_I2C3_IC_CLR_START_DET_ADDR  ALT_I2C_CLR_START_DET_ADDR(ALT_I2C3_ADDR)
/* The address of the ALT_I2C_CLR_GEN_CALL register for the ALT_I2C3 instance. */
#define ALT_I2C3_IC_CLR_GEN_CALL_ADDR  ALT_I2C_CLR_GEN_CALL_ADDR(ALT_I2C3_ADDR)
/* The address of the ALT_I2C_EN register for the ALT_I2C3 instance. */
#define ALT_I2C3_IC_EN_ADDR  ALT_I2C_EN_ADDR(ALT_I2C3_ADDR)
/* The address of the ALT_I2C_STAT register for the ALT_I2C3 instance. */
#define ALT_I2C3_IC_STAT_ADDR  ALT_I2C_STAT_ADDR(ALT_I2C3_ADDR)
/* The address of the ALT_I2C_TXFLR register for the ALT_I2C3 instance. */
#define ALT_I2C3_IC_TXFLR_ADDR  ALT_I2C_TXFLR_ADDR(ALT_I2C3_ADDR)
/* The address of the ALT_I2C_RXFLR register for the ALT_I2C3 instance. */
#define ALT_I2C3_IC_RXFLR_ADDR  ALT_I2C_RXFLR_ADDR(ALT_I2C3_ADDR)
/* The address of the ALT_I2C_SDA_HOLD register for the ALT_I2C3 instance. */
#define ALT_I2C3_IC_SDA_HOLD_ADDR  ALT_I2C_SDA_HOLD_ADDR(ALT_I2C3_ADDR)
/* The address of the ALT_I2C_TX_ABRT_SRC register for the ALT_I2C3 instance. */
#define ALT_I2C3_IC_TX_ABRT_SRC_ADDR  ALT_I2C_TX_ABRT_SRC_ADDR(ALT_I2C3_ADDR)
/* The address of the ALT_I2C_SLV_DATA_NACK_ONLY register for the ALT_I2C3 instance. */
#define ALT_I2C3_IC_SLV_DATA_NACK_ONLY_ADDR  ALT_I2C_SLV_DATA_NACK_ONLY_ADDR(ALT_I2C3_ADDR)
/* The address of the ALT_I2C_DMA_CR register for the ALT_I2C3 instance. */
#define ALT_I2C3_IC_DMA_CR_ADDR  ALT_I2C_DMA_CR_ADDR(ALT_I2C3_ADDR)
/* The address of the ALT_I2C_DMA_TDLR register for the ALT_I2C3 instance. */
#define ALT_I2C3_IC_DMA_TDLR_ADDR  ALT_I2C_DMA_TDLR_ADDR(ALT_I2C3_ADDR)
/* The address of the ALT_I2C_DMA_RDLR register for the ALT_I2C3 instance. */
#define ALT_I2C3_IC_DMA_RDLR_ADDR  ALT_I2C_DMA_RDLR_ADDR(ALT_I2C3_ADDR)
/* The address of the ALT_I2C_SDA_SETUP register for the ALT_I2C3 instance. */
#define ALT_I2C3_IC_SDA_SETUP_ADDR  ALT_I2C_SDA_SETUP_ADDR(ALT_I2C3_ADDR)
/* The address of the ALT_I2C_ACK_GENERAL_CALL register for the ALT_I2C3 instance. */
#define ALT_I2C3_IC_ACK_GENERAL_CALL_ADDR  ALT_I2C_ACK_GENERAL_CALL_ADDR(ALT_I2C3_ADDR)
/* The address of the ALT_I2C_EN_STAT register for the ALT_I2C3 instance. */
#define ALT_I2C3_IC_EN_STAT_ADDR  ALT_I2C_EN_STAT_ADDR(ALT_I2C3_ADDR)
/* The address of the ALT_I2C_FS_SPKLEN register for the ALT_I2C3 instance. */
#define ALT_I2C3_IC_FS_SPKLEN_ADDR  ALT_I2C_FS_SPKLEN_ADDR(ALT_I2C3_ADDR)
/* The address of the ALT_I2C_COMP_PARAM_1 register for the ALT_I2C3 instance. */
#define ALT_I2C3_IC_COMP_PARAM_1_ADDR  ALT_I2C_COMP_PARAM_1_ADDR(ALT_I2C3_ADDR)
/* The address of the ALT_I2C_COMP_VER register for the ALT_I2C3 instance. */
#define ALT_I2C3_IC_COMP_VER_ADDR  ALT_I2C_COMP_VER_ADDR(ALT_I2C3_ADDR)
/* The address of the ALT_I2C_COMP_TYPE register for the ALT_I2C3 instance. */
#define ALT_I2C3_IC_COMP_TYPE_ADDR  ALT_I2C_COMP_TYPE_ADDR(ALT_I2C3_ADDR)
/* The base address byte offset for the start of the ALT_I2C3 component. */
#define ALT_I2C3_OFST        0xffc07000
/* The start address of the ALT_I2C3 component. */
#define ALT_I2C3_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_HPS_ADDR) + ALT_I2C3_OFST))
/* The lower bound address range of the ALT_I2C3 component. */
#define ALT_I2C3_LB_ADDR     ALT_I2C3_ADDR
/* The upper bound address range of the ALT_I2C3 component. */
#define ALT_I2C3_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_I2C3_ADDR) + 0x100) - 1))


/*
 * Component Instance : sptimer0
 * 
 * Instance sptimer0 of component ALT_TMR.
 * 
 * 
 */
/* The address of the ALT_TMR_TMR1LDCOUNT register for the ALT_SPTMR0 instance. */
#define ALT_SPTMR0_TMR1LDCOUNT_ADDR  ALT_TMR_TMR1LDCOUNT_ADDR(ALT_SPTMR0_ADDR)
/* The address of the ALT_TMR_TMR1CURVAL register for the ALT_SPTMR0 instance. */
#define ALT_SPTMR0_TMR1CURVAL_ADDR  ALT_TMR_TMR1CURVAL_ADDR(ALT_SPTMR0_ADDR)
/* The address of the ALT_TMR_TMR1CTLREG register for the ALT_SPTMR0 instance. */
#define ALT_SPTMR0_TMR1CTLREG_ADDR  ALT_TMR_TMR1CTLREG_ADDR(ALT_SPTMR0_ADDR)
/* The address of the ALT_TMR_TMR1EOI register for the ALT_SPTMR0 instance. */
#define ALT_SPTMR0_TMR1EOI_ADDR  ALT_TMR_TMR1EOI_ADDR(ALT_SPTMR0_ADDR)
/* The address of the ALT_TMR_TMR1INTSTAT register for the ALT_SPTMR0 instance. */
#define ALT_SPTMR0_TMR1INTSTAT_ADDR  ALT_TMR_TMR1INTSTAT_ADDR(ALT_SPTMR0_ADDR)
/* The address of the ALT_TMR_TMRSINTSTAT register for the ALT_SPTMR0 instance. */
#define ALT_SPTMR0_TMRSINTSTAT_ADDR  ALT_TMR_TMRSINTSTAT_ADDR(ALT_SPTMR0_ADDR)
/* The address of the ALT_TMR_TMRSEOI register for the ALT_SPTMR0 instance. */
#define ALT_SPTMR0_TMRSEOI_ADDR  ALT_TMR_TMRSEOI_ADDR(ALT_SPTMR0_ADDR)
/* The address of the ALT_TMR_TMRSRAWINTSTAT register for the ALT_SPTMR0 instance. */
#define ALT_SPTMR0_TMRSRAWINTSTAT_ADDR  ALT_TMR_TMRSRAWINTSTAT_ADDR(ALT_SPTMR0_ADDR)
/* The address of the ALT_TMR_TMRSCOMPVER register for the ALT_SPTMR0 instance. */
#define ALT_SPTMR0_TMRSCOMPVER_ADDR  ALT_TMR_TMRSCOMPVER_ADDR(ALT_SPTMR0_ADDR)
/* The base address byte offset for the start of the ALT_SPTMR0 component. */
#define ALT_SPTMR0_OFST        0xffc08000
/* The start address of the ALT_SPTMR0 component. */
#define ALT_SPTMR0_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_HPS_ADDR) + ALT_SPTMR0_OFST))
/* The lower bound address range of the ALT_SPTMR0 component. */
#define ALT_SPTMR0_LB_ADDR     ALT_SPTMR0_ADDR
/* The upper bound address range of the ALT_SPTMR0 component. */
#define ALT_SPTMR0_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_SPTMR0_ADDR) + 0x100) - 1))


/*
 * Component Instance : sptimer1
 * 
 * Instance sptimer1 of component ALT_TMR.
 * 
 * 
 */
/* The address of the ALT_TMR_TMR1LDCOUNT register for the ALT_SPTMR1 instance. */
#define ALT_SPTMR1_TMR1LDCOUNT_ADDR  ALT_TMR_TMR1LDCOUNT_ADDR(ALT_SPTMR1_ADDR)
/* The address of the ALT_TMR_TMR1CURVAL register for the ALT_SPTMR1 instance. */
#define ALT_SPTMR1_TMR1CURVAL_ADDR  ALT_TMR_TMR1CURVAL_ADDR(ALT_SPTMR1_ADDR)
/* The address of the ALT_TMR_TMR1CTLREG register for the ALT_SPTMR1 instance. */
#define ALT_SPTMR1_TMR1CTLREG_ADDR  ALT_TMR_TMR1CTLREG_ADDR(ALT_SPTMR1_ADDR)
/* The address of the ALT_TMR_TMR1EOI register for the ALT_SPTMR1 instance. */
#define ALT_SPTMR1_TMR1EOI_ADDR  ALT_TMR_TMR1EOI_ADDR(ALT_SPTMR1_ADDR)
/* The address of the ALT_TMR_TMR1INTSTAT register for the ALT_SPTMR1 instance. */
#define ALT_SPTMR1_TMR1INTSTAT_ADDR  ALT_TMR_TMR1INTSTAT_ADDR(ALT_SPTMR1_ADDR)
/* The address of the ALT_TMR_TMRSINTSTAT register for the ALT_SPTMR1 instance. */
#define ALT_SPTMR1_TMRSINTSTAT_ADDR  ALT_TMR_TMRSINTSTAT_ADDR(ALT_SPTMR1_ADDR)
/* The address of the ALT_TMR_TMRSEOI register for the ALT_SPTMR1 instance. */
#define ALT_SPTMR1_TMRSEOI_ADDR  ALT_TMR_TMRSEOI_ADDR(ALT_SPTMR1_ADDR)
/* The address of the ALT_TMR_TMRSRAWINTSTAT register for the ALT_SPTMR1 instance. */
#define ALT_SPTMR1_TMRSRAWINTSTAT_ADDR  ALT_TMR_TMRSRAWINTSTAT_ADDR(ALT_SPTMR1_ADDR)
/* The address of the ALT_TMR_TMRSCOMPVER register for the ALT_SPTMR1 instance. */
#define ALT_SPTMR1_TMRSCOMPVER_ADDR  ALT_TMR_TMRSCOMPVER_ADDR(ALT_SPTMR1_ADDR)
/* The base address byte offset for the start of the ALT_SPTMR1 component. */
#define ALT_SPTMR1_OFST        0xffc09000
/* The start address of the ALT_SPTMR1 component. */
#define ALT_SPTMR1_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_HPS_ADDR) + ALT_SPTMR1_OFST))
/* The lower bound address range of the ALT_SPTMR1 component. */
#define ALT_SPTMR1_LB_ADDR     ALT_SPTMR1_ADDR
/* The upper bound address range of the ALT_SPTMR1 component. */
#define ALT_SPTMR1_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_SPTMR1_ADDR) + 0x100) - 1))


/*
 * Component Instance : sdr
 * 
 * Instance sdr of component ALT_SDR.
 * 
 * 
 */
/*
 * Register Group Instance : ctrlgrp
 * 
 * Instance ctrlgrp of register group ALT_SDR_CTL.
 * 
 * 
 */
/* The address of the ALT_SDR_CTL_CTLCFG register for the ALT_SDR_CTL instance. */
#define ALT_SDR_CTL_CTLCFG_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDR_CTL_ADDR) + ALT_SDR_CTL_CTLCFG_OFST))
/* The address of the ALT_SDR_CTL_DRAMTIMING1 register for the ALT_SDR_CTL instance. */
#define ALT_SDR_CTL_DRAMTIMING1_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDR_CTL_ADDR) + ALT_SDR_CTL_DRAMTIMING1_OFST))
/* The address of the ALT_SDR_CTL_DRAMTIMING2 register for the ALT_SDR_CTL instance. */
#define ALT_SDR_CTL_DRAMTIMING2_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDR_CTL_ADDR) + ALT_SDR_CTL_DRAMTIMING2_OFST))
/* The address of the ALT_SDR_CTL_DRAMTIMING3 register for the ALT_SDR_CTL instance. */
#define ALT_SDR_CTL_DRAMTIMING3_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDR_CTL_ADDR) + ALT_SDR_CTL_DRAMTIMING3_OFST))
/* The address of the ALT_SDR_CTL_DRAMTIMING4 register for the ALT_SDR_CTL instance. */
#define ALT_SDR_CTL_DRAMTIMING4_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDR_CTL_ADDR) + ALT_SDR_CTL_DRAMTIMING4_OFST))
/* The address of the ALT_SDR_CTL_LOWPWRTIMING register for the ALT_SDR_CTL instance. */
#define ALT_SDR_CTL_LOWPWRTIMING_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDR_CTL_ADDR) + ALT_SDR_CTL_LOWPWRTIMING_OFST))
/* The address of the ALT_SDR_CTL_DRAMODT register for the ALT_SDR_CTL instance. */
#define ALT_SDR_CTL_DRAMODT_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDR_CTL_ADDR) + ALT_SDR_CTL_DRAMODT_OFST))
/* The address of the ALT_SDR_CTL_DRAMADDRW register for the ALT_SDR_CTL instance. */
#define ALT_SDR_CTL_DRAMADDRW_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDR_CTL_ADDR) + ALT_SDR_CTL_DRAMADDRW_OFST))
/* The address of the ALT_SDR_CTL_DRAMIFWIDTH register for the ALT_SDR_CTL instance. */
#define ALT_SDR_CTL_DRAMIFWIDTH_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDR_CTL_ADDR) + ALT_SDR_CTL_DRAMIFWIDTH_OFST))
/* The address of the ALT_SDR_CTL_DRAMDEVWIDTH register for the ALT_SDR_CTL instance. */
#define ALT_SDR_CTL_DRAMDEVWIDTH_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDR_CTL_ADDR) + ALT_SDR_CTL_DRAMDEVWIDTH_OFST))
/* The address of the ALT_SDR_CTL_DRAMSTS register for the ALT_SDR_CTL instance. */
#define ALT_SDR_CTL_DRAMSTS_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDR_CTL_ADDR) + ALT_SDR_CTL_DRAMSTS_OFST))
/* The address of the ALT_SDR_CTL_DRAMINTR register for the ALT_SDR_CTL instance. */
#define ALT_SDR_CTL_DRAMINTR_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDR_CTL_ADDR) + ALT_SDR_CTL_DRAMINTR_OFST))
/* The address of the ALT_SDR_CTL_SBECOUNT register for the ALT_SDR_CTL instance. */
#define ALT_SDR_CTL_SBECOUNT_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDR_CTL_ADDR) + ALT_SDR_CTL_SBECOUNT_OFST))
/* The address of the ALT_SDR_CTL_DBECOUNT register for the ALT_SDR_CTL instance. */
#define ALT_SDR_CTL_DBECOUNT_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDR_CTL_ADDR) + ALT_SDR_CTL_DBECOUNT_OFST))
/* The address of the ALT_SDR_CTL_ERRADDR register for the ALT_SDR_CTL instance. */
#define ALT_SDR_CTL_ERRADDR_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDR_CTL_ADDR) + ALT_SDR_CTL_ERRADDR_OFST))
/* The address of the ALT_SDR_CTL_DROPCOUNT register for the ALT_SDR_CTL instance. */
#define ALT_SDR_CTL_DROPCOUNT_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDR_CTL_ADDR) + ALT_SDR_CTL_DROPCOUNT_OFST))
/* The address of the ALT_SDR_CTL_DROPADDR register for the ALT_SDR_CTL instance. */
#define ALT_SDR_CTL_DROPADDR_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDR_CTL_ADDR) + ALT_SDR_CTL_DROPADDR_OFST))
/* The address of the ALT_SDR_CTL_LOWPWREQ register for the ALT_SDR_CTL instance. */
#define ALT_SDR_CTL_LOWPWREQ_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDR_CTL_ADDR) + ALT_SDR_CTL_LOWPWREQ_OFST))
/* The address of the ALT_SDR_CTL_LOWPWRACK register for the ALT_SDR_CTL instance. */
#define ALT_SDR_CTL_LOWPWRACK_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDR_CTL_ADDR) + ALT_SDR_CTL_LOWPWRACK_OFST))
/* The address of the ALT_SDR_CTL_STATICCFG register for the ALT_SDR_CTL instance. */
#define ALT_SDR_CTL_STATICCFG_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDR_CTL_ADDR) + ALT_SDR_CTL_STATICCFG_OFST))
/* The address of the ALT_SDR_CTL_CTLWIDTH register for the ALT_SDR_CTL instance. */
#define ALT_SDR_CTL_CTLWIDTH_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDR_CTL_ADDR) + ALT_SDR_CTL_CTLWIDTH_OFST))
/* The address of the ALT_SDR_CTL_PORTCFG register for the ALT_SDR_CTL instance. */
#define ALT_SDR_CTL_PORTCFG_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDR_CTL_ADDR) + ALT_SDR_CTL_PORTCFG_OFST))
/* The address of the ALT_SDR_CTL_FPGAPORTRST register for the ALT_SDR_CTL instance. */
#define ALT_SDR_CTL_FPGAPORTRST_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDR_CTL_ADDR) + ALT_SDR_CTL_FPGAPORTRST_OFST))
/* The address of the ALT_SDR_CTL_PROTPORTDEFAULT register for the ALT_SDR_CTL instance. */
#define ALT_SDR_CTL_PROTPORTDEFAULT_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDR_CTL_ADDR) + ALT_SDR_CTL_PROTPORTDEFAULT_OFST))
/* The address of the ALT_SDR_CTL_PROTRULEADDR register for the ALT_SDR_CTL instance. */
#define ALT_SDR_CTL_PROTRULEADDR_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDR_CTL_ADDR) + ALT_SDR_CTL_PROTRULEADDR_OFST))
/* The address of the ALT_SDR_CTL_PROTRULEID register for the ALT_SDR_CTL instance. */
#define ALT_SDR_CTL_PROTRULEID_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDR_CTL_ADDR) + ALT_SDR_CTL_PROTRULEID_OFST))
/* The address of the ALT_SDR_CTL_PROTRULEDATA register for the ALT_SDR_CTL instance. */
#define ALT_SDR_CTL_PROTRULEDATA_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDR_CTL_ADDR) + ALT_SDR_CTL_PROTRULEDATA_OFST))
/* The address of the ALT_SDR_CTL_PROTRULERDWR register for the ALT_SDR_CTL instance. */
#define ALT_SDR_CTL_PROTRULERDWR_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDR_CTL_ADDR) + ALT_SDR_CTL_PROTRULERDWR_OFST))
/* The address of the ALT_SDR_CTL_QOSLOWPRI register for the ALT_SDR_CTL instance. */
#define ALT_SDR_CTL_QOSLOWPRI_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDR_CTL_ADDR) + ALT_SDR_CTL_QOSLOWPRI_OFST))
/* The address of the ALT_SDR_CTL_QOSHIGHPRI register for the ALT_SDR_CTL instance. */
#define ALT_SDR_CTL_QOSHIGHPRI_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDR_CTL_ADDR) + ALT_SDR_CTL_QOSHIGHPRI_OFST))
/* The address of the ALT_SDR_CTL_QOSPRIORITYEN register for the ALT_SDR_CTL instance. */
#define ALT_SDR_CTL_QOSPRIORITYEN_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDR_CTL_ADDR) + ALT_SDR_CTL_QOSPRIORITYEN_OFST))
/* The address of the ALT_SDR_CTL_MPPRIORITY register for the ALT_SDR_CTL instance. */
#define ALT_SDR_CTL_MPPRIORITY_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDR_CTL_ADDR) + ALT_SDR_CTL_MPPRIORITY_OFST))
/* The address of the ALT_SDR_CTL_REMAPPRIORITY register for the ALT_SDR_CTL instance. */
#define ALT_SDR_CTL_REMAPPRIORITY_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SDR_CTL_ADDR) + ALT_SDR_CTL_REMAPPRIORITY_OFST))
/*
 * Register Group Instance : ctrlgrp_mpweight
 * 
 * Instance ctrlgrp_mpweight of register group ALT_SDR_CTL_MPWT.
 * 
 * 
 */
/* The address of the ALT_SDR_CTL_MPWT_MPWEIGHT_0_4 register for the ALT_SDR_CTL_CTL_MPWEIGHT instance. */
#define ALT_SDR_CTL_CTL_MPWEIGHT_MPWEIGHT_0_4_ADDR  ALT_SDR_CTL_MPWT_MPWEIGHT_0_4_ADDR(ALT_SDR_CTL_CTL_MPWEIGHT_ADDR)
/* The address of the ALT_SDR_CTL_MPWT_MPWEIGHT_1_4 register for the ALT_SDR_CTL_CTL_MPWEIGHT instance. */
#define ALT_SDR_CTL_CTL_MPWEIGHT_MPWEIGHT_1_4_ADDR  ALT_SDR_CTL_MPWT_MPWEIGHT_1_4_ADDR(ALT_SDR_CTL_CTL_MPWEIGHT_ADDR)
/* The address of the ALT_SDR_CTL_MPWT_MPWEIGHT_2_4 register for the ALT_SDR_CTL_CTL_MPWEIGHT instance. */
#define ALT_SDR_CTL_CTL_MPWEIGHT_MPWEIGHT_2_4_ADDR  ALT_SDR_CTL_MPWT_MPWEIGHT_2_4_ADDR(ALT_SDR_CTL_CTL_MPWEIGHT_ADDR)
/* The address of the ALT_SDR_CTL_MPWT_MPWEIGHT_3_4 register for the ALT_SDR_CTL_CTL_MPWEIGHT instance. */
#define ALT_SDR_CTL_CTL_MPWEIGHT_MPWEIGHT_3_4_ADDR  ALT_SDR_CTL_MPWT_MPWEIGHT_3_4_ADDR(ALT_SDR_CTL_CTL_MPWEIGHT_ADDR)
/* The base address byte offset for the start of the ALT_SDR_CTL_CTL_MPWEIGHT component. */
#define ALT_SDR_CTL_CTL_MPWEIGHT_OFST        0xb0
/* The start address of the ALT_SDR_CTL_CTL_MPWEIGHT component. */
#define ALT_SDR_CTL_CTL_MPWEIGHT_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_SDR_CTL_ADDR) + ALT_SDR_CTL_CTL_MPWEIGHT_OFST))
/* The lower bound address range of the ALT_SDR_CTL_CTL_MPWEIGHT component. */
#define ALT_SDR_CTL_CTL_MPWEIGHT_LB_ADDR     ALT_SDR_CTL_CTL_MPWEIGHT_ADDR
/* The upper bound address range of the ALT_SDR_CTL_CTL_MPWEIGHT component. */
#define ALT_SDR_CTL_CTL_MPWEIGHT_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_SDR_CTL_CTL_MPWEIGHT_ADDR) + 0x10) - 1))


/* The base address byte offset for the start of the ALT_SDR_CTL component. */
#define ALT_SDR_CTL_OFST        0x5000
/* The start address of the ALT_SDR_CTL component. */
#define ALT_SDR_CTL_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_SDR_ADDR) + ALT_SDR_CTL_OFST))
/* The lower bound address range of the ALT_SDR_CTL component. */
#define ALT_SDR_CTL_LB_ADDR     ALT_SDR_CTL_ADDR
/* The upper bound address range of the ALT_SDR_CTL component. */
#define ALT_SDR_CTL_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_SDR_CTL_ADDR) + 0x1000) - 1))


/* The base address byte offset for the start of the ALT_SDR component. */
#define ALT_SDR_OFST        0xffc20000
/* The start address of the ALT_SDR component. */
#define ALT_SDR_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_HPS_ADDR) + ALT_SDR_OFST))
/* The lower bound address range of the ALT_SDR component. */
#define ALT_SDR_LB_ADDR     ALT_SDR_ADDR
/* The upper bound address range of the ALT_SDR component. */
#define ALT_SDR_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_SDR_ADDR) + 0x20000) - 1))


/*
 * Component Instance : osc1timer0
 * 
 * Instance osc1timer0 of component ALT_TMR.
 * 
 * 
 */
/* The address of the ALT_TMR_TMR1LDCOUNT register for the ALT_OSC1TMR0 instance. */
#define ALT_OSC1TMR0_TMR1LDCOUNT_ADDR  ALT_TMR_TMR1LDCOUNT_ADDR(ALT_OSC1TMR0_ADDR)
/* The address of the ALT_TMR_TMR1CURVAL register for the ALT_OSC1TMR0 instance. */
#define ALT_OSC1TMR0_TMR1CURVAL_ADDR  ALT_TMR_TMR1CURVAL_ADDR(ALT_OSC1TMR0_ADDR)
/* The address of the ALT_TMR_TMR1CTLREG register for the ALT_OSC1TMR0 instance. */
#define ALT_OSC1TMR0_TMR1CTLREG_ADDR  ALT_TMR_TMR1CTLREG_ADDR(ALT_OSC1TMR0_ADDR)
/* The address of the ALT_TMR_TMR1EOI register for the ALT_OSC1TMR0 instance. */
#define ALT_OSC1TMR0_TMR1EOI_ADDR  ALT_TMR_TMR1EOI_ADDR(ALT_OSC1TMR0_ADDR)
/* The address of the ALT_TMR_TMR1INTSTAT register for the ALT_OSC1TMR0 instance. */
#define ALT_OSC1TMR0_TMR1INTSTAT_ADDR  ALT_TMR_TMR1INTSTAT_ADDR(ALT_OSC1TMR0_ADDR)
/* The address of the ALT_TMR_TMRSINTSTAT register for the ALT_OSC1TMR0 instance. */
#define ALT_OSC1TMR0_TMRSINTSTAT_ADDR  ALT_TMR_TMRSINTSTAT_ADDR(ALT_OSC1TMR0_ADDR)
/* The address of the ALT_TMR_TMRSEOI register for the ALT_OSC1TMR0 instance. */
#define ALT_OSC1TMR0_TMRSEOI_ADDR  ALT_TMR_TMRSEOI_ADDR(ALT_OSC1TMR0_ADDR)
/* The address of the ALT_TMR_TMRSRAWINTSTAT register for the ALT_OSC1TMR0 instance. */
#define ALT_OSC1TMR0_TMRSRAWINTSTAT_ADDR  ALT_TMR_TMRSRAWINTSTAT_ADDR(ALT_OSC1TMR0_ADDR)
/* The address of the ALT_TMR_TMRSCOMPVER register for the ALT_OSC1TMR0 instance. */
#define ALT_OSC1TMR0_TMRSCOMPVER_ADDR  ALT_TMR_TMRSCOMPVER_ADDR(ALT_OSC1TMR0_ADDR)
/* The base address byte offset for the start of the ALT_OSC1TMR0 component. */
#define ALT_OSC1TMR0_OFST        0xffd00000
/* The start address of the ALT_OSC1TMR0 component. */
#define ALT_OSC1TMR0_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_HPS_ADDR) + ALT_OSC1TMR0_OFST))
/* The lower bound address range of the ALT_OSC1TMR0 component. */
#define ALT_OSC1TMR0_LB_ADDR     ALT_OSC1TMR0_ADDR
/* The upper bound address range of the ALT_OSC1TMR0 component. */
#define ALT_OSC1TMR0_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_OSC1TMR0_ADDR) + 0x100) - 1))


/*
 * Component Instance : osc1timer1
 * 
 * Instance osc1timer1 of component ALT_TMR.
 * 
 * 
 */
/* The address of the ALT_TMR_TMR1LDCOUNT register for the ALT_OSC1TMR1 instance. */
#define ALT_OSC1TMR1_TMR1LDCOUNT_ADDR  ALT_TMR_TMR1LDCOUNT_ADDR(ALT_OSC1TMR1_ADDR)
/* The address of the ALT_TMR_TMR1CURVAL register for the ALT_OSC1TMR1 instance. */
#define ALT_OSC1TMR1_TMR1CURVAL_ADDR  ALT_TMR_TMR1CURVAL_ADDR(ALT_OSC1TMR1_ADDR)
/* The address of the ALT_TMR_TMR1CTLREG register for the ALT_OSC1TMR1 instance. */
#define ALT_OSC1TMR1_TMR1CTLREG_ADDR  ALT_TMR_TMR1CTLREG_ADDR(ALT_OSC1TMR1_ADDR)
/* The address of the ALT_TMR_TMR1EOI register for the ALT_OSC1TMR1 instance. */
#define ALT_OSC1TMR1_TMR1EOI_ADDR  ALT_TMR_TMR1EOI_ADDR(ALT_OSC1TMR1_ADDR)
/* The address of the ALT_TMR_TMR1INTSTAT register for the ALT_OSC1TMR1 instance. */
#define ALT_OSC1TMR1_TMR1INTSTAT_ADDR  ALT_TMR_TMR1INTSTAT_ADDR(ALT_OSC1TMR1_ADDR)
/* The address of the ALT_TMR_TMRSINTSTAT register for the ALT_OSC1TMR1 instance. */
#define ALT_OSC1TMR1_TMRSINTSTAT_ADDR  ALT_TMR_TMRSINTSTAT_ADDR(ALT_OSC1TMR1_ADDR)
/* The address of the ALT_TMR_TMRSEOI register for the ALT_OSC1TMR1 instance. */
#define ALT_OSC1TMR1_TMRSEOI_ADDR  ALT_TMR_TMRSEOI_ADDR(ALT_OSC1TMR1_ADDR)
/* The address of the ALT_TMR_TMRSRAWINTSTAT register for the ALT_OSC1TMR1 instance. */
#define ALT_OSC1TMR1_TMRSRAWINTSTAT_ADDR  ALT_TMR_TMRSRAWINTSTAT_ADDR(ALT_OSC1TMR1_ADDR)
/* The address of the ALT_TMR_TMRSCOMPVER register for the ALT_OSC1TMR1 instance. */
#define ALT_OSC1TMR1_TMRSCOMPVER_ADDR  ALT_TMR_TMRSCOMPVER_ADDR(ALT_OSC1TMR1_ADDR)
/* The base address byte offset for the start of the ALT_OSC1TMR1 component. */
#define ALT_OSC1TMR1_OFST        0xffd01000
/* The start address of the ALT_OSC1TMR1 component. */
#define ALT_OSC1TMR1_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_HPS_ADDR) + ALT_OSC1TMR1_OFST))
/* The lower bound address range of the ALT_OSC1TMR1 component. */
#define ALT_OSC1TMR1_LB_ADDR     ALT_OSC1TMR1_ADDR
/* The upper bound address range of the ALT_OSC1TMR1 component. */
#define ALT_OSC1TMR1_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_OSC1TMR1_ADDR) + 0x100) - 1))


/*
 * Component Instance : l4wd0
 * 
 * Instance l4wd0 of component ALT_L4WD.
 * 
 * 
 */
/* The address of the ALT_L4WD_CR register for the ALT_L4WD0 instance. */
#define ALT_L4WD0_WDT_CR_ADDR  ALT_L4WD_CR_ADDR(ALT_L4WD0_ADDR)
/* The address of the ALT_L4WD_TORR register for the ALT_L4WD0 instance. */
#define ALT_L4WD0_WDT_TORR_ADDR  ALT_L4WD_TORR_ADDR(ALT_L4WD0_ADDR)
/* The address of the ALT_L4WD_CCVR register for the ALT_L4WD0 instance. */
#define ALT_L4WD0_WDT_CCVR_ADDR  ALT_L4WD_CCVR_ADDR(ALT_L4WD0_ADDR)
/* The address of the ALT_L4WD_CRR register for the ALT_L4WD0 instance. */
#define ALT_L4WD0_WDT_CRR_ADDR  ALT_L4WD_CRR_ADDR(ALT_L4WD0_ADDR)
/* The address of the ALT_L4WD_STAT register for the ALT_L4WD0 instance. */
#define ALT_L4WD0_WDT_STAT_ADDR  ALT_L4WD_STAT_ADDR(ALT_L4WD0_ADDR)
/* The address of the ALT_L4WD_EOI register for the ALT_L4WD0 instance. */
#define ALT_L4WD0_WDT_EOI_ADDR  ALT_L4WD_EOI_ADDR(ALT_L4WD0_ADDR)
/* The address of the ALT_L4WD_CP_WDT_USER_TOP_MAX register for the ALT_L4WD0 instance. */
#define ALT_L4WD0_CP_WDT_USER_TOP_MAX_ADDR  ALT_L4WD_CP_WDT_USER_TOP_MAX_ADDR(ALT_L4WD0_ADDR)
/* The address of the ALT_L4WD_CP_WDT_USER_TOP_INIT_MAX register for the ALT_L4WD0 instance. */
#define ALT_L4WD0_CP_WDT_USER_TOP_INIT_MAX_ADDR  ALT_L4WD_CP_WDT_USER_TOP_INIT_MAX_ADDR(ALT_L4WD0_ADDR)
/* The address of the ALT_L4WD_CD_WDT_TOP_RST register for the ALT_L4WD0 instance. */
#define ALT_L4WD0_CD_WDT_TOP_RST_ADDR  ALT_L4WD_CD_WDT_TOP_RST_ADDR(ALT_L4WD0_ADDR)
/* The address of the ALT_L4WD_CP_WDT_CNT_RST register for the ALT_L4WD0 instance. */
#define ALT_L4WD0_CP_WDT_CNT_RST_ADDR  ALT_L4WD_CP_WDT_CNT_RST_ADDR(ALT_L4WD0_ADDR)
/* The address of the ALT_L4WD_COMP_PARAM_1 register for the ALT_L4WD0 instance. */
#define ALT_L4WD0_WDT_COMP_PARAM_1_ADDR  ALT_L4WD_COMP_PARAM_1_ADDR(ALT_L4WD0_ADDR)
/* The address of the ALT_L4WD_COMP_VER register for the ALT_L4WD0 instance. */
#define ALT_L4WD0_WDT_COMP_VER_ADDR  ALT_L4WD_COMP_VER_ADDR(ALT_L4WD0_ADDR)
/* The address of the ALT_L4WD_COMP_TYPE register for the ALT_L4WD0 instance. */
#define ALT_L4WD0_WDT_COMP_TYPE_ADDR  ALT_L4WD_COMP_TYPE_ADDR(ALT_L4WD0_ADDR)
/* The base address byte offset for the start of the ALT_L4WD0 component. */
#define ALT_L4WD0_OFST        0xffd02000
/* The start address of the ALT_L4WD0 component. */
#define ALT_L4WD0_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_HPS_ADDR) + ALT_L4WD0_OFST))
/* The lower bound address range of the ALT_L4WD0 component. */
#define ALT_L4WD0_LB_ADDR     ALT_L4WD0_ADDR
/* The upper bound address range of the ALT_L4WD0 component. */
#define ALT_L4WD0_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_L4WD0_ADDR) + 0x100) - 1))


/*
 * Component Instance : l4wd1
 * 
 * Instance l4wd1 of component ALT_L4WD.
 * 
 * 
 */
/* The address of the ALT_L4WD_CR register for the ALT_L4WD1 instance. */
#define ALT_L4WD1_WDT_CR_ADDR  ALT_L4WD_CR_ADDR(ALT_L4WD1_ADDR)
/* The address of the ALT_L4WD_TORR register for the ALT_L4WD1 instance. */
#define ALT_L4WD1_WDT_TORR_ADDR  ALT_L4WD_TORR_ADDR(ALT_L4WD1_ADDR)
/* The address of the ALT_L4WD_CCVR register for the ALT_L4WD1 instance. */
#define ALT_L4WD1_WDT_CCVR_ADDR  ALT_L4WD_CCVR_ADDR(ALT_L4WD1_ADDR)
/* The address of the ALT_L4WD_CRR register for the ALT_L4WD1 instance. */
#define ALT_L4WD1_WDT_CRR_ADDR  ALT_L4WD_CRR_ADDR(ALT_L4WD1_ADDR)
/* The address of the ALT_L4WD_STAT register for the ALT_L4WD1 instance. */
#define ALT_L4WD1_WDT_STAT_ADDR  ALT_L4WD_STAT_ADDR(ALT_L4WD1_ADDR)
/* The address of the ALT_L4WD_EOI register for the ALT_L4WD1 instance. */
#define ALT_L4WD1_WDT_EOI_ADDR  ALT_L4WD_EOI_ADDR(ALT_L4WD1_ADDR)
/* The address of the ALT_L4WD_CP_WDT_USER_TOP_MAX register for the ALT_L4WD1 instance. */
#define ALT_L4WD1_CP_WDT_USER_TOP_MAX_ADDR  ALT_L4WD_CP_WDT_USER_TOP_MAX_ADDR(ALT_L4WD1_ADDR)
/* The address of the ALT_L4WD_CP_WDT_USER_TOP_INIT_MAX register for the ALT_L4WD1 instance. */
#define ALT_L4WD1_CP_WDT_USER_TOP_INIT_MAX_ADDR  ALT_L4WD_CP_WDT_USER_TOP_INIT_MAX_ADDR(ALT_L4WD1_ADDR)
/* The address of the ALT_L4WD_CD_WDT_TOP_RST register for the ALT_L4WD1 instance. */
#define ALT_L4WD1_CD_WDT_TOP_RST_ADDR  ALT_L4WD_CD_WDT_TOP_RST_ADDR(ALT_L4WD1_ADDR)
/* The address of the ALT_L4WD_CP_WDT_CNT_RST register for the ALT_L4WD1 instance. */
#define ALT_L4WD1_CP_WDT_CNT_RST_ADDR  ALT_L4WD_CP_WDT_CNT_RST_ADDR(ALT_L4WD1_ADDR)
/* The address of the ALT_L4WD_COMP_PARAM_1 register for the ALT_L4WD1 instance. */
#define ALT_L4WD1_WDT_COMP_PARAM_1_ADDR  ALT_L4WD_COMP_PARAM_1_ADDR(ALT_L4WD1_ADDR)
/* The address of the ALT_L4WD_COMP_VER register for the ALT_L4WD1 instance. */
#define ALT_L4WD1_WDT_COMP_VER_ADDR  ALT_L4WD_COMP_VER_ADDR(ALT_L4WD1_ADDR)
/* The address of the ALT_L4WD_COMP_TYPE register for the ALT_L4WD1 instance. */
#define ALT_L4WD1_WDT_COMP_TYPE_ADDR  ALT_L4WD_COMP_TYPE_ADDR(ALT_L4WD1_ADDR)
/* The base address byte offset for the start of the ALT_L4WD1 component. */
#define ALT_L4WD1_OFST        0xffd03000
/* The start address of the ALT_L4WD1 component. */
#define ALT_L4WD1_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_HPS_ADDR) + ALT_L4WD1_OFST))
/* The lower bound address range of the ALT_L4WD1 component. */
#define ALT_L4WD1_LB_ADDR     ALT_L4WD1_ADDR
/* The upper bound address range of the ALT_L4WD1 component. */
#define ALT_L4WD1_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_L4WD1_ADDR) + 0x100) - 1))


/*
 * Component Instance : clkmgr
 * 
 * Instance clkmgr of component ALT_CLKMGR.
 * 
 * 
 */
/* The address of the ALT_CLKMGR_CTL register for the ALT_CLKMGR instance. */
#define ALT_CLKMGR_CTL_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_CLKMGR_ADDR) + ALT_CLKMGR_CTL_OFST))
/* The address of the ALT_CLKMGR_BYPASS register for the ALT_CLKMGR instance. */
#define ALT_CLKMGR_BYPASS_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_CLKMGR_ADDR) + ALT_CLKMGR_BYPASS_OFST))
/* The address of the ALT_CLKMGR_INTER register for the ALT_CLKMGR instance. */
#define ALT_CLKMGR_INTER_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_CLKMGR_ADDR) + ALT_CLKMGR_INTER_OFST))
/* The address of the ALT_CLKMGR_INTREN register for the ALT_CLKMGR instance. */
#define ALT_CLKMGR_INTREN_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_CLKMGR_ADDR) + ALT_CLKMGR_INTREN_OFST))
/* The address of the ALT_CLKMGR_DBCTL register for the ALT_CLKMGR instance. */
#define ALT_CLKMGR_DBCTL_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_CLKMGR_ADDR) + ALT_CLKMGR_DBCTL_OFST))
/* The address of the ALT_CLKMGR_STAT register for the ALT_CLKMGR instance. */
#define ALT_CLKMGR_STAT_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_CLKMGR_ADDR) + ALT_CLKMGR_STAT_OFST))
/*
 * Register Group Instance : mainpllgrp
 * 
 * Instance mainpllgrp of register group ALT_CLKMGR_MAINPLL.
 * 
 * 
 */
/* The address of the ALT_CLKMGR_MAINPLL_VCO register for the ALT_CLKMGR_MAINPLL instance. */
#define ALT_CLKMGR_MAINPLL_VCO_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_CLKMGR_MAINPLL_ADDR) + ALT_CLKMGR_MAINPLL_VCO_OFST))
/* The address of the ALT_CLKMGR_MAINPLL_MISC register for the ALT_CLKMGR_MAINPLL instance. */
#define ALT_CLKMGR_MAINPLL_MISC_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_CLKMGR_MAINPLL_ADDR) + ALT_CLKMGR_MAINPLL_MISC_OFST))
/* The address of the ALT_CLKMGR_MAINPLL_MPUCLK register for the ALT_CLKMGR_MAINPLL instance. */
#define ALT_CLKMGR_MAINPLL_MPUCLK_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_CLKMGR_MAINPLL_ADDR) + ALT_CLKMGR_MAINPLL_MPUCLK_OFST))
/* The address of the ALT_CLKMGR_MAINPLL_MAINCLK register for the ALT_CLKMGR_MAINPLL instance. */
#define ALT_CLKMGR_MAINPLL_MAINCLK_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_CLKMGR_MAINPLL_ADDR) + ALT_CLKMGR_MAINPLL_MAINCLK_OFST))
/* The address of the ALT_CLKMGR_MAINPLL_DBGATCLK register for the ALT_CLKMGR_MAINPLL instance. */
#define ALT_CLKMGR_MAINPLL_DBGATCLK_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_CLKMGR_MAINPLL_ADDR) + ALT_CLKMGR_MAINPLL_DBGATCLK_OFST))
/* The address of the ALT_CLKMGR_MAINPLL_MAINQSPICLK register for the ALT_CLKMGR_MAINPLL instance. */
#define ALT_CLKMGR_MAINPLL_MAINQSPICLK_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_CLKMGR_MAINPLL_ADDR) + ALT_CLKMGR_MAINPLL_MAINQSPICLK_OFST))
/* The address of the ALT_CLKMGR_MAINPLL_MAINNANDSDMMCCLK register for the ALT_CLKMGR_MAINPLL instance. */
#define ALT_CLKMGR_MAINPLL_MAINNANDSDMMCCLK_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_CLKMGR_MAINPLL_ADDR) + ALT_CLKMGR_MAINPLL_MAINNANDSDMMCCLK_OFST))
/* The address of the ALT_CLKMGR_MAINPLL_CFGS2FUSER0CLK register for the ALT_CLKMGR_MAINPLL instance. */
#define ALT_CLKMGR_MAINPLL_CFGS2FUSER0CLK_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_CLKMGR_MAINPLL_ADDR) + ALT_CLKMGR_MAINPLL_CFGS2FUSER0CLK_OFST))
/* The address of the ALT_CLKMGR_MAINPLL_EN register for the ALT_CLKMGR_MAINPLL instance. */
#define ALT_CLKMGR_MAINPLL_EN_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_CLKMGR_MAINPLL_ADDR) + ALT_CLKMGR_MAINPLL_EN_OFST))
/* The address of the ALT_CLKMGR_MAINPLL_MAINDIV register for the ALT_CLKMGR_MAINPLL instance. */
#define ALT_CLKMGR_MAINPLL_MAINDIV_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_CLKMGR_MAINPLL_ADDR) + ALT_CLKMGR_MAINPLL_MAINDIV_OFST))
/* The address of the ALT_CLKMGR_MAINPLL_DBGDIV register for the ALT_CLKMGR_MAINPLL instance. */
#define ALT_CLKMGR_MAINPLL_DBGDIV_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_CLKMGR_MAINPLL_ADDR) + ALT_CLKMGR_MAINPLL_DBGDIV_OFST))
/* The address of the ALT_CLKMGR_MAINPLL_TRACEDIV register for the ALT_CLKMGR_MAINPLL instance. */
#define ALT_CLKMGR_MAINPLL_TRACEDIV_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_CLKMGR_MAINPLL_ADDR) + ALT_CLKMGR_MAINPLL_TRACEDIV_OFST))
/* The address of the ALT_CLKMGR_MAINPLL_L4SRC register for the ALT_CLKMGR_MAINPLL instance. */
#define ALT_CLKMGR_MAINPLL_L4SRC_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_CLKMGR_MAINPLL_ADDR) + ALT_CLKMGR_MAINPLL_L4SRC_OFST))
/* The address of the ALT_CLKMGR_MAINPLL_STAT register for the ALT_CLKMGR_MAINPLL instance. */
#define ALT_CLKMGR_MAINPLL_STAT_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_CLKMGR_MAINPLL_ADDR) + ALT_CLKMGR_MAINPLL_STAT_OFST))
/* The base address byte offset for the start of the ALT_CLKMGR_MAINPLL component. */
#define ALT_CLKMGR_MAINPLL_OFST        0x40
/* The start address of the ALT_CLKMGR_MAINPLL component. */
#define ALT_CLKMGR_MAINPLL_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_CLKMGR_ADDR) + ALT_CLKMGR_MAINPLL_OFST))
/* The lower bound address range of the ALT_CLKMGR_MAINPLL component. */
#define ALT_CLKMGR_MAINPLL_LB_ADDR     ALT_CLKMGR_MAINPLL_ADDR
/* The upper bound address range of the ALT_CLKMGR_MAINPLL component. */
#define ALT_CLKMGR_MAINPLL_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_CLKMGR_MAINPLL_ADDR) + 0x40) - 1))


/*
 * Register Group Instance : perpllgrp
 * 
 * Instance perpllgrp of register group ALT_CLKMGR_PERPLL.
 * 
 * 
 */
/* The address of the ALT_CLKMGR_PERPLL_VCO register for the ALT_CLKMGR_PERPLL instance. */
#define ALT_CLKMGR_PERPLL_VCO_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_CLKMGR_PERPLL_ADDR) + ALT_CLKMGR_PERPLL_VCO_OFST))
/* The address of the ALT_CLKMGR_PERPLL_MISC register for the ALT_CLKMGR_PERPLL instance. */
#define ALT_CLKMGR_PERPLL_MISC_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_CLKMGR_PERPLL_ADDR) + ALT_CLKMGR_PERPLL_MISC_OFST))
/* The address of the ALT_CLKMGR_PERPLL_EMAC0CLK register for the ALT_CLKMGR_PERPLL instance. */
#define ALT_CLKMGR_PERPLL_EMAC0CLK_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_CLKMGR_PERPLL_ADDR) + ALT_CLKMGR_PERPLL_EMAC0CLK_OFST))
/* The address of the ALT_CLKMGR_PERPLL_EMAC1CLK register for the ALT_CLKMGR_PERPLL instance. */
#define ALT_CLKMGR_PERPLL_EMAC1CLK_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_CLKMGR_PERPLL_ADDR) + ALT_CLKMGR_PERPLL_EMAC1CLK_OFST))
/* The address of the ALT_CLKMGR_PERPLL_PERQSPICLK register for the ALT_CLKMGR_PERPLL instance. */
#define ALT_CLKMGR_PERPLL_PERQSPICLK_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_CLKMGR_PERPLL_ADDR) + ALT_CLKMGR_PERPLL_PERQSPICLK_OFST))
/* The address of the ALT_CLKMGR_PERPLL_PERNANDSDMMCCLK register for the ALT_CLKMGR_PERPLL instance. */
#define ALT_CLKMGR_PERPLL_PERNANDSDMMCCLK_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_CLKMGR_PERPLL_ADDR) + ALT_CLKMGR_PERPLL_PERNANDSDMMCCLK_OFST))
/* The address of the ALT_CLKMGR_PERPLL_PERBASECLK register for the ALT_CLKMGR_PERPLL instance. */
#define ALT_CLKMGR_PERPLL_PERBASECLK_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_CLKMGR_PERPLL_ADDR) + ALT_CLKMGR_PERPLL_PERBASECLK_OFST))
/* The address of the ALT_CLKMGR_PERPLL_S2FUSER1CLK register for the ALT_CLKMGR_PERPLL instance. */
#define ALT_CLKMGR_PERPLL_S2FUSER1CLK_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_CLKMGR_PERPLL_ADDR) + ALT_CLKMGR_PERPLL_S2FUSER1CLK_OFST))
/* The address of the ALT_CLKMGR_PERPLL_EN register for the ALT_CLKMGR_PERPLL instance. */
#define ALT_CLKMGR_PERPLL_EN_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_CLKMGR_PERPLL_ADDR) + ALT_CLKMGR_PERPLL_EN_OFST))
/* The address of the ALT_CLKMGR_PERPLL_DIV register for the ALT_CLKMGR_PERPLL instance. */
#define ALT_CLKMGR_PERPLL_DIV_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_CLKMGR_PERPLL_ADDR) + ALT_CLKMGR_PERPLL_DIV_OFST))
/* The address of the ALT_CLKMGR_PERPLL_GPIODIV register for the ALT_CLKMGR_PERPLL instance. */
#define ALT_CLKMGR_PERPLL_GPIODIV_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_CLKMGR_PERPLL_ADDR) + ALT_CLKMGR_PERPLL_GPIODIV_OFST))
/* The address of the ALT_CLKMGR_PERPLL_SRC register for the ALT_CLKMGR_PERPLL instance. */
#define ALT_CLKMGR_PERPLL_SRC_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_CLKMGR_PERPLL_ADDR) + ALT_CLKMGR_PERPLL_SRC_OFST))
/* The address of the ALT_CLKMGR_PERPLL_STAT register for the ALT_CLKMGR_PERPLL instance. */
#define ALT_CLKMGR_PERPLL_STAT_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_CLKMGR_PERPLL_ADDR) + ALT_CLKMGR_PERPLL_STAT_OFST))
/* The base address byte offset for the start of the ALT_CLKMGR_PERPLL component. */
#define ALT_CLKMGR_PERPLL_OFST        0x80
/* The start address of the ALT_CLKMGR_PERPLL component. */
#define ALT_CLKMGR_PERPLL_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_CLKMGR_ADDR) + ALT_CLKMGR_PERPLL_OFST))
/* The lower bound address range of the ALT_CLKMGR_PERPLL component. */
#define ALT_CLKMGR_PERPLL_LB_ADDR     ALT_CLKMGR_PERPLL_ADDR
/* The upper bound address range of the ALT_CLKMGR_PERPLL component. */
#define ALT_CLKMGR_PERPLL_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_CLKMGR_PERPLL_ADDR) + 0x40) - 1))


/*
 * Register Group Instance : sdrpllgrp
 * 
 * Instance sdrpllgrp of register group ALT_CLKMGR_SDRPLL.
 * 
 * 
 */
/* The address of the ALT_CLKMGR_SDRPLL_VCO register for the ALT_CLKMGR_SDRPLL instance. */
#define ALT_CLKMGR_SDRPLL_VCO_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_CLKMGR_SDRPLL_ADDR) + ALT_CLKMGR_SDRPLL_VCO_OFST))
/* The address of the ALT_CLKMGR_SDRPLL_CTL register for the ALT_CLKMGR_SDRPLL instance. */
#define ALT_CLKMGR_SDRPLL_CTL_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_CLKMGR_SDRPLL_ADDR) + ALT_CLKMGR_SDRPLL_CTL_OFST))
/* The address of the ALT_CLKMGR_SDRPLL_DDRDQSCLK register for the ALT_CLKMGR_SDRPLL instance. */
#define ALT_CLKMGR_SDRPLL_DDRDQSCLK_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_CLKMGR_SDRPLL_ADDR) + ALT_CLKMGR_SDRPLL_DDRDQSCLK_OFST))
/* The address of the ALT_CLKMGR_SDRPLL_DDR2XDQSCLK register for the ALT_CLKMGR_SDRPLL instance. */
#define ALT_CLKMGR_SDRPLL_DDR2XDQSCLK_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_CLKMGR_SDRPLL_ADDR) + ALT_CLKMGR_SDRPLL_DDR2XDQSCLK_OFST))
/* The address of the ALT_CLKMGR_SDRPLL_DDRDQCLK register for the ALT_CLKMGR_SDRPLL instance. */
#define ALT_CLKMGR_SDRPLL_DDRDQCLK_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_CLKMGR_SDRPLL_ADDR) + ALT_CLKMGR_SDRPLL_DDRDQCLK_OFST))
/* The address of the ALT_CLKMGR_SDRPLL_S2FUSER2CLK register for the ALT_CLKMGR_SDRPLL instance. */
#define ALT_CLKMGR_SDRPLL_S2FUSER2CLK_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_CLKMGR_SDRPLL_ADDR) + ALT_CLKMGR_SDRPLL_S2FUSER2CLK_OFST))
/* The address of the ALT_CLKMGR_SDRPLL_EN register for the ALT_CLKMGR_SDRPLL instance. */
#define ALT_CLKMGR_SDRPLL_EN_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_CLKMGR_SDRPLL_ADDR) + ALT_CLKMGR_SDRPLL_EN_OFST))
/* The address of the ALT_CLKMGR_SDRPLL_STAT register for the ALT_CLKMGR_SDRPLL instance. */
#define ALT_CLKMGR_SDRPLL_STAT_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_CLKMGR_SDRPLL_ADDR) + ALT_CLKMGR_SDRPLL_STAT_OFST))
/* The base address byte offset for the start of the ALT_CLKMGR_SDRPLL component. */
#define ALT_CLKMGR_SDRPLL_OFST        0xc0
/* The start address of the ALT_CLKMGR_SDRPLL component. */
#define ALT_CLKMGR_SDRPLL_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_CLKMGR_ADDR) + ALT_CLKMGR_SDRPLL_OFST))
/* The lower bound address range of the ALT_CLKMGR_SDRPLL component. */
#define ALT_CLKMGR_SDRPLL_LB_ADDR     ALT_CLKMGR_SDRPLL_ADDR
/* The upper bound address range of the ALT_CLKMGR_SDRPLL component. */
#define ALT_CLKMGR_SDRPLL_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_CLKMGR_SDRPLL_ADDR) + 0x20) - 1))


/* The base address byte offset for the start of the ALT_CLKMGR component. */
#define ALT_CLKMGR_OFST        0xffd04000
/* The start address of the ALT_CLKMGR component. */
#define ALT_CLKMGR_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_HPS_ADDR) + ALT_CLKMGR_OFST))
/* The lower bound address range of the ALT_CLKMGR component. */
#define ALT_CLKMGR_LB_ADDR     ALT_CLKMGR_ADDR
/* The upper bound address range of the ALT_CLKMGR component. */
#define ALT_CLKMGR_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_CLKMGR_ADDR) + 0x200) - 1))


/*
 * Component Instance : rstmgr
 * 
 * Instance rstmgr of component ALT_RSTMGR.
 * 
 * 
 */
/* The address of the ALT_RSTMGR_STAT register for the ALT_RSTMGR instance. */
#define ALT_RSTMGR_STAT_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_RSTMGR_ADDR) + ALT_RSTMGR_STAT_OFST))
/* The address of the ALT_RSTMGR_CTL register for the ALT_RSTMGR instance. */
#define ALT_RSTMGR_CTL_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_RSTMGR_ADDR) + ALT_RSTMGR_CTL_OFST))
/* The address of the ALT_RSTMGR_COUNTS register for the ALT_RSTMGR instance. */
#define ALT_RSTMGR_COUNTS_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_RSTMGR_ADDR) + ALT_RSTMGR_COUNTS_OFST))
/* The address of the ALT_RSTMGR_MPUMODRST register for the ALT_RSTMGR instance. */
#define ALT_RSTMGR_MPUMODRST_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_RSTMGR_ADDR) + ALT_RSTMGR_MPUMODRST_OFST))
/* The address of the ALT_RSTMGR_PERMODRST register for the ALT_RSTMGR instance. */
#define ALT_RSTMGR_PERMODRST_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_RSTMGR_ADDR) + ALT_RSTMGR_PERMODRST_OFST))
/* The address of the ALT_RSTMGR_PER2MODRST register for the ALT_RSTMGR instance. */
#define ALT_RSTMGR_PER2MODRST_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_RSTMGR_ADDR) + ALT_RSTMGR_PER2MODRST_OFST))
/* The address of the ALT_RSTMGR_BRGMODRST register for the ALT_RSTMGR instance. */
#define ALT_RSTMGR_BRGMODRST_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_RSTMGR_ADDR) + ALT_RSTMGR_BRGMODRST_OFST))
/* The address of the ALT_RSTMGR_MISCMODRST register for the ALT_RSTMGR instance. */
#define ALT_RSTMGR_MISCMODRST_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_RSTMGR_ADDR) + ALT_RSTMGR_MISCMODRST_OFST))
/* The base address byte offset for the start of the ALT_RSTMGR component. */
#define ALT_RSTMGR_OFST        0xffd05000
/* The start address of the ALT_RSTMGR component. */
#define ALT_RSTMGR_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_HPS_ADDR) + ALT_RSTMGR_OFST))
/* The lower bound address range of the ALT_RSTMGR component. */
#define ALT_RSTMGR_LB_ADDR     ALT_RSTMGR_ADDR
/* The upper bound address range of the ALT_RSTMGR component. */
#define ALT_RSTMGR_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_RSTMGR_ADDR) + 0x100) - 1))


/*
 * Component Instance : sysmgr
 * 
 * Instance sysmgr of component ALT_SYSMGR.
 * 
 * 
 */
/* The address of the ALT_SYSMGR_SILICONID1 register for the ALT_SYSMGR instance. */
#define ALT_SYSMGR_SILICONID1_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_ADDR) + ALT_SYSMGR_SILICONID1_OFST))
/* The address of the ALT_SYSMGR_SILICONID2 register for the ALT_SYSMGR instance. */
#define ALT_SYSMGR_SILICONID2_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_ADDR) + ALT_SYSMGR_SILICONID2_OFST))
/* The address of the ALT_SYSMGR_WDDBG register for the ALT_SYSMGR instance. */
#define ALT_SYSMGR_WDDBG_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_ADDR) + ALT_SYSMGR_WDDBG_OFST))
/* The address of the ALT_SYSMGR_BOOT register for the ALT_SYSMGR instance. */
#define ALT_SYSMGR_BOOT_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_ADDR) + ALT_SYSMGR_BOOT_OFST))
/* The address of the ALT_SYSMGR_HPSINFO register for the ALT_SYSMGR instance. */
#define ALT_SYSMGR_HPSINFO_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_ADDR) + ALT_SYSMGR_HPSINFO_OFST))
/* The address of the ALT_SYSMGR_PARITYINJ register for the ALT_SYSMGR instance. */
#define ALT_SYSMGR_PARITYINJ_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_ADDR) + ALT_SYSMGR_PARITYINJ_OFST))
/*
 * Register Group Instance : fpgaintfgrp
 * 
 * Instance fpgaintfgrp of register group ALT_SYSMGR_FPGAINTF.
 * 
 * 
 */
/* The address of the ALT_SYSMGR_FPGAINTF_GBL register for the ALT_SYSMGR_FPGAINTF instance. */
#define ALT_SYSMGR_FPGAINTF_GBL_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_FPGAINTF_ADDR) + ALT_SYSMGR_FPGAINTF_GBL_OFST))
/* The address of the ALT_SYSMGR_FPGAINTF_INDIV register for the ALT_SYSMGR_FPGAINTF instance. */
#define ALT_SYSMGR_FPGAINTF_INDIV_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_FPGAINTF_ADDR) + ALT_SYSMGR_FPGAINTF_INDIV_OFST))
/* The address of the ALT_SYSMGR_FPGAINTF_MODULE register for the ALT_SYSMGR_FPGAINTF instance. */
#define ALT_SYSMGR_FPGAINTF_MODULE_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_FPGAINTF_ADDR) + ALT_SYSMGR_FPGAINTF_MODULE_OFST))
/* The base address byte offset for the start of the ALT_SYSMGR_FPGAINTF component. */
#define ALT_SYSMGR_FPGAINTF_OFST        0x20
/* The start address of the ALT_SYSMGR_FPGAINTF component. */
#define ALT_SYSMGR_FPGAINTF_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_ADDR) + ALT_SYSMGR_FPGAINTF_OFST))
/* The lower bound address range of the ALT_SYSMGR_FPGAINTF component. */
#define ALT_SYSMGR_FPGAINTF_LB_ADDR     ALT_SYSMGR_FPGAINTF_ADDR
/* The upper bound address range of the ALT_SYSMGR_FPGAINTF component. */
#define ALT_SYSMGR_FPGAINTF_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_SYSMGR_FPGAINTF_ADDR) + 0x10) - 1))


/*
 * Register Group Instance : scanmgrgrp
 * 
 * Instance scanmgrgrp of register group ALT_SYSMGR_SCANMGR.
 * 
 * 
 */
/* The address of the ALT_SYSMGR_SCANMGR_CTL register for the ALT_SYSMGR_SCANMGR instance. */
#define ALT_SYSMGR_SCANMGR_CTL_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_SCANMGR_ADDR) + ALT_SYSMGR_SCANMGR_CTL_OFST))
/* The base address byte offset for the start of the ALT_SYSMGR_SCANMGR component. */
#define ALT_SYSMGR_SCANMGR_OFST        0x30
/* The start address of the ALT_SYSMGR_SCANMGR component. */
#define ALT_SYSMGR_SCANMGR_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_ADDR) + ALT_SYSMGR_SCANMGR_OFST))
/* The lower bound address range of the ALT_SYSMGR_SCANMGR component. */
#define ALT_SYSMGR_SCANMGR_LB_ADDR     ALT_SYSMGR_SCANMGR_ADDR
/* The upper bound address range of the ALT_SYSMGR_SCANMGR component. */
#define ALT_SYSMGR_SCANMGR_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_SYSMGR_SCANMGR_ADDR) + 0x4) - 1))


/*
 * Register Group Instance : frzctrl
 * 
 * Instance frzctrl of register group ALT_SYSMGR_FRZCTL.
 * 
 * 
 */
/* The address of the ALT_SYSMGR_FRZCTL_VIOCTL register for the ALT_SYSMGR_FRZCTL instance. */
#define ALT_SYSMGR_FRZCTL_VIOCTL_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_FRZCTL_ADDR) + ALT_SYSMGR_FRZCTL_VIOCTL_OFST))
/* The address of the ALT_SYSMGR_FRZCTL_HIOCTL register for the ALT_SYSMGR_FRZCTL instance. */
#define ALT_SYSMGR_FRZCTL_HIOCTL_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_FRZCTL_ADDR) + ALT_SYSMGR_FRZCTL_HIOCTL_OFST))
/* The address of the ALT_SYSMGR_FRZCTL_SRC register for the ALT_SYSMGR_FRZCTL instance. */
#define ALT_SYSMGR_FRZCTL_SRC_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_FRZCTL_ADDR) + ALT_SYSMGR_FRZCTL_SRC_OFST))
/* The address of the ALT_SYSMGR_FRZCTL_HWCTL register for the ALT_SYSMGR_FRZCTL instance. */
#define ALT_SYSMGR_FRZCTL_HWCTL_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_FRZCTL_ADDR) + ALT_SYSMGR_FRZCTL_HWCTL_OFST))
/* The base address byte offset for the start of the ALT_SYSMGR_FRZCTL component. */
#define ALT_SYSMGR_FRZCTL_OFST        0x40
/* The start address of the ALT_SYSMGR_FRZCTL component. */
#define ALT_SYSMGR_FRZCTL_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_ADDR) + ALT_SYSMGR_FRZCTL_OFST))
/* The lower bound address range of the ALT_SYSMGR_FRZCTL component. */
#define ALT_SYSMGR_FRZCTL_LB_ADDR     ALT_SYSMGR_FRZCTL_ADDR
/* The upper bound address range of the ALT_SYSMGR_FRZCTL component. */
#define ALT_SYSMGR_FRZCTL_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_SYSMGR_FRZCTL_ADDR) + 0x20) - 1))


/*
 * Register Group Instance : emacgrp
 * 
 * Instance emacgrp of register group ALT_SYSMGR_EMAC.
 * 
 * 
 */
/* The address of the ALT_SYSMGR_EMAC_CTL register for the ALT_SYSMGR_EMAC instance. */
#define ALT_SYSMGR_EMAC_CTL_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_EMAC_ADDR) + ALT_SYSMGR_EMAC_CTL_OFST))
/* The address of the ALT_SYSMGR_EMAC_L3MST register for the ALT_SYSMGR_EMAC instance. */
#define ALT_SYSMGR_EMAC_L3MST_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_EMAC_ADDR) + ALT_SYSMGR_EMAC_L3MST_OFST))
/* The base address byte offset for the start of the ALT_SYSMGR_EMAC component. */
#define ALT_SYSMGR_EMAC_OFST        0x60
/* The start address of the ALT_SYSMGR_EMAC component. */
#define ALT_SYSMGR_EMAC_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_ADDR) + ALT_SYSMGR_EMAC_OFST))
/* The lower bound address range of the ALT_SYSMGR_EMAC component. */
#define ALT_SYSMGR_EMAC_LB_ADDR     ALT_SYSMGR_EMAC_ADDR
/* The upper bound address range of the ALT_SYSMGR_EMAC component. */
#define ALT_SYSMGR_EMAC_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_SYSMGR_EMAC_ADDR) + 0x10) - 1))


/*
 * Register Group Instance : dmagrp
 * 
 * Instance dmagrp of register group ALT_SYSMGR_DMA.
 * 
 * 
 */
/* The address of the ALT_SYSMGR_DMA_CTL register for the ALT_SYSMGR_DMA instance. */
#define ALT_SYSMGR_DMA_CTL_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_DMA_ADDR) + ALT_SYSMGR_DMA_CTL_OFST))
/* The address of the ALT_SYSMGR_DMA_PERSECURITY register for the ALT_SYSMGR_DMA instance. */
#define ALT_SYSMGR_DMA_PERSECURITY_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_DMA_ADDR) + ALT_SYSMGR_DMA_PERSECURITY_OFST))
/* The base address byte offset for the start of the ALT_SYSMGR_DMA component. */
#define ALT_SYSMGR_DMA_OFST        0x70
/* The start address of the ALT_SYSMGR_DMA component. */
#define ALT_SYSMGR_DMA_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_ADDR) + ALT_SYSMGR_DMA_OFST))
/* The lower bound address range of the ALT_SYSMGR_DMA component. */
#define ALT_SYSMGR_DMA_LB_ADDR     ALT_SYSMGR_DMA_ADDR
/* The upper bound address range of the ALT_SYSMGR_DMA component. */
#define ALT_SYSMGR_DMA_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_SYSMGR_DMA_ADDR) + 0x8) - 1))


/*
 * Register Group Instance : iswgrp
 * 
 * Instance iswgrp of register group ALT_SYSMGR_ISW.
 * 
 * 
 */
/* The address of the ALT_SYSMGR_ISW_HANDOFF register for the ALT_SYSMGR_ISW instance. */
#define ALT_SYSMGR_ISW_HANDOFF_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_ISW_ADDR) + ALT_SYSMGR_ISW_HANDOFF_OFST))
/* The base address byte offset for the start of the ALT_SYSMGR_ISW component. */
#define ALT_SYSMGR_ISW_OFST        0x80
/* The start address of the ALT_SYSMGR_ISW component. */
#define ALT_SYSMGR_ISW_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_ADDR) + ALT_SYSMGR_ISW_OFST))
/* The lower bound address range of the ALT_SYSMGR_ISW component. */
#define ALT_SYSMGR_ISW_LB_ADDR     ALT_SYSMGR_ISW_ADDR
/* The upper bound address range of the ALT_SYSMGR_ISW component. */
#define ALT_SYSMGR_ISW_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_SYSMGR_ISW_ADDR) + 0x20) - 1))


/*
 * Register Group Instance : romcodegrp
 * 
 * Instance romcodegrp of register group ALT_SYSMGR_ROMCODE.
 * 
 * 
 */
/* The address of the ALT_SYSMGR_ROMCODE_CTL register for the ALT_SYSMGR_ROMCODE instance. */
#define ALT_SYSMGR_ROMCODE_CTL_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_ROMCODE_ADDR) + ALT_SYSMGR_ROMCODE_CTL_OFST))
/* The address of the ALT_SYSMGR_ROMCODE_CPU1STARTADDR register for the ALT_SYSMGR_ROMCODE instance. */
#define ALT_SYSMGR_ROMCODE_CPU1STARTADDR_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_ROMCODE_ADDR) + ALT_SYSMGR_ROMCODE_CPU1STARTADDR_OFST))
/* The address of the ALT_SYSMGR_ROMCODE_INITSWSTATE register for the ALT_SYSMGR_ROMCODE instance. */
#define ALT_SYSMGR_ROMCODE_INITSWSTATE_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_ROMCODE_ADDR) + ALT_SYSMGR_ROMCODE_INITSWSTATE_OFST))
/* The address of the ALT_SYSMGR_ROMCODE_INITSWLASTLD register for the ALT_SYSMGR_ROMCODE instance. */
#define ALT_SYSMGR_ROMCODE_INITSWLASTLD_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_ROMCODE_ADDR) + ALT_SYSMGR_ROMCODE_INITSWLASTLD_OFST))
/* The address of the ALT_SYSMGR_ROMCODE_BOOTROMSWSTATE register for the ALT_SYSMGR_ROMCODE instance. */
#define ALT_SYSMGR_ROMCODE_BOOTROMSWSTATE_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_ROMCODE_ADDR) + ALT_SYSMGR_ROMCODE_BOOTROMSWSTATE_OFST))
/*
 * Register Group Instance : romcodegrp_warmramgrp
 * 
 * Instance romcodegrp_warmramgrp of register group ALT_SYSMGR_ROMCODE_WARMRAM.
 * 
 * 
 */
/* The address of the ALT_SYSMGR_ROMCODE_WARMRAM_EN register for the ALT_SYSMGR_ROMCODE_ROMCODE_WARMRAMGRP instance. */
#define ALT_SYSMGR_ROMCODE_ROMCODE_WARMRAM_EN_ADDR  ALT_SYSMGR_ROMCODE_WARMRAM_EN_ADDR(ALT_SYSMGR_ROMCODE_ROMCODE_WARMRAMGRP_ADDR)
/* The address of the ALT_SYSMGR_ROMCODE_WARMRAM_DATASTART register for the ALT_SYSMGR_ROMCODE_ROMCODE_WARMRAMGRP instance. */
#define ALT_SYSMGR_ROMCODE_ROMCODE_WARMRAM_DATASTART_ADDR  ALT_SYSMGR_ROMCODE_WARMRAM_DATASTART_ADDR(ALT_SYSMGR_ROMCODE_ROMCODE_WARMRAMGRP_ADDR)
/* The address of the ALT_SYSMGR_ROMCODE_WARMRAM_LEN register for the ALT_SYSMGR_ROMCODE_ROMCODE_WARMRAMGRP instance. */
#define ALT_SYSMGR_ROMCODE_ROMCODE_WARMRAM_LEN_ADDR  ALT_SYSMGR_ROMCODE_WARMRAM_LEN_ADDR(ALT_SYSMGR_ROMCODE_ROMCODE_WARMRAMGRP_ADDR)
/* The address of the ALT_SYSMGR_ROMCODE_WARMRAM_EXECUTION register for the ALT_SYSMGR_ROMCODE_ROMCODE_WARMRAMGRP instance. */
#define ALT_SYSMGR_ROMCODE_ROMCODE_WARMRAM_EXECUTION_ADDR  ALT_SYSMGR_ROMCODE_WARMRAM_EXECUTION_ADDR(ALT_SYSMGR_ROMCODE_ROMCODE_WARMRAMGRP_ADDR)
/* The address of the ALT_SYSMGR_ROMCODE_WARMRAM_CRC register for the ALT_SYSMGR_ROMCODE_ROMCODE_WARMRAMGRP instance. */
#define ALT_SYSMGR_ROMCODE_ROMCODE_WARMRAM_CRC_ADDR  ALT_SYSMGR_ROMCODE_WARMRAM_CRC_ADDR(ALT_SYSMGR_ROMCODE_ROMCODE_WARMRAMGRP_ADDR)
/* The base address byte offset for the start of the ALT_SYSMGR_ROMCODE_ROMCODE_WARMRAMGRP component. */
#define ALT_SYSMGR_ROMCODE_ROMCODE_WARMRAMGRP_OFST        0x20
/* The start address of the ALT_SYSMGR_ROMCODE_ROMCODE_WARMRAMGRP component. */
#define ALT_SYSMGR_ROMCODE_ROMCODE_WARMRAMGRP_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_ROMCODE_ADDR) + ALT_SYSMGR_ROMCODE_ROMCODE_WARMRAMGRP_OFST))
/* The lower bound address range of the ALT_SYSMGR_ROMCODE_ROMCODE_WARMRAMGRP component. */
#define ALT_SYSMGR_ROMCODE_ROMCODE_WARMRAMGRP_LB_ADDR     ALT_SYSMGR_ROMCODE_ROMCODE_WARMRAMGRP_ADDR
/* The upper bound address range of the ALT_SYSMGR_ROMCODE_ROMCODE_WARMRAMGRP component. */
#define ALT_SYSMGR_ROMCODE_ROMCODE_WARMRAMGRP_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_SYSMGR_ROMCODE_ROMCODE_WARMRAMGRP_ADDR) + 0x20) - 1))


/* The base address byte offset for the start of the ALT_SYSMGR_ROMCODE component. */
#define ALT_SYSMGR_ROMCODE_OFST        0xc0
/* The start address of the ALT_SYSMGR_ROMCODE component. */
#define ALT_SYSMGR_ROMCODE_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_ADDR) + ALT_SYSMGR_ROMCODE_OFST))
/* The lower bound address range of the ALT_SYSMGR_ROMCODE component. */
#define ALT_SYSMGR_ROMCODE_LB_ADDR     ALT_SYSMGR_ROMCODE_ADDR
/* The upper bound address range of the ALT_SYSMGR_ROMCODE component. */
#define ALT_SYSMGR_ROMCODE_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_SYSMGR_ROMCODE_ADDR) + 0x40) - 1))


/*
 * Register Group Instance : romhwgrp
 * 
 * Instance romhwgrp of register group ALT_SYSMGR_ROMHW.
 * 
 * 
 */
/* The address of the ALT_SYSMGR_ROMHW_CTL register for the ALT_SYSMGR_ROMHW instance. */
#define ALT_SYSMGR_ROMHW_CTL_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_ROMHW_ADDR) + ALT_SYSMGR_ROMHW_CTL_OFST))
/* The base address byte offset for the start of the ALT_SYSMGR_ROMHW component. */
#define ALT_SYSMGR_ROMHW_OFST        0x100
/* The start address of the ALT_SYSMGR_ROMHW component. */
#define ALT_SYSMGR_ROMHW_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_ADDR) + ALT_SYSMGR_ROMHW_OFST))
/* The lower bound address range of the ALT_SYSMGR_ROMHW component. */
#define ALT_SYSMGR_ROMHW_LB_ADDR     ALT_SYSMGR_ROMHW_ADDR
/* The upper bound address range of the ALT_SYSMGR_ROMHW component. */
#define ALT_SYSMGR_ROMHW_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_SYSMGR_ROMHW_ADDR) + 0x4) - 1))


/*
 * Register Group Instance : sdmmcgrp
 * 
 * Instance sdmmcgrp of register group ALT_SYSMGR_SDMMC.
 * 
 * 
 */
/* The address of the ALT_SYSMGR_SDMMC_CTL register for the ALT_SYSMGR_SDMMC instance. */
#define ALT_SYSMGR_SDMMC_CTL_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_SDMMC_ADDR) + ALT_SYSMGR_SDMMC_CTL_OFST))
/* The address of the ALT_SYSMGR_SDMMC_L3MST register for the ALT_SYSMGR_SDMMC instance. */
#define ALT_SYSMGR_SDMMC_L3MST_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_SDMMC_ADDR) + ALT_SYSMGR_SDMMC_L3MST_OFST))
/* The base address byte offset for the start of the ALT_SYSMGR_SDMMC component. */
#define ALT_SYSMGR_SDMMC_OFST        0x108
/* The start address of the ALT_SYSMGR_SDMMC component. */
#define ALT_SYSMGR_SDMMC_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_ADDR) + ALT_SYSMGR_SDMMC_OFST))
/* The lower bound address range of the ALT_SYSMGR_SDMMC component. */
#define ALT_SYSMGR_SDMMC_LB_ADDR     ALT_SYSMGR_SDMMC_ADDR
/* The upper bound address range of the ALT_SYSMGR_SDMMC component. */
#define ALT_SYSMGR_SDMMC_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_SYSMGR_SDMMC_ADDR) + 0x8) - 1))


/*
 * Register Group Instance : nandgrp
 * 
 * Instance nandgrp of register group ALT_SYSMGR_NAND.
 * 
 * 
 */
/* The address of the ALT_SYSMGR_NAND_BOOTSTRAP register for the ALT_SYSMGR_NAND instance. */
#define ALT_SYSMGR_NAND_BOOTSTRAP_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_NAND_ADDR) + ALT_SYSMGR_NAND_BOOTSTRAP_OFST))
/* The address of the ALT_SYSMGR_NAND_L3MST register for the ALT_SYSMGR_NAND instance. */
#define ALT_SYSMGR_NAND_L3MST_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_NAND_ADDR) + ALT_SYSMGR_NAND_L3MST_OFST))
/* The base address byte offset for the start of the ALT_SYSMGR_NAND component. */
#define ALT_SYSMGR_NAND_OFST        0x110
/* The start address of the ALT_SYSMGR_NAND component. */
#define ALT_SYSMGR_NAND_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_ADDR) + ALT_SYSMGR_NAND_OFST))
/* The lower bound address range of the ALT_SYSMGR_NAND component. */
#define ALT_SYSMGR_NAND_LB_ADDR     ALT_SYSMGR_NAND_ADDR
/* The upper bound address range of the ALT_SYSMGR_NAND component. */
#define ALT_SYSMGR_NAND_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_SYSMGR_NAND_ADDR) + 0x8) - 1))


/*
 * Register Group Instance : usbgrp
 * 
 * Instance usbgrp of register group ALT_SYSMGR_USB.
 * 
 * 
 */
/* The address of the ALT_SYSMGR_USB_L3MST register for the ALT_SYSMGR_USB instance. */
#define ALT_SYSMGR_USB_L3MST_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_USB_ADDR) + ALT_SYSMGR_USB_L3MST_OFST))
/* The base address byte offset for the start of the ALT_SYSMGR_USB component. */
#define ALT_SYSMGR_USB_OFST        0x118
/* The start address of the ALT_SYSMGR_USB component. */
#define ALT_SYSMGR_USB_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_ADDR) + ALT_SYSMGR_USB_OFST))
/* The lower bound address range of the ALT_SYSMGR_USB component. */
#define ALT_SYSMGR_USB_LB_ADDR     ALT_SYSMGR_USB_ADDR
/* The upper bound address range of the ALT_SYSMGR_USB component. */
#define ALT_SYSMGR_USB_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_SYSMGR_USB_ADDR) + 0x4) - 1))


/*
 * Register Group Instance : eccgrp
 * 
 * Instance eccgrp of register group ALT_SYSMGR_ECC.
 * 
 * 
 */
/* The address of the ALT_SYSMGR_ECC_L2 register for the ALT_SYSMGR_ECC instance. */
#define ALT_SYSMGR_ECC_L2_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_ECC_ADDR) + ALT_SYSMGR_ECC_L2_OFST))
/* The address of the ALT_SYSMGR_ECC_OCRAM register for the ALT_SYSMGR_ECC instance. */
#define ALT_SYSMGR_ECC_OCRAM_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_ECC_ADDR) + ALT_SYSMGR_ECC_OCRAM_OFST))
/* The address of the ALT_SYSMGR_ECC_USB0 register for the ALT_SYSMGR_ECC instance. */
#define ALT_SYSMGR_ECC_USB0_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_ECC_ADDR) + ALT_SYSMGR_ECC_USB0_OFST))
/* The address of the ALT_SYSMGR_ECC_USB1 register for the ALT_SYSMGR_ECC instance. */
#define ALT_SYSMGR_ECC_USB1_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_ECC_ADDR) + ALT_SYSMGR_ECC_USB1_OFST))
/* The address of the ALT_SYSMGR_ECC_EMAC0 register for the ALT_SYSMGR_ECC instance. */
#define ALT_SYSMGR_ECC_EMAC0_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_ECC_ADDR) + ALT_SYSMGR_ECC_EMAC0_OFST))
/* The address of the ALT_SYSMGR_ECC_EMAC1 register for the ALT_SYSMGR_ECC instance. */
#define ALT_SYSMGR_ECC_EMAC1_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_ECC_ADDR) + ALT_SYSMGR_ECC_EMAC1_OFST))
/* The address of the ALT_SYSMGR_ECC_DMA register for the ALT_SYSMGR_ECC instance. */
#define ALT_SYSMGR_ECC_DMA_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_ECC_ADDR) + ALT_SYSMGR_ECC_DMA_OFST))
/* The address of the ALT_SYSMGR_ECC_CAN0 register for the ALT_SYSMGR_ECC instance. */
#define ALT_SYSMGR_ECC_CAN0_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_ECC_ADDR) + ALT_SYSMGR_ECC_CAN0_OFST))
/* The address of the ALT_SYSMGR_ECC_CAN1 register for the ALT_SYSMGR_ECC instance. */
#define ALT_SYSMGR_ECC_CAN1_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_ECC_ADDR) + ALT_SYSMGR_ECC_CAN1_OFST))
/* The address of the ALT_SYSMGR_ECC_NAND register for the ALT_SYSMGR_ECC instance. */
#define ALT_SYSMGR_ECC_NAND_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_ECC_ADDR) + ALT_SYSMGR_ECC_NAND_OFST))
/* The address of the ALT_SYSMGR_ECC_QSPI register for the ALT_SYSMGR_ECC instance. */
#define ALT_SYSMGR_ECC_QSPI_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_ECC_ADDR) + ALT_SYSMGR_ECC_QSPI_OFST))
/* The address of the ALT_SYSMGR_ECC_SDMMC register for the ALT_SYSMGR_ECC instance. */
#define ALT_SYSMGR_ECC_SDMMC_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_ECC_ADDR) + ALT_SYSMGR_ECC_SDMMC_OFST))
/* The base address byte offset for the start of the ALT_SYSMGR_ECC component. */
#define ALT_SYSMGR_ECC_OFST        0x140
/* The start address of the ALT_SYSMGR_ECC component. */
#define ALT_SYSMGR_ECC_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_ADDR) + ALT_SYSMGR_ECC_OFST))
/* The lower bound address range of the ALT_SYSMGR_ECC component. */
#define ALT_SYSMGR_ECC_LB_ADDR     ALT_SYSMGR_ECC_ADDR
/* The upper bound address range of the ALT_SYSMGR_ECC component. */
#define ALT_SYSMGR_ECC_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_SYSMGR_ECC_ADDR) + 0x40) - 1))


/*
 * Register Group Instance : pinmuxgrp
 * 
 * Instance pinmuxgrp of register group ALT_SYSMGR_PINMUX.
 * 
 * 
 */
/* The address of the ALT_SYSMGR_PINMUX_EMACIO0 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_EMACIO0_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_EMACIO0_OFST))
/* The address of the ALT_SYSMGR_PINMUX_EMACIO1 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_EMACIO1_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_EMACIO1_OFST))
/* The address of the ALT_SYSMGR_PINMUX_EMACIO2 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_EMACIO2_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_EMACIO2_OFST))
/* The address of the ALT_SYSMGR_PINMUX_EMACIO3 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_EMACIO3_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_EMACIO3_OFST))
/* The address of the ALT_SYSMGR_PINMUX_EMACIO4 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_EMACIO4_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_EMACIO4_OFST))
/* The address of the ALT_SYSMGR_PINMUX_EMACIO5 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_EMACIO5_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_EMACIO5_OFST))
/* The address of the ALT_SYSMGR_PINMUX_EMACIO6 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_EMACIO6_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_EMACIO6_OFST))
/* The address of the ALT_SYSMGR_PINMUX_EMACIO7 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_EMACIO7_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_EMACIO7_OFST))
/* The address of the ALT_SYSMGR_PINMUX_EMACIO8 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_EMACIO8_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_EMACIO8_OFST))
/* The address of the ALT_SYSMGR_PINMUX_EMACIO9 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_EMACIO9_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_EMACIO9_OFST))
/* The address of the ALT_SYSMGR_PINMUX_EMACIO10 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_EMACIO10_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_EMACIO10_OFST))
/* The address of the ALT_SYSMGR_PINMUX_EMACIO11 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_EMACIO11_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_EMACIO11_OFST))
/* The address of the ALT_SYSMGR_PINMUX_EMACIO12 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_EMACIO12_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_EMACIO12_OFST))
/* The address of the ALT_SYSMGR_PINMUX_EMACIO13 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_EMACIO13_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_EMACIO13_OFST))
/* The address of the ALT_SYSMGR_PINMUX_EMACIO14 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_EMACIO14_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_EMACIO14_OFST))
/* The address of the ALT_SYSMGR_PINMUX_EMACIO15 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_EMACIO15_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_EMACIO15_OFST))
/* The address of the ALT_SYSMGR_PINMUX_EMACIO16 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_EMACIO16_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_EMACIO16_OFST))
/* The address of the ALT_SYSMGR_PINMUX_EMACIO17 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_EMACIO17_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_EMACIO17_OFST))
/* The address of the ALT_SYSMGR_PINMUX_EMACIO18 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_EMACIO18_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_EMACIO18_OFST))
/* The address of the ALT_SYSMGR_PINMUX_EMACIO19 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_EMACIO19_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_EMACIO19_OFST))
/* The address of the ALT_SYSMGR_PINMUX_FLSHIO0 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_FLSHIO0_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_FLSHIO0_OFST))
/* The address of the ALT_SYSMGR_PINMUX_FLSHIO1 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_FLSHIO1_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_FLSHIO1_OFST))
/* The address of the ALT_SYSMGR_PINMUX_FLSHIO2 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_FLSHIO2_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_FLSHIO2_OFST))
/* The address of the ALT_SYSMGR_PINMUX_FLSHIO3 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_FLSHIO3_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_FLSHIO3_OFST))
/* The address of the ALT_SYSMGR_PINMUX_FLSHIO4 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_FLSHIO4_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_FLSHIO4_OFST))
/* The address of the ALT_SYSMGR_PINMUX_FLSHIO5 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_FLSHIO5_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_FLSHIO5_OFST))
/* The address of the ALT_SYSMGR_PINMUX_FLSHIO6 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_FLSHIO6_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_FLSHIO6_OFST))
/* The address of the ALT_SYSMGR_PINMUX_FLSHIO7 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_FLSHIO7_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_FLSHIO7_OFST))
/* The address of the ALT_SYSMGR_PINMUX_FLSHIO8 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_FLSHIO8_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_FLSHIO8_OFST))
/* The address of the ALT_SYSMGR_PINMUX_FLSHIO9 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_FLSHIO9_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_FLSHIO9_OFST))
/* The address of the ALT_SYSMGR_PINMUX_FLSHIO10 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_FLSHIO10_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_FLSHIO10_OFST))
/* The address of the ALT_SYSMGR_PINMUX_FLSHIO11 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_FLSHIO11_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_FLSHIO11_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GENERALIO0 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GENERALIO0_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GENERALIO0_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GENERALIO1 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GENERALIO1_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GENERALIO1_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GENERALIO2 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GENERALIO2_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GENERALIO2_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GENERALIO3 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GENERALIO3_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GENERALIO3_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GENERALIO4 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GENERALIO4_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GENERALIO4_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GENERALIO5 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GENERALIO5_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GENERALIO5_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GENERALIO6 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GENERALIO6_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GENERALIO6_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GENERALIO7 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GENERALIO7_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GENERALIO7_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GENERALIO8 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GENERALIO8_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GENERALIO8_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GENERALIO9 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GENERALIO9_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GENERALIO9_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GENERALIO10 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GENERALIO10_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GENERALIO10_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GENERALIO11 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GENERALIO11_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GENERALIO11_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GENERALIO12 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GENERALIO12_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GENERALIO12_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GENERALIO13 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GENERALIO13_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GENERALIO13_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GENERALIO14 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GENERALIO14_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GENERALIO14_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GENERALIO15 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GENERALIO15_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GENERALIO15_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GENERALIO16 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GENERALIO16_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GENERALIO16_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GENERALIO17 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GENERALIO17_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GENERALIO17_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GENERALIO18 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GENERALIO18_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GENERALIO18_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GENERALIO19 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GENERALIO19_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GENERALIO19_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GENERALIO20 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GENERALIO20_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GENERALIO20_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GENERALIO21 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GENERALIO21_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GENERALIO21_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GENERALIO22 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GENERALIO22_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GENERALIO22_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GENERALIO23 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GENERALIO23_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GENERALIO23_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GENERALIO24 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GENERALIO24_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GENERALIO24_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GENERALIO25 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GENERALIO25_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GENERALIO25_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GENERALIO26 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GENERALIO26_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GENERALIO26_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GENERALIO27 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GENERALIO27_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GENERALIO27_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GENERALIO28 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GENERALIO28_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GENERALIO28_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GENERALIO29 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GENERALIO29_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GENERALIO29_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GENERALIO30 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GENERALIO30_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GENERALIO30_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GENERALIO31 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GENERALIO31_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GENERALIO31_OFST))
/* The address of the ALT_SYSMGR_PINMUX_MIXED1IO0 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_MIXED1IO0_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_MIXED1IO0_OFST))
/* The address of the ALT_SYSMGR_PINMUX_MIXED1IO1 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_MIXED1IO1_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_MIXED1IO1_OFST))
/* The address of the ALT_SYSMGR_PINMUX_MIXED1IO2 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_MIXED1IO2_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_MIXED1IO2_OFST))
/* The address of the ALT_SYSMGR_PINMUX_MIXED1IO3 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_MIXED1IO3_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_MIXED1IO3_OFST))
/* The address of the ALT_SYSMGR_PINMUX_MIXED1IO4 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_MIXED1IO4_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_MIXED1IO4_OFST))
/* The address of the ALT_SYSMGR_PINMUX_MIXED1IO5 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_MIXED1IO5_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_MIXED1IO5_OFST))
/* The address of the ALT_SYSMGR_PINMUX_MIXED1IO6 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_MIXED1IO6_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_MIXED1IO6_OFST))
/* The address of the ALT_SYSMGR_PINMUX_MIXED1IO7 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_MIXED1IO7_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_MIXED1IO7_OFST))
/* The address of the ALT_SYSMGR_PINMUX_MIXED1IO8 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_MIXED1IO8_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_MIXED1IO8_OFST))
/* The address of the ALT_SYSMGR_PINMUX_MIXED1IO9 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_MIXED1IO9_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_MIXED1IO9_OFST))
/* The address of the ALT_SYSMGR_PINMUX_MIXED1IO10 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_MIXED1IO10_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_MIXED1IO10_OFST))
/* The address of the ALT_SYSMGR_PINMUX_MIXED1IO11 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_MIXED1IO11_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_MIXED1IO11_OFST))
/* The address of the ALT_SYSMGR_PINMUX_MIXED1IO12 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_MIXED1IO12_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_MIXED1IO12_OFST))
/* The address of the ALT_SYSMGR_PINMUX_MIXED1IO13 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_MIXED1IO13_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_MIXED1IO13_OFST))
/* The address of the ALT_SYSMGR_PINMUX_MIXED1IO14 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_MIXED1IO14_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_MIXED1IO14_OFST))
/* The address of the ALT_SYSMGR_PINMUX_MIXED1IO15 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_MIXED1IO15_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_MIXED1IO15_OFST))
/* The address of the ALT_SYSMGR_PINMUX_MIXED1IO16 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_MIXED1IO16_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_MIXED1IO16_OFST))
/* The address of the ALT_SYSMGR_PINMUX_MIXED1IO17 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_MIXED1IO17_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_MIXED1IO17_OFST))
/* The address of the ALT_SYSMGR_PINMUX_MIXED1IO18 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_MIXED1IO18_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_MIXED1IO18_OFST))
/* The address of the ALT_SYSMGR_PINMUX_MIXED1IO19 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_MIXED1IO19_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_MIXED1IO19_OFST))
/* The address of the ALT_SYSMGR_PINMUX_MIXED1IO20 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_MIXED1IO20_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_MIXED1IO20_OFST))
/* The address of the ALT_SYSMGR_PINMUX_MIXED1IO21 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_MIXED1IO21_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_MIXED1IO21_OFST))
/* The address of the ALT_SYSMGR_PINMUX_MIXED2IO0 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_MIXED2IO0_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_MIXED2IO0_OFST))
/* The address of the ALT_SYSMGR_PINMUX_MIXED2IO1 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_MIXED2IO1_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_MIXED2IO1_OFST))
/* The address of the ALT_SYSMGR_PINMUX_MIXED2IO2 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_MIXED2IO2_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_MIXED2IO2_OFST))
/* The address of the ALT_SYSMGR_PINMUX_MIXED2IO3 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_MIXED2IO3_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_MIXED2IO3_OFST))
/* The address of the ALT_SYSMGR_PINMUX_MIXED2IO4 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_MIXED2IO4_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_MIXED2IO4_OFST))
/* The address of the ALT_SYSMGR_PINMUX_MIXED2IO5 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_MIXED2IO5_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_MIXED2IO5_OFST))
/* The address of the ALT_SYSMGR_PINMUX_MIXED2IO6 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_MIXED2IO6_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_MIXED2IO6_OFST))
/* The address of the ALT_SYSMGR_PINMUX_MIXED2IO7 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_MIXED2IO7_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_MIXED2IO7_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLINMUX48 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLINMUX48_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLINMUX48_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLINMUX49 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLINMUX49_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLINMUX49_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLINMUX50 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLINMUX50_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLINMUX50_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLINMUX51 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLINMUX51_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLINMUX51_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLINMUX52 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLINMUX52_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLINMUX52_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLINMUX53 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLINMUX53_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLINMUX53_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLINMUX54 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLINMUX54_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLINMUX54_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLINMUX55 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLINMUX55_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLINMUX55_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLINMUX56 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLINMUX56_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLINMUX56_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLINMUX57 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLINMUX57_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLINMUX57_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLINMUX58 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLINMUX58_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLINMUX58_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLINMUX59 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLINMUX59_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLINMUX59_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLINMUX60 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLINMUX60_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLINMUX60_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLINMUX61 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLINMUX61_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLINMUX61_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLINMUX62 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLINMUX62_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLINMUX62_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLINMUX63 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLINMUX63_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLINMUX63_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLINMUX64 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLINMUX64_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLINMUX64_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLINMUX65 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLINMUX65_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLINMUX65_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLINMUX66 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLINMUX66_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLINMUX66_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLINMUX67 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLINMUX67_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLINMUX67_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLINMUX68 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLINMUX68_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLINMUX68_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLINMUX69 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLINMUX69_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLINMUX69_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLINMUX70 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLINMUX70_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLINMUX70_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX0 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX0_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX0_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX1 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX1_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX1_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX2 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX2_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX2_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX3 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX3_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX3_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX4 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX4_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX4_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX5 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX5_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX5_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX6 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX6_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX6_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX7 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX7_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX7_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX8 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX8_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX8_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX9 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX9_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX9_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX10 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX10_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX10_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX11 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX11_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX11_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX12 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX12_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX12_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX13 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX13_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX13_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX14 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX14_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX14_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX15 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX15_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX15_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX16 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX16_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX16_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX17 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX17_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX17_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX18 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX18_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX18_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX19 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX19_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX19_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX20 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX20_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX20_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX21 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX21_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX21_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX22 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX22_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX22_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX23 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX23_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX23_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX24 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX24_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX24_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX25 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX25_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX25_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX26 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX26_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX26_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX27 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX27_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX27_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX28 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX28_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX28_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX29 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX29_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX29_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX30 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX30_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX30_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX31 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX31_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX31_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX32 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX32_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX32_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX33 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX33_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX33_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX34 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX34_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX34_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX35 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX35_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX35_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX36 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX36_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX36_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX37 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX37_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX37_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX38 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX38_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX38_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX39 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX39_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX39_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX40 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX40_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX40_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX41 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX41_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX41_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX42 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX42_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX42_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX43 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX43_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX43_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX44 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX44_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX44_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX45 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX45_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX45_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX46 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX46_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX46_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX47 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX47_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX47_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX48 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX48_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX48_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX49 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX49_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX49_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX50 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX50_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX50_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX51 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX51_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX51_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX52 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX52_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX52_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX53 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX53_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX53_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX54 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX54_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX54_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX55 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX55_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX55_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX56 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX56_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX56_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX57 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX57_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX57_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX58 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX58_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX58_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX59 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX59_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX59_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX60 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX60_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX60_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX61 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX61_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX61_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX62 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX62_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX62_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX63 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX63_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX63_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX64 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX64_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX64_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX65 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX65_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX65_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX66 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX66_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX66_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX67 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX67_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX67_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX68 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX68_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX68_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX69 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX69_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX69_OFST))
/* The address of the ALT_SYSMGR_PINMUX_GPLMUX70 register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_GPLMUX70_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_GPLMUX70_OFST))
/* The address of the ALT_SYSMGR_PINMUX_NANDUSEFPGA register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_NANDUSEFPGA_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_NANDUSEFPGA_OFST))
/* The address of the ALT_SYSMGR_PINMUX_RGMII1USEFPGA register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_RGMII1USEFPGA_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_RGMII1USEFPGA_OFST))
/* The address of the ALT_SYSMGR_PINMUX_I2C0USEFPGA register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_I2C0USEFPGA_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_I2C0USEFPGA_OFST))
/* The address of the ALT_SYSMGR_PINMUX_RGMII0USEFPGA register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_RGMII0USEFPGA_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_RGMII0USEFPGA_OFST))
/* The address of the ALT_SYSMGR_PINMUX_I2C3USEFPGA register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_I2C3USEFPGA_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_I2C3USEFPGA_OFST))
/* The address of the ALT_SYSMGR_PINMUX_I2C2USEFPGA register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_I2C2USEFPGA_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_I2C2USEFPGA_OFST))
/* The address of the ALT_SYSMGR_PINMUX_I2C1USEFPGA register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_I2C1USEFPGA_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_I2C1USEFPGA_OFST))
/* The address of the ALT_SYSMGR_PINMUX_SPIM1USEFPGA register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_SPIM1USEFPGA_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_SPIM1USEFPGA_OFST))
/* The address of the ALT_SYSMGR_PINMUX_SPIM0USEFPGA register for the ALT_SYSMGR_PINMUX instance. */
#define ALT_SYSMGR_PINMUX_SPIM0USEFPGA_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + ALT_SYSMGR_PINMUX_SPIM0USEFPGA_OFST))
/* The base address byte offset for the start of the ALT_SYSMGR_PINMUX component. */
#define ALT_SYSMGR_PINMUX_OFST        0x400
/* The start address of the ALT_SYSMGR_PINMUX component. */
#define ALT_SYSMGR_PINMUX_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_SYSMGR_ADDR) + ALT_SYSMGR_PINMUX_OFST))
/* The lower bound address range of the ALT_SYSMGR_PINMUX component. */
#define ALT_SYSMGR_PINMUX_LB_ADDR     ALT_SYSMGR_PINMUX_ADDR
/* The upper bound address range of the ALT_SYSMGR_PINMUX component. */
#define ALT_SYSMGR_PINMUX_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_SYSMGR_PINMUX_ADDR) + 0x400) - 1))


/* The base address byte offset for the start of the ALT_SYSMGR component. */
#define ALT_SYSMGR_OFST        0xffd08000
/* The start address of the ALT_SYSMGR component. */
#define ALT_SYSMGR_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_HPS_ADDR) + ALT_SYSMGR_OFST))
/* The lower bound address range of the ALT_SYSMGR component. */
#define ALT_SYSMGR_LB_ADDR     ALT_SYSMGR_ADDR
/* The upper bound address range of the ALT_SYSMGR component. */
#define ALT_SYSMGR_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_SYSMGR_ADDR) + 0x4000) - 1))


/*
 * Component Instance : dmanonsecure
 * 
 * Instance dmanonsecure of component ALT_DMANONSECURE.
 * 
 * 
 */
/* The address of the ALT_DMANONSECURE_REG register for the ALT_DMANONSECURE instance. */
#define ALT_DMANONSECURE_REG_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_DMANONSECURE_ADDR) + ALT_DMANONSECURE_REG_OFST))
/* The base address byte offset for the start of the ALT_DMANONSECURE component. */
#define ALT_DMANONSECURE_OFST        0xffe00000
/* The start address of the ALT_DMANONSECURE component. */
#define ALT_DMANONSECURE_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_HPS_ADDR) + ALT_DMANONSECURE_OFST))
/* The lower bound address range of the ALT_DMANONSECURE component. */
#define ALT_DMANONSECURE_LB_ADDR     ALT_DMANONSECURE_ADDR
/* The upper bound address range of the ALT_DMANONSECURE component. */
#define ALT_DMANONSECURE_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_DMANONSECURE_ADDR) + 0x4) - 1))


/*
 * Component Instance : dmasecure
 * 
 * Instance dmasecure of component ALT_DMASECURE.
 * 
 * 
 */
/* The address of the ALT_DMASECURE_REG register for the ALT_DMASECURE instance. */
#define ALT_DMASECURE_REG_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_DMASECURE_ADDR) + ALT_DMASECURE_REG_OFST))
/* The base address byte offset for the start of the ALT_DMASECURE component. */
#define ALT_DMASECURE_OFST        0xffe01000
/* The start address of the ALT_DMASECURE component. */
#define ALT_DMASECURE_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_HPS_ADDR) + ALT_DMASECURE_OFST))
/* The lower bound address range of the ALT_DMASECURE component. */
#define ALT_DMASECURE_LB_ADDR     ALT_DMASECURE_ADDR
/* The upper bound address range of the ALT_DMASECURE component. */
#define ALT_DMASECURE_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_DMASECURE_ADDR) + 0x4) - 1))


/*
 * Component Instance : spis0
 * 
 * Instance spis0 of component ALT_SPIS.
 * 
 * 
 */
/* The address of the ALT_SPIS_CTLR0 register for the ALT_SPIS0 instance. */
#define ALT_SPIS0_CTLR0_ADDR  ALT_SPIS_CTLR0_ADDR(ALT_SPIS0_ADDR)
/* The address of the ALT_SPIS_SPIENR register for the ALT_SPIS0 instance. */
#define ALT_SPIS0_SPIENR_ADDR  ALT_SPIS_SPIENR_ADDR(ALT_SPIS0_ADDR)
/* The address of the ALT_SPIS_MWCR register for the ALT_SPIS0 instance. */
#define ALT_SPIS0_MWCR_ADDR  ALT_SPIS_MWCR_ADDR(ALT_SPIS0_ADDR)
/* The address of the ALT_SPIS_TXFTLR register for the ALT_SPIS0 instance. */
#define ALT_SPIS0_TXFTLR_ADDR  ALT_SPIS_TXFTLR_ADDR(ALT_SPIS0_ADDR)
/* The address of the ALT_SPIS_RXFTLR register for the ALT_SPIS0 instance. */
#define ALT_SPIS0_RXFTLR_ADDR  ALT_SPIS_RXFTLR_ADDR(ALT_SPIS0_ADDR)
/* The address of the ALT_SPIS_TXFLR register for the ALT_SPIS0 instance. */
#define ALT_SPIS0_TXFLR_ADDR  ALT_SPIS_TXFLR_ADDR(ALT_SPIS0_ADDR)
/* The address of the ALT_SPIS_RXFLR register for the ALT_SPIS0 instance. */
#define ALT_SPIS0_RXFLR_ADDR  ALT_SPIS_RXFLR_ADDR(ALT_SPIS0_ADDR)
/* The address of the ALT_SPIS_SR register for the ALT_SPIS0 instance. */
#define ALT_SPIS0_SR_ADDR  ALT_SPIS_SR_ADDR(ALT_SPIS0_ADDR)
/* The address of the ALT_SPIS_IMR register for the ALT_SPIS0 instance. */
#define ALT_SPIS0_IMR_ADDR  ALT_SPIS_IMR_ADDR(ALT_SPIS0_ADDR)
/* The address of the ALT_SPIS_ISR register for the ALT_SPIS0 instance. */
#define ALT_SPIS0_ISR_ADDR  ALT_SPIS_ISR_ADDR(ALT_SPIS0_ADDR)
/* The address of the ALT_SPIS_RISR register for the ALT_SPIS0 instance. */
#define ALT_SPIS0_RISR_ADDR  ALT_SPIS_RISR_ADDR(ALT_SPIS0_ADDR)
/* The address of the ALT_SPIS_TXOICR register for the ALT_SPIS0 instance. */
#define ALT_SPIS0_TXOICR_ADDR  ALT_SPIS_TXOICR_ADDR(ALT_SPIS0_ADDR)
/* The address of the ALT_SPIS_RXOICR register for the ALT_SPIS0 instance. */
#define ALT_SPIS0_RXOICR_ADDR  ALT_SPIS_RXOICR_ADDR(ALT_SPIS0_ADDR)
/* The address of the ALT_SPIS_RXUICR register for the ALT_SPIS0 instance. */
#define ALT_SPIS0_RXUICR_ADDR  ALT_SPIS_RXUICR_ADDR(ALT_SPIS0_ADDR)
/* The address of the ALT_SPIS_ICR register for the ALT_SPIS0 instance. */
#define ALT_SPIS0_ICR_ADDR  ALT_SPIS_ICR_ADDR(ALT_SPIS0_ADDR)
/* The address of the ALT_SPIS_DMACR register for the ALT_SPIS0 instance. */
#define ALT_SPIS0_DMACR_ADDR  ALT_SPIS_DMACR_ADDR(ALT_SPIS0_ADDR)
/* The address of the ALT_SPIS_DMATDLR register for the ALT_SPIS0 instance. */
#define ALT_SPIS0_DMATDLR_ADDR  ALT_SPIS_DMATDLR_ADDR(ALT_SPIS0_ADDR)
/* The address of the ALT_SPIS_DMARDLR register for the ALT_SPIS0 instance. */
#define ALT_SPIS0_DMARDLR_ADDR  ALT_SPIS_DMARDLR_ADDR(ALT_SPIS0_ADDR)
/* The address of the ALT_SPIS_IDR register for the ALT_SPIS0 instance. */
#define ALT_SPIS0_IDR_ADDR  ALT_SPIS_IDR_ADDR(ALT_SPIS0_ADDR)
/* The address of the ALT_SPIS_SPI_VER_ID register for the ALT_SPIS0 instance. */
#define ALT_SPIS0_SPI_VER_ID_ADDR  ALT_SPIS_SPI_VER_ID_ADDR(ALT_SPIS0_ADDR)
/* The address of the ALT_SPIS_DR register for the ALT_SPIS0 instance. */
#define ALT_SPIS0_DR_ADDR  ALT_SPIS_DR_ADDR(ALT_SPIS0_ADDR)
/* The base address byte offset for the start of the ALT_SPIS0 component. */
#define ALT_SPIS0_OFST        0xffe02000
/* The start address of the ALT_SPIS0 component. */
#define ALT_SPIS0_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_HPS_ADDR) + ALT_SPIS0_OFST))
/* The lower bound address range of the ALT_SPIS0 component. */
#define ALT_SPIS0_LB_ADDR     ALT_SPIS0_ADDR
/* The upper bound address range of the ALT_SPIS0 component. */
#define ALT_SPIS0_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_SPIS0_ADDR) + 0x80) - 1))


/*
 * Component Instance : spis1
 * 
 * Instance spis1 of component ALT_SPIS.
 * 
 * 
 */
/* The address of the ALT_SPIS_CTLR0 register for the ALT_SPIS1 instance. */
#define ALT_SPIS1_CTLR0_ADDR  ALT_SPIS_CTLR0_ADDR(ALT_SPIS1_ADDR)
/* The address of the ALT_SPIS_SPIENR register for the ALT_SPIS1 instance. */
#define ALT_SPIS1_SPIENR_ADDR  ALT_SPIS_SPIENR_ADDR(ALT_SPIS1_ADDR)
/* The address of the ALT_SPIS_MWCR register for the ALT_SPIS1 instance. */
#define ALT_SPIS1_MWCR_ADDR  ALT_SPIS_MWCR_ADDR(ALT_SPIS1_ADDR)
/* The address of the ALT_SPIS_TXFTLR register for the ALT_SPIS1 instance. */
#define ALT_SPIS1_TXFTLR_ADDR  ALT_SPIS_TXFTLR_ADDR(ALT_SPIS1_ADDR)
/* The address of the ALT_SPIS_RXFTLR register for the ALT_SPIS1 instance. */
#define ALT_SPIS1_RXFTLR_ADDR  ALT_SPIS_RXFTLR_ADDR(ALT_SPIS1_ADDR)
/* The address of the ALT_SPIS_TXFLR register for the ALT_SPIS1 instance. */
#define ALT_SPIS1_TXFLR_ADDR  ALT_SPIS_TXFLR_ADDR(ALT_SPIS1_ADDR)
/* The address of the ALT_SPIS_RXFLR register for the ALT_SPIS1 instance. */
#define ALT_SPIS1_RXFLR_ADDR  ALT_SPIS_RXFLR_ADDR(ALT_SPIS1_ADDR)
/* The address of the ALT_SPIS_SR register for the ALT_SPIS1 instance. */
#define ALT_SPIS1_SR_ADDR  ALT_SPIS_SR_ADDR(ALT_SPIS1_ADDR)
/* The address of the ALT_SPIS_IMR register for the ALT_SPIS1 instance. */
#define ALT_SPIS1_IMR_ADDR  ALT_SPIS_IMR_ADDR(ALT_SPIS1_ADDR)
/* The address of the ALT_SPIS_ISR register for the ALT_SPIS1 instance. */
#define ALT_SPIS1_ISR_ADDR  ALT_SPIS_ISR_ADDR(ALT_SPIS1_ADDR)
/* The address of the ALT_SPIS_RISR register for the ALT_SPIS1 instance. */
#define ALT_SPIS1_RISR_ADDR  ALT_SPIS_RISR_ADDR(ALT_SPIS1_ADDR)
/* The address of the ALT_SPIS_TXOICR register for the ALT_SPIS1 instance. */
#define ALT_SPIS1_TXOICR_ADDR  ALT_SPIS_TXOICR_ADDR(ALT_SPIS1_ADDR)
/* The address of the ALT_SPIS_RXOICR register for the ALT_SPIS1 instance. */
#define ALT_SPIS1_RXOICR_ADDR  ALT_SPIS_RXOICR_ADDR(ALT_SPIS1_ADDR)
/* The address of the ALT_SPIS_RXUICR register for the ALT_SPIS1 instance. */
#define ALT_SPIS1_RXUICR_ADDR  ALT_SPIS_RXUICR_ADDR(ALT_SPIS1_ADDR)
/* The address of the ALT_SPIS_ICR register for the ALT_SPIS1 instance. */
#define ALT_SPIS1_ICR_ADDR  ALT_SPIS_ICR_ADDR(ALT_SPIS1_ADDR)
/* The address of the ALT_SPIS_DMACR register for the ALT_SPIS1 instance. */
#define ALT_SPIS1_DMACR_ADDR  ALT_SPIS_DMACR_ADDR(ALT_SPIS1_ADDR)
/* The address of the ALT_SPIS_DMATDLR register for the ALT_SPIS1 instance. */
#define ALT_SPIS1_DMATDLR_ADDR  ALT_SPIS_DMATDLR_ADDR(ALT_SPIS1_ADDR)
/* The address of the ALT_SPIS_DMARDLR register for the ALT_SPIS1 instance. */
#define ALT_SPIS1_DMARDLR_ADDR  ALT_SPIS_DMARDLR_ADDR(ALT_SPIS1_ADDR)
/* The address of the ALT_SPIS_IDR register for the ALT_SPIS1 instance. */
#define ALT_SPIS1_IDR_ADDR  ALT_SPIS_IDR_ADDR(ALT_SPIS1_ADDR)
/* The address of the ALT_SPIS_SPI_VER_ID register for the ALT_SPIS1 instance. */
#define ALT_SPIS1_SPI_VER_ID_ADDR  ALT_SPIS_SPI_VER_ID_ADDR(ALT_SPIS1_ADDR)
/* The address of the ALT_SPIS_DR register for the ALT_SPIS1 instance. */
#define ALT_SPIS1_DR_ADDR  ALT_SPIS_DR_ADDR(ALT_SPIS1_ADDR)
/* The base address byte offset for the start of the ALT_SPIS1 component. */
#define ALT_SPIS1_OFST        0xffe03000
/* The start address of the ALT_SPIS1 component. */
#define ALT_SPIS1_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_HPS_ADDR) + ALT_SPIS1_OFST))
/* The lower bound address range of the ALT_SPIS1 component. */
#define ALT_SPIS1_LB_ADDR     ALT_SPIS1_ADDR
/* The upper bound address range of the ALT_SPIS1 component. */
#define ALT_SPIS1_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_SPIS1_ADDR) + 0x80) - 1))


/*
 * Component Instance : spim0
 * 
 * Instance spim0 of component ALT_SPIM.
 * 
 * 
 */
/* The address of the ALT_SPIM_CTLR0 register for the ALT_SPIM0 instance. */
#define ALT_SPIM0_CTLR0_ADDR  ALT_SPIM_CTLR0_ADDR(ALT_SPIM0_ADDR)
/* The address of the ALT_SPIM_CTLR1 register for the ALT_SPIM0 instance. */
#define ALT_SPIM0_CTLR1_ADDR  ALT_SPIM_CTLR1_ADDR(ALT_SPIM0_ADDR)
/* The address of the ALT_SPIM_SPIENR register for the ALT_SPIM0 instance. */
#define ALT_SPIM0_SPIENR_ADDR  ALT_SPIM_SPIENR_ADDR(ALT_SPIM0_ADDR)
/* The address of the ALT_SPIM_MWCR register for the ALT_SPIM0 instance. */
#define ALT_SPIM0_MWCR_ADDR  ALT_SPIM_MWCR_ADDR(ALT_SPIM0_ADDR)
/* The address of the ALT_SPIM_SER register for the ALT_SPIM0 instance. */
#define ALT_SPIM0_SER_ADDR  ALT_SPIM_SER_ADDR(ALT_SPIM0_ADDR)
/* The address of the ALT_SPIM_BAUDR register for the ALT_SPIM0 instance. */
#define ALT_SPIM0_BAUDR_ADDR  ALT_SPIM_BAUDR_ADDR(ALT_SPIM0_ADDR)
/* The address of the ALT_SPIM_TXFTLR register for the ALT_SPIM0 instance. */
#define ALT_SPIM0_TXFTLR_ADDR  ALT_SPIM_TXFTLR_ADDR(ALT_SPIM0_ADDR)
/* The address of the ALT_SPIM_RXFTLR register for the ALT_SPIM0 instance. */
#define ALT_SPIM0_RXFTLR_ADDR  ALT_SPIM_RXFTLR_ADDR(ALT_SPIM0_ADDR)
/* The address of the ALT_SPIM_TXFLR register for the ALT_SPIM0 instance. */
#define ALT_SPIM0_TXFLR_ADDR  ALT_SPIM_TXFLR_ADDR(ALT_SPIM0_ADDR)
/* The address of the ALT_SPIM_RXFLR register for the ALT_SPIM0 instance. */
#define ALT_SPIM0_RXFLR_ADDR  ALT_SPIM_RXFLR_ADDR(ALT_SPIM0_ADDR)
/* The address of the ALT_SPIM_SR register for the ALT_SPIM0 instance. */
#define ALT_SPIM0_SR_ADDR  ALT_SPIM_SR_ADDR(ALT_SPIM0_ADDR)
/* The address of the ALT_SPIM_IMR register for the ALT_SPIM0 instance. */
#define ALT_SPIM0_IMR_ADDR  ALT_SPIM_IMR_ADDR(ALT_SPIM0_ADDR)
/* The address of the ALT_SPIM_ISR register for the ALT_SPIM0 instance. */
#define ALT_SPIM0_ISR_ADDR  ALT_SPIM_ISR_ADDR(ALT_SPIM0_ADDR)
/* The address of the ALT_SPIM_RISR register for the ALT_SPIM0 instance. */
#define ALT_SPIM0_RISR_ADDR  ALT_SPIM_RISR_ADDR(ALT_SPIM0_ADDR)
/* The address of the ALT_SPIM_TXOICR register for the ALT_SPIM0 instance. */
#define ALT_SPIM0_TXOICR_ADDR  ALT_SPIM_TXOICR_ADDR(ALT_SPIM0_ADDR)
/* The address of the ALT_SPIM_RXOICR register for the ALT_SPIM0 instance. */
#define ALT_SPIM0_RXOICR_ADDR  ALT_SPIM_RXOICR_ADDR(ALT_SPIM0_ADDR)
/* The address of the ALT_SPIM_RXUICR register for the ALT_SPIM0 instance. */
#define ALT_SPIM0_RXUICR_ADDR  ALT_SPIM_RXUICR_ADDR(ALT_SPIM0_ADDR)
/* The address of the ALT_SPIM_ICR register for the ALT_SPIM0 instance. */
#define ALT_SPIM0_ICR_ADDR  ALT_SPIM_ICR_ADDR(ALT_SPIM0_ADDR)
/* The address of the ALT_SPIM_DMACR register for the ALT_SPIM0 instance. */
#define ALT_SPIM0_DMACR_ADDR  ALT_SPIM_DMACR_ADDR(ALT_SPIM0_ADDR)
/* The address of the ALT_SPIM_DMATDLR register for the ALT_SPIM0 instance. */
#define ALT_SPIM0_DMATDLR_ADDR  ALT_SPIM_DMATDLR_ADDR(ALT_SPIM0_ADDR)
/* The address of the ALT_SPIM_DMARDLR register for the ALT_SPIM0 instance. */
#define ALT_SPIM0_DMARDLR_ADDR  ALT_SPIM_DMARDLR_ADDR(ALT_SPIM0_ADDR)
/* The address of the ALT_SPIM_IDR register for the ALT_SPIM0 instance. */
#define ALT_SPIM0_IDR_ADDR  ALT_SPIM_IDR_ADDR(ALT_SPIM0_ADDR)
/* The address of the ALT_SPIM_SPI_VER_ID register for the ALT_SPIM0 instance. */
#define ALT_SPIM0_SPI_VER_ID_ADDR  ALT_SPIM_SPI_VER_ID_ADDR(ALT_SPIM0_ADDR)
/* The address of the ALT_SPIM_DR register for the ALT_SPIM0 instance. */
#define ALT_SPIM0_DR_ADDR  ALT_SPIM_DR_ADDR(ALT_SPIM0_ADDR)
/* The address of the ALT_SPIM_RX_SMPL_DLY register for the ALT_SPIM0 instance. */
#define ALT_SPIM0_RX_SMPL_DLY_ADDR  ALT_SPIM_RX_SMPL_DLY_ADDR(ALT_SPIM0_ADDR)
/* The base address byte offset for the start of the ALT_SPIM0 component. */
#define ALT_SPIM0_OFST        0xfff00000
/* The start address of the ALT_SPIM0 component. */
#define ALT_SPIM0_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_HPS_ADDR) + ALT_SPIM0_OFST))
/* The lower bound address range of the ALT_SPIM0 component. */
#define ALT_SPIM0_LB_ADDR     ALT_SPIM0_ADDR
/* The upper bound address range of the ALT_SPIM0 component. */
#define ALT_SPIM0_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_SPIM0_ADDR) + 0x100) - 1))


/*
 * Component Instance : spim1
 * 
 * Instance spim1 of component ALT_SPIM.
 * 
 * 
 */
/* The address of the ALT_SPIM_CTLR0 register for the ALT_SPIM1 instance. */
#define ALT_SPIM1_CTLR0_ADDR  ALT_SPIM_CTLR0_ADDR(ALT_SPIM1_ADDR)
/* The address of the ALT_SPIM_CTLR1 register for the ALT_SPIM1 instance. */
#define ALT_SPIM1_CTLR1_ADDR  ALT_SPIM_CTLR1_ADDR(ALT_SPIM1_ADDR)
/* The address of the ALT_SPIM_SPIENR register for the ALT_SPIM1 instance. */
#define ALT_SPIM1_SPIENR_ADDR  ALT_SPIM_SPIENR_ADDR(ALT_SPIM1_ADDR)
/* The address of the ALT_SPIM_MWCR register for the ALT_SPIM1 instance. */
#define ALT_SPIM1_MWCR_ADDR  ALT_SPIM_MWCR_ADDR(ALT_SPIM1_ADDR)
/* The address of the ALT_SPIM_SER register for the ALT_SPIM1 instance. */
#define ALT_SPIM1_SER_ADDR  ALT_SPIM_SER_ADDR(ALT_SPIM1_ADDR)
/* The address of the ALT_SPIM_BAUDR register for the ALT_SPIM1 instance. */
#define ALT_SPIM1_BAUDR_ADDR  ALT_SPIM_BAUDR_ADDR(ALT_SPIM1_ADDR)
/* The address of the ALT_SPIM_TXFTLR register for the ALT_SPIM1 instance. */
#define ALT_SPIM1_TXFTLR_ADDR  ALT_SPIM_TXFTLR_ADDR(ALT_SPIM1_ADDR)
/* The address of the ALT_SPIM_RXFTLR register for the ALT_SPIM1 instance. */
#define ALT_SPIM1_RXFTLR_ADDR  ALT_SPIM_RXFTLR_ADDR(ALT_SPIM1_ADDR)
/* The address of the ALT_SPIM_TXFLR register for the ALT_SPIM1 instance. */
#define ALT_SPIM1_TXFLR_ADDR  ALT_SPIM_TXFLR_ADDR(ALT_SPIM1_ADDR)
/* The address of the ALT_SPIM_RXFLR register for the ALT_SPIM1 instance. */
#define ALT_SPIM1_RXFLR_ADDR  ALT_SPIM_RXFLR_ADDR(ALT_SPIM1_ADDR)
/* The address of the ALT_SPIM_SR register for the ALT_SPIM1 instance. */
#define ALT_SPIM1_SR_ADDR  ALT_SPIM_SR_ADDR(ALT_SPIM1_ADDR)
/* The address of the ALT_SPIM_IMR register for the ALT_SPIM1 instance. */
#define ALT_SPIM1_IMR_ADDR  ALT_SPIM_IMR_ADDR(ALT_SPIM1_ADDR)
/* The address of the ALT_SPIM_ISR register for the ALT_SPIM1 instance. */
#define ALT_SPIM1_ISR_ADDR  ALT_SPIM_ISR_ADDR(ALT_SPIM1_ADDR)
/* The address of the ALT_SPIM_RISR register for the ALT_SPIM1 instance. */
#define ALT_SPIM1_RISR_ADDR  ALT_SPIM_RISR_ADDR(ALT_SPIM1_ADDR)
/* The address of the ALT_SPIM_TXOICR register for the ALT_SPIM1 instance. */
#define ALT_SPIM1_TXOICR_ADDR  ALT_SPIM_TXOICR_ADDR(ALT_SPIM1_ADDR)
/* The address of the ALT_SPIM_RXOICR register for the ALT_SPIM1 instance. */
#define ALT_SPIM1_RXOICR_ADDR  ALT_SPIM_RXOICR_ADDR(ALT_SPIM1_ADDR)
/* The address of the ALT_SPIM_RXUICR register for the ALT_SPIM1 instance. */
#define ALT_SPIM1_RXUICR_ADDR  ALT_SPIM_RXUICR_ADDR(ALT_SPIM1_ADDR)
/* The address of the ALT_SPIM_ICR register for the ALT_SPIM1 instance. */
#define ALT_SPIM1_ICR_ADDR  ALT_SPIM_ICR_ADDR(ALT_SPIM1_ADDR)
/* The address of the ALT_SPIM_DMACR register for the ALT_SPIM1 instance. */
#define ALT_SPIM1_DMACR_ADDR  ALT_SPIM_DMACR_ADDR(ALT_SPIM1_ADDR)
/* The address of the ALT_SPIM_DMATDLR register for the ALT_SPIM1 instance. */
#define ALT_SPIM1_DMATDLR_ADDR  ALT_SPIM_DMATDLR_ADDR(ALT_SPIM1_ADDR)
/* The address of the ALT_SPIM_DMARDLR register for the ALT_SPIM1 instance. */
#define ALT_SPIM1_DMARDLR_ADDR  ALT_SPIM_DMARDLR_ADDR(ALT_SPIM1_ADDR)
/* The address of the ALT_SPIM_IDR register for the ALT_SPIM1 instance. */
#define ALT_SPIM1_IDR_ADDR  ALT_SPIM_IDR_ADDR(ALT_SPIM1_ADDR)
/* The address of the ALT_SPIM_SPI_VER_ID register for the ALT_SPIM1 instance. */
#define ALT_SPIM1_SPI_VER_ID_ADDR  ALT_SPIM_SPI_VER_ID_ADDR(ALT_SPIM1_ADDR)
/* The address of the ALT_SPIM_DR register for the ALT_SPIM1 instance. */
#define ALT_SPIM1_DR_ADDR  ALT_SPIM_DR_ADDR(ALT_SPIM1_ADDR)
/* The address of the ALT_SPIM_RX_SMPL_DLY register for the ALT_SPIM1 instance. */
#define ALT_SPIM1_RX_SMPL_DLY_ADDR  ALT_SPIM_RX_SMPL_DLY_ADDR(ALT_SPIM1_ADDR)
/* The base address byte offset for the start of the ALT_SPIM1 component. */
#define ALT_SPIM1_OFST        0xfff01000
/* The start address of the ALT_SPIM1 component. */
#define ALT_SPIM1_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_HPS_ADDR) + ALT_SPIM1_OFST))
/* The lower bound address range of the ALT_SPIM1 component. */
#define ALT_SPIM1_LB_ADDR     ALT_SPIM1_ADDR
/* The upper bound address range of the ALT_SPIM1 component. */
#define ALT_SPIM1_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_SPIM1_ADDR) + 0x100) - 1))


/*
 * Component Instance : scanmgr
 * 
 * Instance scanmgr of component ALT_SCANMGR.
 * 
 * 
 */
/* The address of the ALT_SCANMGR_STAT register for the ALT_SCANMGR instance. */
#define ALT_SCANMGR_STAT_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SCANMGR_ADDR) + ALT_SCANMGR_STAT_OFST))
/* The address of the ALT_SCANMGR_EN register for the ALT_SCANMGR instance. */
#define ALT_SCANMGR_EN_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SCANMGR_ADDR) + ALT_SCANMGR_EN_OFST))
/* The address of the ALT_SCANMGR_FIFOSINGLEBYTE register for the ALT_SCANMGR instance. */
#define ALT_SCANMGR_FIFOSINGLEBYTE_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SCANMGR_ADDR) + ALT_SCANMGR_FIFOSINGLEBYTE_OFST))
/* The address of the ALT_SCANMGR_FIFODOUBLEBYTE register for the ALT_SCANMGR instance. */
#define ALT_SCANMGR_FIFODOUBLEBYTE_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SCANMGR_ADDR) + ALT_SCANMGR_FIFODOUBLEBYTE_OFST))
/* The address of the ALT_SCANMGR_FIFOTRIPLEBYTE register for the ALT_SCANMGR instance. */
#define ALT_SCANMGR_FIFOTRIPLEBYTE_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SCANMGR_ADDR) + ALT_SCANMGR_FIFOTRIPLEBYTE_OFST))
/* The address of the ALT_SCANMGR_FIFOQUADBYTE register for the ALT_SCANMGR instance. */
#define ALT_SCANMGR_FIFOQUADBYTE_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_SCANMGR_ADDR) + ALT_SCANMGR_FIFOQUADBYTE_OFST))
/* The base address byte offset for the start of the ALT_SCANMGR component. */
#define ALT_SCANMGR_OFST        0xfff02000
/* The start address of the ALT_SCANMGR component. */
#define ALT_SCANMGR_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_HPS_ADDR) + ALT_SCANMGR_OFST))
/* The lower bound address range of the ALT_SCANMGR component. */
#define ALT_SCANMGR_LB_ADDR     ALT_SCANMGR_ADDR
/* The upper bound address range of the ALT_SCANMGR component. */
#define ALT_SCANMGR_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_SCANMGR_ADDR) + 0x20) - 1))


/*
 * Component Instance : rom
 * 
 * Instance rom of component ALT_ROM.
 * 
 * 
 */
/* The base address byte offset for the start of the ALT_ROM component. */
#define ALT_ROM_OFST        0xfffd0000
/* The start address of the ALT_ROM component. */
#define ALT_ROM_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_HPS_ADDR) + ALT_ROM_OFST))
/* The lower bound address range of the ALT_ROM component. */
#define ALT_ROM_LB_ADDR     ALT_ROM_ADDR
/* The upper bound address range of the ALT_ROM component. */
#define ALT_ROM_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_ROM_ADDR) + 0x10000) - 1))


/*
 * Component Instance : mpuscu
 * 
 * Instance mpuscu of component ALT_MPUSCU.
 * 
 * 
 */
/* The address of the ALT_MPUSCU_REG register for the ALT_MPUSCU instance. */
#define ALT_MPUSCU_REG_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_MPUSCU_ADDR) + ALT_MPUSCU_REG_OFST))
/* The base address byte offset for the start of the ALT_MPUSCU component. */
#define ALT_MPUSCU_OFST        0xfffec000
/* The start address of the ALT_MPUSCU component. */
#define ALT_MPUSCU_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_HPS_ADDR) + ALT_MPUSCU_OFST))
/* The lower bound address range of the ALT_MPUSCU component. */
#define ALT_MPUSCU_LB_ADDR     ALT_MPUSCU_ADDR
/* The upper bound address range of the ALT_MPUSCU component. */
#define ALT_MPUSCU_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_MPUSCU_ADDR) + 0x4) - 1))


/*
 * Component Instance : mpul2
 * 
 * Instance mpul2 of component ALT_MPUL2.
 * 
 * 
 */
/* The address of the ALT_MPUL2_REG register for the ALT_MPUL2 instance. */
#define ALT_MPUL2_REG_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_MPUL2_ADDR) + ALT_MPUL2_REG_OFST))
/* The base address byte offset for the start of the ALT_MPUL2 component. */
#define ALT_MPUL2_OFST        0xfffef000
/* The start address of the ALT_MPUL2 component. */
#define ALT_MPUL2_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_HPS_ADDR) + ALT_MPUL2_OFST))
/* The lower bound address range of the ALT_MPUL2 component. */
#define ALT_MPUL2_LB_ADDR     ALT_MPUL2_ADDR
/* The upper bound address range of the ALT_MPUL2 component. */
#define ALT_MPUL2_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_MPUL2_ADDR) + 0x4) - 1))


/*
 * Component Instance : ocram
 * 
 * Instance ocram of component ALT_OCRAM.
 * 
 * 
 */
/* The base address byte offset for the start of the ALT_OCRAM component. */
#define ALT_OCRAM_OFST        0xffff0000
/* The start address of the ALT_OCRAM component. */
#define ALT_OCRAM_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_HPS_ADDR) + ALT_OCRAM_OFST))
/* The lower bound address range of the ALT_OCRAM component. */
#define ALT_OCRAM_LB_ADDR     ALT_OCRAM_ADDR
/* The upper bound address range of the ALT_OCRAM component. */
#define ALT_OCRAM_UB_ADDR     ALT_CAST(void *, ((ALT_CAST(char *, ALT_OCRAM_ADDR) + 0x10000) - 1))


/*
 * Address Space : ALT_HPS
 * 
 * Address Map
 * 
 *  Address Range           | Component       
 * :------------------------|:-----------------
 *  0x00000000 - 0xfbffffff | Undefined       
 *  0xfc000000 - 0xfc000003 | ALT_STM         
 *  0xfc000004 - 0xfeffffff | Undefined       
 *  0xff000000 - 0xff000003 | ALT_DAP         
 *  0xff000004 - 0xff1fffff | Undefined       
 *  0xff200000 - 0xff3fffff | ALT_LWFPGASLVS  
 *  0xff400000 - 0xff47ffff | ALT_LWH2F       
 *  0xff480000 - 0xff4fffff | Undefined       
 *  0xff500000 - 0xff507fff | ALT_H2F         
 *  0xff508000 - 0xff5fffff | Undefined       
 *  0xff600000 - 0xff67ffff | ALT_F2H         
 *  0xff680000 - 0xff6fffff | Undefined       
 *  0xff700000 - 0xff701fff | ALT_EMAC0       
 *  0xff702000 - 0xff703fff | ALT_EMAC1       
 *  0xff704000 - 0xff7043ff | ALT_SDMMC       
 *  0xff704400 - 0xff704fff | Undefined       
 *  0xff705000 - 0xff7050ff | ALT_QSPI        
 *  0xff705100 - 0xff705fff | Undefined       
 *  0xff706000 - 0xff706fff | ALT_FPGAMGR     
 *  0xff707000 - 0xff707fff | ALT_ACPIDMAP    
 *  0xff708000 - 0xff70807f | ALT_GPIO0       
 *  0xff708080 - 0xff708fff | Undefined       
 *  0xff709000 - 0xff70907f | ALT_GPIO1       
 *  0xff709080 - 0xff709fff | Undefined       
 *  0xff70a000 - 0xff70a07f | ALT_GPIO2       
 *  0xff70a080 - 0xff7fffff | Undefined       
 *  0xff800000 - 0xff87ffff | ALT_L3          
 *  0xff880000 - 0xff8fffff | Undefined       
 *  0xff900000 - 0xff9fffff | ALT_NANDDATA    
 *  0xffa00000 - 0xffafffff | ALT_QSPIDATA    
 *  0xffb00000 - 0xffb3ffff | ALT_USB0        
 *  0xffb40000 - 0xffb7ffff | ALT_USB1        
 *  0xffb80000 - 0xffb807ff | ALT_NAND        
 *  0xffb80800 - 0xffb8ffff | Undefined       
 *  0xffb90000 - 0xffb90003 | ALT_FPGAMGRDATA 
 *  0xffb90004 - 0xffbfffff | Undefined       
 *  0xffc00000 - 0xffc001ff | ALT_CAN0        
 *  0xffc00200 - 0xffc00fff | Undefined       
 *  0xffc01000 - 0xffc011ff | ALT_CAN1        
 *  0xffc01200 - 0xffc01fff | Undefined       
 *  0xffc02000 - 0xffc020ff | ALT_UART0       
 *  0xffc02100 - 0xffc02fff | Undefined       
 *  0xffc03000 - 0xffc030ff | ALT_UART1       
 *  0xffc03100 - 0xffc03fff | Undefined       
 *  0xffc04000 - 0xffc040ff | ALT_I2C0        
 *  0xffc04100 - 0xffc04fff | Undefined       
 *  0xffc05000 - 0xffc050ff | ALT_I2C1        
 *  0xffc05100 - 0xffc05fff | Undefined       
 *  0xffc06000 - 0xffc060ff | ALT_I2C2        
 *  0xffc06100 - 0xffc06fff | Undefined       
 *  0xffc07000 - 0xffc070ff | ALT_I2C3        
 *  0xffc07100 - 0xffc07fff | Undefined       
 *  0xffc08000 - 0xffc080ff | ALT_SPTMR0      
 *  0xffc08100 - 0xffc08fff | Undefined       
 *  0xffc09000 - 0xffc090ff | ALT_SPTMR1      
 *  0xffc09100 - 0xffc1ffff | Undefined       
 *  0xffc20000 - 0xffc3ffff | ALT_SDR         
 *  0xffc40000 - 0xffcfffff | Undefined       
 *  0xffd00000 - 0xffd000ff | ALT_OSC1TMR0    
 *  0xffd00100 - 0xffd00fff | Undefined       
 *  0xffd01000 - 0xffd010ff | ALT_OSC1TMR1    
 *  0xffd01100 - 0xffd01fff | Undefined       
 *  0xffd02000 - 0xffd020ff | ALT_L4WD0       
 *  0xffd02100 - 0xffd02fff | Undefined       
 *  0xffd03000 - 0xffd030ff | ALT_L4WD1       
 *  0xffd03100 - 0xffd03fff | Undefined       
 *  0xffd04000 - 0xffd041ff | ALT_CLKMGR      
 *  0xffd04200 - 0xffd04fff | Undefined       
 *  0xffd05000 - 0xffd050ff | ALT_RSTMGR      
 *  0xffd05100 - 0xffd07fff | Undefined       
 *  0xffd08000 - 0xffd0bfff | ALT_SYSMGR      
 *  0xffd0c000 - 0xffdfffff | Undefined       
 *  0xffe00000 - 0xffe00003 | ALT_DMANONSECURE
 *  0xffe00004 - 0xffe00fff | Undefined       
 *  0xffe01000 - 0xffe01003 | ALT_DMASECURE   
 *  0xffe01004 - 0xffe01fff | Undefined       
 *  0xffe02000 - 0xffe0207f | ALT_SPIS0       
 *  0xffe02080 - 0xffe02fff | Undefined       
 *  0xffe03000 - 0xffe0307f | ALT_SPIS1       
 *  0xffe03080 - 0xffefffff | Undefined       
 *  0xfff00000 - 0xfff000ff | ALT_SPIM0       
 *  0xfff00100 - 0xfff00fff | Undefined       
 *  0xfff01000 - 0xfff010ff | ALT_SPIM1       
 *  0xfff01100 - 0xfff01fff | Undefined       
 *  0xfff02000 - 0xfff0201f | ALT_SCANMGR     
 *  0xfff02020 - 0xfffcffff | Undefined       
 *  0xfffd0000 - 0xfffdffff | ALT_ROM         
 *  0xfffe0000 - 0xfffebfff | Undefined       
 *  0xfffec000 - 0xfffec003 | ALT_MPUSCU      
 *  0xfffec004 - 0xfffeefff | Undefined       
 *  0xfffef000 - 0xfffef003 | ALT_MPUL2       
 *  0xfffef004 - 0xfffeffff | Undefined       
 *  0xffff0000 - 0xffffffff | ALT_OCRAM       
 */

#ifdef __ASSEMBLY__
#define ALT_CAST(type, ptr)  ptr
#else   /* __ASSEMBLY__ */
#define ALT_CAST(type, ptr)  ((type) (ptr))
#endif  /* __ASSEMBLY__ */
#ifdef __cplusplus
}
#endif  /* __cplusplus */
#endif  /* __ALTERA_HPS_H__ */

