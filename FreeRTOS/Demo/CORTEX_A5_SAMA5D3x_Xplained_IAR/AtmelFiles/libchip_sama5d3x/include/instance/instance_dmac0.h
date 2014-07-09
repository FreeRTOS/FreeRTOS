/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2012, Atmel Corporation
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following condition is met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the disclaimer below.
 *
 * Atmel's name may not be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * DISCLAIMER: THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * ----------------------------------------------------------------------------
 */

#ifndef _SAMA5_DMAC0_INSTANCE_
#define _SAMA5_DMAC0_INSTANCE_

/* ========== Register definition for DMAC0 peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
#define REG_DMAC0_GCFG            (0xFFFFE600U) /**< \brief (DMAC0) DMAC Global Configuration Register */
#define REG_DMAC0_EN              (0xFFFFE604U) /**< \brief (DMAC0) DMAC Enable Register */
#define REG_DMAC0_SREQ            (0xFFFFE608U) /**< \brief (DMAC0) DMAC Software Single Request Register */
#define REG_DMAC0_CREQ            (0xFFFFE60CU) /**< \brief (DMAC0) DMAC Software Chunk Transfer Request Register */
#define REG_DMAC0_LAST            (0xFFFFE610U) /**< \brief (DMAC0) DMAC Software Last Transfer Flag Register */
#define REG_DMAC0_EBCIER          (0xFFFFE618U) /**< \brief (DMAC0) DMAC Error, Chained Buffer Transfer Completed Interrupt and Buffer Transfer Completed Interrupt Enable register. */
#define REG_DMAC0_EBCIDR          (0xFFFFE61CU) /**< \brief (DMAC0) DMAC Error, Chained Buffer Transfer Completed Interrupt and Buffer Transfer Completed Interrupt Disable register. */
#define REG_DMAC0_EBCIMR          (0xFFFFE620U) /**< \brief (DMAC0) DMAC Error, Chained Buffer Transfer Completed Interrupt and Buffer transfer completed Mask Register. */
#define REG_DMAC0_EBCISR          (0xFFFFE624U) /**< \brief (DMAC0) DMAC Error, Chained Buffer Transfer Completed Interrupt and Buffer transfer completed Status Register. */
#define REG_DMAC0_CHER            (0xFFFFE628U) /**< \brief (DMAC0) DMAC Channel Handler Enable Register */
#define REG_DMAC0_CHDR            (0xFFFFE62CU) /**< \brief (DMAC0) DMAC Channel Handler Disable Register */
#define REG_DMAC0_CHSR            (0xFFFFE630U) /**< \brief (DMAC0) DMAC Channel Handler Status Register */
#define REG_DMAC0_SADDR0          (0xFFFFE63CU) /**< \brief (DMAC0) DMAC Channel Source Address Register (ch_num = 0) */
#define REG_DMAC0_DADDR0          (0xFFFFE640U) /**< \brief (DMAC0) DMAC Channel Destination Address Register (ch_num = 0) */
#define REG_DMAC0_DSCR0           (0xFFFFE644U) /**< \brief (DMAC0) DMAC Channel Descriptor Address Register (ch_num = 0) */
#define REG_DMAC0_CTRLA0          (0xFFFFE648U) /**< \brief (DMAC0) DMAC Channel Control A Register (ch_num = 0) */
#define REG_DMAC0_CTRLB0          (0xFFFFE64CU) /**< \brief (DMAC0) DMAC Channel Control B Register (ch_num = 0) */
#define REG_DMAC0_CFG0            (0xFFFFE650U) /**< \brief (DMAC0) DMAC Channel Configuration Register (ch_num = 0) */
#define REG_DMAC0_SPIP0           (0xFFFFE654U) /**< \brief (DMAC0) DMAC Channel Source Picture-in-Picture Configuration Register (ch_num = 0) */
#define REG_DMAC0_DPIP0           (0xFFFFE658U) /**< \brief (DMAC0) DMAC Channel Destination Picture-in-Picture Configuration Register (ch_num = 0) */
#define REG_DMAC0_SADDR1          (0xFFFFE664U) /**< \brief (DMAC0) DMAC Channel Source Address Register (ch_num = 1) */
#define REG_DMAC0_DADDR1          (0xFFFFE668U) /**< \brief (DMAC0) DMAC Channel Destination Address Register (ch_num = 1) */
#define REG_DMAC0_DSCR1           (0xFFFFE66CU) /**< \brief (DMAC0) DMAC Channel Descriptor Address Register (ch_num = 1) */
#define REG_DMAC0_CTRLA1          (0xFFFFE670U) /**< \brief (DMAC0) DMAC Channel Control A Register (ch_num = 1) */
#define REG_DMAC0_CTRLB1          (0xFFFFE674U) /**< \brief (DMAC0) DMAC Channel Control B Register (ch_num = 1) */
#define REG_DMAC0_CFG1            (0xFFFFE678U) /**< \brief (DMAC0) DMAC Channel Configuration Register (ch_num = 1) */
#define REG_DMAC0_SPIP1           (0xFFFFE67CU) /**< \brief (DMAC0) DMAC Channel Source Picture-in-Picture Configuration Register (ch_num = 1) */
#define REG_DMAC0_DPIP1           (0xFFFFE680U) /**< \brief (DMAC0) DMAC Channel Destination Picture-in-Picture Configuration Register (ch_num = 1) */
#define REG_DMAC0_SADDR2          (0xFFFFE68CU) /**< \brief (DMAC0) DMAC Channel Source Address Register (ch_num = 2) */
#define REG_DMAC0_DADDR2          (0xFFFFE690U) /**< \brief (DMAC0) DMAC Channel Destination Address Register (ch_num = 2) */
#define REG_DMAC0_DSCR2           (0xFFFFE694U) /**< \brief (DMAC0) DMAC Channel Descriptor Address Register (ch_num = 2) */
#define REG_DMAC0_CTRLA2          (0xFFFFE698U) /**< \brief (DMAC0) DMAC Channel Control A Register (ch_num = 2) */
#define REG_DMAC0_CTRLB2          (0xFFFFE69CU) /**< \brief (DMAC0) DMAC Channel Control B Register (ch_num = 2) */
#define REG_DMAC0_CFG2            (0xFFFFE6A0U) /**< \brief (DMAC0) DMAC Channel Configuration Register (ch_num = 2) */
#define REG_DMAC0_SPIP2           (0xFFFFE6A4U) /**< \brief (DMAC0) DMAC Channel Source Picture-in-Picture Configuration Register (ch_num = 2) */
#define REG_DMAC0_DPIP2           (0xFFFFE6A8U) /**< \brief (DMAC0) DMAC Channel Destination Picture-in-Picture Configuration Register (ch_num = 2) */
#define REG_DMAC0_SADDR3          (0xFFFFE6B4U) /**< \brief (DMAC0) DMAC Channel Source Address Register (ch_num = 3) */
#define REG_DMAC0_DADDR3          (0xFFFFE6B8U) /**< \brief (DMAC0) DMAC Channel Destination Address Register (ch_num = 3) */
#define REG_DMAC0_DSCR3           (0xFFFFE6BCU) /**< \brief (DMAC0) DMAC Channel Descriptor Address Register (ch_num = 3) */
#define REG_DMAC0_CTRLA3          (0xFFFFE6C0U) /**< \brief (DMAC0) DMAC Channel Control A Register (ch_num = 3) */
#define REG_DMAC0_CTRLB3          (0xFFFFE6C4U) /**< \brief (DMAC0) DMAC Channel Control B Register (ch_num = 3) */
#define REG_DMAC0_CFG3            (0xFFFFE6C8U) /**< \brief (DMAC0) DMAC Channel Configuration Register (ch_num = 3) */
#define REG_DMAC0_SPIP3           (0xFFFFE6CCU) /**< \brief (DMAC0) DMAC Channel Source Picture-in-Picture Configuration Register (ch_num = 3) */
#define REG_DMAC0_DPIP3           (0xFFFFE6D0U) /**< \brief (DMAC0) DMAC Channel Destination Picture-in-Picture Configuration Register (ch_num = 3) */
#define REG_DMAC0_SADDR4          (0xFFFFE6DCU) /**< \brief (DMAC0) DMAC Channel Source Address Register (ch_num = 4) */
#define REG_DMAC0_DADDR4          (0xFFFFE6E0U) /**< \brief (DMAC0) DMAC Channel Destination Address Register (ch_num = 4) */
#define REG_DMAC0_DSCR4           (0xFFFFE6E4U) /**< \brief (DMAC0) DMAC Channel Descriptor Address Register (ch_num = 4) */
#define REG_DMAC0_CTRLA4          (0xFFFFE6E8U) /**< \brief (DMAC0) DMAC Channel Control A Register (ch_num = 4) */
#define REG_DMAC0_CTRLB4          (0xFFFFE6ECU) /**< \brief (DMAC0) DMAC Channel Control B Register (ch_num = 4) */
#define REG_DMAC0_CFG4            (0xFFFFE6F0U) /**< \brief (DMAC0) DMAC Channel Configuration Register (ch_num = 4) */
#define REG_DMAC0_SPIP4           (0xFFFFE6F4U) /**< \brief (DMAC0) DMAC Channel Source Picture-in-Picture Configuration Register (ch_num = 4) */
#define REG_DMAC0_DPIP4           (0xFFFFE6F8U) /**< \brief (DMAC0) DMAC Channel Destination Picture-in-Picture Configuration Register (ch_num = 4) */
#define REG_DMAC0_SADDR5          (0xFFFFE704U) /**< \brief (DMAC0) DMAC Channel Source Address Register (ch_num = 5) */
#define REG_DMAC0_DADDR5          (0xFFFFE708U) /**< \brief (DMAC0) DMAC Channel Destination Address Register (ch_num = 5) */
#define REG_DMAC0_DSCR5           (0xFFFFE70CU) /**< \brief (DMAC0) DMAC Channel Descriptor Address Register (ch_num = 5) */
#define REG_DMAC0_CTRLA5          (0xFFFFE710U) /**< \brief (DMAC0) DMAC Channel Control A Register (ch_num = 5) */
#define REG_DMAC0_CTRLB5          (0xFFFFE714U) /**< \brief (DMAC0) DMAC Channel Control B Register (ch_num = 5) */
#define REG_DMAC0_CFG5            (0xFFFFE718U) /**< \brief (DMAC0) DMAC Channel Configuration Register (ch_num = 5) */
#define REG_DMAC0_SPIP5           (0xFFFFE71CU) /**< \brief (DMAC0) DMAC Channel Source Picture-in-Picture Configuration Register (ch_num = 5) */
#define REG_DMAC0_DPIP5           (0xFFFFE720U) /**< \brief (DMAC0) DMAC Channel Destination Picture-in-Picture Configuration Register (ch_num = 5) */
#define REG_DMAC0_SADDR6          (0xFFFFE72CU) /**< \brief (DMAC0) DMAC Channel Source Address Register (ch_num = 6) */
#define REG_DMAC0_DADDR6          (0xFFFFE730U) /**< \brief (DMAC0) DMAC Channel Destination Address Register (ch_num = 6) */
#define REG_DMAC0_DSCR6           (0xFFFFE734U) /**< \brief (DMAC0) DMAC Channel Descriptor Address Register (ch_num = 6) */
#define REG_DMAC0_CTRLA6          (0xFFFFE738U) /**< \brief (DMAC0) DMAC Channel Control A Register (ch_num = 6) */
#define REG_DMAC0_CTRLB6          (0xFFFFE73CU) /**< \brief (DMAC0) DMAC Channel Control B Register (ch_num = 6) */
#define REG_DMAC0_CFG6            (0xFFFFE740U) /**< \brief (DMAC0) DMAC Channel Configuration Register (ch_num = 6) */
#define REG_DMAC0_SPIP6           (0xFFFFE744U) /**< \brief (DMAC0) DMAC Channel Source Picture-in-Picture Configuration Register (ch_num = 6) */
#define REG_DMAC0_DPIP6           (0xFFFFE748U) /**< \brief (DMAC0) DMAC Channel Destination Picture-in-Picture Configuration Register (ch_num = 6) */
#define REG_DMAC0_SADDR7          (0xFFFFE754U) /**< \brief (DMAC0) DMAC Channel Source Address Register (ch_num = 7) */
#define REG_DMAC0_DADDR7          (0xFFFFE758U) /**< \brief (DMAC0) DMAC Channel Destination Address Register (ch_num = 7) */
#define REG_DMAC0_DSCR7           (0xFFFFE75CU) /**< \brief (DMAC0) DMAC Channel Descriptor Address Register (ch_num = 7) */
#define REG_DMAC0_CTRLA7          (0xFFFFE760U) /**< \brief (DMAC0) DMAC Channel Control A Register (ch_num = 7) */
#define REG_DMAC0_CTRLB7          (0xFFFFE764U) /**< \brief (DMAC0) DMAC Channel Control B Register (ch_num = 7) */
#define REG_DMAC0_CFG7            (0xFFFFE768U) /**< \brief (DMAC0) DMAC Channel Configuration Register (ch_num = 7) */
#define REG_DMAC0_SPIP7           (0xFFFFE76CU) /**< \brief (DMAC0) DMAC Channel Source Picture-in-Picture Configuration Register (ch_num = 7) */
#define REG_DMAC0_DPIP7           (0xFFFFE770U) /**< \brief (DMAC0) DMAC Channel Destination Picture-in-Picture Configuration Register (ch_num = 7) */
#define REG_DMAC0_WPMR            (0xFFFFE7E4U) /**< \brief (DMAC0) DMAC Write Protect Mode Register */
#define REG_DMAC0_WPSR            (0xFFFFE7E8U) /**< \brief (DMAC0) DMAC Write Protect Status Register */
#else
#define REG_DMAC0_GCFG   (*(RwReg*)0xFFFFE600U) /**< \brief (DMAC0) DMAC Global Configuration Register */
#define REG_DMAC0_EN     (*(RwReg*)0xFFFFE604U) /**< \brief (DMAC0) DMAC Enable Register */
#define REG_DMAC0_SREQ   (*(RwReg*)0xFFFFE608U) /**< \brief (DMAC0) DMAC Software Single Request Register */
#define REG_DMAC0_CREQ   (*(RwReg*)0xFFFFE60CU) /**< \brief (DMAC0) DMAC Software Chunk Transfer Request Register */
#define REG_DMAC0_LAST   (*(RwReg*)0xFFFFE610U) /**< \brief (DMAC0) DMAC Software Last Transfer Flag Register */
#define REG_DMAC0_EBCIER (*(WoReg*)0xFFFFE618U) /**< \brief (DMAC0) DMAC Error, Chained Buffer Transfer Completed Interrupt and Buffer Transfer Completed Interrupt Enable register. */
#define REG_DMAC0_EBCIDR (*(WoReg*)0xFFFFE61CU) /**< \brief (DMAC0) DMAC Error, Chained Buffer Transfer Completed Interrupt and Buffer Transfer Completed Interrupt Disable register. */
#define REG_DMAC0_EBCIMR (*(RoReg*)0xFFFFE620U) /**< \brief (DMAC0) DMAC Error, Chained Buffer Transfer Completed Interrupt and Buffer transfer completed Mask Register. */
#define REG_DMAC0_EBCISR (*(RoReg*)0xFFFFE624U) /**< \brief (DMAC0) DMAC Error, Chained Buffer Transfer Completed Interrupt and Buffer transfer completed Status Register. */
#define REG_DMAC0_CHER   (*(WoReg*)0xFFFFE628U) /**< \brief (DMAC0) DMAC Channel Handler Enable Register */
#define REG_DMAC0_CHDR   (*(WoReg*)0xFFFFE62CU) /**< \brief (DMAC0) DMAC Channel Handler Disable Register */
#define REG_DMAC0_CHSR   (*(RoReg*)0xFFFFE630U) /**< \brief (DMAC0) DMAC Channel Handler Status Register */
#define REG_DMAC0_SADDR0 (*(RwReg*)0xFFFFE63CU) /**< \brief (DMAC0) DMAC Channel Source Address Register (ch_num = 0) */
#define REG_DMAC0_DADDR0 (*(RwReg*)0xFFFFE640U) /**< \brief (DMAC0) DMAC Channel Destination Address Register (ch_num = 0) */
#define REG_DMAC0_DSCR0  (*(RwReg*)0xFFFFE644U) /**< \brief (DMAC0) DMAC Channel Descriptor Address Register (ch_num = 0) */
#define REG_DMAC0_CTRLA0 (*(RwReg*)0xFFFFE648U) /**< \brief (DMAC0) DMAC Channel Control A Register (ch_num = 0) */
#define REG_DMAC0_CTRLB0 (*(RwReg*)0xFFFFE64CU) /**< \brief (DMAC0) DMAC Channel Control B Register (ch_num = 0) */
#define REG_DMAC0_CFG0   (*(RwReg*)0xFFFFE650U) /**< \brief (DMAC0) DMAC Channel Configuration Register (ch_num = 0) */
#define REG_DMAC0_SPIP0  (*(RwReg*)0xFFFFE654U) /**< \brief (DMAC0) DMAC Channel Source Picture-in-Picture Configuration Register (ch_num = 0) */
#define REG_DMAC0_DPIP0  (*(RwReg*)0xFFFFE658U) /**< \brief (DMAC0) DMAC Channel Destination Picture-in-Picture Configuration Register (ch_num = 0) */
#define REG_DMAC0_SADDR1 (*(RwReg*)0xFFFFE664U) /**< \brief (DMAC0) DMAC Channel Source Address Register (ch_num = 1) */
#define REG_DMAC0_DADDR1 (*(RwReg*)0xFFFFE668U) /**< \brief (DMAC0) DMAC Channel Destination Address Register (ch_num = 1) */
#define REG_DMAC0_DSCR1  (*(RwReg*)0xFFFFE66CU) /**< \brief (DMAC0) DMAC Channel Descriptor Address Register (ch_num = 1) */
#define REG_DMAC0_CTRLA1 (*(RwReg*)0xFFFFE670U) /**< \brief (DMAC0) DMAC Channel Control A Register (ch_num = 1) */
#define REG_DMAC0_CTRLB1 (*(RwReg*)0xFFFFE674U) /**< \brief (DMAC0) DMAC Channel Control B Register (ch_num = 1) */
#define REG_DMAC0_CFG1   (*(RwReg*)0xFFFFE678U) /**< \brief (DMAC0) DMAC Channel Configuration Register (ch_num = 1) */
#define REG_DMAC0_SPIP1  (*(RwReg*)0xFFFFE67CU) /**< \brief (DMAC0) DMAC Channel Source Picture-in-Picture Configuration Register (ch_num = 1) */
#define REG_DMAC0_DPIP1  (*(RwReg*)0xFFFFE680U) /**< \brief (DMAC0) DMAC Channel Destination Picture-in-Picture Configuration Register (ch_num = 1) */
#define REG_DMAC0_SADDR2 (*(RwReg*)0xFFFFE68CU) /**< \brief (DMAC0) DMAC Channel Source Address Register (ch_num = 2) */
#define REG_DMAC0_DADDR2 (*(RwReg*)0xFFFFE690U) /**< \brief (DMAC0) DMAC Channel Destination Address Register (ch_num = 2) */
#define REG_DMAC0_DSCR2  (*(RwReg*)0xFFFFE694U) /**< \brief (DMAC0) DMAC Channel Descriptor Address Register (ch_num = 2) */
#define REG_DMAC0_CTRLA2 (*(RwReg*)0xFFFFE698U) /**< \brief (DMAC0) DMAC Channel Control A Register (ch_num = 2) */
#define REG_DMAC0_CTRLB2 (*(RwReg*)0xFFFFE69CU) /**< \brief (DMAC0) DMAC Channel Control B Register (ch_num = 2) */
#define REG_DMAC0_CFG2   (*(RwReg*)0xFFFFE6A0U) /**< \brief (DMAC0) DMAC Channel Configuration Register (ch_num = 2) */
#define REG_DMAC0_SPIP2  (*(RwReg*)0xFFFFE6A4U) /**< \brief (DMAC0) DMAC Channel Source Picture-in-Picture Configuration Register (ch_num = 2) */
#define REG_DMAC0_DPIP2  (*(RwReg*)0xFFFFE6A8U) /**< \brief (DMAC0) DMAC Channel Destination Picture-in-Picture Configuration Register (ch_num = 2) */
#define REG_DMAC0_SADDR3 (*(RwReg*)0xFFFFE6B4U) /**< \brief (DMAC0) DMAC Channel Source Address Register (ch_num = 3) */
#define REG_DMAC0_DADDR3 (*(RwReg*)0xFFFFE6B8U) /**< \brief (DMAC0) DMAC Channel Destination Address Register (ch_num = 3) */
#define REG_DMAC0_DSCR3  (*(RwReg*)0xFFFFE6BCU) /**< \brief (DMAC0) DMAC Channel Descriptor Address Register (ch_num = 3) */
#define REG_DMAC0_CTRLA3 (*(RwReg*)0xFFFFE6C0U) /**< \brief (DMAC0) DMAC Channel Control A Register (ch_num = 3) */
#define REG_DMAC0_CTRLB3 (*(RwReg*)0xFFFFE6C4U) /**< \brief (DMAC0) DMAC Channel Control B Register (ch_num = 3) */
#define REG_DMAC0_CFG3   (*(RwReg*)0xFFFFE6C8U) /**< \brief (DMAC0) DMAC Channel Configuration Register (ch_num = 3) */
#define REG_DMAC0_SPIP3  (*(RwReg*)0xFFFFE6CCU) /**< \brief (DMAC0) DMAC Channel Source Picture-in-Picture Configuration Register (ch_num = 3) */
#define REG_DMAC0_DPIP3  (*(RwReg*)0xFFFFE6D0U) /**< \brief (DMAC0) DMAC Channel Destination Picture-in-Picture Configuration Register (ch_num = 3) */
#define REG_DMAC0_SADDR4 (*(RwReg*)0xFFFFE6DCU) /**< \brief (DMAC0) DMAC Channel Source Address Register (ch_num = 4) */
#define REG_DMAC0_DADDR4 (*(RwReg*)0xFFFFE6E0U) /**< \brief (DMAC0) DMAC Channel Destination Address Register (ch_num = 4) */
#define REG_DMAC0_DSCR4  (*(RwReg*)0xFFFFE6E4U) /**< \brief (DMAC0) DMAC Channel Descriptor Address Register (ch_num = 4) */
#define REG_DMAC0_CTRLA4 (*(RwReg*)0xFFFFE6E8U) /**< \brief (DMAC0) DMAC Channel Control A Register (ch_num = 4) */
#define REG_DMAC0_CTRLB4 (*(RwReg*)0xFFFFE6ECU) /**< \brief (DMAC0) DMAC Channel Control B Register (ch_num = 4) */
#define REG_DMAC0_CFG4   (*(RwReg*)0xFFFFE6F0U) /**< \brief (DMAC0) DMAC Channel Configuration Register (ch_num = 4) */
#define REG_DMAC0_SPIP4  (*(RwReg*)0xFFFFE6F4U) /**< \brief (DMAC0) DMAC Channel Source Picture-in-Picture Configuration Register (ch_num = 4) */
#define REG_DMAC0_DPIP4  (*(RwReg*)0xFFFFE6F8U) /**< \brief (DMAC0) DMAC Channel Destination Picture-in-Picture Configuration Register (ch_num = 4) */
#define REG_DMAC0_SADDR5 (*(RwReg*)0xFFFFE704U) /**< \brief (DMAC0) DMAC Channel Source Address Register (ch_num = 5) */
#define REG_DMAC0_DADDR5 (*(RwReg*)0xFFFFE708U) /**< \brief (DMAC0) DMAC Channel Destination Address Register (ch_num = 5) */
#define REG_DMAC0_DSCR5  (*(RwReg*)0xFFFFE70CU) /**< \brief (DMAC0) DMAC Channel Descriptor Address Register (ch_num = 5) */
#define REG_DMAC0_CTRLA5 (*(RwReg*)0xFFFFE710U) /**< \brief (DMAC0) DMAC Channel Control A Register (ch_num = 5) */
#define REG_DMAC0_CTRLB5 (*(RwReg*)0xFFFFE714U) /**< \brief (DMAC0) DMAC Channel Control B Register (ch_num = 5) */
#define REG_DMAC0_CFG5   (*(RwReg*)0xFFFFE718U) /**< \brief (DMAC0) DMAC Channel Configuration Register (ch_num = 5) */
#define REG_DMAC0_SPIP5  (*(RwReg*)0xFFFFE71CU) /**< \brief (DMAC0) DMAC Channel Source Picture-in-Picture Configuration Register (ch_num = 5) */
#define REG_DMAC0_DPIP5  (*(RwReg*)0xFFFFE720U) /**< \brief (DMAC0) DMAC Channel Destination Picture-in-Picture Configuration Register (ch_num = 5) */
#define REG_DMAC0_SADDR6 (*(RwReg*)0xFFFFE72CU) /**< \brief (DMAC0) DMAC Channel Source Address Register (ch_num = 6) */
#define REG_DMAC0_DADDR6 (*(RwReg*)0xFFFFE730U) /**< \brief (DMAC0) DMAC Channel Destination Address Register (ch_num = 6) */
#define REG_DMAC0_DSCR6  (*(RwReg*)0xFFFFE734U) /**< \brief (DMAC0) DMAC Channel Descriptor Address Register (ch_num = 6) */
#define REG_DMAC0_CTRLA6 (*(RwReg*)0xFFFFE738U) /**< \brief (DMAC0) DMAC Channel Control A Register (ch_num = 6) */
#define REG_DMAC0_CTRLB6 (*(RwReg*)0xFFFFE73CU) /**< \brief (DMAC0) DMAC Channel Control B Register (ch_num = 6) */
#define REG_DMAC0_CFG6   (*(RwReg*)0xFFFFE740U) /**< \brief (DMAC0) DMAC Channel Configuration Register (ch_num = 6) */
#define REG_DMAC0_SPIP6  (*(RwReg*)0xFFFFE744U) /**< \brief (DMAC0) DMAC Channel Source Picture-in-Picture Configuration Register (ch_num = 6) */
#define REG_DMAC0_DPIP6  (*(RwReg*)0xFFFFE748U) /**< \brief (DMAC0) DMAC Channel Destination Picture-in-Picture Configuration Register (ch_num = 6) */
#define REG_DMAC0_SADDR7 (*(RwReg*)0xFFFFE754U) /**< \brief (DMAC0) DMAC Channel Source Address Register (ch_num = 7) */
#define REG_DMAC0_DADDR7 (*(RwReg*)0xFFFFE758U) /**< \brief (DMAC0) DMAC Channel Destination Address Register (ch_num = 7) */
#define REG_DMAC0_DSCR7  (*(RwReg*)0xFFFFE75CU) /**< \brief (DMAC0) DMAC Channel Descriptor Address Register (ch_num = 7) */
#define REG_DMAC0_CTRLA7 (*(RwReg*)0xFFFFE760U) /**< \brief (DMAC0) DMAC Channel Control A Register (ch_num = 7) */
#define REG_DMAC0_CTRLB7 (*(RwReg*)0xFFFFE764U) /**< \brief (DMAC0) DMAC Channel Control B Register (ch_num = 7) */
#define REG_DMAC0_CFG7   (*(RwReg*)0xFFFFE768U) /**< \brief (DMAC0) DMAC Channel Configuration Register (ch_num = 7) */
#define REG_DMAC0_SPIP7  (*(RwReg*)0xFFFFE76CU) /**< \brief (DMAC0) DMAC Channel Source Picture-in-Picture Configuration Register (ch_num = 7) */
#define REG_DMAC0_DPIP7  (*(RwReg*)0xFFFFE770U) /**< \brief (DMAC0) DMAC Channel Destination Picture-in-Picture Configuration Register (ch_num = 7) */
#define REG_DMAC0_WPMR   (*(RwReg*)0xFFFFE7E4U) /**< \brief (DMAC0) DMAC Write Protect Mode Register */
#define REG_DMAC0_WPSR   (*(RoReg*)0xFFFFE7E8U) /**< \brief (DMAC0) DMAC Write Protect Status Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAMA5_DMAC0_INSTANCE_ */
