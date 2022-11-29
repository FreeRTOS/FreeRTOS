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

#ifndef _SAMA5_DMAC1_INSTANCE_
#define _SAMA5_DMAC1_INSTANCE_

/* ========== Register definition for DMAC1 peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
#define REG_DMAC1_GCFG            (0xFFFFE800U) /**< \brief (DMAC1) DMAC Global Configuration Register */
#define REG_DMAC1_EN              (0xFFFFE804U) /**< \brief (DMAC1) DMAC Enable Register */
#define REG_DMAC1_SREQ            (0xFFFFE808U) /**< \brief (DMAC1) DMAC Software Single Request Register */
#define REG_DMAC1_CREQ            (0xFFFFE80CU) /**< \brief (DMAC1) DMAC Software Chunk Transfer Request Register */
#define REG_DMAC1_LAST            (0xFFFFE810U) /**< \brief (DMAC1) DMAC Software Last Transfer Flag Register */
#define REG_DMAC1_EBCIER          (0xFFFFE818U) /**< \brief (DMAC1) DMAC Error, Chained Buffer Transfer Completed Interrupt and Buffer Transfer Completed Interrupt Enable register. */
#define REG_DMAC1_EBCIDR          (0xFFFFE81CU) /**< \brief (DMAC1) DMAC Error, Chained Buffer Transfer Completed Interrupt and Buffer Transfer Completed Interrupt Disable register. */
#define REG_DMAC1_EBCIMR          (0xFFFFE820U) /**< \brief (DMAC1) DMAC Error, Chained Buffer Transfer Completed Interrupt and Buffer transfer completed Mask Register. */
#define REG_DMAC1_EBCISR          (0xFFFFE824U) /**< \brief (DMAC1) DMAC Error, Chained Buffer Transfer Completed Interrupt and Buffer transfer completed Status Register. */
#define REG_DMAC1_CHER            (0xFFFFE828U) /**< \brief (DMAC1) DMAC Channel Handler Enable Register */
#define REG_DMAC1_CHDR            (0xFFFFE82CU) /**< \brief (DMAC1) DMAC Channel Handler Disable Register */
#define REG_DMAC1_CHSR            (0xFFFFE830U) /**< \brief (DMAC1) DMAC Channel Handler Status Register */
#define REG_DMAC1_SADDR0          (0xFFFFE83CU) /**< \brief (DMAC1) DMAC Channel Source Address Register (ch_num = 0) */
#define REG_DMAC1_DADDR0          (0xFFFFE840U) /**< \brief (DMAC1) DMAC Channel Destination Address Register (ch_num = 0) */
#define REG_DMAC1_DSCR0           (0xFFFFE844U) /**< \brief (DMAC1) DMAC Channel Descriptor Address Register (ch_num = 0) */
#define REG_DMAC1_CTRLA0          (0xFFFFE848U) /**< \brief (DMAC1) DMAC Channel Control A Register (ch_num = 0) */
#define REG_DMAC1_CTRLB0          (0xFFFFE84CU) /**< \brief (DMAC1) DMAC Channel Control B Register (ch_num = 0) */
#define REG_DMAC1_CFG0            (0xFFFFE850U) /**< \brief (DMAC1) DMAC Channel Configuration Register (ch_num = 0) */
#define REG_DMAC1_SPIP0           (0xFFFFE854U) /**< \brief (DMAC1) DMAC Channel Source Picture-in-Picture Configuration Register (ch_num = 0) */
#define REG_DMAC1_DPIP0           (0xFFFFE858U) /**< \brief (DMAC1) DMAC Channel Destination Picture-in-Picture Configuration Register (ch_num = 0) */
#define REG_DMAC1_SADDR1          (0xFFFFE864U) /**< \brief (DMAC1) DMAC Channel Source Address Register (ch_num = 1) */
#define REG_DMAC1_DADDR1          (0xFFFFE868U) /**< \brief (DMAC1) DMAC Channel Destination Address Register (ch_num = 1) */
#define REG_DMAC1_DSCR1           (0xFFFFE86CU) /**< \brief (DMAC1) DMAC Channel Descriptor Address Register (ch_num = 1) */
#define REG_DMAC1_CTRLA1          (0xFFFFE870U) /**< \brief (DMAC1) DMAC Channel Control A Register (ch_num = 1) */
#define REG_DMAC1_CTRLB1          (0xFFFFE874U) /**< \brief (DMAC1) DMAC Channel Control B Register (ch_num = 1) */
#define REG_DMAC1_CFG1            (0xFFFFE878U) /**< \brief (DMAC1) DMAC Channel Configuration Register (ch_num = 1) */
#define REG_DMAC1_SPIP1           (0xFFFFE87CU) /**< \brief (DMAC1) DMAC Channel Source Picture-in-Picture Configuration Register (ch_num = 1) */
#define REG_DMAC1_DPIP1           (0xFFFFE880U) /**< \brief (DMAC1) DMAC Channel Destination Picture-in-Picture Configuration Register (ch_num = 1) */
#define REG_DMAC1_SADDR2          (0xFFFFE88CU) /**< \brief (DMAC1) DMAC Channel Source Address Register (ch_num = 2) */
#define REG_DMAC1_DADDR2          (0xFFFFE890U) /**< \brief (DMAC1) DMAC Channel Destination Address Register (ch_num = 2) */
#define REG_DMAC1_DSCR2           (0xFFFFE894U) /**< \brief (DMAC1) DMAC Channel Descriptor Address Register (ch_num = 2) */
#define REG_DMAC1_CTRLA2          (0xFFFFE898U) /**< \brief (DMAC1) DMAC Channel Control A Register (ch_num = 2) */
#define REG_DMAC1_CTRLB2          (0xFFFFE89CU) /**< \brief (DMAC1) DMAC Channel Control B Register (ch_num = 2) */
#define REG_DMAC1_CFG2            (0xFFFFE8A0U) /**< \brief (DMAC1) DMAC Channel Configuration Register (ch_num = 2) */
#define REG_DMAC1_SPIP2           (0xFFFFE8A4U) /**< \brief (DMAC1) DMAC Channel Source Picture-in-Picture Configuration Register (ch_num = 2) */
#define REG_DMAC1_DPIP2           (0xFFFFE8A8U) /**< \brief (DMAC1) DMAC Channel Destination Picture-in-Picture Configuration Register (ch_num = 2) */
#define REG_DMAC1_SADDR3          (0xFFFFE8B4U) /**< \brief (DMAC1) DMAC Channel Source Address Register (ch_num = 3) */
#define REG_DMAC1_DADDR3          (0xFFFFE8B8U) /**< \brief (DMAC1) DMAC Channel Destination Address Register (ch_num = 3) */
#define REG_DMAC1_DSCR3           (0xFFFFE8BCU) /**< \brief (DMAC1) DMAC Channel Descriptor Address Register (ch_num = 3) */
#define REG_DMAC1_CTRLA3          (0xFFFFE8C0U) /**< \brief (DMAC1) DMAC Channel Control A Register (ch_num = 3) */
#define REG_DMAC1_CTRLB3          (0xFFFFE8C4U) /**< \brief (DMAC1) DMAC Channel Control B Register (ch_num = 3) */
#define REG_DMAC1_CFG3            (0xFFFFE8C8U) /**< \brief (DMAC1) DMAC Channel Configuration Register (ch_num = 3) */
#define REG_DMAC1_SPIP3           (0xFFFFE8CCU) /**< \brief (DMAC1) DMAC Channel Source Picture-in-Picture Configuration Register (ch_num = 3) */
#define REG_DMAC1_DPIP3           (0xFFFFE8D0U) /**< \brief (DMAC1) DMAC Channel Destination Picture-in-Picture Configuration Register (ch_num = 3) */
#define REG_DMAC1_SADDR4          (0xFFFFE8DCU) /**< \brief (DMAC1) DMAC Channel Source Address Register (ch_num = 4) */
#define REG_DMAC1_DADDR4          (0xFFFFE8E0U) /**< \brief (DMAC1) DMAC Channel Destination Address Register (ch_num = 4) */
#define REG_DMAC1_DSCR4           (0xFFFFE8E4U) /**< \brief (DMAC1) DMAC Channel Descriptor Address Register (ch_num = 4) */
#define REG_DMAC1_CTRLA4          (0xFFFFE8E8U) /**< \brief (DMAC1) DMAC Channel Control A Register (ch_num = 4) */
#define REG_DMAC1_CTRLB4          (0xFFFFE8ECU) /**< \brief (DMAC1) DMAC Channel Control B Register (ch_num = 4) */
#define REG_DMAC1_CFG4            (0xFFFFE8F0U) /**< \brief (DMAC1) DMAC Channel Configuration Register (ch_num = 4) */
#define REG_DMAC1_SPIP4           (0xFFFFE8F4U) /**< \brief (DMAC1) DMAC Channel Source Picture-in-Picture Configuration Register (ch_num = 4) */
#define REG_DMAC1_DPIP4           (0xFFFFE8F8U) /**< \brief (DMAC1) DMAC Channel Destination Picture-in-Picture Configuration Register (ch_num = 4) */
#define REG_DMAC1_SADDR5          (0xFFFFE904U) /**< \brief (DMAC1) DMAC Channel Source Address Register (ch_num = 5) */
#define REG_DMAC1_DADDR5          (0xFFFFE908U) /**< \brief (DMAC1) DMAC Channel Destination Address Register (ch_num = 5) */
#define REG_DMAC1_DSCR5           (0xFFFFE90CU) /**< \brief (DMAC1) DMAC Channel Descriptor Address Register (ch_num = 5) */
#define REG_DMAC1_CTRLA5          (0xFFFFE910U) /**< \brief (DMAC1) DMAC Channel Control A Register (ch_num = 5) */
#define REG_DMAC1_CTRLB5          (0xFFFFE914U) /**< \brief (DMAC1) DMAC Channel Control B Register (ch_num = 5) */
#define REG_DMAC1_CFG5            (0xFFFFE918U) /**< \brief (DMAC1) DMAC Channel Configuration Register (ch_num = 5) */
#define REG_DMAC1_SPIP5           (0xFFFFE91CU) /**< \brief (DMAC1) DMAC Channel Source Picture-in-Picture Configuration Register (ch_num = 5) */
#define REG_DMAC1_DPIP5           (0xFFFFE920U) /**< \brief (DMAC1) DMAC Channel Destination Picture-in-Picture Configuration Register (ch_num = 5) */
#define REG_DMAC1_SADDR6          (0xFFFFE92CU) /**< \brief (DMAC1) DMAC Channel Source Address Register (ch_num = 6) */
#define REG_DMAC1_DADDR6          (0xFFFFE930U) /**< \brief (DMAC1) DMAC Channel Destination Address Register (ch_num = 6) */
#define REG_DMAC1_DSCR6           (0xFFFFE934U) /**< \brief (DMAC1) DMAC Channel Descriptor Address Register (ch_num = 6) */
#define REG_DMAC1_CTRLA6          (0xFFFFE938U) /**< \brief (DMAC1) DMAC Channel Control A Register (ch_num = 6) */
#define REG_DMAC1_CTRLB6          (0xFFFFE93CU) /**< \brief (DMAC1) DMAC Channel Control B Register (ch_num = 6) */
#define REG_DMAC1_CFG6            (0xFFFFE940U) /**< \brief (DMAC1) DMAC Channel Configuration Register (ch_num = 6) */
#define REG_DMAC1_SPIP6           (0xFFFFE944U) /**< \brief (DMAC1) DMAC Channel Source Picture-in-Picture Configuration Register (ch_num = 6) */
#define REG_DMAC1_DPIP6           (0xFFFFE948U) /**< \brief (DMAC1) DMAC Channel Destination Picture-in-Picture Configuration Register (ch_num = 6) */
#define REG_DMAC1_SADDR7          (0xFFFFE954U) /**< \brief (DMAC1) DMAC Channel Source Address Register (ch_num = 7) */
#define REG_DMAC1_DADDR7          (0xFFFFE958U) /**< \brief (DMAC1) DMAC Channel Destination Address Register (ch_num = 7) */
#define REG_DMAC1_DSCR7           (0xFFFFE95CU) /**< \brief (DMAC1) DMAC Channel Descriptor Address Register (ch_num = 7) */
#define REG_DMAC1_CTRLA7          (0xFFFFE960U) /**< \brief (DMAC1) DMAC Channel Control A Register (ch_num = 7) */
#define REG_DMAC1_CTRLB7          (0xFFFFE964U) /**< \brief (DMAC1) DMAC Channel Control B Register (ch_num = 7) */
#define REG_DMAC1_CFG7            (0xFFFFE968U) /**< \brief (DMAC1) DMAC Channel Configuration Register (ch_num = 7) */
#define REG_DMAC1_SPIP7           (0xFFFFE96CU) /**< \brief (DMAC1) DMAC Channel Source Picture-in-Picture Configuration Register (ch_num = 7) */
#define REG_DMAC1_DPIP7           (0xFFFFE970U) /**< \brief (DMAC1) DMAC Channel Destination Picture-in-Picture Configuration Register (ch_num = 7) */
#define REG_DMAC1_WPMR            (0xFFFFE9E4U) /**< \brief (DMAC1) DMAC Write Protect Mode Register */
#define REG_DMAC1_WPSR            (0xFFFFE9E8U) /**< \brief (DMAC1) DMAC Write Protect Status Register */
#else
#define REG_DMAC1_GCFG   (*(RwReg*)0xFFFFE800U) /**< \brief (DMAC1) DMAC Global Configuration Register */
#define REG_DMAC1_EN     (*(RwReg*)0xFFFFE804U) /**< \brief (DMAC1) DMAC Enable Register */
#define REG_DMAC1_SREQ   (*(RwReg*)0xFFFFE808U) /**< \brief (DMAC1) DMAC Software Single Request Register */
#define REG_DMAC1_CREQ   (*(RwReg*)0xFFFFE80CU) /**< \brief (DMAC1) DMAC Software Chunk Transfer Request Register */
#define REG_DMAC1_LAST   (*(RwReg*)0xFFFFE810U) /**< \brief (DMAC1) DMAC Software Last Transfer Flag Register */
#define REG_DMAC1_EBCIER (*(WoReg*)0xFFFFE818U) /**< \brief (DMAC1) DMAC Error, Chained Buffer Transfer Completed Interrupt and Buffer Transfer Completed Interrupt Enable register. */
#define REG_DMAC1_EBCIDR (*(WoReg*)0xFFFFE81CU) /**< \brief (DMAC1) DMAC Error, Chained Buffer Transfer Completed Interrupt and Buffer Transfer Completed Interrupt Disable register. */
#define REG_DMAC1_EBCIMR (*(RoReg*)0xFFFFE820U) /**< \brief (DMAC1) DMAC Error, Chained Buffer Transfer Completed Interrupt and Buffer transfer completed Mask Register. */
#define REG_DMAC1_EBCISR (*(RoReg*)0xFFFFE824U) /**< \brief (DMAC1) DMAC Error, Chained Buffer Transfer Completed Interrupt and Buffer transfer completed Status Register. */
#define REG_DMAC1_CHER   (*(WoReg*)0xFFFFE828U) /**< \brief (DMAC1) DMAC Channel Handler Enable Register */
#define REG_DMAC1_CHDR   (*(WoReg*)0xFFFFE82CU) /**< \brief (DMAC1) DMAC Channel Handler Disable Register */
#define REG_DMAC1_CHSR   (*(RoReg*)0xFFFFE830U) /**< \brief (DMAC1) DMAC Channel Handler Status Register */
#define REG_DMAC1_SADDR0 (*(RwReg*)0xFFFFE83CU) /**< \brief (DMAC1) DMAC Channel Source Address Register (ch_num = 0) */
#define REG_DMAC1_DADDR0 (*(RwReg*)0xFFFFE840U) /**< \brief (DMAC1) DMAC Channel Destination Address Register (ch_num = 0) */
#define REG_DMAC1_DSCR0  (*(RwReg*)0xFFFFE844U) /**< \brief (DMAC1) DMAC Channel Descriptor Address Register (ch_num = 0) */
#define REG_DMAC1_CTRLA0 (*(RwReg*)0xFFFFE848U) /**< \brief (DMAC1) DMAC Channel Control A Register (ch_num = 0) */
#define REG_DMAC1_CTRLB0 (*(RwReg*)0xFFFFE84CU) /**< \brief (DMAC1) DMAC Channel Control B Register (ch_num = 0) */
#define REG_DMAC1_CFG0   (*(RwReg*)0xFFFFE850U) /**< \brief (DMAC1) DMAC Channel Configuration Register (ch_num = 0) */
#define REG_DMAC1_SPIP0  (*(RwReg*)0xFFFFE854U) /**< \brief (DMAC1) DMAC Channel Source Picture-in-Picture Configuration Register (ch_num = 0) */
#define REG_DMAC1_DPIP0  (*(RwReg*)0xFFFFE858U) /**< \brief (DMAC1) DMAC Channel Destination Picture-in-Picture Configuration Register (ch_num = 0) */
#define REG_DMAC1_SADDR1 (*(RwReg*)0xFFFFE864U) /**< \brief (DMAC1) DMAC Channel Source Address Register (ch_num = 1) */
#define REG_DMAC1_DADDR1 (*(RwReg*)0xFFFFE868U) /**< \brief (DMAC1) DMAC Channel Destination Address Register (ch_num = 1) */
#define REG_DMAC1_DSCR1  (*(RwReg*)0xFFFFE86CU) /**< \brief (DMAC1) DMAC Channel Descriptor Address Register (ch_num = 1) */
#define REG_DMAC1_CTRLA1 (*(RwReg*)0xFFFFE870U) /**< \brief (DMAC1) DMAC Channel Control A Register (ch_num = 1) */
#define REG_DMAC1_CTRLB1 (*(RwReg*)0xFFFFE874U) /**< \brief (DMAC1) DMAC Channel Control B Register (ch_num = 1) */
#define REG_DMAC1_CFG1   (*(RwReg*)0xFFFFE878U) /**< \brief (DMAC1) DMAC Channel Configuration Register (ch_num = 1) */
#define REG_DMAC1_SPIP1  (*(RwReg*)0xFFFFE87CU) /**< \brief (DMAC1) DMAC Channel Source Picture-in-Picture Configuration Register (ch_num = 1) */
#define REG_DMAC1_DPIP1  (*(RwReg*)0xFFFFE880U) /**< \brief (DMAC1) DMAC Channel Destination Picture-in-Picture Configuration Register (ch_num = 1) */
#define REG_DMAC1_SADDR2 (*(RwReg*)0xFFFFE88CU) /**< \brief (DMAC1) DMAC Channel Source Address Register (ch_num = 2) */
#define REG_DMAC1_DADDR2 (*(RwReg*)0xFFFFE890U) /**< \brief (DMAC1) DMAC Channel Destination Address Register (ch_num = 2) */
#define REG_DMAC1_DSCR2  (*(RwReg*)0xFFFFE894U) /**< \brief (DMAC1) DMAC Channel Descriptor Address Register (ch_num = 2) */
#define REG_DMAC1_CTRLA2 (*(RwReg*)0xFFFFE898U) /**< \brief (DMAC1) DMAC Channel Control A Register (ch_num = 2) */
#define REG_DMAC1_CTRLB2 (*(RwReg*)0xFFFFE89CU) /**< \brief (DMAC1) DMAC Channel Control B Register (ch_num = 2) */
#define REG_DMAC1_CFG2   (*(RwReg*)0xFFFFE8A0U) /**< \brief (DMAC1) DMAC Channel Configuration Register (ch_num = 2) */
#define REG_DMAC1_SPIP2  (*(RwReg*)0xFFFFE8A4U) /**< \brief (DMAC1) DMAC Channel Source Picture-in-Picture Configuration Register (ch_num = 2) */
#define REG_DMAC1_DPIP2  (*(RwReg*)0xFFFFE8A8U) /**< \brief (DMAC1) DMAC Channel Destination Picture-in-Picture Configuration Register (ch_num = 2) */
#define REG_DMAC1_SADDR3 (*(RwReg*)0xFFFFE8B4U) /**< \brief (DMAC1) DMAC Channel Source Address Register (ch_num = 3) */
#define REG_DMAC1_DADDR3 (*(RwReg*)0xFFFFE8B8U) /**< \brief (DMAC1) DMAC Channel Destination Address Register (ch_num = 3) */
#define REG_DMAC1_DSCR3  (*(RwReg*)0xFFFFE8BCU) /**< \brief (DMAC1) DMAC Channel Descriptor Address Register (ch_num = 3) */
#define REG_DMAC1_CTRLA3 (*(RwReg*)0xFFFFE8C0U) /**< \brief (DMAC1) DMAC Channel Control A Register (ch_num = 3) */
#define REG_DMAC1_CTRLB3 (*(RwReg*)0xFFFFE8C4U) /**< \brief (DMAC1) DMAC Channel Control B Register (ch_num = 3) */
#define REG_DMAC1_CFG3   (*(RwReg*)0xFFFFE8C8U) /**< \brief (DMAC1) DMAC Channel Configuration Register (ch_num = 3) */
#define REG_DMAC1_SPIP3  (*(RwReg*)0xFFFFE8CCU) /**< \brief (DMAC1) DMAC Channel Source Picture-in-Picture Configuration Register (ch_num = 3) */
#define REG_DMAC1_DPIP3  (*(RwReg*)0xFFFFE8D0U) /**< \brief (DMAC1) DMAC Channel Destination Picture-in-Picture Configuration Register (ch_num = 3) */
#define REG_DMAC1_SADDR4 (*(RwReg*)0xFFFFE8DCU) /**< \brief (DMAC1) DMAC Channel Source Address Register (ch_num = 4) */
#define REG_DMAC1_DADDR4 (*(RwReg*)0xFFFFE8E0U) /**< \brief (DMAC1) DMAC Channel Destination Address Register (ch_num = 4) */
#define REG_DMAC1_DSCR4  (*(RwReg*)0xFFFFE8E4U) /**< \brief (DMAC1) DMAC Channel Descriptor Address Register (ch_num = 4) */
#define REG_DMAC1_CTRLA4 (*(RwReg*)0xFFFFE8E8U) /**< \brief (DMAC1) DMAC Channel Control A Register (ch_num = 4) */
#define REG_DMAC1_CTRLB4 (*(RwReg*)0xFFFFE8ECU) /**< \brief (DMAC1) DMAC Channel Control B Register (ch_num = 4) */
#define REG_DMAC1_CFG4   (*(RwReg*)0xFFFFE8F0U) /**< \brief (DMAC1) DMAC Channel Configuration Register (ch_num = 4) */
#define REG_DMAC1_SPIP4  (*(RwReg*)0xFFFFE8F4U) /**< \brief (DMAC1) DMAC Channel Source Picture-in-Picture Configuration Register (ch_num = 4) */
#define REG_DMAC1_DPIP4  (*(RwReg*)0xFFFFE8F8U) /**< \brief (DMAC1) DMAC Channel Destination Picture-in-Picture Configuration Register (ch_num = 4) */
#define REG_DMAC1_SADDR5 (*(RwReg*)0xFFFFE904U) /**< \brief (DMAC1) DMAC Channel Source Address Register (ch_num = 5) */
#define REG_DMAC1_DADDR5 (*(RwReg*)0xFFFFE908U) /**< \brief (DMAC1) DMAC Channel Destination Address Register (ch_num = 5) */
#define REG_DMAC1_DSCR5  (*(RwReg*)0xFFFFE90CU) /**< \brief (DMAC1) DMAC Channel Descriptor Address Register (ch_num = 5) */
#define REG_DMAC1_CTRLA5 (*(RwReg*)0xFFFFE910U) /**< \brief (DMAC1) DMAC Channel Control A Register (ch_num = 5) */
#define REG_DMAC1_CTRLB5 (*(RwReg*)0xFFFFE914U) /**< \brief (DMAC1) DMAC Channel Control B Register (ch_num = 5) */
#define REG_DMAC1_CFG5   (*(RwReg*)0xFFFFE918U) /**< \brief (DMAC1) DMAC Channel Configuration Register (ch_num = 5) */
#define REG_DMAC1_SPIP5  (*(RwReg*)0xFFFFE91CU) /**< \brief (DMAC1) DMAC Channel Source Picture-in-Picture Configuration Register (ch_num = 5) */
#define REG_DMAC1_DPIP5  (*(RwReg*)0xFFFFE920U) /**< \brief (DMAC1) DMAC Channel Destination Picture-in-Picture Configuration Register (ch_num = 5) */
#define REG_DMAC1_SADDR6 (*(RwReg*)0xFFFFE92CU) /**< \brief (DMAC1) DMAC Channel Source Address Register (ch_num = 6) */
#define REG_DMAC1_DADDR6 (*(RwReg*)0xFFFFE930U) /**< \brief (DMAC1) DMAC Channel Destination Address Register (ch_num = 6) */
#define REG_DMAC1_DSCR6  (*(RwReg*)0xFFFFE934U) /**< \brief (DMAC1) DMAC Channel Descriptor Address Register (ch_num = 6) */
#define REG_DMAC1_CTRLA6 (*(RwReg*)0xFFFFE938U) /**< \brief (DMAC1) DMAC Channel Control A Register (ch_num = 6) */
#define REG_DMAC1_CTRLB6 (*(RwReg*)0xFFFFE93CU) /**< \brief (DMAC1) DMAC Channel Control B Register (ch_num = 6) */
#define REG_DMAC1_CFG6   (*(RwReg*)0xFFFFE940U) /**< \brief (DMAC1) DMAC Channel Configuration Register (ch_num = 6) */
#define REG_DMAC1_SPIP6  (*(RwReg*)0xFFFFE944U) /**< \brief (DMAC1) DMAC Channel Source Picture-in-Picture Configuration Register (ch_num = 6) */
#define REG_DMAC1_DPIP6  (*(RwReg*)0xFFFFE948U) /**< \brief (DMAC1) DMAC Channel Destination Picture-in-Picture Configuration Register (ch_num = 6) */
#define REG_DMAC1_SADDR7 (*(RwReg*)0xFFFFE954U) /**< \brief (DMAC1) DMAC Channel Source Address Register (ch_num = 7) */
#define REG_DMAC1_DADDR7 (*(RwReg*)0xFFFFE958U) /**< \brief (DMAC1) DMAC Channel Destination Address Register (ch_num = 7) */
#define REG_DMAC1_DSCR7  (*(RwReg*)0xFFFFE95CU) /**< \brief (DMAC1) DMAC Channel Descriptor Address Register (ch_num = 7) */
#define REG_DMAC1_CTRLA7 (*(RwReg*)0xFFFFE960U) /**< \brief (DMAC1) DMAC Channel Control A Register (ch_num = 7) */
#define REG_DMAC1_CTRLB7 (*(RwReg*)0xFFFFE964U) /**< \brief (DMAC1) DMAC Channel Control B Register (ch_num = 7) */
#define REG_DMAC1_CFG7   (*(RwReg*)0xFFFFE968U) /**< \brief (DMAC1) DMAC Channel Configuration Register (ch_num = 7) */
#define REG_DMAC1_SPIP7  (*(RwReg*)0xFFFFE96CU) /**< \brief (DMAC1) DMAC Channel Source Picture-in-Picture Configuration Register (ch_num = 7) */
#define REG_DMAC1_DPIP7  (*(RwReg*)0xFFFFE970U) /**< \brief (DMAC1) DMAC Channel Destination Picture-in-Picture Configuration Register (ch_num = 7) */
#define REG_DMAC1_WPMR   (*(RwReg*)0xFFFFE9E4U) /**< \brief (DMAC1) DMAC Write Protect Mode Register */
#define REG_DMAC1_WPSR   (*(RoReg*)0xFFFFE9E8U) /**< \brief (DMAC1) DMAC Write Protect Status Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAMA5_DMAC1_INSTANCE_ */
