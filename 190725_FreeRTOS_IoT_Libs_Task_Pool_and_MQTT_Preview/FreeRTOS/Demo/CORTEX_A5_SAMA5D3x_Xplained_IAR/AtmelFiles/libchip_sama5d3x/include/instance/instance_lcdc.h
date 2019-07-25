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

#ifndef _SAMA5_LCDC_INSTANCE_
#define _SAMA5_LCDC_INSTANCE_

/* ========== Register definition for LCDC peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
#define REG_LCDC_LCDCFG0                (0xF0030000U) /**< \brief (LCDC) LCD Controller Configuration Register 0 */
#define REG_LCDC_LCDCFG1                (0xF0030004U) /**< \brief (LCDC) LCD Controller Configuration Register 1 */
#define REG_LCDC_LCDCFG2                (0xF0030008U) /**< \brief (LCDC) LCD Controller Configuration Register 2 */
#define REG_LCDC_LCDCFG3                (0xF003000CU) /**< \brief (LCDC) LCD Controller Configuration Register 3 */
#define REG_LCDC_LCDCFG4                (0xF0030010U) /**< \brief (LCDC) LCD Controller Configuration Register 4 */
#define REG_LCDC_LCDCFG5                (0xF0030014U) /**< \brief (LCDC) LCD Controller Configuration Register 5 */
#define REG_LCDC_LCDCFG6                (0xF0030018U) /**< \brief (LCDC) LCD Controller Configuration Register 6 */
#define REG_LCDC_LCDEN                  (0xF0030020U) /**< \brief (LCDC) LCD Controller Enable Register */
#define REG_LCDC_LCDDIS                 (0xF0030024U) /**< \brief (LCDC) LCD Controller Disable Register */
#define REG_LCDC_LCDSR                  (0xF0030028U) /**< \brief (LCDC) LCD Controller Status Register */
#define REG_LCDC_LCDIER                 (0xF003002CU) /**< \brief (LCDC) LCD Controller Interrupt Enable Register */
#define REG_LCDC_LCDIDR                 (0xF0030030U) /**< \brief (LCDC) LCD Controller Interrupt Disable Register */
#define REG_LCDC_LCDIMR                 (0xF0030034U) /**< \brief (LCDC) LCD Controller Interrupt Mask Register */
#define REG_LCDC_LCDISR                 (0xF0030038U) /**< \brief (LCDC) LCD Controller Interrupt Status Register */
#define REG_LCDC_BASECHER               (0xF0030040U) /**< \brief (LCDC) Base Layer Channel Enable Register */
#define REG_LCDC_BASECHDR               (0xF0030044U) /**< \brief (LCDC) Base Layer Channel Disable Register */
#define REG_LCDC_BASECHSR               (0xF0030048U) /**< \brief (LCDC) Base Layer Channel Status Register */
#define REG_LCDC_BASEIER                (0xF003004CU) /**< \brief (LCDC) Base Layer Interrupt Enable Register */
#define REG_LCDC_BASEIDR                (0xF0030050U) /**< \brief (LCDC) Base Layer Interrupt Disabled Register */
#define REG_LCDC_BASEIMR                (0xF0030054U) /**< \brief (LCDC) Base Layer Interrupt Mask Register */
#define REG_LCDC_BASEISR                (0xF0030058U) /**< \brief (LCDC) Base Layer Interrupt status Register */
#define REG_LCDC_BASEHEAD               (0xF003005CU) /**< \brief (LCDC) Base DMA Head Register */
#define REG_LCDC_BASEADDR               (0xF0030060U) /**< \brief (LCDC) Base DMA Address Register */
#define REG_LCDC_BASECTRL               (0xF0030064U) /**< \brief (LCDC) Base DMA Control Register */
#define REG_LCDC_BASENEXT               (0xF0030068U) /**< \brief (LCDC) Base DMA Next Register */
#define REG_LCDC_BASECFG0               (0xF003006CU) /**< \brief (LCDC) Base Configuration register 0 */
#define REG_LCDC_BASECFG1               (0xF0030070U) /**< \brief (LCDC) Base Configuration register 1 */
#define REG_LCDC_BASECFG2               (0xF0030074U) /**< \brief (LCDC) Base Configuration register 2 */
#define REG_LCDC_BASECFG3               (0xF0030078U) /**< \brief (LCDC) Base Configuration register 3 */
#define REG_LCDC_BASECFG4               (0xF003007CU) /**< \brief (LCDC) Base Configuration register 4 */
#define REG_LCDC_BASECFG5               (0xF0030080U) /**< \brief (LCDC) Base Configuration register 5 */
#define REG_LCDC_BASECFG6               (0xF0030084U) /**< \brief (LCDC) Base Configuration register 6 */
#define REG_LCDC_OVR1CHER               (0xF0030140U) /**< \brief (LCDC) Overlay 1 Channel Enable Register */
#define REG_LCDC_OVR1CHDR               (0xF0030144U) /**< \brief (LCDC) Overlay 1 Channel Disable Register */
#define REG_LCDC_OVR1CHSR               (0xF0030148U) /**< \brief (LCDC) Overlay 1 Channel Status Register */
#define REG_LCDC_OVR1IER                (0xF003014CU) /**< \brief (LCDC) Overlay 1 Interrupt Enable Register */
#define REG_LCDC_OVR1IDR                (0xF0030150U) /**< \brief (LCDC) Overlay 1 Interrupt Disable Register */
#define REG_LCDC_OVR1IMR                (0xF0030154U) /**< \brief (LCDC) Overlay 1 Interrupt Mask Register */
#define REG_LCDC_OVR1ISR                (0xF0030158U) /**< \brief (LCDC) Overlay 1 Interrupt Status Register */
#define REG_LCDC_OVR1HEAD               (0xF003015CU) /**< \brief (LCDC) Overlay 1 DMA Head Register */
#define REG_LCDC_OVR1ADDR               (0xF0030160U) /**< \brief (LCDC) Overlay 1 DMA Address Register */
#define REG_LCDC_OVR1CTRL               (0xF0030164U) /**< \brief (LCDC) Overlay1 DMA Control Register */
#define REG_LCDC_OVR1NEXT               (0xF0030168U) /**< \brief (LCDC) Overlay1 DMA Next Register */
#define REG_LCDC_OVR1CFG0               (0xF003016CU) /**< \brief (LCDC) Overlay 1 Configuration 0 Register */
#define REG_LCDC_OVR1CFG1               (0xF0030170U) /**< \brief (LCDC) Overlay 1 Configuration 1 Register */
#define REG_LCDC_OVR1CFG2               (0xF0030174U) /**< \brief (LCDC) Overlay 1 Configuration 2 Register */
#define REG_LCDC_OVR1CFG3               (0xF0030178U) /**< \brief (LCDC) Overlay 1 Configuration 3 Register */
#define REG_LCDC_OVR1CFG4               (0xF003017CU) /**< \brief (LCDC) Overlay 1 Configuration 4 Register */
#define REG_LCDC_OVR1CFG5               (0xF0030180U) /**< \brief (LCDC) Overlay 1 Configuration 5 Register */
#define REG_LCDC_OVR1CFG6               (0xF0030184U) /**< \brief (LCDC) Overlay 1 Configuration 6 Register */
#define REG_LCDC_OVR1CFG7               (0xF0030188U) /**< \brief (LCDC) Overlay 1 Configuration 7 Register */
#define REG_LCDC_OVR1CFG8               (0xF003018CU) /**< \brief (LCDC) Overlay 1 Configuration 8Register */
#define REG_LCDC_OVR1CFG9               (0xF0030190U) /**< \brief (LCDC) Overlay 1 Configuration 9 Register */
#define REG_LCDC_OVR2CHER               (0xF0030240U) /**< \brief (LCDC) Overlay 2 Channel Enable Register */
#define REG_LCDC_OVR2CHDR               (0xF0030244U) /**< \brief (LCDC) Overlay 2 Channel Disable Register */
#define REG_LCDC_OVR2CHSR               (0xF0030248U) /**< \brief (LCDC) Overlay 2 Channel Status Register */
#define REG_LCDC_OVR2IER                (0xF003024CU) /**< \brief (LCDC) Overlay 2 Interrupt Enable Register */
#define REG_LCDC_OVR2IDR                (0xF0030250U) /**< \brief (LCDC) Overlay 2 Interrupt Disable Register */
#define REG_LCDC_OVR2IMR                (0xF0030254U) /**< \brief (LCDC) Overlay 2 Interrupt Mask Register */
#define REG_LCDC_OVR2ISR                (0xF0030258U) /**< \brief (LCDC) Overlay 2 Interrupt status Register */
#define REG_LCDC_OVR2HEAD               (0xF003025CU) /**< \brief (LCDC) Overlay 2 DMA Head Register */
#define REG_LCDC_OVR2ADDR               (0xF0030260U) /**< \brief (LCDC) Overlay 2 DMA Address Register */
#define REG_LCDC_OVR2CTRL               (0xF0030264U) /**< \brief (LCDC) Overlay 2 DMA Control Register */
#define REG_LCDC_OVR2NEXT               (0xF0030268U) /**< \brief (LCDC) Overlay 2 DMA Next Register */
#define REG_LCDC_OVR2CFG0               (0xF003026CU) /**< \brief (LCDC) Overlay 2 Configuration 0 Register */
#define REG_LCDC_OVR2CFG1               (0xF0030270U) /**< \brief (LCDC) Overlay 2 Configuration 1 Register */
#define REG_LCDC_OVR2CFG2               (0xF0030274U) /**< \brief (LCDC) Overlay 2 Configuration 2 Register */
#define REG_LCDC_OVR2CFG3               (0xF0030278U) /**< \brief (LCDC) Overlay 2 Configuration 3 Register */
#define REG_LCDC_OVR2CFG4               (0xF003027CU) /**< \brief (LCDC) Overlay 2 Configuration 4 Register */
#define REG_LCDC_OVR2CFG5               (0xF0030280U) /**< \brief (LCDC) Overlay 2 Configuration 5 Register */
#define REG_LCDC_OVR2CFG6               (0xF0030284U) /**< \brief (LCDC) Overlay 2 Configuration 6 Register */
#define REG_LCDC_OVR2CFG7               (0xF0030288U) /**< \brief (LCDC) Overlay 2 Configuration 7 Register */
#define REG_LCDC_OVR2CFG8               (0xF003028CU) /**< \brief (LCDC) Overlay 2 Configuration 8 Register */
#define REG_LCDC_OVR2CFG9               (0xF0030290U) /**< \brief (LCDC) Overlay 2 Configuration 9 Register */
#define REG_LCDC_HEOCHER                (0xF0030340U) /**< \brief (LCDC) High-End Overlay Channel Enable Register */
#define REG_LCDC_HEOCHDR                (0xF0030344U) /**< \brief (LCDC) High-End Overlay Channel Disable Register */
#define REG_LCDC_HEOCHSR                (0xF0030348U) /**< \brief (LCDC) High-End Overlay Channel Status Register */
#define REG_LCDC_HEOIER                 (0xF003034CU) /**< \brief (LCDC) High-End Overlay Interrupt Enable Register */
#define REG_LCDC_HEOIDR                 (0xF0030350U) /**< \brief (LCDC) High-End Overlay Interrupt Disable Register */
#define REG_LCDC_HEOIMR                 (0xF0030354U) /**< \brief (LCDC) High-End Overlay Interrupt Mask Register */
#define REG_LCDC_HEOISR                 (0xF0030358U) /**< \brief (LCDC) High-End Overlay Interrupt Status Register */
#define REG_LCDC_HEOHEAD                (0xF003035CU) /**< \brief (LCDC) High-End Overlay DMA Head Register */
#define REG_LCDC_HEOADDR                (0xF0030360U) /**< \brief (LCDC) High-End Overlay DMA Address Register */
#define REG_LCDC_HEOCTRL                (0xF0030364U) /**< \brief (LCDC) High-End Overlay DMA Control Register */
#define REG_LCDC_HEONEXT                (0xF0030368U) /**< \brief (LCDC) High-End Overlay DMA Next Register */
#define REG_LCDC_HEOUHEAD               (0xF003036CU) /**< \brief (LCDC) High-End Overlay U DMA Head Register */
#define REG_LCDC_HEOUADDR               (0xF0030370U) /**< \brief (LCDC) High-End Overlay U DMA Address Register */
#define REG_LCDC_HEOUCTRL               (0xF0030374U) /**< \brief (LCDC) High-End Overlay U DMA control Register */
#define REG_LCDC_HEOUNEXT               (0xF0030378U) /**< \brief (LCDC) High-End Overlay U DMA Next Register */
#define REG_LCDC_HEOVHEAD               (0xF003037CU) /**< \brief (LCDC) High-End Overlay V DMA Head Register */
#define REG_LCDC_HEOVADDR               (0xF0030380U) /**< \brief (LCDC) High-End Overlay V DMA Address Register */
#define REG_LCDC_HEOVCTRL               (0xF0030384U) /**< \brief (LCDC) High-End Overlay V DMA control Register */
#define REG_LCDC_HEOVNEXT               (0xF0030388U) /**< \brief (LCDC) High-End Overlay VDMA Next Register */
#define REG_LCDC_HEOCFG0                (0xF003038CU) /**< \brief (LCDC) High-End Overlay Configuration Register 0 */
#define REG_LCDC_HEOCFG1                (0xF0030390U) /**< \brief (LCDC) High-End Overlay Configuration Register 1 */
#define REG_LCDC_HEOCFG2                (0xF0030394U) /**< \brief (LCDC) High-End Overlay Configuration Register 2 */
#define REG_LCDC_HEOCFG3                (0xF0030398U) /**< \brief (LCDC) High-End Overlay Configuration Register 3 */
#define REG_LCDC_HEOCFG4                (0xF003039CU) /**< \brief (LCDC) High-End Overlay Configuration Register 4 */
#define REG_LCDC_HEOCFG5                (0xF00303A0U) /**< \brief (LCDC) High-End Overlay Configuration Register 5 */
#define REG_LCDC_HEOCFG6                (0xF00303A4U) /**< \brief (LCDC) High-End Overlay Configuration Register 6 */
#define REG_LCDC_HEOCFG7                (0xF00303A8U) /**< \brief (LCDC) High-End Overlay Configuration Register 7 */
#define REG_LCDC_HEOCFG8                (0xF00303ACU) /**< \brief (LCDC) High-End Overlay Configuration Register 8 */
#define REG_LCDC_HEOCFG9                (0xF00303B0U) /**< \brief (LCDC) High-End Overlay Configuration Register 9 */
#define REG_LCDC_HEOCFG10               (0xF00303B4U) /**< \brief (LCDC) High-End Overlay Configuration Register 10 */
#define REG_LCDC_HEOCFG11               (0xF00303B8U) /**< \brief (LCDC) High-End Overlay Configuration Register 11 */
#define REG_LCDC_HEOCFG12               (0xF00303BCU) /**< \brief (LCDC) High-End Overlay Configuration Register 12 */
#define REG_LCDC_HEOCFG13               (0xF00303C0U) /**< \brief (LCDC) High-End Overlay Configuration Register 13 */
#define REG_LCDC_HEOCFG14               (0xF00303C4U) /**< \brief (LCDC) High-End Overlay Configuration Register 14 */
#define REG_LCDC_HEOCFG15               (0xF00303C8U) /**< \brief (LCDC) High-End Overlay Configuration Register 15 */
#define REG_LCDC_HEOCFG16               (0xF00303CCU) /**< \brief (LCDC) High-End Overlay Configuration Register 16 */
#define REG_LCDC_HEOCFG17               (0xF00303D0U) /**< \brief (LCDC) High-End Overlay Configuration Register 17 */
#define REG_LCDC_HEOCFG18               (0xF00303D4U) /**< \brief (LCDC) High-End Overlay Configuration Register 18 */
#define REG_LCDC_HEOCFG19               (0xF00303D8U) /**< \brief (LCDC) High-End Overlay Configuration Register 19 */
#define REG_LCDC_HEOCFG20               (0xF00303DCU) /**< \brief (LCDC) High-End Overlay Configuration Register 20 */
#define REG_LCDC_HEOCFG21               (0xF00303E0U) /**< \brief (LCDC) High-End Overlay Configuration Register 21 */
#define REG_LCDC_HEOCFG22               (0xF00303E4U) /**< \brief (LCDC) High-End Overlay Configuration Register 22 */
#define REG_LCDC_HEOCFG23               (0xF00303E8U) /**< \brief (LCDC) High-End Overlay Configuration Register 23 */
#define REG_LCDC_HEOCFG24               (0xF00303ECU) /**< \brief (LCDC) High-End Overlay Configuration Register 24 */
#define REG_LCDC_HEOCFG25               (0xF00303F0U) /**< \brief (LCDC) High-End Overlay Configuration Register 25 */
#define REG_LCDC_HEOCFG26               (0xF00303F4U) /**< \brief (LCDC) High-End Overlay Configuration Register 26 */
#define REG_LCDC_HEOCFG27               (0xF00303F8U) /**< \brief (LCDC) High-End Overlay Configuration Register 27 */
#define REG_LCDC_HEOCFG28               (0xF00303FCU) /**< \brief (LCDC) High-End Overlay Configuration Register 28 */
#define REG_LCDC_HEOCFG29               (0xF0030400U) /**< \brief (LCDC) High-End Overlay Configuration Register 29 */
#define REG_LCDC_HEOCFG30               (0xF0030404U) /**< \brief (LCDC) High-End Overlay Configuration Register 30 */
#define REG_LCDC_HEOCFG31               (0xF0030408U) /**< \brief (LCDC) High-End Overlay Configuration Register 31 */
#define REG_LCDC_HEOCFG32               (0xF003040CU) /**< \brief (LCDC) High-End Overlay Configuration Register 32 */
#define REG_LCDC_HEOCFG33               (0xF0030410U) /**< \brief (LCDC) High-End Overlay Configuration Register 33 */
#define REG_LCDC_HEOCFG34               (0xF0030414U) /**< \brief (LCDC) High-End Overlay Configuration Register 34 */
#define REG_LCDC_HEOCFG35               (0xF0030418U) /**< \brief (LCDC) High-End Overlay Configuration Register 35 */
#define REG_LCDC_HEOCFG36               (0xF003041CU) /**< \brief (LCDC) High-End Overlay Configuration Register 36 */
#define REG_LCDC_HEOCFG37               (0xF0030420U) /**< \brief (LCDC) High-End Overlay Configuration Register 37 */
#define REG_LCDC_HEOCFG38               (0xF0030424U) /**< \brief (LCDC) High-End Overlay Configuration Register 38 */
#define REG_LCDC_HEOCFG39               (0xF0030428U) /**< \brief (LCDC) High-End Overlay Configuration Register 39 */
#define REG_LCDC_HEOCFG40               (0xF003042CU) /**< \brief (LCDC) High-End Overlay Configuration Register 40 */
#define REG_LCDC_HEOCFG41               (0xF0030430U) /**< \brief (LCDC) High-End Overlay Configuration Register 41 */
#define REG_LCDC_HCRCHER                (0xF0030440U) /**< \brief (LCDC) Hardware Cursor Channel Enable Register */
#define REG_LCDC_HCRCHDR                (0xF0030444U) /**< \brief (LCDC) Hardware Cursor Channel disable Register */
#define REG_LCDC_HCRCHSR                (0xF0030448U) /**< \brief (LCDC) Hardware Cursor Channel Status Register */
#define REG_LCDC_HCRIER                 (0xF003044CU) /**< \brief (LCDC) Hardware Cursor Interrupt Enable Register */
#define REG_LCDC_HCRIDR                 (0xF0030450U) /**< \brief (LCDC) Hardware Cursor Interrupt Disable Register */
#define REG_LCDC_HCRIMR                 (0xF0030454U) /**< \brief (LCDC) Hardware Cursor Interrupt Mask Register */
#define REG_LCDC_HCRISR                 (0xF0030458U) /**< \brief (LCDC) Hardware Cursor Interrupt Status Register */
#define REG_LCDC_HCRHEAD                (0xF003045CU) /**< \brief (LCDC) Hardware Cursor DMA Head Register */
#define REG_LCDC_HCRADDR                (0xF0030460U) /**< \brief (LCDC) Hardware cursor DMA Address Register */
#define REG_LCDC_HCRCTRL                (0xF0030464U) /**< \brief (LCDC) Hardware Cursor DMA Control Register */
#define REG_LCDC_HCRNEXT                (0xF0030468U) /**< \brief (LCDC) Hardware Cursor DMA NExt Register */
#define REG_LCDC_HCRCFG0                (0xF003046CU) /**< \brief (LCDC) Hardware Cursor Configuration 0 Register */
#define REG_LCDC_HCRCFG1                (0xF0030470U) /**< \brief (LCDC) Hardware Cursor Configuration 1 Register */
#define REG_LCDC_HCRCFG2                (0xF0030474U) /**< \brief (LCDC) Hardware Cursor Configuration 2 Register */
#define REG_LCDC_HCRCFG3                (0xF0030478U) /**< \brief (LCDC) Hardware Cursor Configuration 3 Register */
#define REG_LCDC_HCRCFG4                (0xF003047CU) /**< \brief (LCDC) Hardware Cursor Configuration 4 Register */
#define REG_LCDC_HCRCFG6                (0xF0030484U) /**< \brief (LCDC) Hardware Cursor Configuration 6 Register */
#define REG_LCDC_HCRCFG7                (0xF0030488U) /**< \brief (LCDC) Hardware Cursor Configuration 7 Register */
#define REG_LCDC_HCRCFG8                (0xF003048CU) /**< \brief (LCDC) Hardware Cursor Configuration 8 Register */
#define REG_LCDC_HCRCFG9                (0xF0030490U) /**< \brief (LCDC) Hardware Cursor Configuration 9 Register */
#define REG_LCDC_PPCHER                 (0xF0030540U) /**< \brief (LCDC) Post Processing Channel Enable Register */
#define REG_LCDC_PPCHDR                 (0xF0030544U) /**< \brief (LCDC) Post Processing Channel Disable Register */
#define REG_LCDC_PPCHSR                 (0xF0030548U) /**< \brief (LCDC) Post Processing Channel Status Register */
#define REG_LCDC_PPIER                  (0xF003054CU) /**< \brief (LCDC) Post Processing Interrupt Enable Register */
#define REG_LCDC_PPIDR                  (0xF0030550U) /**< \brief (LCDC) Post Processing Interrupt Disable Register */
#define REG_LCDC_PPIMR                  (0xF0030554U) /**< \brief (LCDC) Post Processing Interrupt Mask Register */
#define REG_LCDC_PPISR                  (0xF0030558U) /**< \brief (LCDC) Post Processing Interrupt Status Register */
#define REG_LCDC_PPHEAD                 (0xF003055CU) /**< \brief (LCDC) Post Processing Head Register */
#define REG_LCDC_PPADDR                 (0xF0030560U) /**< \brief (LCDC) Post Processing Address Register */
#define REG_LCDC_PPCTRL                 (0xF0030564U) /**< \brief (LCDC) Post Processing Control Register */
#define REG_LCDC_PPNEXT                 (0xF0030568U) /**< \brief (LCDC) Post Processing Next Register */
#define REG_LCDC_PPCFG0                 (0xF003056CU) /**< \brief (LCDC) Post Processing Configuration Register 0 */
#define REG_LCDC_PPCFG1                 (0xF0030570U) /**< \brief (LCDC) Post Processing Configuration Register 1 */
#define REG_LCDC_PPCFG2                 (0xF0030574U) /**< \brief (LCDC) Post Processing Configuration Register 2 */
#define REG_LCDC_PPCFG3                 (0xF0030578U) /**< \brief (LCDC) Post Processing Configuration Register 3 */
#define REG_LCDC_PPCFG4                 (0xF003057CU) /**< \brief (LCDC) Post Processing Configuration Register 4 */
#define REG_LCDC_PPCFG5                 (0xF0030580U) /**< \brief (LCDC) Post Processing Configuration Register 5 */
#define REG_LCDC_BASECLUT               (0xF0030600U) /**< \brief (LCDC) Base CLUT Register */
#define REG_LCDC_OVR1CLUT               (0xF0030A00U) /**< \brief (LCDC) Overlay 1 CLUT Register */
#define REG_LCDC_OVR2CLUT               (0xF0030E00U) /**< \brief (LCDC) Overlay 2 CLUT Register */
#define REG_LCDC_HEOCLUT                (0xF0031200U) /**< \brief (LCDC) High End Overlay CLUT Register */
#define REG_LCDC_HCRCLUT                (0xF0031600U) /**< \brief (LCDC) Hardware Cursor CLUT Register */
#else
#define REG_LCDC_LCDCFG0       (*(RwReg*)0xF0030000U) /**< \brief (LCDC) LCD Controller Configuration Register 0 */
#define REG_LCDC_LCDCFG1       (*(RwReg*)0xF0030004U) /**< \brief (LCDC) LCD Controller Configuration Register 1 */
#define REG_LCDC_LCDCFG2       (*(RwReg*)0xF0030008U) /**< \brief (LCDC) LCD Controller Configuration Register 2 */
#define REG_LCDC_LCDCFG3       (*(RwReg*)0xF003000CU) /**< \brief (LCDC) LCD Controller Configuration Register 3 */
#define REG_LCDC_LCDCFG4       (*(RwReg*)0xF0030010U) /**< \brief (LCDC) LCD Controller Configuration Register 4 */
#define REG_LCDC_LCDCFG5       (*(RwReg*)0xF0030014U) /**< \brief (LCDC) LCD Controller Configuration Register 5 */
#define REG_LCDC_LCDCFG6       (*(RwReg*)0xF0030018U) /**< \brief (LCDC) LCD Controller Configuration Register 6 */
#define REG_LCDC_LCDEN         (*(WoReg*)0xF0030020U) /**< \brief (LCDC) LCD Controller Enable Register */
#define REG_LCDC_LCDDIS        (*(WoReg*)0xF0030024U) /**< \brief (LCDC) LCD Controller Disable Register */
#define REG_LCDC_LCDSR         (*(RoReg*)0xF0030028U) /**< \brief (LCDC) LCD Controller Status Register */
#define REG_LCDC_LCDIER        (*(WoReg*)0xF003002CU) /**< \brief (LCDC) LCD Controller Interrupt Enable Register */
#define REG_LCDC_LCDIDR        (*(WoReg*)0xF0030030U) /**< \brief (LCDC) LCD Controller Interrupt Disable Register */
#define REG_LCDC_LCDIMR        (*(RoReg*)0xF0030034U) /**< \brief (LCDC) LCD Controller Interrupt Mask Register */
#define REG_LCDC_LCDISR        (*(RoReg*)0xF0030038U) /**< \brief (LCDC) LCD Controller Interrupt Status Register */
#define REG_LCDC_BASECHER      (*(WoReg*)0xF0030040U) /**< \brief (LCDC) Base Layer Channel Enable Register */
#define REG_LCDC_BASECHDR      (*(WoReg*)0xF0030044U) /**< \brief (LCDC) Base Layer Channel Disable Register */
#define REG_LCDC_BASECHSR      (*(RoReg*)0xF0030048U) /**< \brief (LCDC) Base Layer Channel Status Register */
#define REG_LCDC_BASEIER       (*(WoReg*)0xF003004CU) /**< \brief (LCDC) Base Layer Interrupt Enable Register */
#define REG_LCDC_BASEIDR       (*(WoReg*)0xF0030050U) /**< \brief (LCDC) Base Layer Interrupt Disabled Register */
#define REG_LCDC_BASEIMR       (*(RoReg*)0xF0030054U) /**< \brief (LCDC) Base Layer Interrupt Mask Register */
#define REG_LCDC_BASEISR       (*(RoReg*)0xF0030058U) /**< \brief (LCDC) Base Layer Interrupt status Register */
#define REG_LCDC_BASEHEAD      (*(RwReg*)0xF003005CU) /**< \brief (LCDC) Base DMA Head Register */
#define REG_LCDC_BASEADDR      (*(RwReg*)0xF0030060U) /**< \brief (LCDC) Base DMA Address Register */
#define REG_LCDC_BASECTRL      (*(RwReg*)0xF0030064U) /**< \brief (LCDC) Base DMA Control Register */
#define REG_LCDC_BASENEXT      (*(RwReg*)0xF0030068U) /**< \brief (LCDC) Base DMA Next Register */
#define REG_LCDC_BASECFG0      (*(RwReg*)0xF003006CU) /**< \brief (LCDC) Base Configuration register 0 */
#define REG_LCDC_BASECFG1      (*(RwReg*)0xF0030070U) /**< \brief (LCDC) Base Configuration register 1 */
#define REG_LCDC_BASECFG2      (*(RwReg*)0xF0030074U) /**< \brief (LCDC) Base Configuration register 2 */
#define REG_LCDC_BASECFG3      (*(RwReg*)0xF0030078U) /**< \brief (LCDC) Base Configuration register 3 */
#define REG_LCDC_BASECFG4      (*(RwReg*)0xF003007CU) /**< \brief (LCDC) Base Configuration register 4 */
#define REG_LCDC_BASECFG5      (*(RwReg*)0xF0030080U) /**< \brief (LCDC) Base Configuration register 5 */
#define REG_LCDC_BASECFG6      (*(RwReg*)0xF0030084U) /**< \brief (LCDC) Base Configuration register 6 */
#define REG_LCDC_OVR1CHER      (*(WoReg*)0xF0030140U) /**< \brief (LCDC) Overlay 1 Channel Enable Register */
#define REG_LCDC_OVR1CHDR      (*(WoReg*)0xF0030144U) /**< \brief (LCDC) Overlay 1 Channel Disable Register */
#define REG_LCDC_OVR1CHSR      (*(RoReg*)0xF0030148U) /**< \brief (LCDC) Overlay 1 Channel Status Register */
#define REG_LCDC_OVR1IER       (*(WoReg*)0xF003014CU) /**< \brief (LCDC) Overlay 1 Interrupt Enable Register */
#define REG_LCDC_OVR1IDR       (*(WoReg*)0xF0030150U) /**< \brief (LCDC) Overlay 1 Interrupt Disable Register */
#define REG_LCDC_OVR1IMR       (*(RoReg*)0xF0030154U) /**< \brief (LCDC) Overlay 1 Interrupt Mask Register */
#define REG_LCDC_OVR1ISR       (*(RoReg*)0xF0030158U) /**< \brief (LCDC) Overlay 1 Interrupt Status Register */
#define REG_LCDC_OVR1HEAD      (*(RwReg*)0xF003015CU) /**< \brief (LCDC) Overlay 1 DMA Head Register */
#define REG_LCDC_OVR1ADDR      (*(RwReg*)0xF0030160U) /**< \brief (LCDC) Overlay 1 DMA Address Register */
#define REG_LCDC_OVR1CTRL      (*(RwReg*)0xF0030164U) /**< \brief (LCDC) Overlay1 DMA Control Register */
#define REG_LCDC_OVR1NEXT      (*(RwReg*)0xF0030168U) /**< \brief (LCDC) Overlay1 DMA Next Register */
#define REG_LCDC_OVR1CFG0      (*(RwReg*)0xF003016CU) /**< \brief (LCDC) Overlay 1 Configuration 0 Register */
#define REG_LCDC_OVR1CFG1      (*(RwReg*)0xF0030170U) /**< \brief (LCDC) Overlay 1 Configuration 1 Register */
#define REG_LCDC_OVR1CFG2      (*(RwReg*)0xF0030174U) /**< \brief (LCDC) Overlay 1 Configuration 2 Register */
#define REG_LCDC_OVR1CFG3      (*(RwReg*)0xF0030178U) /**< \brief (LCDC) Overlay 1 Configuration 3 Register */
#define REG_LCDC_OVR1CFG4      (*(RwReg*)0xF003017CU) /**< \brief (LCDC) Overlay 1 Configuration 4 Register */
#define REG_LCDC_OVR1CFG5      (*(RwReg*)0xF0030180U) /**< \brief (LCDC) Overlay 1 Configuration 5 Register */
#define REG_LCDC_OVR1CFG6      (*(RwReg*)0xF0030184U) /**< \brief (LCDC) Overlay 1 Configuration 6 Register */
#define REG_LCDC_OVR1CFG7      (*(RwReg*)0xF0030188U) /**< \brief (LCDC) Overlay 1 Configuration 7 Register */
#define REG_LCDC_OVR1CFG8      (*(RwReg*)0xF003018CU) /**< \brief (LCDC) Overlay 1 Configuration 8Register */
#define REG_LCDC_OVR1CFG9      (*(RwReg*)0xF0030190U) /**< \brief (LCDC) Overlay 1 Configuration 9 Register */
#define REG_LCDC_OVR2CHER      (*(WoReg*)0xF0030240U) /**< \brief (LCDC) Overlay 2 Channel Enable Register */
#define REG_LCDC_OVR2CHDR      (*(WoReg*)0xF0030244U) /**< \brief (LCDC) Overlay 2 Channel Disable Register */
#define REG_LCDC_OVR2CHSR      (*(RoReg*)0xF0030248U) /**< \brief (LCDC) Overlay 2 Channel Status Register */
#define REG_LCDC_OVR2IER       (*(WoReg*)0xF003024CU) /**< \brief (LCDC) Overlay 2 Interrupt Enable Register */
#define REG_LCDC_OVR2IDR       (*(WoReg*)0xF0030250U) /**< \brief (LCDC) Overlay 2 Interrupt Disable Register */
#define REG_LCDC_OVR2IMR       (*(RoReg*)0xF0030254U) /**< \brief (LCDC) Overlay 2 Interrupt Mask Register */
#define REG_LCDC_OVR2ISR       (*(RoReg*)0xF0030258U) /**< \brief (LCDC) Overlay 2 Interrupt status Register */
#define REG_LCDC_OVR2HEAD      (*(RwReg*)0xF003025CU) /**< \brief (LCDC) Overlay 2 DMA Head Register */
#define REG_LCDC_OVR2ADDR      (*(RwReg*)0xF0030260U) /**< \brief (LCDC) Overlay 2 DMA Address Register */
#define REG_LCDC_OVR2CTRL      (*(RwReg*)0xF0030264U) /**< \brief (LCDC) Overlay 2 DMA Control Register */
#define REG_LCDC_OVR2NEXT      (*(RwReg*)0xF0030268U) /**< \brief (LCDC) Overlay 2 DMA Next Register */
#define REG_LCDC_OVR2CFG0      (*(RwReg*)0xF003026CU) /**< \brief (LCDC) Overlay 2 Configuration 0 Register */
#define REG_LCDC_OVR2CFG1      (*(RwReg*)0xF0030270U) /**< \brief (LCDC) Overlay 2 Configuration 1 Register */
#define REG_LCDC_OVR2CFG2      (*(RwReg*)0xF0030274U) /**< \brief (LCDC) Overlay 2 Configuration 2 Register */
#define REG_LCDC_OVR2CFG3      (*(RwReg*)0xF0030278U) /**< \brief (LCDC) Overlay 2 Configuration 3 Register */
#define REG_LCDC_OVR2CFG4      (*(RwReg*)0xF003027CU) /**< \brief (LCDC) Overlay 2 Configuration 4 Register */
#define REG_LCDC_OVR2CFG5      (*(RwReg*)0xF0030280U) /**< \brief (LCDC) Overlay 2 Configuration 5 Register */
#define REG_LCDC_OVR2CFG6      (*(RwReg*)0xF0030284U) /**< \brief (LCDC) Overlay 2 Configuration 6 Register */
#define REG_LCDC_OVR2CFG7      (*(RwReg*)0xF0030288U) /**< \brief (LCDC) Overlay 2 Configuration 7 Register */
#define REG_LCDC_OVR2CFG8      (*(RwReg*)0xF003028CU) /**< \brief (LCDC) Overlay 2 Configuration 8 Register */
#define REG_LCDC_OVR2CFG9      (*(RwReg*)0xF0030290U) /**< \brief (LCDC) Overlay 2 Configuration 9 Register */
#define REG_LCDC_HEOCHER       (*(WoReg*)0xF0030340U) /**< \brief (LCDC) High-End Overlay Channel Enable Register */
#define REG_LCDC_HEOCHDR       (*(WoReg*)0xF0030344U) /**< \brief (LCDC) High-End Overlay Channel Disable Register */
#define REG_LCDC_HEOCHSR       (*(RoReg*)0xF0030348U) /**< \brief (LCDC) High-End Overlay Channel Status Register */
#define REG_LCDC_HEOIER        (*(WoReg*)0xF003034CU) /**< \brief (LCDC) High-End Overlay Interrupt Enable Register */
#define REG_LCDC_HEOIDR        (*(WoReg*)0xF0030350U) /**< \brief (LCDC) High-End Overlay Interrupt Disable Register */
#define REG_LCDC_HEOIMR        (*(RoReg*)0xF0030354U) /**< \brief (LCDC) High-End Overlay Interrupt Mask Register */
#define REG_LCDC_HEOISR        (*(RoReg*)0xF0030358U) /**< \brief (LCDC) High-End Overlay Interrupt Status Register */
#define REG_LCDC_HEOHEAD       (*(RwReg*)0xF003035CU) /**< \brief (LCDC) High-End Overlay DMA Head Register */
#define REG_LCDC_HEOADDR       (*(RwReg*)0xF0030360U) /**< \brief (LCDC) High-End Overlay DMA Address Register */
#define REG_LCDC_HEOCTRL       (*(RwReg*)0xF0030364U) /**< \brief (LCDC) High-End Overlay DMA Control Register */
#define REG_LCDC_HEONEXT       (*(RwReg*)0xF0030368U) /**< \brief (LCDC) High-End Overlay DMA Next Register */
#define REG_LCDC_HEOUHEAD      (*(RwReg*)0xF003036CU) /**< \brief (LCDC) High-End Overlay U DMA Head Register */
#define REG_LCDC_HEOUADDR      (*(RwReg*)0xF0030370U) /**< \brief (LCDC) High-End Overlay U DMA Address Register */
#define REG_LCDC_HEOUCTRL      (*(RwReg*)0xF0030374U) /**< \brief (LCDC) High-End Overlay U DMA control Register */
#define REG_LCDC_HEOUNEXT      (*(RwReg*)0xF0030378U) /**< \brief (LCDC) High-End Overlay U DMA Next Register */
#define REG_LCDC_HEOVHEAD      (*(RwReg*)0xF003037CU) /**< \brief (LCDC) High-End Overlay V DMA Head Register */
#define REG_LCDC_HEOVADDR      (*(RwReg*)0xF0030380U) /**< \brief (LCDC) High-End Overlay V DMA Address Register */
#define REG_LCDC_HEOVCTRL      (*(RwReg*)0xF0030384U) /**< \brief (LCDC) High-End Overlay V DMA control Register */
#define REG_LCDC_HEOVNEXT      (*(RwReg*)0xF0030388U) /**< \brief (LCDC) High-End Overlay VDMA Next Register */
#define REG_LCDC_HEOCFG0       (*(RwReg*)0xF003038CU) /**< \brief (LCDC) High-End Overlay Configuration Register 0 */
#define REG_LCDC_HEOCFG1       (*(RwReg*)0xF0030390U) /**< \brief (LCDC) High-End Overlay Configuration Register 1 */
#define REG_LCDC_HEOCFG2       (*(RwReg*)0xF0030394U) /**< \brief (LCDC) High-End Overlay Configuration Register 2 */
#define REG_LCDC_HEOCFG3       (*(RwReg*)0xF0030398U) /**< \brief (LCDC) High-End Overlay Configuration Register 3 */
#define REG_LCDC_HEOCFG4       (*(RwReg*)0xF003039CU) /**< \brief (LCDC) High-End Overlay Configuration Register 4 */
#define REG_LCDC_HEOCFG5       (*(RwReg*)0xF00303A0U) /**< \brief (LCDC) High-End Overlay Configuration Register 5 */
#define REG_LCDC_HEOCFG6       (*(RwReg*)0xF00303A4U) /**< \brief (LCDC) High-End Overlay Configuration Register 6 */
#define REG_LCDC_HEOCFG7       (*(RwReg*)0xF00303A8U) /**< \brief (LCDC) High-End Overlay Configuration Register 7 */
#define REG_LCDC_HEOCFG8       (*(RwReg*)0xF00303ACU) /**< \brief (LCDC) High-End Overlay Configuration Register 8 */
#define REG_LCDC_HEOCFG9       (*(RwReg*)0xF00303B0U) /**< \brief (LCDC) High-End Overlay Configuration Register 9 */
#define REG_LCDC_HEOCFG10      (*(RwReg*)0xF00303B4U) /**< \brief (LCDC) High-End Overlay Configuration Register 10 */
#define REG_LCDC_HEOCFG11      (*(RwReg*)0xF00303B8U) /**< \brief (LCDC) High-End Overlay Configuration Register 11 */
#define REG_LCDC_HEOCFG12      (*(RwReg*)0xF00303BCU) /**< \brief (LCDC) High-End Overlay Configuration Register 12 */
#define REG_LCDC_HEOCFG13      (*(RwReg*)0xF00303C0U) /**< \brief (LCDC) High-End Overlay Configuration Register 13 */
#define REG_LCDC_HEOCFG14      (*(RwReg*)0xF00303C4U) /**< \brief (LCDC) High-End Overlay Configuration Register 14 */
#define REG_LCDC_HEOCFG15      (*(RwReg*)0xF00303C8U) /**< \brief (LCDC) High-End Overlay Configuration Register 15 */
#define REG_LCDC_HEOCFG16      (*(RwReg*)0xF00303CCU) /**< \brief (LCDC) High-End Overlay Configuration Register 16 */
#define REG_LCDC_HEOCFG17      (*(RwReg*)0xF00303D0U) /**< \brief (LCDC) High-End Overlay Configuration Register 17 */
#define REG_LCDC_HEOCFG18      (*(RwReg*)0xF00303D4U) /**< \brief (LCDC) High-End Overlay Configuration Register 18 */
#define REG_LCDC_HEOCFG19      (*(RwReg*)0xF00303D8U) /**< \brief (LCDC) High-End Overlay Configuration Register 19 */
#define REG_LCDC_HEOCFG20      (*(RwReg*)0xF00303DCU) /**< \brief (LCDC) High-End Overlay Configuration Register 20 */
#define REG_LCDC_HEOCFG21      (*(RwReg*)0xF00303E0U) /**< \brief (LCDC) High-End Overlay Configuration Register 21 */
#define REG_LCDC_HEOCFG22      (*(RwReg*)0xF00303E4U) /**< \brief (LCDC) High-End Overlay Configuration Register 22 */
#define REG_LCDC_HEOCFG23      (*(RwReg*)0xF00303E8U) /**< \brief (LCDC) High-End Overlay Configuration Register 23 */
#define REG_LCDC_HEOCFG24      (*(RwReg*)0xF00303ECU) /**< \brief (LCDC) High-End Overlay Configuration Register 24 */
#define REG_LCDC_HEOCFG25      (*(RwReg*)0xF00303F0U) /**< \brief (LCDC) High-End Overlay Configuration Register 25 */
#define REG_LCDC_HEOCFG26      (*(RwReg*)0xF00303F4U) /**< \brief (LCDC) High-End Overlay Configuration Register 26 */
#define REG_LCDC_HEOCFG27      (*(RwReg*)0xF00303F8U) /**< \brief (LCDC) High-End Overlay Configuration Register 27 */
#define REG_LCDC_HEOCFG28      (*(RwReg*)0xF00303FCU) /**< \brief (LCDC) High-End Overlay Configuration Register 28 */
#define REG_LCDC_HEOCFG29      (*(RwReg*)0xF0030400U) /**< \brief (LCDC) High-End Overlay Configuration Register 29 */
#define REG_LCDC_HEOCFG30      (*(RwReg*)0xF0030404U) /**< \brief (LCDC) High-End Overlay Configuration Register 30 */
#define REG_LCDC_HEOCFG31      (*(RwReg*)0xF0030408U) /**< \brief (LCDC) High-End Overlay Configuration Register 31 */
#define REG_LCDC_HEOCFG32      (*(RwReg*)0xF003040CU) /**< \brief (LCDC) High-End Overlay Configuration Register 32 */
#define REG_LCDC_HEOCFG33      (*(RwReg*)0xF0030410U) /**< \brief (LCDC) High-End Overlay Configuration Register 33 */
#define REG_LCDC_HEOCFG34      (*(RwReg*)0xF0030414U) /**< \brief (LCDC) High-End Overlay Configuration Register 34 */
#define REG_LCDC_HEOCFG35      (*(RwReg*)0xF0030418U) /**< \brief (LCDC) High-End Overlay Configuration Register 35 */
#define REG_LCDC_HEOCFG36      (*(RwReg*)0xF003041CU) /**< \brief (LCDC) High-End Overlay Configuration Register 36 */
#define REG_LCDC_HEOCFG37      (*(RwReg*)0xF0030420U) /**< \brief (LCDC) High-End Overlay Configuration Register 37 */
#define REG_LCDC_HEOCFG38      (*(RwReg*)0xF0030424U) /**< \brief (LCDC) High-End Overlay Configuration Register 38 */
#define REG_LCDC_HEOCFG39      (*(RwReg*)0xF0030428U) /**< \brief (LCDC) High-End Overlay Configuration Register 39 */
#define REG_LCDC_HEOCFG40      (*(RwReg*)0xF003042CU) /**< \brief (LCDC) High-End Overlay Configuration Register 40 */
#define REG_LCDC_HEOCFG41      (*(RwReg*)0xF0030430U) /**< \brief (LCDC) High-End Overlay Configuration Register 41 */
#define REG_LCDC_HCRCHER       (*(WoReg*)0xF0030440U) /**< \brief (LCDC) Hardware Cursor Channel Enable Register */
#define REG_LCDC_HCRCHDR       (*(WoReg*)0xF0030444U) /**< \brief (LCDC) Hardware Cursor Channel disable Register */
#define REG_LCDC_HCRCHSR       (*(RoReg*)0xF0030448U) /**< \brief (LCDC) Hardware Cursor Channel Status Register */
#define REG_LCDC_HCRIER        (*(WoReg*)0xF003044CU) /**< \brief (LCDC) Hardware Cursor Interrupt Enable Register */
#define REG_LCDC_HCRIDR        (*(WoReg*)0xF0030450U) /**< \brief (LCDC) Hardware Cursor Interrupt Disable Register */
#define REG_LCDC_HCRIMR        (*(RoReg*)0xF0030454U) /**< \brief (LCDC) Hardware Cursor Interrupt Mask Register */
#define REG_LCDC_HCRISR        (*(RoReg*)0xF0030458U) /**< \brief (LCDC) Hardware Cursor Interrupt Status Register */
#define REG_LCDC_HCRHEAD       (*(RwReg*)0xF003045CU) /**< \brief (LCDC) Hardware Cursor DMA Head Register */
#define REG_LCDC_HCRADDR       (*(RwReg*)0xF0030460U) /**< \brief (LCDC) Hardware cursor DMA Address Register */
#define REG_LCDC_HCRCTRL       (*(RwReg*)0xF0030464U) /**< \brief (LCDC) Hardware Cursor DMA Control Register */
#define REG_LCDC_HCRNEXT       (*(RwReg*)0xF0030468U) /**< \brief (LCDC) Hardware Cursor DMA NExt Register */
#define REG_LCDC_HCRCFG0       (*(RwReg*)0xF003046CU) /**< \brief (LCDC) Hardware Cursor Configuration 0 Register */
#define REG_LCDC_HCRCFG1       (*(RwReg*)0xF0030470U) /**< \brief (LCDC) Hardware Cursor Configuration 1 Register */
#define REG_LCDC_HCRCFG2       (*(RwReg*)0xF0030474U) /**< \brief (LCDC) Hardware Cursor Configuration 2 Register */
#define REG_LCDC_HCRCFG3       (*(RwReg*)0xF0030478U) /**< \brief (LCDC) Hardware Cursor Configuration 3 Register */
#define REG_LCDC_HCRCFG4       (*(RwReg*)0xF003047CU) /**< \brief (LCDC) Hardware Cursor Configuration 4 Register */
#define REG_LCDC_HCRCFG6       (*(RwReg*)0xF0030484U) /**< \brief (LCDC) Hardware Cursor Configuration 6 Register */
#define REG_LCDC_HCRCFG7       (*(RwReg*)0xF0030488U) /**< \brief (LCDC) Hardware Cursor Configuration 7 Register */
#define REG_LCDC_HCRCFG8       (*(RwReg*)0xF003048CU) /**< \brief (LCDC) Hardware Cursor Configuration 8 Register */
#define REG_LCDC_HCRCFG9       (*(RwReg*)0xF0030490U) /**< \brief (LCDC) Hardware Cursor Configuration 9 Register */
#define REG_LCDC_PPCHER        (*(WoReg*)0xF0030540U) /**< \brief (LCDC) Post Processing Channel Enable Register */
#define REG_LCDC_PPCHDR        (*(WoReg*)0xF0030544U) /**< \brief (LCDC) Post Processing Channel Disable Register */
#define REG_LCDC_PPCHSR        (*(RoReg*)0xF0030548U) /**< \brief (LCDC) Post Processing Channel Status Register */
#define REG_LCDC_PPIER         (*(WoReg*)0xF003054CU) /**< \brief (LCDC) Post Processing Interrupt Enable Register */
#define REG_LCDC_PPIDR         (*(WoReg*)0xF0030550U) /**< \brief (LCDC) Post Processing Interrupt Disable Register */
#define REG_LCDC_PPIMR         (*(RoReg*)0xF0030554U) /**< \brief (LCDC) Post Processing Interrupt Mask Register */
#define REG_LCDC_PPISR         (*(RoReg*)0xF0030558U) /**< \brief (LCDC) Post Processing Interrupt Status Register */
#define REG_LCDC_PPHEAD        (*(RwReg*)0xF003055CU) /**< \brief (LCDC) Post Processing Head Register */
#define REG_LCDC_PPADDR        (*(RwReg*)0xF0030560U) /**< \brief (LCDC) Post Processing Address Register */
#define REG_LCDC_PPCTRL        (*(RwReg*)0xF0030564U) /**< \brief (LCDC) Post Processing Control Register */
#define REG_LCDC_PPNEXT        (*(RwReg*)0xF0030568U) /**< \brief (LCDC) Post Processing Next Register */
#define REG_LCDC_PPCFG0        (*(RwReg*)0xF003056CU) /**< \brief (LCDC) Post Processing Configuration Register 0 */
#define REG_LCDC_PPCFG1        (*(RwReg*)0xF0030570U) /**< \brief (LCDC) Post Processing Configuration Register 1 */
#define REG_LCDC_PPCFG2        (*(RwReg*)0xF0030574U) /**< \brief (LCDC) Post Processing Configuration Register 2 */
#define REG_LCDC_PPCFG3        (*(RwReg*)0xF0030578U) /**< \brief (LCDC) Post Processing Configuration Register 3 */
#define REG_LCDC_PPCFG4        (*(RwReg*)0xF003057CU) /**< \brief (LCDC) Post Processing Configuration Register 4 */
#define REG_LCDC_PPCFG5        (*(RwReg*)0xF0030580U) /**< \brief (LCDC) Post Processing Configuration Register 5 */
#define REG_LCDC_BASECLUT      (*(RwReg*)0xF0030600U) /**< \brief (LCDC) Base CLUT Register */
#define REG_LCDC_OVR1CLUT      (*(RwReg*)0xF0030A00U) /**< \brief (LCDC) Overlay 1 CLUT Register */
#define REG_LCDC_OVR2CLUT      (*(RwReg*)0xF0030E00U) /**< \brief (LCDC) Overlay 2 CLUT Register */
#define REG_LCDC_HEOCLUT       (*(RwReg*)0xF0031200U) /**< \brief (LCDC) High End Overlay CLUT Register */
#define REG_LCDC_HCRCLUT       (*(RwReg*)0xF0031600U) /**< \brief (LCDC) Hardware Cursor CLUT Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAMA5_LCDC_INSTANCE_ */
