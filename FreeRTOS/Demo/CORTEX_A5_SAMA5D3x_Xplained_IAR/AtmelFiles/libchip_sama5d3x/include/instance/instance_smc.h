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

#ifndef _SAMA5_SMC_INSTANCE_
#define _SAMA5_SMC_INSTANCE_

/* ========== Register definition for SMC peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
#define REG_SMC_CFG                 (0xFFFFC000U) /**< \brief (SMC) SMC NFC Configuration Register */
#define REG_SMC_CTRL                (0xFFFFC004U) /**< \brief (SMC) SMC NFC Control Register */
#define REG_SMC_SR                  (0xFFFFC008U) /**< \brief (SMC) SMC NFC Status Register */
#define REG_SMC_IER                 (0xFFFFC00CU) /**< \brief (SMC) SMC NFC Interrupt Enable Register */
#define REG_SMC_IDR                 (0xFFFFC010U) /**< \brief (SMC) SMC NFC Interrupt Disable Register */
#define REG_SMC_IMR                 (0xFFFFC014U) /**< \brief (SMC) SMC NFC Interrupt Mask Register */
#define REG_SMC_ADDR                (0xFFFFC018U) /**< \brief (SMC) SMC NFC Address Cycle Zero Register */
#define REG_SMC_BANK                (0xFFFFC01CU) /**< \brief (SMC) SMC Bank Address Register */
#define REG_SMC_ECC_CTRL            (0xFFFFC020U) /**< \brief (SMC) SMC ECC Control Register */
#define REG_SMC_ECC_MD              (0xFFFFC024U) /**< \brief (SMC) SMC ECC Mode Register */
#define REG_SMC_ECC_SR1             (0xFFFFC028U) /**< \brief (SMC) SMC ECC Status 1 Register */
#define REG_SMC_ECC_PR0             (0xFFFFC02CU) /**< \brief (SMC) SMC ECC Parity 0 Register */
#define REG_SMC_ECC_PR1             (0xFFFFC030U) /**< \brief (SMC) SMC ECC parity 1 Register */
#define REG_SMC_ECC_SR2             (0xFFFFC034U) /**< \brief (SMC) SMC ECC status 2 Register */
#define REG_SMC_ECC_PR2             (0xFFFFC038U) /**< \brief (SMC) SMC ECC parity 2 Register */
#define REG_SMC_ECC_PR3             (0xFFFFC03CU) /**< \brief (SMC) SMC ECC parity 3 Register */
#define REG_SMC_ECC_PR4             (0xFFFFC040U) /**< \brief (SMC) SMC ECC parity 4 Register */
#define REG_SMC_ECC_PR5             (0xFFFFC044U) /**< \brief (SMC) SMC ECC parity 5 Register */
#define REG_SMC_ECC_PR6             (0xFFFFC048U) /**< \brief (SMC) SMC ECC parity 6 Register */
#define REG_SMC_ECC_PR7             (0xFFFFC04CU) /**< \brief (SMC) SMC ECC parity 7 Register */
#define REG_SMC_ECC_PR8             (0xFFFFC050U) /**< \brief (SMC) SMC ECC parity 8 Register */
#define REG_SMC_ECC_PR9             (0xFFFFC054U) /**< \brief (SMC) SMC ECC parity 9 Register */
#define REG_SMC_ECC_PR10            (0xFFFFC058U) /**< \brief (SMC) SMC ECC parity 10 Register */
#define REG_SMC_ECC_PR11            (0xFFFFC05CU) /**< \brief (SMC) SMC ECC parity 11 Register */
#define REG_SMC_ECC_PR12            (0xFFFFC060U) /**< \brief (SMC) SMC ECC parity 12 Register */
#define REG_SMC_ECC_PR13            (0xFFFFC064U) /**< \brief (SMC) SMC ECC parity 13 Register */
#define REG_SMC_ECC_PR14            (0xFFFFC068U) /**< \brief (SMC) SMC ECC parity 14 Register */
#define REG_SMC_ECC_PR15            (0xFFFFC06CU) /**< \brief (SMC) SMC ECC parity 15 Register */
#define REG_SMC_PMECCFG             (0xFFFFC070U) /**< \brief (SMC) PMECC Configuration Register */
#define REG_SMC_PMECCSAREA          (0xFFFFC074U) /**< \brief (SMC) PMECC Spare Area Size Register */
#define REG_SMC_PMECCSADDR          (0xFFFFC078U) /**< \brief (SMC) PMECC Start Address Register */
#define REG_SMC_PMECCEADDR          (0xFFFFC07CU) /**< \brief (SMC) PMECC End Address Register */
#define REG_SMC_PMECCTRL            (0xFFFFC084U) /**< \brief (SMC) PMECC Control Register */
#define REG_SMC_PMECCSR             (0xFFFFC088U) /**< \brief (SMC) PMECC Status Register */
#define REG_SMC_PMECCIER            (0xFFFFC08CU) /**< \brief (SMC) PMECC Interrupt Enable register */
#define REG_SMC_PMECCIDR            (0xFFFFC090U) /**< \brief (SMC) PMECC Interrupt Disable Register */
#define REG_SMC_PMECCIMR            (0xFFFFC094U) /**< \brief (SMC) PMECC Interrupt Mask Register */
#define REG_SMC_PMECCISR            (0xFFFFC098U) /**< \brief (SMC) PMECC Interrupt Status Register */
#define REG_SMC_PMECC0_0            (0xFFFFC0B0U) /**< \brief (SMC) PMECC Redundancy 0 Register (sec_num = 0) */
#define REG_SMC_PMECC1_0            (0xFFFFC0B4U) /**< \brief (SMC) PMECC Redundancy 1 Register (sec_num = 0) */
#define REG_SMC_PMECC2_0            (0xFFFFC0B8U) /**< \brief (SMC) PMECC Redundancy 2 Register (sec_num = 0) */
#define REG_SMC_PMECC3_0            (0xFFFFC0BCU) /**< \brief (SMC) PMECC Redundancy 3 Register (sec_num = 0) */
#define REG_SMC_PMECC4_0            (0xFFFFC0C0U) /**< \brief (SMC) PMECC Redundancy 4 Register (sec_num = 0) */
#define REG_SMC_PMECC5_0            (0xFFFFC0C4U) /**< \brief (SMC) PMECC Redundancy 5 Register (sec_num = 0) */
#define REG_SMC_PMECC6_0            (0xFFFFC0C8U) /**< \brief (SMC) PMECC Redundancy 6 Register (sec_num = 0) */
#define REG_SMC_PMECC7_0            (0xFFFFC0CCU) /**< \brief (SMC) PMECC Redundancy 7 Register (sec_num = 0) */
#define REG_SMC_PMECC8_0            (0xFFFFC0D0U) /**< \brief (SMC) PMECC Redundancy 8 Register (sec_num = 0) */
#define REG_SMC_PMECC9_0            (0xFFFFC0D4U) /**< \brief (SMC) PMECC Redundancy 9 Register (sec_num = 0) */
#define REG_SMC_PMECC10_0           (0xFFFFC0D8U) /**< \brief (SMC) PMECC Redundancy 10 Register (sec_num = 0) */
#define REG_SMC_PMECC0_1            (0xFFFFC0F0U) /**< \brief (SMC) PMECC Redundancy 0 Register (sec_num = 1) */
#define REG_SMC_PMECC1_1            (0xFFFFC0F4U) /**< \brief (SMC) PMECC Redundancy 1 Register (sec_num = 1) */
#define REG_SMC_PMECC2_1            (0xFFFFC0F8U) /**< \brief (SMC) PMECC Redundancy 2 Register (sec_num = 1) */
#define REG_SMC_PMECC3_1            (0xFFFFC0FCU) /**< \brief (SMC) PMECC Redundancy 3 Register (sec_num = 1) */
#define REG_SMC_PMECC4_1            (0xFFFFC100U) /**< \brief (SMC) PMECC Redundancy 4 Register (sec_num = 1) */
#define REG_SMC_PMECC5_1            (0xFFFFC104U) /**< \brief (SMC) PMECC Redundancy 5 Register (sec_num = 1) */
#define REG_SMC_PMECC6_1            (0xFFFFC108U) /**< \brief (SMC) PMECC Redundancy 6 Register (sec_num = 1) */
#define REG_SMC_PMECC7_1            (0xFFFFC10CU) /**< \brief (SMC) PMECC Redundancy 7 Register (sec_num = 1) */
#define REG_SMC_PMECC8_1            (0xFFFFC110U) /**< \brief (SMC) PMECC Redundancy 8 Register (sec_num = 1) */
#define REG_SMC_PMECC9_1            (0xFFFFC114U) /**< \brief (SMC) PMECC Redundancy 9 Register (sec_num = 1) */
#define REG_SMC_PMECC10_1           (0xFFFFC118U) /**< \brief (SMC) PMECC Redundancy 10 Register (sec_num = 1) */
#define REG_SMC_PMECC0_2            (0xFFFFC130U) /**< \brief (SMC) PMECC Redundancy 0 Register (sec_num = 2) */
#define REG_SMC_PMECC1_2            (0xFFFFC134U) /**< \brief (SMC) PMECC Redundancy 1 Register (sec_num = 2) */
#define REG_SMC_PMECC2_2            (0xFFFFC138U) /**< \brief (SMC) PMECC Redundancy 2 Register (sec_num = 2) */
#define REG_SMC_PMECC3_2            (0xFFFFC13CU) /**< \brief (SMC) PMECC Redundancy 3 Register (sec_num = 2) */
#define REG_SMC_PMECC4_2            (0xFFFFC140U) /**< \brief (SMC) PMECC Redundancy 4 Register (sec_num = 2) */
#define REG_SMC_PMECC5_2            (0xFFFFC144U) /**< \brief (SMC) PMECC Redundancy 5 Register (sec_num = 2) */
#define REG_SMC_PMECC6_2            (0xFFFFC148U) /**< \brief (SMC) PMECC Redundancy 6 Register (sec_num = 2) */
#define REG_SMC_PMECC7_2            (0xFFFFC14CU) /**< \brief (SMC) PMECC Redundancy 7 Register (sec_num = 2) */
#define REG_SMC_PMECC8_2            (0xFFFFC150U) /**< \brief (SMC) PMECC Redundancy 8 Register (sec_num = 2) */
#define REG_SMC_PMECC9_2            (0xFFFFC154U) /**< \brief (SMC) PMECC Redundancy 9 Register (sec_num = 2) */
#define REG_SMC_PMECC10_2           (0xFFFFC158U) /**< \brief (SMC) PMECC Redundancy 10 Register (sec_num = 2) */
#define REG_SMC_PMECC0_3            (0xFFFFC170U) /**< \brief (SMC) PMECC Redundancy 0 Register (sec_num = 3) */
#define REG_SMC_PMECC1_3            (0xFFFFC174U) /**< \brief (SMC) PMECC Redundancy 1 Register (sec_num = 3) */
#define REG_SMC_PMECC2_3            (0xFFFFC178U) /**< \brief (SMC) PMECC Redundancy 2 Register (sec_num = 3) */
#define REG_SMC_PMECC3_3            (0xFFFFC17CU) /**< \brief (SMC) PMECC Redundancy 3 Register (sec_num = 3) */
#define REG_SMC_PMECC4_3            (0xFFFFC180U) /**< \brief (SMC) PMECC Redundancy 4 Register (sec_num = 3) */
#define REG_SMC_PMECC5_3            (0xFFFFC184U) /**< \brief (SMC) PMECC Redundancy 5 Register (sec_num = 3) */
#define REG_SMC_PMECC6_3            (0xFFFFC188U) /**< \brief (SMC) PMECC Redundancy 6 Register (sec_num = 3) */
#define REG_SMC_PMECC7_3            (0xFFFFC18CU) /**< \brief (SMC) PMECC Redundancy 7 Register (sec_num = 3) */
#define REG_SMC_PMECC8_3            (0xFFFFC190U) /**< \brief (SMC) PMECC Redundancy 8 Register (sec_num = 3) */
#define REG_SMC_PMECC9_3            (0xFFFFC194U) /**< \brief (SMC) PMECC Redundancy 9 Register (sec_num = 3) */
#define REG_SMC_PMECC10_3           (0xFFFFC198U) /**< \brief (SMC) PMECC Redundancy 10 Register (sec_num = 3) */
#define REG_SMC_PMECC0_4            (0xFFFFC1B0U) /**< \brief (SMC) PMECC Redundancy 0 Register (sec_num = 4) */
#define REG_SMC_PMECC1_4            (0xFFFFC1B4U) /**< \brief (SMC) PMECC Redundancy 1 Register (sec_num = 4) */
#define REG_SMC_PMECC2_4            (0xFFFFC1B8U) /**< \brief (SMC) PMECC Redundancy 2 Register (sec_num = 4) */
#define REG_SMC_PMECC3_4            (0xFFFFC1BCU) /**< \brief (SMC) PMECC Redundancy 3 Register (sec_num = 4) */
#define REG_SMC_PMECC4_4            (0xFFFFC1C0U) /**< \brief (SMC) PMECC Redundancy 4 Register (sec_num = 4) */
#define REG_SMC_PMECC5_4            (0xFFFFC1C4U) /**< \brief (SMC) PMECC Redundancy 5 Register (sec_num = 4) */
#define REG_SMC_PMECC6_4            (0xFFFFC1C8U) /**< \brief (SMC) PMECC Redundancy 6 Register (sec_num = 4) */
#define REG_SMC_PMECC7_4            (0xFFFFC1CCU) /**< \brief (SMC) PMECC Redundancy 7 Register (sec_num = 4) */
#define REG_SMC_PMECC8_4            (0xFFFFC1D0U) /**< \brief (SMC) PMECC Redundancy 8 Register (sec_num = 4) */
#define REG_SMC_PMECC9_4            (0xFFFFC1D4U) /**< \brief (SMC) PMECC Redundancy 9 Register (sec_num = 4) */
#define REG_SMC_PMECC10_4           (0xFFFFC1D8U) /**< \brief (SMC) PMECC Redundancy 10 Register (sec_num = 4) */
#define REG_SMC_PMECC0_5            (0xFFFFC1F0U) /**< \brief (SMC) PMECC Redundancy 0 Register (sec_num = 5) */
#define REG_SMC_PMECC1_5            (0xFFFFC1F4U) /**< \brief (SMC) PMECC Redundancy 1 Register (sec_num = 5) */
#define REG_SMC_PMECC2_5            (0xFFFFC1F8U) /**< \brief (SMC) PMECC Redundancy 2 Register (sec_num = 5) */
#define REG_SMC_PMECC3_5            (0xFFFFC1FCU) /**< \brief (SMC) PMECC Redundancy 3 Register (sec_num = 5) */
#define REG_SMC_PMECC4_5            (0xFFFFC200U) /**< \brief (SMC) PMECC Redundancy 4 Register (sec_num = 5) */
#define REG_SMC_PMECC5_5            (0xFFFFC204U) /**< \brief (SMC) PMECC Redundancy 5 Register (sec_num = 5) */
#define REG_SMC_PMECC6_5            (0xFFFFC208U) /**< \brief (SMC) PMECC Redundancy 6 Register (sec_num = 5) */
#define REG_SMC_PMECC7_5            (0xFFFFC20CU) /**< \brief (SMC) PMECC Redundancy 7 Register (sec_num = 5) */
#define REG_SMC_PMECC8_5            (0xFFFFC210U) /**< \brief (SMC) PMECC Redundancy 8 Register (sec_num = 5) */
#define REG_SMC_PMECC9_5            (0xFFFFC214U) /**< \brief (SMC) PMECC Redundancy 9 Register (sec_num = 5) */
#define REG_SMC_PMECC10_5           (0xFFFFC218U) /**< \brief (SMC) PMECC Redundancy 10 Register (sec_num = 5) */
#define REG_SMC_PMECC0_6            (0xFFFFC230U) /**< \brief (SMC) PMECC Redundancy 0 Register (sec_num = 6) */
#define REG_SMC_PMECC1_6            (0xFFFFC234U) /**< \brief (SMC) PMECC Redundancy 1 Register (sec_num = 6) */
#define REG_SMC_PMECC2_6            (0xFFFFC238U) /**< \brief (SMC) PMECC Redundancy 2 Register (sec_num = 6) */
#define REG_SMC_PMECC3_6            (0xFFFFC23CU) /**< \brief (SMC) PMECC Redundancy 3 Register (sec_num = 6) */
#define REG_SMC_PMECC4_6            (0xFFFFC240U) /**< \brief (SMC) PMECC Redundancy 4 Register (sec_num = 6) */
#define REG_SMC_PMECC5_6            (0xFFFFC244U) /**< \brief (SMC) PMECC Redundancy 5 Register (sec_num = 6) */
#define REG_SMC_PMECC6_6            (0xFFFFC248U) /**< \brief (SMC) PMECC Redundancy 6 Register (sec_num = 6) */
#define REG_SMC_PMECC7_6            (0xFFFFC24CU) /**< \brief (SMC) PMECC Redundancy 7 Register (sec_num = 6) */
#define REG_SMC_PMECC8_6            (0xFFFFC250U) /**< \brief (SMC) PMECC Redundancy 8 Register (sec_num = 6) */
#define REG_SMC_PMECC9_6            (0xFFFFC254U) /**< \brief (SMC) PMECC Redundancy 9 Register (sec_num = 6) */
#define REG_SMC_PMECC10_6           (0xFFFFC258U) /**< \brief (SMC) PMECC Redundancy 10 Register (sec_num = 6) */
#define REG_SMC_PMECC0_7            (0xFFFFC270U) /**< \brief (SMC) PMECC Redundancy 0 Register (sec_num = 7) */
#define REG_SMC_PMECC1_7            (0xFFFFC274U) /**< \brief (SMC) PMECC Redundancy 1 Register (sec_num = 7) */
#define REG_SMC_PMECC2_7            (0xFFFFC278U) /**< \brief (SMC) PMECC Redundancy 2 Register (sec_num = 7) */
#define REG_SMC_PMECC3_7            (0xFFFFC27CU) /**< \brief (SMC) PMECC Redundancy 3 Register (sec_num = 7) */
#define REG_SMC_PMECC4_7            (0xFFFFC280U) /**< \brief (SMC) PMECC Redundancy 4 Register (sec_num = 7) */
#define REG_SMC_PMECC5_7            (0xFFFFC284U) /**< \brief (SMC) PMECC Redundancy 5 Register (sec_num = 7) */
#define REG_SMC_PMECC6_7            (0xFFFFC288U) /**< \brief (SMC) PMECC Redundancy 6 Register (sec_num = 7) */
#define REG_SMC_PMECC7_7            (0xFFFFC28CU) /**< \brief (SMC) PMECC Redundancy 7 Register (sec_num = 7) */
#define REG_SMC_PMECC8_7            (0xFFFFC290U) /**< \brief (SMC) PMECC Redundancy 8 Register (sec_num = 7) */
#define REG_SMC_PMECC9_7            (0xFFFFC294U) /**< \brief (SMC) PMECC Redundancy 9 Register (sec_num = 7) */
#define REG_SMC_PMECC10_7           (0xFFFFC298U) /**< \brief (SMC) PMECC Redundancy 10 Register (sec_num = 7) */
#define REG_SMC_REM0_0              (0xFFFFC2B0U) /**< \brief (SMC) PMECC Remainder 0 Register (sec_num = 0) */
#define REG_SMC_REM1_0              (0xFFFFC2B4U) /**< \brief (SMC) PMECC Remainder 1 Register (sec_num = 0) */
#define REG_SMC_REM2_0              (0xFFFFC2B8U) /**< \brief (SMC) PMECC Remainder 2 Register (sec_num = 0) */
#define REG_SMC_REM3_0              (0xFFFFC2BCU) /**< \brief (SMC) PMECC Remainder 3 Register (sec_num = 0) */
#define REG_SMC_REM4_0              (0xFFFFC2C0U) /**< \brief (SMC) PMECC Remainder 4 Register (sec_num = 0) */
#define REG_SMC_REM5_0              (0xFFFFC2C4U) /**< \brief (SMC) PMECC Remainder 5 Register (sec_num = 0) */
#define REG_SMC_REM6_0              (0xFFFFC2C8U) /**< \brief (SMC) PMECC Remainder 6 Register (sec_num = 0) */
#define REG_SMC_REM7_0              (0xFFFFC2CCU) /**< \brief (SMC) PMECC Remainder 7 Register (sec_num = 0) */
#define REG_SMC_REM8_0              (0xFFFFC2D0U) /**< \brief (SMC) PMECC Remainder 8 Register (sec_num = 0) */
#define REG_SMC_REM9_0              (0xFFFFC2D4U) /**< \brief (SMC) PMECC Remainder 9 Register (sec_num = 0) */
#define REG_SMC_REM10_0             (0xFFFFC2D8U) /**< \brief (SMC) PMECC Remainder 10 Register (sec_num = 0) */
#define REG_SMC_REM11_0             (0xFFFFC2DCU) /**< \brief (SMC) PMECC Remainder 11 Register (sec_num = 0) */
#define REG_SMC_REM0_1              (0xFFFFC2F0U) /**< \brief (SMC) PMECC Remainder 0 Register (sec_num = 1) */
#define REG_SMC_REM1_1              (0xFFFFC2F4U) /**< \brief (SMC) PMECC Remainder 1 Register (sec_num = 1) */
#define REG_SMC_REM2_1              (0xFFFFC2F8U) /**< \brief (SMC) PMECC Remainder 2 Register (sec_num = 1) */
#define REG_SMC_REM3_1              (0xFFFFC2FCU) /**< \brief (SMC) PMECC Remainder 3 Register (sec_num = 1) */
#define REG_SMC_REM4_1              (0xFFFFC300U) /**< \brief (SMC) PMECC Remainder 4 Register (sec_num = 1) */
#define REG_SMC_REM5_1              (0xFFFFC304U) /**< \brief (SMC) PMECC Remainder 5 Register (sec_num = 1) */
#define REG_SMC_REM6_1              (0xFFFFC308U) /**< \brief (SMC) PMECC Remainder 6 Register (sec_num = 1) */
#define REG_SMC_REM7_1              (0xFFFFC30CU) /**< \brief (SMC) PMECC Remainder 7 Register (sec_num = 1) */
#define REG_SMC_REM8_1              (0xFFFFC310U) /**< \brief (SMC) PMECC Remainder 8 Register (sec_num = 1) */
#define REG_SMC_REM9_1              (0xFFFFC314U) /**< \brief (SMC) PMECC Remainder 9 Register (sec_num = 1) */
#define REG_SMC_REM10_1             (0xFFFFC318U) /**< \brief (SMC) PMECC Remainder 10 Register (sec_num = 1) */
#define REG_SMC_REM11_1             (0xFFFFC31CU) /**< \brief (SMC) PMECC Remainder 11 Register (sec_num = 1) */
#define REG_SMC_REM0_2              (0xFFFFC330U) /**< \brief (SMC) PMECC Remainder 0 Register (sec_num = 2) */
#define REG_SMC_REM1_2              (0xFFFFC334U) /**< \brief (SMC) PMECC Remainder 1 Register (sec_num = 2) */
#define REG_SMC_REM2_2              (0xFFFFC338U) /**< \brief (SMC) PMECC Remainder 2 Register (sec_num = 2) */
#define REG_SMC_REM3_2              (0xFFFFC33CU) /**< \brief (SMC) PMECC Remainder 3 Register (sec_num = 2) */
#define REG_SMC_REM4_2              (0xFFFFC340U) /**< \brief (SMC) PMECC Remainder 4 Register (sec_num = 2) */
#define REG_SMC_REM5_2              (0xFFFFC344U) /**< \brief (SMC) PMECC Remainder 5 Register (sec_num = 2) */
#define REG_SMC_REM6_2              (0xFFFFC348U) /**< \brief (SMC) PMECC Remainder 6 Register (sec_num = 2) */
#define REG_SMC_REM7_2              (0xFFFFC34CU) /**< \brief (SMC) PMECC Remainder 7 Register (sec_num = 2) */
#define REG_SMC_REM8_2              (0xFFFFC350U) /**< \brief (SMC) PMECC Remainder 8 Register (sec_num = 2) */
#define REG_SMC_REM9_2              (0xFFFFC354U) /**< \brief (SMC) PMECC Remainder 9 Register (sec_num = 2) */
#define REG_SMC_REM10_2             (0xFFFFC358U) /**< \brief (SMC) PMECC Remainder 10 Register (sec_num = 2) */
#define REG_SMC_REM11_2             (0xFFFFC35CU) /**< \brief (SMC) PMECC Remainder 11 Register (sec_num = 2) */
#define REG_SMC_REM0_3              (0xFFFFC370U) /**< \brief (SMC) PMECC Remainder 0 Register (sec_num = 3) */
#define REG_SMC_REM1_3              (0xFFFFC374U) /**< \brief (SMC) PMECC Remainder 1 Register (sec_num = 3) */
#define REG_SMC_REM2_3              (0xFFFFC378U) /**< \brief (SMC) PMECC Remainder 2 Register (sec_num = 3) */
#define REG_SMC_REM3_3              (0xFFFFC37CU) /**< \brief (SMC) PMECC Remainder 3 Register (sec_num = 3) */
#define REG_SMC_REM4_3              (0xFFFFC380U) /**< \brief (SMC) PMECC Remainder 4 Register (sec_num = 3) */
#define REG_SMC_REM5_3              (0xFFFFC384U) /**< \brief (SMC) PMECC Remainder 5 Register (sec_num = 3) */
#define REG_SMC_REM6_3              (0xFFFFC388U) /**< \brief (SMC) PMECC Remainder 6 Register (sec_num = 3) */
#define REG_SMC_REM7_3              (0xFFFFC38CU) /**< \brief (SMC) PMECC Remainder 7 Register (sec_num = 3) */
#define REG_SMC_REM8_3              (0xFFFFC390U) /**< \brief (SMC) PMECC Remainder 8 Register (sec_num = 3) */
#define REG_SMC_REM9_3              (0xFFFFC394U) /**< \brief (SMC) PMECC Remainder 9 Register (sec_num = 3) */
#define REG_SMC_REM10_3             (0xFFFFC398U) /**< \brief (SMC) PMECC Remainder 10 Register (sec_num = 3) */
#define REG_SMC_REM11_3             (0xFFFFC39CU) /**< \brief (SMC) PMECC Remainder 11 Register (sec_num = 3) */
#define REG_SMC_REM0_4              (0xFFFFC3B0U) /**< \brief (SMC) PMECC Remainder 0 Register (sec_num = 4) */
#define REG_SMC_REM1_4              (0xFFFFC3B4U) /**< \brief (SMC) PMECC Remainder 1 Register (sec_num = 4) */
#define REG_SMC_REM2_4              (0xFFFFC3B8U) /**< \brief (SMC) PMECC Remainder 2 Register (sec_num = 4) */
#define REG_SMC_REM3_4              (0xFFFFC3BCU) /**< \brief (SMC) PMECC Remainder 3 Register (sec_num = 4) */
#define REG_SMC_REM4_4              (0xFFFFC3C0U) /**< \brief (SMC) PMECC Remainder 4 Register (sec_num = 4) */
#define REG_SMC_REM5_4              (0xFFFFC3C4U) /**< \brief (SMC) PMECC Remainder 5 Register (sec_num = 4) */
#define REG_SMC_REM6_4              (0xFFFFC3C8U) /**< \brief (SMC) PMECC Remainder 6 Register (sec_num = 4) */
#define REG_SMC_REM7_4              (0xFFFFC3CCU) /**< \brief (SMC) PMECC Remainder 7 Register (sec_num = 4) */
#define REG_SMC_REM8_4              (0xFFFFC3D0U) /**< \brief (SMC) PMECC Remainder 8 Register (sec_num = 4) */
#define REG_SMC_REM9_4              (0xFFFFC3D4U) /**< \brief (SMC) PMECC Remainder 9 Register (sec_num = 4) */
#define REG_SMC_REM10_4             (0xFFFFC3D8U) /**< \brief (SMC) PMECC Remainder 10 Register (sec_num = 4) */
#define REG_SMC_REM11_4             (0xFFFFC3DCU) /**< \brief (SMC) PMECC Remainder 11 Register (sec_num = 4) */
#define REG_SMC_REM0_5              (0xFFFFC3F0U) /**< \brief (SMC) PMECC Remainder 0 Register (sec_num = 5) */
#define REG_SMC_REM1_5              (0xFFFFC3F4U) /**< \brief (SMC) PMECC Remainder 1 Register (sec_num = 5) */
#define REG_SMC_REM2_5              (0xFFFFC3F8U) /**< \brief (SMC) PMECC Remainder 2 Register (sec_num = 5) */
#define REG_SMC_REM3_5              (0xFFFFC3FCU) /**< \brief (SMC) PMECC Remainder 3 Register (sec_num = 5) */
#define REG_SMC_REM4_5              (0xFFFFC400U) /**< \brief (SMC) PMECC Remainder 4 Register (sec_num = 5) */
#define REG_SMC_REM5_5              (0xFFFFC404U) /**< \brief (SMC) PMECC Remainder 5 Register (sec_num = 5) */
#define REG_SMC_REM6_5              (0xFFFFC408U) /**< \brief (SMC) PMECC Remainder 6 Register (sec_num = 5) */
#define REG_SMC_REM7_5              (0xFFFFC40CU) /**< \brief (SMC) PMECC Remainder 7 Register (sec_num = 5) */
#define REG_SMC_REM8_5              (0xFFFFC410U) /**< \brief (SMC) PMECC Remainder 8 Register (sec_num = 5) */
#define REG_SMC_REM9_5              (0xFFFFC414U) /**< \brief (SMC) PMECC Remainder 9 Register (sec_num = 5) */
#define REG_SMC_REM10_5             (0xFFFFC418U) /**< \brief (SMC) PMECC Remainder 10 Register (sec_num = 5) */
#define REG_SMC_REM11_5             (0xFFFFC41CU) /**< \brief (SMC) PMECC Remainder 11 Register (sec_num = 5) */
#define REG_SMC_REM0_6              (0xFFFFC430U) /**< \brief (SMC) PMECC Remainder 0 Register (sec_num = 6) */
#define REG_SMC_REM1_6              (0xFFFFC434U) /**< \brief (SMC) PMECC Remainder 1 Register (sec_num = 6) */
#define REG_SMC_REM2_6              (0xFFFFC438U) /**< \brief (SMC) PMECC Remainder 2 Register (sec_num = 6) */
#define REG_SMC_REM3_6              (0xFFFFC43CU) /**< \brief (SMC) PMECC Remainder 3 Register (sec_num = 6) */
#define REG_SMC_REM4_6              (0xFFFFC440U) /**< \brief (SMC) PMECC Remainder 4 Register (sec_num = 6) */
#define REG_SMC_REM5_6              (0xFFFFC444U) /**< \brief (SMC) PMECC Remainder 5 Register (sec_num = 6) */
#define REG_SMC_REM6_6              (0xFFFFC448U) /**< \brief (SMC) PMECC Remainder 6 Register (sec_num = 6) */
#define REG_SMC_REM7_6              (0xFFFFC44CU) /**< \brief (SMC) PMECC Remainder 7 Register (sec_num = 6) */
#define REG_SMC_REM8_6              (0xFFFFC450U) /**< \brief (SMC) PMECC Remainder 8 Register (sec_num = 6) */
#define REG_SMC_REM9_6              (0xFFFFC454U) /**< \brief (SMC) PMECC Remainder 9 Register (sec_num = 6) */
#define REG_SMC_REM10_6             (0xFFFFC458U) /**< \brief (SMC) PMECC Remainder 10 Register (sec_num = 6) */
#define REG_SMC_REM11_6             (0xFFFFC45CU) /**< \brief (SMC) PMECC Remainder 11 Register (sec_num = 6) */
#define REG_SMC_REM0_7              (0xFFFFC470U) /**< \brief (SMC) PMECC Remainder 0 Register (sec_num = 7) */
#define REG_SMC_REM1_7              (0xFFFFC474U) /**< \brief (SMC) PMECC Remainder 1 Register (sec_num = 7) */
#define REG_SMC_REM2_7              (0xFFFFC478U) /**< \brief (SMC) PMECC Remainder 2 Register (sec_num = 7) */
#define REG_SMC_REM3_7              (0xFFFFC47CU) /**< \brief (SMC) PMECC Remainder 3 Register (sec_num = 7) */
#define REG_SMC_REM4_7              (0xFFFFC480U) /**< \brief (SMC) PMECC Remainder 4 Register (sec_num = 7) */
#define REG_SMC_REM5_7              (0xFFFFC484U) /**< \brief (SMC) PMECC Remainder 5 Register (sec_num = 7) */
#define REG_SMC_REM6_7              (0xFFFFC488U) /**< \brief (SMC) PMECC Remainder 6 Register (sec_num = 7) */
#define REG_SMC_REM7_7              (0xFFFFC48CU) /**< \brief (SMC) PMECC Remainder 7 Register (sec_num = 7) */
#define REG_SMC_REM8_7              (0xFFFFC490U) /**< \brief (SMC) PMECC Remainder 8 Register (sec_num = 7) */
#define REG_SMC_REM9_7              (0xFFFFC494U) /**< \brief (SMC) PMECC Remainder 9 Register (sec_num = 7) */
#define REG_SMC_REM10_7             (0xFFFFC498U) /**< \brief (SMC) PMECC Remainder 10 Register (sec_num = 7) */
#define REG_SMC_REM11_7             (0xFFFFC49CU) /**< \brief (SMC) PMECC Remainder 11 Register (sec_num = 7) */
#define REG_SMC_ELCFG               (0xFFFFC500U) /**< \brief (SMC) PMECC Error Location Configuration Register */
#define REG_SMC_ELPRIM              (0xFFFFC504U) /**< \brief (SMC) PMECC Error Location Primitive Register */
#define REG_SMC_ELEN                (0xFFFFC508U) /**< \brief (SMC) PMECC Error Location Enable Register */
#define REG_SMC_ELDIS               (0xFFFFC50CU) /**< \brief (SMC) PMECC Error Location Disable Register */
#define REG_SMC_ELSR                (0xFFFFC510U) /**< \brief (SMC) PMECC Error Location Status Register */
#define REG_SMC_ELIER               (0xFFFFC514U) /**< \brief (SMC) PMECC Error Location Interrupt Enable register */
#define REG_SMC_ELIDR               (0xFFFFC518U) /**< \brief (SMC) PMECC Error Location Interrupt Disable Register */
#define REG_SMC_ELIMR               (0xFFFFC51CU) /**< \brief (SMC) PMECC Error Location Interrupt Mask Register */
#define REG_SMC_ELISR               (0xFFFFC520U) /**< \brief (SMC) PMECC Error Location Interrupt Status Register */
#define REG_SMC_SIGMA0              (0xFFFFC528U) /**< \brief (SMC) PMECC Error Location SIGMA 0 Register */
#define REG_SMC_SIGMA1              (0xFFFFC52CU) /**< \brief (SMC) PMECC Error Location SIGMA 1 Register */
#define REG_SMC_SIGMA2              (0xFFFFC530U) /**< \brief (SMC) PMECC Error Location SIGMA 2 Register */
#define REG_SMC_SIGMA3              (0xFFFFC534U) /**< \brief (SMC) PMECC Error Location SIGMA 3 Register */
#define REG_SMC_SIGMA4              (0xFFFFC538U) /**< \brief (SMC) PMECC Error Location SIGMA 4 Register */
#define REG_SMC_SIGMA5              (0xFFFFC53CU) /**< \brief (SMC) PMECC Error Location SIGMA 5 Register */
#define REG_SMC_SIGMA6              (0xFFFFC540U) /**< \brief (SMC) PMECC Error Location SIGMA 6 Register */
#define REG_SMC_SIGMA7              (0xFFFFC544U) /**< \brief (SMC) PMECC Error Location SIGMA 7 Register */
#define REG_SMC_SIGMA8              (0xFFFFC548U) /**< \brief (SMC) PMECC Error Location SIGMA 8 Register */
#define REG_SMC_SIGMA9              (0xFFFFC54CU) /**< \brief (SMC) PMECC Error Location SIGMA 9 Register */
#define REG_SMC_SIGMA10             (0xFFFFC550U) /**< \brief (SMC) PMECC Error Location SIGMA 10 Register */
#define REG_SMC_SIGMA11             (0xFFFFC554U) /**< \brief (SMC) PMECC Error Location SIGMA 11 Register */
#define REG_SMC_SIGMA12             (0xFFFFC558U) /**< \brief (SMC) PMECC Error Location SIGMA 12 Register */
#define REG_SMC_SIGMA13             (0xFFFFC55CU) /**< \brief (SMC) PMECC Error Location SIGMA 13 Register */
#define REG_SMC_SIGMA14             (0xFFFFC560U) /**< \brief (SMC) PMECC Error Location SIGMA 14 Register */
#define REG_SMC_SIGMA15             (0xFFFFC564U) /**< \brief (SMC) PMECC Error Location SIGMA 15 Register */
#define REG_SMC_SIGMA16             (0xFFFFC568U) /**< \brief (SMC) PMECC Error Location SIGMA 16 Register */
#define REG_SMC_SIGMA17             (0xFFFFC56CU) /**< \brief (SMC) PMECC Error Location SIGMA 17 Register */
#define REG_SMC_SIGMA18             (0xFFFFC570U) /**< \brief (SMC) PMECC Error Location SIGMA 18 Register */
#define REG_SMC_SIGMA19             (0xFFFFC574U) /**< \brief (SMC) PMECC Error Location SIGMA 19 Register */
#define REG_SMC_SIGMA20             (0xFFFFC578U) /**< \brief (SMC) PMECC Error Location SIGMA 20 Register */
#define REG_SMC_SIGMA21             (0xFFFFC57CU) /**< \brief (SMC) PMECC Error Location SIGMA 21 Register */
#define REG_SMC_SIGMA22             (0xFFFFC580U) /**< \brief (SMC) PMECC Error Location SIGMA 22 Register */
#define REG_SMC_SIGMA23             (0xFFFFC584U) /**< \brief (SMC) PMECC Error Location SIGMA 23 Register */
#define REG_SMC_SIGMA24             (0xFFFFC588U) /**< \brief (SMC) PMECC Error Location SIGMA 24 Register */
#define REG_SMC_ERRLOC              (0xFFFFC58CU) /**< \brief (SMC) PMECC Error Location 0 Register */
#define REG_SMC_SETUP0              (0xFFFFC600U) /**< \brief (SMC) SMC Setup Register (CS_number = 0) */
#define REG_SMC_PULSE0              (0xFFFFC604U) /**< \brief (SMC) SMC Pulse Register (CS_number = 0) */
#define REG_SMC_CYCLE0              (0xFFFFC608U) /**< \brief (SMC) SMC Cycle Register (CS_number = 0) */
#define REG_SMC_TIMINGS0            (0xFFFFC60CU) /**< \brief (SMC) SMC Timings Register (CS_number = 0) */
#define REG_SMC_MODE0               (0xFFFFC610U) /**< \brief (SMC) SMC Mode Register (CS_number = 0) */
#define REG_SMC_SETUP1              (0xFFFFC614U) /**< \brief (SMC) SMC Setup Register (CS_number = 1) */
#define REG_SMC_PULSE1              (0xFFFFC618U) /**< \brief (SMC) SMC Pulse Register (CS_number = 1) */
#define REG_SMC_CYCLE1              (0xFFFFC61CU) /**< \brief (SMC) SMC Cycle Register (CS_number = 1) */
#define REG_SMC_TIMINGS1            (0xFFFFC620U) /**< \brief (SMC) SMC Timings Register (CS_number = 1) */
#define REG_SMC_MODE1               (0xFFFFC624U) /**< \brief (SMC) SMC Mode Register (CS_number = 1) */
#define REG_SMC_SETUP2              (0xFFFFC628U) /**< \brief (SMC) SMC Setup Register (CS_number = 2) */
#define REG_SMC_PULSE2              (0xFFFFC62CU) /**< \brief (SMC) SMC Pulse Register (CS_number = 2) */
#define REG_SMC_CYCLE2              (0xFFFFC630U) /**< \brief (SMC) SMC Cycle Register (CS_number = 2) */
#define REG_SMC_TIMINGS2            (0xFFFFC634U) /**< \brief (SMC) SMC Timings Register (CS_number = 2) */
#define REG_SMC_MODE2               (0xFFFFC638U) /**< \brief (SMC) SMC Mode Register (CS_number = 2) */
#define REG_SMC_SETUP3              (0xFFFFC63CU) /**< \brief (SMC) SMC Setup Register (CS_number = 3) */
#define REG_SMC_PULSE3              (0xFFFFC640U) /**< \brief (SMC) SMC Pulse Register (CS_number = 3) */
#define REG_SMC_CYCLE3              (0xFFFFC644U) /**< \brief (SMC) SMC Cycle Register (CS_number = 3) */
#define REG_SMC_TIMINGS3            (0xFFFFC648U) /**< \brief (SMC) SMC Timings Register (CS_number = 3) */
#define REG_SMC_MODE3               (0xFFFFC64CU) /**< \brief (SMC) SMC Mode Register (CS_number = 3) */
#define REG_SMC_OCMS                (0xFFFFC6A0U) /**< \brief (SMC) SMC OCMS Register */
#define REG_SMC_KEY1                (0xFFFFC6A4U) /**< \brief (SMC) SMC OCMS KEY1 Register */
#define REG_SMC_KEY2                (0xFFFFC6A8U) /**< \brief (SMC) SMC OCMS KEY2 Register */
#define REG_SMC_WPCR                (0xFFFFC6E4U) /**< \brief (SMC) SMC Write Protection Control Register */
#define REG_SMC_WPSR                (0xFFFFC6E8U) /**< \brief (SMC) SMC Write Protection Status Register */
#else
#define REG_SMC_CFG        (*(RwReg*)0xFFFFC000U) /**< \brief (SMC) SMC NFC Configuration Register */
#define REG_SMC_CTRL       (*(WoReg*)0xFFFFC004U) /**< \brief (SMC) SMC NFC Control Register */
#define REG_SMC_SR         (*(RoReg*)0xFFFFC008U) /**< \brief (SMC) SMC NFC Status Register */
#define REG_SMC_IER        (*(WoReg*)0xFFFFC00CU) /**< \brief (SMC) SMC NFC Interrupt Enable Register */
#define REG_SMC_IDR        (*(WoReg*)0xFFFFC010U) /**< \brief (SMC) SMC NFC Interrupt Disable Register */
#define REG_SMC_IMR        (*(RoReg*)0xFFFFC014U) /**< \brief (SMC) SMC NFC Interrupt Mask Register */
#define REG_SMC_ADDR       (*(RwReg*)0xFFFFC018U) /**< \brief (SMC) SMC NFC Address Cycle Zero Register */
#define REG_SMC_BANK       (*(RwReg*)0xFFFFC01CU) /**< \brief (SMC) SMC Bank Address Register */
#define REG_SMC_ECC_CTRL   (*(WoReg*)0xFFFFC020U) /**< \brief (SMC) SMC ECC Control Register */
#define REG_SMC_ECC_MD     (*(RwReg*)0xFFFFC024U) /**< \brief (SMC) SMC ECC Mode Register */
#define REG_SMC_ECC_SR1    (*(RoReg*)0xFFFFC028U) /**< \brief (SMC) SMC ECC Status 1 Register */
#define REG_SMC_ECC_PR0    (*(RoReg*)0xFFFFC02CU) /**< \brief (SMC) SMC ECC Parity 0 Register */
#define REG_SMC_ECC_PR1    (*(RoReg*)0xFFFFC030U) /**< \brief (SMC) SMC ECC parity 1 Register */
#define REG_SMC_ECC_SR2    (*(RoReg*)0xFFFFC034U) /**< \brief (SMC) SMC ECC status 2 Register */
#define REG_SMC_ECC_PR2    (*(RoReg*)0xFFFFC038U) /**< \brief (SMC) SMC ECC parity 2 Register */
#define REG_SMC_ECC_PR3    (*(RoReg*)0xFFFFC03CU) /**< \brief (SMC) SMC ECC parity 3 Register */
#define REG_SMC_ECC_PR4    (*(RoReg*)0xFFFFC040U) /**< \brief (SMC) SMC ECC parity 4 Register */
#define REG_SMC_ECC_PR5    (*(RoReg*)0xFFFFC044U) /**< \brief (SMC) SMC ECC parity 5 Register */
#define REG_SMC_ECC_PR6    (*(RoReg*)0xFFFFC048U) /**< \brief (SMC) SMC ECC parity 6 Register */
#define REG_SMC_ECC_PR7    (*(RoReg*)0xFFFFC04CU) /**< \brief (SMC) SMC ECC parity 7 Register */
#define REG_SMC_ECC_PR8    (*(RoReg*)0xFFFFC050U) /**< \brief (SMC) SMC ECC parity 8 Register */
#define REG_SMC_ECC_PR9    (*(RoReg*)0xFFFFC054U) /**< \brief (SMC) SMC ECC parity 9 Register */
#define REG_SMC_ECC_PR10   (*(RoReg*)0xFFFFC058U) /**< \brief (SMC) SMC ECC parity 10 Register */
#define REG_SMC_ECC_PR11   (*(RoReg*)0xFFFFC05CU) /**< \brief (SMC) SMC ECC parity 11 Register */
#define REG_SMC_ECC_PR12   (*(RoReg*)0xFFFFC060U) /**< \brief (SMC) SMC ECC parity 12 Register */
#define REG_SMC_ECC_PR13   (*(RoReg*)0xFFFFC064U) /**< \brief (SMC) SMC ECC parity 13 Register */
#define REG_SMC_ECC_PR14   (*(RoReg*)0xFFFFC068U) /**< \brief (SMC) SMC ECC parity 14 Register */
#define REG_SMC_ECC_PR15   (*(RoReg*)0xFFFFC06CU) /**< \brief (SMC) SMC ECC parity 15 Register */
#define REG_SMC_PMECCFG    (*(RwReg*)0xFFFFC070U) /**< \brief (SMC) PMECC Configuration Register */
#define REG_SMC_PMECCSAREA (*(RwReg*)0xFFFFC074U) /**< \brief (SMC) PMECC Spare Area Size Register */
#define REG_SMC_PMECCSADDR (*(RwReg*)0xFFFFC078U) /**< \brief (SMC) PMECC Start Address Register */
#define REG_SMC_PMECCEADDR (*(RwReg*)0xFFFFC07CU) /**< \brief (SMC) PMECC End Address Register */
#define REG_SMC_PMECCTRL   (*(WoReg*)0xFFFFC084U) /**< \brief (SMC) PMECC Control Register */
#define REG_SMC_PMECCSR    (*(RoReg*)0xFFFFC088U) /**< \brief (SMC) PMECC Status Register */
#define REG_SMC_PMECCIER   (*(WoReg*)0xFFFFC08CU) /**< \brief (SMC) PMECC Interrupt Enable register */
#define REG_SMC_PMECCIDR   (*(WoReg*)0xFFFFC090U) /**< \brief (SMC) PMECC Interrupt Disable Register */
#define REG_SMC_PMECCIMR   (*(RoReg*)0xFFFFC094U) /**< \brief (SMC) PMECC Interrupt Mask Register */
#define REG_SMC_PMECCISR   (*(RoReg*)0xFFFFC098U) /**< \brief (SMC) PMECC Interrupt Status Register */
#define REG_SMC_PMECC0_0   (*(RoReg*)0xFFFFC0B0U) /**< \brief (SMC) PMECC Redundancy 0 Register (sec_num = 0) */
#define REG_SMC_PMECC1_0   (*(RoReg*)0xFFFFC0B4U) /**< \brief (SMC) PMECC Redundancy 1 Register (sec_num = 0) */
#define REG_SMC_PMECC2_0   (*(RoReg*)0xFFFFC0B8U) /**< \brief (SMC) PMECC Redundancy 2 Register (sec_num = 0) */
#define REG_SMC_PMECC3_0   (*(RoReg*)0xFFFFC0BCU) /**< \brief (SMC) PMECC Redundancy 3 Register (sec_num = 0) */
#define REG_SMC_PMECC4_0   (*(RoReg*)0xFFFFC0C0U) /**< \brief (SMC) PMECC Redundancy 4 Register (sec_num = 0) */
#define REG_SMC_PMECC5_0   (*(RoReg*)0xFFFFC0C4U) /**< \brief (SMC) PMECC Redundancy 5 Register (sec_num = 0) */
#define REG_SMC_PMECC6_0   (*(RoReg*)0xFFFFC0C8U) /**< \brief (SMC) PMECC Redundancy 6 Register (sec_num = 0) */
#define REG_SMC_PMECC7_0   (*(RoReg*)0xFFFFC0CCU) /**< \brief (SMC) PMECC Redundancy 7 Register (sec_num = 0) */
#define REG_SMC_PMECC8_0   (*(RoReg*)0xFFFFC0D0U) /**< \brief (SMC) PMECC Redundancy 8 Register (sec_num = 0) */
#define REG_SMC_PMECC9_0   (*(RoReg*)0xFFFFC0D4U) /**< \brief (SMC) PMECC Redundancy 9 Register (sec_num = 0) */
#define REG_SMC_PMECC10_0  (*(RoReg*)0xFFFFC0D8U) /**< \brief (SMC) PMECC Redundancy 10 Register (sec_num = 0) */
#define REG_SMC_PMECC0_1   (*(RoReg*)0xFFFFC0F0U) /**< \brief (SMC) PMECC Redundancy 0 Register (sec_num = 1) */
#define REG_SMC_PMECC1_1   (*(RoReg*)0xFFFFC0F4U) /**< \brief (SMC) PMECC Redundancy 1 Register (sec_num = 1) */
#define REG_SMC_PMECC2_1   (*(RoReg*)0xFFFFC0F8U) /**< \brief (SMC) PMECC Redundancy 2 Register (sec_num = 1) */
#define REG_SMC_PMECC3_1   (*(RoReg*)0xFFFFC0FCU) /**< \brief (SMC) PMECC Redundancy 3 Register (sec_num = 1) */
#define REG_SMC_PMECC4_1   (*(RoReg*)0xFFFFC100U) /**< \brief (SMC) PMECC Redundancy 4 Register (sec_num = 1) */
#define REG_SMC_PMECC5_1   (*(RoReg*)0xFFFFC104U) /**< \brief (SMC) PMECC Redundancy 5 Register (sec_num = 1) */
#define REG_SMC_PMECC6_1   (*(RoReg*)0xFFFFC108U) /**< \brief (SMC) PMECC Redundancy 6 Register (sec_num = 1) */
#define REG_SMC_PMECC7_1   (*(RoReg*)0xFFFFC10CU) /**< \brief (SMC) PMECC Redundancy 7 Register (sec_num = 1) */
#define REG_SMC_PMECC8_1   (*(RoReg*)0xFFFFC110U) /**< \brief (SMC) PMECC Redundancy 8 Register (sec_num = 1) */
#define REG_SMC_PMECC9_1   (*(RoReg*)0xFFFFC114U) /**< \brief (SMC) PMECC Redundancy 9 Register (sec_num = 1) */
#define REG_SMC_PMECC10_1  (*(RoReg*)0xFFFFC118U) /**< \brief (SMC) PMECC Redundancy 10 Register (sec_num = 1) */
#define REG_SMC_PMECC0_2   (*(RoReg*)0xFFFFC130U) /**< \brief (SMC) PMECC Redundancy 0 Register (sec_num = 2) */
#define REG_SMC_PMECC1_2   (*(RoReg*)0xFFFFC134U) /**< \brief (SMC) PMECC Redundancy 1 Register (sec_num = 2) */
#define REG_SMC_PMECC2_2   (*(RoReg*)0xFFFFC138U) /**< \brief (SMC) PMECC Redundancy 2 Register (sec_num = 2) */
#define REG_SMC_PMECC3_2   (*(RoReg*)0xFFFFC13CU) /**< \brief (SMC) PMECC Redundancy 3 Register (sec_num = 2) */
#define REG_SMC_PMECC4_2   (*(RoReg*)0xFFFFC140U) /**< \brief (SMC) PMECC Redundancy 4 Register (sec_num = 2) */
#define REG_SMC_PMECC5_2   (*(RoReg*)0xFFFFC144U) /**< \brief (SMC) PMECC Redundancy 5 Register (sec_num = 2) */
#define REG_SMC_PMECC6_2   (*(RoReg*)0xFFFFC148U) /**< \brief (SMC) PMECC Redundancy 6 Register (sec_num = 2) */
#define REG_SMC_PMECC7_2   (*(RoReg*)0xFFFFC14CU) /**< \brief (SMC) PMECC Redundancy 7 Register (sec_num = 2) */
#define REG_SMC_PMECC8_2   (*(RoReg*)0xFFFFC150U) /**< \brief (SMC) PMECC Redundancy 8 Register (sec_num = 2) */
#define REG_SMC_PMECC9_2   (*(RoReg*)0xFFFFC154U) /**< \brief (SMC) PMECC Redundancy 9 Register (sec_num = 2) */
#define REG_SMC_PMECC10_2  (*(RoReg*)0xFFFFC158U) /**< \brief (SMC) PMECC Redundancy 10 Register (sec_num = 2) */
#define REG_SMC_PMECC0_3   (*(RoReg*)0xFFFFC170U) /**< \brief (SMC) PMECC Redundancy 0 Register (sec_num = 3) */
#define REG_SMC_PMECC1_3   (*(RoReg*)0xFFFFC174U) /**< \brief (SMC) PMECC Redundancy 1 Register (sec_num = 3) */
#define REG_SMC_PMECC2_3   (*(RoReg*)0xFFFFC178U) /**< \brief (SMC) PMECC Redundancy 2 Register (sec_num = 3) */
#define REG_SMC_PMECC3_3   (*(RoReg*)0xFFFFC17CU) /**< \brief (SMC) PMECC Redundancy 3 Register (sec_num = 3) */
#define REG_SMC_PMECC4_3   (*(RoReg*)0xFFFFC180U) /**< \brief (SMC) PMECC Redundancy 4 Register (sec_num = 3) */
#define REG_SMC_PMECC5_3   (*(RoReg*)0xFFFFC184U) /**< \brief (SMC) PMECC Redundancy 5 Register (sec_num = 3) */
#define REG_SMC_PMECC6_3   (*(RoReg*)0xFFFFC188U) /**< \brief (SMC) PMECC Redundancy 6 Register (sec_num = 3) */
#define REG_SMC_PMECC7_3   (*(RoReg*)0xFFFFC18CU) /**< \brief (SMC) PMECC Redundancy 7 Register (sec_num = 3) */
#define REG_SMC_PMECC8_3   (*(RoReg*)0xFFFFC190U) /**< \brief (SMC) PMECC Redundancy 8 Register (sec_num = 3) */
#define REG_SMC_PMECC9_3   (*(RoReg*)0xFFFFC194U) /**< \brief (SMC) PMECC Redundancy 9 Register (sec_num = 3) */
#define REG_SMC_PMECC10_3  (*(RoReg*)0xFFFFC198U) /**< \brief (SMC) PMECC Redundancy 10 Register (sec_num = 3) */
#define REG_SMC_PMECC0_4   (*(RoReg*)0xFFFFC1B0U) /**< \brief (SMC) PMECC Redundancy 0 Register (sec_num = 4) */
#define REG_SMC_PMECC1_4   (*(RoReg*)0xFFFFC1B4U) /**< \brief (SMC) PMECC Redundancy 1 Register (sec_num = 4) */
#define REG_SMC_PMECC2_4   (*(RoReg*)0xFFFFC1B8U) /**< \brief (SMC) PMECC Redundancy 2 Register (sec_num = 4) */
#define REG_SMC_PMECC3_4   (*(RoReg*)0xFFFFC1BCU) /**< \brief (SMC) PMECC Redundancy 3 Register (sec_num = 4) */
#define REG_SMC_PMECC4_4   (*(RoReg*)0xFFFFC1C0U) /**< \brief (SMC) PMECC Redundancy 4 Register (sec_num = 4) */
#define REG_SMC_PMECC5_4   (*(RoReg*)0xFFFFC1C4U) /**< \brief (SMC) PMECC Redundancy 5 Register (sec_num = 4) */
#define REG_SMC_PMECC6_4   (*(RoReg*)0xFFFFC1C8U) /**< \brief (SMC) PMECC Redundancy 6 Register (sec_num = 4) */
#define REG_SMC_PMECC7_4   (*(RoReg*)0xFFFFC1CCU) /**< \brief (SMC) PMECC Redundancy 7 Register (sec_num = 4) */
#define REG_SMC_PMECC8_4   (*(RoReg*)0xFFFFC1D0U) /**< \brief (SMC) PMECC Redundancy 8 Register (sec_num = 4) */
#define REG_SMC_PMECC9_4   (*(RoReg*)0xFFFFC1D4U) /**< \brief (SMC) PMECC Redundancy 9 Register (sec_num = 4) */
#define REG_SMC_PMECC10_4  (*(RoReg*)0xFFFFC1D8U) /**< \brief (SMC) PMECC Redundancy 10 Register (sec_num = 4) */
#define REG_SMC_PMECC0_5   (*(RoReg*)0xFFFFC1F0U) /**< \brief (SMC) PMECC Redundancy 0 Register (sec_num = 5) */
#define REG_SMC_PMECC1_5   (*(RoReg*)0xFFFFC1F4U) /**< \brief (SMC) PMECC Redundancy 1 Register (sec_num = 5) */
#define REG_SMC_PMECC2_5   (*(RoReg*)0xFFFFC1F8U) /**< \brief (SMC) PMECC Redundancy 2 Register (sec_num = 5) */
#define REG_SMC_PMECC3_5   (*(RoReg*)0xFFFFC1FCU) /**< \brief (SMC) PMECC Redundancy 3 Register (sec_num = 5) */
#define REG_SMC_PMECC4_5   (*(RoReg*)0xFFFFC200U) /**< \brief (SMC) PMECC Redundancy 4 Register (sec_num = 5) */
#define REG_SMC_PMECC5_5   (*(RoReg*)0xFFFFC204U) /**< \brief (SMC) PMECC Redundancy 5 Register (sec_num = 5) */
#define REG_SMC_PMECC6_5   (*(RoReg*)0xFFFFC208U) /**< \brief (SMC) PMECC Redundancy 6 Register (sec_num = 5) */
#define REG_SMC_PMECC7_5   (*(RoReg*)0xFFFFC20CU) /**< \brief (SMC) PMECC Redundancy 7 Register (sec_num = 5) */
#define REG_SMC_PMECC8_5   (*(RoReg*)0xFFFFC210U) /**< \brief (SMC) PMECC Redundancy 8 Register (sec_num = 5) */
#define REG_SMC_PMECC9_5   (*(RoReg*)0xFFFFC214U) /**< \brief (SMC) PMECC Redundancy 9 Register (sec_num = 5) */
#define REG_SMC_PMECC10_5  (*(RoReg*)0xFFFFC218U) /**< \brief (SMC) PMECC Redundancy 10 Register (sec_num = 5) */
#define REG_SMC_PMECC0_6   (*(RoReg*)0xFFFFC230U) /**< \brief (SMC) PMECC Redundancy 0 Register (sec_num = 6) */
#define REG_SMC_PMECC1_6   (*(RoReg*)0xFFFFC234U) /**< \brief (SMC) PMECC Redundancy 1 Register (sec_num = 6) */
#define REG_SMC_PMECC2_6   (*(RoReg*)0xFFFFC238U) /**< \brief (SMC) PMECC Redundancy 2 Register (sec_num = 6) */
#define REG_SMC_PMECC3_6   (*(RoReg*)0xFFFFC23CU) /**< \brief (SMC) PMECC Redundancy 3 Register (sec_num = 6) */
#define REG_SMC_PMECC4_6   (*(RoReg*)0xFFFFC240U) /**< \brief (SMC) PMECC Redundancy 4 Register (sec_num = 6) */
#define REG_SMC_PMECC5_6   (*(RoReg*)0xFFFFC244U) /**< \brief (SMC) PMECC Redundancy 5 Register (sec_num = 6) */
#define REG_SMC_PMECC6_6   (*(RoReg*)0xFFFFC248U) /**< \brief (SMC) PMECC Redundancy 6 Register (sec_num = 6) */
#define REG_SMC_PMECC7_6   (*(RoReg*)0xFFFFC24CU) /**< \brief (SMC) PMECC Redundancy 7 Register (sec_num = 6) */
#define REG_SMC_PMECC8_6   (*(RoReg*)0xFFFFC250U) /**< \brief (SMC) PMECC Redundancy 8 Register (sec_num = 6) */
#define REG_SMC_PMECC9_6   (*(RoReg*)0xFFFFC254U) /**< \brief (SMC) PMECC Redundancy 9 Register (sec_num = 6) */
#define REG_SMC_PMECC10_6  (*(RoReg*)0xFFFFC258U) /**< \brief (SMC) PMECC Redundancy 10 Register (sec_num = 6) */
#define REG_SMC_PMECC0_7   (*(RoReg*)0xFFFFC270U) /**< \brief (SMC) PMECC Redundancy 0 Register (sec_num = 7) */
#define REG_SMC_PMECC1_7   (*(RoReg*)0xFFFFC274U) /**< \brief (SMC) PMECC Redundancy 1 Register (sec_num = 7) */
#define REG_SMC_PMECC2_7   (*(RoReg*)0xFFFFC278U) /**< \brief (SMC) PMECC Redundancy 2 Register (sec_num = 7) */
#define REG_SMC_PMECC3_7   (*(RoReg*)0xFFFFC27CU) /**< \brief (SMC) PMECC Redundancy 3 Register (sec_num = 7) */
#define REG_SMC_PMECC4_7   (*(RoReg*)0xFFFFC280U) /**< \brief (SMC) PMECC Redundancy 4 Register (sec_num = 7) */
#define REG_SMC_PMECC5_7   (*(RoReg*)0xFFFFC284U) /**< \brief (SMC) PMECC Redundancy 5 Register (sec_num = 7) */
#define REG_SMC_PMECC6_7   (*(RoReg*)0xFFFFC288U) /**< \brief (SMC) PMECC Redundancy 6 Register (sec_num = 7) */
#define REG_SMC_PMECC7_7   (*(RoReg*)0xFFFFC28CU) /**< \brief (SMC) PMECC Redundancy 7 Register (sec_num = 7) */
#define REG_SMC_PMECC8_7   (*(RoReg*)0xFFFFC290U) /**< \brief (SMC) PMECC Redundancy 8 Register (sec_num = 7) */
#define REG_SMC_PMECC9_7   (*(RoReg*)0xFFFFC294U) /**< \brief (SMC) PMECC Redundancy 9 Register (sec_num = 7) */
#define REG_SMC_PMECC10_7  (*(RoReg*)0xFFFFC298U) /**< \brief (SMC) PMECC Redundancy 10 Register (sec_num = 7) */
#define REG_SMC_REM0_0     (*(RoReg*)0xFFFFC2B0U) /**< \brief (SMC) PMECC Remainder 0 Register (sec_num = 0) */
#define REG_SMC_REM1_0     (*(RoReg*)0xFFFFC2B4U) /**< \brief (SMC) PMECC Remainder 1 Register (sec_num = 0) */
#define REG_SMC_REM2_0     (*(RoReg*)0xFFFFC2B8U) /**< \brief (SMC) PMECC Remainder 2 Register (sec_num = 0) */
#define REG_SMC_REM3_0     (*(RoReg*)0xFFFFC2BCU) /**< \brief (SMC) PMECC Remainder 3 Register (sec_num = 0) */
#define REG_SMC_REM4_0     (*(RoReg*)0xFFFFC2C0U) /**< \brief (SMC) PMECC Remainder 4 Register (sec_num = 0) */
#define REG_SMC_REM5_0     (*(RoReg*)0xFFFFC2C4U) /**< \brief (SMC) PMECC Remainder 5 Register (sec_num = 0) */
#define REG_SMC_REM6_0     (*(RoReg*)0xFFFFC2C8U) /**< \brief (SMC) PMECC Remainder 6 Register (sec_num = 0) */
#define REG_SMC_REM7_0     (*(RoReg*)0xFFFFC2CCU) /**< \brief (SMC) PMECC Remainder 7 Register (sec_num = 0) */
#define REG_SMC_REM8_0     (*(RoReg*)0xFFFFC2D0U) /**< \brief (SMC) PMECC Remainder 8 Register (sec_num = 0) */
#define REG_SMC_REM9_0     (*(RoReg*)0xFFFFC2D4U) /**< \brief (SMC) PMECC Remainder 9 Register (sec_num = 0) */
#define REG_SMC_REM10_0    (*(RoReg*)0xFFFFC2D8U) /**< \brief (SMC) PMECC Remainder 10 Register (sec_num = 0) */
#define REG_SMC_REM11_0    (*(RoReg*)0xFFFFC2DCU) /**< \brief (SMC) PMECC Remainder 11 Register (sec_num = 0) */
#define REG_SMC_REM0_1     (*(RoReg*)0xFFFFC2F0U) /**< \brief (SMC) PMECC Remainder 0 Register (sec_num = 1) */
#define REG_SMC_REM1_1     (*(RoReg*)0xFFFFC2F4U) /**< \brief (SMC) PMECC Remainder 1 Register (sec_num = 1) */
#define REG_SMC_REM2_1     (*(RoReg*)0xFFFFC2F8U) /**< \brief (SMC) PMECC Remainder 2 Register (sec_num = 1) */
#define REG_SMC_REM3_1     (*(RoReg*)0xFFFFC2FCU) /**< \brief (SMC) PMECC Remainder 3 Register (sec_num = 1) */
#define REG_SMC_REM4_1     (*(RoReg*)0xFFFFC300U) /**< \brief (SMC) PMECC Remainder 4 Register (sec_num = 1) */
#define REG_SMC_REM5_1     (*(RoReg*)0xFFFFC304U) /**< \brief (SMC) PMECC Remainder 5 Register (sec_num = 1) */
#define REG_SMC_REM6_1     (*(RoReg*)0xFFFFC308U) /**< \brief (SMC) PMECC Remainder 6 Register (sec_num = 1) */
#define REG_SMC_REM7_1     (*(RoReg*)0xFFFFC30CU) /**< \brief (SMC) PMECC Remainder 7 Register (sec_num = 1) */
#define REG_SMC_REM8_1     (*(RoReg*)0xFFFFC310U) /**< \brief (SMC) PMECC Remainder 8 Register (sec_num = 1) */
#define REG_SMC_REM9_1     (*(RoReg*)0xFFFFC314U) /**< \brief (SMC) PMECC Remainder 9 Register (sec_num = 1) */
#define REG_SMC_REM10_1    (*(RoReg*)0xFFFFC318U) /**< \brief (SMC) PMECC Remainder 10 Register (sec_num = 1) */
#define REG_SMC_REM11_1    (*(RoReg*)0xFFFFC31CU) /**< \brief (SMC) PMECC Remainder 11 Register (sec_num = 1) */
#define REG_SMC_REM0_2     (*(RoReg*)0xFFFFC330U) /**< \brief (SMC) PMECC Remainder 0 Register (sec_num = 2) */
#define REG_SMC_REM1_2     (*(RoReg*)0xFFFFC334U) /**< \brief (SMC) PMECC Remainder 1 Register (sec_num = 2) */
#define REG_SMC_REM2_2     (*(RoReg*)0xFFFFC338U) /**< \brief (SMC) PMECC Remainder 2 Register (sec_num = 2) */
#define REG_SMC_REM3_2     (*(RoReg*)0xFFFFC33CU) /**< \brief (SMC) PMECC Remainder 3 Register (sec_num = 2) */
#define REG_SMC_REM4_2     (*(RoReg*)0xFFFFC340U) /**< \brief (SMC) PMECC Remainder 4 Register (sec_num = 2) */
#define REG_SMC_REM5_2     (*(RoReg*)0xFFFFC344U) /**< \brief (SMC) PMECC Remainder 5 Register (sec_num = 2) */
#define REG_SMC_REM6_2     (*(RoReg*)0xFFFFC348U) /**< \brief (SMC) PMECC Remainder 6 Register (sec_num = 2) */
#define REG_SMC_REM7_2     (*(RoReg*)0xFFFFC34CU) /**< \brief (SMC) PMECC Remainder 7 Register (sec_num = 2) */
#define REG_SMC_REM8_2     (*(RoReg*)0xFFFFC350U) /**< \brief (SMC) PMECC Remainder 8 Register (sec_num = 2) */
#define REG_SMC_REM9_2     (*(RoReg*)0xFFFFC354U) /**< \brief (SMC) PMECC Remainder 9 Register (sec_num = 2) */
#define REG_SMC_REM10_2    (*(RoReg*)0xFFFFC358U) /**< \brief (SMC) PMECC Remainder 10 Register (sec_num = 2) */
#define REG_SMC_REM11_2    (*(RoReg*)0xFFFFC35CU) /**< \brief (SMC) PMECC Remainder 11 Register (sec_num = 2) */
#define REG_SMC_REM0_3     (*(RoReg*)0xFFFFC370U) /**< \brief (SMC) PMECC Remainder 0 Register (sec_num = 3) */
#define REG_SMC_REM1_3     (*(RoReg*)0xFFFFC374U) /**< \brief (SMC) PMECC Remainder 1 Register (sec_num = 3) */
#define REG_SMC_REM2_3     (*(RoReg*)0xFFFFC378U) /**< \brief (SMC) PMECC Remainder 2 Register (sec_num = 3) */
#define REG_SMC_REM3_3     (*(RoReg*)0xFFFFC37CU) /**< \brief (SMC) PMECC Remainder 3 Register (sec_num = 3) */
#define REG_SMC_REM4_3     (*(RoReg*)0xFFFFC380U) /**< \brief (SMC) PMECC Remainder 4 Register (sec_num = 3) */
#define REG_SMC_REM5_3     (*(RoReg*)0xFFFFC384U) /**< \brief (SMC) PMECC Remainder 5 Register (sec_num = 3) */
#define REG_SMC_REM6_3     (*(RoReg*)0xFFFFC388U) /**< \brief (SMC) PMECC Remainder 6 Register (sec_num = 3) */
#define REG_SMC_REM7_3     (*(RoReg*)0xFFFFC38CU) /**< \brief (SMC) PMECC Remainder 7 Register (sec_num = 3) */
#define REG_SMC_REM8_3     (*(RoReg*)0xFFFFC390U) /**< \brief (SMC) PMECC Remainder 8 Register (sec_num = 3) */
#define REG_SMC_REM9_3     (*(RoReg*)0xFFFFC394U) /**< \brief (SMC) PMECC Remainder 9 Register (sec_num = 3) */
#define REG_SMC_REM10_3    (*(RoReg*)0xFFFFC398U) /**< \brief (SMC) PMECC Remainder 10 Register (sec_num = 3) */
#define REG_SMC_REM11_3    (*(RoReg*)0xFFFFC39CU) /**< \brief (SMC) PMECC Remainder 11 Register (sec_num = 3) */
#define REG_SMC_REM0_4     (*(RoReg*)0xFFFFC3B0U) /**< \brief (SMC) PMECC Remainder 0 Register (sec_num = 4) */
#define REG_SMC_REM1_4     (*(RoReg*)0xFFFFC3B4U) /**< \brief (SMC) PMECC Remainder 1 Register (sec_num = 4) */
#define REG_SMC_REM2_4     (*(RoReg*)0xFFFFC3B8U) /**< \brief (SMC) PMECC Remainder 2 Register (sec_num = 4) */
#define REG_SMC_REM3_4     (*(RoReg*)0xFFFFC3BCU) /**< \brief (SMC) PMECC Remainder 3 Register (sec_num = 4) */
#define REG_SMC_REM4_4     (*(RoReg*)0xFFFFC3C0U) /**< \brief (SMC) PMECC Remainder 4 Register (sec_num = 4) */
#define REG_SMC_REM5_4     (*(RoReg*)0xFFFFC3C4U) /**< \brief (SMC) PMECC Remainder 5 Register (sec_num = 4) */
#define REG_SMC_REM6_4     (*(RoReg*)0xFFFFC3C8U) /**< \brief (SMC) PMECC Remainder 6 Register (sec_num = 4) */
#define REG_SMC_REM7_4     (*(RoReg*)0xFFFFC3CCU) /**< \brief (SMC) PMECC Remainder 7 Register (sec_num = 4) */
#define REG_SMC_REM8_4     (*(RoReg*)0xFFFFC3D0U) /**< \brief (SMC) PMECC Remainder 8 Register (sec_num = 4) */
#define REG_SMC_REM9_4     (*(RoReg*)0xFFFFC3D4U) /**< \brief (SMC) PMECC Remainder 9 Register (sec_num = 4) */
#define REG_SMC_REM10_4    (*(RoReg*)0xFFFFC3D8U) /**< \brief (SMC) PMECC Remainder 10 Register (sec_num = 4) */
#define REG_SMC_REM11_4    (*(RoReg*)0xFFFFC3DCU) /**< \brief (SMC) PMECC Remainder 11 Register (sec_num = 4) */
#define REG_SMC_REM0_5     (*(RoReg*)0xFFFFC3F0U) /**< \brief (SMC) PMECC Remainder 0 Register (sec_num = 5) */
#define REG_SMC_REM1_5     (*(RoReg*)0xFFFFC3F4U) /**< \brief (SMC) PMECC Remainder 1 Register (sec_num = 5) */
#define REG_SMC_REM2_5     (*(RoReg*)0xFFFFC3F8U) /**< \brief (SMC) PMECC Remainder 2 Register (sec_num = 5) */
#define REG_SMC_REM3_5     (*(RoReg*)0xFFFFC3FCU) /**< \brief (SMC) PMECC Remainder 3 Register (sec_num = 5) */
#define REG_SMC_REM4_5     (*(RoReg*)0xFFFFC400U) /**< \brief (SMC) PMECC Remainder 4 Register (sec_num = 5) */
#define REG_SMC_REM5_5     (*(RoReg*)0xFFFFC404U) /**< \brief (SMC) PMECC Remainder 5 Register (sec_num = 5) */
#define REG_SMC_REM6_5     (*(RoReg*)0xFFFFC408U) /**< \brief (SMC) PMECC Remainder 6 Register (sec_num = 5) */
#define REG_SMC_REM7_5     (*(RoReg*)0xFFFFC40CU) /**< \brief (SMC) PMECC Remainder 7 Register (sec_num = 5) */
#define REG_SMC_REM8_5     (*(RoReg*)0xFFFFC410U) /**< \brief (SMC) PMECC Remainder 8 Register (sec_num = 5) */
#define REG_SMC_REM9_5     (*(RoReg*)0xFFFFC414U) /**< \brief (SMC) PMECC Remainder 9 Register (sec_num = 5) */
#define REG_SMC_REM10_5    (*(RoReg*)0xFFFFC418U) /**< \brief (SMC) PMECC Remainder 10 Register (sec_num = 5) */
#define REG_SMC_REM11_5    (*(RoReg*)0xFFFFC41CU) /**< \brief (SMC) PMECC Remainder 11 Register (sec_num = 5) */
#define REG_SMC_REM0_6     (*(RoReg*)0xFFFFC430U) /**< \brief (SMC) PMECC Remainder 0 Register (sec_num = 6) */
#define REG_SMC_REM1_6     (*(RoReg*)0xFFFFC434U) /**< \brief (SMC) PMECC Remainder 1 Register (sec_num = 6) */
#define REG_SMC_REM2_6     (*(RoReg*)0xFFFFC438U) /**< \brief (SMC) PMECC Remainder 2 Register (sec_num = 6) */
#define REG_SMC_REM3_6     (*(RoReg*)0xFFFFC43CU) /**< \brief (SMC) PMECC Remainder 3 Register (sec_num = 6) */
#define REG_SMC_REM4_6     (*(RoReg*)0xFFFFC440U) /**< \brief (SMC) PMECC Remainder 4 Register (sec_num = 6) */
#define REG_SMC_REM5_6     (*(RoReg*)0xFFFFC444U) /**< \brief (SMC) PMECC Remainder 5 Register (sec_num = 6) */
#define REG_SMC_REM6_6     (*(RoReg*)0xFFFFC448U) /**< \brief (SMC) PMECC Remainder 6 Register (sec_num = 6) */
#define REG_SMC_REM7_6     (*(RoReg*)0xFFFFC44CU) /**< \brief (SMC) PMECC Remainder 7 Register (sec_num = 6) */
#define REG_SMC_REM8_6     (*(RoReg*)0xFFFFC450U) /**< \brief (SMC) PMECC Remainder 8 Register (sec_num = 6) */
#define REG_SMC_REM9_6     (*(RoReg*)0xFFFFC454U) /**< \brief (SMC) PMECC Remainder 9 Register (sec_num = 6) */
#define REG_SMC_REM10_6    (*(RoReg*)0xFFFFC458U) /**< \brief (SMC) PMECC Remainder 10 Register (sec_num = 6) */
#define REG_SMC_REM11_6    (*(RoReg*)0xFFFFC45CU) /**< \brief (SMC) PMECC Remainder 11 Register (sec_num = 6) */
#define REG_SMC_REM0_7     (*(RoReg*)0xFFFFC470U) /**< \brief (SMC) PMECC Remainder 0 Register (sec_num = 7) */
#define REG_SMC_REM1_7     (*(RoReg*)0xFFFFC474U) /**< \brief (SMC) PMECC Remainder 1 Register (sec_num = 7) */
#define REG_SMC_REM2_7     (*(RoReg*)0xFFFFC478U) /**< \brief (SMC) PMECC Remainder 2 Register (sec_num = 7) */
#define REG_SMC_REM3_7     (*(RoReg*)0xFFFFC47CU) /**< \brief (SMC) PMECC Remainder 3 Register (sec_num = 7) */
#define REG_SMC_REM4_7     (*(RoReg*)0xFFFFC480U) /**< \brief (SMC) PMECC Remainder 4 Register (sec_num = 7) */
#define REG_SMC_REM5_7     (*(RoReg*)0xFFFFC484U) /**< \brief (SMC) PMECC Remainder 5 Register (sec_num = 7) */
#define REG_SMC_REM6_7     (*(RoReg*)0xFFFFC488U) /**< \brief (SMC) PMECC Remainder 6 Register (sec_num = 7) */
#define REG_SMC_REM7_7     (*(RoReg*)0xFFFFC48CU) /**< \brief (SMC) PMECC Remainder 7 Register (sec_num = 7) */
#define REG_SMC_REM8_7     (*(RoReg*)0xFFFFC490U) /**< \brief (SMC) PMECC Remainder 8 Register (sec_num = 7) */
#define REG_SMC_REM9_7     (*(RoReg*)0xFFFFC494U) /**< \brief (SMC) PMECC Remainder 9 Register (sec_num = 7) */
#define REG_SMC_REM10_7    (*(RoReg*)0xFFFFC498U) /**< \brief (SMC) PMECC Remainder 10 Register (sec_num = 7) */
#define REG_SMC_REM11_7    (*(RoReg*)0xFFFFC49CU) /**< \brief (SMC) PMECC Remainder 11 Register (sec_num = 7) */
#define REG_SMC_ELCFG      (*(RwReg*)0xFFFFC500U) /**< \brief (SMC) PMECC Error Location Configuration Register */
#define REG_SMC_ELPRIM     (*(RoReg*)0xFFFFC504U) /**< \brief (SMC) PMECC Error Location Primitive Register */
#define REG_SMC_ELEN       (*(WoReg*)0xFFFFC508U) /**< \brief (SMC) PMECC Error Location Enable Register */
#define REG_SMC_ELDIS      (*(WoReg*)0xFFFFC50CU) /**< \brief (SMC) PMECC Error Location Disable Register */
#define REG_SMC_ELSR       (*(RoReg*)0xFFFFC510U) /**< \brief (SMC) PMECC Error Location Status Register */
#define REG_SMC_ELIER      (*(WoReg*)0xFFFFC514U) /**< \brief (SMC) PMECC Error Location Interrupt Enable register */
#define REG_SMC_ELIDR      (*(WoReg*)0xFFFFC518U) /**< \brief (SMC) PMECC Error Location Interrupt Disable Register */
#define REG_SMC_ELIMR      (*(RoReg*)0xFFFFC51CU) /**< \brief (SMC) PMECC Error Location Interrupt Mask Register */
#define REG_SMC_ELISR      (*(RoReg*)0xFFFFC520U) /**< \brief (SMC) PMECC Error Location Interrupt Status Register */
#define REG_SMC_SIGMA0     (*(RwReg*)0xFFFFC528U) /**< \brief (SMC) PMECC Error Location SIGMA 0 Register */
#define REG_SMC_SIGMA1     (*(RwReg*)0xFFFFC52CU) /**< \brief (SMC) PMECC Error Location SIGMA 1 Register */
#define REG_SMC_SIGMA2     (*(RwReg*)0xFFFFC530U) /**< \brief (SMC) PMECC Error Location SIGMA 2 Register */
#define REG_SMC_SIGMA3     (*(RwReg*)0xFFFFC534U) /**< \brief (SMC) PMECC Error Location SIGMA 3 Register */
#define REG_SMC_SIGMA4     (*(RwReg*)0xFFFFC538U) /**< \brief (SMC) PMECC Error Location SIGMA 4 Register */
#define REG_SMC_SIGMA5     (*(RwReg*)0xFFFFC53CU) /**< \brief (SMC) PMECC Error Location SIGMA 5 Register */
#define REG_SMC_SIGMA6     (*(RwReg*)0xFFFFC540U) /**< \brief (SMC) PMECC Error Location SIGMA 6 Register */
#define REG_SMC_SIGMA7     (*(RwReg*)0xFFFFC544U) /**< \brief (SMC) PMECC Error Location SIGMA 7 Register */
#define REG_SMC_SIGMA8     (*(RwReg*)0xFFFFC548U) /**< \brief (SMC) PMECC Error Location SIGMA 8 Register */
#define REG_SMC_SIGMA9     (*(RwReg*)0xFFFFC54CU) /**< \brief (SMC) PMECC Error Location SIGMA 9 Register */
#define REG_SMC_SIGMA10    (*(RwReg*)0xFFFFC550U) /**< \brief (SMC) PMECC Error Location SIGMA 10 Register */
#define REG_SMC_SIGMA11    (*(RwReg*)0xFFFFC554U) /**< \brief (SMC) PMECC Error Location SIGMA 11 Register */
#define REG_SMC_SIGMA12    (*(RwReg*)0xFFFFC558U) /**< \brief (SMC) PMECC Error Location SIGMA 12 Register */
#define REG_SMC_SIGMA13    (*(RwReg*)0xFFFFC55CU) /**< \brief (SMC) PMECC Error Location SIGMA 13 Register */
#define REG_SMC_SIGMA14    (*(RwReg*)0xFFFFC560U) /**< \brief (SMC) PMECC Error Location SIGMA 14 Register */
#define REG_SMC_SIGMA15    (*(RwReg*)0xFFFFC564U) /**< \brief (SMC) PMECC Error Location SIGMA 15 Register */
#define REG_SMC_SIGMA16    (*(RwReg*)0xFFFFC568U) /**< \brief (SMC) PMECC Error Location SIGMA 16 Register */
#define REG_SMC_SIGMA17    (*(RwReg*)0xFFFFC56CU) /**< \brief (SMC) PMECC Error Location SIGMA 17 Register */
#define REG_SMC_SIGMA18    (*(RwReg*)0xFFFFC570U) /**< \brief (SMC) PMECC Error Location SIGMA 18 Register */
#define REG_SMC_SIGMA19    (*(RwReg*)0xFFFFC574U) /**< \brief (SMC) PMECC Error Location SIGMA 19 Register */
#define REG_SMC_SIGMA20    (*(RwReg*)0xFFFFC578U) /**< \brief (SMC) PMECC Error Location SIGMA 20 Register */
#define REG_SMC_SIGMA21    (*(RwReg*)0xFFFFC57CU) /**< \brief (SMC) PMECC Error Location SIGMA 21 Register */
#define REG_SMC_SIGMA22    (*(RwReg*)0xFFFFC580U) /**< \brief (SMC) PMECC Error Location SIGMA 22 Register */
#define REG_SMC_SIGMA23    (*(RwReg*)0xFFFFC584U) /**< \brief (SMC) PMECC Error Location SIGMA 23 Register */
#define REG_SMC_SIGMA24    (*(RwReg*)0xFFFFC588U) /**< \brief (SMC) PMECC Error Location SIGMA 24 Register */
#define REG_SMC_ERRLOC     (*(RoReg*)0xFFFFC58CU) /**< \brief (SMC) PMECC Error Location 0 Register */
#define REG_SMC_SETUP0     (*(RwReg*)0xFFFFC600U) /**< \brief (SMC) SMC Setup Register (CS_number = 0) */
#define REG_SMC_PULSE0     (*(RwReg*)0xFFFFC604U) /**< \brief (SMC) SMC Pulse Register (CS_number = 0) */
#define REG_SMC_CYCLE0     (*(RwReg*)0xFFFFC608U) /**< \brief (SMC) SMC Cycle Register (CS_number = 0) */
#define REG_SMC_TIMINGS0   (*(RwReg*)0xFFFFC60CU) /**< \brief (SMC) SMC Timings Register (CS_number = 0) */
#define REG_SMC_MODE0      (*(RwReg*)0xFFFFC610U) /**< \brief (SMC) SMC Mode Register (CS_number = 0) */
#define REG_SMC_SETUP1     (*(RwReg*)0xFFFFC614U) /**< \brief (SMC) SMC Setup Register (CS_number = 1) */
#define REG_SMC_PULSE1     (*(RwReg*)0xFFFFC618U) /**< \brief (SMC) SMC Pulse Register (CS_number = 1) */
#define REG_SMC_CYCLE1     (*(RwReg*)0xFFFFC61CU) /**< \brief (SMC) SMC Cycle Register (CS_number = 1) */
#define REG_SMC_TIMINGS1   (*(RwReg*)0xFFFFC620U) /**< \brief (SMC) SMC Timings Register (CS_number = 1) */
#define REG_SMC_MODE1      (*(RwReg*)0xFFFFC624U) /**< \brief (SMC) SMC Mode Register (CS_number = 1) */
#define REG_SMC_SETUP2     (*(RwReg*)0xFFFFC628U) /**< \brief (SMC) SMC Setup Register (CS_number = 2) */
#define REG_SMC_PULSE2     (*(RwReg*)0xFFFFC62CU) /**< \brief (SMC) SMC Pulse Register (CS_number = 2) */
#define REG_SMC_CYCLE2     (*(RwReg*)0xFFFFC630U) /**< \brief (SMC) SMC Cycle Register (CS_number = 2) */
#define REG_SMC_TIMINGS2   (*(RwReg*)0xFFFFC634U) /**< \brief (SMC) SMC Timings Register (CS_number = 2) */
#define REG_SMC_MODE2      (*(RwReg*)0xFFFFC638U) /**< \brief (SMC) SMC Mode Register (CS_number = 2) */
#define REG_SMC_SETUP3     (*(RwReg*)0xFFFFC63CU) /**< \brief (SMC) SMC Setup Register (CS_number = 3) */
#define REG_SMC_PULSE3     (*(RwReg*)0xFFFFC640U) /**< \brief (SMC) SMC Pulse Register (CS_number = 3) */
#define REG_SMC_CYCLE3     (*(RwReg*)0xFFFFC644U) /**< \brief (SMC) SMC Cycle Register (CS_number = 3) */
#define REG_SMC_TIMINGS3   (*(RwReg*)0xFFFFC648U) /**< \brief (SMC) SMC Timings Register (CS_number = 3) */
#define REG_SMC_MODE3      (*(RwReg*)0xFFFFC64CU) /**< \brief (SMC) SMC Mode Register (CS_number = 3) */
#define REG_SMC_OCMS       (*(RwReg*)0xFFFFC6A0U) /**< \brief (SMC) SMC OCMS Register */
#define REG_SMC_KEY1       (*(WoReg*)0xFFFFC6A4U) /**< \brief (SMC) SMC OCMS KEY1 Register */
#define REG_SMC_KEY2       (*(WoReg*)0xFFFFC6A8U) /**< \brief (SMC) SMC OCMS KEY2 Register */
#define REG_SMC_WPCR       (*(WoReg*)0xFFFFC6E4U) /**< \brief (SMC) SMC Write Protection Control Register */
#define REG_SMC_WPSR       (*(RoReg*)0xFFFFC6E8U) /**< \brief (SMC) SMC Write Protection Status Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAMA5_SMC_INSTANCE_ */
