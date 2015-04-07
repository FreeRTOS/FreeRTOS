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

#ifndef _SAMA5_CAN0_INSTANCE_
#define _SAMA5_CAN0_INSTANCE_

/* ========== Register definition for CAN0 peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
#define REG_CAN0_MR               (0xF000C000U) /**< \brief (CAN0) Mode Register */
#define REG_CAN0_IER              (0xF000C004U) /**< \brief (CAN0) Interrupt Enable Register */
#define REG_CAN0_IDR              (0xF000C008U) /**< \brief (CAN0) Interrupt Disable Register */
#define REG_CAN0_IMR              (0xF000C00CU) /**< \brief (CAN0) Interrupt Mask Register */
#define REG_CAN0_SR               (0xF000C010U) /**< \brief (CAN0) Status Register */
#define REG_CAN0_BR               (0xF000C014U) /**< \brief (CAN0) Baudrate Register */
#define REG_CAN0_TIM              (0xF000C018U) /**< \brief (CAN0) Timer Register */
#define REG_CAN0_TIMESTP          (0xF000C01CU) /**< \brief (CAN0) Timestamp Register */
#define REG_CAN0_ECR              (0xF000C020U) /**< \brief (CAN0) Error Counter Register */
#define REG_CAN0_TCR              (0xF000C024U) /**< \brief (CAN0) Transfer Command Register */
#define REG_CAN0_ACR              (0xF000C028U) /**< \brief (CAN0) Abort Command Register */
#define REG_CAN0_WPMR             (0xF000C0E4U) /**< \brief (CAN0) Write Protect Mode Register */
#define REG_CAN0_WPSR             (0xF000C0E8U) /**< \brief (CAN0) Write Protect Status Register */
#define REG_CAN0_MMR0             (0xF000C200U) /**< \brief (CAN0) Mailbox Mode Register (MB = 0) */
#define REG_CAN0_MAM0             (0xF000C204U) /**< \brief (CAN0) Mailbox Acceptance Mask Register (MB = 0) */
#define REG_CAN0_MID0             (0xF000C208U) /**< \brief (CAN0) Mailbox ID Register (MB = 0) */
#define REG_CAN0_MFID0            (0xF000C20CU) /**< \brief (CAN0) Mailbox Family ID Register (MB = 0) */
#define REG_CAN0_MSR0             (0xF000C210U) /**< \brief (CAN0) Mailbox Status Register (MB = 0) */
#define REG_CAN0_MDL0             (0xF000C214U) /**< \brief (CAN0) Mailbox Data Low Register (MB = 0) */
#define REG_CAN0_MDH0             (0xF000C218U) /**< \brief (CAN0) Mailbox Data High Register (MB = 0) */
#define REG_CAN0_MCR0             (0xF000C21CU) /**< \brief (CAN0) Mailbox Control Register (MB = 0) */
#define REG_CAN0_MMR1             (0xF000C220U) /**< \brief (CAN0) Mailbox Mode Register (MB = 1) */
#define REG_CAN0_MAM1             (0xF000C224U) /**< \brief (CAN0) Mailbox Acceptance Mask Register (MB = 1) */
#define REG_CAN0_MID1             (0xF000C228U) /**< \brief (CAN0) Mailbox ID Register (MB = 1) */
#define REG_CAN0_MFID1            (0xF000C22CU) /**< \brief (CAN0) Mailbox Family ID Register (MB = 1) */
#define REG_CAN0_MSR1             (0xF000C230U) /**< \brief (CAN0) Mailbox Status Register (MB = 1) */
#define REG_CAN0_MDL1             (0xF000C234U) /**< \brief (CAN0) Mailbox Data Low Register (MB = 1) */
#define REG_CAN0_MDH1             (0xF000C238U) /**< \brief (CAN0) Mailbox Data High Register (MB = 1) */
#define REG_CAN0_MCR1             (0xF000C23CU) /**< \brief (CAN0) Mailbox Control Register (MB = 1) */
#define REG_CAN0_MMR2             (0xF000C240U) /**< \brief (CAN0) Mailbox Mode Register (MB = 2) */
#define REG_CAN0_MAM2             (0xF000C244U) /**< \brief (CAN0) Mailbox Acceptance Mask Register (MB = 2) */
#define REG_CAN0_MID2             (0xF000C248U) /**< \brief (CAN0) Mailbox ID Register (MB = 2) */
#define REG_CAN0_MFID2            (0xF000C24CU) /**< \brief (CAN0) Mailbox Family ID Register (MB = 2) */
#define REG_CAN0_MSR2             (0xF000C250U) /**< \brief (CAN0) Mailbox Status Register (MB = 2) */
#define REG_CAN0_MDL2             (0xF000C254U) /**< \brief (CAN0) Mailbox Data Low Register (MB = 2) */
#define REG_CAN0_MDH2             (0xF000C258U) /**< \brief (CAN0) Mailbox Data High Register (MB = 2) */
#define REG_CAN0_MCR2             (0xF000C25CU) /**< \brief (CAN0) Mailbox Control Register (MB = 2) */
#define REG_CAN0_MMR3             (0xF000C260U) /**< \brief (CAN0) Mailbox Mode Register (MB = 3) */
#define REG_CAN0_MAM3             (0xF000C264U) /**< \brief (CAN0) Mailbox Acceptance Mask Register (MB = 3) */
#define REG_CAN0_MID3             (0xF000C268U) /**< \brief (CAN0) Mailbox ID Register (MB = 3) */
#define REG_CAN0_MFID3            (0xF000C26CU) /**< \brief (CAN0) Mailbox Family ID Register (MB = 3) */
#define REG_CAN0_MSR3             (0xF000C270U) /**< \brief (CAN0) Mailbox Status Register (MB = 3) */
#define REG_CAN0_MDL3             (0xF000C274U) /**< \brief (CAN0) Mailbox Data Low Register (MB = 3) */
#define REG_CAN0_MDH3             (0xF000C278U) /**< \brief (CAN0) Mailbox Data High Register (MB = 3) */
#define REG_CAN0_MCR3             (0xF000C27CU) /**< \brief (CAN0) Mailbox Control Register (MB = 3) */
#define REG_CAN0_MMR4             (0xF000C280U) /**< \brief (CAN0) Mailbox Mode Register (MB = 4) */
#define REG_CAN0_MAM4             (0xF000C284U) /**< \brief (CAN0) Mailbox Acceptance Mask Register (MB = 4) */
#define REG_CAN0_MID4             (0xF000C288U) /**< \brief (CAN0) Mailbox ID Register (MB = 4) */
#define REG_CAN0_MFID4            (0xF000C28CU) /**< \brief (CAN0) Mailbox Family ID Register (MB = 4) */
#define REG_CAN0_MSR4             (0xF000C290U) /**< \brief (CAN0) Mailbox Status Register (MB = 4) */
#define REG_CAN0_MDL4             (0xF000C294U) /**< \brief (CAN0) Mailbox Data Low Register (MB = 4) */
#define REG_CAN0_MDH4             (0xF000C298U) /**< \brief (CAN0) Mailbox Data High Register (MB = 4) */
#define REG_CAN0_MCR4             (0xF000C29CU) /**< \brief (CAN0) Mailbox Control Register (MB = 4) */
#define REG_CAN0_MMR5             (0xF000C2A0U) /**< \brief (CAN0) Mailbox Mode Register (MB = 5) */
#define REG_CAN0_MAM5             (0xF000C2A4U) /**< \brief (CAN0) Mailbox Acceptance Mask Register (MB = 5) */
#define REG_CAN0_MID5             (0xF000C2A8U) /**< \brief (CAN0) Mailbox ID Register (MB = 5) */
#define REG_CAN0_MFID5            (0xF000C2ACU) /**< \brief (CAN0) Mailbox Family ID Register (MB = 5) */
#define REG_CAN0_MSR5             (0xF000C2B0U) /**< \brief (CAN0) Mailbox Status Register (MB = 5) */
#define REG_CAN0_MDL5             (0xF000C2B4U) /**< \brief (CAN0) Mailbox Data Low Register (MB = 5) */
#define REG_CAN0_MDH5             (0xF000C2B8U) /**< \brief (CAN0) Mailbox Data High Register (MB = 5) */
#define REG_CAN0_MCR5             (0xF000C2BCU) /**< \brief (CAN0) Mailbox Control Register (MB = 5) */
#define REG_CAN0_MMR6             (0xF000C2C0U) /**< \brief (CAN0) Mailbox Mode Register (MB = 6) */
#define REG_CAN0_MAM6             (0xF000C2C4U) /**< \brief (CAN0) Mailbox Acceptance Mask Register (MB = 6) */
#define REG_CAN0_MID6             (0xF000C2C8U) /**< \brief (CAN0) Mailbox ID Register (MB = 6) */
#define REG_CAN0_MFID6            (0xF000C2CCU) /**< \brief (CAN0) Mailbox Family ID Register (MB = 6) */
#define REG_CAN0_MSR6             (0xF000C2D0U) /**< \brief (CAN0) Mailbox Status Register (MB = 6) */
#define REG_CAN0_MDL6             (0xF000C2D4U) /**< \brief (CAN0) Mailbox Data Low Register (MB = 6) */
#define REG_CAN0_MDH6             (0xF000C2D8U) /**< \brief (CAN0) Mailbox Data High Register (MB = 6) */
#define REG_CAN0_MCR6             (0xF000C2DCU) /**< \brief (CAN0) Mailbox Control Register (MB = 6) */
#define REG_CAN0_MMR7             (0xF000C2E0U) /**< \brief (CAN0) Mailbox Mode Register (MB = 7) */
#define REG_CAN0_MAM7             (0xF000C2E4U) /**< \brief (CAN0) Mailbox Acceptance Mask Register (MB = 7) */
#define REG_CAN0_MID7             (0xF000C2E8U) /**< \brief (CAN0) Mailbox ID Register (MB = 7) */
#define REG_CAN0_MFID7            (0xF000C2ECU) /**< \brief (CAN0) Mailbox Family ID Register (MB = 7) */
#define REG_CAN0_MSR7             (0xF000C2F0U) /**< \brief (CAN0) Mailbox Status Register (MB = 7) */
#define REG_CAN0_MDL7             (0xF000C2F4U) /**< \brief (CAN0) Mailbox Data Low Register (MB = 7) */
#define REG_CAN0_MDH7             (0xF000C2F8U) /**< \brief (CAN0) Mailbox Data High Register (MB = 7) */
#define REG_CAN0_MCR7             (0xF000C2FCU) /**< \brief (CAN0) Mailbox Control Register (MB = 7) */
#else
#define REG_CAN0_MR      (*(RwReg*)0xF000C000U) /**< \brief (CAN0) Mode Register */
#define REG_CAN0_IER     (*(WoReg*)0xF000C004U) /**< \brief (CAN0) Interrupt Enable Register */
#define REG_CAN0_IDR     (*(WoReg*)0xF000C008U) /**< \brief (CAN0) Interrupt Disable Register */
#define REG_CAN0_IMR     (*(RoReg*)0xF000C00CU) /**< \brief (CAN0) Interrupt Mask Register */
#define REG_CAN0_SR      (*(RoReg*)0xF000C010U) /**< \brief (CAN0) Status Register */
#define REG_CAN0_BR      (*(RwReg*)0xF000C014U) /**< \brief (CAN0) Baudrate Register */
#define REG_CAN0_TIM     (*(RoReg*)0xF000C018U) /**< \brief (CAN0) Timer Register */
#define REG_CAN0_TIMESTP (*(RoReg*)0xF000C01CU) /**< \brief (CAN0) Timestamp Register */
#define REG_CAN0_ECR     (*(RoReg*)0xF000C020U) /**< \brief (CAN0) Error Counter Register */
#define REG_CAN0_TCR     (*(WoReg*)0xF000C024U) /**< \brief (CAN0) Transfer Command Register */
#define REG_CAN0_ACR     (*(WoReg*)0xF000C028U) /**< \brief (CAN0) Abort Command Register */
#define REG_CAN0_WPMR    (*(RwReg*)0xF000C0E4U) /**< \brief (CAN0) Write Protect Mode Register */
#define REG_CAN0_WPSR    (*(RoReg*)0xF000C0E8U) /**< \brief (CAN0) Write Protect Status Register */
#define REG_CAN0_MMR0    (*(RwReg*)0xF000C200U) /**< \brief (CAN0) Mailbox Mode Register (MB = 0) */
#define REG_CAN0_MAM0    (*(RwReg*)0xF000C204U) /**< \brief (CAN0) Mailbox Acceptance Mask Register (MB = 0) */
#define REG_CAN0_MID0    (*(RwReg*)0xF000C208U) /**< \brief (CAN0) Mailbox ID Register (MB = 0) */
#define REG_CAN0_MFID0   (*(RoReg*)0xF000C20CU) /**< \brief (CAN0) Mailbox Family ID Register (MB = 0) */
#define REG_CAN0_MSR0    (*(RoReg*)0xF000C210U) /**< \brief (CAN0) Mailbox Status Register (MB = 0) */
#define REG_CAN0_MDL0    (*(RwReg*)0xF000C214U) /**< \brief (CAN0) Mailbox Data Low Register (MB = 0) */
#define REG_CAN0_MDH0    (*(RwReg*)0xF000C218U) /**< \brief (CAN0) Mailbox Data High Register (MB = 0) */
#define REG_CAN0_MCR0    (*(WoReg*)0xF000C21CU) /**< \brief (CAN0) Mailbox Control Register (MB = 0) */
#define REG_CAN0_MMR1    (*(RwReg*)0xF000C220U) /**< \brief (CAN0) Mailbox Mode Register (MB = 1) */
#define REG_CAN0_MAM1    (*(RwReg*)0xF000C224U) /**< \brief (CAN0) Mailbox Acceptance Mask Register (MB = 1) */
#define REG_CAN0_MID1    (*(RwReg*)0xF000C228U) /**< \brief (CAN0) Mailbox ID Register (MB = 1) */
#define REG_CAN0_MFID1   (*(RoReg*)0xF000C22CU) /**< \brief (CAN0) Mailbox Family ID Register (MB = 1) */
#define REG_CAN0_MSR1    (*(RoReg*)0xF000C230U) /**< \brief (CAN0) Mailbox Status Register (MB = 1) */
#define REG_CAN0_MDL1    (*(RwReg*)0xF000C234U) /**< \brief (CAN0) Mailbox Data Low Register (MB = 1) */
#define REG_CAN0_MDH1    (*(RwReg*)0xF000C238U) /**< \brief (CAN0) Mailbox Data High Register (MB = 1) */
#define REG_CAN0_MCR1    (*(WoReg*)0xF000C23CU) /**< \brief (CAN0) Mailbox Control Register (MB = 1) */
#define REG_CAN0_MMR2    (*(RwReg*)0xF000C240U) /**< \brief (CAN0) Mailbox Mode Register (MB = 2) */
#define REG_CAN0_MAM2    (*(RwReg*)0xF000C244U) /**< \brief (CAN0) Mailbox Acceptance Mask Register (MB = 2) */
#define REG_CAN0_MID2    (*(RwReg*)0xF000C248U) /**< \brief (CAN0) Mailbox ID Register (MB = 2) */
#define REG_CAN0_MFID2   (*(RoReg*)0xF000C24CU) /**< \brief (CAN0) Mailbox Family ID Register (MB = 2) */
#define REG_CAN0_MSR2    (*(RoReg*)0xF000C250U) /**< \brief (CAN0) Mailbox Status Register (MB = 2) */
#define REG_CAN0_MDL2    (*(RwReg*)0xF000C254U) /**< \brief (CAN0) Mailbox Data Low Register (MB = 2) */
#define REG_CAN0_MDH2    (*(RwReg*)0xF000C258U) /**< \brief (CAN0) Mailbox Data High Register (MB = 2) */
#define REG_CAN0_MCR2    (*(WoReg*)0xF000C25CU) /**< \brief (CAN0) Mailbox Control Register (MB = 2) */
#define REG_CAN0_MMR3    (*(RwReg*)0xF000C260U) /**< \brief (CAN0) Mailbox Mode Register (MB = 3) */
#define REG_CAN0_MAM3    (*(RwReg*)0xF000C264U) /**< \brief (CAN0) Mailbox Acceptance Mask Register (MB = 3) */
#define REG_CAN0_MID3    (*(RwReg*)0xF000C268U) /**< \brief (CAN0) Mailbox ID Register (MB = 3) */
#define REG_CAN0_MFID3   (*(RoReg*)0xF000C26CU) /**< \brief (CAN0) Mailbox Family ID Register (MB = 3) */
#define REG_CAN0_MSR3    (*(RoReg*)0xF000C270U) /**< \brief (CAN0) Mailbox Status Register (MB = 3) */
#define REG_CAN0_MDL3    (*(RwReg*)0xF000C274U) /**< \brief (CAN0) Mailbox Data Low Register (MB = 3) */
#define REG_CAN0_MDH3    (*(RwReg*)0xF000C278U) /**< \brief (CAN0) Mailbox Data High Register (MB = 3) */
#define REG_CAN0_MCR3    (*(WoReg*)0xF000C27CU) /**< \brief (CAN0) Mailbox Control Register (MB = 3) */
#define REG_CAN0_MMR4    (*(RwReg*)0xF000C280U) /**< \brief (CAN0) Mailbox Mode Register (MB = 4) */
#define REG_CAN0_MAM4    (*(RwReg*)0xF000C284U) /**< \brief (CAN0) Mailbox Acceptance Mask Register (MB = 4) */
#define REG_CAN0_MID4    (*(RwReg*)0xF000C288U) /**< \brief (CAN0) Mailbox ID Register (MB = 4) */
#define REG_CAN0_MFID4   (*(RoReg*)0xF000C28CU) /**< \brief (CAN0) Mailbox Family ID Register (MB = 4) */
#define REG_CAN0_MSR4    (*(RoReg*)0xF000C290U) /**< \brief (CAN0) Mailbox Status Register (MB = 4) */
#define REG_CAN0_MDL4    (*(RwReg*)0xF000C294U) /**< \brief (CAN0) Mailbox Data Low Register (MB = 4) */
#define REG_CAN0_MDH4    (*(RwReg*)0xF000C298U) /**< \brief (CAN0) Mailbox Data High Register (MB = 4) */
#define REG_CAN0_MCR4    (*(WoReg*)0xF000C29CU) /**< \brief (CAN0) Mailbox Control Register (MB = 4) */
#define REG_CAN0_MMR5    (*(RwReg*)0xF000C2A0U) /**< \brief (CAN0) Mailbox Mode Register (MB = 5) */
#define REG_CAN0_MAM5    (*(RwReg*)0xF000C2A4U) /**< \brief (CAN0) Mailbox Acceptance Mask Register (MB = 5) */
#define REG_CAN0_MID5    (*(RwReg*)0xF000C2A8U) /**< \brief (CAN0) Mailbox ID Register (MB = 5) */
#define REG_CAN0_MFID5   (*(RoReg*)0xF000C2ACU) /**< \brief (CAN0) Mailbox Family ID Register (MB = 5) */
#define REG_CAN0_MSR5    (*(RoReg*)0xF000C2B0U) /**< \brief (CAN0) Mailbox Status Register (MB = 5) */
#define REG_CAN0_MDL5    (*(RwReg*)0xF000C2B4U) /**< \brief (CAN0) Mailbox Data Low Register (MB = 5) */
#define REG_CAN0_MDH5    (*(RwReg*)0xF000C2B8U) /**< \brief (CAN0) Mailbox Data High Register (MB = 5) */
#define REG_CAN0_MCR5    (*(WoReg*)0xF000C2BCU) /**< \brief (CAN0) Mailbox Control Register (MB = 5) */
#define REG_CAN0_MMR6    (*(RwReg*)0xF000C2C0U) /**< \brief (CAN0) Mailbox Mode Register (MB = 6) */
#define REG_CAN0_MAM6    (*(RwReg*)0xF000C2C4U) /**< \brief (CAN0) Mailbox Acceptance Mask Register (MB = 6) */
#define REG_CAN0_MID6    (*(RwReg*)0xF000C2C8U) /**< \brief (CAN0) Mailbox ID Register (MB = 6) */
#define REG_CAN0_MFID6   (*(RoReg*)0xF000C2CCU) /**< \brief (CAN0) Mailbox Family ID Register (MB = 6) */
#define REG_CAN0_MSR6    (*(RoReg*)0xF000C2D0U) /**< \brief (CAN0) Mailbox Status Register (MB = 6) */
#define REG_CAN0_MDL6    (*(RwReg*)0xF000C2D4U) /**< \brief (CAN0) Mailbox Data Low Register (MB = 6) */
#define REG_CAN0_MDH6    (*(RwReg*)0xF000C2D8U) /**< \brief (CAN0) Mailbox Data High Register (MB = 6) */
#define REG_CAN0_MCR6    (*(WoReg*)0xF000C2DCU) /**< \brief (CAN0) Mailbox Control Register (MB = 6) */
#define REG_CAN0_MMR7    (*(RwReg*)0xF000C2E0U) /**< \brief (CAN0) Mailbox Mode Register (MB = 7) */
#define REG_CAN0_MAM7    (*(RwReg*)0xF000C2E4U) /**< \brief (CAN0) Mailbox Acceptance Mask Register (MB = 7) */
#define REG_CAN0_MID7    (*(RwReg*)0xF000C2E8U) /**< \brief (CAN0) Mailbox ID Register (MB = 7) */
#define REG_CAN0_MFID7   (*(RoReg*)0xF000C2ECU) /**< \brief (CAN0) Mailbox Family ID Register (MB = 7) */
#define REG_CAN0_MSR7    (*(RoReg*)0xF000C2F0U) /**< \brief (CAN0) Mailbox Status Register (MB = 7) */
#define REG_CAN0_MDL7    (*(RwReg*)0xF000C2F4U) /**< \brief (CAN0) Mailbox Data Low Register (MB = 7) */
#define REG_CAN0_MDH7    (*(RwReg*)0xF000C2F8U) /**< \brief (CAN0) Mailbox Data High Register (MB = 7) */
#define REG_CAN0_MCR7    (*(WoReg*)0xF000C2FCU) /**< \brief (CAN0) Mailbox Control Register (MB = 7) */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAMA5_CAN0_INSTANCE_ */
