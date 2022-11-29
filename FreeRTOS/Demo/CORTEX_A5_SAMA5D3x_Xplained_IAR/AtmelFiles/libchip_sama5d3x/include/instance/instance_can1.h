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

#ifndef _SAMA5_CAN1_INSTANCE_
#define _SAMA5_CAN1_INSTANCE_

/* ========== Register definition for CAN1 peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
#define REG_CAN1_MR               (0xF8010000U) /**< \brief (CAN1) Mode Register */
#define REG_CAN1_IER              (0xF8010004U) /**< \brief (CAN1) Interrupt Enable Register */
#define REG_CAN1_IDR              (0xF8010008U) /**< \brief (CAN1) Interrupt Disable Register */
#define REG_CAN1_IMR              (0xF801000CU) /**< \brief (CAN1) Interrupt Mask Register */
#define REG_CAN1_SR               (0xF8010010U) /**< \brief (CAN1) Status Register */
#define REG_CAN1_BR               (0xF8010014U) /**< \brief (CAN1) Baudrate Register */
#define REG_CAN1_TIM              (0xF8010018U) /**< \brief (CAN1) Timer Register */
#define REG_CAN1_TIMESTP          (0xF801001CU) /**< \brief (CAN1) Timestamp Register */
#define REG_CAN1_ECR              (0xF8010020U) /**< \brief (CAN1) Error Counter Register */
#define REG_CAN1_TCR              (0xF8010024U) /**< \brief (CAN1) Transfer Command Register */
#define REG_CAN1_ACR              (0xF8010028U) /**< \brief (CAN1) Abort Command Register */
#define REG_CAN1_WPMR             (0xF80100E4U) /**< \brief (CAN1) Write Protect Mode Register */
#define REG_CAN1_WPSR             (0xF80100E8U) /**< \brief (CAN1) Write Protect Status Register */
#define REG_CAN1_MMR0             (0xF8010200U) /**< \brief (CAN1) Mailbox Mode Register (MB = 0) */
#define REG_CAN1_MAM0             (0xF8010204U) /**< \brief (CAN1) Mailbox Acceptance Mask Register (MB = 0) */
#define REG_CAN1_MID0             (0xF8010208U) /**< \brief (CAN1) Mailbox ID Register (MB = 0) */
#define REG_CAN1_MFID0            (0xF801020CU) /**< \brief (CAN1) Mailbox Family ID Register (MB = 0) */
#define REG_CAN1_MSR0             (0xF8010210U) /**< \brief (CAN1) Mailbox Status Register (MB = 0) */
#define REG_CAN1_MDL0             (0xF8010214U) /**< \brief (CAN1) Mailbox Data Low Register (MB = 0) */
#define REG_CAN1_MDH0             (0xF8010218U) /**< \brief (CAN1) Mailbox Data High Register (MB = 0) */
#define REG_CAN1_MCR0             (0xF801021CU) /**< \brief (CAN1) Mailbox Control Register (MB = 0) */
#define REG_CAN1_MMR1             (0xF8010220U) /**< \brief (CAN1) Mailbox Mode Register (MB = 1) */
#define REG_CAN1_MAM1             (0xF8010224U) /**< \brief (CAN1) Mailbox Acceptance Mask Register (MB = 1) */
#define REG_CAN1_MID1             (0xF8010228U) /**< \brief (CAN1) Mailbox ID Register (MB = 1) */
#define REG_CAN1_MFID1            (0xF801022CU) /**< \brief (CAN1) Mailbox Family ID Register (MB = 1) */
#define REG_CAN1_MSR1             (0xF8010230U) /**< \brief (CAN1) Mailbox Status Register (MB = 1) */
#define REG_CAN1_MDL1             (0xF8010234U) /**< \brief (CAN1) Mailbox Data Low Register (MB = 1) */
#define REG_CAN1_MDH1             (0xF8010238U) /**< \brief (CAN1) Mailbox Data High Register (MB = 1) */
#define REG_CAN1_MCR1             (0xF801023CU) /**< \brief (CAN1) Mailbox Control Register (MB = 1) */
#define REG_CAN1_MMR2             (0xF8010240U) /**< \brief (CAN1) Mailbox Mode Register (MB = 2) */
#define REG_CAN1_MAM2             (0xF8010244U) /**< \brief (CAN1) Mailbox Acceptance Mask Register (MB = 2) */
#define REG_CAN1_MID2             (0xF8010248U) /**< \brief (CAN1) Mailbox ID Register (MB = 2) */
#define REG_CAN1_MFID2            (0xF801024CU) /**< \brief (CAN1) Mailbox Family ID Register (MB = 2) */
#define REG_CAN1_MSR2             (0xF8010250U) /**< \brief (CAN1) Mailbox Status Register (MB = 2) */
#define REG_CAN1_MDL2             (0xF8010254U) /**< \brief (CAN1) Mailbox Data Low Register (MB = 2) */
#define REG_CAN1_MDH2             (0xF8010258U) /**< \brief (CAN1) Mailbox Data High Register (MB = 2) */
#define REG_CAN1_MCR2             (0xF801025CU) /**< \brief (CAN1) Mailbox Control Register (MB = 2) */
#define REG_CAN1_MMR3             (0xF8010260U) /**< \brief (CAN1) Mailbox Mode Register (MB = 3) */
#define REG_CAN1_MAM3             (0xF8010264U) /**< \brief (CAN1) Mailbox Acceptance Mask Register (MB = 3) */
#define REG_CAN1_MID3             (0xF8010268U) /**< \brief (CAN1) Mailbox ID Register (MB = 3) */
#define REG_CAN1_MFID3            (0xF801026CU) /**< \brief (CAN1) Mailbox Family ID Register (MB = 3) */
#define REG_CAN1_MSR3             (0xF8010270U) /**< \brief (CAN1) Mailbox Status Register (MB = 3) */
#define REG_CAN1_MDL3             (0xF8010274U) /**< \brief (CAN1) Mailbox Data Low Register (MB = 3) */
#define REG_CAN1_MDH3             (0xF8010278U) /**< \brief (CAN1) Mailbox Data High Register (MB = 3) */
#define REG_CAN1_MCR3             (0xF801027CU) /**< \brief (CAN1) Mailbox Control Register (MB = 3) */
#define REG_CAN1_MMR4             (0xF8010280U) /**< \brief (CAN1) Mailbox Mode Register (MB = 4) */
#define REG_CAN1_MAM4             (0xF8010284U) /**< \brief (CAN1) Mailbox Acceptance Mask Register (MB = 4) */
#define REG_CAN1_MID4             (0xF8010288U) /**< \brief (CAN1) Mailbox ID Register (MB = 4) */
#define REG_CAN1_MFID4            (0xF801028CU) /**< \brief (CAN1) Mailbox Family ID Register (MB = 4) */
#define REG_CAN1_MSR4             (0xF8010290U) /**< \brief (CAN1) Mailbox Status Register (MB = 4) */
#define REG_CAN1_MDL4             (0xF8010294U) /**< \brief (CAN1) Mailbox Data Low Register (MB = 4) */
#define REG_CAN1_MDH4             (0xF8010298U) /**< \brief (CAN1) Mailbox Data High Register (MB = 4) */
#define REG_CAN1_MCR4             (0xF801029CU) /**< \brief (CAN1) Mailbox Control Register (MB = 4) */
#define REG_CAN1_MMR5             (0xF80102A0U) /**< \brief (CAN1) Mailbox Mode Register (MB = 5) */
#define REG_CAN1_MAM5             (0xF80102A4U) /**< \brief (CAN1) Mailbox Acceptance Mask Register (MB = 5) */
#define REG_CAN1_MID5             (0xF80102A8U) /**< \brief (CAN1) Mailbox ID Register (MB = 5) */
#define REG_CAN1_MFID5            (0xF80102ACU) /**< \brief (CAN1) Mailbox Family ID Register (MB = 5) */
#define REG_CAN1_MSR5             (0xF80102B0U) /**< \brief (CAN1) Mailbox Status Register (MB = 5) */
#define REG_CAN1_MDL5             (0xF80102B4U) /**< \brief (CAN1) Mailbox Data Low Register (MB = 5) */
#define REG_CAN1_MDH5             (0xF80102B8U) /**< \brief (CAN1) Mailbox Data High Register (MB = 5) */
#define REG_CAN1_MCR5             (0xF80102BCU) /**< \brief (CAN1) Mailbox Control Register (MB = 5) */
#define REG_CAN1_MMR6             (0xF80102C0U) /**< \brief (CAN1) Mailbox Mode Register (MB = 6) */
#define REG_CAN1_MAM6             (0xF80102C4U) /**< \brief (CAN1) Mailbox Acceptance Mask Register (MB = 6) */
#define REG_CAN1_MID6             (0xF80102C8U) /**< \brief (CAN1) Mailbox ID Register (MB = 6) */
#define REG_CAN1_MFID6            (0xF80102CCU) /**< \brief (CAN1) Mailbox Family ID Register (MB = 6) */
#define REG_CAN1_MSR6             (0xF80102D0U) /**< \brief (CAN1) Mailbox Status Register (MB = 6) */
#define REG_CAN1_MDL6             (0xF80102D4U) /**< \brief (CAN1) Mailbox Data Low Register (MB = 6) */
#define REG_CAN1_MDH6             (0xF80102D8U) /**< \brief (CAN1) Mailbox Data High Register (MB = 6) */
#define REG_CAN1_MCR6             (0xF80102DCU) /**< \brief (CAN1) Mailbox Control Register (MB = 6) */
#define REG_CAN1_MMR7             (0xF80102E0U) /**< \brief (CAN1) Mailbox Mode Register (MB = 7) */
#define REG_CAN1_MAM7             (0xF80102E4U) /**< \brief (CAN1) Mailbox Acceptance Mask Register (MB = 7) */
#define REG_CAN1_MID7             (0xF80102E8U) /**< \brief (CAN1) Mailbox ID Register (MB = 7) */
#define REG_CAN1_MFID7            (0xF80102ECU) /**< \brief (CAN1) Mailbox Family ID Register (MB = 7) */
#define REG_CAN1_MSR7             (0xF80102F0U) /**< \brief (CAN1) Mailbox Status Register (MB = 7) */
#define REG_CAN1_MDL7             (0xF80102F4U) /**< \brief (CAN1) Mailbox Data Low Register (MB = 7) */
#define REG_CAN1_MDH7             (0xF80102F8U) /**< \brief (CAN1) Mailbox Data High Register (MB = 7) */
#define REG_CAN1_MCR7             (0xF80102FCU) /**< \brief (CAN1) Mailbox Control Register (MB = 7) */
#else
#define REG_CAN1_MR      (*(RwReg*)0xF8010000U) /**< \brief (CAN1) Mode Register */
#define REG_CAN1_IER     (*(WoReg*)0xF8010004U) /**< \brief (CAN1) Interrupt Enable Register */
#define REG_CAN1_IDR     (*(WoReg*)0xF8010008U) /**< \brief (CAN1) Interrupt Disable Register */
#define REG_CAN1_IMR     (*(RoReg*)0xF801000CU) /**< \brief (CAN1) Interrupt Mask Register */
#define REG_CAN1_SR      (*(RoReg*)0xF8010010U) /**< \brief (CAN1) Status Register */
#define REG_CAN1_BR      (*(RwReg*)0xF8010014U) /**< \brief (CAN1) Baudrate Register */
#define REG_CAN1_TIM     (*(RoReg*)0xF8010018U) /**< \brief (CAN1) Timer Register */
#define REG_CAN1_TIMESTP (*(RoReg*)0xF801001CU) /**< \brief (CAN1) Timestamp Register */
#define REG_CAN1_ECR     (*(RoReg*)0xF8010020U) /**< \brief (CAN1) Error Counter Register */
#define REG_CAN1_TCR     (*(WoReg*)0xF8010024U) /**< \brief (CAN1) Transfer Command Register */
#define REG_CAN1_ACR     (*(WoReg*)0xF8010028U) /**< \brief (CAN1) Abort Command Register */
#define REG_CAN1_WPMR    (*(RwReg*)0xF80100E4U) /**< \brief (CAN1) Write Protect Mode Register */
#define REG_CAN1_WPSR    (*(RoReg*)0xF80100E8U) /**< \brief (CAN1) Write Protect Status Register */
#define REG_CAN1_MMR0    (*(RwReg*)0xF8010200U) /**< \brief (CAN1) Mailbox Mode Register (MB = 0) */
#define REG_CAN1_MAM0    (*(RwReg*)0xF8010204U) /**< \brief (CAN1) Mailbox Acceptance Mask Register (MB = 0) */
#define REG_CAN1_MID0    (*(RwReg*)0xF8010208U) /**< \brief (CAN1) Mailbox ID Register (MB = 0) */
#define REG_CAN1_MFID0   (*(RoReg*)0xF801020CU) /**< \brief (CAN1) Mailbox Family ID Register (MB = 0) */
#define REG_CAN1_MSR0    (*(RoReg*)0xF8010210U) /**< \brief (CAN1) Mailbox Status Register (MB = 0) */
#define REG_CAN1_MDL0    (*(RwReg*)0xF8010214U) /**< \brief (CAN1) Mailbox Data Low Register (MB = 0) */
#define REG_CAN1_MDH0    (*(RwReg*)0xF8010218U) /**< \brief (CAN1) Mailbox Data High Register (MB = 0) */
#define REG_CAN1_MCR0    (*(WoReg*)0xF801021CU) /**< \brief (CAN1) Mailbox Control Register (MB = 0) */
#define REG_CAN1_MMR1    (*(RwReg*)0xF8010220U) /**< \brief (CAN1) Mailbox Mode Register (MB = 1) */
#define REG_CAN1_MAM1    (*(RwReg*)0xF8010224U) /**< \brief (CAN1) Mailbox Acceptance Mask Register (MB = 1) */
#define REG_CAN1_MID1    (*(RwReg*)0xF8010228U) /**< \brief (CAN1) Mailbox ID Register (MB = 1) */
#define REG_CAN1_MFID1   (*(RoReg*)0xF801022CU) /**< \brief (CAN1) Mailbox Family ID Register (MB = 1) */
#define REG_CAN1_MSR1    (*(RoReg*)0xF8010230U) /**< \brief (CAN1) Mailbox Status Register (MB = 1) */
#define REG_CAN1_MDL1    (*(RwReg*)0xF8010234U) /**< \brief (CAN1) Mailbox Data Low Register (MB = 1) */
#define REG_CAN1_MDH1    (*(RwReg*)0xF8010238U) /**< \brief (CAN1) Mailbox Data High Register (MB = 1) */
#define REG_CAN1_MCR1    (*(WoReg*)0xF801023CU) /**< \brief (CAN1) Mailbox Control Register (MB = 1) */
#define REG_CAN1_MMR2    (*(RwReg*)0xF8010240U) /**< \brief (CAN1) Mailbox Mode Register (MB = 2) */
#define REG_CAN1_MAM2    (*(RwReg*)0xF8010244U) /**< \brief (CAN1) Mailbox Acceptance Mask Register (MB = 2) */
#define REG_CAN1_MID2    (*(RwReg*)0xF8010248U) /**< \brief (CAN1) Mailbox ID Register (MB = 2) */
#define REG_CAN1_MFID2   (*(RoReg*)0xF801024CU) /**< \brief (CAN1) Mailbox Family ID Register (MB = 2) */
#define REG_CAN1_MSR2    (*(RoReg*)0xF8010250U) /**< \brief (CAN1) Mailbox Status Register (MB = 2) */
#define REG_CAN1_MDL2    (*(RwReg*)0xF8010254U) /**< \brief (CAN1) Mailbox Data Low Register (MB = 2) */
#define REG_CAN1_MDH2    (*(RwReg*)0xF8010258U) /**< \brief (CAN1) Mailbox Data High Register (MB = 2) */
#define REG_CAN1_MCR2    (*(WoReg*)0xF801025CU) /**< \brief (CAN1) Mailbox Control Register (MB = 2) */
#define REG_CAN1_MMR3    (*(RwReg*)0xF8010260U) /**< \brief (CAN1) Mailbox Mode Register (MB = 3) */
#define REG_CAN1_MAM3    (*(RwReg*)0xF8010264U) /**< \brief (CAN1) Mailbox Acceptance Mask Register (MB = 3) */
#define REG_CAN1_MID3    (*(RwReg*)0xF8010268U) /**< \brief (CAN1) Mailbox ID Register (MB = 3) */
#define REG_CAN1_MFID3   (*(RoReg*)0xF801026CU) /**< \brief (CAN1) Mailbox Family ID Register (MB = 3) */
#define REG_CAN1_MSR3    (*(RoReg*)0xF8010270U) /**< \brief (CAN1) Mailbox Status Register (MB = 3) */
#define REG_CAN1_MDL3    (*(RwReg*)0xF8010274U) /**< \brief (CAN1) Mailbox Data Low Register (MB = 3) */
#define REG_CAN1_MDH3    (*(RwReg*)0xF8010278U) /**< \brief (CAN1) Mailbox Data High Register (MB = 3) */
#define REG_CAN1_MCR3    (*(WoReg*)0xF801027CU) /**< \brief (CAN1) Mailbox Control Register (MB = 3) */
#define REG_CAN1_MMR4    (*(RwReg*)0xF8010280U) /**< \brief (CAN1) Mailbox Mode Register (MB = 4) */
#define REG_CAN1_MAM4    (*(RwReg*)0xF8010284U) /**< \brief (CAN1) Mailbox Acceptance Mask Register (MB = 4) */
#define REG_CAN1_MID4    (*(RwReg*)0xF8010288U) /**< \brief (CAN1) Mailbox ID Register (MB = 4) */
#define REG_CAN1_MFID4   (*(RoReg*)0xF801028CU) /**< \brief (CAN1) Mailbox Family ID Register (MB = 4) */
#define REG_CAN1_MSR4    (*(RoReg*)0xF8010290U) /**< \brief (CAN1) Mailbox Status Register (MB = 4) */
#define REG_CAN1_MDL4    (*(RwReg*)0xF8010294U) /**< \brief (CAN1) Mailbox Data Low Register (MB = 4) */
#define REG_CAN1_MDH4    (*(RwReg*)0xF8010298U) /**< \brief (CAN1) Mailbox Data High Register (MB = 4) */
#define REG_CAN1_MCR4    (*(WoReg*)0xF801029CU) /**< \brief (CAN1) Mailbox Control Register (MB = 4) */
#define REG_CAN1_MMR5    (*(RwReg*)0xF80102A0U) /**< \brief (CAN1) Mailbox Mode Register (MB = 5) */
#define REG_CAN1_MAM5    (*(RwReg*)0xF80102A4U) /**< \brief (CAN1) Mailbox Acceptance Mask Register (MB = 5) */
#define REG_CAN1_MID5    (*(RwReg*)0xF80102A8U) /**< \brief (CAN1) Mailbox ID Register (MB = 5) */
#define REG_CAN1_MFID5   (*(RoReg*)0xF80102ACU) /**< \brief (CAN1) Mailbox Family ID Register (MB = 5) */
#define REG_CAN1_MSR5    (*(RoReg*)0xF80102B0U) /**< \brief (CAN1) Mailbox Status Register (MB = 5) */
#define REG_CAN1_MDL5    (*(RwReg*)0xF80102B4U) /**< \brief (CAN1) Mailbox Data Low Register (MB = 5) */
#define REG_CAN1_MDH5    (*(RwReg*)0xF80102B8U) /**< \brief (CAN1) Mailbox Data High Register (MB = 5) */
#define REG_CAN1_MCR5    (*(WoReg*)0xF80102BCU) /**< \brief (CAN1) Mailbox Control Register (MB = 5) */
#define REG_CAN1_MMR6    (*(RwReg*)0xF80102C0U) /**< \brief (CAN1) Mailbox Mode Register (MB = 6) */
#define REG_CAN1_MAM6    (*(RwReg*)0xF80102C4U) /**< \brief (CAN1) Mailbox Acceptance Mask Register (MB = 6) */
#define REG_CAN1_MID6    (*(RwReg*)0xF80102C8U) /**< \brief (CAN1) Mailbox ID Register (MB = 6) */
#define REG_CAN1_MFID6   (*(RoReg*)0xF80102CCU) /**< \brief (CAN1) Mailbox Family ID Register (MB = 6) */
#define REG_CAN1_MSR6    (*(RoReg*)0xF80102D0U) /**< \brief (CAN1) Mailbox Status Register (MB = 6) */
#define REG_CAN1_MDL6    (*(RwReg*)0xF80102D4U) /**< \brief (CAN1) Mailbox Data Low Register (MB = 6) */
#define REG_CAN1_MDH6    (*(RwReg*)0xF80102D8U) /**< \brief (CAN1) Mailbox Data High Register (MB = 6) */
#define REG_CAN1_MCR6    (*(WoReg*)0xF80102DCU) /**< \brief (CAN1) Mailbox Control Register (MB = 6) */
#define REG_CAN1_MMR7    (*(RwReg*)0xF80102E0U) /**< \brief (CAN1) Mailbox Mode Register (MB = 7) */
#define REG_CAN1_MAM7    (*(RwReg*)0xF80102E4U) /**< \brief (CAN1) Mailbox Acceptance Mask Register (MB = 7) */
#define REG_CAN1_MID7    (*(RwReg*)0xF80102E8U) /**< \brief (CAN1) Mailbox ID Register (MB = 7) */
#define REG_CAN1_MFID7   (*(RoReg*)0xF80102ECU) /**< \brief (CAN1) Mailbox Family ID Register (MB = 7) */
#define REG_CAN1_MSR7    (*(RoReg*)0xF80102F0U) /**< \brief (CAN1) Mailbox Status Register (MB = 7) */
#define REG_CAN1_MDL7    (*(RwReg*)0xF80102F4U) /**< \brief (CAN1) Mailbox Data Low Register (MB = 7) */
#define REG_CAN1_MDH7    (*(RwReg*)0xF80102F8U) /**< \brief (CAN1) Mailbox Data High Register (MB = 7) */
#define REG_CAN1_MCR7    (*(WoReg*)0xF80102FCU) /**< \brief (CAN1) Mailbox Control Register (MB = 7) */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAMA5_CAN1_INSTANCE_ */
