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

#ifndef _SAMA5_PWM_INSTANCE_
#define _SAMA5_PWM_INSTANCE_

/* ========== Register definition for PWM peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
#define REG_PWM_CLK               (0xF002C000U) /**< \brief (PWM) PWM Clock Register */
#define REG_PWM_ENA               (0xF002C004U) /**< \brief (PWM) PWM Enable Register */
#define REG_PWM_DIS               (0xF002C008U) /**< \brief (PWM) PWM Disable Register */
#define REG_PWM_SR                (0xF002C00CU) /**< \brief (PWM) PWM Status Register */
#define REG_PWM_IER1              (0xF002C010U) /**< \brief (PWM) PWM Interrupt Enable Register 1 */
#define REG_PWM_IDR1              (0xF002C014U) /**< \brief (PWM) PWM Interrupt Disable Register 1 */
#define REG_PWM_IMR1              (0xF002C018U) /**< \brief (PWM) PWM Interrupt Mask Register 1 */
#define REG_PWM_ISR1              (0xF002C01CU) /**< \brief (PWM) PWM Interrupt Status Register 1 */
#define REG_PWM_SCM               (0xF002C020U) /**< \brief (PWM) PWM Sync Channels Mode Register */
#define REG_PWM_SCUC              (0xF002C028U) /**< \brief (PWM) PWM Sync Channels Update Control Register */
#define REG_PWM_SCUP              (0xF002C02CU) /**< \brief (PWM) PWM Sync Channels Update Period Register */
#define REG_PWM_SCUPUPD           (0xF002C030U) /**< \brief (PWM) PWM Sync Channels Update Period Update Register */
#define REG_PWM_IER2              (0xF002C034U) /**< \brief (PWM) PWM Interrupt Enable Register 2 */
#define REG_PWM_IDR2              (0xF002C038U) /**< \brief (PWM) PWM Interrupt Disable Register 2 */
#define REG_PWM_IMR2              (0xF002C03CU) /**< \brief (PWM) PWM Interrupt Mask Register 2 */
#define REG_PWM_ISR2              (0xF002C040U) /**< \brief (PWM) PWM Interrupt Status Register 2 */
#define REG_PWM_OOV               (0xF002C044U) /**< \brief (PWM) PWM Output Override Value Register */
#define REG_PWM_OS                (0xF002C048U) /**< \brief (PWM) PWM Output Selection Register */
#define REG_PWM_OSS               (0xF002C04CU) /**< \brief (PWM) PWM Output Selection Set Register */
#define REG_PWM_OSC               (0xF002C050U) /**< \brief (PWM) PWM Output Selection Clear Register */
#define REG_PWM_OSSUPD            (0xF002C054U) /**< \brief (PWM) PWM Output Selection Set Update Register */
#define REG_PWM_OSCUPD            (0xF002C058U) /**< \brief (PWM) PWM Output Selection Clear Update Register */
#define REG_PWM_FMR               (0xF002C05CU) /**< \brief (PWM) PWM Fault Mode Register */
#define REG_PWM_FSR               (0xF002C060U) /**< \brief (PWM) PWM Fault Status Register */
#define REG_PWM_FCR               (0xF002C064U) /**< \brief (PWM) PWM Fault Clear Register */
#define REG_PWM_FPV1              (0xF002C068U) /**< \brief (PWM) PWM Fault Protection Value Register 1 */
#define REG_PWM_FPE               (0xF002C06CU) /**< \brief (PWM) PWM Fault Protection Enable Register */
#define REG_PWM_ELMR              (0xF002C07CU) /**< \brief (PWM) PWM Event Line 0 Mode Register */
#define REG_PWM_FPV2              (0xF002C0C0U) /**< \brief (PWM) PWM Fault Protection Value 2 Register */
#define REG_PWM_WPCR              (0xF002C0E4U) /**< \brief (PWM) PWM Write Protect Control Register */
#define REG_PWM_WPSR              (0xF002C0E8U) /**< \brief (PWM) PWM Write Protect Status Register */
#define REG_PWM_CMPV0             (0xF002C130U) /**< \brief (PWM) PWM Comparison 0 Value Register */
#define REG_PWM_CMPVUPD0          (0xF002C134U) /**< \brief (PWM) PWM Comparison 0 Value Update Register */
#define REG_PWM_CMPM0             (0xF002C138U) /**< \brief (PWM) PWM Comparison 0 Mode Register */
#define REG_PWM_CMPMUPD0          (0xF002C13CU) /**< \brief (PWM) PWM Comparison 0 Mode Update Register */
#define REG_PWM_CMPV1             (0xF002C140U) /**< \brief (PWM) PWM Comparison 1 Value Register */
#define REG_PWM_CMPVUPD1          (0xF002C144U) /**< \brief (PWM) PWM Comparison 1 Value Update Register */
#define REG_PWM_CMPM1             (0xF002C148U) /**< \brief (PWM) PWM Comparison 1 Mode Register */
#define REG_PWM_CMPMUPD1          (0xF002C14CU) /**< \brief (PWM) PWM Comparison 1 Mode Update Register */
#define REG_PWM_CMPV2             (0xF002C150U) /**< \brief (PWM) PWM Comparison 2 Value Register */
#define REG_PWM_CMPVUPD2          (0xF002C154U) /**< \brief (PWM) PWM Comparison 2 Value Update Register */
#define REG_PWM_CMPM2             (0xF002C158U) /**< \brief (PWM) PWM Comparison 2 Mode Register */
#define REG_PWM_CMPMUPD2          (0xF002C15CU) /**< \brief (PWM) PWM Comparison 2 Mode Update Register */
#define REG_PWM_CMPV3             (0xF002C160U) /**< \brief (PWM) PWM Comparison 3 Value Register */
#define REG_PWM_CMPVUPD3          (0xF002C164U) /**< \brief (PWM) PWM Comparison 3 Value Update Register */
#define REG_PWM_CMPM3             (0xF002C168U) /**< \brief (PWM) PWM Comparison 3 Mode Register */
#define REG_PWM_CMPMUPD3          (0xF002C16CU) /**< \brief (PWM) PWM Comparison 3 Mode Update Register */
#define REG_PWM_CMPV4             (0xF002C170U) /**< \brief (PWM) PWM Comparison 4 Value Register */
#define REG_PWM_CMPVUPD4          (0xF002C174U) /**< \brief (PWM) PWM Comparison 4 Value Update Register */
#define REG_PWM_CMPM4             (0xF002C178U) /**< \brief (PWM) PWM Comparison 4 Mode Register */
#define REG_PWM_CMPMUPD4          (0xF002C17CU) /**< \brief (PWM) PWM Comparison 4 Mode Update Register */
#define REG_PWM_CMPV5             (0xF002C180U) /**< \brief (PWM) PWM Comparison 5 Value Register */
#define REG_PWM_CMPVUPD5          (0xF002C184U) /**< \brief (PWM) PWM Comparison 5 Value Update Register */
#define REG_PWM_CMPM5             (0xF002C188U) /**< \brief (PWM) PWM Comparison 5 Mode Register */
#define REG_PWM_CMPMUPD5          (0xF002C18CU) /**< \brief (PWM) PWM Comparison 5 Mode Update Register */
#define REG_PWM_CMPV6             (0xF002C190U) /**< \brief (PWM) PWM Comparison 6 Value Register */
#define REG_PWM_CMPVUPD6          (0xF002C194U) /**< \brief (PWM) PWM Comparison 6 Value Update Register */
#define REG_PWM_CMPM6             (0xF002C198U) /**< \brief (PWM) PWM Comparison 6 Mode Register */
#define REG_PWM_CMPMUPD6          (0xF002C19CU) /**< \brief (PWM) PWM Comparison 6 Mode Update Register */
#define REG_PWM_CMPV7             (0xF002C1A0U) /**< \brief (PWM) PWM Comparison 7 Value Register */
#define REG_PWM_CMPVUPD7          (0xF002C1A4U) /**< \brief (PWM) PWM Comparison 7 Value Update Register */
#define REG_PWM_CMPM7             (0xF002C1A8U) /**< \brief (PWM) PWM Comparison 7 Mode Register */
#define REG_PWM_CMPMUPD7          (0xF002C1ACU) /**< \brief (PWM) PWM Comparison 7 Mode Update Register */
#define REG_PWM_CMR0              (0xF002C200U) /**< \brief (PWM) PWM Channel Mode Register (ch_num = 0) */
#define REG_PWM_CDTY0             (0xF002C204U) /**< \brief (PWM) PWM Channel Duty Cycle Register (ch_num = 0) */
#define REG_PWM_CDTYUPD0          (0xF002C208U) /**< \brief (PWM) PWM Channel Duty Cycle Update Register (ch_num = 0) */
#define REG_PWM_CPRD0             (0xF002C20CU) /**< \brief (PWM) PWM Channel Period Register (ch_num = 0) */
#define REG_PWM_CPRDUPD0          (0xF002C210U) /**< \brief (PWM) PWM Channel Period Update Register (ch_num = 0) */
#define REG_PWM_CCNT0             (0xF002C214U) /**< \brief (PWM) PWM Channel Counter Register (ch_num = 0) */
#define REG_PWM_DT0               (0xF002C218U) /**< \brief (PWM) PWM Channel Dead Time Register (ch_num = 0) */
#define REG_PWM_DTUPD0            (0xF002C21CU) /**< \brief (PWM) PWM Channel Dead Time Update Register (ch_num = 0) */
#define REG_PWM_CMR1              (0xF002C220U) /**< \brief (PWM) PWM Channel Mode Register (ch_num = 1) */
#define REG_PWM_CDTY1             (0xF002C224U) /**< \brief (PWM) PWM Channel Duty Cycle Register (ch_num = 1) */
#define REG_PWM_CDTYUPD1          (0xF002C228U) /**< \brief (PWM) PWM Channel Duty Cycle Update Register (ch_num = 1) */
#define REG_PWM_CPRD1             (0xF002C22CU) /**< \brief (PWM) PWM Channel Period Register (ch_num = 1) */
#define REG_PWM_CPRDUPD1          (0xF002C230U) /**< \brief (PWM) PWM Channel Period Update Register (ch_num = 1) */
#define REG_PWM_CCNT1             (0xF002C234U) /**< \brief (PWM) PWM Channel Counter Register (ch_num = 1) */
#define REG_PWM_DT1               (0xF002C238U) /**< \brief (PWM) PWM Channel Dead Time Register (ch_num = 1) */
#define REG_PWM_DTUPD1            (0xF002C23CU) /**< \brief (PWM) PWM Channel Dead Time Update Register (ch_num = 1) */
#define REG_PWM_CMR2              (0xF002C240U) /**< \brief (PWM) PWM Channel Mode Register (ch_num = 2) */
#define REG_PWM_CDTY2             (0xF002C244U) /**< \brief (PWM) PWM Channel Duty Cycle Register (ch_num = 2) */
#define REG_PWM_CDTYUPD2          (0xF002C248U) /**< \brief (PWM) PWM Channel Duty Cycle Update Register (ch_num = 2) */
#define REG_PWM_CPRD2             (0xF002C24CU) /**< \brief (PWM) PWM Channel Period Register (ch_num = 2) */
#define REG_PWM_CPRDUPD2          (0xF002C250U) /**< \brief (PWM) PWM Channel Period Update Register (ch_num = 2) */
#define REG_PWM_CCNT2             (0xF002C254U) /**< \brief (PWM) PWM Channel Counter Register (ch_num = 2) */
#define REG_PWM_DT2               (0xF002C258U) /**< \brief (PWM) PWM Channel Dead Time Register (ch_num = 2) */
#define REG_PWM_DTUPD2            (0xF002C25CU) /**< \brief (PWM) PWM Channel Dead Time Update Register (ch_num = 2) */
#define REG_PWM_CMR3              (0xF002C260U) /**< \brief (PWM) PWM Channel Mode Register (ch_num = 3) */
#define REG_PWM_CDTY3             (0xF002C264U) /**< \brief (PWM) PWM Channel Duty Cycle Register (ch_num = 3) */
#define REG_PWM_CDTYUPD3          (0xF002C268U) /**< \brief (PWM) PWM Channel Duty Cycle Update Register (ch_num = 3) */
#define REG_PWM_CPRD3             (0xF002C26CU) /**< \brief (PWM) PWM Channel Period Register (ch_num = 3) */
#define REG_PWM_CPRDUPD3          (0xF002C270U) /**< \brief (PWM) PWM Channel Period Update Register (ch_num = 3) */
#define REG_PWM_CCNT3             (0xF002C274U) /**< \brief (PWM) PWM Channel Counter Register (ch_num = 3) */
#define REG_PWM_DT3               (0xF002C278U) /**< \brief (PWM) PWM Channel Dead Time Register (ch_num = 3) */
#define REG_PWM_DTUPD3            (0xF002C27CU) /**< \brief (PWM) PWM Channel Dead Time Update Register (ch_num = 3) */
#define REG_PWM_CMUPD0            (0xF002C400U) /**< \brief (PWM) PWM Channel Mode Update Register (ch_num = 0) */
#define REG_PWM_CMUPD1            (0xF002C420U) /**< \brief (PWM) PWM Channel Mode Update Register (ch_num = 1) */
#define REG_PWM_CMUPD2            (0xF002C440U) /**< \brief (PWM) PWM Channel Mode Update Register (ch_num = 2) */
#define REG_PWM_CMUPD3            (0xF002C460U) /**< \brief (PWM) PWM Channel Mode Update Register (ch_num = 3) */
#else
#define REG_PWM_CLK      (*(RwReg*)0xF002C000U) /**< \brief (PWM) PWM Clock Register */
#define REG_PWM_ENA      (*(WoReg*)0xF002C004U) /**< \brief (PWM) PWM Enable Register */
#define REG_PWM_DIS      (*(WoReg*)0xF002C008U) /**< \brief (PWM) PWM Disable Register */
#define REG_PWM_SR       (*(RoReg*)0xF002C00CU) /**< \brief (PWM) PWM Status Register */
#define REG_PWM_IER1     (*(WoReg*)0xF002C010U) /**< \brief (PWM) PWM Interrupt Enable Register 1 */
#define REG_PWM_IDR1     (*(WoReg*)0xF002C014U) /**< \brief (PWM) PWM Interrupt Disable Register 1 */
#define REG_PWM_IMR1     (*(RoReg*)0xF002C018U) /**< \brief (PWM) PWM Interrupt Mask Register 1 */
#define REG_PWM_ISR1     (*(RoReg*)0xF002C01CU) /**< \brief (PWM) PWM Interrupt Status Register 1 */
#define REG_PWM_SCM      (*(RwReg*)0xF002C020U) /**< \brief (PWM) PWM Sync Channels Mode Register */
#define REG_PWM_SCUC     (*(RwReg*)0xF002C028U) /**< \brief (PWM) PWM Sync Channels Update Control Register */
#define REG_PWM_SCUP     (*(RwReg*)0xF002C02CU) /**< \brief (PWM) PWM Sync Channels Update Period Register */
#define REG_PWM_SCUPUPD  (*(WoReg*)0xF002C030U) /**< \brief (PWM) PWM Sync Channels Update Period Update Register */
#define REG_PWM_IER2     (*(WoReg*)0xF002C034U) /**< \brief (PWM) PWM Interrupt Enable Register 2 */
#define REG_PWM_IDR2     (*(WoReg*)0xF002C038U) /**< \brief (PWM) PWM Interrupt Disable Register 2 */
#define REG_PWM_IMR2     (*(RoReg*)0xF002C03CU) /**< \brief (PWM) PWM Interrupt Mask Register 2 */
#define REG_PWM_ISR2     (*(RoReg*)0xF002C040U) /**< \brief (PWM) PWM Interrupt Status Register 2 */
#define REG_PWM_OOV      (*(RwReg*)0xF002C044U) /**< \brief (PWM) PWM Output Override Value Register */
#define REG_PWM_OS       (*(RwReg*)0xF002C048U) /**< \brief (PWM) PWM Output Selection Register */
#define REG_PWM_OSS      (*(WoReg*)0xF002C04CU) /**< \brief (PWM) PWM Output Selection Set Register */
#define REG_PWM_OSC      (*(WoReg*)0xF002C050U) /**< \brief (PWM) PWM Output Selection Clear Register */
#define REG_PWM_OSSUPD   (*(WoReg*)0xF002C054U) /**< \brief (PWM) PWM Output Selection Set Update Register */
#define REG_PWM_OSCUPD   (*(WoReg*)0xF002C058U) /**< \brief (PWM) PWM Output Selection Clear Update Register */
#define REG_PWM_FMR      (*(RwReg*)0xF002C05CU) /**< \brief (PWM) PWM Fault Mode Register */
#define REG_PWM_FSR      (*(RoReg*)0xF002C060U) /**< \brief (PWM) PWM Fault Status Register */
#define REG_PWM_FCR      (*(WoReg*)0xF002C064U) /**< \brief (PWM) PWM Fault Clear Register */
#define REG_PWM_FPV1     (*(RwReg*)0xF002C068U) /**< \brief (PWM) PWM Fault Protection Value Register 1 */
#define REG_PWM_FPE      (*(RwReg*)0xF002C06CU) /**< \brief (PWM) PWM Fault Protection Enable Register */
#define REG_PWM_ELMR     (*(RwReg*)0xF002C07CU) /**< \brief (PWM) PWM Event Line 0 Mode Register */
#define REG_PWM_FPV2     (*(RwReg*)0xF002C0C0U) /**< \brief (PWM) PWM Fault Protection Value 2 Register */
#define REG_PWM_WPCR     (*(WoReg*)0xF002C0E4U) /**< \brief (PWM) PWM Write Protect Control Register */
#define REG_PWM_WPSR     (*(RoReg*)0xF002C0E8U) /**< \brief (PWM) PWM Write Protect Status Register */
#define REG_PWM_CMPV0    (*(RwReg*)0xF002C130U) /**< \brief (PWM) PWM Comparison 0 Value Register */
#define REG_PWM_CMPVUPD0 (*(WoReg*)0xF002C134U) /**< \brief (PWM) PWM Comparison 0 Value Update Register */
#define REG_PWM_CMPM0    (*(RwReg*)0xF002C138U) /**< \brief (PWM) PWM Comparison 0 Mode Register */
#define REG_PWM_CMPMUPD0 (*(WoReg*)0xF002C13CU) /**< \brief (PWM) PWM Comparison 0 Mode Update Register */
#define REG_PWM_CMPV1    (*(RwReg*)0xF002C140U) /**< \brief (PWM) PWM Comparison 1 Value Register */
#define REG_PWM_CMPVUPD1 (*(WoReg*)0xF002C144U) /**< \brief (PWM) PWM Comparison 1 Value Update Register */
#define REG_PWM_CMPM1    (*(RwReg*)0xF002C148U) /**< \brief (PWM) PWM Comparison 1 Mode Register */
#define REG_PWM_CMPMUPD1 (*(WoReg*)0xF002C14CU) /**< \brief (PWM) PWM Comparison 1 Mode Update Register */
#define REG_PWM_CMPV2    (*(RwReg*)0xF002C150U) /**< \brief (PWM) PWM Comparison 2 Value Register */
#define REG_PWM_CMPVUPD2 (*(WoReg*)0xF002C154U) /**< \brief (PWM) PWM Comparison 2 Value Update Register */
#define REG_PWM_CMPM2    (*(RwReg*)0xF002C158U) /**< \brief (PWM) PWM Comparison 2 Mode Register */
#define REG_PWM_CMPMUPD2 (*(WoReg*)0xF002C15CU) /**< \brief (PWM) PWM Comparison 2 Mode Update Register */
#define REG_PWM_CMPV3    (*(RwReg*)0xF002C160U) /**< \brief (PWM) PWM Comparison 3 Value Register */
#define REG_PWM_CMPVUPD3 (*(WoReg*)0xF002C164U) /**< \brief (PWM) PWM Comparison 3 Value Update Register */
#define REG_PWM_CMPM3    (*(RwReg*)0xF002C168U) /**< \brief (PWM) PWM Comparison 3 Mode Register */
#define REG_PWM_CMPMUPD3 (*(WoReg*)0xF002C16CU) /**< \brief (PWM) PWM Comparison 3 Mode Update Register */
#define REG_PWM_CMPV4    (*(RwReg*)0xF002C170U) /**< \brief (PWM) PWM Comparison 4 Value Register */
#define REG_PWM_CMPVUPD4 (*(WoReg*)0xF002C174U) /**< \brief (PWM) PWM Comparison 4 Value Update Register */
#define REG_PWM_CMPM4    (*(RwReg*)0xF002C178U) /**< \brief (PWM) PWM Comparison 4 Mode Register */
#define REG_PWM_CMPMUPD4 (*(WoReg*)0xF002C17CU) /**< \brief (PWM) PWM Comparison 4 Mode Update Register */
#define REG_PWM_CMPV5    (*(RwReg*)0xF002C180U) /**< \brief (PWM) PWM Comparison 5 Value Register */
#define REG_PWM_CMPVUPD5 (*(WoReg*)0xF002C184U) /**< \brief (PWM) PWM Comparison 5 Value Update Register */
#define REG_PWM_CMPM5    (*(RwReg*)0xF002C188U) /**< \brief (PWM) PWM Comparison 5 Mode Register */
#define REG_PWM_CMPMUPD5 (*(WoReg*)0xF002C18CU) /**< \brief (PWM) PWM Comparison 5 Mode Update Register */
#define REG_PWM_CMPV6    (*(RwReg*)0xF002C190U) /**< \brief (PWM) PWM Comparison 6 Value Register */
#define REG_PWM_CMPVUPD6 (*(WoReg*)0xF002C194U) /**< \brief (PWM) PWM Comparison 6 Value Update Register */
#define REG_PWM_CMPM6    (*(RwReg*)0xF002C198U) /**< \brief (PWM) PWM Comparison 6 Mode Register */
#define REG_PWM_CMPMUPD6 (*(WoReg*)0xF002C19CU) /**< \brief (PWM) PWM Comparison 6 Mode Update Register */
#define REG_PWM_CMPV7    (*(RwReg*)0xF002C1A0U) /**< \brief (PWM) PWM Comparison 7 Value Register */
#define REG_PWM_CMPVUPD7 (*(WoReg*)0xF002C1A4U) /**< \brief (PWM) PWM Comparison 7 Value Update Register */
#define REG_PWM_CMPM7    (*(RwReg*)0xF002C1A8U) /**< \brief (PWM) PWM Comparison 7 Mode Register */
#define REG_PWM_CMPMUPD7 (*(WoReg*)0xF002C1ACU) /**< \brief (PWM) PWM Comparison 7 Mode Update Register */
#define REG_PWM_CMR0     (*(RwReg*)0xF002C200U) /**< \brief (PWM) PWM Channel Mode Register (ch_num = 0) */
#define REG_PWM_CDTY0    (*(RwReg*)0xF002C204U) /**< \brief (PWM) PWM Channel Duty Cycle Register (ch_num = 0) */
#define REG_PWM_CDTYUPD0 (*(WoReg*)0xF002C208U) /**< \brief (PWM) PWM Channel Duty Cycle Update Register (ch_num = 0) */
#define REG_PWM_CPRD0    (*(RwReg*)0xF002C20CU) /**< \brief (PWM) PWM Channel Period Register (ch_num = 0) */
#define REG_PWM_CPRDUPD0 (*(WoReg*)0xF002C210U) /**< \brief (PWM) PWM Channel Period Update Register (ch_num = 0) */
#define REG_PWM_CCNT0    (*(RoReg*)0xF002C214U) /**< \brief (PWM) PWM Channel Counter Register (ch_num = 0) */
#define REG_PWM_DT0      (*(RwReg*)0xF002C218U) /**< \brief (PWM) PWM Channel Dead Time Register (ch_num = 0) */
#define REG_PWM_DTUPD0   (*(WoReg*)0xF002C21CU) /**< \brief (PWM) PWM Channel Dead Time Update Register (ch_num = 0) */
#define REG_PWM_CMR1     (*(RwReg*)0xF002C220U) /**< \brief (PWM) PWM Channel Mode Register (ch_num = 1) */
#define REG_PWM_CDTY1    (*(RwReg*)0xF002C224U) /**< \brief (PWM) PWM Channel Duty Cycle Register (ch_num = 1) */
#define REG_PWM_CDTYUPD1 (*(WoReg*)0xF002C228U) /**< \brief (PWM) PWM Channel Duty Cycle Update Register (ch_num = 1) */
#define REG_PWM_CPRD1    (*(RwReg*)0xF002C22CU) /**< \brief (PWM) PWM Channel Period Register (ch_num = 1) */
#define REG_PWM_CPRDUPD1 (*(WoReg*)0xF002C230U) /**< \brief (PWM) PWM Channel Period Update Register (ch_num = 1) */
#define REG_PWM_CCNT1    (*(RoReg*)0xF002C234U) /**< \brief (PWM) PWM Channel Counter Register (ch_num = 1) */
#define REG_PWM_DT1      (*(RwReg*)0xF002C238U) /**< \brief (PWM) PWM Channel Dead Time Register (ch_num = 1) */
#define REG_PWM_DTUPD1   (*(WoReg*)0xF002C23CU) /**< \brief (PWM) PWM Channel Dead Time Update Register (ch_num = 1) */
#define REG_PWM_CMR2     (*(RwReg*)0xF002C240U) /**< \brief (PWM) PWM Channel Mode Register (ch_num = 2) */
#define REG_PWM_CDTY2    (*(RwReg*)0xF002C244U) /**< \brief (PWM) PWM Channel Duty Cycle Register (ch_num = 2) */
#define REG_PWM_CDTYUPD2 (*(WoReg*)0xF002C248U) /**< \brief (PWM) PWM Channel Duty Cycle Update Register (ch_num = 2) */
#define REG_PWM_CPRD2    (*(RwReg*)0xF002C24CU) /**< \brief (PWM) PWM Channel Period Register (ch_num = 2) */
#define REG_PWM_CPRDUPD2 (*(WoReg*)0xF002C250U) /**< \brief (PWM) PWM Channel Period Update Register (ch_num = 2) */
#define REG_PWM_CCNT2    (*(RoReg*)0xF002C254U) /**< \brief (PWM) PWM Channel Counter Register (ch_num = 2) */
#define REG_PWM_DT2      (*(RwReg*)0xF002C258U) /**< \brief (PWM) PWM Channel Dead Time Register (ch_num = 2) */
#define REG_PWM_DTUPD2   (*(WoReg*)0xF002C25CU) /**< \brief (PWM) PWM Channel Dead Time Update Register (ch_num = 2) */
#define REG_PWM_CMR3     (*(RwReg*)0xF002C260U) /**< \brief (PWM) PWM Channel Mode Register (ch_num = 3) */
#define REG_PWM_CDTY3    (*(RwReg*)0xF002C264U) /**< \brief (PWM) PWM Channel Duty Cycle Register (ch_num = 3) */
#define REG_PWM_CDTYUPD3 (*(WoReg*)0xF002C268U) /**< \brief (PWM) PWM Channel Duty Cycle Update Register (ch_num = 3) */
#define REG_PWM_CPRD3    (*(RwReg*)0xF002C26CU) /**< \brief (PWM) PWM Channel Period Register (ch_num = 3) */
#define REG_PWM_CPRDUPD3 (*(WoReg*)0xF002C270U) /**< \brief (PWM) PWM Channel Period Update Register (ch_num = 3) */
#define REG_PWM_CCNT3    (*(RoReg*)0xF002C274U) /**< \brief (PWM) PWM Channel Counter Register (ch_num = 3) */
#define REG_PWM_DT3      (*(RwReg*)0xF002C278U) /**< \brief (PWM) PWM Channel Dead Time Register (ch_num = 3) */
#define REG_PWM_DTUPD3   (*(WoReg*)0xF002C27CU) /**< \brief (PWM) PWM Channel Dead Time Update Register (ch_num = 3) */
#define REG_PWM_CMUPD0   (*(WoReg*)0xF002C400U) /**< \brief (PWM) PWM Channel Mode Update Register (ch_num = 0) */
#define REG_PWM_CMUPD1   (*(WoReg*)0xF002C420U) /**< \brief (PWM) PWM Channel Mode Update Register (ch_num = 1) */
#define REG_PWM_CMUPD2   (*(WoReg*)0xF002C440U) /**< \brief (PWM) PWM Channel Mode Update Register (ch_num = 2) */
#define REG_PWM_CMUPD3   (*(WoReg*)0xF002C460U) /**< \brief (PWM) PWM Channel Mode Update Register (ch_num = 3) */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAMA5_PWM_INSTANCE_ */
