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

#ifndef _SAMA5_EMAC_INSTANCE_
#define _SAMA5_EMAC_INSTANCE_

/* ========== Register definition for EMAC peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
#define REG_EMAC_NCR            (0xF802C000U) /**< \brief (EMAC) Network Control Register */
#define REG_EMAC_NCFGR          (0xF802C004U) /**< \brief (EMAC) Network Configuration Register */
#define REG_EMAC_NSR            (0xF802C008U) /**< \brief (EMAC) Network Status Register */
#define REG_EMAC_TSR            (0xF802C014U) /**< \brief (EMAC) Transmit Status Register */
#define REG_EMAC_RBQP           (0xF802C018U) /**< \brief (EMAC) Receive Buffer Queue Pointer Register */
#define REG_EMAC_TBQP           (0xF802C01CU) /**< \brief (EMAC) Transmit Buffer Queue Pointer Register */
#define REG_EMAC_RSR            (0xF802C020U) /**< \brief (EMAC) Receive Status Register */
#define REG_EMAC_ISR            (0xF802C024U) /**< \brief (EMAC) Interrupt Status Register */
#define REG_EMAC_IER            (0xF802C028U) /**< \brief (EMAC) Interrupt Enable Register */
#define REG_EMAC_IDR            (0xF802C02CU) /**< \brief (EMAC) Interrupt Disable Register */
#define REG_EMAC_IMR            (0xF802C030U) /**< \brief (EMAC) Interrupt Mask Register */
#define REG_EMAC_MAN            (0xF802C034U) /**< \brief (EMAC) Phy Maintenance Register */
#define REG_EMAC_PTR            (0xF802C038U) /**< \brief (EMAC) Pause Time Register */
#define REG_EMAC_PFR            (0xF802C03CU) /**< \brief (EMAC) Pause Frames Received Register */
#define REG_EMAC_FTO            (0xF802C040U) /**< \brief (EMAC) Frames Transmitted Ok Register */
#define REG_EMAC_SCF            (0xF802C044U) /**< \brief (EMAC) Single Collision Frames Register */
#define REG_EMAC_MCF            (0xF802C048U) /**< \brief (EMAC) Multiple Collision Frames Register */
#define REG_EMAC_FRO            (0xF802C04CU) /**< \brief (EMAC) Frames Received Ok Register */
#define REG_EMAC_FCSE           (0xF802C050U) /**< \brief (EMAC) Frame Check Sequence Errors Register */
#define REG_EMAC_ALE            (0xF802C054U) /**< \brief (EMAC) Alignment Errors Register */
#define REG_EMAC_DTF            (0xF802C058U) /**< \brief (EMAC) Deferred Transmission Frames Register */
#define REG_EMAC_LCOL           (0xF802C05CU) /**< \brief (EMAC) Late Collisions Register */
#define REG_EMAC_ECOL           (0xF802C060U) /**< \brief (EMAC) Excessive Collisions Register */
#define REG_EMAC_TUND           (0xF802C064U) /**< \brief (EMAC) Transmit Underrun Errors Register */
#define REG_EMAC_CSE            (0xF802C068U) /**< \brief (EMAC) Carrier Sense Errors Register */
#define REG_EMAC_RRE            (0xF802C06CU) /**< \brief (EMAC) Receive Resource Errors Register */
#define REG_EMAC_ROV            (0xF802C070U) /**< \brief (EMAC) Receive Overrun Errors Register */
#define REG_EMAC_RSE            (0xF802C074U) /**< \brief (EMAC) Receive Symbol Errors Register */
#define REG_EMAC_ELE            (0xF802C078U) /**< \brief (EMAC) Excessive Length Errors Register */
#define REG_EMAC_RJA            (0xF802C07CU) /**< \brief (EMAC) Receive Jabbers Register */
#define REG_EMAC_USF            (0xF802C080U) /**< \brief (EMAC) Undersize Frames Register */
#define REG_EMAC_STE            (0xF802C084U) /**< \brief (EMAC) SQE Test Errors Register */
#define REG_EMAC_RLE            (0xF802C088U) /**< \brief (EMAC) Received Length Field Mismatch Register */
#define REG_EMAC_HRB            (0xF802C090U) /**< \brief (EMAC) Hash Register Bottom [31:0] Register */
#define REG_EMAC_HRT            (0xF802C094U) /**< \brief (EMAC) Hash Register Top [63:32] Register */
#define REG_EMAC_SA1B           (0xF802C098U) /**< \brief (EMAC) Specific Address 1 Bottom Register */
#define REG_EMAC_SA1T           (0xF802C09CU) /**< \brief (EMAC) Specific Address 1 Top Register */
#define REG_EMAC_SA2B           (0xF802C0A0U) /**< \brief (EMAC) Specific Address 2 Bottom Register */
#define REG_EMAC_SA2T           (0xF802C0A4U) /**< \brief (EMAC) Specific Address 2 Top Register */
#define REG_EMAC_SA3B           (0xF802C0A8U) /**< \brief (EMAC) Specific Address 3 Bottom Register */
#define REG_EMAC_SA3T           (0xF802C0ACU) /**< \brief (EMAC) Specific Address 3 Top Register */
#define REG_EMAC_SA4B           (0xF802C0B0U) /**< \brief (EMAC) Specific Address 4 Bottom Register */
#define REG_EMAC_SA4T           (0xF802C0B4U) /**< \brief (EMAC) Specific Address 4 Top Register */
#define REG_EMAC_TID            (0xF802C0B8U) /**< \brief (EMAC) Type ID Checking Register */
#define REG_EMAC_USRIO          (0xF802C0C0U) /**< \brief (EMAC) User Input/Output Register */
#define REG_EMAC_WOL            (0xF802C0C4U) /**< \brief (EMAC) Wake on LAN Register */
#else
#define REG_EMAC_NCR   (*(RwReg*)0xF802C000U) /**< \brief (EMAC) Network Control Register */
#define REG_EMAC_NCFGR (*(RwReg*)0xF802C004U) /**< \brief (EMAC) Network Configuration Register */
#define REG_EMAC_NSR   (*(RoReg*)0xF802C008U) /**< \brief (EMAC) Network Status Register */
#define REG_EMAC_TSR   (*(RwReg*)0xF802C014U) /**< \brief (EMAC) Transmit Status Register */
#define REG_EMAC_RBQP  (*(RwReg*)0xF802C018U) /**< \brief (EMAC) Receive Buffer Queue Pointer Register */
#define REG_EMAC_TBQP  (*(RwReg*)0xF802C01CU) /**< \brief (EMAC) Transmit Buffer Queue Pointer Register */
#define REG_EMAC_RSR   (*(RwReg*)0xF802C020U) /**< \brief (EMAC) Receive Status Register */
#define REG_EMAC_ISR   (*(RwReg*)0xF802C024U) /**< \brief (EMAC) Interrupt Status Register */
#define REG_EMAC_IER   (*(WoReg*)0xF802C028U) /**< \brief (EMAC) Interrupt Enable Register */
#define REG_EMAC_IDR   (*(WoReg*)0xF802C02CU) /**< \brief (EMAC) Interrupt Disable Register */
#define REG_EMAC_IMR   (*(RoReg*)0xF802C030U) /**< \brief (EMAC) Interrupt Mask Register */
#define REG_EMAC_MAN   (*(RwReg*)0xF802C034U) /**< \brief (EMAC) Phy Maintenance Register */
#define REG_EMAC_PTR   (*(RwReg*)0xF802C038U) /**< \brief (EMAC) Pause Time Register */
#define REG_EMAC_PFR   (*(RwReg*)0xF802C03CU) /**< \brief (EMAC) Pause Frames Received Register */
#define REG_EMAC_FTO   (*(RwReg*)0xF802C040U) /**< \brief (EMAC) Frames Transmitted Ok Register */
#define REG_EMAC_SCF   (*(RwReg*)0xF802C044U) /**< \brief (EMAC) Single Collision Frames Register */
#define REG_EMAC_MCF   (*(RwReg*)0xF802C048U) /**< \brief (EMAC) Multiple Collision Frames Register */
#define REG_EMAC_FRO   (*(RwReg*)0xF802C04CU) /**< \brief (EMAC) Frames Received Ok Register */
#define REG_EMAC_FCSE  (*(RwReg*)0xF802C050U) /**< \brief (EMAC) Frame Check Sequence Errors Register */
#define REG_EMAC_ALE   (*(RwReg*)0xF802C054U) /**< \brief (EMAC) Alignment Errors Register */
#define REG_EMAC_DTF   (*(RwReg*)0xF802C058U) /**< \brief (EMAC) Deferred Transmission Frames Register */
#define REG_EMAC_LCOL  (*(RwReg*)0xF802C05CU) /**< \brief (EMAC) Late Collisions Register */
#define REG_EMAC_ECOL  (*(RwReg*)0xF802C060U) /**< \brief (EMAC) Excessive Collisions Register */
#define REG_EMAC_TUND  (*(RwReg*)0xF802C064U) /**< \brief (EMAC) Transmit Underrun Errors Register */
#define REG_EMAC_CSE   (*(RwReg*)0xF802C068U) /**< \brief (EMAC) Carrier Sense Errors Register */
#define REG_EMAC_RRE   (*(RwReg*)0xF802C06CU) /**< \brief (EMAC) Receive Resource Errors Register */
#define REG_EMAC_ROV   (*(RwReg*)0xF802C070U) /**< \brief (EMAC) Receive Overrun Errors Register */
#define REG_EMAC_RSE   (*(RwReg*)0xF802C074U) /**< \brief (EMAC) Receive Symbol Errors Register */
#define REG_EMAC_ELE   (*(RwReg*)0xF802C078U) /**< \brief (EMAC) Excessive Length Errors Register */
#define REG_EMAC_RJA   (*(RwReg*)0xF802C07CU) /**< \brief (EMAC) Receive Jabbers Register */
#define REG_EMAC_USF   (*(RwReg*)0xF802C080U) /**< \brief (EMAC) Undersize Frames Register */
#define REG_EMAC_STE   (*(RwReg*)0xF802C084U) /**< \brief (EMAC) SQE Test Errors Register */
#define REG_EMAC_RLE   (*(RwReg*)0xF802C088U) /**< \brief (EMAC) Received Length Field Mismatch Register */
#define REG_EMAC_HRB   (*(RwReg*)0xF802C090U) /**< \brief (EMAC) Hash Register Bottom [31:0] Register */
#define REG_EMAC_HRT   (*(RwReg*)0xF802C094U) /**< \brief (EMAC) Hash Register Top [63:32] Register */
#define REG_EMAC_SA1B  (*(RwReg*)0xF802C098U) /**< \brief (EMAC) Specific Address 1 Bottom Register */
#define REG_EMAC_SA1T  (*(RwReg*)0xF802C09CU) /**< \brief (EMAC) Specific Address 1 Top Register */
#define REG_EMAC_SA2B  (*(RwReg*)0xF802C0A0U) /**< \brief (EMAC) Specific Address 2 Bottom Register */
#define REG_EMAC_SA2T  (*(RwReg*)0xF802C0A4U) /**< \brief (EMAC) Specific Address 2 Top Register */
#define REG_EMAC_SA3B  (*(RwReg*)0xF802C0A8U) /**< \brief (EMAC) Specific Address 3 Bottom Register */
#define REG_EMAC_SA3T  (*(RwReg*)0xF802C0ACU) /**< \brief (EMAC) Specific Address 3 Top Register */
#define REG_EMAC_SA4B  (*(RwReg*)0xF802C0B0U) /**< \brief (EMAC) Specific Address 4 Bottom Register */
#define REG_EMAC_SA4T  (*(RwReg*)0xF802C0B4U) /**< \brief (EMAC) Specific Address 4 Top Register */
#define REG_EMAC_TID   (*(RwReg*)0xF802C0B8U) /**< \brief (EMAC) Type ID Checking Register */
#define REG_EMAC_USRIO (*(RwReg*)0xF802C0C0U) /**< \brief (EMAC) User Input/Output Register */
#define REG_EMAC_WOL   (*(RwReg*)0xF802C0C4U) /**< \brief (EMAC) Wake on LAN Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAMA5_EMAC_INSTANCE_ */
