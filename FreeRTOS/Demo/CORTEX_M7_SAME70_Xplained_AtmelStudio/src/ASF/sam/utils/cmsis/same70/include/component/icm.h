/**
 * \file
 *
 * Copyright (c) 2015 Atmel Corporation. All rights reserved.
 *
 * \asf_license_start
 *
 * \page License
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 *    this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 *    this list of conditions and the following disclaimer in the documentation
 *    and/or other materials provided with the distribution.
 *
 * 3. The name of Atmel may not be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 * 4. This software may only be redistributed and used in connection with an
 *    Atmel microcontroller product.
 *
 * THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR IMPLIED
 * WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * EXPRESSLY AND SPECIFICALLY DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR
 * ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
 * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
 * ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 *
 * \asf_license_stop
 *
 */
/*
 * Support and FAQ: visit <a href="http://www.atmel.com/design-support/">Atmel Support</a>
 */

#ifndef _SAME70_ICM_COMPONENT_
#define _SAME70_ICM_COMPONENT_

/* ============================================================================= */
/**  SOFTWARE API DEFINITION FOR Integrity Check Monitor */
/* ============================================================================= */
/** \addtogroup SAME70_ICM Integrity Check Monitor */
/*@{*/

#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
/** \brief Icm hardware registers */
typedef struct {
  __IO uint32_t ICM_CFG;       /**< \brief (Icm Offset: 0x00) Configuration Register */
  __O  uint32_t ICM_CTRL;      /**< \brief (Icm Offset: 0x04) Control Register */
  __O  uint32_t ICM_SR;        /**< \brief (Icm Offset: 0x08) Status Register */
  __I  uint32_t Reserved1[1];
  __O  uint32_t ICM_IER;       /**< \brief (Icm Offset: 0x10) Interrupt Enable Register */
  __O  uint32_t ICM_IDR;       /**< \brief (Icm Offset: 0x14) Interrupt Disable Register */
  __I  uint32_t ICM_IMR;       /**< \brief (Icm Offset: 0x18) Interrupt Mask Register */
  __I  uint32_t ICM_ISR;       /**< \brief (Icm Offset: 0x1C) Interrupt Status Register */
  __I  uint32_t ICM_UASR;      /**< \brief (Icm Offset: 0x20) Undefined Access Status Register */
  __I  uint32_t Reserved2[3];
  __IO uint32_t ICM_DSCR;      /**< \brief (Icm Offset: 0x30) Region Descriptor Area Start Address Register */
  __IO uint32_t ICM_HASH;      /**< \brief (Icm Offset: 0x34) Region Hash Area Start Address Register */
  __O  uint32_t ICM_UIHVAL[8]; /**< \brief (Icm Offset: 0x38) User Initial Hash Value 0 Register */
} Icm;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */
/* -------- ICM_CFG : (ICM Offset: 0x00) Configuration Register -------- */
#define ICM_CFG_WBDIS (0x1u << 0) /**< \brief (ICM_CFG) Write Back Disable */
#define ICM_CFG_EOMDIS (0x1u << 1) /**< \brief (ICM_CFG) End of Monitoring Disable */
#define ICM_CFG_SLBDIS (0x1u << 2) /**< \brief (ICM_CFG) Secondary List Branching Disable */
#define ICM_CFG_BBC_Pos 4
#define ICM_CFG_BBC_Msk (0xfu << ICM_CFG_BBC_Pos) /**< \brief (ICM_CFG) Bus Burden Control */
#define ICM_CFG_BBC(value) ((ICM_CFG_BBC_Msk & ((value) << ICM_CFG_BBC_Pos)))
#define ICM_CFG_ASCD (0x1u << 8) /**< \brief (ICM_CFG) Automatic Switch To Compare Digest */
#define ICM_CFG_DUALBUFF (0x1u << 9) /**< \brief (ICM_CFG) Dual Input Buffer */
#define ICM_CFG_UIHASH (0x1u << 12) /**< \brief (ICM_CFG) User Initial Hash Value */
#define ICM_CFG_UALGO_Pos 13
#define ICM_CFG_UALGO_Msk (0x7u << ICM_CFG_UALGO_Pos) /**< \brief (ICM_CFG) User SHA Algorithm */
#define ICM_CFG_UALGO(value) ((ICM_CFG_UALGO_Msk & ((value) << ICM_CFG_UALGO_Pos)))
#define   ICM_CFG_UALGO_SHA1 (0x0u << 13) /**< \brief (ICM_CFG) SHA1 algorithm processed */
#define   ICM_CFG_UALGO_SHA256 (0x1u << 13) /**< \brief (ICM_CFG) SHA256 algorithm processed */
#define   ICM_CFG_UALGO_SHA224 (0x4u << 13) /**< \brief (ICM_CFG) SHA224 algorithm processed */
#define ICM_CFG_HAPROT_Pos 16
#define ICM_CFG_HAPROT_Msk (0x3fu << ICM_CFG_HAPROT_Pos) /**< \brief (ICM_CFG) Region Hash Area Protection */
#define ICM_CFG_HAPROT(value) ((ICM_CFG_HAPROT_Msk & ((value) << ICM_CFG_HAPROT_Pos)))
#define ICM_CFG_DAPROT_Pos 24
#define ICM_CFG_DAPROT_Msk (0x3fu << ICM_CFG_DAPROT_Pos) /**< \brief (ICM_CFG) Region Descriptor Area Protection */
#define ICM_CFG_DAPROT(value) ((ICM_CFG_DAPROT_Msk & ((value) << ICM_CFG_DAPROT_Pos)))
/* -------- ICM_CTRL : (ICM Offset: 0x04) Control Register -------- */
#define ICM_CTRL_ENABLE (0x1u << 0) /**< \brief (ICM_CTRL) ICM Enable */
#define ICM_CTRL_DISABLE (0x1u << 1) /**< \brief (ICM_CTRL) ICM Disable Register */
#define ICM_CTRL_SWRST (0x1u << 2) /**< \brief (ICM_CTRL) Software Reset */
#define ICM_CTRL_REHASH_Pos 4
#define ICM_CTRL_REHASH_Msk (0xfu << ICM_CTRL_REHASH_Pos) /**< \brief (ICM_CTRL) Recompute Internal Hash */
#define ICM_CTRL_REHASH(value) ((ICM_CTRL_REHASH_Msk & ((value) << ICM_CTRL_REHASH_Pos)))
#define ICM_CTRL_RMDIS_Pos 8
#define ICM_CTRL_RMDIS_Msk (0xfu << ICM_CTRL_RMDIS_Pos) /**< \brief (ICM_CTRL) Region Monitoring Disable */
#define ICM_CTRL_RMDIS(value) ((ICM_CTRL_RMDIS_Msk & ((value) << ICM_CTRL_RMDIS_Pos)))
#define ICM_CTRL_RMEN_Pos 12
#define ICM_CTRL_RMEN_Msk (0xfu << ICM_CTRL_RMEN_Pos) /**< \brief (ICM_CTRL) Region Monitoring Enable */
#define ICM_CTRL_RMEN(value) ((ICM_CTRL_RMEN_Msk & ((value) << ICM_CTRL_RMEN_Pos)))
/* -------- ICM_SR : (ICM Offset: 0x08) Status Register -------- */
#define ICM_SR_ENABLE (0x1u << 0) /**< \brief (ICM_SR) ICM Controller Enable Register */
#define ICM_SR_RAWRMDIS_Pos 8
#define ICM_SR_RAWRMDIS_Msk (0xfu << ICM_SR_RAWRMDIS_Pos) /**< \brief (ICM_SR) RAW Region Monitoring Disabled Status */
#define ICM_SR_RAWRMDIS(value) ((ICM_SR_RAWRMDIS_Msk & ((value) << ICM_SR_RAWRMDIS_Pos)))
#define ICM_SR_RMDIS_Pos 12
#define ICM_SR_RMDIS_Msk (0xfu << ICM_SR_RMDIS_Pos) /**< \brief (ICM_SR) Region Monitoring Disabled Status */
#define ICM_SR_RMDIS(value) ((ICM_SR_RMDIS_Msk & ((value) << ICM_SR_RMDIS_Pos)))
/* -------- ICM_IER : (ICM Offset: 0x10) Interrupt Enable Register -------- */
#define ICM_IER_RHC_Pos 0
#define ICM_IER_RHC_Msk (0xfu << ICM_IER_RHC_Pos) /**< \brief (ICM_IER) Region Hash Completed Interrupt Enable */
#define ICM_IER_RHC(value) ((ICM_IER_RHC_Msk & ((value) << ICM_IER_RHC_Pos)))
#define ICM_IER_RDM_Pos 4
#define ICM_IER_RDM_Msk (0xfu << ICM_IER_RDM_Pos) /**< \brief (ICM_IER) Region Digest Mismatch Interrupt Enable */
#define ICM_IER_RDM(value) ((ICM_IER_RDM_Msk & ((value) << ICM_IER_RDM_Pos)))
#define ICM_IER_RBE_Pos 8
#define ICM_IER_RBE_Msk (0xfu << ICM_IER_RBE_Pos) /**< \brief (ICM_IER) Region Bus Error Interrupt Enable */
#define ICM_IER_RBE(value) ((ICM_IER_RBE_Msk & ((value) << ICM_IER_RBE_Pos)))
#define ICM_IER_RWC_Pos 12
#define ICM_IER_RWC_Msk (0xfu << ICM_IER_RWC_Pos) /**< \brief (ICM_IER) Region Wrap Condition detected Interrupt Enable */
#define ICM_IER_RWC(value) ((ICM_IER_RWC_Msk & ((value) << ICM_IER_RWC_Pos)))
#define ICM_IER_REC_Pos 16
#define ICM_IER_REC_Msk (0xfu << ICM_IER_REC_Pos) /**< \brief (ICM_IER) Region End bit Condition Detected Interrupt Enable */
#define ICM_IER_REC(value) ((ICM_IER_REC_Msk & ((value) << ICM_IER_REC_Pos)))
#define ICM_IER_RSU_Pos 20
#define ICM_IER_RSU_Msk (0xfu << ICM_IER_RSU_Pos) /**< \brief (ICM_IER) Region Status Updated Interrupt Disable */
#define ICM_IER_RSU(value) ((ICM_IER_RSU_Msk & ((value) << ICM_IER_RSU_Pos)))
#define ICM_IER_URAD (0x1u << 24) /**< \brief (ICM_IER) Undefined Register Access Detection Interrupt Enable */
/* -------- ICM_IDR : (ICM Offset: 0x14) Interrupt Disable Register -------- */
#define ICM_IDR_RHC_Pos 0
#define ICM_IDR_RHC_Msk (0xfu << ICM_IDR_RHC_Pos) /**< \brief (ICM_IDR) Region Hash Completed Interrupt Disable */
#define ICM_IDR_RHC(value) ((ICM_IDR_RHC_Msk & ((value) << ICM_IDR_RHC_Pos)))
#define ICM_IDR_RDM_Pos 4
#define ICM_IDR_RDM_Msk (0xfu << ICM_IDR_RDM_Pos) /**< \brief (ICM_IDR) Region Digest Mismatch Interrupt Disable */
#define ICM_IDR_RDM(value) ((ICM_IDR_RDM_Msk & ((value) << ICM_IDR_RDM_Pos)))
#define ICM_IDR_RBE_Pos 8
#define ICM_IDR_RBE_Msk (0xfu << ICM_IDR_RBE_Pos) /**< \brief (ICM_IDR) Region Bus Error Interrupt Disable */
#define ICM_IDR_RBE(value) ((ICM_IDR_RBE_Msk & ((value) << ICM_IDR_RBE_Pos)))
#define ICM_IDR_RWC_Pos 12
#define ICM_IDR_RWC_Msk (0xfu << ICM_IDR_RWC_Pos) /**< \brief (ICM_IDR) Region Wrap Condition Detected Interrupt Disable */
#define ICM_IDR_RWC(value) ((ICM_IDR_RWC_Msk & ((value) << ICM_IDR_RWC_Pos)))
#define ICM_IDR_REC_Pos 16
#define ICM_IDR_REC_Msk (0xfu << ICM_IDR_REC_Pos) /**< \brief (ICM_IDR) Region End bit Condition detected Interrupt Disable */
#define ICM_IDR_REC(value) ((ICM_IDR_REC_Msk & ((value) << ICM_IDR_REC_Pos)))
#define ICM_IDR_RSU_Pos 20
#define ICM_IDR_RSU_Msk (0xfu << ICM_IDR_RSU_Pos) /**< \brief (ICM_IDR) Region Status Updated Interrupt Disable */
#define ICM_IDR_RSU(value) ((ICM_IDR_RSU_Msk & ((value) << ICM_IDR_RSU_Pos)))
#define ICM_IDR_URAD (0x1u << 24) /**< \brief (ICM_IDR) Undefined Register Access Detection Interrupt Disable */
/* -------- ICM_IMR : (ICM Offset: 0x18) Interrupt Mask Register -------- */
#define ICM_IMR_RHC_Pos 0
#define ICM_IMR_RHC_Msk (0xfu << ICM_IMR_RHC_Pos) /**< \brief (ICM_IMR) Region Hash Completed Interrupt Mask */
#define ICM_IMR_RDM_Pos 4
#define ICM_IMR_RDM_Msk (0xfu << ICM_IMR_RDM_Pos) /**< \brief (ICM_IMR) Region Digest Mismatch Interrupt Mask */
#define ICM_IMR_RBE_Pos 8
#define ICM_IMR_RBE_Msk (0xfu << ICM_IMR_RBE_Pos) /**< \brief (ICM_IMR) Region Bus Error Interrupt Mask */
#define ICM_IMR_RWC_Pos 12
#define ICM_IMR_RWC_Msk (0xfu << ICM_IMR_RWC_Pos) /**< \brief (ICM_IMR) Region Wrap Condition Detected Interrupt Mask */
#define ICM_IMR_REC_Pos 16
#define ICM_IMR_REC_Msk (0xfu << ICM_IMR_REC_Pos) /**< \brief (ICM_IMR) Region End bit Condition Detected Interrupt Mask */
#define ICM_IMR_RSU_Pos 20
#define ICM_IMR_RSU_Msk (0xfu << ICM_IMR_RSU_Pos) /**< \brief (ICM_IMR) Region Status Updated Interrupt Mask */
#define ICM_IMR_URAD (0x1u << 24) /**< \brief (ICM_IMR) Undefined Register Access Detection Interrupt Mask */
/* -------- ICM_ISR : (ICM Offset: 0x1C) Interrupt Status Register -------- */
#define ICM_ISR_RHC_Pos 0
#define ICM_ISR_RHC_Msk (0xfu << ICM_ISR_RHC_Pos) /**< \brief (ICM_ISR) Region Hash Completed */
#define ICM_ISR_RDM_Pos 4
#define ICM_ISR_RDM_Msk (0xfu << ICM_ISR_RDM_Pos) /**< \brief (ICM_ISR) Region Digest Mismatch */
#define ICM_ISR_RBE_Pos 8
#define ICM_ISR_RBE_Msk (0xfu << ICM_ISR_RBE_Pos) /**< \brief (ICM_ISR) Region Bus Error */
#define ICM_ISR_RWC_Pos 12
#define ICM_ISR_RWC_Msk (0xfu << ICM_ISR_RWC_Pos) /**< \brief (ICM_ISR) Region Wrap Condition Detected */
#define ICM_ISR_REC_Pos 16
#define ICM_ISR_REC_Msk (0xfu << ICM_ISR_REC_Pos) /**< \brief (ICM_ISR) Region End bit Condition Detected */
#define ICM_ISR_RSU_Pos 20
#define ICM_ISR_RSU_Msk (0xfu << ICM_ISR_RSU_Pos) /**< \brief (ICM_ISR) Region Status Updated Detected */
#define ICM_ISR_URAD (0x1u << 24) /**< \brief (ICM_ISR) Undefined Register Access Detection Status */
/* -------- ICM_UASR : (ICM Offset: 0x20) Undefined Access Status Register -------- */
#define ICM_UASR_URAT_Pos 0
#define ICM_UASR_URAT_Msk (0x7u << ICM_UASR_URAT_Pos) /**< \brief (ICM_UASR) Undefined Register Access Trace */
#define   ICM_UASR_URAT_UNSPEC_STRUCT_MEMBER (0x0u << 0) /**< \brief (ICM_UASR) Unspecified structure member set to one detected when the descriptor is loaded. */
#define   ICM_UASR_URAT_ICM_CFG_MODIFIED (0x1u << 0) /**< \brief (ICM_UASR) ICM_CFG modified during active monitoring. */
#define   ICM_UASR_URAT_ICM_DSCR_MODIFIED (0x2u << 0) /**< \brief (ICM_UASR) ICM_DSCR modified during active monitoring. */
#define   ICM_UASR_URAT_ICM_HASH_MODIFIED (0x3u << 0) /**< \brief (ICM_UASR) ICM_HASH modified during active monitoring */
#define   ICM_UASR_URAT_READ_ACCESS (0x4u << 0) /**< \brief (ICM_UASR) Write-only register read access */
/* -------- ICM_DSCR : (ICM Offset: 0x30) Region Descriptor Area Start Address Register -------- */
#define ICM_DSCR_DASA_Pos 6
#define ICM_DSCR_DASA_Msk (0x3ffffffu << ICM_DSCR_DASA_Pos) /**< \brief (ICM_DSCR) Descriptor Area Start Address */
#define ICM_DSCR_DASA(value) ((ICM_DSCR_DASA_Msk & ((value) << ICM_DSCR_DASA_Pos)))
/* -------- ICM_HASH : (ICM Offset: 0x34) Region Hash Area Start Address Register -------- */
#define ICM_HASH_HASA_Pos 7
#define ICM_HASH_HASA_Msk (0x1ffffffu << ICM_HASH_HASA_Pos) /**< \brief (ICM_HASH) Hash Area Start Address */
#define ICM_HASH_HASA(value) ((ICM_HASH_HASA_Msk & ((value) << ICM_HASH_HASA_Pos)))
/* -------- ICM_UIHVAL[8] : (ICM Offset: 0x38) User Initial Hash Value 0 Register -------- */
#define ICM_UIHVAL_VAL_Pos 0
#define ICM_UIHVAL_VAL_Msk (0xffffffffu << ICM_UIHVAL_VAL_Pos) /**< \brief (ICM_UIHVAL[8]) Initial Hash Value */
#define ICM_UIHVAL_VAL(value) ((ICM_UIHVAL_VAL_Msk & ((value) << ICM_UIHVAL_VAL_Pos)))

/*@}*/


#endif /* _SAME70_ICM_COMPONENT_ */
