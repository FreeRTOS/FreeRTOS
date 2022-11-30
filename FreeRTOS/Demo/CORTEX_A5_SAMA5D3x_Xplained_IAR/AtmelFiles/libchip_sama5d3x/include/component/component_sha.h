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

#ifndef _SAMA5_SHA_COMPONENT_
#define _SAMA5_SHA_COMPONENT_

/* ============================================================================= */
/**  SOFTWARE API DEFINITION FOR Secure Hash Algorithm */
/* ============================================================================= */
/** \addtogroup SAMA5_SHA Secure Hash Algorithm */
/*@{*/

#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
/** \brief Sha hardware registers */
typedef struct {
  WoReg SHA_CR;          /**< \brief (Sha Offset: 0x00) Control Register */
  RwReg SHA_MR;          /**< \brief (Sha Offset: 0x04) Mode Register */
  RoReg Reserved1[2];
  WoReg SHA_IER;         /**< \brief (Sha Offset: 0x10) Interrupt Enable Register */
  WoReg SHA_IDR;         /**< \brief (Sha Offset: 0x14) Interrupt Disable Register */
  RoReg SHA_IMR;         /**< \brief (Sha Offset: 0x18) Interrupt Mask Register */
  RoReg SHA_ISR;         /**< \brief (Sha Offset: 0x1C) Interrupt Status Register */
  RoReg Reserved2[8];
  WoReg SHA_IDATAR[16];  /**< \brief (Sha Offset: 0x40) Input Data 0 Register */
  RwReg SHA_IODATAR[16]; /**< \brief (Sha Offset: 0x80) Input/Output Data 0 Register */
} Sha;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */
/* -------- SHA_CR : (SHA Offset: 0x00) Control Register -------- */
#define SHA_CR_START (0x1u << 0) /**< \brief (SHA_CR) Start Processing */
#define SHA_CR_FIRST (0x1u << 4) /**< \brief (SHA_CR) First Block of a Message */
#define SHA_CR_SWRST (0x1u << 8) /**< \brief (SHA_CR) Software Reset */
/* -------- SHA_MR : (SHA Offset: 0x04) Mode Register -------- */
#define SHA_MR_SMOD_Pos 0
#define SHA_MR_SMOD_Msk (0x3u << SHA_MR_SMOD_Pos) /**< \brief (SHA_MR) Start Mode */
#define   SHA_MR_SMOD_MANUAL_START (0x0u << 0) /**< \brief (SHA_MR) Manual Mode */
#define   SHA_MR_SMOD_AUTO_START (0x1u << 0) /**< \brief (SHA_MR) Auto Mode */
#define   SHA_MR_SMOD_IDATAR0_START (0x2u << 0) /**< \brief (SHA_MR) SHA_IDATAR0 access only Auto Mode */
#define SHA_MR_PROCDLY (0x1u << 4) /**< \brief (SHA_MR) Processing Delay */
#define   SHA_MR_PROCDLY_SHORTEST (0x0u << 4) /**< \brief (SHA_MR) SHA processing runtime is the shortest one */
#define   SHA_MR_PROCDLY_LONGEST (0x1u << 4) /**< \brief (SHA_MR) SHA processing runtime is the longest one */
#define SHA_MR_ALGO_Pos 8
#define SHA_MR_ALGO_Msk (0x7u << SHA_MR_ALGO_Pos) /**< \brief (SHA_MR) SHA Algorithm. */
#define   SHA_MR_ALGO_SHA1 (0x0u << 8) /**< \brief (SHA_MR) SHA1 algorithm processed */
#define   SHA_MR_ALGO_SHA256 (0x1u << 8) /**< \brief (SHA_MR) SHA256 algorithm processed */
#define   SHA_MR_ALGO_SHA384 (0x2u << 8) /**< \brief (SHA_MR) SHA384 algorithm processed */
#define   SHA_MR_ALGO_SHA512 (0x3u << 8) /**< \brief (SHA_MR) SHA512 algorithm processed */
#define   SHA_MR_ALGO_SHA224 (0x4u << 8) /**< \brief (SHA_MR) SHA224 algorithm processed */
#define SHA_MR_DUALBUFF (0x1u << 16) /**< \brief (SHA_MR) Dual Input BUFFer */
#define   SHA_MR_DUALBUFF_INACTIVE (0x0u << 16) /**< \brief (SHA_MR) SHA_IDATARx and SHA_IODATARx cannot be written during processing of previous block. */
#define   SHA_MR_DUALBUFF_ACTIVE (0x1u << 16) /**< \brief (SHA_MR) SHA_IDATARx and SHA_IODATARx can be written during processing of previous block when SMOD=0x2. It speeds up the overall runtime of large files. */
/* -------- SHA_IER : (SHA Offset: 0x10) Interrupt Enable Register -------- */
#define SHA_IER_DATRDY (0x1u << 0) /**< \brief (SHA_IER) Data Ready Interrupt Enable */
#define SHA_IER_URAD (0x1u << 8) /**< \brief (SHA_IER) Unspecified Register Access Detection Interrupt Enable */
/* -------- SHA_IDR : (SHA Offset: 0x14) Interrupt Disable Register -------- */
#define SHA_IDR_DATRDY (0x1u << 0) /**< \brief (SHA_IDR) Data Ready Interrupt Disable */
#define SHA_IDR_URAD (0x1u << 8) /**< \brief (SHA_IDR) Unspecified Register Access Detection Interrupt Disable */
/* -------- SHA_IMR : (SHA Offset: 0x18) Interrupt Mask Register -------- */
#define SHA_IMR_DATRDY (0x1u << 0) /**< \brief (SHA_IMR) Data Ready Interrupt Mask */
#define SHA_IMR_URAD (0x1u << 8) /**< \brief (SHA_IMR) Unspecified Register Access Detection Interrupt Mask */
/* -------- SHA_ISR : (SHA Offset: 0x1C) Interrupt Status Register -------- */
#define SHA_ISR_DATRDY (0x1u << 0) /**< \brief (SHA_ISR) Data Ready */
#define SHA_ISR_URAD (0x1u << 8) /**< \brief (SHA_ISR) Unspecified Register Access Detection Status */
#define SHA_ISR_URAT_Pos 12
#define SHA_ISR_URAT_Msk (0x7u << SHA_ISR_URAT_Pos) /**< \brief (SHA_ISR) Unspecified Register Access Type */
/* -------- SHA_IDATAR[16] : (SHA Offset: 0x40) Input Data 0 Register -------- */
#define SHA_IDATAR_IDATA_Pos 0
#define SHA_IDATAR_IDATA_Msk (0xffffffffu << SHA_IDATAR_IDATA_Pos) /**< \brief (SHA_IDATAR[16]) Input Data */
#define SHA_IDATAR_IDATA(value) ((SHA_IDATAR_IDATA_Msk & ((value) << SHA_IDATAR_IDATA_Pos)))
/* -------- SHA_IODATAR[16] : (SHA Offset: 0x80) Input/Output Data 0 Register -------- */
#define SHA_IODATAR_IODATA_Pos 0
#define SHA_IODATAR_IODATA_Msk (0xffffffffu << SHA_IODATAR_IODATA_Pos) /**< \brief (SHA_IODATAR[16]) Input/Output Data */
#define SHA_IODATAR_IODATA(value) ((SHA_IODATAR_IODATA_Msk & ((value) << SHA_IODATAR_IODATA_Pos)))

/*@}*/


#endif /* _SAMA5_SHA_COMPONENT_ */
