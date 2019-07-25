/* ---------------------------------------------------------------------------- */
/*                  Atmel Microcontroller Software Support                      */
/*                       SAM Software Package License                           */
/* ---------------------------------------------------------------------------- */
/* Copyright (c) 2015, Atmel Corporation                                        */
/*                                                                              */
/* All rights reserved.                                                         */
/*                                                                              */
/* Redistribution and use in source and binary forms, with or without           */
/* modification, are permitted provided that the following condition is met:    */
/*                                                                              */
/* - Redistributions of source code must retain the above copyright notice,     */
/* this list of conditions and the disclaimer below.                            */
/*                                                                              */
/* Atmel's name may not be used to endorse or promote products derived from     */
/* this software without specific prior written permission.                     */
/*                                                                              */
/* DISCLAIMER:  THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR   */
/* IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF */
/* MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE   */
/* DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,      */
/* INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT */
/* LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,  */
/* OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF    */
/* LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING         */
/* NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, */
/* EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.                           */
/* ---------------------------------------------------------------------------- */

#ifndef _SAMA5D2_SHA_COMPONENT_
#define _SAMA5D2_SHA_COMPONENT_

/* ============================================================================= */
/**  SOFTWARE API DEFINITION FOR Secure Hash Algorithm */
/* ============================================================================= */
/** \addtogroup SAMA5D2_SHA Secure Hash Algorithm */
/*@{*/

#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
/** \brief Sha hardware registers */
typedef struct {
  __O  uint32_t SHA_CR;          /**< \brief (Sha Offset: 0x00) Control Register */
  __IO uint32_t SHA_MR;          /**< \brief (Sha Offset: 0x04) Mode Register */
  __I  uint32_t Reserved1[2];
  __O  uint32_t SHA_IER;         /**< \brief (Sha Offset: 0x10) Interrupt Enable Register */
  __O  uint32_t SHA_IDR;         /**< \brief (Sha Offset: 0x14) Interrupt Disable Register */
  __I  uint32_t SHA_IMR;         /**< \brief (Sha Offset: 0x18) Interrupt Mask Register */
  __I  uint32_t SHA_ISR;         /**< \brief (Sha Offset: 0x1C) Interrupt Status Register */
  __IO uint32_t SHA_MSR;         /**< \brief (Sha Offset: 0x20) Message Size Register */
  __I  uint32_t Reserved2[3];
  __IO uint32_t SHA_BCR;         /**< \brief (Sha Offset: 0x30) Bytes Count Register */
  __I  uint32_t Reserved3[3];
  __O  uint32_t SHA_IDATAR[16];  /**< \brief (Sha Offset: 0x40) Input Data 0 Register */
  __IO uint32_t SHA_IODATAR[16]; /**< \brief (Sha Offset: 0x80) Input/Output Data 0 Register */
  __I  uint32_t SHA_VERSION;     /**< \brief (Sha Offset: 0xFC) Version Register */
} Sha;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */
/* -------- SHA_CR : (SHA Offset: 0x00) Control Register -------- */
#define SHA_CR_START (0x1u << 0) /**< \brief (SHA_CR) Start Processing */
#define SHA_CR_FIRST (0x1u << 4) /**< \brief (SHA_CR) First Block of a Message */
#define SHA_CR_SWRST (0x1u << 8) /**< \brief (SHA_CR) Software Reset */
#define SHA_CR_WUIHV (0x1u << 12) /**< \brief (SHA_CR) Write User Initial Hash Values */
#define SHA_CR_WUIEHV (0x1u << 13) /**< \brief (SHA_CR) Write User Initial or Expected Hash Values */
/* -------- SHA_MR : (SHA Offset: 0x04) Mode Register -------- */
#define SHA_MR_SMOD_Pos 0
#define SHA_MR_SMOD_Msk (0x3u << SHA_MR_SMOD_Pos) /**< \brief (SHA_MR) Start Mode */
#define SHA_MR_SMOD(value) ((SHA_MR_SMOD_Msk & ((value) << SHA_MR_SMOD_Pos)))
#define   SHA_MR_SMOD_MANUAL_START (0x0u << 0) /**< \brief (SHA_MR) Manual Mode */
#define   SHA_MR_SMOD_AUTO_START (0x1u << 0) /**< \brief (SHA_MR) Auto Mode */
#define   SHA_MR_SMOD_IDATAR0_START (0x2u << 0) /**< \brief (SHA_MR) SHA_IDATAR0 access only Auto Mode */
#define SHA_MR_PROCDLY (0x1u << 4) /**< \brief (SHA_MR) Processing Delay */
#define   SHA_MR_PROCDLY_SHORTEST (0x0u << 4) /**< \brief (SHA_MR) SHA processing runtime is the shortest one */
#define   SHA_MR_PROCDLY_LONGEST (0x1u << 4) /**< \brief (SHA_MR) SHA processing runtime is the longest one (reduces the SHA bandwidth requirement, reduces the system bus overload) */
#define SHA_MR_UIHV (0x1u << 5) /**< \brief (SHA_MR) User Initial Hash Value Registers */
#define SHA_MR_UIEHV (0x1u << 6) /**< \brief (SHA_MR) User Initial or Expected Hash Value Registers */
#define SHA_MR_ALGO_Pos 8
#define SHA_MR_ALGO_Msk (0xfu << SHA_MR_ALGO_Pos) /**< \brief (SHA_MR) SHA Algorithm */
#define SHA_MR_ALGO(value) ((SHA_MR_ALGO_Msk & ((value) << SHA_MR_ALGO_Pos)))
#define   SHA_MR_ALGO_SHA1 (0x0u << 8) /**< \brief (SHA_MR) SHA1 algorithm processed */
#define   SHA_MR_ALGO_SHA256 (0x1u << 8) /**< \brief (SHA_MR) SHA256 algorithm processed */
#define   SHA_MR_ALGO_SHA384 (0x2u << 8) /**< \brief (SHA_MR) SHA384 algorithm processed */
#define   SHA_MR_ALGO_SHA512 (0x3u << 8) /**< \brief (SHA_MR) SHA512 algorithm processed */
#define   SHA_MR_ALGO_SHA224 (0x4u << 8) /**< \brief (SHA_MR) SHA224 algorithm processed */
#define   SHA_MR_ALGO_HMAC_SHA1 (0x8u << 8) /**< \brief (SHA_MR) HMAC algorithm with SHA1 Hash processed */
#define   SHA_MR_ALGO_HMAC_SHA256 (0x9u << 8) /**< \brief (SHA_MR) HMAC algorithm with SHA256 Hash processed */
#define   SHA_MR_ALGO_HMAC_SHA384 (0xAu << 8) /**< \brief (SHA_MR) HMAC algorithm with SHA384 Hash processed */
#define   SHA_MR_ALGO_HMAC_SHA512 (0xBu << 8) /**< \brief (SHA_MR) HMAC algorithm with SHA512 Hash processed */
#define   SHA_MR_ALGO_HMAC_SHA224 (0xCu << 8) /**< \brief (SHA_MR) HMAC algorithm with SHA224 Hash processed */
#define SHA_MR_DUALBUFF (0x1u << 16) /**< \brief (SHA_MR) Dual Input Buffer */
#define   SHA_MR_DUALBUFF_INACTIVE (0x0u << 16) /**< \brief (SHA_MR) SHA_IDATARx and SHA_IODATARx cannot be written during processing of previous block. */
#define   SHA_MR_DUALBUFF_ACTIVE (0x1u << 16) /**< \brief (SHA_MR) SHA_IDATARx and SHA_IODATARx can be written during processing of previous block when SMOD value = 2. It speeds up the overall runtime of large files. */
#define SHA_MR_CHECK_Pos 24
#define SHA_MR_CHECK_Msk (0x3u << SHA_MR_CHECK_Pos) /**< \brief (SHA_MR) Hash Check */
#define SHA_MR_CHECK(value) ((SHA_MR_CHECK_Msk & ((value) << SHA_MR_CHECK_Pos)))
#define   SHA_MR_CHECK_NO_CHECK (0x0u << 24) /**< \brief (SHA_MR) No check is performed */
#define   SHA_MR_CHECK_CHECK_EHV (0x1u << 24) /**< \brief (SHA_MR) Check is performed with expected hash stored in internal expected hash value registers. */
#define   SHA_MR_CHECK_CHECK_MESSAGE (0x2u << 24) /**< \brief (SHA_MR) Check is performed with expected hash provided after the message. */
#define SHA_MR_CHKCNT_Pos 28
#define SHA_MR_CHKCNT_Msk (0xfu << SHA_MR_CHKCNT_Pos) /**< \brief (SHA_MR) Check Counter */
#define SHA_MR_CHKCNT(value) ((SHA_MR_CHKCNT_Msk & ((value) << SHA_MR_CHKCNT_Pos)))
/* -------- SHA_IER : (SHA Offset: 0x10) Interrupt Enable Register -------- */
#define SHA_IER_DATRDY (0x1u << 0) /**< \brief (SHA_IER) Data Ready Interrupt Enable */
#define SHA_IER_URAD (0x1u << 8) /**< \brief (SHA_IER) Unspecified Register Access Detection Interrupt Enable */
#define SHA_IER_CHECKF (0x1u << 16) /**< \brief (SHA_IER) Check Done Interrupt Enable */
/* -------- SHA_IDR : (SHA Offset: 0x14) Interrupt Disable Register -------- */
#define SHA_IDR_DATRDY (0x1u << 0) /**< \brief (SHA_IDR) Data Ready Interrupt Disable */
#define SHA_IDR_URAD (0x1u << 8) /**< \brief (SHA_IDR) Unspecified Register Access Detection Interrupt Disable */
#define SHA_IDR_CHECKF (0x1u << 16) /**< \brief (SHA_IDR) Check Done Interrupt Disable */
/* -------- SHA_IMR : (SHA Offset: 0x18) Interrupt Mask Register -------- */
#define SHA_IMR_DATRDY (0x1u << 0) /**< \brief (SHA_IMR) Data Ready Interrupt Mask */
#define SHA_IMR_URAD (0x1u << 8) /**< \brief (SHA_IMR) Unspecified Register Access Detection Interrupt Mask */
#define SHA_IMR_CHECKF (0x1u << 16) /**< \brief (SHA_IMR) Check Done Interrupt Mask */
/* -------- SHA_ISR : (SHA Offset: 0x1C) Interrupt Status Register -------- */
#define SHA_ISR_DATRDY (0x1u << 0) /**< \brief (SHA_ISR) Data Ready (cleared by writing a 1 to bit SWRST or START in SHA_CR, or by reading SHA_IODATARx) */
#define SHA_ISR_WRDY (0x1u << 4) /**< \brief (SHA_ISR) Input Data Register Write Ready */
#define SHA_ISR_URAD (0x1u << 8) /**< \brief (SHA_ISR) Unspecified Register Access Detection Status (cleared by writing a 1 to SWRST bit in SHA_CR) */
#define SHA_ISR_URAT_Pos 12
#define SHA_ISR_URAT_Msk (0x7u << SHA_ISR_URAT_Pos) /**< \brief (SHA_ISR) Unspecified Register Access Type (cleared by writing a 1 to SWRST bit in SHA_CR) */
#define SHA_ISR_CHECKF (0x1u << 16) /**< \brief (SHA_ISR) Check Done Status (cleared by writing START or SWRST bits in SHA_CR or by reading SHA_IODATARx) */
#define SHA_ISR_CHKST_Pos 20
#define SHA_ISR_CHKST_Msk (0xfu << SHA_ISR_CHKST_Pos) /**< \brief (SHA_ISR) Check Status (cleared by writing START or SWRST bits in SHA_CR or by reading SHA_IODATARx) */
/* -------- SHA_MSR : (SHA Offset: 0x20) Message Size Register -------- */
#define SHA_MSR_MSGSIZE_Pos 0
#define SHA_MSR_MSGSIZE_Msk (0xffffffffu << SHA_MSR_MSGSIZE_Pos) /**< \brief (SHA_MSR) Message Size */
#define SHA_MSR_MSGSIZE(value) ((SHA_MSR_MSGSIZE_Msk & ((value) << SHA_MSR_MSGSIZE_Pos)))
/* -------- SHA_BCR : (SHA Offset: 0x30) Bytes Count Register -------- */
#define SHA_BCR_BYTCNT_Pos 0
#define SHA_BCR_BYTCNT_Msk (0xffffffffu << SHA_BCR_BYTCNT_Pos) /**< \brief (SHA_BCR) Remaining Byte Count Before Auto Padding */
#define SHA_BCR_BYTCNT(value) ((SHA_BCR_BYTCNT_Msk & ((value) << SHA_BCR_BYTCNT_Pos)))
/* -------- SHA_IDATAR[16] : (SHA Offset: 0x40) Input Data 0 Register -------- */
#define SHA_IDATAR_IDATA_Pos 0
#define SHA_IDATAR_IDATA_Msk (0xffffffffu << SHA_IDATAR_IDATA_Pos) /**< \brief (SHA_IDATAR[16]) Input Data */
#define SHA_IDATAR_IDATA(value) ((SHA_IDATAR_IDATA_Msk & ((value) << SHA_IDATAR_IDATA_Pos)))
/* -------- SHA_IODATAR[16] : (SHA Offset: 0x80) Input/Output Data 0 Register -------- */
#define SHA_IODATAR_IODATA_Pos 0
#define SHA_IODATAR_IODATA_Msk (0xffffffffu << SHA_IODATAR_IODATA_Pos) /**< \brief (SHA_IODATAR[16]) Input/Output Data */
#define SHA_IODATAR_IODATA(value) ((SHA_IODATAR_IODATA_Msk & ((value) << SHA_IODATAR_IODATA_Pos)))
/* -------- SHA_VERSION : (SHA Offset: 0xFC) Version Register -------- */
#define SHA_VERSION_VERSION_Pos 0
#define SHA_VERSION_VERSION_Msk (0xfffu << SHA_VERSION_VERSION_Pos) /**< \brief (SHA_VERSION) Version of the Hardware Module */
#define SHA_VERSION_MFN_Pos 16
#define SHA_VERSION_MFN_Msk (0x7u << SHA_VERSION_MFN_Pos) /**< \brief (SHA_VERSION) Metal Fix Number */

/*@}*/


#endif /* _SAMA5D2_SHA_COMPONENT_ */
