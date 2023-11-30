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

#ifndef _SAMA5D2_AESB_COMPONENT_
#define _SAMA5D2_AESB_COMPONENT_

/* ============================================================================= */
/**  SOFTWARE API DEFINITION FOR Advanced Encryption Standard Bridge */
/* ============================================================================= */
/** \addtogroup SAMA5D2_AESB Advanced Encryption Standard Bridge */
/*@{*/

#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
/** \brief Aesb hardware registers */
typedef struct {
  __O  uint32_t AESB_CR;        /**< \brief (Aesb Offset: 0x00) Control Register */
  __IO uint32_t AESB_MR;        /**< \brief (Aesb Offset: 0x04) Mode Register */
  __I  uint32_t Reserved1[2];
  __O  uint32_t AESB_IER;       /**< \brief (Aesb Offset: 0x10) Interrupt Enable Register */
  __O  uint32_t AESB_IDR;       /**< \brief (Aesb Offset: 0x14) Interrupt Disable Register */
  __I  uint32_t AESB_IMR;       /**< \brief (Aesb Offset: 0x18) Interrupt Mask Register */
  __I  uint32_t AESB_ISR;       /**< \brief (Aesb Offset: 0x1C) Interrupt Status Register */
  __O  uint32_t AESB_KEYWR[4];  /**< \brief (Aesb Offset: 0x20) Key Word Register */
  __I  uint32_t Reserved2[4];
  __O  uint32_t AESB_IDATAR[4]; /**< \brief (Aesb Offset: 0x40) Input Data Register */
  __I  uint32_t AESB_ODATAR[4]; /**< \brief (Aesb Offset: 0x50) Output Data Register */
  __O  uint32_t AESB_IVR[4];    /**< \brief (Aesb Offset: 0x60) Initialization Vector Register */
  __I  uint32_t Reserved3[35];
  __I  uint32_t AESB_VERSION;   /**< \brief (Aesb Offset: 0xFC) Version Register */
} Aesb;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */
/* -------- AESB_CR : (AESB Offset: 0x00) Control Register -------- */
#define AESB_CR_START (0x1u << 0) /**< \brief (AESB_CR) Start Processing */
#define AESB_CR_SWRST (0x1u << 8) /**< \brief (AESB_CR) Software Reset */
#define AESB_CR_LOADSEED (0x1u << 16) /**< \brief (AESB_CR) Random Number Generator Seed Loading */
/* -------- AESB_MR : (AESB Offset: 0x04) Mode Register -------- */
#define AESB_MR_CIPHER (0x1u << 0) /**< \brief (AESB_MR) Processing Mode */
#define AESB_MR_AAHB (0x1u << 2) /**< \brief (AESB_MR) Automatic Bridge Mode */
#define AESB_MR_DUALBUFF (0x1u << 3) /**< \brief (AESB_MR) Dual Input Buffer */
#define   AESB_MR_DUALBUFF_INACTIVE (0x0u << 3) /**< \brief (AESB_MR) AESB_IDATARx cannot be written during processing of previous block. */
#define   AESB_MR_DUALBUFF_ACTIVE (0x1u << 3) /**< \brief (AESB_MR) AESB_IDATARx can be written during processing of previous block when SMOD = 0x2. It speeds up the overall runtime of large files. */
#define AESB_MR_PROCDLY_Pos 4
#define AESB_MR_PROCDLY_Msk (0xfu << AESB_MR_PROCDLY_Pos) /**< \brief (AESB_MR) Processing Delay */
#define AESB_MR_PROCDLY(value) ((AESB_MR_PROCDLY_Msk & ((value) << AESB_MR_PROCDLY_Pos)))
#define AESB_MR_SMOD_Pos 8
#define AESB_MR_SMOD_Msk (0x3u << AESB_MR_SMOD_Pos) /**< \brief (AESB_MR) Start Mode */
#define AESB_MR_SMOD(value) ((AESB_MR_SMOD_Msk & ((value) << AESB_MR_SMOD_Pos)))
#define   AESB_MR_SMOD_MANUAL_START (0x0u << 8) /**< \brief (AESB_MR) Manual Mode */
#define   AESB_MR_SMOD_AUTO_START (0x1u << 8) /**< \brief (AESB_MR) Auto Mode */
#define   AESB_MR_SMOD_IDATAR0_START (0x2u << 8) /**< \brief (AESB_MR) AESB_IDATAR0 access only Auto Mode */
#define AESB_MR_OPMOD_Pos 12
#define AESB_MR_OPMOD_Msk (0x7u << AESB_MR_OPMOD_Pos) /**< \brief (AESB_MR) Operation Mode */
#define AESB_MR_OPMOD(value) ((AESB_MR_OPMOD_Msk & ((value) << AESB_MR_OPMOD_Pos)))
#define   AESB_MR_OPMOD_ECB (0x0u << 12) /**< \brief (AESB_MR) Electronic Code Book mode */
#define   AESB_MR_OPMOD_CBC (0x1u << 12) /**< \brief (AESB_MR) Cipher Block Chaining mode */
#define   AESB_MR_OPMOD_CTR (0x4u << 12) /**< \brief (AESB_MR) Counter mode (16-bit internal counter) */
#define AESB_MR_LOD (0x1u << 15) /**< \brief (AESB_MR) Last Output Data Mode */
#define AESB_MR_CKEY_Pos 20
#define AESB_MR_CKEY_Msk (0xfu << AESB_MR_CKEY_Pos) /**< \brief (AESB_MR) Countermeasure Key */
#define AESB_MR_CKEY(value) ((AESB_MR_CKEY_Msk & ((value) << AESB_MR_CKEY_Pos)))
#define   AESB_MR_CKEY_PASSWD (0xEu << 20) /**< \brief (AESB_MR) This field must be written with 0xE to allow CMTYPx fields change. Any other values will abort the write operation in CMTYPx fields.Always reads as 0. */
#define AESB_MR_CMTYP1 (0x1u << 24) /**< \brief (AESB_MR) Countermeasure Type 1 */
#define   AESB_MR_CMTYP1_NOPROT_EXTKEY (0x0u << 24) /**< \brief (AESB_MR) Countermeasure type 1 is disabled. */
#define   AESB_MR_CMTYP1_PROT_EXTKEY (0x1u << 24) /**< \brief (AESB_MR) Countermeasure type 1 is enabled. */
#define AESB_MR_CMTYP2 (0x1u << 25) /**< \brief (AESB_MR) Countermeasure Type 2 */
#define   AESB_MR_CMTYP2_NO_PAUSE (0x0u << 25) /**< \brief (AESB_MR) Countermeasure type 2 is disabled. */
#define   AESB_MR_CMTYP2_PAUSE (0x1u << 25) /**< \brief (AESB_MR) Countermeasure type 2 is enabled. */
#define AESB_MR_CMTYP3 (0x1u << 26) /**< \brief (AESB_MR) Countermeasure Type 3 */
#define   AESB_MR_CMTYP3_NO_DUMMY (0x0u << 26) /**< \brief (AESB_MR) Countermeasure type 3 is disabled. */
#define   AESB_MR_CMTYP3_DUMMY (0x1u << 26) /**< \brief (AESB_MR) Countermeasure type 3 is enabled. */
#define AESB_MR_CMTYP4 (0x1u << 27) /**< \brief (AESB_MR) Countermeasure Type 4 */
#define   AESB_MR_CMTYP4_NO_RESTART (0x0u << 27) /**< \brief (AESB_MR) Countermeasure type 4 is disabled. */
#define   AESB_MR_CMTYP4_RESTART (0x1u << 27) /**< \brief (AESB_MR) Countermeasure type 4 is enabled. */
#define AESB_MR_CMTYP5 (0x1u << 28) /**< \brief (AESB_MR) Countermeasure Type 5 */
#define   AESB_MR_CMTYP5_NO_ADDACCESS (0x0u << 28) /**< \brief (AESB_MR) Countermeasure type 5 is disabled. */
#define   AESB_MR_CMTYP5_ADDACCESS (0x1u << 28) /**< \brief (AESB_MR) Countermeasure type 5 is enabled. */
#define AESB_MR_CMTYP6 (0x1u << 29) /**< \brief (AESB_MR) CounterMeasure Type 6 */
#define   AESB_MR_CMTYP6_NO_IDLECURRENT (0x0u << 29) /**< \brief (AESB_MR) Countermeasure type 6 is disabled. */
#define   AESB_MR_CMTYP6_IDLECURRENT (0x1u << 29) /**< \brief (AESB_MR) Countermeasure type 6 is enabled. */
/* -------- AESB_IER : (AESB Offset: 0x10) Interrupt Enable Register -------- */
#define AESB_IER_DATRDY (0x1u << 0) /**< \brief (AESB_IER) Data Ready Interrupt Enable */
#define AESB_IER_URAD (0x1u << 8) /**< \brief (AESB_IER) Unspecified Register Access Detection Interrupt Enable */
/* -------- AESB_IDR : (AESB Offset: 0x14) Interrupt Disable Register -------- */
#define AESB_IDR_DATRDY (0x1u << 0) /**< \brief (AESB_IDR) Data Ready Interrupt Disable */
#define AESB_IDR_URAD (0x1u << 8) /**< \brief (AESB_IDR) Unspecified Register Access Detection Interrupt Disable */
/* -------- AESB_IMR : (AESB Offset: 0x18) Interrupt Mask Register -------- */
#define AESB_IMR_DATRDY (0x1u << 0) /**< \brief (AESB_IMR) Data Ready Interrupt Mask */
#define AESB_IMR_URAD (0x1u << 8) /**< \brief (AESB_IMR) Unspecified Register Access Detection Interrupt Mask */
/* -------- AESB_ISR : (AESB Offset: 0x1C) Interrupt Status Register -------- */
#define AESB_ISR_DATRDY (0x1u << 0) /**< \brief (AESB_ISR) Data Ready */
#define AESB_ISR_URAD (0x1u << 8) /**< \brief (AESB_ISR) Unspecified Register Access Detection Status */
#define AESB_ISR_URAT_Pos 12
#define AESB_ISR_URAT_Msk (0xfu << AESB_ISR_URAT_Pos) /**< \brief (AESB_ISR) Unspecified Register Access */
#define   AESB_ISR_URAT_IDR_WR_PROCESSING (0x0u << 12) /**< \brief (AESB_ISR) Input Data Register written during the data processing when SMOD = 0x2 mode */
#define   AESB_ISR_URAT_ODR_RD_PROCESSING (0x1u << 12) /**< \brief (AESB_ISR) Output Data Register read during the data processing */
#define   AESB_ISR_URAT_MR_WR_PROCESSING (0x2u << 12) /**< \brief (AESB_ISR) Mode Register written during the data processing */
#define   AESB_ISR_URAT_ODR_RD_SUBKGEN (0x3u << 12) /**< \brief (AESB_ISR) Output Data Register read during the sub-keys generation */
#define   AESB_ISR_URAT_MR_WR_SUBKGEN (0x4u << 12) /**< \brief (AESB_ISR) Mode Register written during the sub-keys generation */
#define   AESB_ISR_URAT_WOR_RD_ACCESS (0x5u << 12) /**< \brief (AESB_ISR) Write-only register read access */
/* -------- AESB_KEYWR[4] : (AESB Offset: 0x20) Key Word Register -------- */
#define AESB_KEYWR_KEYW_Pos 0
#define AESB_KEYWR_KEYW_Msk (0xffffffffu << AESB_KEYWR_KEYW_Pos) /**< \brief (AESB_KEYWR[4]) Key Word */
#define AESB_KEYWR_KEYW(value) ((AESB_KEYWR_KEYW_Msk & ((value) << AESB_KEYWR_KEYW_Pos)))
/* -------- AESB_IDATAR[4] : (AESB Offset: 0x40) Input Data Register -------- */
#define AESB_IDATAR_IDATA_Pos 0
#define AESB_IDATAR_IDATA_Msk (0xffffffffu << AESB_IDATAR_IDATA_Pos) /**< \brief (AESB_IDATAR[4]) Input Data Word */
#define AESB_IDATAR_IDATA(value) ((AESB_IDATAR_IDATA_Msk & ((value) << AESB_IDATAR_IDATA_Pos)))
/* -------- AESB_ODATAR[4] : (AESB Offset: 0x50) Output Data Register -------- */
#define AESB_ODATAR_ODATA_Pos 0
#define AESB_ODATAR_ODATA_Msk (0xffffffffu << AESB_ODATAR_ODATA_Pos) /**< \brief (AESB_ODATAR[4]) Output Data */
/* -------- AESB_IVR[4] : (AESB Offset: 0x60) Initialization Vector Register -------- */
#define AESB_IVR_IV_Pos 0
#define AESB_IVR_IV_Msk (0xffffffffu << AESB_IVR_IV_Pos) /**< \brief (AESB_IVR[4]) Initialization Vector */
#define AESB_IVR_IV(value) ((AESB_IVR_IV_Msk & ((value) << AESB_IVR_IV_Pos)))
/* -------- AESB_VERSION : (AESB Offset: 0xFC) Version Register -------- */
#define AESB_VERSION_VERSION_Pos 0
#define AESB_VERSION_VERSION_Msk (0xfffu << AESB_VERSION_VERSION_Pos) /**< \brief (AESB_VERSION) Version of the Hardware Module */
#define AESB_VERSION_MFN_Pos 16
#define AESB_VERSION_MFN_Msk (0x7u << AESB_VERSION_MFN_Pos) /**< \brief (AESB_VERSION) Metal Fix Number */

/*@}*/


#endif /* _SAMA5D2_AESB_COMPONENT_ */
