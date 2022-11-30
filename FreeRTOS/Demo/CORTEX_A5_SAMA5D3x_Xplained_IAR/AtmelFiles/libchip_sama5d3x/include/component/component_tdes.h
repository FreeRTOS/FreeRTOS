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

#ifndef _SAMA5_TDES_COMPONENT_
#define _SAMA5_TDES_COMPONENT_

/* ============================================================================= */
/**  SOFTWARE API DEFINITION FOR Triple Data Encryption Standard */
/* ============================================================================= */
/** \addtogroup SAMA5_TDES Triple Data Encryption Standard */
/*@{*/

#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
/** \brief Tdes hardware registers */
typedef struct {
  WoReg TDES_CR;        /**< \brief (Tdes Offset: 0x00) Control Register */
  RwReg TDES_MR;        /**< \brief (Tdes Offset: 0x04) Mode Register */
  RoReg Reserved1[2];
  WoReg TDES_IER;       /**< \brief (Tdes Offset: 0x10) Interrupt Enable Register */
  WoReg TDES_IDR;       /**< \brief (Tdes Offset: 0x14) Interrupt Disable Register */
  RoReg TDES_IMR;       /**< \brief (Tdes Offset: 0x18) Interrupt Mask Register */
  RoReg TDES_ISR;       /**< \brief (Tdes Offset: 0x1C) Interrupt Status Register */
  WoReg TDES_KEY1WR[2]; /**< \brief (Tdes Offset: 0x20) Key 1 Word Register */
  WoReg TDES_KEY2WR[2]; /**< \brief (Tdes Offset: 0x28) Key 2 Word Register */
  WoReg TDES_KEY3WR[2]; /**< \brief (Tdes Offset: 0x30) Key 3 Word Register */
  RoReg Reserved2[2];
  WoReg TDES_IDATAR[2]; /**< \brief (Tdes Offset: 0x40) Input Data Register */
  RoReg Reserved3[2];
  RoReg TDES_ODATAR[2]; /**< \brief (Tdes Offset: 0x50) Output Data Register */
  RoReg Reserved4[2];
  WoReg TDES_IVR[2];    /**< \brief (Tdes Offset: 0x60) Initialization Vector Register */
  RoReg Reserved5[2];
  RwReg TDES_XTEARNDR;  /**< \brief (Tdes Offset: 0x70) XTEA Rounds Register */
} Tdes;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */
/* -------- TDES_CR : (TDES Offset: 0x00) Control Register -------- */
#define TDES_CR_START (0x1u << 0) /**< \brief (TDES_CR) Start Processing */
#define TDES_CR_SWRST (0x1u << 8) /**< \brief (TDES_CR) Software Reset */
#define TDES_CR_LOADSEED (0x1u << 16) /**< \brief (TDES_CR) Load Seed */
/* -------- TDES_MR : (TDES Offset: 0x04) Mode Register -------- */
#define TDES_MR_CIPHER (0x1u << 0) /**< \brief (TDES_MR) Processing Mode */
#define   TDES_MR_CIPHER_DECRYPT (0x0u << 0) /**< \brief (TDES_MR) Decrypts data. */
#define   TDES_MR_CIPHER_ENCRYPT (0x1u << 0) /**< \brief (TDES_MR) Encrypts data. */
#define TDES_MR_TDESMOD_Pos 1
#define TDES_MR_TDESMOD_Msk (0x3u << TDES_MR_TDESMOD_Pos) /**< \brief (TDES_MR) ALGORITHM mode */
#define TDES_MR_TDESMOD(value) ((TDES_MR_TDESMOD_Msk & ((value) << TDES_MR_TDESMOD_Pos)))
#define TDES_MR_KEYMOD (0x1u << 4) /**< \brief (TDES_MR) Key Mode */
#define TDES_MR_SMOD_Pos 8
#define TDES_MR_SMOD_Msk (0x3u << TDES_MR_SMOD_Pos) /**< \brief (TDES_MR) Start Mode */
#define   TDES_MR_SMOD_MANUAL_START (0x0u << 8) /**< \brief (TDES_MR) Manual Mode */
#define   TDES_MR_SMOD_AUTO_START (0x1u << 8) /**< \brief (TDES_MR) Auto Mode */
#define   TDES_MR_SMOD_IDATAR0_START (0x2u << 8) /**< \brief (TDES_MR) TDES_IDATAR0 access only Auto Mode */
#define TDES_MR_OPMOD_Pos 12
#define TDES_MR_OPMOD_Msk (0x3u << TDES_MR_OPMOD_Pos) /**< \brief (TDES_MR) Operation Mode */
#define   TDES_MR_OPMOD_ECB (0x0u << 12) /**< \brief (TDES_MR) ECB: Electronic Code Book mode */
#define   TDES_MR_OPMOD_CBC (0x1u << 12) /**< \brief (TDES_MR) CBC: Cipher Block Chaining mode */
#define   TDES_MR_OPMOD_OFB (0x2u << 12) /**< \brief (TDES_MR) OFB: Output Feedback mode */
#define   TDES_MR_OPMOD_CFB (0x3u << 12) /**< \brief (TDES_MR) CFB: Cipher Feedback mode */
#define TDES_MR_LOD (0x1u << 15) /**< \brief (TDES_MR) Last Output Data Mode */
#define TDES_MR_CFBS_Pos 16
#define TDES_MR_CFBS_Msk (0x3u << TDES_MR_CFBS_Pos) /**< \brief (TDES_MR) Cipher Feedback Data Size */
#define   TDES_MR_CFBS_SIZE_64BIT (0x0u << 16) /**< \brief (TDES_MR) 64-bit */
#define   TDES_MR_CFBS_SIZE_32BIT (0x1u << 16) /**< \brief (TDES_MR) 32-bit */
#define   TDES_MR_CFBS_SIZE_16BIT (0x2u << 16) /**< \brief (TDES_MR) 16-bit */
#define   TDES_MR_CFBS_SIZE_8BIT (0x3u << 16) /**< \brief (TDES_MR) 8-bit */
#define TDES_MR_CKEY_Pos 20
#define TDES_MR_CKEY_Msk (0xfu << TDES_MR_CKEY_Pos) /**< \brief (TDES_MR) Countermeasure Key */
#define TDES_MR_CKEY(value) ((TDES_MR_CKEY_Msk & ((value) << TDES_MR_CKEY_Pos)))
#define TDES_MR_CMTYP1 (0x1u << 24) /**< \brief (TDES_MR) CounterMeasure Type 1 */
#define   TDES_MR_CMTYP1_NO_PAUSE (0x0u << 24) /**< \brief (TDES_MR) Counter-Measure type 1 is disabled */
#define   TDES_MR_CMTYP1_PAUSE (0x1u << 24) /**< \brief (TDES_MR) Counter-Measure type 1 is enabled */
#define TDES_MR_CMTYP2 (0x1u << 25) /**< \brief (TDES_MR) CounterMeasure Type 2 */
#define   TDES_MR_CMTYP2_NO_DUMMY (0x0u << 25) /**< \brief (TDES_MR) Counter-Measure type 2 is disabled */
#define   TDES_MR_CMTYP2_DUMMY (0x1u << 25) /**< \brief (TDES_MR) Counter-Measure type 2 is enabled */
#define TDES_MR_CMTYP3 (0x1u << 26) /**< \brief (TDES_MR) CounterMeasure Type 3 */
#define   TDES_MR_CMTYP3_NO_RESTART (0x0u << 26) /**< \brief (TDES_MR) Counter-Measure type 3 is disabled */
#define   TDES_MR_CMTYP3_RESTART (0x1u << 26) /**< \brief (TDES_MR) Counter-Measure type 3 is enabled */
#define TDES_MR_CMTYP4 (0x1u << 27) /**< \brief (TDES_MR) CounterMeasure Type 4 */
#define   TDES_MR_CMTYP4_NO_IDLECURRENT (0x0u << 27) /**< \brief (TDES_MR) Counter-Measure type 4 is disabled */
#define   TDES_MR_CMTYP4_IDLECURRENT (0x1u << 27) /**< \brief (TDES_MR) Counter-Measure type 4 is enabled */
#define TDES_MR_CMTYP5 (0x1u << 28) /**< \brief (TDES_MR) CounterMeasure Type 5 */
#define   TDES_MR_CMTYP5_NO_ADDACCESS (0x0u << 28) /**< \brief (TDES_MR) Counter-Measure type 5 is disabled */
#define   TDES_MR_CMTYP5_ADDACCESS (0x1u << 28) /**< \brief (TDES_MR) Counter-Measure type 5 is enabled */
/* -------- TDES_IER : (TDES Offset: 0x10) Interrupt Enable Register -------- */
#define TDES_IER_DATRDY (0x1u << 0) /**< \brief (TDES_IER) Data Ready Interrupt Enable */
#define TDES_IER_URAD (0x1u << 8) /**< \brief (TDES_IER) Unspecified Register Access Detection Interrupt Enable */
/* -------- TDES_IDR : (TDES Offset: 0x14) Interrupt Disable Register -------- */
#define TDES_IDR_DATRDY (0x1u << 0) /**< \brief (TDES_IDR) Data Ready Interrupt Disable */
#define TDES_IDR_URAD (0x1u << 8) /**< \brief (TDES_IDR) Unspecified Register Access Detection Interrupt Disable */
/* -------- TDES_IMR : (TDES Offset: 0x18) Interrupt Mask Register -------- */
#define TDES_IMR_DATRDY (0x1u << 0) /**< \brief (TDES_IMR) Data Ready Interrupt Mask */
#define TDES_IMR_URAD (0x1u << 8) /**< \brief (TDES_IMR) Unspecified Register Access Detection Interrupt Mask */
/* -------- TDES_ISR : (TDES Offset: 0x1C) Interrupt Status Register -------- */
#define TDES_ISR_DATRDY (0x1u << 0) /**< \brief (TDES_ISR) Data Ready */
#define TDES_ISR_URAD (0x1u << 8) /**< \brief (TDES_ISR) Unspecified Register Access Detection Status */
#define TDES_ISR_URAT_Pos 12
#define TDES_ISR_URAT_Msk (0x3u << TDES_ISR_URAT_Pos) /**< \brief (TDES_ISR) Unspecified Register Access */
#define   TDES_ISR_URAT_IDR_WR_PROCESSING (0x0u << 12) /**< \brief (TDES_ISR) Input Data Register written during the data processing when SMOD=0x2 mode. */
#define   TDES_ISR_URAT_ODR_RD_PROCESSING (0x1u << 12) /**< \brief (TDES_ISR) Output Data Register read during the data processing. */
#define   TDES_ISR_URAT_MR_WR_PROCESSING (0x2u << 12) /**< \brief (TDES_ISR) Mode Register written during the data processing. */
#define   TDES_ISR_URAT_WOR_RD_ACCESS (0x3u << 12) /**< \brief (TDES_ISR) Write-only register read access. */
/* -------- TDES_KEY1WR[2] : (TDES Offset: 0x20) Key 1 Word Register -------- */
#define TDES_KEY1WR_KEY1W_Pos 0
#define TDES_KEY1WR_KEY1W_Msk (0xffffffffu << TDES_KEY1WR_KEY1W_Pos) /**< \brief (TDES_KEY1WR[2]) Key 1 Word */
#define TDES_KEY1WR_KEY1W(value) ((TDES_KEY1WR_KEY1W_Msk & ((value) << TDES_KEY1WR_KEY1W_Pos)))
/* -------- TDES_KEY2WR[2] : (TDES Offset: 0x28) Key 2 Word Register -------- */
#define TDES_KEY2WR_KEY2W_Pos 0
#define TDES_KEY2WR_KEY2W_Msk (0xffffffffu << TDES_KEY2WR_KEY2W_Pos) /**< \brief (TDES_KEY2WR[2]) Key 2 Word */
#define TDES_KEY2WR_KEY2W(value) ((TDES_KEY2WR_KEY2W_Msk & ((value) << TDES_KEY2WR_KEY2W_Pos)))
/* -------- TDES_KEY3WR[2] : (TDES Offset: 0x30) Key 3 Word Register -------- */
#define TDES_KEY3WR_KEY3W_Pos 0
#define TDES_KEY3WR_KEY3W_Msk (0xffffffffu << TDES_KEY3WR_KEY3W_Pos) /**< \brief (TDES_KEY3WR[2]) Key 3 Word */
#define TDES_KEY3WR_KEY3W(value) ((TDES_KEY3WR_KEY3W_Msk & ((value) << TDES_KEY3WR_KEY3W_Pos)))
/* -------- TDES_IDATAR[2] : (TDES Offset: 0x40) Input Data Register -------- */
#define TDES_IDATAR_IDATA_Pos 0
#define TDES_IDATAR_IDATA_Msk (0xffffffffu << TDES_IDATAR_IDATA_Pos) /**< \brief (TDES_IDATAR[2]) Input Data */
#define TDES_IDATAR_IDATA(value) ((TDES_IDATAR_IDATA_Msk & ((value) << TDES_IDATAR_IDATA_Pos)))
/* -------- TDES_ODATAR[2] : (TDES Offset: 0x50) Output Data Register -------- */
#define TDES_ODATAR_ODATA_Pos 0
#define TDES_ODATAR_ODATA_Msk (0xffffffffu << TDES_ODATAR_ODATA_Pos) /**< \brief (TDES_ODATAR[2]) Output Data */
/* -------- TDES_IVR[2] : (TDES Offset: 0x60) Initialization Vector Register -------- */
#define TDES_IVR_IV_Pos 0
#define TDES_IVR_IV_Msk (0xffffffffu << TDES_IVR_IV_Pos) /**< \brief (TDES_IVR[2]) Initialization Vector */
#define TDES_IVR_IV(value) ((TDES_IVR_IV_Msk & ((value) << TDES_IVR_IV_Pos)))

/*@}*/


#endif /* _SAMA5_TDES_COMPONENT_ */
