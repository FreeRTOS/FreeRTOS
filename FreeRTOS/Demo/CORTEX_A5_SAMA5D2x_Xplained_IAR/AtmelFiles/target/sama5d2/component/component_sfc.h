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

#ifndef _SAMA5D2_SFC_COMPONENT_
#define _SAMA5D2_SFC_COMPONENT_

/* ============================================================================= */
/**  SOFTWARE API DEFINITION FOR Secure Fuse Controller */
/* ============================================================================= */
/** \addtogroup SAMA5D2_SFC Secure Fuse Controller */
/*@{*/

#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
/** \brief Sfc hardware registers */
typedef struct {
  __O  uint32_t SFC_KR;        /**< \brief (Sfc Offset: 0x00) SFC Key Register */
  __IO uint32_t SFC_MR;        /**< \brief (Sfc Offset: 0X04) SFC Mode Register */
  __I  uint32_t Reserved1[2];
  __IO uint32_t SFC_IER;       /**< \brief (Sfc Offset: 0x10) SFC Interrupt Enable Register */
  __IO uint32_t SFC_IDR;       /**< \brief (Sfc Offset: 0x14) SFC Interrupt Disable Register */
  __I  uint32_t SFC_IMR;       /**< \brief (Sfc Offset: 0x18) SFC Interrupt Mask Register */
  __I  uint32_t SFC_SR;        /**< \brief (Sfc Offset: 0x1C) SFC Status Register */
  __IO uint32_t SFC_DR[24];    /**< \brief (Sfc Offset: 0x20) SFC Data Register */
  __I  uint32_t Reserved2[31];
  __I  uint32_t SFC_VERSION;   /**< \brief (Sfc Offset: 0xFC) Version Register */
} Sfc;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */
/* -------- SFC_KR : (SFC Offset: 0x00) SFC Key Register -------- */
#define SFC_KR_KEY_Pos 0
#define SFC_KR_KEY_Msk (0xffu << SFC_KR_KEY_Pos) /**< \brief (SFC_KR) Key Code */
#define SFC_KR_KEY(value) ((SFC_KR_KEY_Msk & ((value) << SFC_KR_KEY_Pos)))
/* -------- SFC_MR : (SFC Offset: 0X04) SFC Mode Register -------- */
#define SFC_MR_MSK (0x1u << 0) /**< \brief (SFC_MR) Mask Data Registers */
#define SFC_MR_SASEL (0x1u << 4) /**< \brief (SFC_MR) Sense Amplifier Selection */
/* -------- SFC_IER : (SFC Offset: 0x10) SFC Interrupt Enable Register -------- */
#define SFC_IER_PGMC (0x1u << 0) /**< \brief (SFC_IER) Programming Sequence Completed Interrupt Enable */
#define SFC_IER_PGMF (0x1u << 1) /**< \brief (SFC_IER) Programming Sequence Failed Interrupt Enable */
#define SFC_IER_LCHECK (0x1u << 4) /**< \brief (SFC_IER) Live Integrity Check Error Interrupt Enable */
#define SFC_IER_APLE (0x1u << 16) /**< \brief (SFC_IER) Atmel Programming Lock Error Interrupt Enable */
#define SFC_IER_ACE (0x1u << 17) /**< \brief (SFC_IER) Atmel Check Error Interrupt Enable */
/* -------- SFC_IDR : (SFC Offset: 0x14) SFC Interrupt Disable Register -------- */
#define SFC_IDR_PGMC (0x1u << 0) /**< \brief (SFC_IDR) Programming Sequence Completed Interrupt Disable */
#define SFC_IDR_PGMF (0x1u << 1) /**< \brief (SFC_IDR) Programming Sequence Failed Interrupt Disable */
#define SFC_IDR_LCHECK (0x1u << 4) /**< \brief (SFC_IDR) Live Integrity Check Error Interrupt Disable */
#define SFC_IDR_APLE (0x1u << 16) /**< \brief (SFC_IDR) Atmel Programming Lock Error Interrupt Disable */
#define SFC_IDR_ACE (0x1u << 17) /**< \brief (SFC_IDR) Atmel Check Error Interrupt Disable */
/* -------- SFC_IMR : (SFC Offset: 0x18) SFC Interrupt Mask Register -------- */
#define SFC_IMR_PGMC (0x1u << 0) /**< \brief (SFC_IMR) Programming Sequence Completed Interrupt Mask */
#define SFC_IMR_PGMF (0x1u << 1) /**< \brief (SFC_IMR) Programming Sequence Failed Interrupt Mask */
#define SFC_IMR_LCHECK (0x1u << 4) /**< \brief (SFC_IMR) Live Integrity Checking Error Interrupt Mask */
#define SFC_IMR_APLE (0x1u << 16) /**< \brief (SFC_IMR) Atmel Programming Lock Error Interrupt Mask */
#define SFC_IMR_ACE (0x1u << 17) /**< \brief (SFC_IMR) Atmel Check Error Interrupt Mask */
/* -------- SFC_SR : (SFC Offset: 0x1C) SFC Status Register -------- */
#define SFC_SR_PGMC (0x1u << 0) /**< \brief (SFC_SR) Programming Sequence Completed (cleared on read) */
#define SFC_SR_PGMF (0x1u << 1) /**< \brief (SFC_SR) Programming Sequence Failed (cleared on read) */
#define SFC_SR_LCHECK (0x1u << 4) /**< \brief (SFC_SR) Live Integrity Checking Error (cleared on read) */
#define SFC_SR_APLE (0x1u << 16) /**< \brief (SFC_SR) Atmel Programming Lock Error (cleared on read) */
#define SFC_SR_ACE (0x1u << 17) /**< \brief (SFC_SR) Atmel Check Error (cleared on read) */
/* -------- SFC_DR[24] : (SFC Offset: 0x20) SFC Data Register -------- */
#define SFC_DR_DATA_Pos 0
#define SFC_DR_DATA_Msk (0xffffffffu << SFC_DR_DATA_Pos) /**< \brief (SFC_DR[24]) Fuse Data */
#define SFC_DR_DATA(value) ((SFC_DR_DATA_Msk & ((value) << SFC_DR_DATA_Pos)))
/* -------- SFC_VERSION : (SFC Offset: 0xFC) Version Register -------- */
#define SFC_VERSION_VERSION_Pos 0
#define SFC_VERSION_VERSION_Msk (0xfffu << SFC_VERSION_VERSION_Pos) /**< \brief (SFC_VERSION) Hardware Module Version */
#define SFC_VERSION_MFN_Pos 16
#define SFC_VERSION_MFN_Msk (0x7u << SFC_VERSION_MFN_Pos) /**< \brief (SFC_VERSION) Metal Fix Number */

/*@}*/


#endif /* _SAMA5D2_SFC_COMPONENT_ */
