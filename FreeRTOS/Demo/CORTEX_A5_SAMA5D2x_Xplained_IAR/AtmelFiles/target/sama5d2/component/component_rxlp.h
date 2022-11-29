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

#ifndef _SAMA5D2_RXLP_COMPONENT_
#define _SAMA5D2_RXLP_COMPONENT_

/* ============================================================================= */
/**  SOFTWARE API DEFINITION FOR Low Power Asynchronous Receiver */
/* ============================================================================= */
/** \addtogroup SAMA5D2_RXLP Low Power Asynchronous Receiver */
/*@{*/

#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
/** \brief Rxlp hardware registers */
typedef struct {
  __O  uint32_t RXLP_CR;       /**< \brief (Rxlp Offset: 0x0000) Control Register */
  __IO uint32_t RXLP_MR;       /**< \brief (Rxlp Offset: 0x0004) Mode Register */
  __I  uint32_t Reserved1[4];
  __I  uint32_t RXLP_RHR;      /**< \brief (Rxlp Offset: 0x0018) Receive Holding Register */
  __I  uint32_t Reserved2[1];
  __IO uint32_t RXLP_BRGR;     /**< \brief (Rxlp Offset: 0x0020) Baud Rate Generator Register */
  __IO uint32_t RXLP_CMPR;     /**< \brief (Rxlp Offset: 0x0024) Comparison Register */
  __I  uint32_t Reserved3[47];
  __IO uint32_t RXLP_WPMR;     /**< \brief (Rxlp Offset: 0x00E4) Write Protection Mode Register */
  __I  uint32_t Reserved4[5];
  __I  uint32_t RXLP_VERSION;  /**< \brief (Rxlp Offset: 0x00FC) Version Register */
} Rxlp;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */
/* -------- RXLP_CR : (RXLP Offset: 0x0000) Control Register -------- */
#define RXLP_CR_RSTRX (0x1u << 2) /**< \brief (RXLP_CR) Reset Receiver */
#define RXLP_CR_RXEN (0x1u << 4) /**< \brief (RXLP_CR) Receiver Enable */
#define RXLP_CR_RXDIS (0x1u << 5) /**< \brief (RXLP_CR) Receiver Disable */
/* -------- RXLP_MR : (RXLP Offset: 0x0004) Mode Register -------- */
#define RXLP_MR_FILTER (0x1u << 4) /**< \brief (RXLP_MR) Receiver Digital Filter */
#define   RXLP_MR_FILTER_DISABLED (0x0u << 4) /**< \brief (RXLP_MR) RXLP does not filter the receive line. */
#define   RXLP_MR_FILTER_ENABLED (0x1u << 4) /**< \brief (RXLP_MR) RXLP filters the receive line using a three-sample filter (16x-bit clock) (2 over 3 majority). */
#define RXLP_MR_PAR_Pos 9
#define RXLP_MR_PAR_Msk (0x7u << RXLP_MR_PAR_Pos) /**< \brief (RXLP_MR) Parity Type */
#define RXLP_MR_PAR(value) ((RXLP_MR_PAR_Msk & ((value) << RXLP_MR_PAR_Pos)))
#define   RXLP_MR_PAR_EVEN (0x0u << 9) /**< \brief (RXLP_MR) Even Parity */
#define   RXLP_MR_PAR_ODD (0x1u << 9) /**< \brief (RXLP_MR) Odd Parity */
#define   RXLP_MR_PAR_SPACE (0x2u << 9) /**< \brief (RXLP_MR) Parity forced to 0 */
#define   RXLP_MR_PAR_MARK (0x3u << 9) /**< \brief (RXLP_MR) Parity forced to 1 */
#define   RXLP_MR_PAR_NO (0x4u << 9) /**< \brief (RXLP_MR) No parity */
/* -------- RXLP_RHR : (RXLP Offset: 0x0018) Receive Holding Register -------- */
#define RXLP_RHR_RXCHR_Pos 0
#define RXLP_RHR_RXCHR_Msk (0xffu << RXLP_RHR_RXCHR_Pos) /**< \brief (RXLP_RHR) Received Character */
/* -------- RXLP_BRGR : (RXLP Offset: 0x0020) Baud Rate Generator Register -------- */
#define RXLP_BRGR_CD_Pos 0
#define RXLP_BRGR_CD_Msk (0x3u << RXLP_BRGR_CD_Pos) /**< \brief (RXLP_BRGR) Clock Divisor */
#define RXLP_BRGR_CD(value) ((RXLP_BRGR_CD_Msk & ((value) << RXLP_BRGR_CD_Pos)))
/* -------- RXLP_CMPR : (RXLP Offset: 0x0024) Comparison Register -------- */
#define RXLP_CMPR_VAL1_Pos 0
#define RXLP_CMPR_VAL1_Msk (0xffu << RXLP_CMPR_VAL1_Pos) /**< \brief (RXLP_CMPR) First Comparison Value for Received Character */
#define RXLP_CMPR_VAL1(value) ((RXLP_CMPR_VAL1_Msk & ((value) << RXLP_CMPR_VAL1_Pos)))
#define RXLP_CMPR_VAL2_Pos 16
#define RXLP_CMPR_VAL2_Msk (0xffu << RXLP_CMPR_VAL2_Pos) /**< \brief (RXLP_CMPR) Second Comparison Value for Received Character */
#define RXLP_CMPR_VAL2(value) ((RXLP_CMPR_VAL2_Msk & ((value) << RXLP_CMPR_VAL2_Pos)))
/* -------- RXLP_WPMR : (RXLP Offset: 0x00E4) Write Protection Mode Register -------- */
#define RXLP_WPMR_WPEN (0x1u << 0) /**< \brief (RXLP_WPMR) Write Protection Enable */
#define RXLP_WPMR_WPKEY_Pos 8
#define RXLP_WPMR_WPKEY_Msk (0xffffffu << RXLP_WPMR_WPKEY_Pos) /**< \brief (RXLP_WPMR) Write Protection Key */
#define RXLP_WPMR_WPKEY(value) ((RXLP_WPMR_WPKEY_Msk & ((value) << RXLP_WPMR_WPKEY_Pos)))
#define   RXLP_WPMR_WPKEY_PASSWD (0x52584Cu << 8) /**< \brief (RXLP_WPMR) Writing any other value in this field aborts the write operation.Always reads as 0. */
/* -------- RXLP_VERSION : (RXLP Offset: 0x00FC) Version Register -------- */
#define RXLP_VERSION_VERSION_Pos 0
#define RXLP_VERSION_VERSION_Msk (0xfffu << RXLP_VERSION_VERSION_Pos) /**< \brief (RXLP_VERSION) Hardware Module Version */
#define RXLP_VERSION_MFN_Pos 16
#define RXLP_VERSION_MFN_Msk (0x7u << RXLP_VERSION_MFN_Pos) /**< \brief (RXLP_VERSION) Metal Fix Number */

/*@}*/


#endif /* _SAMA5D2_RXLP_COMPONENT_ */
