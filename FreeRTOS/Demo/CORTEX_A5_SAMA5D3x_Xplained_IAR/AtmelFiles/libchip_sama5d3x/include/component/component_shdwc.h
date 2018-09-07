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

#ifndef _SAMA5_SHDWC_COMPONENT_
#define _SAMA5_SHDWC_COMPONENT_

/* ============================================================================= */
/**  SOFTWARE API DEFINITION FOR Shutdown Controller */
/* ============================================================================= */
/** \addtogroup SAMA5_SHDWC Shutdown Controller */
/*@{*/

#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
/** \brief Shdwc hardware registers */
typedef struct {
  WoReg SHDW_CR; /**< \brief (Shdwc Offset: 0x00) Shutdown Control Register */
  RwReg SHDW_MR; /**< \brief (Shdwc Offset: 0x04) Shutdown Mode Register */
  RoReg SHDW_SR; /**< \brief (Shdwc Offset: 0x08) Shutdown Status Register */
} Shdwc;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */
/* -------- SHDW_CR : (SHDWC Offset: 0x00) Shutdown Control Register -------- */
#define SHDW_CR_SHDW (0x1u << 0) /**< \brief (SHDW_CR) Shutdown Command */
#define SHDW_CR_KEY_Pos 24
#define SHDW_CR_KEY_Msk (0xffu << SHDW_CR_KEY_Pos) /**< \brief (SHDW_CR) Password */
#define SHDW_CR_KEY(value) ((SHDW_CR_KEY_Msk & ((value) << SHDW_CR_KEY_Pos)))
/* -------- SHDW_MR : (SHDWC Offset: 0x04) Shutdown Mode Register -------- */
#define SHDW_MR_WKMODE0_Pos 0
#define SHDW_MR_WKMODE0_Msk (0x3u << SHDW_MR_WKMODE0_Pos) /**< \brief (SHDW_MR) Wake-up Mode 0 */
#define SHDW_MR_WKMODE0(value) ((SHDW_MR_WKMODE0_Msk & ((value) << SHDW_MR_WKMODE0_Pos)))
#define SHDW_MR_CPTWK0_Pos 4
#define SHDW_MR_CPTWK0_Msk (0xfu << SHDW_MR_CPTWK0_Pos) /**< \brief (SHDW_MR) Counter on Wake-up 0 */
#define SHDW_MR_CPTWK0(value) ((SHDW_MR_CPTWK0_Msk & ((value) << SHDW_MR_CPTWK0_Pos)))
#define SHDW_MR_RTCWKEN (0x1u << 17) /**< \brief (SHDW_MR) Real-time Clock Wake-up Enable */
/* -------- SHDW_SR : (SHDWC Offset: 0x08) Shutdown Status Register -------- */
#define SHDW_SR_WAKEUP0 (0x1u << 0) /**< \brief (SHDW_SR) Wake-up 0 Status */
#define SHDW_SR_RTCWK (0x1u << 17) /**< \brief (SHDW_SR) Real-time Clock Wake-up */

/*@}*/


#endif /* _SAMA5_SHDWC_COMPONENT_ */
