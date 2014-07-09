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

#ifndef _SAMA5_FUSE_COMPONENT_
#define _SAMA5_FUSE_COMPONENT_

/* ============================================================================= */
/**  SOFTWARE API DEFINITION FOR Fuse Controller */
/* ============================================================================= */
/** \addtogroup SAMA5_FUSE Fuse Controller */
/*@{*/

#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
/** \brief Fuse hardware registers */
typedef struct {
  WoReg FUSE_CR;    /**< \brief (Fuse Offset: 0x00) Fuse Control Register */
  WoReg FUSE_MR;    /**< \brief (Fuse Offset: 0x04) Fuse Mode Register */
  RwReg FUSE_IR;    /**< \brief (Fuse Offset: 0x08) Fuse Index Register */
  RwReg FUSE_DR;    /**< \brief (Fuse Offset: 0x0C) Fuse Data Register */
  RoReg FUSE_SR[8]; /**< \brief (Fuse Offset: 0x10) Fuse Status Register */
} Fuse;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */
/* -------- FUSE_CR : (FUSE Offset: 0x00) Fuse Control Register -------- */
#define FUSE_CR_WRQ (0x1u << 0) /**< \brief (FUSE_CR) Write Request */
#define FUSE_CR_RRQ (0x1u << 1) /**< \brief (FUSE_CR) Read Request */
#define FUSE_CR_KEY_Pos 8
#define FUSE_CR_KEY_Msk (0xffu << FUSE_CR_KEY_Pos) /**< \brief (FUSE_CR) Key code */
#define   FUSE_CR_KEY_VALID (0xFBu << 8) /**< \brief (FUSE_CR) valid key. */
/* -------- FUSE_MR : (FUSE Offset: 0x04) Fuse Mode Register -------- */
#define FUSE_MR_MSK (0x1u << 0) /**< \brief (FUSE_MR) Mask Fuse Status Registers */
/* -------- FUSE_IR : (FUSE Offset: 0x08) Fuse Index Register -------- */
#define FUSE_IR_WS (0x1u << 0) /**< \brief (FUSE_IR) Write Status */
#define FUSE_IR_RS (0x1u << 1) /**< \brief (FUSE_IR) Read Status */
#define FUSE_IR_WSEL_Pos 8
#define FUSE_IR_WSEL_Msk (0xfu << FUSE_IR_WSEL_Pos) /**< \brief (FUSE_IR) Word Selection */
#define FUSE_IR_WSEL(value) ((FUSE_IR_WSEL_Msk & ((value) << FUSE_IR_WSEL_Pos)))
/* -------- FUSE_DR : (FUSE Offset: 0x0C) Fuse Data Register -------- */
#define FUSE_DR_DATA_Pos 0
#define FUSE_DR_DATA_Msk (0xffffffffu << FUSE_DR_DATA_Pos) /**< \brief (FUSE_DR) Data to Program */
#define FUSE_DR_DATA(value) ((FUSE_DR_DATA_Msk & ((value) << FUSE_DR_DATA_Pos)))
/* -------- FUSE_SR[8] : (FUSE Offset: 0x10) Fuse Status Register -------- */
#define FUSE_SR_FUSE_Pos 0
#define FUSE_SR_FUSE_Msk (0xffffffffu << FUSE_SR_FUSE_Pos) /**< \brief (FUSE_SR[8]) Fuse Status */

/*@}*/


#endif /* _SAMA5_FUSE_COMPONENT_ */
