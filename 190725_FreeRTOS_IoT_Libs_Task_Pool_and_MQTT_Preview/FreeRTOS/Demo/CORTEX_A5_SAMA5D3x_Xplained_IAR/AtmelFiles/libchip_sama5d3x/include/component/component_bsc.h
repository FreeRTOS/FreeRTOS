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

#ifndef _SAMA5_BSC_COMPONENT_
#define _SAMA5_BSC_COMPONENT_

/* ============================================================================= */
/**  SOFTWARE API DEFINITION FOR Boot Sequence Controller */
/* ============================================================================= */
/** \addtogroup SAMA5_BSC Boot Sequence Controller */
/*@{*/

#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
/** \brief Bsc hardware registers */
typedef struct {
  RwReg BSC_CR; /**< \brief (Bsc Offset: 0x0) Boot Sequence Configuration Register */
} Bsc;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */
/* -------- BSC_CR : (BSC Offset: 0x0) Boot Sequence Configuration Register -------- */
#define BSC_CR_BOOT_Pos 0
#define BSC_CR_BOOT_Msk (0xffu << BSC_CR_BOOT_Pos) /**< \brief (BSC_CR) Boot media sequence */
#define BSC_CR_BOOT(value) ((BSC_CR_BOOT_Msk & ((value) << BSC_CR_BOOT_Pos)))
#define BSC_CR_BOOTKEY_Pos 16
#define BSC_CR_BOOTKEY_Msk (0xffffu << BSC_CR_BOOTKEY_Pos) /**< \brief (BSC_CR)  */
#define   BSC_CR_BOOTKEY_BSC_KEY (0x6683u << 16) /**< \brief (BSC_CR) valid key to write BSC_CR register; it needs to be written at the same time as the BOOT field. */

/*@}*/


#endif /* _SAMA5_BSC_COMPONENT_ */
