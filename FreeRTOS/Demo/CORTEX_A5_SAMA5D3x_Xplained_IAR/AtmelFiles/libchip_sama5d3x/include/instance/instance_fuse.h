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

#ifndef _SAMA5_FUSE_INSTANCE_
#define _SAMA5_FUSE_INSTANCE_

/* ========== Register definition for FUSE peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
#define REG_FUSE_CR             (0xFFFFE400U) /**< \brief (FUSE) Fuse Control Register */
#define REG_FUSE_MR             (0xFFFFE404U) /**< \brief (FUSE) Fuse Mode Register */
#define REG_FUSE_IR             (0xFFFFE408U) /**< \brief (FUSE) Fuse Index Register */
#define REG_FUSE_DR             (0xFFFFE40CU) /**< \brief (FUSE) Fuse Data Register */
#define REG_FUSE_SR             (0xFFFFE410U) /**< \brief (FUSE) Fuse Status Register */
#else
#define REG_FUSE_CR    (*(WoReg*)0xFFFFE400U) /**< \brief (FUSE) Fuse Control Register */
#define REG_FUSE_MR    (*(WoReg*)0xFFFFE404U) /**< \brief (FUSE) Fuse Mode Register */
#define REG_FUSE_IR    (*(RwReg*)0xFFFFE408U) /**< \brief (FUSE) Fuse Index Register */
#define REG_FUSE_DR    (*(RwReg*)0xFFFFE40CU) /**< \brief (FUSE) Fuse Data Register */
#define REG_FUSE_SR    (*(RoReg*)0xFFFFE410U) /**< \brief (FUSE) Fuse Status Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAMA5_FUSE_INSTANCE_ */
