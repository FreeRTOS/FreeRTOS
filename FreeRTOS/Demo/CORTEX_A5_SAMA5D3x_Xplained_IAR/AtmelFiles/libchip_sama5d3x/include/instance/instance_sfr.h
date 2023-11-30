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

#ifndef _SAMA5_SFR_INSTANCE_
#define _SAMA5_SFR_INSTANCE_

/* ========== Register definition for SFR peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
#define REG_SFR_OHCIICR             (0xF0038010U) /**< \brief (SFR) OHCI Interrupt Configuration Register */
#define REG_SFR_OHCIISR             (0xF0038014U) /**< \brief (SFR) OHCI Interrupt Status Register */
#define REG_SFR_AHB                 (0xF0038020U) /**< \brief (SFR) AHB Configuration Register */
#define REG_SFR_BRIDGE              (0xF0038024U) /**< \brief (SFR) Bridge Configuration Register */
#define REG_SFR_SECURE              (0xF0038028U) /**< \brief (SFR) Security Configuration Register */
#define REG_SFR_UTMICKTRIM          (0xF0038030U) /**< \brief (SFR) UTMI Clock Trimming Register */
#define REG_SFR_UTMIHSTRIM          (0xF0038034U) /**< \brief (SFR) UTMI High Speed Trimming Register */
#define REG_SFR_UTMIFSTRIM          (0xF0038038U) /**< \brief (SFR) UTMI Full Speed Trimming Register */
#define REG_SFR_UTMISWAP            (0xF003803CU) /**< \brief (SFR) UTMI DP/DM Pin Swapping Register */
#define REG_SFR_EBICFG              (0xF0038040U) /**< \brief (SFR) EBI Configuration Register */
#else
#define REG_SFR_OHCIICR    (*(RwReg*)0xF0038010U) /**< \brief (SFR) OHCI Interrupt Configuration Register */
#define REG_SFR_OHCIISR    (*(RoReg*)0xF0038014U) /**< \brief (SFR) OHCI Interrupt Status Register */
#define REG_SFR_AHB        (*(RwReg*)0xF0038020U) /**< \brief (SFR) AHB Configuration Register */
#define REG_SFR_BRIDGE     (*(RwReg*)0xF0038024U) /**< \brief (SFR) Bridge Configuration Register */
#define REG_SFR_SECURE     (*(RwReg*)0xF0038028U) /**< \brief (SFR) Security Configuration Register */
#define REG_SFR_UTMICKTRIM (*(RwReg*)0xF0038030U) /**< \brief (SFR) UTMI Clock Trimming Register */
#define REG_SFR_UTMIHSTRIM (*(RwReg*)0xF0038034U) /**< \brief (SFR) UTMI High Speed Trimming Register */
#define REG_SFR_UTMIFSTRIM (*(RwReg*)0xF0038038U) /**< \brief (SFR) UTMI Full Speed Trimming Register */
#define REG_SFR_UTMISWAP   (*(RwReg*)0xF003803CU) /**< \brief (SFR) UTMI DP/DM Pin Swapping Register */
#define REG_SFR_EBICFG     (*(RwReg*)0xF0038040U) /**< \brief (SFR) EBI Configuration Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAMA5_SFR_INSTANCE_ */
