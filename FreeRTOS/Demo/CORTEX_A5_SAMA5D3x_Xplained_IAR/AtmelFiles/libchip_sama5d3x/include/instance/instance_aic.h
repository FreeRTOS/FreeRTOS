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

#ifndef _SAMA5_AIC_INSTANCE_
#define _SAMA5_AIC_INSTANCE_

/* ========== Register definition for AIC peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
#define REG_AIC_SSR            (0xFFFFF000U) /**< \brief (AIC) Source Select Register */
#define REG_AIC_SMR            (0xFFFFF004U) /**< \brief (AIC) Source Mode Register */
#define REG_AIC_SVR            (0xFFFFF008U) /**< \brief (AIC) Source Vector Register */
#define REG_AIC_IVR            (0xFFFFF010U) /**< \brief (AIC) Interrupt Vector Register */
#define REG_AIC_FVR            (0xFFFFF014U) /**< \brief (AIC) FIQ Interrupt Vector Register */
#define REG_AIC_ISR            (0xFFFFF018U) /**< \brief (AIC) Interrupt Status Register */
#define REG_AIC_IPR0           (0xFFFFF020U) /**< \brief (AIC) Interrupt Pending Register 0 */
#define REG_AIC_IPR1           (0xFFFFF024U) /**< \brief (AIC) Interrupt Pending Register 1 */
#define REG_AIC_IPR2           (0xFFFFF028U) /**< \brief (AIC) Interrupt Pending Register 2 */
#define REG_AIC_IPR3           (0xFFFFF02CU) /**< \brief (AIC) Interrupt Pending Register 3 */
#define REG_AIC_IMR            (0xFFFFF030U) /**< \brief (AIC) Interrupt Mask Register */
#define REG_AIC_CISR           (0xFFFFF034U) /**< \brief (AIC) Core Interrupt Status Register */
#define REG_AIC_EOICR          (0xFFFFF038U) /**< \brief (AIC) End of Interrupt Command Register */
#define REG_AIC_SPU            (0xFFFFF03CU) /**< \brief (AIC) Spurious Interrupt Vector Register */
#define REG_AIC_IECR           (0xFFFFF040U) /**< \brief (AIC) Interrupt Enable Command Register */
#define REG_AIC_IDCR           (0xFFFFF044U) /**< \brief (AIC) Interrupt Disable Command Register */
#define REG_AIC_ICCR           (0xFFFFF048U) /**< \brief (AIC) Interrupt Clear Command Register */
#define REG_AIC_ISCR           (0xFFFFF04CU) /**< \brief (AIC) Interrupt Set Command Register */
#define REG_AIC_FFER           (0xFFFFF050U) /**< \brief (AIC) Fast Forcing Enable Register */
#define REG_AIC_FFDR           (0xFFFFF054U) /**< \brief (AIC) Fast Forcing Disable Register */
#define REG_AIC_FFSR           (0xFFFFF058U) /**< \brief (AIC) Fast Forcing Status Register */
#define REG_AIC_DCR            (0xFFFFF06CU) /**< \brief (AIC) Debug Control Register */
#define REG_AIC_WPMR           (0xFFFFF0E4U) /**< \brief (AIC) Write Protect Mode Register */
#define REG_AIC_WPSR           (0xFFFFF0E8U) /**< \brief (AIC) Write Protect Status Register */
#else
#define REG_AIC_SSR   (*(RwReg*)0xFFFFF000U) /**< \brief (AIC) Source Select Register */
#define REG_AIC_SMR   (*(RwReg*)0xFFFFF004U) /**< \brief (AIC) Source Mode Register */
#define REG_AIC_SVR   (*(RwReg*)0xFFFFF008U) /**< \brief (AIC) Source Vector Register */
#define REG_AIC_IVR   (*(RoReg*)0xFFFFF010U) /**< \brief (AIC) Interrupt Vector Register */
#define REG_AIC_FVR   (*(RoReg*)0xFFFFF014U) /**< \brief (AIC) FIQ Interrupt Vector Register */
#define REG_AIC_ISR   (*(RoReg*)0xFFFFF018U) /**< \brief (AIC) Interrupt Status Register */
#define REG_AIC_IPR0  (*(RoReg*)0xFFFFF020U) /**< \brief (AIC) Interrupt Pending Register 0 */
#define REG_AIC_IPR1  (*(RoReg*)0xFFFFF024U) /**< \brief (AIC) Interrupt Pending Register 1 */
#define REG_AIC_IPR2  (*(RoReg*)0xFFFFF028U) /**< \brief (AIC) Interrupt Pending Register 2 */
#define REG_AIC_IPR3  (*(RoReg*)0xFFFFF02CU) /**< \brief (AIC) Interrupt Pending Register 3 */
#define REG_AIC_IMR   (*(RoReg*)0xFFFFF030U) /**< \brief (AIC) Interrupt Mask Register */
#define REG_AIC_CISR  (*(RoReg*)0xFFFFF034U) /**< \brief (AIC) Core Interrupt Status Register */
#define REG_AIC_EOICR (*(WoReg*)0xFFFFF038U) /**< \brief (AIC) End of Interrupt Command Register */
#define REG_AIC_SPU   (*(RwReg*)0xFFFFF03CU) /**< \brief (AIC) Spurious Interrupt Vector Register */
#define REG_AIC_IECR  (*(WoReg*)0xFFFFF040U) /**< \brief (AIC) Interrupt Enable Command Register */
#define REG_AIC_IDCR  (*(WoReg*)0xFFFFF044U) /**< \brief (AIC) Interrupt Disable Command Register */
#define REG_AIC_ICCR  (*(WoReg*)0xFFFFF048U) /**< \brief (AIC) Interrupt Clear Command Register */
#define REG_AIC_ISCR  (*(WoReg*)0xFFFFF04CU) /**< \brief (AIC) Interrupt Set Command Register */
#define REG_AIC_FFER  (*(WoReg*)0xFFFFF050U) /**< \brief (AIC) Fast Forcing Enable Register */
#define REG_AIC_FFDR  (*(WoReg*)0xFFFFF054U) /**< \brief (AIC) Fast Forcing Disable Register */
#define REG_AIC_FFSR  (*(RoReg*)0xFFFFF058U) /**< \brief (AIC) Fast Forcing Status Register */
#define REG_AIC_DCR   (*(RwReg*)0xFFFFF06CU) /**< \brief (AIC) Debug Control Register */
#define REG_AIC_WPMR  (*(RwReg*)0xFFFFF0E4U) /**< \brief (AIC) Write Protect Mode Register */
#define REG_AIC_WPSR  (*(RoReg*)0xFFFFF0E8U) /**< \brief (AIC) Write Protect Status Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAMA5_AIC_INSTANCE_ */
