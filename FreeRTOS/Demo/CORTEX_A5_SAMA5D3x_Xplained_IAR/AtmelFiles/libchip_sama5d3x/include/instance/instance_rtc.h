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

#ifndef _SAMA5_RTC_INSTANCE_
#define _SAMA5_RTC_INSTANCE_

/* ========== Register definition for RTC peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
#define REG_RTC_CR              (0xFFFFFEB0U) /**< \brief (RTC) Control Register */
#define REG_RTC_MR              (0xFFFFFEB4U) /**< \brief (RTC) Mode Register */
#define REG_RTC_TIMR            (0xFFFFFEB8U) /**< \brief (RTC) Time Register */
#define REG_RTC_CALR            (0xFFFFFEBCU) /**< \brief (RTC) Calendar Register */
#define REG_RTC_TIMALR          (0xFFFFFEC0U) /**< \brief (RTC) Time Alarm Register */
#define REG_RTC_CALALR          (0xFFFFFEC4U) /**< \brief (RTC) Calendar Alarm Register */
#define REG_RTC_SR              (0xFFFFFEC8U) /**< \brief (RTC) Status Register */
#define REG_RTC_SCCR            (0xFFFFFECCU) /**< \brief (RTC) Status Clear Command Register */
#define REG_RTC_IER             (0xFFFFFED0U) /**< \brief (RTC) Interrupt Enable Register */
#define REG_RTC_IDR             (0xFFFFFED4U) /**< \brief (RTC) Interrupt Disable Register */
#define REG_RTC_IMR             (0xFFFFFED8U) /**< \brief (RTC) Interrupt Mask Register */
#define REG_RTC_VER             (0xFFFFFEDCU) /**< \brief (RTC) Valid Entry Register */
#else
#define REG_RTC_CR     (*(RwReg*)0xFFFFFEB0U) /**< \brief (RTC) Control Register */
#define REG_RTC_MR     (*(RwReg*)0xFFFFFEB4U) /**< \brief (RTC) Mode Register */
#define REG_RTC_TIMR   (*(RwReg*)0xFFFFFEB8U) /**< \brief (RTC) Time Register */
#define REG_RTC_CALR   (*(RwReg*)0xFFFFFEBCU) /**< \brief (RTC) Calendar Register */
#define REG_RTC_TIMALR (*(RwReg*)0xFFFFFEC0U) /**< \brief (RTC) Time Alarm Register */
#define REG_RTC_CALALR (*(RwReg*)0xFFFFFEC4U) /**< \brief (RTC) Calendar Alarm Register */
#define REG_RTC_SR     (*(RoReg*)0xFFFFFEC8U) /**< \brief (RTC) Status Register */
#define REG_RTC_SCCR   (*(WoReg*)0xFFFFFECCU) /**< \brief (RTC) Status Clear Command Register */
#define REG_RTC_IER    (*(WoReg*)0xFFFFFED0U) /**< \brief (RTC) Interrupt Enable Register */
#define REG_RTC_IDR    (*(WoReg*)0xFFFFFED4U) /**< \brief (RTC) Interrupt Disable Register */
#define REG_RTC_IMR    (*(RoReg*)0xFFFFFED8U) /**< \brief (RTC) Interrupt Mask Register */
#define REG_RTC_VER    (*(RoReg*)0xFFFFFEDCU) /**< \brief (RTC) Valid Entry Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAMA5_RTC_INSTANCE_ */
