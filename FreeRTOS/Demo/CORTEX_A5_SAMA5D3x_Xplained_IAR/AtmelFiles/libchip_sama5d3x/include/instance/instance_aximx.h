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

#ifndef _SAMA5_AXIMX_INSTANCE_
#define _SAMA5_AXIMX_INSTANCE_

/* ========== Register definition for AXIMX peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
#define REG_AXIMX_REMAP                        (0x00800000U) /**< \brief (AXIMX) Remap Register */
#define REG_AXIMX_PERIPH_ID4                   (0x00801FD0U) /**< \brief (AXIMX) Peripheral ID Register 4 */
#define REG_AXIMX_PERIPH_ID5                   (0x00801FD4U) /**< \brief (AXIMX) Peripheral ID Register 5 */
#define REG_AXIMX_PERIPH_ID6                   (0x00801FD8U) /**< \brief (AXIMX) Peripheral ID Register 6 */
#define REG_AXIMX_PERIPH_ID7                   (0x00801FDCU) /**< \brief (AXIMX) Peripheral ID Register 7 */
#define REG_AXIMX_PERIPH_ID0                   (0x00801FE0U) /**< \brief (AXIMX) Peripheral ID Register 0 */
#define REG_AXIMX_PERIPH_ID1                   (0x00801FE4U) /**< \brief (AXIMX) Peripheral ID Register 1 */
#define REG_AXIMX_PERIPH_ID2                   (0x00801FE8U) /**< \brief (AXIMX) Peripheral ID Register 2 */
#define REG_AXIMX_PERIPH_ID3                   (0x00801FECU) /**< \brief (AXIMX) Peripheral ID Register 3 */
#define REG_AXIMX_COMP_ID                      (0x00801FF0U) /**< \brief (AXIMX) Component ID Register */
#define REG_AXIMX_AMIB3_FN_MOD_BM_ISS          (0x00805008U) /**< \brief (AXIMX) AMIB3 Bus Matrix Functionality Modification Register */
#define REG_AXIMX_AMIB3_FN_MOD2                (0x00805024U) /**< \brief (AXIMX) AMIB3 Bypass Merge */
#define REG_AXIMX_ASIB0_READ_QOS               (0x00842100U) /**< \brief (AXIMX) ASIB0 Read Channel QoS Register */
#define REG_AXIMX_ASIB0_WRITE_QOS              (0x00842104U) /**< \brief (AXIMX) ASIB0 Write Channel QoS Register */
#define REG_AXIMX_ASIB1_FN_MOD_AHB             (0x00843028U) /**< \brief (AXIMX) ASIB1 AHB Functionality Modification Register */
#define REG_AXIMX_ASIB1_READ_QOS               (0x00843100U) /**< \brief (AXIMX) ASIB1 Read Channel QoS Register */
#define REG_AXIMX_ASIB1_WRITE_QOS              (0x00843104U) /**< \brief (AXIMX) ASIB1 Write Channel QoS Register */
#define REG_AXIMX_ASIB1_FN_MOD                 (0x00843108U) /**< \brief (AXIMX) ASIB1 Issuing Functionality Modification Register */
#else
#define REG_AXIMX_REMAP               (*(WoReg*)0x00800000U) /**< \brief (AXIMX) Remap Register */
#define REG_AXIMX_PERIPH_ID4          (*(RoReg*)0x00801FD0U) /**< \brief (AXIMX) Peripheral ID Register 4 */
#define REG_AXIMX_PERIPH_ID5          (*(RoReg*)0x00801FD4U) /**< \brief (AXIMX) Peripheral ID Register 5 */
#define REG_AXIMX_PERIPH_ID6          (*(RoReg*)0x00801FD8U) /**< \brief (AXIMX) Peripheral ID Register 6 */
#define REG_AXIMX_PERIPH_ID7          (*(RoReg*)0x00801FDCU) /**< \brief (AXIMX) Peripheral ID Register 7 */
#define REG_AXIMX_PERIPH_ID0          (*(RoReg*)0x00801FE0U) /**< \brief (AXIMX) Peripheral ID Register 0 */
#define REG_AXIMX_PERIPH_ID1          (*(RoReg*)0x00801FE4U) /**< \brief (AXIMX) Peripheral ID Register 1 */
#define REG_AXIMX_PERIPH_ID2          (*(RoReg*)0x00801FE8U) /**< \brief (AXIMX) Peripheral ID Register 2 */
#define REG_AXIMX_PERIPH_ID3          (*(RoReg*)0x00801FECU) /**< \brief (AXIMX) Peripheral ID Register 3 */
#define REG_AXIMX_COMP_ID             (*(RoReg*)0x00801FF0U) /**< \brief (AXIMX) Component ID Register */
#define REG_AXIMX_AMIB3_FN_MOD_BM_ISS (*(RwReg*)0x00805008U) /**< \brief (AXIMX) AMIB3 Bus Matrix Functionality Modification Register */
#define REG_AXIMX_AMIB3_FN_MOD2       (*(RwReg*)0x00805024U) /**< \brief (AXIMX) AMIB3 Bypass Merge */
#define REG_AXIMX_ASIB0_READ_QOS      (*(RwReg*)0x00842100U) /**< \brief (AXIMX) ASIB0 Read Channel QoS Register */
#define REG_AXIMX_ASIB0_WRITE_QOS     (*(RwReg*)0x00842104U) /**< \brief (AXIMX) ASIB0 Write Channel QoS Register */
#define REG_AXIMX_ASIB1_FN_MOD_AHB    (*(RwReg*)0x00843028U) /**< \brief (AXIMX) ASIB1 AHB Functionality Modification Register */
#define REG_AXIMX_ASIB1_READ_QOS      (*(RwReg*)0x00843100U) /**< \brief (AXIMX) ASIB1 Read Channel QoS Register */
#define REG_AXIMX_ASIB1_WRITE_QOS     (*(RwReg*)0x00843104U) /**< \brief (AXIMX) ASIB1 Write Channel QoS Register */
#define REG_AXIMX_ASIB1_FN_MOD        (*(RwReg*)0x00843108U) /**< \brief (AXIMX) ASIB1 Issuing Functionality Modification Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAMA5_AXIMX_INSTANCE_ */
