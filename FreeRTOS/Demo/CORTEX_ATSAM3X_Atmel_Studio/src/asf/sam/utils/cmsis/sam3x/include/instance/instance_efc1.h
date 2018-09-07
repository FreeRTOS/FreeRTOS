/**
 * \file
 *
 * Copyright (c) 2012 Atmel Corporation. All rights reserved.
 *
 * \asf_license_start
 *
 * \page License
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 *    this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 *    this list of conditions and the following disclaimer in the documentation
 *    and/or other materials provided with the distribution.
 *
 * 3. The name of Atmel may not be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 * 4. This software may only be redistributed and used in connection with an
 *    Atmel microcontroller product.
 *
 * THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR IMPLIED
 * WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * EXPRESSLY AND SPECIFICALLY DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR
 * ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
 * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
 * ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 *
 * \asf_license_stop
 *
 */

#ifndef _SAM3XA_EFC1_INSTANCE_
#define _SAM3XA_EFC1_INSTANCE_

/* ========== Register definition for EFC1 peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
#define REG_EFC1_FMR           (0x400E0C00U) /**< \brief (EFC1) EEFC Flash Mode Register */
#define REG_EFC1_FCR           (0x400E0C04U) /**< \brief (EFC1) EEFC Flash Command Register */
#define REG_EFC1_FSR           (0x400E0C08U) /**< \brief (EFC1) EEFC Flash Status Register */
#define REG_EFC1_FRR           (0x400E0C0CU) /**< \brief (EFC1) EEFC Flash Result Register */
#else
#define REG_EFC1_FMR  (*(RwReg*)0x400E0C00U) /**< \brief (EFC1) EEFC Flash Mode Register */
#define REG_EFC1_FCR  (*(WoReg*)0x400E0C04U) /**< \brief (EFC1) EEFC Flash Command Register */
#define REG_EFC1_FSR  (*(RoReg*)0x400E0C08U) /**< \brief (EFC1) EEFC Flash Status Register */
#define REG_EFC1_FRR  (*(RoReg*)0x400E0C0CU) /**< \brief (EFC1) EEFC Flash Result Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAM3XA_EFC1_INSTANCE_ */
