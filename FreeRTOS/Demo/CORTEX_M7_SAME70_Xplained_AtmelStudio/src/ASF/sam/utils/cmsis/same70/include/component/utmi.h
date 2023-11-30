/**
 * \file
 *
 * Copyright (c) 2015 Atmel Corporation. All rights reserved.
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
/*
 * Support and FAQ: visit <a href="http://www.atmel.com/design-support/">Atmel Support</a>
 */

#ifndef _SAME70_UTMI_COMPONENT_
#define _SAME70_UTMI_COMPONENT_

/* ============================================================================= */
/**  SOFTWARE API DEFINITION FOR USB Transmitter Interface Macrocell */
/* ============================================================================= */
/** \addtogroup SAME70_UTMI USB Transmitter Interface Macrocell */
/*@{*/

#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
/** \brief Utmi hardware registers */
typedef struct {
  __I  uint32_t Reserved1[4];
  __IO uint32_t UTMI_OHCIICR; /**< \brief (Utmi Offset: 0x10) OHCI Interrupt Configuration Register */
  __I  uint32_t Reserved2[7];
  __IO uint32_t UTMI_CKTRIM;  /**< \brief (Utmi Offset: 0x30) UTMI Clock Trimming Register */
} Utmi;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */
/* -------- UTMI_OHCIICR : (UTMI Offset: 0x10) OHCI Interrupt Configuration Register -------- */
#define UTMI_OHCIICR_RES0 (0x1u << 0) /**< \brief (UTMI_OHCIICR) USB PORTx Reset */
#define UTMI_OHCIICR_ARIE (0x1u << 4) /**< \brief (UTMI_OHCIICR) OHCI Asynchronous Resume Interrupt Enable */
#define UTMI_OHCIICR_APPSTART (0x1u << 5) /**< \brief (UTMI_OHCIICR) Reserved */
#define UTMI_OHCIICR_UDPPUDIS (0x1u << 23) /**< \brief (UTMI_OHCIICR) USB Device Pull-up Disable */
/* -------- UTMI_CKTRIM : (UTMI Offset: 0x30) UTMI Clock Trimming Register -------- */
#define UTMI_CKTRIM_FREQ_Pos 0
#define UTMI_CKTRIM_FREQ_Msk (0x3u << UTMI_CKTRIM_FREQ_Pos) /**< \brief (UTMI_CKTRIM) UTMI Reference Clock Frequency */
#define UTMI_CKTRIM_FREQ(value) ((UTMI_CKTRIM_FREQ_Msk & ((value) << UTMI_CKTRIM_FREQ_Pos)))
#define   UTMI_CKTRIM_FREQ_XTAL12 (0x0u << 0) /**< \brief (UTMI_CKTRIM) 12 MHz reference clock */
#define   UTMI_CKTRIM_FREQ_XTAL16 (0x1u << 0) /**< \brief (UTMI_CKTRIM) 16 MHz reference clock */

/*@}*/


#endif /* _SAME70_UTMI_COMPONENT_ */
