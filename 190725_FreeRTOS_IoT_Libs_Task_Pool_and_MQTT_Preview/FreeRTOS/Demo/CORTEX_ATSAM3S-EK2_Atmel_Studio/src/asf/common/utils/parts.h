/**
 * \file
 *
 * \brief Atmel part identification macros
 *
 * Copyright (C) 2012 Atmel Corporation. All rights reserved.
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

#ifndef ATMEL_PARTS_H
#define ATMEL_PARTS_H

/**
 * \defgroup part_macros_group Atmel part identification macros
 *
 * This collection of macros identify which series and families that the various
 * Atmel parts belong to. These can be used to select part-dependent sections of
 * code at compile time.
 *
 * @{
 */

/**
 * \name Convenience macros for part checking
 * @{
 */
//! Check GCC and IAR part definition for 8-bit AVR
#define AVR8_PART_IS_DEFINED(part) \
	(defined(__ ## part ## __) || defined(__AVR_ ## part ## __))

//! Check GCC and IAR part definition for 32-bit AVR
#define AVR32_PART_IS_DEFINED(part) \
	(defined(__AT32 ## part ## __) || defined(__AVR32_ ## part ## __))

//! Check GCC and IAR part definition for SAM
#define SAM_PART_IS_DEFINED(part) (defined(__ ## part ## __))
/** @} */

/**
 * \defgroup uc3_part_macros_group AVR UC3 parts
 * @{
 */

/**
 * \name AVR UC3 A series
 * @{
 */
#define UC3A0 ( \
		AVR32_PART_IS_DEFINED(UC3A0128) || \
		AVR32_PART_IS_DEFINED(UC3A0256) || \
		AVR32_PART_IS_DEFINED(UC3A0512)    \
	)

#define UC3A1 ( \
		AVR32_PART_IS_DEFINED(UC3A1128) || \
		AVR32_PART_IS_DEFINED(UC3A1256) || \
		AVR32_PART_IS_DEFINED(UC3A1512)    \
	)

#define UC3A3 ( \
		AVR32_PART_IS_DEFINED(UC3A364)   || \
		AVR32_PART_IS_DEFINED(UC3A364S)  || \
		AVR32_PART_IS_DEFINED(UC3A3128)  || \
		AVR32_PART_IS_DEFINED(UC3A3128S) || \
		AVR32_PART_IS_DEFINED(UC3A3256)  || \
		AVR32_PART_IS_DEFINED(UC3A3256S)    \
	)

#define UC3A4 ( \
		AVR32_PART_IS_DEFINED(UC3A464)   || \
		AVR32_PART_IS_DEFINED(UC3A464S)  || \
		AVR32_PART_IS_DEFINED(UC3A4128)  || \
		AVR32_PART_IS_DEFINED(UC3A4128S) || \
		AVR32_PART_IS_DEFINED(UC3A4256)  || \
		AVR32_PART_IS_DEFINED(UC3A4256S)    \
	)
/** @} */

/**
 * \name AVR UC3 B series
 * @{
 */
#define UC3B0 ( \
		AVR32_PART_IS_DEFINED(UC3B064)  || \
		AVR32_PART_IS_DEFINED(UC3B0128) || \
		AVR32_PART_IS_DEFINED(UC3B0256) || \
		AVR32_PART_IS_DEFINED(UC3B0512)    \
	)

#define UC3B1 ( \
		AVR32_PART_IS_DEFINED(UC3B164)  || \
		AVR32_PART_IS_DEFINED(UC3B1128) || \
		AVR32_PART_IS_DEFINED(UC3B1256) || \
		AVR32_PART_IS_DEFINED(UC3B1512)    \
	)
/** @} */

/**
 * \name AVR UC3 C series
 * @{
 */
#define UC3C0 ( \
		AVR32_PART_IS_DEFINED(UC3C064C)  || \
		AVR32_PART_IS_DEFINED(UC3C0128C) || \
		AVR32_PART_IS_DEFINED(UC3C0256C) || \
		AVR32_PART_IS_DEFINED(UC3C0512C)    \
	)

#define UC3C1 ( \
		AVR32_PART_IS_DEFINED(UC3C164C)  || \
		AVR32_PART_IS_DEFINED(UC3C1128C) || \
		AVR32_PART_IS_DEFINED(UC3C1256C) || \
		AVR32_PART_IS_DEFINED(UC3C1512C)    \
	)

#define UC3C2 ( \
		AVR32_PART_IS_DEFINED(UC3C264C)  || \
		AVR32_PART_IS_DEFINED(UC3C2128C) || \
		AVR32_PART_IS_DEFINED(UC3C2256C) || \
		AVR32_PART_IS_DEFINED(UC3C2512C)    \
	)
/** @} */

/**
 * \name AVR UC3 D series
 * @{
 */
#define UC3D3 ( \
		AVR32_PART_IS_DEFINED(UC64D3)  || \
		AVR32_PART_IS_DEFINED(UC128D3)    \
	)

#define UC3D4 ( \
		AVR32_PART_IS_DEFINED(UC64D4)  || \
		AVR32_PART_IS_DEFINED(UC128D4)    \
	)
/** @} */

/**
 * \name AVR UC3 L series
 * @{
 */
#define UC3L0 ( \
		AVR32_PART_IS_DEFINED(UC3L016) || \
		AVR32_PART_IS_DEFINED(UC3L032) || \
		AVR32_PART_IS_DEFINED(UC3L064)    \
	)

#define UC3L0128 ( \
		AVR32_PART_IS_DEFINED(UC3L0128) \
	)

#define UC3L0256 ( \
		AVR32_PART_IS_DEFINED(UC3L0256) \
	)

#define UC3L3 ( \
		AVR32_PART_IS_DEFINED(UC64L3U)  || \
		AVR32_PART_IS_DEFINED(UC128L3U) || \
		AVR32_PART_IS_DEFINED(UC256L3U)    \
	)

#define UC3L4 ( \
		AVR32_PART_IS_DEFINED(UC64L4U)  || \
		AVR32_PART_IS_DEFINED(UC128L4U) || \
		AVR32_PART_IS_DEFINED(UC256L4U)    \
	)

#define UC3L3_L4 (UC3L3 || UC3L4)
/** @} */

/**
 * \name AVR UC3 families
 * @{
 */
/** AVR UC3 A family */
#define UC3A (UC3A0 || UC3A1 || UC3A3 || UC3A4)

/** AVR UC3 B family */
#define UC3B (UC3B0 || UC3B1)

/** AVR UC3 C family */
#define UC3C (UC3C0 || UC3C1 || UC3C2)

/** AVR UC3 D family */
#define UC3D (UC3D3 || UC3D4)

/** AVR UC3 L family */
#define UC3L (UC3L0 || UC3L0128 || UC3L0256 || UC3L3_L4)
/** @} */

/** AVR UC3 product line */
#define UC3  (UC3A || UC3B || UC3C || UC3D || UC3L)

/** @} */

/**
 * \defgroup xmega_part_macros_group AVR XMEGA parts
 * @{
 */

/**
 * \name AVR XMEGA A series
 * @{
 */
#define XMEGA_A1 ( \
		AVR8_PART_IS_DEFINED(ATxmega64A1)  || \
		AVR8_PART_IS_DEFINED(ATxmega128A1)    \
	)

#define XMEGA_A3 ( \
		AVR8_PART_IS_DEFINED(ATxmega64A3)  || \
		AVR8_PART_IS_DEFINED(ATxmega128A3) || \
		AVR8_PART_IS_DEFINED(ATxmega192A3) || \
		AVR8_PART_IS_DEFINED(ATxmega256A3)    \
	)

#define XMEGA_A3B ( \
		AVR8_PART_IS_DEFINED(ATxmega256A3B) \
	)

#define XMEGA_A4 ( \
		AVR8_PART_IS_DEFINED(ATxmega16A4) || \
		AVR8_PART_IS_DEFINED(ATxmega32A4)    \
	)
/** @} */

/**
 * \name AVR XMEGA AU series
 * @{
 */
#define XMEGA_A1U ( \
		AVR8_PART_IS_DEFINED(ATxmega64A1U)  || \
		AVR8_PART_IS_DEFINED(ATxmega128A1U)    \
	)

#define XMEGA_A3U ( \
		AVR8_PART_IS_DEFINED(ATxmega64A3U)  || \
		AVR8_PART_IS_DEFINED(ATxmega128A3U) || \
		AVR8_PART_IS_DEFINED(ATxmega192A3U) || \
		AVR8_PART_IS_DEFINED(ATxmega256A3U)    \
	)

#define XMEGA_A3BU ( \
		AVR8_PART_IS_DEFINED(ATxmega256A3BU) \
	)

#define XMEGA_A4U ( \
		AVR8_PART_IS_DEFINED(ATxmega16A4U)  || \
		AVR8_PART_IS_DEFINED(ATxmega32A4U)  || \
		AVR8_PART_IS_DEFINED(ATxmega64A4U)  || \
		AVR8_PART_IS_DEFINED(ATxmega128A4U)    \
	)
/** @} */

/**
 * \name AVR XMEGA B series
 * @{
 */
#define XMEGA_B1  ( \
		AVR8_PART_IS_DEFINED(ATxmega64B1)  || \
		AVR8_PART_IS_DEFINED(ATxmega128B1)    \
	)

#define XMEGA_B3  ( \
		AVR8_PART_IS_DEFINED(ATxmega64B3)  || \
		AVR8_PART_IS_DEFINED(ATxmega128B3)    \
	)
/** @} */

/**
 * \name AVR XMEGA C series
 * @{
 */
#define XMEGA_C3 ( \
		AVR8_PART_IS_DEFINED(ATxmega384C3)  || \
		AVR8_PART_IS_DEFINED(ATxmega256C3)     \
	)

#define XMEGA_C4 ( \
		AVR8_PART_IS_DEFINED(ATxmega32C4)  || \
		AVR8_PART_IS_DEFINED(ATxmega16C4)     \
	)
/** @} */

/**
 * \name AVR XMEGA D series
 * @{
 */
#define XMEGA_D3 ( \
		AVR8_PART_IS_DEFINED(ATxmega64D3)  || \
		AVR8_PART_IS_DEFINED(ATxmega128D3) || \
		AVR8_PART_IS_DEFINED(ATxmega192D3) || \
		AVR8_PART_IS_DEFINED(ATxmega256D3) || \
		AVR8_PART_IS_DEFINED(ATxmega384D3)    \
	)

#define XMEGA_D4 ( \
		AVR8_PART_IS_DEFINED(ATxmega16D4)  || \
		AVR8_PART_IS_DEFINED(ATxmega32D4)  || \
		AVR8_PART_IS_DEFINED(ATxmega64D4)  || \
		AVR8_PART_IS_DEFINED(ATxmega128D4)    \
	)
/** @} */

/**
 * \name AVR XMEGA families
 * @{
 */
/** AVR XMEGA A family */
#define XMEGA_A (XMEGA_A1 || XMEGA_A3 || XMEGA_A3B || XMEGA_A4)

/** AVR XMEGA AU family */
#define XMEGA_AU (XMEGA_A1U || XMEGA_A3U || XMEGA_A3BU || XMEGA_A4U)

/** AVR XMEGA B family */
#define XMEGA_B (XMEGA_B1 || XMEGA_B3)

/** AVR XMEGA C family */
#define XMEGA_C (XMEGA_C3 || XMEGA_C4)

/** AVR XMEGA D family */
#define XMEGA_D (XMEGA_D3 || XMEGA_D4)
/** @} */

/** AVR XMEGA product line */
#define XMEGA (XMEGA_A || XMEGA_AU || XMEGA_B || XMEGA_C || XMEGA_D)

/** @} */

/**
 * \defgroup mega_part_macros_group megaAVR parts
 *
 * \note These megaAVR groupings are based on the groups in AVR Libc for the
 * part header files. They are not names of official megaAVR device series or
 * families.
 *
 * @{
 */

/**
 * \name ATmegaxx0/xx1 subgroups
 * @{
 */
#define MEGA_XX0 ( \
		AVR8_PART_IS_DEFINED(ATmega640)  || \
		AVR8_PART_IS_DEFINED(ATmega1280) || \
		AVR8_PART_IS_DEFINED(ATmega2560)    \
	)

#define MEGA_XX1 ( \
		AVR8_PART_IS_DEFINED(ATmega1281) || \
		AVR8_PART_IS_DEFINED(ATmega2561)    \
	)
/** @} */

/**
 * \name megaAVR groups
 * @{
 */
/** ATmegaxx0/xx1 group */
#define MEGA_XX0_1 (MEGA_XX0 || MEGA_XX1)

/** ATmegaxx4 group */
#define MEGA_XX4 ( \
		AVR8_PART_IS_DEFINED(ATmega164A)  || \
		AVR8_PART_IS_DEFINED(ATmega164PA) || \
		AVR8_PART_IS_DEFINED(ATmega324)   || \
		AVR8_PART_IS_DEFINED(ATmega324A)  || \
		AVR8_PART_IS_DEFINED(ATmega324PA) || \
		AVR8_PART_IS_DEFINED(ATmega644)   || \
		AVR8_PART_IS_DEFINED(ATmega644A)  || \
		AVR8_PART_IS_DEFINED(ATmega644PA) || \
		AVR8_PART_IS_DEFINED(ATmega1284P)    \
	)

/** ATmegaxx4 group */
#define MEGA_XX4_A ( \
		AVR8_PART_IS_DEFINED(ATmega164A)  || \
		AVR8_PART_IS_DEFINED(ATmega164PA) || \
		AVR8_PART_IS_DEFINED(ATmega324A)  || \
		AVR8_PART_IS_DEFINED(ATmega324PA) || \
		AVR8_PART_IS_DEFINED(ATmega644A)  || \
		AVR8_PART_IS_DEFINED(ATmega644PA) || \
		AVR8_PART_IS_DEFINED(ATmega1284P)    \
	)

/** ATmegaxx8 group */
#define MEGA_XX8 ( \
		AVR8_PART_IS_DEFINED(ATmega48)    || \
		AVR8_PART_IS_DEFINED(ATmega48A)   || \
		AVR8_PART_IS_DEFINED(ATmega48PA)  || \
		AVR8_PART_IS_DEFINED(ATmega88)    || \
		AVR8_PART_IS_DEFINED(ATmega88A)   || \
		AVR8_PART_IS_DEFINED(ATmega88PA)  || \
		AVR8_PART_IS_DEFINED(ATmega168)   || \
		AVR8_PART_IS_DEFINED(ATmega168A)  || \
		AVR8_PART_IS_DEFINED(ATmega168PA) || \
		AVR8_PART_IS_DEFINED(ATmega328)   || \
		AVR8_PART_IS_DEFINED(ATmega328P)     \
	)

/** ATmegaxx8A/P/PA group */
#define MEGA_XX8_A ( \
		AVR8_PART_IS_DEFINED(ATmega48A)   || \
		AVR8_PART_IS_DEFINED(ATmega48PA)  || \
		AVR8_PART_IS_DEFINED(ATmega88A)   || \
		AVR8_PART_IS_DEFINED(ATmega88PA)  || \
		AVR8_PART_IS_DEFINED(ATmega168A)  || \
		AVR8_PART_IS_DEFINED(ATmega168PA) || \
		AVR8_PART_IS_DEFINED(ATmega328P)     \
	)

/** ATmegaxx group */
#define MEGA_XX ( \
		AVR8_PART_IS_DEFINED(ATmega16)   || \
		AVR8_PART_IS_DEFINED(ATmega16A)  || \
		AVR8_PART_IS_DEFINED(ATmega32)   || \
		AVR8_PART_IS_DEFINED(ATmega32A)  || \
		AVR8_PART_IS_DEFINED(ATmega64)   || \
		AVR8_PART_IS_DEFINED(ATmega64A)  || \
		AVR8_PART_IS_DEFINED(ATmega128)  || \
		AVR8_PART_IS_DEFINED(ATmega128A)    \
	)

/** ATmegaxxA/P/PA group */
#define MEGA_XX_A ( \
		AVR8_PART_IS_DEFINED(ATmega16A)  || \
		AVR8_PART_IS_DEFINED(ATmega32A)  || \
		AVR8_PART_IS_DEFINED(ATmega64A)  || \
		AVR8_PART_IS_DEFINED(ATmega128A)    \
	)

/** Unspecified group */
#define MEGA_UNSPECIFIED ( \
		AVR8_PART_IS_DEFINED(ATmega16)    || \
		AVR8_PART_IS_DEFINED(ATmega16A)   || \
		AVR8_PART_IS_DEFINED(ATmega32)    || \
		AVR8_PART_IS_DEFINED(ATmega32A)   || \
		AVR8_PART_IS_DEFINED(ATmega64)    || \
		AVR8_PART_IS_DEFINED(ATmega64A)   || \
		AVR8_PART_IS_DEFINED(ATmega128)   || \
		AVR8_PART_IS_DEFINED(ATmega128A)  || \
		AVR8_PART_IS_DEFINED(ATmega169P)  || \
		AVR8_PART_IS_DEFINED(ATmega169PA) || \
		AVR8_PART_IS_DEFINED(ATmega329P)  || \
		AVR8_PART_IS_DEFINED(ATmega329PA)    \
	)
/** @} */

/** megaAVR product line */
#define MEGA (MEGA_XX0_1 || MEGA_XX4 || MEGA_XX8 || MEGA_XX || MEGA_UNSPECIFIED)

/** @} */

/**
 * \defgroup sam_part_macros_group SAM parts
 * @{
 */

/**
 * \name SAM3S series
 * @{
 */
#define SAM3S1 ( \
		SAM_PART_IS_DEFINED(SAM3S1A) || \
		SAM_PART_IS_DEFINED(SAM3S1B) || \
		SAM_PART_IS_DEFINED(SAM3S1C)    \
	)

#define SAM3S2 ( \
		SAM_PART_IS_DEFINED(SAM3S2A) || \
		SAM_PART_IS_DEFINED(SAM3S2B) || \
		SAM_PART_IS_DEFINED(SAM3S2C)    \
	)

#define SAM3S4 ( \
		SAM_PART_IS_DEFINED(SAM3S4A) || \
		SAM_PART_IS_DEFINED(SAM3S4B) || \
		SAM_PART_IS_DEFINED(SAM3S4C)    \
	)

#define SAM3S8 ( \
		SAM_PART_IS_DEFINED(SAM3S8B) || \
		SAM_PART_IS_DEFINED(SAM3S8C)    \
	)

#define SAM3SD8 ( \
		SAM_PART_IS_DEFINED(SAM3SD8B) || \
		SAM_PART_IS_DEFINED(SAM3SD8C)    \
	)
/** @} */

/**
 * \name SAM3U series
 * @{
 */
#define SAM3U1 ( \
		SAM_PART_IS_DEFINED(SAM3U1C) || \
		SAM_PART_IS_DEFINED(SAM3U1E)    \
	)

#define SAM3U2 ( \
		SAM_PART_IS_DEFINED(SAM3U2C) || \
		SAM_PART_IS_DEFINED(SAM3U2E)    \
	)

#define SAM3U4 ( \
		SAM_PART_IS_DEFINED(SAM3U4C) || \
		SAM_PART_IS_DEFINED(SAM3U4E)    \
	)
/** @} */

/**
 * \name SAM3N series
 * @{
 */
#define SAM3N1 ( \
		SAM_PART_IS_DEFINED(SAM3N1A) || \
		SAM_PART_IS_DEFINED(SAM3N1B) || \
		SAM_PART_IS_DEFINED(SAM3N1C)    \
	)

#define SAM3N2 ( \
		SAM_PART_IS_DEFINED(SAM3N2A) || \
		SAM_PART_IS_DEFINED(SAM3N2B) || \
		SAM_PART_IS_DEFINED(SAM3N2C)    \
	)

#define SAM3N4 ( \
		SAM_PART_IS_DEFINED(SAM3N4A) || \
		SAM_PART_IS_DEFINED(SAM3N4B) || \
		SAM_PART_IS_DEFINED(SAM3N4C)    \
	)
/** @} */

/**
 * \name SAM3X series
 * @{
 */
#define SAM3X4 ( \
		SAM_PART_IS_DEFINED(SAM3X4C) || \
		SAM_PART_IS_DEFINED(SAM3X4E)    \
	)

#define SAM3X8 ( \
		SAM_PART_IS_DEFINED(SAM3X8C) || \
		SAM_PART_IS_DEFINED(SAM3X8E) || \
		SAM_PART_IS_DEFINED(SAM3X8H)    \
	)
/** @} */

/**
 * \name SAM3A series
 * @{
 */
#define SAM3A4 ( \
		SAM_PART_IS_DEFINED(SAM3A4C)    \
	)

#define SAM3A8 ( \
		SAM_PART_IS_DEFINED(SAM3A8C)    \
	)
/** @} */

/**
 * \name SAM4S series
 * @{
 */
#define SAM4S8 ( \
		SAM_PART_IS_DEFINED(SAM4S8B) || \
		SAM_PART_IS_DEFINED(SAM4S8C)    \
	)

#define SAM4S16 ( \
		SAM_PART_IS_DEFINED(SAM4S16B) || \
		SAM_PART_IS_DEFINED(SAM4S16C)    \
	)
/** @} */

/**
 * \name SAM families
 * @{
 */
/** SAM3S Family */
#define SAM3S (SAM3S1 || SAM3S2 || SAM3S4 || SAM3S8 || SAM3SD8)

/** SAM3U Family */
#define SAM3U (SAM3U1 || SAM3U2 || SAM3U4)

/** SAM3N Family */
#define SAM3N (SAM3N1 || SAM3N2 || SAM3N4)

/** SAM3XA Family */
#define SAM3XA (SAM3X4 || SAM3X8 || SAM3A4 || SAM3A8)

/** SAM4S Family */
#define SAM4S (SAM4S8 || SAM4S16)
/** @} */

/** SAM product line */
#define SAM (SAM3S || SAM3U || SAM3N || SAM3XA || SAM4S)

/** @} */

/** @} */

#endif /* ATMEL_PARTS_H */
