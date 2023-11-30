/**
 * \file
 *
 * \brief Atmel part identification macros
 *
 * Copyright (C) 2012-2015 Atmel Corporation. All rights reserved.
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
/* ! Check GCC and IAR part definition for 8-bit AVR */
#define AVR8_PART_IS_DEFINED(part) \
	(defined(__ ## part ## __) || defined(__AVR_ ## part ## __))

/* ! Check GCC and IAR part definition for 32-bit AVR */
#define AVR32_PART_IS_DEFINED(part) \
	(defined(__AT32 ## part ## __) || defined(__AVR32_ ## part ## __))

/* ! Check GCC and IAR part definition for SAM */
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
#define UC3A0 (	\
		AVR32_PART_IS_DEFINED(UC3A0128) || \
		AVR32_PART_IS_DEFINED(UC3A0256) || \
		AVR32_PART_IS_DEFINED(UC3A0512)	\
		)

#define UC3A1 (	\
		AVR32_PART_IS_DEFINED(UC3A1128) || \
		AVR32_PART_IS_DEFINED(UC3A1256) || \
		AVR32_PART_IS_DEFINED(UC3A1512)	\
		)

#define UC3A3 (	\
		AVR32_PART_IS_DEFINED(UC3A364)   || \
		AVR32_PART_IS_DEFINED(UC3A364S)  || \
		AVR32_PART_IS_DEFINED(UC3A3128)  || \
		AVR32_PART_IS_DEFINED(UC3A3128S) || \
		AVR32_PART_IS_DEFINED(UC3A3256)  || \
		AVR32_PART_IS_DEFINED(UC3A3256S) \
		)

#define UC3A4 (	\
		AVR32_PART_IS_DEFINED(UC3A464)   || \
		AVR32_PART_IS_DEFINED(UC3A464S)  || \
		AVR32_PART_IS_DEFINED(UC3A4128)  || \
		AVR32_PART_IS_DEFINED(UC3A4128S) || \
		AVR32_PART_IS_DEFINED(UC3A4256)  || \
		AVR32_PART_IS_DEFINED(UC3A4256S) \
		)
/** @} */

/**
 * \name AVR UC3 B series
 * @{
 */
#define UC3B0 (	\
		AVR32_PART_IS_DEFINED(UC3B064)  || \
		AVR32_PART_IS_DEFINED(UC3B0128) || \
		AVR32_PART_IS_DEFINED(UC3B0256) || \
		AVR32_PART_IS_DEFINED(UC3B0512)	\
		)

#define UC3B1 (	\
		AVR32_PART_IS_DEFINED(UC3B164)  || \
		AVR32_PART_IS_DEFINED(UC3B1128) || \
		AVR32_PART_IS_DEFINED(UC3B1256) || \
		AVR32_PART_IS_DEFINED(UC3B1512)	\
		)
/** @} */

/**
 * \name AVR UC3 C series
 * @{
 */
#define UC3C0 (	\
		AVR32_PART_IS_DEFINED(UC3C064C)  || \
		AVR32_PART_IS_DEFINED(UC3C0128C) || \
		AVR32_PART_IS_DEFINED(UC3C0256C) || \
		AVR32_PART_IS_DEFINED(UC3C0512C) \
		)

#define UC3C1 (	\
		AVR32_PART_IS_DEFINED(UC3C164C)  || \
		AVR32_PART_IS_DEFINED(UC3C1128C) || \
		AVR32_PART_IS_DEFINED(UC3C1256C) || \
		AVR32_PART_IS_DEFINED(UC3C1512C) \
		)

#define UC3C2 (	\
		AVR32_PART_IS_DEFINED(UC3C264C)  || \
		AVR32_PART_IS_DEFINED(UC3C2128C) || \
		AVR32_PART_IS_DEFINED(UC3C2256C) || \
		AVR32_PART_IS_DEFINED(UC3C2512C) \
		)
/** @} */

/**
 * \name AVR UC3 D series
 * @{
 */
#define UC3D3 (	\
		AVR32_PART_IS_DEFINED(UC64D3)  || \
		AVR32_PART_IS_DEFINED(UC128D3) \
		)

#define UC3D4 (	\
		AVR32_PART_IS_DEFINED(UC64D4)  || \
		AVR32_PART_IS_DEFINED(UC128D4) \
		)
/** @} */

/**
 * \name AVR UC3 L series
 * @{
 */
#define UC3L0 (	\
		AVR32_PART_IS_DEFINED(UC3L016) || \
		AVR32_PART_IS_DEFINED(UC3L032) || \
		AVR32_PART_IS_DEFINED(UC3L064) \
		)

#define UC3L0128 ( \
		AVR32_PART_IS_DEFINED(UC3L0128)	\
		)

#define UC3L0256 ( \
		AVR32_PART_IS_DEFINED(UC3L0256)	\
		)

#define UC3L3 (	\
		AVR32_PART_IS_DEFINED(UC64L3U)  || \
		AVR32_PART_IS_DEFINED(UC128L3U) || \
		AVR32_PART_IS_DEFINED(UC256L3U)	\
		)

#define UC3L4 (	\
		AVR32_PART_IS_DEFINED(UC64L4U)  || \
		AVR32_PART_IS_DEFINED(UC128L4U) || \
		AVR32_PART_IS_DEFINED(UC256L4U)	\
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
		AVR8_PART_IS_DEFINED(ATxmega128A1) \
		)

#define XMEGA_A3 ( \
		AVR8_PART_IS_DEFINED(ATxmega64A3)  || \
		AVR8_PART_IS_DEFINED(ATxmega128A3) || \
		AVR8_PART_IS_DEFINED(ATxmega192A3) || \
		AVR8_PART_IS_DEFINED(ATxmega256A3) \
		)

#define XMEGA_A3B ( \
		AVR8_PART_IS_DEFINED(ATxmega256A3B) \
		)

#define XMEGA_A4 ( \
		AVR8_PART_IS_DEFINED(ATxmega16A4) || \
		AVR8_PART_IS_DEFINED(ATxmega32A4) \
		)
/** @} */

/**
 * \name AVR XMEGA AU series
 * @{
 */
#define XMEGA_A1U ( \
		AVR8_PART_IS_DEFINED(ATxmega64A1U)  || \
		AVR8_PART_IS_DEFINED(ATxmega128A1U) \
		)

#define XMEGA_A3U ( \
		AVR8_PART_IS_DEFINED(ATxmega64A3U)  || \
		AVR8_PART_IS_DEFINED(ATxmega128A3U) || \
		AVR8_PART_IS_DEFINED(ATxmega192A3U) || \
		AVR8_PART_IS_DEFINED(ATxmega256A3U) \
		)

#define XMEGA_A3BU ( \
		AVR8_PART_IS_DEFINED(ATxmega256A3BU) \
		)

#define XMEGA_A4U ( \
		AVR8_PART_IS_DEFINED(ATxmega16A4U)  || \
		AVR8_PART_IS_DEFINED(ATxmega32A4U)  || \
		AVR8_PART_IS_DEFINED(ATxmega64A4U)  || \
		AVR8_PART_IS_DEFINED(ATxmega128A4U) \
		)
/** @} */

/**
 * \name AVR XMEGA B series
 * @{
 */
#define XMEGA_B1  ( \
		AVR8_PART_IS_DEFINED(ATxmega64B1)  || \
		AVR8_PART_IS_DEFINED(ATxmega128B1) \
		)

#define XMEGA_B3  ( \
		AVR8_PART_IS_DEFINED(ATxmega64B3)  || \
		AVR8_PART_IS_DEFINED(ATxmega128B3) \
		)
/** @} */

/**
 * \name AVR XMEGA C series
 * @{
 */
#define XMEGA_C3 ( \
		AVR8_PART_IS_DEFINED(ATxmega384C3)  || \
		AVR8_PART_IS_DEFINED(ATxmega256C3)  || \
		AVR8_PART_IS_DEFINED(ATxmega192C3)  || \
		AVR8_PART_IS_DEFINED(ATxmega128C3)  || \
		AVR8_PART_IS_DEFINED(ATxmega64C3)   || \
		AVR8_PART_IS_DEFINED(ATxmega32C3) \
		)

#define XMEGA_C4 ( \
		AVR8_PART_IS_DEFINED(ATxmega32C4)  || \
		AVR8_PART_IS_DEFINED(ATxmega16C4) \
		)
/** @} */

/**
 * \name AVR XMEGA D series
 * @{
 */
#define XMEGA_D3 ( \
		AVR8_PART_IS_DEFINED(ATxmega32D3)  || \
		AVR8_PART_IS_DEFINED(ATxmega64D3)  || \
		AVR8_PART_IS_DEFINED(ATxmega128D3) || \
		AVR8_PART_IS_DEFINED(ATxmega192D3) || \
		AVR8_PART_IS_DEFINED(ATxmega256D3) || \
		AVR8_PART_IS_DEFINED(ATxmega384D3) \
		)

#define XMEGA_D4 ( \
		AVR8_PART_IS_DEFINED(ATxmega16D4)  || \
		AVR8_PART_IS_DEFINED(ATxmega32D4)  || \
		AVR8_PART_IS_DEFINED(ATxmega64D4)  || \
		AVR8_PART_IS_DEFINED(ATxmega128D4) \
		)
/** @} */

/**
 * \name AVR XMEGA E series
 * @{
 */
#define XMEGA_E5 ( \
		AVR8_PART_IS_DEFINED(ATxmega8E5)   || \
		AVR8_PART_IS_DEFINED(ATxmega16E5)  || \
		AVR8_PART_IS_DEFINED(ATxmega32E5)     \
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

/** AVR XMEGA E family */
#define XMEGA_E (XMEGA_E5)
/** @} */


/** AVR XMEGA product line */
#define XMEGA (XMEGA_A || XMEGA_AU || XMEGA_B || XMEGA_C || XMEGA_D || XMEGA_E)

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
		AVR8_PART_IS_DEFINED(ATmega2560) \
		)

#define MEGA_XX1 ( \
		AVR8_PART_IS_DEFINED(ATmega1281) || \
		AVR8_PART_IS_DEFINED(ATmega2561) \
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
		AVR8_PART_IS_DEFINED(ATmega324A)  || \
		AVR8_PART_IS_DEFINED(ATmega324PA) || \
		AVR8_PART_IS_DEFINED(ATmega644)   || \
		AVR8_PART_IS_DEFINED(ATmega644A)  || \
		AVR8_PART_IS_DEFINED(ATmega644PA) || \
		AVR8_PART_IS_DEFINED(ATmega1284P)   || \
		AVR8_PART_IS_DEFINED(ATmega128RFA1) \
		)

/** ATmegaxx4 group */
#define MEGA_XX4_A ( \
		AVR8_PART_IS_DEFINED(ATmega164A)  || \
		AVR8_PART_IS_DEFINED(ATmega164PA) || \
		AVR8_PART_IS_DEFINED(ATmega324A)  || \
		AVR8_PART_IS_DEFINED(ATmega324PA) || \
		AVR8_PART_IS_DEFINED(ATmega644A)  || \
		AVR8_PART_IS_DEFINED(ATmega644PA) || \
		AVR8_PART_IS_DEFINED(ATmega1284P) \
		)

/** ATmegaxx8 group */
#define MEGA_XX8 ( \
		AVR8_PART_IS_DEFINED(ATmega48)    || \
		AVR8_PART_IS_DEFINED(ATmega48A)   || \
		AVR8_PART_IS_DEFINED(ATmega48PA)  || \
		AVR8_PART_IS_DEFINED(ATmega48PB)  || \
		AVR8_PART_IS_DEFINED(ATmega88)    || \
		AVR8_PART_IS_DEFINED(ATmega88A)   || \
		AVR8_PART_IS_DEFINED(ATmega88PA)  || \
		AVR8_PART_IS_DEFINED(ATmega88PB)  || \
		AVR8_PART_IS_DEFINED(ATmega168)   || \
		AVR8_PART_IS_DEFINED(ATmega168A)  || \
		AVR8_PART_IS_DEFINED(ATmega168PA) || \
		AVR8_PART_IS_DEFINED(ATmega168PB) || \
		AVR8_PART_IS_DEFINED(ATmega328)   || \
		AVR8_PART_IS_DEFINED(ATmega328P)  || \
		AVR8_PART_IS_DEFINED(ATmega328PB) \
		)

/** ATmegaxx8A/P/PA group */
#define MEGA_XX8_A ( \
		AVR8_PART_IS_DEFINED(ATmega48A)   || \
		AVR8_PART_IS_DEFINED(ATmega48PA)  || \
		AVR8_PART_IS_DEFINED(ATmega88A)   || \
		AVR8_PART_IS_DEFINED(ATmega88PA)  || \
		AVR8_PART_IS_DEFINED(ATmega168A)  || \
		AVR8_PART_IS_DEFINED(ATmega168PA) || \
		AVR8_PART_IS_DEFINED(ATmega328P) \
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
		AVR8_PART_IS_DEFINED(ATmega128A) \
		)

/** ATmegaxxA/P/PA group */
#define MEGA_XX_A ( \
		AVR8_PART_IS_DEFINED(ATmega16A)  || \
		AVR8_PART_IS_DEFINED(ATmega32A)  || \
		AVR8_PART_IS_DEFINED(ATmega64A)  || \
		AVR8_PART_IS_DEFINED(ATmega128A) \
		)
/** ATmegaxxRFA1 group */
#define MEGA_RFA1 ( \
		AVR8_PART_IS_DEFINED(ATmega128RFA1) \
		)

/** ATmegaxxRFR2 group */
#define MEGA_RFR2 ( \
		AVR8_PART_IS_DEFINED(ATmega64RFR2)   || \
		AVR8_PART_IS_DEFINED(ATmega128RFR2)  || \
		AVR8_PART_IS_DEFINED(ATmega256RFR2)  || \
		AVR8_PART_IS_DEFINED(ATmega644RFR2)  || \
		AVR8_PART_IS_DEFINED(ATmega1284RFR2) || \
		AVR8_PART_IS_DEFINED(ATmega2564RFR2) \
		)


/** ATmegaxxRFxx group */
#define MEGA_RF (MEGA_RFA1 || MEGA_RFR2)

/**
 * \name ATmegaxx_un0/un1/un2 subgroups
 * @{
 */
#define MEGA_XX_UN0 ( \
		AVR8_PART_IS_DEFINED(ATmega16)    || \
		AVR8_PART_IS_DEFINED(ATmega16A)   || \
		AVR8_PART_IS_DEFINED(ATmega32)    || \
		AVR8_PART_IS_DEFINED(ATmega32A)	\
		)

/** ATmegaxx group without power reduction and
 *  And interrupt sense register.
 */
#define MEGA_XX_UN1 ( \
		AVR8_PART_IS_DEFINED(ATmega64)    || \
		AVR8_PART_IS_DEFINED(ATmega64A)   || \
		AVR8_PART_IS_DEFINED(ATmega128)   || \
		AVR8_PART_IS_DEFINED(ATmega128A) \
		)

/** ATmegaxx group without power reduction and
 *  And interrupt sense register.
 */
#define MEGA_XX_UN2 ( \
		AVR8_PART_IS_DEFINED(ATmega169P)  || \
		AVR8_PART_IS_DEFINED(ATmega169PA) || \
		AVR8_PART_IS_DEFINED(ATmega329P)  || \
		AVR8_PART_IS_DEFINED(ATmega329PA) \
		)

/** Devices added to complete megaAVR offering.
 *  Please do not use this group symbol as it is not intended
 *  to be permanent: the devices should be regrouped.
 */
#define MEGA_UNCATEGORIZED ( \
		AVR8_PART_IS_DEFINED(AT90CAN128)     || \
		AVR8_PART_IS_DEFINED(AT90CAN32)      || \
		AVR8_PART_IS_DEFINED(AT90CAN64)      || \
		AVR8_PART_IS_DEFINED(AT90PWM1)       || \
		AVR8_PART_IS_DEFINED(AT90PWM216)     || \
		AVR8_PART_IS_DEFINED(AT90PWM2B)      || \
		AVR8_PART_IS_DEFINED(AT90PWM316)     || \
		AVR8_PART_IS_DEFINED(AT90PWM3B)      || \
		AVR8_PART_IS_DEFINED(AT90PWM81)      || \
		AVR8_PART_IS_DEFINED(AT90USB1286)    || \
		AVR8_PART_IS_DEFINED(AT90USB1287)    || \
		AVR8_PART_IS_DEFINED(AT90USB162)     || \
		AVR8_PART_IS_DEFINED(AT90USB646)     || \
		AVR8_PART_IS_DEFINED(AT90USB647)     || \
		AVR8_PART_IS_DEFINED(AT90USB82)      || \
		AVR8_PART_IS_DEFINED(ATmega1284)     || \
		AVR8_PART_IS_DEFINED(ATmega162)      || \
		AVR8_PART_IS_DEFINED(ATmega164P)     || \
		AVR8_PART_IS_DEFINED(ATmega165A)     || \
		AVR8_PART_IS_DEFINED(ATmega165P)     || \
		AVR8_PART_IS_DEFINED(ATmega165PA)    || \
		AVR8_PART_IS_DEFINED(ATmega168P)     || \
		AVR8_PART_IS_DEFINED(ATmega169A)     || \
		AVR8_PART_IS_DEFINED(ATmega16M1)     || \
		AVR8_PART_IS_DEFINED(ATmega16U2)     || \
		AVR8_PART_IS_DEFINED(ATmega16U4)     || \
		AVR8_PART_IS_DEFINED(ATmega256RFA2)  || \
		AVR8_PART_IS_DEFINED(ATmega324P)     || \
		AVR8_PART_IS_DEFINED(ATmega325)      || \
		AVR8_PART_IS_DEFINED(ATmega3250)     || \
		AVR8_PART_IS_DEFINED(ATmega3250A)    || \
		AVR8_PART_IS_DEFINED(ATmega3250P)    || \
		AVR8_PART_IS_DEFINED(ATmega3250PA)   || \
		AVR8_PART_IS_DEFINED(ATmega325A)     || \
		AVR8_PART_IS_DEFINED(ATmega325P)     || \
		AVR8_PART_IS_DEFINED(ATmega325PA)    || \
		AVR8_PART_IS_DEFINED(ATmega329)      || \
		AVR8_PART_IS_DEFINED(ATmega3290)     || \
		AVR8_PART_IS_DEFINED(ATmega3290A)    || \
		AVR8_PART_IS_DEFINED(ATmega3290P)    || \
		AVR8_PART_IS_DEFINED(ATmega3290PA)   || \
		AVR8_PART_IS_DEFINED(ATmega329A)     || \
		AVR8_PART_IS_DEFINED(ATmega32M1)     || \
		AVR8_PART_IS_DEFINED(ATmega32U2)     || \
		AVR8_PART_IS_DEFINED(ATmega32U4)     || \
		AVR8_PART_IS_DEFINED(ATmega48P)      || \
		AVR8_PART_IS_DEFINED(ATmega644P)     || \
		AVR8_PART_IS_DEFINED(ATmega645)      || \
		AVR8_PART_IS_DEFINED(ATmega6450)     || \
		AVR8_PART_IS_DEFINED(ATmega6450A)    || \
		AVR8_PART_IS_DEFINED(ATmega6450P)    || \
		AVR8_PART_IS_DEFINED(ATmega645A)     || \
		AVR8_PART_IS_DEFINED(ATmega645P)     || \
		AVR8_PART_IS_DEFINED(ATmega649)      || \
		AVR8_PART_IS_DEFINED(ATmega6490)     || \
		AVR8_PART_IS_DEFINED(ATmega6490A)    || \
		AVR8_PART_IS_DEFINED(ATmega6490P)    || \
		AVR8_PART_IS_DEFINED(ATmega649A)     || \
		AVR8_PART_IS_DEFINED(ATmega649P)     || \
		AVR8_PART_IS_DEFINED(ATmega64M1)     || \
		AVR8_PART_IS_DEFINED(ATmega64RFA2)   || \
		AVR8_PART_IS_DEFINED(ATmega8)        || \
		AVR8_PART_IS_DEFINED(ATmega8515)     || \
		AVR8_PART_IS_DEFINED(ATmega8535)     || \
		AVR8_PART_IS_DEFINED(ATmega88P)      || \
		AVR8_PART_IS_DEFINED(ATmega8A)       || \
		AVR8_PART_IS_DEFINED(ATmega8U2)         \
	)

/** Unspecified group */
#define MEGA_UNSPECIFIED (MEGA_XX_UN0 || MEGA_XX_UN1 || MEGA_XX_UN2 || \
	MEGA_UNCATEGORIZED)

/** @} */

/** megaAVR product line */
#define MEGA (MEGA_XX0_1 || MEGA_XX4 || MEGA_XX8 || MEGA_XX || MEGA_RF || \
	MEGA_UNSPECIFIED)

/** @} */

/**
 * \defgroup tiny_part_macros_group tinyAVR parts
 *
 * @{
 */

/**
 * \name tinyAVR groups
 * @{
 */

/** Devices added to complete tinyAVR offering.
 *  Please do not use this group symbol as it is not intended
 *  to be permanent: the devices should be regrouped.
 */
#define TINY_UNCATEGORIZED ( \
		AVR8_PART_IS_DEFINED(ATtiny10)    || \
		AVR8_PART_IS_DEFINED(ATtiny13)    || \
		AVR8_PART_IS_DEFINED(ATtiny13A)   || \
		AVR8_PART_IS_DEFINED(ATtiny1634)  || \
		AVR8_PART_IS_DEFINED(ATtiny167)   || \
		AVR8_PART_IS_DEFINED(ATtiny20)    || \
		AVR8_PART_IS_DEFINED(ATtiny2313)  || \
		AVR8_PART_IS_DEFINED(ATtiny2313A) || \
		AVR8_PART_IS_DEFINED(ATtiny24)    || \
		AVR8_PART_IS_DEFINED(ATtiny24A)   || \
		AVR8_PART_IS_DEFINED(ATtiny25)    || \
		AVR8_PART_IS_DEFINED(ATtiny26)    || \
		AVR8_PART_IS_DEFINED(ATtiny261)   || \
		AVR8_PART_IS_DEFINED(ATtiny261A)  || \
		AVR8_PART_IS_DEFINED(ATtiny4)     || \
		AVR8_PART_IS_DEFINED(ATtiny40)    || \
		AVR8_PART_IS_DEFINED(ATtiny4313)  || \
		AVR8_PART_IS_DEFINED(ATtiny43U)   || \
		AVR8_PART_IS_DEFINED(ATtiny44)    || \
		AVR8_PART_IS_DEFINED(ATtiny44A)   || \
		AVR8_PART_IS_DEFINED(ATtiny45)    || \
		AVR8_PART_IS_DEFINED(ATtiny461)   || \
		AVR8_PART_IS_DEFINED(ATtiny461A)  || \
		AVR8_PART_IS_DEFINED(ATtiny48)    || \
		AVR8_PART_IS_DEFINED(ATtiny5)     || \
		AVR8_PART_IS_DEFINED(ATtiny828)   || \
		AVR8_PART_IS_DEFINED(ATtiny84)    || \
		AVR8_PART_IS_DEFINED(ATtiny84A)   || \
		AVR8_PART_IS_DEFINED(ATtiny85)    || \
		AVR8_PART_IS_DEFINED(ATtiny861)   || \
		AVR8_PART_IS_DEFINED(ATtiny861A)  || \
		AVR8_PART_IS_DEFINED(ATtiny87)    || \
		AVR8_PART_IS_DEFINED(ATtiny88)    || \
		AVR8_PART_IS_DEFINED(ATtiny9)        \
	)

/** @} */

/** tinyAVR product line */
#define TINY (TINY_UNCATEGORIZED)

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
		SAM_PART_IS_DEFINED(SAM3S1A) ||	\
		SAM_PART_IS_DEFINED(SAM3S1B) ||	\
		SAM_PART_IS_DEFINED(SAM3S1C) \
		)

#define SAM3S2 ( \
		SAM_PART_IS_DEFINED(SAM3S2A) ||	\
		SAM_PART_IS_DEFINED(SAM3S2B) ||	\
		SAM_PART_IS_DEFINED(SAM3S2C) \
		)

#define SAM3S4 ( \
		SAM_PART_IS_DEFINED(SAM3S4A) ||	\
		SAM_PART_IS_DEFINED(SAM3S4B) ||	\
		SAM_PART_IS_DEFINED(SAM3S4C) \
		)

#define SAM3S8 ( \
		SAM_PART_IS_DEFINED(SAM3S8B) ||	\
		SAM_PART_IS_DEFINED(SAM3S8C) \
		)

#define SAM3SD8 ( \
		SAM_PART_IS_DEFINED(SAM3SD8B) || \
		SAM_PART_IS_DEFINED(SAM3SD8C) \
		)
/** @} */

/**
 * \name SAM3U series
 * @{
 */
#define SAM3U1 ( \
		SAM_PART_IS_DEFINED(SAM3U1C) ||	\
		SAM_PART_IS_DEFINED(SAM3U1E) \
		)

#define SAM3U2 ( \
		SAM_PART_IS_DEFINED(SAM3U2C) ||	\
		SAM_PART_IS_DEFINED(SAM3U2E) \
		)

#define SAM3U4 ( \
		SAM_PART_IS_DEFINED(SAM3U4C) ||	\
		SAM_PART_IS_DEFINED(SAM3U4E) \
		)
/** @} */

/**
 * \name SAM3N series
 * @{
 */
#define SAM3N00 ( \
		SAM_PART_IS_DEFINED(SAM3N00A) ||	\
		SAM_PART_IS_DEFINED(SAM3N00B) \
		)

#define SAM3N0 ( \
		SAM_PART_IS_DEFINED(SAM3N0A) ||	\
		SAM_PART_IS_DEFINED(SAM3N0B) ||	\
		SAM_PART_IS_DEFINED(SAM3N0C) \
		)

#define SAM3N1 ( \
		SAM_PART_IS_DEFINED(SAM3N1A) ||	\
		SAM_PART_IS_DEFINED(SAM3N1B) ||	\
		SAM_PART_IS_DEFINED(SAM3N1C) \
		)

#define SAM3N2 ( \
		SAM_PART_IS_DEFINED(SAM3N2A) ||	\
		SAM_PART_IS_DEFINED(SAM3N2B) ||	\
		SAM_PART_IS_DEFINED(SAM3N2C) \
		)

#define SAM3N4 ( \
		SAM_PART_IS_DEFINED(SAM3N4A) ||	\
		SAM_PART_IS_DEFINED(SAM3N4B) ||	\
		SAM_PART_IS_DEFINED(SAM3N4C) \
		)
/** @} */

/**
 * \name SAM3X series
 * @{
 */
#define SAM3X4 ( \
		SAM_PART_IS_DEFINED(SAM3X4C) ||	\
		SAM_PART_IS_DEFINED(SAM3X4E) \
		)

#define SAM3X8 ( \
		SAM_PART_IS_DEFINED(SAM3X8C) ||	\
		SAM_PART_IS_DEFINED(SAM3X8E) ||	\
		SAM_PART_IS_DEFINED(SAM3X8H) \
		)
/** @} */

/**
 * \name SAM3A series
 * @{
 */
#define SAM3A4 ( \
		SAM_PART_IS_DEFINED(SAM3A4C) \
		)

#define SAM3A8 ( \
		SAM_PART_IS_DEFINED(SAM3A8C) \
		)
/** @} */

/**
 * \name SAM4S series
 * @{
 */
#define SAM4S2 ( \
		SAM_PART_IS_DEFINED(SAM4S2A) || \
 		SAM_PART_IS_DEFINED(SAM4S2B) || \
 		SAM_PART_IS_DEFINED(SAM4S2C) \
 		)

#define SAM4S4 ( \
		SAM_PART_IS_DEFINED(SAM4S4A) || \
 		SAM_PART_IS_DEFINED(SAM4S4B) || \
 		SAM_PART_IS_DEFINED(SAM4S4C) \
 		)

#define SAM4S8 ( \
		SAM_PART_IS_DEFINED(SAM4S8B) ||	\
		SAM_PART_IS_DEFINED(SAM4S8C) \
		)

#define SAM4S16 ( \
		SAM_PART_IS_DEFINED(SAM4S16B) || \
		SAM_PART_IS_DEFINED(SAM4S16C) \
		)

#define SAM4SA16 ( \
		SAM_PART_IS_DEFINED(SAM4SA16B) || \
		SAM_PART_IS_DEFINED(SAM4SA16C)    \
	)

#define SAM4SD16 ( \
		SAM_PART_IS_DEFINED(SAM4SD16B) || \
		SAM_PART_IS_DEFINED(SAM4SD16C)    \
	)

#define SAM4SD32 ( \
		SAM_PART_IS_DEFINED(SAM4SD32B) || \
		SAM_PART_IS_DEFINED(SAM4SD32C)    \
	)
/** @} */

/**
 * \name SAM4L series
 * @{
 */
#define SAM4LS ( \
		SAM_PART_IS_DEFINED(SAM4LS2A) || \
		SAM_PART_IS_DEFINED(SAM4LS2B) || \
		SAM_PART_IS_DEFINED(SAM4LS2C) || \
		SAM_PART_IS_DEFINED(SAM4LS4A) || \
		SAM_PART_IS_DEFINED(SAM4LS4B) || \
		SAM_PART_IS_DEFINED(SAM4LS4C) || \
		SAM_PART_IS_DEFINED(SAM4LS8A) || \
		SAM_PART_IS_DEFINED(SAM4LS8B) || \
		SAM_PART_IS_DEFINED(SAM4LS8C)    \
		)

#define SAM4LC ( \
		SAM_PART_IS_DEFINED(SAM4LC2A) || \
		SAM_PART_IS_DEFINED(SAM4LC2B) || \
		SAM_PART_IS_DEFINED(SAM4LC2C) || \
		SAM_PART_IS_DEFINED(SAM4LC4A) || \
		SAM_PART_IS_DEFINED(SAM4LC4B) || \
		SAM_PART_IS_DEFINED(SAM4LC4C) || \
		SAM_PART_IS_DEFINED(SAM4LC8A) || \
		SAM_PART_IS_DEFINED(SAM4LC8B) || \
		SAM_PART_IS_DEFINED(SAM4LC8C)    \
		)
/** @} */

/**
 * \name SAMD20 series
 * @{
 */
#define SAMD20J ( \
		SAM_PART_IS_DEFINED(SAMD20J14) || \
		SAM_PART_IS_DEFINED(SAMD20J15) || \
		SAM_PART_IS_DEFINED(SAMD20J16) || \
		SAM_PART_IS_DEFINED(SAMD20J17) || \
		SAM_PART_IS_DEFINED(SAMD20J18) \
	)

#define SAMD20G ( \
		SAM_PART_IS_DEFINED(SAMD20G14)  || \
		SAM_PART_IS_DEFINED(SAMD20G15)  || \
		SAM_PART_IS_DEFINED(SAMD20G16)  || \
		SAM_PART_IS_DEFINED(SAMD20G17)  || \
		SAM_PART_IS_DEFINED(SAMD20G17U) || \
		SAM_PART_IS_DEFINED(SAMD20G18)  || \
		SAM_PART_IS_DEFINED(SAMD20G18U) \
	)

#define SAMD20E ( \
		SAM_PART_IS_DEFINED(SAMD20E14) || \
		SAM_PART_IS_DEFINED(SAMD20E15) || \
		SAM_PART_IS_DEFINED(SAMD20E16) || \
		SAM_PART_IS_DEFINED(SAMD20E17) || \
		SAM_PART_IS_DEFINED(SAMD20E18) \
	)
/** @} */

/**
 * \name SAMD21 series
 * @{
 */
#define SAMD21J ( \
		SAM_PART_IS_DEFINED(SAMD21J15A) || \
		SAM_PART_IS_DEFINED(SAMD21J16A) || \
		SAM_PART_IS_DEFINED(SAMD21J17A) || \
		SAM_PART_IS_DEFINED(SAMD21J18A) || \
		SAM_PART_IS_DEFINED(SAMD21J15B) || \
		SAM_PART_IS_DEFINED(SAMD21J16B) \
	)

#define SAMD21G ( \
		SAM_PART_IS_DEFINED(SAMD21G15A) || \
		SAM_PART_IS_DEFINED(SAMD21G16A) || \
		SAM_PART_IS_DEFINED(SAMD21G17A) || \
		SAM_PART_IS_DEFINED(SAMD21G17AU) || \
		SAM_PART_IS_DEFINED(SAMD21G18A) || \
		SAM_PART_IS_DEFINED(SAMD21G18AU) || \
		SAM_PART_IS_DEFINED(SAMD21G15B) || \
		SAM_PART_IS_DEFINED(SAMD21G16B) || \
		SAM_PART_IS_DEFINED(SAMD21G15L) || \
		SAM_PART_IS_DEFINED(SAMD21G16L) \
	)

#define SAMD21GXXL ( \
		SAM_PART_IS_DEFINED(SAMD21G15L) || \
		SAM_PART_IS_DEFINED(SAMD21G16L) \
		)

#define SAMD21E ( \
		SAM_PART_IS_DEFINED(SAMD21E15A) || \
		SAM_PART_IS_DEFINED(SAMD21E16A) || \
		SAM_PART_IS_DEFINED(SAMD21E17A) || \
		SAM_PART_IS_DEFINED(SAMD21E18A) || \
		SAM_PART_IS_DEFINED(SAMD21E15B) || \
		SAM_PART_IS_DEFINED(SAMD21E15BU) || \
		SAM_PART_IS_DEFINED(SAMD21E16B) || \
		SAM_PART_IS_DEFINED(SAMD21E16BU) || \
		SAM_PART_IS_DEFINED(SAMD21E15L) || \
		SAM_PART_IS_DEFINED(SAMD21E16L) \
	)

#define SAMD21EXXL ( \
		SAM_PART_IS_DEFINED(SAMD21E15L) || \
		SAM_PART_IS_DEFINED(SAMD21E16L) \
		)

/** @} */

/**
 * \name SAMR21 series
 * @{
 */
#define SAMR21G ( \
		SAM_PART_IS_DEFINED(SAMR21G16A) || \
		SAM_PART_IS_DEFINED(SAMR21G17A) || \
		SAM_PART_IS_DEFINED(SAMR21G18A) \
	)

#define SAMR21E ( \
		SAM_PART_IS_DEFINED(SAMR21E16A) || \
		SAM_PART_IS_DEFINED(SAMR21E17A) || \
		SAM_PART_IS_DEFINED(SAMR21E18A) || \
		SAM_PART_IS_DEFINED(SAMR21E19A) \
	)
/** @} */

/**
 * \name SAMB11 series
 * @{
 */
#define SAMB11G ( \
		SAM_PART_IS_DEFINED(SAMB11G18A) \
	)
/** @} */

/**
 * \name SAMD09 series
 * @{
 */
#define SAMD09C ( \
		SAM_PART_IS_DEFINED(SAMD09C13A) \
	)

#define SAMD09D ( \
		SAM_PART_IS_DEFINED(SAMD09D14A) \
	)
/** @} */

/**
 * \name SAMD10 series
 * @{
 */
#define SAMD10C ( \
		SAM_PART_IS_DEFINED(SAMD10C12A) || \
		SAM_PART_IS_DEFINED(SAMD10C13A) || \
		SAM_PART_IS_DEFINED(SAMD10C14A) \
	)

#define SAMD10DS ( \
		SAM_PART_IS_DEFINED(SAMD10D12AS) || \
		SAM_PART_IS_DEFINED(SAMD10D13AS) || \
		SAM_PART_IS_DEFINED(SAMD10D14AS) \
	)

#define SAMD10DM ( \
		SAM_PART_IS_DEFINED(SAMD10D12AM) || \
		SAM_PART_IS_DEFINED(SAMD10D13AM) || \
		SAM_PART_IS_DEFINED(SAMD10D14AM) \
	)

#define SAMD10DU ( \
		SAM_PART_IS_DEFINED(SAMD10D14AU) \
	)
/** @} */

/**
 * \name SAMD11 series
 * @{
 */
#define SAMD11C ( \
		SAM_PART_IS_DEFINED(SAMD11C14A) \
	)

#define SAMD11DS ( \
		SAM_PART_IS_DEFINED(SAMD11D14AS) \
	)

#define SAMD11DM ( \
		SAM_PART_IS_DEFINED(SAMD11D14AM) \
	)

#define SAMD11DU ( \
		SAM_PART_IS_DEFINED(SAMD11D14AU) \
	)
/** @} */

/**
 * \name SAML21 series
 * @{
 */
#define SAML21E ( \
		SAM_PART_IS_DEFINED(SAML21E18A) || \
		SAM_PART_IS_DEFINED(SAML21E15B) || \
		SAM_PART_IS_DEFINED(SAML21E16B) || \
		SAM_PART_IS_DEFINED(SAML21E17B) || \
		SAM_PART_IS_DEFINED(SAML21E18B) \
	)

#define SAML21G ( \
		SAM_PART_IS_DEFINED(SAML21G18A) || \
		SAM_PART_IS_DEFINED(SAML21G16B) || \
		SAM_PART_IS_DEFINED(SAML21G17B) || \
		SAM_PART_IS_DEFINED(SAML21G18B) \
	)

#define SAML21J ( \
		SAM_PART_IS_DEFINED(SAML21J18A) || \
		SAM_PART_IS_DEFINED(SAML21J16B) || \
		SAM_PART_IS_DEFINED(SAML21J17B) || \
		SAM_PART_IS_DEFINED(SAML21J18B) \
	)

/* Group for SAML21 A variant: SAML21[E/G/J][18]A */
#define SAML21XXXA ( \
		SAM_PART_IS_DEFINED(SAML21E18A) || \
		SAM_PART_IS_DEFINED(SAML21G18A) || \
		SAM_PART_IS_DEFINED(SAML21J18A) \
	)

/* Group for SAML21 B variant: SAML21[E/G/J][15/16/1718]B */
#define SAML21XXXB ( \
		SAM_PART_IS_DEFINED(SAML21E15B) || \
		SAM_PART_IS_DEFINED(SAML21E16B) || \
		SAM_PART_IS_DEFINED(SAML21E17B) || \
		SAM_PART_IS_DEFINED(SAML21E18B) || \
		SAM_PART_IS_DEFINED(SAML21G16B) || \
		SAM_PART_IS_DEFINED(SAML21G17B) || \
		SAM_PART_IS_DEFINED(SAML21G18B) || \
		SAM_PART_IS_DEFINED(SAML21J16B) || \
		SAM_PART_IS_DEFINED(SAML21J17B) || \
		SAM_PART_IS_DEFINED(SAML21J18B) \
	)

/** @} */

/**
 * \name SAML22 series
 * @{
 */
#define SAML22N ( \
		SAM_PART_IS_DEFINED(SAML22N16A) || \
		SAM_PART_IS_DEFINED(SAML22N17A) || \
		SAM_PART_IS_DEFINED(SAML22N18A) \
	)

#define SAML22G ( \
		SAM_PART_IS_DEFINED(SAML22G16A) || \
		SAM_PART_IS_DEFINED(SAML22G17A) || \
		SAM_PART_IS_DEFINED(SAML22G18A) \
	)

#define SAML22J ( \
		SAM_PART_IS_DEFINED(SAML22J16A) || \
		SAM_PART_IS_DEFINED(SAML22J17A) || \
		SAM_PART_IS_DEFINED(SAML22J18A) \
	)
/** @} */

/**
 * \name SAMDA0 series
 * @{
 */
#define SAMDA0J ( \
		SAM_PART_IS_DEFINED(SAMDA0J14A) || \
		SAM_PART_IS_DEFINED(SAMDA0J15A) || \
		SAM_PART_IS_DEFINED(SAMDA0J16A) \
	)

#define SAMDA0G ( \
		SAM_PART_IS_DEFINED(SAMDA0G14A) || \
		SAM_PART_IS_DEFINED(SAMDA0G15A) || \
		SAM_PART_IS_DEFINED(SAMDA0G16A) \
	)

#define SAMDA0E ( \
		SAM_PART_IS_DEFINED(SAMDA0E14A) || \
		SAM_PART_IS_DEFINED(SAMDA0E15A) || \
		SAM_PART_IS_DEFINED(SAMDA0E16A) \
	)
/** @} */

/**
 * \name SAMDA1 series
 * @{
 */
#define SAMDA1J ( \
		SAM_PART_IS_DEFINED(SAMDA1J14A) || \
		SAM_PART_IS_DEFINED(SAMDA1J15A) || \
		SAM_PART_IS_DEFINED(SAMDA1J16A) \
	)

#define SAMDA1G ( \
		SAM_PART_IS_DEFINED(SAMDA1G14A) || \
		SAM_PART_IS_DEFINED(SAMDA1G15A) || \
		SAM_PART_IS_DEFINED(SAMDA1G16A) \
	)

#define SAMDA1E ( \
		SAM_PART_IS_DEFINED(SAMDA1E14A) || \
		SAM_PART_IS_DEFINED(SAMDA1E15A) || \
		SAM_PART_IS_DEFINED(SAMDA1E16A) \
	)
/** @} */

/**
 * \name SAMC20 series
 * @{
 */
#define SAMC20E ( \
		SAM_PART_IS_DEFINED(SAMC20E15A) || \
		SAM_PART_IS_DEFINED(SAMC20E16A) || \
		SAM_PART_IS_DEFINED(SAMC20E17A) || \
		SAM_PART_IS_DEFINED(SAMC20E18A) \
	)

#define SAMC20G ( \
		SAM_PART_IS_DEFINED(SAMC20G15A) || \
		SAM_PART_IS_DEFINED(SAMC20G16A) || \
		SAM_PART_IS_DEFINED(SAMC20G17A) || \
		SAM_PART_IS_DEFINED(SAMC20G18A) \
	)

#define SAMC20J ( \
		SAM_PART_IS_DEFINED(SAMC20J15A) || \
		SAM_PART_IS_DEFINED(SAMC20J16A) || \
		SAM_PART_IS_DEFINED(SAMC20J17A) || \
		SAM_PART_IS_DEFINED(SAMC20J18A) \
	)
/** @} */

/**
 * \name SAMC21 series
 * @{
 */
#define SAMC21E ( \
		SAM_PART_IS_DEFINED(SAMC21E15A) || \
		SAM_PART_IS_DEFINED(SAMC21E16A) || \
		SAM_PART_IS_DEFINED(SAMC21E17A) || \
		SAM_PART_IS_DEFINED(SAMC21E18A) \
	)

#define SAMC21G ( \
		SAM_PART_IS_DEFINED(SAMC21G15A) || \
		SAM_PART_IS_DEFINED(SAMC21G16A) || \
		SAM_PART_IS_DEFINED(SAMC21G17A) || \
		SAM_PART_IS_DEFINED(SAMC21G18A) \
	)

#define SAMC21J ( \
		SAM_PART_IS_DEFINED(SAMC21J15A) || \
		SAM_PART_IS_DEFINED(SAMC21J16A) || \
		SAM_PART_IS_DEFINED(SAMC21J17A) || \
		SAM_PART_IS_DEFINED(SAMC21J18A) \
	)
/** @} */

/**
 * \name SAM4E series
 * @{
 */
#define SAM4E8 ( \
		SAM_PART_IS_DEFINED(SAM4E8C) || \
		SAM_PART_IS_DEFINED(SAM4E8CB) || \
		SAM_PART_IS_DEFINED(SAM4E8E) \
		)

#define SAM4E16 ( \
		SAM_PART_IS_DEFINED(SAM4E16C) || \
		SAM_PART_IS_DEFINED(SAM4E16CB) || \
		SAM_PART_IS_DEFINED(SAM4E16E) \
		)
/** @} */

/**
 * \name SAM4N series
 * @{
 */
#define SAM4N8 ( \
		SAM_PART_IS_DEFINED(SAM4N8A) || \
		SAM_PART_IS_DEFINED(SAM4N8B) || \
		SAM_PART_IS_DEFINED(SAM4N8C) \
		)

#define SAM4N16 ( \
		SAM_PART_IS_DEFINED(SAM4N16B) || \
		SAM_PART_IS_DEFINED(SAM4N16C) \
		)
/** @} */

/**
 * \name SAM4C series
 * @{
 */
#define SAM4C4_0 ( \
		SAM_PART_IS_DEFINED(SAM4C4C_0) \
		)

#define SAM4C4_1 ( \
		SAM_PART_IS_DEFINED(SAM4C4C_1) \
		)

#define SAM4C4 (SAM4C4_0 || SAM4C4_1)

#define SAM4C8_0 ( \
		SAM_PART_IS_DEFINED(SAM4C8C_0) \
		)

#define SAM4C8_1 ( \
		SAM_PART_IS_DEFINED(SAM4C8C_1) \
		)

#define SAM4C8 (SAM4C8_0 || SAM4C8_1)

#define SAM4C16_0 ( \
		SAM_PART_IS_DEFINED(SAM4C16C_0) \
		)

#define SAM4C16_1 ( \
		SAM_PART_IS_DEFINED(SAM4C16C_1) \
		)

#define SAM4C16 (SAM4C16_0 || SAM4C16_1)

#define SAM4C32_0 ( \
		SAM_PART_IS_DEFINED(SAM4C32C_0) ||\
		SAM_PART_IS_DEFINED(SAM4C32E_0) \
		)

#define SAM4C32_1 ( \
		SAM_PART_IS_DEFINED(SAM4C32C_1) ||\
		SAM_PART_IS_DEFINED(SAM4C32E_1) \
		)


#define SAM4C32 (SAM4C32_0 || SAM4C32_1)

/** @} */

/**
 * \name SAM4CM series
 * @{
 */
#define SAM4CMP8_0 ( \
		SAM_PART_IS_DEFINED(SAM4CMP8C_0) \
		)

#define SAM4CMP8_1 ( \
		SAM_PART_IS_DEFINED(SAM4CMP8C_1) \
		)

#define SAM4CMP8 (SAM4CMP8_0 || SAM4CMP8_1)

#define SAM4CMP16_0 ( \
		SAM_PART_IS_DEFINED(SAM4CMP16C_0) \
		)

#define SAM4CMP16_1 ( \
		SAM_PART_IS_DEFINED(SAM4CMP16C_1) \
		)

#define SAM4CMP16 (SAM4CMP16_0 || SAM4CMP16_1)

#define SAM4CMP32_0 ( \
		SAM_PART_IS_DEFINED(SAM4CMP32C_0) \
		)

#define SAM4CMP32_1 ( \
		SAM_PART_IS_DEFINED(SAM4CMP32C_1) \
		)

#define SAM4CMP32 (SAM4CMP32_0 || SAM4CMP32_1)

#define SAM4CMS4_0 ( \
		SAM_PART_IS_DEFINED(SAM4CMS4C_0) \
		)

#define SAM4CMS4_1 ( \
		SAM_PART_IS_DEFINED(SAM4CMS4C_1) \
		)

#define SAM4CMS4 (SAM4CMS4_0 || SAM4CMS4_1)

#define SAM4CMS8_0 ( \
		SAM_PART_IS_DEFINED(SAM4CMS8C_0) \
		)

#define SAM4CMS8_1 ( \
		SAM_PART_IS_DEFINED(SAM4CMS8C_1) \
		)

#define SAM4CMS8 (SAM4CMS8_0 || SAM4CMS8_1)

#define SAM4CMS16_0 ( \
		SAM_PART_IS_DEFINED(SAM4CMS16C_0) \
		)

#define SAM4CMS16_1 ( \
		SAM_PART_IS_DEFINED(SAM4CMS16C_1) \
		)

#define SAM4CMS16 (SAM4CMS16_0 || SAM4CMS16_1)

#define SAM4CMS32_0 ( \
		SAM_PART_IS_DEFINED(SAM4CMS32C_0) \
		)

#define SAM4CMS32_1 ( \
		SAM_PART_IS_DEFINED(SAM4CMS32C_1) \
		)

#define SAM4CMS32 (SAM4CMS32_0 || SAM4CMS32_1)

/** @} */

/**
 * \name SAM4CP series
 * @{
 */
#define SAM4CP16_0 ( \
		SAM_PART_IS_DEFINED(SAM4CP16B_0) \
		)

#define SAM4CP16_1 ( \
		SAM_PART_IS_DEFINED(SAM4CP16B_1) \
		)

#define SAM4CP16 (SAM4CP16_0 || SAM4CP16_1)
/** @} */

/**
 * \name SAMG series
 * @{
 */
#define SAMG51 ( \
		SAM_PART_IS_DEFINED(SAMG51G18) \
		)

#define SAMG53 ( \
		SAM_PART_IS_DEFINED(SAMG53G19) ||\
		SAM_PART_IS_DEFINED(SAMG53N19) \
		)

#define SAMG54 ( \
		SAM_PART_IS_DEFINED(SAMG54G19) ||\
		SAM_PART_IS_DEFINED(SAMG54J19) ||\
		SAM_PART_IS_DEFINED(SAMG54N19) \
		)

#define SAMG55 ( \
		SAM_PART_IS_DEFINED(SAMG55G18) ||\
		SAM_PART_IS_DEFINED(SAMG55G19) ||\
		SAM_PART_IS_DEFINED(SAMG55J18) ||\
		SAM_PART_IS_DEFINED(SAMG55J19) ||\
		SAM_PART_IS_DEFINED(SAMG55N19) \
		)
/** @} */

/**
 * \name SAMV71 series
 * @{
 */
#define SAMV71J ( \
		SAM_PART_IS_DEFINED(SAMV71J19) || \
		SAM_PART_IS_DEFINED(SAMV71J20) || \
		SAM_PART_IS_DEFINED(SAMV71J21) \
	)

#define SAMV71N ( \
		SAM_PART_IS_DEFINED(SAMV71N19) || \
		SAM_PART_IS_DEFINED(SAMV71N20) || \
		SAM_PART_IS_DEFINED(SAMV71N21) \
	)

#define SAMV71Q ( \
		SAM_PART_IS_DEFINED(SAMV71Q19) || \
		SAM_PART_IS_DEFINED(SAMV71Q20) || \
		SAM_PART_IS_DEFINED(SAMV71Q21) \
	)
/** @} */

/**
 * \name SAMV70 series
 * @{
 */
#define SAMV70J ( \
		SAM_PART_IS_DEFINED(SAMV70J19) || \
		SAM_PART_IS_DEFINED(SAMV70J20) \
	)

#define SAMV70N ( \
		SAM_PART_IS_DEFINED(SAMV70N19) || \
		SAM_PART_IS_DEFINED(SAMV70N20) \
	)

#define SAMV70Q ( \
		SAM_PART_IS_DEFINED(SAMV70Q19) || \
		SAM_PART_IS_DEFINED(SAMV70Q20) \
	)
/** @} */

/**
 * \name SAMS70 series
 * @{
 */
#define SAMS70J ( \
		SAM_PART_IS_DEFINED(SAMS70J19) || \
		SAM_PART_IS_DEFINED(SAMS70J20) || \
		SAM_PART_IS_DEFINED(SAMS70J21) \
	)

#define SAMS70N ( \
		SAM_PART_IS_DEFINED(SAMS70N19) || \
		SAM_PART_IS_DEFINED(SAMS70N20) || \
		SAM_PART_IS_DEFINED(SAMS70N21) \
	)

#define SAMS70Q ( \
		SAM_PART_IS_DEFINED(SAMS70Q19) || \
		SAM_PART_IS_DEFINED(SAMS70Q20) || \
		SAM_PART_IS_DEFINED(SAMS70Q21) \
	)
/** @} */

/**
 * \name SAME70 series
 * @{
 */
#define SAME70J ( \
		SAM_PART_IS_DEFINED(SAME70J19) || \
		SAM_PART_IS_DEFINED(SAME70J20) || \
		SAM_PART_IS_DEFINED(SAME70J21) \
	)

#define SAME70N ( \
		SAM_PART_IS_DEFINED(SAME70N19) || \
		SAM_PART_IS_DEFINED(SAME70N20) || \
		SAM_PART_IS_DEFINED(SAME70N21) \
	)

#define SAME70Q ( \
		SAM_PART_IS_DEFINED(SAME70Q19) || \
		SAM_PART_IS_DEFINED(SAME70Q20) || \
		SAM_PART_IS_DEFINED(SAME70Q21) \
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
#define SAM3N (SAM3N00 || SAM3N0 || SAM3N1 || SAM3N2 || SAM3N4)

/** SAM3XA Family */
#define SAM3XA (SAM3X4 || SAM3X8 || SAM3A4 || SAM3A8)

/** SAM4S Family */
#define SAM4S (SAM4S2 || SAM4S4 || SAM4S8 || SAM4S16 || SAM4SA16 || SAM4SD16 || SAM4SD32)

/** SAM4L Family */
#define SAM4L (SAM4LS || SAM4LC)

/** SAMD20 Family */
#define SAMD20 (SAMD20J || SAMD20G || SAMD20E)

/** SAMD21 Family */
#define SAMD21 (SAMD21J || SAMD21G || SAMD21E)

/** SAMD09 Family */
#define SAMD09 (SAMD09C || SAMD09D)

/** SAMD10 Family */
#define SAMD10 (SAMD10C || SAMD10DS || SAMD10DM || SAMD10DU)

/** SAMD11 Family */
#define SAMD11 (SAMD11C || SAMD11DS || SAMD11DM || SAMD11DU)

/** SAMDA1 Family */
#define SAMDA1 (SAMDA1J || SAMDA1G || SAMDA1E)

/** SAMD Family */
#define SAMD   (SAMD20 || SAMD21 || SAMD09 || SAMD10 || SAMD11 || SAMDA1)

/** SAMR21 Family */
#define SAMR21 (SAMR21G || SAMR21E)

/** SAMB11 Family */
#define SAMB11 (SAMB11G)

/** SAML21 Family */
#define SAML21 (SAML21J || SAML21G || SAML21E)

/** SAML22 Family */
#define SAML22 (SAML22J || SAML22G || SAML22N)
/** SAMC20 Family */
#define SAMC20 (SAMC20J || SAMC20G || SAMC20E)

/** SAMC21 Family */
#define SAMC21 (SAMC21J || SAMC21G || SAMC21E)

/** SAM4E Family */
#define SAM4E (SAM4E8 || SAM4E16)

/** SAM4N Family */
#define SAM4N (SAM4N8 || SAM4N16)

/** SAM4C Family */
#define SAM4C_0 (SAM4C4_0 || SAM4C8_0 || SAM4C16_0 || SAM4C32_0)
#define SAM4C_1 (SAM4C4_1 || SAM4C8_1 || SAM4C16_1 || SAM4C32_1)
#define SAM4C   (SAM4C4 || SAM4C8 || SAM4C16 || SAM4C32)

/** SAM4CM Family */
#define SAM4CM_0 (SAM4CMP8_0 || SAM4CMP16_0 || SAM4CMP32_0 || \
			SAM4CMS4_0 || SAM4CMS8_0 || SAM4CMS16_0 || SAM4CMS32_0)
#define SAM4CM_1 (SAM4CMP8_1 || SAM4CMP16_1 || SAM4CMP32_1 || \
			SAM4CMS4_1 || SAM4CMS8_1 || SAM4CMS16_1 || SAM4CMS32_1)
#define SAM4CM   (SAM4CMP8 || SAM4CMP16 || SAM4CMP32 || \
			SAM4CMS4 || SAM4CMS8 || SAM4CMS16 || SAM4CMS32)

/** SAM4CP Family */
#define SAM4CP_0 (SAM4CP16_0)
#define SAM4CP_1 (SAM4CP16_1)
#define SAM4CP   (SAM4CP16)

/** SAMG Family */
#define SAMG (SAMG51 || SAMG53 || SAMG54 || SAMG55)

/** SAMB Family */
#define SAMB (SAMB11)

/** SAMV71 Family */
#define SAMV71 (SAMV71J || SAMV71N || SAMV71Q)

/** SAMV70 Family */
#define SAMV70 (SAMV70J || SAMV70N || SAMV70Q)

/** SAME70 Family */
#define SAME70 (SAME70J || SAME70N || SAME70Q)

/** SAMS70 Family */
#define SAMS70 (SAMS70J || SAMS70N || SAMS70Q)

/** SAM0 product line (cortex-m0+) */
#define SAM0 (SAMD20 || SAMD21 || SAMR21 || SAMD10 || SAMD11 || SAML21 ||\
		SAMDA1 || SAMC20 || SAMC21 || SAML22 || SAMD09)

/** @} */

/** SAM product line */
#define SAM (SAM3S || SAM3U || SAM3N || SAM3XA || SAM4S || SAM4L || SAM4E || \
		SAM0 || SAM4N || SAM4C || SAM4CM || SAM4CP || SAMG || SAMV71 || SAMV70 || SAME70 || SAMS70)

/** @} */

/** @} */

/** @} */

#endif /* ATMEL_PARTS_H */
