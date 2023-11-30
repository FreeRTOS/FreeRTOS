/**
 * \file
 *
 * \brief Chip-specific sleep manager configuration
 *
 * Copyright (c) 2012 - 2013 Atmel Corporation. All rights reserved.
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

#ifndef SAM_SLEEPMGR_INCLUDED
#define SAM_SLEEPMGR_INCLUDED

#ifdef __cplusplus
extern "C" {
#endif

#include <compiler.h>
#include <conf_sleepmgr.h>
#include <interrupt.h>
#include "bpm.h"
#include "sleep.h"

/**
 * \weakgroup sleepmgr_group
 * @{
 */

enum sleepmgr_mode {
	/** Active mode. */
	SLEEPMGR_ACTIVE = 0,

	/**
	 *  Sleep mode.
	 *  Potential Wake Up sources: fast startup events and interrupt.
	 */
	SLEEPMGR_SLEEP_0,
	SLEEPMGR_SLEEP_1,
	SLEEPMGR_SLEEP_2,
	SLEEPMGR_SLEEP_3,

	/**
	 *  Wait mode.
	 *  Potential Wake Up sources: fast startup events
	 */
	SLEEPMGR_WAIT,

	/**
	 *  Retention mode.
	 *  Potential Wake Up sources: fast startup events
	 */
	SLEEPMGR_RET,

	/** Backup mode. Potential Wake Up sources: WKUPs, SM, RTT, RTC. */
	SLEEPMGR_BACKUP,

	SLEEPMGR_NR_OF_MODES,
};

/**
 * \internal
 * \name Internal arrays
 * @{
 */
#if defined(CONFIG_SLEEPMGR_ENABLE) || defined(__DOXYGEN__)
/** Sleep mode lock counters */
extern uint8_t sleepmgr_locks[];
#endif /* CONFIG_SLEEPMGR_ENABLE */
/** @} */

static inline void sleepmgr_sleep(const enum sleepmgr_mode sleep_mode)
{
	Assert(sleep_mode != SLEEPMGR_ACTIVE);
#ifdef CONFIG_SLEEPMGR_ENABLE
	cpu_irq_disable();

	/* Enter the sleep mode. */
	bpm_sleep(BPM, sleep_mode);
#else
	UNUSED(sleep_mode);
	cpu_irq_enable();
#endif /* CONFIG_SLEEPMGR_ENABLE */
}

/** @} */

#ifdef __cplusplus
}
#endif

#endif /* SAM_SLEEPMGR_INCLUDED */
