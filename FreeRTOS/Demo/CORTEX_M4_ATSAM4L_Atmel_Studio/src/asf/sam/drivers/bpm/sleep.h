/**
 * \file
 *
 * \brief Sleep mode access
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

#ifndef SLEEP_H
#define SLEEP_H

#ifdef __cplusplus
extern "C" {
#endif

#include <compiler.h>

/**
 * \defgroup sleep_group Backup Power Manager (BPM)
 *
 * This is a stub on the SAM4L Backup Power Manager(BPM) for the sleepmgr service.
 *
 * \note To minimize the code overhead, these functions do not feature
 * interrupt-protected access since they are likely to be called inside
 * interrupt handlers or in applications where such protection is not
 * necessary. If such protection is needed, it must be ensured by the calling
 * code.
 *
 * @{
 */

#if defined(__DOXYGEN__)
/**
 * \brief Sets the MCU in the specified sleep mode
 * \param sleep_mode Sleep mode to set.
 */
#endif

#include "bpm.h"

static inline void bpm_sleep(Bpm *bpm, uint32_t sleep_mode)
{
	uint32_t pmcon;

	/* Read PMCON register */
	pmcon = bpm->BPM_PMCON;
	pmcon &= ~BPM_PMCON_BKUP;
	pmcon &= ~BPM_PMCON_RET;
	pmcon &= ~BPM_PMCON_SLEEP_Msk;

	/* Unlock PMCON register */
	BPM_UNLOCK(PMCON);

	if (sleep_mode == BPM_SM_SLEEP_0) {
		pmcon |= BPM_PMCON_SLEEP(0);
		bpm->BPM_PMCON = pmcon;
		SCB->SCR &= ~SCB_SCR_SLEEPDEEP_Msk;
	} else if (sleep_mode == BPM_SM_SLEEP_1) {
		pmcon |= BPM_PMCON_SLEEP(1);
		bpm->BPM_PMCON = pmcon;
		SCB->SCR &= ~SCB_SCR_SLEEPDEEP_Msk;
	} else if (sleep_mode == BPM_SM_SLEEP_2) {
		pmcon |= BPM_PMCON_SLEEP(2);
		bpm->BPM_PMCON = pmcon;
		SCB->SCR &= ~SCB_SCR_SLEEPDEEP_Msk;
	} else if (sleep_mode == BPM_SM_SLEEP_3) {
		pmcon |= BPM_PMCON_SLEEP(3);
		bpm->BPM_PMCON = pmcon;
		SCB->SCR &= ~SCB_SCR_SLEEPDEEP_Msk;
	} else if (sleep_mode == BPM_SM_WAIT) {
		bpm->BPM_PMCON = pmcon;
		SCB->SCR |= SCB_SCR_SLEEPDEEP_Msk;
	} else if (sleep_mode == BPM_SM_RET) {
		pmcon |= BPM_PMCON_RET;
		bpm->BPM_PMCON = pmcon;
		SCB->SCR |= SCB_SCR_SLEEPDEEP_Msk;
	} else { /* if (sleep_mode == BPM_SM_BACKUP) */
		pmcon |= BPM_PMCON_BKUP;
		bpm->BPM_PMCON = pmcon;
		SCB->SCR |= SCB_SCR_SLEEPDEEP_Msk;
	}

	/* Wait until vreg is ok. */
	while(!(BSCIF->BSCIF_PCLKSR & BSCIF_PCLKSR_VREGOK));
	asm volatile ("wfi");
	/* ensure sleep request propagation to flash. */
	asm volatile ("nop");

	/* The interrupts wake-up from the previous wfi, but there are still
	 * masked since we are in the critical section thanks to the previous
	 * set_pri_mask(1). Thus, we need to leave the critical section.
	 * Please note that we should probably use something like
	 * cpu_leave_critical(), using set_pri_mask(0)
	 */
	/* In this demo interrupts are managed by the FreeRTOS kernel and must not
	be altered here so the following line has been removed _RB_
	cpu_irq_enable(); */
}


//! @}

#ifdef __cplusplus
}
#endif

#endif /* SLEEP_H */

