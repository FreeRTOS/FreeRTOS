/**
 * \file
 *
 * \brief Sleep mode access
 *
 * Copyright (c) 2012-2015 Atmel Corporation. All rights reserved.
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

#ifndef SLEEP_H
#define SLEEP_H

#ifdef __cplusplus
extern "C" {
#endif

#include <compiler.h>

/**
 * \defgroup sleep_group Power Manager (PM)
 *
 * This is a stub on the SAM Power Manager Control (PMC) for the sleepmgr
 * service.
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
/* SAM3,SAM4,SAMG,SAMV,SAME and SAMS series */
#if (SAM3S || SAM3N || SAM3XA || SAM3U || SAM4S || SAM4E || SAM4N || SAM4C || \
		SAM4CM || SAM4CP || SAMG || SAMV71 || SAME70 || SAMS70)

#if (SAM3S || SAM3N || SAM3XA || SAM3U || SAM4S || SAM4E || SAM4N || SAM4C || \
		SAM4CM || SAM4CP || SAMG55 || SAMV71 || SAME70 || SAMS70)
# define  SAM_PM_SMODE_ACTIVE     0 /**< Active */
# define  SAM_PM_SMODE_SLEEP_WFE  1 /**< Wait for Events */
# define  SAM_PM_SMODE_SLEEP_WFI  2 /**< Wait for Interrupts */
# define  SAM_PM_SMODE_WAIT_FAST  3 /**< Wait Mode, startup fast (in 3ms) */
# define  SAM_PM_SMODE_WAIT       4 /**< Wait Mode */
# define  SAM_PM_SMODE_BACKUP     5 /**< Backup Mode */
#else
# define  SAM_PM_SMODE_ACTIVE     0 /**< Active */
# define  SAM_PM_SMODE_WAIT_FAST  1 /**< Wait Mode, startup fast (in 3ms) */
# define  SAM_PM_SMODE_WAIT       2 /**< Wait Mode */
#endif

/** (SCR) Sleep deep bit */
#define SCR_SLEEPDEEP   (0x1 <<  2)

/**
 * Clocks restored callback function type.
 * Registered by routine pmc_wait_wakeup_clocks_restore()
 * Callback called when all clocks are restored.
 */
typedef void (*pmc_callback_wakeup_clocks_restored_t) (void);

/**
 * Enter sleep mode
 * \param sleep_mode Sleep mode to enter
 */
void pmc_sleep(int sleep_mode);

/**
 * Check if clocks are restored after wakeup
 * (For WAIT mode. In WAIT mode, clocks are switched to FASTRC.
 *  After wakeup clocks should be restored, before that some of the
 *  ISR should not be served, otherwise there may be timing or clock issue.)
 */
bool pmc_is_wakeup_clocks_restored(void);

/**
 * \return true if start waiting
 */
void pmc_wait_wakeup_clocks_restore(
		pmc_callback_wakeup_clocks_restored_t callback);

#endif

//! @}

#ifdef __cplusplus
}
#endif

#endif /* SLEEP_H */
