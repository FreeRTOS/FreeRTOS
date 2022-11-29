/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2015, Atmel Corporation
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
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

/**
 * \file
 *
 * \section Purpose
 * Interface for Watchdog Timer (WDT) controller.
 *
 * \section Usage
 * -# Enable watchdog with given mode using \ref wdt_enable().
 * -# Disable watchdog using \ref wdt_disable()
 * -# Restart the watchdog using \ref wdt_restart().
 * -# Get watchdog status using \ref  wdt_get_status().
 */

#ifndef _WDT_H_
#define _WDT_H_

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "chip.h"
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/


/**
 * \brief Enable watchdog with given mode.
 *
 * \note The Watchdog Mode Register (WDT_MR) can be written only once.
 * Only a processor reset resets it.
 *
 * \param mode WDT mode to be set
 * \param delta WDT delta value
 * \param counter WDT counter value
 */
extern void wdt_enable(uint32_t mode, uint32_t delta, uint32_t counter);

/**
 * \brief Disable watchdog.
 *
 * \note The Watchdog Mode Register (WDT_MR) can be written only once.
 * Only a processor reset resets it.
 */
extern void wdt_disable(void);

/**
 * \brief Watchdog restart.
 */
extern void wdt_restart(void);

/**
 * \brief Watchdog get status.
 */
extern uint32_t wdt_get_status(void);

/**
 * \brief Watchdog get counter value.
 */
extern uint32_t wdt_get_counter_value(void);

#ifdef __cplusplus
}
#endif

#endif /* _WDT_H_ */
