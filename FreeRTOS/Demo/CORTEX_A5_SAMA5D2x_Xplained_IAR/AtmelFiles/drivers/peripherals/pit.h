/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2011, Atmel Corporation
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

#ifndef _PIT_H_
#define _PIT_H_

/*------------------------------------------------------------------------------
 *         Headers
 *------------------------------------------------------------------------------*/

#include <stdint.h>

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

#ifdef __cplusplus
extern "C" {
#endif

/**
* \brief Initialize the Periodic Interval Timer to generate a tick at the
* specified period, given the current master clock frequency.
*
*  \param period Period in micro seconds.
*/
extern void pit_init(uint32_t period);

/**
 * \brief Set the Periodic Interval Value of the PIT.
 *
 *  \param piv  PIV value to set.
 */
extern void pit_set_piv(uint32_t piv);

/**
 * \brief Enables the PIT if this is not already the case.
 *
 */
extern void pit_enable(void);

/**
 * \brief Disnables the PIT when PIV value is reached.
 *
 */
extern void pit_disable(void);

/**
 * \brief Enable the PIT periodic interrupt.
 *
 */
extern void pit_enable_it(void);

/**
 * \brief Disables the PIT periodic interrupt.
 *
 */
extern void pit_disable_it(void);

/**
 * \brief Returns the value of the PIT mode register.
 *
 * \return PIT_MR value.
 */
extern uint32_t pit_get_mode(void);

/**
 * \brief Returns the value of the PIT status register, clearing it as
 * a side effect.
 *
 * \return PIT_SR value.
 */
extern uint32_t pit_get_status(void);

/**
 * \brief Returns the value of the PIT Image Register, to read PICNT
 *  and CPIV without clearing the current values.
 *
 * \return PIT_PIIR value.
 */
extern uint32_t pit_get_piir(void);

/**
 * \brief Returns the value of the PIT Value Register, clearing it as
 * a side effect.
 *
 * \return PITC_PIVR value.
 */
extern uint32_t pit_get_pivr(void);

#ifdef __cplusplus
}
#endif

#endif	/* #ifndef _PIT_H_ */
