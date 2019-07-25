/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2013, Atmel Corporation
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

/** \addtogroup rtng_module Working with RTNG
 * \ingroup peripherals_module
 * The TRNG driver provides the interface to configure and use the TRNG peripheral.
 * \n
 *
 * The True Random Number Generator (TRNG) passes the American NIST Special Publication
 * 800-22 and Diehard Random Tests Suites. As soon as the TRNG is enabled (TRNG_Enable()), 
 * the generator provides one 32-bit value every 84 clock cycles. 
 * Interrupt trng_int can be enabled through TRNG_EnableIt()(respectively disabled in TRNG_IDR).
 * This interrupt is set when a new random value is available and is cleared when the status 
 * register is read (TRNG_SR register). The flag DATRDY of the status register (TRNG_ISR) is set
 * when the random data is ready to be read out on the 32-bit output data through TRNG_GetRandData().
 *
 * For more accurate information, please look at the SHA section of the
 * Datasheet.
 *
 * Related files :\n
 * \ref trng.c\n
 * \ref trng.h\n
 */
/*@{*/
/*@}*/

/**
 * \file
 *
 * Implementation of True Random Number Generator (TRNG)
 *
 */

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "chip.h"

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

/**
 * \brief Enables the TRNG to provide Random Values.
 * \param key  This key is to be written when the ENABLE bit is set.
 */
void TRNG_Enable(void)
{
    TRNG->TRNG_CR = TRNG_CR_ENABLE | TRNG_CR_KEY_PASSWD;
}

/**
 * \brief Disables the TRNG to provide Random Values.
 * \param key  This key is to be written when the DISABLE bit is set.
 */
void TRNG_Disable(void)
{
    TRNG->TRNG_CR = TRNG_CR_KEY_PASSWD;
}

/**
 * \brief Data Ready Interrupt enable.
 */
void TRNG_EnableIt(void)
{
    TRNG->TRNG_IER = TRNG_IER_DATRDY;
}

/**
 * \brief Data Ready Interrupt Disable.
 */
void TRNG_DisableIt(void)
{
    TRNG->TRNG_IDR = TRNG_IDR_DATRDY;
}

/**
 * \brief Get the current status register of the given TRNG peripheral.
 * \return  TRNG status register.
 */
uint32_t TRNG_GetStatus(void)
{
    return TRNG->TRNG_ISR;
}

/**
 * \brief Get the  32-bit Output Data from TRNG peripheral.
 * \return  TRNG output data.
 */
uint32_t TRNG_GetRandData(void)
{
    return TRNG->TRNG_ODATA;
}
