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
 *  \file
 *
 *  \section Purpose
 *
 *  This file provides a basic API for PIO configuration and usage of
 *  user-controlled pins. Please refer to the board.h file for a list of
 *  available pin definitions.
 *
 *  \section Usage
 *
 *  -# Define a constant pin description array such as the following one, using
 *     the existing definitions provided by the board.h file if possible:
 *     \code
 *        const struct _pin pins[] = {PIN_USART0_TXD, PIN_USART0_RXD};
 *     \endcode
 *     Alternatively, it is possible to add new pins by provided the full Pin
 *     structure:
 *     \code
 *     // Pin instance to configure PA10 & PA11 as inputs with the internal
 *     // pull-up enabled.
 *     const Pin pins = {
 *          (1 << 10) | (1 << 11),
 *          REG_PIOA,
 *          ID_PIOA,
 *          PIO_INPUT,
 *          PIO_PULLUP
 *     };
 *     \endcode
 *  -# Configure a pin array by calling pio_configure() with a pointer to the
 *     array and its size (which is computed using the ARRAY_SIZE macro).
 *  -# Change and get the value of a user-controlled pin using the pio_set,
 *     pio_clear and pio_get methods.
 *  -# Get the level being currently output by a user-controlled pin configured
 *     as an output using pio_get_output_date_status().
 */

#ifndef _PIO_H
#error "pio3.h cannot be included. pio.h should be used instead"
#endif

#ifndef _PIO4_H
#define _PIO4_H

/*------------------------------------------------------------------------------
 *         Headers
 *------------------------------------------------------------------------------*/

#include "chip.h"
#include <stdint.h>

/*------------------------------------------------------------------------------
 *         Definitions
 *------------------------------------------------------------------------------*/

/* The IO group is A (or 0) */
#define PIO_GROUP_A                 0
/* The IO group is B (or 1) */
#define PIO_GROUP_B                 1
/* The IO group is C (or 2) */
#define PIO_GROUP_C                 2
/* The IO group is D (or 3) */
#define PIO_GROUP_D                 3

#define PIO_GROUP_LENGTH            PIOIO_GROUP_NUMBER

/*  The pin is controlled by the generic PIO. */
#define PIO_GENERIC                 0
/*  The pin is controlled by the associated signal of peripheral A. */
#define PIO_PERIPH_A                1
/*  The pin is controlled by the associated signal of peripheral B. */
#define PIO_PERIPH_B                2
/*  The pin is controlled by the associated signal of peripheral C. */
#define PIO_PERIPH_C                3
/*  The pin is controlled by the associated signal of peripheral D. */
#define PIO_PERIPH_D                4
/*  The pin is controlled by the associated signal of peripheral E. */
#define PIO_PERIPH_E                5
/*  The pin is controlled by the associated signal of peripheral F. */
#define PIO_PERIPH_F                6
/*  The pin is controlled by the associated signal of peripheral G. */
#define PIO_PERIPH_G                7

/*  The pin is an input. */
#define PIO_INPUT		    10
/*  The pin is an output. */
#define PIO_OUTPUT		    11
/*  The pin is an output and has a default level of 0. */
#define PIO_OUTPUT_0                11
/*  The pin is an output and has a default level of 1. */
#define PIO_OUTPUT_1                12


/*  Default pin configuration (no attribute). */
#define PIO_DEFAULT                 (0x0u << 0)
/*  The internal pin pull-up is active. */
#define PIO_PULLUP                  (0x1u << 0)
/* The internal pin pull-down is active. */
#define PIO_PULLDOWN                (0x1u << 1)
/*  The pin is open-drain. */
#define PIO_OPENDRAIN               (0x1u << 2)
/*  The internal glitch filter is active. */
#define PIO_DEGLITCH                (0x1u << 3)
/* The internal Debounce filter is active. */
#define PIO_DEBOUNCE                (0x1u << 4)
/*  The internal Schmitt trigger is disable. */
#define PIO_TRIGGER_DIS             (0x1u << 5)

/*  Drive Strength. */
#define PIO_DRVSTR_Pos              10
#define PIO_DRVSTR_Msk              (0x3u << 10)
#define PIO_DRVSTR_HI               (0x2u << 10) /* High drive */
#define PIO_DRVSTR_ME               (0x1u << 10) /* Medium drive */
#define PIO_DRVSTR_LO               (0x0u << 10) /* Low drive */

#define PIO_EVTSEL_Pos              12
#define PIO_EVTSEL_Msk              (0x7u << 12)
/* Event detection on input falling edge. */
#define PIO_IT_FALL_EDGE            (0x0u << 12)
/* Event detection on input rising edge. */
#define PIO_IT_RISE_EDGE            (0x1u << 12)
/* Event detection on input both edge. */
#define PIO_IT_BOTH_EDGE            (0x2u << 12)
/* Event detection on low level input. */
#define PIO_IT_LOW_LEVEL            (0x3u << 12)
/*Event detection on high level input. */
#define PIO_IT_HIGH_LEVEL           (0x4u << 12)

#define PIO_WPMR_WPEN_EN            ( 0x01 << 0 )

#define PIO_WPMR_WPEN_DIS           ( 0x00 << 0 )

#define PIO_WPMR_WPKEY_VALID        ( 0x50494F << 8 )

#endif	/* #ifndef _PIO4_H */
