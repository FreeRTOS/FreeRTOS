/* ----------------------------------------------------------------------------
 *         ATMEL Microcontroller Software Support 
 * ----------------------------------------------------------------------------
 * Copyright (c) 2008, Atmel Corporation
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

//------------------------------------------------------------------------------
/// \dir
/// !Purpose
///
///     Definition of methods and structures for using PIOs in a transparent
///     way. The main purpose is to allow portability between several boards.
///
/// !Usage
///
///     -# To configure and use pins, see pio.h.
///     -# To enable and use interrupt generation on PIO status change, see
///      pio_it.h.
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
/// \unit
/// !Purpose
/// 
/// Simple & portable usage of PIO pins.
/// 
/// !Usage
/// 
/// -# Define a constant pin description array such as the following one:
///    \code
///       const Pin at91board_dbgu[] = {
///            {AT91C_BASE_PIOA, (1 << 30), PIO_PERIPH_A, PIO_DEFAULT},
///            {AT91C_BASE_PIOA, (1 << 31), PIO_PERIPH_A, PIO_DEFAULT},
///        };
///    \endcode
///    Alternatively, constants defined in the piodefs.h header file of the
///    board module can be used:
///    \code
///    const Pin at91board_dbgu[] = {PINS_DBGU};
///    const Pin at91board_usart[] = {PIN_USART0_RXD, PIN_USART0_TXD};
///    \endcode
///    It is possible to group multiple pins if they share the same
///    attributes, to save memory. Here is the previous DBGU example
///    rewritten in such a way:
///    \code
///    const Pin at91board_dbgu[] = {
///         {AT91C_BASE_PIOA, 0xC0000000, PIO_PERIPH_A, PIO_DEFAULT}
///    };
///    \endcode
/// -# For pins configured as inputs, the PIO controller must be enabled
///    in the PMC (*enabled by PIO_Configure at the moment*).
/// -# Configure a pin array by calling PIO_Configure, using
///    the PIO_LISTSIZE macro to calculate the array size if needed. Do not
///    forget to check the return value for any error.
/// -# Set and get the value of a pin using the PIO_Set, PIO_Clear and
///    PIO_Get methods.
//------------------------------------------------------------------------------
 
#ifndef PIO_H
#define PIO_H

//------------------------------------------------------------------------------
//         Headers
//------------------------------------------------------------------------------

#include <board.h>

//------------------------------------------------------------------------------
//         Definitions
//------------------------------------------------------------------------------
//------------------------------------------------------------------------------
/// \page "Pin types" 
/// This page lists the available types for a Pin instance (in its type field).
/// !Types
/// - PIO_PERIPH_A 
/// - PIO_PERIPH_B 
/// - PIO_INPUT 
/// - PIO_OUTPUT_0 
/// - PIO_OUTPUT_1 

/// The pin is controlled by the associated signal of peripheral A.
#define PIO_PERIPH_A                0
/// The pin is controlled by the associated signal of peripheral B.
#define PIO_PERIPH_B                1
/// The pin is an input.
#define PIO_INPUT                   2
/// The pin is an output and has a default level of 0.
#define PIO_OUTPUT_0                3
/// The pin is an output and has a default level of 1.
#define PIO_OUTPUT_1                4
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
/// \page "Pin attributes"
/// This page lists the valid values for the attribute field of a Pin instance.
/// !Attributes
/// - PIO_DEFAULT
/// - PIO_PULLUP
/// - PIO_DEGLITCH
/// - PIO_OPENDRAIN

/// Default pin configuration (no attribute).
#define PIO_DEFAULT                 (0 << 0)
/// The internal pin pull-up is active.
#define PIO_PULLUP                  (1 << 0)
/// The internal glitch filter is active.
#define PIO_DEGLITCH                (1 << 1)
/// The pin is open-drain.
#define PIO_OPENDRAIN               (1 << 2)
//------------------------------------------------------------------------------

/// Calculates the size of a Pin instances array. The array must be local (i.e.
/// not a pointer), otherwise the computation will not be correct.
#define PIO_LISTSIZE(list)    (sizeof(list) / sizeof(Pin))

//------------------------------------------------------------------------------
//         Types
//------------------------------------------------------------------------------
//------------------------------------------------------------------------------
/// Describes the type and attribute of one PIO pin or a group of similar pins.
typedef struct {
    /// Bitmask indicating which pin(s) to configure.
    unsigned int mask; 
    /// Pointer to the PIO controller which has the pin(s).
    AT91S_PIO    *pio;
    /// Peripheral ID of the PIO controller which has the pin(s).
    unsigned char id;
    /// Pin type (see "Pin types").
    unsigned char type;
    /// Pin attribute (see "Pin attributes").
    unsigned char attribute;
} Pin;
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
//         Exported functions
//------------------------------------------------------------------------------
extern unsigned char PIO_Configure(const Pin *list, unsigned int size);
extern void PIO_Set(const Pin *pin );
extern void PIO_Clear(const Pin *pin);
extern unsigned char PIO_Get(const Pin *pin);
extern unsigned int PIO_GetISR(const Pin *pin);
extern unsigned char PIO_GetOutputDataStatus(const Pin *pin);

#endif //#ifndef PIO_H

