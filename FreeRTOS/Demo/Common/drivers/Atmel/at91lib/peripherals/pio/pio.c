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
//         Headers
//------------------------------------------------------------------------------

#include "pio.h"
#include <board.h>

//------------------------------------------------------------------------------
//         Internal definitions
//------------------------------------------------------------------------------
/// \internal Returns the current value of a register.
#define READ(peripheral, register)          (peripheral->register)
/// \internal Modifies the current value of a register.
#define WRITE(peripheral, register, value)  (peripheral->register = value)

//------------------------------------------------------------------------------
//         Internal functions
//------------------------------------------------------------------------------
//------------------------------------------------------------------------------
/// Configures one or more pin(s) of a PIO controller as being controlled by
/// peripheral A. Optionally, the corresponding internal pull-up(s) can be
/// enabled.
/// \param pio  Pointer to a PIO controller.
/// \param mask  Bitmask of one or more pin(s) to configure.
/// \param enablePullUp  Indicates if the pin(s) internal pull-up shall be
///                      configured.
//------------------------------------------------------------------------------
static void PIO_SetPeripheralA(AT91S_PIO *pio,
                               unsigned int mask,
                               unsigned char enablePullUp)
{
    // Disable interrupts on the pin(s)
    WRITE(pio, PIO_IDR, mask);

    // Enable the pull-up(s) if necessary
    if (enablePullUp) {

        WRITE(pio, PIO_PPUER, mask);
    }
    else {

        WRITE(pio, PIO_PPUDR, mask);
    }

    // Configure pin
    WRITE(pio, PIO_ASR, mask);
    WRITE(pio, PIO_PDR, mask);
}

//------------------------------------------------------------------------------
/// Configures one or more pin(s) of a PIO controller as being controlled by
/// peripheral A. Optionally, the corresponding internal pull-up(s) can be
/// enabled.
/// \param pio  Pointer to a PIO controller.
/// \param mask  Bitmask of one or more pin(s) to configure.
/// \param enablePullUp  Indicates if the pin(s) internal pull-up shall be
///                      configured.
//------------------------------------------------------------------------------
static void PIO_SetPeripheralB(AT91S_PIO *pio,
                               unsigned int mask,
                               unsigned char enablePullUp)
{
    // Disable interrupts on the pin(s)
    WRITE(pio, PIO_IDR, mask);

    // Enable the pull-up(s) if necessary
    if (enablePullUp) {

        WRITE(pio, PIO_PPUER, mask);
    }
    else {

        WRITE(pio, PIO_PPUDR, mask);
    }

    // Configure pin
    WRITE(pio, PIO_BSR, mask);
    WRITE(pio, PIO_PDR, mask);
}

//------------------------------------------------------------------------------
/// Configures one or more pin(s) or a PIO controller as inputs. Optionally,
/// the corresponding internal pull-up(s) and glitch filter(s) can be
/// enabled.
/// \param pio  Pointer to a PIO controller.
/// \param mask  Bitmask indicating which pin(s) to configure as input(s).
/// \param enablePullUp  Indicates if the internal pull-up(s) must be enabled.
/// \param enableFilter  Indicates if the glitch filter(s) must be enabled.
//------------------------------------------------------------------------------
static void PIO_SetInput(AT91S_PIO *pio,
                         unsigned int mask,
                         unsigned char enablePullUp,
                         unsigned char enableFilter)
{
    // Disable interrupts
    WRITE(pio, PIO_IDR, mask);

    // Enable pull-up(s) if necessary
    if (enablePullUp) {
    
        WRITE(pio, PIO_PPUER, mask);
    }
    else {
    
        WRITE(pio, PIO_PPUDR, mask);
    }

    // Enable filter(s) if necessary
    if (enableFilter) {
    
        WRITE(pio, PIO_IFER, mask);
    }
    else {
    
        WRITE(pio, PIO_IFDR, mask);
    }

    // Configure pin as input
    WRITE(pio, PIO_ODR, mask);
    WRITE(pio, PIO_PER, mask);
}

//------------------------------------------------------------------------------
/// Configures one or more pin(s) of a PIO controller as outputs, with the
/// given default value. Optionally, the multi-drive feature can be enabled
/// on the pin(s).
/// \param pio  Pointer to a PIO controller.
/// \param mask  Bitmask indicating which pin(s) to configure.
/// \param defaultValue  Default level on the pin(s).
/// \param enableMultiDrive  Indicates if the pin(s) shall be configured as
///                          open-drain.
/// \param enablePullUp  Indicates if the pin shall have its pull-up activated.
//------------------------------------------------------------------------------
static void PIO_SetOutput(AT91S_PIO *pio,
                          unsigned int mask,
                          unsigned char defaultValue,
                          unsigned char enableMultiDrive,
                          unsigned char enablePullUp)
{
    // Disable interrupts
    WRITE(pio, PIO_IDR, mask);

    // Enable pull-up(s) if necessary
    if (enablePullUp) {
    
        WRITE(pio, PIO_PPUER, mask);
    }
    else {
    
        WRITE(pio, PIO_PPUDR, mask);
    }

    // Enable multi-drive if necessary
    if (enableMultiDrive) {
    
        WRITE(pio, PIO_MDER, mask);
    }
    else {
    
        WRITE(pio, PIO_MDDR, mask);
    }

    // Set default value
    if (defaultValue) {

        WRITE(pio, PIO_SODR, mask);
    }
    else {

        WRITE(pio, PIO_CODR, mask);
    }

    // Configure pin(s) as output(s)
    WRITE(pio, PIO_OER, mask);
    WRITE(pio, PIO_PER, mask);
}

//------------------------------------------------------------------------------
//         Exported functions
//------------------------------------------------------------------------------
//------------------------------------------------------------------------------
/// Configures a list of Pin instances, which can either hold a single pin or a 
/// group of pins, depending on the mask value; all pins are configured by this 
/// function.
/// Returns 1 if the configuration has been performed successfully; otherwise 0.
/// \param list  Pointer to a list of Pin instances.
/// \param size  Size of the Pin list (see <PIO_LISTSIZE>).
//------------------------------------------------------------------------------
unsigned char PIO_Configure(const Pin *list, unsigned int size)
{
    // Configure pins
    while (size > 0) {
    
        switch (list->type) {
    
            case PIO_PERIPH_A:
                PIO_SetPeripheralA(list->pio,
                                   list->mask,
                                   (list->attribute & PIO_PULLUP) ? 1 : 0);
                break;
    
            case PIO_PERIPH_B:
                PIO_SetPeripheralB(list->pio,
                                   list->mask,
                                   (list->attribute & PIO_PULLUP) ? 1 : 0);
                break;
    
            case PIO_INPUT:
                AT91C_BASE_PMC->PMC_PCER = 1 << list->id;
                PIO_SetInput(list->pio,
                             list->mask,
                             (list->attribute & PIO_PULLUP) ? 1 : 0,
                             (list->attribute & PIO_DEGLITCH)? 1 : 0);
                break;
    
            case PIO_OUTPUT_0:
            case PIO_OUTPUT_1:
                PIO_SetOutput(list->pio,
                              list->mask,
                              (list->type == PIO_OUTPUT_1),
                              (list->attribute & PIO_OPENDRAIN) ? 1 : 0,
                              (list->attribute & PIO_PULLUP) ? 1 : 0);
                break;
    
            default: return 0;
        }

        list++;
        size--;
    }

    return 1;
}

//------------------------------------------------------------------------------
/// Sets a high output level on one or more pin(s) (if configured as output(s)).
/// \param pin  Pointer to a Pin instance describing one or more pins.
//------------------------------------------------------------------------------
void PIO_Set(const Pin *pin)
{
    WRITE(pin->pio, PIO_SODR, pin->mask);
}

//------------------------------------------------------------------------------
/// Sets a low output level on one or more pin(s) (if configured as output(s)).
/// \param pin  Pointer to a Pin instance describing one or more pins.
//------------------------------------------------------------------------------
void PIO_Clear(const Pin *pin)
{
    WRITE(pin->pio, PIO_CODR, pin->mask);
}

//------------------------------------------------------------------------------
/// Returns 1 if one or more PIO of the given Pin instance currently have a high
/// level; otherwise returns 0.
/// \param pin  Pointer to a Pin instance describing one or more pins.
//------------------------------------------------------------------------------
unsigned char PIO_Get(const Pin *pin)
{
    unsigned int reg;
    if ((pin->type == PIO_OUTPUT_0) || (pin->type == PIO_OUTPUT_1)) {

        reg = READ(pin->pio, PIO_ODSR);
    }
    else {

        reg = READ(pin->pio, PIO_PDSR);
    }

    if ((reg & pin->mask) == 0) {

        return 0;
    }
    else {

        return 1;
    }
}


//------------------------------------------------------------------------------
/// Returns 1 if one or more PIO of the given Pin data to be driven on the I/O line
/// level; otherwise returns 0.
/// \param pin  Pointer to a Pin instance describing one or more pins.
//------------------------------------------------------------------------------
unsigned char PIO_GetOutputDataStatus(const Pin *pin)
{
    if ((READ(pin->pio, PIO_ODSR) & pin->mask) == 0) {

        return 0;
    }
    else {

        return 1;
    }
}

//------------------------------------------------------------------------------
/// Returns the value of ISR for the PIO controller of the pin.
/// Reading this register acknoledges all the ITs.
/// \param pin  Pointer to a Pin instance describing one or more pins.
//------------------------------------------------------------------------------
unsigned int PIO_GetISR(const Pin *pin)
{
    return (READ(pin->pio, PIO_ISR));
}

