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

/** \file */

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/
#include "chip.h"

/*----------------------------------------------------------------------------
 *        Local functions
 *----------------------------------------------------------------------------*/

/**
 * \brief Configures one or more pin(s) of a PIO controller as being controlled by
 * peripheral A. Optionally, the corresponding internal pull-up(s) can be enabled.
 *
 * \param pio  Pointer to a PIO controller.
 * \param mask  Bitmask of one or more pin(s) to configure.
 * \param enablePullUp  Indicates if the pin(s) internal pull-up shall be
 *                      configured.
 */
static void PIO_SetPeripheralA(
    Pio *pio,
    unsigned int mask,
    unsigned char enablePullUp)
{
    unsigned int abcdsr;
    /* Disable interrupts on the pin(s) */
    pio->PIO_IDR = mask;

    /* Enable the pull-up(s) if necessary */
    if (enablePullUp) {
        pio->PIO_PPDDR = mask;
        pio->PIO_PUER = mask;
    }
    else {
        //pio->PIO_PUDR = mask;
        pio->PIO_PPDDR = mask;
    }

    abcdsr = pio->PIO_ABCDSR[0];
    pio->PIO_ABCDSR[0] &= (~mask & abcdsr);
    abcdsr = pio->PIO_ABCDSR[1];
    pio->PIO_ABCDSR[1] &= (~mask & abcdsr);
    pio->PIO_PDR = mask;

}

/**
 * \brief Configures one or more pin(s) of a PIO controller as being controlled by
 * peripheral B. Optionally, the corresponding internal pull-up(s) can be enabled.
 *
 * \param pio  Pointer to a PIO controller.
 * \param mask  Bitmask of one or more pin(s) to configure.
 * \param enablePullUp  Indicates if the pin(s) internal pull-up shall be
 *                      configured.
 */
static void PIO_SetPeripheralB(
    Pio *pio,
    unsigned int mask,
    unsigned char enablePullUp)
{
    unsigned int abcdsr;
    /* Disable interrupts on the pin(s) */
    pio->PIO_IDR = mask;

    /* Enable the pull-up(s) if necessary */
    if (enablePullUp) {
        pio->PIO_PPDDR = mask;
        pio->PIO_PUER = mask;
    }
    else {
        pio->PIO_PUDR = mask;
        pio->PIO_PPDDR = mask;
    }

    abcdsr = pio->PIO_ABCDSR[0];
    pio->PIO_ABCDSR[0] = (mask | abcdsr);
    abcdsr = pio->PIO_ABCDSR[1];
    pio->PIO_ABCDSR[1] &= (~mask & abcdsr);

    pio->PIO_PDR = mask;
}

/**
 * \brief Configures one or more pin(s) of a PIO controller as being controlled by
 * peripheral C. Optionally, the corresponding internal pull-up(s) can be enabled.
 *
 * \param pio  Pointer to a PIO controller.
 * \param mask  Bitmask of one or more pin(s) to configure.
 * \param enablePullUp  Indicates if the pin(s) internal pull-up shall be
 *                      configured.
 */
static void PIO_SetPeripheralC(
    Pio *pio,
    unsigned int mask,
    unsigned char enablePullUp)
{
    unsigned int abcdsr;
    /* Disable interrupts on the pin(s) */
    pio->PIO_IDR = mask;

    /* Enable the pull-up(s) if necessary */
    if (enablePullUp) {
        pio->PIO_PPDDR = mask;
        pio->PIO_PUER = mask;
    }
    else {
        pio->PIO_PUDR = mask;
      //  pio->PIO_PPDDR = mask;
    }

    abcdsr = pio->PIO_ABCDSR[0];
    pio->PIO_ABCDSR[0] &= (~mask & abcdsr);
    abcdsr = pio->PIO_ABCDSR[1];
    pio->PIO_ABCDSR[1] = (mask | abcdsr);

    pio->PIO_PDR = mask;
}

/**
 * \brief Configures one or more pin(s) of a PIO controller as being controlled by
 * peripheral D. Optionally, the corresponding internal pull-up(s) can be enabled.
 *
 * \param pio  Pointer to a PIO controller.
 * \param mask  Bitmask of one or more pin(s) to configure.
 * \param enablePullUp  Indicates if the pin(s) internal pull-up shall be
 *                      configured.
 */
static void PIO_SetPeripheralD(
    Pio *pio,
    unsigned int mask,
    unsigned char enablePullUp)
{
    unsigned int abcdsr;
    /* Disable interrupts on the pin(s) */
    pio->PIO_IDR = mask;

    /* Enable the pull-up(s) if necessary */
    if (enablePullUp) {
        
        pio->PIO_PPDDR = mask;
        pio->PIO_PUER = mask;
    }
    else {
        pio->PIO_PUDR = mask;
    }

    abcdsr = pio->PIO_ABCDSR[0];
    pio->PIO_ABCDSR[0] = (mask | abcdsr);
    abcdsr = pio->PIO_ABCDSR[1];
    pio->PIO_ABCDSR[1] = (mask | abcdsr);

    pio->PIO_PDR = mask;
}

/**
 * \brief Configures one or more pin(s) or a PIO controller as inputs. Optionally,
 * the corresponding internal pull-up(s) and glitch filter(s) can be enabled.
 *
 * \param pio  Pointer to a PIO controller.
 * \param mask  Bitmask indicating which pin(s) to configure as input(s).
 * \param enablePullUp  Indicates if the internal pull-up(s) must be enabled.
 * \param enableFilter  Indicates if the glitch filter(s) must be enabled.
 */
static void PIO_SetInput(
    Pio *pio,
    unsigned int mask,
    unsigned char attribute)
{
    /* Disable interrupts */
    pio->PIO_IDR = mask;

    /* Enable pull-up(s) if necessary */
    if (attribute & PIO_PULLUP)
    {
        pio->PIO_PPDDR = mask;
        pio->PIO_PUER = mask;
    }
    else
    {
        pio->PIO_PUDR = mask;
    }
    /* Enable Input Filter if necessary */
    if (attribute & (PIO_DEGLITCH | PIO_DEBOUNCE))
        pio->PIO_IFER = mask;
    else
        pio->PIO_IFDR = mask;

    /* Enable de-glitch or de-bounce if necessary */
    if (attribute & PIO_DEGLITCH) {
        pio->PIO_IFSCDR = mask;
    } else if (attribute & PIO_DEBOUNCE) {
        pio->PIO_IFSCER = mask;
    }

    /* Configure pin as input */
    pio->PIO_ODR = mask;
    pio->PIO_PER = mask;
}

/**
 * \brief Configures one or more pin(s) of a PIO controller as outputs, with the
 * given default value. Optionally, the multi-drive feature can be enabled
 * on the pin(s).
 *
 * \param pio  Pointer to a PIO controller.
 * \param mask  Bitmask indicating which pin(s) to configure.
 * \param defaultValue  Default level on the pin(s).
 * \param enableMultiDrive  Indicates if the pin(s) shall be configured as
 *                          open-drain.
 * \param enablePullUp  Indicates if the pin shall have its pull-up activated.
 */
static void PIO_SetOutput(
    Pio *pio,
    unsigned int mask,
    unsigned char defaultValue,
    unsigned char enableMultiDrive,
    unsigned char enablePullUp)
{
    /* Disable interrupts */
    pio->PIO_IDR = mask;

    /* Enable pull-up(s) if necessary */
    if (enablePullUp) {
        pio->PIO_PPDDR = mask;
        pio->PIO_PUER = mask;
    }
    else {
        pio->PIO_PUDR = mask;
    }

    /* Enable multi-drive if necessary */
    if (enableMultiDrive) {

        pio->PIO_MDER = mask;
    }
    else {

        pio->PIO_MDDR = mask;
    }

    /* Set default value */
    if (defaultValue) {

        pio->PIO_SODR = mask;
    }
    else {

        pio->PIO_CODR = mask;
    }

    /* Configure pin(s) as output(s) */
    pio->PIO_OER = mask;
    pio->PIO_PER = mask;
}

/*----------------------------------------------------------------------------
 *         Global functions
 *----------------------------------------------------------------------------*/

/**
 * \brief Configures a list of Pin instances, each of which can either hold a single
 * pin or a group of pins, depending on the mask value; all pins are configured
 * by this function. The size of the array must also be provided and is easily
 * computed using PIO_LISTSIZE whenever its length is not known in advance.
 *
 * \param list  Pointer to a list of Pin instances.
 * \param size  Size of the Pin list (calculated using PIO_LISTSIZE).
 *
 * \return 1 if the pins have been configured properly; otherwise 0.
 */
uint8_t PIO_Configure( const Pin *list, uint32_t size )
{
    /* Configure pins */
    while ( size > 0 )
    {
        switch ( list->type )
        {

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

            case PIO_PERIPH_C:
                PIO_SetPeripheralC(list->pio,
                                   list->mask,
                                   (list->attribute & PIO_PULLUP) ? 1 : 0);
            break;

            case PIO_PERIPH_D:
                PIO_SetPeripheralD(list->pio,
                                   list->mask,
                                   (list->attribute & PIO_PULLUP) ? 1 : 0);
            break;
            case PIO_INPUT:
                PMC_EnablePeripheral(list->id);
                PIO_SetInput(list->pio,
                             list->mask,
                             list->attribute);
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

/**
 * \brief Sets a high output level on all the PIOs defined in the given Pin instance.
 * This has no immediate effects on PIOs that are not output, but the PIO
 * controller will memorize the value they are changed to outputs.
 *
 * \param pin  Pointer to a Pin instance describing one or more pins.
 */
void PIO_Set(const Pin *pin)
{
    pin->pio->PIO_SODR = pin->mask;
}

/**
 * \brief Sets a low output level on all the PIOs defined in the given Pin instance.
 * This has no immediate effects on PIOs that are not output, but the PIO
 * controller will memorize the value they are changed to outputs.
 *
 * \param pin  Pointer to a Pin instance describing one or more pins.
 */
void PIO_Clear(const Pin *pin)
{
    pin->pio->PIO_CODR = pin->mask;
}

/**
 * \brief Returns 1 if one or more PIO of the given Pin instance currently have
 * a high level; otherwise returns 0. This method returns the actual value that
 * is being read on the pin. To return the supposed output value of a pin, use
 * PIO_GetOutputDataStatus() instead.
 *
 * \param pin  Pointer to a Pin instance describing one or more pins.
 *
 * \return 1 if the Pin instance contains at least one PIO that currently has
 * a high level; otherwise 0.
 */
unsigned char PIO_Get( const Pin *pin )
{
    unsigned int reg ;

    if ( (pin->type == PIO_OUTPUT_0) || (pin->type == PIO_OUTPUT_1) )
    {
        reg = pin->pio->PIO_ODSR ;
    }
    else
    {
        reg = pin->pio->PIO_PDSR ;
    }

    if ( (reg & pin->mask) == 0 )
    {
        return 0 ;
    }
    else
    {
        return 1 ;
    }
}

/**
 * \brief Returns 1 if one or more PIO of the given Pin are configured to output a
 * high level (even if they are not output).
 * To get the actual value of the pin, use PIO_Get() instead.
 *
 * \param pin  Pointer to a Pin instance describing one or more pins.
 *
 * \return 1 if the Pin instance contains at least one PIO that is configured
 * to output a high level; otherwise 0.
 */
unsigned char PIO_GetOutputDataStatus(const Pin *pin)
{
    if ((pin->pio->PIO_ODSR & pin->mask) == 0)
    {
        return 0;
    }
    else
    {
        return 1;
    }
}

/*
 * \brief Configures Glitch or Debouncing filter for input.
 *
 * \param pin  Pointer to a Pin instance describing one or more pins.
 * \param cuttoff  Cutt off frequency for debounce filter.
 */
void PIO_SetDebounceFilter( const Pin *pin, uint32_t cuttoff )
{
    Pio *pio = pin->pio;

    if (cuttoff == 0)
    {
        pio->PIO_IFSCDR = pin->mask;
        pio->PIO_SCDR = 0;
    }
    else
    {
        /* set Debouncing, 0 bit field no effect */
        pio->PIO_IFSCER = pin->mask;
        /* the lowest 14 bits work */
        pio->PIO_SCDR = ((32678/(2*(cuttoff))) - 1) & 0x3FFF;
    }
}

/*
 * \brief Enable write protect.
 *
 * \param pin  Pointer to a Pin instance describing one or more pins.
 */


void PIO_EnableWriteProtect( const Pin *pin )
{
   Pio *pio = pin->pio;

   pio->PIO_WPMR = ( PIO_WPMR_WPKEY_VALID | PIO_WPMR_WPEN_EN );
}

/*
 * \brief Disable write protect.
 *
 * \param pin  Pointer to a Pin instance describing one or more pins.
 */

void PIO_DisableWriteProtect( const Pin *pin )
{
   Pio *pio = pin->pio;

   pio->PIO_WPMR = ( PIO_WPMR_WPKEY_VALID | PIO_WPMR_WPEN_DIS );
}

/*
 * \brief Get write protect violation information.
 *
 * \param pin  Pointer to a Pin instance describing one or more pins.
 */

uint32_t PIO_GetWriteProtectViolationInfo( const Pin * pin )
{
    Pio *pio = pin->pio;
    return (pio->PIO_WPSR);
}



/*
 * \brief Configure all pio output low
 *
 * \param pin  Pointer to a Pin instance describing one or more pins.
 * \param pioId PIO ID
 * \param mask  Bitmask of one or more pin(s) to configure.
 */

void PIO_Output_Low (Pio * pio, uint32_t pioId, uint32_t mask)
{
   PMC->PMC_PCER0 = 1 << pioId;
   pio->PIO_PUDR  = mask;   // all Pull-up Disable
   pio->PIO_PPDDR = mask;   // all Pull-down Disable
   pio->PIO_PER   = mask;   // all PIO enable
   pio->PIO_OER   = mask;   // all PIO output mode
   pio->PIO_CODR  = mask;   // all PIO clear output
}
