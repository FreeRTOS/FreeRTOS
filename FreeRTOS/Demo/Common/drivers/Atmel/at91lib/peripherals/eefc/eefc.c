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

#ifndef trace_LEVEL
    #define trace_LEVEL trace_INFO
#endif

//------------------------------------------------------------------------------
//         Headers
//------------------------------------------------------------------------------

#include "eefc.h"

#ifdef BOARD_FLASH_EEFC

#include <utility/assert.h>
#include <utility/trace.h>

//------------------------------------------------------------------------------
//         Global functions
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
/// Enables the flash ready interrupt source on the EEFC peripheral.
//------------------------------------------------------------------------------
void EFC_EnableFrdyIt(void)
{
    AT91C_BASE_EFC->EFC_FMR |= AT91C_EFC_FRDY;
}

//------------------------------------------------------------------------------
/// Disables the flash ready interrupt source on the EEFC peripheral.
//------------------------------------------------------------------------------
void EFC_DisableFrdyIt(void)
{
    AT91C_BASE_EFC->EFC_FMR &= ~AT91C_EFC_FRDY;
}

//------------------------------------------------------------------------------
/// Translates the given address page and offset values. The resulting
/// values are stored in the provided variables if they are not null.
/// \param address  Address to translate.
/// \param pPage  First page accessed.
/// \param pOffset  Byte offset in first page.
//------------------------------------------------------------------------------
void EFC_TranslateAddress(
    unsigned int address,
    unsigned short *pPage,
    unsigned short *pOffset)
{
    unsigned short page;
    unsigned short offset;

    SANITY_CHECK(address >= AT91C_IFLASH);
    SANITY_CHECK(address <= (AT91C_IFLASH + AT91C_IFLASH_SIZE));

    // Calculate page & offset
    page = (address - AT91C_IFLASH) / AT91C_IFLASH_PAGE_SIZE;
    offset = (address - AT91C_IFLASH) % AT91C_IFLASH_PAGE_SIZE;
    trace_LOG(trace_DEBUG,
              "-D- Translated 0x%08X to page=%d and offset=%d\n\r",
              address, page, offset);

    // Store values
    if (pPage) {

        *pPage = page;
    }
    if (pOffset) {

        *pOffset = offset;
    }
}

//------------------------------------------------------------------------------
/// Computes the address of a flash access given the page and offset.
/// \param page  Page number.
/// \param offset  Byte offset inside page.
/// \param pAddress  Computed address (optional).
//------------------------------------------------------------------------------
void EFC_ComputeAddress(
    unsigned short page,
    unsigned short offset,
    unsigned int *pAddress)
{
    unsigned int address;

    SANITY_CHECK(page <= AT91C_IFLASH_NB_OF_PAGES);
    SANITY_CHECK(offset < AT91C_IFLASH_PAGE_SIZE);

    // Compute address
    address = AT91C_IFLASH + page * AT91C_IFLASH_PAGE_SIZE + offset;

    // Store result
    if (pAddress) {

        *pAddress = address;
    }
}

//------------------------------------------------------------------------------
/// Starts the executing the given command on the EEFC. This function returns
/// as soon as the command is started. It does NOT set the FMCN field automatically.
/// \param command  Command to execute.
/// \param argument  Command argument (should be 0 if not used).
//------------------------------------------------------------------------------
void EFC_StartCommand(unsigned char command, unsigned short argument)
{
    // Check command & argument
    switch (command) {

        case AT91C_EFC_FCMD_WP:
        case AT91C_EFC_FCMD_WPL:
        case AT91C_EFC_FCMD_EWP: 
        case AT91C_EFC_FCMD_EWPL:
        case AT91C_EFC_FCMD_EPL:
        case AT91C_EFC_FCMD_EPA:
        case AT91C_EFC_FCMD_SLB:
        case AT91C_EFC_FCMD_CLB:
            ASSERT(argument < AT91C_IFLASH_NB_OF_PAGES,
                   "-F- Embedded flash has only %d pages\n\r",
                   AT91C_IFLASH_NB_OF_PAGES);
            break;

        case AT91C_EFC_FCMD_SFB:
        case AT91C_EFC_FCMD_CFB:
            ASSERT(argument < EFC_NUM_GPNVMS, "-F- Embedded flash has only %d GPNVMs\n\r", EFC_NUM_GPNVMS);
            break;

        case AT91C_EFC_FCMD_GETD:
        case AT91C_EFC_FCMD_EA:
        case AT91C_EFC_FCMD_GLB:
        case AT91C_EFC_FCMD_GFB:
            ASSERT(argument == 0, "-F- Argument is meaningless for the given command.\n\r");
            break;

        default: ASSERT(0, "-F- Unknown command %d\n\r", command);
    }

    // Start commandEmbedded flash 
    ASSERT((AT91C_BASE_EFC->EFC_FSR & AT91C_EFC_FRDY) == AT91C_EFC_FRDY, "-F- EEFC is not ready\n\r");
    AT91C_BASE_EFC->EFC_FCR = (0x5A << 24) | (argument << 8) | command;
}

//------------------------------------------------------------------------------
/// Performs the given command and wait until its completion (or an error).
/// Returns 0 if successful; otherwise returns an error code.
/// \param command  Command to perform.
/// \param argument  Optional command argument.
//------------------------------------------------------------------------------
#ifdef __ICCARM__
__ramfunc
#else
__attribute__ ((section (".ramfunc")))
#endif
unsigned char EFC_PerformCommand(unsigned char command, unsigned short argument)
{
    unsigned int status;

#ifdef BOARD_FLASH_IAP_ADDRESS
    // Pointer on IAP function in ROM
    static void (*IAP_PerformCommand)(unsigned int);
    IAP_PerformCommand = (void (*)(unsigned int)) *((unsigned int *) BOARD_FLASH_IAP_ADDRESS);

    // Check if IAP function is implemented (opcode in SWI != 'b' or 'ldr') */
    if ((((((unsigned long) IAP_PerformCommand >> 24) & 0xFF) != 0xEA) &&
        (((unsigned long) IAP_PerformCommand >> 24) & 0xFF) != 0xE5)) {

        IAP_PerformCommand((0x5A << 24) | (argument << 8) | command);
        return (AT91C_BASE_EFC->EFC_FSR & (AT91C_EFC_LOCKE | AT91C_EFC_FCMDE));
    }
#endif

    AT91C_BASE_EFC->EFC_FCR = (0x5A << 24) | (argument << 8) | command;
    do {

        status = AT91C_BASE_EFC->EFC_FSR;
    }
    while ((status & AT91C_EFC_FRDY) != AT91C_EFC_FRDY);

    return (status & (AT91C_EFC_LOCKE | AT91C_EFC_FCMDE));
}

//------------------------------------------------------------------------------
/// Returns the current status of the EEFC. Keep in mind that this function clears
/// the value of some status bits (LOCKE, PROGE).
//------------------------------------------------------------------------------
unsigned int EFC_GetStatus(void)
{
    return AT91C_BASE_EFC->EFC_FSR;
}

//------------------------------------------------------------------------------
/// Returns the result of the last executed command.
//------------------------------------------------------------------------------
unsigned int EFC_GetResult(void) {

    return AT91C_BASE_EFC->EFC_FRR;
}

#endif //#ifdef BOARD_FLASH_EEFC

