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

#include "efc.h"

#ifdef BOARD_FLASH_EFC

#include <utility/assert.h>
#include <utility/trace.h>

//------------------------------------------------------------------------------
//         Local definitions
//------------------------------------------------------------------------------

// Round a number to the nearest integral value (number must have been
// multiplied by 10, e.g. to round 10.3 enter 103).
#define ROUND(n)    ((((n) % 10) >= 5) ? (((n) / 10) + 1) : ((n) / 10))

// Returns the FMCN field value when manipulating lock bits, given MCK.
#if defined(at91sam7a3)
    #define FMCN_BITS(mck)      (ROUND((mck) / 1000000) << 16)
#else
    #define FMCN_BITS(mck)      (ROUND((mck) / 100000) << 16)
#endif

// Returns the FMCN field value when manipulating the rest of the flash.
#define FMCN_FLASH(mck)         ((((mck) / 2000000) * 3) << 16)

//------------------------------------------------------------------------------
//         Local functions
//------------------------------------------------------------------------------

/// Master clock frequency, used to infer the value of the FMCN field.
#ifdef MCK_VARIABLE
static unsigned int lMck = 0;
#else
static const unsigned int lMck = BOARD_MCK;
#endif

//------------------------------------------------------------------------------
//         Global functions
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
/// Sets the system master clock so the FMCN field of the EFC(s) can be
/// programmed properly.
/// \param mck  Master clock frequency in Hz.
//------------------------------------------------------------------------------
void EFC_SetMasterClock(unsigned int mck)
{
#ifdef MCK_VARIABLE
    lMck = mck;
#else
    ASSERT(mck == BOARD_MCK, "-F- EFC has not been configured to work at a freq. different from %dMHz", BOARD_MCK);
#endif
}

//------------------------------------------------------------------------------
/// Enables the given interrupt sources on an EFC peripheral.
/// \param pEfc  Pointer to an AT91S_EFC structure.
/// \param sources  Interrupt sources to enable.
//------------------------------------------------------------------------------
void EFC_EnableIt(AT91S_EFC *pEfc, unsigned int sources)
{
    SANITY_CHECK(pEfc);
    SANITY_CHECK((sources & ~0x0000000D) == 0);

    pEfc->EFC_FMR |= sources;
}

//------------------------------------------------------------------------------
/// Disables the given interrupt sources on an EFC peripheral.
/// \param pEfc  Pointer to an AT91S_EFC structure.
/// \param sources  Interrupt sources to disable.
//------------------------------------------------------------------------------
void EFC_DisableIt(AT91S_EFC *pEfc, unsigned int sources)
{
    SANITY_CHECK(pEfc);
    SANITY_CHECK((sources & ~(AT91C_MC_FRDY | AT91C_MC_LOCKE | AT91C_MC_PROGE)) == 0);

    pEfc->EFC_FMR &= ~sources;
}

//------------------------------------------------------------------------------
/// Enables or disable the "Erase before programming" feature of an EFC.
/// \param pEfc  Pointer to an AT91S_EFC structure.
/// \param enable  If 1, the feature is enabled; otherwise it is disabled.
//------------------------------------------------------------------------------
void EFC_SetEraseBeforeProgramming(AT91S_EFC *pEfc, unsigned char enable)
{
    SANITY_CHECK(pEfc);

    if (enable) {

        pEfc->EFC_FMR &= ~AT91C_MC_NEBP;
    }
    else {

        pEfc->EFC_FMR |= AT91C_MC_NEBP;
    }
}

//------------------------------------------------------------------------------
/// Translates the given address into EFC, page and offset values. The resulting
/// values are stored in the provided variables if they are not null.
/// \param address  Address to translate.
/// \param ppEfc  Pointer to target EFC peripheral.
/// \param pPage  First page accessed.
/// \param pOffset  Byte offset in first page.
//------------------------------------------------------------------------------
void EFC_TranslateAddress(
    unsigned int address,
    AT91S_EFC **ppEfc,
    unsigned short *pPage,
    unsigned short *pOffset)
{
    AT91S_EFC *pEfc;
    unsigned short page;
    unsigned short offset;

    SANITY_CHECK(address >= AT91C_IFLASH);
    SANITY_CHECK(address <= (AT91C_IFLASH + AT91C_IFLASH_SIZE));

#if defined(AT91C_BASE_EFC0)
    if (address >= (AT91C_IFLASH + AT91C_IFLASH_SIZE / 2)) {

        pEfc = AT91C_BASE_EFC1;
        page = (address - AT91C_IFLASH - AT91C_IFLASH_SIZE / 2) / AT91C_IFLASH_PAGE_SIZE;
        offset = (address - AT91C_IFLASH - AT91C_IFLASH_SIZE / 2) % AT91C_IFLASH_PAGE_SIZE;
    }
    else {

        pEfc = AT91C_BASE_EFC0;
        page = (address - AT91C_IFLASH) / AT91C_IFLASH_PAGE_SIZE;
        offset = (address - AT91C_IFLASH) % AT91C_IFLASH_PAGE_SIZE;
    }
#else
    pEfc = AT91C_BASE_EFC;
    page = (address - AT91C_IFLASH) / AT91C_IFLASH_PAGE_SIZE;
    offset = (address - AT91C_IFLASH) % AT91C_IFLASH_PAGE_SIZE;
#endif
    TRACE_DEBUG("Translated 0x%08X to EFC=0x%08X, page=%d and offset=%d\n\r",
              address, (unsigned int) pEfc, page, offset);

    // Store values
    if (ppEfc) {

        *ppEfc = pEfc;
    }
    if (pPage) {

        *pPage = page;
    }
    if (pOffset) {

        *pOffset = offset;
    }
}

//------------------------------------------------------------------------------
/// Computes the address of a flash access given the EFC, page and offset.
/// \param pEfc  Pointer to an AT91S_EFC structure.
/// \param page  Page number.
/// \param offset  Byte offset inside page.
/// \param pAddress  Computed address (optional).
//------------------------------------------------------------------------------
void EFC_ComputeAddress(
    AT91S_EFC *pEfc,
    unsigned short page,
    unsigned short offset,
    unsigned int *pAddress)
{
    unsigned int address;

    SANITY_CHECK(pEfc);
#if defined(AT91C_BASE_EFC1)
    SANITY_CHECK(page <= (AT91C_IFLASH_NB_OF_PAGES / 2));
#else
    SANITY_CHECK(page <= AT91C_IFLASH_NB_OF_PAGES);
#endif
    SANITY_CHECK(offset < AT91C_IFLASH_PAGE_SIZE);

    // Compute address
    address = AT91C_IFLASH + page * AT91C_IFLASH_PAGE_SIZE + offset;
#if defined(AT91C_BASE_EFC1)
    if (pEfc == AT91C_BASE_EFC1) {

        address += AT91C_IFLASH_SIZE / 2;
    }
#endif

    // Store result
    if (pAddress) {

        *pAddress = address;
    }
}

//------------------------------------------------------------------------------
/// Starts the executing the given command on an EFC. This function returns
/// as soon as the command is started. It does NOT set the FMCN field automatically.
/// \param pEfc  Pointer to an AT91S_EFC structure.
/// \param command  Command to execute.
/// \param argument  Command argument (should be 0 if not used).
//------------------------------------------------------------------------------
#if defined(flash)
   #ifdef __ICCARM__
__ramfunc
   #else
__attribute__ ((section (".ramfunc")))
   #endif
#endif
void EFC_StartCommand(
    AT91S_EFC *pEfc,
    unsigned char command,
    unsigned short argument)
{
    SANITY_CHECK(pEfc);
    ASSERT(lMck != 0, "-F- Master clock not set.\n\r");
    
    // Check command & argument
    switch (command) {

        case AT91C_MC_FCMD_PROG_AND_LOCK:
            ASSERT(0, "-F- Write and lock command cannot be carried out.\n\r");
            break;

        case AT91C_MC_FCMD_START_PROG:
        case AT91C_MC_FCMD_LOCK:
        case AT91C_MC_FCMD_UNLOCK:
            ASSERT(argument < AT91C_IFLASH_NB_OF_PAGES,
                   "-F- Maximum number of pages is %d (argument was %d)\n\r",
                   AT91C_IFLASH_NB_OF_PAGES,
                   argument);
            break;

#if (EFC_NUM_GPNVMS > 0)
        case AT91C_MC_FCMD_SET_GP_NVM:
        case AT91C_MC_FCMD_CLR_GP_NVM:
            ASSERT(argument < EFC_NUM_GPNVMS, "-F- A maximum of %d GPNVMs are available on the chip.\n\r", EFC_NUM_GPNVMS);
            break;
#endif

        case AT91C_MC_FCMD_ERASE_ALL:

#if !defined(EFC_NO_SECURITY_BIT)
        case AT91C_MC_FCMD_SET_SECURITY:
#endif
            ASSERT(argument == 0, "-F- Argument is meaningless for the given command\n\r");
            break;

        default: ASSERT(0, "-F- Unknown command %d\n\r", command);
    }

    // Set FMCN
    switch (command) {

        case AT91C_MC_FCMD_LOCK:
        case AT91C_MC_FCMD_UNLOCK:
#if (EFC_NUM_GPNVMS > 0)
        case AT91C_MC_FCMD_SET_GP_NVM:
        case AT91C_MC_FCMD_CLR_GP_NVM:
#endif
#if !defined(EFC_NO_SECURITY_BIT)
        case AT91C_MC_FCMD_SET_SECURITY:
#endif
            pEfc->EFC_FMR = (pEfc->EFC_FMR & ~AT91C_MC_FMCN) | FMCN_BITS(lMck);
            break;

        case AT91C_MC_FCMD_START_PROG:
        case AT91C_MC_FCMD_ERASE_ALL:
            pEfc->EFC_FMR = (pEfc->EFC_FMR & ~AT91C_MC_FMCN) | FMCN_FLASH(lMck);
            break;
    }

    // Start command
    ASSERT((pEfc->EFC_FSR & AT91C_MC_FRDY) != 0, "-F- Efc is not ready\n\r");
    pEfc->EFC_FCR = (0x5A << 24) | (argument << 8) | command;
}

//------------------------------------------------------------------------------
/// Performs the given command and wait until its completion (or an error).
/// Returns 0 if successful; otherwise returns an error code.
/// \param pEfc  Pointer to an AT91S_EFC structure.
/// \param command  Command to perform.
/// \param argument  Optional command argument.
//------------------------------------------------------------------------------
#if defined(flash)
   #ifdef __ICCARM__
__ramfunc
   #else
__attribute__ ((section (".ramfunc")))
   #endif
#endif
unsigned char EFC_PerformCommand(
    AT91S_EFC *pEfc,
    unsigned char command,
    unsigned short argument)
{
    unsigned int status;

    // Set FMCN
    switch (command) {

        case AT91C_MC_FCMD_LOCK:
        case AT91C_MC_FCMD_UNLOCK:
#if (EFC_NUM_GPNVMS > 0)
        case AT91C_MC_FCMD_SET_GP_NVM:
        case AT91C_MC_FCMD_CLR_GP_NVM:
#endif
#if !defined(EFC_NO_SECURITY_BIT)
        case AT91C_MC_FCMD_SET_SECURITY:
#endif
            pEfc->EFC_FMR = (pEfc->EFC_FMR & ~AT91C_MC_FMCN) | FMCN_BITS(lMck);
            break;

        case AT91C_MC_FCMD_START_PROG:
        case AT91C_MC_FCMD_ERASE_ALL:
            pEfc->EFC_FMR = (pEfc->EFC_FMR & ~AT91C_MC_FMCN) | FMCN_FLASH(lMck);
            break;
    }

#ifdef BOARD_FLASH_IAP_ADDRESS
    // Pointer on IAP function in ROM
    static void (*IAP_PerformCommand)(unsigned int, unsigned int);
    unsigned int index = 0;
#ifdef AT91C_BASE_EFC1
    if (pEfc == AT91C_BASE_EFC1) {

        index = 1;
    }
#endif
    IAP_PerformCommand = (void (*)(unsigned int, unsigned int)) *((unsigned int *) BOARD_FLASH_IAP_ADDRESS);

    // Check if IAP function is implemented (opcode in SWI != 'b' or 'ldr') */
    if ((((((unsigned long) IAP_PerformCommand >> 24) & 0xFF) != 0xEA) &&
        (((unsigned long) IAP_PerformCommand >> 24) & 0xFF) != 0xE5)) {

        IAP_PerformCommand(index, (0x5A << 24) | (argument << 8) | command);
        return (pEfc->EFC_FSR & (AT91C_MC_LOCKE | AT91C_MC_PROGE));
    }
#endif

    pEfc->EFC_FCR = (0x5A << 24) | (argument << 8) | command;
    do {

        status = pEfc->EFC_FSR;
    }
    while ((status & AT91C_MC_FRDY) == 0);

    return (status & (AT91C_MC_PROGE | AT91C_MC_LOCKE));
}

//------------------------------------------------------------------------------
/// Returns the current status of an EFC. Keep in mind that this function clears
/// the value of some status bits (LOCKE, PROGE).
/// \param pEfc  Pointer to an AT91S_EFC structure.
//------------------------------------------------------------------------------
unsigned int EFC_GetStatus(AT91S_EFC *pEfc)
{
    return pEfc->EFC_FSR;
}

#endif //#ifdef BOARD_FLASH_EFC

