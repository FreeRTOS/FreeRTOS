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

#include "mci.h"
#include <utility/assert.h>
#include <utility/trace.h>

//------------------------------------------------------------------------------
//         Local constants
//------------------------------------------------------------------------------

/// Bit mask for status register errors.
#define STATUS_ERRORS (AT91C_MCI_UNRE  \
                       | AT91C_MCI_OVRE \
                       | AT91C_MCI_DTOE \
                       | AT91C_MCI_DCRCE \
                       | AT91C_MCI_RTOE \
                       | AT91C_MCI_RENDE \
                       | AT91C_MCI_RCRCE \
                       | AT91C_MCI_RDIRE \
                       | AT91C_MCI_RINDE)

/// MCI data timeout configuration with 1048576 MCK cycles between 2 data transfers.
#define DTOR_1MEGA_CYCLES           (AT91C_MCI_DTOCYC | AT91C_MCI_DTOMUL)

/// MCI MR: disable MCI Clock when FIFO is full
#ifndef AT91C_MCI_WRPROOF
    #define AT91C_MCI_WRPROOF 0
#endif
#ifndef AT91C_MCI_RDPROOF
    #define AT91C_MCI_RDPROOF 0
#endif

#define SDCARD_APP_OP_COND_CMD      (41 | AT91C_MCI_SPCMD_NONE  | AT91C_MCI_RSPTYP_48   | AT91C_MCI_TRCMD_NO )
#define MMC_SEND_OP_COND_CMD        (1  | AT91C_MCI_TRCMD_NO    | AT91C_MCI_SPCMD_NONE  | AT91C_MCI_RSPTYP_48 | AT91C_MCI_OPDCMD)


#define DISABLE    0    // Disable MCI interface
#define ENABLE     1    // Enable MCI interface


//------------------------------------------------------------------------------
//         Local macros
//------------------------------------------------------------------------------

/// Used to write in PMC registers.
#define WRITE_PMC(pPmc, regName, value)     pPmc->regName = (value)

/// Used to write in MCI registers.
#define WRITE_MCI(pMci, regName, value)     pMci->regName = (value)

/// Used to read from MCI registers.
#define READ_MCI(pMci, regName)             (pMci->regName)

//------------------------------------------------------------------------------
//         Global functions
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
/// Enable/disable a MCI driver instance.
/// \param pMci  Pointer to a MCI driver instance.
/// \param enb  0 for disable MCI and 1 for enable MCI.
//------------------------------------------------------------------------------
void MCI_Enable(Mci *pMci, unsigned char enb)
{
    AT91S_MCI *pMciHw = pMci->pMciHw;

    SANITY_CHECK(pMci);
    SANITY_CHECK(pMci->pMciHw);

    // Set the Control Register: Enable/Disable MCI interface clock
    if(enb == DISABLE) {
        WRITE_MCI(pMciHw, MCI_CR, AT91C_MCI_MCIDIS);
    }
    else {
        WRITE_MCI(pMciHw, MCI_CR, AT91C_MCI_MCIEN);
    }
}

//------------------------------------------------------------------------------
/// Initializes a MCI driver instance and the underlying peripheral.
/// \param pMci  Pointer to a MCI driver instance.
/// \param pMciHw  Pointer to a MCI peripheral.
/// \param mciId  MCI peripheral identifier.
/// \param mode  Slot and type of connected card.
//------------------------------------------------------------------------------
void MCI_Init(
    Mci *pMci,
    AT91S_MCI *pMciHw,
    unsigned char mciId,
    unsigned int mode)
{
    unsigned short clkDiv;

    SANITY_CHECK(pMci);
    SANITY_CHECK(pMciHw);
    SANITY_CHECK((mode == MCI_MMC_SLOTA) || (mode == MCI_MMC_SLOTB)
                 || (mode == MCI_SD_SLOTA) || (mode == MCI_SD_SLOTB));

    // Initialize the MCI driver structure
    pMci->pMciHw = pMciHw;
    pMci->mciId  = mciId;
    pMci->semaphore = 1;
    pMci->pCommand = 0;

    // Enable the MCI clock
    WRITE_PMC(AT91C_BASE_PMC, PMC_PCER, (1 << mciId));

     // Reset the MCI
    WRITE_MCI(pMciHw, MCI_CR, AT91C_MCI_SWRST);

    // Disable the MCI
    WRITE_MCI(pMciHw, MCI_CR, AT91C_MCI_MCIDIS | AT91C_MCI_PWSDIS);

    // Disable all the interrupts
    WRITE_MCI(pMciHw, MCI_IDR, 0xFFFFFFFF);

    // Set the Data Timeout Register
    WRITE_MCI(pMciHw, MCI_DTOR, DTOR_1MEGA_CYCLES);

    // Set the Mode Register: 400KHz for MCK = 48MHz (CLKDIV = 58)
    clkDiv = (BOARD_MCK / (400000 * 2)) - 1;
    WRITE_MCI(pMciHw, MCI_MR, (clkDiv | (AT91C_MCI_PWSDIV & (0x7 << 8))));

    // Set the SDCard Register
    WRITE_MCI(pMciHw, MCI_SDCR, mode);

    // Enable the MCI and the Power Saving
    WRITE_MCI(pMciHw, MCI_CR, AT91C_MCI_MCIEN);

    // Disable the MCI peripheral clock.
    WRITE_PMC(AT91C_BASE_PMC, PMC_PCDR, (1 << mciId));
}

//------------------------------------------------------------------------------
/// Close a MCI driver instance and the underlying peripheral.
/// \param pMci  Pointer to a MCI driver instance.
/// \param pMciHw  Pointer to a MCI peripheral.
/// \param mciId  MCI peripheral identifier.
//------------------------------------------------------------------------------
void MCI_Close(Mci *pMci)
{
    AT91S_MCI *pMciHw = pMci->pMciHw;

    SANITY_CHECK(pMci);
    SANITY_CHECK(pMciHw);

    // Initialize the MCI driver structure
    pMci->semaphore = 1;
    pMci->pCommand = 0;

    // Disable the MCI peripheral clock.
    WRITE_PMC(AT91C_BASE_PMC, PMC_PCDR, (1 << pMci->mciId));

    // Disable the MCI
    WRITE_MCI(pMciHw, MCI_CR, AT91C_MCI_MCIDIS);

    // Disable all the interrupts
    WRITE_MCI(pMciHw, MCI_IDR, 0xFFFFFFFF);
}

//------------------------------------------------------------------------------
/// Configure the  MCI CLKDIV in the MCI_MR register. The max. for MCI clock is
/// MCK/2 and corresponds to CLKDIV = 0
/// \param pMci  Pointer to the low level MCI driver.
/// \param mciSpeed  MCI clock speed in Hz.
//------------------------------------------------------------------------------
void MCI_SetSpeed(Mci *pMci, unsigned int mciSpeed)
{
    AT91S_MCI *pMciHw = pMci->pMciHw;
    unsigned int mciMr;
    unsigned int clkdiv;

    SANITY_CHECK(pMci);
    SANITY_CHECK(pMci->pMciHw);

    // Set the Mode Register: 400KHz for MCK = 48MHz (CLKDIV = 58)
    mciMr = READ_MCI(pMciHw, MCI_MR) & (~AT91C_MCI_CLKDIV);

    // Multimedia Card Interface clock (MCCK or MCI_CK) is Master Clock (MCK)
    // divided by (2*(CLKDIV+1))
    if (mciSpeed > 0) {

        clkdiv = (BOARD_MCK / (mciSpeed * 2));
        if (clkdiv > 0) {

            clkdiv -= 1;
        }
        ASSERT( (clkdiv & 0xFFFFFF00) == 0, "mciSpeed too small");
    }
    else {

        clkdiv = 0;
    }

    WRITE_MCI(pMciHw, MCI_MR, mciMr | clkdiv);
}

//------------------------------------------------------------------------------
/// Configure the  MCI SDCBUS in the MCI_SDCR register. Only two modes available
///
/// \param pMci  Pointer to the low level MCI driver.
/// \param busWidth  MCI bus width mode.
//------------------------------------------------------------------------------
void MCI_SetBusWidth(Mci *pMci, unsigned char busWidth)
{
    AT91S_MCI *pMciHw = pMci->pMciHw;
    unsigned int mciSdcr;

    SANITY_CHECK(pMci);
    SANITY_CHECK(pMci->pMciHw);

    mciSdcr = (READ_MCI(pMciHw, MCI_SDCR) & ~(AT91C_MCI_SCDBUS));

    WRITE_MCI(pMciHw, MCI_SDCR, mciSdcr | busWidth);
}

//------------------------------------------------------------------------------
/// Starts a MCI  transfer. This is a non blocking function. It will return
/// as soon as the transfer is started.
/// Return 0 if successful; otherwise returns MCI_ERROR_LOCK if the driver is
/// already in use.
/// \param pMci  Pointer to an MCI driver instance.
/// \param pCommand  Pointer to the command to execute.
//------------------------------------------------------------------------------
unsigned char MCI_SendCommand(Mci *pMci, MciCmd *pCommand)
{
    AT91PS_MCI pMciHw = pMci->pMciHw;
    unsigned int mciIer, mciMr;

    SANITY_CHECK(pMci);
    SANITY_CHECK(pMciHw);
    SANITY_CHECK(pCommand);

    // Try to acquire the MCI semaphore
    if (pMci->semaphore == 0) {

        return MCI_ERROR_LOCK;
    }
    pMci->semaphore--;
    // TRACE_DEBUG("MCI_SendCommand %x %d\n\r", READ_MCI(pMciHw, MCI_SR), pCommand->cmd & 0x3f);

    // Command is now being executed
    pMci->pCommand = pCommand;
    pCommand->status = MCI_STATUS_PENDING;

    // Enable the MCI clock
    WRITE_PMC(AT91C_BASE_PMC, PMC_PCER, (1 << pMci->mciId));

    //Disable MCI clock, for multi-block data transfer
    MCI_Enable(pMci, DISABLE);

    // Set PDC data transfer direction
    if(pCommand->blockSize > 0) {
        if(pCommand->isRead) {
            WRITE_MCI(pMciHw, MCI_PTCR, AT91C_PDC_RXTEN);
        }
        else {
            WRITE_MCI(pMciHw, MCI_PTCR, AT91C_PDC_TXTEN);
        }
    }
    // Disable transmitter and receiver
    WRITE_MCI(pMciHw, MCI_PTCR, AT91C_PDC_RXTDIS | AT91C_PDC_TXTDIS);

    mciMr = READ_MCI(pMciHw, MCI_MR) & (~(AT91C_MCI_WRPROOF|AT91C_MCI_RDPROOF|AT91C_MCI_BLKLEN | AT91C_MCI_PDCMODE));

    // Command with DATA stage
    if (pCommand->blockSize > 0) {
        // Enable PDC mode and set block size
        if(pCommand->conTrans != MCI_CONTINUE_TRANSFER) {

            WRITE_MCI(pMciHw, MCI_MR, mciMr | AT91C_MCI_PDCMODE |AT91C_MCI_RDPROOF|AT91C_MCI_WRPROOF|(pCommand->blockSize << 16));
        }

        // DATA transfer from card to host
        if (pCommand->isRead) {
            WRITE_MCI(pMciHw, MCI_RPR, (int) pCommand->pData);

            // Sanity check
            if (pCommand->nbBlock == 0)
                pCommand->nbBlock = 1;
            ////////
            if ((pCommand->blockSize & 0x3) != 0) {
                WRITE_MCI(pMciHw, MCI_RCR, (pCommand->nbBlock * pCommand->blockSize) / 4 + 1);
            }
            else {
                WRITE_MCI(pMciHw, MCI_RCR, (pCommand->nbBlock * pCommand->blockSize) / 4);
            }

            WRITE_MCI(pMciHw, MCI_PTCR, AT91C_PDC_RXTEN);
            mciIer = AT91C_MCI_ENDRX | STATUS_ERRORS;
            // mciIer = AT91C_MCI_RXBUFF | STATUS_ERRORS;
        }

        // DATA transfer from host to card
        else {
            // Sanity check
            if (pCommand->nbBlock == 0)
                pCommand->nbBlock = 1;
            WRITE_MCI(pMciHw, MCI_TPR, (int) pCommand->pData);
            // Update the PDC counter
            if ((pCommand->blockSize & 0x3) != 0) {
                WRITE_MCI(pMciHw, MCI_TCR, (pCommand->nbBlock * pCommand->blockSize) / 4 + 1);
            }
            else {
                WRITE_MCI(pMciHw, MCI_TCR, (pCommand->nbBlock * pCommand->blockSize) / 4);
            }
            // MCI_BLKE notifies the end of Multiblock command
            mciIer = AT91C_MCI_BLKE | STATUS_ERRORS;
        }
    }
    // No data transfer: stop at the end of the command
    else {
        WRITE_MCI(pMciHw, MCI_MR, mciMr);
        mciIer = AT91C_MCI_CMDRDY | STATUS_ERRORS;
    }
    // Enable MCI clock
    MCI_Enable(pMci, ENABLE);

    // Send the command
    if((pCommand->conTrans != MCI_CONTINUE_TRANSFER)
        || (pCommand->blockSize == 0)) {

        WRITE_MCI(pMciHw, MCI_ARGR, pCommand->arg);
        WRITE_MCI(pMciHw, MCI_CMDR, pCommand->cmd);
    }

    // In case of transmit, the PDC shall be enabled after sending the command
    if ((pCommand->blockSize > 0) && !(pCommand->isRead)) {
        WRITE_MCI(pMciHw, MCI_PTCR, AT91C_PDC_TXTEN);
    }

    // Ignore data error
    mciIer &= ~(AT91C_MCI_UNRE | AT91C_MCI_OVRE \
              | AT91C_MCI_DTOE | AT91C_MCI_DCRCE);

    // Interrupt enable shall be done after PDC TXTEN and RXTEN
    WRITE_MCI(pMciHw, MCI_IER, mciIer);

    return 0;
}

//------------------------------------------------------------------------------
/// Check NOTBUSY and DTIP bits of status register on the given MCI driver.
/// Return value, 0 for bus ready, 1 for bus busy
/// \param pMci  Pointer to a MCI driver instance.
//------------------------------------------------------------------------------
unsigned char MCI_CheckBusy(Mci *pMci)
{
    AT91S_MCI *pMciHw = pMci->pMciHw;
    unsigned int status;

    // Enable MCI clock
    MCI_Enable(pMci, ENABLE);

    status = READ_MCI(pMciHw, MCI_SR);
    // TRACE_DEBUG("status %x\n\r",status);


    if(((status & AT91C_MCI_NOTBUSY)!=0)
        && ((status & AT91C_MCI_DTIP)==0)) {

        // Disable MCI clock
        MCI_Enable(pMci, DISABLE);

        return 0;
    }
    else {
        return 1;
    }
}

//------------------------------------------------------------------------------
/// Check BLKE bit of status register on the given MCI driver.
/// \param pMci  Pointer to a MCI driver instance.
//------------------------------------------------------------------------------
unsigned char MCI_CheckBlke(Mci *pMci)
{
    AT91S_MCI *pMciHw = pMci->pMciHw;
    unsigned int status;

    status = READ_MCI(pMciHw, MCI_SR);
    // TRACE_DEBUG("status %x\n\r",status);

    if((status & AT91C_MCI_BLKE)!=0) {
        return 0;
    }
    else {
        return 1;
    }
}

//------------------------------------------------------------------------------
/// Processes pending events on the given MCI driver.
/// \param pMci  Pointer to a MCI driver instance.
//------------------------------------------------------------------------------
void MCI_Handler(Mci *pMci)
{
    AT91S_MCI *pMciHw = pMci->pMciHw;
    MciCmd *pCommand = pMci->pCommand;
    unsigned int status;
    unsigned char i;
    #if defined(at91rm9200)
    unsigned int mciCr, mciSdcr, mciMr, mciDtor;
    #endif

    SANITY_CHECK(pMci);
    SANITY_CHECK(pMciHw);
    SANITY_CHECK(pCommand);

    // Read the status register
    status = READ_MCI(pMciHw, MCI_SR) & READ_MCI(pMciHw, MCI_IMR);
    // TRACE_DEBUG("status %x\n\r", status);

    // Check if an error has occured
    if ((status & STATUS_ERRORS) != 0) {

        // Check error code
        if ((status & STATUS_ERRORS) == AT91C_MCI_RTOE) {

            pCommand->status = MCI_STATUS_NORESPONSE;
        }
        // if the command is SEND_OP_COND the CRC error flag is always present
        // (cf : R3 response)
        else if (((status & STATUS_ERRORS) != AT91C_MCI_RCRCE)
                  || ((pCommand->cmd != SDCARD_APP_OP_COND_CMD)
                      && (pCommand->cmd != MMC_SEND_OP_COND_CMD))) {

            pCommand->status = MCI_STATUS_ERROR;
        }
    }

    // Check if a transfer has been completed
    if (((status & AT91C_MCI_CMDRDY) != 0)
        || ((status & AT91C_MCI_ENDRX) != 0)
        || ((status & AT91C_MCI_RXBUFF) != 0)
        || ((status & AT91C_MCI_ENDTX) != 0)
        || ((status & AT91C_MCI_BLKE) != 0)
        || ((status & AT91C_MCI_RTOE) != 0)) {

        if (((status & AT91C_MCI_ENDRX) != 0)
            || ((status & AT91C_MCI_RXBUFF) != 0)
            || ((status & AT91C_MCI_ENDTX) != 0)) {

            MCI_Enable(pMci, DISABLE);
        }

        /// On AT91RM9200-EK, if stop transmission, software reset MCI.
        #if defined(at91rm9200)
        if ((pCommand->cmd & AT91C_MCI_TRCMD_STOP) != 0) {
            mciMr = READ_MCI(pMciHw, MCI_MR);
            mciSdcr = READ_MCI(pMciHw, MCI_SDCR);
            mciDtor = READ_MCI(pMciHw, MCI_DTOR);
            WRITE_MCI(pMciHw, MCI_CR, AT91C_MCI_SWRST);
            // TRACE_DEBUG("reset MCI\n\r");

            WRITE_MCI(pMciHw, MCI_CR, AT91C_MCI_MCIDIS | AT91C_MCI_PWSDIS);
            WRITE_MCI(pMciHw, MCI_MR, mciMr);
            WRITE_MCI(pMciHw, MCI_SDCR, mciSdcr);
            WRITE_MCI(pMciHw, MCI_DTOR, mciDtor);
        }
        #endif

        // If no error occured, the transfer is successful
        if (pCommand->status == MCI_STATUS_PENDING) {
            pCommand->status = 0;
        }
#if 0
        if ((status & AT91C_MCI_CMDRDY) != 0)
            TRACE_DEBUG_WP(".");
        if ((status & AT91C_MCI_ENDRX) != 0)
            TRACE_DEBUG_WP("<");
        if ((status & AT91C_MCI_ENDTX) != 0)
            TRACE_DEBUG_WP("-");
        if ((status & AT91C_MCI_BLKE) != 0)
            TRACE_DEBUG_WP(">");
        TRACE_DEBUG_WP("\n\r");
#endif
        // Store the card response in the provided buffer
        if (pCommand->pResp) {
            unsigned char resSize;

            switch (pCommand->resType) {
                case 1:
                resSize = 1;
                break;

                case 2:
                resSize = 4;
                break;

                case 3:
                resSize = 1;
                break;

                case 4:
                resSize = 1;
                break;

                case 5:
                resSize = 1;
                break;

                case 6:
                resSize = 1;
                break;

                case 7:
                resSize = 1;
                break;

                default:
                resSize = 0;
                break;
            }
            for (i=0; i < resSize; i++) {

                pCommand->pResp[i] = READ_MCI(pMciHw, MCI_RSPR[0]);
            }
        }

        // Disable interrupts
        WRITE_MCI(pMciHw, MCI_IDR, READ_MCI(pMciHw, MCI_IMR));

        // Release the semaphore
        pMci->semaphore++;

        // Invoke the callback associated with the current command (if any)
        if (pCommand->callback) {
            (pCommand->callback)(pCommand->status, pCommand);
        }
    }
}

//------------------------------------------------------------------------------
/// Returns 1 if the given MCI transfer is complete; otherwise returns 0.
/// \param pCommand  Pointer to a MciCmd instance.
//------------------------------------------------------------------------------
unsigned char MCI_IsTxComplete(MciCmd *pCommand)
{
    if (pCommand->status != MCI_STATUS_PENDING) {
        if (pCommand->status != 0) {
            TRACE_DEBUG("MCI_IsTxComplete %d\n\r", pCommand->status);
        }
        return 1;
    }
    else {
        return 0;
    }
}
