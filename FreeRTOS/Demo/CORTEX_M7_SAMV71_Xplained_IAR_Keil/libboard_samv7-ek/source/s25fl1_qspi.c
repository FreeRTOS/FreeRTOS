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


/** 
 * \addtogroup at25_spi_module S25FL1 SPI driver
 * \ingroup lib_spiflash
 *
 * The S25FL1 serial firmware dataflash driver is based on top of the
 * corresponding Spi driver. A Dataflash structure instance has to be
 * initialized using the S25FL1_Configure() function. Then a command can be send 
 * to the serial flash using the SPI_SendCommand() function. 
 *
 * \section Usage
 * <ul>
 * <li>Initializes an S25FL1 instance and configures SPI chip select pin
 *    using S25FL1_Configure(). </li>
 * <li>Detect DF and returns DF description corresponding to the device
 *    connected using S25FL1D_ReadJedecId() and S25FL1_FindDevice().
 *    This function shall be called by the application before S25FL1_SendCommand().</li>
 * <li> Sends a command to the DF through the SPI using S25FL1_SendCommand().
 *    The command is identified by its command code and the number of
 *    bytes to transfer.</li>
 *    <li> Example code for sending command to write a page to DF.</li>
 *    \code
 *        // Program page
 *        error = S25FL1_SendCommand(pS25fl1, S25FL1_BYTE_PAGE_PROGRAM, 4,
 *                pData, writeSize, address, 0, 0);
 *    \endcode
 *    <li> Example code for sending command to read a page from DF.
 *       If data needs to be received, then a data buffer must be
 *       provided.</li>
 *    \code
 *        // Start a read operation
 *        error = S25FL1_SendCommand(pS25fl1, S25FL1_READ_ARRAY_LF,
 *                4, pData, size, address, 0, 0);
 *    \endcode
 *    <li> This function does not block; its optional callback will
 *       be invoked when the transfer completes.</li>
 * <li> Check the S25FL1 driver is ready or not by polling S25FL1_IsBusy().</li>
 * </ul>
 *
 * Related files :\n
 * \ref at25_spi.c\n
 * \ref at25_spi.h.\n
 */

/**
 * \file
 *
 * Implementation for the S25FL1 SPI driver.
 *
 */

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/
#include <board.h>
//#include <libspiflash.h>
#include <assert.h>

/*----------------------------------------------------------------------------
 *        Local definitions
 *----------------------------------------------------------------------------*/



/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

/**
 * \brief Initializes an S25FL1 driver instance with the given SPI driver and chip
 * select value.
 *
 * \param pS25fl1  Pointer to an S25FL1 driver instance.
 * \param pSpid  Pointer to an SPI driver instance.
 * \param cs  Chip select value to communicate with the serial flash.
 * \param polling Uses polling mode instead of IRQ trigger.
 */
void S25FL1_Configure(S25fl1 *pS25fl1, Qspid *pQspid, uint8_t polling)
{
    SpidCmd *pCommand;

    assert(pS25fl1);
    assert(pQSpid);


    /* Initialize the S25FL1 fields */
    pS25fl1->pQspid = pSpid;
    pS25fl1->pDesc = 0;
    pS25fl1->pollingMode = polling;

    /* Initialize the command structure */
    pCommand = &(pS25fl1->command);
    pCommand->pCmd = (uint8_t *) pS25fl1->CmdBuffer;
    pCommand->callback = 0;
    pCommand->pArgument = 0;
}

/**
 * \brief Is serial flash driver busy.
 *
 * \param pS25fl1  Pointer to an S25fl1 driver instance.
 *
 * \return 1 if the serial flash driver is currently busy executing a command;
 * otherwise returns 0.
 */
uint8_t S25FL1_IsBusy(S25fl1 *pS25fl1)
{
    if (pS25fl1->pollingMode)
    {
        SPID_Handler(pS25fl1->pSpid);
        SPID_DmaHandler(pS25fl1->pSpid);
    }
    return SPID_IsBusy(pS25fl1->pSpid);
}

/**
 * \brief Sends a command to the serial flash through the SPI. The command is made up
 * of two parts: the first is used to transmit the command byte and optionally,
 * address and dummy bytes. The second part is the data to send or receive.
 * This function does not block: it returns as soon as the transfer has been
 * started. An optional callback can be invoked to notify the end of transfer.
 *
 * \param pS25fl1  Pointer to an S25fl1 driver instance.
 * \param cmd  Command byte.
 * \param cmdSize  Size of command (command byte + address bytes + dummy bytes).
 * \param pData Data buffer.
 * \param dataSize  Number of bytes to send/receive.
 * \param address  Address to transmit.
 * \param callback  Optional user-provided callback to invoke at end of transfer.
 * \param pArgument  Optional argument to the callback function.
 *
 * \return 0 if successful; otherwise, returns S25FL1_ERROR_BUSY if the S25FL1
 * driver is currently executing a command, or S25FL1_ERROR_SPI if the command
 * cannot be sent because of a SPI error.
 */
uint8_t S25FL1_SendCommand(uint8_t Instr, uint8_t ReadWrite)

{  
    pDev->Instruction = Instr; 
    QSPI_SendFrame(QSPI, pDev, ReadWrite);
}

/**
 * \brief Tries to detect a serial firmware flash device given its JEDEC identifier.
 * The JEDEC id can be retrieved by sending the correct command to the device.
 *
 * \param pS25fl1  Pointer to an S25FL1 driver instance.
 * \param jedecId  JEDEC identifier of device.
 *
 * \return the corresponding S25FL1 descriptor if found; otherwise returns 0.
 */
const S25fl1Desc * S25FL1_FindDevice(S25fl1 *pS25fl1, uint32_t jedecId)
{
    uint32_t i = 0;

    assert(pS25fl1);

    /* Search if device is recognized */
    pS25fl1->pDesc = 0;
    while ((i < NUMDATAFLASH) && !(pS25fl1->pDesc)) {

        if ((jedecId & 0xFF00FFFF) == (at25Devices[i].jedecId & 0xFF00FFFF)) {

            pS25fl1->pDesc = &(at25Devices[i]);
        }

        i++;
    }

    return pS25fl1->pDesc;
}
