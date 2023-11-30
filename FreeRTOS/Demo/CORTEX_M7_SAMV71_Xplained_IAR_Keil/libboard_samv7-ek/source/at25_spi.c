/* ----------------------------------------------------------------------------
 *         ATMEL Microcontroller Software Support
 * ----------------------------------------------------------------------------
 * Copyright (c) 2010, Atmel Corporation
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
 * \addtogroup at25_spi_module AT25 SPI driver
 * \ingroup at25d_module
 *
 * The AT25 serial firmware dataflash driver is based on top of the
 * corresponding Spi driver. A Dataflash structure instance has to be
 * initialized using the AT25_Configure() function. Then a command can be send 
 * to the serial flash using the SPI_SendCommand() function. 
 *
 * \section Usage
 * <ul>
 * <li>Initializes an AT25 instance and configures SPI chip select pin
 *    using AT25_Configure(). </li>
 * <li>Detect DF and returns DF description corresponding to the device
 *    connected using AT25D_ReadJedecId() and AT25_FindDevice().
 *    This function shall be called by the application before AT25_SendCommand().</li>
 * <li> Sends a command to the DF through the SPI using AT25_SendCommand().
 *    The command is identified by its command code and the number of
 *    bytes to transfer.</li>
 *    <li> Example code for sending command to write a page to DF.</li>
 *    \code
 *        // Program page
 *        error = AT25_SendCommand(pAt25, AT25_BYTE_PAGE_PROGRAM, 4,
 *                pData, writeSize, address, 0, 0);
 *    \endcode
 *    <li> Example code for sending command to read a page from DF.
 *       If data needs to be received, then a data buffer must be
 *       provided.</li>
 *    \code
 *        // Start a read operation
 *        error = AT25_SendCommand(pAt25, AT25_READ_ARRAY_LF,
 *                4, pData, size, address, 0, 0);
 *    \endcode
 *    <li> This function does not block; its optional callback will
 *       be invoked when the transfer completes.</li>
 * <li> Check the AT25 driver is ready or not by polling AT25_IsBusy().</li>
 * </ul>
 *
 * Related files :\n
 * \ref at25_spi.c\n
 * \ref at25_spi.h.\n
 */

/**
 * \file
 *
 * Implementation for the AT25 SPI driver.
 *
 */

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/
#include <board.h>
#include <assert.h>

/*----------------------------------------------------------------------------
 *        Local definitions
 *----------------------------------------------------------------------------*/

/** SPI clock frequency used in Hz. */
#define SPCK            1000000

/** SPI chip select configuration value. */
#define CSR             (SPI_CSR_NCPHA | \
                         SPID_CSR_DLYBCT(BOARD_MCK, 100) | \
                         SPID_CSR_DLYBS(BOARD_MCK, 10) | \
                         SPID_CSR_SCBR(BOARD_MCK, SPCK))

/** Number of recognized dataflash. */
#define NUMDATAFLASH    (sizeof(at25Devices) / sizeof(At25Desc))

/*----------------------------------------------------------------------------
 *        Local variables
 *----------------------------------------------------------------------------*/

/** Array of recognized serial firmware dataflash chips. */
static const At25Desc at25Devices[] = {
    /* name,        Jedec ID,       size,  page size, block size, block erase command */
    {"AT25DF041A" , 0x0001441F,      512 * 1024, 256,  4 * 1024, AT25_BLOCK_ERASE_4K},
    {"AT25DF161"  , 0x0002461F, 2 * 1024 * 1024, 256,  4 * 1024, AT25_BLOCK_ERASE_4K},
    {"AT26DF081A" , 0x0001451F, 1 * 1024 * 1024, 256,  4 * 1024, AT25_BLOCK_ERASE_4K},
    {"AT26DF0161" , 0x0000461F, 2 * 1024 * 1024, 256,  4 * 1024, AT25_BLOCK_ERASE_4K},
    {"AT26DF161A" , 0x0001461F, 2 * 1024 * 1024, 256,  4 * 1024, AT25_BLOCK_ERASE_4K},
    {"AT25DF321"  , 0x0000471F, 4 * 1024 * 1024, 256,  4 * 1024, AT25_BLOCK_ERASE_4K},
    {"AT25DF321A" , 0x0001471F, 4 * 1024 * 1024, 256,  4 * 1024, AT25_BLOCK_ERASE_4K},
    {"AT25DF512B" , 0x0001651F,       64 * 1024, 256,  4 * 1024, AT25_BLOCK_ERASE_4K},
    {"AT25DF512B" , 0x0000651F,       64 * 1024, 256,  4 * 1024, AT25_BLOCK_ERASE_4K},
    {"AT25DF021"  , 0x0000431F,      256 * 1024, 256,  4 * 1024, AT25_BLOCK_ERASE_4K},
    {"AT26DF641"  , 0x0000481F, 8 * 1024 * 1024, 256,  4 * 1024, AT25_BLOCK_ERASE_4K},
    /* Manufacturer: ST */
    {"M25P05"     , 0x00102020,       64 * 1024, 256, 32 * 1024, AT25_BLOCK_ERASE_64K},
    {"M25P10"     , 0x00112020,      128 * 1024, 256, 32 * 1024, AT25_BLOCK_ERASE_64K},
    {"M25P20"     , 0x00122020,      256 * 1024, 256, 64 * 1024, AT25_BLOCK_ERASE_64K},
    {"M25P40"     , 0x00132020,      512 * 1024, 256, 64 * 1024, AT25_BLOCK_ERASE_64K},
    {"M25P80"     , 0x00142020, 1 * 1024 * 1024, 256, 64 * 1024, AT25_BLOCK_ERASE_64K},
    {"M25P16"     , 0x00152020, 2 * 1024 * 1024, 256, 64 * 1024, AT25_BLOCK_ERASE_64K},
    {"M25P32"     , 0x00162020, 4 * 1024 * 1024, 256, 64 * 1024, AT25_BLOCK_ERASE_64K},
    {"M25P64"     , 0x00172020, 8 * 1024 * 1024, 256, 64 * 1024, AT25_BLOCK_ERASE_64K},
    /* Manufacturer: Windbond */
    {"W25X10"     , 0x001130EF,      128 * 1024, 256,  4 * 1024, AT25_BLOCK_ERASE_4K},
    {"W25X20"     , 0x001230EF,      256 * 1024, 256,  4 * 1024, AT25_BLOCK_ERASE_4K},
    {"W25X40"     , 0x001330EF,      512 * 1024, 256,  4 * 1024, AT25_BLOCK_ERASE_4K},
    {"W25X80"     , 0x001430EF, 1 * 1024 * 1024, 256,  4 * 1024, AT25_BLOCK_ERASE_4K},
    /* Manufacturer: Macronix */
    {"MX25L512"   , 0x001020C2,       64 * 1024, 256,  4 * 1024, AT25_BLOCK_ERASE_4K},
    {"MX25L3205"  , 0x001620C2, 4 * 1024 * 1024, 256, 64 * 1024, AT25_BLOCK_ERASE_64K},
    {"MX25L6405"  , 0x001720C2, 8 * 1024 * 1024, 256,  4 * 1024, AT25_BLOCK_ERASE_4K},
    {"MX25L8005"  , 0x001420C2,     1024 * 1024, 256,  4 * 1024, AT25_BLOCK_ERASE_4K},
    /* Other */
    {"SST25VF040" , 0x008D25BF,      512 * 1024, 256,  4 * 1024, AT25_BLOCK_ERASE_4K},
    {"SST25VF080" , 0x008E25BF, 1 * 1024 * 1024, 256,  4 * 1024, AT25_BLOCK_ERASE_4K},
    {"SST25VF032" , 0x004A25BF, 4 * 1024 * 1024, 256,  4 * 1024, AT25_BLOCK_ERASE_4K},
    {"SST25VF064" , 0x004B25BF, 8 * 1024 * 1024, 256,  4 * 1024, AT25_BLOCK_ERASE_4K}
};

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

/**
 * \brief Initializes an AT25 driver instance with the given SPI driver and chip
 * select value.
 *
 * \param pAt25  Pointer to an AT25 driver instance.
 * \param pSpid  Pointer to an SPI driver instance.
 * \param cs  Chip select value to communicate with the serial flash.
 */
void AT25_Configure(At25 *pAt25, Spid *pSpid, unsigned char cs)
{
    SpidCmd *pCommand;

    assert(pAt25);
    assert(pSpid);
    assert(cs < 4);

    /* Configure the SPI chip select for the serial flash */
    SPID_ConfigureCS(pSpid, cs, CSR);

    /* Initialize the AT25 fields */
    pAt25->pSpid = pSpid;
    pAt25->pDesc = 0;

    /* Initialize the command structure */
    pCommand = &(pAt25->command);
    pCommand->pCmd = (unsigned char *) pAt25->pCmdBuffer;
    pCommand->callback = 0;
    pCommand->pArgument = 0;
    pCommand->spiCs = cs;
}

/**
 * \brief Is serial flash driver busy.
 *
 * \param pAt25  Pointer to an At25 driver instance.
 *
 * \return 1 if the serial flash driver is currently busy executing a command;
 * otherwise returns 0.
 */
unsigned char AT25_IsBusy(At25 *pAt25)
{
    return SPID_IsBusy(pAt25->pSpid);
}

/**
 * \brief Sends a command to the serial flash through the SPI. The command is made up
 * of two parts: the first is used to transmit the command byte and optionally,
 * address and dummy bytes. The second part is the data to send or receive.
 * This function does not block: it returns as soon as the transfer has been
 * started. An optional callback can be invoked to notify the end of transfer.
 *
 * \param pAt25  Pointer to an At25 driver instance.
 * \param cmd  Command byte.
 * \param cmdSize  Size of command (command byte + address bytes + dummy bytes).
 * \param pData Data buffer.
 * \param dataSize  Number of bytes to send/receive.
 * \param address  Address to transmit.
 * \param callback  Optional user-provided callback to invoke at end of transfer.
 * \param pArgument  Optional argument to the callback function.
 *
 * \return 0 if successful; otherwise, returns AT25_ERROR_BUSY if the AT25
 * driver is currently executing a command, or AT25_ERROR_SPI if the command
 * cannot be sent because of a SPI error.
 */
unsigned char AT25_SendCommand(
    At25 *pAt25,
    unsigned char cmd,
    unsigned char cmdSize,
    unsigned char *pData,
    unsigned int dataSize,
    unsigned int address,
    SpidCallback callback,
    void *pArgument)

{
    SpidCmd *pCommand;

    assert(pAt25);

    /* Check if the SPI driver is available */
    if (AT25_IsBusy(pAt25)) {

        return AT25_ERROR_BUSY;
    }

    /* Store command and address in command buffer */
    pAt25->pCmdBuffer[0] = (cmd & 0x000000FF)
                           | ((address & 0x0000FF) << 24)
                           | ((address & 0x00FF00) << 8)
                           | ((address & 0xFF0000) >> 8);

    /* Update the SPI transfer descriptor */
    pCommand = &(pAt25->command);
    pCommand->cmdSize = cmdSize;
    pCommand->pData = pData;
    pCommand->dataSize = dataSize;
    pCommand->callback = callback;
    pCommand->pArgument = pArgument;

    /* Start the SPI transfer */
    if (SPID_SendCommand(pAt25->pSpid, pCommand)) {

        return AT25_ERROR_SPI;
    }
    return 0;
}

/**
 * \brief Tries to detect a serial firmware flash device given its JEDEC identifier.
 * The JEDEC id can be retrieved by sending the correct command to the device.
 *
 * \param pAt25  Pointer to an AT25 driver instance.
 * \param jedecId  JEDEC identifier of device.
 *
 * \return the corresponding AT25 descriptor if found; otherwise returns 0.
 */
const At25Desc * AT25_FindDevice(At25 *pAt25, unsigned int jedecId)
{
    unsigned int i = 0;

    assert(pAt25);

    /* Search if device is recognized */
    pAt25->pDesc = 0;
    while ((i < NUMDATAFLASH) && !(pAt25->pDesc)) {

        if ((jedecId & 0xFF00FFFF) == (at25Devices[i].jedecId & 0xFF00FFFF)) {

            pAt25->pDesc = &(at25Devices[i]);
        }

        i++;
    }

    return pAt25->pDesc;
}
