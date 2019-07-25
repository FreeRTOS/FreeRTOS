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
 * \addtogroup external_component External Component
 *
 * \addtogroup at25d_module AT25 driver
 * \ingroup external_component
 * The AT25 serial dataflash driver is based on the corresponding AT25 SPI driver.
 * A AT25 instance has to be initialized using the Dataflash levle function
 * AT25_Configure(). AT25 Dataflash can be automatically detected using
 * the AT25_FindDevice() function. Then AT25 dataflash operations such as
 * read, write and erase DF can be launched using AT25_SendCommand function
 * with corresponding AT25 command set.
 *
 * \section Usage
 * <ul>
 * <li> Reads a serial flash device ID using AT25D_ReadJedecId().</li>
 * <li> Reads data from the At25 at the specified address using AT25D_Read().</li>
 * <li> Writes data on the At25 at the specified address using AT25D_Write().</li>
 * <li> Erases all chip using AT25D_EraseBlock().</li>
 * <li> Erases a specified block using AT25D_EraseBlock().</li>
 * <li> Poll until the At25 has completed of corresponding operations using
 * AT25D_WaitReady().</li>
 * <li> Retrieves and returns the At25 current using AT25D_ReadStatus().</li>
 * </ul>
 *
 * Related files :\n
 * \ref at25d.c\n
 * \ref at25d.h.\n
 */
/*@{*/
/*@}*/

/**
 * \file
 *
 * Implementation for the AT25 Serialflash driver.
 *
 */

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include <board.h>

#include <assert.h>

/*----------------------------------------------------------------------------
 *        Local functions
 *----------------------------------------------------------------------------*/

/**
 * \brief Wait for transfer to finish calling the SPI driver ISR. (interrupts are disabled)
 *
 * \param pAt25  Pointer to an AT25 driver instance.
 */
static void AT25D_Wait(At25 *pAt25)
{
    /* Wait for transfer to finish */
    while (AT25_IsBusy(pAt25))
        SPID_Handler(pAt25->pSpid);
}

/**
 * \brief Reads and returns the status register of the serial flash.
 *
 * \param pAt25  Pointer to an AT25 driver instance.
 */
static unsigned char AT25D_ReadStatus(At25 *pAt25)
{
    unsigned char error, status;

    assert(pAt25);

    /* Issue a status read command */
    error = AT25_SendCommand(pAt25, AT25_READ_STATUS, 1, &status, 1, 0, 0, 0);
    assert(!error);

    /* Wait for transfer to finish */
    AT25D_Wait(pAt25);

    return status;
}

/**
 * \brief Writes the given value in the status register of the serial flash device.
 *
 * \param pAt25  Pointer to an AT25 driver instance.
 * \param status  Status to write.
 */
static void AT25D_WriteStatus(At25 *pAt25, unsigned char status)
{
    unsigned char error;

    assert(pAt25);

    /* Issue a write status command */
    error = AT25_SendCommand(pAt25, AT25_WRITE_STATUS, 1, &status, 1, 0, 0, 0);
    assert(!error);

    /* Wait for transfer to finish */
    AT25D_Wait(pAt25);
}

/*----------------------------------------------------------------------------
 *         Global functions
 *----------------------------------------------------------------------------*/

/**
 * \brief  Waits for the serial flash device to become ready to accept new commands.
 *
 * \param pAt25  Pointer to an AT25 driver instance.
 */
void AT25D_WaitReady(At25 *pAt25)
{
    unsigned char ready = 0;

    assert(pAt25);

    /* Read status register and check busy bit */
    while (!ready) {

        ready = ((AT25D_ReadStatus(pAt25) & AT25_STATUS_RDYBSY) == AT25_STATUS_RDYBSY_READY);
    }
}

/**
 * \brief Reads and returns the serial flash device ID.
 *
 * \param pAt25  Pointer to an AT25 driver instance.
 */
unsigned int AT25D_ReadJedecId(At25 *pAt25)
{
    unsigned char error;
    unsigned int id = 0;

    assert(pAt25);

    /* Issue a read ID command */
    error = AT25_SendCommand(pAt25, AT25_READ_JEDEC_ID, 1,
                             (unsigned char *) &id, 3, 0, 0, 0);
    assert(!error);

    /* Wait for transfer to finish */
    AT25D_Wait(pAt25);

    return id;
}

/**
 * \brief Enables critical writes operation on a serial flash device, such as sector
 * protection, status register, etc.
 *
 * \para pAt25  Pointer to an AT25 driver instance.
 */
void AT25D_EnableWrite(At25 *pAt25)
{
    unsigned char error;

    assert(pAt25);

    /* Issue a write enable command */
    error = AT25_SendCommand(pAt25, AT25_WRITE_ENABLE, 1, 0, 0, 0, 0, 0);
    assert(!error);

    /* Wait for transfer to finish */
    AT25D_Wait(pAt25);
}

/**
 * \brief Disables write operation on a serial flash device.
 *
 * \para pAt25  Pointer to an AT25 driver instance.
 */
void AT25D_DisableWrite(At25 *pAt25)
{
    unsigned char error;

    assert(pAt25);

    /* Issue a write enable command */
    error = AT25_SendCommand(pAt25, AT25_WRITE_DISABLE, 1, 0, 0, 0, 0, 0);
    assert(!error);

    /* Wait for transfer to finish */
    AT25D_Wait(pAt25);
}

/**
 * \brief Unprotects the contents of the serial flash device.
 *
 * \param pAt25  Pointer to an AT25 driver instance.
 *
 * \return 0 if the device has been unprotected; otherwise returns
 * AT25_ERROR_PROTECTED.
 */
unsigned char AT25D_Unprotect(At25 *pAt25)
{
    unsigned char status;

    assert(pAt25);

    /* Get the status register value to check the current protection */
    status = AT25D_ReadStatus(pAt25);
    if ((status & AT25_STATUS_SWP) == AT25_STATUS_SWP_PROTNONE) {

        /* Protection already disabled */
        return 0;
    }

    /* Check if sector protection registers are locked */
    if ((status & AT25_STATUS_SPRL) == AT25_STATUS_SPRL_LOCKED) {

        /* Unprotect sector protection registers by writing the status reg. */
        AT25D_EnableWrite(pAt25);
        AT25D_WriteStatus(pAt25, 0);
    }

    /* Perform a global unprotect command */
    AT25D_EnableWrite(pAt25);

    AT25D_WriteStatus(pAt25, 0);

    /* Check the new status */
    status = AT25D_ReadStatus(pAt25);
    if ((status & (AT25_STATUS_SPRL | AT25_STATUS_SWP)) != 0) {

        return AT25_ERROR_PROTECTED;
    }
    else {

        return 0;
    }
}

/**
 * \brief Erases all the content of the memory chip.
 *
 * \param pAt25  Pointer to an AT25 driver instance.
 *
 * \return 0 if the device has been unprotected; otherwise returns
 * AT25_ERROR_PROTECTED.
 */
unsigned char AT25D_EraseChip(At25 *pAt25)
{
    unsigned char status;
    unsigned char error;

    assert(pAt25);

    /* Check that the flash is unprotected */
    status = AT25D_ReadStatus(pAt25);
    if ((status & AT25_STATUS_SWP) != AT25_STATUS_SWP_PROTNONE) {
        return AT25_ERROR_PROTECTED;
    }

    /* Enable critical write operation */
      AT25D_EnableWrite(pAt25);

    /* Erase the chip */
    error = AT25_SendCommand(pAt25, AT25_CHIP_ERASE_2, 1, 0, 0, 0, 0, 0);
    assert(!error);

    /* Wait for transfer to finish */
    AT25D_Wait(pAt25);
    /* Poll the Serial flash status register until the operation is achieved */
    AT25D_WaitReady(pAt25);

    return 0;
}

/**
 *\brief  Erases the specified block of the serial firmware dataflash.
 *
 * \param pAt25  Pointer to an AT25 driver instance.
 * \param address  Address of the block to erase.
 *
 * \return 0 if successful; otherwise returns AT25_ERROR_PROTECTED if the
 * device is protected or AT25_ERROR_BUSY if it is busy executing a command.
 */
unsigned char AT25D_EraseBlock(At25 *pAt25, unsigned int address)
{
    unsigned char status;
    unsigned char error;

    assert(pAt25);

    /* Check that the flash is ready and unprotected */
    status = AT25D_ReadStatus(pAt25);
    if ((status & AT25_STATUS_RDYBSY) != AT25_STATUS_RDYBSY_READY) {
        TRACE_ERROR("AT25D_EraseBlock : Flash busy\n\r");
        return AT25_ERROR_BUSY;
    }
    else if ((status & AT25_STATUS_SWP) != AT25_STATUS_SWP_PROTNONE) {
        TRACE_ERROR("AT25D_EraseBlock : Flash protected\n\r");
        return AT25_ERROR_PROTECTED;
    }

    /* Enable critical write operation */
      AT25D_EnableWrite(pAt25);

    /* Start the block erase command */
    error = AT25_SendCommand(pAt25, AT25_BlockEraseCmd(pAt25), 4, 0, 0, address, 0, 0);
    assert(!error);

    /* Wait for transfer to finish */
    AT25D_Wait(pAt25);
    /* Poll the Serial flash status register until the operation is achieved */
    AT25D_WaitReady(pAt25);

    return 0;
}


/**
 *\brief  Erases the specified 64KB block of the serial firmware dataflash.
 *
 * \param pAt25  Pointer to an AT25 driver instance.
 * \param address  Address of the block to erase.
 *
 * \return 0 if successful; otherwise returns AT25_ERROR_PROTECTED if the
 * device is protected or AT25_ERROR_BUSY if it is busy executing a command.
 */
unsigned char AT25D_Erase64KBlock(At25 *pAt25, unsigned int address)
{
    unsigned char status;
    unsigned char error;

    assert(pAt25);

    /* Check that the flash is ready and unprotected */
    status = AT25D_ReadStatus(pAt25);
    if ((status & AT25_STATUS_RDYBSY) != AT25_STATUS_RDYBSY_READY) {
        TRACE_ERROR("AT25D_EraseBlock : Flash busy\n\r");
        return AT25_ERROR_BUSY;
    }
    else if ((status & AT25_STATUS_SWP) != AT25_STATUS_SWP_PROTNONE) {
        TRACE_ERROR("AT25D_EraseBlock : Flash protected\n\r");
        return AT25_ERROR_PROTECTED;
    }

    /* Enable critical write operation */
      AT25D_EnableWrite(pAt25);

    /* Start the block erase command */
    error = AT25_SendCommand(pAt25, AT25_BLOCK_ERASE_64K, 4, 0, 0, address, 0, 0);
    assert(!error);

    /* Wait for transfer to finish */
    AT25D_Wait(pAt25);
    /* Poll the Serial flash status register until the operation is achieved */
    AT25D_WaitReady(pAt25);

    return 0;
}


/**
 * \brief Writes data at the specified address on the serial firmware dataflash. The
 * page(s) to program must have been erased prior to writing. This function
 * handles page boundary crossing automatically.
 *
 * \param pAt25  Pointer to an AT25 driver instance.
 * \param pData  Data buffer.
 * \param size  Number of bytes in buffer.
 * \param address  Write address.
 *
 * \return 0 if successful; otherwise, returns AT25_ERROR_PROGRAM is there has
 * been an error during the data programming.
 */
unsigned char AT25D_Write(
    At25 *pAt25,
    unsigned char *pData,
    unsigned int size,
    unsigned int address)
{
    unsigned int pageSize;
    unsigned int writeSize;
    unsigned char error;
    unsigned char status;
    unsigned int i = 0;

    assert(pAt25);
    assert(pData);

    /* Retrieve device page size */
    pageSize = AT25_PageSize(pAt25);

    /* Program one page after the other */
    while (size > 0) {
        /* Compute number of bytes to program in page */
        writeSize = min(size, pageSize - (address % pageSize));

        /* Enable critical write operation */
        AT25D_EnableWrite(pAt25);

        /* Program page */
        if (AT25_ManId(pAt25) == SST_SPI_FLASH) {

            error = AT25_SendCommand(pAt25, AT25_SEQUENTIAL_PROGRAM_1, 4,
                               pData, 2, address, 0, 0);
            
            assert(!error);
    
            /* Wait for transfer to finish */
            AT25D_Wait(pAt25);
            /* Poll the Serial flash status register until the operation is achieved */
            AT25D_WaitReady(pAt25);

            for (i = 2; i < pageSize; i += 2) {
                error = AT25_SendCommand(pAt25, AT25_SEQUENTIAL_PROGRAM_1, 1,
                                   pData + i, 2, 0, 0, 0);

                assert(!error);
        
                /* Wait for transfer to finish */
                AT25D_Wait(pAt25);
                /* Poll the Serial flash status register until the operation is achieved */
                AT25D_WaitReady(pAt25);
            }
        
        }
        else {
        error = AT25_SendCommand(pAt25, AT25_BYTE_PAGE_PROGRAM, 4,
                           pData, writeSize, address, 0, 0);

        assert(!error);

        /* Wait for transfer to finish */
        AT25D_Wait(pAt25);
        /* Poll the Serial flash status register until the operation is achieved */
        AT25D_WaitReady(pAt25);

        }
        
        /* Make sure that write was without error */
        status = AT25D_ReadStatus(pAt25);
        if ((status & AT25_STATUS_EPE) == AT25_STATUS_EPE_ERROR) {

            return AT25_ERROR_PROGRAM;
        }

        pData += writeSize;
        size -= writeSize;
        address += writeSize;
    }

    /* Enable critical write operation */
    AT25D_DisableWrite(pAt25);

    return 0;
}

/**
 * \brief Reads data from the specified address on the serial flash.
 *
 * \param pAt25  Pointer to an AT25 driver instance.
 * \param pData  Data buffer.
 * \param size  Number of bytes to read.
 * \param address  Read address.
 *
 * \return 0 if successful; otherwise, fail.
 */
unsigned char AT25D_Read(
    At25 *pAt25,
    unsigned char *pData,
    unsigned int size,
    unsigned int address)
{
    unsigned char error;

    /* Start a read operation */
    error = AT25_SendCommand(pAt25, AT25_READ_ARRAY_LF, 4, pData, size, address, 0, 0);
    assert(!error);

    /* Wait for transfer to finish */
    AT25D_Wait(pAt25);

    return error;
}

