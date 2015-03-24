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
 * \addtogroup at25d_module S25FL1 driver
 * \ingroup lib_spiflash
 * The S25FL1 serial dataflash driver is based on the corresponding S25FL1 SPI driver.
 * A S25FL1 instance has to be initialized using the Dataflash levle function
 * S25FL1D_Configure(). S25FL1 Dataflash can be automatically detected using
 * the S25FL1D_FindDevice() function. Then S25FL1 dataflash operations such as
 * read, write and erase DF can be launched using S25FL1D_SendCommand function
 * with corresponding S25FL1 command set.
 *
 * \section Usage
 * <ul>
 * <li> Reads a serial flash device ID using S25FL1D_ReadJedecId().</li>
 * <li> Reads data from the S25fl1 at the specified address using S25FL1D_Read().</li>
 * <li> Writes data on the S25fl1 at the specified address using S25FL1D_Write().</li>
 * <li> Erases all chip using S25FL1D_EraseBlock().</li>
 * <li> Erases a specified block using S25FL1D_EraseBlock().</li>
 * <li> Poll until the S25fl1 has completed of corresponding operations using
 * S25FL1D_IsBusy().</li>
 * <li> Retrieves and returns the S25fl1 current using S25FL1D_ReadStatus().</li>
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
 * Implementation for the S25FL1 Serialflash driver.
 *
 */

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include <board.h>
//#include <libspiflash.h>
#include <assert.h>
#include "stdlib.h"
#include "string.h"


static qspiFrame *pDev, *pMem;
#define READ_DEV        0
#define WRITE_DEV       1 
/*----------------------------------------------------------------------------
 *        Local functions
 *----------------------------------------------------------------------------*/



static void S25FL1D_DefaultParams(void)
{      
    pDev->spiMode = QSPI_IFR_WIDTH_SINGLE_BIT_SPI;
    pDev->ContinuousRead = 0;
    pDev->DataSize = 0;
    pDev->DummyCycles = 0;
    pDev->InstAddr = 0;
    pDev->InstAddrFlag = 0;
    pDev->OptionEn = 0;

}


static uint8_t S25FL1D_SendCommand(uint8_t Instr, AccesType ReadWrite)

{  
    pDev->Instruction = Instr;
    QSPI_SendFrame(QSPI, pDev, ReadWrite);

    return 0;
}


/**
 * \brief Reads and returns the status register of the serial flash.
 *
 * \param pS25fl1  Pointer to an S25FL1 driver instance.
 */
static uint8_t S25FL1D_ReadStatus(void)
{
    uint8_t status;

    pDev->DataSize = 1;    
    S25FL1D_SendCommand(0x05, READ_DEV);
    status = *(pDev->pData);
    return status;
}

/**
 * \brief Reads and returns the status register of the serial flash.
 *
 * \param pS25fl1  Pointer to an S25FL1 driver instance.
 */
static uint8_t S25FL1D_ReadStatus2(void)
{
    uint8_t status;

    pDev->DataSize = 1;
    S25FL1D_SendCommand(0x35, READ_DEV);
    status = *(pDev->pData);
    return status;
}

/**
 * \brief Reads and returns the status register of the serial flash.
 *
 * \param pS25fl1  Pointer to an S25FL1 driver instance.
 */
static uint8_t S25FL1D_ReadStatus3(void)
{
    uint8_t status;

    pDev->DataSize = 1;
    S25FL1D_SendCommand(0x33, READ_DEV);
    status = *(pDev->pData);
    return status;
}
/**
 * \brief Wait for transfer to finish calling the SPI driver ISR. (interrupts are disabled)
 *
 * \param pS25fl1  Pointer to an S25FL1 driver instance.
 */
static void S25FL1D_IsBusy(void)
{
    while(S25FL1D_ReadStatus() & STATUS_RDYBSY);
}





static void S25FL1D_EnableWrite(void)
{
    uint8_t status;

    status = S25FL1D_ReadStatus();


    while(status != STATUS_WEL)
    {      
        pDev->DataSize = 0;
        S25FL1D_SendCommand(WRITE_ENABLE, READ_DEV);
        status = S25FL1D_ReadStatus();
    }
}


static void S25FL1D_DisableWrite(void)
{
    uint8_t status;

    status = S25FL1D_ReadStatus();

    while( (status & STATUS_WEL) != 0)
    {      
        pDev->DataSize = 0;
        S25FL1D_SendCommand(WRITE_DISABLE, READ_DEV);
        status = S25FL1D_ReadStatus();
    }
}
/**
 * \brief Writes the given value in the status register of the serial flash device.
 *
 * \param pS25fl1  Pointer to an S25FL1 driver instance.
 * \param status  Status to write.
 */
static void S25FL1D_WriteStatus( uint8_t *pStatus)
{
    S25FL1D_EnableWrite();

    pDev->DataSize = 3;
    pDev->Instruction = WRITE_STATUS; 
    pDev->pData = pStatus;
    QSPI_SendFrame(QSPI, pDev, Device_Write);
    S25FL1D_DisableWrite();
}

/**
 * \brief Writes the given value in the status register of the serial flash device.
 *
 * \param pS25fl1  Pointer to an S25FL1 driver instance.
 * \param status  Status to write.
 */
static void S25FL1D_WriteVolatileStatus( uint8_t *pStatus)
{


    pDev->DataSize = 0;
    S25FL1D_SendCommand(0x50, READ_DEV);

    pDev->DataSize = 3;
    pDev->Instruction = WRITE_STATUS; 
    pDev->pData = pStatus;
    QSPI_SendFrame(QSPI, pDev, Device_Write);
    S25FL1D_DisableWrite();
}
/*----------------------------------------------------------------------------
 *         Global functions
 *----------------------------------------------------------------------------*/


void S25FL1D_InitFlashInterface(void)
{
    pDev = (qspiFrame *)malloc (sizeof(qspiFrame));  
    memset(pDev, 0, sizeof(qspiFrame));
    pDev->spiMode = QSPI_IFR_WIDTH_SINGLE_BIT_SPI;
    pDev->pData = (uint8_t *)malloc (sizeof(uint32_t));


    pMem = (qspiFrame *)malloc (sizeof(qspiFrame));
    memset(pMem, 0, sizeof(qspiFrame));
    pMem->spiMode = QSPI_IFR_WIDTH_SINGLE_BIT_SPI;
    pMem->pData = (uint8_t *)malloc (sizeof(uint8_t));
}

/**
 * \brief Reads and returns the serial flash device ID.
 *
 * \param pS25fl1  Pointer to an S25FL1 driver instance.
 */
unsigned int S25FL1D_ReadJedecId(void)
{
    unsigned int id = 0;

    pDev->DataSize = 3;
    S25FL1D_SendCommand(READ_JEDEC_ID, READ_DEV);

    id = ( (pDev->pData[0] << 16)  || (pDev->pData[1] << 8) || (pDev->pData[2]));

    return id;
}

/**
 * \brief Enables critical writes operation on a serial flash device, such as sector
 * protection, status register, etc.
 *
 * \para pS25fl1  Pointer to an S25FL1 driver instance.
 */
void S25FL1D_EnableQuadMode(void)
{

    uint8_t status[3];

    status[0] = S25FL1D_ReadStatus();
    status[1] = S25FL1D_ReadStatus2();
    status[2] = S25FL1D_ReadStatus3();

    while(!(status[1] & STATUS_QUAD_ENABLE))
    {
        status[1] |= STATUS_QUAD_ENABLE;
        S25FL1D_WriteStatus(status);
        status[1] = S25FL1D_ReadStatus2();
        Wait(50);
    }
}


/**
 * \brief Enables critical writes operation on a serial flash device, such as sector
 * protection, status register, etc.
 *
 * \para pS25fl1  Pointer to an S25FL1 driver instance.
 */
void S25FL1D_EnableWrap(uint8_t ByetAlign)
{

    uint8_t status[3];

    status[0] = S25FL1D_ReadStatus();
    status[1] = S25FL1D_ReadStatus2();
    status[2] = S25FL1D_ReadStatus3();

    status[2] = (ByetAlign << 5);

    pDev->DataSize = 1;
    *(pDev->pData) = status[2];
    pDev->DummyCycles = 24;
    S25FL1D_SendCommand(WRAP_ENABLE, WRITE_DEV);
    pDev->DummyCycles = 0;

    S25FL1D_WriteVolatileStatus(status);
    status[2] = S25FL1D_ReadStatus3();
    Wait(50);
}

void S25FL1D_SoftReset(void)
{

    pDev->DataSize = 0;
    S25FL1D_SendCommand(SOFT_RESET_ENABLE, READ_DEV);
    S25FL1D_SendCommand(SOFT_RESET, READ_DEV);

}

/**
 * \brief Unprotects the contents of the serial flash device.
 *
 * \param pS25fl1  Pointer to an S25FL1 driver instance.
 *
 * \return 0 if the device has been unprotected; otherwise returns
 * S25FL1D_ERROR_PROTECTED.
 */
unsigned char S25FL1D_Unprotect(void)
{
    unsigned char status[3];



    /* Get the status register value to check the current protection */
    status[0]= S25FL1D_ReadStatus();
    status[1]= S25FL1D_ReadStatus2();
    status[2]= S25FL1D_ReadStatus3();
    if ((status[0] & STATUS_SWP) == STATUS_SWP_PROTNONE) {

        /* Protection already disabled */
        return 0;
    }

    status[0] &= (!STATUS_SWP);
    /* Check if sector protection registers are locked */
    if ((status[0] & STATUS_SPRL) == STATUS_SPRL_LOCKED) {
        status[0] &= (!STATUS_SPRL);
        /* Unprotect sector protection registers by writing the status reg. */
        S25FL1D_WriteStatus(status);
    }

    S25FL1D_WriteStatus(status);

    /* Check the new status */
    status[0] = S25FL1D_ReadStatus();
    if ((status[0] & (STATUS_SPRL | STATUS_SWP)) != 0) {

        return ERROR_PROTECTED;
    }
    else {

        return 0;
    }
}


/**
 * \brief Unprotects the contents of the serial flash device.
 *
 * \param pS25fl1  Pointer to an S25FL1 driver instance.
 *
 * \return 0 if the device has been unprotected; otherwise returns
 * S25FL1D_ERROR_PROTECTED.
 */
unsigned char S25FL1D_Protect(uint32_t StartAddr, uint32_t Size)
{
    unsigned char status[3];



    /* Get the status register value to check the current protection */
    status[0]= S25FL1D_ReadStatus();
    status[1]= S25FL1D_ReadStatus2();
    status[2]= S25FL1D_ReadStatus3();

    status[0] &= (!STATUS_SWP);
    /* Check if sector protection registers are locked */
    if ((status[0] & STATUS_SPRL) == STATUS_SPRL_LOCKED) {
        status[0] &= (!STATUS_SPRL);
        /* Unprotect sector protection registers by writing the status reg. */
        S25FL1D_WriteStatus(status);
    }

    S25FL1D_WriteStatus(status);

    /* Check the new status */
    status[0] = S25FL1D_ReadStatus();
    if ((status[0] & (STATUS_SPRL | STATUS_SWP)) != 0) {

        return ERROR_PROTECTED;
    }
    else {

        return 0;
    }
}


/**
 * \brief Erases all the content of the memory chip.
 *
 * \param pS25fl1  Pointer to an S25FL1 driver instance.
 *
 * \return 0 if the device has been unprotected; otherwise returns
 * ERROR_PROTECTED.
 */
unsigned char S25FL1D_EraseChip(void)
{
    char wait_ch[4] = {'\\','|','/','-' };
    uint8_t i=0;

    S25FL1D_EnableWrite();   
    pDev->DataSize=0;
    S25FL1D_SendCommand(CHIP_ERASE_2, READ_DEV);
    S25FL1D_ReadStatus();

    while(*(pDev->pData) & STATUS_RDYBSY)
    {
        S25FL1D_ReadStatus();      
        Wait(500);
        printf("Erasing flash memory %c\r", wait_ch[i]);
        i++;
        if(i==4)
            i=0;
    }
    printf("\rErasing flash memory done..... 100%\n\r");
    return 0;
}

/**
 *\brief  Erases the specified block of the serial firmware dataflash.
 *
 * \param pS25fl1  Pointer to an S25FL1 driver instance.
 * \param address  Address of the block to erase.
 *
 * \return 0 if successful; otherwise returns ERROR_PROTECTED if the
 * device is protected or ERROR_BUSY if it is busy executing a command.
 */
unsigned char S25FL1D_EraseSector(unsigned int address)
{
    uint8_t status;
    uint32_t EraseAddr;

    EraseAddr = address;

    /* Check that the flash is ready and unprotected */
    status = S25FL1D_ReadStatus();
    if ((status & STATUS_RDYBSY) != STATUS_RDYBSY_READY) {
        TRACE_ERROR("EraseBlock : Flash busy\n\r");
        return ERROR_BUSY;
    }
    else if ((status & STATUS_SWP) != STATUS_SWP_PROTNONE) {
        TRACE_ERROR("S25FL1D_EraseBlock : Flash protected\n\r");
        return ERROR_PROTECTED;
    }


    /* Enable critical write operation */
    S25FL1D_EnableWrite();

    pDev->InstAddrFlag = 1;
    pDev->InstAddr = address;
    /* Start the block erase command */
    S25FL1D_SendCommand(BLOCK_ERASE_4K, WRITE_DEV);
    S25FL1D_DefaultParams();

    /* Wait for transfer to finish */
    S25FL1D_IsBusy();


    return 0;
}

/**
 *\brief  Erases the specified 64KB block of the serial firmware dataflash.
 *
 * \param pS25fl1  Pointer to an S25FL1 driver instance.
 * \param address  Address of the block to erase.
 *
 * \return 0 if successful; otherwise returns ERROR_PROTECTED if the
 * device is protected or ERROR_BUSY if it is busy executing a command.
 */
unsigned char S25FL1D_Erase64KBlock( unsigned int address)
{
    unsigned char status;

    /* Check that the flash is ready and unprotected */
    status = S25FL1D_ReadStatus();
    if ((status & STATUS_RDYBSY) != STATUS_RDYBSY_READY) {
        TRACE_ERROR("S25FL1D_EraseBlock : Flash busy\n\r");
        return ERROR_BUSY;
    }
    else if ((status & STATUS_SWP) != STATUS_SWP_PROTNONE) {
        TRACE_ERROR("EraseBlock : Flash protected\n\r");
        return ERROR_PROTECTED;
    }

    /* Enable critical write operation */
    S25FL1D_EnableWrite();

    pDev->DataSize = 0;
    pDev->InstAddrFlag = 1;
    pDev->InstAddr = address;

    /* Start the block erase command */
    S25FL1D_SendCommand(BLOCK_ERASE_64K, WRITE_DEV);
    S25FL1D_DefaultParams();

    /* Wait for transfer to finish */
    S25FL1D_IsBusy();


    return 0;
}

/**
 * \brief Writes data at the specified address on the serial firmware dataflash. The
 * page(s) to program must have been erased prior to writing. This function
 * handles page boundary crossing automatically.
 *
 * \param pS25fl1  Pointer to an S25FL1 driver instance.
 * \param pData  Data buffer.
 * \param size  Number of bytes in buffer.
 * \param address  Write address.
 *
 * \return 0 if successful; otherwise, returns ERROR_PROGRAM is there has
 * been an error during the data programming.
 */
unsigned char S25FL1D_Write(
        uint8_t *pData,
        uint32_t size,
        uint32_t address)
{
    unsigned int pageSize = 256;
    unsigned int writeSize;
    unsigned int i = 0;


    writeSize = size >> 8;
    S25FL1D_EnableWrite();
    pMem->Instruction = 0x02; 
    pMem->InstAddrFlag=1; pMem->InstAddr=address;  
    if(writeSize ==0)   // if less than page size
    {
        pMem->pData = (pData);
        pMem->DataSize = size;
        QSPI_SendFrameToMem(QSPI, pMem, Device_Write);
    }
    else                // mulptiple pagesize
    {     
        pMem->DataSize = pageSize;
        for(i=0; i< writeSize; i++)
        {
            S25FL1D_EnableWrite();
            pMem->pData = pData;        
            QSPI_SendFrameToMem(QSPI, pMem, Device_Write);
            S25FL1D_IsBusy();
            pData += pageSize;
            pMem->InstAddr += pageSize;
            memory_barrier();
        }
        if((writeSize * pageSize) < size)
        {
            S25FL1D_EnableWrite();
            pMem->DataSize = (size - (writeSize * pageSize)) ;
            pMem->pData = pData;        
            QSPI_SendFrameToMem(QSPI, pMem, Device_Write);
            S25FL1D_IsBusy();
        }
    }

    S25FL1D_DisableWrite();


    return 0;
}

/**
 * \brief Reads data from the specified address on the serial flash.
 *
 * \param pS25fl1  Pointer to an S25FL1 driver instance.
 * \param pData  Data buffer.
 * \param size  Number of bytes to read.
 * \param address  Read address.
 *
 * \return 0 if successful; otherwise, fail.
 */
unsigned char S25FL1D_Read(
        uint8_t *pData,
        uint32_t size,
        uint32_t address)
{    
    pMem->Instruction = READ_ARRAY_LF;
    pMem->InstAddrFlag=1; pMem->InstAddr=address;
    pMem->pData = pData;
    pMem->DataSize = size;
    pMem->DummyCycles = 0;
    pMem->spiMode = QSPI_IFR_WIDTH_SINGLE_BIT_SPI;
    QSPI_SendFrameToMem(QSPI, pMem, Device_Read);

    return 0;
}


/**
 * \brief Reads data from the specified address on the serial flash.
 *
 * \param pS25fl1  Pointer to an S25FL1 driver instance.
 * \param pData  Data buffer.
 * \param size  Number of bytes to read.
 * \param address  Read address.
 *
 * \return 0 if successful; otherwise, fail.
 */
unsigned char S25FL1D_ReadDual(
        uint8_t *pData,
        uint32_t size,
        uint32_t address)
{
    pMem->Instruction = READ_ARRAY_DUAL;
    pMem->InstAddrFlag=1; pMem->InstAddr=address;
    pMem->pData = pData;
    pMem->DataSize = size;
    pMem->DummyCycles = 8;
    pMem->spiMode = QSPI_IFR_WIDTH_DUAL_OUTPUT;
    QSPI_SendFrameToMem(QSPI, pMem, Device_Read);


    return 0;
}


/**
 * \brief Reads data from the specified address on the serial flash.
 *
 * \param pS25fl1  Pointer to an S25FL1 driver instance.
 * \param pData  Data buffer.
 * \param size  Number of bytes to read.
 * \param address  Read address.
 *
 * \return 0 if successful; otherwise, fail.
 */
unsigned char S25FL1D_ReadQuad(
        uint8_t *pData,
        uint32_t size,
        uint32_t address)
{

    pMem->Instruction = READ_ARRAY_QUAD;
    pMem->InstAddrFlag=1; pMem->InstAddr=address;
    pMem->pData = pData;
    pMem->DataSize = size;
    pMem->DummyCycles = 8;
    pMem->spiMode = QSPI_IFR_WIDTH_QUAD_OUTPUT;
    QSPI_SendFrameToMem(QSPI, pMem, Device_Read);


    return 0;
}

/**
 * \brief Reads data from the specified address on the serial flash.
 *
 * \param pS25fl1  Pointer to an S25FL1 driver instance.
 * \param pData  Data buffer.
 * \param size  Number of bytes to read.
 * \param address  Read address.
 *
 * \return 0 if successful; otherwise, fail.
 */
unsigned char S25FL1D_ReadQuadIO(
        uint8_t *pData,
        uint32_t size,
        uint32_t address,
        uint8_t ContMode)
{

    pMem->Instruction = READ_ARRAY_QUAD_IO;
    pMem->InstAddrFlag=1; 
    pMem->InstAddr=address;
    pMem->pData = pData;
    pMem->DataSize = size;    
    pMem->DummyCycles = 6;
    if(ContMode)
    {
        pMem->OptionLen = QSPI_IFR_OPTL_OPTION_4BIT;
        pMem->Option = 0x2;
        pMem->ContinuousRead = ContMode;
        pMem->DummyCycles = 5;
        pMem->OptionEn = ContMode;
    }

    pMem->spiMode = QSPI_IFR_WIDTH_QUAD_IO;
    QSPI_SendFrameToMem(QSPI, pMem, Device_Read);
    pMem->OptionEn = 0;
    pMem->ContinuousRead = 0;

    return 0;
}



