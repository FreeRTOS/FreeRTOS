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
 * The S25FL1 serial dataflash driver is based on the corresponding S25FL1 SPI
 * driver.
 * A S25FL1 instance has to be initialized using the Dataflash level function
 * S25FL1D_Configure(). S25FL1 Dataflash can be automatically detected using
 * the S25FL1D_FindDevice() function. Then S25FL1 dataflash operations such as
 * read, write and erase DF can be launched using S25FL1D_SendCommand function
 * with corresponding S25FL1 command set.
 *
 * \section Usage
 * <ul>
 * <li> Reads a serial flash device ID using S25FL1D_ReadJedecId().</li>
 * <li> Reads data from the S25fl1 at the specified address using S25FL1D_Read().
 * </li>
 * <li> Writes data on the S25fl1 at the specified address using S25FL1D_Write().
 * </li>
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
#include <assert.h>
#include "stdlib.h"
#include "string.h"


/*----------------------------------------------------------------------------
 *        Variable
 *----------------------------------------------------------------------------*/
static QspiInstFrame_t *pDev, *pMem;

static QspiDma_t qspiDma;
static sXdmad qspiDmaInst;


/*----------------------------------------------------------------------------
 *        Definition
 *----------------------------------------------------------------------------*/
#define READ_DEV        0
#define WRITE_DEV       1 

#define PAGE_SIZE       256
/**
 * \brief XDMA handler.
 */
void XDMAC_Handler(void)
{
	XDMAD_Handler(&qspiDmaInst);
}

/**
 * \brief Start S25FL1D Send command with/without data write/read.
 * \param Instr Instruct 
 * \param pTxData point to Tx buffer address
 * \param pRxData point to Rx buffer address
 * \param ReadWrite Command/Write/Read access
 * \param Size buffer size in byte
 * \returns 0
 */
static uint8_t S25FL1D_SendCommand(uint8_t Instr, uint32_t *pTxData,
		uint32_t *pRxData, Access_t ReadWrite, uint32_t size)
{
	qspiDma.Qspid.qspiCommand.Instruction = Instr;
	
	if(qspiDma.Qspid.qspiMode) {
		pDev->InstFrame.bm.bInstEn = 1;
		qspiDma.Qspid.pQspiFrame =  pDev;
		qspiDma.Qspid.qspiBuffer.pDataTx = pTxData;
		qspiDma.Qspid.qspiBuffer.pDataRx = pRxData;

		// to prevent unaligned access
		if( (size % sizeof(uint32_t)) && size > 1) {
			size += (sizeof(uint32_t) - (size % sizeof(uint32_t)));
		}

	if(ReadWrite == CmdAccess) {
		pDev->InstFrame.bm.bXfrType 
			= (QSPI_IFR_TFRTYP_TRSFR_READ >> QSPI_IFR_TFRTYP_Pos);
		pDev->InstFrame.bm.bDataEn = 0;
		
		QSPI_SendCommand(&qspiDma.Qspid, 0);
		
	} else if (ReadWrite == WriteAccess) {
		pDev->InstFrame.bm.bDataEn = 1;
		pDev->InstFrame.bm.bXfrType 
			= (QSPI_IFR_TFRTYP_TRSFR_WRITE >> QSPI_IFR_TFRTYP_Pos);
		qspiDma.Qspid.qspiBuffer.TxDataSize  = size;
		QSPI_SendCommandWithData(&qspiDma.Qspid, 0);
		
	} else {
			pDev->InstFrame.bm.bXfrType 
				= (QSPI_IFR_TFRTYP_TRSFR_READ >> QSPI_IFR_TFRTYP_Pos);
			pDev->InstFrame.bm.bDataEn = 1;
			qspiDma.Qspid.qspiBuffer.RxDataSize  = size;
			QSPI_ReadCommand(&qspiDma.Qspid, 0);
		}
	} else {
		if((ReadWrite == CmdAccess) || (ReadWrite == WriteAccess)) {
			qspiDma.Qspid.qspiBuffer.pDataTx = malloc(size+1);
			qspiDma.Qspid.qspiBuffer.pDataTx[0] 
				= qspiDma.Qspid.qspiCommand.Instruction;
			if(size) {
				memcpy(&qspiDma.Qspid.qspiBuffer.pDataTx[1], pTxData, size);
			}
			qspiDma.Qspid.qspiBuffer.TxDataSize  = size+1;

			QSPI_MultiWriteSPI(&qspiDma.Qspid, 
				(uint16_t const*)qspiDma.Qspid.qspiBuffer.pDataTx, 
				qspiDma.Qspid.qspiBuffer.TxDataSize); 

			free(qspiDma.Qspid.qspiBuffer.pDataTx);
		} else if (ReadWrite == ReadAccess) { 
			qspiDma.Qspid.qspiBuffer.pDataRx = pRxData;
			QSPI_SingleWriteSPI(&qspiDma.Qspid,
					(uint16_t const*)&qspiDma.Qspid.qspiCommand.Instruction);
			QSPI_MultiReadSPI(&qspiDma.Qspid, 
					(uint16_t *)qspiDma.Qspid.qspiBuffer.pDataRx, size);
		} else {
			TRACE_ERROR("%s Wrong access parameter \n\r", __FUNCTION__);
		} 
		QSPI_EndTransfer(qspiDma.Qspid.pQspiHw);
	}
	return 0;
}


/**
 * \brief Start S25FL1D Memory access with/without data write/read.
 * \param Instr Instruct 
 * \param pTxData point to Tx buffer address
 * \param pRxData point to Rx buffer address
 * \param ReadWrite Command/Write/Read access
 * \param Size buffer size in byte
 * \returns 0
 */
static uint8_t S25FL1D_MemoryAccess(uint8_t Instr, uint32_t Addr, 
				uint32_t *pTxData, uint32_t *pRxData, Access_t ReadWrite, 
				uint32_t size, uint8_t Secure)
{
	uint8_t SpiBuffer[4];
	qspiDma.Qspid.qspiCommand.Instruction = Instr;
	
	if(qspiDma.Qspid.qspiMode) {
		qspiDma.Qspid.qspiBuffer.pDataTx = pTxData;
		qspiDma.Qspid.qspiBuffer.pDataRx = pRxData;
		pMem->Addr=Addr;
		pMem->InstFrame.bm.bInstEn = 1;
		pMem->InstFrame.bm.bDataEn = 1;
		pMem->InstFrame.bm.bAddrEn = 1;
		qspiDma.Qspid.pQspiFrame =  pMem;
		if (ReadWrite == WriteAccess) {
		pMem->InstFrame.bm.bXfrType 
			= (QSPI_IFR_TFRTYP_TRSFR_WRITE_MEMORY >> QSPI_IFR_TFRTYP_Pos);
		qspiDma.Qspid.qspiBuffer.TxDataSize = size;
		} else {
		pMem->InstFrame.bm.bXfrType 
			= (QSPI_IFR_TFRTYP_TRSFR_READ_MEMORY >> QSPI_IFR_TFRTYP_Pos);
		qspiDma.Qspid.qspiBuffer.RxDataSize = size;
		}
		QSPI_EnableMemAccess(&qspiDma.Qspid, 0, Secure);
#ifdef USE_QSPI_DMA
		QSPID_ReadWriteQSPI(&qspiDma, ReadWrite);
#else
		QSPI_ReadWriteMem(&qspiDma.Qspid, ReadWrite);
#endif
	} else {
		qspiDma.Qspid.qspiBuffer.pDataTx = malloc((size+4));
		SpiBuffer[0] = Instr;
		SpiBuffer[1] = (uint8_t)(Addr >> 16);
		SpiBuffer[2] = (uint8_t)(Addr >> 8);
		SpiBuffer[3] = (uint8_t)(Addr); 
		memcpy(qspiDma.Qspid.qspiBuffer.pDataTx, SpiBuffer, 4);
        if(pTxData !=NULL) {
          memcpy((qspiDma.Qspid.qspiBuffer.pDataTx+1), pTxData, size);
        }
		
		if (ReadWrite == WriteAccess) {
		qspiDma.Qspid.qspiBuffer.TxDataSize  = size+4;
#ifdef USE_QSPI_DMA
		qspiDma.Qspid.qspiBuffer.RxDataSize  = size+4;
		qspiDma.Qspid.qspiBuffer.pDataRx = qspiDma.Qspid.qspiBuffer.pDataTx;
		QSPID_ReadWriteSPI(&qspiDma, ReadWrite);
#else        
		
		QSPI_MultiWriteSPI(&qspiDma.Qspid, 
						(uint16_t *)qspiDma.Qspid.qspiBuffer.pDataTx,
						qspiDma.Qspid.qspiBuffer.TxDataSize);
#endif
		} else {
#ifdef USE_QSPI_DMA
		qspiDma.Qspid.qspiBuffer.pDataRx = pRxData;
		/* instr(1) + addrs(3) + dummy read(1)*/
		qspiDma.Qspid.qspiBuffer.RxDataSize  = size+6;
		qspiDma.Qspid.qspiBuffer.TxDataSize  = size+6;
		QSPID_ReadWriteSPI(&qspiDma, ReadWrite);
		while(qspiDma.progress);
		/*qspiDma.Qspid.qspiBuffer.pDataRx = pRxData;
		qspiDma.Qspid.qspiBuffer.RxDataSize  = size;
		qspiDma.Qspid.qspiBuffer.TxDataSize  = size;
		QSPID_ReadWriteSPI(&qspiDma, ReadWrite);*/
#else
		qspiDma.Qspid.qspiBuffer.pDataRx = pRxData;
		qspiDma.Qspid.qspiBuffer.RxDataSize  = size;
		qspiDma.Qspid.qspiBuffer.TxDataSize  = 4;
		QSPI_MultiWriteSPI(&qspiDma.Qspid, 
						(uint16_t *)qspiDma.Qspid.qspiBuffer.pDataTx,
						qspiDma.Qspid.qspiBuffer.TxDataSize);
		QSPI_MultiReadSPI(&qspiDma.Qspid, 
						(uint16_t *)qspiDma.Qspid.qspiBuffer.pDataRx,
						size);
        QSPI_EndTransfer(qspiDma.Qspid.pQspiHw);
#endif
		}
		free(qspiDma.Qspid.qspiBuffer.pDataTx);
		qspiDma.Qspid.qspiBuffer.pDataTx= NULL;
	}
	return 0;
}

/**
 * \brief Reads and returns the status register of the serial flash.
 *
 * \param pS25fl1  Pointer to an S25FL1 driver instance.
 */
static uint32_t S25FL1D_ReadStatus(void)
{
	uint32_t status, ReadStatus;

	S25FL1D_SendCommand(READ_STATUS_1, 0, &ReadStatus, ReadAccess, 1);
	status = ReadStatus;
	
	S25FL1D_SendCommand(READ_STATUS_2, 0, &ReadStatus, ReadAccess, 1);
	status |= ((ReadStatus << 8) & 0xFF00);
	
	S25FL1D_SendCommand(READ_STATUS_3, 0, &ReadStatus, ReadAccess, 1);
	status |= ((ReadStatus << 16) & 0xFF0000);
	return status;
}

/**
 * \brief Reads and returns the status register of the serial flash.
 *
 * \param pS25fl1  Pointer to an S25FL1 driver instance.
 */
static uint8_t S25FL1D_ReadStatus1(void)
{
	uint8_t status;
	S25FL1D_SendCommand(READ_STATUS_1, 0, (uint32_t *)&status, ReadAccess, 1);
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
	S25FL1D_SendCommand(READ_STATUS_2, 0, (uint32_t *)&status, ReadAccess, 1);
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
	S25FL1D_SendCommand(READ_STATUS_3, 0, (uint32_t *)&status, ReadAccess, 1);
	return status;
}
/**
 * \brief Wait for transfer to finish calling the SPI driver ISR.
 * (interrupts are disabled)
 *
 * \param pS25fl1  Pointer to an S25FL1 driver instance.
 */
static void S25FL1D_IsBusy(void)
{
#ifdef USE_QSPI_DMA  
	while(QSPID_IsBusy(&qspiDma.progress) ) {
		Wait(1);
	}
#endif
	while(S25FL1D_ReadStatus1() & STATUS_RDYBSY);
}

static void S25FL1D_EnableWrite(void)
{
	uint8_t status = 0;


	while(!(status & STATUS_WEL)) {
		S25FL1D_SendCommand(WRITE_ENABLE, 0, 0, CmdAccess, 0);
		status = S25FL1D_ReadStatus1();
	}
}


static void S25FL1D_DisableWrite(void)
{
	uint8_t status;

	status = S25FL1D_ReadStatus1();

	while( (status & STATUS_WEL) != 0) {
		S25FL1D_SendCommand(WRITE_DISABLE, 0, 0, CmdAccess, 0);
		status = S25FL1D_ReadStatus1();
	}
}
/**
 * \brief Writes the given value in the status register of the serial flash
 * device.
 *
 * \param pS25fl1  Pointer to an S25FL1 driver instance.
 * \param status  Status to write.
 */
static void S25FL1D_WriteStatus( uint8_t *pStatus)
{
	S25FL1D_EnableWrite();

	S25FL1D_SendCommand(WRITE_STATUS, (uint32_t *)pStatus, 0, WriteAccess, 3);
	
	S25FL1D_DisableWrite();
}

/**
 * \brief Writes the given value in the status register of the serial flash
 * device.
 *
 * \param pS25fl1  Pointer to an S25FL1 driver instance.
 * \param status  Status to write.
 */
static void S25FL1D_WriteVolatileStatus( uint8_t *pStatus)
{
	uint32_t DataWr = 0;
	DataWr = *pStatus;
	
	S25FL1D_SendCommand(0x50, 0, 0 , CmdAccess, 0);
	
	S25FL1D_SendCommand(WRITE_STATUS,&DataWr, 0 , WriteAccess, 3);
	S25FL1D_DisableWrite();
}


static uint8_t S25FL1D_CheckProtectedAddr(uint8_t Status1, uint32_t Addr)
{
	const uint32_t AddrJump 
			= (Status1 & SEC_PROTECT_Msk) ? 0x001000UL : 0x010000UL;
	static uint8_t Protected = 0;
	
	const uint8_t blockBits = ((Status1 & BLOCK_PROTECT_Msk) >> 2);

	switch(blockBits) {
	case 1:
	if (Status1 & TOP_BTM_PROTECT_Msk) {
		if( ( Addr > 0x000000) && ( Addr < (0x000000 + AddrJump - 1) ) ) {
		Protected = 1;
		}
	} else {
		if( ( Addr > (0x1FFFFF - AddrJump + 1) ) && ( Addr < 0x1FFFFF  ) ) {
		Protected = 1;
		}
	}
	break;
	
	case 2:
	if (Status1 & TOP_BTM_PROTECT_Msk) {
		if( ( Addr > 0x000000) && ( Addr < (0x000000 + (2* AddrJump)- 1 )) ) {
		Protected = 1;
		}
	} else {
		if( ( Addr > (0x1FFFFF - ( 2*AddrJump ) + 1) ) && ( Addr < 0x1FFFFF  ) ){
		Protected = 1;
		}
	}
	break;
	case 3:
	if (Status1 & TOP_BTM_PROTECT_Msk) {
		if( ( Addr > 0x000000) && ( Addr < (0x000000 + (4 * AddrJump) - 1) )) {
		Protected = 1;
		}
	} else {
		if( ( Addr > (0x1FFFFF - ( 4*AddrJump ) + 1) ) && ( Addr < 0x1FFFFF  )) {
		Protected = 1;
		}
	}
	break;
	
	case 4:
	if (Status1 & TOP_BTM_PROTECT_Msk) {
		if( ( Addr > 0x000000) && ( Addr < (0x000000 + (8 * AddrJump) - 1) )) {
		Protected = 1;
		}
	} else {
		if( ( Addr > (0x1FFFFF - ( 8*AddrJump ) + 1) ) && ( Addr < 0x1FFFFF  )) {
		Protected = 1;
		}
	}
	break; 
	case 5:
	if( !(Status1 & SEC_PROTECT_Msk) ) {
		if (Status1 & TOP_BTM_PROTECT_Msk) {
			if( ( Addr > 0x000000) && ( Addr < (0x000000 + (16 * AddrJump) - 1) )) {
				Protected = 1;
			}
		} else {
			if( ( Addr > (0x1FFFFF - ( 16*AddrJump ) + 1) ) && ( Addr < 0x1FFFFF )) {
				Protected = 1;
			}
		}
	}
	break;
	
	case 6:
	
	if( !(Status1 & SEC_PROTECT_Msk) ) {
	
		if (Status1 & TOP_BTM_PROTECT_Msk) {
		if( ( Addr > 0x000000) && ( Addr < (0x000000 + (32 * AddrJump) - 1) )) {
			Protected = 1;
		}
		}
	}
	break;
	}

	return Protected;
}

/*----------------------------------------------------------------------------
 *         Global functions
 *----------------------------------------------------------------------------*/
void S25FL1D_InitFlashInterface(uint8_t Mode)
{   
	if(Mode) {
		QSPID_Configure(&qspiDma, QspiMemMode,
						QSPI_MR_CSMODE_LASTXFER, &qspiDmaInst);
		qspiDma.Qspid.qspiMode = (QspiMode_t)QSPI_MR_SMM_MEMORY;
		
		pDev = (QspiInstFrame_t *)malloc (sizeof(QspiInstFrame_t));
		memset(pDev, 0, sizeof(QspiInstFrame_t));
		pDev->InstFrame.bm.bwidth = QSPI_IFR_WIDTH_SINGLE_BIT_SPI;


		pMem = (QspiInstFrame_t *)malloc (sizeof(QspiInstFrame_t));
		memset(pMem, 0, sizeof(QspiInstFrame_t));
		pMem->InstFrame.bm.bwidth = QSPI_IFR_WIDTH_SINGLE_BIT_SPI;
	} else {
		QSPID_Configure(&qspiDma,
						SpiMode,(QSPI_MR_CSMODE_LASTXFER | QSPI_MR_DLYCS (20)),
						&qspiDmaInst);
		qspiDma.Qspid.qspiMode = (QspiMode_t)QSPI_MR_SMM_SPI;
	}
	
	QSPI_ConfigureClock(QSPI, ClockMode_00, QSPI_SCR_SCBR(1));
	
	QSPI_Enable(QSPI);
	
}

/**
 * \brief Reads and returns the serial flash device ID.
 *
 * \param pS25fl1  Pointer to an S25FL1 driver instance.
 */
uint32_t S25FL1D_ReadJedecId(void)
{
	static uint32_t pId;
	S25FL1D_SendCommand(READ_JEDEC_ID, 0, &pId, ReadAccess, 3);

	return pId;
}

/**
 * \brief Enables critical writes operation on a serial flash device, such as 
 * sector protection, status register, etc.
 *
 * \para pS25fl1  Pointer to an S25FL1 driver instance.
 */
void S25FL1D_QuadMode(uint8_t Enable)
{

	uint8_t status[3];
	
	status[0] = S25FL1D_ReadStatus1();
	status[1] = S25FL1D_ReadStatus2();
	status[2] = S25FL1D_ReadStatus3();

	if(Enable) {
		while(!(status[1] & STATUS_QUAD_ENABLE)) {
			status[1] |= STATUS_QUAD_ENABLE ;
			S25FL1D_WriteStatus(status);
			status[1] = S25FL1D_ReadStatus2();
			Wait(50);
		}
	} else {
		while((status[1] & STATUS_QUAD_ENABLE)) {
			status[1] &= (~STATUS_QUAD_ENABLE);
			S25FL1D_WriteStatus(status);
			status[1] = S25FL1D_ReadStatus2();
			Wait(50);
		}
	}
}


/**
 * \brief Enables critical writes operation on a serial flash device, such as 
 * sector protection, status register, etc.
 *
 * \para pS25fl1  Pointer to an S25FL1 driver instance.
 */
void S25FL1D_EnableWrap(uint8_t ByetAlign)
{

	uint8_t status[3];

	status[0] = S25FL1D_ReadStatus1();
	status[1] = S25FL1D_ReadStatus2();
	status[2] = S25FL1D_ReadStatus3();

	status[2] |= (ByetAlign << 5);

	pDev->InstFrame.bm.bDummyCycles = 24;
	S25FL1D_SendCommand(WRAP_ENABLE,(uint32_t *)&status[2], 0,  WriteAccess, 1);

	S25FL1D_WriteVolatileStatus(status);
	status[2] = S25FL1D_ReadStatus3();
	Wait(50);
}


/**
 * \brief Enables critical writes operation on a serial flash device, such as
 * sector protection, status register, etc.
 *
 * \para pS25fl1  Pointer to an S25FL1 driver instance.
 */
void S25FL1D_SetReadLatencyControl(uint8_t Latency)
{

	uint8_t status[3];

	status[0] = S25FL1D_ReadStatus();
	status[1] = S25FL1D_ReadStatus2();
	status[2] = S25FL1D_ReadStatus3();

	status[2] |= Latency;

	qspiDma.Qspid.qspiBuffer.pDataTx = (uint32_t *)&status[2];
	while(  (status[2] & STATUS_LATENCY_CTRL) != Latency) {
		S25FL1D_WriteVolatileStatus(status);
		status[2] = S25FL1D_ReadStatus3();
		Wait(50);
	}
}
void S25FL1D_SoftReset(void)
{
	S25FL1D_SendCommand(SOFT_RESET_ENABLE,0, 0,  CmdAccess, 0);
	S25FL1D_SendCommand(SOFT_RESET, 0, 0, CmdAccess, 0);
}

/**
 * \brief Unprotected the contents of the serial flash device.
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
		/* Unprotected sector protection registers by writing the status reg. */
		S25FL1D_WriteStatus(status);
	}
	S25FL1D_WriteStatus(status);

	/* Check the new status */
	status[0] = S25FL1D_ReadStatus();
	if ((status[0] & (STATUS_SPRL | STATUS_SWP)) != 0) {
		return ERROR_PROTECTED;
	} else {

		return 0;
	}
}

/**
 * \brief Unprotected the contents of the serial flash device.
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
	status[0]= S25FL1D_ReadStatus1();
	status[1]= S25FL1D_ReadStatus2();
	status[2]= S25FL1D_ReadStatus3();

	status[0] &= (!STATUS_SWP);
	/* Check if sector protection registers are locked */
	if ((status[0] & STATUS_SPRL) == STATUS_SPRL_LOCKED) {
		status[0] &= (!STATUS_SPRL);
		/* Unprotected sector protection registers by writing the status reg. */
		S25FL1D_WriteStatus(status);
	}
	S25FL1D_WriteStatus(status);

	/* Check the new status */
	status[0] = S25FL1D_ReadStatus();
	if ((status[0] & (STATUS_SPRL | STATUS_SWP)) != 0) {
		return ERROR_PROTECTED;
	} else {
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
	uint8_t Status = STATUS_RDYBSY;
	uint8_t ChipStatus= S25FL1D_ReadStatus1();
	
	if(ChipStatus & CHIP_PROTECT_Msk) {
		TRACE_ERROR("Chip is Protected \n\r");
		TRACE_INFO("Flash Status Register 1 is %x", ChipStatus);
		return 1;
	} else {
		S25FL1D_EnableWrite();
		S25FL1D_SendCommand(CHIP_ERASE_2, 0, 0, CmdAccess, 0);

		while(Status & STATUS_RDYBSY) {
			 
			Wait(200);
			printf("Erasing flash memory %c\r", wait_ch[i]);
			i++;
			Status = S25FL1D_ReadStatus1();
			memory_barrier();
			i = i % 4;
		}
		printf("\rErasing flash memory done..... 100%%\n\r");
		return 0;
	}
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
	uint8_t Secure = 0;
	/* Check that the flash is ready and unprotected */
	status = S25FL1D_ReadStatus1();
	if ((status & STATUS_RDYBSY) != STATUS_RDYBSY_READY) {
		TRACE_ERROR("%s : Flash busy\n\r", __FUNCTION__);
		return ERROR_BUSY;
	} else if (status & BLOCK_PROTECT_Msk) {
		if(S25FL1D_CheckProtectedAddr(status, address)) {
			TRACE_ERROR("%s : Flash Addrs is protected\n\r", __FUNCTION__);
			return ERROR_PROTECTED;
		}
	}

	/* Enable critical write operation */
	S25FL1D_EnableWrite();

	if(qspiDma.Qspid.qspiMode) {
		pDev->Addr = address;
		pDev->InstFrame.bm.bAddrEn = 1;
		/* Start the block erase command */
		S25FL1D_SendCommand(BLOCK_ERASE_4K, 0, 0, CmdAccess, 0);
	} else {
		/* Start the block erase command */
		S25FL1D_MemoryAccess(BLOCK_ERASE_4K, address, 0, 0, WriteAccess,
						0, Secure);
	}
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

	if(qspiDma.Qspid.qspiMode) {
		pDev->Addr = address;
		pDev->InstFrame.bm.bAddrEn = 1;
		/* Start the block erase command */
		S25FL1D_SendCommand(BLOCK_ERASE_64K, 0, 0, CmdAccess, 0);
	} else {
#ifdef USE_QSPI_DMA
		if(QSPID_EnableSpiChannel(&qspiDma) == QSPID_ERROR_LOCK)
			return 1;
#endif
		/* Start the block erase command */
		S25FL1D_MemoryAccess(BLOCK_ERASE_64K, address, 0, 0, WriteAccess, 0, 0);
#ifdef USE_QSPI_DMA
		QSPID_DisableSpiChannel(&qspiDma);
#endif
	}
	
	/* Wait for transfer to finish */
	S25FL1D_IsBusy();
	return 0;
}

/**
 * \brief Writes data at the specified address on the serial firmware dataflash.
 * The page(s) to program must have been erased prior to writing. This function
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
		uint32_t *pData,
		uint32_t size,
		uint32_t address,
		uint8_t Secure)
{
	unsigned int i = 0;
	
	uint32_t  NumberOfWrites = (size >> 8); //  ( (Size / pagezize)  )
	uint32_t Addrs = address;
  
#ifdef USE_QSPI_DMA    
	if(qspiDma.Qspid.qspiMode) {
		if(QSPID_EnableQspiTxChannel(&qspiDma) == QSPID_ERROR_LOCK)
		return 1;
	} else {
		if(QSPID_EnableSpiChannel(&qspiDma) == QSPID_ERROR_LOCK)
		return 1;
	}
#endif
	// if less than page size
	if(NumberOfWrites == 0) {
		S25FL1D_EnableWrite();
		S25FL1D_MemoryAccess(BYTE_PAGE_PROGRAM , Addrs, pData, 0, 
						WriteAccess, size, Secure);
	// multiple page
	} else {
		for(i=0; i< NumberOfWrites; i++) {
			S25FL1D_EnableWrite();
			S25FL1D_MemoryAccess(BYTE_PAGE_PROGRAM , Addrs, pData, 0,
							WriteAccess, PAGE_SIZE, Secure);
			S25FL1D_IsBusy();
			pData += (PAGE_SIZE >> 2);
			Addrs += PAGE_SIZE;
		}
		if(size % PAGE_SIZE ) {
			S25FL1D_EnableWrite();
			S25FL1D_MemoryAccess(BYTE_PAGE_PROGRAM , Addrs, pData, 0, 
							WriteAccess, (size - (NumberOfWrites * PAGE_SIZE)),
							Secure);
			S25FL1D_IsBusy();
		}
	}
#ifdef USE_QSPI_DMA
	  
		if(qspiDma.Qspid.qspiMode) {
		QSPID_DisableQspiTxChannel(&qspiDma);
		} else {
		QSPID_DisableSpiChannel(&qspiDma);
		}
	  
#endif
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
		uint32_t *pData,
		uint32_t size,
		uint32_t address)
{    
	uint8_t Secure = 0;
	
#ifdef USE_QSPI_DMA
	if(qspiDma.Qspid.qspiMode) {
		if(QSPID_EnableQspiRxChannel(&qspiDma) == QSPID_ERROR_LOCK)
		return 1;
	} else {
		if(QSPID_EnableSpiChannel(&qspiDma) == QSPID_ERROR_LOCK)
		return 1;
	}
#endif
		
		S25FL1D_MemoryAccess(READ_ARRAY , address, 0, pData, 
						ReadAccess, size , Secure);
    
#ifdef USE_QSPI_DMA
		
		if(qspiDma.Qspid.qspiMode) {
			QSPID_DisableQspiRxChannel(&qspiDma);
		} else {
			QSPID_DisableSpiChannel(&qspiDma);
		}
#endif
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
		uint32_t *pData,
		uint32_t size,
		uint32_t address)
{
  
	uint8_t Secure = 0;
#ifdef USE_QSPI_DMA  
	if(qspiDma.Qspid.qspiMode) {
		if(QSPID_EnableQspiRxChannel(&qspiDma) == QSPID_ERROR_LOCK)
		return 1;
	} else {
		if(QSPID_EnableSpiChannel(&qspiDma) == QSPID_ERROR_LOCK)
		return 1;
	}
#endif
		pMem->InstFrame.bm.bDummyCycles = 8;
		pMem->InstFrame.bm.bwidth = QSPI_IFR_WIDTH_DUAL_OUTPUT;
	  
		S25FL1D_MemoryAccess(READ_ARRAY_DUAL , address, 0, pData, 
						ReadAccess, size, Secure);
	  
#ifdef USE_QSPI_DMA
	while(QSPID_IsBusy(&qspiDma.progress) ) {
		Wait(1);
	}
	if(qspiDma.Qspid.qspiMode) {
		QSPID_DisableQspiRxChannel(&qspiDma);
	} else {
		QSPID_DisableSpiChannel(&qspiDma);
	}
#endif
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
		uint32_t *pData,
		uint32_t size,
		uint32_t address)
{
	uint8_t Secure = 0;
#ifdef USE_QSPI_DMA
	if(qspiDma.Qspid.qspiMode) {
		if(QSPID_EnableQspiRxChannel(&qspiDma) == QSPID_ERROR_LOCK)
		return 1;
	} else {
		if(QSPID_EnableSpiChannel(&qspiDma) == QSPID_ERROR_LOCK)
		return 1;
	}
#endif
	pMem->InstFrame.bm.bDummyCycles = 8;
	pMem->InstFrame.bm.bwidth = QSPI_IFR_WIDTH_QUAD_OUTPUT;
	S25FL1D_MemoryAccess(READ_ARRAY_QUAD,	address, 0, pData,
					ReadAccess, size, Secure);
	
#ifdef USE_QSPI_DMA
	while(QSPID_IsBusy(&qspiDma.progress) ) {
		Wait(1);
	}
	if(qspiDma.Qspid.qspiMode) {
		QSPID_DisableQspiRxChannel(&qspiDma);
	} else {
		QSPID_DisableSpiChannel(&qspiDma);
	}
#endif
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
unsigned char S25FL1D_ReadDualIO(
		uint32_t *pData,
		uint32_t size,
		uint32_t address,
		uint8_t ContMode,
		uint8_t Secure)
{
#ifdef USE_QSPI_DMA  
	if(qspiDma.Qspid.qspiMode) {
		if(QSPID_EnableQspiRxChannel(&qspiDma) == QSPID_ERROR_LOCK)
		return 1;
	} else {
		if(QSPID_EnableSpiChannel(&qspiDma) == QSPID_ERROR_LOCK)
		return 1;
	}
#endif
	pMem->InstFrame.bm.bDummyCycles = 4;
	if(ContMode) {
		pMem->InstFrame.bm.bOptLen
			= (QSPI_IFR_OPTL_OPTION_4BIT >> QSPI_IFR_OPTL_Pos);
		qspiDma.Qspid.qspiCommand.Option= 0x2;
		pMem->InstFrame.bm.bContinuesRead = ContMode;
		pMem->InstFrame.bm.bDummyCycles = 3;
	}
	pMem->InstFrame.bm.bwidth = QSPI_IFR_WIDTH_DUAL_IO;
	S25FL1D_MemoryAccess(READ_ARRAY_DUAL_IO , address, 0,
					pData, ReadAccess, size, Secure);
	pMem->InstFrame.bm.bOptEn = 0;
	pMem->InstFrame.bm.bContinuesRead  = 0;
#ifdef USE_QSPI_DMA
	while(QSPID_IsBusy(&qspiDma.progress) ) {
		Wait(1);
	}
	if(qspiDma.Qspid.qspiMode) {
		QSPID_DisableQspiRxChannel(&qspiDma);
	} else {
		QSPID_DisableSpiChannel(&qspiDma);
	}
#endif
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
		uint32_t *pData,
		uint32_t size,
		uint32_t address,
		uint8_t ContMode,
		uint8_t Secure)
{
#ifdef USE_QSPI_DMA  
	if(qspiDma.Qspid.qspiMode) {
		if(QSPID_EnableQspiRxChannel(&qspiDma) == QSPID_ERROR_LOCK)
		return 1;
	} else {
	if(QSPID_EnableSpiChannel(&qspiDma) == QSPID_ERROR_LOCK)
		return 1;
	}
#endif
	pMem->InstFrame.bm.bDummyCycles = 6;
	if(ContMode) {
		pMem->InstFrame.bm.bOptLen
			= (QSPI_IFR_OPTL_OPTION_4BIT >> QSPI_IFR_OPTL_Pos);
		qspiDma.Qspid.qspiCommand.Option= 0x2;
		pMem->InstFrame.bm.bContinuesRead = ContMode;
		pMem->InstFrame.bm.bDummyCycles = 5;
		pMem->InstFrame.bm.bOptEn = 1;
	}

	pMem->InstFrame.bm.bwidth = QSPI_IFR_WIDTH_QUAD_IO;
	S25FL1D_MemoryAccess(READ_ARRAY_QUAD_IO , address, 0,
						pData, ReadAccess, size, Secure);
	pMem->InstFrame.bm.bOptEn = 0;
	pMem->InstFrame.bm.bContinuesRead = 0;
#ifdef USE_QSPI_DMA
	while(QSPID_IsBusy(&qspiDma.progress) ) {
		Wait(1);
	}
	if(qspiDma.Qspid.qspiMode) {
		QSPID_DisableQspiRxChannel(&qspiDma);
	} else {
		QSPID_DisableSpiChannel(&qspiDma);
	}
#endif
	return 0;
}

